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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 306 of its 365 lines of code are new or changed and 394 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_HDRA: the point walk from
   RS1 0x86534 (the first strip's return, lib/B/Prog/mf_hdra_m.v HDA_RS1_stmt) to REF 0x867c0 (HDA_REF_stmt) or
   RIEQ 0x86558 (ieq's return, HDA_RIEQ_stmt). A sub-lane of a walk lane of the image-B m_file-family owner's G2B.
   proves no function (kind: segment lemma of m_file's image-B walk: the point RS1 -> REF / RIEQ of segment
   S_MF_HDRA).

   hda_rs1 : forall n, HDA_REF_stmt B n -> HDA_RIEQ_stmt B n -> HDA_RS1_stmt B n.

   THE CODE (the neutral listing of m_file in image B, lines 255-264; listing slots AF_m_file + 0x3f4 ..
   + 0x414 = SegList.v lines 1552-1560):
     86534 ld a1,200(s1)                    a1 = be = p + r1 (the cell 200(s1), mf_slot; atom 53)
     86538 ld a0,208(s1)                    a0 = b = p + q1 (the cell 208(s1), mf_slot; atom 52)
     8653c sub a1,a1,a0 / 86540 li a2,8
     86544 blt a1,a2,867c0                  be - b < 8 (signed): to REF, the model is the refusal (mf_hdra_t.v
                                            hd_ix_short over r1 < q1 + 8)
     86548 auipc a1 / 8654c addi a2,a1      a2 = 0x21100 "segment" (listing object 16, m_file_sd.v mf_lit_obj)
     86550 li a1,7
     86554 jal ieq                          ieq(b, 7, "segment") (m_file_iq.v mf_ieq_call), back at 0x86558
   Two loads from m_file's own frame cells, no store, no instrumented check (the frame cells are not checked), no
   UBSan trap branch: this piece owns no trap and no check. be - b = r1 - q1 lies in [0, 2 ^ 63) (mf_hdra_t.v
   hd_q1r1: q1 <= r1 <= j - 1 inside the line, mf_loop's sa_addr: p + |rest| + 1 <= 2 ^ 63), so the signed `blt`
   is the compare of r1 - q1 with 8 (hd3_ux: the engine's a1 = be + b * (-1) is be - b; hd3_br, over hd3_blt).
   THE RUN starts from m_file_sd.v's mf_seed with the cells 208(s1) = b (atom 52) and 200(s1) = be (atom 53) as caller
   chunks slx of the frame-cell region (region 1, [16, 216)), narrowed to read-only (hd3_rs, image A's
   hda_ro_slots idiom at image B's bounds), so each token run changes no byte (hd3_frame_ro) and m_file_k.v's
   mf_carry_eq carries the point's facts (hd3_line_carry). The engine steps the `jal` (slot PCall SS_ieq 1) to
   SIGMA SS_ieq, which SIGP (SegObj.v seg_sig_prog) equates with BASE + AF_ieq; ieq is the shared step
   mf_ieq_call (KCHAIN / KROD / KLIT: m_file_k.v mf_chain, mf_rod_now under RELRO, mf_lit_now) with the 7 bytes
   seg_spec.zb (slice q1 (q1 + 7) rest) at b in the text's block (hd3_slice_facts); at the return the cells 208(s1)
   and 200(s1) lie above s1, outside ieq's window [s1 - STK_ieq, s1) (hd3_slot_keep), and the registers s5, s11 and
   mf_regs_at's eleven are callee-saved.
   POSITIONAL NAMES checked against image B's listing and SegAddr.v: HDA_RS1 = AF_m_file + 0x3f4 (0x86534), HDA_REF
   = + 0x680 (0x867c0, the blt's target 0x86544 + 0x27c), HDA_RIEQ = + 0x418 (0x86558), the jal slot + 0x414
   (PCall SS_ieq), A_OBJ 16 = seg_objs[16] = 0x21100 (= 0x86548 + (0xfff9b << 12) - 1096), the cell offsets 200 /
   208 (words 0x0c84b583 / 0x0d04b503), the frame-cell region index 1 and the atoms 52 / 53 (this file's xs).
   Section hypotheses: SIGP (ieq's call target), VOBJS (the seed, the literal bridge), RELRO (mf_rod_now), IEQ. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k ieq_c m_file_iq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_hdra_t mf_hdra_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ieq_pre's bytes: the list Z read at a through an ASan reader, as list byte, and back (mf_kmod_a.v
   mka_bytes_of_zs) *)
Lemma hd3_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
  sa_bytes (aview segs H mem) a (seg_spec.zb l) /\ seg_spec.zs (seg_spec.zb l) = l.
Proof.
intros segs H mem a l HZ.
assert (HR : Forall (fun z => 0 <= z < 256) l).
{ apply Forall_forall. intros z Hz. apply In_nth with (d := 0) in Hz as (i & Hi & <-).
  exact (sa_aview_rng segs H mem _ _ (HZ i Hi)). }
split; [|exact (sa_zs_zb l HR)].
intros i Hi. unfold seg_spec.zb in Hi. rewrite length_map in Hi. rewrite (HZ i Hi). f_equal.
unfold seg_spec.zb. rewrite (nth_indep _ ZB0 (Z_to_bv 8 0)) by (rewrite length_map; exact Hi).
rewrite map_nth. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
symmetry. apply Z.mod_small. exact (proj1 (Forall_forall _ _) HR _ (nth_In _ _ Hi)).
Qed.

(* the scratch-cell chunks: 208(s1) = b (atom 52), 200(s1) = be (atom 53) *)
Definition hd3_slx : list YP09.chunk :=
  [YP09.mkChunk 208 (CVal 8 (SOff 52 0)); YP09.mkChunk 200 (CVal 8 (SOff 53 0))].
(* the seed's regions (no frame-cell chunk but 120 and the two scratch cells) and the same with the frame cells
   read-only: every write window empty *)
Definition hd3_regions : smem := mf_regions false false hd3_slx false false [] false MF_LOW_OFF.
Definition hd3_rs : smem :=
  [mf_r_saved; set_window (mf_r_slots false false hd3_slx) 0 0; mf_r_fh false; mf_r_low false []; mf_r_ft;
   mf_r_fs false MF_LOW_OFF].
Lemma hd3_wf : regions_wf hd3_regions = true /\ regions_wf hd3_rs = true.
Proof. split; vm_compute; reflexivity. Qed.

(* the signed branch `blt` as a compare of the wrapped values *)
Lemma hd3_blt : forall E a b,
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (bv_swrap 64 (U E a) <? bv_swrap 64 (U E b)).
Proof. intros E a b. cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned. reflexivity. Qed.
(* the engine's a1 at the blt (0x8653c `sub a1,a1,a0`): be + b * (-1), which is be - b *)
Lemma hd3_ux : forall E b be, ew E 52 = Z_to_bv 64 b -> ew E 53 = Z_to_bv 64 be -> 0 <= b <= be -> be < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 52 0) (SLit (-1))) (SOff 53 0)) = be - b.
Proof.
intros E b be H52 H53 Hb Hbe.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw]. rewrite U_SLit.
rewrite (U_atom E 53 be H53), (U_atom E 52 b H52) by lia.
change (zcanon (-1)) with (2 ^ 64 - 1). unfold zcanon, M64.
Z.div_mod_to_equations. lia.
Qed.
(* the blt 0x86544 over be - b and 8: taken exactly when be - b < 8 (be - b < 2 ^ 63, so signed = unsigned) *)
Lemma hd3_br : forall E b be (t : bool), ew E 52 = Z_to_bv 64 b -> ew E 53 = Z_to_bv 64 be -> 0 <= b <= be ->
  be < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E (SAlu ALU_ADD (SMd M_MUL (SOff 52 0) (SLit (-1))) (SOff 53 0))) (sv_denot E (SLit 8))
    = t ->
  if t then be - b < 8 else 8 <= be - b.
Proof.
intros E b be t H52 H53 Hb Hbe H. rewrite hd3_blt in H.
rewrite (hd3_ux E b be H52 H53 Hb ltac:(lia)), U_SLit in H. change (zcanon 8) with 8 in H.
rewrite !swrap64_id in H by (unfold half64; lia).
destruct t; [apply Z.ltb_lt in H | apply Z.ltb_ge in H]; lia.
Qed.

(* the write-permission goal of a run whose regions are all read-only *)
Ltac hd3_awr_ro :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom *)
Lemma hd3_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
  st_ok segs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff n 0 -> getr (ms_regs ms) r = ew E n.
Proof.
intros segs E ss H ms r n HS Hr. rewrite (st_ok_restrict_reg segs H E ss ms r HS), Hr.
cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a run over a state whose regions are all read-only changed no byte (image A's hda_frame_ro) *)
Lemma hd3_frame_ro : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true ->
  forall a, aview SEGS H m' a = aview SEGS H m a.
Proof.
intros E rs H m m' HF Hro a. unfold aview, mbyte. rewrite HF; [reflexivity|].
intros (r & Hin & Hr). pose proof (proj1 (forallb_forall _ _) Hro r Hin) as Hw. apply Z.leb_le in Hw. lia.
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis SIGP : seg_sig_prog.
Hypothesis VOBJS : seg_val_objs.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the text left's sub-range [o, o + n): its bytes as list byte, addressable, in the text block (mf_kmod_a.v
   mka_slice_facts) *)
Lemma hd3_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n,
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
destruct (hd3_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HZB).
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

(* the callee-saved registers of a state whose symbolic registers are the seed's on CALLEE_SAVED *)
Lemma hd3_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
  E = mfE regs1 v lyc pos cur np xs -> mf_regs_base v regs1 ->
  (forall r, getr rr r = sv_denot E (sr_get R r)) ->
  forallb (fun r : bv 5 => sv_eqb (sr_get R r) (sr_get sr_mf r)) CALLEE_SAVED = true ->
  aregs_preserved regs1 rr.
Proof.
intros E R regs1 v lyc pos cur np xs rr HE RB HR HC r Hr.
pose proof (mf_regs_ok v regs1 lyc pos cur np xs RB) as HO. rewrite <- HE in HO.
rewrite HR, HO. f_equal. apply sv_eqb_eq.
assert (Hin : In (Z_to_bv 5 r) CALLEE_SAVED).
{ unfold acallee_saved in Hr.
  assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
    r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
    unfold CALLEE_SAVED; cbn [In]; first [ tauto | intuition (apply bv_eq; reflexivity) ]. }
exact (proj1 (forallb_forall _ _) HC _ Hin).
Qed.

(* a scratch cell as a chunk of the extra atom 52 + i *)
Lemma hd3_slot_chunk : forall v regs1 lyc pos cur np (xs : list Z) (Wc : world SEGS) memc off (i : nat) x,
  nth i xs 0 = x -> (52 + i < A_TEXT)%nat -> 0 <= x < 2 ^ 64 -> mf_slot v memc Wc off x ->
  YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))
    (YP09.mkChunk off (CVal 8 (SOff (52 + i) 0))).
Proof.
intros v regs1 lyc pos cur np xs Wc memc off i x Hx Hi Hx64 Hs.
apply (mf_chunk_atom _ _ _ off (52 + i) 0 x); [rewrite (mfE_xs regs1 v lyc pos cur np xs i Hi), Hx; reflexivity
  | exact Hx64 | lia | rewrite Z.add_0_r; exact Hs].
Qed.
Lemma hd3_slx_ok : forall v regs1 lyc pos cur np (Wc : world SEGS) memc b be,
  0 <= b < 2 ^ 64 -> 0 <= be < 2 ^ 64 -> mf_slot v memc Wc 208 b -> mf_slot v memc Wc 200 be ->
  Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np [b; be]) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) hd3_slx.
Proof.
intros v regs1 lyc pos cur np Wc memc b be Hb Hbe Sb Sbe. unfold hd3_slx.
apply Forall_cons; [apply (hd3_slot_chunk v regs1 lyc pos cur np [b; be] Wc memc 208 0 b); [reflexivity | unfold A_TEXT; lia | exact Hb | exact Sb]|].
apply Forall_cons; [apply (hd3_slot_chunk v regs1 lyc pos cur np [b; be] Wc memc 200 1 be); [reflexivity | unfold A_TEXT; lia | exact Hbe | exact Sbe]|].
apply Forall_nil.
Qed.

(* the piece's symbolic state at pc: mf_seed (cur, np not read) with the frame cells read-only *)
Lemma hd3_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc b be pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_regs_at B v lyc pos regs1 ->
  0 <= b < 2 ^ 64 -> 0 <= be < 2 ^ 64 -> mf_slot v memc Wc 208 b -> mf_slot v memc Wc 200 be ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos None 0 [b; be]) (mkSS pc sr_mf hd3_rs None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc b be pc CX CORE RA Hb Hbe Sb Sbe.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
destruct hd3_wf as (WF1 & WF2).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc None 0 [b; be] pc false false hd3_slx
  false false [] false CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia)
  ltac:(intros Hf; discriminate Hf) ltac:(lia) ltac:(unfold MF_LOW_OFF; lia)
  (hd3_slx_ok v regs1 lyc pos None 0 Wc memc b be Hb Hbe Sb Sbe) (Forall_nil _) WF1) as HS.
set (E := mfE regs1 v lyc pos None 0 [b; be]) in *.
set (r := mf_r_slots false false hd3_slx).
assert (Hn : nth_error (ss_mem (ss_mf pc false false hd3_slx false false [] false MF_LOW_OFF)) 1 = Some r)
  by reflexivity.
exact (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS Hn eq_refl WF2
  (region_ok_rewindow _ E _ r 0 0 (st_ok_pi_region_nth E _ _ 1 r HS Hn) ltac:(intros o Ho; lia))).
Qed.

(* an 8-byte frame cell off(s1) is kept by a change outside a window [lo, hi) below s1 *)
Lemma hd3_slot_keep : forall v (W W' : world SEGS) m m' lo hi off x,
  mf_cx B v -> hi <= mf_s1 (mv_sp v) -> 0 <= off -> off + 8 <= 216 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> rdW W' m' a = rdW W m a) ->
  mf_slot v m W off x -> mf_slot v m' W' off x.
Proof.
intros v W W' m m' lo hi off x CX Hhi Ho0 Ho8 K H. unfold mf_slot in *.
destruct (mf_s1_facts B v CX) as (Hs1 & _ & Hc). destruct (mf_sp0 B v CX) as (_ & H47 & _).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((C1 & C2) & C3). unfold YG0f.ASAN_CEIL in C1, C2, C3.
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hc.
apply (iq_val_keep W W' m m' _ 8 x); [|exact H].
intros a Ha. change (Z.of_nat 8) with 8 in Ha. apply K; destruct Hs1 as [E1 | E1]; rewrite E1 in *; lia.
Qed.

(* the point's line facts across a run that changed no byte (image A's hda_line_carry, over m_file_k.v's
   mf_carry_eq) *)
Lemma hd3_line_carry : forall n v lyc Sc Wc memc mdc memc' mdc' pos mcc cur line p rest,
  hda_line B n v lyc Sc Wc memc mdc pos mcc cur line p rest ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc memc' mdc' 0 ->
  (forall a, rdW Wc memc' a = rdW Wc memc a) ->
  hda_line B n v lyc Sc Wc memc' mdc' pos mcc cur line p rest.
Proof.
intros n v lyc Sc Wc memc mdc memc' mdc' pos mcc cur line p rest
  (CX & LS & FRM & CORE & CELLS & Hlen & Hne & LOOP & NP) HJ KA.
destruct (mf_carry_eq B v lyc Sc Wc memc mdc memc' mdc' pos MF_LOW_OFF mcc mcc cur line p rest CX CORE HJ
  (fun a _ => KA a) LOOP) as (CORE' & LOOP' & CELLSK & NPK).
exact (conj CX (conj LS (conj FRM (conj CORE' (conj (CELLSK cur CELLS) (conj Hlen (conj Hne (conj LOOP' (NPK _ NP))))))))).
Qed.

(* the literal's register: "segment" is listing object 16 *)
Lemma hd3_lit_reg : forall E, img_env VAL A_LIM E ->
  sv_denot E (SOff (A_OBJ 16) 0) = w64 (SegInstB.seg_litA_fz S_segment).
Proof.
intros E HEI. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (mf_lit_obj VOBJS S_segment 16 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
unfold w64. f_equal. apply (HEI (A_OBJ 16)). unfold A_OBJ, A_TEXT, A_LIM; lia.
Qed.

(* RS1 0x86534: a1 = 200(s1) = be, a0 = 208(s1) = b; be - b < 8 refuses (REF 0x867c0); else a2 = "segment",
   a1 = 7, ieq(b, 7, "segment") (m_file_iq.v mf_ieq_call), then RIEQ 0x86558 *)
Lemma hda_rs1 : forall n, HDA_REF_stmt B n -> HDA_RIEQ_stmt B n -> HDA_RS1_stmt B n.
Proof.
intros n REF RIEQ. unfold HDA_RS1_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j HL RA HH HC S208 S200 R21 R27.
unfold mf_at.
pose proof HL as (CX & LS & FRM & CORE & CELLS & LEN & NE & LOOP & NP).
pose proof HH as (Hl512 & Hij & Hjl & _ & _ & FIN).
pose proof HC as (_ & H2).
pose proof (hd_line_le rest) as Hml.
destruct (hd_q1r1 rest i j ltac:(lia) H2) as (Q1a & Q1b).
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & _).
assert (Hb64 : 0 <= p + Z.of_nat (hda_q1 rest i j) < 2 ^ 64) by lia.
assert (Hbe64 : 0 <= p + Z.of_nat (hda_r1 rest i j) < 2 ^ 64) by lia.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof (hd3_seed v lyc Sc Wc regs1 memc mdc pos mcc (p + Z.of_nat (hda_q1 rest i j)) (p + Z.of_nat (hda_r1 rest i j))
  HDA_RS1 CX CORE RA Hb64 Hbe64 S208 S200) as HS.
set (E := mfE regs1 v lyc pos None 0 [p + Z.of_nat (hda_q1 rest i j); p + Z.of_nat (hda_r1 rest i j)]) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
assert (E52 : ew E 52 = Z_to_bv 64 (p + Z.of_nat (hda_q1 rest i j)))
  by exact (mfE_xs regs1 v lyc pos None 0 [p + Z.of_nat (hda_q1 rest i j); p + Z.of_nat (hda_r1 rest i j)] 0
    ltac:(unfold A_TEXT; lia)).
assert (E53 : ew E 53 = Z_to_bv 64 (p + Z.of_nat (hda_r1 rest i j)))
  by exact (mfE_xs regs1 v lyc pos None 0 [p + Z.of_nat (hda_q1 rest i j); p + Z.of_nat (hda_r1 rest i j)] 1
    ltac:(unfold A_TEXT; lia)).
pose proof CORE as (HJ & _).
(* 0x86534-0x86540: a1 = be, a0 = b, a1 = be - b, a2 = 8; the run stops at the blt 0x86544 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ hd3_awr_ro. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq1 := d) in *; clearbody mdq1 end.
pose proof (hd3_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA1.
pose proof (hd3_line_carry n v lyc Sc Wc memc mdc (ms_mem ms) mdq1 pos mcc cur line p rest HL HJ KA1) as HL1.
pose proof (hd3_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 208 _ CX (Z.le_refl _)
  ltac:(lia) ltac:(lia) (fun a _ _ => KA1 a) S208) as S208a.
pose proof (hd3_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 200 _ CX (Z.le_refl _)
  ltac:(lia) ltac:(lia) (fun a _ _ => KA1 a) S200) as S200a.
clear HF HFr HG KA1 HL CORE CELLS LOOP NP S208 S200.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* be - b < 8: m_header refuses (mf_hdra_t.v hd_ix_short), to REF 0x867c0 *)
  pose proof (hd3_br E _ _ true E52 E53 ltac:(lia) ltac:(lia) Hc) as Hlt. cbv beta iota in Hlt. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan HDA_REF.
  { hd3_awr_ro. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq2 := d) in *; clearbody mdq2 end.
  pose proof (hd3_frame_ro E _ (w_H Wc) (ms_mem ms1) (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA2.
  pose proof (hd3_line_carry n v lyc Sc Wc (ms_mem ms1) mdq1 (ms_mem ms) mdq2 pos mcc cur line p rest HL1 HJ KA2)
    as HL2.
  assert (HPc : aregs_preserved regs1 (ms_regs ms)).
  { eapply (hd3_pres E _ regs1 v lyc pos None 0 [p + Z.of_nat (hda_q1 rest i j); p + Z.of_nat (hda_r1 rest i j)]
      (ms_regs ms) eq_refl RB).
    - intros r. exact (st_ok_pi_restrict_reg (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  assert (HM : m_header mcc (hda_sl rest i j) (line + 1) = (m_refuse mcc (line + 1) false, None))
    by (apply hd_ix_short; solve [exact HC | lia]).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst _ (Z_to_bv 64 (_ + ?kk)) _ _) _) _ =>
    replace kk with HDA_REF by (unfold HDA_REF, AF_m_file; reflexivity) end.
  apply (REF v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq2 pos mcc cur line p rest HL2
    (mf_regs_keep B v lyc pos regs1 (ms_regs ms) RA HPc)).
  + rewrite <- HM. exact FIN.
  + transitivity (getr regs1 27); [exact (HPc 27 ltac:(unfold acallee_saved; lia)) | exact R27].
- (* q1 + 8 <= r1: a2 = "segment", a1 = 7, the jal to ieq *)
  pose proof (hd3_br E _ _ false E52 E53 ltac:(lia) ltac:(lia) Hc) as Hge. cbv beta iota in Hge. clear Hc.
  paj_run_tok RUN HS HJ SHOK Bspan.
  { hd3_awr_ro. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq2 := d) in *; clearbody mdq2 end.
  pose proof (hd3_frame_ro E _ (w_H Wc) (ms_mem ms1) (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA2.
  pose proof (hd3_line_carry n v lyc Sc Wc (ms_mem ms1) mdq1 (ms_mem ms) mdq2 pos mcc cur line p rest HL1 HJ KA2)
    as HL2.
  pose proof (hd3_slot_keep v Wc Wc (ms_mem ms1) (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 208 _ CX
    (Z.le_refl _) ltac:(lia) ltac:(lia) (fun a _ _ => KA2 a) S208a) as S208b.
  pose proof (hd3_slot_keep v Wc Wc (ms_mem ms1) (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 200 _ CX
    (Z.le_refl _) ltac:(lia) ltac:(lia) (fun a _ _ => KA2 a) S200a) as S200b.
  assert (HPc : aregs_preserved regs1 (ms_regs ms)).
  { eapply (hd3_pres E _ regs1 v lyc pos None 0 [p + Z.of_nat (hda_q1 rest i j); p + Z.of_nat (hda_r1 rest i j)]
      (ms_regs ms) eq_refl RB).
    - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS).
    - vm_compute. reflexivity. }
  (* the registers at the jal: the callee-saved ones are the point's, a0 = b, a1 = 7, a2 = "segment",
     ra = RIEQ *)
  pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
  assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
  assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
  assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
  assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
  assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat (hda_q1 rest i j))).
  { rewrite (hd3_st_reg SEGS _ _ _ _ 10%bv 52%nat HS) by (vm_compute; reflexivity). exact E52. }
  assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat 7)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 11%bv HS).
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    reflexivity. }
  assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_segment)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 12%bv HS).
    lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
    exact (hd3_lit_reg E HEI). }
  assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + HDA_RIEQ)).
  { rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
    lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
      transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
    exact (codeptr_val E HDA_RIEQ HEI). }
  (* the jal's target *)
  rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
  replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
  pose proof HL2 as (_ & _ & _ & CORE2 & CELLS2 & _ & _ & LOOP2 & NP2).
  destruct (hd3_slice_facts v lyc Sc Wc (ms_mem ms) mdq2 pos MF_LOW_OFF mcc cur line p rest (hda_q1 rest i j) 7
    CX CORE2 LOOP2 ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
  refine (mf_ieq_call B IEQ (mf_chain B) (mf_rod_now B RELRO) (mf_lit_now B) v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq2
    pos MF_LOW_OFF mcc cur line p rest (mf_next p rest) HDA_RIEQ (p + Z.of_nat (hda_q1 rest i j)) (Z.of_nat 7)
    (seg_spec.zb (firstn 7 (skipn (hda_q1 rest i j) rest))) S_segment CX LS CORE2 CELLS2 LOOP2 NP2
    Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
  + unfold HDA_RIEQ, AF_m_file; lia.
  + unfold HDA_RIEQ, AF_m_file; reflexivity.
  + unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
  + (* 0x86558, ieq's return: RIEQ with the point's state and a0 = b2z (ieq b[0, 7) "segment") *)
    intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE3 CELLS3 LOOP3 NP3 HP2 A02 K2.
    assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
    rewrite SZ in A02.
    apply (RIEQ v lyc S2 W2 regs2 mem2 md2 pos mcc cur line p rest i j).
    * exact (conj CX (conj LS2 (conj FRM (conj CORE3 (conj CELLS3 (conj LEN (conj NE (conj LOOP3 NP3)))))))).
    * exact (mf_regs_keep B v lyc pos regs1 regs2 RA HP12).
    * exact HH.
    * exact HC.
    * lia.
    * exact (hd3_slot_keep v Wc W2 (ms_mem ms) mem2 _ _ 208 _ CX (Z.le_refl _) ltac:(lia) ltac:(lia) K2 S208b).
    * exact (hd3_slot_keep v Wc W2 (ms_mem ms) mem2 _ _ 200 _ CX (Z.le_refl _) ltac:(lia) ltac:(lia) K2 S200b).
    * rewrite A02. unfold slice. replace (hda_q1 rest i j + 7 - hda_q1 rest i j)%nat with 7%nat by lia. reflexivity.
    * transitivity (getr regs1 21); [exact (HP12 21 ltac:(unfold acallee_saved; lia)) | exact R21].
    * transitivity (getr regs1 27); [exact (HP12 27 ltac:(unfold acallee_saved; lia)) | exact R27].
Qed.
End e.
End f.
End d.

About hda_rs1.
Print Assumptions hda_rs1.
