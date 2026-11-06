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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 231 of its 289 lines of code are new or changed and 395 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KMOD: its first piece, from
   the cut KMODEL 0x86840 (lib/B/Prog/m_file_m.v MF_KMODEL_stmt) to ieq's return MK_IRET 0x86854
   (lib/B/Prog/mf_kmod_m.v MK_IRET_stmt). A sub-lane of a walk lane of the image-B m_file-family owner's G2B.
   proves no function (kind: segment lemma of m_file's image-B walk, S_MF_KMOD piece a).
   Adapted from image A's lib/A/Prog/m_file_s_kmod_a.v (commit c1e1a58468c5, mk_kmodel_ok up to
   ieq's call) and image B's KDISP / KIGN ieq call sites (working-branch files mf_krole_d.v
   kr_s_disp and mf_kignp_1.v ki_s_kign: the same code shape).

   mk_kmodel_ok : forall n, MK_IRET_stmt B n -> MF_KMODEL_stmt B n.

   THE CODE (the neutral listing of m_file in image B lines 450-454):
     86840 ld a0,208(s1)                    a0 = k = p + ok (the K cut's 208(s1), mf_slot)
     86844 auipc a1 / 86848 addi a2,a1      a2 = 0x21220 "model" (listing object 19, m_file_sd.v mf_lit_obj)
     8684c mv a1,s5                         a1 = kl
     86850 jal ieq                          a0 = b2z (ieq k "model") (m_file_iq.v mf_ieq_call), back at 0x86854
   One load from the frame cell 208(s1), no store, no instrumented check (the load is from m_file's own frame
   cells, which the code does not check), no UBSan trap branch. The run starts from m_file_sd.v's mf_seed with the
   scratch cells 208(s1) = k (atom 52) and 192(s1) = v (atom 53) as chunks of the frame-cell region, every region
   read-only (mka_seed), so the run changes no byte (mka_ro_frame) and m_file_k.v's mf_keep_run0 carries the cut
   facts to the jal. ieq is the shared step mf_ieq_call (its KCHAIN / KROD / KLIT: m_file_k.v mf_chain, mf_rod_now
   under RELRO, mf_lit_now), with the key's bytes seg_spec.zb k at p + ok in the text's block (mka_slice_facts); at
   the return the frame cells 208(s1) and 192(s1) lie above s1, outside ieq's window [s1 - STK_ieq, s1)
   (mka_slot_keep), the registers s5, s10, s11 and mf_regs_at's eleven are callee-saved, and MK_IRET_stmt closes.
   Section hypotheses: VOBJS (the seed, the literal bridge), SIGP (ieq's call target), RELRO (mf_rod_now), IEQ. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kmod_m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the line is a prefix of the text left *)
Lemma mka_line_le : forall rest, (length (mf_line rest) <= length rest)%nat.
Proof.
unfold mf_line. induction rest as [|b r IH]; cbn [break_nl]; [cbn; lia|].
destruct (b =? NL); [cbn; lia|]. destruct (break_nl r) as [l q] eqn:E. cbn [fst] in IH |- *. cbn [length]. lia.
Qed.

(* ieq_pre's bytes: the list Z read at a through an ASan reader, as list byte, and back *)
Lemma mka_bytes_of_zs : forall segs H mem a (l : list Z), sa_zs (aview segs H mem) a l ->
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

(* the scratch-cell chunks: 208(s1) = k (atom 52), 192(s1) = v (atom 53) *)
Definition mka_slx : list YP09.chunk :=
  [YP09.mkChunk 208 (CVal 8 (SOff 52 0)); YP09.mkChunk 192 (CVal 8 (SOff 53 0))].
(* the seed's regions (m_file_sd.v mf_regions with the frame cells' chunk 120 and the scratch cells only) and the
   same with the frame cells read-only: every write window empty *)
Definition mka_regions : smem := mf_regions false false mka_slx false false [] false MF_LOW_ON.
Definition mka_rs : smem :=
  [mf_r_saved; set_window (mf_r_slots false false mka_slx) 0 0; mf_r_fh false; mf_r_low false []; mf_r_ft;
   mf_r_fs false MF_LOW_ON].
Lemma mka_wf : regions_wf mka_regions = true /\ regions_wf mka_rs = true.
Proof. split; vm_compute; reflexivity. Qed.
(* a run from such a state changed no byte *)
Lemma mka_ro_frame : forall E (m m' : word -> option byte), frame_of E mka_rs m m' -> forall x, m' x = m x.
Proof.
intros E m m' HF x. apply HF. intros (r & Hin & Hw).
unfold mka_rs, mf_r_saved, set_window, mf_r_slots, mf_r_fh, mf_r_low, mf_r_ft, mf_r_fs in Hin.
cbn [In] in Hin.
repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_wlo YP09.r_whi] in Hw; lia |]). destruct Hin.
Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* a register the symbolic state still names by an atom *)
Lemma mka_st_reg : forall segs E ss (H : word -> bool) ms (r : bv 5) (n : nat),
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
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis VOBJS : seg_val_objs.
Hypothesis SIGP : seg_sig_prog.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState, ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.
Let RUN := paj_run B LAWS.

(* the text left's sub-range [o, o + n): its bytes as list byte, addressable, in the text block *)
Lemma mka_slice_facts : forall v lyc Sc Wc memc mdc pos lowsh mcc cur line p rest o n,
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
destruct (mka_bytes_of_zs SEGS (w_H Wc) memc _ _ HZ) as (HB & HZB).
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
Lemma mka_pres : forall E R regs1 v lyc pos cur np xs (rr : bvmap 5 word),
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
Lemma mka_slot_chunk : forall v regs1 lyc pos cur np (xs : list Z) (Wc : world SEGS) memc off (i : nat) x,
  nth i xs 0 = x -> (52 + i < A_TEXT)%nat -> 0 <= x < 2 ^ 64 -> mf_slot v memc Wc off x ->
  YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np xs) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))
    (YP09.mkChunk off (CVal 8 (SOff (52 + i) 0))).
Proof.
intros v regs1 lyc pos cur np xs Wc memc off i x Hx Hi Hx64 Hs.
apply (mf_chunk_atom _ _ _ off (52 + i) 0 x); [rewrite (mfE_xs regs1 v lyc pos cur np xs i Hi), Hx; reflexivity
  | exact Hx64 | lia | rewrite Z.add_0_r; exact Hs].
Qed.
Lemma mka_slx_ok : forall v regs1 lyc pos cur np (Wc : world SEGS) memc ko vo,
  0 <= ko < 2 ^ 64 -> 0 <= vo < 2 ^ 64 -> mf_slot v memc Wc 208 ko -> mf_slot v memc Wc 192 vo ->
  Forall (YP09.chunk_ok SEGS (mfE regs1 v lyc pos cur np [ko; vo]) (mrestrict (w_H Wc) memc) (mf_s1 (mv_sp v))) mka_slx.
Proof.
intros v regs1 lyc pos cur np Wc memc ko vo Hk Hv Sk Sv. unfold mka_slx.
apply Forall_cons; [apply (mka_slot_chunk v regs1 lyc pos cur np [ko; vo] Wc memc 208 0 ko); [reflexivity | unfold A_TEXT; lia | exact Hk | exact Sk]|].
apply Forall_cons; [apply (mka_slot_chunk v regs1 lyc pos cur np [ko; vo] Wc memc 192 1 vo); [reflexivity | unfold A_TEXT; lia | exact Hv | exact Sv]|].
apply Forall_nil.
Qed.

(* the piece's symbolic state at pc: mf_seed (no frame-cell chunk but 120 and the two scratch cells; cur, np not
   read) with the frame cells read-only *)
Lemma mka_seed : forall v lyc Sc Wc regs1 memc mdc pos mcc ko vo pc,
  mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc -> mf_regs_at B v lyc pos regs1 ->
  0 <= ko < 2 ^ 64 -> 0 <= vo < 2 ^ 64 -> mf_slot v memc Wc 208 ko -> mf_slot v memc Wc 192 vo ->
  st_ok_pi SEGS VAL (mfE regs1 v lyc pos None 0 [ko; vo]) (mkSS pc sr_mf mka_rs None mf_facts)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc ko vo pc CX CORE RA Hk Hv Sk Sv.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
destruct mka_wf as (WF1 & WF2).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc None 0 [ko; vo] pc false false mka_slx
  false false [] false CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia)
  ltac:(intros Hf; discriminate Hf) ltac:(lia) ltac:(unfold MF_LOW_ON; lia)
  (mka_slx_ok v regs1 lyc pos None 0 Wc memc ko vo Hk Hv Sk Sv) (Forall_nil _) WF1) as HS.
set (E := mfE regs1 v lyc pos None 0 [ko; vo]) in *.
set (r := mf_r_slots false false mka_slx).
assert (Hn : nth_error (ss_mem (ss_mf pc false false mka_slx false false [] false MF_LOW_ON)) 1 = Some r)
  by reflexivity.
exact (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS Hn eq_refl WF2
  (region_ok_rewindow _ E _ r 0 0 (st_ok_pi_region_nth E _ _ 1 r HS Hn) ltac:(intros o Ho; lia))).
Qed.

(* an 8-byte frame cell off(s1) is kept by a change outside a window [lo, hi) below s1 *)
Lemma mka_slot_keep : forall v (W W' : world SEGS) m m' lo hi off x,
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

(* the literal's register: "model" is listing object 19 *)
Lemma mka_lit_reg : forall E, img_env VAL A_LIM E ->
  sv_denot E (SOff (A_OBJ 19) 0) = w64 (SegInstB.seg_litA_fz S_model).
Proof.
intros E HEI. cbn [sv_denot]. rewrite Z.add_0_r.
rewrite (mf_lit_obj VOBJS S_model 19 ltac:(unfold MF_LIT_OBJS; repeat (first [left; reflexivity | right]))).
unfold w64. f_equal. apply (HEI (A_OBJ 19)). unfold A_OBJ, A_TEXT, A_LIM; lia.
Qed.

(* KMODEL 0x86840: a0 = 208(s1) = k, a2 = "model", a1 = s5 = kl; ieq(k, kl, "model") (m_file_iq.v mf_ieq_call),
   then MK_IRET 0x86854 with a0 = b2z (ieq k "model") *)
Lemma mk_kmodel_ok : forall n, MK_IRET_stmt B n -> MF_KMODEL_stmt B n.
Proof.
intros n IRET. unfold MF_KMODEL_stmt, MF_KAT_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv
  CX LS FRM CORE CELLS RA LEN NE LOOP KV MISS FIN S208 _ R21 S192 R26 R27 NP.
unfold mf_at.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof (mka_line_le rest) as Hml.
pose proof LOOP as (_ & _ & _ & _ & (LA0 & LA1 & _) & _).
assert (Hk64 : 0 <= p + Z.of_nat ok < 2 ^ 64) by lia.
assert (Hv64 : 0 <= p + Z.of_nat ov < 2 ^ 64) by lia.
pose proof (mka_seed v lyc Sc Wc regs1 memc mdc pos mcc (p + Z.of_nat ok) (p + Z.of_nat ov) MF_KMODEL CX CORE RA
  Hk64 Hv64 S208 S192) as HS.
set (E := mfE regs1 v lyc pos None 0 [p + Z.of_nat ok; p + Z.of_nat ov]) in *.
assert (HEI : img_env VAL A_LIM E) by (unfold E, mfE; apply Eimg_env).
assert (SHOK : sh_ok SEGS (SOff 32 0) (@nil shent) E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; apply Forall_nil).
pose proof CORE as (HJ & _).
(* 0x86840-0x86850: a0 = k, a2 = "model", a1 = kl; the jal to ieq *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  repeat (apply awr_ok_cons_ro; [cbn; lia|]). apply awr_ok_nil. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg _ ?d) _ => set (mdq := d) in *; clearbody mdq end.
pose proof (mka_ro_frame E _ _ HF) as HMEQ.
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HMEQ; reflexivity).
assert (HPc : aregs_preserved regs1 (ms_regs ms)).
{ eapply (mka_pres E _ regs1 v lyc pos None 0 [p + Z.of_nat ok; p + Z.of_nat ov] (ms_regs ms) eq_refl RB).
  - intros r. exact (st_ok_restrict_reg SEGS (w_H Wc) E _ ms r HS).
  - vm_compute. reflexivity. }
(* the registers at the jal: the callee-saved ones are the cut's, a0 = k, a1 = kl, a2 = "model", ra = MK_IRET *)
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
assert (Q2 : getr (ms_regs ms) 2 = w64 (mf_s1 (mv_sp v))) by (rewrite <- R2; exact (HPc 2 ltac:(unfold acallee_saved; lia))).
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite <- R3; exact (HPc 3 ltac:(unfold acallee_saved; lia))).
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite <- R4; exact (HPc 4 ltac:(unfold acallee_saved; lia))).
assert (Q8 : getr (ms_regs ms) 8 = w64 (mv_sp v)) by (rewrite <- R8; exact (HPc 8 ltac:(unfold acallee_saved; lia))).
assert (Q10 : getr (ms_regs ms) 10 = w64 (p + Z.of_nat ok)).
{ rewrite (mka_st_reg SEGS _ _ _ _ 10%bv 52%nat HS) by (vm_compute; reflexivity).
  exact (mfE_xs regs1 v lyc pos None 0 [p + Z.of_nat ok; p + Z.of_nat ov] 0 ltac:(unfold A_TEXT; lia)). }
assert (Q11 : getr (ms_regs ms) 11 = w64 (Z.of_nat kl)).
{ rewrite (mka_st_reg SEGS _ _ _ _ 11%bv 21%nat HS) by (vm_compute; reflexivity).
  unfold E. rewrite (mfE_reg regs1 v lyc pos None 0 _ 21 (Z_to_bv 5 21) eq_refl). exact R21. }
assert (Q12 : getr (ms_regs ms) 12 = w64 (SegInstB.seg_litA_fz S_model)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 12%bv HS).
  lazymatch goal with |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e' end.
  exact (mka_lit_reg E HEI). }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + MK_IRET)).
{ rewrite (st_ok_restrict_reg SEGS (w_H Wc) E _ ms 1%bv HS).
  lazymatch goal with |- _ = Z_to_bv 64 (_ + ?kk) =>
    transitivity (sv_denot E (SOff A_TEXT kk)); [f_equal; vm_compute; reflexivity|] end.
  exact (codeptr_val E MK_IRET HEI). }
(* the jal's target *)
rewrite (SIGP SS_ieq ltac:(unfold seg_prog_syms; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_ieq) with AF_ieq by (vm_compute; reflexivity).
(* the cut's facts at the jal's memory (the run changed no byte) *)
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) (ms_mem ms) mdq CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
pose proof (NPk _ NP) as NP'. pose proof (LPk mcc (Some gi) line p rest LOOP) as LOOP'.
pose proof (mka_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 208 _ CX (Z.le_refl _)
  ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S208) as S208'.
pose proof (mka_slot_keep v Wc Wc memc (ms_mem ms) (mf_s1 (mv_sp v)) (mf_s1 (mv_sp v)) 192 _ CX (Z.le_refl _)
  ltac:(lia) ltac:(lia) (fun a Ha _ => EQV a Ha) S192) as S192'.
destruct (mka_slice_facts v lyc Sc Wc (ms_mem ms) mdq pos MF_LOW_ON mcc (Some gi) line p rest ok kl CX CORE' LOOP'
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite KV3 in SB, SZ, SL.
refine (mf_ieq_call B IEQ (mf_chain B) (mf_rod_now B RELRO) (mf_lit_now B) v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdq
  pos MF_LOW_ON mcc (Some gi) line p rest (mf_next p rest) MK_IRET (p + Z.of_nat ok) (Z.of_nat kl) (seg_spec.zb k)
  S_model CX LS CORE' CELLS' LOOP' NP' Q2 Q3 Q4 Q8 Q1 _ _ _ Q10 Q11 Q12 S0 SB SL SA SH _).
- unfold MK_IRET, AF_m_file; lia.
- unfold MK_IRET, AF_m_file; reflexivity.
- unfold M_FILE_LITS; repeat (first [left; reflexivity | right]).
- (* 0x86854, ieq's return: MK_IRET with the cut's state and a0 = b2z (ieq k "model") *)
  intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
  assert (HP12 : aregs_preserved regs1 regs2) by exact (aregs_preserved_trans _ _ _ HPc HP2).
  rewrite SZ in A02.
  apply (IRET v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv).
  + unfold mk_base.
    refine (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj (mf_regs_keep B v lyc pos regs1 regs2 RA HP12)
      (conj LEN (conj NE (conj LOOP2 (conj NP2 _)))))))))).
    transitivity (getr regs1 27); [exact (HP12 27 ltac:(unfold acallee_saved; lia)) | exact R27].
  + exact KV.
  + exact MISS.
  + exact FIN.
  + exact (mka_slot_keep v Wc W2 (ms_mem ms) mem2 _ _ 208 _ CX (Z.le_refl _) ltac:(lia) ltac:(lia) K2 S208').
  + transitivity (getr regs1 21); [exact (HP12 21 ltac:(unfold acallee_saved; lia)) | exact R21].
  + exact (mka_slot_keep v Wc W2 (ms_mem ms) mem2 _ _ 192 _ CX (Z.le_refl _) ltac:(lia) ltac:(lia) K2 S192').
  + transitivity (getr regs1 26); [exact (HP12 26 ltac:(unfold acallee_saved; lia)) | exact R26].
  + exact A02.
Qed.
End e.
End f.
End d.

About mk_kmodel_ok.
Print Assumptions mk_kmodel_ok.
