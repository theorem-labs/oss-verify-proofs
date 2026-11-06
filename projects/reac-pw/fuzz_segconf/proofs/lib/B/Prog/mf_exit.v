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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 179 of its 225 lines of code are new or changed and 407 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140): the segment S_MF_EXIT of its walk, 57
   instructions from the cut EXIT 0x86da0 to the `ret` 0x86e80 (the image-B m_file segment table section 13,
   the image-B m_file cut map section 4). A walk lane of the image-B m_file-family owner's G2B. Adapted from image A's lib/A/Prog/m_file_s_exit.v
   (the image-A m_file-family lane, commit ba33778143e7) at image B's numbers. No call and no
   UBSan trap: the side-stack frame is released inline.

   What the code does (B pc), on the side-stack frame path (FB = FAKE = s7 <> 0; mf_core, mf_regs_ex):
     0x86da0-0x86dac  a0 = 0x45e0360e; a1 = 120(s1) = FB; FB + 0 = a0 (the retired-frame magic)
     0x86db0          `beqz s7` not taken (s7 = FB >= 4096; image A: s8)
     0x86db4-0x86df4  the frame's 16 shadow bytes at s8 = shadow(FB) = 0xf5 (the bytes are marked unusable; image A:
                      s10)
     0x86df8-0x86dfc  a0 = 120(s7), the flag pointer in the frame's last word; the flag byte = 0 (the inline release;
                      kit astack_free_law / frame_flag_lawP through PaLibF.v aj_flag_store_pi)
     0x86e00          `j 0x86e44`
     0x86e44-0x86e7c  sp = s0 - 320; ra, s0 .. s11 loaded back from sp0 - 8 .. sp0 - 104; sp = sp0
     0x86e80          `ret`
   The real-stack branch 0x86e04-0x86e40 (s7 = 0) is not taken. The post is apost_baseF at this segment's FP state
   through PaFx.v apost_baseF_of_base (no FP state change): the journal with the frame released (stack_free_state 1
   pos), the callee-saved registers back, the mconf block unchanged by the epilogue (mf_tx_mconf, the
   shared lib/B/Prog/m_file_k.v) and so holding mf_final v, and the frame form sa_noalloc (the layout kept, the state the
   entry's up to st_fs). The allocator model's laws aj_flag_store_pi takes are model_laws_ok (lib/B/YG05.v) of AR's
   am_universe at the cut state, so the segment's only frame hypotheses are astack_free_law and frame_flag_lawP. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YG05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Open Scope Z_scope.

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
(* the seed's listing objects, and the frame's inline release (the kit's laws astack_free_law, frame_flag_lawP;
   the image-B m_file segment table's callee table, row "the inline release") *)
Hypothesis VOBJS : seg_val_objs.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RET := paj_ret_at (PL := PL_seg) (PI := PI).

(* the contract's post at the return, from the state the epilogue leaves: the journal with the frame released,
   the callee-saved registers back, every byte outside mf_win as at the cut *)
Lemma mf_exit_post : forall v lyc Sc (Wc : world SEGS) memc mdc pos regs' mem' md',
mf_cx B v -> mf_ls v lyc Sc -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF (mf_final v) ->
ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [] lyc (stack_free_state 1 pos Sc) Wc mem' md' 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a ->
  rdW Wc mem' a = rdW Wc memc a) ->
aregs_preserved (mv_regs v) regs' ->
MF_POST B v Wc (mkCfg (mkst regs' (getr (mv_regs v) 1) mem' (seg_rom SEGS)) md').
Proof.
intros v lyc Sc Wc memc mdc pos regs' mem' md' CX LS CORE HJ' K HP.
pose proof CORE as (_ & HPerm & _ & _ & _ & _ & Hmc & _).
unfold MF_POST. apply (apost_baseF_of_base SEGS). unfold apost_base.
exists lyc, (stack_free_state 1 pos Sc), regs', mem', md'.
split; [reflexivity|]. split; [exact HJ'|]. split; [exact HP|]. split.
- exact (mf_tx_mconf B v lyc Sc Wc memc mdc mem' pos MF_LOW_OFF (mf_final v) (mf_final v) CX CORE K Hmc).
- split; [unfold ablocks; rewrite blocks_stack_free_state; exact HPerm|].
  destruct LS as (Ely & fS & ES). split; [exact Ely|].
  exists (st_fs (stack_free_state 1 pos Sc)). rewrite ES. reflexivity.
Qed.

(* the state's form, computed *)
Ltac mfx_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

(* S_MF_EXIT at one FP state *)
Lemma mf_exit_at : MF_EXIT_stmt B.
Proof.
unfold MF_EXIT_stmt. intros v lyc Sc Wc regs1 memc mdc pos CX LS CORE RX.
pose proof pa_segs_low as Hsegs.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (al_frames SEGS B LAWS _ _ _ _ _ 1 pos HAR Hin) as (_ & _ & _ & HFSpres).
destruct (FFL _ _ _ _ _ 1 pos HAR Hin) as (HFLp & _ & _ & HFL4096 & _ & _).
change (fs_frame_bytes 1 / 8) with 16 in HFSpres.
(* the allocator model's laws, from AR at the cut state *)
pose proof (YG05.model_laws_ok (as_universe B) (am_universe _ _ _ _ (proj1 HAR))) as ML.
pose proof (aj_flag_store_pi B LAWS ML ASF FFL) as RUNF.
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in S1.
pose proof CX as (HPRE & _). pose proof HPRE as (_ & Hra & _ & Hgp & Htp & _).
pose proof (mf_regs_base_of_ex B v lyc pos regs1 RX) as RB.
pose proof RX as (R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 320) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
(* the flag cell is the runtime's: outside the frame and its shadow *)
assert (SF1 : flag_addr lyc 1 pos + 1 <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= flag_addr lyc 1 pos).
{ destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (frame_addr lyc 1 pos)) as [h | h]; [left; lia|].
  destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (frame_addr lyc 1 pos + 128)) as [h' | h']; [|right; lia].
  exfalso. exact (F4 _ (conj h h') F5). }
assert (SS1 : flag_addr lyc 1 pos + 1 <= SHADOW_OFF + frame_addr lyc 1 pos / 8 \/
  SHADOW_OFF + frame_addr lyc 1 pos / 8 + 16 <= flag_addr lyc 1 pos).
{ destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (SHADOW_OFF + frame_addr lyc 1 pos / 8)) as [h | h]; [left; lia|].
  destruct (Z_lt_le_dec (flag_addr lyc 1 pos) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + 16)) as [h' | h']; [|right; lia].
  exfalso. destruct (HFSpres (flag_addr lyc 1 pos - (SHADOW_OFF + frame_addr lyc 1 pos / 8)) ltac:(lia)) as [_ Hno].
  apply Hno. unfold shadow_addr. replace (SHADOW_OFF + frame_addr lyc 1 pos / 8 +
    (flag_addr lyc 1 pos - (SHADOW_OFF + frame_addr lyc 1 pos / 8))) with (flag_addr lyc 1 pos) by lia. exact F5. }
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF (mf_final v) None 0 [] MF_EXIT false false [] true
  false [] true CX CORE RB ltac:(intros Hf; discriminate Hf) ltac:(cbn [mf_cur_ptr]; lia) ltac:(intros Hf; discriminate Hf)
  ltac:(lia) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos None 0 []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos None 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 3%nat ltac:(unfold A_TEXT; lia)) as E35.
pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
cbn [Nat.add nth mf_extra map app] in E34, E35, E36.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64, mf_s1; apply unsigned_lit_small; lia).
assert (U8 : bv_unsigned (ew E 8) = mv_sp v)
  by (rewrite (EE 8%nat 8%bv eq_refl), R8; unfold w64; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = flag_addr lyc 1 pos) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
(* the frame cells read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. mfx_norm HS1.
(* s7 = FB (atom 34), s8 = shadow(FB) (atom 36) *)
apply (ast_ok_pi_set_reg_fp E _ _ (23%bv : bv 5) (SOff 34 0)) in HS1;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E34; cbn [ms_regs restrict mkst];
     rewrite R23; reflexivity].
mfx_norm HS1.
apply (ast_ok_pi_set_reg_fp E _ _ (24%bv : bv 5) (SOff 36 0)) in HS1;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E36; cbn [ms_regs restrict mkst];
     rewrite R24; reflexivity].
mfx_norm HS1.
(* the flag cell, written by the release *)
assert (HS2 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 35%nat) 0 1 0 1 []) HS1 ltac:(vm_compute; reflexivity)).
clear HS1.
lapply HS2; clear HS2; [intros HS2|].
2:{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U35. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. replace (flag_addr lyc 1 pos + o) with (flag_addr lyc 1 pos) by lia. cbn [restrict ms_mem mkst].
    apply (apresent_writable SEGS). exact HFLp. }
lapply HS2; clear HS2; [intros HS2|].
2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U35, ?U2, ?U8, ?U34, ?U36.
    unfold mf_s1, SHADOW_OFF in *. repeat split; first [exact I | lia]. }
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
unfold mf_at.
(* the release and the return, one plain run to the `ret` *)
paj_run_flag_sh RUNF HS2 HJ.
- lia.
- intros a (r & Hr & Ha).
  lazymatch type of Hr with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr end.
  cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite ?U34, ?U35, ?U36 in Ha;
    first [ exfalso; lia
    | right; lia
    | left; right; right; right; left; exists 1, pos; split; [left; reflexivity|];
      first [ left; unfold in_zr; cbn [fst snd]; change (fs_frame_bytes 1) with 128; lia
            | right; unfold in_zr, shadow_addr; cbn [fst snd]; change (fs_frame_bytes 1 / 8) with 16; lia ] ] |]);
  destruct Hr.
- intros msr HSr. unfold st_ok_pi in HSr.
  pose proof (st_ok_mem_ok SEGS E _ msr HSr) as (_ & HOK & _).
  unfold abs_ss, setpc in HOK. cbn [ss_mem] in HOK.
  apply Forall_inv in HOK. destruct HOK as (_ & _ & _ & HC). apply Forall_inv in HC.
  destruct (HC 0 ltac:(split; [lia | cbv; reflexivity])) as (b & Hb1 & Hb2).
  cbn [base_val YP09.r_base YP09.c_off] in Hb2. rewrite U35 in Hb2.
  replace (flag_addr lyc 1 pos + 0 + 0) with (flag_addr lyc 1 pos) in Hb2 by lia. rewrite Hb2.
  cbn [YP09.cbyte YP09.c_val sv_denot] in Hb1. injection Hb1 as <-. vm_compute. reflexivity.
- lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a ->
      rdW Wc (ms_mem msc) a = rdW Wc m0 a);
    [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc)
        (mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos)) HFr _ a Ha HnW);
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw];
        [injection Hq as <- <- <-; cbn [base_val] in Hr; rewrite ?U34, ?U35, ?U36 in Hr; unfold mf_win; lia |]);
      destruct Hinw | ] end.
  assert (E39 : ew E 39 = getr (mv_regs v) (1%bv : bv 5))
    by (change 39%nat with (32 + 7)%nat; rewrite EX by (unfold A_TEXT; lia); reflexivity).
  prreg HS2 (1%bv : bv 5) Q1.
  eapply (RET Wc _ _ _ _ _ HS2 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbn [ms_regs ms_mem].
  unfold YK0s.ret_ok in Hra. rewrite Q1, E39, Hra.
  apply (mf_exit_post v lyc Sc Wc memc mdc pos _ _ _ CX LS CORE).
  + apply (ajournal_materialize SEGS B LAWS Hsegs). exact HJ.
  + exact K.
  + unfold aregs_preserved. intros r Hr.
    assert (Hcases : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
      r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27 \/ False) by (unfold acallee_saved in Hr; lia).
    clear Hr.
    repeat (destruct Hcases as [-> | Hcases]); [..| destruct Hcases];
    (rewrite (st_ok_pi_restrict_reg (w_H Wc) E _ _ _ HS2); cbn [ms_regs];
     lazymatch goal with |- sv_denot _ (sr_get ?a ?rr2) = _ =>
       let e := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with e end;
     cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned).
    all: try (lazymatch goal with |- ew _ ?n = getr _ (Z_to_bv 5 ?rr) =>
      let j := eval compute in (n - 32)%nat in change n with (32 + j)%nat; rewrite (EX j) by (unfold A_TEXT; lia);
      reflexivity end).
    all: first
    [ rewrite (EE 8%nat 8%bv eq_refl), R8; replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity);
      unfold w64, mv_sp, spZ; apply Z_to_bv_bv_unsigned
    | rewrite (EE 3%nat 3%bv eq_refl), R3; replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity);
      rewrite Hgp; reflexivity
    | rewrite (EE 4%nat 4%bv eq_refl), R4; replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity);
      rewrite Htp; reflexivity ].
Qed.
End e.
End f.
End d.

(* the segment at every FP state (m_file_m.v's S_MF_EXIT = MF_EXIT_F) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Lemma S_MF_EXIT_ok : S_MF_EXIT (rc := rc) (SK := SK) (PI := PI) B.
Proof. intros fx0. exact (mf_exit_at (fx := fx0) B VOBJS ASF FFL). Qed.
(* inside the Sections: the segment's hypotheses as its assumptions *)
About S_MF_EXIT_ok. Print Assumptions S_MF_EXIT_ok.
End i.
End h.
End g.
About S_MF_EXIT_ok. Print Assumptions S_MF_EXIT_ok.
