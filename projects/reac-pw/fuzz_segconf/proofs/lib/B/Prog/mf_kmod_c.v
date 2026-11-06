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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module names changed; 220 of its 268 lines of code are new or changed and 405 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, 0x86140), segment S_MF_KMOD, piece c
   (lib/B/Prog/mf_kmod_m.v): mk_cret_ok : MK_LI_stmt B n -> MK_CRET_stmt B n, from checked_memcpy's return MK_CRET
   0x868a4 to MK_LI 0x86c18. A walk lane of the image-B m_file-family owner's G2B (a piece agent). proves no function (kind:
   segment lemma of m_file's image-B walk, S_MF_KMOD piece c). Templates: image A's lib/A/Prog/m_file_s_krole_h.v
   (kr_hit_run / kr_s_hit: the stores into g at atom 37 with a shadow entry of the mconf block, then mf_keep and
   mf_loop_next), in the form of image B's lib/B/Prog/mf_krole_x.v (kr_miss_ret: one run to a cut, then the cut).

   THE CODE (listing m_file.fuzz_segconf.asan-ubsan.s lines 475-483 and 696; the slow path 735-738; the error path 886):
     0x868a4  addi a0,s4,32          a0 = g + 32 = &g->model_set (s4 = g = c + 256 gi, MK_CRET_stmt)
     0x868a8  srli a1,a0,3; add a1,a1,s2; lb a1,0(a1); bnez a1,0x86cb4
                                     the instrumented check of the 4-byte store at g + 32: a load of the shadow byte
                                     at (a0 >> 3) + the shadow base and a compare; the slow path 0x86cb4-0x86cc0 and
                                     the error path 0x86f10 (a call of errpath_store4) are not reached
     0x868b8  li a1,1; sw a1,0(a0)   g->model_set = 1
     0x868c0  ld s9,112(s1)          s9 = c (mf_cells' 112(s1))
     0x868c4  j 0x86c18              MK_LI
   No UBSan trap branch is in this code.
   THE CHECK 0x868b0 and why its taken edge is refuted: the shadow entry mkSHE 37 32 36 (atom 37 = g, the 136(s1)
   value mf_cur_ptr c (Some gi), pinned to s4), from mf_core's sa_addr c 9236 (the mconf block is addressable) by
   shent_ok_of_range, the block outside the shadow span (m_file_sd.v mf_blk_app): the shadow byte of [g + 32, g + 36)
   shows the 4 bytes addressable, so the token executor takes the fast path and the slow and error paths are not run.
   THE STORE: the region [g + 32, g + 36) at atom 37, writable (the mconf block's bytes are present), allowed by awr_ok:
   the bytes are in M_FILE_FP's entry gi (mf_kmod_t.v mkt_mk_fp_seg, gi < |mc_seg (mf_final v)| from the model
   equation by mkt_mf_fin_segs_mono) and in the mconf block's heap block.
   THE MODEL: at MK_CRET the block holds m_upd mcc gi (mkt_set_model low); its entry gi's model field holds low ++ [0]
   (mc_model_zs); with g->model_set = 1 the block holds m_upd mcc gi (ms_with_model low) (mf_kmod_t.v
   mkt_sa_mconf_with_model, mkt_upd_upd_model). The cut facts at the new memory by m_file_k.v mf_keep_run_s (the
   written set [g + 32, g + 36) lies in the mconf block), the next line by mf_loop_next (the counters are the
   entry's: m_upd keeps them), and MK_LI_stmt at (line + 1, mf_next p rest, mf_rest rest, cur = Some gi), whose model
   equation is MK_CRET's (mf_fin). Section hypothesis: VOBJS (mf_seed). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaFx SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kmod_t mf_kmod_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* entry gi's model field through the reader: its C string and its NUL at g + 0x24 (seg_spec.mseg_enc's cstr_enc 24) *)
Lemma mc_model_zs : forall (rd : reader) c mc gi, sa_mconf rd c mc -> (gi < length (mc_seg mc))%nat ->
  sa_zs rd (seg_spec.mseg_addr c gi + seg_spec.MS_MODEL) (ms_model (nth gi (mc_seg mc) mseg_d) ++ [0]).
Proof.
intros rd c mc gi (bs & Hb & He) Hgi.
destruct He as (HL & Hn32 & Hsegs & _).
pose proof (Hsegs gi Hgi) as Henc.
destruct Henc as (_ & _ & _ & _ & _ & _ & _ & Hmod & _).
unfold seg_spec.fldz in Hmod. change (Z.to_nat seg_spec.MS_MODEL) with 36%nat in Hmod.
change (Z.to_nat 24) with 24%nat in Hmod.
destruct Hmod as (Hl24 & Hlt & _ & Hz).
unfold seg_spec.SEG_M_SIZE in HL.
set (s := ms_model (nth gi (mc_seg mc) mseg_d)) in *.
intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
rewrite <- Hz. rewrite mkt_nth_firstn by lia.
rewrite mkt_zs_nth by (rewrite Hl24; lia).
rewrite mkt_fld_nth by lia. rewrite mkt_fld_nth by lia.
replace (seg_spec.mseg_addr c gi + seg_spec.MS_MODEL + Z.of_nat j) with (c + Z.of_nat (256 * gi + (36 + j)))
  by (unfold seg_spec.mseg_addr, seg_spec.MSEG_SIZE, seg_spec.MS_MODEL; lia).
apply Hb. lia.
Qed.

(* the regions of the run: the frame cells read-only (with mf_cells' cells) and g->model_set at atom 37, written *)
Definition mc_slots : YP09.region := YP09.mkRegion (Some 2%nat) 16 216 0 0 (mf_chunk120 :: mf_cell_chunks).
Definition mc_g : YP09.region := YP09.mkRegion (Some 37%nat) 32 36 32 36 [].
(* the state's form, computed *)
Ltac mc_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a field of the restricted memory is the same field through the world's view (m_file_strip.v's text) *)
Lemma mc_sa_val : forall (W : world SEGS) mem a n v,
  val_mem SEGS (mrestrict (w_H W) mem) a n v -> sa_val (rdW W mem) a n v.
Proof.
intros W mem a n v H k Hk. unfold aview. rewrite (H k Hk). cbn [option_map]. f_equal.
pose proof (Z.mod_pos_bound (Z.shiftr (v mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k)) 256 ltac:(lia)) as HR.
rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [reflexivity|].
change (bv_modulus 8) with 256. exact HR.
Qed.

Section e.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUNTO := paj_run_to B LAWS.

Lemma mk_cret_ok : forall n, MK_LI_stmt B n -> MK_CRET_stmt B n.
Proof.
intros n LI. unfold MK_CRET_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest low KB Hlow Hnul Hrange FIN R20.
destruct KB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & NP & R27).
set (mcc1 := m_upd mcc gi (mkt_set_model low)) in *.
set (mcc' := m_upd mcc gi (ms_with_model low)) in *.
pose proof CORE as (HJ & HPerm & VFL & VSH & VSV & V120 & HMC & HMA & HMT).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hc64 & _ & _ & _ & _ & HMP & _).
pose proof HMP as (Hc0 & Hc16 & _).
pose proof LOOP as (_ & _ & _ & _ & _ & LCUR & _).
pose proof HMA as (_ & _ & _ & HRAc & _).
destruct (mf_blk_c B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc1 CX CORE) as (bc & mbc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS _ _ _ _ _ bc mbc HAR Hbc) as (_ & Hb4096 & Hbceil & _ & Hbpres & _ & Hbm).
pose proof (req_size_pos mbc ltac:(lia)) as [_ Hreq].
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CRlo & CRhi) & _). unfold YG0f.ASAN_CEIL in CRlo, CRhi.
destruct (mf_sp0 B v CX) as (Sp1 & Sp2 & Sp3).
destruct (mf_s1_facts B v CX) as (Ss1 & Ss2 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Sp1.
assert (Hs1r : alloc_ceiling + 8000 <= mf_s1 (mv_sp v) <= 2 ^ 47) by (destruct Ss1 as [E1 | E1]; rewrite E1; lia).
(* the model's sizes: entry gi exists before and after, and in the final model *)
pose proof HMC as (bs0 & _ & (_ & HL32 & _)).
assert (Hgi1 : (gi < length (mc_seg mcc1))%nat) by exact LCUR.
assert (Hlen1 : length (mc_seg mcc1) = length (mc_seg mcc)) by (unfold mcc1; apply mkt_m_upd_segs_len).
assert (Hlen' : length (mc_seg mcc') = length (mc_seg mcc)) by (unfold mcc'; apply mkt_m_upd_segs_len).
assert (Hgi32 : (gi < 32)%nat) by lia.
assert (Hfin : (gi < length (mc_seg (mf_final v)))%nat).
{ pose proof (mkt_mf_fin_segs_mono (mcc', Some gi) line rest) as G. rewrite FIN in G. cbn [fst] in G. lia. }
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc1 (Some gi) CX CORE LCUR) as Hcur.
(* the seed at MK_CRET *)
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc1 (Some gi) 0 [] MK_CRET true false []
  false false [] false CX CORE RB (fun _ => CELLS) Hcur ltac:(intros Hf; discriminate Hf) ltac:(lia)
  ltac:(unfold MF_LOW_ON; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
pose proof (mfE_U32 regs1 v lyc pos (Some gi) 0 []) as U32.
remember (mfE regs1 v lyc pos (Some gi) 0 []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos (Some gi) 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 1%nat ltac:(unfold A_TEXT; lia)) as E33.
pose proof (EX 2%nat ltac:(unfold A_TEXT; lia)) as E34. pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
pose proof (EX 5%nat ltac:(unfold A_TEXT; lia)) as E37.
cbn [Nat.add nth mf_extra map app] in E32, E33, E34, E36, E37.
unfold mf_cur_ptr in E37.
set (c := mv_c v) in *.
set (g := seg_spec.mseg_addr c gi) in *.
set (s1 := mf_s1 (mv_sp v)) in *.
set (F := frame_addr lyc 1 pos) in *.
assert (Hg : g = c + 256 * Z.of_nat gi) by (unfold g, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
unfold seg_spec.SEG_M_SIZE in *.
assert (U37 : bv_unsigned (ew E 37) = g) by (rewrite E37; apply unsigned_lit_small; lia).
assert (B37 : base_val E (Some 37%nat) = g) by (cbn [base_val]; exact U37).
assert (B2 : base_val E (Some 2%nat) = s1)
  by (cbn [base_val]; rewrite (EE 2%nat 2%bv eq_refl), R2; apply mf_w64_u; lia).
(* the frame cells only, read-only *)
assert (HS1 : st_ok_pi SEGS VAL E (mkSS MK_CRET sr_mf [mc_slots] None mf_facts)
  (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + MK_CRET)) memc (seg_rom SEGS)))).
{ refine (st_ok_pi_submem E _ _ [mc_slots] HS0 _ ltac:(vm_compute; reflexivity)).
  cbn [ss_mem ss_mf]. unfold mf_regions. apply submem_drop. apply submem_keep; [|apply submem_nil].
  unfold subregion, mc_slots, mf_r_slots. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [left; lia|]. intros ch Hch.
  rewrite !app_nil_r. exact Hch. }
clear HS0.
(* s4 = g as atom 37 *)
apply (ast_ok_pi_set_reg_fp E _ _ (20%bv : bv 5) (SOff 37 0)) in HS1;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E37; cbn [ms_regs restrict mkst];
     rewrite R20; reflexivity].
mc_norm HS1.
(* atom 37's fact *)
assert (F37 : afact_ok E 37 (HPTR 0)).
{ unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2]. rewrite U37.
  rewrite Z.pow_0_r, Z.mod_1_r. split; [lia|]. split; [reflexivity|]. lia. }
pose proof (st_ok_pi_add_fact E _ _ 37 _ HS1 F37) as HS2. clear HS1. mc_norm HS2.
(* g->model_set: [g + 32, g + 36) writable *)
assert (GOK : region_ok SEGS E (mrestrict (w_H Wc) memc) mc_g).
{ unfold region_ok, mc_g. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks]. rewrite B37.
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hbpres (g + o) ltac:(lia))). }
assert (DISJ : all_disjoint E mc_g [mc_slots]).
{ apply all_disjoint_of_extents. unfold mc_g, mc_slots, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite B37, B2.
  cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia. }
pose proof (st_ok_pi_add_region E _ _ mc_g HS2 eq_refl GOK DISJ) as HS. clear HS2. mc_norm HS.
(* the shadow entry of the check 0x868b0: g->model_set's 4 bytes, in the mconf block *)
assert (SHOK : sh_ok SEGS (SOff 32 0) [mkSHE 37 32 36] E (mrestrict (w_H Wc) memc)).
{ unfold sh_ok. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E (SOff 32 0) 37 c 9236 g 32 36 HRAc U32
    (U_atom E 37 g E37 ltac:(lia))); [lia | lia |].
  intros x Hx. rewrite Z.min_l, Z.max_r in Hx by lia. apply (mf_blk_app B v CX). fold c.
  unfold seg_spec.SEG_M_SIZE. lia. }
unfold mf_at.
(* 0x868a4 .. 0x868c4: the check (fast path), g->model_set = 1, s9 = 112(s1), `j` to MK_LI *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan MK_LI.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end.
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 37%nat g); [reflexivity | exact U37 | |].
  - intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    + apply (mkt_mk_fp_seg c (mv_k0 v) (mf_final v) gi a Hfin). fold g. unfold seg_spec.MSEG_SIZE. lia.
    + exists bc, mbc. split; [exact Hbc | lia].
  - apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
(* the bytes: every byte but g->model_set's 4 keeps its view *)
set (RW := fun a : Z => g + 32 <= a < g + 36).
assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) RW HFr _ a Ha HnW);
    intros bb wlo whi y Hinw Hy; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hy; first [lia | rewrite U37 in Hy; unfold RW; lia] |]);
    destruct Hinw end. }
(* g->model_set = 1 at the end of the run *)
assert (VRS : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (g + 32) 4 1).
{ lazymatch goal with HSx : st_ok_pi _ _ ?Ex ?ssx (restrict _ ms) |- _ =>
    assert (HAE : env_agree 64 E Ex) by env_agree_chain (env_agree_refl 64 E);
    assert (UG : bv_unsigned (ew Ex 37) = g) by (rewrite (proj1 HAE 37%nat ltac:(lia)); exact U37);
    pose proof (st_ok_pi_region_nth Ex ssx (restrict (w_H Wc) ms) 0 _ HSx eq_refl) as HR0 end.
  cbn [restrict ms_mem] in HR0.
  pose proof (field_of_region _ _ 37 g _ _ _ _ _ 32 4%N (SLit 1) 1 HR0 UG
    ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl
    ltac:(assert (H32 : 2 ^ (8 * Z.of_N 4) = 4294967296) by reflexivity; rewrite H32; lia) ltac:(cbn; lia)) as V.
  change (N.to_nat 4) with 4%nat in V. exact V. }
(* the block: entry gi's model field before the store, then g->model_set = 1 *)
assert (HZ : sa_zs (rdW Wc memc) (g + seg_spec.MS_MODEL) (low ++ [0])).
{ pose proof (mc_model_zs (rdW Wc memc) c mcc1 gi HMC Hgi1) as Z0.
  unfold mcc1, m_upd, m_set_segs in Z0. cbn [mc_seg] in Z0.
  rewrite mkt_nth_upd in Z0 by lia. rewrite Nat.eqb_refl in Z0. cbn [mkt_set_model ms_model] in Z0. exact Z0. }
assert (HZ' : sa_zs (rdW Wc (ms_mem ms)) (g + seg_spec.MS_MODEL) (low ++ [0])).
{ intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. unfold seg_spec.MS_MODEL in *.
  rewrite K; [apply HZ; rewrite length_app; cbn [length]; lia | lia | unfold RW; lia]. }
assert (MC2 : sa_mconf (rdW Wc (ms_mem ms)) c mcc').
{ pose proof (mkt_sa_mconf_with_model (rdW Wc memc) (rdW Wc (ms_mem ms)) c mcc1 gi low HMC Hgi1 Hlow Hnul Hrange)
    as MW.
  unfold mcc1 in MW. rewrite mkt_upd_upd_model in MW. apply MW.
  - intros a Ha H1 H2. unfold seg_spec.SEG_M_SIZE, seg_spec.MS_MODEL_SET in *. fold g in H1.
    apply K; [lia | unfold RW; lia].
  - fold g. exact HZ'.
  - fold g. unfold seg_spec.MS_MODEL_SET. exact (mc_sa_val Wc (ms_mem ms) (g + 32) 4 1 VRS). }
(* the cut facts at the new memory *)
assert (RWok : forall a, RW a -> mf_rw v lyc pos a)
  by (intros a Ha; unfold RW in Ha; unfold mf_rw, seg_spec.SEG_M_SIZE; right; left; fold c; lia).
assert (RWS : mf_rws v RW) by (intros a Ha Hs; exfalso; unfold RW in Ha; fold s1 in Hs; lia).
assert (FD : 0 <= F / 8 <= 2 ^ 44 - 2 ^ 20)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + F / 8 + i) 1 MF_LOW_ON).
{ intros i Hi. apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia | | exact (VSH i Hi)].
  intros kk Hkk HR. change (Z.of_nat 1) with 1 in Hkk. unfold RW in HR.
  apply (mf_blk_app B v CX (SHADOW_OFF + F / 8 + i + kk)); [fold c; unfold seg_spec.SEG_M_SIZE; lia | lia]. }
assert (V136' : val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (s1 + 136) 8 (mf_cur_ptr c (Some gi))).
{ apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 8 _ K);
    [lia | change (Z.of_nat 8) with 8; lia | | exact V136].
  intros kk Hkk HR. unfold RW in HR. lia. }
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc1 (Some gi) (ms_mem ms) mdw RW MF_LOW_ON (Some gi)
  mcc' CX CORE CELLS HJ K RWok RWS VSH' V136' MC2) as (CORE' & CELLS' & LOOPf).
assert (NP' : mf_np v (ms_mem ms) Wc (mf_next p rest)).
{ unfold mf_np, mf_slot in NP |- *. apply (mf_val_keep Wc Wc memc (ms_mem ms) RW _ 8 _ K);
    [lia | change (Z.of_nat 8) with 8; lia | | exact NP].
  intros kk Hkk HR. unfold RW in HR. fold s1. lia. }
(* the next line: m_upd keeps the counters *)
assert (LOOPn : mf_loop v Wc (ms_mem ms) mcc' (Some gi) (line + 1) (mf_next p rest) (mf_rest rest)).
{ apply (mf_loop_next v Wc (ms_mem ms) mcc1 (Some gi) line p rest mcc' (Some gi) (LOOPf _ _ _ _ _ LOOP) Hne).
  - unfold mcc', mcc1, m_upd, m_set_segs. cbn [mc_refused]. lia.
  - unfold mcc', mcc1, m_upd, m_set_segs. cbn [mc_overflow]. lia.
  - unfold mcc', mcc1, m_upd, m_set_segs. cbn [mc_kept]. lia.
  - unfold mf_cur_ok. lia. }
(* the registers at MK_LI *)
prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8.
prreg HS (9%bv : bv 5) Q9. prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (19%bv : bv 5) Q19. prreg HS (22%bv : bv 5) Q22. prreg HS (25%bv : bv 5) Q25.
prreg HS (27%bv : bv 5) Q27.
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
  - rewrite Q25, E33, R25. reflexivity. }
assert (Hn' : (length (mf_rest rest) < n)%nat).
{ destruct (mf_break_snd rest) as (_ & Bk2 & _). pose proof (Bk2 Hne) as Bk. unfold mf_rest. lia. }
pmkst HS.
apply (LI v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc' (Some gi) (line + 1) (mf_next p rest) (mf_rest rest)
  CX LS FRM CORE' CELLS' RA' Hn' LOOPn).
- unfold mf_fin in FIN. exact FIN.
- exact NP'.
- rewrite Q27, (EE 27%nat 27%bv eq_refl). exact R27.
Qed.
End e.
End f.
End d.

About mk_cret_ok.
Print Assumptions mk_cret_ok.
