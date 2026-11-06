(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147;
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AChd.v:180-183, 357-361,
   for libreac/fuzz_identity's ASan build (lib/A). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/reac_box_catalogue.v, with its module paths and numbers changed; 204 of its 254 lines of code are new or changed and 319 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/check_ignore.v, with its module paths and module names changed; 339 of its 373 lines of code are new or changed and 220 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A, 0x85ebc): the segments S_MF_TAIL (13 instructions from the cut TAIL
   0x86cf8) and S_MF_KDONE (10 instructions from the cut KDONE 0x86cd0) of its walk (the G2 walk owner's
   guide/MF-CUTS-A.md sections 2 and 4). The TAIL / EXIT segment lane of the G2 walk owner's G2. Neither segment calls anything.

   S_MF_TAIL (`mf_tail_at`, `s_mf_tail`): 0x86cf8-0x86d04 the instrumented check of *p, p = a7 (a load of the
   shadow byte at (p >> 3) + s2 and a compare; the error path 0x86d18-0x86d20, 0x86fd4-0x86fd8, a call of
   errpath_load1, is not reached: the token run turns the check into the obligation `p is addressable', which
   mf_loop's sa_addr gives); 0x86d08 `lbu a0,0(a7)`; 0x86d0c s11 = a7; 0x86d10 `bnez a0` back to HEAD 0x860d0;
   0x86d14 `j` EXIT 0x86e70. *p is the first byte of the text left (mf_loop_hd): 0 exactly when the text left is
   empty, and then the block holds the final model (the line list of [] is [], mf_lines_nil). The run writes no
   byte: every region of its state is read-only, so the cut facts hold at the new memory (mf_carry_eq).
   S_MF_KDONE (`mf_kdone_at`, `s_mf_kdone`): 0x86cd0 a7 = 144(s1) = the next line's address; 0x86cd4-0x86cf4 low.i's
   8 shadow bytes (shadow(FB) + 4 .. + 11) = 0xf8 (the bytes are marked unusable again); then TAIL. The run writes
   only the frame's shadow (mf_tx_core / mf_tx_cells / mf_tx_loop of lib/A/Prog/m_file_k.v carry the rest).

   The seed is lib/A/Prog/m_file_sd.v's mf_seed (the m_file cut-statement lane); the spill slots' region is made read-only here
   (ast_ok_pi_set_region, as fuzz_command's check_reply_s7.v cr7_seed does with its frame header).
   Closed against G2 FINAL at 6f783602b5e3 (the image-A owner's contracts, round 5). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* every region of the state is read-only: a run from it writes nothing (check_reply_s7.v cr7_awr) *)
Ltac mf_awr_ro :=
lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
  let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the state's form, computed *)
Ltac mf_norm HS := lazymatch type of HS with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS end.

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
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.

(* S_MF_TAIL at one FP state *)
Lemma mf_tail_at : forall n, MF_HEAD_stmt B n -> MF_EXIT_stmt B -> MF_TAIL_stmt B n.
Proof.
intros n HEAD EXIT. unfold MF_TAIL_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA R24 Hn LOOP MOD R17 R21 R22.
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
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & (PA1 & PA2 & PA3 & PRA & _) & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE Hcurok) as Hcur.
destruct (mf_loop_hd v Wc memc mcc cur line p rest LOOP) as (Hp & Hrest).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
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
  assert (U17 : bv_unsigned (ew E 17) = p) by (rewrite (EE 17%nat 17%bv eq_refl), R17; unfold w64; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
    by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
  assert (UP : U E (SOff 17 0) = p) by (apply (U_atom E 17 p); [rewrite (EE 17%nat 17%bv eq_refl); exact R17 | lia]).
  (* the spill slots read-only *)
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
  lazymatch type of HR1 with region_ok _ _ _ ?r =>
    pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
  clear HS0 HR1. mf_norm HS1.
  (* p, the cursor in a7, is a heap pointer (the fact the token run's obligation needs) *)
  apply (st_ok_pi_add_fact E _ _ 17 (HPTR 0)) in HS1;
    [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U17; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
  mf_norm HS1.
  (* the byte at p *)
  assert (HS2 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 17%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS1
    ltac:(vm_compute; reflexivity)).
  clear HS1.
  lapply HS2; clear HS2; [intros HS2|].
  2:{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U17. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 1 (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. cbn [restrict ms_mem mkst].
      exact (mf_val1_of_aview (w_H Wc) memc p 0 Hp). }
  lapply HS2; clear HS2; [intros HS2|].
  2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U17, ?U2, ?U8, ?U34, ?U36.
      unfold mf_s1, SHADOW_OFF in *. repeat split; first [exact I | lia]. }
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
  unfold mf_at.
  paj_run_to_tok RUNTO HS2 HJ SHOK Bspan MF_EXIT.
  { rewrite UP. eapply (obl_of_range SEGS _ _ E (SOff 32 0) p 1 p _ PRA UB); cbn [length Z.of_nat]; lia. }
  { mf_awr_ro. }
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
    [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
      intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_OFF mcc mcc cur line p [] CX CORE HJ K0 LOOP)
    as (CORE' & _ & _ & _).
  rewrite mf_lines_nil in MOD. cbn [fst] in MOD. rewrite MOD in CORE'.
  prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
  prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (25%bv : bv 5) Q25.
  prreg HS2 (26%bv : bv 5) Q26. prreg HS2 (24%bv : bv 5) Q24.
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
  { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
    - rewrite Q2. apply EE. reflexivity.
    - rewrite Q3. apply EE. reflexivity.
    - rewrite Q4. apply EE. reflexivity.
    - rewrite Q8. apply EE. reflexivity.
    - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
    - rewrite Q18, E32, R18. reflexivity.
    - rewrite Q19. apply EE. reflexivity.
    - rewrite Q25. apply EE. reflexivity.
    - rewrite Q26. apply EE. reflexivity. }
  pmkst HS2.
  apply (EXIT v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos CX LS CORE' (mf_regs_ex_of_at B v lyc pos (ms_regs ms) RA')).
  rewrite Q24, (EE 24%nat 24%bv eq_refl). exact R24.
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
  assert (U17 : bv_unsigned (ew E 17) = p) by (rewrite (EE 17%nat 17%bv eq_refl), R17; unfold w64; apply unsigned_lit_small; lia).
  assert (U34 : bv_unsigned (ew E 34) = frame_addr lyc 1 pos) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
    by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U52 : bv_unsigned (ew E 52) = b) by (rewrite E52; apply unsigned_lit_small; lia).
  assert (UB : U E (SOff 32 0) = SHADOW_OFF) by (apply (U_atom E 32 SHADOW_OFF E32); unfold SHADOW_OFF; lia).
  assert (UP : U E (SOff 17 0) = p) by (apply (U_atom E 17 p); [rewrite (EE 17%nat 17%bv eq_refl); exact R17 | lia]).
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
  lazymatch type of HR1 with region_ok _ _ _ ?r =>
    pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
      (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
  clear HS0 HR1. mf_norm HS1.
  (* the byte's atom 52 is in [1, 255] *)
  pose proof (st_ok_pi_add_fact E _ _ 52 (mkAF 1 255 0) HS1) as HS1'.
  lapply HS1'; clear HS1'; [intros HS1'|].
  2:{ unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U52. change (2 ^ 0) with 1. rewrite Z.mod_1_r. lia. }
  clear HS1. mf_norm HS1'.
  apply (st_ok_pi_add_fact E _ _ 17 (HPTR 0)) in HS1';
    [| unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite U17; change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia].
  mf_norm HS1'.
  assert (HS2 := st_ok_pi_add_region E _ _ (YP09.mkRegion (Some 17%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 52 0))])
    HS1' ltac:(vm_compute; reflexivity)).
  clear HS1'.
  lapply HS2; clear HS2; [intros HS2|].
  2:{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U17. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ p 0 1 (SOff 52 0) b);
        [cbn [sv_denot]; rewrite E52, Z.add_0_r, unsigned_lit_small by lia; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. cbn [restrict ms_mem mkst].
      exact (mf_val1_of_aview (w_H Wc) memc p b Hp). }
  lapply HS2; clear HS2; [intros HS2|].
  2:{ cbn [all_disjoint ss_mem]. unfold extent_disjoint.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?U17, ?U2, ?U8, ?U34, ?U36.
      unfold mf_s1, SHADOW_OFF in *. repeat split; first [exact I | lia]. }
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
  unfold mf_at.
  paj_run_to_tok RUNTO HS2 HJ SHOK Bspan MF_HEAD.
  { rewrite UP. eapply (obl_of_range SEGS _ _ E (SOff 32 0) p 1 p _ PRA UB); cbn [length Z.of_nat]; lia. }
  { mf_awr_ro. }
  lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
    assert (K0 : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem msc) a = rdW Wc m0 a);
    [ intros a Ha; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc) (fun _ => False) HFr _ a Ha (fun x => x));
      intros bb' wlo whi x Hinw Hr; vm_compute in Hinw;
      repeat (destruct Hinw as [Hq | Hinw]; [injection Hq as <- <- <-; lia |]); destruct Hinw | ] end.
  set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
  destruct (mf_carry_eq B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_OFF mcc mcc cur line p (b :: rest') CX CORE
    HJ K0 LOOP) as (CORE' & LOOP' & CELLSf & _).
  prreg HS2 (2%bv : bv 5) Q2. prreg HS2 (3%bv : bv 5) Q3. prreg HS2 (4%bv : bv 5) Q4. prreg HS2 (8%bv : bv 5) Q8.
  prreg HS2 (9%bv : bv 5) Q9. prreg HS2 (18%bv : bv 5) Q18. prreg HS2 (19%bv : bv 5) Q19. prreg HS2 (25%bv : bv 5) Q25.
  prreg HS2 (26%bv : bv 5) Q26. prreg HS2 (24%bv : bv 5) Q24. prreg HS2 (27%bv : bv 5) Q27.
  prreg HS2 (21%bv : bv 5) Q21. prreg HS2 (22%bv : bv 5) Q22.
  assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
  { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
    - rewrite Q2. apply EE. reflexivity.
    - rewrite Q3. apply EE. reflexivity.
    - rewrite Q4. apply EE. reflexivity.
    - rewrite Q8. apply EE. reflexivity.
    - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
    - rewrite Q18, E32, R18. reflexivity.
    - rewrite Q19. apply EE. reflexivity.
    - rewrite Q25. apply EE. reflexivity.
    - rewrite Q26. apply EE. reflexivity. }
  pmkst HS2.
  apply (HEAD v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc cur line p (b :: rest') CX LS FRM CORE' (CELLSf cur CELLS)
    RA' ltac:(rewrite Q24, (EE 24%nat 24%bv eq_refl); exact R24) Hn ltac:(discriminate) LOOP' MOD).
  + rewrite Q27, (EE 17%nat 17%bv eq_refl). exact R17.
  + rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
  + rewrite Q22, (EE 22%nat 22%bv eq_refl). exact R22.
Qed.

(* one byte of low.i's shadow after the re-poisoning run: the final frame-shadow region's chunk *)
Ltac kd_byte HR5 U36 :=
lazymatch goal with |- val_mem _ _ (?b + ?i) 1 _ =>
  let V := fresh "V" in
  pose proof (field_of_region_any _ _ 36 b _ 0 16 0 16 i 1%N _ HR5 U36
    ltac:(cbn; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
  lazymatch type of V with val_mem _ _ _ _ ?x => replace x with MF_LOW_OFF in V by (vm_compute; reflexivity) end;
  change (N.to_nat 1) with 1%nat in V; exact V
end.

(* S_MF_KDONE at one FP state *)
Lemma mf_kdone_at : forall n, MF_TAIL_stmt B n -> MF_KDONE_stmt B n.
Proof.
intros n TAIL. unfold MF_KDONE_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA R24 Hn LOOP MOD NP R21 R22.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & F3 & F4 & F5 & F6).
destruct (mf_loop_blk B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc mcc cur line p rest CX CORE LOOP)
  as (bt & mt & Hbt & Hbt1 & Hbt2 & Htp).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & Btceil & _).
destruct (mf_sp0 B v CX) as (S1 & S2 & S3).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity. rewrite HSTK in S1.
pose proof LOOP as (_ & _ & _ & _ & _ & Hcurok & _).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc cur CX CORE Hcurok) as Hcur.
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.mod_pos_bound (mv_sp v - 288) 32 ltac:(lia)) as M32.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
assert (Hp64 : 0 <= p < 2 ^ 64) by lia.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_ON mcc cur p [] MF_KDONE true true [] false false
  [] true CX CORE RB (fun _ => CELLS) Hcur (fun _ => NP) Hp64 ltac:(unfold MF_LOW_ON; lia) (Forall_nil _)
  (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur p []) as E eqn:HE.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur p []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. pose proof (EX 4%nat ltac:(unfold A_TEXT; lia)) as E36.
pose proof (EX 6%nat ltac:(unfold A_TEXT; lia)) as E38.
cbn [Nat.add nth mf_extra map app] in E32, E36, E38.
assert (U36 : bv_unsigned (ew E 36) = SHADOW_OFF + frame_addr lyc 1 pos / 8)
  by (rewrite E36; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
(* the spill slots read-only *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 0 0) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 0 0 HR1 ltac:(intros o Ho; lia))) as HS1 end.
clear HS0 HR1. mf_norm HS1.
(* s10 = shadow(FB) as the frame shadow's atom 36 *)
apply (ast_ok_pi_set_reg_fp E _ _ (26%bv : bv 5) (SOff 36 0)) in HS1;
  [| reflexivity | cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, E36; cbn [ms_regs restrict mkst];
     rewrite R26; reflexivity].
mf_norm HS1.
unfold mf_at.
(* the run 0x86cd0 .. 0x86cf4: a7 = 144(s1); low.i's 8 shadow bytes = 0xf8 *)
paj_run_to_sh RUNTOP HS1 HJ MF_TAIL.
{ lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end.
  do 5 (apply awr_ok_cons_ro; [cbn; lia|]).
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 36%nat (SHADOW_OFF + frame_addr lyc 1 pos / 8));
    [reflexivity | exact U36 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 1, pos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd].
    change (fs_frame_bytes 1 / 8) with 16. lia. }
  apply awr_ok_nil. }
lazymatch goal with HFr : frame_of ?Ex ?rs (mrestrict _ ?m0) (mrestrict _ (ms_mem ?msc)) |- _ =>
  assert (K : forall a, 0 <= a < 2 ^ 64 -> ~ mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos) a ->
    rdW Wc (ms_mem msc) a = rdW Wc m0 a);
  [ intros a Ha HnW; refine (kept_of_frame Ex rs (w_H Wc) m0 (ms_mem msc)
      (mf_win (frame_addr lyc 1 pos) (flag_addr lyc 1 pos)) HFr _ a Ha HnW);
    intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq | Hinw];
      [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U36 in Hr; right; left; lia] |]);
    destruct Hinw | ] end.
set (mdw := with_vm_backing (m_vm_lazy mdc) mat mdc) in *.
assert (G : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a; apply (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG)).
assert (VSH' : forall i, 4 <= i < 12 ->
  val_mem SEGS (mrestrict (w_H Wc) (ms_mem ms)) (SHADOW_OFF + frame_addr lyc 1 pos / 8 + i) 1 MF_LOW_OFF).
{ pose proof (st_ok_pi_region_nth E _ _ 5 _ HS1 eq_refl) as HR5. cbn [restrict ms_mem] in HR5.
  intros i Hi. assert (Hc : i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11) by lia.
  repeat (destruct Hc as [-> | Hc]; [kd_byte HR5 U36 |]). subst i. kd_byte HR5 U36. }
pose proof (mf_tx_core B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_ON MF_LOW_OFF mcc CX CORE HJ K G VSH') as CORE'.
pose proof (mf_tx_cells B v lyc Sc Wc memc mdc (ms_mem ms) pos MF_LOW_ON mcc cur CX CORE K CELLS) as CELLS'.
pose proof (mf_tx_loop B v lyc Sc Wc memc mdc (ms_mem ms) mdw pos MF_LOW_ON mcc mcc cur line p rest CX CORE (proj1 HJ)
  K G LOOP) as LOOP'.
prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (25%bv : bv 5) Q25.
prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (24%bv : bv 5) Q24. prreg HS1 (17%bv : bv 5) Q17.
prreg HS1 (21%bv : bv 5) Q21. prreg HS1 (22%bv : bv 5) Q22.
assert (RA' : mf_regs_at B v lyc pos (ms_regs ms)).
{ apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms) RA).
  - rewrite Q2. apply EE. reflexivity.
  - rewrite Q3. apply EE. reflexivity.
  - rewrite Q4. apply EE. reflexivity.
  - rewrite Q8. apply EE. reflexivity.
  - rewrite Q9, (EE 2%nat 2%bv eq_refl), R2, R9. reflexivity.
  - rewrite Q18, E32, R18. reflexivity.
  - rewrite Q19. apply EE. reflexivity.
  - rewrite Q25. apply EE. reflexivity.
  - rewrite Q26, E36, R26. reflexivity. }
pmkst HS1.
apply (TAIL v lyc Sc Wc (ms_regs ms) (ms_mem ms) mdw pos mcc cur line p rest CX LS FRM CORE' CELLS' RA'
  ltac:(rewrite Q24, (EE 24%nat 24%bv eq_refl); exact R24) Hn LOOP' MOD).
+ rewrite Q17, E38. reflexivity.
+ rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
+ rewrite Q22, (EE 22%nat 22%bv eq_refl). exact R22.
Qed.
End e.
End f.
End d.

(* the segments at every FP state (m_file_m.v's S_MF_<X> shapes) *)
Section g. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section h.
Context {PI : PAImg seg_listing}.
Section i.
Variable B : asyms.
Hypothesis VOBJS : seg_val_objs.
Lemma s_mf_tail : S_MF_TAIL B.
Proof. intros n HEAD EXIT fx0. exact (mf_tail_at (fx := fx0) B VOBJS n (HEAD fx0) (EXIT fx0)). Qed.
Lemma s_mf_kdone : S_MF_KDONE B.
Proof. intros n TAIL fx0. exact (mf_kdone_at (fx := fx0) B VOBJS n (TAIL fx0)). Qed.
(* inside the Sections: the segments' hypotheses as their assumptions *)
About s_mf_tail. Print Assumptions s_mf_tail.
About s_mf_kdone. Print Assumptions s_mf_kdone.
End i.
End h.
End g.
About s_mf_tail. Print Assumptions s_mf_tail.
About s_mf_kdone. Print Assumptions s_mf_kdone.
