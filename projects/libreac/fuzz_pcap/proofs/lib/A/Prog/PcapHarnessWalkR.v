(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new walk for libreac/fuzz_pcap (a Theorem Labs lane). The generic helpers pe_land_m32,
   pe_denot_and_m32(_add0), pe_trim_* / pe_submem_to / pe_prreg_raw / pe_add_fact / pe_sregion are cgif_file_fuzzer
   lib/A/ACer.v's (origin/ossv/recipes c8557374ad2e) as a Theorem Labs lane's lib/A/Prog/PcapSourceOpen.v restates them
   (a working branch f0d76b020fe); pe_U_srl, pe_cbyte .. pe_word_at and pe_saved_of are
   a Theorem Labs lane's lib/A/Prog/GrantEntryHead.v (a working branch b83b8251684) restated over PAImg pcap_listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapHarnessPE.v, with its module names changed; 389 of its 443 lines of code are new or changed and 1253 lines of the source are left out. *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap v1.9.0, ASan build: the pinned
   fuzz_pcap.asan image (sha256 b7a91d9b1fb0017d...; symbols from its
   unstripped twin, capstone 5 disassembly). Ported from lib/A/Prog/PcapHarnessWalk.v's pe_KL2_at (its Sections, its
   cut shape at_cut and its walk), with that file's write-window pattern (hfacts_KD, the atom-9 fact) for the one
   store of this segment; PcapHarnessWalk.v's helpers (hw_sp, hw_geom, the windowed transport hw_body_on /
   hw_pslots_on / hw_pslot_on / hw_pglob_on / hw_pspad_on / hw_preader_on, hw_recbytes_len) are Required, not re-proved. *)
(* The record loop of fuzz_pcap's entry function LLVMFuzzerTestOneInput (0x807c8) on the ASan build of libreac
   v1.9.0, from the loop's head PP_K4 (0x80b34) to the head of the harness's skip loop PP_KR (0x80b70), and the loop:

     pe_K4    : at_cut GI_KR POST n -> at_cut GI_K4 POST n         the straight segment PP_K4 -> PP_KR
     pe_WalkR : pe_from POST GI_K5 -> pe_from POST GI_K4           induction on the loop measure hw_meas

   pe_WalkR takes the skip loop's body (PP_KL2 -> PP_KR, another lane's file) as the Section hypothesis KR, and the
   loop's exit PP_KL2 -> PP_K4 / PP_K5 from PcapHarnessWalk.v's pe_KL2_at. The cuts are lib/A/Prog/PcapEntryPhases.v's.

   The segment, listing offsets 0x3fc .. 0x438 (15 instructions; s1 = c_sp1, the realigned frame pointer, reg 9):
     0x80b34 ld a1,0x40(s1)      the spill slot PS_GLEN: the auipc value 8               (region hwR_K4s, atom 33)
     0x80b38 ld a1,0x618(a1)     g_file_len = |F|; HGLEN: auipc value 8 + 0x618 = object 4 (region hwR_K4g, atom 34)
     0x80b3c addi a3,a1,-0x18    0x80b40 srli a3,a3,4
     0x80b44 bgeu s9,a3          -> PP_abort 0x81340
     0x80b48 mv a3,a2            0x80b4c ld t1,0x58(s1)   the spill slot PS_PSP: &ps        (region hwR_K4s, atom 35)
     0x80b50 beqz s9,+8          -> 0x80b58               0x80b54 mv a3,a0
     0x80b58 bltu s5,a2          -> PP_abort
     0x80b5c sd a3,0x48(s1)      `first` into the spill slot PS_FIRST: the write window [s1 + 72, s1 + 80)
     0x80b60 addi a4,s2,0x10     0x80b64 bltu a1,a4       -> PP_abort
     0x80b68 lw s8,8(t1)         ps.swapped                                              (region hwR_K4p, atom 36)
     0x80b6c addi s9,s9,1        -> 0x80b70 = PP_KR.
   The three branches to PP_abort are refuted at the branch from GI_K4's facts (the comments at each name the lemma
   and the premise); none is budgeted.

   Beyond PcapHarnessWalk.v's Section hypotheses (LAWS, ASIL, HGX) the segment needs one fact no cut carries, stated
   with the text the sibling harness lanes use and discharged by PcapEntryTop.v at the instance:
     HGLEN  pa_val (A_HI 8) + 1560 = pa_val (A_OBJ 4)   (0x80b38 reads g_file_len through the auipc value 8;
            PcapEntryTop.pi_pcap_glen; PcapHarnessTail.v and PcapHarnessA.v state the same hypothesis).
   ASIL (asource_img_laws SK SEGS B KS) is what keeps GI_KR's stream predicate across the store 0x80b5c: the stdio
   environment cells lie in the image only by asil_env. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0s YI16 YG0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YE00 YG0p YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase YC4b YC81 YC1g YC1h YC85 PcapFrame PcapEntry PcapEntryA PcapEntryDefs PcapEntryPhases PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournalFs PaGxSites.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalk.
(* PcapHarnessWalk.v's walk: at_cut, hw_meas, the cut helpers and the loop exit pe_KL2_at. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapHarnessWalk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the branches and values of the segment, as the walk reads them ---- *)

Lemma hw_branch_ltu : forall a b : word, branch_taken BC_LTU a b = (bv_unsigned a <? bv_unsigned b).
Proof. intros a b. reflexivity. Qed.

Lemma hw_branch_geu : forall a b : word, branch_taken BC_GEU a b = negb (bv_unsigned a <? bv_unsigned b).
Proof. intros a b. reflexivity. Qed.

Lemma hw_branch_eq : forall a b : word, branch_taken BC_EQ a b = (bv_unsigned a =? bv_unsigned b).
Proof. intros a b. reflexivity. Qed.

Lemma hw_den_off : forall (E : env) (n : nat) (v z : Z), ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n z)) = v + z.
Proof.
  intros E n v z Hv Hr Hr'. cbn [sv_denot]. rewrite Hv. unfold w64.
  rewrite (unsigned_lit_small v Hr). apply unsigned_lit_small. exact Hr'.
Qed.

Lemma hw_den_srl4 : forall (E : env) (a : sv),
  bv_unsigned (sv_denot E (SAlu ALU_SRL a (SLit 4))) = bv_unsigned (sv_denot E a) / 16.
Proof.
  intros E a. cbn [sv_denot alu64 alu]. rewrite bv_shiftr_unsigned, land63_lit.
  change (Z.land (zcanon 4) 63) with 4. rewrite Z.shiftr_div_pow2 by lia. reflexivity.
Qed.

(* lw of ps.swapped (0 or 1) sign-extends to itself. *)
Lemma hw_sext_01 : forall z, z = 0 \/ z = 1 -> sext 64 (bv_extract 0 32 (w64 z)) = w64 z.
Proof. intros z [-> | ->]; vm_compute; reflexivity. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* SK is explicit, as in PcapHarnessWalk.v: the closure of sink_head is the plain build's, so it is never inferred. *)
Context (SK : OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable.YI16.sink_head).
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Notation VAL := (@pa_val _ pcap_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Notation BASE := (@pa_val _ pcap_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
(* PcapHarnessWalk.v's cut shape at these B MT KS and this sink head, so that the statements read as in its Section. *)
#[local] Notation at_cut := (@PcapHarnessWalk.at_cut _ SK PI B MT KS).

Hypothesis LAWS : AR_laws SEGS B.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_pcap) (PI := PI).

(* gx_ok for the harness's two globals, as PcapHarnessWalk.v takes it; the run chain of W_journal.v needs it. *)
Hypothesis HGX : gx_ok SEGS B pe_G.
Let RUN := paj_run_x B LAWS pe_G HGX 0 [].
Let RUNTO := paj_run_to_x B LAWS pe_G HGX 0 [].

(* g_file_len is the auipc value 8 + 0x618 (0x80b38); PcapEntryTop.pi_pcap_glen at the instance. *)
Hypothesis HGLEN : pa_val (A_HI 8) + PE_GLEN_LO = pa_val (A_OBJ 4).
(* The stream's image laws (PSourceMeta.v): its stdio environment cells are image bytes (asil_env). *)
Hypothesis ASIL : asource_img_laws SK SEGS B KS.

(* ---- the symbolic state at PP_K4 ---- *)
(* Three regions, as the segment's loads and its one store need them:
   - the machine frame [s1 + 64, s1 + 96): PS_GLEN (+64, atom 33) and PS_PSP (+88, atom 35) read, PS_FIRST
     (+72) written: the write window [s1 + 72, s1 + 80);
   - g_file_len at atom 33 + 0x618 (= object 4 by HGLEN), read only, its value |F| as atom 34;
   - ps.swapped at atom 35 + 8, read only (lw), its value as atom 36.
   The fact on atom 9 (hfacts_KD) puts the window outside the shadow band. *)
Definition hwR_K4s : YP09.region := YP09.mkRegion (Some 9%nat) 64 96 72 80
  [YP09.mkChunk 64 (CVal 8 (SOff 33 0)); YP09.mkChunk 88 (CVal 8 (SOff 35 0))].
Definition hwR_K4g : YP09.region := YP09.mkRegion (Some 33%nat) PE_GLEN_LO PE_GLEN_LO8 0 0
  [YP09.mkChunk PE_GLEN_LO (CVal 8 (SOff 34 0))].
Definition hwR_K4p : YP09.region := YP09.mkRegion (Some 35%nat) 8 12 0 0
  [YP09.mkChunk 8 (CVal 4 (SOff 36 0))].
Definition hss_K4 : sstate := mkSS PP_K4 sr_atoms [hwR_K4s; hwR_K4g; hwR_K4p] None hfacts_KD.

Lemma hw_entry0_K4 : forall (W3 : world SEGS) (regs : bvmap 5 word) (mem : word -> option byte)
    (sp1 hi ln ps sw : Z),
  getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall o, 72 <= o < 80 -> apresent (w_H W3) mem (sp1 + o)) ->
  rdword (aview SEGS (w_H W3) mem) (sp1 + 64) = Some hi ->
  rdword (aview SEGS (w_H W3) mem) (sp1 + 88) = Some ps ->
  val_mem SEGS (mrestrict (w_H W3) mem) (hi + PE_GLEN_LO) 8 ln ->
  val_mem SEGS (mrestrict (w_H W3) mem) (ps + 8) 4 sw ->
  0 <= hi -> hi + PE_GLEN_LO8 <= sp1 + 64 -> 0 <= ln < 2 ^ 64 -> 0 <= ps -> ps + 12 <= sp1 + 64 -> 0 <= sw < 2 ^ 32 ->
  hi + PE_GLEN_LO8 <= ps + 8 \/ ps + 12 <= hi + PE_GLEN_LO ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs [w64 HW_SB; w64 hi; w64 ln; w64 ps; w64 sw])) hss_K4
    (restrict (w_H W3) (mkst regs (Z_to_bv 64 (BASE + PP_K4)) mem (seg_rom SEGS))).
Proof.
  intros W3 regs mem sp1 hi ln ps sw H9 Hsp1 Hsp1m Hpres Hhi Hps Hln Hsw Hhi0 Hhi1 Hln0 Hps0 Hps1 Hsw0 Hd.
  set (E := Eimg (Ereg regs [w64 HW_SB; w64 hi; w64 ln; w64 ps; w64 sw])).
  assert (EX : forall j, (j < 5)%nat ->
    ew E (32 + j) = nth j [w64 HW_SB; w64 hi; w64 ln; w64 ps; w64 sw] (Z_to_bv 64 0)).
  { intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
  assert (E9 : ew E 9%nat = w64 sp1).
  { subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl). exact H9. }
  assert (U9 : bv_unsigned (ew E 9%nat) = sp1) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
  assert (U33 : bv_unsigned (ew E 33%nat) = hi).
  { change (ew E 33%nat) with (ew E (32 + 1)). rewrite (EX 1%nat ltac:(lia)). cbn [nth].
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U34 : bv_unsigned (ew E 34%nat) = ln).
  { change (ew E 34%nat) with (ew E (32 + 2)). rewrite (EX 2%nat ltac:(lia)). cbn [nth].
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U35 : bv_unsigned (ew E 35%nat) = ps).
  { change (ew E 35%nat) with (ew E (32 + 3)). rewrite (EX 3%nat ltac:(lia)). cbn [nth].
    unfold w64. apply unsigned_lit_small. lia. }
  assert (U36 : bv_unsigned (ew E 36%nat) = sw).
  { change (ew E 36%nat) with (ew E (32 + 4)). rewrite (EX 4%nat ltac:(lia)). cbn [nth].
    unfold w64. apply unsigned_lit_small. lia. }
  assert (D : forall (j : nat) v, bv_unsigned (ew E j) = v -> sv_denot E (SOff j 0) = Z_to_bv 64 v).
  { intros j v Hj. cbn [sv_denot]. rewrite Hj, Z.add_0_r. reflexivity. }
  rewrite restrict_mkst_fx. unfold hss_K4.
  apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]];
      unfold hwR_K4s, hwR_K4g, hwR_K4p, region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia. }
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val SEGS E _ sp1 64 8 (SOff 33 0) hi (D 33%nat hi U33) ltac:(cbn; lia) ltac:(cbn; lia)).
        exact (val_mem_of_rdword SEGS (w_H W3) mem _ _ Hhi).
      * apply (chunk_ok_val SEGS E _ sp1 88 8 (SOff 35 0) ps (D 35%nat ps U35) ltac:(cbn; lia) ltac:(cbn; lia)).
        exact (val_mem_of_rdword SEGS (w_H W3) mem _ _ Hps).
    + rewrite U33. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      exact (chunk_ok_val SEGS E _ hi PE_GLEN_LO 8 (SOff 34 0) ln (D 34%nat ln U34) ltac:(cbn; lia) ltac:(cbn; lia) Hln).
    + rewrite U35. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      exact (chunk_ok_val SEGS E _ ps 8 4 (SOff 36 0) sw (D 36%nat sw U36) ltac:(cbn; lia) ltac:(cbn; lia) Hsw).
  - cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [hwR_K4s hwR_K4g hwR_K4p YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U33, U35.
    split; [split; [lia | split; [lia | exact I]]|]. split; [split; [lia | exact I]|]. split; exact I.
  - unfold hfacts_KD, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [|split; exact I]. split; [|exact I]. unfold afact_ok.
    cbn [af_lo af_hi af_al2]. rewrite U9. split; [lia|]. split; [exact Hsp1m | lia].
Qed.

Lemma hw_entryK4 : forall (W3 : world SEGS) (ms3 : machine_state) (sp1 hi ln ps sw : Z),
  ms_pc_val ms3 = w64 (BASE + PP_K4) -> ms_resv ms3 = None -> ms_svc_pending ms3 = None ->
  ms_rom ms3 = seg_rom SEGS -> ms_fregs ms3 = fp_regs -> ms_fcsr ms3 = fp_csr ->
  getr (ms_regs ms3) 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  (forall o, 72 <= o < 80 -> apresent (w_H W3) (ms_mem ms3) (sp1 + o)) ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + 64) = Some hi ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) (sp1 + 88) = Some ps ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (hi + PE_GLEN_LO) 8 ln ->
  val_mem SEGS (mrestrict (w_H W3) (ms_mem ms3)) (ps + 8) 4 sw ->
  0 <= hi -> hi + PE_GLEN_LO8 <= sp1 + 64 -> 0 <= ln < 2 ^ 64 -> 0 <= ps -> ps + 12 <= sp1 + 64 -> 0 <= sw < 2 ^ 32 ->
  hi + PE_GLEN_LO8 <= ps + 8 \/ ps + 12 <= hi + PE_GLEN_LO ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms3) [w64 HW_SB; w64 hi; w64 ln; w64 ps; w64 sw])) hss_K4
    (restrict (w_H W3) ms3).
Proof.
  intros W3 ms3 sp1 hi ln ps sw Hpc Hrv Hsv Hrom Hfr Hcsr. intros.
  destruct ms3 as [rg fg pcv svc resv fcsr mm rom].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *. subst.
  apply (hw_entry0_K4 W3 rg mm sp1); assumption.
Qed.

(* ---- the run's footprint: the one window [s1 + 72, s1 + 80), whatever the chunks ---- *)

(* The write obligation: the window is in the call's machine stack. *)
Lemma hw_awr_K4 : forall (E : env) (c0 c1 c2 : list YP09.chunk) (STK sp0 : Z) FP bl0 blc ly own G OUT,
  sp0 - STK <= bv_unsigned (ew E 9) + 72 -> bv_unsigned (ew E 9) + 80 <= sp0 ->
  awr_ok_x E [YP09.mkRegion (Some 9%nat) 64 96 72 80 c0; YP09.mkRegion (Some 33%nat) PE_GLEN_LO PE_GLEN_LO8 0 0 c1;
              YP09.mkRegion (Some 35%nat) 8 12 0 0 c2] G 0 OUT STK sp0 FP bl0 blc ly own.
Proof.
  intros E c0 c1 c2 STK sp0 FP bl0 blc ly own G OUT H1 H2. apply awr_ok_x_of0.
  apply (awr_ok_cons_stack_off E _ _ STK sp0 FP bl0 blc ly own 9%nat (bv_unsigned (ew E 9) - sp0));
    [reflexivity | lia | cbn; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil.
Qed.

(* What a run keeps: every byte outside the window. *)
Lemma hw_kept_K4 : forall (E : env) (c0 c1 c2 : list YP09.chunk) (H : word -> bool) (m m' : word -> option byte),
  frame_of E [YP09.mkRegion (Some 9%nat) 64 96 72 80 c0; YP09.mkRegion (Some 33%nat) PE_GLEN_LO PE_GLEN_LO8 0 0 c1;
              YP09.mkRegion (Some 35%nat) 8 12 0 0 c2] (mrestrict H m) (mrestrict H m') ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (bv_unsigned (ew E 9) + 72 <= a < bv_unsigned (ew E 9) + 80) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E c0 c1 c2 H m m' HF.
  apply (kept_of_frame (segs := SEGS) E _ H m m'
    (fun a => bv_unsigned (ew E 9) + 72 <= a < bv_unsigned (ew E 9) + 80) HF).
  intros bW wloW whiW aW HinW HrrW. cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi In] in HinW.
  destruct HinW as [HqW | [HqW | [HqW | []]]]; injection HqW as <- <- <-; cbn [base_val] in HrrW; lia.
Qed.

Lemma hw_eqon_step : forall W (m0 m1 m2 : word -> option byte) (P : Z -> Prop),
  hw_eqon W m0 m1 P -> (forall a, P a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m1 a) -> hw_eqon W m0 m2 P.
Proof. intros W m0 m1 m2 P H1 H2 a Ha. rewrite (H2 a Ha). exact (H1 a Ha). Qed.

(* ---- the walk's tactics ---- *)

(* The write obligation of a run from a state over the three regions. *)
Ltac hwk4_awr U9 :=
  lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end;
  apply hw_awr_K4; rewrite U9; unfold LLVMF_STK; lia.

(* After a run: fold its frame into HK, the bytes kept since PP_K4. *)
Ltac hwk4_keep U9 HK :=
  lazymatch goal with HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    let UNr := fresh "UNr" in let HK' := fresh "HKn" in
    pose proof (hw_kept_K4 _ _ _ _ _ _ _ HFr) as UNr; rewrite U9 in UNr;
    pose proof (hw_eqon_step _ _ _ _ _ HK (fun a Ha => UNr a (proj1 Ha) (proj2 Ha))) as HK';
    clear HK UNr; rename HK' into HK
  end;
  lazymatch goal with HF : frame_of _ _ _ _, HFr : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ =>
    clear HF HFr end.

(* ---- PP_K4 (0x80b34) -> PP_KR (0x80b70) ---- *)
Lemma pe_K4 : forall POST n, at_cut (GI_KR B MT KS) POST n -> at_cut (GI_K4 B MT KS) POST n.
Proof.
intros POST n HKR cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG Hmeas.
destruct HG as (b & h & buf & i & p & HCUT & Hpad & H26 & Hgood & Hi0 & Hip & Hfit & Hfst
  & R12 & R18 & R19 & R21 & R22 & R23 & R25 & Hls & Hglob & Hrd).
pose proof HCUT as (HBODY & Hk3 & Hacc & HPerm & Hfds & Hfs).
pose proof HBODY as (Hpc & Hrv & Hsv & Hrom & Hfreg & Hfcsr & Hregs & Hsaved & Hhdr & Hshd & Hshlen & Hinp).
pose proof Hregs as (G2 & G8 & G9 & G27 & G3 & G4).
(* the geometry: the machine stack lies above the allocator's ceiling, everything else below it *)
pose proof (hw_sp SK B MT KS cx fp k ly3 S3 W3 ms3 md3 HB HJ) as (Hal16 & Hceil & H47 & Hs1 & Hs1m & Hpres).
pose proof (hw_geom SK B LAWS cx fp k ly3 S3 W3 ms3 md3 HJ Hfrs) as (HF4096 & HFceil & HSH4096 & HSHceil).
pose proof (ASAN_CEIL_range (rc := rc)) as ((HC1 & HC1') & HC2). unfold ASAN_CEIL in HC1, HC1', HC2.
unfold LLVMF_STK in Hceil, Hpres. unfold PE_FRAME in HFceil.
pose proof (p_sizes cx) as (HnF & Hcap & Hbn).
pose proof (pa_obj_img 4 ltac:(lia)) as HO4. pose proof (pa_obj_img 2 ltac:(lia)) as HO2.
pose proof (pa_val_range (A_HI 8)) as Hhir.
unfold pcap_img_end, YImgTop.IMG_TOP in HO4, HO2.
pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (HAR & Hly & _).
assert (Hblk : forall q m, In (q, m) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ->
  4096 <= q /\ q + m <= alloc_ceiling).
{ intros q m Hq.
  assert (Hq3 : In (q, m) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; right; exact Hq).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hq3) as (_ & H4 & Hc & _).
  assert (Hm0 : 0 <= m).
  { cbn [In] in Hq. unfold SRC_FILE_BLOCK in Hq.
    destruct Hq as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; lia. }
  pose proof (req_size_pos m Hm0). lia. }
pose proof (Hblk b (p_nF cx) ltac:(left; reflexivity)) as (Hb4 & Hbc).
pose proof (Hblk h SRC_FILE_BLOCK ltac:(right; left; reflexivity)) as (Hh4 & Hhc).
pose proof (Hblk buf (p_bn cx) ltac:(right; right; left; reflexivity)) as (Hu4 & Huc).
assert (Hinb : forall a, c_p cx <= a < c_p cx + c_n cx -> 0 <= a < alloc_ceiling).
{ intros a Ha. pose proof HB as (_ & _ & _ & _ & Hinp0 & _).
  destruct Hinp0 as [(Hn0 & _) | (Hn & Hin0)]; [lia|].
  assert (Hq3 : In (c_p cx, c_n cx) (ablocks B ly3 S3))
    by (apply (Permutation_in _ (Permutation_sym HPerm)); apply in_or_app; left; exact Hin0).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hq3) as (_ & H4 & Hc & _).
  pose proof (req_size_pos (c_n cx) ltac:(lia)). lia. }
(* g_file_len's bytes are image bytes (HGX), the frame's are not (frm_img): the two read regions are apart *)
assert (Hdisj : pa_val (A_OBJ 4) + 8 <= pPS cx fp + 8 \/ pPS cx fp + 12 <= pa_val (A_OBJ 4)).
{ destruct (Z_le_gt_dec (pa_val (A_OBJ 4) + 8) (pPS cx fp + 8)) as [Hd|Hd]; [left; exact Hd|].
  destruct (Z_le_gt_dec (pPS cx fp + 12) (pa_val (A_OBJ 4))) as [Hd'|Hd']; [right; exact Hd'|].
  exfalso. set (a := Z.max (pa_val (A_OBJ 4)) (pPS cx fp + 8)).
  assert (Hin : In (PE_CID, fp) (frames S3)) by (rewrite Hfrs; left; reflexivity).
  assert (Efa : frame_addr ly3 PE_CID fp = frame_addr (c_ly cx) PE_CID fp).
  { unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
  apply (frm_img SEGS B LAWS ly3 S3 W3 _ md3 PE_CID fp a HAR Hin).
  - rewrite Efa. change (fs_frame_bytes PE_CID) with 128. unfold pPS, pF, PO_PS in *. unfold a. lia.
  - apply (proj1 (HGX a ltac:(unfold pe_G, inG; apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; unfold a; lia))). }
(* the model: the fit record psn_q p, found from p, answered n = p_res .. *)
pose proof (PW.psn_q_ge (p_sw cx) (p_F cx) (p_cap cx) p) as Hqp.
change (PSN.psn_q (p_sw cx) (p_F cx) (p_cap cx) p) with (p_q cx p) in Hqp.
pose proof (PW.kind_fit (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p) Hfit) as (Hres & Hrl & _ & Hend & Hincl).
change (PSN.flen (p_F cx)) with (p_nF cx) in Hend.
change (PSN.res_of (p_sw cx) (p_F cx) (p_cap cx) (p_q cx p)) with (p_res cx (p_q cx p)) in Hres.
rewrite <- Hres in Hrl.
assert (Hp24 : 24 <= p) by lia.
assert (Hp17 : p + 17 <= p_nF cx) by lia.
assert (Hsw01 : p_swz cx = 0 \/ p_swz cx = 1)
  by (unfold p_swz, PST.pcap_sw; destruct (_ =? _); [right | left]; reflexivity).
(* the symbolic state at PP_K4 *)
pose proof Hls as ((S1 & S2 & _) & _). unfold pslot, PS_PSP, PS_GLEN in S1, S2.
pose proof Hrd as (_ & (_ & Hswv) & _). unfold pval in Hswv.
pose proof (hw_entryK4 W3 ms3 (c_sp1 cx) (pa_val (A_HI 8)) (p_nF cx) (pPS cx fp) (p_swz cx)
  Hpc Hrv Hsv Hrom Hfreg Hfcsr G9 ltac:(lia) Hs1m ltac:(intros o Ho; apply Hpres; lia) S2 S1
  ltac:(rewrite HGLEN; exact (proj2 Hglob)) Hswv
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold pPS, PO_PS; lia) ltac:(unfold pPS, PO_PS; lia) ltac:(lia)
  ltac:(lia)) as HS.
set (E := Eimg (Ereg (ms_regs ms3) [w64 HW_SB; w64 (pa_val (A_HI 8)); w64 (p_nF cx); w64 (pPS cx fp); w64 (p_swz cx)]))
  in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EEo : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr (ms_regs ms3) r).
{ intros i0 r Hi. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5.
  change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hi. }
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) =
  nth j [w64 HW_SB; w64 (pa_val (A_HI 8)); w64 (p_nF cx); w64 (pPS cx fp); w64 (p_swz cx)] (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (U9 : bv_unsigned (ew E 9) = c_sp1 cx)
  by (rewrite (EEo 9%nat 9%bv eq_refl), G9; unfold w64; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = w64 (p_nF cx)) by exact (EX 2%nat ltac:(lia)).
assert (E35 : ew E 35 = w64 (pPS cx fp)) by exact (EX 3%nat ltac:(lia)).
assert (E36 : ew E 36 = w64 (p_swz cx)) by exact (EX 4%nat ltac:(lia)).
assert (EEr : forall (i0 : nat) (r : bv 5) v, Z.of_nat i0 = bv_unsigned r -> getr (ms_regs ms3) r = w64 v ->
  ew E i0 = w64 v) by (intros i0 r v Hi Hv; rewrite (EEo i0 r Hi); exact Hv).
pose proof (hw_sh_nil E (mrestrict (w_H W3) (ms_mem ms3))) as SHOK.
set (P := fun a => 0 <= a < 2 ^ 64 /\ ~ (c_sp1 cx + 72 <= a < c_sp1 cx + 80)).
assert (HK : hw_eqon W3 (ms_mem ms3) (ms_mem ms3) P) by (intros a _; reflexivity).
(* run 1: 0x80b34 .. 0x80b40, to the branch 0x80b44 *)
paj_run_tok RUN HS HJ SHOK HWspan; [hwk4_awr U9|].
hwk4_keep U9 HK. clear HG HEI0.
psrr_branch_tok RUN BR HS SHOK HWspan.
{ (* 0x80b44: refuted by PW.kind_fit, from 24 + 17 i <= p and the fit record psn_q p (p + 17 <= |F|), so
     i < (|F| - 24) / 16 (bgeu s9,a3 not taken) *)
  exfalso. rewrite hw_branch_geu in Hc. apply negb_true_iff, Z.ltb_ge in Hc.
  rewrite hw_den_srl4 in Hc.
  rewrite (hw_den_off E 25 i 0 (EEr 25%nat 25%bv i eq_refl R25) ltac:(lia) ltac:(lia)),
          (hw_den_off E 34 (p_nF cx) (-24) E34 ltac:(lia) ltac:(lia)) in Hc.
  assert (i + 1 <= (p_nF cx + -24) / 16) by (apply Z.div_le_lower_bound; lia).
  lia. }
(* run 2: 0x80b48, 0x80b4c, to the branch 0x80b50 *)
clear Hc.
paj_run_tok RUN HS HJ SHOK HWspan; [hwk4_awr U9|].
hwk4_keep U9 HK. clear HG HEI0.
psrr_branch_tok RUN BR HS SHOK HWspan.
(* 0x80b50 beqz s9: both arms are walked; each stores `first` at 0x80b5c *)
all: [> (* taken: i = 0, so p = 24 and a3 = a2 = the first answer *)
        rewrite hw_branch_eq in Hc; apply Z.eqb_eq in Hc;
        rewrite (hw_den_off E 25 i 0 (EEr 25%nat 25%bv i eq_refl R25) ltac:(lia) ltac:(lia)) in Hc;
        change (bv_unsigned (sv_denot E (SLit 0))) with 0 in Hc;
        destruct Hfst as [(_ & Hp) | (Hi & _)]; [|lia];
        assert (HA3 : bv_unsigned (sv_denot E (SOff 12 0)) = p_first cx mod 2 ^ 64)
          by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEo 12%nat 12%bv eq_refl), R12, Hp;
              unfold w64, p_first; rewrite Z_to_bv_unsigned; reflexivity);
        clear Hc
      | (* not taken: 0 < i, so a3 = a0 = the first answer *)
        rewrite hw_branch_eq in Hc; apply Z.eqb_neq in Hc;
        rewrite (hw_den_off E 25 i 0 (EEr 25%nat 25%bv i eq_refl R25) ltac:(lia) ltac:(lia)) in Hc;
        change (bv_unsigned (sv_denot E (SLit 0))) with 0 in Hc;
        destruct Hfst as [(Hi & _) | (_ & R10)]; [lia|];
        assert (HA3 : bv_unsigned (sv_denot E (SOff 10 0)) = p_first cx mod 2 ^ 64)
          by (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EEo 10%nat 10%bv eq_refl), R10;
              unfold w64; rewrite Z_to_bv_unsigned; reflexivity);
        clear Hc ].
(* run 3: (0x80b54,) to the branch 0x80b58 *)
all: paj_run_tok RUN HS HJ SHOK HWspan; [hwk4_awr U9|].
all: hwk4_keep U9 HK; clear HG HEI0.
all: psrr_branch_tok RUN BR HS SHOK HWspan;
  [ (* 0x80b58: refuted by PW.kind_fit, from the fit record psn_q p: n = rec_len <= cap (bltu s5,a2 not taken) *)
    exfalso; rewrite hw_branch_ltu in Hc; apply Z.ltb_lt in Hc;
    rewrite (hw_den_off E 21 (p_cap cx) 0 (EEr 21%nat 21%bv _ eq_refl R21) ltac:(lia) ltac:(lia)),
            (hw_den_off E 12 (p_res cx (p_q cx p)) 0 (EEr 12%nat 12%bv _ eq_refl R12) ltac:(lia) ltac:(lia)) in Hc;
    lia
  | ].
(* run 4: the store 0x80b5c, 0x80b60, to the branch 0x80b64 *)
all: clear Hc.
all: paj_run_tok RUN HS HJ SHOK HWspan; [hwk4_awr U9|].
all: hwk4_keep U9 HK; clear HG HEI0.
all: psrr_branch_tok RUN BR HS SHOK HWspan;
  [ (* 0x80b64: refuted by PW.kind_fit and PW.psn_q_ge, from the fit record psn_q p >= p: p + 16 <= |F|
       (bltu a1,a4 not taken) *)
    exfalso; rewrite hw_branch_ltu in Hc; apply Z.ltb_lt in Hc;
    rewrite (hw_den_off E 34 (p_nF cx) 0 E34 ltac:(lia) ltac:(lia)),
            (hw_den_off E 18 p 16 (EEr 18%nat 18%bv _ eq_refl R18) ltac:(lia) ltac:(lia)) in Hc;
    lia
  | ].
(* run 5: 0x80b68, 0x80b6c, to PP_KR *)
all: clear Hc.
all: paj_run_to_tok RUNTO HS HJ SHOK HWspan PP_KR; [hwk4_awr U9|].
all: hwk4_keep U9 HK; clear HG HEI0.
all: lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ =>
  pose proof (st_ok_pi_restrict_mkst (w_H W3) _ _ msx HS eq_refl) as Hshape;
  cbn [ss_pc] in Hshape;
  prreg HS (2%bv : bv 5) Q2; prreg HS (3%bv : bv 5) Q3; prreg HS (4%bv : bv 5) Q4;
  prreg HS (6%bv : bv 5) Q6; prreg HS (8%bv : bv 5) Q8; prreg HS (9%bv : bv 5) Q9;
  prreg HS (11%bv : bv 5) Q11; prreg HS (12%bv : bv 5) Q12; prreg HS (14%bv : bv 5) Q14;
  prreg HS (18%bv : bv 5) Q18; prreg HS (19%bv : bv 5) Q19; prreg HS (21%bv : bv 5) Q21;
  prreg HS (22%bv : bv 5) Q22; prreg HS (23%bv : bv 5) Q23; prreg HS (24%bv : bv 5) Q24;
  prreg HS (25%bv : bv 5) Q25; prreg HS (27%bv : bv 5) Q27;
  pose proof (st_ok_pi_region_nth E _ (restrict (w_H W3) msx) 0 _ HS eq_refl) as HR0;
  apply (HKR cx fp k acc ly3 S3 W3 msx mdx HB HJ Hfrs Hmo) end.
(* the measure: s2 = p is unchanged *)
all: lazymatch goal with
  | |- (hw_meas _ _ <= _)%nat =>
      unfold hw_meas, hw_pos in Hmeas |- *; rewrite Q18, (EEo 18%nat 18%bv eq_refl), R18;
      rewrite R18 in Hmeas; exact Hmeas
  | |- _ => idtac end.
(* GI_KR at e = p: every byte the cut reads lies outside the window, except PS_FIRST, the window itself *)
all: assert (PL : forall a, 0 <= a < alloc_ceiling -> P a) by (intros a Ha; unfold P; lia).
all: unfold GI_KR; exists b, h, buf, i, p, p.
all: destruct (hw_fields_of_shape _ _ _ _ Hshape) as (HQpc & HQrv & HQsv & HQrom & HQfr & HQcs).
all: lazymatch goal with |- p_cut _ _ _ _ _ _ _ _ _ _ _ _ _ ?msx _ /\ _ =>
  assert (HQregs : pregs cx msx)
    by (unfold pregs; rewrite Q2, Q8, Q9, Q27, Q3, Q4, (EEo 2%nat 2%bv eq_refl), (EEo 8%nat 8%bv eq_refl),
          (EEo 9%nat 9%bv eq_refl), (EEo 27%nat 27%bv eq_refl), (EEo 3%nat 3%bv eq_refl), (EEo 4%nat 4%bv eq_refl);
        exact Hregs);
  (* the body from PP_K4 to PP_KR across the window (PcapHarnessWalk.v's hw_body_on) *)
  pose proof (hw_body_on cx fp PP_K4 PP_KR W3 ms3 msx PSH_ts P HK HQpc HQrv HQsv HQrom HQfr HQcs HQregs
    ltac:(intros j Hj; apply PL; lia) ltac:(intros j Hj; apply PL; lia)
    ltac:(intros j Hj; unfold P; lia)
    ltac:(intros j Hj; apply PL; apply Hinb; unfold c_n; lia) HBODY) as HBk end.
all: split; [split; [exact HBk|]|].
all: lazymatch goal with
  | |- _ <= 3 /\ _ =>
      split; [exact Hk3|]; split; [exact Hacc|]; split; [exact HPerm|];
      split; [ etransitivity; [apply (proj1 (hw_md_fds _ _)) | exact Hfds]
             | etransitivity; [apply (proj2 (hw_md_fds _ _)) | exact Hfs] ]
  | |- _ => idtac end.
all: split; [apply (hw_pspad_on cx fp W3 ms3 _ P HK); [intros j Hj; apply PL; unfold pPS, PO_PS; lia | exact Hpad]|].
all: split; [exact H26|]. all: split; [exact Hgood|]. all: split; [exact Hi0|]. all: split; [exact Hip|].
all: split; [exact Hfit|]. all: split; [lia|].
all: split; [exact (PW.psn_q_skips (p_sw cx) (p_F cx) (p_cap cx) p ltac:(lia))|].
all: split; [lia|].
(* the registers: t1 = &ps (atom 35), a1 = |F| (atom 34), a4 = e + 16, s8 = ps.swapped (atom 36), s9 = i + 1 *)
all: split; [rewrite Q6, E35; reflexivity|].
all: split; [rewrite Q11, E34; reflexivity|].
all: split; [rewrite Q12; exact (EEr 12%nat 12%bv _ eq_refl R12)|].
all: split; [rewrite Q14, (EEr 18%nat 18%bv _ eq_refl R18); unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
all: split; [rewrite Q18; exact (EEr 18%nat 18%bv _ eq_refl R18)|].
all: split; [rewrite Q19; exact (EEr 19%nat 19%bv _ eq_refl R19)|].
all: split; [rewrite Q21; exact (EEr 21%nat 21%bv _ eq_refl R21)|].
all: split; [rewrite Q22; exact (EEr 22%nat 22%bv _ eq_refl R22)|].
all: split; [rewrite Q23; exact (EEr 23%nat 23%bv _ eq_refl R23)|].
all: split; [rewrite Q24, E36; exact (hw_sext_01 _ Hsw01)|].
all: split; [rewrite Q25, (EEr 25%nat 25%bv _ eq_refl R25); unfold w64; rewrite unsigned_lit_small by lia; reflexivity|].
(* the slots: all but PS_FIRST lie outside the window (PcapHarnessWalk.v's hw_pslots_on / hw_pslot_on) *)
all: split; [ destruct Hls as (Hps7 & SV & SB & SU); split;
  [ apply (hw_pslots_on cx fp W3 ms3 _ P HK); [|exact Hps7];
    intros off Hoff j Hj; unfold PS_PSP, PS_GLEN, PS_D, PS_SH, PS_F, PS_FK, PS_TSP in Hoff; unfold P; lia
  | split; [|split];
    [ apply (hw_pslot_on cx W3 ms3 _ P _ _ HK); [intros j Hj; unfold PS_VMASK, P; lia | exact SV]
    | apply (hw_pslot_on cx W3 ms3 _ P _ _ HK); [intros j Hj; unfold PS_BUF12, P; lia | exact SB]
    | apply (hw_pslot_on cx W3 ms3 _ P _ _ HK); [intros j Hj; unfold PS_USEC, P; lia | exact SU] ] ] |].
(* PS_FIRST: the store 0x80b5c left `first` there (the region's chunk at +72) *)
all: lazymatch goal with |- pslot _ _ ?msx _ _ /\ _ =>
  split; [ cbn [ms_mem restrict] in HR0;
    pose proof (field_of_region_any E _ 9 (c_sp1 cx) _ 64 96 72 80 72 8 _ HR0 U9 ltac:(left; reflexivity)
      ltac:(lia)) as V72;
    rewrite HA3 in V72; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in V72; rewrite Z.mod_mod in V72 by lia;
    unfold pslot, PS_FIRST; apply (rdword_of_val_mem SEGS (w_H W3) (ms_mem msx));
    [exact V72 | apply Z.mod_pos_bound; lia] |] end.
all: split; [apply (hw_pglob_on cx W3 ms3 _ b P HK); [intros j Hj; apply PL; lia | intros j Hj; apply PL; lia | exact Hglob]|].
(* the reader: the FILE block, the copy, the stream's environment (image bytes, ASIL), ps, ts and buf *)
all: apply (hw_preader_on KS cx fp W3 ms3 _ b h buf p P HK); [ | | | | exact Hrd].
all: [> intros a [Ha | [Ha | Ha]]; apply PL;
        [ unfold SRC_FILE_BLOCK in *; lia
        | unfold p_C in Ha; rewrite length_map in Ha; change (Z.of_nat (length (p_F cx))) with (p_nF cx) in Ha; lia
        | destruct (asil_env SK SEGS B KS ASIL a Ha) as (Hai & _ & _); pose proof (pa_img_range a Hai);
          unfold pcap_img_end, YImgTop.IMG_TOP in *; lia ]
     | intros j Hj; apply PL; unfold pPS, PO_PS; lia
     | intros j Hj; apply PL; unfold pTS, PO_TS; lia
     | intros _ j Hj; rewrite (hw_recbytes_len cx (p_q cx p) ltac:(lia) Hfit) in Hj; apply PL; unfold p_bn in *; lia
     | intros a [Ha | [Ha | Ha]]; apply PL;
        [ unfold SRC_FILE_BLOCK in *; lia
        | unfold p_C in Ha; rewrite length_map in Ha; change (Z.of_nat (length (p_F cx))) with (p_nF cx) in Ha; lia
        | destruct (asil_env SK SEGS B KS ASIL a Ha) as (Hai & _ & _); pose proof (pa_img_range a Hai);
          unfold pcap_img_end, YImgTop.IMG_TOP in *; lia ]
     | intros j Hj; apply PL; unfold pPS, PO_PS; lia
     | intros j Hj; apply PL; unfold pTS, PO_TS; lia
     | intros _ j Hj; rewrite (hw_recbytes_len cx (p_q cx p) ltac:(lia) Hfit) in Hj; apply PL; unfold p_bn in *; lia ].
Qed.

(* ---- the record loop: PP_K4 back to PP_K4 through PP_KL2 and the skip loop PP_KR ---- *)

(* The skip loop's body, PP_KL2 -> PP_KR (another lane's file). *)
Hypothesis KR : forall POST n, at_cut (GI_KL2 B MT KS) POST n -> at_cut (GI_KR B MT KS) POST (S n).

(* At measure 0 there is no PP_KR state: GI_KR gives e + 16 <= |F| and s2 = e (e < 2^64: |F| <= c_n < 2^26),
   so hw_meas = |F| - e >= 16. *)
Lemma hw_KR_0 : forall POST, at_cut (GI_KR B MT KS) POST 0.
Proof.
  intros POST cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG Hmeas. exfalso.
  destruct HG as (b & h & buf & i & p & e & HCUT & Hpad & H26 & Hgood & Hi0 & Hip & Hfit & Hpe & Hsk & He16
    & R6 & R11 & R12 & R14 & R18 & _).
  pose proof (p_sizes cx) as (HnF & _ & _).
  unfold hw_meas, hw_pos in Hmeas. rewrite R18 in Hmeas. unfold w64 in Hmeas.
  rewrite unsigned_lit_small in Hmeas by lia. lia.
Qed.

(* By induction on the measure n: at_cut GI_K4 n -> (pe_KL2_at, with the loop's exit GI_K5) at_cut GI_KL2 n ->
   (KR) at_cut GI_KR (S n) -> (pe_K4) at_cut GI_K4 (S n); at 0 from hw_KR_0 and pe_K4. *)
Lemma pe_WalkR : forall POST, pe_from SK B MT KS POST (GI_K5 B MT KS) -> pe_from SK B MT KS POST (GI_K4 B MT KS).
Proof.
  intros POST HK5.
  assert (IH : forall n, at_cut (GI_K4 B MT KS) POST n).
  { induction n as [|n IHn].
    - exact (pe_K4 POST 0 (hw_KR_0 POST)).
    - refine (pe_K4 POST (S n) (KR POST n _)).
      (* PcapHarnessWalk.v's loop exit; its Section hypotheses are this file's (LAWS, ASIL, HGX) *)
      eapply (pe_KL2_at SK B MT KS); eassumption. }
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG.
  exact (IH (hw_meas cx ms3) cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfrs Hmo HG (le_n _)).
Qed.

End c.
End b.
End a.
