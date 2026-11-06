(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: lib/B's walk of pcap_source_open in the asan-ubsan instance of fuzz_pcap
   (libreac v1.9.0; pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22a...; function at 0x811e0 =
   BASE + AF_pcap_source_open, AF = 0xa58), proving lib/A's image-generic contract tpcap_source_open_specX
   (lib/A/Prog/PcapSourceOpenDefs.v) at SEGS = pa_segs, rlo / rhi = pa_relro_lo / pa_relro_hi,
   apath / alen / afile = VAL (A_OBJ 3) / VAL (A_OBJ 4) / VAL (A_OBJ 2) (0x20d00 "<fuzz-input>", g_file_len
   0x5d3e40, g_file 0x5d3e60), with FM_RA and roimg as parameters. At ossv/recipes 25e3d17bdb50 (2026-10-29), there was no released proof of this function at
   this image (rule 24 lookup, a Theorem Labs lane, 22:35Z): the v1.8 ubsan proof (lib/U/Prog/pcap_source_open.v at
   origin/ossv/recipes c8557374ad2e) serves only as the template for the UBSan guards.

   The code. Up to the fopen call it is lib/A's ASan code byte for byte at
   other pcs (asan 0x8145c.. = asan-ubsan 0x811e0..): the prologue saves ra, s0 .. s9 (0x811e0..0x81210) and
   realigns s1 = sp = (sp - 96) & -32 (0x81218); the use-after-return flag is read through the GOT (0x81228
   auipc / 0x8122c ld, listing object 0 = 0x99750) from the runtime cell at 0x81234 (object 16 = 0xa17c0): the
   walk takes it as 1 (the kit's AR_const_law through al_const, with uar_cell_regionP (A_OBJ 16) holding SLit 1;
   the pin's file holds 0 and the runtime sets 1 at init), so 0x81240 `beqz a2` is not taken;
   __asan_stack_malloc_1(0x60) at 0x81248 returns the class-1 frame F (aj_stack_malloc_atS, YC85.v:292), whose
   two caller premises are discharged at op_to_call's frame request: count_cid 1 (frames Sc) < fs_frames 1 from
   op_pre's length (frames Sc) <= 7 through count_cid_le_length and 8 <= fs_frames 1, and the apath premise by
   op_SMP (stack_malloc_progressP from lib/Reusable/YG05.v:70, as cgif_file_fuzzer lib/A/ACed.v:129-130), so
   F >= 4096, 0x8125c `bnez s2` is taken and the machine-frame arm 0x81260..0x81278 is dead; then *(s1) = F
   (0x8127c), the header (0x41b58ab3, objects 10 and 11; 0x812a4..0x812ac), the twelve shadow bytes
   (0x812b8..0x812e4: 0xf1 x4, 0xf8 x3, 0xf3 x5), the mode literal "rb" (object 12, 0x812e8 / 0x812ec; HMODE)
   and the call of libreac_fuzz_fopen (0x812f4) through cl_callS (YC85.v:383) with FOPEN as the callee.

   The cut. This file walks the head: entry -> op_to_call (a Qed checkpoint at the call, op_at_call) ->
   head_to_fopen, which makes the call and establishes PcapSourceOpenPhF.v's op_fopen_ret at the return
   0x812f8. From there PcapSourceOpenPhM.v (op_from_fopen) walks to the two cuts of PcapSourceOpenPh.v and
   PcapSourceOpenB.v (op_from_null / op_from_read) to the return; pb_pcap_source_openX composes the three.
   The three UBSan guards are therefore decided outside this file, at these pcs and against these template lines:
   in PcapSourceOpenPhM.v 0x812f8 `beqz s3` (ps = 0, not taken: ps >= 4096 from op_pre's frame bounds; template
   :114 / :334, premise :93 / :290) and 0x81300 / 0x81304 `andi a0,s3,7; bnez a0` (ps mod 8 <> 0, not taken:
   op_pre's ps mod 8 = 0; template :115 / :335); in PcapSourceOpenB.v 0x81390 / 0x81394 `addi a0,zero,-3;
   bgeu s4,a0` (F + 32 >=u 2^64 - 3, not taken: F + 128 <= alloc_ceiling < 2^47; template :408-412, premise
   :291 and :295-299); all three
   go to the `unimp` at 0x8153c, and every ASan report path 0x81540..0x815b4 is dead because ps's 24 bytes are
   addressable and ps mod 8 = 0. In the head, op_at_call carries what those walks need: ps unwritten and still
   range_addressable, and op_fopen_ret's FILE-block footprint fact for the fclose of the tail.

   The callee hypotheses, used at this image as Section hypotheses: FOPEN : tlibreac_fuzz_fopen_specX
   (lib/A/Prog/PcapFuzzFopenDefs.v), AFREAD : afread_spec (lib/A/Stdio/PFreadISpec.v:138), AFCLOSE :
   afclose_source_spec (lib/A/Stdio/PFclose.v:209), ASM1 : astack_malloc_realizes (lib/Reusable/YG0d.v:285),
   ASF : astack_free_law (lib/Reusable/YG0d.v:301) and FFL : frame_flag_lawP (lib/Reusable/YCbq.v:797), the meter laws MLAW / MLAWF /
   FM, ASIL : asource_img_laws, and the kit's LAWS / TL / TLF / ML. Four instance obligations beyond the kit:
   ROK (roimg reads only image bytes outside the runtime's statics, errno and the open-file list head; applied at
   the fopen call to carry roimg from the entry memory across the prologue and the frame setup), HPATH (the path
   literal's shadow, as a law of every AR state: the frame request's kept clauses do not keep a global's shadow,
   YG0n.v:241 makes it aowned; discharged by the instance through AR_zshadow_law, YG0d.v:435-438), HGX (g_file_len
   and g_file are image bytes outside the runtime's statics and errno; the gx_ok shape of
   lib/A/Prog/PcapEntryDefs.v:366, 395, discharged by the harness), and RO : ro_below_ofl (as
   lib/A/Prog/PcapHarnessTail.v:37). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 695 of its 778 lines of code are new or changed and 1468 lines of the source are left out. *)
(* reac_code_emit (fuzz_link.asan 0x89be4, listing offset AF_reac_code_emit = 0x7a18) on image A: the ENTRY phase of
   its walk, from the contract's entry to the cut EM_f1_ra (+0x120, wrapper_fprintf returned) of
   lib/A/Prog/reac_code_emitDefs.v.

   The code walked (listing (internal path) (internal record, sha256 102ac6881148)):
     +0x00..+0x70  the 128-byte machine frame, the probe `sd zero,0(sp)`, ra and s0..s7 saved, s0 := sp0 - 0x20,
                   `andi sp,sp,-0x20`, s1 := sp, s2 := fmt, s4 := f, the two .got words, the va_list's four slots,
                   `beqz a0` (not taken: the switch cell's region holds 1, AR's const law), frame_alloc_0(0x40)
                   (the token run, LinkWalk.v paj_run_x)
     +0x70         frame_alloc_0 (0x3d914) through LinkWalkSide.v aj_gx_stack_malloc_at
     +0x74..+0x11c s3 := s6 := F, `bnez s3` (taken: 4096 <= F), F into s1 + 0x10, F's header, F's 8 shadow bytes,
                   the three literals (the plain run, LinkWalkSide.v paj_run_call_plain_x, which stops at the call)
     +0x11c        wrapper_fprintf (f, "%s: %s ", "reac-pw", "E_NOT_MARKED") through LinkWalkMkPrintf.v
                   aj_gx_printf_mf_at, returning at some fx' with BoxBase.fxr fx fx'.
   The model of the entry state and of the side-frame steps is the alias-write head lane's
   lib/A/Prog/reac_link_alias_writeHead.v.

   Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG AMemFileSink AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkVfInst LinkPfPiece.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b PcapRelro.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkMkPrintf LinkWalkMkFmt LinkWalkMkFile LinkWalkMkCr.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_decide_c reac_code_emit_c reac_code_emitDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkZsh LinkWalkCall reac_code_emitLit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require printf_facts_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require RT_pf_sh.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require BoxBase.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AB1v AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic entry state ----
   Atoms 0..31: the entry registers; 32: the shadow base (the extra word). Regions: the 128-byte machine frame below
   sp, the shadow base's .got word (A_OBJ 1) and its cell (A_OBJ 64), the side-stack switch's .got word (A_OBJ 0)
   and its cell (A_OBJ 65). *)
Definition EMBx : sv := SOff 32 0.
Definition EMspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition EM_extra : list word := [Z_to_bv 64 SHADOW_OFF].
Definition em_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition em_ss0 : sstate :=
  mkSS AF_reac_code_emit sr_atoms
    [stack_region REAC_CODE_EMIT_AFRAME; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 65);
     uar_cell_regionP (A_OBJ 65)]
    None em_facts0.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis HV : LinkVals.
Hypothesis TL : PALib B.
(* the certificate of link's image: lib/A/AF0m.v PcapSyms, discharged at link's B by AD2l.PcapB_syms *)
Hypothesis TB : AF0m.PcapSyms B.
(* the segments the listing is certified against (lib/A/AB1v.v tfibsegs); the link PAImg instance has it by
   reflexivity *)
Hypothesis HSEGS : pa_segs = AB1v.tfibsegs.
(* the read-only window is image bytes (PcapRelroA.v pcap_relro_in_image at tfibsegs) *)
Hypothesis RELRO_IMG : forall a, PCAP_RLO <= a < PCAP_RHI -> in_img pa_segs a.
(* frame_alloc_0 (0x3d914): lib/A/StackMalloc0.v stack_malloc0_contract B LAWS TB *)
Hypothesis ASM0 : astack_malloc_realizes pa_segs B 0.
(* wrapper_fprintf (0x43084): `forall fx rc, link_afprintf_contract` (lib/A/Rt/LinkVfInst.v)
   at the walk's pa_segs / B (the top rewrites pa_segs = tfibsegs) *)
Hypothesis FPR : forall fx' : YK11.FPState,
  @afprintf_mf_realizes fx' rc pa_segs B link_amf PCAP_RLO PCAP_RHI link_vf_FF LFP_STK LinkMfDefs.LA_GOT_GUARD
    LinkMfDefs.LA_GUARD LA_W_FPRINTF.

Let errno_low := pal_env B TL.

Lemma em_obj_vals :
  pa_val (A_OBJ 0) = 0xa1a28 /\ pa_val (A_OBJ 1) = 0xa19d0 /\ pa_val (A_OBJ 64) = 0xaa438 /\
  pa_val (A_OBJ 65) = 0xaa440 /\ pa_val A_TEXT = 0x821cc.
Proof.
  repeat split; first [rewrite (lv_text HV); reflexivity | rewrite (lv_obj HV) by (vm_compute; lia); reflexivity].
Qed.

(* frame_alloc_0's entry in the certificate's code table is the listing's call target; so is the fprintf wrapper *)
Lemma em_hsm0 : pc_stack_malloc (as_code B) 0 = pa_sigma LS___asan_stack_malloc_0.
Proof. rewrite (AF0m.ts_code B TB), (lv_sigma HV). reflexivity. Qed.
Lemma em_hfpr : pa_sigma LS___interceptor_trampoline_fprintf = LA_W_FPRINTF.
Proof. rewrite (lv_sigma HV). reflexivity. Qed.

(* The entry state, from the journal at the call (as reac_link_alias_writeHead.v aw_entry_st, at this function's
   128-byte frame and window). *)
Lemma em_entry_st : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CODE_EMIT_AK -> spZ regs <= sp0 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs EM_extra)) em_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_code_emit)) memc (seg_rom pa_segs))).
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hwlo Hwhi.
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : REAC_CODE_EMIT_AK = 9360) by reflexivity. rewrite HK in Hwlo.
  destruct (aj_gx_const_cells SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
    mdc k HJ)
    as (Kuar & Kguar & Kcell & Kgot).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
  destruct em_obj_vals as (V0 & V1 & V64 & V65 & _).
  set (E := Eimg (Ereg regs EM_extra)).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs EM_extra) nn)
    by (intros nn Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (EO : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
    by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
  { intros nn v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  pose proof (EO 0%nat ltac:(lia)) as EO0. pose proof (EO 1%nat ltac:(lia)) as EO1.
  pose proof (EO 64%nat ltac:(lia)) as EO64. pose proof (EO 65%nat ltac:(lia)) as EO65.
  rewrite V0 in EO0, Kguar. rewrite V1 in EO1, Kgot. rewrite V64 in EO64, Kgot, Kcell.
  rewrite V65 in EO65, Kguar, Kuar.
  rewrite restrict_mkst_fx. unfold em_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. fold E. rewrite Usp. split; [unfold REAC_CODE_EMIT_AFRAME; lia|]. split; [lia|].
      split; [|constructor].
      intros o Ho. apply (apresent_writable pa_segs). apply Hpres. unfold REAC_CODE_EMIT_AFRAME in Ho. lia.
    + fold E. rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ 0xa19d0 0 8 (SOff (A_OBJ 64) 0) 0xaa438);
        [cbn [sv_denot]; rewrite EO64, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kgot).
    + fold E. rewrite (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ 0xaa438 0 8 (SOff 32 0) SHADOW_OFF);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r; reflexivity | cbn; unfold SHADOW_OFF; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kcell).
    + fold E. rewrite (VB (A_OBJ 0) 0xa1a28 EO0 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ 0xa1a28 0 8 (SOff (A_OBJ 65) 0) 0xaa440);
        [cbn [sv_denot]; rewrite EO65, Z.add_0_r; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kguar).
    + fold E. rewrite (VB (A_OBJ 65) 0xaa440 EO65 ltac:(lia)).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val pa_segs E _ 0xaa440 0 4 (SLit 1) 1); [reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 pa_segs (w_H W) memc _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    fold E. rewrite (VB (A_OBJ 1) 0xa19d0 EO1 ltac:(lia)), (VB (A_OBJ 64) 0xaa438 EO64 ltac:(lia)),
      (VB (A_OBJ 0) 0xa1a28 EO0 ltac:(lia)), (VB (A_OBJ 65) 0xaa440 EO65 ltac:(lia)).
    cbn [base_val]. rewrite Usp.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, REAC_CODE_EMIT_AFRAME. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO. clear. intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [em_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO Hal16.
    clear. unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* Disjointness of a new region from the state's regions, the atoms' values substituted. *)
Ltac em_disj U60 U44 U62 U3_2 :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U60, ?U44, ?U62, ?U3_2;
  try change (fs_frame_bytes 0) with 64; try change (64 / 8) with 8.

(* the three literals' addresses, the atoms the listing's auipc pairs at +0x100..+0x114 load *)
Lemma em_obj_lits : pa_val (A_OBJ 58) = 0x21640 /\ pa_val (A_OBJ 59) = 0x212e0 /\ pa_val (A_OBJ 60) = 0x21660.
Proof. repeat split; rewrite (lv_obj HV) by (vm_compute; lia); reflexivity. Qed.

(* an 8-byte chunk of a region based at an atom, read back as a word of the view (reac_link_alias_writeHead.v
   aw_region_word) *)
Lemma em_region_word : forall Ex H m (r : YP09.region) (b : nat) bv off (n : nat),
  region_ok pa_segs Ex (mrestrict H m) r -> YP09.r_base r = Some b -> bv_unsigned (ew Ex b) = bv ->
  In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks r) ->
  rdword (aview pa_segs H m) (bv + off) = Some (bv_unsigned (ew Ex n)).
Proof.
  intros Ex H m [rb lo hi wlo whi cs] b bv off n HR Hb Hbv Hin. cbn [YP09.r_base YP09.r_chunks] in Hb, Hin. subst rb.
  pose proof (bv_unsigned_in_range 64 (ew Ex n)) as Hr.
  apply (rdword_of_val_mem pa_segs); [| change (bv_modulus 64) with (2 ^ 64) in Hr; exact Hr].
  exact (field_of_region Ex (mrestrict H m) b bv cs lo hi wlo whi off 8%N (SOff n 0) (bv_unsigned (ew Ex n)) HR Hbv Hin
    ltac:(cbn [sv_denot]; rewrite Z.add_0_r; reflexivity)
    ltac:(change (2 ^ (8 * Z.of_N 8)) with (bv_modulus 64); exact Hr) ltac:(cbn; lia)).
Qed.

(* the first line's format and arguments, and its text *)
Definition EM_FMT : list Z := [37; 115; 58; 32; 37; 115; 32].
Definition EM_L1 : list Z := [114; 101; 97; 99; 45; 112; 119].
Definition EM_L2 : list Z := [69; 95; 78; 79; 84; 95; 77; 65; 82; 75; 69; 68].
Definition EM_PS : list printf_facts_c.pf_piece :=
  [printf_facts_c.Ps; printf_facts_c.PLit 58; printf_facts_c.PLit 32; printf_facts_c.Ps; printf_facts_c.PLit 32].
Definition EM_ARGS : list printf_facts_c.pf_arg := [printf_facts_c.APtr EM_L1; printf_facts_c.APtr EM_L2].
Definition EM_T : list Z := EM_L1 ++ [58; 32] ++ EM_L2 ++ [32].
Lemma em_parse : printf_facts_c.pf_parse EM_FMT = Some EM_PS.
Proof. vm_compute. reflexivity. Qed.
Lemma em_text : printf_facts_c.pf_text EM_PS EM_ARGS = Some EM_T.
Proof. vm_compute. reflexivity. Qed.
Lemma em_T_len : Z.of_nat (length EM_T) = EMIT_HEAD.
Proof. reflexivity. Qed.
Lemma em_pieces : Forall apf_link_piece EM_PS.
Proof. repeat constructor. Qed.
Lemma em_fmt_rng : Forall (fun c => 0 < c < 256) EM_FMT.
Proof. repeat constructor; lia. Qed.
Lemma em_l1_rng : Forall (fun c => 0 < c < 256) EM_L1.
Proof. repeat constructor; lia. Qed.
Lemma em_l2_rng : Forall (fun c => 0 < c < 256) EM_L2.
Proof. repeat constructor; lia. Qed.

(* image bytes, by a segment of tfibsegs that holds them *)
Definition em_img_b (lo hi : Z) : bool :=
  existsb (fun s => (Z.of_N (seg_base s) <=? lo) && (hi <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) AB1v.tfibsegs.
Lemma em_img_of_b : forall lo hi a, em_img_b lo hi = true -> lo <= a < hi -> in_img pa_segs a.
Proof.
  intros lo hi a H Ha. rewrite HSEGS. unfold em_img_b in H. apply existsb_exists in H as (s & Hs & Hc).
  apply andb_true_iff in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hs | lia].
Qed.

(* a register of a callee-saved slot, in the literal form the invariants use *)
Lemma em_getr_lit : forall (regs : bvmap 5 word) (r : bv 5), getr regs (Z_to_bv 5 (bv_unsigned r)) = getr regs r.
Proof. intros regs r. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma em_cs : forall z : Z,
  ((z =? 2) || (z =? 3) || (z =? 4) || (z =? 8) || (z =? 9) || ((18 <=? z) && (z <=? 27)))%bool = true ->
  acallee_saved z.
Proof.
  intros z H. unfold acallee_saved.
  rewrite !Bool.orb_true_iff, !Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le in H. lia.
Qed.

Lemma em_sbm_fds : forall m m', same_but_materialized m m' -> m_fds m' = m_fds m /\ m_fs m' = m_fs m.
Proof. intros m m' H. rewrite H. apply wvb_fds_fs. Qed.

Theorem em_entry : (forall fx' : YK11.FPState, em_from SK B fx' (em_f1_inv B)) -> em_start SK B fx.
Proof.
intros NEXT cx Hfrm HBASE.
pose proof HBASE as (HPRE & HRD & Hf0 & Hfp0 & HFIN & HMF & HBLK & HFIT & HFMT & HL1 & HL1r & HL2 & HL2r & HL3 & HL3r).
pose proof HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
destruct cx as [G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fmt ps args T kf].
cbn [e_G e_XO e_OUT e_STK e_sp0 e_FP e_ly e_S e_W0 e_mem0 e_md0 e_own e_lyc e_Sc e_W e_memc e_mdc e_k e_regs
  e_fmt e_ps e_args e_T e_kf] in *.
pose proof HJ as HJ0.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : REAC_CODE_EMIT_AK = 9360) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (aj_gx_unpack SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lia) Hal16 ltac:(rewrite HK in Hwlo; lia) Hwhi)
  as (memS & _ & _ & _ & HSTK & HXO & _ & _ & _ & _ & Hceil & H47).
clear memS.
rewrite HK in Hwlo.
assert (Hspc : alloc_ceiling + 9360 <= spZ regs) by lia.
assert (Hspw : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as HAR.
pose proof (aj_gx_present SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
  as HJpres.
(* the entry state *)
pose proof (em_entry_st G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16
  ltac:(rewrite HK; exact Hwlo) Hwhi) as HS.
remember (Eimg (Ereg regs EM_extra)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E13 : ew E 13 = getr regs 13) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 13 13%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (EREG : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hr; subst E; exact (ew_Eimg_Ereg_nat regs _ n r Hr)).
clear HEdef.
assert (SHOK : sh_ok pa_segs EMBx (@nil shent) E (mrestrict (w_H W) memc)) by (apply Forall_nil).
assert (HCFG : @cfg_at fx pa_segs (BASE + EM_entry) regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_reac_code_emit)) memc (seg_rom pa_segs)) mdc)
  by reflexivity.
rewrite HCFG. clear HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNP := paj_run_call_plain_x SK B LAWS G HGok XO OUT).
(* ---- +0x00 .. +0x70: the prologue, the two .got words, the va_list, the switch test, up to frame_alloc_0 ---- *)
paj_run_tok RUN HS HJ SHOK EMspan.
{ unfold em_ss0. cbn [ss_mem].
  repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP
      bcell_regionP uar_got_regionP uar_cell_regionP] in Hx;
    first [lia | rewrite Usp in Hx; left; split; [left; unfold REAC_CODE_EMIT_AFRAME in Hx; lia | lia]] |]).
  apply awr_ok_x_nil. }
pmkst HS.
sreg HS (2%bv : bv 5) R2. cbn [ms_regs restrict] in R2.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
(* s1 = sp = (sp0 - 128) & -32 (+0x30, +0x34) *)
set (sp1 := 32 * ((spZ regs - 128) / 32)).
destruct (sp1_facts (spZ regs - 128) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al32 & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al32, Hsp1al16.
assert (Hsp1w : 0 <= sp1 < 2 ^ 64) by lia.
assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
assert (Rsp1 : getr (ms_regs ms) 2 = Z_to_bv 64 sp1).
{ rewrite R2. rewrite (denot_and_m32 E 2 (spZ regs) (-128) E2') by lia. unfold sp1.
  replace (spZ regs + -128) with (spZ regs - 128) by lia. reflexivity. }
assert (Usp1 : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Rsp1; apply unsigned_lit_small; exact Hsp1w).
(* the machine frame trimmed to the saves and the va_list [sp0 - 104, sp0); the probe word and the .got words are not
   read again *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (pick (trim_stack rs (-104) 0) [0]%nat) in
  pose proof (st_ok_submem pa_segs Ex ssx msx rs' HS ltac:(cbn [ss_mem setpc]; submem_to) ltac:(vm_compute; reflexivity))
    as HS2; clear HS; rename HS2 into HS end.
cbn [ss_pc ss_regs ss_resv ss_facts setpc] in HS.
(* ---- +0x70: frame_alloc_0(0x40), the class-0 side frame fpos on top of own ---- *)
eapply SRr_bind.
{ eapply (aj_gx_stack_malloc_at SK pa_segs B LAWS pa_segs_low errno_low 0 ASM0 ltac:(lia)
    (pa_sigma LS___asan_stack_malloc_0) G XO OUT W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
    _ k (getr (ms_regs ms) 1) em_hsm0 HJ).
  - rewrite Usp1. exact Hsp1al16.
  - rewrite Usp1, Hes. lia.
  - rewrite Usp1. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact (aside_room_take Sc [(EM_CID, 1)] 0 1 Hside ltac:(left; reflexivity) ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
  & Hbb2 & HfS & HF4096 & HFceil & Hz & Hflag & HKc & Hsbm & Hraw2).
rewrite Usp1, Hes in HKc, Hraw2.
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W mem2 md2 k HJ2)
  as HAR2.
assert (Hfin2 : In (0, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (aj_gx_present SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2
  W mem2 md2 k HJ2) as HJpres2.
jafter_call_keep_pi HS 40%nat regs2 (mrestrict (w_H W) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp; intros a Ha.
  - apply (mbyte_of_aview pa_segs). pose proof HKc as (K1 & _). apply K1; lia.
  - intros _. apply (apresent_writable pa_segs). apply HJpres2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite R1.
remember (havoc E 40 (map (getr regs2) CLOB)) as Ev1 eqn:HE1 in HS.
assert (HEI1 : img_env pa_val A_LIM Ev1) by (rewrite HE1; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLD1 : forall nn, (nn < 40)%nat -> ew Ev1 nn = ew E nn)
  by (intros nn Hnn; rewrite HE1; apply YN3v.ew_havoc_old; exact Hnn).
clear HE1.
(* the frame F (a0 after the call, atom 44), its flag FL and its shadow *)
set (F := frame_addr lyc 0 fpos) in *. set (FL := flag_addr lyc 0 fpos) in *.
prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 F) by (rewrite <- R10, Ha0; reflexivity). clear R10.
destruct (frames_bounds pa_segs B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (_ & _ & HFapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. fold F in HFapp.
pose proof (frame_al64 pa_segs B lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (HFa64 & _ & _). fold F in HFa64.
change (fs_frame_bytes 0) with 64 in HFapp, HFceil, Hz, Hflag.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (_ & _ & HFpres & HFSpres).
fold F in HFpres, HFSpres. change (fs_frame_bytes 0) with 64 in HFpres, HFSpres.
change (64 / 8) with 8 in HFSpres.
destruct (al_flag _ _ LAWS _ _ _ _ _ 0 fpos HAR2 Hfin2) as (HFLpres & _ & HFLapp & HFLceil).
fold FL in HFLpres, HFLapp, HFLceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
pose proof (frm_off_imgP B lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as HFimg.
unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in HFimg. fold F in HFimg. change (fs_frame_bytes 0) with 64 in HFimg.
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8 : (SHADOW_OFF + F / 8) mod 8 = 0).
{ unfold SHADOW_OFF. destruct (div8_of_mul64 F HFa64) as [EF8 _]. rewrite EF8.
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
(* sp and s1: rebind them to the atom 60 = sp1 (+0x30's masked address) *)
assert (E12 : ew Ev1 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD1 by lia; exact E2').
prreg_raw HS (2%bv : bv 5) Rsp2. prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (denot_and_m32 Ev1 2 (spZ regs) (-128) E12) in Rsp2 by lia.
rewrite (denot_and_m32_add0 Ev1 2 (spZ regs) (-128) E12) in Rs12 by lia.
change (32 * ((spZ regs + -128) / 32)) with sp1 in Rsp2, Rs12.
pose proof (st_ok_pi_havoc_hi 60 Ev1 _ _ [Z_to_bv 64 sp1] HS ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc Ev1 60 [Z_to_bv 64 sp1]) as E2v eqn:HE2 in HS.
assert (OLD2 : forall nn, (nn < 60)%nat -> ew E2v nn = ew Ev1 nn)
  by (intros nn Hnn; rewrite HE2; apply YN3v.ew_havoc_old; exact Hnn).
assert (E60 : ew E2v 60 = Z_to_bv 64 sp1)
  by (rewrite HE2; exact (ew_havoc_new Ev1 60 [Z_to_bv 64 sp1] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (HEI2 : img_env pa_val A_LIM E2v) by (rewrite HE2; apply img_env_havoc; [exact HEI1 | cbv; lia]).
clear HE2.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rsp2)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 60 0) HS ltac:(vm_compute; reflexivity)
    ltac:(cbn [sv_denot ms_regs restrict mkst]; rewrite E60, Z.add_0_r, Z_to_bv_bv_unsigned; symmetry; exact Rs12)) as HS3 end.
clear HS; rename HS3 into HS.
(* the flag FL (atom 61) and the shadow SH = SHADOW_OFF + F / 8 (atom 62) *)
pose proof (st_ok_pi_havoc_hi 61 E2v _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] HS
  ltac:(vm_compute; reflexivity)) as HS3.
clear HS. rename HS3 into HS.
remember (havoc E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)]) as E3v eqn:HE3 in HS.
assert (OLD3 : forall nn, (nn < 61)%nat -> ew E3v nn = ew E2v nn)
  by (intros nn Hnn; rewrite HE3; apply YN3v.ew_havoc_old; exact Hnn).
assert (E61 : ew E3v 61 = Z_to_bv 64 FL)
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 0 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (E62 : ew E3v 62 = Z_to_bv 64 (SHADOW_OFF + F / 8))
  by (rewrite HE3; exact (ew_havoc_new E2v 61 [Z_to_bv 64 FL; Z_to_bv 64 (SHADOW_OFF + F / 8)] 1 (Z_to_bv 64 0)
        ltac:(cbn; lia))).
assert (HEI3 : img_env pa_val A_LIM E3v) by (rewrite HE3; apply img_env_havoc; [exact HEI2 | cbv; lia]).
clear HE3.
assert (OLDA : forall nn, (nn < 40)%nat -> ew E3v nn = ew E nn) by (intros nn Hnn; rewrite OLD3, OLD2, OLD1 by lia; reflexivity).
assert (E3_32 : ew E3v 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite OLDA by lia; exact E32).
assert (E3_44 : ew E3v 44 = Z_to_bv 64 F) by (rewrite OLD3, OLD2 by lia; exact E44).
assert (E3_60 : ew E3v 60 = Z_to_bv 64 sp1) by (rewrite OLD3 by lia; exact E60).
assert (U60 : bv_unsigned (ew E3v 60) = sp1) by (rewrite E3_60; apply unsigned_lit_small; lia).
assert (U44 : bv_unsigned (ew E3v 44) = F) by (rewrite E3_44; apply unsigned_lit_small; lia).
assert (U62 : bv_unsigned (ew E3v 62) = SHADOW_OFF + F / 8) by (rewrite E62; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U3_2 : bv_unsigned (ew E3v 2) = spZ regs) by (rewrite OLDA by lia; exact Usp).
add_fact HS 60%nat (mkAF (2 ^ 46) (2 ^ 47) 5)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U60; change (2 ^ 5) with 32;
        repeat split; first [exact Hsp1al32 | lia]).
add_fact HS 44%nat (mkAF 4096 (2 ^ 47) 6)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U44; change (2 ^ 6) with 64;
        repeat split; first [exact HFa64 | lia]).
add_fact HS 61%nat (mkAF 4096 (2 ^ 47) 0)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E61, unsigned_lit_small by lia;
        rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia).
add_fact HS 62%nat (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 3)
  ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U62; change (2 ^ 3) with 8;
        repeat split; first [exact HF8 | unfold SHADOW_OFF; lia]).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS
    (shadow_decl_ok Ev 44 32 62 F SHADOW_OFF E3_44 ltac:(lia) E3_32 E62)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* the three new regions: s1 + 0x10's word (+0xa4 `sd s6,0x10(s1)`), F (its flag pointer at 56), F's 8 shadow bytes
   (frame_alloc_0's zero_shadow, one CZero chunk) *)
assert (ZB : forall i, 0 <= i < 8 ->
  mbyte pa_segs (mrestrict (w_H W) mem2) (SHADOW_OFF + F / 8 + 0 + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. unfold zero_shadow in Hz. pose proof (Hz i ltac:(change (64 / 8) with 8; lia)) as Hzi.
  unfold shadow_of_addr in Hzi. destruct (aview_byte pa_segs _ _ _ _ Hzi) as (bb & Hbb & Hv & _).
  replace (SHADOW_OFF + F / 8 + 0 + i) with (SHADOW_OFF + F / 8 + i) by lia.
  rewrite Hbb. f_equal. apply bv_eq. rewrite <- Hv. reflexivity. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 16 24 16 24 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); apply HJpres2; lia)
  ltac:(em_disj U60 U44 U62 U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 0 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 0) with 64; rewrite U44; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs); apply (proj1 (HFpres (F + o) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val pa_segs _ _ F 56 8 _ FL);
          [cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia
          | replace (F + 56) with (F + 64 - 8) by lia; exact (val_mem_of_rdword pa_segs _ _ _ _ Hflag)] ])
  ltac:(em_disj U60 U44 U62 U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 0 0 8 [YP09.mkChunk 0 (CZero 8)]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 0 / 8) with 8; rewrite U62; split; [unfold SHADOW_OFF; lia|]; split; [unfold SHADOW_OFF; lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs);
          replace (SHADOW_OFF + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; lia);
          apply (proj1 (HFSpres o ltac:(lia)))
        | apply Forall_cons; [apply chunk_ok_zero; exact ZB | apply Forall_nil] ])
  ltac:(em_disj U60 U44 U62 U3_2; unfold SHADOW_OFF; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* ---- +0x74 .. +0x11c: the frame's header and shadow, the three literals, up to wrapper_fprintf (plain engine) ---- *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch type of RUNP with context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
    lazymatch r with (?ssf, PRS_call ?sf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
      eapply (RUNP Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI3 HS Hrun HJ2);
      clear Hrun
    end
  end
end.
{ cbn [ss_mem].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U62 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own)
      lyc S2 W mem2 md2 k 0 fpos a HJ2 (or_introl eq_refl)).
    right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 0 / 8) with 8. fold F. lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U44 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own)
      lyc S2 W mem2 md2 k 0 fpos a HJ2 (or_introl eq_refl)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 0) with 64. fold F. lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U60 in Ha.
    left; split; [left; lia | lia]. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U3_2 in Ha.
    left; split; [left; lia | lia]. }
  apply awr_ok_x_nil. }
cbv beta. intros ms3 mat3 HS5 HJ3 HF3 HFr3 HG3.
cbn [ms_mem mkst] in HF3, HFr3, HG3.
(* what the walk kept so far: the window, frame_alloc_0's acall_kept, the two runs' frames *)
set (Ea := aside_rng lyc 0 fpos).
set (slo := spZ regs - REAC_CODE_EMIT_AK).
assert (Hslo_c : alloc_ceiling <= slo) by (unfold slo; rewrite HK; lia).
assert (K0 : akept pa_segs B lyc Sc W memc W memc slo (spZ regs) Ea).
{ apply (akept_refl SK pa_segs B LAWS pa_segs_low). intros a Ha. apply HJpres. unfold slo in Ha. rewrite HK in Ha. lia. }
pose proof (kept_of_frame (segs := pa_segs) E (ss_mem em_ss0) (w_H W) memc (ms_mem ms)
  (fun a => spZ regs - 128 <= a < spZ regs) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?Usp in HrrW; cbv beta; lia|]); destruct HinW)) as UN1.
assert (K1 : akept pa_segs B lyc Sc W memc W (ms_mem ms) slo (spZ regs) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W memc W (ms_mem ms) slo (spZ regs) Ea Ea
    (fun a => spZ regs - 128 <= a < spZ regs) HAR Hslo_c ltac:(lia) K0 UN1).
  - intros a _ Hp. eapply apresent_grows; [exact HG | exact Hp].
  - intros a H; exact H.
  - intros a Ha. right. unfold slo; rewrite HK. cbv beta in Ha. lia. }
assert (K2 : akept pa_segs B lyc Sc W memc W mem2 slo (spZ regs) Ea).
{ eapply (akept_trans SK pa_segs B LAWS pa_segs_low lyc Sc W memc Sc W (ms_mem ms) W mem2 slo (spZ regs)
    (sp1 - 4096) sp1 Ea Ea Ea Hslo_c ltac:(lia) K1
    (akept_of_acall_kept SK pa_segs B LAWS pa_segs_low lyc Sc W (ms_mem ms) W mem2 (sp1 - 4096) sp1
       (fun _ => False) Ea HKc (fun a H => match H with end))).
  - unfold slo; rewrite HK; lia.
  - lia.
  - intros bb mm H; exact H.
  - intros f0 H; exact H.
  - intros a H; exact H.
  - intros a H; exact H. }
set (X3 := fun a : Z => (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 8) \/ (F <= a < F + 64) \/
  (sp1 + 16 <= a < sp1 + 24) \/ (spZ regs - 104 <= a < spZ regs)).
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ X3 HFr3
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?U62, ?U44, ?U60, ?U3_2 in HrrW; unfold X3; lia|]); destruct HinW)) as UN3.
assert (K3 : akept pa_segs B lyc Sc W memc W (ms_mem ms3) slo (spZ regs) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W mem2 W (ms_mem ms3) slo (spZ regs) Ea Ea X3
    HAR Hslo_c ltac:(lia) K2 UN3).
  - intros a _ Hp. eapply apresent_grows; [exact HG3 | exact Hp].
  - intros a H; exact H.
  - intros a Ha. unfold X3 in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
    + left. unfold Ea, aside_rng. right; left. unfold in_zr, shadow_addr. cbn [fst snd].
      change (fs_frame_bytes 0 / 8) with 8. fold F. lia.
    + left. unfold Ea, aside_rng. left. unfold in_zr, frame_rng. cbn [fst snd].
      change (fs_frame_bytes 0) with 64. fold F. lia.
    + right. unfold slo; rewrite HK. lia.
    + right. unfold slo; rewrite HK. lia. }
(* ---- the state at the fprintf call (+0x11c) ---- *)
set (cx := mkEMCX G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fmt ps args T kf) in *.
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W (ms_mem ms3) _ k HJ3)
  as HAR3.
pose proof K3 as (_ & K3blk & K3img & _).
assert (NSIDE : forall a, in_img pa_segs a -> ~ Ea a).
{ intros a Hi HEa.
  destruct (aside_rng_low SK pa_segs B LAWS pa_segs_low lyc S2 W mem2 md2 0 fpos a HAR2 Hfin2 HEa) as (_ & Hn).
  exact (Hn Hi). }
assert (HROD3 : arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W) (ms_mem ms3))).
{ intros a Hro Ho He.
  assert (Hia : in_img pa_segs a)
    by (destruct Hro as [(s0 & Hs & _ & Hr) | Hr]; [exists s0; split; [exact Hs | lia] | exact (RELRO_IMG a Hr)]).
  rewrite (K3img a Hia Ho He (NSIDE a Hia)). exact (HROD a Hro Ho He). }
(* the FILE block: a block of Sc (and of S2), outside the side frame, its bytes as at the entry *)
assert (HFIN2 : In (e_f cx, AMF_BLOCK) (ablocks B lyc S2)) by (rewrite Eab; exact HFIN).
destruct (al_blocks _ _ LAWS _ _ _ _ _ (e_f cx) AMF_BLOCK HAR3 HFIN2) as (_ & Hf4096 & Hfceil & Hfapp & Hfpres & _ & _).
change (req_size AMF_BLOCK) with AMF_BLOCK in Hfceil, Hfapp, Hfpres.
assert (BNS : forall b m a, In (b, m) (ablocks B lyc Sc) -> b <= a < b + req_size m -> ~ Ea a).
{ intros b m a Hbm Ha.
  assert (Hb1 : In (b, m) (ablocks B lyc S2)) by (rewrite Eab; exact Hbm).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ b m HAR2 Hb1) as (_ & H4096 & Hbc & Hbapp & Hpo & _ & _).
  destruct (frames_bounds pa_segs B LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (Hf4 & Hfc & _).
  destruct (al_flag _ _ LAWS lyc S2 W mem2 md2 0 fpos HAR2 Hfin2) as (_ & Hfo & _ & _).
  pose proof (fs_frame_bytes_nonneg 0) as Hnn.
  pose proof (shadow_addr_bounds (frame_addr lyc 0 fpos) ltac:(lia)) as Hsb1.
  pose proof (shadow_addr_bounds (frame_addr lyc 0 fpos + fs_frame_bytes 0) ltac:(lia)) as Hsb2.
  pose proof (shadow_range_end (frame_addr lyc 0 fpos) (fs_frame_bytes 0) Hnn) as Hse.
  unfold Ea, aside_rng. intros [Hr | [Hr | Hr]].
  - pose proof (sep_block_frame pa_segs B LAWS lyc S2 W mem2 md2 b m 0 fpos HAR2 Hb1 Hfin2) as Hd.
    unfold zdisjoint, in_zr, frame_rng in Hd, Hr. cbn [fst snd] in Hd, Hr. lia.
  - pose proof (in_app_addr _ _ a Hbapp ltac:(lia)) as Hap. unfold app_addr in Hap.
    unfold in_zr in Hr. cbn [fst snd] in Hr. unfold kLowShadowBeg, ASAN_CEIL in Hap. lia.
  - exact (proj2 (Hpo a ltac:(lia)) (eq_ind_r (fun x => aowned B lyc S2 x) Hfo Hr)). }
assert (FB : forall a, e_f cx <= a < e_f cx + AMF_BLOCK ->
  mbyte pa_segs (rdW W (ms_mem ms3)) a = mbyte pa_segs (e_m cx) a).
{ intros a Ha. apply (mbyte_of_aview pa_segs).
  pose proof (K3blk (e_f cx) AMF_BLOCK (a - e_f cx) HFIN ltac:(change (req_size AMF_BLOCK) with AMF_BLOCK; lia)
    ltac:(replace (e_f cx + (a - e_f cx)) with a by lia;
          exact (BNS _ _ a HFIN ltac:(change (req_size AMF_BLOCK) with AMF_BLOCK; lia)))) as Hv.
  replace (e_f cx + (a - e_f cx)) with a in Hv by lia. exact Hv. }
destruct (amf_k_of_amemfile_k pa_segs (e_m cx) (e_f cx) kf HMF) as (HMFk & HMFw & HMFg).
pose proof (amf_k_ext pa_segs link_amf (e_m cx) (rdW W (ms_mem ms3)) (e_f cx) kf FB HMFk) as HMF3.
assert (HFIT' : kf + 22 <= 1024) by (unfold EMIT_HEAD, AMF_BUFSIZ in HFIT; lia).
assert (VIS : forall i, 0 <= i < kf -> ard pa_segs (rdW W (ms_mem ms3)) (e_f cx + AMF_BUF + i) <> None).
{ intros i Hi. destruct (Hfpres (e_f cx + AMF_BUF + i) ltac:(unfold AMF_BUF, AMF_BLOCK in *; lia)) as (Hp & _).
  destruct Hp as (Hh & b0 & Hb0). unfold ard, mbyte, mrestrict. rewrite Hh, Hb0. discriminate. }
destruct (amf_k_facts pa_segs link_amf _ (e_f cx) kf HMF3 VIS)
  as (fl & om & wend & wpos & wbase & pos & len & pb & Hdyn & Hpend & Hplen).
(* the literals at the call's memory *)
destruct (em_lit_keep_ok B TB HSEGS PCAP_RLO PCAP_RHI W memc lyc S2 W (ms_mem ms3) _ regs REAC_CODE_EMIT_AK
  LA_FMT_SS S_FMT_SS em_lit_fmt HAR3 HROD HROD3 HL1 HL1r) as (HL1' & HL1r').
destruct (em_lit_keep_ok B TB HSEGS PCAP_RLO PCAP_RHI W memc lyc S2 W (ms_mem ms3) _ regs REAC_CODE_EMIT_AK
  LA_S_REACPW S_REACPW em_lit_reacpw HAR3 HROD HROD3 HL2 HL2r) as (HL2' & HL2r').
destruct (em_lit_keep_ok B TB HSEGS PCAP_RLO PCAP_RHI W memc lyc S2 W (ms_mem ms3) _ regs REAC_CODE_EMIT_AK
  LA_S_E_NOT_MARKED S_E_NOT_MARKED em_lit_enm HAR3 HROD HROD3 HL3 HL3r) as (HL3' & HL3r').
(* the registers at the call *)
sreg HS5 (1%bv : bv 5) Q1. sreg HS5 (2%bv : bv 5) Q2. sreg HS5 (3%bv : bv 5) Q3. sreg HS5 (4%bv : bv 5) Q4.
sreg HS5 (8%bv : bv 5) Q8. sreg HS5 (9%bv : bv 5) Q9. sreg HS5 (10%bv : bv 5) Q10. sreg HS5 (11%bv : bv 5) Q11.
sreg HS5 (12%bv : bv 5) Q12. sreg HS5 (13%bv : bv 5) Q13. sreg HS5 (18%bv : bv 5) Q18. sreg HS5 (19%bv : bv 5) Q19.
sreg HS5 (20%bv : bv 5) Q20. sreg HS5 (21%bv : bv 5) Q21. sreg HS5 (22%bv : bv 5) Q22. sreg HS5 (23%bv : bv 5) Q23.
sreg HS5 (24%bv : bv 5) Q24. sreg HS5 (25%bv : bv 5) Q25. sreg HS5 (26%bv : bv 5) Q26. sreg HS5 (27%bv : bv 5) Q27.
cbn [sv_denot] in Q1, Q2, Q3, Q4, Q8, Q9, Q10, Q11, Q12, Q13, Q18, Q19, Q20, Q21, Q22, Q23, Q24, Q25, Q26, Q27.
assert (IMG : forall nn, (A_TEXT <= nn < A_LIM)%nat -> bv_unsigned (ew E3v nn) = pa_val nn) by exact HEI3.
destruct em_obj_lits as (V58 & V59 & V60).
rewrite (IMG 240%nat ltac:(cbv; lia)) in Q1. change (pa_val 240) with BASE in Q1.
rewrite (IMG 299%nat ltac:(cbv; lia)) in Q11. change (pa_val 299) with (pa_val (A_OBJ 58)) in Q11. rewrite V58 in Q11.
rewrite (IMG 300%nat ltac:(cbv; lia)) in Q12. change (pa_val 300) with (pa_val (A_OBJ 59)) in Q12. rewrite V59 in Q12.
rewrite (IMG 301%nat ltac:(cbv; lia)) in Q13. change (pa_val 301) with (pa_val (A_OBJ 60)) in Q13. rewrite V60 in Q13.
rewrite U60 in Q2, Q9. rewrite U44 in Q19, Q22. rewrite U62 in Q21. rewrite ?Z.add_0_r in *.
rewrite (OLDA 3%nat ltac:(lia)), E3, Z_to_bv_bv_unsigned in Q3.
rewrite (OLDA 4%nat ltac:(lia)), E4, Z_to_bv_bv_unsigned in Q4.
rewrite (OLDA 10%nat ltac:(lia)), E10, Z_to_bv_bv_unsigned in Q10, Q20.
rewrite (OLDA 13%nat ltac:(lia)), E13, Z_to_bv_bv_unsigned in Q18.
rewrite (OLDA 2%nat ltac:(lia)), Usp in Q8.
rewrite (OLDA 24%nat ltac:(lia)), (EREG 24%nat 24%bv eq_refl), Z_to_bv_bv_unsigned in Q24.
rewrite (OLDA 25%nat ltac:(lia)), (EREG 25%nat 25%bv eq_refl), Z_to_bv_bv_unsigned in Q25.
rewrite (OLDA 26%nat ltac:(lia)), (EREG 26%nat 26%bv eq_refl), Z_to_bv_bv_unsigned in Q26.
rewrite (OLDA 27%nat ltac:(lia)), (EREG 27%nat 27%bv eq_refl), Z_to_bv_bv_unsigned in Q27.
assert (Hsp3 : spZ (ms_regs ms3) = sp1) by (unfold spZ; rewrite Q2; apply unsigned_lit_small; lia).
(* ---- +0x11c: wrapper_fprintf (f, "%s: %s ", "reac-pw", "E_NOT_MARKED") ---- *)
pmkst HS5. rewrite em_hfpr.
set (md3 := with_vm_backing (m_vm_lazy md2) mat3 md2) in *.
set (WS := map (argZ (ms_regs ms3)) [2; 3; 4; 5; 6; 7] ++ []).
assert (HWS : WS = LA_S_REACPW :: LA_S_E_NOT_MARKED :: map (argZ (ms_regs ms3)) [4; 5; 6; 7]).
{ unfold WS. rewrite app_nil_r. cbn [map]. unfold argZ at 1 2.
  change (Z_to_bv 5 (10 + 2)) with (Z_to_bv 5 (bv_unsigned (12%bv : bv 5))).
  change (Z_to_bv 5 (10 + 3)) with (Z_to_bv 5 (bv_unsigned (13%bv : bv 5))).
  rewrite !em_getr_lit, Q12, Q13, !unsigned_lit_small by lia. reflexivity. }
assert (HWIN : win_in (spZ regs) REAC_CODE_EMIT_AK sp1 LFP_STK).
{ unfold win_in, LFP_STK, LVF_MUSL_STK. rewrite HK. repeat split; lia. }
assert (HLapart : forall p q, em_img_b p (p + q) = true -> 0 < q -> apart p q (e_f cx) AMF_BLOCK).
{ intros p q Hb Hq. apply (blk_apart_img B LAWS lyc S2 W (ms_mem ms3) md3 (e_f cx) AMF_BLOCK p q HAR3 HFIN2);
    [unfold AMF_BLOCK; lia | intros a Ha; exact (em_img_of_b p (p + q) a Hb Ha) | exact Hq]. }
destruct (link_guard_val HSEGS W (ms_mem ms3)) as (cval & Hcval).
destruct (link_guard_apart B LAWS HSEGS lyc S2 W (ms_mem ms3) md3 LFP_STK sp1 (e_f cx) HAR3 HFIN2
  ltac:(unfold LFP_STK, LVF_MUSL_STK; lia) ltac:(unfold LFP_STK, LVF_MUSL_STK; lia)) as (HGA1 & HGA2).
destruct (aj_gx_printf_pre SK pa_segs B LFP_STK G XO OUT STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 W
  (ms_mem ms3) md3 k (ms_regs ms3) HJ3 ltac:(unfold LFP_STK, LVF_MUSL_STK; rewrite Hes; lia) ltac:(rewrite Hsp3; exact Hsp1al16)
  ltac:(rewrite Hsp3; unfold LFP_STK, LVF_MUSL_STK; lia) ltac:(rewrite Hsp3; lia)
  ltac:(rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]) ltac:(rewrite Q3; exact Hgp) ltac:(rewrite Q4; exact Htp))
  as (Hecall & Hstklo & Hwinp).
eapply SRr_bind.
{ eapply (aj_gx_printf_mf_at SK pa_segs B LAWS pa_segs_low LFP_STK LA_W_FPRINTF G XO OUT W (ms_regs ms3) (ms_mem ms3)
    STK sp0 FP ly S W0 mem0 md0 ((0, fpos) :: own) lyc S2 md3 k (getr (ms_regs ms3) 1) (e_f cx) kf pb EM_T fl om wend
    pos len HGok HJ3 ltac:(unfold LFP_STK, LVF_MUSL_STK; lia) ltac:(rewrite Hsp3; unfold LFP_STK, LVF_MUSL_STK; lia) ltac:(rewrite Hsp3; lia)
    eq_refl).
  - intros a Ha.
    eapply ajw_mono.
    + apply Hajw. apply (proj2 (e_E_file cx a Hf0)). exact Ha.
    + intros bb mm Hbm. rewrite Eab. exact Hbm.
    + intros x Hx. right. exact Hx.
    + intros c q. reflexivity.
  - rewrite <- Hsp3 in HGA1, HGA2.
    refine (FPR fx lyc S2 W (ms_regs ms3) (ms_mem ms3) md3 (e_f cx) LA_FMT_SS kf fl om wend wpos wbase pos len pb []
      WS EM_T cval Hecall Hstklo _ _ _ HFIN2 _ HMF3 Hdyn Hpend Hplen _ HROD3 _ Hcval _ _ _ _ HGA1 HGA2 _ _ _ _ _ Hfrm).
    + exact Hwinp.
    + rewrite Q10. unfold w64.
      change (e_f cx) with (bv_unsigned (getr regs (Z_to_bv 5 (bv_unsigned (10%bv : bv 5))))).
      rewrite em_getr_lit, Z_to_bv_bv_unsigned. reflexivity.
    + rewrite Q11. reflexivity.
    + rewrite Hsp3. cbn [vmf_out pairwise]. split; [|split; [constructor | exact I]].
      constructor; [|constructor]. unfold zdisjoint. cbn [fst snd]. unfold LFP_STK, LVF_MUSL_STK, AMF_BLOCK in *. lia.
    + rewrite em_T_len. unfold EMIT_HEAD, AMF_BUFSIZ. lia.
    + exact (link_guard_got B TB HSEGS lyc S2 W (ms_mem ms3) md3 HAR3).
    + unfold LinkMfDefs.LA_GOT_GUARD. lia.
    + unfold LinkMfDefs.LA_GOT_GUARD. lia.
    + unfold LinkMfDefs.LA_GUARD. lia.
    + unfold LinkMfDefs.LA_GUARD. lia.
    + split; [reflexivity|]. intros i Hi. cbn [length] in Hi. lia.
    + rewrite Hsp3. cbn [length]. lia.
    + rewrite Hsp3. cbn [vmf_out length]. constructor; [|constructor; [|constructor]]; unfold zdisjoint; cbn [fst snd];
        unfold LFP_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia.
    + rewrite Hsp3, HWS.
      apply (link_vf_FF_of_c _ _ LA_FMT_SS EM_FMT EM_PS EM_ARGS EM_T _).
      * exact (afmt_at pa_segs regs REAC_CODE_EMIT_AK (rdW W (ms_mem ms3)) LA_FMT_SS EM_FMT LFP_STK sp1 (e_f cx)
          HWIN em_fmt_rng HL1' HL1r' (HLapart LA_FMT_SS 15 ltac:(vm_compute; reflexivity) ltac:(lia))).
      * exact em_parse.
      * exact em_pieces.
      * cbn [map pa_tr pf_args_asan]. split.
        { exact (astr_asan pa_segs regs REAC_CODE_EMIT_AK (rdW W (ms_mem ms3)) LA_S_REACPW EM_L1 LFP_STK sp1 (e_f cx)
            HWIN em_l1_rng HL2' HL2r' (HLapart LA_S_REACPW 15 ltac:(vm_compute; reflexivity) ltac:(lia))). }
        split; [|exact I].
        exact (astr_asan pa_segs regs REAC_CODE_EMIT_AK (rdW W (ms_mem ms3)) LA_S_E_NOT_MARKED EM_L2 LFP_STK sp1 (e_f cx)
          HWIN em_l2_rng HL3' HL3r' (HLapart LA_S_E_NOT_MARKED 20 ltac:(vm_compute; reflexivity) ltac:(lia))).
      * exact em_text.
      * unfold LA_FMT_SS. lia.
      * cbn [length EM_FMT]. unfold LA_FMT_SS. lia.
      * cbn [map pa_tr pf_args_slack]. unfold amem_range.
        split; [left; vm_compute; congruence|]. split; [left; vm_compute; congruence | exact I].
      * discriminate.
      * cbn [map pa_tr RT_pf_sh.pf_args_amem]. unfold amem_range.
        split; [left; vm_compute; congruence|]. split; [left; vm_compute; congruence | exact I].
    + rewrite em_T_len. unfold EMIT_HEAD. lia. }
cbv beta. intros W4 c4 _ (-> & fx' & regs4 & mem4 & md4 & -> & Hfxr & HJ4 & HP4 & Hsm4 & H10 & Hfp4 & Hkept4 & Hpres4).
(* ---- +0x120: wrapper_fprintf returned at fx'; the cut EM_f1_ra ---- *)
set (X4 := fun a : Z => (e_f cx <= a < e_f cx + AMF_BLOCK) \/ (sp1 - LFP_STK <= a < sp1)).
assert (UN4 : forall a, 0 <= a < 2 ^ 64 -> ~ X4 a ->
  aview pa_segs (w_H W) mem4 a = aview pa_segs (w_H W) (ms_mem ms3) a).
{ intros a Ha HX. apply Hkept4; [exact Ha | intro H; apply HX; left; exact H |].
  rewrite Hsp3. intro H; apply HX; right; exact H. }
assert (K4 : akept pa_segs B lyc Sc W memc W mem4 slo (spZ regs) (fun a => e_E cx a \/ Ea a)).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W (ms_mem ms3) W mem4 slo (spZ regs) Ea
    (fun a => e_E cx a \/ Ea a) X4 HAR Hslo_c ltac:(lia) K3 UN4).
  - intros a _ Hp. exact (Hpres4 a Hp).
  - intros a H; right; exact H.
  - intros a Ha. unfold X4 in Ha. destruct Ha as [Ha | Ha].
    + left. left. exact (proj2 (e_E_file cx a Hf0) Ha).
    + right. unfold slo, LFP_STK, LVF_MUSL_STK in *. rewrite HK. lia. }
pose proof K4 as (_ & _ & K4img & _).
assert (HROD4 : arodata_okP pa_segs PCAP_RLO PCAP_RHI B (aview pa_segs (w_H W) mem4)).
{ intros a Hro Ho He.
  assert (Hia : in_img pa_segs a)
    by (destruct Hro as [(s0 & Hs & _ & Hr) | Hr]; [exists s0; split; [exact Hs | lia] | exact (RELRO_IMG a Hr)]).
  rewrite (K4img a Hia Ho He ltac:(intros [HE | HE]; [exact (Hnro a HE Hro) | exact (NSIDE a Hia HE)])).
  exact (HROD a Hro Ho He). }
assert (Hfd : m_fds md4 = m_fds mdc /\ m_fs md4 = m_fs mdc).
{ destruct (em_sbm_fds _ _ Hsm4) as [A1 A2]. unfold md3 in A1, A2.
  destruct (wvb_fds_fs (m_vm_lazy md2) mat3 md2) as [B1 B2].
  destruct (em_sbm_fds _ _ Hsbm) as [Cf1 Cf2].
  destruct (wvb_fds_fs (m_vm_lazy mdc) mat mdc) as [D1 D2]. split; congruence. }
(* the callee-saved registers, in the literal form *)
assert (PR : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs4 r = getr (ms_regs ms3) r).
{ intros r Hr. rewrite <- (em_getr_lit regs4 r), <- (em_getr_lit (ms_regs ms3) r). exact (HP4 _ Hr). }
(* the words the walk reads back: outside the callee's window and the FILE block *)
assert (KW : forall a, 0 <= a -> a + 8 <= 2 ^ 64 -> ~ (e_f cx < a + 8 /\ a < e_f cx + AMF_BLOCK) ->
  ~ (sp1 - LFP_STK < a + 8 /\ a < sp1) ->
  rdword (aview pa_segs (w_H W) mem4) a = rdword (aview pa_segs (w_H W) (ms_mem ms3)) a).
{ intros a H0 H1 H2 H3. apply rdword_ext. intros j Hj. apply UN4; [lia|]. unfold X4. lia. }
sregion HS5 3%nat HRst. sregion HS5 1%nat HRF.
pose proof (sep_block_frame pa_segs B LAWS lyc S2 W mem2 md2 (e_f cx) AMF_BLOCK 0 fpos HAR2 HFIN2 Hfin2) as HsepF.
unfold zdisjoint in HsepF. cbn [fst snd] in HsepF. change (req_size AMF_BLOCK) with AMF_BLOCK in HsepF.
change (fs_frame_bytes 0) with 64 in HsepF. fold F in HsepF.
apply (NEXT fx' fx cx fpos k lyc S2 W (@mkst fx' regs4 (getr (ms_regs ms3) 1) mem4 (seg_rom pa_segs)) md4
  Hfxr Hfrm HBASE HJ4).
unfold em_f1_inv.
destruct (ms_shape_mkst (fx := fx') pa_segs (mkst regs4 (getr (ms_regs ms3) 1) mem4 (seg_rom pa_segs)) regs4 _ mem4
  eq_refl) as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
split.
{ unfold em_shape. rewrite Z6, Q1. split; [reflexivity|]. split; [exact Z1|]. split; [exact Z2|].
  split; [exact Z3|]. split; [exact Z4 | exact Z5]. }
split.
{ unfold em_regs. cbn [ms_regs mkst].
  rewrite (PR 2%bv ltac:(apply em_cs; reflexivity)), (PR 8%bv ltac:(apply em_cs; reflexivity)),
    (PR 9%bv ltac:(apply em_cs; reflexivity)), (PR 18%bv ltac:(apply em_cs; reflexivity)),
    (PR 20%bv ltac:(apply em_cs; reflexivity)), (PR 3%bv ltac:(apply em_cs; reflexivity)),
    (PR 4%bv ltac:(apply em_cs; reflexivity)), (PR 24%bv ltac:(apply em_cs; reflexivity)),
    (PR 25%bv ltac:(apply em_cs; reflexivity)), (PR 26%bv ltac:(apply em_cs; reflexivity)),
    (PR 27%bv ltac:(apply em_cs; reflexivity)).
  rewrite Q2, Q8, Q9, Q18, Q20, Q3, Q4, Q24, Q25, Q26, Q27. repeat split; reflexivity. }
split.
{ unfold em_fregs. cbn [ms_regs mkst].
  rewrite (PR 19%bv ltac:(apply em_cs; reflexivity)), (PR 22%bv ltac:(apply em_cs; reflexivity)),
    (PR 21%bv ltac:(apply em_cs; reflexivity)), (PR 23%bv ltac:(apply em_cs; reflexivity)).
  rewrite Q19, Q22, Q21, Q23. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  apply bv_eq. rewrite !Z_to_bv_unsigned. reflexivity. }
split.
{ unfold em_saved, em_at. cbn [ms_mem mkst]. change (e_spe cx) with (spZ regs). split.
  - rewrite KW by (unfold EM_RA, LFP_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia).
    unfold EM_RA. rewrite (em_region_word _ _ _ _ 2%nat (spZ regs) (-0x28) 1%nat HRst eq_refl U3_2
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))).
    rewrite (OLDA 1%nat ltac:(lia)), E1. reflexivity.
  - intros j Hj. rewrite KW by (unfold EM_S0, LFP_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia).
    assert (Hj8 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by lia.
    unfold EM_S0.
    destruct Hj8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
    cbn [Z.ltb Z.compare]; lazymatch goal with |- rdword _ (?sp + ?o - 8 * ?j) = Some (bv_unsigned (getr ?rg (Z_to_bv 5 ?e))) =>
      let off := eval vm_compute in (o - 8 * j) in
      let n := eval vm_compute in (Z.to_nat e) in
      replace (sp + o - 8 * j) with (sp + off) by lia;
      rewrite (em_region_word _ _ _ _ 2%nat (spZ regs) off n HRst eq_refl U3_2
        ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])));
      rewrite (OLDA n ltac:(lia));
      rewrite (EREG n (Z_to_bv 5 e) ltac:(rewrite Z_to_bv_unsigned; reflexivity));
      reflexivity
    end. }
split.
{ unfold em_va, em_at. cbn [ms_mem mkst]. change (e_spe cx) with (spZ regs). intros j Hj.
  rewrite KW by (unfold EM_VA, LFP_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia).
  assert (Hj4 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia. unfold EM_VA.
  destruct Hj4 as [-> | [-> | [-> | ->]]];
  lazymatch goal with |- rdword _ (?sp + ?o + 8 * ?j) = Some (bv_unsigned (getr ?rg (Z_to_bv 5 ?e))) =>
    let off := eval vm_compute in (o + 8 * j) in
    let n := eval vm_compute in (Z.to_nat e) in
    replace (sp + o + 8 * j) with (sp + off) by lia;
    rewrite (em_region_word _ _ _ _ 2%nat (spZ regs) off n HRst eq_refl U3_2
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])));
    rewrite (OLDA n ltac:(lia));
    rewrite (EREG n (Z_to_bv 5 e) ltac:(rewrite Z_to_bv_unsigned; reflexivity));
    reflexivity
  end. }
split.
{ unfold em_flagw, em_at. cbn [ms_mem mkst]. unfold eF, eFL, EM_CID. cbn [e_lyc cx]. fold F FL.
  change (fs_frame_bytes 0) with 64.
  rewrite KW by (unfold LFP_STK, LVF_MUSL_STK, AMF_BLOCK in *; lia).
  replace (F + 64 - 8) with (F + 56) by lia.
  rewrite (em_region_word _ _ _ _ 44%nat F 56 61%nat HRF eq_refl U44
    ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))).
  rewrite E61, unsigned_lit_small by lia. reflexivity. }
split; [exact HF4096|].
split; [exact HFceil|].
split.
{ unfold em_jbk. split; [reflexivity|].
  split; [rewrite Eab; apply Permutation_refl|].
  split; [exact (set_fs_of_exists S2 Sc HfS)|].
  split; [exact Hfrs2|]. split; [exact Hnin|].
  split; [intros c q; reflexivity|]. split; [intros c q; reflexivity|].
  split; [exists S2, W, mem2, md2; split; [exact HAR2 | split; [exact Hfrs2 | exact Eab]]|].
  exact Hfd. }
split.
{ unfold em_kept. cbn [ms_mem mkst]. split; [exact K4|]. split; [exact HROD4 | intros a H; exact H]. }
{ unfold em_file. cbn [ms_mem mkst].
  destruct (apf_file_post_parts _ _ _ _ _ _ _ _ _ _ _ _ Hfp4) as (HF4 & _ & _).
  rewrite em_T_len in HF4. exact HF4. }
Qed.

About em_entry.
Print Assumptions em_entry.

End b.
End a.
