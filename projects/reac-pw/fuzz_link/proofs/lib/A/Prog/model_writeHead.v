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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module paths, module names and numbers changed; 574 of its 653 lines of code are new or changed and 1472 lines of the source are left out. *)
(* model_write (fuzz_link.asan 0x88100, listing offset AF_model_write = 0x5f34) on image A: the HEAD of its walk, from
   the contract's entry to the MID cut (+0x124 `beqz s6`) of lib/A/Prog/model_writeDefs.v. Template: the
   head of reac_link_alias_write's walk (lib/A/Prog/reac_link_alias_writeHead.v).

   The code walked (listing (internal path) (internal record, sha256 2152d78b142c)):
     +0x00..+0x74  the 128-byte machine frame, the probe `sd zero,0(sp)`, ra and s0..s11 saved, s0 := the entry sp,
                   `andi sp,sp,-0x20`, s1 := sp, s3 := alias, s6 := name, the two .got words, s4 := m, `beqz a2`
                   (not taken: the switch cell's region holds 1, AR's const law), frame_alloc_4(0x260)
                   (the token run, LinkWalk.v paj_run_x)
     +0x74         frame_alloc_4 (0x3ddc4) through LinkWalkSide.v aj_gx_stack_malloc_at
     +0x78..+0xf8  s2 := s11 := F, `bnez s2` (taken: 4096 <= F), s1's word, F's header, F's shadow bytes 0..3 := 0xf1,
                   s7 := F's shadow + 4, the call of meta_fill_f8 (the plain run, LinkWalkSide.v paj_run_call_plain_x)
     +0xf8         meta_fill_f8 (0x55f94) through LinkWalkSide.v aj_gx_set_shadow_at: shadow bytes 4..67 := 0xf8
     +0xfc..+0x120 shadow bytes 0x44..0x4b := 0xf3, s8 := -22 (the plain run, which stops at `beqz s6`)
   The theorem `mw_head` composes the head with the MID obligation into the contract.

   Section hypotheses: LAWS (AR_laws), LV (LinkVals), TL (PALib), TB (the image's asyms record AF0m.PcapSyms; it
   gives frame_alloc_4's entry in the certificate's code table, `mw_hsm4`), ASM4 (frame_alloc_4's contract,
   lib/A/Rt/StackSideInst.v link_stack_malloc_4), MFF8 (meta_fill_f8's contract, lib/A/Rt/SetShadow.v
   link_set_shadow_f8).

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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
index_of_c talk_c model_write_c model_writeDefs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AF0m.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic entry state ----
   Atoms 0..31: the entry registers; 32: the shadow base (the extra word). Regions: the 144 bytes below sp (the
   128-byte frame and the 16 bytes the realignment may add), the shadow base's .got word (A_OBJ 1) and its cell
   (A_OBJ 64), the side-stack switch's .got word (A_OBJ 0) and its cell (A_OBJ 65). *)
Definition MWBx : sv := SOff 32 0.
Definition MWspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition MW_extra : list word := [Z_to_bv 64 SHADOW_OFF].
Definition mw_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition mw_ss0 : sstate :=
  mkSS AF_model_write sr_atoms
    [stack_region MW_SPAN; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 65); uar_cell_regionP (A_OBJ 65)]
    None mw_facts0.

(* Disjointness of a new region from the state's regions, the atoms' values substituted (PcapSourceOpen.v op_disj). *)
Ltac mw_disj U60 U44 U62 U3_2 :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?U60, ?U44, ?U62, ?U3_2;
  try change (fs_frame_bytes 4) with 1024; try change (1024 / 8) with 128.

Lemma mw_sbm_fds : forall md md', same_but_materialized md md' -> m_fds md' = m_fds md /\ m_fs md' = m_fs md.
Proof. intros md md' H. unfold same_but_materialized in H. rewrite H. apply wvb_fds_fs. Qed.

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
Hypothesis LV : LinkVals.
Hypothesis TL : PALib B.
Hypothesis TB : AF0m.PcapSyms B.
(* frame_alloc_4 (0x3ddc4): lib/A/Rt/StackSideInst.v link_stack_malloc_4 *)
Hypothesis ASM4 : astack_malloc_realizes pa_segs B 4.
(* meta_fill_f8 (0x55f94): lib/A/Rt/SetShadow.v link_set_shadow_f8 *)
Hypothesis MFF8 : aset_shadow_realizes pa_segs B (pa_sigma LS___asan_set_shadow_f8) 0xf8.

Let errno_low := pal_env B TL.

Lemma mw_obj_vals :
  pa_val (A_OBJ 0) = 0xa1a28 /\ pa_val (A_OBJ 1) = 0xa19d0 /\ pa_val (A_OBJ 64) = 0xaa438 /\
  pa_val (A_OBJ 65) = 0xaa440 /\ pa_val A_TEXT = 0x821cc.
Proof.
  repeat split; first [rewrite (lv_text LV); reflexivity | rewrite (lv_obj LV) by (vm_compute; lia); reflexivity].
Qed.

(* frame_alloc_4's entry in the certificate's code table is the listing's call target *)
Lemma mw_hsm4 : pc_stack_malloc (as_code B) 4 = pa_sigma LS___asan_stack_malloc_4.
Proof. rewrite (AF0m.ts_code B TB), (lv_sigma LV). reflexivity. Qed.

(* The entry state, from the journal at the call (as reac_link_alias_writeHead.v aw_entry_st, at this function's
   144-byte span and window). *)
Lemma mw_entry_st : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MODEL_WRITE_AK -> spZ regs <= sp0 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs MW_extra)) mw_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_model_write)) memc (seg_rom pa_segs))).
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16 Hwlo Hwhi.
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : MODEL_WRITE_AK = 8416) by reflexivity. rewrite HK in Hwlo.
  destruct (aj_gx_const_cells SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
    mdc k HJ)
    as (Kuar & Kguar & Kcell & Kgot).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
  destruct mw_obj_vals as (V0 & V1 & V64 & V65 & _).
  set (E := Eimg (Ereg regs MW_extra)).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs MW_extra) nn)
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
  rewrite restrict_mkst_fx. unfold mw_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. fold E. rewrite Usp. split; [unfold MW_SPAN; lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable pa_segs). apply Hpres. unfold MW_SPAN in Ho. lia.
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
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, MW_SPAN. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO. clear. intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [mw_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO Hal16.
    clear. unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* an 8-byte chunk of a region based at an atom, read back as a word of the view *)
Lemma mw_region_word : forall Ex H m (r : YP09.region) (b : nat) bv off (n : nat),
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

(* One saved word of the prologue at a cut, read off the stack region (atom 2) of the cut's state. *)
Ltac mw_save HRst U3_2 OLDA EREG :=
  lazymatch goal with |- rdword _ (?sp - 16 - 8 * ?j) = Some (bv_unsigned (getr ?rg (Z_to_bv 5 ?e))) =>
    let n := eval vm_compute in (Z.to_nat e) in
    let off := eval vm_compute in (-16 - 8 * j) in
    replace (sp - 16 - 8 * j) with (sp + off) by lia;
    replace (Z_to_bv 5 e) with (Z_to_bv 5 (Z.of_nat n)) by reflexivity;
    rewrite <- (EREG n ltac:(lia)), <- (OLDA n ltac:(lia));
    rewrite (mw_region_word _ _ _ _ 2%nat sp off n HRst eq_refl U3_2
      ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right])));
    reflexivity
  end.

Theorem mw_head : mw_mid_obl SK B -> forall rlo rhi, model_write_acontract SK pa_segs rlo rhi B.
Proof.
intros MID rlo rhi.
unfold model_write_acontract, aleaf_rd.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HPRE HRD HP.
set (cx := mkMWCX rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs).
assert (HPX : mw_pre SK B cx) by exact (conj HPRE (conj HRD HP)).
change (SRr pa_segs W (cfg_at pa_segs MODEL_WRITE_A regs memc mdc) (mw_post SK B cx)).
pose proof HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & _).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : MODEL_WRITE_AK = 8416) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (aj_gx_unpack SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  regs 0 HJ ltac:(lia) Hal16 ltac:(rewrite HK in Hwlo; lia) Hwhi)
  as (memS & _ & _ & _ & HSTK & HXO & _ & _ & _ & _ & Hceil & H47).
clear memS.
rewrite HK in Hwlo.
assert (Hspc : alloc_ceiling + 8416 <= spZ regs) by lia.
assert (Hspw : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ) as HAR.
pose proof (aj_gx_present SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k HJ)
  as HJpres.
(* the entry state *)
pose proof (mw_entry_st G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJ Hal16
  ltac:(rewrite HK; exact Hwlo) Hwhi) as HS.
remember (Eimg (Ereg regs MW_extra)) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (EREG : forall r : nat, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))).
{ intros r Hr. subst E. apply ew_Eimg_Ereg_nat.
  rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 5) with 32.
  symmetry. apply Z.mod_small. lia. }
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regs 3) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regs 4) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 4 4%bv eq_refl)).
assert (E10 : ew E 10 = getr regs 10) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E11 : ew E 11 = getr regs 11) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 11 11%bv eq_refl)).
assert (E12 : ew E 12 = getr regs 12) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 12 12%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HEdef.
assert (SHOK : sh_ok pa_segs MWBx (@nil shent) E (mrestrict (w_H W) memc)) by (apply Forall_nil).
assert (HCFG : cfg_at pa_segs MODEL_WRITE_A regs memc mdc
             = mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_model_write)) memc (seg_rom pa_segs)) mdc).
{ unfold cfg_at. rewrite (lv_text LV). reflexivity. }
rewrite HCFG. clear HCFG.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNC := paj_run_call_plain_x SK B LAWS G HGok XO OUT).
pose (RUNP := paj_run_plain_x SK B LAWS G HGok XO OUT).
(* ---- +0x00 .. +0x74: the prologue, the two .got words, the switch test, up to frame_alloc_4 ---- *)
paj_run_tok RUN HS HJ SHOK MWspan.
{ unfold mw_ss0. cbn [ss_mem].
  repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP
      bcell_regionP uar_got_regionP uar_cell_regionP] in Hx;
    first [lia | rewrite Usp in Hx; left; split; [left; unfold MW_SPAN in Hx; lia | lia]] |]).
  apply awr_ok_x_nil. }
pmkst HS.
sreg HS (2%bv : bv 5) R2. cbn [ms_regs restrict] in R2.
prreg HS (1%bv : bv 5) R1. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
(* s1 = sp = (sp0' - 128) & -32 (+0x40, +0x44) *)
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
(* the machine frame trimmed to the twelve saves [sp0' - 104, sp0'); the probe word and the GOT words are not read
   again *)
lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (ss_mem ssx) in
  let rs' := eval vm_compute in (pick (trim_stack rs (-104) 0) [0]%nat) in
  pose proof (st_ok_submem pa_segs Ex ssx msx rs' HS ltac:(cbn [ss_mem setpc]; submem_to) ltac:(vm_compute; reflexivity))
    as HS2; clear HS; rename HS2 into HS end.
cbn [ss_pc ss_regs ss_resv ss_facts setpc] in HS.
(* ---- +0x74: frame_alloc_4(0x260), the class-4 side frame fpos on top of own ---- *)
eapply SRr_bind.
{ eapply (aj_gx_stack_malloc_at SK pa_segs B LAWS pa_segs_low errno_low 4 ASM4 ltac:(lia)
    (pa_sigma LS___asan_stack_malloc_4) G XO OUT W (ms_regs ms) (ms_mem ms) STK sp0 FP ly S W0 mem0 md0 own lyc Sc
    _ k (getr (ms_regs ms) 1) mw_hsm4 HJ).
  - rewrite Usp1. exact Hsp1al16.
  - rewrite Usp1, Hes. lia.
  - rewrite Usp1. lia.
  - rewrite R3, E3. exact Hgp.
  - rewrite R4, E4. exact Htp.
  - reflexivity.
  - rewrite R1. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact (aside_room_take Sc MODEL_WRITE_ASIDE 4 1 Hside
      ltac:(unfold MODEL_WRITE_ASIDE; left; reflexivity) ltac:(lia)). }
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2
  & Hbb2 & HfS & HF4096 & HFceil & Hz & Hflag & HKc & Hsbm & Hraw2).
rewrite Usp1, Hes in HKc, Hraw2.
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own) lyc S2 W mem2 md2 k HJ2)
  as HAR2.
assert (Hfin2 : In (4, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof (aj_gx_present SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own) lyc S2
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
set (F := frame_addr lyc 4 fpos) in *. set (FL := flag_addr lyc 4 fpos) in *.
prreg HS (10%bv : bv 5) R10.
assert (E44 : ew Ev1 44 = Z_to_bv 64 F) by (rewrite <- R10, Ha0; reflexivity). clear R10.
destruct (frames_bounds pa_segs B LAWS lyc S2 W mem2 md2 4 fpos HAR2 Hfin2) as (_ & _ & HFapp).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. fold F in HFapp.
pose proof (frame_al64 pa_segs B lyc S2 W mem2 md2 4 fpos HAR2 Hfin2) as (HFa64 & _ & _). fold F in HFa64.
change (fs_frame_bytes 4) with 1024 in HFapp, HFceil, Hz, Hflag.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (_ & _ & HFpres & HFSpres).
fold F in HFpres, HFSpres. change (fs_frame_bytes 4) with 1024 in HFpres, HFSpres.
change (1024 / 8) with 128 in HFSpres.
destruct (al_flag _ _ LAWS _ _ _ _ _ 4 fpos HAR2 Hfin2) as (HFLpres & _ & HFLapp & HFLceil).
fold FL in HFLpres, HFLapp, HFLceil. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
assert (HF8b : 0 <= F / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HF8 : (SHADOW_OFF + F / 8) mod 8 = 0).
{ unfold SHADOW_OFF. destruct (div8_of_mul64 F HFa64) as [EF8 _]. rewrite EF8.
  rewrite Z.add_mod by lia. rewrite (Z.mul_comm 8), Z.mod_mul by lia. reflexivity. }
pose proof (frame_facts B lyc S2 _ 4 fpos (proj1 HAR2) Hfin2) as (_ & Hfpos & _).
(* sp and s1: rebind them to the atom 60 = sp1 (+0x40's masked address) *)
assert (E12' : ew Ev1 2 = Z_to_bv 64 (spZ regs)) by (rewrite OLD1 by lia; exact E2').
prreg_raw HS (2%bv : bv 5) Rsp2. prreg_raw HS (9%bv : bv 5) Rs12.
rewrite (denot_and_m32 Ev1 2 (spZ regs) (-128) E12') in Rsp2 by lia.
rewrite (denot_and_m32_add0 Ev1 2 (spZ regs) (-128) E12') in Rs12 by lia.
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
(* the three new regions: s1's 24 bytes (+0xa8 `sd s11,0x10(s1)`), F (its flag pointer at 1016), F's 128 shadow
   bytes (frame_alloc_4's zero_shadow, one CZero chunk) *)
assert (ZB : forall i, 0 <= i < 128 ->
  mbyte pa_segs (mrestrict (w_H W) mem2) (SHADOW_OFF + F / 8 + 0 + i) = Some (Z_to_bv 8 0)).
{ intros i Hi. unfold zero_shadow in Hz. pose proof (Hz i ltac:(change (1024 / 8) with 128; lia)) as Hzi.
  unfold shadow_of_addr in Hzi. destruct (aview_byte pa_segs _ _ _ _ Hzi) as (bb & Hbb & Hv & _).
  replace (SHADOW_OFF + F / 8 + 0 + i) with (SHADOW_OFF + F / 8 + i) by lia.
  rewrite Hbb. f_equal. apply bv_eq. rewrite <- Hv. reflexivity. }
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (YP09.mkRegion (Some 60%nat) 0 24 0 24 []) HS eq_refl
  ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst];
        rewrite U60; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
        intros o Ho; apply (apresent_writable pa_segs); apply HJpres2; lia)
  ltac:(mw_disj U60 U44 U62 U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fframe_region 44 61 4 []) HS eq_refl
  ltac:(unfold region_ok, fframe_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 4) with 1024; rewrite U44; split; [lia|]; split; [lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs); apply (proj1 (HFpres (F + o) ltac:(lia)))
        | apply Forall_cons; [|apply Forall_nil]; apply (chunk_ok_val pa_segs _ _ F 1016 8 _ FL);
          [cbn [sv_denot]; rewrite E61, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia
          | replace (F + 1016) with (F + 1024 - 8) by lia; exact (val_mem_of_rdword pa_segs _ _ _ _ Hflag)] ])
  ltac:(mw_disj U60 U44 U62 U3_2; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 4 0 128 [YP09.mkChunk 0 (CZero 128)]) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 4 / 8) with 128; rewrite U62; split; [unfold SHADOW_OFF; lia|]; split; [unfold SHADOW_OFF; lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs);
          replace (SHADOW_OFF + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; lia);
          apply (proj1 (HFSpres o ltac:(lia)))
        | apply Forall_cons; [apply chunk_ok_zero; exact ZB | apply Forall_nil] ])
  ltac:(mw_disj U60 U44 U62 U3_2; unfold SHADOW_OFF; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* ---- +0x78 .. +0xf8: s2 = s11 = F, `bnez s2` (4096 <= F), s1's word, F's header and its first 4 shadow bytes,
   up to the call of meta_fill_f8 ---- *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch type of RUNC with context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
    lazymatch r with (?ssf, PRS_call ?sf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, PRS_call sf)) by (vm_compute; reflexivity);
      eapply (RUNC Wx FUEL Ev ssx ssf sf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI3 HS Hrun HJ2);
      clear Hrun
    end
  end
end.
{ cbn [ss_mem].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U62 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own)
      lyc S2 W mem2 md2 k 4 fpos a HJ2 (or_introl eq_refl)).
    right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 4 / 8) with 128. fold F. lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U44 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own)
      lyc S2 W mem2 md2 k 4 fpos a HJ2 (or_introl eq_refl)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. fold F. lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U60 in Ha.
    left; split; [left; lia | lia]. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U3_2 in Ha.
    left; split; [left; lia | lia]. }
  apply awr_ok_x_nil. }
cbv beta. intros ms3 mat3 HS5 HJ3 HF3 HFr3 HG3.
cbn [ms_mem mkst] in HF3, HFr3, HG3.
pmkst HS5.
prreg HS5 (1%bv : bv 5) Q1. prreg HS5 (3%bv : bv 5) Q3. prreg HS5 (4%bv : bv 5) Q4.
prreg HS5 (10%bv : bv 5) Q10. prreg HS5 (11%bv : bv 5) Q11. prreg HS5 (2%bv : bv 5) Q2.
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own) lyc S2 W (ms_mem ms3) _ k HJ3)
  as HAR3.
(* ---- +0xf8: meta_fill_f8(F's shadow + 4, 64) ---- *)
eapply SRr_bind.
{ eapply (aj_gx_set_shadow_at SK pa_segs B LAWS pa_segs_low (pa_sigma LS___asan_set_shadow_f8) 0xf8 MFF8
    G XO OUT W (ms_regs ms3) (ms_mem ms3) STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own) lyc S2 _ k 4 fpos
    (SHADOW_OFF + F / 8 + 4) 64 (getr (ms_regs ms3) 1) HGok HJ3 (or_introl eq_refl)).
  - rewrite Q10, U62. reflexivity.
  - rewrite Q11. reflexivity.
  - lia.
  - unfold shadow_addr. fold F. unfold SHADOW_OFF. lia.
  - unfold shadow_addr. fold F. change (fs_frame_bytes 4 / 8) with 128. unfold SHADOW_OFF. lia.
  - unfold spZ. rewrite Q2, U60. exact Hsp1al16.
  - unfold spZ. rewrite Q2, U60, Hes. lia.
  - unfold spZ. rewrite Q2, U60. lia.
  - rewrite Q3, OLDA, E3 by lia. exact Hgp.
  - rewrite Q4, OLDA, E4 by lia. exact Htp.
  - reflexivity.
  - rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity]. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hset4 & Hun4 & Hpres4 & Hsm4).
pose proof (ajournal_gx_AR pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own) lyc S2 W mem4 md4 k HJ4)
  as HAR4.
destruct (al_frames _ _ LAWS _ _ _ _ _ 4 fpos HAR4 Hfin2) as (_ & _ & HFpres4 & HFSpres4).
fold F in HFpres4, HFSpres4. change (fs_frame_bytes 4) with 1024 in HFpres4, HFSpres4.
change (1024 / 8) with 128 in HFSpres4.
pose proof (aj_gx_present SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own) lyc S2
  W mem4 md4 k HJ4) as HJpres4.
(* the frame, s1's word and the saves survive the call; the frame's shadow region is put back with no chunks *)
jafter_call_keep_hi HS5 520%nat regs4 (mrestrict (w_H W) mem4) HP4 [1; 2; 3]%nat HS6.
match type of HS6 with ?tq -> _ => assert (HRK : tq); [|specialize (HS6 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. unfold fframe_region.
  repeat apply Forall_cons; try apply Forall_nil;
    split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val];
    rewrite ?U44, ?U60, ?U3_2; try change (fs_frame_bytes 4) with 1024; intros a Ha.
  - apply (mbyte_of_aview pa_segs). apply Hun4; [lia|]. unfold SHADOW_OFF in *. lia.
  - intros _. apply (apresent_writable pa_segs). apply (proj1 (HFpres4 a ltac:(lia))).
  - apply (mbyte_of_aview pa_segs). apply Hun4; [lia|]. unfold SHADOW_OFF in *. lia.
  - intros _. apply (apresent_writable pa_segs). apply HJpres4. lia.
  - apply (mbyte_of_aview pa_segs). apply Hun4; [lia|]. unfold SHADOW_OFF in *. lia.
  - intros _. apply (apresent_writable pa_segs). apply HJpres4. lia. }
clear HS HS5. rewrite <- restrict_mkst_fx in HS6. rename HS6 into HS.
rewrite Q1.
remember (havoc E3v 520 (map (getr regs4) CLOB)) as E4v eqn:HE4 in HS.
assert (HEI4 : img_env pa_val A_LIM E4v) by (rewrite HE4; apply img_env_havoc_hi; [exact HEI3 | cbv; lia]).
assert (OLD4 : forall nn, (nn < 520)%nat -> ew E4v nn = ew E3v nn)
  by (intros nn Hnn; rewrite HE4; apply YN3v.ew_havoc_old; exact Hnn).
clear HE4.
assert (U4_60 : bv_unsigned (ew E4v 60) = sp1) by (rewrite OLD4 by lia; exact U60).
assert (U4_44 : bv_unsigned (ew E4v 44) = F) by (rewrite OLD4 by lia; exact U44).
assert (U4_62 : bv_unsigned (ew E4v 62) = SHADOW_OFF + F / 8) by (rewrite OLD4 by lia; exact U62).
assert (U4_2 : bv_unsigned (ew E4v 2) = spZ regs) by (rewrite OLD4 by lia; exact U3_2).
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
pose proof (st_ok_pi_add_region Ev _ _ (fshadow_region 62 4 0 128 []) HS eq_refl
  ltac:(unfold region_ok, fshadow_region; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem restrict mkst app];
        change (fs_frame_bytes 4 / 8) with 128; rewrite U4_62; split; [unfold SHADOW_OFF; lia|]; split; [unfold SHADOW_OFF; lia|]; split;
        [ intros o Ho; apply (apresent_writable pa_segs);
          replace (SHADOW_OFF + F / 8 + o) with (shadow_addr F + o) by (unfold shadow_addr; lia);
          apply (proj1 (HFSpres4 o ltac:(lia)))
        | apply Forall_nil ])
  ltac:(mw_disj U4_60 U4_44 U4_62 U4_2; unfold SHADOW_OFF; repeat split; lia)) as HS3 end.
clear HS; rename HS3 into HS; norm_pi HS.
(* ---- +0xfc .. +0x120: F's shadow bytes 0x44..0x4b := 0xf3, s8 := -22; the plain run stops at +0x124 `beqz s6`
   ---- *)
lazymatch type of HS with
| st_ok_pi _ _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) =>
  lazymatch type of RUNP with context [sym_runN_pi ?tpi _ _] =>
    let r := eval vm_compute in (sym_runN_pi tpi FUEL ssx) in
    lazymatch r with (?ssf, ?stf) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi tpi FUEL ssx = (ssf, stf)) by (vm_compute; reflexivity);
      eapply (RUNP Wx FUEL Ev ssx ssf stf msx _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI4 HS Hrun I HJ4);
      clear Hrun
    end
  end
end.
{ cbn [ss_mem].
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U4_62 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own)
      lyc S2 W mem4 md4 k 4 fpos a HJ4 (or_introl eq_refl)).
    right. unfold in_zr, shadow_addr. cbn [fst snd]. change (fs_frame_bytes 4 / 8) with 128. fold F. lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U4_44 in Ha.
    left. apply (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 ((4, fpos) :: own)
      lyc S2 W mem4 md4 k 4 fpos a HJ4 (or_introl eq_refl)).
    left. unfold in_zr, frame_rng. cbn [fst snd]. change (fs_frame_bytes 4) with 1024. fold F. lia. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U4_60 in Ha.
    left; split; [left; lia | lia]. }
  apply awr_ok_x_cons.
  { intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U4_2 in Ha.
    left; split; [left; lia | lia]. }
  apply awr_ok_x_nil. }
cbv beta. intros ms5 mat5 HS7 HJ5 HF5 HFr5 HG5.
cbn [ms_mem mkst] in HF5, HFr5, HG5.
(* ---- the MID cut ---- *)
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS7 eq_refl) as Hms5.
destruct (ms_shape_mkst pa_segs ms5 _ _ _ Hms5) as (Hr5 & Hsv5 & Hrom5 & Hfr5 & Hfc5 & Hpc5).
cbn [ss_pc] in Hpc5.
prreg HS7 (2%bv : bv 5) F2. prreg HS7 (9%bv : bv 5) F9. prreg HS7 (8%bv : bv 5) F8.
prreg HS7 (18%bv : bv 5) F18. prreg HS7 (27%bv : bv 5) F27. prreg HS7 (21%bv : bv 5) F21.
prreg HS7 (23%bv : bv 5) F23. prreg HS7 (19%bv : bv 5) F19. prreg HS7 (20%bv : bv 5) F20.
prreg HS7 (3%bv : bv 5) F3. prreg HS7 (4%bv : bv 5) F4.
prreg HS7 (22%bv : bv 5) F22. prreg HS7 (24%bv : bv 5) F24. prreg HS7 (25%bv : bv 5) F25.
spregion HS7 3%nat HRst. spregion HS7 1%nat HRF.
(* what the head kept: the window, frame_alloc_4's acall_kept, the three runs' frames, meta_fill_f8's range *)
set (Ea := aside_rng lyc 4 fpos).
set (slo := spZ regs - MODEL_WRITE_AK).
assert (Hslo_c : alloc_ceiling <= slo) by (unfold slo; rewrite HK; lia).
assert (K0 : akept pa_segs B lyc Sc W memc W memc slo (spZ regs) Ea).
{ apply (akept_refl SK pa_segs B LAWS pa_segs_low). intros a Ha. apply HJpres. unfold slo in Ha. rewrite HK in Ha. lia. }
pose proof (kept_of_frame (segs := pa_segs) E (ss_mem mw_ss0) (w_H W) memc (ms_mem ms)
  (fun a => spZ regs - 144 <= a < spZ regs) HFr
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?Usp in HrrW; cbv beta; lia|]); destruct HinW)) as UN1.
assert (K1 : akept pa_segs B lyc Sc W memc W (ms_mem ms) slo (spZ regs) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W memc W (ms_mem ms) slo (spZ regs) Ea Ea
    (fun a => spZ regs - 144 <= a < spZ regs) HAR Hslo_c ltac:(lia) K0 UN1).
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
  - intros f H; exact H.
  - intros a H; exact H.
  - intros a H; exact H. }
set (X3 := fun a : Z => (SHADOW_OFF + F / 8 <= a < SHADOW_OFF + F / 8 + 128) \/ (F <= a < F + 1024) \/
  (sp1 <= a < sp1 + 24) \/ (spZ regs - 104 <= a < spZ regs)).
assert (HX3 : forall a, X3 a -> Ea a \/ slo <= a < spZ regs).
{ intros a Ha. unfold X3 in Ha. destruct Ha as [Ha | [Ha | [Ha | Ha]]].
  + left. unfold Ea, aside_rng. right; left. unfold in_zr, shadow_addr. cbn [fst snd].
    change (fs_frame_bytes 4 / 8) with 128. fold F. lia.
  + left. unfold Ea, aside_rng. left. unfold in_zr, frame_rng. cbn [fst snd].
    change (fs_frame_bytes 4) with 1024. fold F. lia.
  + right. unfold slo; rewrite HK. lia.
  + right. unfold slo; rewrite HK. lia. }
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ X3 HFr3
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?U62, ?U44, ?U60, ?U3_2 in HrrW; unfold X3; lia|]); destruct HinW)) as UN3.
assert (K3 : akept pa_segs B lyc Sc W memc W (ms_mem ms3) slo (spZ regs) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W mem2 W (ms_mem ms3) slo (spZ regs) Ea Ea X3
    HAR Hslo_c ltac:(lia) K2 UN3).
  - intros a _ Hp. eapply apresent_grows; [exact HG3 | exact Hp].
  - intros a H; exact H.
  - exact HX3. }
assert (K4 : akept pa_segs B lyc Sc W memc W mem4 slo (spZ regs) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W (ms_mem ms3) W mem4 slo (spZ regs) Ea Ea
    (fun a => SHADOW_OFF + F / 8 + 4 <= a < SHADOW_OFF + F / 8 + 4 + 64) HAR Hslo_c ltac:(lia) K3).
  - intros a Ha Hn. exact (Hun4 a Ha Hn).
  - intros a _ Hp. exact (Hpres4 a Hp).
  - intros a H; exact H.
  - intros a Ha. left. unfold Ea, aside_rng. right; left. unfold in_zr, shadow_addr. cbn [fst snd].
    change (fs_frame_bytes 4 / 8) with 128. fold F. lia. }
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ X3 HFr5
  ltac:(intros bbW wloW whiW aW HinW HrrW; vm_compute in HinW;
        repeat (destruct HinW as [HqW | HinW]; [injection HqW as <- <- <-; cbn [base_val] in HrrW;
                rewrite ?U4_62, ?U4_44, ?U4_60, ?U4_2 in HrrW; unfold X3; lia|]); destruct HinW)) as UN5.
assert (K5 : akept pa_segs B lyc Sc W memc W (ms_mem ms5) slo (spZ regs) Ea).
{ eapply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W mem4 W (ms_mem ms5) slo (spZ regs) Ea Ea X3
    HAR Hslo_c ltac:(lia) K4 UN5).
  - intros a _ Hp. eapply apresent_grows; [exact HG5 | exact Hp].
  - intros a H; exact H.
  - exact HX3. }
assert (Hfd : m_fds (with_vm_backing (m_vm_lazy md4) mat5 md4) = m_fds mdc /\
              m_fs (with_vm_backing (m_vm_lazy md4) mat5 md4) = m_fs mdc).
{ destruct (wvb_fds_fs (m_vm_lazy md4) mat5 md4) as [A1 A2]. rewrite A1, A2.
  destruct (mw_sbm_fds _ _ Hsm4) as [B1 B2]. rewrite B1, B2.
  destruct (wvb_fds_fs (m_vm_lazy md2) mat3 md2) as [C1' C2']. rewrite C1', C2'.
  destruct (mw_sbm_fds _ _ Hsbm) as [D1 D2]. rewrite D1, D2.
  destruct (wvb_fds_fs (m_vm_lazy mdc) mat mdc) as [G1 G2]. rewrite G1, G2. split; reflexivity. }
refine (MID cx fpos lyc S2 W ms5 _ HPX _).
unfold mw_gi_mid, mw_base. cbv zeta.
unfold mw_FL, mw_SH, mw_sp1, mw_name, mw_alias, mw_m, mw_E, mw_wr, mw_m0. unfold mw_F, mw_sp.
unfold cx. cbn [mw_rlo mw_rhi mw_G mw_XO mw_OUT mw_STK mw_sp0 mw_FP mw_ly mw_S mw_W0 mw_mem0 mw_md0 mw_own mw_lyc mw_Sc
  mw_W mw_memc mw_mdc mw_k mw_regs].
unfold MW_CID, MW_FLAGPTR, MW_FRAME. rewrite HK. fold F. fold FL. fold sp1.
split; [rewrite Hpc5; apply (f_equal (Z_to_bv 64)); unfold MW_CUT_MID, AF_model_write; lia|].
split; [rewrite F22, OLD4, OLDA by lia; rewrite (EREG 11%nat ltac:(lia)); unfold w64, aarg, argZ;
        rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite F24; unfold w64; apply bv_eq; rewrite !Z_to_bv_unsigned; reflexivity|].
split; [rewrite F25, OLD4, E3_32 by lia; reflexivity|].
split; [exact Hr5|]. split; [exact Hsv5|]. split; [exact Hrom5|]. split; [exact Hfr5|]. split; [exact Hfc5|].
split; [exact HJ5|].
split; [exact Hfrs2|]. split; [exact Hnin|]. split; [exact Hfpos|]. split; [exact HfS|].
split; [rewrite Eab; apply Permutation_refl|].
split; [exists S2, W, mem2, md2; split; [exact HAR2 | split; [exact Hfrs2 | exact Eab]]|].
split; [intros c q; reflexivity|].
split; [rewrite F2, OLD4, E3_60 by lia; reflexivity|].
split; [rewrite F9, OLD4, E3_60 by lia; reflexivity|].
split; [rewrite F8, OLD4, OLDA, E2 by lia; unfold w64, spZ; symmetry; apply Z_to_bv_bv_unsigned|].
split; [rewrite F18, OLD4, E3_44 by lia; reflexivity|].
split; [rewrite F27, OLD4, E3_44 by lia; reflexivity|].
split; [rewrite F21, OLD4, E62 by lia; reflexivity|].
split; [rewrite F23, OLD4 by lia; unfold w64; rewrite U62; reflexivity|].
split; [rewrite F19, OLD4, OLDA by lia; rewrite (EREG 12%nat ltac:(lia)); unfold w64, aarg, argZ;
        rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite F20, OLD4, OLDA by lia; rewrite (EREG 10%nat ltac:(lia)); unfold w64, aarg, argZ;
        rewrite Z_to_bv_bv_unsigned; reflexivity|].
split; [rewrite F3, OLD4, OLDA by lia; exact E3|].
split; [rewrite F4, OLD4, OLDA by lia; exact E4|].
assert (OLDB : forall nn, (nn < 40)%nat -> ew E4v nn = ew E nn) by (intros nn Hnn; rewrite OLD4, OLDA by lia; reflexivity).
split.
{ replace (spZ regs - 8) with (spZ regs + -8) by lia.
  rewrite (mw_region_word _ _ _ _ 2%nat (spZ regs) (-8) 1%nat HRst eq_refl U4_2
    ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))).
  rewrite OLDB, E1 by lia. reflexivity. }
split.
{ intros j Hj.
  assert (Hj12 : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/
                 j = 10 \/ j = 11) by lia.
  destruct Hj12 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]];
    mw_save HRst U4_2 OLDB EREG. }
split.
{ rewrite (mw_region_word _ _ _ _ 44%nat F 1016 61%nat HRF eq_refl U4_44
    ltac:(cbn [YP09.r_chunks]; repeat (first [left; reflexivity | right]))).
  rewrite OLD4, E61, unsigned_lit_small by lia. reflexivity. }
split.
{ exact (akept_mono SK pa_segs B LAWS pa_segs_low lyc Sc W memc W (ms_mem ms5) slo (spZ regs) Ea _ K5
    (fun a H => or_intror H)). }
split; [exact (proj1 Hfd) | exact (proj2 Hfd)].
Qed.

About mw_head.
Print Assumptions mw_head.

End b.
End a.
