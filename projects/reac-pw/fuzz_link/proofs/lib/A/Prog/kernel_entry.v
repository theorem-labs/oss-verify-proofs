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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_link/lib/A/Prog/reac_code_emitEntry.v, with its module names changed; 721 of its 866 lines of code are new or changed and 633 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A: kernel's ENTRY phase, +0x00 -> kin_poison (+0x194) (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 4).

   WHAT THE CODE DOES HERE (listing (internal path) (internal record, sha256 7bc02d6772b3)):
   - +0x00 .. +0x3c: the 352-byte frame (`addi sp, sp, -0x160`), the probe `sd zero, 0(sp)`, ra and s0..s11 saved at
     sp0 - 8 .. sp0 - 104, s0 := sp0;
   - +0x40 .. +0x44: `andi sp, sp, -0x20`, s1 := sp (the realigned sp1, an atom of its own from here on);
   - +0x48 .. +0x60: s4 := the shadow base (.got+0x60 -> the cell), a2 := the side-stack switch cell (.got+0xb8 ->
     the cell, `lw` +0x58), s2 := a0; `beqz a2` +0x64 is decided by the switch cell's region (AR's const law: 1);
   - +0x68 .. +0x70: frame_alloc_8(0x2240) (0x3df90), through LinkWalkSide.v aj_gx_stack_malloc_sz_at;
   - +0x74 .. +0xd4: s3 := s5 := F, `bnez s3` +0x84 decided by F >= 4096 (frames_bounds), F's header;
   - +0xd8 .. +0xf8: s6 := shadow(F), 4 x 0xf1, slot 0x50 := shadow(F) + 4; meta_fill_f8(shadow(F) + 4, 0x202)
     +0xfc (0x55f94), through aj_gx_set_shadow_at;
   - +0x100 .. +0x18c: 32 x 0xf2, slot 0x80 := shadow(F) + 0x226; meta_fill_f8(shadow(F) + 0x226, 0x202) +0x190.
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
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d YC20 AsStackSz SetShadowDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import
link_aaddr link_amem link_ajkit LinkWalk LinkWalkNlw LinkWalkPi LinkWalkSide.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import kernel_c kernel_img kernel_defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkCall PcapRelro kernel_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* the window kept by a run whose writable regions all lie in the kept window (copy_attr.v's ca_frame_tac) *)
Ltac kn_frame_tac :=
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
  intros b wlo whi x Hin Hrr; vm_compute in Hin;
  repeat (destruct Hin as [Hq | Hin];
    [injection Hq as <- <- <-; cbn [base_val] in Hrr;
     repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H in Hrr end; lia|]);
  destruct Hin.

(* a PLAIN run (no shadow tokens: the stores into the side frame F and its shadow, which the token engine's static
   check refuses) to a call, over ajournal_gx (LinkWalkSide.v paj_run_call_plain_x); leaves the awr_ok_x goal and
   the continuation with ms' mat' HS HJ HF HFr HG introduced *)
Ltac kn_run_call_plain RUNC HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi link_tpi 4000%N ss) in
    lazymatch r with
    | (?ss', PRS_call ?s) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi link_tpi 4000%N ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNC W 4000%N E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
      [ clear Hrun
      | clear Hrun HS HJ;
        let ms' := fresh "ms" in let mat' := fresh "mat" in
        intros ms' mat' HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ ]
    | ?x => idtac "kn_run_call_plain: the run ends" x; fail
    end
  end.

(* ---- the symbolic entry state ----
   Atoms 0..31: the entry registers; 32: the shadow base (EXT 0). Regions: the 352 bytes below sp (the saves and
   the probe word), the shadow base's .got word and cell, the switch's .got word and cell (A_OBJ 0, A_OBJ 65). *)
Definition kn_Bx : sv := SOff 32 0.
Definition kn_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition kn_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0)] [] [].
Definition kn_ss0 : sstate :=
  mkSS (kpc KP_ENTRY) sr_atoms
    [stack_region KN_MFRAME; got_regionP; bcell_regionP 32; uar_got_regionP (A_OBJ 65); uar_cell_regionP (A_OBJ 65)]
    None kn_facts0.

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

Lemma kn_obj_vals :
  pa_val (A_OBJ 0) = 0xa1a28 /\ pa_val (A_OBJ 1) = 0xa19d0 /\ pa_val (A_OBJ 64) = 0xaa438 /\
  pa_val (A_OBJ 65) = 0xaa440 /\ pa_val (A_OBJ 13) = 0x1c1bd /\ pa_val (A_OBJ 14) = 0x83d30 /\
  pa_val A_TEXT = 0x821cc.
Proof.
  repeat split; first [rewrite (lv_text HV); reflexivity | rewrite (lv_obj HV) by (vm_compute; lia); reflexivity].
Qed.

(* The entry state, from the journal at the call. The extra atoms are 32 = the shadow base and the rest of ext
   (the walk puts the realigned sp1 at 33). *)
Lemma kn_entry_st : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ext,
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - KERNEL_AK -> spZ regs <= sp0 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs (w64 SHADOW_OFF :: ext))) kn_ss0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + kpc KP_ENTRY)) memc (seg_rom pa_segs))).
Proof.
  intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ext HJ Hal16 Hwlo Hwhi.
  pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
  pose proof HJi as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
  assert (HK : KERNEL_AK = 4640) by reflexivity. rewrite HK in Hwlo.
  destruct (aj_gx_const_cells SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc
    mdc k HJ)
    as (Kuar & Kguar & Kcell & Kgot).
  rewrite (pal_got_shadow B TL), (pal_cell B TL) in Kgot. rewrite (pal_cell B TL) in Kcell.
  rewrite (pal_got_uar B TL), (pal_uar_cell B TL) in Kguar. rewrite (pal_uar_cell B TL) in Kuar.
  destruct kn_obj_vals as (V0 & V1 & V64 & V65 & _).
  set (E := Eimg (Ereg regs (w64 SHADOW_OFF :: ext))).
  assert (EL : forall nn, (nn < A_TEXT)%nat -> ew E nn = ew (Ereg regs (w64 SHADOW_OFF :: ext)) nn)
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
  rewrite restrict_mkst_fx. unfold kn_ss0. apply pa_entry_st_ok_full.
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. fold E. rewrite Usp. split; [unfold KN_MFRAME; lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable pa_segs). apply Hpres. unfold KN_MFRAME in Ho. lia.
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
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj, KN_MFRAME. cbn [fst snd].
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO. clear. intros. repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [kn_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    fold E. rewrite Usp, E32, unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
    revert Hslo Hshi H47 Hceil C1a Hwlo Hwhi HSTK HXO Hal16.
    clear. unfold SHADOW_OFF. intros. repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
Qed.

(* a word of a region's chunk, and a byte of a region's one-byte literal chunk (kernel_setup.v su_rd_of_region) *)
Lemma ke_rd_of_region : forall E (H : word -> bool) (mm : word -> option byte) n b cs lo hi wlo whi off e v,
  region_ok pa_segs E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 8 e)) cs ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview pa_segs H mm) (b + off) = Some v.
Proof.
  intros E H mm n b cs lo hi wlo whi off e v HR Hb Hin He Hv.
  apply (rdword_of_val_mem pa_segs H mm (b + off) v); [|exact Hv].
  apply (field_of_region (segs := pa_segs) E (mrestrict H mm) n b cs lo hi wlo whi off 8 e v HR Hb Hin He).
  - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hv.
  - change (Z.of_N 8) with 8. lia.
Qed.

Lemma ke_byte_of_region : forall E (H : word -> bool) (mm : word -> option byte) n b cs lo hi wlo whi off z,
  region_ok pa_segs E (mrestrict H mm) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 1 (SLit z))) cs -> 0 <= z < 2 ^ 64 ->
  aview pa_segs H mm (b + off) = Some (z mod 256).
Proof.
  intros E H mm n b cs lo hi wlo whi off z HR Hb Hin Hz.
  apply aview_of_val_mem1; [|apply Z.mod_pos_bound; lia].
  pose proof (field_of_region_any (segs := pa_segs) E (mrestrict H mm) n b cs lo hi wlo whi off 1 (SLit z)
    HR Hb Hin ltac:(cbn; lia)) as Hv.
  cbn [sv_denot] in Hv. rewrite unsigned_lit_small in Hv by lia.
  change (N.to_nat 1) with 1%nat in Hv. change (2 ^ (8 * Z.of_N 1)) with 256 in Hv. exact Hv.
Qed.

(* an image byte of the relro window (KernImg's ki_relro) *)
Lemma ke_relro_img : forall segs B', KernImg segs B' -> forall a, PCAP_RLO <= a < PCAP_RHI -> in_img segs a.
Proof.
  intros segs B' KI' a Ha. pose proof (ki_relro segs B' KI') as H. apply existsb_exists in H as (s & Hs & Hr).
  unfold relro_in_seg in Hr. apply andb_prop in Hr as [Hr H3]. apply andb_prop in Hr as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  exists s. split; [exact Hs|]. unfold PCAP_RLO, PCAP_RHI in *. lia.
Qed.

(* the runtime entries this phase calls (link-a/plan/kernel-plan.md (internal record, sha256 440bf3b40ab7) section 4; the callee table of link-a/plan/PLAN.md (internal record, sha256 2ce66196196e)), and the image facts *)
Hypothesis KI : KernImg pa_segs B.                                      (* kernel_img_tfib.v kernel_img_syms *)
Hypothesis ASM8 : astack_malloc_sz_realizes pa_segs B 0x3df90 8.       (* StackSideInst.v link_stack_malloc_8 *)
Hypothesis ASSF8 : aset_shadow_realizes pa_segs B 0x55f94 0xf8.        (* SetShadow.v link_set_shadow_f8 *)

Theorem kn_entry : forall POST, kfrom SK B POST (kin_poison B) -> kstart SK B POST.
Proof.
intros POST HNEXT cx HB.
destruct cx as [G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs kbs wp wn d la].
pose proof HB as HB0.
unfold kbase, km0, ksp, ka0 in HB.
cbn [k_G k_XO k_OUT k_STK k_sp0 k_FP k_ly k_S k_W0 k_mem0 k_md0 k_own k_lyc k_Sc k_W k_memc k_mdc k_k k_regs
     k_kbs k_wp k_wn k_d k_la] in HB |- *.
destruct HB as (HPRE & HRD & HKP & HNK & HWF & HWP & HWN & HWPr & HWNr & HD & HDL & HLA & HLAL).
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hroom & Hajw & HWRO).
pose proof pa_segs_low as Hsegs. pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : KERNEL_AK = 4640) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJ as (HSTK & HXO & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & H47 & _). clear memS HJi Hstk.
rewrite HK in Hwlo.
(* the realigned sp1 = 32 * ((sp - 352) / 32), atom 33 from the start *)
set (sp1 := 32 * ((spZ regs - 352) / 32)).
destruct (sp1_facts (spZ regs - 352) ltac:(lia) ltac:(rewrite Zminus_mod, Hal16; reflexivity))
  as (Hsp1r & Hsp1al & Hsp1al16).
fold sp1 in Hsp1r, Hsp1al, Hsp1al16.
assert (Hsp1 : spZ regs - 368 <= sp1 <= spZ regs - 352) by lia. clear Hsp1r.
assert (Hspw : 0 <= spZ regs < 2 ^ 64) by (unfold spZ; apply getr_rng).
assert (Hsp1w : 0 <= sp1 < 2 ^ 64) by lia.
pose proof (kn_entry_st G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs [w64 sp1] HJ Hal16
  ltac:(rewrite HK; exact Hwlo) Hwhi) as HS.
remember (Eimg (Ereg regs [w64 SHADOW_OFF; w64 sp1])) as E eqn:HEdef.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Eimg_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E33 : ew E 33 = Z_to_bv 64 sp1)
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok pa_segs kn_Bx [] E (mrestrict (w_H W) memc)) by (apply Forall_nil).
unfold cfg_at, w64.
pose (RUN := paj_run_x SK B LAWS G HGok XO OUT).
pose (RUNTO := paj_run_to_x SK B LAWS G HGok XO OUT).
pose (BR := paj_branch (PI := PI)).
(* +0x00 .. +0x44: the frame, the saves, s0, the realignment, s1 *)
paj_run_to_tok RUNTO HS HJ SHOK kn_span (kpc 0x48).
{ unfold kn_ss0. cbn [ss_mem].
  repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val stack_region got_regionP
      bcell_regionP uar_got_regionP uar_cell_regionP] in Hx;
    first [lia | rewrite Usp in Hx; left; split; [left; unfold KN_MFRAME in Hx; lia | lia]] |]).
  apply awr_ok_x_nil. }
assert (U33 : bv_unsigned (ew E 33) = sp1) by (rewrite E33; apply unsigned_lit_small; lia).
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 4640 <= x < spZ regs) HFr
  ltac:(kn_frame_tac)) as UN1.
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P1.
clear HF HFr HG.
(* +0x48: sp and s1 := atom 33 = sp1, with its range fact *)
assert (HAND : sv_denot E (SAlu ALU_AND (SOff 2 (-352)) (SLit (-32))) = Z_to_bv 64 sp1)
  by (apply (denot_and_m32 E 2 (spZ regs) (-352)); [rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned
      | lia | lia | exact Hspw]).
assert (HAND0 : sv_denot E (SAlu ALU_ADD (SAlu ALU_AND (SOff 2 (-352)) (SLit (-32))) (SLit 0)) = Z_to_bv 64 sp1)
  by (apply (denot_and_m32_add0 E 2 (spZ regs) (-352)); [rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned
      | lia | lia | exact Hspw]).
assert (HD33 : sv_denot E (SOff 33 0) = Z_to_bv 64 sp1)
  by (cbn [sv_denot]; rewrite E33, unsigned_lit_small, Z.add_0_r by lia; reflexivity).
prreg_raw HS (2%bv : bv 5) R2. prreg_raw HS (9%bv : bv 5) R9.
first [rewrite HAND in R2 | rewrite HAND0 in R2]. first [rewrite HAND in R9 | rewrite HAND0 in R9].
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (2%bv : bv 5) (SOff 33 0) HS eq_refl
    ltac:(cbn [ms_regs restrict]; rewrite HD33; symmetry; exact R2)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (ast_ok_pi_set_reg_fp Ev ssx msx (9%bv : bv 5) (SOff 33 0) HS eq_refl
    ltac:(cbn [ms_regs restrict]; rewrite HD33; symmetry; exact R9)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 33%nat (mkAF (2 ^ 46 - 512) (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E33, unsigned_lit_small by lia;
          change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS. norm_pi HS.
(* the stack region narrowed to the saves [sp - 104, sp); the spill area [sp1, sp1 + 0xf8) as a region of atom 33 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  let rs := eval vm_compute in (trim_region (nth 0 (ss_mem ssx) (stack_region 0)) (-104) 0 :: tl (ss_mem ssx)) in
  pose proof (st_ok_pi_submem Ev ssx msx rs HS ltac:(vm_compute; submem_to) ltac:(vm_compute; reflexivity)) as HS3
end.
clear HS. rename HS3 into HS. norm_pi HS.
pose proof (aj_gx_present SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W _ _ k HJ)
  as HJpres.
assert (Ebase : forall nn v, ew E nn = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some nn) = v).
{ intros nn v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
destruct kn_obj_vals as (V0 & V1 & V64 & V65 & V13 & V14 & VT).
assert (EO : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 33%nat) 0 0xf8 0 0xf8 []) HS eq_refl) as HS3
end.
lazymatch type of HS3 with ?t -> _ => assert (HR : t); [|specialize (HS3 HR); clear HR] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite (Ebase 33%nat sp1 E33 Hsp1w).
  split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply (apresent_writable pa_segs). apply HJpres. lia. }
lazymatch type of HS3 with ?t -> _ => assert (HR : t); [|specialize (HS3 HR); clear HR] end.
{ cbn [ss_mem all_disjoint extent_disjoint YP09.r_base YP09.r_lo YP09.r_hi base_val].
  pose proof (EO 1%nat ltac:(lia)) as EO1. pose proof (EO 64%nat ltac:(lia)) as EO64.
  pose proof (EO 0%nat ltac:(lia)) as EO0. pose proof (EO 65%nat ltac:(lia)) as EO65.
  rewrite V1 in EO1. rewrite V64 in EO64. rewrite V0 in EO0. rewrite V65 in EO65.
  cbn [A_OBJ Nat.add] in EO1, EO64, EO0, EO65.
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite ?E33, ?EO1, ?EO64, ?EO0, ?EO65, ?Usp. rewrite ?unsigned_lit_small by lia.
  rewrite ?Usp. repeat split; lia. }
clear HS. rename HS3 into HS. norm_pi HS.
assert (SHOK2 : sh_ok pa_segs kn_Bx [] E (mrestrict (w_H W) (ms_mem ms))) by (apply Forall_nil).
clear SHOK. rename SHOK2 into SHOK.
(* +0x48 .. +0x70: the shadow base, the switch cell (1: `beqz a2` falls through), s2, frame_alloc_8(0x2240) *)
paj_run_tok RUN HS HJ SHOK kn_span.
{ cbn [ss_mem].
  repeat (apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx;
    first [lia | rewrite E33, unsigned_lit_small in Hx by lia; left; split; [left; lia | lia]
           | rewrite Usp in Hx; left; split; [left; lia | lia]] |]).
  apply awr_ok_x_nil. }
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _ (fun x => spZ regs - 4640 <= x < spZ regs) HFr
  ltac:(kn_frame_tac)) as UN2.
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P2.
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ =>
  assert (UN3 : forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - 4640 <= x < spZ regs) ->
    aview pa_segs (w_H W) (ms_mem msx) x = aview pa_segs (w_H W) memc x)
    by (let x := fresh "x" in let Hx := fresh "Hx" in let Hw := fresh "Hw" in
        intros x Hx Hw; rewrite (UN2 x Hx Hw); exact (UN1 x Hx Hw));
  assert (P3 : forall x, apresent (w_H W) memc x -> apresent (w_H W) (ms_mem msx) x)
    by (let x := fresh "x" in let Hp := fresh "Hp" in intros x Hp; exact (P2 x (P1 x Hp)))
end; clear UN1 P1 UN2 P2.
(* the call of frame_alloc_8(0x2240) at +0x70 (LinkWalkSide.v's lift (b)) *)
pmkst HS.
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2b. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10.
rewrite (lv_sigma HV). change (link_sigma LS___asan_stack_malloc_8) with 0x3df90.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  assert (Q3 : getr rg 3 = w64 (as_gp B))
    by (rewrite R3; subst E; rewrite (ew_Eimg_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp);
  assert (Q4 : getr rg 4 = w64 (as_tp B))
    by (rewrite R4; subst E; rewrite (ew_Eimg_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp);
  assert (Qsp : spZ rg = sp1) by (unfold spZ at 1; rewrite R2b, U33; reflexivity);
  assert (Q10 : getr rg 10 = w64 0x2240) by (rewrite R10; reflexivity)
end.
repeat rewrite wvb_collapse in HJ.
assert (Hroom8 : count_cid 8 (frames Sc) < fs_frames 8).
{ unfold aside_room, KERNEL_SIDE in Hroom. apply Forall_inv in Hroom. cbn [fst snd] in Hroom. lia. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  eapply SRr_bind;
  [ eapply (aj_gx_stack_malloc_sz_at SK pa_segs B LAWS pa_segs_low (pal_env B TL) 0x3df90 8 ASM8 ltac:(lia)
      G XO OUT W rg mm STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdx k _ 0x2240 HJ);
    [ rewrite Qsp; first [exact Hsp1al16 | lia] | rewrite Qsp; lia | rewrite Qsp; lia
    | exact Q3 | exact Q4 | exact R1 | apply ret_ok_codeptr_v; [lia | reflexivity]
    | exact Q10 | split; [lia | vm_compute; discriminate] | reflexivity | exact Hroom8 ]
  | ]
end.
cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & R10F & Hbl & Hfr2 & Hnin & Hnev
  & Hbb & Hfs & H4096 & Hceil2 & Hzs & Hflag & Hacall & Hsbm & Hraw2).
jafter_call_keep_pi HS 34%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1]%nat HS2.
pose proof (aj_gx_present SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as HJp2.
pose proof Hacall as (Hac1 & _). rewrite Qsp in Hac1. assert (HES : ESTACK = 4096) by reflexivity.
lazymatch type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite ?U33, ?Usp; intros x Hx.
  - apply kn_mbyte_of_aview. apply Hac1; lia.
  - intros _. apply kn_apresent_writable. apply HJp2. lia.
  - apply kn_mbyte_of_aview. apply Hac1; lia.
  - intros _. apply kn_apresent_writable. apply HJp2. lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* +0x74: F = frame_addr lyc 8 fpos in a0 (atom 38 of the havoc'd env); AR at the new state gives F's alignment,
   presence of F and of its shadow *)
remember (havoc E 34 (map (getr regs2) CLOB)) as Ek eqn:HEk in HS.
assert (HEIk : img_env pa_val A_LIM Ek) by (rewrite HEk; apply img_env_havoc; [assumption | cbv; lia]).
assert (K38 : ew Ek 38 = w64 (frame_addr lyc 8 fpos)) by (rewrite HEk; exact R10F).
assert (K33 : ew Ek 33 = Z_to_bv 64 sp1) by (rewrite HEk, ew_havoc_old by lia; exact E33).
assert (K2 : ew Ek 2 = getr regs 2) by (rewrite HEk, ew_havoc_old by lia; exact E2).
assert (K32 : ew Ek 32 = Z_to_bv 64 SHADOW_OFF)
  by (rewrite HEk, ew_havoc_old by lia; subst E; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_extra regs _ 0)).
pose proof HJ2 as (_ & _ & (memS2 & HJi2 & _) & _). pose proof HJi2 as (HAR2 & _). clear memS2 HJi2.
lazymatch type of HAR2 with AR _ _ ?lyx ?Sx ?Wx ?mx ?mdx =>
  destruct (al_frames _ _ LAWS lyx Sx Wx mx mdx 8 fpos HAR2 ltac:(rewrite Hfr2; left; reflexivity))
    as (HF32 & HFapp & HFpres & HFshpres) end.
set (F := frame_addr lyc 8 fpos) in *.
assert (Hfb8 : fs_frame_bytes 8 = 16384) by reflexivity.
rewrite Hfb8 in Hceil2, HFapp, HFpres, HFshpres.
(* atom 600 := shadow(F); F's range and alignment; shadow(F)'s; the alias (F >> 3) + s4 = atom 600 *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_havoc_hi 600 Ev ssx msx [Z_to_bv 64 (shadow_addr F)] HS ltac:(vm_compute; reflexivity)) as HS3;
  pose proof (img_env_havoc_hi Ev 600 [Z_to_bv 64 (shadow_addr F)] HEIk ltac:(unfold A_LIM; lia)) as HEI3 end.
clear HS. rename HS3 into HS.
remember (havoc Ek 600 [Z_to_bv 64 (shadow_addr F)]) as E3 eqn:HE3 in HS.
rewrite <- HE3 in HEI3.
assert (E3o : forall i, (i < 600)%nat -> ew E3 i = ew Ek i) by (intros i Hi; rewrite HE3; apply ew_havoc_old; exact Hi).
assert (E3600 : ew E3 600 = Z_to_bv 64 (shadow_addr F))
  by (rewrite HE3; unfold havoc; cbn [ew]; rewrite Nat.ltb_irrefl, Nat.sub_diag; reflexivity).
pose proof asan_consts as ((C1a' & C1b') & C2' & C3' & C4' & C5').
assert (HFlo : 4096 <= F) by exact H4096.
assert (HFhi : F + 16384 <= alloc_ceiling) by exact Hceil2.
assert (HshF : shadow_addr F = SHADOW_OFF + F / 8) by reflexivity.
assert (HF8 : F mod 8 = 0) by (rewrite <- (Z.mod_mod F 32) in HF32 by lia; clear -HF32; lia).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 38%nat (mkAF 4096 (2 ^ 47) 5) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3o, K38 by lia; unfold w64;
          rewrite unsigned_lit_small by lia; change (2 ^ 5) with 32; lia)) as HS3 end.
clear HS. rename HS3 into HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_fact Ev ssx msx 600%nat (mkAF SHADOW_OFF (SHADOW_OFF + 2 ^ 44) 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E3600, HshF;
          rewrite unsigned_lit_small by (unfold SHADOW_OFF in *; lia); change (2 ^ 0) with 1;
          unfold SHADOW_OFF in *; lia)) as HS3 end.
clear HS. rename HS3 into HS.
assert (HAL : sv_denot E3 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 38 0) (SLit 3)) (SOff 32 0)) = sv_denot E3 (SOff 600 0)).
{ rewrite (denot_shadow_cell E3 38 32 F SHADOW_OFF); [| rewrite E3o, K38 by lia; reflexivity | lia
    | rewrite E3o, K32 by lia; reflexivity | unfold SHADOW_OFF; lia | unfold SHADOW_OFF in *; lia].
  cbn [sv_denot]. rewrite E3600, HshF, unsigned_lit_small, Z.add_0_r by (unfold SHADOW_OFF in *; lia). reflexivity. }
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_alias Ev ssx msx _ _ HS HAL) as HS3 end.
clear HS. rename HS3 into HS.
norm_pi HS.
assert (U38 : base_val E3 (Some 38%nat) = F)
  by (cbn [base_val]; rewrite E3o, K38 by lia; unfold w64; apply unsigned_lit_small; lia).
assert (U600 : base_val E3 (Some 600%nat) = shadow_addr F)
  by (cbn [base_val]; rewrite E3600; apply unsigned_lit_small; rewrite HshF; unfold SHADOW_OFF in *; lia).
assert (U33k : base_val E3 (Some 33%nat) = sp1)
  by (cbn [base_val]; rewrite E3o, K33 by lia; apply unsigned_lit_small; lia).
assert (U2k : base_val E3 (Some 2%nat) = spZ regs)
  by (cbn [base_val]; rewrite E3o, K2 by lia; reflexivity).
pose proof HFapp as HFapp'. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp'.
(* F's header [F, F + 24) and the first 4 shadow bytes of F as writable regions *)
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 38%nat) 0 24 0 24 []) HS eq_refl) as HS3 end.
lazymatch type of HS3 with ?t -> _ => assert (HR : t); [|specialize (HS3 HR); clear HR] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite U38. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
  intros o Ho. apply kn_apresent_writable. apply HFpres. lia. }
lazymatch type of HS3 with ?t -> _ => assert (HR : t); [|specialize (HS3 HR); clear HR] end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U38, ?U33k, ?U2k.   repeat split; unfold SHADOW_OFF in *; lia. }
clear HS. rename HS3 into HS. norm_pi HS.
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 600%nat) 0 4 0 4 []) HS eq_refl) as HS3 end.
lazymatch type of HS3 with ?t -> _ => assert (HR : t); [|specialize (HS3 HR); clear HR] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite U600, HshF. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [|apply Forall_nil].
  intros o Ho. apply kn_apresent_writable. rewrite <- HshF. apply HFshpres. lia. }
lazymatch type of HS3 with ?t -> _ => assert (HR : t); [|specialize (HS3 HR); clear HR] end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite U600, HshF, U38, ?U33k, ?U2k.   repeat split; unfold SHADOW_OFF in *; lia. }
clear HS. rename HS3 into HS. norm_pi HS.
(* +0x74 .. +0xfc: s3 = s5 = F, `bnez s3` (F >= 4096), slot 0xf0, F's header, s6 = shadow(F), 4 x f1, slot 0x50,
   up to the call of meta_fill_f8 (a PLAIN run: no instrumented check here) *)
pose (RUNC := paj_run_call_plain_x SK B LAWS G HGok XO OUT).
kn_run_call_plain RUNC HS HJ2.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite U600 in Hx; left;
    exact (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 _ lyc S2 W mem2 md2 k
      8 fpos x HJ2 ltac:(left; reflexivity)
      ltac:(right; unfold in_zr; cbn [fst snd]; fold F; rewrite Hfb8; rewrite HshF in Hx; lia)) |].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite U38 in Hx; left;
    exact (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 _ lyc S2 W mem2 md2 k
      8 fpos x HJ2 ltac:(left; reflexivity)
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; rewrite Hfb8; lia)) |].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite U33k in Hx;
    left; split; [left; lia | lia] |].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite U2k in Hx;
    left; split; [left; lia | lia] |].
  apply awr_ok_x_nil. }
(* the run's kept facts: it wrote only F's header, F's first shadow bytes, the spill slots *)
assert (V600 : bv_unsigned (ew E3 600) = shadow_addr F) by (rewrite <- U600; reflexivity).
assert (V38 : bv_unsigned (ew E3 38) = F) by (rewrite <- U38; reflexivity).
assert (V33 : bv_unsigned (ew E3 33) = sp1) by (rewrite <- U33k; reflexivity).
assert (V2 : bv_unsigned (ew E3 2) = spZ regs) by (rewrite <- U2k; reflexivity).
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _
  (fun x => (spZ regs - 4640 <= x < spZ regs) \/ (F <= x < F + 24) \/ (shadow_addr F <= x < shadow_addr F + 4) \/
     (shadow_addr F + 0x206 <= x < shadow_addr F + 0x226)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
        let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
        intros b wlo whi x Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?V600, ?V38, ?V33, ?V2 in Hrr;
           first [left; lia | right; left; lia | right; right; left; lia | right; right; right; lia] |]);
        destruct Hin)) as UN4.
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P4.
clear HF HFr HG.
(* the call of meta_fill_f8(shadow(F) + 4, 0x202) at +0xfc (LinkWalkSide.v's lift (e)) *)
pmkst HS.
prreg HS (1%bv : bv 5) R1c. prreg HS (2%bv : bv 5) R2c. prreg HS (3%bv : bv 5) R3c. prreg HS (4%bv : bv 5) R4c.
prreg HS (10%bv : bv 5) R10c. prreg HS (11%bv : bv 5) R11c.
rewrite (lv_sigma HV). change (link_sigma LS___asan_set_shadow_f8) with 0x55f94.
assert (Hshw : 0 <= shadow_addr F + 4 < 2 ^ 64) by (rewrite HshF; unfold SHADOW_OFF in *; lia).
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  assert (Q3c : getr rg 3 = w64 (as_gp B)) by (rewrite R3c, E3o by lia; rewrite HEk, ew_havoc_old by lia; rewrite HEdef, (ew_Eimg_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp);
  assert (Q4c : getr rg 4 = w64 (as_tp B)) by (rewrite R4c, E3o by lia; rewrite HEk, ew_havoc_old by lia; rewrite HEdef, (ew_Eimg_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp);
  assert (Qspc : spZ rg = sp1) by (unfold spZ at 1; rewrite R2c; exact V33);
  assert (Q10c : getr rg 10 = w64 (shadow_addr F + 4))
    by (rewrite R10c, V600; reflexivity);
  assert (Q11c : getr rg 11 = w64 0x202) by (rewrite R11c; reflexivity);
  eapply SRr_bind;
  [ eapply (aj_gx_set_shadow_at SK pa_segs B LAWS pa_segs_low 0x55f94 0xf8 ASSF8
      G XO OUT W rg mm STK sp0 FP ly S W0 mem0 md0 _ lyc S2 mdx k 8 fpos (shadow_addr F + 4) 0x202 _ HGok HJ2);
    [ left; reflexivity | exact Q10c | exact Q11c | lia | fold F; lia
    | fold F; rewrite Hfb8; lia
    | rewrite Qspc; first [exact Hsp1al16 | lia] | rewrite Qspc; lia | rewrite Qspc; lia
    | exact Q3c | exact Q4c | exact R1c | apply ret_ok_codeptr_v; [lia | reflexivity] ]
  | ]
end.
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Hf8a & Hkeep3 & Hpres3 & Hsbm3).
jafter_call_keep_pi HS 50%nat regs3 (mrestrict (w_H W) mem3) HP3 [0; 1; 2; 3]%nat HS2.
lazymatch type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?U600, ?U38, ?U33k, ?U2k; intros x Hx;
    rewrite ?HshF in Hx |- *.
  - apply kn_mbyte_of_aview. apply Hkeep3; [unfold SHADOW_OFF in *; lia | rewrite ?HshF; lia].
  - intros _. apply kn_apresent_writable. apply Hpres3. apply P4.
    replace x with (shadow_addr F + (x - shadow_addr F)) by lia. apply HFshpres. rewrite HshF; lia.
  - apply kn_mbyte_of_aview. apply Hkeep3; [lia | rewrite ?HshF; unfold SHADOW_OFF in *; lia].
  - intros _. apply kn_apresent_writable. apply Hpres3. apply P4. apply HFpres. lia.
  - apply kn_mbyte_of_aview. apply Hkeep3; [lia | rewrite ?HshF; unfold SHADOW_OFF in *; lia].
  - intros _. apply kn_apresent_writable. apply Hpres3.
    apply (aj_gx_present SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2). lia.
  - apply kn_mbyte_of_aview. apply Hkeep3; [lia | rewrite ?HshF; unfold SHADOW_OFF in *; lia].
  - intros _. apply kn_apresent_writable. apply Hpres3.
    apply (aj_gx_present SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* +0x100 .. +0x18c: 32 x f2 at shadow(F) + 0x206, slot 0x80, up to the second meta_fill_f8 call *)
remember (havoc E3 50 (map (getr regs3) CLOB)) as E4 eqn:HE4 in HS.
assert (HEI4 : img_env pa_val A_LIM E4) by (rewrite HE4; apply img_env_havoc; [assumption | cbv; lia]).
assert (E4o : forall i, (i < 50)%nat -> ew E4 i = ew E3 i) by (intros i Hi; rewrite HE4; apply ew_havoc_old; exact Hi).
assert (E4600 : ew E4 600 = ew E3 600) by (rewrite HE4; apply ew_havoc_above; cbn; lia).
assert (W600 : base_val E4 (Some 600%nat) = shadow_addr F) by (cbn [base_val]; rewrite E4600; exact V600).
assert (W38 : base_val E4 (Some 38%nat) = F) by (cbn [base_val]; rewrite E4o by lia; exact V38).
assert (W33 : base_val E4 (Some 33%nat) = sp1) by (cbn [base_val]; rewrite E4o by lia; exact V33).
assert (W2 : base_val E4 (Some 2%nat) = spZ regs) by (cbn [base_val]; rewrite E4o by lia; exact V2).
lazymatch type of HS with st_ok_pi _ _ ?Ev ?ssx ?msx =>
  pose proof (st_ok_pi_add_region Ev ssx msx (YP09.mkRegion (Some 600%nat) 0x206 0x226 0x206 0x226 []) HS eq_refl) as HS3 end.
lazymatch type of HS3 with ?t -> _ => assert (HR : t); [|specialize (HS3 HR); clear HR] end.
{ unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict].
  rewrite W600, HshF. split; [unfold SHADOW_OFF; lia|]. split; [unfold SHADOW_OFF in *; lia|]. split; [|apply Forall_nil].
  intros o Ho. apply kn_apresent_writable. apply Hpres3. apply P4. rewrite <- HshF. apply HFshpres. lia. }
lazymatch type of HS3 with ?t -> _ => assert (HR : t); [|specialize (HS3 HR); clear HR] end.
{ cbn [ss_mem all_disjoint]. unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
  rewrite W600, HshF, W38, ?W33, ?W2. repeat split; unfold SHADOW_OFF in *; lia. }
clear HS. rename HS3 into HS. norm_pi HS.
kn_run_call_plain RUNC HS HJ3.
{ cbn [ss_mem].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite W600 in Hx; left;
    exact (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 _ lyc S2 W mem3 md3 k
      8 fpos x HJ3 ltac:(left; reflexivity)
      ltac:(right; unfold in_zr; cbn [fst snd]; fold F; rewrite Hfb8; rewrite HshF in Hx; lia)) |].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite W600 in Hx; left;
    exact (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 _ lyc S2 W mem3 md3 k
      8 fpos x HJ3 ltac:(left; reflexivity)
      ltac:(right; unfold in_zr; cbn [fst snd]; fold F; rewrite Hfb8; rewrite HshF in Hx; lia)) |].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite W38 in Hx; left;
    exact (aj_gx_awr_frame SK pa_segs B LAWS pa_segs_low G XO OUT STK sp0 FP ly S W0 mem0 md0 _ lyc S2 W mem3 md3 k
      8 fpos x HJ3 ltac:(left; reflexivity)
      ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; fold F; rewrite Hfb8; lia)) |].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite W33 in Hx;
    left; split; [left; lia | lia] |].
  apply awr_ok_x_cons; [intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite W2 in Hx;
    left; split; [left; lia | lia] |].
  apply awr_ok_x_nil. }
assert (X600 : bv_unsigned (ew E4 600) = shadow_addr F) by (rewrite E4600; exact V600).
assert (X38 : bv_unsigned (ew E4 38) = F) by (rewrite E4o by lia; exact V38).
assert (X33 : bv_unsigned (ew E4 33) = sp1) by (rewrite E4o by lia; exact V33).
assert (X2 : bv_unsigned (ew E4 2) = spZ regs) by (rewrite E4o by lia; exact V2).
pose proof (kept_of_frame (segs := pa_segs) _ _ _ _ _
  (fun x => (spZ regs - 4640 <= x < spZ regs) \/ (F <= x < F + 24) \/ (shadow_addr F <= x < shadow_addr F + 4) \/
     (shadow_addr F + 0x206 <= x < shadow_addr F + 0x226)) HFr
  ltac:(let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
        let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq := fresh "Hq" in
        intros b wlo whi x Hin Hrr; vm_compute in Hin;
        repeat (destruct Hin as [Hq | Hin];
          [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?X600, ?X38, ?X33, ?X2 in Hrr;
           first [left; lia | right; left; lia | right; right; left; lia | right; right; right; lia] |]);
        destruct Hin)) as UN5.
pose proof (fun x Hp => apresent_grows _ _ _ x HG Hp) as P5.
clear HF HFr HG.
(* the call of meta_fill_f8(shadow(F) + 0x226, 0x202) at +0x190 *)
pmkst HS.
prreg HS (1%bv : bv 5) R1d. prreg HS (2%bv : bv 5) R2d. prreg HS (3%bv : bv 5) R3d. prreg HS (4%bv : bv 5) R4d.
prreg HS (10%bv : bv 5) R10d. prreg HS (11%bv : bv 5) R11d.
rewrite (lv_sigma HV). change (link_sigma LS___asan_set_shadow_f8) with 0x55f94.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdx) _ =>
  assert (Q3d : getr rg 3 = w64 (as_gp B))
    by (rewrite R3d, E4o, E3o by lia; rewrite HEk, ew_havoc_old by lia; rewrite HEdef, (ew_Eimg_Ereg_nat regs _ 3 3%bv eq_refl); exact Hgp);
  assert (Q4d : getr rg 4 = w64 (as_tp B))
    by (rewrite R4d, E4o, E3o by lia; rewrite HEk, ew_havoc_old by lia; rewrite HEdef, (ew_Eimg_Ereg_nat regs _ 4 4%bv eq_refl); exact Htp);
  assert (Qspd : spZ rg = sp1) by (unfold spZ at 1; rewrite R2d; exact X33);
  assert (Q10d : getr rg 10 = w64 (shadow_addr F + 0x226)) by (rewrite R10d, X600; reflexivity);
  assert (Q11d : getr rg 11 = w64 0x202) by (rewrite R11d; reflexivity);
  eapply SRr_bind;
  [ eapply (aj_gx_set_shadow_at SK pa_segs B LAWS pa_segs_low 0x55f94 0xf8 ASSF8
      G XO OUT W rg mm STK sp0 FP ly S W0 mem0 md0 _ lyc S2 mdx k 8 fpos (shadow_addr F + 0x226) 0x202 _ HGok HJ3);
    [ left; reflexivity | exact Q10d | exact Q11d | lia | fold F; lia
    | fold F; rewrite Hfb8; lia
    | rewrite Qspd; first [exact Hsp1al16 | lia] | rewrite Qspd; lia | rewrite Qspd; lia
    | exact Q3d | exact Q4d | exact R1d | apply ret_ok_codeptr_v; [lia | reflexivity] ]
  | ]
end.
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hf8b & Hkeep4 & Hpres4 & Hsbm4).
jafter_call_keep_pi HS 66%nat regs4 (mrestrict (w_H W) mem4) HP4 [0; 1; 2; 3; 4]%nat HS2.
lazymatch type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict].
  repeat apply Forall_cons; try apply Forall_nil; split;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi]; rewrite ?W600, ?W38, ?W33, ?W2; intros x Hx;
    rewrite ?HshF in Hx |- *.
  - apply kn_mbyte_of_aview. apply Hkeep4; [unfold SHADOW_OFF in *; lia | rewrite ?HshF; lia].
  - intros _. apply kn_apresent_writable. apply Hpres4. apply P5. apply Hpres3. apply P4.
    replace x with (shadow_addr F + (x - shadow_addr F)) by lia. apply HFshpres. rewrite HshF; lia.
  - apply kn_mbyte_of_aview. apply Hkeep4; [unfold SHADOW_OFF in *; lia | rewrite ?HshF; lia].
  - intros _. apply kn_apresent_writable. apply Hpres4. apply P5. apply Hpres3. apply P4.
    replace x with (shadow_addr F + (x - shadow_addr F)) by lia. apply HFshpres. rewrite HshF; lia.
  - apply kn_mbyte_of_aview. apply Hkeep4; [lia | rewrite ?HshF; unfold SHADOW_OFF in *; lia].
  - intros _. apply kn_apresent_writable. apply Hpres4. apply P5. apply Hpres3. apply P4. apply HFpres. lia.
  - apply kn_mbyte_of_aview. apply Hkeep4; [lia | rewrite ?HshF; unfold SHADOW_OFF in *; lia].
  - intros _. apply kn_apresent_writable. apply Hpres4.
    apply (aj_gx_present SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3). lia.
  - apply kn_mbyte_of_aview. apply Hkeep4; [lia | rewrite ?HshF; unfold SHADOW_OFF in *; lia].
  - intros _. apply kn_apresent_writable. apply Hpres4.
    apply (aj_gx_present SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3). lia. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
(* ---- the cut kin_poison at +0x194. The memories: memc -(run 1)-> ms0 -(frame_alloc_8)-> mem2 -(run 2)-> ms1
   -(meta_fill_f8)-> mem3 -(run 3)-> ms2 -(meta_fill_f8)-> mem4. ---- *)
remember (havoc E4 66 (map (getr regs4) CLOB)) as E5 eqn:HE5 in HS.
assert (E5o : forall i, (i < 66)%nat -> ew E5 i = ew E4 i) by (intros i Hi; rewrite HE5; apply ew_havoc_old; exact Hi).
assert (E5600 : ew E5 600 = ew E4 600) by (rewrite HE5; apply ew_havoc_above; cbn; lia).
assert (ER : forall i, (i < 34)%nat -> ew E5 i = ew E i).
{ intros i Hi. rewrite E5o, E4o, E3o by lia. rewrite HEk, ew_havoc_old by lia. reflexivity. }
assert (EREG : forall i (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r -> ew E5 i = getr regs r).
{ intros i r Hi Hr. rewrite ER by lia. rewrite HEdef. apply ew_Eimg_Ereg_nat. exact Hr. }
assert (Y33 : bv_unsigned (ew E5 33) = sp1) by (rewrite E5o by lia; exact X33).
assert (Y2 : bv_unsigned (ew E5 2) = spZ regs) by (rewrite E5o by lia; exact X2).
assert (Y38 : bv_unsigned (ew E5 38) = F) by (rewrite E5o by lia; exact X38).
assert (Y600 : bv_unsigned (ew E5 600) = shadow_addr F) by (rewrite E5600; exact X600).
assert (Y32 : ew E5 32 = Z_to_bv 64 SHADOW_OFF) by (rewrite ER by lia; rewrite HEdef, Eimg_low by (unfold A_TEXT; lia);
  exact (ew_Ereg_extra regs _ 0)).
assert (YO : forall i, (i < 66)%nat -> ew E5 (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i))).
{ intros i Hi. rewrite HE5, ew_havoc_above by (cbn; unfold A_OBJ; lia). rewrite HE4, ew_havoc_above by (cbn; unfold A_OBJ; lia).
  rewrite HE3, ew_havoc_old by (unfold A_OBJ; lia). rewrite HEk, ew_havoc_above by (cbn; unfold A_OBJ; lia).
  rewrite HEdef. apply Eimg_img. unfold A_OBJ, A_TEXT, A_LIM; lia. }
(* the journal's bookkeeping at the cut *)
lazymatch type of HB0 with kbase _ _ ?c => set (cx := c) in * end.
assert (KJ : kjbk B cx fpos k lyc S2 md4).
{ unfold kjbk, cx; cbn [k_k k_Sc k_lyc k_mdc].
  split; [reflexivity|]. split; [destruct Hfs as (f & Hf); rewrite Hf; reflexivity|].
  split; [rewrite Hbl; apply Permutation_refl|]. split; [exact Hnin|].
  split; [exists S2, W, mem2, md2; split; [exact HAR2|]; split; [exact Hfr2 | exact Hbl]|].
  destruct (kn_sbm_fds_fs _ _ Hsbm4) as (F1 & F2). destruct (kn_sbm_fds_fs _ _ Hsbm3) as (F3 & F4).
  destruct (kn_sbm_fds_fs _ _ Hsbm) as (F5 & F6).
  rewrite (proj1 (wvb_fds_fs _ _ _)) in F1. rewrite (proj1 (wvb_fds_fs _ _ _)) in F3.
  rewrite (proj1 (wvb_fds_fs _ _ _)) in F5. rewrite (proj2 (wvb_fds_fs _ _ _)) in F2.
  rewrite (proj2 (wvb_fds_fs _ _ _)) in F4. rewrite (proj2 (wvb_fds_fs _ _ _)) in F6.
  split; congruence. }
(* the steps after frame_alloc_8 change only the window, F and F's shadow *)
assert (UNP : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 4640 <= a < spZ regs) \/ (F <= a < F + 16384) \/
    (shadow_addr F <= a < shadow_addr F + 2048)) -> aview pa_segs (w_H W) mem4 a = aview pa_segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite (Hkeep4 a Ha) by lia. rewrite (UN5 a Ha) by (cbv beta; lia).
  rewrite (Hkeep3 a Ha) by lia. exact (UN4 a Ha ltac:(cbv beta; lia)). }
assert (PP : forall a, apresent (w_H W) mem2 a -> apresent (w_H W) mem4 a)
  by (intros a Hp; exact (Hpres4 a (P5 a (Hpres3 a (P4 a Hp))))).
assert (UNS : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 4640 <= a < spZ regs) \/ (F <= a < F + 24) \/
    (shadow_addr F <= a < shadow_addr F + 4) \/ (shadow_addr F + 4 <= a < shadow_addr F + 0x428)) ->
    aview pa_segs (w_H W) mem4 a = aview pa_segs (w_H W) mem2 a).
{ intros a Ha Hn. rewrite (Hkeep4 a Ha) by lia. rewrite (UN5 a Ha) by (cbv beta; lia).
  rewrite (Hkeep3 a Ha) by lia. exact (UN4 a Ha ltac:(cbv beta; lia)). }
(* the call: what frame_alloc_8 keeps, in akept's form *)
rewrite Qsp in Hacall.
assert (AKC : akept pa_segs B lyc Sc W (ms_mem ms0) W mem2 (sp1 - ESTACK) sp1 (fun _ => False)).
{ destruct Hacall as (A1 & A2 & A3 & A4 & A5 & A6).
  split; [intros a Ha Hw _; exact (A1 a Ha Hw)|]. split; [exact A2|].
  split; [intros a H1 H2 H3 _; exact (A3 a H1 H2 H3)|].
  split; [exact A4|]. split; [exact A5 | exact A6]. }
pose proof HB0 as HB1. unfold kbase in HB1. destruct HB1 as (HPRE0 & _).
pose proof HPRE0 as (HJ0 & _).
pose proof HJ0 as (_ & _ & (memS0 & HJi0 & _) & _). pose proof HJi0 as (HAR0 & _).
(* every byte of kernel's read set is the entry's *)
assert (KARD : forall a, kernel_ard pa_segs regs (rdW W memc) a ->
  aview pa_segs (w_H W) mem4 a = aview pa_segs (w_H W) memc a).
{ intros a Ha.
  destruct (kn_rd_facts SK B LAWS cx fpos k lyc S2 md4 a HB0 KJ Ha) as (Hab & Hsb & Hfs').
  destruct (kn_ard_bound SK B LAWS cx a HB0 Ha) as (_ & Hwin).
  change (ksp cx) with (spZ regs) in Hwin. unfold kn_fside, in_zr, frame_rng in Hfs'. cbn [fst snd] in Hfs'.
  change (kF cx fpos) with F in Hfs'. change (frame_addr (k_lyc cx) KN_CID fpos) with F in Hfs'.
  change (fs_frame_bytes KN_CID) with 16384 in Hfs'.
  rewrite (UNP a ltac:(lia)) by (rewrite ?HK in Hwin; lia).
  assert (Hakb : akb pa_segs B lyc Sc (sp1 - ESTACK) sp1 a).
  { apply (akb_sub pa_segs B lyc Sc lyc Sc (spZ regs - KERNEL_AK) (spZ regs) (sp1 - ESTACK) sp1 a (HRD a Ha));
      [rewrite HK, HES; lia | lia | reflexivity | reflexivity | intros; assumption | intros; assumption
      | intros; reflexivity]. }
  rewrite (akept_akb_gx SK pa_segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ AKC Hakb (fun H => H)).
  apply UN3; [lia | rewrite ?HK in Hwin; lia]. }
(* every read-only byte is the entry's *)
assert (KRO : forall a, in_roP pa_segs PCAP_RLO PCAP_RHI a -> ~ Exists (in_zr a) (as_owned_static B) ->
  ~ (as_errno B <= a < as_errno B + 4) -> aview pa_segs (w_H W) mem4 a = aview pa_segs (w_H W) memc a).
{ intros a Hro Hno Her. pose proof (kn_ro_low a Hro) as Hlow.
  assert (Himg : in_img pa_segs a).
  { destruct Hro as [(s & Hs & _ & Hr) | Hr]; [exists s; split; [exact Hs | exact Hr] | exact (ke_relro_img _ _ KI a Hr)]. }
  destruct (kn_F_facts B LAWS cx fpos k lyc S2 md4 KJ) as (_ & _ & _ & _ & _ & HFimg & _).
  change (kF cx fpos) with F in HFimg. change (fs_frame_bytes KN_CID) with 16384 in HFimg.
  assert (HnF : ~ (F <= a < F + 16384)) by (intros HF'; exact (HFimg a HF' Himg)).
  rewrite (UNP a ltac:(lia)) by (rewrite HshF; unfold SHADOW_OFF in *; lia).
  destruct Hacall as (_ & _ & A3 & _). rewrite (A3 a Himg Hno Her).
  apply UN3; [lia | lia]. }
(* the akept clause of the cut: the entry's, through the six steps *)
assert (AK0 : akept pa_segs B lyc Sc W memc W memc (spZ regs - KERNEL_AK) (spZ regs) (fun _ => False)).
{ split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [intros; reflexivity|]. split; [intros a _ _ Hp; exact Hp|].
  intros a Ha. apply (aj_gx_present SK pa_segs B LAWS pa_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0).
  change (k_sp0 cx) with sp0. change (k_STK cx) with STK. rewrite HK in Ha. lia. }
assert (AK1 : akept pa_segs B lyc Sc W memc W (ms_mem ms0) (spZ regs - KERNEL_AK) (spZ regs) (fun _ => False)).
{ apply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W memc W (ms_mem ms0)
    (spZ regs - KERNEL_AK) (spZ regs) (fun _ => False) (fun _ => False) (fun x => spZ regs - 4640 <= x < spZ regs) HAR0);
  [rewrite HK; lia | lia | exact AK0 | exact UN3 | intros a _ Hp; exact (P3 a Hp) | intros a Ha; exact Ha
  | intros a Ha; right; rewrite HK; exact Ha]. }
assert (AK2 : akept pa_segs B lyc Sc W memc W mem2 (spZ regs - KERNEL_AK) (spZ regs)
  (fun a => kE cx a \/ aside_rng lyc 8 fpos a)).
{ apply (akept_trans SK pa_segs B LAWS pa_segs_low lyc Sc W memc Sc W (ms_mem ms0) W mem2 (spZ regs - KERNEL_AK)
    (spZ regs) (sp1 - ESTACK) sp1 (fun _ => False) (fun _ => False) _);
  [rewrite HK; lia | lia | exact AK1 | exact AKC | rewrite HK, HES; lia | lia | intros; assumption | intros; assumption
  | intros a [] | intros a []]. }
assert (AK : akept pa_segs B lyc Sc W memc W mem4 (spZ regs - KERNEL_AK) (spZ regs)
  (fun a => kE cx a \/ aside_rng lyc 8 fpos a)).
{ apply (akept_step SK pa_segs B LAWS pa_segs_low lyc Sc W memc mdc W mem2 W mem4 (spZ regs - KERNEL_AK) (spZ regs)
    (fun a => kE cx a \/ aside_rng lyc 8 fpos a) (fun a => kE cx a \/ aside_rng lyc 8 fpos a) (fun a => (spZ regs - 4640 <= a < spZ regs) \/ (F <= a < F + 16384) \/
                  (shadow_addr F <= a < shadow_addr F + 2048)) HAR0);
  [rewrite HK; lia | lia | exact AK2 | exact UNP | intros a _ Hp; exact (PP a Hp) | intros a Ha; exact Ha | ].
  intros a [Ha | [Ha | Ha]].
  - right. rewrite HK. exact Ha.
  - left. right. unfold aside_rng, in_zr, frame_rng. cbn [fst snd]. left. rewrite Hfb8. exact Ha.
  - left. right. unfold aside_rng, in_zr. cbn [fst snd]. right. left. rewrite Hfb8. exact Ha. }
(* registers of the end state *)
prreg HS (Z_to_bv 5 2) Rg2. prreg HS (Z_to_bv 5 9) Rg9. prreg HS (Z_to_bv 5 8) Rg8. prreg HS (Z_to_bv 5 3) Rg3.
prreg HS (Z_to_bv 5 4) Rg4. prreg HS (Z_to_bv 5 18) Rg18. prreg HS (Z_to_bv 5 20) Rg20.
prreg HS (Z_to_bv 5 19) Rg19. prreg HS (Z_to_bv 5 21) Rg21. prreg HS (Z_to_bv 5 22) Rg22.
assert (Z33 : ew E5 33 = Z_to_bv 64 sp1) by (rewrite <- Y33; symmetry; apply Z_to_bv_bv_unsigned).
assert (Z38 : ew E5 38 = Z_to_bv 64 F) by (rewrite <- Y38; symmetry; apply Z_to_bv_bv_unsigned).
assert (Z600 : ew E5 600 = Z_to_bv 64 (shadow_addr F)) by (rewrite <- Y600; symmetry; apply Z_to_bv_bv_unsigned).
assert (ZR : forall i (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  ew E5 i = Z_to_bv 64 (bv_unsigned (getr regs r))) by (intros i r Hi Hr; rewrite Z_to_bv_bv_unsigned; exact (EREG i r Hi Hr)).
(* the regions of the end state: 0 = F's shadow [0x206, 0x226), 1 = F's shadow [0, 4), 2 = F's header,
   3 = the spill slots at s1, 4 = the saved words *)
spregion HS 0%nat HR0. spregion HS 1%nat HR1. spregion HS 2%nat HR2. spregion HS 3%nat HR3. spregion HS 4%nat HR4.
lazymatch type of HR0 with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
  assert (IN0 : forall j, (j < 32)%nat ->
    In (YP09.mkChunk (518 + Z.of_nat j) (CVal 1 (SLit 18446744073709551602))) cs)
    by (intros j Hj; do 32 (destruct j as [|j]; [cbn; repeat (first [left; reflexivity | right]) |]); lia) end.
lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion _ _ _ _ _ ?cs) =>
  assert (IN1 : forall j, (j < 4)%nat -> In (YP09.mkChunk (Z.of_nat j) (CVal 1 (SLit 18446744073709551601))) cs)
    by (intros j Hj; do 4 (destruct j as [|j]; [cbn; repeat (first [left; reflexivity | right]) |]); lia) end.
(* ---- the cut ---- *)
apply (HNEXT cx fpos k lyc S2 W (mkst regs4 (Z_to_bv 64 (BASE + 7416)) mem4 (seg_rom pa_segs)) md4 HB0 HJ4 Hfr2).
unfold kin_poison, kat.
split.
(* kms *)
{ destruct (ms_shape_mkst pa_segs (mkst regs4 (Z_to_bv 64 (BASE + 7416)) mem4 (seg_rom pa_segs)) regs4 _ mem4 eq_refl)
    as (M1 & M2 & M3 & M4 & M5 & M6).
  unfold kms. rewrite M1, M2, M3, M4, M5, M6. repeat split; reflexivity. }
split.
(* kregs0 *)
{ unfold kregs0. change (ksp1 cx) with sp1. change (ksp cx) with (spZ regs). change (k_regs cx) with regs.
  change (ka0 cx) with (aarg regs 0). cbn [ms_regs mkst].
  split; [etransitivity; [exact Rg2|]; exact Z33|].
  split; [etransitivity; [exact Rg9|]; exact Z33|].
  split; [etransitivity; [exact Rg8|]; unfold w64, spZ; apply ZR; [lia | reflexivity]|].
  split; [etransitivity; [exact Rg3|]; transitivity (Z_to_bv 64 (bv_unsigned (getr regs 3)));
          [apply ZR; [lia | reflexivity] | apply Z_to_bv_bv_unsigned]|].
  split; [etransitivity; [exact Rg4|]; transitivity (Z_to_bv 64 (bv_unsigned (getr regs 4)));
          [apply ZR; [lia | reflexivity] | apply Z_to_bv_bv_unsigned]|].
  split; [etransitivity; [exact Rg18|]; unfold w64, aarg, argZ; apply ZR; [lia | reflexivity]|].
  etransitivity; [exact Rg20|]. exact Y32. }
split.
(* kregs_eq *)
{ unfold kregs_eq. change (kF cx fpos) with F. change (kFSH cx fpos) with (shadow_addr F).
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ms_regs mkst].
  - etransitivity; [exact Rg19|]. exact Z38.
  - etransitivity; [exact Rg21|]. exact Z38.
  - etransitivity; [exact Rg22|]. exact Z600. }
split.
(* ksaved *)
{ unfold ksaved. change (ksp cx) with (spZ regs). change (k_regs cx) with regs. cbn [ms_mem mkst].
  split.
  - replace (spZ regs - 8) with (spZ regs + -8) by lia.
    apply (ke_rd_of_region E5 (w_H W) mem4 2 (spZ regs) _ _ _ _ _ (-8) (SOff 1 0) (raZ regs) HR4 Y2).
    + cbn. repeat (first [left; reflexivity | right]).
    + apply sv_off0. unfold raZ. apply ZR; [lia | reflexivity].
    + unfold raZ. apply getr_rng.
  - intros j Hj.
    replace (spZ regs - 16 - 8 * j) with (spZ regs + (-16 - 8 * j)) by lia.
    apply (ke_rd_of_region E5 (w_H W) mem4 2 (spZ regs) _ _ _ _ _ (-16 - 8 * j)
             (SOff (Z.to_nat (if j <? 2 then 8 + j else 16 + j)) 0) _ HR4 Y2).
    + assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/
                    j = 10 \/ j = 11) by lia.
      destruct Hj' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]];
        cbn; repeat (first [left; reflexivity | right]).
    + apply sv_off0. apply ZR; [destruct (j <? 2); lia|].
      rewrite Z2Nat.id by (destruct (j <? 2); lia).
      assert (Hj' : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7 \/ j = 8 \/ j = 9 \/
                    j = 10 \/ j = 11) by lia.
      destruct Hj' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]; reflexivity.
    + apply getr_rng. }
split.
(* kframe *)
{ unfold kframe. change (kF cx fpos) with F. change (kFL cx fpos) with (flag_addr lyc 8 fpos).
  change (kFSH cx fpos) with (shadow_addr F). change KN_CID with 8%Z. cbn [ms_mem mkst].
  split.
  { pose proof (ke_rd_of_region E5 (w_H W) mem4 38 F _ _ _ _ _ 0 (SLit 1102416563) KN_MAGIC HR2 Y38
      ltac:(cbn; repeat (first [left; reflexivity | right])) eq_refl ltac:(unfold KN_MAGIC; lia)) as Hx.
    rewrite Z.add_0_r in Hx. exact Hx. }
  split.
  { apply (ke_rd_of_region E5 (w_H W) mem4 38 F _ _ _ _ _ 8 (SOff (A_OBJ 13) 0) _ HR2 Y38).
    + cbn. repeat (first [left; reflexivity | right]).
    + apply sv_off0. apply YO. lia.
    + rewrite V13. lia. }
  split.
  { apply (ke_rd_of_region E5 (w_H W) mem4 38 F _ _ _ _ _ 16 (SOff (A_OBJ 14) 0) _ HR2 Y38).
    + cbn. repeat (first [left; reflexivity | right]).
    + apply sv_off0. apply YO. lia.
    + rewrite V14. lia. }
  split.
  { rewrite (kk_rdword_agree (aview pa_segs (w_H W) mem2) (aview pa_segs (w_H W) mem4)); [exact Hflag|].
    intros i Hi. rewrite Hfb8. apply UNS; [lia|]. rewrite HshF. unfold SHADOW_OFF in *. lia. }
  split.
  { intros a Ha. apply PP. apply HFpres. rewrite Hfb8 in Ha. lia. }
  intros a Ha. apply PP. rewrite Hfb8 in Ha. change (16384 / 8) with 2048 in Ha.
  replace a with (shadow_addr F + (a - shadow_addr F)) by lia. apply HFshpres. rewrite ?HshF; lia. }
split.
(* kshadow *)
{ unfold kshadow. change (kFSH cx fpos) with (shadow_addr F). cbn [ms_mem mkst].
  intros i Hi. rewrite kfsh_length in Hi. rewrite kn_kfsh_nth.
  destruct (Nat.ltb_spec i 4) as [H4|H4].
  { exact (ke_byte_of_region E5 (w_H W) mem4 600 (shadow_addr F) _ _ _ _ _ (Z.of_nat i) 18446744073709551601
      HR1 Y600 (IN1 i H4) ltac:(lia)). }
  destruct (Nat.ltb_spec i 518) as [H518|H518].
  { rewrite (Hkeep4 (shadow_addr F + Z.of_nat i)) by (rewrite ?HshF; unfold SHADOW_OFF in *; lia).
    rewrite (UN5 (shadow_addr F + Z.of_nat i)) by (cbv beta; rewrite ?HshF; unfold SHADOW_OFF in *; lia).
    replace (shadow_addr F + Z.of_nat i) with (shadow_addr F + 4 + (Z.of_nat i - 4)) by lia.
    apply Hf8a. lia. }
  destruct (Nat.ltb_spec i 550) as [H550|H550].
  { replace (Z.of_nat i) with (518 + Z.of_nat (i - 518)) by lia.
    exact (ke_byte_of_region E5 (w_H W) mem4 600 (shadow_addr F) _ _ _ _ _ (518 + Z.of_nat (i - 518))
      18446744073709551602 HR0 Y600 (IN0 (i - 518)%nat ltac:(lia)) ltac:(lia)). }
  destruct (Nat.ltb_spec i 1064) as [H1064|H1064].
  { replace (shadow_addr F + Z.of_nat i) with (shadow_addr F + 550 + (Z.of_nat i - 550)) by lia.
    apply Hf8b. lia. }
  destruct (Nat.ltb_spec i 1096) as [H1096|H1096]; [|lia].
  rewrite (UNS (shadow_addr F + Z.of_nat i)) by (rewrite ?HshF; unfold SHADOW_OFF in *; lia).
  change (shadow_of_addr SHADOW_OFF F) with (shadow_addr F) in Hzs.
  replace (Z.of_nat i) with (Z.of_nat i) by reflexivity.
  apply Hzs. change (8768 / 8) with 1096. lia. }
split.
(* kslots_eq *)
{ unfold kslots_eq. change (ksp1 cx) with sp1. change (kFSH cx fpos) with (shadow_addr F). change (kF cx fpos) with F.
  repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd ms_mem mkst].
  - apply (ke_rd_of_region E5 (w_H W) mem4 33 sp1 _ _ _ _ _ KS_W1SH (SOff 600 4) (shadow_addr F + 4) HR3 Y33).
    + cbn. repeat (first [left; reflexivity | right]).
    + cbn [sv_denot]. rewrite Y600. reflexivity.
    + rewrite HshF; unfold SHADOW_OFF in *; lia.
  - apply (ke_rd_of_region E5 (w_H W) mem4 33 sp1 _ _ _ _ _ KS_W2SH (SOff 600 550) (shadow_addr F + 0x226) HR3 Y33).
    + cbn. repeat (first [left; reflexivity | right]).
    + cbn [sv_denot]. rewrite Y600. reflexivity.
    + rewrite HshF; unfold SHADOW_OFF in *; lia.
  - apply (ke_rd_of_region E5 (w_H W) mem4 33 sp1 _ _ _ _ _ KS_F2 (SOff 38 0) F HR3 Y33).
    + cbn. repeat (first [left; reflexivity | right]).
    + apply sv_off0. exact Z38.
    + lia. }
split; [exact KJ|].
split.
(* kkept *)
{ split; [exact AK|]. intros a Hro Hno Her. cbn [ms_mem mkst]. rewrite (KRO a Hro Hno Her). exact (HROD a Hro Hno Her). }
split.
(* kcursor *)
{ unfold kcursor. change (k_wn cx) with wn. change (k_wp cx) with wp. change (ka0 cx) with (aarg regs 0).
  cbn [ms_mem mkst].
  assert (CUR : forall i, 0 <= i < 16 ->
    aview pa_segs (w_H W) mem4 (aarg regs 0 + i) = aview pa_segs (w_H W) memc (aarg regs 0 + i))
    by (intros i Hi; apply KARD; left; lia).
  split; [lia|]. split; [|split].
  - rewrite Z.add_0_r. apply (val_mem_moved pa_segs (w_H W) (w_H W) memc mem4 (aarg regs 0) (aarg regs 0) 8 wp);
      [|exact HWP]. intros i Hi. apply CUR. cbn in Hi. lia.
  - rewrite Z.sub_0_r.
    apply (val_mem_moved pa_segs (w_H W) (w_H W) memc mem4 (aarg regs 0 + 8) (aarg regs 0 + 8) 8 wn); [|exact HWN].
    intros i Hi. cbn in Hi. replace (aarg regs 0 + 8 + i) with (aarg regs 0 + (8 + i)) by lia. apply CUR. lia.
  - intros i Hi. apply kn_writable_of_view.
    + destruct (kn_ard_bound SK B LAWS cx (aarg regs 0 + i) HB0 ltac:(left; change (k_regs cx) with regs; lia))
        as (Hb & _). lia.
    + rewrite CUR by lia. unfold aview.
      destruct (Z_lt_le_dec i 8) as [Hi8|Hi8].
      * pose proof (HWP (Z.to_nat i) ltac:(lia)) as Hm. rewrite Z2Nat.id in Hm by lia. rewrite Hm. discriminate.
      * pose proof (HWN (Z.to_nat (i - 8)) ltac:(lia)) as Hm. rewrite Z2Nat.id in Hm by lia.
        replace (aarg regs 0 + 8 + (i - 8)) with (aarg regs 0 + i) in Hm by lia. rewrite Hm. discriminate.
    + apply HWRO. exists (aarg regs 0, aarg regs 0 + 16). split; [cbn; right; right; left; reflexivity | cbn; lia]. }
split.
(* g_nl: the entry's *)
{ cbn [kgnl_at ms_mem mkst]. change (k_kbs cx) with kbs.
  pose proof HNK as ((HNa & HNw) & HNl). split; [split|exact HNl].
  - apply (kk_abytes_keep pa_segs (w_H W) (w_H W) memc mem4 LA_G_NL kbs); [|exact HNa].
    intros i Hi. apply KARD. right; right; left. rewrite HNl in Hi. lia.
  - intros i Hi. rewrite HNl in Hi.
    apply (writable_at_of_wseg pa_segs _ LA_G_NL NK_SIZE); [unfold LA_G_NL; lia | unfold LA_G_NL, NK_SIZE; lia
      | exact (ki_gnl_wseg _ _ KI) | lia]. }
(* long_alias: the entry's *)
{ cbn [ms_mem mkst]. exists la. split; [|exact HLAL]. destruct HLA as (HLb & HLw). split.
  - apply (kk_abytes_keep pa_segs (w_H W) (w_H W) memc mem4 LA_LONG_ALIAS (la ++ [zb 0])); [|exact HLb].
    intros i Hi. rewrite length_app in Hi. cbn [length] in Hi. apply KARD.
    repeat (first [left; unfold LONG_ALIAS_SIZE; lia | right]).
  - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
    apply (writable_at_of_wseg pa_segs _ LA_LONG_ALIAS LONG_ALIAS_SIZE); [unfold LA_LONG_ALIAS; lia
      | unfold LA_LONG_ALIAS, LONG_ALIAS_SIZE; lia | exact (ki_la_wseg _ _ KI) | unfold LONG_ALIAS_SIZE; lia]. }
Qed.

End b.
End a.

Print Assumptions kn_entry.
