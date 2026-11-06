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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 1440 of its 1488 lines of code are new or changed and 405 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s18.v, with its module paths and module names changed; 158 of its 203 lines of code are new or changed and 1443 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A: the harness walk of group G1 (the G1 harness walk), pb_LLVMFuzzerTestOneInput
   (lib/A/Prog/LLVMFuzzerTestOneInput.v), at image A's listing instance PI := SegImg.PB_seg, the sink head
   AE2k.tfib_sink_head, the trivial meter MT := YCbp.ameter_triv and an allocator record B with HB : AF0m.SegBSyms B, with
   every premise discharged that the landed text allows (the walk's Arguments order and rows: the G1 lane's
   WALK-HYPOTHESES.md):
   - record and listing facts, each from one lemma: TL / TLF / ML / PRW (SegRecRest seg_palib / seg_palibf /
     seg_model_laws / seg_prw_tfib at B HB), VOBJS / SIGP (seg_val_objs_PB / seg_sig_prog_PB), ASF / FFL
     (seg_astack_free_law / seg_frame_flag_law), BSYM := HB, the meter laws MTL / MTFL (kit YCbp.ameter_triv_laws /
     ameter_triv_fs_laws);
   - image facts from IMG := SegRecImg.seg_img_facts_tfib B HB: IMGS (mkS10Img from cif_relro_img and cif_guard_rom),
     HPGS (ts_prog and cif_prog_img), HPG_RO (cif_prog_not_ro), MCR (cif_snl_rom for the read-only half,
     SegHimgA.unowned_of_b by computation for the unowned / not-errno half);
   - image numbers by computation: cstk := 18576 with HCSTK (336 + 18576 <= 32768), snp_lo := 0x10000,
     snp_hi := kImgEnd with HSNP_LO, HSNP_CEIL (kImgEnd <= alloc_ceiling), HSNP_LIT (the four harness literals lie in
     [0x10000, gotwA)), HPG_PTR (every m_key.words and catalogue pointer is below longlA - 65536, read from the image's
     own bytes), and HSNP_FAKE from the kit: AR's layout_ok puts the image hull below the fake stack
     (YG0t.hull_below_F) and PB_seg's pa_img_cover puts kImgEnd inside the hull.
   What is left are Section hypotheses of exactly the walk's own texts: the runtime rows not yet closed (side stack
   class 3, malloc / free rules, memchr, strrchr, the checked memcpy / memset, strlen, strcmp, calloc at window 18576,
   snprintf at 0x10000 / kImgEnd / snp_cr with HSNP_CR, set_shadow f5) and the 21 callee contracts, which
   lib/A/Prog/SegProgClosed.v discharges from the groups' closures at the core's record SegB.
   The walk is the G1 harness walk at bd12cd505428 (= 124c1c45c8bc with its comments cleaned),
   merged into this close; FINAL 6f783602b5e3 is an ancestor (checked). This file states no
   contract: the lemma's statement is LLVMFuzzerTestOneInput_contract at contracts FINAL 6f783602b5e3, at SegInstA's
   terms, as the walk states it.
   proves no function (kind: merge; the instantiation of G1's walk theorem). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK14 YK0s YK15 YP09 YI04 YI09 YN3v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI00 YC5d YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YCbp YG0t YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable SegSyms SegList SegPa SegGlob
  SegPaLib PaLibF SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtShadow RtSegCalloc RtSeg RtPFSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require AF0m AE2k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import reac_segconf_init_c check_refusals_c
  check_address_c check_knock_refused_c reac_segconf_declared_c check_declared_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import check_segments_c reac_segconf_role_c
  check_role_c reac_segconf_model_c check_model_c reac_segconf_ignored_c check_ignore_c reac_segconf_role_file_c
  reac_segconf_ignore_file_c check_provenance_c reac_segconf_parse_c m_refuse_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require m_find_c check_absent_c m_file_c
  reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s10k LLVMFuzzerTestOneInput_s14k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegImg SegRecBase SegRecRest SegRecImg SegHimgA
  LLVMFuzzerTestOneInput.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section g1. Context {rc : YM05.RunCeil}.
#[local] Existing Instance AE2k.tfib_sink_head | 0.
#[local] Notation PB := SegImg.PB_seg.
#[local] Notation SEGS := (@pa_segs _ seg_listing SegImg.PB_seg).
#[local] Notation BASE := (@pa_val _ seg_listing SegImg.PB_seg A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing SegImg.PB_seg s).
Variable B : asyms.
Hypothesis HB : AF0m.SegBSyms B.

(* ---- the runtime rows not yet closed (the walk's own texts, at MT := YCbp.ameter_triv, cstk := 18576,
   snp_lo := 0x10000, snp_hi := kImgEnd) ---- *)
Hypothesis SM3 : forall fx0 : YK11.FPState, @astack_malloc_realizes fx0 rc SEGS B 3.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc AE2k.tfib_sink_head SEGS B YCbp.ameter_triv.
Hypothesis AFREE4 : forall fx0 : YK11.FPState, afree04_rule (fx := fx0) SEGS B YCbp.ameter_triv.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  MemchrDef.amemchr_realizesM (fx := fx0) SEGS B memchr_loA memchr_hiA (SIG SS___interceptor_trampoline_memchr).
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strrchr).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState,
  @RtString.astrlen_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strlen).
Hypothesis ASTRCMP : forall fx0 : YK11.FPState,
  @RtString.astrcmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcmp).
Hypothesis ACALLOC4 : forall fx0 : YK11.FPState,
  @RtSegCalloc.aseg_calloc04_rule fx0 rc AE2k.tfib_sink_head SEGS B YCbp.ameter_triv
    (SIG SS___interceptor_trampoline_calloc) 18576.
Variable snp_cr : list (Z * Z).
Hypothesis ASNPRINTF : forall fx0 : YK11.FPState,
  @RtPFSeg.seg_asnprintf_realizes fx0 rc SEGS B 0x10000 kImgEnd snp_cr (SIG SS___interceptor_trampoline_snprintf)
    gotwA guardA.
Hypothesis HSNP_CR : Forall (fun r => 0x10000 <= fst r /\ 0 <= snd r /\ fst r + snd r <= kImgEnd) snp_cr.
Hypothesis SHF5 : forall fx0 : YK11.FPState,
  @RtShadow.aset_shadow_realizes fx0 rc SEGS B (SIG SS___asan_set_shadow_f5) 0xf5.

(* ---- the 21 callee contracts (the walk's own texts) ---- *)
Hypothesis HINIT : forall fx0 : YK11.FPState,
  @reac_segconf_init_contract fx0 rc AE2k.tfib_sink_head SEGS B (BASE + AF_reac_segconf_init) STK_reac_segconf_init.
Hypothesis HCR : forall fx0 : YK11.FPState,
  check_refusals_contract (fx := fx0) SEGS B (BASE + AF_check_refusals) STK_check_refusals.
Hypothesis HCA : forall fx0 : YK11.FPState,
  check_address_contract (fx := fx0) SEGS B (BASE + AF_check_address) STK_check_address RLO_A RHI_A.
Hypothesis HCK : forall fx0 : YK11.FPState,
  check_knock_refused_contract (fx := fx0) SEGS B (BASE + AF_check_knock_refused) STK_check_knock_refused
    RLO_A RHI_A seg_litA_fz gotwA guardA.
Hypothesis HDECL : forall fx0 : YK11.FPState, reac_segconf_declared_contract (fx := fx0) SEGS B
  (BASE + AF_reac_segconf_declared) STK_reac_segconf_declared RLO_A RHI_A gotwA guardA.
Hypothesis HCHKD : forall fx0 : YK11.FPState, check_declared_contract (fx := fx0) SEGS B
  (BASE + AF_check_declared) STK_check_declared RLO_A RHI_A.
Hypothesis HCSEG : forall fx0 : YK11.FPState,
  check_segments_contract (fx := fx0) SEGS B (BASE + AF_check_segments) STK_check_segments RLO_A RHI_A.
Hypothesis HROLE : forall fx0 : YK11.FPState,
  reac_segconf_role_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role) STK_reac_segconf_role RLO_A RHI_A.
Hypothesis HCROLE : forall fx0 : YK11.FPState,
  check_role_contract (fx := fx0) SEGS B (BASE + AF_check_role) STK_check_role.
Hypothesis HMODEL : forall fx0 : YK11.FPState,
  reac_segconf_model_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_model) STK_reac_segconf_model RLO_A RHI_A.
Hypothesis HCMODEL : forall fx0 : YK11.FPState,
  check_model_contract (fx := fx0) SEGS B (BASE + AF_check_model) STK_check_model RLO_A RHI_A.
Hypothesis HIGNORED : forall fx0 : YK11.FPState,
  reac_segconf_ignored_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignored) STK_reac_segconf_ignored RLO_A RHI_A.
Hypothesis HCIGNORE : forall fx0 : YK11.FPState,
  check_ignore_contract (fx := fx0) SEGS B (BASE + AF_check_ignore) STK_check_ignore.
Hypothesis HROLEFILE : forall fx0 : YK11.FPState,
  reac_segconf_role_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_role_file) STK_reac_segconf_role_file
    RLO_A RHI_A.
Hypothesis HIGNFILE : forall fx0 : YK11.FPState,
  reac_segconf_ignore_file_contract (fx := fx0) SEGS B (BASE + AF_reac_segconf_ignore_file) STK_reac_segconf_ignore_file
    RLO_A RHI_A.
Hypothesis HCPROV : forall fx0 : YK11.FPState,
  check_provenance_contract (fx := fx0) SEGS B (BASE + AF_check_provenance) STK_check_provenance RLO_A RHI_A.
Hypothesis HPARSE : forall fx0 : YK11.FPState, reac_segconf_parse_contract (fx := fx0) SEGS B
  (BASE + AF_reac_segconf_parse) STK_reac_segconf_parse RLO_A RHI_A seg_litA_rc catA gotwA guardA.
Hypothesis HM_FIND : forall fx0 : YK11.FPState,
  @m_find_c.m_find_contract fx0 rc AE2k.tfib_sink_head SEGS B (BASE + AF_m_find) STK_m_find RLO_A RHI_A.
Hypothesis HCHECK_ABSENT : forall fx0 : YK11.FPState,
  @check_absent_c.check_absent_contract fx0 rc AE2k.tfib_sink_head SEGS B (BASE + AF_check_absent) STK_check_absent
    RLO_A RHI_A.
Hypothesis MREF : forall fx0 : YK11.FPState,
  @m_refuse_contract fx0 rc AE2k.tfib_sink_head SEGS B (BASE + AF_m_refuse) STK_m_refuse RLO_A RHI_A seg_litA_fz
    gotwA guardA.
Hypothesis HM_FILE : forall fx0 : YK11.FPState,
  @m_file_c.m_file_contract fx0 rc AE2k.tfib_sink_head SEGS B (BASE + AF_m_file) STK_m_file RLO_A RHI_A seg_litA_fz
    wordsA rolesA catA gotwA guardA.
Hypothesis HPARSE_FILE : forall fx0 : YK11.FPState,
  @reac_segconf_parse_file_c.reac_segconf_parse_file_contract fx0 rc AE2k.tfib_sink_head SEGS B
    (BASE + AF_reac_segconf_parse_file) STK_reac_segconf_parse_file RLO_A RHI_A seg_litA_rc catA gotwA guardA.

(* ---- the record, listing and image facts ---- *)
Lemma g1_img : SegRecBase.seg_img_facts SEGS B.
Proof. exact (SegRecImg.seg_img_facts_tfib B HB). Qed.
Lemma g1_IMGS : s10_img (PI := PB).
Proof. constructor; [exact (SegRecBase.cif_relro_img _ _ g1_img) | exact (SegRecBase.cif_guard_rom _ _ g1_img)]. Qed.
Lemma g1_MCR : s14_memchr_rom SEGS B.
Proof.
intros a Ha. split; [exact (SegRecBase.cif_snl_rom _ _ g1_img a Ha)|].
apply (SegHimgA.unowned_of_b B HB memchr_loA (memchr_hiA - memchr_loA));
  [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.
Lemma g1_HPGS : forall a, inFP (ltoi_PG longlA) a -> Exists (in_zr a) (as_prog_static B) /\ in_img SEGS a.
Proof.
intros a Ha. split.
- rewrite (AF0m.ts_prog B HB). unfold AF0m.TFIB_PROG_STATIC.
  destruct Ha as (r & Hr & Hra). unfold ltoi_PG in Hr. destruct Hr as [<-|[]]. cbn [fst snd] in Hra.
  apply Exists_cons_hd. unfold in_zr. cbn [fst snd].
  unfold longlA, SegGlob.A_LONGL, LLVMFuzzerTestOneInput_c.LONGL_N in Hra. lia.
- exact (SegRecBase.cif_prog_img _ _ g1_img a Ha).
Qed.
Lemma g1_HPG_RO : forall a, inFP (ltoi_PG longlA) a -> ~ in_roP SEGS RLO_A RHI_A a.
Proof. intros a Ha. exact (SegRecBase.cif_prog_not_ro _ _ g1_img a Ha). Qed.
(* the pointers m_file and parse_file read from m_key.words and the box table, from the image's own bytes *)
Definition g1_ptr_ok (a : Z) : bool :=
  match rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a with
  | Some p => p + 65536 <=? longlA
  | None => true
  end.
Lemma g1_ptr_words : forallb (fun i => g1_ptr_ok (wordsA + 8 * Z.of_nat i)) (seq 0 5) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma g1_ptr_cat : forallb (fun i => g1_ptr_ok (pin_spec.row_addr catA i)) (seq 0 pin_spec.CAT_N) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma g1_HPG_PTR : forall a p,
  ((exists i, (i < 5)%nat /\ a = wordsA + 8 * Z.of_nat i) \/
   (exists i, (i < pin_spec.CAT_N)%nat /\ a = pin_spec.row_addr catA i)) ->
  rdword (fun x => option_map (fun b : byte => bv_unsigned b) (seg_rom SEGS (Z_to_bv 64 x))) a = Some p ->
  p + 65536 <= longlA.
Proof.
intros a p [[i [Hi ->]]|[i [Hi ->]]] Hrd.
- pose proof (proj1 (forallb_forall _ _) g1_ptr_words i ltac:(apply in_seq; lia)) as H.
  unfold g1_ptr_ok in H. rewrite Hrd in H. apply Z.leb_le. exact H.
- pose proof (proj1 (forallb_forall _ _) g1_ptr_cat i ltac:(apply in_seq; lia)) as H.
  unfold g1_ptr_ok in H. rewrite Hrd in H. apply Z.leb_le. exact H.
Qed.
Lemma g1_HCSTK : 0 <= 18576 /\ LTOI_FRAME_MAX + 18576 <= STK_LLVMFuzzerTestOneInput.
Proof. split; [lia | apply Z.leb_le; vm_compute; reflexivity]. Qed.
Lemma g1_HSNP_LIT : forall x, In x LLVMFuzzerTestOneInput_c.LTOI_LITS ->
  0x10000 <= seg_litA_fz x /\ seg_litA_fz x + Z.of_nat (length x) + 1 <= gotwA.
Proof.
assert (Hb : forallb (fun x => (0x10000 <=? seg_litA_fz x) && (seg_litA_fz x + Z.of_nat (length x) + 1 <=? gotwA))
  LLVMFuzzerTestOneInput_c.LTOI_LITS = true) by (vm_compute; reflexivity).
intros x Hx. pose proof (proj1 (forallb_forall _ _) Hb x Hx) as H. apply andb_prop in H as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. split; assumption.
Qed.
Lemma g1_HSNP_LO : 0 <= 0x10000.
Proof. lia. Qed.
(* alloc_ceiling is the run ceiling's (YM05.RunCeil); its law puts it at or above CEIL_MIN, which is above kImgEnd *)
Lemma g1_HSNP_CEIL : kImgEnd <= alloc_ceiling.
Proof.
pose proof (@YM05.alloc_ceiling_value rc) as [[H _] _].
assert (E : kImgEnd <= YM05.CEIL_MIN) by (apply Z.leb_le; vm_compute; reflexivity).
lia.
Qed.
Lemma g1_HSNP_FAKE : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> kImgEnd <= ly_F ly.
Proof.
intros ly S W mem md HAR. destruct HAR as [HM [HL _]].
assert (LO : layout_ok ly) by (eapply am_layout; exact HM).
assert (H1 : fst (ly_img ly) + snd (ly_img ly) <= ly_F ly)
  by first [exact (YG0t.hull_below_F ly LO) | exact (YG0t.hull_below_F B ly LO)].
pose proof (@pa_img_cover _ seg_listing SegImg.PB_seg ly S md HL) as [_ H2].
lia.
Qed.

(* ---- the harness's closure ---- *)
Corollary cl_LLVMFuzzerTestOneInput : forall fx0 : YK11.FPState,
  @LLVMFuzzerTestOneInput_contract fx0 rc AE2k.tfib_sink_head SEGS B YCbp.ameter_triv
    (BASE + AF_LLVMFuzzerTestOneInput) STK_LLVMFuzzerTestOneInput emptyA RLO_A RHI_A longlA mod40A catA wordsA
    rolesA gotwA guardA seg_litA_fz seg_litA_rc.
Proof.
intros fx0.
exact (@LLVMFuzzerTestOneInput.pb_LLVMFuzzerTestOneInput fx0 rc AE2k.tfib_sink_head PB B YCbp.ameter_triv
  (SegRecRest.seg_palib B HB) (SegRecRest.seg_palibf B HB) g1_IMGS HB g1_MCR g1_HPGS g1_HPG_RO g1_HPG_PTR
  (SegRecRest.seg_prw_tfib B HB) SegRecRest.seg_val_objs_PB SegRecRest.seg_sig_prog_PB
  (SegRecRest.seg_model_laws B HB) YCbp.ameter_triv_laws YCbp.ameter_triv_fs_laws SM3
  (SegRecRest.seg_astack_free_law B) (SegRecRest.seg_frame_flag_law B) AMALLOC4 AFREE4 AMEMCHR ASTRRCHR
  AMEMCPY AMEMSET ASTRLEN ASTRCMP 18576 g1_HCSTK ACALLOC4 0x10000 kImgEnd snp_cr ASNPRINTF g1_HSNP_LIT HSNP_CR
  g1_HSNP_LO g1_HSNP_CEIL g1_HSNP_FAKE SHF5 HINIT HCR HCA HCK HDECL HCHKD HCSEG HROLE HCROLE HMODEL HCMODEL
  HIGNORED HCIGNORE HROLEFILE HIGNFILE HCPROV HPARSE HM_FIND HCHECK_ABSENT MREF HM_FILE HPARSE_FILE).
Qed.
End g1.

About cl_LLVMFuzzerTestOneInput.
Print Assumptions cl_LLVMFuzzerTestOneInput.
