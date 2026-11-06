(* The closing composition of libreac/fuzz_grant's image B (fuzz_grant.asan-ubsan, bin/ sha256 fde52226dc48,
   unstripped twin 5a5ee7c02b4e): the entry contract tb_LLVMFuzzerTestOneInput_spec of lib/B/Prog/GrantBContracts.v,
   composed BOTTOM-UP from the walk statements walk_<f> of that file. This file proves no function: it composes
   walks and walks none.

   The shape is grant image A's lib/A/GrantTop.v (a working branch 7d31e8f3534):
   - every PROVED walk is plugged in by its theorem `pb_<f> : walk_<f> B` (three in GrantBContracts.v itself, the
     others in the walk files under lib/B/Prog), never as a hypothesis;
   - every still-OPEN walk is ONE named Section hypothesis `PB_<f> : walk_<f> ... B`, with the statement its owner's
     file (GrantBContracts.v) gives; nothing is restated;
   - every runtime or image fact (the conjuncts of the hyps_<f> of GrantBContracts.v) is ONE named Section
     hypothesis, stated once, and every hyps_<f> is built from those names (hyps_<f>_B below); the two conjuncts
     that are closed facts of image B (IMG_RO_BELOW, IMG_CTRL_ROW_IMG) are proved here by computation instead;
   - each callee hypothesis of a walk_<f> is discharged by that callee's composed contract tb_<g>_holds_B.
   The call graph (from the walk_<f> statements; no cycle):
     LLVMFuzzerTestOneInput -> reac_headamp_tx_init, reac_headamp_tx_set, reac_headamp_tx_effective,
       reac_headamp_default, reac_grant_alloc_fits, reac_grant_allocate, reac_grant_build_sweep, want_of,
       check_groupa, reac_ctrl_identity_poll_block, reac_headamp_tx_arm_scene, reac_headamp_tx_set_resweep,
       reac_headamp_tx_next
     reac_headamp_tx_next -> reac_headamp_tx_effective          want_of -> reac_headamp_default
     reac_grant_build_sweep -> reac_headamp_tx_effective, reac_ctrl_build_grant_sweep
     reac_ctrl_build_grant_sweep -> reac_ctrl_stamp_headamp -> ctrl_lay_block, ctrl_finish
     ctrl_finish -> reac_ctrl_record_cksum_stamp, reac_ctrl_block_cksum_stamp
     check_groupa -> reac_ctrl_parse, reac_headamp_tx_effective, reac_ctrl_headamp_record_verify,
       reac_ctrl_checksum_verify            reac_ctrl_parse -> kind_of_link1
   asan.module_ctor and asan.module_dtor are the image's constructor / destructor (.init_array[0] / .fini_array[0]):
   no walk calls them, so they are not in the entry contract's composition, and this file takes neither (the
   statement owner's decision): the init and exit paths are discharged inside the B core, as on
   image A (see INIT AND EXIT PATHS after tb_LLVMFuzzerTestOneInput_holds_B).

   THE SINK INSTANCE IS EXPLICIT (image A's rule, lib/A/GrantTop.v): SK is image B's own sink head,
   grantB_sink_head, whose overflow head is image B's `ofl_head` 0x5f9008. The plain build's sink hints are removed,
   and every walk, contract and fact below names `(SK := grantB_sink_head)` where its statement takes SK;
   sk_probe_is_asan_ubsan shows what a bare `sink_head` resolves to. The image is named the same way:
   `(PI := PI_grant)`, image B's PAImg instance (lib/B/Prog/GrantImg.v:152). The runtime's symbol record B : asyms
   and the two machine parameters fx / rc stay Section variables: they are parameters of the contract itself.

   Print Assumptions of the top (inside the Section, and again after it) lists exactly the open walks PB_<f>, the
   runtime and image facts RT_* / IMG_* that reach it, the three parameters fx, rc, B, and axioms of
   origin/ossv/recipes:toolchain/allowed-axioms.txt. *)

From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YN3g.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable.R Require Import Cfg.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo GrantImg GrantBContracts.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require
CtrlBlockCksumStamp CtrlRecordCksumStamp CtrlChecksumVerify CtrlHeadampRecordVerify CtrlIdentityPollBlock
CtrlFinish CtrlStampHeadamp CtrlParse CheckGroupa WantOf GrantAllocFits GrantAllocate CtrlLayBlock
HeadampTxArmScene HeadampTxEffective HeadampTxSet HeadampTxSetResweep HeadampTxNextClose LLVMFuzzerTestOneInput
GrantBuildSweepWalk GrantBTraces CtrlBuildGrantSweep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require YCej.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YI5b YI5c.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the sink: image B's own overflow head ---------------------------------------------------------------------
   0x5f9008 is the symbol `ofl_head` (musl ofl.c, OBJECT, 8 bytes) in the symbol table of image B's unstripped twin
   fuzz_grant.asan-ubsan
   (sha256 5a5ee7c02b4e2a1d1653dc0c256182c9b65c33dde3a7ddc98b9de2afffe7a417); `ofl_lock` is 0x5f9000. Image A's head
   (lib/A/AE2k.v A_ofl_head 0x5f81c8) is a different number and is not used here. The B core has no named constant
   for it yet; this is its twin of AE2k.v's A_ofl_head / tfib_sink_head. *)
Definition B_ofl_head : Z := 0x5f9008.
(* A plain Definition with a LOCAL instance: a file that Requires or Imports this one gets no sink_head instance from it
   and names the sink explicitly, as GrantBTFIB.v does. (Image A's head is `#[export] Instance tfib_sink_head`,
   lib/A/AE2k.v:35 on this branch; image B's is kept out of every other file's typeclass search.) *)
Definition grantB_sink_head : YI16.sink_head := {| YI16.sk_ofl_head := B_ofl_head |}.
#[local] Existing Instance grantB_sink_head.

(* The guard: the plain build's sink hints are out of the way, so no `{SK}` of a walk or of a contract can be filled
   with the plain build's head. *)
#[local] Remove Hints YI5b.src0_sink_head : typeclass_instances.
#[local] Remove Hints YI5c.src0_sink : typeclass_instances.

(* What a bare `sink_head` resolves to in this file: image B's own head (the twin of image A's sk_probe_is_asan). *)
Definition sk_probe : YI16.sink_head := _.
Lemma sk_probe_is_asan_ubsan : sk_probe = grantB_sink_head.
Proof. reflexivity. Qed.

(* ---- IMG_RO_BELOW, closed by computation ------------------------------------------------------------------------
   ro_below_ofl (lib/B/PaBase.v:27): every address of the read-only range lies below the sink's overflow head.
   On image B the read-only range is the two PT_LOADs that are not writable (they end at 0x2f984 and 0x9bfc8) and the
   RELRO range [0x9d000, 0x9e3c8) (GrantImg.v:89-90); all of it lies below 0x5f9008. The check runs over
   grantsegsB0's segment records. *)
Lemma ro_below_ofl_grantB : forall a, in_roP grantsegsB0 grant_relro_lo grant_relro_hi a -> a < B_ofl_head.
Proof.
  intros a [[s [Hin [Hw Ha]]] | Ha].
  - assert (HB : forallb (fun t => (seg_writable t || (Z.of_N (seg_base t) + Z.of_N (seg_size t) <=? B_ofl_head))%bool)
                   grantsegsB0 = true) by (vm_compute; reflexivity).
    rewrite forallb_forall in HB. specialize (HB s Hin). rewrite Hw in HB. cbn [orb] in HB.
    apply Z.leb_le in HB. lia.
  - unfold grant_relro_lo, grant_relro_hi in Ha. unfold B_ofl_head. lia.
Qed.

Section closeB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The runtime's symbol record of image B: a parameter of every contract of GrantBContracts.v. *)
Variable B : asyms.

(* ---- the runtime and image facts, one named hypothesis each (the conjuncts of the hyps_<f>) ------------------- *)
(* RT_LAWS: AR_laws: the runtime's state laws (GrantBContracts.v:333). *)
Hypothesis RT_LAWS : GrantBContracts.RT_LAWS (PI := PI_grant) B.
(* RT_PALIB: PALib: the walk layer's library facts (GrantBContracts.v:334). *)
Hypothesis RT_PALIB : GrantBContracts.RT_PALIB (PI := PI_grant) B.
(* RT_PALIBF: PALibF: the side-stack library facts (GrantBContracts.v:335). *)
Hypothesis RT_PALIBF : GrantBContracts.RT_PALIBF (PI := PI_grant) B.
(* RT_ML: model_laws of the trace universe (GrantBContracts.v:336). *)
Hypothesis RT_ML : GrantBContracts.RT_ML B.
(* RT_SMP: stack_malloc_progressP (GrantBContracts.v:337). *)
Hypothesis RT_SMP : GrantBContracts.RT_SMP B.
(* RT_ASF: astack_free_law (GrantBContracts.v:338). *)
Hypothesis RT_ASF : GrantBContracts.RT_ASF (PI := PI_grant) B.
(* RT_FFL: frame_flag_lawP (GrantBContracts.v:339). *)
Hypothesis RT_FFL : GrantBContracts.RT_FFL (PI := PI_grant) B.
(* RT_TP_FS: the fake stack's thread-local pointer (GrantBContracts.v:367). *)
Hypothesis RT_TP_FS : GrantBContracts.RT_TP_FS (PI := PI_grant) B.
(* RT_MALLOC: the malloc wrapper's jump 0x52edc (GrantBContracts.v:341). *)
Hypothesis RT_MALLOC : GrantBContracts.RT_MALLOC (PI := PI_grant) B.
(* RT_FREE: the free wrapper's jump 0x52ed8 (GrantBContracts.v:342). *)
Hypothesis RT_FREE : GrantBContracts.RT_FREE (PI := PI_grant) B.
(* RT_MEMCPY: __asan_memcpy 0x51b88 (GrantBContracts.v:344). *)
Hypothesis RT_MEMCPY : GrantBContracts.RT_MEMCPY (PI := PI_grant) B.
(* RT_MEMSET: __asan_memset 0x52024 (GrantBContracts.v:345). *)
Hypothesis RT_MEMSET : GrantBContracts.RT_MEMSET (PI := PI_grant) B.
(* RT_BCMP: the bcmp wrapper's jump 0x424d0 (GrantBContracts.v:347). *)
Hypothesis RT_BCMP : GrantBContracts.RT_BCMP (PI := PI_grant) B.
(* RT_SM0: __asan_stack_malloc_0 0x3cf4c (GrantBContracts.v:352, c = 0). *)
Hypothesis RT_SM0 : GrantBContracts.RT_SM (PI := PI_grant) B 0.
(* RT_SM1: __asan_stack_malloc_1 0x3d0c0 (GrantBContracts.v:352, c = 1). *)
Hypothesis RT_SM1 : GrantBContracts.RT_SM (PI := PI_grant) B 1.
(* RT_SM2: __asan_stack_malloc_2 0x3d250 (GrantBContracts.v:352, c = 2). *)
Hypothesis RT_SM2 : GrantBContracts.RT_SM (PI := PI_grant) B 2.
(* RT_SM4: __asan_stack_malloc_4 0x3d3ec (GrantBContracts.v:352, c = 4). *)
Hypothesis RT_SM4 : GrantBContracts.RT_SM (PI := PI_grant) B 4.
(* RT_SM6: __asan_stack_malloc_6 0x3d5b8 (GrantBContracts.v:352, c = 6). *)
Hypothesis RT_SM6 : GrantBContracts.RT_SM (PI := PI_grant) B 6.
(* RT_SF6: __asan_stack_free_6 0x3d754 (GrantBContracts.v:354). *)
Hypothesis RT_SF6 : GrantBContracts.RT_SF6 (PI := PI_grant) B.
(* RT_SS00: __asan_set_shadow_00 0x54a48 (GrantBContracts.v:356). *)
Hypothesis RT_SS00 : GrantBContracts.RT_SS00 (PI := PI_grant) B.
(* RT_SSF5: __asan_set_shadow_f5 0x54b50 (GrantBContracts.v:357). *)
Hypothesis RT_SSF5 : GrantBContracts.RT_SSF5 (PI := PI_grant) B.
(* RT_SSF8: __asan_set_shadow_f8 0x54b68 (GrantBContracts.v:358). *)
Hypothesis RT_SSF8 : GrantBContracts.RT_SSF8 (PI := PI_grant) B.
(* RT_IMGSH: the shadow of image B's read range is mapped (GrantBContracts.v:361). *)
Hypothesis RT_IMGSH : GrantBContracts.RT_IMGSH (PI := PI_grant) B.
(* RT_GLOBS: image B's 13 registered globals are marked (GrantBContracts.v:362). *)
Hypothesis RT_GLOBS : GrantBContracts.RT_GLOBS (PI := PI_grant) B.
(* IMG_CTRL_ROW: the row B_ROW 0x9d4d0: aligned, placed, in as_zero_shadow, apart (GrantBContracts.v:969). *)
Hypothesis IMG_CTRL_ROW : GrantBContracts.IMG_CTRL_ROW (PI := PI_grant) B.
(* IMG_CTRL_ROW_FIN: the row's bytes ctrl_finish reads (GrantBContracts.v:974). *)
Hypothesis IMG_CTRL_ROW_FIN : GrantBContracts.IMG_CTRL_ROW_FIN (PI := PI_grant) B.
(* IMG_CTRL_LAY_JT: entry 2 of ctrl_lay_block's jump table 0x21034 (GrantBContracts.v:992). *)
Hypothesis IMG_CTRL_LAY_JT : GrantBContracts.IMG_CTRL_LAY_JT (PI := PI_grant) B.
(* IMG_CTRL_STAMP_TM: the last conjunct of IMG_CTRL_STAMP (GrantBContracts.v:1011): the template TM the row names. *)
Hypothesis IMG_CTRL_STAMP_TM : exists TM, GrantBContracts.tmpl_place (PI := PI_grant) B TM /\ GrantBContracts.IMG_CTRL_ROW_LAY (PI := PI_grant) B TM /\
    GrantBContracts.IMG_CTRL_TMPL (PI := PI_grant) B TM.
(* IMG_BGS_ROWS: the three row tables reac_ctrl_build_grant_sweep copies (GrantBContracts.v:1017). *)
Hypothesis IMG_BGS_ROWS : GrantBContracts.IMG_BGS_ROWS (PI := PI_grant) B.
(* IMG_reac_ctrl_parse: .str.4 (object 15): its entry, place and six 0xff bytes (GrantBContracts.v:1626). *)
Hypothesis IMG_reac_ctrl_parse : GrantBContracts.IMG_reac_ctrl_parse (PI := PI_grant) B.
(* IMG_check_groupa: __const.check_groupa.frame (object 9) (GrantBContracts.v:1699). *)
Hypothesis IMG_check_groupa : GrantBContracts.IMG_check_groupa (PI := PI_grant) B.
(* IMG_LLVMF_TRACES (GrantBContracts.v:1896) is PROVED here, by GrantBTraces.img_llvmf_traces_grant
   (lib/B/Prog/GrantBTraces.v:85), from three facts of the runtime's symbol record B. Each is the field of image A's
   concrete record that image A's proof reads, and each closes by reflexivity at image B's concrete asyms record,
   lib/B/GrantBCloseInst.v:366, :369, :372. *)
(* H_universe_B: B's trace universe is image B's (lib/B/YCej.v:61 Tfib_universe); A: lib/A/AD2l.v:38
   `as_universe := Tfib_universe`. *)
Hypothesis H_universe_B : as_universe B = YCej.Tfib_universe.
(* H_malloc_ra0_B: the malloc interceptor's return address after its GetCurrentPc call, 0x53178 on image B;
   A: lib/A/AF0l.v:10 `pc_malloc_ra0 := 0x52dec`. *)
Hypothesis H_malloc_ra0_B : pc_malloc_ra0 (as_code B) = 0x53178.
(* H_free_ra0_B: the free interceptor's, 0x53018 on image B; A: lib/A/AF0l.v:11 `pc_free_ra0 := 0x52c8c`. *)
Hypothesis H_free_ra0_B : pc_free_ra0 (as_code B) = 0x53018.
(* IMG_LLVMF_SWEEP: the four read-only tables the entry reads (GrantBContracts.v:1911). *)
Hypothesis IMG_LLVMF_SWEEP : GrantBContracts.IMG_LLVMF_SWEEP (PI := PI_grant) B.
(* IMG_NEXT_DIV3: reac_headamp_tx_next's multiplier 0xAAAAAAAAAAAAAAAB at object 34 (0x10320) (GrantBContracts.v:690), a
   conjunct of hyps_reac_headamp_tx_next on the core; b_next_div3_check (:173) checks its bytes on image B. *)
Hypothesis IMG_NEXT_DIV3 : GrantBContracts.IMG_NEXT_DIV3 (PI := PI_grant) B.

(* ---- the open walks: NONE. Every walk_<f> of GrantBContracts.v that reaches the entry top is taken by its proved
   theorem in the composition below. *)

(* ---- the two image facts that are closed on image B ------------------------------------------------------------ *)
(* IMG_RO_BELOW (GrantBContracts.v:1029) at image B's sink and image: ro_below_ofl_grantB above. *)
Lemma img_ro_below_B : GrantBContracts.IMG_RO_BELOW (SK := grantB_sink_head) (PI := PI_grant).
Proof. exact ro_below_ofl_grantB. Qed.
(* IMG_CTRL_ROW_IMG (GrantBContracts.v:1001): the row B_ROW = object 18 + 240 = 0x9d4d0 (GrantImg.v grant_row_val) and its
   24 bytes lie in image B's RELRO range [0x9d000, 0x9e3c8), which is image B's (GrantImg.v grant_relro_img). *)
Lemma img_ctrl_row_img_B : GrantBContracts.IMG_CTRL_ROW_IMG (PI := PI_grant).
Proof.
  unfold GrantBContracts.IMG_CTRL_ROW_IMG. intros a Ha.
  assert (HR : GrantBContracts.B_ROW (PI := PI_grant) = 0x9d4d0) by exact grant_row_val.
  rewrite HR in Ha. apply grant_relro_img. unfold grant_relro_lo, grant_relro_hi. lia.
Qed.
(* IMG_CTRL_STAMP (GrantBContracts.v:1011), from its five conjuncts. *)
Lemma img_ctrl_stamp_B : GrantBContracts.IMG_CTRL_STAMP (PI := PI_grant) B.
Proof. exact (conj IMG_CTRL_ROW (conj img_ctrl_row_img_B (conj IMG_CTRL_ROW_FIN (conj IMG_CTRL_LAY_JT IMG_CTRL_STAMP_TM)))). Qed.

(* IMG_LLVMF_TRACES, from the three record facts above. *)
Lemma img_llvmf_traces_B : GrantBContracts.IMG_LLVMF_TRACES (PI := PI_grant) B.
Proof. exact (GrantBTraces.img_llvmf_traces_grant B H_universe_B H_malloc_ra0_B H_free_ra0_B). Qed.

(* ---- every hyps_<f>, built from the named facts ------------------------------------------------------------------ *)
Lemma hyps_kind_of_link1_B : hyps_kind_of_link1 (PI := PI_grant) B.
Proof. exact RT_LAWS. Qed.
Lemma hyps_reac_headamp_tx_init_B : hyps_reac_headamp_tx_init (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_MEMSET). Qed.
Lemma hyps_reac_headamp_default_B : hyps_reac_headamp_default (PI := PI_grant) B.
Proof. exact RT_LAWS. Qed.
Lemma hyps_reac_headamp_tx_set_B : hyps_reac_headamp_tx_set (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_headamp_tx_effective_B : hyps_reac_headamp_tx_effective (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_headamp_tx_arm_scene_B : hyps_reac_headamp_tx_arm_scene (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_headamp_tx_set_resweep_B : hyps_reac_headamp_tx_set_resweep (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_ctrl_block_cksum_stamp_B : hyps_reac_ctrl_block_cksum_stamp (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_ctrl_record_cksum_stamp_B : hyps_reac_ctrl_record_cksum_stamp (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_ctrl_checksum_verify_B : hyps_reac_ctrl_checksum_verify (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_ctrl_headamp_record_verify_B : hyps_reac_ctrl_headamp_record_verify (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_ctrl_identity_poll_block_B : hyps_reac_ctrl_identity_poll_block (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj RT_MEMCPY (conj RT_GLOBS RT_IMGSH)))). Qed.
Lemma hyps_ctrl_lay_block_B : hyps_ctrl_lay_block (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj RT_PALIBF (conj RT_ML (conj RT_SMP (conj RT_SM1 (conj RT_ASF (conj RT_FFL (conj RT_TP_FS (conj RT_MEMSET (conj RT_MEMCPY (conj RT_IMGSH (conj img_ro_below_B (conj IMG_CTRL_ROW (conj img_ctrl_row_img_B IMG_CTRL_LAY_JT))))))))))))))). Qed.
Lemma hyps_reac_grant_alloc_fits_B : hyps_reac_grant_alloc_fits (PI := PI_grant) B.
Proof. exact RT_LAWS. Qed.
Lemma hyps_reac_grant_allocate_B : hyps_reac_grant_allocate (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_reac_headamp_tx_next_B : hyps_reac_headamp_tx_next (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB IMG_NEXT_DIV3)). Qed.
Lemma hyps_want_of_B : hyps_want_of (PI := PI_grant) B.
Proof. exact (conj RT_LAWS RT_PALIB). Qed.
Lemma hyps_ctrl_finish_B : hyps_ctrl_finish (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj IMG_CTRL_ROW img_ctrl_row_img_B))). Qed.
Lemma hyps_reac_ctrl_stamp_headamp_B : hyps_reac_ctrl_stamp_headamp (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj RT_PALIBF (conj RT_ML (conj RT_SMP (conj RT_SM0 (conj RT_ASF (conj RT_FFL (conj RT_TP_FS (conj img_ro_below_B img_ctrl_stamp_B)))))))))). Qed.
Lemma hyps_reac_ctrl_build_grant_sweep_B : hyps_reac_ctrl_build_grant_sweep (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj RT_PALIBF (conj RT_ML (conj RT_SMP (conj RT_SM6 (conj RT_SF6 (conj RT_FFL (conj RT_TP_FS (conj RT_SS00 (conj RT_SSF8 (conj RT_MEMCPY (conj RT_MEMSET (conj RT_IMGSH (conj RT_GLOBS (conj img_ro_below_B IMG_BGS_ROWS)))))))))))))))). Qed.
Lemma hyps_reac_grant_build_sweep_B : hyps_reac_grant_build_sweep (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj RT_PALIBF (conj RT_ML (conj RT_SM2 (conj RT_SMP (conj RT_ASF (conj RT_FFL (conj RT_TP_FS img_ro_below_B))))))))). Qed.
Lemma hyps_reac_ctrl_parse_B : hyps_reac_ctrl_parse (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj RT_PALIBF (conj RT_ML (conj RT_MEMSET (conj RT_MEMCPY (conj RT_BCMP (conj RT_SM1 (conj RT_SMP (conj RT_ASF (conj RT_FFL (conj RT_TP_FS (conj RT_IMGSH (conj RT_GLOBS (conj img_ro_below_B IMG_reac_ctrl_parse))))))))))))))). Qed.
Lemma hyps_check_groupa_B : hyps_check_groupa (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj RT_PALIBF (conj RT_ML (conj RT_MEMCPY (conj RT_SM2 (conj RT_SMP (conj RT_ASF (conj RT_FFL (conj RT_TP_FS (conj RT_IMGSH (conj RT_GLOBS (conj img_ro_below_B IMG_check_groupa))))))))))))). Qed.
Lemma hyps_LLVMFuzzerTestOneInput_B : hyps_LLVMFuzzerTestOneInput (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (conj RT_LAWS (conj RT_PALIB (conj RT_PALIBF (conj RT_ML (conj RT_SMP (conj RT_ASF (conj RT_FFL (conj RT_MALLOC (conj RT_FREE (conj RT_MEMSET (conj RT_BCMP (conj RT_SM4 (conj RT_SSF5 (conj RT_IMGSH (conj RT_GLOBS (conj RT_TP_FS (conj img_ro_below_B (conj img_llvmf_traces_B IMG_LLVMF_SWEEP)))))))))))))))))). Qed.

(* ---- the composition, bottom-up: each contract from its walk, its facts and its callees' contracts -------------- *)
(* kind_of_link1: PROVED, pb_walk_kind_of_link1 (lib/B/Prog/GrantBContracts.v:420). *)
Lemma tb_kind_of_link1_holds_B : tb_kind_of_link1_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (pb_walk_kind_of_link1 (SK := grantB_sink_head) (PI := PI_grant) B hyps_kind_of_link1_B). Qed.
(* reac_headamp_tx_init: PROVED, pb_walk_reac_headamp_tx_init (lib/B/Prog/GrantBContracts.v:425). *)
Lemma tb_reac_headamp_tx_init_holds_B : tb_reac_headamp_tx_init_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (pb_walk_reac_headamp_tx_init (SK := grantB_sink_head) (PI := PI_grant) B hyps_reac_headamp_tx_init_B). Qed.
(* reac_headamp_default: PROVED, pb_walk_reac_headamp_default (lib/B/Prog/GrantBContracts.v:430). *)
Lemma tb_reac_headamp_default_holds_B : tb_reac_headamp_default_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof. exact (pb_walk_reac_headamp_default (SK := grantB_sink_head) (PI := PI_grant) B hyps_reac_headamp_default_B). Qed.
(* reac_headamp_tx_set: PROVED, HeadampTxSet.pb_reac_headamp_tx_set (lib/B/Prog/HeadampTxSet.v:655). *)
Lemma tb_reac_headamp_tx_set_holds_B : tb_reac_headamp_tx_set_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (HeadampTxSet.pb_reac_headamp_tx_set (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_headamp_tx_set_B).
Qed.
(* reac_headamp_tx_effective: PROVED, HeadampTxEffective.pb_reac_headamp_tx_effective (lib/B/Prog/HeadampTxEffective.v:523). *)
Lemma tb_reac_headamp_tx_effective_holds_B : tb_reac_headamp_tx_effective_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (HeadampTxEffective.pb_reac_headamp_tx_effective (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_headamp_tx_effective_B).
Qed.
(* reac_headamp_tx_arm_scene: PROVED, HeadampTxArmScene.pb_reac_headamp_tx_arm_scene (lib/B/Prog/HeadampTxArmScene.v:612). *)
Lemma tb_reac_headamp_tx_arm_scene_holds_B : tb_reac_headamp_tx_arm_scene_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (HeadampTxArmScene.pb_reac_headamp_tx_arm_scene (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_headamp_tx_arm_scene_B).
Qed.
(* reac_headamp_tx_set_resweep: PROVED, HeadampTxSetResweep.pb_reac_headamp_tx_set_resweep (lib/B/Prog/HeadampTxSetResweep.v:179). *)
Lemma tb_reac_headamp_tx_set_resweep_holds_B : tb_reac_headamp_tx_set_resweep_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (HeadampTxSetResweep.pb_reac_headamp_tx_set_resweep (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_headamp_tx_set_resweep_B).
Qed.
(* reac_ctrl_block_cksum_stamp: PROVED, CtrlBlockCksumStamp.pb_reac_ctrl_block_cksum_stamp (lib/B/Prog/CtrlBlockCksumStamp.v:328). *)
Lemma tb_reac_ctrl_block_cksum_stamp_holds_B : tb_reac_ctrl_block_cksum_stamp_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlBlockCksumStamp.pb_reac_ctrl_block_cksum_stamp (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_ctrl_block_cksum_stamp_B).
Qed.
(* reac_ctrl_record_cksum_stamp: PROVED, CtrlRecordCksumStamp.pb_reac_ctrl_record_cksum_stamp (lib/B/Prog/CtrlRecordCksumStamp.v:1184). *)
Lemma tb_reac_ctrl_record_cksum_stamp_holds_B : tb_reac_ctrl_record_cksum_stamp_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlRecordCksumStamp.pb_reac_ctrl_record_cksum_stamp (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_ctrl_record_cksum_stamp_B).
Qed.
(* reac_ctrl_checksum_verify: PROVED, CtrlChecksumVerify.pb_reac_ctrl_checksum_verify (lib/B/Prog/CtrlChecksumVerify.v:355). *)
Lemma tb_reac_ctrl_checksum_verify_holds_B : tb_reac_ctrl_checksum_verify_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlChecksumVerify.pb_reac_ctrl_checksum_verify (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_ctrl_checksum_verify_B).
Qed.
(* reac_ctrl_headamp_record_verify: PROVED, CtrlHeadampRecordVerify.pb_reac_ctrl_headamp_record_verify (lib/B/Prog/CtrlHeadampRecordVerify.v:361). *)
Lemma tb_reac_ctrl_headamp_record_verify_holds_B : tb_reac_ctrl_headamp_record_verify_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlHeadampRecordVerify.pb_reac_ctrl_headamp_record_verify (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_ctrl_headamp_record_verify_B).
Qed.
(* reac_ctrl_identity_poll_block: PROVED, CtrlIdentityPollBlock.pb_reac_ctrl_identity_poll_block (lib/B/Prog/CtrlIdentityPollBlock.v:315). *)
Lemma tb_reac_ctrl_identity_poll_block_holds_B : tb_reac_ctrl_identity_poll_block_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlIdentityPollBlock.pb_reac_ctrl_identity_poll_block (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_ctrl_identity_poll_block_B).
Qed.
(* ctrl_lay_block: PROVED, CtrlLayBlock.pb_walk_ctrl_lay_block (lib/B/Prog/CtrlLayBlock.v:1175). *)
Lemma tb_ctrl_lay_block_holds_B : tb_ctrl_lay_block_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlLayBlock.pb_walk_ctrl_lay_block (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_ctrl_lay_block_B).
Qed.
(* reac_grant_alloc_fits: PROVED, GrantAllocFits.pb_reac_grant_alloc_fits (lib/B/Prog/GrantAllocFits.v:272). *)
Lemma tb_reac_grant_alloc_fits_holds_B : tb_reac_grant_alloc_fits_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (GrantAllocFits.pb_reac_grant_alloc_fits (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_grant_alloc_fits_B).
Qed.
(* reac_grant_allocate: PROVED, GrantAllocate.pb_reac_grant_allocate (lib/B/Prog/GrantAllocate.v:597). *)
Lemma tb_reac_grant_allocate_holds_B : tb_reac_grant_allocate_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (GrantAllocate.pb_reac_grant_allocate (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_grant_allocate_B).
Qed.
(* reac_headamp_tx_next: PROVED, HeadampTxNextClose.pb_reac_headamp_tx_next (lib/B/Prog/HeadampTxNextClose.v:57);
   callees: reac_headamp_tx_effective. *)
Lemma tb_reac_headamp_tx_next_holds_B : tb_reac_headamp_tx_next_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (HeadampTxNextClose.pb_reac_headamp_tx_next (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_headamp_tx_next_B
           tb_reac_headamp_tx_effective_holds_B).
Qed.
(* want_of: PROVED, WantOf.pb_want_of (lib/B/Prog/WantOf.v:479); callees: reac_headamp_default. *)
Lemma tb_want_of_holds_B : tb_want_of_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (WantOf.pb_want_of (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_want_of_B
           tb_reac_headamp_default_holds_B).
Qed.
(* ctrl_finish: PROVED, CtrlFinish.pb_ctrl_finish (lib/B/Prog/CtrlFinish.v:834); callees: reac_ctrl_record_cksum_stamp,
   reac_ctrl_block_cksum_stamp. *)
Lemma tb_ctrl_finish_holds_B : tb_ctrl_finish_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlFinish.pb_ctrl_finish (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_ctrl_finish_B
           tb_reac_ctrl_record_cksum_stamp_holds_B
           tb_reac_ctrl_block_cksum_stamp_holds_B).
Qed.
(* reac_ctrl_stamp_headamp: PROVED, CtrlStampHeadamp.pb_reac_ctrl_stamp_headamp (lib/B/Prog/CtrlStampHeadamp.v:1548);
   callees: ctrl_lay_block, ctrl_finish. *)
Lemma tb_reac_ctrl_stamp_headamp_holds_B : tb_reac_ctrl_stamp_headamp_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlStampHeadamp.pb_reac_ctrl_stamp_headamp (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_ctrl_stamp_headamp_B
           tb_ctrl_lay_block_holds_B
           tb_ctrl_finish_holds_B).
Qed.
(* reac_ctrl_build_grant_sweep: PROVED, CtrlBuildGrantSweep.pb_reac_ctrl_build_grant_sweep (lib/B/Prog/CtrlBuildGrantSweep.v:4229),
   accepted at a working branch 583b6421912 (a Theorem Labs build tool: rc=0, 1931 files, 0 failed:
   an internal build log; its audit leaf is not part of the release tree);
   callees: reac_ctrl_stamp_headamp. *)
Lemma tb_reac_ctrl_build_grant_sweep_holds_B : tb_reac_ctrl_build_grant_sweep_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlBuildGrantSweep.pb_reac_ctrl_build_grant_sweep (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_ctrl_build_grant_sweep_B
           tb_reac_ctrl_stamp_headamp_holds_B).
Qed.
(* reac_grant_build_sweep: PROVED, GrantBuildSweepWalk.pb_reac_grant_build_sweep (lib/B/Prog/GrantBuildSweepWalk.v:37);
   callees: reac_headamp_tx_effective, reac_ctrl_build_grant_sweep. *)
Lemma tb_reac_grant_build_sweep_holds_B : tb_reac_grant_build_sweep_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (GrantBuildSweepWalk.pb_reac_grant_build_sweep (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_grant_build_sweep_B
           tb_reac_headamp_tx_effective_holds_B
           tb_reac_ctrl_build_grant_sweep_holds_B).
Qed.
(* reac_ctrl_parse: PROVED, CtrlParse.pb_reac_ctrl_parse (lib/B/Prog/CtrlParse.v:347); callees: kind_of_link1. *)
Lemma tb_reac_ctrl_parse_holds_B : tb_reac_ctrl_parse_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CtrlParse.pb_reac_ctrl_parse (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_reac_ctrl_parse_B
           tb_kind_of_link1_holds_B).
Qed.
(* check_groupa: PROVED, CheckGroupa.pb_check_groupa (lib/B/Prog/CheckGroupa.v:1381); callees: reac_ctrl_parse,
   reac_headamp_tx_effective, reac_ctrl_headamp_record_verify, reac_ctrl_checksum_verify. *)
Lemma tb_check_groupa_holds_B : tb_check_groupa_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (CheckGroupa.pb_check_groupa (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_check_groupa_B
           tb_reac_ctrl_parse_holds_B
           tb_reac_headamp_tx_effective_holds_B
           tb_reac_ctrl_headamp_record_verify_holds_B
           tb_reac_ctrl_checksum_verify_holds_B).
Qed.
(* LLVMFuzzerTestOneInput: PROVED, LLVMFuzzerTestOneInput.pb_LLVMFuzzerTestOneInput (lib/B/Prog/LLVMFuzzerTestOneInput.v:184),
   accepted at a working branch 1061c1773db, merged at 4a431dd26e1 with header and settings lines only (a Theorem Labs build tool: rc=0, 2012 files, 0 failed:
   an internal build log; its Print Assumptions audit leaf is not part of the release tree);
   callees: reac_headamp_tx_init, reac_headamp_tx_set, reac_headamp_tx_effective, reac_headamp_default, reac_grant_alloc_fits,
   reac_grant_allocate, reac_grant_build_sweep, want_of, check_groupa, reac_ctrl_identity_poll_block,
   reac_headamp_tx_arm_scene, reac_headamp_tx_set_resweep, reac_headamp_tx_next. *)
Theorem tb_LLVMFuzzerTestOneInput_holds_B : tb_LLVMFuzzerTestOneInput_spec (SK := grantB_sink_head) (PI := PI_grant) B.
Proof.
  exact (LLVMFuzzerTestOneInput.pb_LLVMFuzzerTestOneInput (SK := grantB_sink_head) (PI := PI_grant) B
           hyps_LLVMFuzzerTestOneInput_B
           tb_reac_headamp_tx_init_holds_B
           tb_reac_headamp_tx_set_holds_B
           tb_reac_headamp_tx_effective_holds_B
           tb_reac_headamp_default_holds_B
           tb_reac_grant_alloc_fits_holds_B
           tb_reac_grant_allocate_holds_B
           tb_reac_grant_build_sweep_holds_B
           tb_want_of_holds_B
           tb_check_groupa_holds_B
           tb_reac_ctrl_identity_poll_block_holds_B
           tb_reac_headamp_tx_arm_scene_holds_B
           tb_reac_headamp_tx_set_resweep_holds_B
           tb_reac_headamp_tx_next_holds_B).
Qed.

(* ---- INIT AND EXIT PATHS: why asan.module_ctor, asan.module_dtor and RTC_* are not in this file ------------------
   The two statements of image B quantify over WHOLE executions: asan_ubsan_halts
   (projects/libreac/fuzz_grant/Statements.v:95-96) is halts_within_budget, "EVERY execution of [img] ends by calling
   exit_group with a status in [allowed]" with no error (theories/Shapes.v:270-287), and asan_ubsan_agrees
   (Statements.v:127-128) is agrees_in, whose conclusion is error_free of the whole run of the sanitizer build
   (Shapes.v:151-160). So both take the init path and the exit path. On image B, musl's start-up calls
   asan.module_ctor 0x824ec through .init_array[0] (0x9cfc8, its only caller; the next slot is 0x309cc __do_init),
   and exit() reaches asan.module_dtor 0x82524 through .fini_array[0] (0x9cfe8, its only caller; the next slot is
   0x30a40 __do_fini), also after exit 2 (slots read from the unstripped twin's .init_array / .fini_array).
   Neither function is a callee of any walk, and tb_LLVMFuzzerTestOneInput_spec does not mention them.

   Image A discharges both paths inside its relocated core, through TFIB_T, so lib/A/GrantTop.v takes no module walk
   and no RTC_* fact:
   - EXIT path, walked in the core: lib/A/AE37.v:200 x2_realizes (asan.module_dtor, A 0x81f5c, with
     __asan_unregister_globals over the 13 descriptors; its writes XW2, AE23.v:35-37),
     lib/A/AE36.v:106 x1_realizes (the atexit handler) and AE36.v:142 x3_realizes (__do_fini); AE23's
     exit run calls them (AE23.v:361-365); lib/A/AD1j.v:123 tfib_exit_site closes the exit path.
   - INIT path: the START-UP CERTIFICATE, whose AB01 states are taken AT main, after .init_array ran. So A has no
     ctor walk and no RTC_REG premise.
   - All of it is inside AGrantT.grant_TFIB_T_of_lib's closure.
   Image B gets the same from its core: the B twins of AE37 / AE36 / AE23 / AD1j for B's dtor
   0x82524, B's __do_fini 0x30a40 and B's exit run; and B's start-up certificate (YB01 at main 0x8059c, walker PASS,
   an internal gate record), which ASSERTS the ctor's result, 104 cells of 0xf9 at 0x8000c3f0. TFIB_TB, the
   B twin of TFIB_T, is lib/B/GrantTFIBB.v:19, used
   as the Hypothesis TFIBB at lib/B/AsanUbsanTop.v:28. The step that joins this file's entry top with TFIB_TB is
   lib/B/Prog/GrantBTFIB.v:524 grant_TFIB_TB_of_lib (used at lib/B/GrantBTop.v:184).
   Therefore (the statement owner's decision) this file takes neither module walk and none of
   RTC_INIT, RTC_VCHK, RTC_REG, RTC_UNREG (GrantBContracts.v:1977-1978, :1997-1998). The two module walks stay proved
   on their branches (a working branch 9c0eb366154, lib/B/Prog/AsanModuleCtor.v:461 there; a working branch
   6a46e28f21c, lib/B/Prog/AsanModuleDtor.v:259 there); this file does not Require them, and this branch does not carry them. A note for the core port:
   RTC_REG / RTC_UNREG as GrantBContracts.v states them are satisfiable only if the poisoned redzone
   shadow that the registration writes (about 0x7fffa1d8 .. 0x8000bab7, outside every PT_LOAD) is in AR's owned set. *)

(* Inside the Section, Print Assumptions lists what the closed contract rests on: the Section variables (the open
   walks PB_<f>, the runtime and image facts, and the parameters fx, rc, B) next to the axioms
   toolchain/allowed-axioms.txt allows. *)
Print Assumptions tb_LLVMFuzzerTestOneInput_holds_B.
End closeB.

(* After the Section, the same theorem in its closed form: every Section hypothesis is now a premise of its type, and
   Print Assumptions lists only the axioms. *)
Check tb_LLVMFuzzerTestOneInput_holds_B.
Print Assumptions tb_LLVMFuzzerTestOneInput_holds_B.

(* ==== THE TOP'S OBLIGATION SET =====================================================================================
   What tb_LLVMFuzzerTestOneInput_holds_B rests on (Print Assumptions above lists the same names).

   Open walks: none. Every walk that reaches the top is taken by its theorem.

   Runtime and image facts that reach the top undischarged (33):
     RT_LAWS: AR_laws: the runtime's state laws (GrantBContracts.v:333)
     RT_PALIB: PALib: the walk layer's library facts (GrantBContracts.v:334)
     RT_PALIBF: PALibF: the side-stack library facts (GrantBContracts.v:335)
     RT_ML: model_laws of the trace universe (GrantBContracts.v:336)
     RT_SMP: stack_malloc_progressP (GrantBContracts.v:337)
     RT_ASF: astack_free_law (GrantBContracts.v:338)
     RT_FFL: frame_flag_lawP (GrantBContracts.v:339)
     RT_TP_FS: the fake stack's thread-local pointer (GrantBContracts.v:367)
     RT_MALLOC: the malloc wrapper's jump 0x52edc (GrantBContracts.v:341)
     RT_FREE: the free wrapper's jump 0x52ed8 (GrantBContracts.v:342)
     RT_MEMCPY: __asan_memcpy 0x51b88 (GrantBContracts.v:344)
     RT_MEMSET: __asan_memset 0x52024 (GrantBContracts.v:345)
     RT_BCMP: the bcmp wrapper's jump 0x424d0 (GrantBContracts.v:347)
     RT_SM0: __asan_stack_malloc_0 0x3cf4c (GrantBContracts.v:352, c = 0)
     RT_SM1: __asan_stack_malloc_1 0x3d0c0 (GrantBContracts.v:352, c = 1)
     RT_SM2: __asan_stack_malloc_2 0x3d250 (GrantBContracts.v:352, c = 2)
     RT_SM4: __asan_stack_malloc_4 0x3d3ec (GrantBContracts.v:352, c = 4)
     RT_SM6: __asan_stack_malloc_6 0x3d5b8 (GrantBContracts.v:352, c = 6)
     RT_SF6: __asan_stack_free_6 0x3d754 (GrantBContracts.v:354)
     RT_SS00: __asan_set_shadow_00 0x54a48 (GrantBContracts.v:356)
     RT_SSF5: __asan_set_shadow_f5 0x54b50 (GrantBContracts.v:357)
     RT_SSF8: __asan_set_shadow_f8 0x54b68 (GrantBContracts.v:358)
     RT_IMGSH: the shadow of image B's read range is mapped (GrantBContracts.v:361)
     RT_GLOBS: image B's 13 registered globals are marked (GrantBContracts.v:362)
     IMG_CTRL_ROW: the row B_ROW 0x9d4d0: aligned, placed, in as_zero_shadow, apart (GrantBContracts.v:969)
     IMG_CTRL_ROW_FIN: the row's bytes ctrl_finish reads (GrantBContracts.v:974)
     IMG_CTRL_LAY_JT: entry 2 of ctrl_lay_block's jump table 0x21034 (GrantBContracts.v:992)
     IMG_CTRL_STAMP_TM: the last conjunct of IMG_CTRL_STAMP (GrantBContracts.v:1011): the template TM the row names
     IMG_BGS_ROWS: the three row tables reac_ctrl_build_grant_sweep copies (GrantBContracts.v:1017)
     IMG_reac_ctrl_parse: .str.4 (object 15): its entry, place and six 0xff bytes (GrantBContracts.v:1626)
     IMG_check_groupa: __const.check_groupa.frame (object 9) (GrantBContracts.v:1699)
     IMG_LLVMF_SWEEP: the four read-only tables the entry reads (GrantBContracts.v:1911)
     IMG_NEXT_DIV3: reac_headamp_tx_next's multiplier at object 34 (GrantBContracts.v:690)

   Facts of the runtime's symbol record B that reach the top (3; each closes by reflexivity at B's concrete record):
     H_universe_B: as_universe B = YCej.Tfib_universe (A: lib/A/AD2l.v:38)
     H_malloc_ra0_B: pc_malloc_ra0 (as_code B) = 0x53178 (A: lib/A/AF0l.v:10)
     H_free_ra0_B: pc_free_ra0 (as_code B) = 0x53018 (A: lib/A/AF0l.v:11)

   No RTC_* fact and no module walk reaches the top: see INIT AND EXIT PATHS above.

   Discharged here, not hypotheses of the top: IMG_LLVMF_TRACES (img_llvmf_traces_B, from the three record facts by
   GrantBTraces.img_llvmf_traces_grant, a working branch efbbabd737d), IMG_RO_BELOW (img_ro_below_B, by
   computation over image B's
   segments and RELRO range at the sink 0x5f9008) and IMG_CTRL_ROW_IMG (img_ctrl_row_img_B, from GrantImg.v
   grant_row_val and grant_relro_img).
   Parameters, not obligations: fx, rc (the machine's FP state and run ceiling) and B (the runtime's symbol record).
   Caller obligations of the entry walk that GrantBContracts.v names (OBL_alloc_fits_bound, OBL_grant_allocate_bound,
   want_of's 0 <= p < 3) are discharged inside the walk of LLVMFuzzerTestOneInput, which is proved here
   (pb_LLVMFuzzerTestOneInput), so they add no hypothesis. One more of the same kind
   : want_of's `0 <= c < 48` at the two SWEEP call sites 0x8163c and 0x816e8 is not a branch of the entry; it
   follows from reac_grant_allocate's post `base + width <= 48` and the success test at 0x8138c. It is owed by the
   walk of the SWEEP phase of LLVMFuzzerTestOneInput, next to `0 <= p < 3`, and that walk is
   proved (a working branch 1061c1773db).

   THE MERGED WALK HEADS. This branch is image B's walk layer on the core (a working branch c3515bfe0db, on
   a working branch e47e01e8e06), with the heads that carry every proved walk onto it. Each walk file below comes from the
   head named. With comments and Require lines removed, 18 of these 22 files and 81 of the 84 parts are equal to their heads; the other 4 files (CtrlStampHeadamp.v, CheckGroupa.v, CtrlLayBlock.v, CtrlBuildGrantSweep.v) and 3 parts (GrantBuildSweep.v, GrantBuildSweepCell.v, LLVMFEntryInit.v) add helper tactics or lemmas and also change existing proof steps. The line numbers are this tree's. Acceptance builds of the
   walk heads (a Theorem Labs build tool, FACTS f0e6eb38667): an internal build log
   (twelve walks), an internal build log (seven walks at
   13b1d4fdf0a, reac_grant_build_sweep included; six earlier ones also at 4d49926a82f,
   an internal build log), and LLVMFuzzerTestOneInput's (below).
     branch                                        head          file (lib/B/Prog)           theorem taken here
     a working branch (layer)               c3515bfe0db   GrantBContracts.v           pb_walk_kind_of_link1 :420
                                                                 GrantBContracts.v           pb_walk_reac_headamp_tx_init :425
                                                                 GrantBContracts.v           pb_walk_reac_headamp_default :430
     a working branch                      13b1d4fdf0a   HeadampTxSet.v              pb_reac_headamp_tx_set :655
                                                                 HeadampTxEffective.v        pb_reac_headamp_tx_effective :523
                                                                 HeadampTxArmScene.v         pb_reac_headamp_tx_arm_scene :612
                                                                 HeadampTxSetResweep.v       pb_reac_headamp_tx_set_resweep :179
                                                                 CtrlStampHeadamp.v          pb_reac_ctrl_stamp_headamp :1548
                                                                 HeadampTxNextClose.v (+ 8 parts)pb_reac_headamp_tx_next :57
                                                                 GrantBuildSweepWalk.v (+ 4) pb_reac_grant_build_sweep :37
     a working branch                      893bc4d10e1   CtrlChecksumVerify.v        pb_reac_ctrl_checksum_verify :355
                                                                 CtrlHeadampRecordVerify.v   pb_reac_ctrl_headamp_record_verify :361
                                                                 CtrlIdentityPollBlock.v     pb_reac_ctrl_identity_poll_block :315
                                                                 GrantAllocFits.v            pb_reac_grant_alloc_fits :272
                                                                 GrantAllocate.v             pb_reac_grant_allocate :597
                                                                 CtrlBlockCksumStamp.v       pb_reac_ctrl_block_cksum_stamp :328
                                                                 CtrlRecordCksumStamp.v      pb_reac_ctrl_record_cksum_stamp :1184
                                                                 WantOf.v                    pb_want_of :479
                                                                 CtrlFinish.v                pb_ctrl_finish :834
                                                                 CtrlParse.v (+ 15 parts)    pb_reac_ctrl_parse :347
                                                                 CheckGroupa.v               pb_check_groupa :1381
                                                                 CtrlLayBlock.v              pb_walk_ctrl_lay_block :1175
     a working branch                       4a431dd26e1   LLVMFuzzerTestOneInput.v (+ 57)pb_LLVMFuzzerTestOneInput :184
     a working branch                        583b6421912   CtrlBuildGrantSweep.v       pb_reac_ctrl_build_grant_sweep :4229
   AsanModuleCtor.v and AsanModuleDtor.v are not on this branch: their pre-core copies (ctor2 9c0eb366154, dtor2
   6a46e28f21c, which Require lib.A.Prog) were removed (approved 2026-10-29); the module walks are not taken here
   (INIT AND EXIT PATHS). *)
