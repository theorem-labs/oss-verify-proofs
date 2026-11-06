(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: grant image B's walk contracts, written for libreac/fuzz_grant. Copied lines: tcj_kept and twr_ok (the caller-journal shapes) restate proofs/cgif/cgif_file_fuzzer/lib/YC20.v's tlzw_kept and its write-right form, by way of image A's lib/A/Prog/CtrlFinish.v; the header of Section F (the Context line for PI and the notations SEGS / VAL / SIGMA / BASE) has the shape of proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v's section header. Every other line is written for image B. *)
(* The CONTRACT of every program function that the walks of image B (fuzz_grant.asan-ubsan, bin/ sha256
   fde52226dc48, symbols 5a5ee7c02b4e; FACTS f0e6eb38667, PAU originals) must prove, stated over image B's walk
   layer (lib/B/Prog), as Definitions. No walk is proved here.

   For each function f (C name; `asan.module_ctor` is written asan_module_ctor):
     tb_f_spec     the contract: afn_pre / apost_base, or cgif's caller-journal form (an ajournal premise) for a
                   function that writes its caller's memory (an internal convention);
     hyps_f        the runtime callees (and image facts) its walk takes, each by its name below;
     walk_f        what the walk of f proves: hyps_f, then the contract of every program function f calls, imply
                   tb_f_spec. A walk lane proves `Theorem pb_f : walk_f`.

   ERROR FREEDOM. Every contract concludes `SRr SEGS W (cfg_at SEGS (BASE + AF_f) regs mem md) Post`. SRr
   (lib/Reusable/YA0n.v:35) is `forall T, (forall Post state, srealizes it T) -> srealizes (entry) T`, and
   srealizes implies `~ reaches_error_cfg` (lib/Reusable/YK18.v:142 srealizes_no_error); so a proved contract
   rules out every SError step between the entry and the post. A reached `unimp` (the 26 trap sites of image B,
   0xc0001073) is such a step (EDefinedIllegal -> MachineFault -> SError). contract_error_free below states the
   consequence once. The __asan_report_* entries RETURN on image B (load1 0x58ca0 ret 0x58cec, load8 0x58e80 ret
   0x58ecc, store1 0x58fc0 ret 0x5900c, ...): no hyps_f holds a contract for them, so a walk cannot pass a report
   call; it refutes each report branch from the shadow facts of its premises.

   Fall-through table (scan of every image-B program function's last instruction: the 30 functions of the listing, lib/B/Prog/GrantList.v, 21 hits).
   A report entry returns, so the call falls through into the next
   function. The walk of the function that ENDS in the call refutes the branch into it.
   | function                         | last call (pc, entry)          | falls into                       | edges into it              | walk obligation |
   | LLVMFuzzerTestOneInput           | 0x82070 report_load1           | check_groupa 0x82074             | fall-through from 0x8206c  | pb_LLVMFuzzerTestOneInput (ft 0x82070) |
   | want_of                          | 0x824e8 report_load1           | asan.module_ctor 0x824ec         | from 0x824e4 (blt)         | pb_want_of (ft 0x824e8; and 0x824dc report_load1 -> 0x824e0) |
   | reac_ctrl_block_cksum_stamp      | 0x82608 report_store1          | reac_ctrl_checksum_verify 0x8260c| from 0x82604 (blt)         | pb_reac_ctrl_block_cksum_stamp |
   | reac_ctrl_record_cksum_stamp     | 0x82770 report_store1          | reac_ctrl_parse 0x82774          | from 0x8276c               | pb_reac_ctrl_record_cksum_stamp |
   | reac_ctrl_parse                  | 0x831f4 report_store1          | kind_of_link1 0x831f8            | from 0x831f0               | pb_reac_ctrl_parse |
   | reac_ctrl_stamp_headamp          | 0x834d8 report_store1          | reac_ctrl_headamp_record_verify  | from 0x834d4 (blt)         | pb_reac_ctrl_stamp_headamp |
   | reac_ctrl_headamp_record_verify  | 0x835d8 report_load1           | reac_ctrl_identity_poll_block    | from 0x835d4               | pb_reac_ctrl_headamp_record_verify |
   | reac_ctrl_build_grant_sweep      | 0x83bf8 report_load1           | ctrl_lay_block 0x83bfc           | j at 0x83b34               | pb_reac_ctrl_build_grant_sweep |
   | ctrl_lay_block                   | 0x83fd8 report_load8           | ctrl_finish 0x83fdc              | bnez 0x83e20; after 0x83fd4 report_store1 | pb_ctrl_lay_block |
   | ctrl_finish                      | 0x840cc report_load1           | reac_box_model_block 0x840d0     | from 0x840c8 (blt)         | pb_ctrl_finish |
   | reac_box_model_block (unreached) | 0x84e48 report_load1           | build_dt1_single 0x84e4c         | from 0x84e44               | not walked: unreached (ctrl_lay_block's 0x83e64 not taken) |
   | build_dt1_single (unreached)     | 0x85000 report_store1          | dt1_head 0x85004                 | from 0x84ffc               | not walked: unreached |
   | dt1_head (unreached)             | 0x853fc report_store1          | name_field 0x85400               | from 0x853f8               | not walked: unreached |
   | name_field (unreached)           | 0x85514 report_load1           | reac_grant_alloc_fits 0x85518    | from 0x85510               | not walked: unreached |
   | reac_grant_allocate              | 0x855f8 report_store1          | reac_grant_build_sweep 0x855fc   | from 0x855f4 (blt)         | pb_reac_grant_allocate |
   | reac_grant_build_sweep           | 0x85a6c report_load1           | reac_headamp_tx_init 0x85a70     | from 0x85a68               | pb_reac_grant_build_sweep |
   | reac_headamp_tx_set              | 0x85bec report_store4          | reac_headamp_default 0x85bf0     | from 0x85be8 (blt)         | pb_reac_headamp_tx_set |
   | reac_headamp_tx_effective        | 0x85ce0 report_load1           | reac_headamp_tx_arm_scene 0x85ce4| from 0x85cdc (blt)         | pb_reac_headamp_tx_effective |
   | reac_headamp_tx_arm_scene        | 0x85e74 report_store4          | reac_headamp_tx_set_resweep      | from 0x85e70 (blt)         | pb_reac_headamp_tx_arm_scene |
   | reac_headamp_tx_set_resweep      | 0x85ef8 report_store4          | reac_headamp_tx_next 0x85efc     | from 0x85ef4 (blt)         | pb_reac_headamp_tx_set_resweep |
   | reac_headamp_tx_next             | 0x8663c report_store4          | __wrap_getenv 0x86640            | from 0x86638               | pb_reac_headamp_tx_next |
   The walk obligation is part of pb_f: tb_f_spec cannot be proved while a path reaches the last call, since
   hyps_f gives no contract for the report entry. *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require StackFreeDef.
(* The contract of the shadow-fill entries, lib/Reusable/SetShadowDef.v (moved here from lib/A/Rt). Its
   aset_shadow_realizes adds one conjunct to the post, `forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a`
   (the call keeps every present byte present); RT_SS00 / RT_SSF5 / RT_SSF8 name it unchanged. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaStep PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo.
(* The three code-identical walks, relocated (their contracts are restated below by name). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require KindOfLink1 HeadampTxInit HeadampDefault.
(* The address-free layout of the 460-byte head-amp table (TX_SIZE, LAY_TX, tx_vals): lib/Prog/HeadampLayout.v,
   which holds no address and no image value, and whose Require closure holds only image-neutral core modules (it
   Requires no per-image module of lib/Reusable or lib/B; measured: it uses no name of YCbq), so it adds no image's
   module to this file's closure. Required, NOT imported, and always named
   through the alias ATx. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require HeadampLayout.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require
  NextModel reac_headamp_tx_set_c reac_headamp_tx_arm_scene_c reac_headamp_tx_set_resweep_c.
(* a Theorem Labs lane: the checksum models (Required, not imported: RcFin and RcLeaf both define rsum). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require RcModel RcFin RcLeaf RcRec.
(* laystamp: RcFin.fin (ctrl_finish's result, as image A states it) and image B's check of ctrl_lay_block's jump
   table (GrantImg.v lay_jt_slots), named through the alias BImg at @@TOP@@. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require RcFin.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require GrantImg.
(* GrantModel: fits, int32 (Pau's address-free admission rule); BuildSweepModel: bsw_ok, sweep_vals, tx_set01, tx_legal. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel BuildSweepModel.
(* parsegroupa: Pau's parse model (ctrlparse, cp_v, cp_z) and the group-A frame model (T0z). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import RcParse GroupaModel.
(* none: every name below is in the skeleton's Require closure. *)
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module ATx := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.HeadampLayout.

(* ---- address-free definitions -------------------------------------------------------------------------- *)
(* ===== headamp ===== *)
(* fragment headamp: the address-free parts. *)
Module HdNx := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.NextModel.
Module HdSetC := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.reac_headamp_tx_set_c.
Module HdArmC := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.reac_headamp_tx_arm_scene_c.
Module HdRswC := OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog.reac_headamp_tx_set_resweep_c.
(* The table invariant reac_headamp_tx_next needs (else trap 0x8644c is reached through 0x86204 / 0x86214):
   replay_width (byte 437) <> 0 -> 0 <= replay_idx (the signed 4-byte field at 440). *)
Definition thd_replay_ok (T : list byte) : Prop := tb T 437 <> 0 -> 0 <= HdNx.s32 T 440.
(* The cell reac_headamp_tx_set accepts, the bytes it writes, and the table it leaves. *)
Definition thd_set_fp (tx ch p v : Z) : list (Z * Z) :=
  if ((ch <? 48) && legalb p v)%bool
  then [ (tx + 3 * ch + p, tx + 3 * ch + p + 1); (tx + 144 + 3 * ch + p, tx + 145 + 3 * ch + p);
         (tx + 288 + 3 * ch + p, tx + 289 + 3 * ch + p); (tx + 432, tx + 436) ]
  else [].
Definition thd_set_T (T : list byte) (ch p v : Z) : list byte :=
  if ((ch <? 48) && legalb p v)%bool then HdSetC.set_T T ch p v else T.
(* The table reac_headamp_tx_arm_scene leaves. *)
Definition thd_arm_T (T : list byte) (sb sw : Z) : list byte :=
  if (sw =? 0) || (48 <=? sb) then T else HdArmC.arm_T T sb sw.
(* Image B's frame of each of the five: the first slot of each is addi sp,sp,-16 (0xff010113) or, for
   reac_headamp_tx_next, addi sp,sp,-96 (0xfa010113). *)
Lemma thd_entry_frames_B :
  map (plookup_list gsym grant_listing)
    [AF_reac_headamp_tx_set; AF_reac_headamp_tx_effective; AF_reac_headamp_tx_arm_scene;
     AF_reac_headamp_tx_set_resweep; AF_reac_headamp_tx_next]
  = map (fun w => Some (PW w)) [0xff010113; 0xff010113; 0xff010113; 0xff010113; 0xfa010113].
Proof. vm_compute. reflexivity. Qed.

(* ===== ctrlleaves ===== *)
(* a Theorem Labs lane. GRANT_GROUPB of image B (object 19, B_GROUPB, 0x21080): a registered global of 204 bytes, and
   its 204 bytes are the address-free table GBallz (lib/Prog/GrantSweepModel.v, the six 34-byte rows GBz 0..5 that
   image A's 0x21040 holds), checked against image B's segments by computation. reac_ctrl_identity_poll_block's
   contract names the table through these two facts (its premises In (.., 204) GRANT_GLOBS_B and garr8 .. GBallz). *)
Lemma b_groupb_check :
  existsb (fun g => (fst g =? 0x21080) && (snd g =? 204))%bool GRANT_GLOBS_B = true /\
  map (fun j => romB8 (0x21080 + Z.of_nat j)) (seq 0 204) = map Some GBallz.
Proof. split; vm_compute; reflexivity. Qed.

(* The 18 bytes of POLL (object 6 on image B, 0x20ec0, a registered global of 18 bytes), which
   LLVMFuzzerTestOneInput compares through the bcmp wrapper at 0x817d4. Measured on image B (bin/ sha256
   fde52226dc48) at 0x20ec0: 00 00 04 06 00 08 10 00 11 10 11 09 11 00 11 11 11 09; b_llvmf_sweep_check checks it. *)
Definition POLLz : list Z := [0; 0; 4; 6; 0; 8; 16; 0; 17; 16; 17; 9; 17; 0; 17; 17; 17; 9].
(* The three other read-only tables the entry reads, checked against image B by computation: HEAD_ACK (object 4,
   0x20f00, 34 bytes, compared at 0x815e0), HEAD_MARK (object 5, 0x20f60, 34 bytes, compared at 0x81604) and POLL
   (object 6, 0x20ec0, 18 bytes, compared at 0x817d4): each object's address in the listing, its entry in
   GRANT_GLOBS_B, its bytes, and its place inside image B with 64 bytes to spare on each side. HEAD_ACK and
   HEAD_MARK hold the same bytes as GRANT_HEAD_ACK / GRANT_HEAD_MARK (objects 22 / 23), so the address-free names
   HEAD_ACK34z / HEAD_MARK34z of lib/Prog/GrantSweepModel.v name them. GRANT_GROUPB's half is b_groupb_check. *)
Lemma b_llvmf_sweep_check :
  grant_obj 4 = 0x20f00 /\ grant_obj 5 = 0x20f60 /\ grant_obj 6 = 0x20ec0 /\
  existsb (fun g => (fst g =? grant_obj 4) && (snd g =? 34))%bool GRANT_GLOBS_B = true /\
  existsb (fun g => (fst g =? grant_obj 5) && (snd g =? 34))%bool GRANT_GLOBS_B = true /\
  existsb (fun g => (fst g =? grant_obj 6) && (snd g =? 18))%bool GRANT_GLOBS_B = true /\
  map (fun j => romB8 (grant_obj 4 + Z.of_nat j)) (seq 0 34) = map Some HEAD_ACK34z /\
  map (fun j => romB8 (grant_obj 5 + Z.of_nat j)) (seq 0 34) = map Some HEAD_MARK34z /\
  map (fun j => romB8 (grant_obj 6 + Z.of_nat j)) (seq 0 18) = map Some POLLz /\
  IMG_LO_B + 64 <= grant_obj 4 /\ grant_obj 4 + 34 + 64 <= IMG_TOP_B /\
  IMG_LO_B + 64 <= grant_obj 5 /\ grant_obj 5 + 34 + 64 <= IMG_TOP_B /\
  IMG_LO_B + 64 <= grant_obj 6 /\ grant_obj 6 + 18 + 64 <= IMG_TOP_B.
Proof.
  repeat split; try (vm_compute; reflexivity);
  rewrite ?IMG_LO_B_val, ?IMG_TOP_B_val; vm_compute; discriminate.
Qed.
(* reac_headamp_tx_next's multiplier (IMG_NEXT_DIV3): object 34 of image B's listing is 0x10320, its 8 bytes read
   from image B are ab aa aa aa aa aa aa aa = 0xAAAAAAAAAAAAAAAB, and it lies inside the image with 64 bytes to spare.
   The bytes are in the first PT_LOAD (0x10000, 0x1f984 bytes, read-only), so arodata_okP covers them. *)
Lemma b_next_div3_check :
  grant_obj 34 = 0x10320 /\
  map (fun j => romB8 (grant_obj 34 + Z.of_nat j)) (seq 0 8) = map Some [0xab; 0xaa; 0xaa; 0xaa; 0xaa; 0xaa; 0xaa; 0xaa] /\
  0xab + 256 * (0xaa + 256 * (0xaa + 256 * (0xaa + 256 * (0xaa + 256 * (0xaa + 256 * (0xaa + 256 * 0xaa)))))) =
    12297829382473034411 /\
  IMG_LO_B + 64 <= grant_obj 34 /\ grant_obj 34 + 8 + 64 <= IMG_TOP_B.
Proof.
  repeat split; try (vm_compute; reflexivity);
  rewrite ?IMG_LO_B_val, ?IMG_TOP_B_val; vm_compute; discriminate.
Qed.

(* ===== laystamp ===== *)
(* ---- laystamp: the address-free names of ctrl_finish, ctrl_lay_block, reac_ctrl_stamp_headamp and
   reac_ctrl_build_grant_sweep ------------------------------------------------------------------------------------ *)
Module BImg := OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog.GrantImg.
(* The machine stack each call needs below its entry sp: its own frame, the 16 bytes `andi sp,sp,-32` may drop (sp is
   16-aligned at entry, so the realigned sp is 0 or 16 bytes lower), and the deepest callee's need, which ends in
   ESTACK (what the runtime's entries use below sp). The frames on the side stack for frames are not on the machine
   stack, and the machine-stack carves are refuted; neither is counted. *)
(* ctrl_finish: own 16 (0x83fdc), then reac_ctrl_record_cksum_stamp's 16 (0x82694) and ESTACK below it; the
   tail-jump to reac_ctrl_block_cksum_stamp at 0x84094 releases the 16 first. *)
Definition STK_ctrl_finish : Z := 16 + 16 + ESTACK.
(* ctrl_lay_block: own 128 (0x83bfc) and the andi (0x83c38); __asan_stack_malloc_1, __asan_memset and
   __asan_memcpy each use ESTACK. *)
Definition STK_ctrl_lay_block : Z := 128 + 16 + ESTACK.
(* reac_ctrl_stamp_headamp: own 96 (0x8326c) and the andi (0x832a4); ctrl_lay_block is the deepest callee
   (STK_ctrl_finish is less, __asan_stack_malloc_0 uses ESTACK). *)
Definition STK_reac_ctrl_stamp_headamp : Z := 96 + 16 + STK_ctrl_lay_block.
(* reac_ctrl_build_grant_sweep: own 256 (0x8363c) and the andi (0x8367c); reac_ctrl_stamp_headamp is the deepest
   callee (every runtime entry it calls uses ESTACK). laystamp_numbers checks the sum: 528 + ESTACK. *)
Definition STK_reac_ctrl_build_grant_sweep : Z := 256 + 16 + STK_reac_ctrl_stamp_headamp.
(* ctrl_lay_block's switch: the index is the row's byte +2 (`lbu` at 0x83d5c), bounded by `li a1,9; bltu a1,a0`
   (0x83d60 / 0x83d64: an index above 9 goes to 0x83e4c), and the `jr a0` at 0x83d84 goes to B_JT_LAY + entry
   (object 26, 0x21034, 10 sign-extended 4-byte entries). The ten targets, as slots (offsets from the listing's
   base 0x80a3c) that GrantImg.v lay_jt_slots holds and grant_lay_jt_check / jt_ok_entry check by computation:
     entry 0  slot 0x3444  0x83e80  no body: straight to the argument copy
     entry 1  slot 0x334c  0x83d88  the inline loop that stores 0x00 / 0x7a over the 32 bytes
     entry 2  slot 0x33d4  0x83e10  the template case: __asan_memcpy (p + 18, the row's word +8, 32) at 0x83e7c
                                    (the entry the walked call takes: the row's byte +2 is 2)
     entry 3  slot 0x341c  0x83e58  a1 = 0, then reac_box_model_block at 0x83e64
     entry 4  slot 0x33c4  0x83e00  a1 = 5, then the call at 0x83e64
     entry 5  slot 0x3400  0x83e3c  a1 = 1, then the call at 0x83e64
     entry 6  slot 0x3408  0x83e44  a1 = 2, then the call at 0x83e64
     entry 7  slot 0x33f8  0x83e34  a1 = 3, then the call at 0x83e64
     entry 8  slot 0x3418  0x83e54  a1 = 4, then the call at 0x83e64
     entry 9  slot 0x33cc  0x83e08  a1 = 6, then the call at 0x83e64
     index > 9    slot 0x3410  0x83e4c  a1 = -1, then the call at 0x83e64
   LAY_BOX_SLOTS holds every arm that reaches the call of reac_box_model_block at 0x83e64: entries 3 .. 9 and the
   arm of an index above 9 (ctrl_lay_block + 0x250). *)
Definition LAY_TMPL_ENTRY : nat := 2%nat.
Definition LAY_BOX_SLOTS : list Z := skipn 3 BImg.lay_jt_slots ++ [AF_ctrl_lay_block + 0x250].
(* GRANT_HEAD_ACK and GRANT_HEAD_MARK: objects 22 and 23 on image B (0x21200 / 0x21260, 34 bytes each). *)
Definition B_ACK : nat := 22%nat.
Definition B_MARK : nat := 23%nat.
(* The rows reac_ctrl_build_grant_sweep lays for a width w, and the arguments it accepts (0x837f4 .. 0x8384c):
   s <> 0, V <> 0, 1 <= w, base + w <= 48, 8 + 3 w <= mx. *)
Definition bgs_rows (w : Z) : Z := 8 + 3 * w.
Definition bgs_ok (s V mx base w : Z) : Prop :=
  s <> 0 /\ V <> 0 /\ 1 <= w /\ base + w <= 48 /\ bgs_rows w <= mx.
(* [a, a + n) and [b, b + m) are apart. *)
Definition ls_apart (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.
(* Image B's numbers: entry 2's slot is the template case 0x83e10 = ctrl_lay_block + 0x214, it is none of the arms
   that call reac_box_model_block, and the sweep's stack is 528 + ESTACK. *)
Lemma laystamp_numbers :
  (nth LAY_TMPL_ENTRY BImg.lay_jt_slots 0,
   existsb (Z.eqb (nth LAY_TMPL_ENTRY BImg.lay_jt_slots 0)) LAY_BOX_SLOTS,
   STK_reac_ctrl_build_grant_sweep - ESTACK) = (AF_ctrl_lay_block + 0x214, false, 528).
Proof. vm_compute. reflexivity. Qed.

(* ===== grant ===== *)
(* The rows reac_grant_build_sweep has written at return (through reac_ctrl_build_grant_sweep), as a footprint: the
   8 + 3 * w rows of 34 bytes at s, when the call admits its arguments (BuildSweepModel.bsw_ok). *)
Definition tb_reac_grant_build_sweep_FP (s al mx base w : Z) : list (Z * Z) :=
  if bsw_ok s al mx base w then [(s, s + 34 * (8 + 3 * w))] else [].
(* The side-stack class reac_grant_build_sweep takes at 0x85674 (`li a0,192; jal __asan_stack_malloc_2`): class 2
   has 256-byte frames (the flag pointer at F + 248) and 4096 frames per thread (kStackSizeLog 20). *)
Lemma grant_b_class2_sizes : ((fs_frame_bytes 2 =? 256) && (fs_frames 2 =? 4096))%bool = true.
Proof. vm_compute. reflexivity. Qed.

(* ===== parsegroupa ===== *)
(* parsegroupa: image B's numbers that the statements of reac_ctrl_parse and check_groupa use, checked by
   computation over image B's segments: .str.4 (object 15, grant_obj 15 = 0x21060) begins with six bytes 0xff;
   __const.check_groupa.frame (object 9, grant_obj 9 = 0x20fc0) begins with T0z (lib/Prog/GroupaModel.v); both are
   in image B's list of registered globals, with sizes 7 and 50; the side stack for frames holds 8192 frames of
   class 1 and 4096 frames of class 2. *)
Lemma parsegroupa_img_check :
  (map (fun i => romB8 (grant_obj 15 + Z.of_nat i)) (seq 0 6),
   map (fun i => romB8 (grant_obj 9 + Z.of_nat i)) (seq 0 50),
   existsb (fun g => andb (fst g =? grant_obj 15) (snd g =? 7)) GRANT_GLOBS_B,
   existsb (fun g => andb (fst g =? grant_obj 9) (snd g =? 50)) GRANT_GLOBS_B,
   fs_frames 1, fs_frames 2)
  = (repeat (Some 255) 6, map Some (T0z ++ repeat 0 34), true, true, 8192, 4096).
Proof. vm_compute. reflexivity. Qed.

(* ===== entry ===== *)
(* LLVMFuzzerTestOneInput's interface on image B, from the driver target_run (0x8086c): `jal 0x80a3c` at 0x80934
   (word 0x108000ef) returns to 0x80938; the driver passes s1 = s4 + 16 (0x80918) for an empty input, with
   s4 = target_run.initialized = 0x808a0 + 0x557000 + 1840 (`auipc a1,0x557` 0x808a0, `addi s4,a1,1840` 0x808a4),
   so its static empty buffer is 0x5d7fe0. *)
Definition RA_LLVMF_B : Z := 0x80938.
Definition A_EMPTY_B : Z := 0x5d7fe0.
(* The library shape's bounds for the whole call (the driver contract's EV_LIB / LIVE_LIB / LLVMF_STK; they name no
   address). The stack bound: image B's worst need is 17566 bytes below the entry sp (the 288-byte frame, at most 16
   bytes lost to `andi sp,sp,-32` at 0x80a7c, and the deepest callee path), under 32768. *)
Definition EV_LIB_B : Z := 2000.
Definition LIVE_LIB_B : Z := 2 ^ 33.
Definition STK_LLVMFuzzerTestOneInput : Z := 32768.
(* The three calls of the malloc wrapper (the `jal` at 0x80db4, 0x813d0, 0x818b4) and the three of the free wrapper
   (0x81808, 0x81940, 0x81da8), as offsets from the function's first slot of the RETURN of each, which is the call's
   address plus 4 (0x80db8, 0x813d4, 0x818b8 and 0x8180c, 0x81944, 0x81dac): the call sites whose call trace the
   wrappers' contracts ask for. *)
Definition TB_LLVMF_MSITES : list Z := [0x37c; 0x998; 0xe7c].
Definition TB_LLVMF_FSITES : list Z := [0xdd0; 0xf08; 0x1370].
(* asan.module_ctor / asan.module_dtor: a 16-byte frame (ra at sp + 8), then each runtime call's ESTACK. *)
Definition STK_asan_module_ctor : Z := 16 + ESTACK.
Definition STK_asan_module_dtor : Z := 16 + ESTACK.
(* The numbers above, checked on image B: the class-4 frame LLVMFuzzerTestOneInput takes at 0x80ab0 has 1024 bytes
   and 1024 frames per thread (so `frames S = []` gives live_ok 4 S); the driver's words at 0x80934 (the call),
   0x808a0 / 0x808a4 / 0x80918 (the empty buffer), and the empty buffer's address computed from them. *)
Lemma tb_llvmf_b_numbers :
  (fs_frame_bytes 4, fs_frames 4, romB32 (RA_LLVMF_B - 4), romB32 0x808a0, romB32 0x808a4, romB32 0x80918, A_EMPTY_B)
  = (1024, 1024, Some 0x108000ef, Some 0x557597, Some 0x73058a13, Some 0x10a0493, 0x808a0 + 0x557 * 4096 + 1840 + 16).
Proof. vm_compute. reflexivity. Qed.


Section D. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The sink head stays a section variable: the consumer passes image B's own ASan sink head. No instance of
   sink_head is in this file's Require closure (lib/Reusable/YI5b.v, the plain build's, is not). *)
Context {SK : YI16.sink_head}.

(* ---- the form's consequence: a proved contract excludes every error step ----------------------------- *)
Lemma contract_error_free : forall (segs : list Segment) (W : world segs) (c : config) (Q : world segs -> config -> Prop),
  SRr segs W c Q -> AI segs (w_H W) (w_A W) (cfg_model c) ->
  forall T, (forall W' c', wle W W' -> AI segs (w_H W') (w_A W') (cfg_model c') -> Q W' c' -> srealizes segs c' T) ->
  ~ reaches_error_cfg segs ACFG c.
Proof. intros segs W c Q H HI T HK. exact (srealizes_no_error segs c T (H HI T HK)). Qed.

Section F.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* The shadow offset of this runtime (the same in every unit). *)
Definition SB : Z := 0x7fff8000.
(* reac_ctrl_stamp_headamp's control-frame row CTRL_FRAMES[CTRL_HEADAMP]: object 18 is CTRL_FRAMES + 0 on image B
   (0x9d3e0; on image A object 18 is the row itself), so the row is object 18 + 240 = 0x9d4d0
   (GrantImg.v grant_row_val checks the number). Its byte +2 is 2 (BLOCK_TMPL). *)
Definition B_ROW : Z := VAL (A_OBJ 18) + 240.
(* ctrl_lay_block's jump table (object 26, 0x21034, 10 entries; GrantImg.v grant_lay_jt_check). *)
Definition B_JT_LAY : nat := 26%nat.
(* GRANT_GROUPB (object 19, 0x21080; 204 bytes, byte-identical to image A's 0x21040). *)
Definition B_GROUPB : nat := 19%nat.

Section H.
Variable B : asyms.

(* ---- the runtime callees, by name ------------------------------------------------------------------------
   A walk takes these as Section hypotheses (hyps_f lists each walk's). None is proved here; their owners prove
   them at image B's addresses (GrantImg.v grant_rt_sigma checks SIGMA of each). *)
Definition RT_LAWS : Prop := AR_laws SEGS B.
Definition RT_PALIB : Prop := PALib B.
Definition RT_PALIBF : Prop := PALibF B.
Definition RT_ML : Prop := model_laws (as_universe B).
Definition RT_SMP : Prop := stack_malloc_progressP B.
Definition RT_ASF : Prop := astack_free_law SEGS B.
Definition RT_FFL : Prop := frame_flag_lawP SEGS B.
(* the wrappers' 4-byte jumps of malloc / free (0x52edc / 0x52ed8); PALib ties SIGMA to pc_wrap_malloc / free *)
Definition RT_MALLOC : Prop := amalloc_realizes SEGS B.
Definition RT_FREE : Prop := afree_realizes SEGS B.
(* __asan_memcpy 0x51b88 / __asan_memset 0x52024 (the B core relocates cgif's YE2q / YE2r) *)
Definition RT_MEMCPY : Prop := aintrin_realizes SEGS B OCpy (SIGMA GS___asan_memcpy).
Definition RT_MEMSET : Prop := aintrin_realizes SEGS B OSet (SIGMA GS___asan_memset).
(* the bcmp wrapper's 4-byte jump 0x424d0 (2 * ESTACK below sp) *)
Definition RT_BCMP : Prop := abcmp_realizes SEGS B (SIGMA GS___interceptor_trampoline_bcmp).
(* __asan_stack_malloc_c, c = 0 1 2 4 6 (0x3cf4c 0x3d0c0 0x3d250 0x3d3ec 0x3d5b8); class 6 is libreac/fuzz_disco's form,
   relocated with image B's constants (FS_N 256, FS_FLOFF 0x8e00, FS_B 4096, FS_FROFF 0x609000, FS_HOFF 0x30,
   kFakeStackSize 0xb09000, FS_WIN 192). The class contract reads the fake stack's thread-local pointer; that
   dependency is RT_TP_FS, a named premise of every walk that takes RT_SM. *)
Definition RT_SM (c : Z) : Prop := astack_malloc_realizes SEGS B c.
(* __asan_stack_free_6 0x3d754 (lib/Reusable/StackFreeDef.v, a working branch c3bfa00452c) *)
Definition RT_SF6 : Prop := StackFreeDef.astack_free_realizes SEGS B (SIGMA GS___asan_stack_free_6) 6.
(* __asan_set_shadow_00 / _f5 / _f8 (0x54a48 / 0x54b50 / 0x54b68) *)
Definition RT_SS00 : Prop := SetShadowDef.aset_shadow_realizes SEGS B (SIGMA GS___asan_set_shadow_00) 0x00.
Definition RT_SSF5 : Prop := SetShadowDef.aset_shadow_realizes SEGS B (SIGMA GS___asan_set_shadow_f5) 0xf5.
Definition RT_SSF8 : Prop := SetShadowDef.aset_shadow_realizes SEGS B (SIGMA GS___asan_set_shadow_f8) 0xf8.
(* The shadow of image B's read range is mapped, and image B's 13 registered globals are marked (whole granules in
   as_zero_shadow, the last partial granule `size mod 8`): GrantRo.v's two facts, over GrantTop.v's GRANT_GLOBS_B. *)
Definition RT_IMGSH : Prop := img_shadow_vis SEGS B.
Definition RT_GLOBS : Prop := globs_marked SEGS B GRANT_GLOBS_B.
(* RT's thread part: the fake stack's thread-local pointer
   __asan::fake_stack_tls (image B's PT_TLS offset 0, RT_TP) is not established at main on the originals for every
   unit. No contract here rests on an at-main invariant for it: a walk that needs it (every walk that takes a
   side-stack frame, through RT_SM) takes this named premise. *)
Definition RT_TP_FS : Prop :=
  forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> rdword (aview SEGS (w_H W) mem) (as_tp B) = Some (ly_F ly).

(* ---- the caller-journal shapes (image B restatement of lib/A/Prog/CtrlFinish.v's, over SEGS of image B) --- *)
(* What a call keeps: everything but its own stack window and the bytes E it is allowed to write
   (cgif lib/YC20.v:311-323). *)
Definition tcj_kept (STK : Z) (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
(W2 : world SEGS) (mem2 : word -> option byte) (sp : Z) (E : Z -> Prop) : Prop :=
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> ~ E a ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall cid pos a, In (cid, pos) (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK <= a < sp) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
(forall a, sp - STK <= a < sp -> apresent (w_H W2) mem2 a).
(* The caller's right to let the call write [q, q + n) (cgif lib/YC20.v:358-359). *)
Definition twr_ok (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
(lyc : alayout) (Sc : astate) (own : list (Z * Z)) (W : world SEGS) (memc : word -> option byte)
(sp q n : Z) : Prop :=
forall a, q <= a < q + n ->
awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a /\
apresent (w_H W) memc a /\ ~ aowned B lyc Sc a /\ ~ (sp - ESTACK <= a < sp).
(* A range the call reads. *)
Definition tsrc_ok (W : world SEGS) (memc : word -> option byte) (sp q n : Z) : Prop :=
(forall a, q <= a < q + n -> aview SEGS (w_H W) memc a <> None /\ ~ (sp - ESTACK <= a < sp)) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q n /\
shadow_hull_vis (aview SEGS (w_H W) memc) q n /\ amem_range q n /\ 0 <= q /\ q + n <= 2 ^ 63.
(* The partial-granule form of "the byte at x is addressable" that the instrumented check tests, and that the walk
   engine's shadow entries and the checked-copy contract both ask for: the kit's `range_addressable`
   (lib/Reusable/YG0v.v:29,33 - the shadow byte s of x's granule is 0, or (x mod 8) < s < 8). A caller that hands
   over a buffer whose last granule is partial (the harness marks those shadow bytes 0x01 / 0x02 / 0x04) meets this
   form, not `s = 0`. `bytes_ok` is the name this file uses for it. *)
Definition bytes_ok (W : world SEGS) (mem : word -> option byte) (x n : Z) : Prop :=
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x n.
Definition byte_ok (W : world SEGS) (mem : word -> option byte) (x : Z) : Prop := bytes_ok W mem x 1.
(* The per-class live-frame bound a side-stack caller discharges at its own call site (astack_malloc_realizes's
   `count_cid cid (frames S) < fs_frames cid`, YG0d.v:288). *)
Definition live_ok (c : Z) (S : astate) : Prop := count_cid c (frames S) < fs_frames c.

(* ==== the three code-identical functions: contracts and walks RELOCATED from image A ======================
   kind_of_link1 0x831f8 (29 instructions), reac_headamp_tx_init 0x85a70 (8), reac_headamp_default 0x85bf0 (4):
   image B's listing slots equal image A's slot for slot. kind_of_link1 (29 words) and reac_headamp_default (4) are
   byte-identical between the two images; reac_headamp_tx_init is identical MODULO RELOCATION: 7 of its 8 words are
   equal and the eighth is the call of __asan_memset, whose offset differs (image A 0x84d2c, image B 0x85a80). The
   listing slot is the same in both (`PCall GS___asan_memset`), which is what the walk reads (lib/B/Prog/
   KindOfLink1.v, HeadampTxInit.v, HeadampDefault.v hold image A's text over image B's walk layer and compile). *)
Definition tb_kind_of_link1_spec : Prop := KindOfLink1.tkind_of_link1_spec B.
Definition hyps_kind_of_link1 : Prop := RT_LAWS.
Definition walk_kind_of_link1 : Prop := hyps_kind_of_link1 -> tb_kind_of_link1_spec.
Lemma pb_walk_kind_of_link1 : walk_kind_of_link1.
Proof. intros HL. exact (KindOfLink1.pb_kind_of_link1 B HL). Qed.
Definition tb_reac_headamp_tx_init_spec : Prop := HeadampTxInit.treac_headamp_tx_init_spec B.
Definition hyps_reac_headamp_tx_init : Prop := RT_LAWS /\ RT_MEMSET.
Definition walk_reac_headamp_tx_init : Prop := hyps_reac_headamp_tx_init -> tb_reac_headamp_tx_init_spec.
Lemma pb_walk_reac_headamp_tx_init : walk_reac_headamp_tx_init.
Proof. intros [HL HM]. exact (HeadampTxInit.pb_reac_headamp_tx_init B HL HM). Qed.
Definition tb_reac_headamp_default_spec : Prop := HeadampDefault.treac_headamp_default_spec B.
Definition hyps_reac_headamp_default : Prop := RT_LAWS.
Definition walk_reac_headamp_default : Prop := hyps_reac_headamp_default -> tb_reac_headamp_default_spec.
Lemma pb_walk_reac_headamp_default : walk_reac_headamp_default.
Proof. intros HL. exact (HeadampDefault.pb_reac_headamp_default B HL). Qed.

(* ================================================= headamp ================================================= *)
(* ==== fragment headamp: reac_headamp_tx_set 0x85a90, reac_headamp_tx_effective 0x85c00,
   reac_headamp_tx_arm_scene 0x85ce4, reac_headamp_tx_set_resweep 0x85e78, reac_headamp_tx_next 0x85efc ========
   The table at tx is the 460-byte head-amp table. The harness gets it from malloc(460) (0x80db4), so it is a heap
   block of the caller: `In (tx, ATx.TX_SIZE) (ablocks B ly S)`. ATx.LAY_TX and ATx.tx_vals give its layout
   (0..143 value, 144..287 set, 288..431 dirty, 432 active (4), 436 replay_base, 437 replay_width,
   440 replay_idx (4), 444 replay_wait (4), 448 replay_set_only, 449 scene_base, 450 scene_width,
   452 resweep_period (4), 456 resweep_wait (4)). AR's block law (YG0d.v AR_blocks_law) gives tx mod 16 = 0,
   4096 <= tx and tx + 460 <= alloc_ceiling (< 2^47); with these every trap guard of the four leaves is false
   (tx <> 0, tx mod 4 = 0, tx + 431 < 2^64 for tx_set, tx + 287 < 2^64 for tx_effective). AR's shadow law gives
   the 460 bytes addressable in the partial-granule form (range_addressable_of_block): bytes 0..455 are 57 whole
   granules (shadow 0), bytes 456..459 are the last granule (shadow 4). The check before each 4-byte access at
   tx + 456 (arm_scene 0x85dd8, set_resweep 0x85ec0, tx_next 0x860f0 / 0x862b4 / 0x86308 / 0x86438) takes its
   second test on every call (shadow 4 <> 0). reac_headamp_tx_next's contract states that byte range as
   `bytes_ok W memc (tx + 456) 4` (kept, though its walk does not need it); the walks of reac_headamp_tx_arm_scene and
   reac_headamp_tx_set_resweep refute it from the block's own shadow entry (mkSHE 10 0 460) and their contracts state
   nothing.
   Before its first table access each function reads the GOT word 0x9d6d0 (object 1) and, through it, the
   shadow-base cell 0xa5978 (object 35):
   RT_PALIB (pal_got_shadow, pal_cell) gives both. None of the five reads tp, the thread-local cells or errno; none
   takes a frame on the side stack for frames, so no live_ok obligation and no RT_TP_FS. *)

(* reac_headamp_tx_set(tx, ch, p, v), 0x85a90: frame 16 (addi sp,sp,-16; ra saved at sp + 8), no live call (ESTACK
   below the frame is what the runtime's error-path entries use, as for every leaf here). For ch < 48 and
   (p < 2 and v <= 1, or p = 2 and v <= 55) it does the 1-byte stores v at tx + 3ch + p, 1 at tx + 144 + 3ch + p,
   1 at tx + 288 + 3ch + p and the 4-byte store 1 at tx + 432, and returns 0 in a0; else it writes nothing and
   returns -1. Trap 0x85bac (guards 0x85ad0 tx = 0, 0x85ad8 tx mod 4, and the checks that tx + off does not pass
   2^64 at 0x85ae8 / 0x85afc / 0x85b20 / 0x85b2c / 0x85b54 / 0x85b60) is not reached for a live block; the error-path
   branches 0x85bbc / 0x85bcc / 0x85bdc (store1) and 0x85bec (store4, the last slot, which falls into
   reac_headamp_default 0x85bf0) are false from the block's shadow (whole granules). *)
Definition STK_reac_headamp_tx_set : Z := 16 + ESTACK.
Definition tb_reac_headamp_tx_set_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (tx ch p v : Z)
  (T : list byte) : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_reac_headamp_tx_set (thd_set_fp tx ch p v) regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       ly' = ly /\ S' = S /\ W' = W /\
       getr regs' 10 = w64 (if ((ch <? 48) && legalb p v)%bool then 0 else -1) /\
       obj_at SEGS (mrestrict (w_H W) mem') tx ATx.LAY_TX (ATx.tx_vals (thd_set_T T ch p v))).
Definition tb_reac_headamp_tx_set_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (tx ch p v : Z) (T : list byte),
  afn_pre SEGS B STK_reac_headamp_tx_set ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 ch -> getr regs 12 = w64 p -> getr regs 13 = w64 v ->
  0 <= ch < 256 -> 0 <= p < 256 -> 0 <= v < 256 ->
  In (tx, ATx.TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) mem) tx ATx.LAY_TX (ATx.tx_vals T) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_headamp_tx_set) regs mem md)
    (tb_reac_headamp_tx_set_post regs ly S W mem md tx ch p v T).
Definition hyps_reac_headamp_tx_set : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_headamp_tx_set : Prop := hyps_reac_headamp_tx_set -> tb_reac_headamp_tx_set_spec.

(* reac_headamp_tx_effective(tx, ch, p), 0x85c00: frame 16 (ra saved at sp + 8), no live call, writes no byte
   outside its frame. For p > 2 it returns 0; for tx = 0 (the test at 0x85c18 is C's `t &&`, not a trap) or
   ch > 47 it returns dflt p (32 for p = 2, else 0); else it loads the set byte at tx + 144 + 3ch + p and, when that
   byte is not 0, returns the value byte at tx + 3ch + p, else dflt p: a0 = eff T tx ch p. The contract ALLOWS
   tx = 0 (it then reads no table byte) and any ch, p below 256 (reac_headamp_tx_next's call 0x863dc passes
   c & 0xff and p & 0xff). Trap 0x85cc4 (guards 0x85c28 tx mod 4, and the checks that tx + off does not pass 2^64
   at 0x85c3c / 0x85c50 / 0x85c80 / 0x85c8c) is not reached for a live block; the error-path branches 0x85cd4 and
   0x85ce0 (load1, the latter the last slot, which falls into reac_headamp_tx_arm_scene 0x85ce4) are false from
   the block's shadow. apost_base keeps sp, gp, tp, s0..s11 (aregs_preserved): s2..s10 of reac_headamp_tx_next
   live across the call. *)
Definition STK_reac_headamp_tx_effective : Z := 16 + ESTACK.
Definition tb_reac_headamp_tx_effective_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (tx ch p : Z)
  (T : list byte) : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_reac_headamp_tx_effective [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       ly' = ly /\ S' = S /\ W' = W /\ getr regs' 10 = w64 (eff T tx ch p) /\
       (tx <> 0 -> obj_at SEGS (mrestrict (w_H W) mem') tx ATx.LAY_TX (ATx.tx_vals T))).
Definition tb_reac_headamp_tx_effective_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (tx ch p : Z) (T : list byte),
  afn_pre SEGS B STK_reac_headamp_tx_effective ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 ch -> getr regs 12 = w64 p ->
  0 <= ch < 256 -> 0 <= p < 256 -> length T = 460%nat ->
  (tx = 0 \/
   (In (tx, ATx.TX_SIZE) (ablocks B ly S) /\
    obj_at SEGS (mrestrict (w_H W) mem) tx ATx.LAY_TX (ATx.tx_vals T))) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_headamp_tx_effective) regs mem md)
    (tb_reac_headamp_tx_effective_post regs ly S W mem md tx ch p T).
Definition hyps_reac_headamp_tx_effective : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_headamp_tx_effective : Prop :=
  hyps_reac_headamp_tx_effective -> tb_reac_headamp_tx_effective_spec.

(* reac_headamp_tx_arm_scene(tx, sb, sw), 0x85ce4: frame 16, ra saved at sp + 8 (image A's frame is 48), no live call:
   image A's memset of tx + 440..448 is three stores here (4-byte 0 at 440 and 444, 1-byte 0 at 448). For sb > 47
   or sw = 0 it writes nothing. Else, with w = (sb + sw > 48 ? 48 - sb : sw), it does the 1-byte stores sb at
   tx + 436 and w at tx + 437, the 4-byte stores 0 at tx + 440 and tx + 444, the 1-byte stores 0 at tx + 448,
   sb at tx + 449 and w at tx + 450, and the 4-byte store 0 at tx + 456 (the block's last granule, shadow 4): the
   table becomes arm_T T sb sw. It writes replay_width (437) and replay_idx (440): the post keeps the table
   invariant thd_replay_ok. Trap 0x85dec (guards 0x85cf8 tx = 0, 0x85d00 tx mod 4) is not reached for a live block;
   the error-path branches 0x85dfc / 0x85e0c / 0x85e44 / 0x85e54 / 0x85e64 (store1) and 0x85e20 / 0x85e34 / 0x85e74
   (store4; 0x85e74 is the last slot, which falls into reac_headamp_tx_set_resweep 0x85e78) are false from the
   block's OWN shadow entry (mkSHE 10 0 460, whose last granule is the partial one, shadow 4), as for
   reac_headamp_tx_set_resweep. The premise `bytes_ok W mem (tx + 456) 4` that this contract once carried was REMOVED
   for that reason: the walk never used it (lib/B/Prog/HeadampTxArmScene.v:408-410 says why none is needed),
   so its callers owe nothing extra. *)
Definition STK_reac_headamp_tx_arm_scene : Z := 16 + ESTACK.
Definition tb_reac_headamp_tx_arm_scene_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (tx sb sw : Z)
  (T : list byte) : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_reac_headamp_tx_arm_scene
    [(tx + 436, tx + 438); (tx + 440, tx + 451); (tx + 456, tx + 460)] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       ly' = ly /\ S' = S /\ W' = W /\
       obj_at SEGS (mrestrict (w_H W) mem') tx ATx.LAY_TX (ATx.tx_vals (thd_arm_T T sb sw)) /\
       (thd_replay_ok T -> thd_replay_ok (thd_arm_T T sb sw))).
Definition tb_reac_headamp_tx_arm_scene_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (tx sb sw : Z) (T : list byte),
  afn_pre SEGS B STK_reac_headamp_tx_arm_scene ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 sb -> getr regs 12 = w64 sw ->
  0 <= sb < 256 -> 0 <= sw < 256 ->
  In (tx, ATx.TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) mem) tx ATx.LAY_TX (ATx.tx_vals T) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_headamp_tx_arm_scene) regs mem md)
    (tb_reac_headamp_tx_arm_scene_post regs ly S W mem md tx sb sw T).
Definition hyps_reac_headamp_tx_arm_scene : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_headamp_tx_arm_scene : Prop :=
  hyps_reac_headamp_tx_arm_scene -> tb_reac_headamp_tx_arm_scene_spec.

(* reac_headamp_tx_set_resweep(tx, per), 0x85e78: frame 16 (ra saved at sp + 8), no live call. It does the 4-byte
   store of the low 32 bits of a1 at tx + 452 and the 4-byte store 0 at tx + 456 (the block's last granule): the
   table becomes set_resweep_T T a1. It does not write 437 or 440. Trap 0x85ed4 (guards 0x85e80 tx = 0, 0x85e88
   tx mod 4) is not reached for a live block; the error-path branches 0x85ee8 and 0x85ef8 (store4, the latter the
   last slot, which falls into reac_headamp_tx_next 0x85efc) are false from the block's OWN shadow entry
   (rsw_SH = [mkSHE 10 0 460], lib/B/Prog/HeadampTxSetResweep.v:78), as image A discharges its 456 store. The
   premise `bytes_ok W mem (tx + 456) 4` that this contract once carried was REMOVED for that reason: the walk never
   used it, so the caller LLVMFuzzerTestOneInput owes nothing extra at the call 0x81a4c. *)
Definition STK_reac_headamp_tx_set_resweep : Z := 16 + ESTACK.
Definition tb_reac_headamp_tx_set_resweep_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (tx : Z)
  (T : list byte) : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_reac_headamp_tx_set_resweep [(tx + 452, tx + 460)] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       ly' = ly /\ S' = S /\ W' = W /\
       obj_at SEGS (mrestrict (w_H W) mem') tx ATx.LAY_TX
         (ATx.tx_vals (HdRswC.set_resweep_T T (getr regs 11)))).
Definition tb_reac_headamp_tx_set_resweep_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (tx : Z) (T : list byte),
  afn_pre SEGS B STK_reac_headamp_tx_set_resweep ly S W regs mem md ch0 ->
  getr regs 10 = w64 tx ->
  In (tx, ATx.TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) mem) tx ATx.LAY_TX (ATx.tx_vals T) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_headamp_tx_set_resweep) regs mem md)
    (tb_reac_headamp_tx_set_resweep_post regs ly S W mem md tx T).
Definition hyps_reac_headamp_tx_set_resweep : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_headamp_tx_set_resweep : Prop :=
  hyps_reac_headamp_tx_set_resweep -> tb_reac_headamp_tx_set_resweep_spec.

(* reac_headamp_tx_next(tx, chp, parp, valp), 0x85efc: frame 96 (image A's is 80): it saves ra and s0..s10 at
   sp + 88 .. sp + 0, takes no frame on the side stack for frames, and makes one call, reac_headamp_tx_effective at
   0x863dc (a0 = tx, a1 = c & 0xff, a2 = p & 0xff; s2..s10 live across it), whose window is the deepest: STK = 96 +
   STK_reac_headamp_tx_effective. It reads the 8-byte constant 0xAAAAAAAAAAAAAAAB at 0x10320 (object 34, listing
   slot 5466 `PLdHi t4 a0 67 (A_OBJ 34) 0 SZ8`; the multiplier of its division by 3 through mulhu, where image A
   divides by the immediate 171): arodata_okP gives that the byte is the image's, and IMG_NEXT_DIV3 gives its VALUE,
   as every other image byte a walk reads enters through an IMG_ premise. It also reads the GOT word /
   shadow-base cell. It reads and writes the table (the new table
   and the answer are NextModel.next_model T tx) and, when it answers 1, does the 1-byte stores c, p, v at chp,
   parp, valp: bytes of the caller's frame (the harness holds them in its class-4 frame and marks each with shadow
   1 at frame-shadow offsets 98 / 100 / 102), so the contract is in the caller-journal form (CtrlFinish's shape:
   tcj_kept / twr_ok). It writes replay_width (437) and replay_idx (440): the pre-condition carries
   thd_replay_ok T and the post gives thd_replay_ok of the new table. Trap 0x8644c, 18 guards: 0x85f30 tx = 0,
   0x85f3c tx mod 4, 0x85fd0 / 0x85ff0 (dirty-cell address checks), 0x8604c / 0x863a0 chp = 0, 0x86064 / 0x863b8
   parp = 0, 0x860b4 / 0x863e0 valp = 0, 0x860a4 / 0x860a8 / 0x860ac / 0x860b0 (value-cell address checks),
   0x86204 (c = replay_base + replay_idx / 3 as an unsigned number above 47) and 0x86214 (replay_idx mod 3 < 0),
   both false from thd_replay_ok since the scan runs only for replay_width <> 0, and 0x86210 / 0x86220 (set-cell
   address checks); and the fall-through of the error-path call 0x86448 (store4 at tx + 456) into 0x8644c, false
   from `bytes_ok W memc (tx + 456) 4`. The 35 error-path branches (load1 0x8603c 0x8625c 0x86498 0x864c8 0x864d4
   0x86518 0x86558 0x86568 0x86584; load4 0x8645c 0x864e8 0x864f8 0x8652c 0x8653c 0x86610; store1 0x8646c 0x8647c
   0x8648c 0x864a8 0x8654c 0x86594 0x865a4 0x865d4 0x865e4 0x865f4 0x86604 0x86634; store4 0x86448 0x864b8 0x8650c
   0x86578 0x865b4 0x865c4 0x86624 0x8663c, the last one the last slot, which falls into __wrap_getenv 0x86640)
   are false from the block's shadow and byte_ok of chp, parp, valp. The premise `bytes_ok W memc (tx + 456) 4`:
   the walk does not need it; its tx + 456 stores are covered by the block's own shadow entry (a Theorem Labs lane's build on
   00912ab7565 without it, an internal build log); it is kept because it is true and the entry walk proves it at
   0x81bd8. reac_headamp_tx_arm_scene's and reac_headamp_tx_set_resweep's were dropped (unused there). *)
Definition STK_reac_headamp_tx_next : Z := 96 + STK_reac_headamp_tx_effective.
(* Where one of the three bytes the caller holds must lie: above page 0 and below 2^47, clear of the table, of
   this call's own stack window, of the image and of the shadow map. *)
Definition thd_out_ok (sp tx q : Z) : Prop :=
  4096 <= q /\ q + 1 <= 2 ^ 47 /\ ~ (tx <= q < tx + ATx.TX_SIZE) /\
  (q + 1 <= sp - STK_reac_headamp_tx_next \/ sp <= q) /\ ~ in_img SEGS q /\
  ~ (SHADOW_OFF <= q < SHADOW_OFF + 2 ^ 44).
Definition tb_reac_headamp_tx_next_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (tx chp parp valp : Z) (T : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\
    tcj_kept STK_reac_headamp_tx_next lyc Sc W memc W2 mem2 (spZ regs)
      (fun a => (tx <= a < tx + ATx.TX_SIZE) \/ a = chp \/ a = parp \/ a = valp) /\
    match HdNx.next_model T tx with
    | (r, (c, p, v), T') =>
        getr regs2 10 = w64 r /\
        obj_at SEGS (mrestrict (w_H W2) mem2) tx ATx.LAY_TX (ATx.tx_vals T') /\
        thd_replay_ok T' /\
        (r = 1 -> aview SEGS (w_H W2) mem2 chp = Some c /\
                  aview SEGS (w_H W2) mem2 parp = Some p /\
                  aview SEGS (w_H W2) mem2 valp = Some v) /\
        (r = 0 -> aview SEGS (w_H W2) mem2 chp = aview SEGS (w_H W) memc chp /\
                  aview SEGS (w_H W2) mem2 parp = aview SEGS (w_H W) memc parp /\
                  aview SEGS (w_H W2) mem2 valp = aview SEGS (w_H W) memc valp)
    end.
(* tb_reac_headamp_tx_next_spec AGAINST IMAGE A's theadamp_tx_next_spec (lib/A/Prog/HeadampTxNext.v:178-206),
   premise by premise, for an internal ledger row:
   - DROPPED `achain lyc .. (spZ regs) (s0Z regs) ch`: image B's code keeps no frame pointer; s0 := tx at 0x85f34,
     before its only call (0x863dc). So at that call s0 is the table, a heap block, below alloc_ceiling (every heap
     section ends at or below alloc_ceiling, YG0n.v:195), and the callee's afn_pre chain is achain's first case with
     the empty chain, whatever the caller's chain is. Neither image's post states a chain.
   - DROPPED `forall a, spZ regs - NEXT_STK <= a < spZ regs -> apresent ..`: implied. ajournal gives every byte of
     [sp0 - STK, sp0) present (YCbq.v:367), and `sp0 - STK <= spZ regs - STK_reac_headamp_tx_next`, `spZ regs <= sp0`
     put this call's window inside it.
   - DROPPED `I1 T` (lib/Prog/SlotNeeds_c.v:22), REPLACED by `thd_replay_ok T`: of I1's clauses only the sign of
     replay_idx reaches a trap guard of image B's code. 0x86204 traps iff c = replay_base + replay_idx / 3 is negative
     (the signed branch 0x86200 sends c > 47 to the C code's own path first), and 0x86214 iff replay_idx mod 3 < 0;
     both are false when replay_idx >= 0. next_model is total, and the post claims no clause of I1.
   - ADDED `thd_replay_ok T` (above); the post gives thd_replay_ok of the new table, so the next call has it.
   - ADDED `bytes_ok W memc (tx + 456) 4`: the block's last granule (shadow 4) in the partial-granule form. The walk
     does not need it (its tx + 456 stores are covered by the block's own shadow entry); it is kept because it is true
     and the entry walk proves it at 0x81bd8. Image A's spec has no such premise.
   - DROPPED the three `range_addressable .. SHADOW_OFF chp 1` (parp, valp): NOT dropped in substance. They are
     `byte_ok W memc chp` (parp, valp) here, which is the same statement: byte_ok W mem x := bytes_ok W mem x 1 :=
     range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x 1.
   - MAPPED `apresent (w_H W) memc chp` (parp, valp) INTO `twr_ok .. chp 1`, whose second conjunct is that apresent.
   - MAPPED `nx_may_write .. chp` (parp, valp) TO `twr_ok .. chp 1`: twr_ok's first conjunct is the same awr_byte with
     the same arguments; it adds apresent, ~ aowned and "not in this call's machine-stack window", which the caller
     has for bytes of its own frame.
   - MAPPED `forall a, tx <= a < tx + TX_SIZE -> nx_may_write .. a` TO `twr_ok .. tx ATx.TX_SIZE`: the same awr_byte
     for every table byte, plus the same three facts, which the caller has for a live block it holds.
   - MAPPED `nx_out_ok` TO `thd_out_ok`: the same clauses, except image A's literal bound
     `p + 1 <= 0x10000 \/ 0x5fa000 <= p` becomes `~ in_img SEGS q` (image-independent), and NEXT_STK becomes
     STK_reac_headamp_tx_next; the shadow bound 17592186044416 is 2 ^ 44 in both.
   - The entry `A_reac_headamp_tx_nextP` is `BASE + AF_reac_headamp_tx_next`; TX_SIZE / LAY_TX / tx_vals are ATx's
     (lib/Prog/HeadampLayout.v, the same definitions). *)
Definition tb_reac_headamp_tx_next_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
         (regs : bvmap 5 word) (tx chp parp valp : Z) (T : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 chp -> getr regs 12 = w64 parp -> getr regs 13 = w64 valp ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_headamp_tx_next -> spZ regs <= sp0 ->
  (* the table: a live block of the caller, its bytes, the replay invariant, the caller's right to write it *)
  In (tx, ATx.TX_SIZE) (ablocks B lyc Sc) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) memc) tx ATx.LAY_TX (ATx.tx_vals T) ->
  thd_replay_ok T ->
  bytes_ok W memc (tx + 456) 4 ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) tx ATx.TX_SIZE ->
  (* the three bytes the caller holds, each addressable for one byte in the partial-granule form *)
  thd_out_ok (spZ regs) tx chp -> thd_out_ok (spZ regs) tx parp -> thd_out_ok (spZ regs) tx valp ->
  chp <> parp -> chp <> valp -> parp <> valp ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) chp 1 ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) parp 1 ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) valp 1 ->
  byte_ok W memc chp -> byte_ok W memc parp -> byte_ok W memc valp ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_headamp_tx_next) regs memc mdc)
    (tb_reac_headamp_tx_next_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T).
(* The multiplier of the division by 3 (object 34, 0x10320 in image B's read-only PT_LOAD): its place inside the
   image with 64 bytes to spare, and its 8 bytes 0xAAAAAAAAAAAAAAAB = 12297829382473034411 through the read-only
   view. b_next_div3_check checks the address, the bytes and the bounds on image B by computation. *)
Definition IMG_NEXT_DIV3 : Prop :=
  IMG_LO + 64 <= VAL (A_OBJ 34) /\ VAL (A_OBJ 34) + 8 + 64 <= IMG_HI /\
  (forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
     val_mem SEGS (mrestrict H mem) (VAL (A_OBJ 34)) 8 12297829382473034411).
Definition hyps_reac_headamp_tx_next : Prop := RT_LAWS /\ RT_PALIB /\ IMG_NEXT_DIV3.
Definition walk_reac_headamp_tx_next : Prop :=
  hyps_reac_headamp_tx_next -> tb_reac_headamp_tx_effective_spec -> tb_reac_headamp_tx_next_spec.

(* ================================================= ctrlleaves ================================================= *)
(* ==== a Theorem Labs lane: want_of 0x82434, reac_ctrl_block_cksum_stamp 0x82554, reac_ctrl_checksum_verify 0x8260c,
   reac_ctrl_record_cksum_stamp 0x82694, reac_ctrl_headamp_record_verify 0x834dc,
   reac_ctrl_identity_poll_block 0x835dc.
   Every in-code check of these six is `lb s, shadow(x); bnez s; andi t, x, 7; blt t, s` (continue when s = 0 or
   (x mod 8) < s): the shadow premises are in the partial-granule form `range_addressable` (YG0v.v saddr_ok:
   s = 0, or (x mod 8) < s < 8), directly or as afobj's shadow conjunct. None of the six takes a frame on the side
   stack for frames, so none has a live_ok obligation. ======================================================= *)

(* ---- want_of 0x82434 (image B only; inlined on image A) -------------------------------------------------------
   want_of(w, v, c, p): a0 = w and a1 = v are two 144-byte tables of the caller (LLVMFuzzerTestOneInput loads them
   with ld 136(s1) / ld 128(s1) before each of its three calls 0x8163c, 0x816e8, 0x81c40), a2 = c the channel,
   a3 = p the parameter. The call reads the
   byte w[3c + p]. When it is 0, the call puts p in a0, restores ra and sp and jumps to reac_headamp_default
   (0x824cc, a tail call: the callee returns dflt p to want_of's caller). Else it reads v[3c + p] and returns it
   in a0. Frame 16 (ra at sp - 8), released before the tail jump, so the need is the callee's ESTACK, not
   16 + ESTACK. It writes nothing outside its frame. The value is lib/U/Prog/want_of_c.v's `want`, stated here
   with lib/Prog/HeadampModel.v's tb and dflt (want_of_c.v is not Required: its closure holds image U's snapshot
   through lib/U/Img0.v).
   Traps (unimp 0x824d0): 0x82448 (w + 3c carries past 2^64), 0x82450 (p >=u 3; the code cannot exclude it, so
   0 <= p < 3 is a premise), 0x8245c (w + 3c + p carries), 0x8248c (v + 3c carries), 0x82498 (v + 3c + p carries);
   the four carries are false from 0 <= w, v and amem_range. Report branches: 0x824dc (load1 at w + 3c + p; it
   returns into 0x824e0) and 0x824e8 (load1 at v + 3c + p, the last instruction; it returns into asan.module_ctor
   0x824ec): both false from the shadow premise of the byte read. *)
(* The premise `0 <= p < 3` (the guard `li a3,3; bgeu a3` at 0x82450 cannot be proved inside the function; image U's
   contract, lib/U/Prog/want_of.v, states the same). Its three call sites are all in LLVMFuzzerTestOneInput, and in
   each one the walk of that function discharges it from a path fact of its own:
     0x8163c  a3 = s10, the counter of the loop 0x81618 .. 0x81664 (s10 := 0 at 0x8160c, s5 := s10 + 1 at 0x81628,
              s10 := s5 at 0x81660, `bne s5,s4` with s4 = 3 at 0x81664): 0 <= s10 <= 2 on every pass;
     0x816e8  a3 = s10 = zext.b s7 (0x816d4), s7 the counter of the loop 0x81684 .. 0x81708 (s7 := 0 at 0x81684,
              s7 := s7 + 1 at 0x81704, `bne s7,s6` with s6 = 3 at 0x81708): 0 <= s7 <= 2 on every pass;
     0x81c40  a3 is the byte loaded at 0x81c24, and the branch `bltu s11,a3` at 0x81c28 with s11 = 2 (0x81b78)
              leaves the call only when a3 <= 2.
   No premise of tb_LLVMFuzzerTestOneInput_spec is needed for it. *)
Definition STK_want_of : Z := ESTACK.
Definition tb_want_of_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (WS VS : list byte) (c p : Z)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_want_of [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\
       getr regs' 10 = w64 (if tb WS (3 * c + p) =? 0 then dflt p else tb VS (3 * c + p))).
Definition tb_want_of_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch (w v c p : Z) (WS VS : list byte),
  afn_pre SEGS B STK_want_of ly S W regs mem md ch ->
  getr regs 10 = w64 w -> getr regs 11 = w64 v -> getr regs 12 = w64 c -> getr regs 13 = w64 p ->
  0 <= c < 48 -> 0 <= p < 3 ->
  (* the two tables; the call reads index 3c + p of each *)
  length WS = 144%nat -> garr8 SEGS (mrestrict (w_H W) mem) w (map bv_unsigned WS) ->
  length VS = 144%nat -> garr8 SEGS (mrestrict (w_H W) mem) v (map bv_unsigned VS) ->
  0 <= w -> amem_range w 144 -> (w + 144 <= IMG_LO_B \/ IMG_TOP_B <= w) ->
  0 <= v -> amem_range v 144 -> (v + 144 <= IMG_LO_B \/ IMG_TOP_B <= v) ->
  (w + 144 <= v \/ v + 144 <= w) ->
  (spZ regs <= w \/ w + 144 <= spZ regs - STK_want_of) ->
  (spZ regs <= v \/ v + 144 <= spZ regs - STK_want_of) ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (w + (3 * c + p)) 1 ->
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (v + (3 * c + p)) 1 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_want_of) regs mem md) (tb_want_of_post regs ly S W mem md WS VS c p).
Definition hyps_want_of : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_want_of : Prop := hyps_want_of -> tb_reac_headamp_default_spec -> tb_want_of_spec.

(* ---- reac_ctrl_block_cksum_stamp 0x82554 (image B only; inlined into ctrl_finish on image A) ------------------
   a0 = q, the caller's 32-byte control block (ctrl_finish passes p + 18 by the tail jump at 0x84094). The call
   sums the 31 bytes q[0..31) and stores the low byte of the negated sum at q + 31 (lib/Prog/RcFin.v stamp32). It
   writes no other byte outside its own 16-byte frame and returns no value. It writes a byte of its caller's block,
   so the contract is in the caller-journal form (image A's CtrlFinish.v). Frame 16; it takes no call (both report
   calls are refuted), so its need is 16.
   Trap (unimp 0x825fc): 0x8257c (q + j <u q), 0x82588 ((q <> 0) = (q + j = 0)), 0x8258c (q = 0), 0x825d0
   (q >=u 2^64 - 31): false from 0 < q and amem_range q 32. Report branches: 0x825c8 (load1 at q + j, j < 31; it
   returns into 0x825cc) and 0x82608 (store1 at q + 31, the last instruction; it returns into
   reac_ctrl_checksum_verify 0x8260c): false from the shadow premise over [q, q + 32). *)
Definition STK_reac_ctrl_block_cksum_stamp : Z := 16.
Definition tb_reac_ctrl_block_cksum_stamp_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (q : Z) (Bk : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\
    garr8 SEGS (mrestrict (w_H W2) mem2) q (map bv_unsigned (RcFin.stamp32 Bk)) /\
    tcj_kept STK_reac_ctrl_block_cksum_stamp lyc Sc W memc W2 mem2 (spZ regs) (fun a => a = q + 31).
Definition tb_reac_ctrl_block_cksum_stamp_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (q : Z) (Bk : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 q ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_ctrl_block_cksum_stamp -> spZ regs <= sp0 ->
  (* the caller's 32-byte block: q[0..31) read, q + 31 written *)
  length Bk = 32%nat -> garr8 SEGS (mrestrict (w_H W) memc) q (map bv_unsigned Bk) ->
  0 < q -> amem_range q 32 -> (q + 32 <= IMG_LO_B \/ IMG_TOP_B <= q) ->
  (spZ regs <= q \/ q + 32 <= spZ regs - STK_reac_ctrl_block_cksum_stamp) ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) (q + 31) 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q 32 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_block_cksum_stamp) regs memc mdc)
    (tb_reac_ctrl_block_cksum_stamp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs q Bk).
Definition hyps_reac_ctrl_block_cksum_stamp : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_ctrl_block_cksum_stamp : Prop :=
  hyps_reac_ctrl_block_cksum_stamp -> tb_reac_ctrl_block_cksum_stamp_spec.

(* ---- reac_ctrl_record_cksum_stamp 0x82694 (image B only; inlined into ctrl_finish on image A) -----------------
   a0 = r, a1 = n: an n-byte record inside the caller's block (ctrl_finish passes block + rec_off and rec_len, the
   row's bytes +18 and +19, at 0x84070 / 0x84074). The call sums the n - 1 bytes r[0..n-1) and stores
   (- sum) mod 128 at r + n - 1 (`negw; andi 127` at 0x82748; lib/Prog/RcRec.v stampck). For n = 1 the branch at
   0x826b0 skips the loop and the stored value is 0. The loop count is a1 - 1 (0x826ac, 0x82700). It writes one byte
   of its caller's block: caller-journal form. Frame 16; it takes no call; need 16.
   Trap (unimp 0x82760): 0x826c8 (r + j <u r), 0x826d4 ((r <> 0) = (r + j = 0)), 0x826d8 (r = 0), 0x82720
   (r + n - 1 <u r: n = 0 or a carry), 0x82730 ((r <> 0) = (r + n - 1 = 0)), 0x82734 (r = 0): false from 0 < r,
   1 <= n and amem_range r n. Report branches: 0x82714 (load1 at r + j; it returns into 0x82718) and 0x82770
   (store1 at r + n - 1, the last instruction; it returns into reac_ctrl_parse 0x82774): false from the shadow
   premise over [r, r + n). *)
Definition STK_reac_ctrl_record_cksum_stamp : Z := 16.
Definition tb_reac_ctrl_record_cksum_stamp_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (r n : Z) (RS : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\
    garr8 SEGS (mrestrict (w_H W2) mem2) r (map bv_unsigned (RS ++ [Z_to_bv 8 (RcRec.stampck RS)])) /\
    tcj_kept STK_reac_ctrl_record_cksum_stamp lyc Sc W memc W2 mem2 (spZ regs) (fun a => a = r + n - 1).
Definition tb_reac_ctrl_record_cksum_stamp_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (r n : Z) (RS : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 r -> getr regs 11 = w64 n ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_ctrl_record_cksum_stamp -> spZ regs <= sp0 ->
  (* the record: r[0..n-1) read, r + n - 1 written *)
  1 <= n -> Z.of_nat (length RS) = n - 1 -> garr8 SEGS (mrestrict (w_H W) memc) r (map bv_unsigned RS) ->
  0 < r -> amem_range r n -> (r + n <= IMG_LO_B \/ IMG_TOP_B <= r) ->
  (spZ regs <= r \/ r + n <= spZ regs - STK_reac_ctrl_record_cksum_stamp) ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) (r + n - 1) 1 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF r n ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_record_cksum_stamp) regs memc mdc)
    (tb_reac_ctrl_record_cksum_stamp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs r n RS).
Definition hyps_reac_ctrl_record_cksum_stamp : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_ctrl_record_cksum_stamp : Prop :=
  hyps_reac_ctrl_record_cksum_stamp -> tb_reac_ctrl_record_cksum_stamp_spec.

(* ---- reac_ctrl_checksum_verify 0x8260c (image A's twin: lib/A/Prog/CtrlChecksumVerify.v) ----------------------
   a0 = f, the caller's 50-byte object (check_groupa passes its frame object s7 = frame + 32 at 0x82274; the
   object's last granule is partial: check_groupa writes shadow 0x02 for frame + 80 at 0x82190). The call sums the
   32 bytes f[18..50) and returns 0 when the sum is 0 mod 256, else -1 (RcModel.blocksum). It writes nothing
   outside its 16-byte frame and takes no call; need 16.
   Trap (unimp 0x82690): 0x82614 (f = 0) and 0x8263c (~f <u 18 + j, j < 32: f + 18 + j carries): false from afobj
   (the object lies in a side-stack frame, so 4096 <= f and f + 50 <= alloc_ceiling). Report branch: 0x82674
   (load1 at f + 18 + j; it returns into 0x82678): false from afobj's shadow conjunct. *)
Definition STK_reac_ctrl_checksum_verify : Z := 16.
Definition tb_reac_ctrl_checksum_verify_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (BS : list Z)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_reac_ctrl_checksum_verify [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\
       getr regs' 10 = w64 (if RcModel.blocksum (map (Z_to_bv 8) BS) =? 0 then 0 else -1)).
Definition tb_reac_ctrl_checksum_verify_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch (f : Z) (BS : list Z),
  afn_pre SEGS B STK_reac_ctrl_checksum_verify ly S W regs mem md ch ->
  getr regs 10 = w64 f ->
  afobj SEGS B ly S W mem f 50 ->
  length BS = 32%nat -> garr8 SEGS (mrestrict (w_H W) mem) (f + 18) BS ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_checksum_verify) regs mem md)
    (tb_reac_ctrl_checksum_verify_post regs ly S W mem md BS).
Definition hyps_reac_ctrl_checksum_verify : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_ctrl_checksum_verify : Prop := hyps_reac_ctrl_checksum_verify -> tb_reac_ctrl_checksum_verify_spec.

(* ---- reac_ctrl_headamp_record_verify 0x834dc (image A's twin: lib/A/Prog/CtrlHeadampRecordVerify.v) ----------
   a0 = f, the same 50-byte frame object of check_groupa (0x82268). The call reads f[18]; when it is 4 it reads
   f[19]; when that is 3 it sums the six bytes f[34..40) and returns 0 when the sum is 0 mod 128. Every other case
   returns -1 (RcLeaf.hv). It writes nothing outside its 16-byte frame and takes no call; need 16.
   Trap (unimp 0x835b8): 0x834e4 (f = 0), 0x834ec (f >=u 2^64 - 18), 0x83524 (f >u 2^64 - 20), 0x8354c
   (f + 18 >u 2^64 - 17), 0x83564 (~(f + 34) <u j): false from afobj. Report branches: 0x835c8 (load1 at f + 18;
   it returns into 0x835cc), 0x835d8 (load1 at f + 19, the last instruction; it returns into
   reac_ctrl_identity_poll_block 0x835dc), 0x83598 (load1 at f + 34 + j; it returns into 0x8359c): false from
   afobj's shadow conjunct. *)
Definition STK_reac_ctrl_headamp_record_verify : Z := 16.
Definition tb_reac_ctrl_headamp_record_verify_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (b0 b1 : Z) (REC : list Z) : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_reac_ctrl_headamp_record_verify [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' => ly' = ly /\ S' = S /\ W' = W /\
       getr regs' 10 = w64 (if RcLeaf.hv (Z_to_bv 8 b0) (Z_to_bv 8 b1) (map (Z_to_bv 8) REC) then 0 else -1)).
Definition tb_reac_ctrl_headamp_record_verify_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch (f b0 b1 : Z) (REC : list Z),
  afn_pre SEGS B STK_reac_ctrl_headamp_record_verify ly S W regs mem md ch ->
  getr regs 10 = w64 f ->
  afobj SEGS B ly S W mem f 50 ->
  garr8 SEGS (mrestrict (w_H W) mem) (f + 18) [b0; b1] ->
  length REC = 6%nat -> garr8 SEGS (mrestrict (w_H W) mem) (f + 34) REC ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_headamp_record_verify) regs mem md)
    (tb_reac_ctrl_headamp_record_verify_post regs ly S W mem md b0 b1 REC).
Definition hyps_reac_ctrl_headamp_record_verify : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_ctrl_headamp_record_verify : Prop :=
  hyps_reac_ctrl_headamp_record_verify -> tb_reac_ctrl_headamp_record_verify_spec.

(* ---- reac_ctrl_identity_poll_block 0x835dc (image A's twin: lib/A/Prog/CtrlIdentityPollBlock.v) ---------------
   a0 = i (a C int), a1 = o, a 34-byte destination of the caller (LLVMFuzzerTestOneInput passes ld 80(s1) at
   0x81758, after it writes the shadow bytes 0, 0, 0, 0, 0x02 of a 34-byte object at 0x8173c..0x81750: a partial
   last granule). For 0 <= i <= 5 and o <> 0 the call copies the 34-byte row i of GRANT_GROUPB (object 19 =
   B_GROUPB, 0x21080, 204 bytes; byte-identical to image A's table: b_groupb_check) to o through __asan_memcpy
   (0x83620) and returns 0 (GrantSweepModel.GBz i). For i >u 5 (0x835ec) or o = 0 (0x835f0) it returns -1 and
   writes nothing outside its stack. The epilogue 0x83628 is reached from three arms with different a2 (-1, -1, 0),
   so a walk replays it per arm. Frame 16 + __asan_memcpy's ESTACK.
   The o = 0 arm is not taken: twr_ok over [o, o + 34) gives 4096 <= o (awr_byte_cases).
   The destination is written by the copy: caller-journal form (twr_ok, tcj_kept). Its shadow premise is the
   partial-granule form __asan_memcpy's contract asks for (YG0d.v aintrin_realizes: range_addressable and
   shadow_hull_vis).
   Trap (unimp 0x83638): guard `not a5, a3; bltu a5, a4` at 0x83604 / 0x83608 (a3 = GRANT_GROUPB, a4 = 34 * i):
   reached only after the branch at 0x835ec has given i <=u 5, so 34 * i <= 170, and the table's image bound gives
   ~GRANT_GROUPB > 170. No report call. *)
Definition STK_reac_ctrl_identity_poll_block : Z := 16 + ESTACK.
Definition tb_reac_ctrl_identity_poll_block_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (i o : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\
    tcj_kept STK_reac_ctrl_identity_poll_block lyc Sc W memc W2 mem2 (spZ regs) (fun a => o <= a < o + 34) /\
    (if ((0 <=? i) && (i <=? 5))%bool
     then getr regs2 10 = w64 0 /\ garr8 SEGS (mrestrict (w_H W2) mem2) o (GBz i)
     else getr regs2 10 = w64 (-1) /\
          (forall a, o <= a < o + 34 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a)).
Definition tb_reac_ctrl_identity_poll_block_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (i o : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 i -> - 2 ^ 31 <= i < 2 ^ 31 -> getr regs 11 = w64 o ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_ctrl_identity_poll_block -> spZ regs <= sp0 ->
  (* the destination [o, o + 34) *)
  (spZ regs <= o \/ o + 34 <= spZ regs - STK_reac_ctrl_identity_poll_block) ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 34 ->
  amem_range o 34 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF o 34 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) o 34 ->
  (VAL (A_OBJ B_GROUPB) + 204 <= o \/ o + 34 <= VAL (A_OBJ B_GROUPB)) ->
  (* the source table GRANT_GROUPB: its bytes, its registration, its place in image B *)
  garr8 SEGS (mrestrict (w_H W) memc) (VAL (A_OBJ B_GROUPB)) GBallz ->
  In (VAL (A_OBJ B_GROUPB), 204) GRANT_GLOBS_B ->
  IMG_LO_B + 64 <= VAL (A_OBJ B_GROUPB) -> VAL (A_OBJ B_GROUPB) + 204 + 64 <= IMG_TOP_B ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_identity_poll_block) regs memc mdc)
    (tb_reac_ctrl_identity_poll_block_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs i o).
Definition hyps_reac_ctrl_identity_poll_block : Prop := RT_LAWS /\ RT_PALIB /\ RT_MEMCPY /\ RT_GLOBS /\ RT_IMGSH.
Definition walk_reac_ctrl_identity_poll_block : Prop :=
  hyps_reac_ctrl_identity_poll_block -> tb_reac_ctrl_identity_poll_block_spec.

(* ================================================= laystamp ================================================= *)
(* ==== laystamp: ctrl_finish, ctrl_lay_block, reac_ctrl_stamp_headamp, reac_ctrl_build_grant_sweep ===============
   One call chain: reac_ctrl_build_grant_sweep -> reac_ctrl_stamp_headamp -> ctrl_lay_block, then ctrl_finish. Each
   call writes bytes of its caller, so each contract is in the caller-journal form of aspecs/CtrlFinish.v: the
   premise is the caller's journal (ajournal ... lyc Sc W memc mdc k), `twr_ok` gives the right to write the bytes,
   and the post extends the same journal (no call adds an event: k is kept) and states `tcj_kept`. *)
(* reac_ctrl_record_cksum_stamp is the control-leaves fragment's (a Theorem Labs lane); its stub Variable was replaced
   by that group's Definition at integration. *)
(* tb_reac_ctrl_record_cksum_stamp_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_ctrl_block_cksum_stamp is the control-leaves fragment's (a Theorem Labs lane); its stub Variable was replaced
   by that group's Definition at integration. *)
(* tb_reac_ctrl_block_cksum_stamp_spec is the Definition below / above in this file (stub removed at integration). *)

(* ---- facts of image B alone that these walks take (proved in lib/B/GrantBCloseInst.v, except IMG_CTRL_ROW_IMG, IMG_CTRL_STAMP and IMG_RO_BELOW: lib/B/Prog/GrantBClose.v) -------
   The bytes are read through the constant-cell route: arodata_okP over pa_relro_lo / pa_relro_hi makes a byte of
   the read-only segment or of RELRO read as image B's initial byte. The row B_ROW (0x9d4d0, 24 bytes) is in RELRO;
   the template (0x211c0) and the tables (0x21034, 0x21080, 0x21200, 0x21260) are in the read-only segment. Their
   shadow is not a caller premise. CTRL_FRAMES (0x9d3e0, 264 bytes, guard bytes from 0x9d4e8) and TMPL_HEADAMP
   (0x211c0, 32 bytes) are registered globals of whole granules: they lie in as_zero_shadow (in_zs), whose shadow AR
   keeps 0 in every state. GRANT_HEAD_ACK, GRANT_HEAD_MARK (34 bytes) and GRANT_GROUPB (204) end in a partial
   granule: they are read through globs_marked (RT_GLOBS over GRANT_GLOBS_B). B_JT_LAY is read by an `lw` with no
   instrumented check. *)
(* The row: 8-aligned (`andi a0,s4,7` at 0x83d40 in ctrl_lay_block and `andi a2,a1,7` at 0x83fe8 in ctrl_finish
   go to the trap otherwise), inside the image, inside as_zero_shadow, and apart from the four cells the walks read
   (the GOT words objects 0 / 1, the shadow-base cell object 35, the side-stack flag cell object 36). *)
Definition IMG_CTRL_ROW : Prop :=
  B_ROW mod 8 = 0 /\ IMG_LO + 64 <= B_ROW /\ B_ROW + 24 + 64 <= IMG_HI /\ in_zs B B_ROW 24 /\
  ls_apart B_ROW 24 (VAL (A_OBJ 0)) 8 /\ ls_apart B_ROW 24 (VAL (A_OBJ 1)) 8 /\
  ls_apart B_ROW 24 (VAL (A_OBJ 35)) 8 /\ ls_apart B_ROW 24 (VAL (A_OBJ 36)) 8.
(* The row's bytes ctrl_finish reads: +18 the record offset 16, +19 the record length 6, +20 the checksum kind 2. *)
Definition IMG_CTRL_ROW_FIN : Prop :=
  forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) (B_ROW + 18) [16; 6; 2].
(* The row's bytes ctrl_lay_block reads: +2 the block kind 2 (the switch index), +8 the template pointer TM,
   +16 the argument offset 18, +17 the argument length 3. *)
Definition IMG_CTRL_ROW_LAY (TM : Z) : Prop :=
  forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  val_mem SEGS (mrestrict H mem) (B_ROW + 2) 1 2 /\ val_mem SEGS (mrestrict H mem) (B_ROW + 8) 8 TM /\
  val_mem SEGS (mrestrict H mem) (B_ROW + 16) 1 18 /\ val_mem SEGS (mrestrict H mem) (B_ROW + 17) 1 3.
(* The template TM names (TMPL_HEADAMP, 0x211c0): the 32 bytes T32z, inside the image, inside as_zero_shadow,
   apart from the row and the table. *)
Definition IMG_CTRL_TMPL (TM : Z) : Prop :=
  IMG_LO + 64 <= TM /\ TM + 32 + 64 <= IMG_HI /\ in_zs B TM 32 /\
  ls_apart TM 32 B_ROW 24 /\ ls_apart TM 32 (VAL (A_OBJ B_JT_LAY)) 40 /\
  forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  garr8 SEGS (mrestrict H mem) TM T32z.
(* Entry 2 of B_JT_LAY: JE (0x62ddc on image B), which the `lw` at 0x83d78 sign-extends; the `jr a0` at 0x83d84
   goes to VAL (A_OBJ B_JT_LAY) + JE = BASE + slot 0x33d4 = 0x83e10, the template case. *)
Definition IMG_CTRL_LAY_JT : Prop :=
  exists JE, 0 <= JE < 2 ^ 31 /\
  VAL (A_OBJ B_JT_LAY) + JE = BASE + nth LAY_TMPL_ENTRY BImg.lay_jt_slots 0 /\
  IMG_LO + 64 <= VAL (A_OBJ B_JT_LAY) /\ VAL (A_OBJ B_JT_LAY) + 40 + 64 <= IMG_HI /\
  ls_apart B_ROW 24 (VAL (A_OBJ B_JT_LAY)) 40 /\
  forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
  val_mem SEGS (mrestrict H mem) (VAL (A_OBJ B_JT_LAY) + 4 * Z.of_nat LAY_TMPL_ENTRY) 4 JE.
(* The row's 24 bytes are bytes of image B (lib/A/Prog/CtrlFinish.v's HROWimg form): ctrl_finish and ctrl_lay_block
   take this image fact; the row's VALUES are premises of their contracts over the caller's memory. *)
Definition IMG_CTRL_ROW_IMG : Prop := forall a, B_ROW <= a < B_ROW + 24 -> in_img SEGS a.
(* Where the template TM lies: inside image B and its read range, inside as_zero_shadow, apart from the row and
   the jump table. A premise of ctrl_lay_block's contract (its caller knows TM from the row). *)
Definition tmpl_place (TM : Z) : Prop :=
  IMG_LO + 64 <= TM /\ TM + 32 + 64 <= IMG_HI /\ in_zs B TM 32 /\
  ls_apart TM 32 B_ROW 24 /\ ls_apart TM 32 (VAL (A_OBJ B_JT_LAY)) 40 /\
  (forall a, TM <= a < TM + 32 -> in_img SEGS a).
(* The image facts reac_ctrl_stamp_headamp's walk takes to give its two callees the row's and the template's
   bytes: each one is read through the image view (arodata_okP over image B's read-only range, which holds for
   CTRL_FRAMES' client bytes: they are never owned statics, YG0n.v:236-241), never through a constant cell of AR. *)
Definition IMG_CTRL_STAMP : Prop :=
  IMG_CTRL_ROW /\ IMG_CTRL_ROW_IMG /\ IMG_CTRL_ROW_FIN /\ IMG_CTRL_LAY_JT /\
  exists TM, tmpl_place TM /\ IMG_CTRL_ROW_LAY TM /\ IMG_CTRL_TMPL TM.
(* The three row tables reac_ctrl_build_grant_sweep copies: GRANT_HEAD_ACK (object 22, 0x21200, 34 bytes),
   GRANT_HEAD_MARK (object 23, 0x21260, 34 bytes) and GRANT_GROUPB (object 19, 0x21080, 204 bytes): their bytes,
   their entries in GRANT_GLOBS_B, and their place inside the image. *)
Definition IMG_BGS_ROWS : Prop :=
  (forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ B_ACK)) HEAD_ACK34z /\
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ B_MARK)) HEAD_MARK34z /\
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ B_GROUPB)) GBallz) /\
  In (VAL (A_OBJ B_ACK), 34) GRANT_GLOBS_B /\ In (VAL (A_OBJ B_MARK), 34) GRANT_GLOBS_B /\
  In (VAL (A_OBJ B_GROUPB), 204) GRANT_GLOBS_B /\
  IMG_LO + 64 <= VAL (A_OBJ B_ACK) /\ VAL (A_OBJ B_ACK) + 34 + 64 <= IMG_HI /\
  IMG_LO + 64 <= VAL (A_OBJ B_MARK) /\ VAL (A_OBJ B_MARK) + 34 + 64 <= IMG_HI /\
  IMG_LO + 64 <= VAL (A_OBJ B_GROUPB) /\ VAL (A_OBJ B_GROUPB) + 204 + 64 <= IMG_HI.
(* The read-only range lies below the sink head's overflow head, so a journal keeps arodata_okP across a call
   (lib/B/PaBase.v arodata_ok_journalP): image A's walks take it as their section's Context RO. *)
Definition IMG_RO_BELOW : Prop := ro_below_ofl SEGS pa_relro_lo pa_relro_hi.

(* ==== ctrl_finish 0x83fdc (BASE + AF_ctrl_finish) ===============================================================
   a0 = p, a1 = B_ROW; the caller's 32-byte control block is [p + 18, p + 50). Frame 16 on the machine stack (ra at
   sp + 8, s0 = p at sp + 0); no frame on the side stack for frames, no runtime entry. It reads the shadow base
   through the GOT word object 1. Its trap `unimp` 0x840a8 has six guards: the row is not 8-aligned (0x83fec),
   p = 0 (0x84028, 0x84078), p + 18 wraps past 2 ^ 64 (`bgeu` 0x84030, `bltu` 0x84080), and p + 18 + the record
   offset wraps (`not a0,a4; bltu a0,a3` 0x84054); IMG_CTRL_ROW, `p <> 0` and `p + 50 <= 2 ^ 47 - 8` make each false.
   It reads the row's bytes +20 (2), +18 (16) and +19 (6), each after the instrumented check of its shadow byte; that
   byte is 0 (IMG_CTRL_ROW, in_zs), so the branches 0x84010 -> 0x840ac -> 0x840b4, 0x84044 -> 0x840b8 -> 0x840c0
   and 0x84068 -> 0x840c4 -> 0x840cc (errpath_load1; the last falls into reac_box_model_block 0x840d0) are not
   taken. For kind 2 it calls reac_ctrl_record_cksum_stamp (a0 = p + 34, a1 = 6) at 0x84074, which writes the
   record's checksum at p + 39, then releases its frame and tail-jumps at 0x84094 to reac_ctrl_block_cksum_stamp
   (a0 = p + 18), which writes the block's checksum at p + 49 and returns to ctrl_finish's caller. Image A inlines
   both (aspecs/CtrlFinish.v); here they are the two stubs above. The 32 bytes are then RcFin.fin 2 16 6 Bk of the
   block Bk the caller handed in; every other byte off this call's stack window is kept.
   Stack: 16 + reac_ctrl_record_cksum_stamp's 16 + ESTACK. *)
Definition tb_ctrl_finish_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p : Z) (Bk : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18) (map bv_unsigned (RcFin.fin 2 16 6 Bk)) /\
    tcj_kept STK_ctrl_finish lyc Sc W memc W2 mem2 (spZ regs) (fun a => p + 18 <= a < p + 50).
Definition tb_ctrl_finish_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p : Z) (Bk : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 B_ROW ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_ctrl_finish -> spZ regs <= sp0 ->
  (* the row it reads (lib/A/Prog/CtrlFinish.v's form): rec_off 16, rec_len 6, cksum 2 (CKSUM_RECORD), and their
     shadow; the caller discharges both through the image view *)
  garr8 SEGS (mrestrict (w_H W) memc) (B_ROW + 18) [16; 6; 2] ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (B_ROW + 18) 3 ->
  (* the caller's 32-byte control block at p + 18: image A's range, and the trap guards p = 0 (0x84028 / 0x84078) *)
  length Bk = 32%nat -> garr8 SEGS (mrestrict (w_H W) memc) (p + 18) (map bv_unsigned Bk) ->
  0 <= p -> p + 50 <= 2 ^ 47 - 8 -> p <> 0 -> amem_range (p + 18) 32 ->
  (* off image B's range (the form the two stamps take; it gives ~ in_img by pa_img_range) *)
  (p + 50 <= IMG_LO_B \/ IMG_TOP_B <= p + 18) ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 18) 32 ->
  (* the bytes are clear of the stack this call and the runtime's entries use *)
  (spZ regs <= p + 18 \/ p + 50 <= spZ regs - STK_ctrl_finish) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) (p + 18) 32 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_ctrl_finish) regs memc mdc)
    (tb_ctrl_finish_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p Bk).
Definition hyps_ctrl_finish : Prop := RT_LAWS /\ RT_PALIB /\ IMG_CTRL_ROW /\ IMG_CTRL_ROW_IMG.
Definition walk_ctrl_finish : Prop :=
  hyps_ctrl_finish ->
  tb_reac_ctrl_record_cksum_stamp_spec -> tb_reac_ctrl_block_cksum_stamp_spec ->
  tb_ctrl_finish_spec.

(* ==== ctrl_lay_block 0x83bfc (BASE + AF_ctrl_lay_block) ==========================================================
   a0 = p, a1 = B_ROW, a2 = 0 (no model), a3 = g = the caller's class-0 frame + 32 (the three bytes ch, pm, v). Frame
   128 on the machine stack (ra, s0-s10; s0 = the entry sp), then `andi sp,sp,-32` (0x83c38). It reads the
   side-stack flag through the GOT word object 0 and the shadow base through the GOT word object 1. With the flag 1
   (AR's constant cell, object 36) it calls __asan_stack_malloc_1 (a0 = 96) at 0x83c70 and takes a class-1 frame G
   of 128 bytes (descriptor "1 32 32 7 gen:846", object 24). The class contract returns frame_addr ly 1 pos, which
   is not 0, so the machine-stack carve 0x83c88 .. 0x83ca0 (reached when the flag is 0 or the result is 0) is not
   reached: the walk refutes it from the flag's value 1 and that result. It writes G's header (G + 0, G + 8,
   G + 16) and G's shadow bytes 0..3 0xf1, 4..7 0xf8, 8..11 0xf3, then 4..7 0x00 (0x83d20).
   Its trap `unimp` 0x83fac has six guards: p = 0 (0x83d10), p + 18 wraps (0x83d18), the row is not 8-aligned
   (0x83d44), p + 18 + the argument offset wraps (`not a1,s5; bltu a1,a0` 0x83ebc), and 0x83d9c / 0x83db8 in entry
   1's arm, which is not taken. It calls __asan_memset (p + 18, 0, 32) at 0x83d3c, reads the row's byte +2 (2) after
   the instrumented check 0x83d58 and switches on it (LAY_BOX_SLOTS's table). Entry 2 reads the row's word +8 (TM;
   check 0x83e20, whose branch goes straight to errpath_load8 0x83fd8, which falls into ctrl_finish) and calls
   __asan_memcpy (p + 18, TM, 32) at 0x83e7c. With g <> 0 (`beqz s3` at 0x83e80 not taken) it reads the row's
   bytes +17 (3) and +16 (18) after the checks 0x83e94 / 0x83eb0 and calls __asan_memcpy (p + 36, g, 3) at 0x83ec8.
   The row's granules have shadow 0 (IMG_CTRL_ROW), so the branches into the error path on the walked arm
   (0x83d58 -> 0x83fb0 -> 0x83fb8, 0x83e20 -> 0x83fd8, 0x83e94 -> 0x83fbc -> 0x83fc4, 0x83eb0 -> 0x83fc8 -> 0x83fd0)
   are not taken; entry 1's (0x83db0 -> 0x83de0 -> 0x83fd4, 0x83dcc -> 0x83dec -> 0x83dfc) are on an arm not taken.
   The release is inline (0x83ecc ..): shadow 4..7 0xf8, the retired magic at G + 0, G's 16 shadow bytes 0xf5, and
   the flag byte 0 through the pointer at G + 0x78 (0x83f34 / 0x83f38); the no-frame epilogue 0x83f40 is not
   reached. The 32 bytes are then lay_z ch pm v (T32z with ch, pm, v at 18 .. 20).
   OBLIGATION: the call of reac_box_model_block at 0x83e64 is not taken. The row's byte +2 is 2 (IMG_CTRL_ROW_LAY's val_mem at B_ROW + 2);
   2 <= 9, so the bound check 0x83d60 / 0x83d64 does not send the index to 0x83e4c; entry 2 sends the `jr` at
   0x83d84 to slot 0x33d4 = 0x83e10 (IMG_CTRL_LAY_JT), which is none of LAY_BOX_SLOTS (laystamp_numbers); from
   0x83e10 the path goes 0x83e30 -> 0x83e7c -> 0x83e80 and never through 0x83e58 .. 0x83e64. walk_ctrl_lay_block
   takes no contract of reac_box_model_block: its proof refutes every arm that reaches the call.
   live_ok 1 at 0x83c70 is this call's own: count_cid 1 (frames Sc) <= length (frames Sc) <= 10 < fs_frames 1 = 8192
   (GrantFrame.v count_cid_le_length), from the premise `Z.of_nat (length (frames Sc)) <= 10`.
   Stack: 128 + 16 + ESTACK. *)
Definition tb_ctrl_lay_block_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p ch pm v : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    (exists f, S2 = set_fs f Sc) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (p + 18) (lay_z ch pm v) /\
    tcj_kept STK_ctrl_lay_block lyc Sc W memc W2 mem2 (spZ regs) (fun a => p + 18 <= a < p + 50).
(* tb_ctrl_lay_block_spec AGAINST IMAGE A's tctrl_lay_block_spec (lib/A/Prog/CtrlLayBlockSpec.v:63-89 and the
   walk's Section hypotheses lib/A/Prog/CtrlLayBlock.v:81-115, a working branch af735a950e2), premise by premise:
   - SAME: ajournal, arodata_okP, ret_ok, 4096 <= ra, gp, tp, a0 = p, a2 = 0, a3 = g, sp 16-aligned, the stack bound,
     0 <= p, p + 50 <= 2 ^ 47 - 8, amem_range (p + 18) 32, twr_ok (p + 18) 32, g <> 0, tsrc_ok g 3, garr8 g [ch; pm; v],
     afobj g 3, and the disjointness of [p + 18, p + 50) and [g, g + 3).
   - a1: image A's row object VAL (A_OBJ A_ROW) is B_ROW = VAL (A_OBJ 18) + 240 (image B's object 18 is the table's
     start). The stack bound uses STK_ctrl_lay_block = 128 + 16 + ESTACK: with sp 16-aligned, `andi sp,sp,-32` drops
     at most 16 bytes (image A allows 32).
   - ADDED TM / tmpl_place TM / IMG_CTRL_ROW_LAY TM / IMG_CTRL_TMPL TM: image A takes the same image facts (the row's
     bytes +2, +8 = TM, +16, +17, the template's 32 bytes, all under arodata_okP, and TM's place) as SECTION
     HYPOTHESES of its walk (HTM_rng, HROW_k, HROW_tm, HROW_ao, HROW_al, HTMPL, HZS_TM). Here they are premises of
     the contract, with TM bound by it, so the caller supplies them: reac_ctrl_stamp_headamp holds them in
     IMG_CTRL_STAMP. The row's range, the table's, and in_zs of the row / the table are in hyps (IMG_CTRL_ROW,
     IMG_CTRL_LAY_JT), as image A's HROW_rng / HJT_* / HZS_ROW / HZS_JT.
   - ADDED `p <> 0`: image B's code has a UBSan trap guard p = 0 (0x83d10) that image A's has not.
   - RECAST `forall x, p + 18 <= x < p + 50 -> ~ in_img SEGS x` AS `p + 50 <= IMG_LO_B \/ IMG_TOP_B <= p + 18`:
     stronger (it implies A's form through pa_img_range), the form the two stamps take, and the caller has it: the
     bytes lie in a side-stack frame, which frm_off_imgB places off image B's range.
   - REPLACED `spZ regs <= p + 18 -> p + 50 <= sp0` (the bytes in the caller's MACHINE stack) BY the frame premises
     `In (cb, pb) (frames Sc)`, `frame_addr lyc cb pb <= p + 18`, `p + 50 <= frame_addr lyc cb pb + fs_frame_bytes cb`
     and the disjointness `spZ regs <= p + 18 \/ p + 50 <= spZ regs - STK_ctrl_lay_block`: on image B the bytes are
     reac_ctrl_build_grant_sweep's scratch in its CLASS-6 SIDE-STACK frame (image A's sweep has a fixed machine-stack
     frame). A live frame's bytes are client bytes, so the class-1 frame this call takes leaves them and their shadow
     unchanged (YG0d.v:298-299); the disjointness keeps them clear of this call's own window.
   - ADDED `range_addressable .. SHADOW_OFF (p + 18) 32`: the checked fill and copy (aintrin_realizes) ask for it.
     Image A gets it from AR, which marks the whole machine stack usable in every state (YG0n.v:188-191); a side-stack
     frame's shadow is the caller's to set (reac_ctrl_build_grant_sweep's __asan_set_shadow_00), so here it is a
     premise.
   - ADDED `In (cg, pg) (frames Sc)` and `g = frame_addr lyc cg pg + 32`: the three argument bytes are
     reac_ctrl_stamp_headamp's class-0 frame bytes F0 + 32 .. F0 + 34; pinning g there makes them client bytes that
     survive the class-1 frame call, the same reason as (cb, pb). Image A states it in words (CtrlLayBlockSpec.v:81-83).
   - `Z.of_nat (length (frames Sc)) <= 10` (image A: <= 9): either gives live_ok 1 (fs_frames 1 = 8192); 10 is what
     image B's callers pass. *)
Definition tb_ctrl_lay_block_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p g cb pb cg pg ch pm v TM : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 B_ROW -> getr regs 12 = w64 0 -> getr regs 13 = w64 g ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_ctrl_lay_block -> spZ regs <= sp0 ->
  (* The row's bytes it reads (+2 the block kind 2, the switch index; +8 the template pointer TM = 0x211c0,
     TMPL_HEADAMP; +16 the argument offset 18; +17 the argument length 3) and the template's 32 bytes T32z, in the
     IMAGE-VIEW form, as image A's closed walk states them (lib/A/Prog/CtrlLayBlock.v:91-108 on a working branch
     5470d0c9c50): each is `arodata_okP ... -> the bytes`, for ANY state, not a premise over this call's entry
     memory `memc`. Reason (a Theorem Labs lane): the code reads the row at 0x83d5c / 0x83e1c / 0x83e98 / 0x83eb4 and copies
     the template at 0x83e7c, all AFTER the class-1 frame call at 0x83c70, and astack_malloc_realizes keeps an
     image byte only when it is not an owned static and not the errno cell (YG0d.v:298, acall_kept YCbq.v:828,
     ajournal YCbq.v:361). Nothing here gives that for the row or the template, so a premise over `memc` cannot be
     carried to the read; `arodata_okP` carries the same ~owned / ~errno side condition and so survives the call
     (lib/B/PaBase.v arodata_ok_journalP, with IMG_RO_BELOW). IMG_CTRL_STAMP holds all three, so
     reac_ctrl_stamp_headamp's walk discharges them. *)
  tmpl_place TM -> IMG_CTRL_ROW_LAY TM -> IMG_CTRL_TMPL TM ->
  (* the live-frame bound that gives live_ok 1 (frames Sc) at 0x83c70 *)
  Z.of_nat (length (frames Sc)) <= 10 ->
  (* the 32 bytes it lays down, [p + 18, p + 50): image A's range, the trap guard p = 0 (0x83d10), the right to
     write them, their shadow, and their place in a live frame (cb, pb) of the side stack for frames, which makes
     them client bytes that the class-1 frame this call takes leaves alone with their shadow *)
  0 <= p -> p + 50 <= 2 ^ 47 - 8 -> p <> 0 -> amem_range (p + 18) 32 ->
  (p + 50 <= IMG_LO_B \/ IMG_TOP_B <= p + 18) ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 18) 32 ->
  In (cb, pb) (frames Sc) -> frame_addr lyc cb pb <= p + 18 -> p + 50 <= frame_addr lyc cb pb + fs_frame_bytes cb ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (p + 18) 32 ->
  (* the three argument bytes it copies to p + 36: a3 is pinned to the caller's live frame (cg, pg) + 32, and is
     not 0, so the walk takes the copy arm only *)
  In (cg, pg) (frames Sc) -> g = frame_addr lyc cg pg + 32 -> g <> 0 ->
  tsrc_ok W memc (spZ regs) g 3 -> afobj SEGS B lyc Sc W memc g 3 ->
  garr8 SEGS (mrestrict (w_H W) memc) g [ch; pm; v] ->
  (* the two disjointness premises: the block against this call's stack window, and against the source bytes *)
  (spZ regs <= p + 18 \/ p + 50 <= spZ regs - STK_ctrl_lay_block) ->
  (p + 50 <= g \/ g + 3 <= p + 18) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_ctrl_lay_block) regs memc mdc)
    (tb_ctrl_lay_block_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p ch pm v).
Definition hyps_ctrl_lay_block : Prop :=
  RT_LAWS /\ RT_PALIB /\ RT_PALIBF /\ RT_ML /\ RT_SMP /\ RT_SM 1 /\ RT_ASF /\ RT_FFL /\ RT_TP_FS /\
  RT_MEMSET /\ RT_MEMCPY /\ RT_IMGSH /\ IMG_RO_BELOW /\ IMG_CTRL_ROW /\ IMG_CTRL_ROW_IMG /\ IMG_CTRL_LAY_JT.
(* No contract of reac_box_model_block: the OBLIGATION above. *)
Definition walk_ctrl_lay_block : Prop := hyps_ctrl_lay_block -> tb_ctrl_lay_block_spec.

(* ==== reac_ctrl_stamp_headamp 0x8326c (BASE + AF_reac_ctrl_stamp_headamp) ========================================
   a0 = p, a1 = ch, a2 = pm, a3 = v. Frame 96 on the machine stack (ra, s0-s9), then `andi sp,sp,-32` (0x832a4).
   With the flag 1 it calls __asan_stack_malloc_0 (a0 = 64) at 0x832dc and takes a class-0 frame F0 of 64 bytes
   (descriptor "1 32 3 9 args:1288", object 16); the carve 0x832f4 .. 0x8330c is refuted as in ctrl_lay_block. It
   writes F0's header, F0's shadow bytes 0..3 0xf1, 4 = 0x03, 5..7 0xf3, and ch, pm, v at F0 + 32 .. F0 + 34. When
   legalb pm v is false (0x83380 .. 0x83398) it returns -1 and writes no byte of its caller's. Otherwise: its trap
   `unimp` 0x834c0 has four guards, CTRL_FRAMES + 240 = 0 (0x833a8; false: object 18 is in the image, pa_obj_img),
   p = 0 (0x833ac), p + 16 wraps (0x833b4) and p + 18 wraps (0x833d8): `0 < p` and `p + 50 <= 2 ^ 64` make them false.
   It stores 0xcd at p + 16 and 0xea at p + 17, each after the instrumented check of its shadow byte (0x833c8,
   0x833ec). The caller's scratch has shadow 0x00 there (reac_ctrl_build_grant_sweep sets it with
   __asan_set_shadow_00 at 0x838d4 / 0x83ac0), so the branches 0x833c8 -> 0x834c4 -> 0x834c8 -> errpath_store1 0x834cc
   and 0x833ec -> 0x834d0 -> 0x834d4 -> errpath_store1 0x834d8 (which falls into reac_ctrl_headamp_record_verify) are
   not taken: this walk refutes 0x833c8 / 0x834c8 and 0x833ec / 0x834d4. Then it calls ctrl_lay_block (p, B_ROW, 0,
   F0 + 32) at 0x8340c and ctrl_finish (p, B_ROW) at 0x83418, a1 from s4, which ctrl_lay_block's post keeps
   (aregs_preserved), and returns 0. The release is inline (0x83420 ..): shadow 4 0xf8, the retired magic at F0, F0's
   8 shadow bytes 0xf5, and the flag byte 0 through the pointer at F0 + 56; the no-frame epilogue 0x83468 is not
   reached. The 34 bytes [p + 16, p + 50) are then GAz ch pm v.
   live_ok 0 at 0x832dc is this call's own: count_cid 0 (frames Sc) <= 9 < fs_frames 0 = 16384, from the premise
   `Z.of_nat (length (frames Sc)) <= 9`; F0 is live at the call of ctrl_lay_block, whose bound 10 follows.
   Stack: 96 + 16 + STK_ctrl_lay_block. *)
Definition tb_reac_ctrl_stamp_headamp_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p ch pm v : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    (exists f, S2 = set_fs f Sc) /\
    getr regs2 10 = w64 res /\
    tcj_kept STK_reac_ctrl_stamp_headamp lyc Sc W memc W2 mem2 (spZ regs) (fun a => p + 16 <= a < p + 50) /\
    (if legalb pm v
     then res = 0 /\ garr8 SEGS (mrestrict (w_H W2) mem2) (p + 16) (GAz ch pm v)
     else res = -1 /\ (forall a, p + 16 <= a < p + 50 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a)).
Definition tb_reac_ctrl_stamp_headamp_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p ch pm v cb pb : Z)
    (cl : list (Z * Z * Z)),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 ch -> getr regs 12 = w64 pm -> getr regs 13 = w64 v ->
  0 <= ch < 256 -> 0 <= pm < 256 -> 0 <= v < 256 ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) cl ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_ctrl_stamp_headamp -> spZ regs <= sp0 ->
  (* the live-frame bound that gives live_ok 0 (frames Sc) at 0x832dc *)
  Z.of_nat (length (frames Sc)) <= 9 ->
  (* the trap 0x834c0: its guards 0x833ac, 0x833b4 and 0x833d8 are false *)
  0 < p -> p + 50 <= 2 ^ 64 ->
  (* the 34 bytes [p + 16, p + 50): the range ctrl_lay_block and ctrl_finish take, their place in a live frame
     (cb, pb) of the side stack for frames (the caller's scratch), the shadow 0x00 its caller sets over that
     scratch (the checked stores 0x833d4 / 0x833f8: the branches 0x833c8 and 0x833ec are false), the stack window,
     and the right to write them when it accepts the pair *)
  p + 50 <= 2 ^ 47 - 8 -> amem_range (p + 16) 34 ->
  (p + 50 <= IMG_LO_B \/ IMG_TOP_B <= p + 16) ->
  In (cb, pb) (frames Sc) -> frame_addr lyc cb pb <= p + 16 -> p + 50 <= frame_addr lyc cb pb + fs_frame_bytes cb ->
  (forall x, p + 16 <= x < p + 50 -> aview SEGS (w_H W) memc (shadow_addr x) = Some 0) ->
  (spZ regs <= p + 16 \/ p + 50 <= spZ regs - STK_reac_ctrl_stamp_headamp) ->
  (legalb pm v = true -> twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) (p + 16) 34) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_stamp_headamp) regs memc mdc)
    (tb_reac_ctrl_stamp_headamp_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p ch pm v).
Definition hyps_reac_ctrl_stamp_headamp : Prop :=
  RT_LAWS /\ RT_PALIB /\ RT_PALIBF /\ RT_ML /\ RT_SMP /\ RT_SM 0 /\ RT_ASF /\ RT_FFL /\ RT_TP_FS /\ IMG_RO_BELOW /\
  IMG_CTRL_STAMP.
Definition walk_reac_ctrl_stamp_headamp : Prop :=
  hyps_reac_ctrl_stamp_headamp ->
  tb_ctrl_lay_block_spec -> tb_ctrl_finish_spec ->
  tb_reac_ctrl_stamp_headamp_spec.

(* ==== reac_ctrl_build_grant_sweep 0x8363c (BASE + AF_reac_ctrl_build_grant_sweep) ================================
   a0 = s (the row buffer: a heap block of the caller's), a1 = mx, a2 = base, a3 = w, a4 = V (the 3 w value bytes, in
   a frame of the caller on the side stack for frames). Frame 256 on the machine stack (ra, s0-s11), then
   `andi sp,sp,-32` (0x8367c). With the flag 1 it calls __asan_stack_malloc_6 (a0 = 3296) at 0x836c0 and takes a
   class-6 frame F of 4096 bytes, of which it uses 3296 (descriptor "2 32 1492 17 scratch.i143:1407 1664 1492",
   object 20): two 1492-byte scratches at F + 32 and F + 1664 (image A has one fixed 1632-byte machine-stack frame
   and no such frame). The class contract returns frame_addr ly 6 pos, which is not 0, so the machine-stack carve
   0x836d8 / 0x836dc .. 0x836f4 is not reached (the flag's value 1 and that result); the two branches join at
   0x836f8. It writes F's header and F's shadow: 0..3 0xf1, 4..190 0xf8 (__asan_set_shadow_f8 (sh F + 4, 187) at
   0x8374c), 191..207 0xf2, 208..394 0xf8 (__asan_set_shadow_f8 (sh F + 208, 187) at 0x837a4), 395..411 0xf3. It
   returns -1 unless bgs_ok s V mx base w (0x837f4 .. 0x8384c), before it writes any byte of its caller's.
   Otherwise: __asan_memcpy (s, GRANT_HEAD_ACK, 34) at 0x83880; for p < 3 it reads V[p] (checked at 0x838c4), calls
   __asan_set_shadow_00 (sh F + 208, 186) at 0x838d4 and writes shadow 394 = 0x04 (the scratch F + 1664 is usable,
   its last granule partial), __asan_memset (F + 1664, 0, 1492) at 0x838ec, reac_ctrl_stamp_headamp (F + 1664, base,
   p, V[p]) at 0x83900, __asan_memcpy (s + 34 (p + 1), F + 1680, 34) at 0x83914 and __asan_set_shadow_f8 (sh F + 208,
   187) at 0x83920. Then __asan_memcpy (s + 136, GRANT_HEAD_MARK, 34) at 0x83974 and the six GRANT_GROUPB rows to
   s + 170 .. s + 374 (0x839a4). Then for each channel c in 1 .. w - 1 and p < 3 the same over the scratch F + 32:
   V[3 c + p] checked at 0x83ab0, __asan_set_shadow_00 (sh F + 4, 186) at 0x83ac0 and shadow 190 = 0x04,
   __asan_memset at 0x83ad8, reac_ctrl_stamp_headamp (F + 32, (base + c) & 0xff, p, V[3 c + p]) at 0x83aec,
   __asan_memcpy to row 11 + 3 (c - 1) + p at 0x83b00, __asan_set_shadow_f8 (sh F + 4, 187) at 0x83b0c. It returns
   bgs_rows w. Before it returns it writes the retired magic at F and calls __asan_stack_free_6 (F, 3296) at 0x83b9c.
   The branches after a stamp that returns nonzero (0x83904 -> 0x83948, 0x83af0 -> 0x83b6c, with
   __asan_set_shadow_f8 at 0x83b74) are not taken: every pair handed to the stamp is one legalb accepts
   (vals_legal). The no-frame branch at 0x83b8c (`beqz s2`) and its __asan_set_shadow_00 (sh F, 412) at 0x83bac are
   not taken: that entry's premise (a range inside a live frame's shadow) is false there, so the walk refutes the
   branch and never applies RT_SS00 to it. RT_SS00 is applied at 0x838d4 and 0x83ac0, on the live path after the
   join at 0x836f8.
   Its trap `unimp` 0x83bf4: the int check of base + w (`add` against `addw`, 0x8381c; `base + w < 2 ^ 31` makes it
   false), of 3 w and 3 w + 8 (0x8383c, 0x83848; w <= 48 there), the pointer steps over s and V (0x8389c, 0x838a4,
   0x838a8, 0x8395c, 0x8398c, 0x83994, 0x83a48, 0x83a60, 0x83a84, 0x83a9c; s + 34 bgs_rows w <= 2 ^ 47 - 8,
   0 <= V < 2 ^ 63) and the int checks of the row and value indexes (0x83a44, 0x83a68, 0x83a74; w <= 48). The two
   value loads take the error path when the shadow byte k of the value byte x is not 0 and not x mod 8 < k
   (0x838c4 -> 0x8393c -> 0x83944 errpath_load1; 0x83ab0 -> 0x83b2c -> 0x83b34 -> 0x83bf8 errpath_load1, which falls
   into ctrl_lay_block): the values' frame (afobj, partial-granule form) makes both false.
   The shadow 0x00 reac_ctrl_stamp_headamp needs over [p + 16, p + 50) of its scratch is the post of
   __asan_set_shadow_00 at 0x838d4 / 0x83ac0 (186 shadow bytes), kept by the __asan_memset that follows; the scratch
   lies in F, live at both stamp calls 0x83900 / 0x83aec.
   live_ok 6 at 0x836c0 is this call's own: count_cid 6 (frames Sc) <= 8 < fs_frames 6 = 256, from the premise
   `Z.of_nat (length (frames Sc)) <= 8`; F is live at both stamp calls, whose bound 9 follows.
   Stack: 256 + 16 + STK_reac_ctrl_stamp_headamp = 528 + ESTACK. *)
Definition tb_reac_ctrl_build_grant_sweep_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (s mx base w V : Z) (vals : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2 (res : Z),
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    (exists f, S2 = set_fs f Sc) /\
    getr regs2 10 = w64 res /\
    (* the exempt set is guarded by bgs_ok, as image A's (lib/A/Prog/CtrlBuildGrantSweepSpec.v:65, a working branch
       eacc832ec38a): on the refusal path nothing bounds s, so without the guard a caller's frame could lie inside it *)
    tcj_kept STK_reac_ctrl_build_grant_sweep lyc Sc W memc W2 mem2 (spZ regs)
      (fun a => bgs_ok s V mx base w /\ s <= a < s + 34 * bgs_rows w) /\
    (bgs_ok s V mx base w /\ res = bgs_rows w /\
       garr8 SEGS (mrestrict (w_H W2) mem2) s (map bv_unsigned (SWEEP base (Z.to_nat w) vals))
     \/ ~ bgs_ok s V mx base w /\ res = -1 /\
       (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - STK_reac_ctrl_build_grant_sweep <= a < spZ regs) ->
          aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
       (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
          aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i))).
Definition tb_reac_ctrl_build_grant_sweep_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (s mx base w V : Z)
    (vals : list byte) (cl : list (Z * Z * Z)),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 mx -> getr regs 12 = w64 base ->
  getr regs 13 = w64 w -> getr regs 14 = w64 V ->
  0 <= s < 2 ^ 63 -> - 2 ^ 31 <= mx < 2 ^ 31 -> 0 <= base < 256 -> - 2 ^ 31 <= w < 2 ^ 31 -> 0 <= V < 2 ^ 63 ->
  (* the trap 0x83bf4 at 0x8381c: the C sum base + w is an int *)
  base + w < 2 ^ 31 ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) cl ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_ctrl_build_grant_sweep -> spZ regs <= sp0 ->
  (* the live-frame bound that gives live_ok 6 (frames Sc) at 0x836c0 *)
  Z.of_nat (length (frames Sc)) <= 8 ->
  (* the values the caller hands in: they live in a frame of the caller on the side stack for frames, so they and
     their shadow survive the frame this call takes and the calls it makes *)
  (1 <= w -> V <> 0 ->
     length vals = Z.to_nat (3 * w) /\ vals_legal (Z.to_nat w) vals /\
     garr8 SEGS (mrestrict (w_H W) memc) V (map bv_unsigned vals) /\
     tsrc_ok W memc (spZ regs) V (3 * w) /\
     afobj SEGS B lyc Sc W memc V (3 * w) /\
     (spZ regs <= V \/ V + 3 * w <= spZ regs - STK_reac_ctrl_build_grant_sweep)) ->
  (* the row buffer, only when the burst is laid down: one heap block of the caller's *)
  (bgs_ok s V mx base w ->
     amem_range s (34 * bgs_rows w) /\ s + 34 * bgs_rows w <= 2 ^ 47 - 8 /\
     (s + 34 * bgs_rows w <= IMG_LO_B \/ IMG_TOP_B <= s) /\
     twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) s (34 * bgs_rows w) /\
     range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF s (34 * bgs_rows w) /\
     shadow_hull_vis (aview SEGS (w_H W) memc) s (34 * bgs_rows w) /\
     (exists b m, In (b, m) (ablocks B lyc Sc) /\ b <= s /\ s + 34 * bgs_rows w <= b + req_size m) /\
     (spZ regs <= s \/ s + 34 * bgs_rows w <= spZ regs - STK_reac_ctrl_build_grant_sweep) /\
     (V + 3 * w <= s \/ s + 34 * bgs_rows w <= V)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_build_grant_sweep) regs memc mdc)
    (tb_reac_ctrl_build_grant_sweep_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs s mx base w V vals).
Definition hyps_reac_ctrl_build_grant_sweep : Prop :=
  RT_LAWS /\ RT_PALIB /\ RT_PALIBF /\ RT_ML /\ RT_SMP /\ RT_SM 6 /\ RT_SF6 /\ RT_FFL /\ RT_TP_FS /\
  RT_SS00 /\ RT_SSF8 /\ RT_MEMCPY /\ RT_MEMSET /\ RT_IMGSH /\ RT_GLOBS /\ IMG_RO_BELOW /\ IMG_BGS_ROWS.
Definition walk_reac_ctrl_build_grant_sweep : Prop :=
  hyps_reac_ctrl_build_grant_sweep -> tb_reac_ctrl_stamp_headamp_spec -> tb_reac_ctrl_build_grant_sweep_spec.

(* ================================================= grant ================================================= *)
(* reac_headamp_tx_effective is the headamp fragment's; its stub Variable was replaced by that group's Definition
   at integration. *)
(* tb_reac_headamp_tx_effective_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_ctrl_build_grant_sweep is the laystamp fragment's; its stub Variable was replaced by that group's
   Definition at integration. *)
(* tb_reac_ctrl_build_grant_sweep_spec is the Definition below / above in this file (stub removed at integration). *)

(* ==== reac_grant_alloc_fits 0x85518 (BASE + 0x4adc; 15 instructions, 60 bytes) ===================================
   The call reads no memory, writes no memory, takes no frame and calls nothing. From the int32 arguments base (a0)
   and width (a1) it returns in a0 1 when 0 <= base, 1 <= width <= 40 and base + width <= 48 (GrantModel.fits),
   else 0: 0x85520 `bltz` (base < 0) and 0x8552c `bltu` (width - 41 as a 32-bit value, against -40) return 0, and
   0x85548 `slti a0,a0,48` gives (base + width - 1) < 48. Its one trap, `unimp` at 0x85550, has two guards:
   0x85538 `bne a1,a0` (the 32-bit sum addw against the 64-bit sum add, i.e. base + width is not an int32) and
   0x85544 `bge a0,a1` (sext32 (sum - 1) >= sext32 sum). Both are reached only when base >= 0 and
   1 <= width <= 40. The premise `0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31` makes the first false;
   then 1 <= sum < 2 ^ 31, so sum - 1 < sum makes the second false (the code is the same as image U's 0x152f4,
   lib/U/Prog/reac_grant_alloc_fits.v, which does this arithmetic). Stack: no frame; ESTACK for the runtime. *)
Definition STK_reac_grant_alloc_fits : Z := 0 + ESTACK.
Definition tb_reac_grant_alloc_fits_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (base width : Z)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_reac_grant_alloc_fits [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (Z.b2z (fits base width)) /\ ly' = ly /\ S' = S /\ W' = W /\
       (forall x, mem' x = mem x) /\ Permutation (ablocks B ly' S') (ablocks B ly S)).
Definition tb_reac_grant_alloc_fits_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch (base width : Z),
  afn_pre SEGS B STK_reac_grant_alloc_fits ly S W regs mem md ch ->
  getr regs 10 = w64 base -> getr regs 11 = w64 width ->
  int32 base -> int32 width ->
  (* the trap 0x85550: both guards (0x85538, 0x85544) are false *)
  (0 <= base -> 1 <= width <= 40 -> base + width < 2 ^ 31) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_grant_alloc_fits) regs mem md)
    (tb_reac_grant_alloc_fits_post regs ly S W mem md base width).
Definition hyps_reac_grant_alloc_fits : Prop := RT_LAWS.
Definition walk_reac_grant_alloc_fits : Prop := hyps_reac_grant_alloc_fits -> tb_reac_grant_alloc_fits_spec.

(* ==== reac_grant_allocate 0x85554 (BASE + 0x4b18; 42 instructions) ==============================================
   a0 = p (the caller's struct of two bytes), a1 = base, a2 = width (int32). Frame 16 (`addi sp,sp,-16`, ra at
   sp + 8). It returns -1 in a0 when base < 0 (0x85560), p = 0 (0x85564), width is not in 1..40 (0x85570) or
   base + width > 48 (0x85590, `blt` 47 against sum - 1); else it writes base at p (0x855b0) and width at p + 1
   (0x855cc) and returns 0. reac_grant_alloc_fits is inlined: its trap is `unimp` 0x855e0, with the guards 0x8557c
   (addw against add) and 0x85588 (sext32 (sum - 1) >= sext32 sum), both false under the int32 premise as for
   reac_grant_alloc_fits. Each store is checked: it reads the GOT word object 1 (0x9d6d0), then the shadow-base cell
   object 35, loads the shadow byte of p (0x855a8) / p + 1 (0x855c0) and, when that byte s is not 0, continues only
   when (x mod 8) < s (0x855e8 / 0x855f4); else it calls errpath_store1 (0x855ec, which falls into 0x855f0;
   0x855f8, which falls into reac_grant_build_sweep 0x855fc). The harness marks its struct's granule with the
   shadow byte 0x02 (0x81370) and passes it at 0x81384: `bytes_ok` over p and p + 1 makes both report branches
   false (never shadow = 0). The struct is in the caller's frame on the side stack for frames, so the contract is in
   the caller-journal form: `twr_ok` gives the right to write [p, p + 2), `tcj_kept` says what else is kept. It
   calls no program function, and no runtime function on the paths the premises allow. Stack: 16 + ESTACK. *)
Definition STK_reac_grant_allocate : Z := 16 + ESTACK.
Definition tb_reac_grant_allocate_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (p base w v0 v1 : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k /\
    aregs_preserved regs regs2 /\
    getr regs2 10 = w64 (if fits base w then 0 else -1) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) p (if fits base w then [base mod 256; w mod 256] else [v0; v1]) /\
    tcj_kept STK_reac_grant_allocate lyc Sc W memc W2 mem2 (spZ regs) (fun a => p <= a < p + 2).
Definition tb_reac_grant_allocate_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p base w v0 v1 : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 p -> getr regs 11 = w64 base -> getr regs 12 = w64 w ->
  int32 base -> int32 w ->
  (* the C adds base + width as int; the trap 0x855e0 (guards 0x8557c, 0x85588) is false *)
  (0 <= base -> 1 <= w <= 40 -> base + w <= 2 ^ 31 - 1) ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_grant_allocate -> spZ regs <= sp0 ->
  (* the caller's two bytes: off this call's stack window and off image B, and what they hold now *)
  p + 2 <= 2 ^ 47 - 8 -> (spZ regs <= p \/ p + 2 <= spZ regs - STK_reac_grant_allocate) ->
  (p + 2 <= IMG_LO_B \/ IMG_TOP_B <= p) -> (forall x, p <= x < p + 2 -> app_addr x) ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 2 ->
  (* the checked stores 0x855b0 / 0x855cc: the report branches 0x855ec / 0x855f8 are false *)
  bytes_ok W memc p 2 ->
  garr8 SEGS (mrestrict (w_H W) memc) p [v0; v1] ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_grant_allocate) regs memc mdc)
    (tb_reac_grant_allocate_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p base w v0 v1).
Definition hyps_reac_grant_allocate : Prop := RT_LAWS /\ RT_PALIB.
Definition walk_reac_grant_allocate : Prop := hyps_reac_grant_allocate -> tb_reac_grant_allocate_spec.

(* ==== reac_grant_build_sweep 0x855fc (BASE + 0x4bc0; 285 instructions) ===========================================
   a0 = s (the row buffer), a1 = mx (int), a2 = al (the caller's struct: base at al, width w at al + 1), a3 = tx (the
   460-byte head-amp table). Frame 192 on the machine stack (ra, s0-s11 at sp + 88 .. sp + 184; s0 = the entry
   sp), then `andi sp,sp,-32` (at most 16 more bytes), and a class-2 frame F of 256 bytes on the side stack for
   frames: it reads the UAR flag through the GOT word object 0 (0x9d728 -> object 36) and the shadow base through
   the GOT word object 1 (0x9d6d0 -> object 35); when the flag is not 0 it calls __asan_stack_malloc_2(192) at
   0x85674. When the flag is 0 (0x8566c) or the call returns 0 (0x85688) it carves the frame from the machine stack
   (0x8568c .. 0x856a4); the walk refutes both branches from the flag's value 1 (AR_const_law of RT_LAWS) and the
   class contract's nonzero result frame_addr ly 2 pos. It writes F's header (F + 0, F + 8, F + 16) and marks F's
   shadow bytes 0..3 0xf1, 4..18 0xf8, 19..23 0xf3; F + 32 .. F + 152 is the 120-byte array `vals`.
   It returns -1 when s = 0 (0x85748), al = 0 (0x8574c), w is not in 1..40 (0x85774) or base + w > 48 (0x857a0).
   Otherwise it marks F's shadow bytes 4..18 usable (0x857a4 ..), and for each channel i < w and p < 3 it stores
   reac_headamp_tx_effective(tx, (base + i) & 0xff, p) (call at 0x8584c) at vals[3 i + p]; the index check 0x85850
   (`bgeu` against 120) guards the trap `unimp` 0x85a3c, false because 3 i + p < 3 w <= 120. Then it calls
   reac_ctrl_build_grant_sweep(s, mx, base, w, F + 32) (0x858b0) and returns its result: the callee writes the
   8 + 3 w rows of 34 bytes at s when 8 + 3 w <= mx, else it returns -1. Before the return the call marks F's shadow
   bytes 4..18 0xf8 (0x858bc), writes the retired magic at F + 0, marks F's 32 shadow bytes 0xf5 and clears the flag
   byte through the pointer at F + 248 (0x85990 / 0x85994): the release is inline (no __asan_stack_free_2 call).
   Its four checked loads of the caller's struct, 0x85a4c (on al + 1), 0x85a5c, 0x8588c and 0x85a6c (on al), test
   the shadow byte s of x with `s <> 0 /\ ~ ((x mod 8) < s)` and call errpath_load1; that entry returns, so 0x85a4c
   falls into 0x85a50, 0x85a5c into 0x85a60, 0x8588c into 0x85890 and the last, 0x85a6c, into reac_headamp_tx_init
   0x85a70. The harness marks al's granule with 0x02 (0x81370, 0x81820) and passes it at 0x813e8 / 0x818cc /
   0x81918, so the premise is image A's `afobj` over al, al + 1, whose shadow conjunct is the partial-granule form
   (`range_addressable`, s = 0 or (x mod 8) < s < 8; the skeleton's `bytes_ok`), never shadow = 0: the walk refutes
   all four branches.
   Stack: 192 + 16 + the deepest callee, reac_ctrl_build_grant_sweep (528 + ESTACK: 256 + 16, then
   reac_ctrl_stamp_headamp 96 + 16, then ctrl_lay_block 128 + 16, then ESTACK); reac_headamp_tx_effective needs
   16 + ESTACK and __asan_stack_malloc_2 ESTACK.
   live_ok 2 S (count_cid 2 (frames S) < fs_frames 2 = 4096, grant_b_class2_sizes) is this call's own obligation:
   the walk discharges it at 0x85674 from the premise `Z.of_nat (length (frames S)) <= 7` by count_cid_le_length
   (GrantFrame.v). The same premise gives reac_ctrl_build_grant_sweep its bound `length (frames Sc) <= 8` (F is
   live at that call).
   At 0x858b0 (a0 = s, a1 = mx, a2 = base, a3 = w, a4 = V = F + 32) the walk gives reac_ctrl_build_grant_sweep's
   premises from these: `base + w < 2 ^ 31` (both are bytes, garr8; base + w <= 48 after 0x857a0); the bound 8
   (above); its `achain` (afn_pre's chain, ra / s0 stored at entry sp - 8 / - 16 by 0x85604 / 0x85608, s0 = entry
   sp at 0x85638, and entry sp < ly_top - 16 from `spZ regs + 32 <= ly_top ly`); under bgs_ok (= bsw_ok on that
   path) the row buffer's facts from the block premise and AR: the range form off image B (GrantPaLib.v
   blk_off_imgB), range_addressable_of_block and shadow_hull_vis_of_block (YCbq.v), amem_range and the bound below
   2 ^ 47 - 8 (al_blocks), twr_ok (this call's footprint and al_blocks), apart from V (YCbq.v sep_block_frame) and
   from the machine stack (below alloc_ceiling); V's tsrc_ok and afobj from the class-2 contract's post (frame
   present, zero shadow) and the shadow bytes 4..18 set to 0 at 0x857a4 (3 w <= 120 bytes from F + 32). *)
Definition STK_reac_grant_build_sweep : Z := 208 + 528 + ESTACK.
Definition tb_reac_grant_build_sweep_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  (s al mx tx base w : Z) (T : list byte) : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_reac_grant_build_sweep (tb_reac_grant_build_sweep_FP s al mx base w) regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S /\ (exists f, S' = set_fs f S) /\
       getr regs' 10 = w64 (if bsw_ok s al mx base w then 8 + 3 * w else -1) /\
       (bsw_ok s al mx base w = true ->
        garr8 SEGS (mrestrict (w_H W') mem') s
          (map bv_unsigned (SWEEP base (Z.to_nat w) (sweep_vals T tx base (Z.to_nat w)))))).
Definition tb_reac_grant_build_sweep_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (s mx al tx base w : Z) (T : list byte),
  afn_pre SEGS B STK_reac_grant_build_sweep ly S W regs mem md ch0 ->
  (* the live-frame bound: live_ok 2 S at 0x85674, and the callee's bound 8 *)
  Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 s -> getr regs 11 = w64 mx -> getr regs 12 = w64 al -> getr regs 13 = w64 tx ->
  0 <= s < 2 ^ 63 -> - 2 ^ 31 <= mx < 2 ^ 31 -> 0 <= al < 2 ^ 64 ->
  (* the caller's struct: in a live frame of the side stack for frames, 8-aligned, its two bytes marked usable in
     the partial-granule form the four checked loads test (afobj's range_addressable), and their values *)
  (al <> 0 -> afobj SEGS B ly S W mem al 2 /\ garr8 SEGS (mrestrict (w_H W) mem) al [base; w]) ->
  (* the head-amp table: a live 460-byte block *)
  In (tx, ATx.TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) mem) tx ATx.LAY_TX (ATx.tx_vals T) -> tx_set01 T -> tx_legal T ->
  (* the row buffer, only when the rows are laid down: inside one heap block of the caller's *)
  (bsw_ok s al mx base w = true ->
     exists sb sn, In (sb, sn) (ablocks B ly S) /\ sb <= s /\ s + 34 * (8 + 3 * w) <= sb + sn) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_grant_build_sweep) regs mem md)
    (tb_reac_grant_build_sweep_post regs ly S W mem md s al mx tx base w T).
Definition hyps_reac_grant_build_sweep : Prop :=
  RT_LAWS /\ RT_PALIB /\ RT_PALIBF /\ RT_ML /\ RT_SM 2 /\ RT_SMP /\ RT_ASF /\ RT_FFL /\ RT_TP_FS /\ IMG_RO_BELOW.
Definition walk_reac_grant_build_sweep : Prop :=
  hyps_reac_grant_build_sweep ->
  tb_reac_headamp_tx_effective_spec -> tb_reac_ctrl_build_grant_sweep_spec ->
  tb_reac_grant_build_sweep_spec.

(* ================================================= parsegroupa ================================================= *)
(* ==== parsegroupa: reac_ctrl_parse and check_groupa ========================================================= *)
(* reac_headamp_tx_effective is the head-amp group's (a Theorem Labs lane); its stub Variable was replaced by
   that group's Definition at integration. *)
(* tb_reac_headamp_tx_effective_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_ctrl_headamp_record_verify is the control-leaves group's (a Theorem Labs lane); its stub Variable
   was replaced by that group's Definition at integration. *)
(* tb_reac_ctrl_headamp_record_verify_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_ctrl_checksum_verify is the control-leaves group's (a Theorem Labs lane); its stub Variable was
   replaced by that group's Definition at integration. *)
(* tb_reac_ctrl_checksum_verify_spec is the Definition below / above in this file (stub removed at integration). *)

(* The caller-side fact that a function with a live frame on the side stack for frames states when it calls a
   function that takes a frame of its own there: every byte of each live frame of S, and every shadow byte of such
   a frame, is a client byte of S (aclient_byte, YG0n.v:230-235). `aowned` excludes client bytes (YG0n.v:236-242),
   so the post of __asan_stack_malloc_c keeps them (YG0d.v:298: a byte that is aowned neither before nor after
   the call and lies outside [sp - ESTACK, sp) is unchanged). *)
Definition tb_live_frames_client (ly : alayout) (S : astate) : Prop :=
  forall cid pos a, In (cid, pos) (frames S) ->
  in_zr a (frame_rng ly (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly cid pos), fs_frame_bytes cid / 8) ->
  aclient_byte B ly S a.

(* ---- reac_ctrl_parse 0x82774 (BASE + AF_reac_ctrl_parse, 2692 bytes) ----------------------------------------
   a0 = f, a1 = n, a2 = o. The call reads the control frame [f, f + 50) and writes the 36-byte result at o. The
   result is the caller's memory, so the contract has the caller-journal form. On return a0 = rc, and the 36 bytes
   at o are Pau's `ctrlparse n fr` (lib/Prog/RcParse.v), where fr is the 50 bytes at f.
   Frame: `addi sp,sp,-128` (0x82774); `andi sp,sp,-32` (0x827b0) drops at most 16 more bytes. At 0x827e4 the call
   takes a side-stack frame F of class 1 (128 bytes; __asan_stack_malloc_1, a0 = 128) when the UAR flag word
   (object 0, which points to object 36) is not zero. Image B's machine-stack fallback is 0x827fc..0x82814; it
   runs when the flag word is 0 (`beqz a2`, 0x827dc) or when the class contract returns 0 (`bnez s2` at 0x827f8
   not taken). The walk refutes the fallback: the flag word is 1 and the class contract returns the nonzero frame
   address. The call writes the header F + [0, 24) and the 16 shadow bytes of F (f1 x4, 00 x4, 04, f3 x7).
   F + [32, 68) is a local result struct that the code uses only when o = 0; here o is in a caller frame, so o is
   not 0. Release, inline: shadow bytes 4..8 := f8 (0x82b94), the magic word at F + 0, shadow f5 x16, and the flag
   byte *(F + 120) := 0 (0x82bbc..0x82c04).
   Calls: __asan_memset(o, 0, 36) 0x828b0; __asan_memcpy(o + 10, f, 6) 0x82930; __asan_memcpy(o + 4, f + 6, 6)
   0x82954; the bcmp wrapper (f, object 15 = .str.4, 6) 0x8296c, which needs 2 * ESTACK below sp;
   kind_of_link1(f[22]) 0x82d04 (tb_kind_of_link1_spec). Stack: 128 + 16 + 2 * ESTACK (the bcmp wrapper is the
   deepest callee; the others need ESTACK).
   Trap 0x82f70 (unimp), 21 guards: f = 0 (0x828bc); f + k passes 2^64 for some k <= 38 (0x828c4 0x828ec 0x8293c
   0x8298c 0x82994 0x829f8 0x82a3c 0x82a84 0x82ae8 0x82b2c 0x82b48 0x82d6c 0x82d74 0x82dd8 0x82e00 0x82e48 0x82e8c
   0x82ed0); o mod 4 <> 0 (0x82914, 0x82b90). The two `afobj` premises put f and o in a live frame of the caller
   on the side stack for frames (at least 4096, below 2^47, 8-aligned), so each guard is false.
   Report branches: 39 calls of __asan_report_* (0x82d28 and 0x82f7c .. 0x831f4), after the instrumented checks of
   the 1-byte loads at f + 12 .. f + 22 and f + 32 .. f + 38, the 4-byte load at o, and the stores at o (4 bytes),
   o + 16 (4), o + 20, o + 24, o + 28 (2), o + 22, o + 23, o + 26, o + 30, o + 31, o + 32 (1). `afobj` marks
   [f, f + 50) and [o, o + 36) usable in the partial-granule form (range_addressable: shadow 0, or x mod 8 < s < 8;
   check_groupa sets shadow 02 over f + 48, f + 49 and shadow 04 over o + 32 .. o + 35), so each check passes and no
   report branch is taken. *)
Definition STK_reac_ctrl_parse : Z := 144 + 2 * ESTACK.
Definition tb_reac_ctrl_parse_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (n o : Z) (fr : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 k /\
  aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
  (exists ff, S2 = set_fs ff Sc) /\
  getr regs2 10 = w64 (fst (ctrlparse n fr)) /\
  (forall i, (i < 36)%nat ->
   aview SEGS (w_H W2) mem2 (o + Z.of_nat i) = Some (bv_unsigned (nth i (snd (ctrlparse n fr)) cp_z))) /\
  tcj_kept STK_reac_ctrl_parse lyc Sc W memc W2 mem2 (spZ regs) (fun a => o <= a < o + 36).
Definition tb_reac_ctrl_parse_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch (f n o : Z) (fr : list byte),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 f -> getr regs 11 = w64 n -> getr regs 12 = w64 o -> 0 <= n < 2 ^ 64 ->
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - STK_reac_ctrl_parse -> spZ regs <= sp0 ->
  (* live_ok 1 Sc, discharged by the walk: count_cid 1 (frames Sc) <= length (frames Sc) <= 8 < fs_frames 1 *)
  Z.of_nat (length (frames Sc)) <= 8 ->
  (* the caller's live frames are client bytes, so the class-1 frame this call takes leaves them alone *)
  tb_live_frames_client lyc Sc ->
  (* the control frame and the result, each in a live frame of the caller on the side stack for frames *)
  afobj SEGS B lyc Sc W memc f 50 -> afobj SEGS B lyc Sc W memc o 36 -> f + 50 <= o \/ o + 36 <= f ->
  twr_ok STK sp0 FP ly S lyc Sc own W memc (spZ regs) o 36 ->
  length fr = 50%nat ->
  (forall i, (i < 50)%nat -> aview SEGS (w_H W) memc (f + Z.of_nat i) = Some (cp_v fr i)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_reac_ctrl_parse) regs memc mdc)
    (tb_reac_ctrl_parse_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n o fr).
(* Image B's constant the walk reads: .str.4 (object 15, a registered global of 7 bytes) holds the six bytes 0xff
   that the bcmp wrapper compares with f[0 .. 6). RT_GLOBS marks its shadow through this entry of GRANT_GLOBS_B,
   and RT_IMGSH maps its shadow hull. parsegroupa_img_check checks these numbers on image B by computation. *)
Definition IMG_reac_ctrl_parse : Prop :=
  In (VAL (A_OBJ 15), 7) GRANT_GLOBS_B /\
  IMG_LO + 64 <= VAL (A_OBJ 15) /\ VAL (A_OBJ 15) + 6 + 64 <= IMG_HI /\
  (forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
   forall i, 0 <= i < 6 -> aview SEGS H mem (VAL (A_OBJ 15) + i) = Some 255).
Definition hyps_reac_ctrl_parse : Prop :=
  RT_LAWS /\ RT_PALIB /\ RT_PALIBF /\ RT_ML /\ RT_MEMSET /\ RT_MEMCPY /\ RT_BCMP /\ RT_SM 1 /\ RT_SMP /\
  RT_ASF /\ RT_FFL /\ RT_TP_FS /\ RT_IMGSH /\ RT_GLOBS /\ IMG_RO_BELOW /\ IMG_reac_ctrl_parse.
Definition walk_reac_ctrl_parse : Prop :=
  hyps_reac_ctrl_parse -> tb_kind_of_link1_spec -> tb_reac_ctrl_parse_spec.

(* ---- check_groupa 0x82074 (BASE + AF_check_groupa, 960 bytes) ------------------------------------------------
   a0 = row, a1 = ch, a2 = p, a3 = tx, a4 = want; no result. The row is 34 bytes inside a heap block and holds Pau's
   group-A row `GAz ch p v` (lib/Prog/GrantSweepModel.v) for v = eff T tx ch p (lib/Prog/HeadampModel.v), the
   effective value of the live 460-byte head-amp table at tx, which holds T; want is that value. Image B's harness
   passes an input byte as ch (0x81624) or a zero-extended byte (0x816d0), and tx_effective accepts every ch below
   256, so the contract asks 0 <= ch < 256 (image A's asks ch < 48).
   Frame: `addi sp,sp,-128` (0x82074); `andi sp,sp,-32` (0x820b4) drops at most 16 more bytes. At 0x820f0 the call
   takes a side-stack frame F of class 2 (256 bytes; __asan_stack_malloc_2, a0 = 224) when the UAR flag word is
   not zero. Image B's machine-stack fallback is 0x82108..0x82120; it runs when the flag word is 0 (`beqz a2`,
   0x820e8) or when the class contract returns 0 (`bnez s2` at 0x82104 not taken). The walk refutes the fallback:
   the flag word is 1 and the class contract returns the nonzero frame address. Layout of F: header F + [0, 24);
   the control frame F + [32, 82) (shadow bytes 4..9 := 00, 10 := 02); the parse result F + [128, 164) (shadow
   bytes 16..20 := f8, then 00 x4 and 04 at 0x8220c); guard shadow bytes f1 (0..3), f2 (11..15), f3 (21..27).
   Release, inline: shadow f8 over the two variables (0x822a8), the magic word at F + 0, shadow f5 x32, and the flag
   byte *(F + 248) := 0 (0x822e8..0x82370).
   Calls: __asan_memcpy(F + 32, object 9 = __const.check_groupa.frame, 50) 0x821ec; __asan_memcpy(F + 48, row, 34)
   0x82208; reac_ctrl_parse(F + 32, 50, F + 128) 0x82230; reac_headamp_tx_effective(tx, ch, p) 0x8225c;
   reac_ctrl_headamp_record_verify(F + 32) 0x82268; reac_ctrl_checksum_verify(F + 32) 0x82274. Stack: 128 + 16 +
   STK_reac_ctrl_parse (reac_ctrl_parse is the deepest callee; __asan_memcpy, __asan_stack_malloc_2 and the three
   leaves of frame 16 need less).
   Abort path: each failed check branches to 0x82428 (__asan_handle_no_return), then `jal abort` (0x8242c), then
   the code falls into the trap 0x82430. The checks: rc <> 6 (0x82238); result[30] <> ch (0x82240); result[31] <> p
   (0x82248); result[32] <> the value of tx_effective (0x82260); a nonzero result of either verify call (0x8226c,
   0x82278); (sum of F[66 .. 72)) mod 128 <> 0 (0x82298); result[32] <> want (0x822a0). The control frame holds
   F50 ch p v = T0z ++ GAz ch p v (lib/Prog/GroupaModel.v), so rc = 6 and result[30 .. 33) = ch, p, v
   (ParseLink.parse_F50), the sum is 0 mod 128 (GroupaModel.F50_ga_sum), and v = eff T tx ch p = want. Thus no
   check fails and no contract of __asan_handle_no_return is needed. The trap's one guard, 0x821f4
   (F + 32 >= 2^64 - 16), is false because F < 2^47. There is no call of __asan_report_*: the code does not check
   its reads of F.
   Live-frame bound: live_ok 2 S, discharged by the walk from `length (frames S) <= 7` (count_cid 2 (frames S) <= 7
   < fs_frames 2); after the class-2 frame the state has at most 8 frames, which is reac_ctrl_parse's premise.
   The live class-2 frame across reac_ctrl_parse's class-1 frame: at 0x82230 the state has (2, pos) in its frames,
   so the walk states tb_live_frames_client for it (aclient_byte's second disjunct), and reac_ctrl_parse's post
   (tcj_kept, fourth conjunct) keeps the bytes and shadow bytes of F, except the result [F + 128, F + 164). *)
Definition STK_check_groupa : Z := 144 + STK_reac_ctrl_parse.
Definition tb_check_groupa_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_check_groupa [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' =>
       frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S /\ (exists ff, S' = set_fs ff S)).
Definition tb_check_groupa_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (row ch p tx rb rn : Z) (T : list byte),
  afn_pre SEGS B STK_check_groupa ly S W regs mem md ch0 ->
  (* live_ok 2 S, discharged by the walk; it also gives reac_ctrl_parse's bound after the class-2 frame *)
  Z.of_nat (length (frames S)) <= 7 ->
  spZ regs + 32 <= ly_top ly ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 row -> getr regs 11 = w64 ch -> getr regs 12 = w64 p -> getr regs 13 = w64 tx ->
  getr regs 14 = w64 (eff T tx ch p) ->
  0 <= ch < 256 -> 0 <= p < 3 ->
  (* the head-amp table: a live 460-byte heap block holding T *)
  In (tx, ATx.TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) mem) tx ATx.LAY_TX (ATx.tx_vals T) ->
  (* the row: 34 bytes inside a live heap block, holding GAz ch p (eff T tx ch p) *)
  In (rb, rn) (ablocks B ly S) -> rb <= row -> row + 34 <= rb + rn ->
  garr8 SEGS (mrestrict (w_H W) mem) row (GAz ch p (eff T tx ch p)) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_check_groupa) regs mem md) (tb_check_groupa_post regs ly S W mem md).
(* Image B's constant the walk reads: __const.check_groupa.frame (object 9, a registered global of 50 bytes), the
   source of the copy at 0x821ec, which takes ALL FIFTY bytes (`li a2,50` at 0x821e4; image A's copy took 16). So
   this names all fifty: T0z, which is the first 16, then 34 zero bytes, measured on image B at 0x20fc0..0x20ff1.
   The checked-copy step (YC85.v:249 aj_intrin_atS) asks for every one of the fifty through `src_ok`, which the
   first 16 alone cannot give. RT_GLOBS marks the shadow through this entry of GRANT_GLOBS_B, and RT_IMGSH maps
   its shadow hull. parsegroupa_img_check checks all fifty bytes on image B by computation. *)
Definition IMG_check_groupa : Prop :=
  In (VAL (A_OBJ 9), 50) GRANT_GLOBS_B /\
  IMG_LO + 64 <= VAL (A_OBJ 9) /\ VAL (A_OBJ 9) + 50 + 64 <= IMG_HI /\
  (forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
   garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 9)) (T0z ++ repeat 0 34)).
(* IMG_RO_BELOW and RT_TP_FS: the walk reads object 9 at the checked copy 0x821ec, after the class-2 frame call at
   0x820f0, so it must carry arodata_okP across that call. IMG_RO_BELOW was added for lib/B/PaBase.v:38
   arodata_ok_journalP, but the proved walk does not use it, nor RT_TP_FS: CheckGroupa.v:1378-1385 drops both, and
   carries arodata_okP with its own cg_rod_journal, whose journals have an empty footprint, so the read-only range
   needs no bound under the sink head. Both stay in the list: removing them would be an interface change. *)
Definition hyps_check_groupa : Prop :=
  RT_LAWS /\ RT_PALIB /\ RT_PALIBF /\ RT_ML /\ RT_MEMCPY /\ RT_SM 2 /\ RT_SMP /\
  RT_ASF /\ RT_FFL /\ RT_TP_FS /\ RT_IMGSH /\ RT_GLOBS /\ IMG_RO_BELOW /\ IMG_check_groupa.
Definition walk_check_groupa : Prop :=
  hyps_check_groupa -> tb_reac_ctrl_parse_spec -> tb_reac_headamp_tx_effective_spec ->
  tb_reac_ctrl_headamp_record_verify_spec -> tb_reac_ctrl_checksum_verify_spec -> tb_check_groupa_spec.

(* ==== the 21 functions of image B that END in a call of a report entry ==========================================
   A report entry (__asan_report_load1 / _load2 / _load4 / _load8 / _store1 / _store2 / _store4) RETURNS on image B
   (load1 0x58ca0 ret 0x58cec, load8 0x58e80 ret 0x58ecc, store1 0x58fc0 ret 0x5900c), so a call of one as a
   function's LAST instruction falls through into the next function. In the listing such a call is a `PCall` slot
   (b_last_call_slots below checks all 21 by computation). The engine stops the symbolic run at a `PCall` slot and
   hands the caller the callee's contract (lib/A/Prog/PaShadow.v:122-148 sym_step_pi_tok, :695-699
   sym_step_pi_tok_call: the run continues only at `sigma s`, through a contract the walk supplies). No hyps_<f> of
   this file holds a contract for a report entry, so a walk cannot pass such a slot: proving tb_<f>_spec refutes the
   branch that reaches it, and with it the fall-through. Image A states the same shape in lib/A/Prog/CtrlLayBlock.v:1007.

   | function                         | call pc | slot    | the walk lemma that refutes it    | falls into |
   | LLVMFuzzerTestOneInput           | 0x82070 | 0x1634  | pb_LLVMFuzzerTestOneInput         | check_groupa |
   | want_of                          | 0x824e8 | 0x1aac  | pb_want_of                        | asan.module_ctor |
   | reac_ctrl_block_cksum_stamp      | 0x82608 | 0x1bcc  | pb_reac_ctrl_block_cksum_stamp    | reac_ctrl_checksum_verify |
   | reac_ctrl_record_cksum_stamp     | 0x82770 | 0x1d34  | pb_reac_ctrl_record_cksum_stamp   | reac_ctrl_parse |
   | reac_ctrl_parse                  | 0x831f4 | 0x27b8  | pb_reac_ctrl_parse                | kind_of_link1 |
   | reac_ctrl_stamp_headamp          | 0x834d8 | 0x2a9c  | pb_reac_ctrl_stamp_headamp        | reac_ctrl_headamp_record_verify |
   | reac_ctrl_headamp_record_verify  | 0x835d8 | 0x2b9c  | pb_reac_ctrl_headamp_record_verify | reac_ctrl_identity_poll_block |
   | reac_ctrl_build_grant_sweep      | 0x83bf8 | 0x31bc  | pb_reac_ctrl_build_grant_sweep    | ctrl_lay_block |
   | ctrl_lay_block                   | 0x83fd8 | 0x359c  | pb_ctrl_lay_block                 | ctrl_finish |
   | ctrl_finish                      | 0x840cc | 0x3690  | pb_ctrl_finish                    | reac_box_model_block |
   | reac_box_model_block             | 0x84e48 | 0x440c  | pb_reac_box_model_block           | build_dt1_single |
   | build_dt1_single                 | 0x85000 | 0x45c4  | pb_build_dt1_single               | dt1_head |
   | dt1_head                         | 0x853fc | 0x49c0  | pb_dt1_head                       | name_field |
   | name_field                       | 0x85514 | 0x4ad8  | pb_name_field                     | reac_grant_alloc_fits |
   | reac_grant_allocate              | 0x855f8 | 0x4bbc  | pb_reac_grant_allocate            | reac_grant_build_sweep |
   | reac_grant_build_sweep           | 0x85a6c | 0x5030  | pb_reac_grant_build_sweep         | reac_headamp_tx_init |
   | reac_headamp_tx_set              | 0x85bec | 0x51b0  | pb_reac_headamp_tx_set            | reac_headamp_default |
   | reac_headamp_tx_effective        | 0x85ce0 | 0x52a4  | pb_reac_headamp_tx_effective      | reac_headamp_tx_arm_scene |
   | reac_headamp_tx_arm_scene        | 0x85e74 | 0x5438  | pb_reac_headamp_tx_arm_scene      | reac_headamp_tx_set_resweep |
   | reac_headamp_tx_set_resweep      | 0x85ef8 | 0x54bc  | pb_reac_headamp_tx_set_resweep    | reac_headamp_tx_next |
   | reac_headamp_tx_next             | 0x8663c | 0x5c00  | pb_reac_headamp_tx_next           | __wrap_getenv |
   The four unreached functions (reac_box_model_block 0x840d0, build_dt1_single 0x84e4c, dt1_head 0x85004,
   name_field 0x85400) hold the four trap sites 0x84c98, 0x84fdc, 0x852c4 and 0x85504; this file states no contract
   for them. Image B reaches that block of code only through three edges, and each is refuted by a contract here
   (FORM (a) of the audit):
     OBL_box_call_not_taken: the call of reac_box_model_block at 0x83e64 (slot 0x3428, b_box_call_slot) is not
       taken. CARRIED BY ctrl_lay_block's contract: hyps_ctrl_lay_block holds no contract for
       GS_reac_box_model_block, so walk_ctrl_lay_block cannot be proved while any walked arm reaches that slot. The
       row's byte +2 is 2 (IMG_CTRL_ROW_LAY's val_mem at B_ROW + 2), the bound check 0x83d60 / 0x83d64 passes, and entry 2
       of the table sends the `jr` at 0x83d84 to slot 0x33d4 = 0x83e10, which is none of LAY_BOX_SLOTS.
     OBL_finish_report_dead: ctrl_finish's last call, the report entry at 0x840cc, is not reached; its fall-through
       target is reac_box_model_block's first slot 0x840d0. CARRIED BY ctrl_finish's contract: hyps_ctrl_finish
       holds no contract for GS___asan_report_load1, and the three branches 0x84010 / 0x84044 / 0x84068 that lead
       to it are false under its premises (the row's granule shadow, IMG_CTRL_ROW's in_zs).
     OBL_sweep_report_dead: reac_ctrl_build_grant_sweep's last call, the report entry at
       0x83bf8, is not reached; its fall-through target is ctrl_lay_block's entry 0x83bfc, where a run outside
       ctrl_lay_block's contract could take the default arm 0x83e4c -> 0x83e64 (the call of reac_box_model_block).
       Seventeen edges lead there: sixteen branches to the trap 0x83bf4 just before it (0x8381c 0x8383c 0x83848
       0x8389c 0x838a4 0x838a8 0x8395c 0x8398c 0x83994 0x83a44 0x83a48 0x83a60 0x83a68 0x83a74 0x83a84 0x83a9c) and
       the jump 0x83b34 to 0x83bf8. CARRIED BY reac_ctrl_build_grant_sweep's contract: hyps of its walk hold no
       contract for GS___asan_report_load1, and its walk refutes every one of the seventeen edges.
   Until walk_ctrl_lay_block, walk_ctrl_finish and walk_reac_ctrl_build_grant_sweep are proved, all three are OPEN
   obligations, named here. *)
Lemma b_last_call_slots :
  map (plookup grant_tpi) [0x1634; 0x1aac; 0x1bcc; 0x1d34; 0x27b8; 0x2a9c; 0x2b9c; 0x31bc; 0x359c; 0x3690; 0x440c; 0x45c4; 0x49c0; 0x4ad8; 0x4bbc; 0x5030; 0x51b0; 0x52a4; 0x5438; 0x54bc; 0x5c00]
  = map (fun s => Some (PCall s (1%bv : bv 5)))
      [GS___asan_report_load1; GS___asan_report_load1; GS___asan_report_store1; GS___asan_report_store1; GS___asan_report_store1; GS___asan_report_store1; GS___asan_report_load1; GS___asan_report_load1; GS___asan_report_load8; GS___asan_report_load1; GS___asan_report_load1; GS___asan_report_store1; GS___asan_report_store1; GS___asan_report_load1; GS___asan_report_store1; GS___asan_report_load1; GS___asan_report_store4; GS___asan_report_load1; GS___asan_report_store4; GS___asan_report_store4; GS___asan_report_store4].
Proof. vm_compute. reflexivity. Qed.
Lemma b_box_call_slot : plookup grant_tpi 0x3428 = Some (PCall GS_reac_box_model_block (1%bv : bv 5)).
Proof. vm_compute. reflexivity. Qed.
Definition OBL_box_call_not_taken : Prop := walk_ctrl_lay_block.
Definition OBL_finish_report_dead : Prop := walk_ctrl_finish.
Definition OBL_sweep_report_dead : Prop := walk_reac_ctrl_build_grant_sweep.
(* Together: no run of image B's program code enters reac_box_model_block, build_dt1_single, dt1_head or
   name_field, so their four trap sites need no further proof. *)
Definition OBL_box_model_unreached : Prop :=
  OBL_box_call_not_taken /\ OBL_finish_report_dead /\ OBL_sweep_report_dead.

(* ================================================= entry ================================================= *)
(* reac_headamp_tx_init and reac_headamp_default: the skeleton's relocated Definitions above (no stub). *)
(* reac_headamp_tx_set is the headamp fragment's; its stub Variable was replaced by that group's Definition at
   integration. *)
(* tb_reac_headamp_tx_set_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_headamp_tx_effective is the headamp fragment's; its stub Variable was replaced by that group's Definition at
   integration. *)
(* tb_reac_headamp_tx_effective_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_headamp_tx_arm_scene is the headamp fragment's; its stub Variable was replaced by that group's Definition
   at integration. *)
(* tb_reac_headamp_tx_arm_scene_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_headamp_tx_set_resweep is the headamp fragment's; its stub Variable was replaced by that group's Definition
   at integration. *)
(* tb_reac_headamp_tx_set_resweep_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_headamp_tx_next is the headamp fragment's; its stub Variable was replaced by that group's Definition at
   integration. *)
(* tb_reac_headamp_tx_next_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_grant_alloc_fits is the grant fragment's; its stub Variable was replaced by that group's Definition at
   integration. *)
(* tb_reac_grant_alloc_fits_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_grant_allocate is the grant fragment's; its stub Variable was replaced by that group's Definition at
   integration. *)
(* tb_reac_grant_allocate_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_grant_build_sweep is the grant fragment's; its stub Variable was replaced by that group's Definition at
   integration. *)
(* tb_reac_grant_build_sweep_spec is the Definition below / above in this file (stub removed at integration). *)
(* want_of is the control-leaves fragment's; its stub Variable was replaced by that group's Definition at
   integration. *)
(* tb_want_of_spec is the Definition below / above in this file (stub removed at integration). *)
(* check_groupa is another group's (parse / group-A fragment); its stub Variable was replaced by that group's
   Definition at integration. *)
(* tb_check_groupa_spec is the Definition below / above in this file (stub removed at integration). *)
(* reac_ctrl_identity_poll_block is another group's (control-leaves fragment); its stub Variable was replaced by
   that group's Definition at integration. *)
(* tb_reac_ctrl_identity_poll_block_spec is the Definition below / above in this file (stub removed at integration). *)

(* ==== LLVMFuzzerTestOneInput 0x80a3c (BASE + 0x0; 1422 instructions, 5688 bytes) ==================================
   a0 = p (the input), a1 = n (its size). Frame 288 on the machine stack (`addi sp,sp,-288` 0x80a3c; sd zero at sp,
   ra and s0-s11 at sp + 280 .. sp + 184; s0 = the entry sp 0x80a78), then `andi sp,sp,-32` (0x80a7c) and s1 = the
   realigned sp, which holds the spill slots. It reads the UAR flag through the GOT word object 0 (0x9d728 -> object
   36) and the shadow base through the GOT word object 1 (0x9d6d0 -> object 35, kept at s1 + 144). With the flag not
   0 it calls __asan_stack_malloc_4(832) at 0x80ab0: a class-4 frame F of the side stack for frames (1024-byte slot,
   flag pointer at F + 1016), kept in s5. When the flag is 0 (0x80aa8) or F = 0 (0x80ac4) it carves 832 bytes from
   the machine stack (0x80ac8 .. 0x80ae0); the walk refutes both branches from the flag's value 1 (a constant cell of
   AR) and the class contract's nonzero result frame_addr ly 4 pos. It writes F's header (F + 0 the magic
   0x41b58ab3, F + 8 object 2, F + 16 object 3 = BASE + AF_LLVMFuzzerTestOneInput) and marks F's 104 shadow bytes:
   0xf1 left guard, 0xf8 for was_set (F + 32, 144 bytes), set_to (F + 240, 144), a (F + 448, 2), poll (F + 464, 34),
   raw (F + 560, 2), unset_sent (F + 576, 144), ch (F + 784), param (F + 800), value (F + 816); 4 for the 4-byte
   literal at F + 544; 0xf2 between them; 0xf3 right guard.
   When n >> 26 is not 0 (0x80cd4) it goes straight to the release; the premise n < 2 ^ 26 makes that branch false.
   The body: malloc(460) for the 460-byte head-amp table (0x80db4); reac_headamp_tx_init (0x80dd8); __asan_memset of
   was_set and set_to (0x80e34, 0x80e90) and of unset_sent (0x81b18), 144 bytes each; reac_headamp_tx_set (3 sites),
   reac_headamp_tx_effective (4), reac_headamp_default (2); reac_grant_alloc_fits (0x81364, 0x818e0); it marks a's
   shadow byte 0x02 (0x81370) and calls reac_grant_allocate(F + 448, ..) (0x81384); malloc of the sweep buffer
   (0x813d0), reac_grant_build_sweep (4 sites: 0x813e8 with a, 0x818cc / 0x81918 with raw, 0x81934 with NULL), the bcmp
   wrapper (5 sites: against HEAD_ACK object 4 and HEAD_MARK object 5 at 0x815e0 / 0x81604, the row against poll at
   0x81780, the 4-byte literal at 0x817b8, POLL object 6 at 0x817d4), want_of (3), check_groupa (2),
   reac_ctrl_identity_poll_block (0x8175c), free of the sweep buffer (0x81808); it marks raw's shadow byte 0x02
   (0x81820), then malloc (0x818b4) and free (0x81940) of a second sweep buffer, reac_headamp_tx_arm_scene (2),
   reac_headamp_tx_set_resweep (0x81a4c), reac_headamp_tx_next (0x81bd8) in the frame loop, and free of the table
   (0x81da8). It then jumps to the release (0x81e94 -> 0x80cd8): F + 0 := 0x45e0360e, __asan_set_shadow_f5(shadow of
   F, 128) at 0x80cf0 (all 128 shadow bytes of the 1024-byte slot), and the flag byte through F + 1016 := 0 (0x80cf8);
   a0 := 0, the saved registers are read back and it returns (0x80d54 .. 0x80d94). __asan_set_shadow_00 at 0x80d50 is
   on the no-frame fallback only, where its premise (a live frame of the side stack) is false: the walk refutes that
   path and never applies RT_SS00, which hyps_LLVMFuzzerTestOneInput therefore does not hold.
   The library shape gives the pre-condition (the driver's call: afn_pre with the library's stack bound, ra = 0x80938,
   a0 / a1 = the input, frames S = [], the event and live-byte headroom, the read-only data); the post is what the
   call leaves (apost_base: back at ra with a0 = 0, the journal with no footprint and no frame of its own, so F is
   given back and frames S' = [], the blocks a permutation of the caller's, the input bytes unchanged). The
   allocator meter is the trivial one, at which the library contract is closed (image A's grant_lib_x_closed uses
   ameter_triv), so no meter clause appears.
   ERROR FREEDOM. The trap `unimp` 0x81f48 has 44 guards (the branches into it); the walk shows each false from the
   premises (input and blocks below 2 ^ 47 in AR, n < 2 ^ 26, F and the table in range) and the callees' posts. The
   trap `unimp` 0x81da0 has no guard: it follows `jal __asan_handle_no_return` 0x81d98 and `jal abort` 0x81d9c, and
   0x81d98 is entered only by the 45 branches of the harness's own checks (a malloc result 0 at 0x80dbc / 0x813d4 /
   0x818b8, a callee result the C model rules out, a bcmp result not 0) and by the fall-through of the report call
   0x81d94; hyps holds no contract for handle_no_return or abort, so the walk must refute every one of those branches
   from the library-shape headroom (blocks_bytes S + 2 ^ 33 <= LIVE_MAX: each malloc returns a block) and the callees'
   posts. The 28 report calls (26 report_load1, 2 report_store1: 0x8118c 0x815a0 0x81d94 0x81f5c .. 0x82070) return
   on image B; the walk refutes each branch into them from the shadow of the input block (AR's client range), of F's
   objects (the shadow bytes it wrote), of the table and of the globals (RT_GLOBS, RT_IMGSH), including the last one,
   0x82070, which would fall into check_groupa 0x82074. Where a callee's premise speaks of the bytes of a or raw, the
   walk discharges it as `bytes_ok` (the shadow byte 0x02 written at 0x81370 / 0x81820), never as shadow = 0.
   SIDE STACK. The run starts with no frame on the side stack for frames: the premise `frames S = []` gives live_ok 4 S
   at 0x80ab0 (count_cid 4 [] = 0 < fs_frames 4 = 1024, tb_llvmf_b_numbers); this is the root discharge of the
   frame-count obligation. Every program callee runs with frames = [(4, pos)] (length 1), which the walk passes down
   as the callees' bound on `length (frames S)`: check_groupa's class-2 frame (0x820f0) and reac_ctrl_parse's class 1
   below it (0x827e4); reac_grant_build_sweep's class 2 (0x85674), then reac_ctrl_build_grant_sweep's class 6
   (0x836c0), reac_ctrl_stamp_headamp's class 0 (0x832dc) and ctrl_lay_block's class 1 (0x83c70) below it. *)
Definition tb_LLVMFuzzerTestOneInput_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md (p n : Z)
  : world SEGS -> config -> Prop :=
  apost_base SEGS B STK_LLVMFuzzerTestOneInput [] regs ly S W mem md EV_LIB_B
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 0 /\ frames S' = [] /\
       Permutation (ablocks B ly' S') (ablocks B ly S) /\
       (forall i, 0 <= i < n -> aview SEGS (w_H W') mem' (p + i) = aview SEGS (w_H W) mem (p + i))).
Definition tb_LLVMFuzzerTestOneInput_spec : Prop :=
  forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md (p n : Z) (pl : list byte),
  afn_pre SEGS B STK_LLVMFuzzerTestOneInput ly S W regs mem md [] ->
  raZ regs = RA_LLVMF_B ->
  getr regs 10 = w64 p -> getr regs 11 = w64 n ->
  ((n = 0 /\ p = A_EMPTY_B) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
  n = Z.of_nat (length pl) -> garr8 SEGS (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) pl) ->
  (* no frame on the side stack for frames: gives live_ok 4 S at 0x80ab0 *)
  frames S = [] ->
  st_nev S + EV_LIB_B <= EV_MAX -> blocks_bytes S + LIVE_LIB_B <= LIVE_MAX ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_LLVMFuzzerTestOneInput) regs mem md)
    (tb_LLVMFuzzerTestOneInput_post regs ly S W mem md p n).
(* An image fact the walk takes (image A states it as GrantLibX.v's HTR and proves it from fuzz_grant's trace
   universe, ACej.v): the call traces of the six wrapper calls are in the universe of image B's traces. *)
Definition IMG_LLVMF_TRACES : Prop :=
  forall (ly : alayout) (regs regsT : bvmap 5 word) (pcf : Z),
  raZ regs = RA_LLVMF_B ->
  (pcf = pc_malloc_ra0 (as_code B) /\ In (raZ regsT - (BASE + AF_LLVMFuzzerTestOneInput)) TB_LLVMF_MSITES) \/
  (pcf = pc_free_ra0 (as_code B) /\ In (raZ regsT - (BASE + AF_LLVMFuzzerTestOneInput)) TB_LLVMF_FSITES) ->
  In (call_trace0 pcf regsT (if spZ regs + 16 <? ly_top ly then [(spZ regs, raZ regs, s0Z regs)] else []))
     (as_universe B).
(* The four read-only tables LLVMFuzzerTestOneInput reads between 0x815e0 and 0x817d4 (the entry walk's):
   HEAD_ACK (object 4, 34 bytes; compared by the bcmp wrapper at 0x815e0, the abort branch 0x815e4), HEAD_MARK
   (object 5, 34 bytes; 0x81604, abort 0x81608), POLL (object 6, 18 bytes; 0x817d4, abort 0x817d8), and
   GRANT_GROUPB (object 19, B_GROUPB, 204 bytes), which tb_reac_ctrl_identity_poll_block_spec demands as
   `garr8 .. GBallz`, an `In (.., 204) GRANT_GLOBS_B` entry and two image bounds. PI and B are abstract in the walk,
   so without this conjunct none of the three abort branches can be refuted and the poll call cannot be made.
   Image A's entry walk took the same facts as hypotheses (lib/A/Prog/GrantEntrySweep.v:46-72). The form is
   IMG_BGS_ROWS's; every byte list is checked against image B (b_llvmf_sweep_check, b_groupb_check). *)
Definition IMG_LLVMF_SWEEP : Prop :=
  (forall (H : word -> bool) mem, arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS H mem) ->
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 4)) HEAD_ACK34z /\
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 5)) HEAD_MARK34z /\
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ 6)) POLLz /\
     garr8 SEGS (mrestrict H mem) (VAL (A_OBJ B_GROUPB)) GBallz) /\
  In (VAL (A_OBJ 4), 34) GRANT_GLOBS_B /\ In (VAL (A_OBJ 5), 34) GRANT_GLOBS_B /\
  In (VAL (A_OBJ 6), 18) GRANT_GLOBS_B /\ In (VAL (A_OBJ B_GROUPB), 204) GRANT_GLOBS_B /\
  IMG_LO + 64 <= VAL (A_OBJ 4) /\ VAL (A_OBJ 4) + 34 + 64 <= IMG_HI /\
  IMG_LO + 64 <= VAL (A_OBJ 5) /\ VAL (A_OBJ 5) + 34 + 64 <= IMG_HI /\
  IMG_LO + 64 <= VAL (A_OBJ 6) /\ VAL (A_OBJ 6) + 18 + 64 <= IMG_HI /\
  IMG_LO + 64 <= VAL (A_OBJ B_GROUPB) /\ VAL (A_OBJ B_GROUPB) + 204 + 64 <= IMG_HI.
Definition hyps_LLVMFuzzerTestOneInput : Prop :=
  RT_LAWS /\ RT_PALIB /\ RT_PALIBF /\ RT_ML /\ RT_SMP /\ RT_ASF /\ RT_FFL /\
  RT_MALLOC /\ RT_FREE /\ RT_MEMSET /\ RT_BCMP /\ RT_SM 4 /\ RT_SSF5 /\ RT_IMGSH /\ RT_GLOBS /\ RT_TP_FS /\
  IMG_RO_BELOW /\ IMG_LLVMF_TRACES /\ IMG_LLVMF_SWEEP.
(* OBLIGATION of this walk (never a premise of tb_LLVMFuzzerTestOneInput_spec): want_of's `0 <= p < 3` is
   DISCHARGED at each of its three call sites, 0x8163c and 0x816e8 from the loop invariants (the counters s10 and
   s7 run 0, 1, 2), and 0x81c40 from this walk's own branch at 0x81c28 (`bltu s11,a3` with s11 = 2 at 0x81b78),
   which jumps past the call when the byte loaded at 0x81c24 is above 2. *)
Definition walk_LLVMFuzzerTestOneInput : Prop :=
  hyps_LLVMFuzzerTestOneInput ->
  tb_reac_headamp_tx_init_spec -> tb_reac_headamp_tx_set_spec -> tb_reac_headamp_tx_effective_spec ->
  tb_reac_headamp_default_spec -> tb_reac_grant_alloc_fits_spec -> tb_reac_grant_allocate_spec ->
  tb_reac_grant_build_sweep_spec -> tb_want_of_spec -> tb_check_groupa_spec ->
  tb_reac_ctrl_identity_poll_block_spec -> tb_reac_headamp_tx_arm_scene_spec ->
  tb_reac_headamp_tx_set_resweep_spec -> tb_reac_headamp_tx_next_spec ->
  tb_LLVMFuzzerTestOneInput_spec.

(* ==== two CALLER OBLIGATIONS of walk_LLVMFuzzerTestOneInput, named so that neither is invisible =================
   Each is a premise of a callee's contract that the entry walk DISCHARGES at the call site; neither may be
   assumed. They are named here for the same reason as want_of's bound above and OBL_box_* earlier: a premise
   discharged inside a walk leaves no trace in Print Assumptions, so the obligation has to be written down.
   OBL_alloc_fits_bound: tb_reac_grant_alloc_fits_spec's premise `0 <= base -> 1 <= width <= 40 ->
     base + width < 2 ^ 31` (the two guards of image B's trap 0x85550, at 0x85538 and 0x85544). The entry calls
     reac_grant_alloc_fits at 0x81364 and 0x818e0. Measured (a Theorem Labs lane): at 0x818e0 base and width are bytes, so
     the sum is at most 295; at 0x81364 base comes from the spill slot read by `ld s4,0x58(s1)`, whose only
     reaching stores are 0x80d3c (a byte), 0x80d98 (zero) and 0x811d4 (an int16), so base is in [0, 32767] and
     base + width is at most 32807. Both are far below 2 ^ 31.
   OBL_grant_allocate_bound: tb_reac_grant_allocate_spec carries the same bound (image B inlines
     reac_grant_alloc_fits in it, with its own trap 0x855e0 guarded at 0x8557c and 0x85588). The entry calls
     reac_grant_allocate at 0x81384, which is reached only after the call at 0x81364 returned the value the walk
     expects, with base from the same spill slot, so the same measurement discharges it. *)
Definition OBL_alloc_fits_bound : Prop := walk_LLVMFuzzerTestOneInput.
Definition OBL_grant_allocate_bound : Prop := walk_LLVMFuzzerTestOneInput.

(* ==== the runtime entries asan.module_ctor / asan.module_dtor call ================================================
   The skeleton has no contract for them; these are the named hypotheses their walks take. *)
(* What a call that keeps the state leaves: AR at the same layout and state, the model up to materialized pages, every
   byte outside the window [spZ regs - stk, spZ regs) unchanged, and the window present (the post shape of the
   skeleton's set_shadow and memset entries). *)
Definition rtc_kept (stk : Z) (regs : bvmap 5 word) (ly : alayout) (S : astate) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (mem' : word -> option byte) (md' : Model) : Prop :=
  AR SEGS B ly S W mem' md' /\ same_but_materialized md md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - stk <= a < spZ regs) -> aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) /\
  (forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem' a).
(* __asan_init 0x59e04 (the runtime's start-up entry) and __asan_version_mismatch_check_v8 0x59e98 (the version
   check): called with no argument; from a state where AR holds (the runtime is set up) each returns to ra and keeps
   everything outside its ESTACK window. *)
Definition rtc_noop_realizes (pc : Z) : Prop :=
  forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md,
  ecall_pre SEGS B ly S W regs mem md ->
  SRr SEGS W (cfg_at SEGS pc regs mem md)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = cfg_at SEGS (raZ regs) regs' mem' md' /\ aregs_preserved regs regs' /\
       rtc_kept ESTACK regs ly S W mem md mem' md').
Definition RTC_INIT : Prop := rtc_noop_realizes (SIGMA GS___asan_init).
Definition RTC_VCHK : Prop := rtc_noop_realizes (SIGMA GS___asan_version_mismatch_check_v8).
(* The 8-byte flag word object 12 (0xa22c0) that the globals registration sets and the de-registration clears. *)
Definition tb_glob_flag (a : Z) : Prop := VAL (A_OBJ 12) <= a < VAL (A_OBJ 12) + 8.
(* __asan_register_elf_globals 0x403f8 / __asan_unregister_elf_globals 0x40464 (flag, start, stop): a0 = the flag
   word object 12, a1 / a2 = the words the GOT cells object 10 (0x9e348) / object 11 (0x9e350) hold (the two ends
   of the descriptor array 0xa1f80 .. 0xa22c0). The call returns to ra with the post of a runtime call (YG0d.v
   acall_post): it may change the flag word and the runtime's own bytes (shadow included), keeps the frames and
   the blocks. *)
Definition rtc_globals_realizes (pc : Z) : Prop :=
  forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md,
  ecall_pre SEGS B ly S W regs mem md ->
  getr regs 10 = w64 (VAL (A_OBJ 12)) ->
  rdword (aview SEGS (w_H W) mem) (VAL (A_OBJ 10)) = Some (bv_unsigned (getr regs 11)) ->
  rdword (aview SEGS (w_H W) mem) (VAL (A_OBJ 11)) = Some (bv_unsigned (getr regs 12)) ->
  SRr SEGS W (cfg_at SEGS pc regs mem md)
    (fun W' c' => exists ly' S' regs' mem' md',
       c' = cfg_at SEGS (raZ regs) regs' mem' md' /\
       acall_post SEGS B ESTACK ly S W regs mem md tb_glob_flag ly' S' W' regs' mem' md' /\
       frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S).
Definition RTC_REG : Prop := rtc_globals_realizes (SIGMA GS___asan_register_elf_globals).
Definition RTC_UNREG : Prop := rtc_globals_realizes (SIGMA GS___asan_unregister_elf_globals).

(* ==== asan.module_ctor 0x824ec (BASE + 0x1ab0; 14 instructions) ================================================
   Frame 16 (`addi sp,sp,-16`, ra at sp + 8). It calls, in order, __asan_init (0x824f4), the version check (0x824f8)
   and __asan_register_elf_globals (0x82514) with a0 = object 12 (`auipc` / `addi` 0x8250c / 0x82510), a1 / a2 the
   words loaded from the GOT cells object 10 / object 11 (0x82504 / 0x82508); then it reads ra back and returns. It has
   no checked access, no trap and no report call. Its contract is the sequence of the three calls, seen from its own
   window [sp - STK, sp): the first two keep the state and every byte outside the window, the third is a runtime
   call that may set the flag word. Stack: 16 + ESTACK. *)
Definition tb_asan_module_ctor_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  : world SEGS -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' mem1 md1 mem2 md2,
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
    (* __asan_init, 0x824f4 *)
    rtc_kept STK_asan_module_ctor regs ly S W mem md mem1 md1 /\
    (* the version check, 0x824f8 *)
    rtc_kept STK_asan_module_ctor regs ly S W mem1 md1 mem2 md2 /\
    (* the globals registration, 0x82514; the callee-saved registers are the entry's *)
    acall_post SEGS B STK_asan_module_ctor ly S W regs mem2 md2 tb_glob_flag ly' S' W' regs' mem' md' /\
    frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S.
Definition tb_asan_module_ctor_spec : Prop :=
  forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B STK_asan_module_ctor ly S W regs mem md ch ->
  (* the GOT cells the loads 0x82504 / 0x82508 read hold a word *)
  rdword (aview SEGS (w_H W) mem) (VAL (A_OBJ 10)) <> None ->
  rdword (aview SEGS (w_H W) mem) (VAL (A_OBJ 11)) <> None ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_asan_module_ctor) regs mem md) (tb_asan_module_ctor_post regs ly S W mem md).
(* RT_PALIB is here for `as_errno`: RTC_REG's post is acall_post, whose kept clause (YG0d.v:241) excludes
   `ascratch ESTACK regs` = [sp - ESTACK, sp) together with [as_errno B, as_errno B + 4) (YG0d.v:215-216), and no
   field of AR or of AR_laws bounds as_errno (measured: it occurs in YG0n.v 0 times, in YG0f.v only as the asyms
   field and in YG0d.v only in ascratch). Without a bound the errno cell may lie on the saved return address at
   sp + 8 (`sd ra,8(sp)` 0x824f0, `ld ra,8(sp)` 0x82518). PALib's pal_env (GrantPaLib.v) gives api_env
   (YCbq.v:807-809), which places the four errno bytes inside the image, so they are not on this frame. *)
Definition hyps_asan_module_ctor : Prop := RT_LAWS /\ RT_PALIB /\ RTC_INIT /\ RTC_VCHK /\ RTC_REG.
Definition walk_asan_module_ctor : Prop := hyps_asan_module_ctor -> tb_asan_module_ctor_spec.

(* ==== asan.module_dtor 0x82524 (BASE + 0x1ae8; 12 instructions) ================================================
   Frame 16 (ra at sp + 8). One call: __asan_unregister_elf_globals (0x82544) with a0 = object 12 (0x8253c /
   0x82540), a1 / a2 the words loaded from the GOT cells object 10 / object 11 (0x82534 / 0x82538); then it reads ra
   back and returns. No checked access, no trap, no report call. Its contract is that call's post seen from its own
   window. Stack: 16 + ESTACK. *)
Definition tb_asan_module_dtor_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
  : world SEGS -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md',
    c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom SEGS)) md' /\
    acall_post SEGS B STK_asan_module_dtor ly S W regs mem md tb_glob_flag ly' S' W' regs' mem' md' /\
    frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S.
Definition tb_asan_module_dtor_spec : Prop :=
  forall ly S (W : world SEGS) (regs : bvmap 5 word) mem md ch,
  afn_pre SEGS B STK_asan_module_dtor ly S W regs mem md ch ->
  (* the GOT cells the loads 0x82534 / 0x82538 read hold a word *)
  rdword (aview SEGS (w_H W) mem) (VAL (A_OBJ 10)) <> None ->
  rdword (aview SEGS (w_H W) mem) (VAL (A_OBJ 11)) <> None ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_asan_module_dtor) regs mem md) (tb_asan_module_dtor_post regs ly S W mem md).
(* RT_PALIB for the same reason: RTC_UNREG has the same acall_post post, and the dtor reloads its return address
   from sp + 8 after the call. *)
Definition hyps_asan_module_dtor : Prop := RT_LAWS /\ RT_PALIB /\ RTC_UNREG.
Definition walk_asan_module_dtor : Prop := hyps_asan_module_dtor -> tb_asan_module_dtor_spec.


End H.
End F.
End D.
