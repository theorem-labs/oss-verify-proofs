(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YP0n.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/Reusable/YP0n.v, with its module paths and module names changed; 967 of its 1043 lines of code are new or changed and 1914 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): the SHARED
   CONTRACT of the re-walk of check_no_overread (cno, entry B_prog_slot AS_check_no_overread = slot 201, B' 0x819f0, 312
   instructions) against the kit's text tcheck_no_overread_specX. Lane CnoB102r (a Theorem Labs lane, #102 plan
   the internal file PLAN-cno-caw-102.md sections 5.0 / 5.2). The twin of image A''s lib/A/Prog/Cno102A_Base.v (lane CnoA102r,
   a working branch a64053d93f63, blob 2847f513b75f): the same names with cnb_ for cn_, the same shapes, B''s
   offsets, registers and slots. This file STATES; Cno102B_Ro.v (the step kit), Cno102B_R4.v (CB4-CB6),
   Cno102B_Rpn.v (the three parse_noting steps), Cno102B_R7.v (CB7) and Cno102B_F.v (CB8) prove segments over it,
   Cno102B_Img.v witnesses cnb_img at the instance; the CB0-CB3 / CB9 lanes and the top compose.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   INPUTS (the kit CUT a working branch 7cdbb61b5fa0, merged forward whole; every path but this lane's
   files is the cut's blob):
     the kit texts (one set): lib/A/PRH_Base.v, lib/A/PRH_FnCheck.v c40cf3fdcd2a (ck_cno_copies :264-266,
     ck_cno_evs :268-281, tparse_noting_specX :596-, tcheck_no_overread_specX :738-823, tpadded_specX :954-), lib/A/PRH_FnAlloc.v
     4d8aeba047e5, lib/A/PRH_FnEx.v (tsame_specX: the astack_up_x guard), lib/A/PRH_FnPj.v 5aca5cbe2cfb
     (tpj_free_specX: prh_head_wide; K0-PJF-TIE closed into tparse_noting_specX's Some arm), lib/A/PRH_FnReader.v
     f1ae32e3b2cd, lib/A/PRH_FnTx.v 88468bf162d8, lib/A/PRH_FnParse.v f0d92dcec7e9, lib/A/PRH_FnWriter.v d89d3c67b78c,
     lib/A/PRH_NamesCheck.v 4031fe6f3bb2, lib/A/PRH_Supply.v e9069249fade, lib/A/PRH_PjOrder.v e5917626b82b,
     lib/A/PRH_Reader.v 4266e709561a, lib/A/PRH_Img.v 934516a622e8, lib/B/PRH_ImgB.v 3216eca68342 (the K0-confirmed #102 B'
     record, seven cells: pi_g_own_ran_out = B' 0x5ddd80, width 1), lib/A/PRH_Witness.v 9479acc344ef; the run model
     lib/Spec/PresetRun.v 5ac818ab1fe6 / PresetReqAt.v 43c958024221 / PresetReqAtNoMiss.v f949715d7a12,
     PresetRoomPos.v 943d62290e8e, PresetRoomPosKeep.v; the P'' engine set (the engine's univ-widening,
     25-field AR_laws_x): lib/Reusable/YCbqG.v (ajournal_xw), YCbqGwild.v 0c63874858e4
     (wild_room / wbudget / aj_call_xWFb), YCbqGcallW.v fb6aa11676a2; YCej.v 71ae24321ba4 (the set's Univ form).
     B' start-up records: YD2l.v 95803a8b9493, YF0m.v f82202ebccdf, YImgTop.v d2a97d3111ce.
     Listing (the cut's): lib/B/Listing_prog.v c97cc46b3e13, lib/B/PAImg_prog.v 15fab93fe702, lib/Reusable/YPsym.v
     (B_OBJ 13 = g_own_ran_out, 14 = g_most). This file does not Require lib/B/PAImg_prog.v (it stays parametric in PA,
     with the listing's own tables below); the instance witness cnb_img_inst (Cno102B_Img.v) Requires it. This file
     reads no CfImg instance. PRW_StepKit.v 0df3991c13f4.
   PARAMETRIC over {PA : PAImg B_prog_listing} (owner 12:48Z): no image number is typed here. The image facts the walk
   reads of PA are the record cnb_img, proved at the instance by computation once PAImg_prog.v builds. Offsets are
   DERIVED byte offsets inside check_no_overread (4 * slot), read off the B' disassembly of check_no_overread and
   re-checked against the cut's Listing_prog.v c97cc46b3e13 (slot kinds:
   PHi at 592, PLdHi (B_OBJ 13) at 596, PW words, PCall AS_fuzz_alloc_ran_out / AS_parse_noting / AS_same).
   THE CUTS (DERIVED offset: B' pc, what holds there):
     (entry)      0 0x819f0  CB0 start: cnb_pre at cfg_at (pa_sigma AS_check_no_overread)
     CNB_FRAME  164 0x81a94  CB0 exit / CB1 start (`sd s3, 0x30(s1)`): the fake frame made, s2 = the shadow base
     CNB_COPY   400 0x81b80  CB1 exit / CB2 start (`li a2, 0x31`): F's header and shadow poison stored
     CNB_INIT   460 0x81bbc  CB2 exit / CB3 start (`sb zero, 4(s2)`): the three padded copies made
     CNB_READ1  592 0x81c40  CB3 exit / CB4 start, after CB3's third zeroing memset (`auipc s8, ..`); s9 = r1, s7 = size
     CNB_PN1    632 0x81c68  CB4 exit: the `jal parse_noting` (a0 = r1, a1 = size, a2 = d1)
     CNB_RET1   636 0x81c6c  parse_noting (r1, size, d1)'s return site
     CNB_READ2  636 0x81c6c  CB5 start (`lbu a1, 0x140(s8)`), a0 = rc1
     CNB_PN2    676 0x81c94  CB5 exit: the `jal parse_noting` (a0 = r2, a1 = size, a2 = d2)
     CNB_RET2   680 0x81c98  parse_noting (r2, size, d2)'s return site
     CNB_READ3  680 0x81c98  CB6 start (`lbu a1, 0x140(s8)`), a0 = rc2, s1 + 8 = rc1
     CNB_PN3    720 0x81cc0  CB6 exit: the `jal parse_noting` (a0 = r3, a1 = size, a2 = d3)
     CNB_RET3   724 0x81cc4  parse_noting (r3, size, d3)'s return site (`mv s7, a0`)
     CNB_CMP    728 0x81cc8  CB7 start (`lbu a0, 0x140(s8)`), s7 = rc3, s1 + 8 = rc1, s1 + 0 = rc2
     CNB_FREE   740 0x81cd4  CB8 start (`mv a0, s6`), s8 = r (0x81cd0 `li s8, 1` is the exits' last step)
   The frame: s1 = (entry sp - 160) land -32 (the realigned sp, `addi sp, sp, -0xa0 .. andi sp, sp, -0x20; mv s1, sp`,
   0x819f0 / 0x81a30 / 0x81a34; sp = s1 from CB1 on), s3 = s11 = F = the class-3 fake frame
   (`__asan_stack_malloc_3 (0x140)` at 0x81a60; the real-stack fallback 0x81a78-0x81a90 is CB0's to refute), s2 = F's
   shadow address, s10 = -8 (CB1's poison byte 0xf8, CB9's). The structs: d1 = F + 32 (s6), d2 = F + 128 (s5),
   d3 = F + 224 (s4), 56 bytes each. The real-stack slots of the body (s1 + off): 48 F (0x81a94), 24 r2 (0x81ba4),
   16 r3 (0x81bb8), 8 rc1 (0x81c74), 0 rc2 (0x81ca0). The copies r1 / r2 / r3 ('1', '2', '\0') come from padded's
   __wrap_malloc (a RUNTIME block, not the ledger: the text keeps Lam' ~ Lam). s8 holds the auipc hi of g_own_ran_out
   from 0x81c40 on (Listing_prog.v slot 349 `PHi 24 9`; B_OBJ 13 = B_HI 9 + 0x140, the lbu offset at 0x81c6c / 0x81c98 /
   0x81cc8).
   THE FORM (rulings 12:18Z-12:31Z): every segment is generic in the memory invariant P (srr_inv_laws; srr_inv_call
   across a kit call; srr_inv_mn where the callee asks memnorm at entry) and FORWARD (the internal file lane-102.md :29-30): it ends in
   the exit cut(s) it reaches, cnb_ex_* below, `/\ P (ms_mem (cfg_ms c'))`; the segments compose by SRr_bind.
   g_own_ran_out and g_most (the kit's Batch 2, PRH_Base.v :497-516): the two cells are FIELDS of prh_glob, so prh_ledger
   takes `.. ran most own` and every callee text keeps them by carrying the ledger. Every cut's ledger states
   (bi_most D) and the own value that cut holds (0 before the readings' guard, own0 where CB2 / CB3 left it, ownl at
   the free cut); the function exit cnb_ex_ret is the text's full post.
   THE RUN POSITION (the post-implication form): the text binds no run position at entry; its post gives, for the
   grants o1 o2 o0 it binds and under own' = 0, the exact live set after ck_cno_evs and, for ANY run position i at the
   entry state whose next events are ck_cno_evs, a position i + length at the exit state. So each cut carries cnb_prog
   D E S for the events E made since entry (cnb_cevs: the granted copies; cnb_pe / cnb_revs2 / cnb_revs3: the
   readings, a reading skipped once one ran out), the grants of the readings done as cut parameters (None for a
   skipped one), and g_ran_out = cnb_ranz of them; cnb_ck_cno_evs is the equation C3 ++ revs3 ++ fevs = ck_cno_evs.
   tsame_specX's `S' = S` carries cnb_prog across CB7's two same calls. CB8 adds cnb_fevs: the accepted trees' pj_free
   (at the reader's OWN block lists, ordered against pj_frees by cnb_fo, which the reading's text gives: K0-PJF-TIE is
   closed) and the copies' free.
   THE CUT'S TEXT (7cdbb61b5fa0) ADDS: no DW (prh_univ_closure B CTX0, K0-DW-SPLIT); THE WILD BUDGET, the entry room
   wild_room [] (prh_wk F_check_no_overread) and the budgeted post fpostFbm (wbudget [] 6), so every cut's journal is
   the budgeted ajournal_xw at the spent budget (cnb_J's wk); THE COPIES' OUTCOME, the post's clause that retires the
   caller-discharged K0-CNO-COPY: own' = 0 at a consumer run of the three copies, carried as cnb_cdead where a copy was
   refused. The walk's Section hypotheses PRH_Base.prh_head16 (K0-CFHEAD-16) and prh_head_wide are the lanes', not
   this file's (reflexivity / preset_head_wide at CfParams_preset).
   Numerals: offsets above (DERIVED); 160 / 32 / 56 / 128 / 224 / 48 / 24 / 16 / 8 / 320 (LENGTH: frame, struct and
   slot offsets, the lbu offset 0x140 of the hi/lo pair); 3 (the frame class); 16 (the padded copy's tail); 0 / 2 / 4 /
   6 (COUNT: the spent wild budget, cnb_J's wk); 2 ^ 64 (LENGTH: the word range, as the cf layer's RELRO row spells
   it); -8 (WORD: s10); register numbers (WORD). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YI16 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
(* YK06 is NOT imported: its plain alloc_ceiling would shadow the RunCeil field YM05.alloc_ceiling (Cno102A_Base.v) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0ncf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80x YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar PresetRoomPos.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetHullBudget PresetReqAt PresetRun PresetSecTotal.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnAlloc
  PRH_FnReader PRH_FnPj PRH_FnEx PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfAroBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
(* the PLAIN build's sink instance is loaded transitively; it must never fill an ASan sink argument *)
#[global] Remove Hints OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable.YI5b.src0_sink_head : typeclass_instances.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the cut offsets: DERIVED byte offsets inside check_no_overread ---- *)
(* cno's slot in the listing: DERIVED, = B_prog_slot AS_check_no_overread of the cut's PAImg_prog.v 15fab93fe702 :412
   (B_entry_check_no_overread: sigma 0x819f0, slot 201); the image fact cnbi_entry ties it to pa_sigma *)
Definition CNB_SLOT : nat := 201.
Definition CNB_OFF : Z := 4 * Z.of_nat CNB_SLOT.
Definition CNB_READ1 : Z := 592.
Definition CNB_PN1 : Z := 632.
Definition CNB_RET1 : Z := 636.
Definition CNB_READ2 : Z := 636.
Definition CNB_PN2 : Z := 676.
Definition CNB_RET2 : Z := 680.
Definition CNB_READ3 : Z := 680.
Definition CNB_PN3 : Z := 720.
Definition CNB_RET3 : Z := 724.
Definition CNB_CMP : Z := 728.
Definition CNB_FREE : Z := 740.
(* LENGTH: the class of the fake frame (__asan_stack_malloc_3) *)
Definition CNB_CID : Z := 3.
(* the listing's own tables (the cut's PAImg_prog.v 15fab93fe702 :177-183, the same terms; Cno102A_Base.v's PL_cno_A): the
   engine's vm_compute needs a closed table *)
Definition B_prog_tpi_cno : ptree asym := ptree_of_list B_prog_listing.
Definition B_prog_tw_cno : ctable := Eval vm_compute in (tw_of 0 B_prog_listing).
Definition PL_cno_B : PAListing B_prog_listing :=
{| pl_tpi := B_prog_tpi_cno; pl_tpi_eq := eq_refl; pl_tw := B_prog_tw_cno; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.

(* the configuration at a cut, at the float state the callees left (parse_noting reaches musl strtod) *)
Definition cnb_cfg {segs : list Segment} (fxk : YK11.FPState) (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte)
  (md : Model) : config :=
  mkCfg (@YK11.mkst fxk regs (w64 pc) mem (YK11.seg_rom segs)) md.

(* a register snapshot: each named register holds the given value (H5RttDefs.v's rt_regsat form) *)
Definition cnb_regsat (regs : bvmap 5 word) (l : list (bv 5 * Z)) : Prop :=
  Forall (fun p => getr regs (fst p) = w64 (snd p)) l.

Section cnb. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
#[local] Existing Instance prh_img_B.
Context {PA : PAImg B_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
(* ---- THE IMAGE FACTS the walk reads of PA, each proved at the instance by computation (the cut's PAImg_prog.v
   15fab93fe702: B_prog_val, B_entry_check_no_overread; the object pin 13 = g_own_ran_out, PRH_ImgB.v 3216eca68342;
   the hi atom 9 of the pair at slots 349 / 350); the twin of Cno102A_Base.v 4dc213642458's cn_img B ---- *)
Record cnb_img : Prop := {
  cnbi_base : BASE = B_prog_base;
  cnbi_entry : SIGMA AS_check_no_overread = BASE + CNB_OFF;
  cnbi_own : VAL (A_OBJ 13) = pi_g_own_ran_out;
  cnbi_hi : VAL (A_HI 9) + 320 = VAL (A_OBJ 13);
  (* the program statics are writable data, not read-only bytes: what carries arodata_okP across a call by the
     journal (CawA102's WA4 finding, Caw102A_Base.v 3e9f97debfb cwi_pst_rw; Cno102A_Base.v 8b8e1011d865 cni_pst_rw) *)
  cnbi_pst_rw : forall a, Exists (in_zr a) prh_pst -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a;
  (* a program static is a SEGMENT byte, so a load of it reads a value whatever the memory holds there
     (Cno102A_Base.v's cni_pst_seg, CnoA9's finding) *)
  cnbi_pst_seg : forall a, Exists (in_zr a) prh_pst -> seg_rom SEGS (Z_to_bv 64 a) <> None;
  (* a store to a program static is a store to an image byte the runtime does not own (the journal's PST_ok;
     Cno102A_Base.v's cni_pst_ok, CnoA5's finding) *)
  cnbi_pst_ok : forall a, Exists (in_zr a) prh_pst -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B);
  (* a program static is not errno's word (CnoB102f's finding: the __wrap_free rows keep an image byte only outside
     as_errno .. + 4, YCbq.v acall_kept's 3rd clause; api_env puts errno in the image) *)
  cnbi_pst_errno : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4);
  (* ---- THE cf LAYER'S RELRO ROWS (field round 3, lib/Reusable/YG0ncf.v relro_seg_t / errno_relro_t), the A' twin's
     cni_relro_seg / cni_errno_relro / cni_relro_top / cni_relro_eq: what arodata_ok_cf asks of the image, and so what
     QMm_cf asks at every free / realloc call of the walk. The RELRO range of the cf image lies in ONE segment,
     errno's four bytes are apart from it, the range ends inside the address space, and it IS the listing's read-only
     range. Discharged at the instance as the other fields are. ---- *)
  cnbi_relro_seg : YG0ncf.relro_seg_t SEGS;
  cnbi_errno_relro : YG0ncf.errno_relro_t B;
  cnbi_relro_top : cf_relro_hi <= 2 ^ 64;
  cnbi_relro_eq : cf_relro_lo = @pa_relro_lo _ _ PA /\ cf_relro_hi = @pa_relro_hi _ _ PA;
  cnbi_ro_reads_nw : YGcfAroBridge.ro_reads_nw_t SEGS
}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Notation AJW := (ajournal_xw (SK := SK) SEGS B prh_pst ARx).
#[local] Notation STK := STK_check_no_overread.

Definition cnb_pc (off : Z) : Z := BASE + CNB_OFF + off.

(* ---- THE ENTRY DATA: every variable the text binds, and the position __asan_stack_malloc_3 returned. The text
   binds no run position (its post states the position as an implication over ANY run), so the record has no rp_*
   fields ---- *)
Record cnb_in : Type := mkCnbIn {
  bi_ly : alayout; bi_S : astate; bi_Hp : list Z; bi_W : world SEGS;
  bi_regs : bvmap 5 word; bi_mem : word -> option byte; bi_md : Model; bi_ch : list (Z * Z * Z);
  bi_data : Z; bi_x : list Z; bi_Lam : list (Z * Z); bi_peak : Z; bi_cnt : Z; bi_ran : Z; bi_most : Z;
  bi_fpos : Z
}.

Definition cnb_size (D : cnb_in) : Z := Z.of_nat (length (bi_x D)).
Definition cnb_sp0 (D : cnb_in) : Z := spZ (bi_regs D).
(* the realigned body sp (`addi sp, sp, -160 .. andi sp, sp, -32; mv s1, sp`, 0x819f0 / 0x81a30 / 0x81a34) *)
Definition cnb_S1 (D : cnb_in) : Z := Z.land (cnb_sp0 D - 160) (-32).
(* the fake frame, at the entry layout (layout_le keeps ly_F, YG0f.v :65-70) *)
Definition cnb_F (D : cnb_in) : Z := frame_addr (bi_ly D) CNB_CID (bi_fpos D).
Definition cnb_d1 (D : cnb_in) : Z := cnb_F D + 32.
Definition cnb_d2 (D : cnb_in) : Z := cnb_F D + 128.
Definition cnb_d3 (D : cnb_in) : Z := cnb_F D + 224.
(* the realigned sp is 32-aligned and lies in (entry sp - 192, entry sp - 160] (CnoB102f's CB8 call steps read it) *)
Lemma cnb_land_m32 : forall x, Z.land x (-32) = x - x mod 32.
Proof.
intros x. change (-32) with (Z.lnot (Z.ones 5)).
assert (Hl : Z.land x (Z.lnot (Z.ones 5)) = Z.ldiff x (Z.ones 5)).
{ apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.lnot_spec, Z.ldiff_spec by lia. reflexivity. }
rewrite Hl, Z.ldiff_ones_r, Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32.
rewrite Z.mod_eq by lia. lia.
Qed.
Lemma cnb_S1_bounds : forall D, cnb_sp0 D mod 16 = 0 ->
  cnb_S1 D <= cnb_sp0 D - 160 /\ cnb_sp0 D - 192 < cnb_S1 D /\ cnb_S1 D mod 32 = 0.
Proof.
intros D H16. unfold cnb_S1. rewrite cnb_land_m32.
pose proof (Z.mod_pos_bound (cnb_sp0 D - 160) 32 ltac:(lia)) as Hb.
split; [lia|]. split; [lia|].
rewrite Zminus_mod, Z.mod_mod by lia. rewrite Z.sub_diag. reflexivity.
Qed.

(* ---- THE HULL STAGES (route (b)): the all-granted event list the text's hull premise is stated over
   (PRH_FnCheck.v tcheck_no_overread, `PresetHullBudget.hull_budget S (ck_cno_evs .. x None None None)`), and
   one NAMED SUFFIX per stage of the walk: the part of that list still to be paid after the stage's calls. No
   reading runs out at the grant None (PresetRun.ranout .. None is false), so each suffix is the literal suffix
   of the all-granted list and every split below holds by reflexivity. A cut at a stage carries ONE plain
   conjunct `PresetHullBudget.hull_budget S (cnb_hrest_<stage> (bi_x D))` over its OWN astate, LAST in the cut; the
   conjunct is not inside a journal, so it is the same in X and XR. ---- *)
Definition cnb_hev_all (x : list Z) : list PresetReqAt.hev := ck_cno_evs ReaderRes.jr_strtod x None None None.
(* the pieces: one padded copy's malloc, the three copies' free *)
Definition cnb_hmal (x : list Z) : PresetReqAt.hev :=
  PresetReqAt.HMal (Z.of_nat (length x) + PresetReqAt.FUZZ_PAD).
Definition cnb_hF3 (x : list Z) : list PresetReqAt.hev :=
  repeat (PresetReqAt.HFr (Z.of_nat (length x) + PresetReqAt.FUZZ_PAD)) 3.
(* the stages: cpy1 / cpy2 after one / two of the three padded copies, copies after all three, rd1 / rd2 / rd0
   after each parse_noting, pf1 / pf2 / pf0 after each pj_free, and the three copies' free last *)
Definition cnb_hrest_copies (x : list Z) : list PresetReqAt.hev :=
  PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++
  PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hF3 x.
Definition cnb_hrest_cpy2 (x : list Z) : list PresetReqAt.hev := cnb_hmal x :: cnb_hrest_copies x.
Definition cnb_hrest_cpy1 (x : list Z) : list PresetReqAt.hev := cnb_hmal x :: cnb_hrest_cpy2 x.
Definition cnb_hrest_rd1 (x : list Z) : list PresetReqAt.hev :=
  PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hF3 x.
Definition cnb_hrest_rd2 (x : list Z) : list PresetReqAt.hev :=
  PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hF3 x.
Definition cnb_hrest_rd0 (x : list Z) : list PresetReqAt.hev :=
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hF3 x.
Definition cnb_hrest_pf1 (x : list Z) : list PresetReqAt.hev :=
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hF3 x.
Definition cnb_hrest_pf2 (x : list Z) : list PresetReqAt.hev :=
  PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hF3 x.
Definition cnb_hrest_pf0 (x : list Z) : list PresetReqAt.hev := cnb_hF3 x.
(* the split each stage's payment needs: what that stage's calls pay, then the suffix the next cut carries *)
Lemma cnb_hrest_cpy1_split : forall x, cnb_hev_all x = cnb_hmal x :: cnb_hrest_cpy1 x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_cpy2_split : forall x, cnb_hrest_cpy1 x = cnb_hmal x :: cnb_hrest_cpy2 x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_copies_split : forall x, cnb_hrest_cpy2 x = cnb_hmal x :: cnb_hrest_copies x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_rd1_split : forall x,
  cnb_hrest_copies x = PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ cnb_hrest_rd1 x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_rd2_split : forall x,
  cnb_hrest_rd1 x = PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ cnb_hrest_rd2 x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_rd0_split : forall x,
  cnb_hrest_rd2 x = PresetReqAt.parse_evs ReaderRes.jr_strtod x [] ++ cnb_hrest_rd0 x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_pf1_split : forall x,
  cnb_hrest_rd0 x = PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hrest_pf1 x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_pf2_split : forall x,
  cnb_hrest_pf1 x = PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hrest_pf2 x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_pf0_split : forall x,
  cnb_hrest_pf2 x = PresetRun.p1_tfree ReaderRes.jr_strtod x None ++ cnb_hrest_pf0 x.
Proof. intros x. reflexivity. Qed.
Lemma cnb_hrest_frees_split : forall x, cnb_hrest_pf0 x = cnb_hF3 x.
Proof. intros x. reflexivity. Qed.
(* paying ONE padded copy out of a stage budget: the copy's own one-element budget (what the padded call's premise
   asks, its request spelled `+ 16`), and the rest of the stage's budget after the copy's use *)
Lemma cnb_hpay_copy : forall S x rest,
  PresetHullBudget.hull_budget S (cnb_hmal x :: rest) ->
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (Z.of_nat (length x) + 16)] /\
  (forall S', PresetHullBudget.hull_used S S' [cnb_hmal x] -> PresetHullBudget.hull_budget S' rest).
Proof.
intros S x rest H.
assert (E : PresetReqAt.HMal (Z.of_nat (length x) + 16) = cnb_hmal x)
  by (unfold cnb_hmal, PresetReqAt.FUZZ_PAD; reflexivity).
split.
- rewrite E. apply (PresetHullBudget.hull_budget_weaken S [cnb_hmal x] (cnb_hmal x :: rest) H).
  + change (cnb_hmal x :: rest) with ([cnb_hmal x] ++ rest). rewrite PresetSecTotal.nsec_app. lia.
  + change (cnb_hmal x :: rest) with ([cnb_hmal x] ++ rest). rewrite PresetSecTotal.tsec_app.
    pose proof (PresetSecTotal.tsec_nn rest). lia.
- intros S' U. exact (PresetHullBudget.hull_budget_app S S' [cnb_hmal x] rest H U).
Qed.

(* ---- tcheck_no_overread_specX's premises at one record (PRH_FnCheck.v c40cf3fdcd2a :738-777, the kit cut
   7cdbb61b5fa0), verbatim ---- *)
Definition cnb_pre (CTX0 : list (list Z)) (D : cnb_in) : Prop :=
  let size := cnb_size D in
  fpre B ARx STK (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_regs D) (bi_mem D) (bi_md D) (bi_ch D) /\
  YAkMemnorm.memnorm SEGS (bi_mem D) /\
  prh_univ_closure B CTX0 /\ prh_ctx CTX0 F_check_no_overread (raZ (bi_regs D) :: spine (bi_ch D)) /\
  getr (bi_regs D) 10 = w64 (bi_data D) /\ getr (bi_regs D) 11 = w64 size /\
  size <= 3 * 2 ^ 20 /\
  src_rd (bi_W D) (bi_mem D) (bi_data D) (bi_x D) /\
  (0 < size -> PRH_FnReader.prhReader_home B (bi_ly D) (bi_S D) (bi_Hp D) (bi_Lam D) (bi_data D) size) /\
  prh_ledger B (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D)
    (bi_most D) 0 /\
  bi_cnt D < 2 ^ 62 - 2 ^ 30 /\
  bi_ran D = 0 /\
  PRH_FnPj.RQ_pj_parse (bi_x D) <= bi_most D /\
  blocks_bytes (bi_S D) + LIVE_check_no_overread (bi_x D) <= LIVE_MAX /\
  size + 16 < cf_malloc_max /\ PRH_FnPj.RQ_pj_parse (bi_x D) + cf_head < cf_malloc_max /\
  Z.of_nat (length (frames (bi_S D))) <= ck_FRAMES_CAP - FR_check_no_overread /\
  room_live_cf (bi_S D) /\ ck_frm0 (fx := fx) /\
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F_check_no_overread) (st_depot (bi_S D)) /\
  Z.of_nat (PresetRun.pkR YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None)) <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV /\
  Z.of_nat (PresetRun.pkR (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D)))
    (ck_cno_evs ReaderRes.jr_strtod (bi_x D) None None None)) <= PresetLiveBounds.L24 + PresetLiveBounds.DRV /\
  (* the text's hull premise (PRH_FnCheck.v tcheck_no_overread): the whole call's allocator-hull budget at the
     entry state, which each cut pays down one stage at a time (cnb_hrest_<stage> above) *)
  PresetHullBudget.hull_budget (bi_S D) (cnb_hev_all (bi_x D)).

(* ---- THE REFUSED COPY IS DEAD AT A CONSUMER RUN (K0-CNO-COPY retired into the text's post clause, PRH_FnCheck.v
   c40cf3fdcd2a :801-804; the A' twin's cn_cdead, caw_dead's shape): no model run and position whose next events are the
   three copies, each a consumer event, starts at the entry state. A cut whose g_own_ran_out value is not 0 (a padded
   copy was refused: own0 at init / read1, ownl at free) carries it, from CB2's padded outcome clause (tpadded_specX,
   PRH_FnCheck.v c40cf3fdcd2a :973-978: res <> 0 at a consumer HMal, against the refused arm's res = 0); the post's
   clause follows ---- *)
Definition cnb_cdead (D : cnb_in) : Prop :=
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x0 os i H0 hist (bi_S D) -> PRH_Base.prh_run_at sm x0 os i (ck_cno_copies (bi_x D)) ->
    PRH_Base.prh_cons_from sm x0 os i (length (ck_cno_copies (bi_x D))) -> False.

(* ---- the text's post body at one record (PRH_FnCheck.v c40cf3fdcd2a :787-823), verbatim; the post ---- *)
Definition cnb_Q (D : cnb_in) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) ->
  Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    room_live_cf S' /\ exists Lam' peak' cnt' ran' own',
    Permutation Lam' (bi_Lam D) /\ Permutation (ablocks B ly' S') (ablocks B (bi_ly D) (bi_S D)) /\
    bi_peak D <= peak' /\ bi_cnt D <= cnt' <= bi_cnt D + 3 * ck_ncalls (bi_x D) /\
    prh_ledger B ly' S' Hp' W' mem' Lam' peak' cnt' SIZE_MAXZ ran' (bi_most D) own' /\
    bytes_at W' mem' (bi_data D) (bi_x D) /\
    exists r, getr regs' 10 = w64 r /\
      ((r = 1 /\ (own' = 1 \/ ran' = 1)) \/ (r = 0 /\ own' = 0 /\ ran' = 0)) /\
      (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
         (H0 : list Z) (hist : list YG00.chunk),
         PresetRoomPos.iface_room_pos sm x0 os i H0 hist (bi_S D) ->
         PRH_Base.prh_run_at sm x0 os i (ck_cno_copies (bi_x D)) ->
         PRH_Base.prh_cons_from sm x0 os i (length (ck_cno_copies (bi_x D))) -> own' = 0) /\
      (own' = 0 -> exists o1 o2 o0 : option nat,
         r = (if ck_cno_ranout ReaderRes.jr_strtod (bi_x D) o1 o2 o0 then 1 else 0) /\
         Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S'))
           (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D)))
              (ck_cno_evs ReaderRes.jr_strtod (bi_x D) o1 o2 o0)) /\
         (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
            (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x0 os i H0 hist (bi_S D) ->
            PRH_Base.prh_run_at sm x0 os i (ck_cno_evs ReaderRes.jr_strtod (bi_x D) o1 o2 o0) ->
            exists hist', PresetRoomPos.iface_room_pos sm x0 os
              (i + length (ck_cno_evs ReaderRes.jr_strtod (bi_x D) o1 o2 o0))%nat H0 hist' S')).
Definition cnb_post (D : cnb_in) : world SEGS -> config -> Prop :=
  fpostFbm B ARx SK (YCbqGwild.wbudget [] (prh_wk F_check_no_overread))
    STK [] (bi_regs D) (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D) (cnb_Q D).
(* the post and the exit over a world relation R, through the kit's R families (PRH_Base.v): fpostFbm is AFTER-FREE-ONLY,
   so the kit owner states it IN PLACE at wle' SEGS YGcfRehidePost.RZ_cf and the guards below are the wle' ones (the kit's naming:
   X_R_wle when the plain form is the wle instance, X_R_wle' when it is the wle' instance) *)
Definition cnb_postR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop :=
  fpostFbmR B ARx SK R (YCbqGwild.wbudget [] (prh_wk F_check_no_overread))
    STK [] (bi_regs D) (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D) (cnb_Q D).
Lemma cnb_post_R_wle' : forall D,
  cnb_post D = cnb_postR (wle' SEGS YGcfRehidePost.RZ_cf) D.
Proof. reflexivity. Qed.
(* THE FUNCTION EXIT the segments reach (CB9's exit): the text's post *)
Definition cnb_ex_ret (D : cnb_in) : world SEGS -> config -> Prop := cnb_post D.
Definition cnb_ex_retR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := cnb_postR R D.
Lemma cnb_ex_ret_R_wle' : forall D,
  cnb_ex_ret D = cnb_ex_retR (wle' SEGS YGcfRehidePost.RZ_cf) D.
Proof. reflexivity. Qed.

(* ---- the memory invariant at the top: memnorm of the entry memory gives memnorm at m ---- *)
Definition cnb_mn (D : cnb_in) (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm SEGS (bi_mem D) -> YAkMemnorm.memnorm SEGS m.
Lemma cnb_mn_laws : forall D, srr_inv_laws SEGS (cnb_mn D).
Proof. intros D. exact (srr_inv_laws_imp SEGS (YAkMemnorm.memnorm SEGS) (bi_mem D) (srr_inv_laws_memnorm_k SEGS)). Qed.
Lemma cnb_mn_call : forall D, srr_inv_call SEGS (cnb_mn D).
Proof. intros D. exact (srr_inv_call_imp SEGS (bi_mem D)). Qed.
Lemma cnb_mn_mn : forall CTX0 D, cnb_pre CTX0 D -> srr_inv_mn SEGS (cnb_mn D).
Proof.
intros CTX0 D H. unfold cnb_pre in H. cbv zeta in H. destruct H as (_ & HMN & _).
exact (srr_inv_mn_imp SEGS (bi_mem D) HMN).
Qed.
Lemma cnb_mn_entry : forall D, cnb_mn D (bi_mem D).
Proof. intros D H. exact H. Qed.

(* ---- what every cut from CB4 on carries ---- *)
(* the journal from entry, the function's own class-3 frame in `own`, under THE WILD BUDGET the cut has spent
   (YCbqG.v ajournal_xw: the wild traces stored now are those at entry plus WS; YCbqGwild.wbudget: at most wk of WS
   are outside []). The only wild site of the subtree is the readings' cursor frees, prh_wk F_parse_noting = 2 per
   parse_noting call; the function's own mallocs / frees are fixed-trace sites. The cuts pass the spent budget as a
   constant upper bound (the A' twin's cn_J): 0 up to pn1, 2 at read2 / pn2, 4 at read3 / pn3, 6 = prh_wk
   F_check_no_overread (cnb_wk_total) from cmp on *)
Lemma cnb_wk_total : (3 * prh_wk F_parse_noting)%nat = prh_wk F_check_no_overread.
Proof. reflexivity. Qed.
Definition cnb_J (D : cnb_in) (wk : nat) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  exists WS : list (list Z),
  AJW STK (cnb_sp0 D) [] (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D) (bi_md D) [(CNB_CID, bi_fpos D)]
    ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS.
(* the journal over a world relation R (YCbqG.ajournal_xwR): the cuts after a free or realloc carry it at the
   walk's relation; cnb_J keeps its body (proofs unfold it) and cnb_J_R_wle ties the copy *)
Definition cnb_JR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (wk : nat) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  exists WS : list (list Z),
  ajournal_xwR (SK := SK) SEGS B prh_pst ARx R STK (cnb_sp0 D) [] (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_mem D)
    (bi_md D) [(CNB_CID, bi_fpos D)] ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS.
Lemma cnb_J_R_wle : forall D wk ly S Hp W mem md k,
  cnb_J D wk ly S Hp W mem md k = cnb_JR (@wle SEGS) D wk ly S Hp W mem md k.
Proof. reflexivity. Qed.
(* THE THIRTEEN SAVED WORDS at entry sp - 160 + off (0x819f8-0x81a28): ra 152, s0 144, s1 136, s2 128 .. s11 56 *)
Definition cnb_saved (D : cnb_in) (W : world SEGS) (mem : word -> option byte) : Prop :=
  Forall (fun p : Z * bv 5 =>
            rdword (aview SEGS (w_H W) mem) (cnb_sp0 D - 160 + fst p) = Some (bv_unsigned (getr (bi_regs D) (snd p))))
    [(152, 1%bv); (144, 8%bv); (136, 9%bv); (128, 18%bv); (120, 19%bv); (112, 20%bv); (104, 21%bv);
     (96, 22%bv); (88, 23%bv); (80, 24%bv); (72, 25%bv); (64, 26%bv); (56, 27%bv)].
(* the frame: live on top of the entry's frames, its flag word, its bytes and its shadow present *)
Definition cnb_frame (D : cnb_in) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) : Prop :=
  frames S = (CNB_CID, bi_fpos D) :: frames (bi_S D) /\ ~ In (CNB_CID, bi_fpos D) (frames (bi_S D)) /\
  rdword (aview SEGS (w_H W) mem) (cnb_F D + fs_frame_bytes CNB_CID - 8) = Some (flag_addr ly CNB_CID (bi_fpos D)) /\
  (forall a, cnb_F D <= a < cnb_F D + fs_frame_bytes CNB_CID -> apresent (w_H W) mem a) /\
  (forall a, shadow_addr (cnb_F D) <= a < shadow_addr (cnb_F D) + fs_frame_bytes CNB_CID / 8 -> apresent (w_H W) mem a).
(* the body's real-stack slots at s1 that every cut from CB4 on holds: 48 F, 24 r2, 16 r3 *)
Definition cnb_slots (D : cnb_in) (W : world SEGS) (mem : word -> option byte) (r2 r3 : Z) : Prop :=
  Forall (fun p : Z * Z => rdword (aview SEGS (w_H W) mem) (cnb_S1 D + fst p) = Some (snd p))
    [(48, cnb_F D); (24, r2); (16, r3)].
(* a result slot the body wrote: rc at s1 + off, as the 64-bit word of the sign-extended int *)
Definition cnb_rcslot (D : cnb_in) (W : world SEGS) (mem : word -> option byte) (off rc : Z) : Prop :=
  rdword (aview SEGS (w_H W) mem) (cnb_S1 D + off) = Some (rc mod 2 ^ 64).
(* the registers every cut from CB4 on holds: sp = s1, s0 = the entry sp, s2 = F's shadow, s3 = s11 = F, s4 / s5 / s6
   = d3 / d2 / d1, s10 = -8 *)
Definition cnb_core (D : cnb_in) : list (bv 5 * Z) :=
  [(2%bv, cnb_S1 D); (8%bv, cnb_sp0 D); (9%bv, cnb_S1 D); (18%bv, shadow_addr (cnb_F D)); (19%bv, cnb_F D);
   (20%bv, cnb_d3 D); (21%bv, cnb_d2 D); (22%bv, cnb_d1 D); (26%bv, -8); (27%bv, cnb_F D)].
(* s8: the auipc hi of g_own_ran_out (Listing_prog.v slot 349 `PHi 24 9`) *)
Definition cnb_s8 : bv 5 * Z := (24%bv, VAL (A_HI 9)).
Definition cnb_base (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (wk : nat) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  cnb_J D wk ly S Hp W mem md k /\ cnb_frame D ly S W mem /\ cnb_saved D W mem /\
  getr regs 3 = getr (bi_regs D) 3 /\ getr regs 4 = getr (bi_regs D) 4 /\
  (* the read-only view, fpre's second conjunct at every call *)
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
(* cnb_base over a world relation R (a copy: proofs unfold cnb_base), its journal cnb_JR R. Every cut below is
   stated the same way: X R is the cut over R, X its wle instance (or, where proofs unfold X, a copy of X's body
   tied by X_R_wle) *)
Definition cnb_baseR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (wk : nat) : Prop :=
  frm_zero (@YK11.fp_csr fxk) /\ fregs_kept_x fx fxk /\
  cnb_JR R D wk ly S Hp W mem md k /\ cnb_frame D ly S W mem /\ cnb_saved D W mem /\
  getr regs 3 = getr (bi_regs D) 3 /\ getr regs 4 = getr (bi_regs D) 4 /\
  (* the read-only view, fpre's second conjunct at every call *)
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem).
Lemma cnb_base_R_wle : forall D fxk ly S Hp W regs mem md k wk,
  cnb_base D fxk ly S Hp W regs mem md k wk = cnb_baseR (@wle SEGS) D fxk ly S Hp W regs mem md k wk.
Proof. reflexivity. Qed.

(* ---- THE MONO OVER THE WORLD RELATION, the lift a walk uses at the boundary: a cut proved BEFORE the free
   carries its journal at wle, and the cut AFTER it wants the same cut at the walk's relation. Every XR whose only
   R-carrying part is the journal has one, by YCbqG.ajournal_xwR_mono at the base and by chaining it upwards; at
   R1 := wle, R2 := wle' SEGS RZ_cf the premise is YA0nH.wle_wle'. ---- *)
Lemma cnb_JR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D wk ly S Hp W mem md k, cnb_JR R1 D wk ly S Hp W mem md k -> cnb_JR R2 D wk ly S Hp W mem md k.
Proof.
intros R1 R2 H12 D wk ly S Hp W mem md k (WS & HJ & HB). exists WS. split; [|exact HB].
eapply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx R1 R2 H12). exact HJ.
Qed.
Lemma cnb_baseR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k wk,
  cnb_baseR R1 D fxk ly S Hp W regs mem md k wk -> cnb_baseR R2 D fxk ly S Hp W regs mem md k wk.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k wk (H1 & H2 & HJ & H3).
split; [exact H1|]. split; [exact H2|]. split; [|exact H3].
apply (cnb_JR_mono R1 R2 H12). exact HJ.
Qed.

(* a padded copy: NULL, or a live RUNTIME block of size + 16 (not a harness block) whose first size bytes are x *)
Definition cnb_copy (D : cnb_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (r : Z) : Prop :=
  r = 0 \/ (In (r, cnb_size D + 16) (ablocks B ly S) /\ ~ In r Hp /\ src_rd W mem r (bi_x D)).
Definition cnb_cblk (D : cnb_in) (r : Z) : list (Z * Z) := if r =? 0 then [] else [(r, cnb_size D + 16)].
Definition cnb_cblks (D : cnb_in) (r1 r2 r3 : Z) : list (Z * Z) := cnb_cblk D r1 ++ cnb_cblk D r2 ++ cnb_cblk D r3.
(* ---- check_no_overread's RUN EVENTS, the pieces the cuts carry (the text's own list ck_cno_evs, PRH_FnCheck.v
   c40cf3fdcd2a :268-281, cut where each segment ends; cnb_ck_cno_evs below is the equation) ---- *)
(* the granted copies' __wrap_malloc (padded's P1 arm; a refused copy makes no event) *)
Definition cnb_cevs (D : cnb_in) (r1 r2 r3 : Z) : list PresetReqAt.hev :=
  map (fun _ => PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)) (cnb_cblks D r1 r2 r3).
(* the three copies granted, the text's C3 *)
Definition cnb_C3 (D : cnb_in) : list PresetReqAt.hev := repeat (PresetReqAt.HMal (cnb_size D + PresetReqAt.FUZZ_PAD)) 3.
(* one reading's events under its grant o (pj_parse's reader events, then pj_free (out) on a refusal) *)
Definition cnb_pe (D : cnb_in) (o : option nat) : list PresetReqAt.hev :=
  PresetReqAt.parse_evs ReaderRes.jr_strtod (bi_x D) (PresetRun.okof o).
(* the reading under grant o RAN OUT (the model's ranout) *)
Definition cnb_ro (D : cnb_in) (o : option nat) : bool := PresetRun.ranout ReaderRes.jr_strtod (bi_x D) o.
(* the readings' events after one / two / three reading positions: a reading is skipped once one ran out *)
Definition cnb_revs2 (D : cnb_in) (o1 o2 : option nat) : list PresetReqAt.hev :=
  cnb_pe D o1 ++ (if cnb_ro D o1 then [] else cnb_pe D o2).
Definition cnb_revs3 (D : cnb_in) (o1 o2 o0 : option nat) : list PresetReqAt.hev :=
  cnb_pe D o1 ++ (if cnb_ro D o1 then [] else cnb_pe D o2 ++ (if cnb_ro D o2 then [] else cnb_pe D o0)).
(* the frees' events (CB8): the accepted trees' pj_free, then the three copies' free *)
Definition cnb_fevs (D : cnb_in) (o1 o2 o0 : option nat) : list PresetReqAt.hev :=
  (if cnb_ro D o1 then []
   else if cnb_ro D o2 then PresetRun.p1_tfree ReaderRes.jr_strtod (bi_x D) o1
   else PresetRun.p1_tfree ReaderRes.jr_strtod (bi_x D) o1 ++ PresetRun.p1_tfree ReaderRes.jr_strtod (bi_x D) o2 ++
        PresetRun.p1_tfree ReaderRes.jr_strtod (bi_x D) o0) ++
  repeat (PresetReqAt.HFr (cnb_size D + PresetReqAt.FUZZ_PAD)) 3.
(* g_ran_out after the readings under these grants: 1 exactly when one ran out *)
Definition cnb_ranz (D : cnb_in) (o1 o2 o0 : option nat) : Z :=
  if ck_cno_ranout ReaderRes.jr_strtod (bi_x D) o1 o2 o0 then 1 else 0.
(* THE EQUATION: the pieces are the text's list *)
Lemma cnb_ck_cno_evs : forall D o1 o2 o0,
  cnb_C3 D ++ cnb_revs3 D o1 o2 o0 ++ cnb_fevs D o1 o2 o0 = ck_cno_evs ReaderRes.jr_strtod (bi_x D) o1 o2 o0.
Proof.
intros D o1 o2 o0. unfold cnb_C3, cnb_revs3, cnb_fevs, cnb_pe, cnb_ro, ck_cno_evs, cnb_size. cbv zeta.
destruct (PresetRun.ranout ReaderRes.jr_strtod (bi_x D) o1);
  [|destruct (PresetRun.ranout ReaderRes.jr_strtod (bi_x D) o2)];
  rewrite ?app_nil_r; repeat rewrite <- app_assoc; reflexivity.
Qed.
(* THE PROGRESS FACT a cut carries for the events E made since entry (the text's post-implication form): the live set
   is the entry's advanced by E, and for ANY run position at the entry state whose next events are E, the position
   after E is a position of this state *)
Definition cnb_prog (D : cnb_in) (E : list PresetReqAt.hev) (S : astate) : Prop :=
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf (bi_S D))) E) /\
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x0 os i H0 hist (bi_S D) -> PRH_Base.prh_run_at sm x0 os i E ->
     exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length E)%nat H0 hist' S).

(* a struct's state: a tree the reading built (its blocks in Lam), or the zero struct (`= empty`, the memset) *)
Definition cnb_st : Type := option (PjTree.jv * list (Z * Z)).
Definition cnb_Dof (st : cnb_st) : list (Z * Z) := match st with Some (_, Dd) => Dd | None => [] end.
Definition cnb_doc (W : world SEGS) (mem : word -> option byte) (Lam : list (Z * Z)) (d : Z) (st : cnb_st) : Prop :=
  match st with
  | Some (t, Dd) => pj_nodeR SEGS (rdW W mem) (prh_lin Lam) d t Dd /\ (PjTree.depth t <= PjGrammar.MAXD)%nat
  | None => pj_zeroR SEGS (rdW W mem) d
  end.
(* a struct's 56 bytes addressable and their shadow hull visible (CB3's unpoison; what parse_noting, same and pj_free
   read of the slot) *)
Definition cnb_open (W : world SEGS) (mem : word -> option byte) (d : Z) : Prop :=
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF d 56 /\ shadow_hull_vis (aview SEGS (w_H W) mem) d 56.
(* WHAT A READING WITH NO RAN-OUT GIVES (the compare's refutation rests on it): while g_ran_out is still 0, a reading
   done is the grammar's reading of x; a reading skipped by the guard has g_ran_out = 1. ran is monotone (prh_oks:
   ran' = ran \/ ran' = 1; the accessors keep it), so the CURRENT ran is the premise. *)
Definition cnb_res (D : cnb_in) (ran rc : Z) (st : cnb_st) : Prop :=
  ran = 0 ->
  match ck_read (bi_x D) with
  | Some t => rc = 0 /\ exists Dd, st = Some (t, Dd)
  | None => rc = -1 /\ st = None
  end.
(* THE STRUCT AGAINST THE MODEL (CnoABatch2's gap, both images): a reading done under grant o left its struct a tree
   exactly when the model accepts the reading at okof o, the tree the model reads; this is what ties CB8's pj_free of
   d_k to cnb_fevs's p1_tfree o_k after a later reading ran out (cnb_res speaks only while ran = 0) *)
Definition cnb_rd (D : cnb_in) (o : option nat) (st : cnb_st) : Prop :=
  match st with
  | Some (t, _) => fst (PjGrammar.jr_run ReaderRes.jr_strtod (bi_x D) (PresetRun.okof o)) = Some t
  | None => fst (PjGrammar.jr_run ReaderRes.jr_strtod (bi_x D) (PresetRun.okof o)) = None
  end.
(* the structs after two / three reading positions: a reading done is cnb_rd at its grant; a skipped one (an earlier
   reading ran out) left its struct zero, so CB8's pj_free of it makes no event, as cnb_fevs leaves out its p1_tfree *)
Definition cnb_rds2 (D : cnb_in) (o1 o2 : option nat) (st1 st2 : cnb_st) : Prop :=
  cnb_rd D o1 st1 /\ (if cnb_ro D o1 then st2 = None else cnb_rd D o2 st2).
Definition cnb_rds3 (D : cnb_in) (o1 o2 o0 : option nat) (st1 st2 st3 : cnb_st) : Prop :=
  cnb_rd D o1 st1 /\
  (if cnb_ro D o1 then st2 = None /\ st3 = None
   else cnb_rd D o2 st2 /\ (if cnb_ro D o2 then st3 = None else cnb_rd D o0 st3)).
(* THE TREE'S FREE ORDER AGAINST THE MODEL (K0-PJF-TIE, CLOSED at the cut: tparse_noting_specX's Some arm,
   PRH_FnCheck.v c40cf3fdcd2a, gives it for the reading's own outcomes; at a tree the reading built the outcomes agree
   with okof o on the reading's calls): for every depth bound n >= depth t, pj_free's order list F of the struct's tree
   is the model's reader-side free list pj_frees at grant o (keyed on the reader's own block sizes; K0-CFHEAD-16: under
   cf_head = HEAD). Carried from the reading to CB8 where cnb_rd is (PRH_PjOrder.pj_foR_frame moves it); CB8's
   pj_free takes it; the A' twin's cn_fo *)
Definition cnb_fo (D : cnb_in) (W : world SEGS) (mem : word -> option byte) (Lam : list (Z * Z)) (o : option nat)
  (d : Z) (st : cnb_st) : Prop :=
  match st with
  | Some (t, Dd) =>
      cf_head = PresetReqAt.HEAD -> forall n, (PjTree.depth t <= n)%nat ->
      exists F, PRH_PjOrder.pj_foR SEGS (rdW W mem) (prh_lin Lam) n d Dd F /\
        map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees ReaderRes.jr_strtod (PresetRun.okof o) (bi_x D)
  | None => True
  end.

(* THE STATE FACTS from CB4 on (structs open), nr readings done: copies, ledger (g_most = bi_most D, g_own_ran_out =
   own, the value the cut holds), counts, room, budget, the three structs and the blocks they hold *)
Definition cnb_mid (D : cnb_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (mem : word -> option byte)
  (Lam : list (Z * Z)) (peak cnt ran own : Z) (nr : nat) (r1 r2 r3 : Z) (st1 st2 st3 : cnb_st) : Prop :=
  cnb_copy D ly S Hp W mem r1 /\ cnb_copy D ly S Hp W mem r2 /\ cnb_copy D ly S Hp W mem r3 /\
  prh_ledger B ly S Hp W mem Lam peak cnt SIZE_MAXZ ran (bi_most D) own /\
  bi_peak D <= peak /\ bi_cnt D <= cnt <= bi_cnt D + Z.of_nat nr * ck_ncalls (bi_x D) /\
  room_live_cf S /\
  blocks_bytes S + Z.of_nat (3 - nr) * PRH_FnPj.LIVE_pj_parse (bi_x D) <= LIVE_MAX /\
  cnb_open W mem (cnb_d1 D) /\ cnb_open W mem (cnb_d2 D) /\ cnb_open W mem (cnb_d3 D) /\
  cnb_doc W mem Lam (cnb_d1 D) st1 /\ cnb_doc W mem Lam (cnb_d2 D) st2 /\ cnb_doc W mem Lam (cnb_d3 D) st3 /\
  Permutation Lam (cnb_Dof st1 ++ cnb_Dof st2 ++ cnb_Dof st3 ++ bi_Lam D) /\
  Permutation (ablocks B ly S)
    (cnb_cblks D r1 r2 r3 ++ ck_hblks (cnb_Dof st1 ++ cnb_Dof st2 ++ cnb_Dof st3) ++ ablocks B (bi_ly D) (bi_S D)) /\
  (forall a k, In (a, k) (cnb_Dof st1 ++ cnb_Dof st2 ++ cnb_Dof st3) ->
     ~ In (a - cf_head, k + cf_head) (ablocks B (bi_ly D) (bi_S D))) /\
  bytes_at W mem (bi_data D) (bi_x D).

(* ---- THE CUTS ---- *)
(* the entry data with the fake frame's position __asan_stack_malloc_3 returned (CB0's exit names it) *)
Definition cnb_set_fpos (D : cnb_in) (p : Z) : cnb_in :=
  mkCnbIn (bi_ly D) (bi_S D) (bi_Hp D) (bi_W D) (bi_regs D) (bi_mem D) (bi_md D) (bi_ch D) (bi_data D) (bi_x D)
    (bi_Lam D) (bi_peak D) (bi_cnt D) (bi_ran D) (bi_most D) p.
(* the state facts before the readings that CB0-CB3 keep: the entry's ledger (g_own_ran_out = own, the value the cut
   holds) and blocks (padded's copies come from the RUNTIME __wrap_malloc), the input, the room *)
Definition cnb_pre_mid (D : cnb_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (own : Z) : Prop :=
  Hp = bi_Hp D /\
  prh_ledger B ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) SIZE_MAXZ (bi_ran D) (bi_most D) own /\
  room_live_cf S /\
  src_rd W mem (bi_data D) (bi_x D) /\
  (0 < cnb_size D -> PRH_FnReader.prhReader_home B ly S Hp (bi_Lam D) (bi_data D) (cnb_size D)).
(* CNB_FRAME (CB0's exit, CB1's start, B' 0x81a94 = entry + 164, `sd s3, 0x30(s1)`): the frame made (the fake frame
   F, its position in D; the real-stack fallback refuted), the thirteen words saved, s2 = the shadow base (the GOT
   word of __asan_shadow_memory_dynamic_address, `ld s2, 0(a1)` at 0x81a50), s7 = size, s8 = data, s3 = s11 = F *)
Definition CNB_FRAME : Z := 164.
Definition cnb_at_frame (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs [(2%bv, cnb_S1 D); (8%bv, cnb_sp0 D); (9%bv, cnb_S1 D); (18%bv, SHADOW_OFF); (19%bv, cnb_F D);
                   (23%bv, cnb_size D); (24%bv, bi_data D); (27%bv, cnb_F D)] /\
  cnb_pre_mid D ly S Hp W mem 0 /\ cnb_prog D [] S /\
  ablocks B ly S = ablocks B (bi_ly D) (bi_S D) /\ blocks_bytes S = blocks_bytes (bi_S D) /\
  PresetHullBudget.hull_budget S (cnb_hev_all (bi_x D)).
Definition cnb_at_frameR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs [(2%bv, cnb_S1 D); (8%bv, cnb_sp0 D); (9%bv, cnb_S1 D); (18%bv, SHADOW_OFF); (19%bv, cnb_F D);
                   (23%bv, cnb_size D); (24%bv, bi_data D); (27%bv, cnb_F D)] /\
  cnb_pre_mid D ly S Hp W mem 0 /\ cnb_prog D [] S /\
  ablocks B ly S = ablocks B (bi_ly D) (bi_S D) /\ blocks_bytes S = blocks_bytes (bi_S D) /\
  PresetHullBudget.hull_budget S (cnb_hev_all (bi_x D)).
Lemma cnb_at_frame_R_wle : forall D fxk ly S Hp W regs mem md k,
  cnb_at_frame D fxk ly S Hp W regs mem md k = cnb_at_frameR (@wle SEGS) D fxk ly S Hp W regs mem md k.
Proof. reflexivity. Qed.
(* CNB_COPY (CB1's exit, CB2's start, B' 0x81b80 = entry + 400, `li a2, 0x31`): F's header words and shadow poison
   stored, s2 = F's shadow, s4 / s5 / s6 = d3 / d2 / d1, s10 = -8, F at s1 + 48 *)
Definition CNB_COPY : Z := 400.
Definition cnb_at_copy (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D)]) /\
  rdword (aview SEGS (w_H W) mem) (cnb_S1 D + 48) = Some (cnb_F D) /\
  cnb_pre_mid D ly S Hp W mem 0 /\ cnb_prog D [] S /\
  ablocks B ly S = ablocks B (bi_ly D) (bi_S D) /\ blocks_bytes S = blocks_bytes (bi_S D) /\
  PresetHullBudget.hull_budget S (cnb_hev_all (bi_x D)).
Definition cnb_at_copyR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D)]) /\
  rdword (aview SEGS (w_H W) mem) (cnb_S1 D + 48) = Some (cnb_F D) /\
  cnb_pre_mid D ly S Hp W mem 0 /\ cnb_prog D [] S /\
  ablocks B ly S = ablocks B (bi_ly D) (bi_S D) /\ blocks_bytes S = blocks_bytes (bi_S D) /\
  PresetHullBudget.hull_budget S (cnb_hev_all (bi_x D)).
Lemma cnb_at_copy_R_wle : forall D fxk ly S Hp W regs mem md k,
  cnb_at_copy D fxk ly S Hp W regs mem md k = cnb_at_copyR (@wle SEGS) D fxk ly S Hp W regs mem md k.
Proof. reflexivity. Qed.
(* CNB_INIT (CB2's exit, CB3's start, B' 0x81bbc = entry + 460, after `sd a0, 0x10(s1)`): the three padded copies made
   (r1 in s9, r2 at s1 + 24, r3 at s1 + 16), own0 the g_own_ran_out value the ledger states at this memory (padded's
   NULL arm stores 1), own0 = 0 says no copy is NULL, own0 <> 0 that the refused copy is dead at a consumer run
   (cnb_cdead); the granted copies' events made (cnb_cevs) *)
Definition CNB_INIT : Z := 460.
Definition cnb_at_init (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 own0 : Z) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\
  cnb_copy D ly S Hp W mem r1 /\ cnb_copy D ly S Hp W mem r2 /\ cnb_copy D ly S Hp W mem r3 /\
  (own0 = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0) /\ (own0 <> 0 -> cnb_cdead D) /\
  cnb_pre_mid D ly S Hp W mem own0 /\ cnb_prog D (cnb_cevs D r1 r2 r3) S /\
  Permutation (ablocks B ly S) (cnb_cblks D r1 r2 r3 ++ ablocks B (bi_ly D) (bi_S D)) /\
  blocks_bytes S + 3 * PRH_FnPj.LIVE_pj_parse (bi_x D) <= LIVE_MAX /\
  PresetHullBudget.hull_budget S (cnb_hrest_copies (bi_x D)).
Definition cnb_at_initR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 own0 : Z) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\
  cnb_copy D ly S Hp W mem r1 /\ cnb_copy D ly S Hp W mem r2 /\ cnb_copy D ly S Hp W mem r3 /\
  (own0 = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0) /\ (own0 <> 0 -> cnb_cdead D) /\
  cnb_pre_mid D ly S Hp W mem own0 /\ cnb_prog D (cnb_cevs D r1 r2 r3) S /\
  Permutation (ablocks B ly S) (cnb_cblks D r1 r2 r3 ++ ablocks B (bi_ly D) (bi_S D)) /\
  blocks_bytes S + 3 * PRH_FnPj.LIVE_pj_parse (bi_x D) <= LIVE_MAX /\
  PresetHullBudget.hull_budget S (cnb_hrest_copies (bi_x D)).
Lemma cnb_at_init_R_wle : forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cnb_at_init D fxk ly S Hp W regs mem md k r1 r2 r3 own0 =
  cnb_at_initR (@wle SEGS) D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Proof. reflexivity. Qed.
(* CNB_READ1 (CB4, after CB3's third memset): s7 = size, s8 = data, s9 = r1; the structs open and zero; own0 is the
   g_own_ran_out value the ledger states at this memory (CB3's memsets keep it: their runtime rule keeps every byte
   outside the destination and its window), and own0 = 0 says no copy is NULL (padded's NULL arm stores 1 there,
   B' 0x83114) *)
Definition cnb_at_read1 (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 own0 : Z) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ (own0 = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0) /\ (own0 <> 0 -> cnb_cdead D) /\
  Hp = bi_Hp D /\
  cnb_prog D (cnb_cevs D r1 r2 r3) S /\
  cnb_mid D ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) (bi_ran D) own0 0 r1 r2 r3 None None None /\
  PresetHullBudget.hull_budget S (cnb_hrest_copies (bi_x D)).
Definition cnb_at_read1R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 own0 : Z) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [(23%bv, cnb_size D); (24%bv, bi_data D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ (own0 = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0) /\ (own0 <> 0 -> cnb_cdead D) /\
  Hp = bi_Hp D /\
  cnb_prog D (cnb_cevs D r1 r2 r3) S /\
  cnb_mid D ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) (bi_ran D) own0 0 r1 r2 r3 None None None /\
  PresetHullBudget.hull_budget S (cnb_hrest_copies (bi_x D)).
Lemma cnb_at_read1_R_wle : forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cnb_at_read1 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 =
  cnb_at_read1R (@wle SEGS) D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Proof. reflexivity. Qed.
(* CNB_READ2 (CB5): reading 1 done (rc1 in a0, its struct st1, its grant o1); every copy non-NULL (own0 = 0 was read).
   g_ran_out is 1 exactly when reading 1 ran out *)
Definition cnb_at_read2R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 : Z) (st1 : cnb_st) (o1 : option nat) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 2 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, rc1); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_pe D o1) S /\ ran = cnb_ranz D o1 None None /\
  cnb_mid D ly S Hp W mem Lam peak cnt ran 0 1 r1 r2 r3 st1 None None /\
  cnb_res D ran rc1 st1 /\ cnb_rd D o1 st1 /\ cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd1 (bi_x D)).
Definition cnb_at_read2 (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 : Z) (st1 : cnb_st) (o1 : option nat) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 2 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, rc1); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_pe D o1) S /\ ran = cnb_ranz D o1 None None /\
  cnb_mid D ly S Hp W mem Lam peak cnt ran 0 1 r1 r2 r3 st1 None None /\
  cnb_res D ran rc1 st1 /\ cnb_rd D o1 st1 /\ cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd1 (bi_x D)).
Lemma cnb_at_read2_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1,
  cnb_at_read2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1 =
  cnb_at_read2R (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1.
Proof. reflexivity. Qed.
(* CNB_READ3 (CB6): reading 2 done or skipped (rc2 in a0; its grant o2, None when skipped), rc1 at s1 + 8 *)
Definition cnb_at_read3R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 rc2 : Z) (st1 st2 : cnb_st) (o1 o2 : option nat) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 4 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, rc2); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 rc1 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs2 D o1 o2) S /\ ran = cnb_ranz D o1 o2 None /\
  cnb_mid D ly S Hp W mem Lam peak cnt ran 0 2 r1 r2 r3 st1 st2 None /\
  cnb_res D ran rc1 st1 /\ cnb_res D ran rc2 st2 /\
  cnb_rds2 D o1 o2 st1 st2 /\ cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd2 (bi_x D)).
Definition cnb_at_read3 (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 rc2 : Z) (st1 st2 : cnb_st) (o1 o2 : option nat) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 4 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, rc2); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 rc1 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs2 D o1 o2) S /\ ran = cnb_ranz D o1 o2 None /\
  cnb_mid D ly S Hp W mem Lam peak cnt ran 0 2 r1 r2 r3 st1 st2 None /\
  cnb_res D ran rc1 st1 /\ cnb_res D ran rc2 st2 /\
  cnb_rds2 D o1 o2 st1 st2 /\ cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd2 (bi_x D)).
Lemma cnb_at_read3_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cnb_at_read3 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2 =
  cnb_at_read3R (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Proof. reflexivity. Qed.
(* CNB_CMP (CB7): all three readings done or skipped: rc3 in s7, rc1 at s1 + 8, rc2 at s1 + 0; the grants o1 o2 o0
   (None for a skipped reading) *)
Definition cnb_at_cmpR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 rc2 rc3 : Z) (st1 st2 st3 : cnb_st) (o1 o2 o0 : option nat) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 6 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (23%bv, rc3); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 rc1 /\ cnb_rcslot D W mem 0 rc2 /\
  r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S /\ ran = cnb_ranz D o1 o2 o0 /\
  cnb_mid D ly S Hp W mem Lam peak cnt ran 0 3 r1 r2 r3 st1 st2 st3 /\
  cnb_res D ran rc1 st1 /\ cnb_res D ran rc2 st2 /\ cnb_res D ran rc3 st3 /\
  cnb_rds3 D o1 o2 o0 st1 st2 st3 /\
  cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\ cnb_fo D W mem Lam o0 (cnb_d3 D) st3 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)).
Definition cnb_at_cmp (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (r1 r2 r3 rc1 rc2 rc3 : Z) (st1 st2 st3 : cnb_st) (o1 o2 o0 : option nat) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 6 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (23%bv, rc3); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 rc1 /\ cnb_rcslot D W mem 0 rc2 /\
  r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S /\ ran = cnb_ranz D o1 o2 o0 /\
  cnb_mid D ly S Hp W mem Lam peak cnt ran 0 3 r1 r2 r3 st1 st2 st3 /\
  cnb_res D ran rc1 st1 /\ cnb_res D ran rc2 st2 /\ cnb_res D ran rc3 st3 /\
  cnb_rds3 D o1 o2 o0 st1 st2 st3 /\
  cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\ cnb_fo D W mem Lam o0 (cnb_d3 D) st3 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)).
Lemma cnb_at_cmp_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1
  o2 o0,
  cnb_at_cmp D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0 =
  cnb_at_cmpR (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0.
Proof. reflexivity. Qed.
(* CNB_FREE (CB8): s8 = r, s9 = r1; slots 24 r2, 16 r3. THE r FACT over ownl, the g_own_ran_out value the ledger
   states at this memory. nr <= 3 bounds the count (CnoB102f's ask: cnb_mid's `3 - nr` is nat subtraction). When no
   copy was refused (ownl = 0, the only arm the text's position clause covers), the readings' grants, the events made
   since entry and the trees' free order; when one was (ownl <> 0), the refused copy dead at a consumer run *)
Definition cnb_at_freeR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (nr : nat) (r1 r2 r3 r ownl : Z) (st1 st2 st3 : cnb_st) (o1 o2 o0 : option nat) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 6 /\
  cnb_regsat regs (cnb_core D ++ [(24%bv, r); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\
  cnb_mid D ly S Hp W mem Lam peak cnt ran ownl nr r1 r2 r3 st1 st2 st3 /\ (nr <= 3)%nat /\
  ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0 /\ nr = 3%nat)) /\
  (ownl = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
     cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S /\ ran = cnb_ranz D o1 o2 o0 /\
     cnb_rds3 D o1 o2 o0 st1 st2 st3 /\
     cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\
     cnb_fo D W mem Lam o0 (cnb_d3 D) st3) /\
  (* a refused copy (ownl <> 0): the guard at read1 went straight here, so only the granted copies' events were made
     and no struct was read (the class-24 bound every pj_free asks comes from this live set; CnoABatch2 / CnoBF8) *)
  (ownl <> 0 -> cnb_prog D (cnb_cevs D r1 r2 r3) S /\ st1 = None /\ st2 = None /\ st3 = None /\ cnb_cdead D) /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)).
Definition cnb_at_free (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt ran : Z)
  (nr : nat) (r1 r2 r3 r ownl : Z) (st1 st2 st3 : cnb_st) (o1 o2 o0 : option nat) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 6 /\
  cnb_regsat regs (cnb_core D ++ [(24%bv, r); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\
  cnb_mid D ly S Hp W mem Lam peak cnt ran ownl nr r1 r2 r3 st1 st2 st3 /\ (nr <= 3)%nat /\
  ((r = 1 /\ (ownl <> 0 \/ ran = 1)) \/ (r = 0 /\ ownl = 0 /\ ran = 0 /\ nr = 3%nat)) /\
  (ownl = 0 -> r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
     cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs3 D o1 o2 o0) S /\ ran = cnb_ranz D o1 o2 o0 /\
     cnb_rds3 D o1 o2 o0 st1 st2 st3 /\
     cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\
     cnb_fo D W mem Lam o0 (cnb_d3 D) st3) /\
  (* a refused copy (ownl <> 0): the guard at read1 went straight here, so only the granted copies' events were made
     and no struct was read (the class-24 bound every pj_free asks comes from this live set; CnoABatch2 / CnoBF8) *)
  (ownl <> 0 -> cnb_prog D (cnb_cevs D r1 r2 r3) S /\ st1 = None /\ st2 = None /\ st3 = None /\ cnb_cdead D) /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd0 (bi_x D)).
Lemma cnb_at_free_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1
  o2 o0,
  cnb_at_free D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 =
  cnb_at_freeR (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0.
Proof. reflexivity. Qed.

(* the three parse_noting call states (at the `jal parse_noting`, the arguments set; the PN step lemmas take the jal),
   each the read cut's facts there: the reading is made only when the guard found g_ran_out = 0 and every copy
   non-NULL *)
Definition cnb_at_pn1R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 : Z) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, r1); (11%bv, cnb_size D);
                                  (12%bv, cnb_d1 D); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\ Hp = bi_Hp D /\
  cnb_prog D (cnb_cevs D r1 r2 r3) S /\
  cnb_mid D ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) 0 0 0 r1 r2 r3 None None None /\
  PresetHullBudget.hull_budget S (cnb_hrest_copies (bi_x D)).
Definition cnb_at_pn1 (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (r1 r2 r3 : Z) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 0 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, r1); (11%bv, cnb_size D);
                                  (12%bv, cnb_d1 D); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\ Hp = bi_Hp D /\
  cnb_prog D (cnb_cevs D r1 r2 r3) S /\
  cnb_mid D ly S Hp W mem (bi_Lam D) (bi_peak D) (bi_cnt D) 0 0 0 r1 r2 r3 None None None /\
  PresetHullBudget.hull_budget S (cnb_hrest_copies (bi_x D)).
Lemma cnb_at_pn1_R_wle : forall D fxk ly S Hp W regs mem md k r1 r2 r3,
  cnb_at_pn1 D fxk ly S Hp W regs mem md k r1 r2 r3 =
  cnb_at_pn1R (@wle SEGS) D fxk ly S Hp W regs mem md k r1 r2 r3.
Proof. reflexivity. Qed.
Definition cnb_at_pn2R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 rc1 : Z) (st1 : cnb_st) (o1 : option nat) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 2 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, r2); (11%bv, cnb_size D);
                                  (12%bv, cnb_d2 D); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 rc1 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_pe D o1) S /\ cnb_ro D o1 = false /\
  cnb_mid D ly S Hp W mem Lam peak cnt 0 0 1 r1 r2 r3 st1 None None /\ cnb_res D 0 rc1 st1 /\ cnb_rd D o1 st1 /\
  cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd1 (bi_x D)).
Definition cnb_at_pn2 (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 rc1 : Z) (st1 : cnb_st) (o1 : option nat) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 2 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, r2); (11%bv, cnb_size D);
                                  (12%bv, cnb_d2 D); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 rc1 /\ r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_pe D o1) S /\ cnb_ro D o1 = false /\
  cnb_mid D ly S Hp W mem Lam peak cnt 0 0 1 r1 r2 r3 st1 None None /\ cnb_res D 0 rc1 st1 /\ cnb_rd D o1 st1 /\
  cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd1 (bi_x D)).
Lemma cnb_at_pn2_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  cnb_at_pn2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 =
  cnb_at_pn2R (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1.
Proof. reflexivity. Qed.
Definition cnb_at_pn3R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 rc1 rc2 : Z) (st1 st2 : cnb_st) (o1 o2 : option nat) : Prop :=
  cnb_baseR R D fxk ly S Hp W regs mem md k 4 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, r3); (11%bv, cnb_size D);
                                  (12%bv, cnb_d3 D); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 rc1 /\ cnb_rcslot D W mem 0 rc2 /\
  r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs2 D o1 o2) S /\ cnb_ro D o1 = false /\ cnb_ro D o2 = false /\
  cnb_mid D ly S Hp W mem Lam peak cnt 0 0 2 r1 r2 r3 st1 st2 None /\ cnb_res D 0 rc1 st1 /\ cnb_res D 0 rc2 st2 /\
  cnb_rd D o1 st1 /\ cnb_rd D o2 st2 /\ cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd2 (bi_x D)).
Definition cnb_at_pn3 (D : cnb_in) (fxk : YK11.FPState) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (Lam : list (Z * Z)) (peak cnt : Z)
  (r1 r2 r3 rc1 rc2 : Z) (st1 st2 : cnb_st) (o1 o2 : option nat) : Prop :=
  cnb_base D fxk ly S Hp W regs mem md k 4 /\
  cnb_regsat regs (cnb_core D ++ [cnb_s8; (10%bv, r3); (11%bv, cnb_size D);
                                  (12%bv, cnb_d3 D); (23%bv, cnb_size D); (25%bv, r1)]) /\
  cnb_slots D W mem r2 r3 /\ cnb_rcslot D W mem 8 rc1 /\ cnb_rcslot D W mem 0 rc2 /\
  r1 <> 0 /\ r2 <> 0 /\ r3 <> 0 /\
  cnb_prog D (cnb_cevs D r1 r2 r3 ++ cnb_revs2 D o1 o2) S /\ cnb_ro D o1 = false /\ cnb_ro D o2 = false /\
  cnb_mid D ly S Hp W mem Lam peak cnt 0 0 2 r1 r2 r3 st1 st2 None /\ cnb_res D 0 rc1 st1 /\ cnb_res D 0 rc2 st2 /\
  cnb_rd D o1 st1 /\ cnb_rd D o2 st2 /\ cnb_fo D W mem Lam o1 (cnb_d1 D) st1 /\ cnb_fo D W mem Lam o2 (cnb_d2 D) st2 /\
  PresetHullBudget.hull_budget S (cnb_hrest_rd2 (bi_x D)).
Lemma cnb_at_pn3_R_wle : forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cnb_at_pn3 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2 =
  cnb_at_pn3R (@wle SEGS) D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Proof. reflexivity. Qed.

(* ---- THE EXITS (the brief's FORWARD form, the internal file lane-102.md :29-30): a segment lemma reads
     forall P, srr_inv_laws SEGS P -> .. -> cnb_pre CTX0 D -> cnb_at_X D fxk .. -> P mem ->
     SRr SEGS W (cnb_cfg fxk (cnb_pc OFF_X) regs mem md) (fun W' c' => cnb_ex_Y D W' c' /\ P (ms_mem (cfg_ms c')))
   with cnb_ex_Y the cut it reaches (a disjunction when it has several exits). The float state at an exit is
   existential (parse_noting's post is apost_base_xF); cnb_base carries frm_zero / fregs_kept_x against the entry's.
   The segments compose by SRr_bind. ---- *)
(* CB0's exit: the cut at the frame, for the entry data with the position __asan_stack_malloc_3 returned (CB0 is
   stated for D and reaches cnb_set_fpos D p; cnb_pre does not read bi_fpos) *)
Definition cnb_ex_frame (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists p fxk ly S Hp regs mem md k,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_FRAME) regs mem md /\ cnb_at_frame (cnb_set_fpos D p) fxk ly S Hp W regs mem md k.
Definition cnb_ex_frameR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists p fxk ly S Hp regs mem md k,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_FRAME) regs mem md /\ cnb_at_frameR R (cnb_set_fpos D p) fxk ly S Hp W regs mem md k.
Lemma cnb_ex_frame_R_wle : forall D,
  cnb_ex_frame D = cnb_ex_frameR (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_copyR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_COPY) regs mem md /\ cnb_at_copyR R D fxk ly S Hp W regs mem md k.
Definition cnb_ex_copy (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_COPY) regs mem md /\ cnb_at_copy D fxk ly S Hp W regs mem md k.
Lemma cnb_ex_copy_R_wle : forall D,
  cnb_ex_copy D = cnb_ex_copyR (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_initR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3 own0,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_INIT) regs mem md /\ cnb_at_initR R D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Definition cnb_ex_init (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3 own0,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_INIT) regs mem md /\ cnb_at_init D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Lemma cnb_ex_init_R_wle : forall D,
  cnb_ex_init D = cnb_ex_initR (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_read1R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3 own0,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_READ1) regs mem md /\ cnb_at_read1R R D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Definition cnb_ex_read1 (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3 own0,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_READ1) regs mem md /\ cnb_at_read1 D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Lemma cnb_ex_read1_R_wle : forall D,
  cnb_ex_read1 D = cnb_ex_read1R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_pn1R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_PN1) regs mem md /\ cnb_at_pn1R R D fxk ly S Hp W regs mem md k r1 r2 r3.
Definition cnb_ex_pn1 (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k r1 r2 r3,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_PN1) regs mem md /\ cnb_at_pn1 D fxk ly S Hp W regs mem md k r1 r2 r3.
Lemma cnb_ex_pn1_R_wle : forall D,
  cnb_ex_pn1 D = cnb_ex_pn1R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_read2R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_READ2) regs mem md /\
  cnb_at_read2R R D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1.
Definition cnb_ex_read2 (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_READ2) regs mem md /\
  cnb_at_read2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1.
Lemma cnb_ex_read2_R_wle : forall D,
  cnb_ex_read2 D = cnb_ex_read2R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_pn2R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_PN2) regs mem md /\
  cnb_at_pn2R R D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1.
Definition cnb_ex_pn2 (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_PN2) regs mem md /\
  cnb_at_pn2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1.
Lemma cnb_ex_pn2_R_wle : forall D,
  cnb_ex_pn2 D = cnb_ex_pn2R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_read3R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_READ3) regs mem md /\
  cnb_at_read3R R D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Definition cnb_ex_read3 (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_READ3) regs mem md /\
  cnb_at_read3 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Lemma cnb_ex_read3_R_wle : forall D,
  cnb_ex_read3 D = cnb_ex_read3R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_pn3R (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_PN3) regs mem md /\
  cnb_at_pn3R R D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Definition cnb_ex_pn3 (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_PN3) regs mem md /\
  cnb_at_pn3 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Lemma cnb_ex_pn3_R_wle : forall D,
  cnb_ex_pn3 D = cnb_ex_pn3R (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_cmpR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_CMP) regs mem md /\
  cnb_at_cmpR R D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0.
Definition cnb_ex_cmp (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_CMP) regs mem md /\
  cnb_at_cmp D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0.
Lemma cnb_ex_cmp_R_wle : forall D,
  cnb_ex_cmp D = cnb_ex_cmpR (@wle SEGS) D.
Proof. reflexivity. Qed.
Definition cnb_ex_freeR (R : world SEGS -> world SEGS -> Prop)
  (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_FREE) regs mem md /\
  cnb_at_freeR R D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0.
Definition cnb_ex_free (D : cnb_in) : world SEGS -> config -> Prop := fun W c =>
  exists fxk ly S Hp regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  c = @cnb_cfg SEGS fxk (cnb_pc CNB_FREE) regs mem md /\
  cnb_at_free D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0.
Lemma cnb_ex_free_R_wle : forall D,
  cnb_ex_free D = cnb_ex_freeR (@wle SEGS) D.
Proof. reflexivity. Qed.


Lemma cnb_at_frameR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k,
  cnb_at_frameR R1 D fxk ly S Hp W regs mem md k -> cnb_at_frameR R2 D fxk ly S Hp W regs mem md k.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_copyR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k,
  cnb_at_copyR R1 D fxk ly S Hp W regs mem md k -> cnb_at_copyR R2 D fxk ly S Hp W regs mem md k.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_initR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cnb_at_initR R1 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 ->
  cnb_at_initR R2 D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_read1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3 own0,
  cnb_at_read1R R1 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 ->
  cnb_at_read1R R2 D fxk ly S Hp W regs mem md k r1 r2 r3 own0.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 r2 r3 own0 (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_read2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1,
  cnb_at_read2R R1 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1 ->
  cnb_at_read2R R2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 st1 o1 (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_read3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cnb_at_read3R R1 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2 ->
  cnb_at_read3R R2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 st1 st2 o1 o2
  (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_cmpR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0,
  cnb_at_cmpR R1 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0 ->
  cnb_at_cmpR R2 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt ran r1 r2 r3 rc1 rc2 rc3 st1 st2 st3 o1 o2 o0
  (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_freeR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0,
  cnb_at_freeR R1 D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0 ->
  cnb_at_freeR R2 D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt ran nr r1 r2 r3 r ownl st1 st2 st3 o1 o2 o0
  (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_pn1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k r1 r2 r3,
  cnb_at_pn1R R1 D fxk ly S Hp W regs mem md k r1 r2 r3 -> cnb_at_pn1R R2 D fxk ly S Hp W regs mem md k r1 r2 r3.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k r1 r2 r3 (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_pn2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1,
  cnb_at_pn2R R1 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 ->
  cnb_at_pn2R R2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 st1 o1 (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_at_pn3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2,
  cnb_at_pn3R R1 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2 ->
  cnb_at_pn3R R2 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2.
Proof.
intros R1 R2 H12 D fxk ly S Hp W regs mem md k Lam peak cnt r1 r2 r3 rc1 rc2 st1 st2 o1 o2
  (HB & HR). split; [|exact HR].
apply (cnb_baseR_mono R1 R2 H12). exact HB.
Qed.
Lemma cnb_ex_frameR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_frameR R1 D W c -> cnb_ex_frameR R2 D W c.
Proof.
intros R1 R2 H12 D W c (p & fxk & ly & S & Hp & regs & mem & md & k & E & HA).
exists p, fxk, ly, S, Hp, regs, mem, md, k. split; [exact E|].
apply (cnb_at_frameR_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_copyR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_copyR R1 D W c -> cnb_ex_copyR R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k. split; [exact E|].
apply (cnb_at_copyR_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_initR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_initR R1 D W c -> cnb_ex_initR R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & own0 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, r2, r3, own0. split; [exact E|].
apply (cnb_at_initR_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_read1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_read1R R1 D W c -> cnb_ex_read1R R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & own0 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, r2, r3, own0. split; [exact E|].
apply (cnb_at_read1R_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_pn1R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_pn1R R1 D W c -> cnb_ex_pn1R R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly & S & Hp & regs & mem & md & k & r1 & r2 & r3 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, r1, r2, r3. split; [exact E|].
apply (cnb_at_pn1R_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_read2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_read2R R1 D W c -> cnb_ex_read2R R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & rc1 & st1 & o1 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, r1, r2, r3, rc1, st1, o1. split; [exact E|].
apply (cnb_at_read2R_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_pn2R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_pn2R R1 D W c -> cnb_ex_pn2R R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & r1 & r2 & r3 & rc1 & st1 & o1 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, r1, r2, r3, rc1, st1, o1. split; [exact E|].
apply (cnb_at_pn2R_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_read3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_read3R R1 D W c -> cnb_ex_read3R R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & rc1 & rc2 & st1 & st2 & o1 &
   o2 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, r1, r2, r3, rc1, rc2, st1, st2, o1,
  o2. split; [exact E|].
apply (cnb_at_read3R_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_pn3R_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_pn3R R1 D W c -> cnb_ex_pn3R R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & r1 & r2 & r3 & rc1 & rc2 & st1 & st2 & o1 & o2 & E &
   HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, r1, r2, r3, rc1, rc2, st1, st2, o1, o2. split; [exact E|].
apply (cnb_at_pn3R_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_cmpR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_cmpR R1 D W c -> cnb_ex_cmpR R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & r1 & r2 & r3 & rc1 & rc2 & rc3 & st1 & st2 &
   st3 & o1 & o2 & o0 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, r1, r2, r3, rc1, rc2, rc3, st1, st2, st3, o1, o2,
  o0. split; [exact E|].
apply (cnb_at_cmpR_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_ex_freeR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_freeR R1 D W c -> cnb_ex_freeR R2 D W c.
Proof.
intros R1 R2 H12 D W c
  (fxk & ly & S & Hp & regs & mem & md & k & Lam & peak & cnt & ran & nr & r1 & r2 & r3 & r & ownl & st1 & st2 &
   st3 & o1 & o2 & o0 & E & HA).
exists fxk, ly, S, Hp, regs, mem, md, k, Lam, peak, cnt, ran, nr, r1, r2, r3, r, ownl, st1, st2, st3, o1, o2,
  o0. split; [exact E|].
apply (cnb_at_freeR_mono R1 R2 H12). exact HA.
Qed.
Lemma cnb_postR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_postR R1 D W c -> cnb_postR R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly' & S' & Hp' & regs' & mem' & md' & k & WS & E & Hz & Hfk & HP & HJ & Hr & HQ).
exists fxk, ly', S', Hp', regs', mem', md', k, WS.
split; [exact E|]. split; [exact Hz|]. split; [exact Hfk|]. split; [exact HP|]. split; [|split; [exact Hr | exact HQ]].
eapply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx R1 R2 H12). exact HJ.
Qed.
Lemma cnb_ex_retR_mono : forall (R1 R2 : world SEGS -> world SEGS -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall D W c, cnb_ex_retR R1 D W c -> cnb_ex_retR R2 D W c.
Proof.
intros R1 R2 H12 D W c (fxk & ly' & S' & Hp' & regs' & mem' & md' & k & WS & E & Hz & Hfk & HP & HJ & Hr & HQ).
exists fxk, ly', S', Hp', regs', mem', md', k, WS.
split; [exact E|]. split; [exact Hz|]. split; [exact Hfk|]. split; [exact HP|]. split; [|split; [exact Hr | exact HQ]].
eapply (ajournal_xwR_mono (SK := SK) SEGS B prh_pst ARx R1 R2 H12). exact HJ.
Qed.

End cnb.
