(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the call chain `gch` taken from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v's `rt_ch`, with fuzz_grant's module paths, for the phases of libreac/fuzz_grant's entry function LLVMFuzzerTestOneInput; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryDefs.v, with its module paths changed; 265 of its 330 lines of code are new or changed and 295 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapEntryDefs.v, with its module paths and module names changed; 394 of its 426 lines of code are new or changed and 298 lines of the source are left out. *)
(* lib/B twin of lib/A/Prog/PcapEntryPhases.v: the phase predicates of fuzz_pcap's entry walk (LLVMFuzzerTestOneInput,
   0x80818, asan-ubsan build of libreac v1.9.0): one predicate per cut pc of lib/B/Prog/PcapEntryDefs.v, in the shape
   PcapEntryDefs.pe_from takes them. The cuts are lib/A's wherever the code has the same shape, with the same text
   over this image's registers and slots; this image calls rd32 out of line (six sites), so a cut is ADDED at each
   rd32 return that falls between two of lib/A's cuts: GI_KM (PP_KM, the magic), GI_KRI (PP_KRI, incl in the skip
   loop), GI_KO (PP_KO, orig_len), GI_KT1 / GI_KT2 (PP_KT1 / PP_KT2, the timestamp's two words), GI_KWL (PP_KWL, len
   in the end-of-walk loop). A walk lane proves `pe_from SK B MT KS POST GI_next -> pe_from SK B MT KS POST
   GI_self`; GI_ret (after the side-stack frame is given back) is stated for pe_from_ret, and GI_abort is False.

   Every number is read from the pin fuzz_pcap.asan-ubsan (sha256 9e66f771f22af67a..., image root: the
   original v1.9.0 pins; capstone disassembly of the unstripped twin). The register and spill-slot set stated at
   each cut is the set a liveness pass over the function's 530 instructions finds live there (calls clobber the
   caller-saved registers and use their argument registers; spill slots are the words at s1+off; the same pass over
   the asan function gives lib/A's table), so a cut states what the code after it reads, and nothing it does not,
   besides lib/A's convention slots (PS_F0, and pslots as a whole from PP_KD on). Register numbers: a0 10, a1 11,
   a3 13, s2 18, s3 19, s4 20, s5 21, s6 22, s7 23, s8 24, s9 25, s10 26, s11 27 (sp 2, s0 8, s1 9, gp, tp are
   pe_body's).

   Names. F0 = pF cx fp (the frame on the side stack), SH = pSH cx fp (its shadow), PS = F0 + 32 (struct
   pcap_source ps: f at +0, swapped at +8, last_orig_len at +12, last_vlan_tagged at +16, last_vlan_id at +20),
   TS = F0 + 96 (uint64_t ts), b = the copy of the file (malloc 0x809b4; the harness's `file`), h = the FILE of the
   open stream (inside pcap_source_open), buf = the record buffer (malloc 0x80ac8), hi8 = the listing's auipc value 8
   (0x5d39a8 on the pin; g_file_len = hi8 + 0x498). The input: d = its first byte (0 if empty), F = the rest (the
   file, g_file_len bytes), cap = 8 d, bn = max cap 1; the reader's model is lib/Prog/pcap_source_struct_next.v
   (kind, psn_q, res_of, pos_of, hw, incl, orig, rec_len, rec_ts, rec_bytes) and lib/Prog/Slot/PWalkDef.v (skips).

   cut      pc       live registers                                                 live spill slots (s1+)
   K1       0x809b8  a0=b s3=&g_file s5=src s6=|F| s7=F0 s8=hi8 s9=SH s10=F0         0x18 0x48
   K2       0x80a10  a0=r s2=b s4=PS s6=24 s7=F0 s8=hi8 s9=SH s10=F0                 0x18 0x48
   KM       0x80a3c  a0=magic s2=b s3=r s4=PS s5=-1 s6=24 s8=hi8                     0x10 0x18 0x20 0x28 0x48
   K3       0x80acc  a0=buf s2=b s4=PS s8=hi8                                        0x10 0x18 0x20 0x28 0x48 0x78
   KD       0x80b04  a0=n s2=b s3=buf s4=PS s8=hi8                                   0x10..0x28 0x48 0x58 0x60 0x78
   K4       0x80b40  a3=first(i>0) s2=b s4=PS s5=-8 s7=~b s8=hi8 s10=p               0x10..0x48 0x58..0x78 (step 8)
   KR       0x80b90  s2=b s4=PS s5=-8 s6=e+16 s7=~b s8=hi8 s10=e                     0x10..0x78 (step 8)
   KRI      0x80ba8  a0=incl(e) s2 s3=b+e s4 s5 s6=e+16 s7 s8 s10=e                  0x10..0x78 (step 8)
   KO       0x80bfc  a0=orig(Q) s2 s3=b+Q s4 s5 s6=ps.last_orig_len s7 s8 s9=incl s10=Q s11=incl   0x10..0x78
   KT1      0x80d5c  a0=sec(Q) s2 s3=b+Q s4 s5 s6=ts s7 s8 s10=Q s11=incl            0x10..0x68 0x78
   KT2      0x80d80  a0=usec(Q) s2 s4 s5 s6=ts s7 s8 s9=10^6 sec s10=Q s11=incl      0x10..0x68 0x78
   KL2      0x80dbc  a0=n s2=b s4=PS s5=-8 s7=~b s8=hi8 s10=p                        0x10..0x68 0x78
   K5       0x80e0c  a0=first s2=b s4=PS s8=hi8 s10=p                                0x10..0x28 0x60 0x70 0x78
   KW       0x80fb0  a0=|F| s2=b s3=1 s4=PS s5=first s7=-9 s8=hi8 s10=e              0x10..0x28 0x60 0x70 0x78
   KWL      0x80fe4  a0=len(e) s2 s3 s4 s5 s6=e+16 s7 s8 s9=-1                       0x10..0x28 0x60 0x70 0x78
   K6       0x80e38  s2=b s4=PS s5=first                                             0x10 0x20 0x28 0x60 0x78
   K7, K8   0x80e50, 0x80e68  a0 s2 s4 s5                                            0x10 0x20 0x28 0x60 0x78
   K9       0x80e74  s2 s4                                                           0x10 0x20 0x28 0x60 0x78
   K10      0x80e88  a0=-1 s2                                                        0x10 0x20 0x28 0x60
   K11      0x80e98  s2                                                              0x10 0x20 0x28
   K12      0x80ea0  -                                                               0x10 0x20 0x28
   K12r     0x80eac  s9                                                              0x10 0x20
   leave    0x80ec4  s7=F0 s9=SH s10=F0                                              -
   ret      0x80fa4  a0=0 ra sp (and every callee-saved register restored)

   The input block. The copy b (|F| bytes) is in the cut's block list at every cut from PP_K1 to PP_K11 (it is
   freed at 0x80e9c, or at 0x80a90 on the refused path), with g_file = b and g_file_len = |F| from PP_K2 to PP_K6
   (g_file = src at PP_K1; nothing reads the globals after 0x80e4c, so GI_K7 .. GI_K9 do not state them); GI_KR /
   GI_KRI carry e + 16 <= |F| and GI_KW carries e <= |F|, so a walk decides the guards file + e (0x80b90, 0x80b98,
   0x80fc0, 0x80fd4) and each rd32 site's live-block premise against the block from the invariant and AR's block law.

   What a phase does NOT carry, because the walk derives it from pe_base and pe_from's journal: the meta region
   (PSourceMeta.asrc_meta_inv_kept, with asource_img_laws as a Section hypothesis of the walk), the read-only data
   (PcapBase.arodata_ok_journalP), the stack window and its presence (the inner ajournal's own clauses), the shadow base cell
   and the use-after-return flag (AR), and the header, the saved registers and the input bytes (pe_body).

   What each callee's statement must supply at its sites, for these phases to be met (state the post over these
   PSource predicates and these caller-visible fields of ps; the stack slots above the callee's window, the
   frame's other bytes, the copy's bytes, the globals and the callee-saved registers are kept by the journal or
   by aregs_preserved): lib/A's list, at this image's call sites -
   - pcap_source_open (0x80a0c, 0x80e4c; caller-journal form): a0 = 0 exactly when pcap_good F, and then ps.f = h,
     ps.swapped = pcap_sw F, asource_at KS h b (map unsigned F) 24, the blocks gain (h, 1304), +1 event, meter
     <= mo_malloc 1304; else a0 = -1, ps.f = 0, asource_none KS, blocks unchanged, at most +3 events, meter
     <= mo_malloc 1304 + 2 mo_free. In both arms: frames unchanged and m_fds / m_fs unchanged.
   - pcap_source_next (0x80b00 and 0x80db8 with ts = TS, 0x80e64 and 0x80e84 with ts = NULL): from asource_at KS h b
     C p with ps.f = h and ps.swapped = pcap_sw F: a0 = res_of (psn_q p), asource_at KS h b C (pos_of (psn_q p)),
     ps.f and ps.swapped kept, and for a fit record ps.last_orig_len = orig, ps.last_vlan_tagged / ps.last_vlan_id as
     tagged / rec_vid, the record bytes rec_bytes at buf, and *ts = rec_ts when ts <> NULL; ts untouched otherwise;
     with ps.f = 0: a0 = -1 and nothing changed; always 0 events, meter 0, blocks and frames unchanged.
   - pcap_source_close (0x80e34, 0x80e70): ps.f = 0, asource_none KS, the copy's bytes kept, the blocks lose
     (h, 1304), +2 events, frames unchanged, meter <= 2 mo_free and m_fds / m_fs unchanged.
   - rd32 (0x80a38, 0x80ba4, 0x80bf8, 0x80d58, 0x80d7c, 0x80fe0; lib/B/Prog/Rd32.v trd32_specX): a0 = the four bytes
     at p, little-endian when a1 = 0 and swapped otherwise (= hw (p_sw cx) F q j at p = b + q + j), sign-extended
     from bit 31; the journal at the same layout and state (0 events, meter 0, blocks and frames unchanged), every
     byte outside its 16-byte frame kept. Each site's argument and block bound: PcapEntryDefs.v, "The rd32 sites".
   The harness's own calls take cgif's runtime rules as Section hypotheses: amalloc04_rule (0x809b4, 0x80ac8;
   4096 <= res closes both NULL tests 0x809c0 and 0x80ad0), afree04_rule (0x80a90, 0x80e94, 0x80e9c),
   aintrin_realizes OCpy / OSet (0x809d8, 0x809fc), astack_malloc_realizes 1 (0x80888), abcmp_realizes
   (0x80c94, 0x80cc4, 0x80d40), astack_free_law (the flag store 0x80f1c). The harness writes g_file and
   g_file_len (0x80990, 0x809ac, 0x809dc), which are NOT owned-static (a Theorem Labs lane decision 22:36Z): the call's journal is
   W_journal.v's ajournal_gx SEGS B pe_G 0 [] (pe_from, pe_from_ret, pe_post), its runs use W_journal's paj_run_x /
   paj_run_to_x with the write obligation awr_ok_x (the global stores are bytes of pe_G), and pe_base carries
   gx_ok SEGS B pe_G. A runtime entry is lifted by lib/B/Prog/PaGxSites.v aj_gx_entry_at or, for the allocator rules,
   by opening the journal, applying the rule to its inner donor journal and closing it with ajournal_gx_pack; a program
   callee whose statement takes a FRESH donor journal from the call state (libreac_fuzz_fopen) by
   PaJournalFs.ajournal_gx_callee, and one in the CALLER-JOURNAL form (pcap_source_open / _next / _close, and rd32:
   lib/B/Prog/Rd32.v trd32_specX) by opening the gx journal, passing its inner donor journal to the callee and
   repacking with ajournal_gx_pack (lib/A/Prog/PcapHarnessTail.v's gx_open / gx_pack0). m_fds / m_fs stay exact across the
   harness's own allocator and intrinsic calls
   by lib/A/Prog/PaJournalFs.v (amalloc04_sub_fs, afree04_sub_fs, afree_null04_sub_fs, same_but_materialized_fs; any
   other callee whose journal footprint is sink-closed: ajournal_sub_closed_fs). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapEntry PcapEntryDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YI04 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapList PcapAddr PcapPa.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journalG.
(* The plain functional model of the reader, required without Import (its own imports include lib/Lib). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog Require pcap_source_struct pcap_source_struct_next.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot Require PWalkDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Module PST := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct.
Module PSN := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.pcap_source_struct_next.
Module PWD := OSSVerify.Proofs.libreac.fuzz_pcap.lib.Prog.Slot.PWalkDef.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Local Notation rd W3 ms3 := (mrestrict (w_H W3) (ms_mem ms3)).

(* ---- the input, as the harness splits it (0x80968 lbu, 0x8096c, 0x80970, 0x8097c) ---- *)
Definition p_d (cx : ecx) : Z := match c_pl cx with [] => 0 | d :: _ => bv_unsigned d end.
Definition p_F (cx : ecx) : list byte := tl (c_pl cx).
Definition p_nF (cx : ecx) : Z := Z.of_nat (length (p_F cx)).
Definition p_cap (cx : ecx) : Z := 8 * p_d cx.                (* slli a0,a1,3  0x80ab8 *)
Definition p_bn (cx : ecx) : Z := Z.max (p_cap cx) 1.         (* addi a0,zero,1 0x80ac4 *)
Definition p_C (cx : ecx) : list Z := map (fun x : byte => bv_unsigned x) (p_F cx).
(* g_file's first value (0x80990): the byte after d, or the caller's pointer for an empty input. *)
Definition p_src (cx : ecx) : Z := match c_pl cx with [] => c_p cx | _ :: _ => c_p cx + 1 end.
Definition p_swz (cx : ecx) : Z := PST.pcap_sw (p_F cx).
Definition p_sw (cx : ecx) : bool := p_swz cx =? 1.
Definition p_good (cx : ecx) : bool := PST.pcap_good (p_F cx).
(* NEW: the words the harness's rd32 calls read from the file: the magic (0x80a38, rd32(file, 0), little-endian), and
   the 32-bit word at q + j in the file's own byte order (rd32(file + q + j, ps.swapped)). *)
Definition p_magic (cx : ecx) : Z := PST.pcap_magic (p_F cx).
Definition p_hw (cx : ecx) (q j : Z) : Z := PSN.hw (p_sw cx) (p_F cx) q j.

(* ---- the reader's model at a position ---- *)
Definition p_q (cx : ecx) (p : Z) : Z := PSN.psn_q (p_sw cx) (p_F cx) (p_cap cx) p.
Definition p_kind (cx : ecx) (Q : Z) : PSN.pkind := PSN.kind (p_sw cx) (p_F cx) (p_cap cx) Q.
Definition p_res (cx : ecx) (Q : Z) : Z := PSN.res_of (p_sw cx) (p_F cx) (p_cap cx) Q.
Definition p_pos (cx : ecx) (Q : Z) : Z := PSN.pos_of (p_sw cx) (p_F cx) (p_cap cx) Q.
Definition p_skips (cx : ecx) (q Q : Z) : Prop := PWD.skips (p_sw cx) (p_F cx) (p_cap cx) q Q.
(* The reader's first answer (from position 24), which the harness keeps as `first`. *)
Definition p_first (cx : ecx) : Z := p_res cx (p_q cx 24).

Lemma p_d_range : forall cx, 0 <= p_d cx < 256.
Proof.
  intros cx. unfold p_d. destruct (c_pl cx) as [|d l]; [lia|].
  pose proof (bv_unsigned_in_range 8 d) as R. unfold bv_modulus in R. exact R.
Qed.

Lemma p_sizes : forall cx, 0 <= p_nF cx <= c_n cx /\ 0 <= p_cap cx <= 2040 /\ 1 <= p_bn cx <= 2040.
Proof.
  intros cx. pose proof (p_d_range cx) as R. unfold p_nF, p_F, c_n, p_bn, p_cap.
  destruct (c_pl cx) as [|x l]; cbn [tl length]; lia.
Qed.

(* ---- the meter: what the call has charged at each cut ---- *)
Definition PA_K1 (cx : ecx) : Z := mo_malloc MT (p_nF cx).
Definition PA_K2g (cx : ecx) : Z := PA_K1 cx + mo_malloc MT SRC_FILE_BLOCK.
Definition PA_K2r (cx : ecx) : Z := PA_K1 cx + mo_malloc MT SRC_FILE_BLOCK + 2 * mo_free MT.
Definition PA_K3 (cx : ecx) : Z := PA_K2g cx + mo_malloc MT (p_bn cx).
Definition PA_K6 (cx : ecx) : Z := PA_K3 cx + 2 * mo_free MT.
Definition PA_K7 (cx : ecx) : Z := PA_K6 cx + mo_malloc MT SRC_FILE_BLOCK.
Definition PA_K9 (cx : ecx) : Z := PA_K7 cx + 2 * mo_free MT.
Definition PA_K11 (cx : ecx) : Z := PA_K9 cx + mo_free MT.
Definition PA_K12 (cx : ecx) : Z := PA_K11 cx + mo_free MT.

Lemma PA_K12_need : ameter_laws MT -> forall cx, PA_K12 cx <= pe_need MT (c_n cx).
Proof.
  intros ML cx. pose proof (p_sizes cx) as (H1 & H2 & H3).
  assert (M1 : mo_malloc MT (p_nF cx) <= mo_malloc MT (c_n cx)) by (apply (mo_malloc_mono MT ML); lia).
  assert (M2 : mo_malloc MT (p_bn cx) <= mo_malloc MT 2040) by (apply (mo_malloc_mono MT ML); lia).
  unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g, PA_K1, pe_need. lia.
Qed.

Lemma PA_refused_le : ameter_laws MT -> forall cx, PA_K2r cx + mo_free MT <= PA_K12 cx.
Proof.
  intros ML cx. pose proof (p_sizes cx) as (H1 & H2 & H3).
  pose proof (mo_malloc_nonneg MT ML SRC_FILE_BLOCK ltac:(unfold SRC_FILE_BLOCK; lia)) as N1.
  pose proof (mo_malloc_nonneg MT ML (p_bn cx) ltac:(lia)) as N2.
  pose proof (mo_free_nonneg MT ML) as N3.
  unfold PA_K12, PA_K11, PA_K9, PA_K7, PA_K6, PA_K3, PA_K2g, PA_K2r, PA_K1. lia.
Qed.

(* ---- the objects ---- *)
Definition pPS (cx : ecx) (fp : Z) : Z := pF cx fp + PO_PS.
Definition pTS (cx : ecx) (fp : Z) : Z := pF cx fp + PO_TS.
Definition pval (W3 : world SEGS) (ms3 : machine_state) (a : Z) (n : nat) (v : Z) : Prop :=
  val_mem SEGS (rd W3 ms3) a n v.

(* The harness's two globals (objects 2 and 4 of the listing). *)
Definition p_glob (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) (src : Z) : Prop :=
  pval W3 ms3 (pa_val (A_OBJ 2)) 8 src /\ pval W3 ms3 (pa_val (A_OBJ 4)) 8 (p_nF cx).
(* The copy of the file, byte for byte. *)
Definition p_copy (cx : ecx) (W3 : world SEGS) (ms3 : machine_state) (b : Z) : Prop :=
  garr8 SEGS (rd W3 ms3) b (p_C cx).
(* ps after an accepting open: the two fields the harness reads before the first record (0x80a9c lw 8(s4);
   the f field the reader itself loads). *)
Definition p_psopen (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (h : Z) : Prop :=
  pval W3 ms3 (pPS cx fp) 8 h /\ pval W3 ms3 (pPS cx fp + 8) 4 (p_swz cx).
(* ps after a refused open or a close: the f field is NULL (0x80a84, 0x80e38 ld a0,0(s4)). *)
Definition p_psnull (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  pval W3 ms3 (pPS cx fp) 8 0.

(* What a call of pcap_source_next from position p leaves (KD, K4, KR, KL2, K5, KW and the rd32 cuts between them):
   the stream after the record psn_q p, ps's f and swapped, and for a fit record the fields, the timestamp and the
   record bytes the harness checks (0x80bf0 last_orig_len, 0x80c68 last_vlan_tagged, 0x80cf0 last_vlan_id, 0x80d4c
   ts, the bcmp calls). *)
Definition p_reader (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (b h buf p : Z) : Prop :=
  let Q := p_q cx p in
  asource_at SEGS KS (rd W3 ms3) h b (p_C cx) (p_pos cx Q) /\
  p_psopen cx fp W3 ms3 h /\
  (p_kind cx Q = PSN.KFit ->
     pval W3 ms3 (pPS cx fp + 12) 4 (PSN.orig (p_sw cx) (p_F cx) Q) /\
     pval W3 ms3 (pPS cx fp + 16) 4 (if PSN.tagged (p_sw cx) (p_F cx) Q then 1 else 0) /\
     pval W3 ms3 (pPS cx fp + 20) 2 (if PSN.tagged (p_sw cx) (p_F cx) Q then PSN.rec_vid (p_F cx) Q else 0) /\
     pval W3 ms3 (pTS cx fp) 8 (PSN.rec_ts (p_sw cx) (p_F cx) Q) /\
     garr8 SEGS (rd W3 ms3) buf (map (fun x : byte => bv_unsigned x) (PSN.rec_bytes (p_sw cx) (p_F cx) Q))).

(* The slots of the record loop (0x80acc, 0x80b30, 0x80b14, 0x80b38) beside pslots. *)
Definition p_lslots (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (buf : Z) : Prop :=
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ pslot cx W3 ms3 PS_VMASK 0xf00 /\
  pslot cx W3 ms3 PS_BUF12 (buf + 12) /\ pslot cx W3 ms3 PS_USEC (1000000 * 2 ^ 32).

(* ---- what every cut carries ---- *)
(* pe_body at pc with shadow sh, the event and meter bounds, the blocks the call holds beyond its caller's (L), and
   the descriptors and the file system as the caller left them. *)
Definition p_cut (cx : ecx) (fp pc : Z) (sh : list Z) (k kmax acc amax : Z) (L : list (Z * Z))
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  pe_body cx fp pc W3 ms3 sh /\ k <= kmax /\ acc <= amax /\
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx).

(* ---- the cuts ---- *)

(* PP_K1 0x809b8: malloc 0x809b4 returned the copy b (|F| bytes; malloc(0) for an empty file). g_file = src and
   g_file_len = |F| (0x80990, 0x809ac); the NULL test 0x809c0 follows. *)
Definition GI_K1 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  p_cut cx fp PP_K1 PSH_entry k 1 acc (PA_K1 cx) [(b, p_nF cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ 4096 <= b /\
  getr (ms_regs ms3) 10 = w64 b /\ getr (ms_regs ms3) 19 = w64 (pa_val (A_OBJ 2)) /\
  getr (ms_regs ms3) 21 = w64 (p_src cx) /\ getr (ms_regs ms3) 22 = w64 (p_nF cx) /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\ getr (ms_regs ms3) 26 = w64 (pF cx fp) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_SHB SHADOW_OFF /\
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\
  p_glob cx W3 ms3 (p_src cx) /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K2 0x80a10: pcap_source_open (0x80a0c) returned r. ps is in scope (PSH_ps, 0x809e0); g_file = b (0x809dc).
   Accepted (r = 0) exactly for a good file, with the stream open at 24 in the FILE h; refused (r = -1) with ps.f
   NULL and no stream. s6 = 24 (0x809f4), the bound of the good-file test 0x80a40. *)
Definition GI_K2 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  pe_body cx fp PP_K2 W3 ms3 PSH_ps /\ c_n cx < 2 ^ 26 /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx) /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 22 = w64 24 /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\ getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\
  getr (ms_regs ms3) 26 = w64 (pF cx fp) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_SHB SHADOW_OFF /\
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\
  p_glob cx W3 ms3 b /\ p_copy cx W3 ms3 b /\
  ((p_good cx = true /\ getr (ms_regs ms3) 10 = w64 0 /\ k <= 2 /\ acc <= PA_K2g cx /\
    exists h : Z,
      Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK)]) /\
      p_psopen cx fp W3 ms3 h /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) 24)
   \/
   (p_good cx = false /\ getr (ms_regs ms3) 10 = w64 (-1) /\ k <= 4 /\ acc <= PA_K2r cx /\
    Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx)]) /\
    p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3))).

(* NEW. PP_KM 0x80a3c: rd32 (0x80a38) of the file's first word (a0 = b, a1 = 0) returned the magic, sign-extended;
   reached only when g_file_len >= 4 (0x80a2c). The open's answer r is in s3 (0x80a10), s5 = -1 (0x80a1c); the
   frame, its shadow and the side-stack result are spilled (0x80a20..0x80a28). The arms are GI_K2's. *)
Definition GI_KM (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  pe_body cx fp PP_KM W3 ms3 PSH_ps /\ c_n cx < 2 ^ 26 /\ 4 <= p_nF cx /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx) /\
  getr (ms_regs ms3) 10 = w64 (bv_swrap 32 (p_magic cx)) /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (-1) /\ getr (ms_regs ms3) 22 = w64 24 /\
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_SHB SHADOW_OFF /\
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\ pslot cx W3 ms3 PS_FK (pF cx fp) /\
  pslot cx W3 ms3 PS_F (pF cx fp) /\ pslot cx W3 ms3 PS_SH (pSH cx fp) /\
  p_glob cx W3 ms3 b /\ p_copy cx W3 ms3 b /\
  ((p_good cx = true /\ getr (ms_regs ms3) 19 = w64 0 /\ k <= 2 /\ acc <= PA_K2g cx /\
    exists h : Z,
      Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK)]) /\
      p_psopen cx fp W3 ms3 h /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) 24)
   \/
   (p_good cx = false /\ getr (ms_regs ms3) 19 = w64 (-1) /\ k <= 4 /\ acc <= PA_K2r cx /\
    Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx)]) /\
    p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3))).

(* PP_K3 0x80acc: malloc 0x80ac8 returned the record buffer buf (bn bytes); the NULL test is the next slot
   (PP_bufnull 0x80ad0). cap is spilled (0x80abc). *)
Definition GI_K3 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf : Z,
  p_cut cx fp PP_K3 PSH_ps k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\ 4096 <= buf /\
  getr (ms_regs ms3) 10 = w64 buf /\ getr (ms_regs ms3) 18 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_SHB SHADOW_OFF /\
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\ pslot cx W3 ms3 PS_FK (pF cx fp) /\
  pslot cx W3 ms3 PS_F (pF cx fp) /\ pslot cx W3 ms3 PS_SH (pSH cx fp) /\
  pslot cx W3 ms3 PS_CAP (p_cap cx) /\
  p_glob cx W3 ms3 b /\ p_psopen cx fp W3 ms3 h /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) 24.

(* PP_KD 0x80b04: the first pcap_source_next (0x80b00, from position 24, ts = TS) returned n = first. ts is in scope
   (PSH_ts, 0x80ae0) and was set to ~0 before the call (0x80ae8). *)
Definition GI_KD (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf : Z,
  p_cut cx fp PP_KD PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 10 = w64 (p_first cx) /\ getr (ms_regs ms3) 18 = w64 b /\
  getr (ms_regs ms3) 19 = w64 buf /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf 24.

(* PP_K4 0x80b40, the head of the record loop: i records were checked, the reader's call from p (the harness's
   position `at`, s10) found the fit record psn_q p and answered n (slot PS_N). From KD: i = 0, p = 24, a3 = 0; from
   KL2: a3 = first. The calls bound (0x80b50), n <= cap (0x80b70) and at + 16 <= |F| (0x80b7c) follow from these
   facts. s7 = ~b (0x80b18) and s5 = -8 (0x80b20) are the guards' constants. *)
Definition GI_K4 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p : Z,
  p_cut cx fp PP_K4 PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p_kind cx (p_q cx p) = PSN.KFit /\
  ((i = 0 /\ p = 24) \/ (0 < i /\ getr (ms_regs ms3) 13 = w64 (p_first cx))) /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (-8) /\ getr (ms_regs ms3) 23 = w64 (- b - 1) /\
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\ getr (ms_regs ms3) 26 = w64 p /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_CALLS i /\ pslot cx W3 ms3 PS_N (p_res cx (p_q cx p)) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_KR 0x80b90, the head of the harness's skip loop: the harness is at e on the reader's skip chain from p to
   psn_q p (records of 0 bytes and records larger than cap); `first` is stored (0x80b64) and calls counted
   (0x80b8c). s6 = e + 16 on both entries (0x80b78; 0x80bc8). This slot is the guard `bltu s7,s10` (wrap(file + e)). *)
Definition GI_KR (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p e : Z,
  p_cut cx fp PP_KR PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p_kind cx (p_q cx p) = PSN.KFit /\
  p <= e /\ p_skips cx e (p_q cx p) /\ e + 16 <= p_nF cx /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (-8) /\ getr (ms_regs ms3) 22 = w64 (e + 16) /\
  getr (ms_regs ms3) 23 = w64 (- b - 1) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 26 = w64 e /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_CALLS (i + 1) /\ pslot cx W3 ms3 PS_N (p_res cx (p_q cx p)) /\
  pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* NEW. PP_KRI 0x80ba8: rd32 (0x80ba4) of the record header's incl at e (a0 = b + e + 8, a1 = ps.swapped 0x80b9c)
   returned it, sign-extended; s3 = b + e (0x80b94). GI_KR's facts at the same e. *)
Definition GI_KRI (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p e : Z,
  p_cut cx fp PP_KRI PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p_kind cx (p_q cx p) = PSN.KFit /\
  p <= e /\ p_skips cx e (p_q cx p) /\ e + 16 <= p_nF cx /\
  getr (ms_regs ms3) 10 = w64 (bv_swrap 32 (p_hw cx e 8)) /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 19 = w64 (b + e) /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (-8) /\ getr (ms_regs ms3) 22 = w64 (e + 16) /\
  getr (ms_regs ms3) 23 = w64 (- b - 1) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 26 = w64 e /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_CALLS (i + 1) /\ pslot cx W3 ms3 PS_N (p_res cx (p_q cx p)) /\
  pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* NEW. PP_KO 0x80bfc: the skip loop stopped at the fit record Q = psn_q p (incl <> 0, incl <= cap, 0x80bb4 /
   0x80bbc; Q + 16 + incl <= |F|, 0x80be8), and rd32 (0x80bf8) of its orig_len (a0 = b + Q + 12) returned it,
   sign-extended. s6 = ps.last_orig_len as `lw s6,0xc(s4)` (0x80bf0) loads it; this slot is `bne s6,a0` to
   PP_abort. s9 = incl (0x80bb0), s11 = incl sign-extended (0x80ba8). *)
Definition GI_KO (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p : Z,
  let Q := p_q cx p in
  p_cut cx fp PP_KO PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p <= Q /\ p_kind cx Q = PSN.KFit /\
  getr (ms_regs ms3) 10 = w64 (bv_swrap 32 (p_hw cx Q 12)) /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 19 = w64 (b + Q) /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 21 = w64 (-8) /\
  getr (ms_regs ms3) 22 = w64 (bv_swrap 32 (PSN.orig (p_sw cx) (p_F cx) Q)) /\
  getr (ms_regs ms3) 23 = w64 (- b - 1) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 25 = w64 (p_hw cx Q 8) /\ getr (ms_regs ms3) 26 = w64 Q /\
  getr (ms_regs ms3) 27 = w64 (bv_swrap 32 (p_hw cx Q 8)) /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_CALLS (i + 1) /\ pslot cx W3 ms3 PS_N (p_res cx Q) /\
  pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* NEW. PP_KT1 0x80d5c: the record's checks passed (orig_len, tagged, the bcmp calls 0x80c94 / 0x80cc4 or 0x80d40,
   the VLAN id), and rd32 (0x80d58) of the seconds (a0 = b + Q) returned them, sign-extended. s6 = ts as
   `ld s6,0(a0)` (0x80d4c) loads it. *)
Definition GI_KT1 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p : Z,
  let Q := p_q cx p in
  p_cut cx fp PP_KT1 PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p <= Q /\ p_kind cx Q = PSN.KFit /\
  getr (ms_regs ms3) 10 = w64 (bv_swrap 32 (p_hw cx Q 0)) /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 19 = w64 (b + Q) /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 21 = w64 (-8) /\
  getr (ms_regs ms3) 22 = w64 (PSN.rec_ts (p_sw cx) (p_F cx) Q) /\
  getr (ms_regs ms3) 23 = w64 (- b - 1) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 26 = w64 Q /\ getr (ms_regs ms3) 27 = w64 (bv_swrap 32 (p_hw cx Q 8)) /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_CALLS (i + 1) /\
  pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* NEW. PP_KT2 0x80d80: rd32 (0x80d7c) of the microseconds (a0 = b + Q + 4, 0x80d68) returned them, sign-extended;
   s9 = the seconds times 10^6 (mulhu s9,a0,a2 0x80d74 with a2 = PS_USEC). *)
Definition GI_KT2 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p : Z,
  let Q := p_q cx p in
  p_cut cx fp PP_KT2 PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p <= Q /\ p_kind cx Q = PSN.KFit /\
  getr (ms_regs ms3) 10 = w64 (bv_swrap 32 (p_hw cx Q 4)) /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (-8) /\ getr (ms_regs ms3) 22 = w64 (PSN.rec_ts (p_sw cx) (p_F cx) Q) /\
  getr (ms_regs ms3) 23 = w64 (- b - 1) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 25 = w64 (p_hw cx Q 0 * 1000000) /\ getr (ms_regs ms3) 26 = w64 Q /\
  getr (ms_regs ms3) 27 = w64 (bv_swrap 32 (p_hw cx Q 8)) /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_CALLS (i + 1) /\
  pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_KL2 0x80dbc: the loop's pcap_source_next (0x80db8, ts = TS) from p (the harness's new `at`, 0x80da8) returned
   n; j calls were counted (PS_CALLS); `first` is in PS_FIRST (0x80b64). *)
Definition GI_KL2 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf j p : Z,
  p_cut cx fp PP_KL2 PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  1 <= j /\ 24 + 17 * j <= p /\ p <= p_nF cx /\
  getr (ms_regs ms3) 10 = w64 (p_res cx (p_q cx p)) /\ getr (ms_regs ms3) 18 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 21 = w64 (-8) /\
  getr (ms_regs ms3) 23 = w64 (- b - 1) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 26 = w64 p /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_CALLS j /\ pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_K5 0x80e0c: the walk is over; the reader's call from p (= at) found no fit record and answered n <= 0 (PS_N;
   from KD: 0x80e04 at := 24, 0x80e08; from KL2: 0x80dc8); a0 = first (from KD: n itself; from KL2: 0x80dc0). *)
Definition GI_K5 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p : Z,
  p_cut cx fp PP_K5 PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  24 <= p <= p_nF cx /\ p_kind cx (p_q cx p) <> PSN.KFit /\
  getr (ms_regs ms3) 10 = w64 (p_first cx) /\ getr (ms_regs ms3) 18 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 26 = w64 p /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ pslot cx W3 ms3 PS_N (p_res cx (p_q cx p) mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_KW 0x80fb0, the head of the end-of-walk check (entered when at <> |F|, 0x80e20): the harness's e runs along
   the reader's skip chain from p; want is -1 until the loop decides it (0x80fb4). a0 = |F| (0x80e1c on entry,
   0x8100c on the back edge), s3 = (file <> 0) (0x80fa8), s7 = -9 (0x80fac), s5 = first (0x80e0c). The copy b stays a
   block and e <= |F|, so the guards on file + e (0x80fc0, 0x80fcc, 0x80fd0, 0x80fd4) are decided from this
   invariant. *)
Definition GI_KW (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p e : Z,
  p_cut cx fp PP_KW PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  24 <= p <= e /\ e <= p_nF cx /\ e <> p_nF cx /\ p_skips cx e (p_q cx p) /\ p_kind cx (p_q cx p) <> PSN.KFit /\
  getr (ms_regs ms3) 10 = w64 (p_nF cx) /\ getr (ms_regs ms3) 18 = w64 b /\
  getr (ms_regs ms3) 19 = w64 1 /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (p_first cx) /\ getr (ms_regs ms3) 23 = w64 (-9) /\
  getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\ getr (ms_regs ms3) 26 = w64 e /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ pslot cx W3 ms3 PS_N (p_res cx (p_q cx p) mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* NEW. PP_KWL 0x80fe4: e + 16 <= |F| (0x80fb8), and rd32 (0x80fe0) of the header's len at e (a0 = b + e + 8,
   0x80fdc) returned it, sign-extended; s6 = e + 16 (0x80fb0), want = -1 in s9 (0x80fb4). GI_KW's facts at the same
   e. *)
Definition GI_KWL (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p e : Z,
  p_cut cx fp PP_KWL PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  24 <= p <= e /\ e + 16 <= p_nF cx /\ p_skips cx e (p_q cx p) /\ p_kind cx (p_q cx p) <> PSN.KFit /\
  getr (ms_regs ms3) 10 = w64 (bv_swrap 32 (p_hw cx e 8)) /\ getr (ms_regs ms3) 18 = w64 b /\
  getr (ms_regs ms3) 19 = w64 1 /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (p_first cx) /\ getr (ms_regs ms3) 22 = w64 (e + 16) /\
  getr (ms_regs ms3) 23 = w64 (-9) /\ getr (ms_regs ms3) 24 = w64 (pa_val (A_HI 8)) /\
  getr (ms_regs ms3) 25 = w64 (-1) /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ pslot cx W3 ms3 PS_N (p_res cx (p_q cx p) mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_K6 0x80e38: pcap_source_close (0x80e34) returned; ps.f is NULL (0x80e38) and no stream is open. *)
Definition GI_K6 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf : Z,
  p_cut cx fp PP_K6 PSH_ts k 5 acc (PA_K6 cx) [(b, p_nF cx); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 21 = w64 (p_first cx) /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ p_glob cx W3 ms3 b /\ p_copy cx W3 ms3 b /\
  p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K7 0x80e50: the second pcap_source_open (0x80e4c) returned 0 (the file is good) with the stream open at 24 in
   a new FILE h; this slot is `bnez a0` to PP_abort. *)
Definition GI_K7 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf h : Z,
  p_cut cx fp PP_K7 PSH_ts k 6 acc (PA_K7 cx) [(b, p_nF cx); (buf, p_bn cx); (h, SRC_FILE_BLOCK)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 10 = w64 0 /\ getr (ms_regs ms3) 18 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 21 = w64 (p_first cx) /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\
  p_psopen cx fp W3 ms3 h /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) 24.

(* PP_K8 0x80e68: pcap_source_next (0x80e64, ts = NULL) from 24 returned the same first answer; this slot is
   `bne a0,s5` to PP_abort. *)
Definition GI_K8 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf h : Z,
  p_cut cx fp PP_K8 PSH_ts k 6 acc (PA_K7 cx) [(b, p_nF cx); (buf, p_bn cx); (h, SRC_FILE_BLOCK)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 10 = w64 (p_first cx) /\ getr (ms_regs ms3) 18 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 21 = w64 (p_first cx) /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\
  p_psopen cx fp W3 ms3 h /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) (p_pos cx (p_q cx 24)).

(* PP_K9 0x80e74: the second pcap_source_close (0x80e70) returned. *)
Definition GI_K9 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf : Z,
  p_cut cx fp PP_K9 PSH_ts k 8 acc (PA_K9 cx) [(b, p_nF cx); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pPS cx fp) /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ p_copy cx W3 ms3 b /\
  p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K10 0x80e88: pcap_source_next on the closed reader (0x80e84) returned -1. *)
Definition GI_K10 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf : Z,
  p_cut cx fp PP_K10 PSH_ts k 8 acc (PA_K9 cx) [(b, p_nF cx); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 10 = w64 (-1) /\ getr (ms_regs ms3) 18 = w64 b /\
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_BUF buf /\ p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K11 0x80e98: free 0x80e94 gave the record buffer back. *)
Definition GI_K11 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  p_cut cx fp PP_K11 PSH_ts k 9 acc (PA_K11 cx) [(b, p_nF cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 b /\
  pslots cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K12 0x80ea0: free 0x80e9c gave the copy back; the call holds no block. *)
Definition GI_K12 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  p_cut cx fp PP_K12 PSH_ts k 10 acc (PA_K12 cx) [] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  pslots cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K12r 0x80eac: ts is out of scope (from K12, 0x80ea8) or never was (the refused path lands here from 0x80a98
   after free 0x80a90). s9 = SH on both: reloaded at 0x80ea4, or at 0x80a94; the leave reloads s7 and s10 from
   PS_FK and PS_F (0x80ebc, 0x80ec0), written on both paths at 0x80a20 / 0x80a28. *)
Definition GI_K12r (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  (exists sh : list Z, (sh = PSH_tsout \/ sh = PSH_ps) /\
     p_cut cx fp PP_K12r sh k EV_LIB acc (PA_K12 cx) [] ly3 S3 W3 ms3 md3) /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\
  pslot cx W3 ms3 PS_FK (pF cx fp) /\ pslot cx W3 ms3 PS_F (pF cx fp) /\ asource_none SEGS KS (rd W3 ms3).

(* PP_leave 0x80ec4: the frame is about to be given back, all objects out of scope (PSH_entry: PSH_out_body /
   PSH_out_refused). Reached from K12r and from the early return of an input of 2^26 bytes or more (0x80940),
   which allocates nothing and charges nothing; s7 = the side-stack result (= F0), s10 = F0, s9 = SH on both. *)
Definition GI_leave (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  p_cut cx fp PP_leave PSH_entry k EV_LIB acc (PA_K12 cx) [] ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\ getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\
  getr (ms_regs ms3) 26 = w64 (pF cx fp) /\ asource_none SEGS KS (rd W3 ms3).

(* PP_abort 0x81034: no run reaches it. Every branch into it (0x809c0, 0x80a54, 0x80a60, 0x80a7c, 0x80a88, 0x80ab0,
   0x80ad0, 0x80b50, 0x80b70, 0x80b7c, 0x80bd4, 0x80be8, 0x80bfc, 0x80c6c, 0x80c84, the bcmp tests 0x80c98, 0x80cc8,
   0x80d44, 0x80d24, 0x80d30, 0x80d8c, 0x80e18, 0x80e2c, 0x80e3c, 0x80e50, 0x80e68, 0x80e8c) is refuted by the facts
   of the cut before it. The same holds for PE_TRAP (PcapEntryDefs.PE_GUARDS). *)
Definition GI_abort (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop := False.

Lemma pe_from_abort : forall POST, pe_from SK B MT KS POST GI_abort.
Proof. intros POST cx fp k acc ly3 S3 W3 ms3 md3 _ _ _ _ []. Qed.

(* ---- after the frame is given back ---- *)
(* PP_ret 0x80fa4, the `ret`: the side-stack frame was given back (the flag store 0x80f1c, astack_free_law), so the
   call owns no frame; the saved registers are restored (0x80f6c .. 0x80f9c), a0 = 0 (0x80f64). *)
Definition GI_ret (cx : ecx) (k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  ms_pc_val ms3 = w64 (BASE + PP_ret) /\ ms_resv ms3 = None /\ ms_svc_pending ms3 = None /\
  ms_rom ms3 = seg_rom SEGS /\ ms_fregs ms3 = fp_regs /\ ms_fcsr ms3 = fp_csr /\
  aregs_preserved (c_regs cx) (ms_regs ms3) /\ getr (ms_regs ms3) 1 = getr (c_regs cx) 1 /\
  getr (ms_regs ms3) 10 = w64 0 /\
  k <= EV_LIB /\ acc <= PA_K12 cx /\
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx) /\
  asource_none SEGS KS (rd W3 ms3) /\
  garr8 SEGS (rd W3 ms3) (c_p cx) (map (fun x : byte => bv_unsigned x) (c_pl cx)).

(* The form pe_from takes after the frame is given back: the journal owns no frame and frames S3 = []. *)
Definition pe_from_ret (POST : ecx -> world SEGS -> config -> Prop)
  (GIr : ecx -> Z -> Z -> alayout -> astate -> world SEGS -> machine_state -> Model -> Prop) : Prop :=
  forall (cx : ecx) (k acc : Z) ly3 S3 W3 (ms3 : machine_state) md3,
  pe_base SK B MT KS cx ->
  ajournal_gx SEGS B pe_G 0 [] LLVMF_STK (spZ (c_regs cx)) [sink_token] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx)
    (c_md cx) [] ly3 S3 W3 (ms_mem ms3) md3 k ->
  frames S3 = [] ->
  mo_le MT (c_S cx) S3 acc ->
  GIr cx k acc ly3 S3 W3 ms3 md3 ->
  SRr SEGS W3 (mkCfg ms3 md3) (POST cx).

End c.
End b.
End a.
(* The sink head is EXPLICIT on the two exported names that depend on it (a Theorem Labs lane, 21:57Z; see PcapEntry.v): the only
   global sink_head instance in this closure is the plain build's, so it must never be inferred. The phase
   predicates GI_* do not depend on it. *)
Arguments pe_from_ret {rc} SK {PI} B MT KS POST GIr.
Arguments pe_from_abort {rc} SK {PI} B MT KS POST.
