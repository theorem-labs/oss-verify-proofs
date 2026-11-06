(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the call chain `gch` taken from proofs/cgif/cgif_file_fuzzer/lib/A/ACf5.v's `rt_ch`, with fuzz_grant's module paths, for the phases of libreac/fuzz_grant's entry function LLVMFuzzerTestOneInput; the rest of the file is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntryDefs.v, with its module paths changed; 265 of its 330 lines of code are new or changed and 295 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/A/Prog/PcapEntryDefs.v, with its module paths and module names changed; 312 of its 344 lines of code are new or changed and 298 lines of the source are left out. *)
(* The phase predicates of fuzz_pcap's entry walk (LLVMFuzzerTestOneInput, 0x807c8, ASan build of libreac v1.9.0):
   one predicate per cut pc of PcapEntryDefs.v, in the shape PcapEntryDefs.pe_from takes them, so that the three
   harness lanes (H1: entry, E, EARLY, A, B_acc, B_ref, C up to PP_KD; H2: Walk, PP_KD to PP_K5; H3: W, R1..R7, BT
   up to PP_ret) meet at the same boundaries. A walk lane proves `pe_from SK B MT KS POST GI_next ->
   pe_from SK B MT KS POST GI_self`; GI_ret (after the side-stack frame is given back) is stated for
   pe_from_ret, and GI_abort is False.

   Every number is read from the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d..., image root: the
   original v1.9.0 pins; capstone disassembly of the unstripped twin). The register and spill-slot set stated at
   each cut is the set a liveness pass over the function's 779 instructions finds live there (calls clobber the
   caller-saved registers and use their argument registers; spill slots are the words at s1+off), so a cut states
   what the code after it reads, and nothing it does not. Register numbers: a0 10, a1 11, a2 12, a3 13, a4 14,
   t1 6, t4 29, s2 18, s3 19, s4 20, s5 21, s6 22, s7 23, s8 24, s9 25, s10 26, s11 27 (sp 2, s0 8, s1 9, s11, gp,
   tp are pe_body's).

   Names. F0 = pF cx fp (the frame on the side stack), SH = pSH cx fp (its shadow), PS = F0 + 32 (struct
   pcap_source ps: f at +0, swapped at +8, last_orig_len at +12, last_vlan_tagged at +16, last_vlan_id at +20),
   TS = F0 + 96 (uint64_t ts), b = the copy of the file (malloc 0x80940), h = the FILE of the open stream (inside
   pcap_source_open), buf = the record buffer (malloc 0x80ab8). The input: d = its first byte (0 if empty),
   F = the rest (the file, g_file_len bytes), cap = 8 d, bn = max cap 1; the reader's model is
   lib/Prog/pcap_source_struct_next.v (kind, psn_q, res_of, pos_of, rec_len, rec_ts, rec_bytes) and lib/Prog/Slot/PWalkDef.v (skips).

   cut      pc       live registers                                   live spill slots (s1+)
   K1       0x80944  a0=b s2=&g_file s4=F0 s5=src s6=|F| s7=F0 s9=SH  32 64
   K2       0x809a0  a0=r s3=b s4=F0 s7=F0 s9=SH                      32 64 88
   K3       0x80abc  a0=buf s3=b s4=F0 s5=cap s7=F0 s9=SH             32 64 88
   KD       0x80af4  a0=n s3=b s5=cap s6=buf                          8 16 24 32 64 80 88
   K4       0x80b34  a0=first(i>0) a2=n s2=p s3 s5 s6 s7=0xff00 s9=i  8..64 (step 8) 80 88
   KR       0x80b70  a1=|F| a2=n a4=e+16 t1=PS s2=e s3 s5 s6 s7 s8=sw s9=i+1   8..88 (step 8)
   KL2      0x80fa4  a0=n s2=p s3 s5 s6 s7 s9=j s10=first             8..64 (step 8) 80 88
   K5       0x8107c  a2=n s2=p s3 s5 s6 s10=first                     8 16 24 32 64 88
   KW       0x81224  a1=|F| a2=n a3=-1 a4=0xff00 t4=PS s2=e s3 s4 s5 s6 s7 s10   8 32 88
   K6       0x810ac  s3 s4 s5 s6 s7 s10                               8 88
   K7, K8   0x810c8, 0x810e0  a0 s2=PS s3 s4 s5 s6 s7 s10             8
   K9       0x810ec  s2=PS s3 s4 s5 s6 s7                             8
   K10      0x81100  a0=-1 s3 s4 s6 s7                                8
   K11      0x81110  s3 s4 s7                                         8
   K12      0x81118  s4 s7                                            8
   K12r     0x81124  s4 s7 s9                                         -
   leave    0x81134  s4 s7 s9                                         -
   ret      0x81214  a0=0 ra sp (and every callee-saved register restored)

   The input block. The copy b (|F| bytes) is in the cut's block list at every cut from PP_K1 to PP_K11 (it is
   freed at 0x81114, or at 0x80a84 on the refused path), with g_file = b and g_file_len = |F| from PP_K2 to PP_K6
   (g_file = src at PP_K1; nothing reads the globals after 0x810c4, so GI_K7 .. GI_K9 do not state them); GI_KR carries e + 16 <= |F| and GI_KW carries e <= |F|, so a walk (and the asan-ubsan
   twin's guard at 0x80fc0) decides file + e against the block from the invariant and AR's block law.

   What a phase does NOT carry, because the walk derives it from pe_base and pe_from's journal: the meta region
   (PSourceMeta.asrc_meta_inv_kept, with asource_img_laws as a Section hypothesis of the walk), the read-only data
   (PcapBase.arodata_ok_journalP), the stack window and its presence (the inner ajournal's own clauses), the shadow base cell
   and the use-after-return flag (AR), and the header, the saved registers and the input bytes (pe_body).

   What each callee's statement must supply at its sites, for these phases to be met (state the post over these
   PSource predicates and these caller-visible fields of ps; the stack slots above the callee's window, the
   frame's other bytes, the copy's bytes, the globals and the callee-saved registers are kept by the journal or
   by aregs_preserved):
   - pcap_source_open (a Theorem Labs lane; 0x8099c, 0x810c4; caller-journal form): a0 = 0 exactly when
     pcap_good F, and then ps.f = h, ps.swapped = pcap_sw F, asource_at KS h b (map unsigned F) 24, the blocks
     gain (h, 1304), +1 event, meter <= mo_malloc 1304; else a0 = -1, ps.f = 0, asource_none KS, blocks
     unchanged, at most +3 events (fmemopen's malloc and fclose's two frees; 0 when |F| = 0), meter
     <= mo_malloc 1304 + 2 mo_free. In both arms: frames unchanged and m_fds / m_fs unchanged (its journal's
     footprint carries the sink token, so ajournal alone lets them change).
   - pcap_source_next (a Theorem Labs lane; 0x80af0 and 0x80fa0 with ts = TS, 0x810dc and 0x810fc with
     ts = NULL): from asource_at KS h b C p with ps.f = h and ps.swapped = pcap_sw F: a0 = res_of (psn_q p),
     asource_at KS h b C (pos_of (psn_q p)), ps.f and ps.swapped kept, and for a fit record ps.last_orig_len =
     orig, ps.last_vlan_tagged / ps.last_vlan_id as tagged / rec_vid, the record bytes rec_bytes at buf, and
     *ts = rec_ts when ts <> NULL; ts untouched otherwise; with ps.f = 0: a0 = -1 and nothing changed; always 0
     events, meter 0, blocks and frames unchanged (its class-0 frame is given back before it returns).
   - pcap_source_close (a Theorem Labs lane, tpcap_source_close_specX; 0x810a8, 0x810e8): ps.f = 0,
     asource_none KS, the copy's bytes kept, the blocks lose (h, 1304), +2 events, frames unchanged (its draft
     has these), and meter <= 2 mo_free and m_fds / m_fs unchanged (its draft does not have these yet).
   The harness's own calls take cgif's runtime rules as Section hypotheses: amalloc04_rule (0x80940, 0x80ab8;
   4096 <= res closes both NULL tests 0x8094c and 0x80abc), afree04_rule (0x80a84, 0x8110c, 0x81114),
   aintrin_realizes OCpy / OSet (0x80968, 0x8098c), astack_malloc_realizes 1 (0x80838), abcmp_realizes
   (0x80d8c, 0x80da8, 0x80e08), astack_free_law (the flag store 0x8118c). The harness writes g_file and
   g_file_len (0x80930, 0x80938, 0x80970), which are NOT owned-static (a Theorem Labs lane decision 22:36Z): the call's journal is
   W_journal.v's ajournal_gx SEGS B pe_G 0 [] (pe_from, pe_from_ret, pe_post), its runs use W_journal's paj_run_x /
   paj_run_to_x with the write obligation awr_ok_x (the global stores are bytes of pe_G), and pe_base carries
   gx_ok SEGS B pe_G. A runtime entry is lifted by PaGxSites.aj_gx_entry_at or, for the allocator rules, by opening
   the journal, applying the rule to its inner donor journal and closing it with ajournal_gx_pack; a program callee
   whose statement takes a FRESH donor journal from the call state (libreac_fuzz_fopen) by
   PaJournalFs.ajournal_gx_callee, and one in the CALLER-JOURNAL form (pcap_source_open / _next / _close) by opening
   the gx journal, passing its inner donor journal to the callee and repacking with ajournal_gx_pack (lane
   PcapHarnessTail's gx_open / gx_pack0). m_fds / m_fs stay exact across the harness's own allocator and intrinsic calls by
   lib/A/Prog/PaJournalFs.v (amalloc04_sub_fs, afree04_sub_fs, afree_null04_sub_fs, same_but_materialized_fs; any
   other callee whose journal footprint is sink-closed: ajournal_sub_closed_fs). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapEntry PcapEntryA PcapEntryDefs.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapList PcapAddr PcapPa.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import W_journal.
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

(* ---- the input, as the harness splits it (0x80908 lbu, 0x80910, 0x80914, 0x8091c) ---- *)
Definition p_d (cx : ecx) : Z := match c_pl cx with [] => 0 | d :: _ => bv_unsigned d end.
Definition p_F (cx : ecx) : list byte := tl (c_pl cx).
Definition p_nF (cx : ecx) : Z := Z.of_nat (length (p_F cx)).
Definition p_cap (cx : ecx) : Z := 8 * p_d cx.                (* slli s5,a1,3  0x80aa8 *)
Definition p_bn (cx : ecx) : Z := Z.max (p_cap cx) 1.         (* addi a0,zero,1 0x80ab4 *)
Definition p_C (cx : ecx) : list Z := map (fun x : byte => bv_unsigned x) (p_F cx).
(* g_file's first value (0x80930): the byte after d, or the caller's pointer for an empty input. *)
Definition p_src (cx : ecx) : Z := match c_pl cx with [] => c_p cx | _ :: _ => c_p cx + 1 end.
Definition p_swz (cx : ecx) : Z := PST.pcap_sw (p_F cx).
Definition p_sw (cx : ecx) : bool := p_swz cx =? 1.
Definition p_good (cx : ecx) : bool := PST.pcap_good (p_F cx).

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
(* ps after an accepting open: the two fields the harness reads before the first record (0x80a8c lw 8(t1);
   the f field the reader itself loads). *)
Definition p_psopen (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (h : Z) : Prop :=
  pval W3 ms3 (pPS cx fp) 8 h /\ pval W3 ms3 (pPS cx fp + 8) 4 (p_swz cx).
Definition p_pspad (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  garr8 SEGS (rd W3 ms3) (pPS cx fp + 22) [165; 165].

(* ps right after an accepted pcap_source_open: its post sets last_orig_len (+12), last_vlan_tagged (+16) and
   last_vlan_id (+20) to 0; the two pad bytes +22 / +23 keep the harness's memset value 0xa5 (0x8098c; open writes only
   ps[0 .. 22)). pcap_source_next's open-reader premise reads all of them (found by a Theorem Labs lane). *)
Definition p_psfresh (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  pval W3 ms3 (pPS cx fp + 12) 4 0 /\ pval W3 ms3 (pPS cx fp + 16) 4 0 /\ pval W3 ms3 (pPS cx fp + 20) 2 0 /\
  p_pspad cx fp W3 ms3.

(* ps's two pad bytes, the harness's memset value 0xa5 (0x8098c). No call writes them: pcap_source_open and
   pcap_source_next write ps[0 .. 22), pcap_source_close ps[0 .. 8), so each keeps them as a frame byte outside its
   write set; but tpcap_source_open_post only KEEPS them, so the CALLER must carry them from the memset to the
   second open (found by a Theorem Labs lane: GI_K7's p_psfresh was unprovable at the R1 call without this). *)
(* ps after a refused open or a close: the f field is NULL (0x80a78, 0x810b0 ld a0,0(s2)). *)
Definition p_psnull (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) : Prop :=
  pval W3 ms3 (pPS cx fp) 8 0.

(* What a call of pcap_source_next from position p leaves (KD, K4, KR, KL2, K5, KW): the stream after the record
   psn_q p, ps's f and swapped, and for a fit record the fields, the timestamp and the record bytes the harness
   checks (0x80c80 last_orig_len, 0x80d64 last_vlan_tagged, 0x80dc4 last_vlan_id, 0x80e20 ts, the bcmp calls). *)
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

(* The slots of the record loop (0x80b08, 0x80b24, 0x80b2c) beside pslots. *)
Definition p_lslots (cx : ecx) (fp : Z) (W3 : world SEGS) (ms3 : machine_state) (buf : Z) : Prop :=
  pslots cx fp W3 ms3 /\ pslot cx W3 ms3 PS_VMASK 0xf00 /\ pslot cx W3 ms3 PS_BUF12 (buf + 12) /\
  pslot cx W3 ms3 PS_USEC (1000000 * 2 ^ 32).

(* ---- what every cut carries ---- *)
(* pe_body at pc with shadow sh, the event and meter bounds, the blocks the call holds beyond its caller's (L), and
   the descriptors and the file system as the caller left them. *)
Definition p_cut (cx : ecx) (fp pc : Z) (sh : list Z) (k kmax acc amax : Z) (L : list (Z * Z))
  (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state) (md3 : Model) : Prop :=
  pe_body cx fp pc W3 ms3 sh /\ k <= kmax /\ acc <= amax /\
  Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ L) /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx).

(* ---- the cuts ---- *)

(* PP_K1 0x80944: malloc 0x80940 returned the copy b (|F| bytes; malloc(0) for an empty file). g_file = src and
   g_file_len = |F| (0x80930, 0x80938); the NULL test 0x8094c follows. *)
Definition GI_K1 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  p_cut cx fp PP_K1 PSH_entry k 1 acc (PA_K1 cx) [(b, p_nF cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ 4096 <= b /\
  getr (ms_regs ms3) 10 = w64 b /\ getr (ms_regs ms3) 18 = w64 (pa_val (A_OBJ 2)) /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 21 = w64 (p_src cx) /\
  getr (ms_regs ms3) 22 = w64 (p_nF cx) /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_GLEN (pa_val (A_HI 8)) /\
  pslot cx W3 ms3 PS_F0 (pF cx fp) /\
  p_glob cx W3 ms3 (p_src cx) /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K2 0x809a0: pcap_source_open (0x8099c) returned r. ps is in scope (PSH_ps, 0x80974); g_file = b (0x80970).
   Accepted (r = 0) exactly for a good file, with the stream open at 24 in the FILE h; refused (r = -1) with ps.f
   NULL and no stream. *)
Definition GI_K2 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  pe_body cx fp PP_K2 W3 ms3 PSH_ps /\ c_n cx < 2 ^ 26 /\
  m_fds md3 = m_fds (c_md cx) /\ m_fs md3 = m_fs (c_md cx) /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\ getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_GLEN (pa_val (A_HI 8)) /\
  pslot cx W3 ms3 PS_PSP (pPS cx fp) /\
  p_glob cx W3 ms3 b /\ p_copy cx W3 ms3 b /\
  ((p_good cx = true /\ getr (ms_regs ms3) 10 = w64 0 /\ k <= 2 /\ acc <= PA_K2g cx /\
    exists h : Z,
      Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx); (h, SRC_FILE_BLOCK)]) /\
      p_psopen cx fp W3 ms3 h /\ p_psfresh cx fp W3 ms3 /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) 24)
   \/
   (p_good cx = false /\ getr (ms_regs ms3) 10 = w64 (-1) /\ k <= 4 /\ acc <= PA_K2r cx /\
    Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx) ++ [(b, p_nF cx)]) /\
    p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3))).

(* PP_K3 0x80abc: malloc 0x80ab8 returned the record buffer buf (bn bytes); the NULL test is this slot. *)
Definition GI_K3 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf : Z,
  p_cut cx fp PP_K3 PSH_ps k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\ 4096 <= buf /\
  getr (ms_regs ms3) 10 = w64 buf /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 21 = w64 (p_cap cx) /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\ getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\
  pslot cx W3 ms3 PS_D (p_d cx) /\ pslot cx W3 ms3 PS_GLEN (pa_val (A_HI 8)) /\
  pslot cx W3 ms3 PS_PSP (pPS cx fp) /\
  p_glob cx W3 ms3 b /\ p_psopen cx fp W3 ms3 h /\ p_psfresh cx fp W3 ms3 /\
  asource_at SEGS KS (rd W3 ms3) h b (p_C cx) 24.

(* PP_KD 0x80af4: the first pcap_source_next (0x80af0, from position 24, ts = TS) returned n = first. ts is in scope
   (PSH_ts, 0x80ad4) and was set to ~0 before the call (0x80adc). *)
Definition GI_KD (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf : Z,
  p_cut cx fp PP_KD PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 10 = w64 (p_first cx) /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 21 = w64 (p_cap cx) /\ getr (ms_regs ms3) 22 = w64 buf /\
  pslots cx fp W3 ms3 /\ p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf 24.

(* PP_K4 0x80b34, the head of the record loop: i records were checked, the reader's call from p (the harness's
   position `at`) found the fit record psn_q p and answered n. From KD: i = 0, p = 24, a0 = 0; from KL2: a0 = first.
   The calls bound (0x80b44), n <= cap (0x80b58) and at + 16 <= |F| (0x80b64) follow from these facts. *)
Definition GI_K4 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p : Z,
  p_cut cx fp PP_K4 PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p_kind cx (p_q cx p) = PSN.KFit /\
  ((i = 0 /\ p = 24) \/ (0 < i /\ getr (ms_regs ms3) 10 = w64 (p_first cx))) /\
  getr (ms_regs ms3) 12 = w64 (p_res cx (p_q cx p)) /\ getr (ms_regs ms3) 18 = w64 p /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 21 = w64 (p_cap cx) /\
  getr (ms_regs ms3) 22 = w64 buf /\ getr (ms_regs ms3) 23 = w64 0xff00 /\ getr (ms_regs ms3) 25 = w64 i /\
  p_lslots cx fp W3 ms3 buf /\ p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_KR 0x80b70, the head of the harness's skip loop: the harness is at e on the reader's skip chain from p to
   psn_q p (records of 0 bytes and records larger than cap); `first` is stored (0x80b5c) and calls counted
   (0x80b6c). a4 = e + 16 on both entries (0x80b60; 0x80c28). *)
Definition GI_KR (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf i p e : Z,
  p_cut cx fp PP_KR PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  0 <= i /\ 24 + 17 * i <= p /\ p_kind cx (p_q cx p) = PSN.KFit /\
  p <= e /\ p_skips cx e (p_q cx p) /\ e + 16 <= p_nF cx /\
  getr (ms_regs ms3) 6 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 11 = w64 (p_nF cx) /\
  getr (ms_regs ms3) 12 = w64 (p_res cx (p_q cx p)) /\ getr (ms_regs ms3) 14 = w64 (e + 16) /\
  getr (ms_regs ms3) 18 = w64 e /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 21 = w64 (p_cap cx) /\ getr (ms_regs ms3) 22 = w64 buf /\
  getr (ms_regs ms3) 23 = w64 0xff00 /\ getr (ms_regs ms3) 24 = w64 (p_swz cx) /\
  getr (ms_regs ms3) 25 = w64 (i + 1) /\
  p_lslots cx fp W3 ms3 buf /\ pslot cx W3 ms3 PS_FIRST (p_first cx mod 2 ^ 64) /\
  p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_KL2 0x80fa4: the loop's pcap_source_next (0x80fa0, ts = TS) from p (the harness's new `at`, 0x80f90) returned
   n; j calls were counted; s10 = first (0x80f30). *)
Definition GI_KL2 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf j p : Z,
  p_cut cx fp PP_KL2 PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  1 <= j /\ 24 + 17 * j <= p /\ p <= p_nF cx /\
  getr (ms_regs ms3) 10 = w64 (p_res cx (p_q cx p)) /\ getr (ms_regs ms3) 18 = w64 p /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 21 = w64 (p_cap cx) /\
  getr (ms_regs ms3) 22 = w64 buf /\ getr (ms_regs ms3) 23 = w64 0xff00 /\
  getr (ms_regs ms3) 25 = w64 j /\ getr (ms_regs ms3) 26 = w64 (p_first cx) /\
  p_lslots cx fp W3 ms3 buf /\ p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_K5 0x8107c: the walk is over; the reader's call from p (= at) found no fit record and answered n <= 0
   (from KD: 0x81074 at := 24; from KL2). *)
Definition GI_K5 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p : Z,
  p_cut cx fp PP_K5 PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  24 <= p <= p_nF cx /\ p_kind cx (p_q cx p) <> PSN.KFit /\
  getr (ms_regs ms3) 12 = w64 (p_res cx (p_q cx p)) /\ getr (ms_regs ms3) 18 = w64 p /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 21 = w64 (p_cap cx) /\
  getr (ms_regs ms3) 22 = w64 buf /\ getr (ms_regs ms3) 26 = w64 (p_first cx) /\
  pslots cx fp W3 ms3 /\ p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_KW 0x81224, the head of the end-of-walk check (entered when at <> |F|, 0x81098): the harness's e runs along
   the reader's skip chain from p; want is -1 until the loop decides it (0x81220). The copy b stays a block and
   e <= |F|, so the asan-ubsan twin's guard (file + e) is decided from this invariant. *)
Definition GI_KW (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b h buf p e : Z,
  p_cut cx fp PP_KW PSH_ts k 3 acc (PA_K3 cx) [(b, p_nF cx); (h, SRC_FILE_BLOCK); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  24 <= p <= e /\ e <= p_nF cx /\ e <> p_nF cx /\ p_skips cx e (p_q cx p) /\ p_kind cx (p_q cx p) <> PSN.KFit /\
  getr (ms_regs ms3) 11 = w64 (p_nF cx) /\ getr (ms_regs ms3) 12 = w64 (p_res cx (p_q cx p)) /\
  getr (ms_regs ms3) 13 = w64 (-1) /\ getr (ms_regs ms3) 14 = w64 0xff00 /\
  getr (ms_regs ms3) 18 = w64 e /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 21 = w64 (p_cap cx) /\
  getr (ms_regs ms3) 22 = w64 buf /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 26 = w64 (p_first cx) /\ getr (ms_regs ms3) 29 = w64 (pPS cx fp) /\
  pslots cx fp W3 ms3 /\ p_glob cx W3 ms3 b /\ p_reader cx fp W3 ms3 b h buf p.

(* PP_K6 0x810ac: pcap_source_close (0x810a8) returned; ps.f is NULL (0x810b0) and no stream is open. *)
Definition GI_K6 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf : Z,
  p_cut cx fp PP_K6 PSH_ts k 5 acc (PA_K6 cx) [(b, p_nF cx); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  p_pspad cx fp W3 ms3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 21 = w64 (p_cap cx) /\ getr (ms_regs ms3) 22 = w64 buf /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\ getr (ms_regs ms3) 26 = w64 (p_first cx) /\
  pslots cx fp W3 ms3 /\ p_glob cx W3 ms3 b /\ p_copy cx W3 ms3 b /\
  p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K7 0x810c8: the second pcap_source_open (0x810c4) returned 0 (the file is good) with the stream open at 24 in
   a new FILE h. *)
Definition GI_K7 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf h : Z,
  p_cut cx fp PP_K7 PSH_ts k 6 acc (PA_K7 cx) [(b, p_nF cx); (buf, p_bn cx); (h, SRC_FILE_BLOCK)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 10 = w64 0 /\ getr (ms_regs ms3) 18 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 21 = w64 (p_cap cx) /\ getr (ms_regs ms3) 22 = w64 buf /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\ getr (ms_regs ms3) 26 = w64 (p_first cx) /\
  pslots cx fp W3 ms3 /\
  p_psopen cx fp W3 ms3 h /\ p_psfresh cx fp W3 ms3 /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) 24.

(* PP_K8 0x810e0: pcap_source_next (0x810dc, ts = NULL) from 24 returned the same first answer. *)
Definition GI_K8 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf h : Z,
  p_cut cx fp PP_K8 PSH_ts k 6 acc (PA_K7 cx) [(b, p_nF cx); (buf, p_bn cx); (h, SRC_FILE_BLOCK)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\ p_good cx = true /\
  getr (ms_regs ms3) 10 = w64 (p_first cx) /\ getr (ms_regs ms3) 18 = w64 (pPS cx fp) /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 21 = w64 (p_cap cx) /\ getr (ms_regs ms3) 22 = w64 buf /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\ getr (ms_regs ms3) 26 = w64 (p_first cx) /\
  pslots cx fp W3 ms3 /\
  p_psopen cx fp W3 ms3 h /\ asource_at SEGS KS (rd W3 ms3) h b (p_C cx) (p_pos cx (p_q cx 24)).

(* PP_K9 0x810ec: the second pcap_source_close (0x810e8) returned. *)
Definition GI_K9 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf : Z,
  p_cut cx fp PP_K9 PSH_ts k 8 acc (PA_K9 cx) [(b, p_nF cx); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 18 = w64 (pPS cx fp) /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 21 = w64 (p_cap cx) /\
  getr (ms_regs ms3) 22 = w64 buf /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  pslots cx fp W3 ms3 /\ p_copy cx W3 ms3 b /\
  p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K10 0x81100: pcap_source_next on the closed reader (0x810fc) returned -1. *)
Definition GI_K10 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b buf : Z,
  p_cut cx fp PP_K10 PSH_ts k 8 acc (PA_K9 cx) [(b, p_nF cx); (buf, p_bn cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 10 = w64 (-1) /\ getr (ms_regs ms3) 19 = w64 b /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 22 = w64 buf /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  pslots cx fp W3 ms3 /\ p_psnull cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K11 0x81110: free 0x8110c gave the record buffer back. *)
Definition GI_K11 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  exists b : Z,
  p_cut cx fp PP_K11 PSH_ts k 9 acc (PA_K11 cx) [(b, p_nF cx)] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 19 = w64 b /\ getr (ms_regs ms3) 20 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  pslots cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K12 0x81118: free 0x81114 gave the copy back; the call holds no block. *)
Definition GI_K12 (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  p_cut cx fp PP_K12 PSH_ts k 10 acc (PA_K12 cx) [] ly3 S3 W3 ms3 md3 /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  pslots cx fp W3 ms3 /\ asource_none SEGS KS (rd W3 ms3).

(* PP_K12r 0x81124: ts is out of scope (from K12, 0x81120) or never was (the refused path lands here from 0x80a88
   after free 0x80a84). s9 = SH on both: reloaded at 0x8111c, or kept since the prologue. *)
Definition GI_K12r (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  (exists sh : list Z, (sh = PSH_tsout \/ sh = PSH_ps) /\
     p_cut cx fp PP_K12r sh k EV_LIB acc (PA_K12 cx) [] ly3 S3 W3 ms3 md3) /\
  c_n cx < 2 ^ 26 /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\ asource_none SEGS KS (rd W3 ms3).

(* PP_leave 0x81134: the frame is about to be given back, all objects out of scope (PSH_entry: PSH_out_body /
   PSH_out_refused). Reached from K12r and from the early return of an input of 2^26 bytes or more (0x808f0),
   which allocates nothing and charges nothing. *)
Definition GI_leave (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop :=
  p_cut cx fp PP_leave PSH_entry k EV_LIB acc (PA_K12 cx) [] ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 20 = w64 (pF cx fp) /\ getr (ms_regs ms3) 23 = w64 (pF cx fp) /\
  getr (ms_regs ms3) 25 = w64 (pSH cx fp) /\ asource_none SEGS KS (rd W3 ms3).

(* PP_abort 0x81340: no run reaches it. Every branch into it (0x8094c, 0x80a44 .. 0x80a7c, 0x80aa0, 0x80abc,
   0x80b44 .. 0x80d68, the bcmp tests, 0x80f74, 0x81080, 0x810a0, 0x810b4, 0x810c8, 0x810e0, 0x81104) is refuted
   by the facts of the cut before it. *)
Definition GI_abort (cx : ecx) (fp k acc : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS)
  (ms3 : machine_state) (md3 : Model) : Prop := False.

Lemma pe_from_abort : forall POST, pe_from SK B MT KS POST GI_abort.
Proof. intros POST cx fp k acc ly3 S3 W3 ms3 md3 _ _ _ _ []. Qed.

(* ---- after the frame is given back ---- *)
(* PP_ret 0x81214, the `ret`: the side-stack frame was given back (the flag store 0x8118c, astack_free_law), so the
   call owns no frame; the saved registers are restored (0x811dc .. 0x8120c), a0 = 0 (0x811d4). *)
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
