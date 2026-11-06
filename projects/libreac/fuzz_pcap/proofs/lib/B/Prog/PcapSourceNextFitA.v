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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceOpen.v, with its module names changed; 2607 of its 2671 lines of code are new or changed and 1487 lines of the source are left out. *)
(* pcap_source_next (fuzz_pcap.asan-ubsan 0x815b8, listing offset AF_pcap_source_next = 0xe30) on the ASan+UBSan
   build of libreac v1.9.0: the fit phase, from NP_fit (0x81988, listing offset 0x1200; nx_fit_inv,
   PcapSourceNextFitADefs.v) to NP_ts (0x81b1c, 0x1394; nx_ts_inv, PcapSourceNextFitBDefs.v) or NP_exit (0x818b4,
   0x112c; nx_exit_inv). On this image the path lies after the epilogue (0x81988..0x81b60).

   THE CODE (capstone 5 on the pin fuzz_pcap.asan-ubsan, sha256 9e66f771f22af67a...; slot table
   nxb-handoff.md (sha256 c02dc85fade1; internal record)):
   - 0x81988 `lbu a0,0(s10)`, 0x81990 `bnez a0` -> 0x81c28 (report_load8 of ps): the shadow check of ps;
     0x8198c s3 := F (NS_F0); 0x81994 a3 := ps->f; a1 := 1, a0 := buf (NS_BUF), a2 := s2 = incl;
     0x819a4 `jal __interceptor_trampoline_fread` (fread(buf, 1, incl, f)), returns to NP_fit_ra 0x819a8;
   - 0x819a8 a6 := FK (NS_FK), a7 := ts (NS_TS), a1 := -1; 0x819b4 `bne a0,s2` -> NP_exit (a short read: KCutFit);
   - ps->vtag := 0 (0x819d0) and ps->vid := 0 (0x819f4), each behind its shadow check (4 and 2 bytes);
     s4 := buf (NS_BUF), s2 := ts_sec (NS_SEC);
   - 0x819f8 `bltu s6,18` -> NP_ts (no tag); the UBSan guards `beqz s4` 0x819fc and `bltu -13,s4` 0x81a04 (buf null,
     buf + 12 wraps) to the `unimp` 0x81b64; the shadow check of buf + 12 and `lbu`; 0x81a28 `bne a3,0x81` -> 0x81b10
     (reloads a6, s3, a7) -> NP_ts; the guard 0x81a30, the shadow check of buf + 13 and `lbu`; reloads; 0x81a5c
     `bnez a3` -> NP_ts;
   - the tag: the shadow check of ps + 16 again, ps->vtag := 1 (0x81a70), the guards 0x81a74 0x81a7c, the shadow
     checks of buf + 14, buf + 15 and ps + 20, ps->vid := ((buf[14] << 8) & 0xf00) | buf[15] (0x81ad4), the guard
     0x81ad8, then __asan_memmove(buf + 12, buf + 16, (uint32) (incl - 16)) (0x81af4; the two ranges OVERLAP);
   - NP_mm_ra 0x81af8: s6 := s6 - 4, reloads a6, s3, a7, t0 (NS_FK, NS_F0, NS_TS, NS_SB), `j` NP_ts.
   The walk engine (paj_run_tok / paj_run_to_tok) decides every shadow check and every UBSan guard above from the
   seat's shadow table (ps, and buf's first 18 bytes once incl >= 18) and atom facts (4096 <= buf <= 0x7fffff800000,
   18 <= s6, a1 = 18); it stops only at the fread call, the bne / bltu / bnez on the record, the memmove call and NP_ts.

   THE PROOF of pb_nx_fitA: run to the fread call; the call by afread_spec (caller-journal form); the post seated
   again (fa_seat) at NP_fit_ra; the short read lands at NP_exit (fa_exit_of_mid); else the stores of vtag / vid := 0
   and `bltu s6,18`: s6 < 18 lands at NP_ts (fa_land_ts); else seated again with the record's bytes 12 .. 15
   (fa_seat_buf); buf[12] <> 0x81 and buf[13] <> 0 land at NP_ts; the tag runs to the memmove call, which
   aj_memmove_atS takes (amemmove_realizes, MemmoveDef.v); the moved record is fa_mm_bytes (PcapSourceNextFitAKit.v);
   seated again at NP_mm_ra and run to NP_ts. The middle state moves across each step by fa_mid_step / fa_mid_tag.

   THE TEMPLATE: lib/A/Prog/PcapSourceNextFitA.v (a working branch 9e6538d7889) for the model lemmas and
   aj_memmove_atS (now Required from PcapSourceNextFitAShared.v), and a Theorem Labs lane's closed asan-ubsan run lemmas psn_fit / psn_fit2 /
   psn_mmr (a working branch 988927a8299, pcap_source_next_fit.v (sha256 9c2f85f31386; internal record); read only) for the pcs. *)
(* Modified by Theorem Labs, 2026-10: the walk is new, over lib/B's listing and phase layer. The model lemmas
   fa_nth_byte .. fa_rec_tagged and aj_memmove_atS (once a verbatim copy of lib/A's text) are Required from the
   image-free lib/A/Prog/PcapSourceNextFitAShared.v; the frame lemmas fa_vm_frame / fa_asrc_frame (once a copy of
   lib/B/Prog/PcapSourceNextFitB.v's vm_frame / asource_at_frame, renamed) are replaced by the segs-generic
   vm_frame_segs / asource_at_frame_segs of lib/A/Prog/PcapSourceCloseSpec.v (a Theorem Labs lane). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSyms PcapList PcapAddr PcapPa PcapPaLib.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import YC1g YC1h YC85 PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Rt Require Import MemmoveDef.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextKit.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextFitADefs PcapSourceNextFitBDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.B.Prog Require Import PcapSourceNextFitAKit.
(* The image-free fit-A lemmas (model facts, aj_memmove_atS) and the segs-generic frame lemmas, Required instead of
   restated. PcapSourceCloseSpec is Required without Import: its names are used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextFitAShared.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma fa_raw_nth : forall sw C cap q i, bytes_ok C -> 0 <= q -> 0 <= i < PSN.incl sw (nxF C) q ->
  0 < PSN.incl sw (nxF C) q <= cap -> q + 16 + PSN.incl sw (nxF C) q <= Z.of_nat (length C) ->
  nth (Z.to_nat i) (fa_raw sw C q) 0 = PSN.fb (nxF C) (q + 16 + i).
Proof.
  intros sw C cap q i HC Hq0 Hi Hincl Hfit. unfold fa_raw.
  rewrite nth_firstn. destruct (Nat.ltb_spec (Z.to_nat i) (Z.to_nat (PSN.incl sw (nxF C) q))) as [Hl|Hl]; [|lia].
  rewrite nth_skipn, (fa_fb C (q + 16 + i) HC). f_equal. lia.
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* The symbolic states of the walk                                                                  *)
(* ---------------------------------------------------------------------------------------------- *)

(* The atoms: 0..31 the registers of the state the run starts from, then the values the run reads from
   memory: 32 the shadow base SHADOW_OFF (the slot NS_SB; Bx), 33 ps->f, 34 buf (NS_BUF), 35 F (NS_F0 and
   NS_FK), 36 &ts (NS_TS), 37 the ts_sec word (NS_SEC), 38 .. 41 the record's bytes 12 .. 15 (the tag test
   and the VLAN id). *)
Definition fa_extra (h buf F ts secw b12 b13 b14 b15 : Z) : list word :=
  map (Z_to_bv 64) [SHADOW_OFF; h; buf; F; ts; secw; b12; b13; b14; b15].
Definition fa_Bx : sv := SOff 32 0.
(* s10 holds the shadow address of ps (0x816d8); the token engine reads the check 0x81988 through it. *)
Definition fa_shps : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 0) (SLit 3)) fa_Bx.
Definition fa_sr : list sv := Eval vm_compute in sr_set sr_atoms 26%bv fa_shps.
(* The spill slots the phase reads (offsets from s1, read-only). *)
Definition fa_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) NS_SB (NS_FK + 8) 0 0
    [YP09.mkChunk NS_SB (CVal 8 (SOff 32 0)); YP09.mkChunk NS_TS (CVal 8 (SOff 36 0));
     YP09.mkChunk NS_SEC (CVal 8 (SOff 37 0)); YP09.mkChunk NS_F0 (CVal 8 (SOff 35 0));
     YP09.mkChunk NS_BUF (CVal 8 (SOff 34 0)); YP09.mkChunk NS_FK (CVal 8 (SOff 35 0))].
(* The caller's struct at s5: ps->f read; vtag and vid ([16, 22)) writable on the fit path. *)
Definition fa_ps (pw : bool) : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 PS_LEN (if pw then PS_VT_OFF else 0) (if pw then PS_VID_OFF + 2 else 0)
    [YP09.mkChunk 0 (CVal 8 (SOff 33 0))].
(* The record's bytes 12 .. 15 in the buffer, read-only. *)
Definition fa_buf : YP09.region :=
  YP09.mkRegion (Some 34%nat) 12 16 0 0
    [YP09.mkChunk 12 (CVal 1 (SOff 38 0)); YP09.mkChunk 13 (CVal 1 (SOff 39 0));
     YP09.mkChunk 14 (CVal 1 (SOff 40 0)); YP09.mkChunk 15 (CVal 1 (SOff 41 0))].
Definition fa_G : facts := mkFacts
  [(21%nat, mkAF 4096 (2 ^ 47 - 24) 3); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (34%nat, mkAF 4096 0x7fffff800000 0);
   (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 255 0)] [] [].
Definition fa_SH1 : list shent := [mkSHE 21 0 PS_LEN].
Definition fa_SH2 : list shent := [mkSHE 21 0 PS_LEN; mkSHE 34 0 18].
Definition fa_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).

Lemma fa_U_shx : forall E v, ew E 21 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> 0 <= v < 2 ^ 47 ->
  U E fa_shps = shadow_of_addr SHADOW_OFF v.
Proof.
  intros E v H21 H32 Hv. unfold fa_shps, fa_Bx.
  rewrite !U_SAlu. rewrite (U_atom E 21 v H21) by lia. rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; lia).
  rewrite U_SLit.
  cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= v / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (zcanon_id (v / 8)) by (unfold M64; lia).
  unfold shadow_of_addr, SHADOW_OFF. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.


Definition fa_G2 : facts := mkFacts
  [(11%nat, mkAF 18 18 0); (21%nat, mkAF 4096 (2 ^ 47 - 24) 3); (22%nat, mkAF 18 2040 0); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0);
   (34%nat, mkAF 4096 0x7fffff800000 0);
   (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0); (41%nat, mkAF 0 255 0)] [] [].

Definition fa_sr2 : list sv := Eval vm_compute in sr_set fa_sr 20%bv (SOff 34 0).

Definition fa_ps0 : YP09.region :=
  YP09.mkRegion (Some 21%nat) 0 PS_LEN PS_VT_OFF (PS_VID_OFF + 2)
    [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk PS_VT_OFF (CVal 4 (SLit 0));
     YP09.mkChunk PS_VID_OFF (CVal 2 (SLit 0))].

Definition fa_shx (k : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 21 k) (SLit 3)) fa_Bx.
Definition fa_sr3 : list sv := Eval vm_compute in
  sr_set (sr_set (sr_set (sr_set fa_sr2 10%bv (SOff 21 20)) 12%bv (SOff 21 16)) 14%bv (fa_shx 20)) 15%bv (fa_shx 16).
Lemma fa_U_shx_k : forall E v k, ew E 21 = Z_to_bv 64 v -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> 0 <= v -> 0 <= k ->
  v + k < 2 ^ 47 -> U E (fa_shx k) = shadow_of_addr SHADOW_OFF (v + k).
Proof.
  intros E v k H21 H32 Hv Hk Hvk. unfold fa_shx, fa_Bx.
  rewrite !U_SAlu. rewrite U_off by (rewrite H21, unsigned_lit_small by lia; unfold M64; lia).
  rewrite H21, unsigned_lit_small by lia.
  rewrite (U_atom E 32 SHADOW_OFF H32) by (unfold SHADOW_OFF; lia). rewrite U_SLit.
  cbn [zalu_raw]. change (Z.land (zcanon 3) 63) with 3.
  rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (0 <= (v + k) / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (zcanon_id ((v + k) / 8)) by (unfold M64; lia).
  unfold shadow_of_addr, SHADOW_OFF. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

Ltac fa_inst H := repeat (specialize (H ltac:(lazymatch goal with |- ?G => let t := type of G in lazymatch t with Prop => first [assumption | lia] end end))).

Ltac fa_kept HS regs0 XT0 L K :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    let HA := fresh "HA" in
    assert (HA : env_agree 32 (Ereg regs0 XT0) Ex)
      by (split; [intros n Hn; rewrite ?ew_ewset_other by lia; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs0 XT0 L HS HA ltac:(clear; vm_compute; reflexivity)) as K;
    cbn [restrict ms_regs] in K; clear HA
  end.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ pcap_listing PI).
#[local] Abbreviation VAL := (@pa_val _ pcap_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ pcap_listing PI).
#[local] Abbreviation BASE := (@pa_val _ pcap_listing PI A_TEXT).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Lemma fa_regs_ok : forall regs extra ps,
  nth 0 extra (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF ->
  getr regs 21 = w64 ps -> getr regs 26 = w64 (shadow_of_addr SHADOW_OFF ps) -> 0 <= ps < 2 ^ 47 ->
  regs_ok (Eimg (Ereg regs extra)) fa_sr regs.
Proof.
  intros regs extra ps H32 R21 R26 Hps r.
  assert (E21 : ew (Eimg (Ereg regs extra)) 21 = Z_to_bv 64 ps)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs extra 21 21%bv eq_refl); exact R21).
  assert (E32 : ew (Eimg (Ereg regs extra)) 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite <- H32; exact (ew_Ereg_extra regs extra 0)).
  destruct (decide (r = 26%bv)) as [->|Hne].
  - change fa_sr with (sr_set sr_atoms 26%bv fa_shps). rewrite sr_get_set_same by reflexivity.
    rewrite denot_lit_U, (fa_U_shx _ ps E21 E32 Hps). exact R26.
  - change fa_sr with (sr_set sr_atoms 26%bv fa_shps). rewrite sr_get_set_other by exact Hne.
    apply regs_ok_Eimg_Ereg.
Qed.

Lemma fa_rdword_range : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
  intros H mem a v Hr. unfold rdword in Hr.
  assert (Hb : forall x b, aview SEGS H mem x = Some b -> 0 <= b < 256).
  { intros x b Hx. unfold aview in Hx.
    destruct (YP09.mbyte SEGS (mrestrict H mem) x) as [y|]; cbn [option_map] in Hx; [|discriminate].
    injection Hx as <-. pose proof (bv_unsigned_in_range 8 y) as Hy.
    change (bv_modulus 8) with 256 in Hy. lia. }
  destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
  destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
  destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
  destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
  destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
  destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
  destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
  destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
  injection Hr as <-.
  pose proof (Hb _ _ E0). pose proof (Hb _ _ E1). pose proof (Hb _ _ E2). pose proof (Hb _ _ E3).
  pose proof (Hb _ _ E4). pose proof (Hb _ _ E5). pose proof (Hb _ _ E6). pose proof (Hb _ _ E7). lia.
Qed.

Lemma fa_slot_chunk : forall E H mem sp1 off n v,
  rdword (aview SEGS H mem) (sp1 + off) = Some v -> ew E n = Z_to_bv 64 v ->
  YP09.chunk_ok SEGS E (mrestrict H mem) sp1 (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
  intros E H mem sp1 off n v Hv He.
  pose proof (fa_rdword_range H mem _ v Hv) as Hr.
  apply (chunk_ok_val SEGS E (mrestrict H mem) sp1 off 8%N (SOff n 0) v).
  - cbn [sv_denot]. rewrite He, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hr.
  - cbn [Z.of_N]. lia.
  - cbn [N.to_nat]. apply (val_mem_of_rdword SEGS H mem). exact Hv.
Qed.

(* The spill region, from the six slots it holds. *)
Lemma fa_spill_ok : forall E H mem sp1 buf F ts secw,
  bv_unsigned (ew E 9) = sp1 -> ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 34 = Z_to_bv 64 buf ->
  ew E 35 = Z_to_bv 64 F -> ew E 36 = Z_to_bv 64 ts -> ew E 37 = Z_to_bv 64 secw ->
  0 <= sp1 -> sp1 + 128 <= 2 ^ 64 ->
  rdword (aview SEGS H mem) (sp1 + NS_SB) = Some SHADOW_OFF ->
  rdword (aview SEGS H mem) (sp1 + NS_TS) = Some ts ->
  rdword (aview SEGS H mem) (sp1 + NS_SEC) = Some secw ->
  rdword (aview SEGS H mem) (sp1 + NS_F0) = Some F ->
  rdword (aview SEGS H mem) (sp1 + NS_BUF) = Some buf ->
  rdword (aview SEGS H mem) (sp1 + NS_FK) = Some F ->
  YP09.region_ok SEGS E (mrestrict H mem) fa_spill.
Proof.
  intros E H mem sp1 buf F ts secw U9 E32 E34 E35 E36 E37 Hs0 Hs1 S1 S2 S3 S4 S5 S6.
  unfold YP09.region_ok, fa_spill. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. unfold NS_SB, NS_TS, NS_SEC, NS_F0, NS_BUF, NS_FK in *.
  split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil; eapply fa_slot_chunk; eassumption.
Qed.

(* The struct's region: ps->f, and (pw) the bytes of vtag and vid writable. *)
Lemma fa_ps_ok : forall E H mem ps h (pw : bool),
  bv_unsigned (ew E 21) = ps -> ew E 33 = Z_to_bv 64 h -> 0 <= h < 2 ^ 64 -> 0 <= ps -> ps + PS_LEN <= 2 ^ 64 ->
  val_mem SEGS (mrestrict H mem) ps 8 h ->
  (pw = true -> forall a, ps + PS_VT_OFF <= a < ps + PS_VID_OFF + 2 -> apresent H mem a) ->
  YP09.region_ok SEGS E (mrestrict H mem) (fa_ps pw).
Proof.
  intros E H mem ps h pw U21 E33 Hh Hp0 Hp1 Hv Hw.
  unfold YP09.region_ok, fa_ps. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U21. unfold PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
  split; [lia|]. split; [lia|]. split.
  { intros o Ho. destruct pw; [|lia]. apply (apresent_writable SEGS). apply Hw; [reflexivity | lia]. }
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E (mrestrict H mem) ps 0 8%N (SOff 33 0) h).
  - cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [Z.of_N]. change (8 * 8) with 64. exact Hh.
  - cbn [Z.of_N]. lia.
  - rewrite Z.add_0_r. exact Hv.
Qed.

(* The ps entry of the shadow table: [ps, ps + 24) addressable, ps in application memory. *)
Lemma fa_shent_ps : forall E (m : word -> option byte) ps,
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 21 = Z_to_bv 64 ps -> 0 <= ps -> ps + PS_LEN <= 2 ^ 47 ->
  amem_range ps PS_LEN ->
  range_addressable (rd_of SEGS m) SHADOW_OFF ps PS_LEN ->
  shent_ok SEGS fa_Bx E m (mkSHE 21 0 PS_LEN).
Proof.
  intros E m ps E32 E21 Hp0 Hp1 Hamr Hra. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold fa_Bx.
  rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom E 21 ps E21) by (unfold PS_LEN in *; lia). split.
  - rewrite Z.add_0_r, Z.sub_0_r. exact Hra.
  - intros a Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF, PS_LEN in *. cbn in Ha. lia.
Qed.

(* Every byte the open reader may write lies in [4096, alloc_ceiling): the struct and the timestamp cell in the
   caller's side-stack frames, the buffer and the FILE block in blocks. *)
Lemma fa_E_low : forall B KS cx, AR_laws SEGS B -> nx_base SK B KS cx -> n_h cx <> 0 ->
  forall a, nx_E cx a -> 4096 <= a < alloc_ceiling.
Proof.
  intros B KS cx LAWS HB Hh a HE.
  pose proof HB as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hps4 & _ & _ & Hpsown
    & Hpsf1 & Hpsf2 & _ & _ & _ & _ & _ & HBUFB & HTSB & HSTR & _).
  pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _).
  unfold nx_E, nx_wrset in HE. destruct HE as [Ha | [Ha | [(Ht & Ha) | (_ & Ha)]]].
  - assert (Hin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hpsown).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hc & _). unfold PS_LEN in *. lia.
  - destruct (HBUFB Hh) as (Hin & Hb4 & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & Hc & _).
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hq]. lia.
  - destruct (HTSB Hh Ht) as (_ & _ & Ht4 & _ & _ & (tcid & tpos & Htin & Ht1 & Ht2) & _).
    assert (Hin : In (tcid, tpos) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Htin).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hc & _). lia.
  - destruct (HSTR Hh) as (Hin & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hh4 & Hc & _).
    change (req_size SRC_FILE_BLOCK) with 1304 in Hc. unfold SRC_FILE_BLOCK in Ha. lia.
Qed.

(* The chain this call hands to a callee it calls with sp' (sp' + 16 <= the entry sp): the call's own link
   (sp, ra, s0), saved by the prologue (nsaved), on top of the caller's chain (nx_base), which lies above sp and so
   is kept (nx_kept). *)
Lemma fa_achain : forall B KS cx W3 (ms3 : machine_state) ly3 E sp',
  AR_laws SEGS B -> nx_base SK B KS cx -> n_h cx <> 0 ->
  layout_le (length (st_secs (n_S cx))) (n_ly cx) ly3 ->
  nsaved cx W3 ms3 ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 (ms_mem ms3) (spZ (n_regs cx)) E ->
  (forall a, E a -> nx_E cx a) ->
  sp' + 16 <= spZ (n_regs cx) ->
  achain ly3 (aview SEGS (w_H W3) (ms_mem ms3)) sp' (spZ (n_regs cx)) (nx_ch cx).
Proof.
  intros B KS cx W3 ms3 ly3 E sp' LAWS HB Hh Hly3 (SV1 & SV2) HK HEs Hsp'.
  pose proof HB as (HJc & _ & _ & Hra4 & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & Hch & _).
  pose proof HJc as (_ & Hlyc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
  pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK_B = 8464) by reflexivity.
  destruct Hly3 as (_ & _ & _ & _ & _ & _ & _ & _ & Et3 & _).
  destruct Hlyc as (_ & _ & _ & _ & _ & _ & _ & _ & Etc & _).
  assert (Etop : ly_top ly3 = ly_top (n_lyc cx)) by congruence.
  pose proof (SV2 0 ltac:(lia)) as SV0. cbn in SV0. replace (spZ (n_regs cx) - 16 - 8 * 0) with (spZ (n_regs cx) - 16) in SV0 by lia.
  change (bv_unsigned (getr (n_regs cx) 8)) with (s0Z (n_regs cx)) in SV0.
  unfold nx_ch. destruct (Z.ltb_spec (spZ (n_regs cx) + 16) (ly_top (n_lyc cx))) as [Hlt|Hge].
  - apply (achain_push ly3 (aview SEGS (w_H (n_W cx)) (n_memc cx))).
    + apply (achain_ly_top (n_lyc cx)); [exact Etop | exact Hch].
    + lia.
    + intros a Ha. destruct HK as (K1 & _).
      apply K1; [lia | rewrite HNX; lia |].
      intros HEa. pose proof (fa_E_low B KS cx LAWS HB Hh a (HEs a HEa)). lia.
    + exact SV1.
    + exact SV0.
    + exact Hra4.
    + lia.
    + apply Z.mod_divide in Hal16; [|lia]. apply Z.mod_divide; [lia|]. destruct Hal16 as [z Hz]. exists (2 * z). lia.
    + lia.
    + exact Hsp'.
  - left. split; [right; left; lia | reflexivity].
Qed.

(* ---- facts read through a memory that kept their bytes (from one world to another) ---- *)
Lemma fa_vm_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a n v,
  (forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rdW W m) a n v -> val_mem SEGS (rdW W' m') a n v.
Proof.
  intros W W' m m' a n v K Hv k Hk.
  rewrite (mbyte_of_aview SEGS (w_H W) (w_H W') m m' (a + Z.of_nat k)) by (apply K; lia).
  exact (Hv k Hk).
Qed.

Lemma fa_garr8_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  garr8 SEGS (rdW W m) a l -> garr8 SEGS (rdW W' m') a l.
Proof.
  intros W W' m m' a l K Hg. apply (garr8_frame SEGS (rdW W m) (rdW W' m') a l Hg).
  intros x Hx. apply (mbyte_of_aview SEGS). apply K. exact Hx.
Qed.

Lemma fa_ps_keep : forall (W W' : world SEGS) (m m' : word -> option byte) ps h sw ol vt vid pad,
  (forall x, ps <= x < ps + PS_LEN -> aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  nx_ps_at SEGS (rdW W m) ps h sw ol vt vid pad -> nx_ps_at SEGS (rdW W' m') ps h sw ol vt vid pad.
Proof.
  intros W W' m m' ps h sw ol vt vid pad K (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold nx_ps_at.
  unfold PS_LEN, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
  split; [eapply fa_vm_keep; [|exact P1]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply fa_vm_keep; [|exact P2]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply fa_vm_keep; [|exact P3]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply fa_vm_keep; [|exact P4]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply fa_vm_keep; [|exact P5]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply fa_garr8_keep; [|exact P6]; intros x Hx; apply K; rewrite P7 in Hx; cbn in Hx; lia|].
  exact P7.
Qed.

(* Readable bytes always read some list. *)
Lemma fa_buf_exists : forall (H : word -> bool) (m : word -> option byte) a (n : nat),
  (forall i, (i < n)%nat -> apresent H m (a + Z.of_nat i)) ->
  exists l, garr8 SEGS (mrestrict H m) a l /\ length l = n.
Proof.
  intros H m a n Hp.
  set (f := fun i : nat => match mbyte SEGS (mrestrict H m) (a + Z.of_nat i) with Some b => bv_unsigned b | None => 0 end).
  exists (map f (seq 0 n)).
  split; [|rewrite length_map, length_seq; reflexivity].
  intros j Hj. rewrite length_map, length_seq in Hj.
  assert (Ef : nth j (map f (seq 0 n)) 0 = f j).
  { rewrite (nth_indep (map f (seq 0 n)) 0 (f 0%nat)) by (rewrite length_map, length_seq; exact Hj).
    rewrite map_nth, seq_nth by exact Hj. reflexivity. }
  rewrite Ef. unfold f.
  destruct (Hp j Hj) as (HH & b & Hb).
  assert (Hmb : mbyte SEGS (mrestrict H m) (a + Z.of_nat j) = Some b).
  { unfold mbyte, mrestrict. rewrite HH, Hb. reflexivity. }
  rewrite Hmb. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  split; [|lia].
  intros k Hk. assert (k = 0%nat) by lia. subst k. rewrite Z.add_0_r, Hmb. f_equal.
  unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r. change (2 ^ 8) with 256.
  rewrite !(Z.mod_small (bv_unsigned b)) by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

Lemma fa_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hc. pose proof (HP (bv_unsigned r) Hc) as H. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Lemma fa_rdword_keep : forall (W W' : world SEGS) (m m' : word -> option byte) a v,
  (forall k, 0 <= k < 8 -> aview SEGS (w_H W') m' (a + k) = aview SEGS (w_H W) m (a + k)) ->
  rdword (aview SEGS (w_H W) m) a = Some v -> rdword (aview SEGS (w_H W') m') a = Some v.
Proof. intros W W' m m' a v K Hv. rewrite <- Hv. apply rdword_ext. exact K. Qed.

Lemma fa_src_bytes : forall KS (m : word -> option byte) f b C p, asource_at SEGS KS m f b C p -> bytes_ok C.
Proof.
  intros KS m f b C p (Wn & cpos & fl & md & H). cbv zeta in H.
  destruct H as (_ & _ & _ & _ & _ & _ & _ & Hbok & _). exact Hbok.
Qed.

Lemma fa_denot_extra : forall regs h buf F ts secw b12 b13 b14 b15 (j : nat) v,
  nth j [SHADOW_OFF; h; buf; F; ts; secw; b12; b13; b14; b15] 0 = v -> (j < 10)%nat -> 0 <= v < 2 ^ 64 ->
  sv_denot (Eimg (Ereg regs (fa_extra h buf F ts secw b12 b13 b14 b15))) (SOff (32 + j) 0) = Z_to_bv 64 v.
Proof.
  intros regs h buf F ts secw b12 b13 b14 b15 j v Hv Hj Hr. cbn [sv_denot].
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold fa_extra.
  change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth, Hv.
  rewrite unsigned_lit_small by lia. rewrite Z.add_0_r. reflexivity.
Qed.
Lemma fa_byte_inj : forall (m : word -> option byte) x v1 v2, 0 <= v1 < 256 -> 0 <= v2 < 256 ->
  val_mem SEGS m x 1 v1 -> val_mem SEGS m x 1 v2 -> v1 = v2.
Proof.
  intros m x v1 v2 R1 R2 V1 V2. pose proof (V1 0%nat ltac:(lia)) as E1. pose proof (V2 0%nat ltac:(lia)) as E2.
  rewrite E1 in E2. assert (E3 : Z_to_bv 8 (YO0f.le_byte v1 1 0) = Z_to_bv 8 (YO0f.le_byte v2 1 0)) by congruence.
  clear E1 E2. rename E3 into E2. apply (f_equal (fun w : byte => bv_unsigned w)) in E2.
  rewrite !Z_to_bv_unsigned in E2. unfold YO0f.le_byte in E2. change (8 * Z.of_nat 1) with 8 in E2.
  change (8 * Z.of_nat 0) with 0 in E2. rewrite !Z.shiftr_0_r in E2. change (2 ^ 8) with 256 in E2.
  rewrite !(Z.mod_small v1), !(Z.mod_small v2) in E2 by lia. unfold bv_wrap in E2.
  change (bv_modulus 8) with 256 in E2. rewrite !Z.mod_small in E2 by lia. exact E2.
Qed.

Lemma fa_garr8_prefix : forall (m : word -> option byte) a l1 l2, garr8 SEGS m a l1 -> garr8 SEGS m a l2 ->
  (length l1 <= length l2)%nat -> firstn (length l1) l2 = l1.
Proof.
  intros m a l1 l2 H1 H2 Hl. apply nth_ext with (d := 0) (d' := 0).
  - rewrite length_firstn. lia.
  - intros n Hn. rewrite length_firstn in Hn. rewrite nth_firstn.
    destruct (Nat.ltb_spec n (length l1)) as [Hlt|Hge]; [|lia].
    destruct (H1 n ltac:(lia)) as (V1 & R1). destruct (H2 n ltac:(lia)) as (V2 & R2).
    symmetry. exact (fa_byte_inj m _ _ _ R1 R2 V1 V2).
Qed.

Lemma fa_ps_new : forall (W W' : world SEGS) (m m' : word -> option byte) ps h sw ol vt vid vt' vid' pad,
  nx_ps_at SEGS (rdW W m) ps h sw ol vt vid pad ->
  (forall x, ps <= x < ps + PS_LEN -> ~ (ps + PS_VT_OFF <= x < ps + PS_VID_OFF + 2) ->
     aview SEGS (w_H W') m' x = aview SEGS (w_H W) m x) ->
  val_mem SEGS (rdW W' m') (ps + PS_VT_OFF) 4 vt' -> val_mem SEGS (rdW W' m') (ps + PS_VID_OFF) 2 vid' ->
  nx_ps_at SEGS (rdW W' m') ps h sw ol vt' vid' pad.
Proof.
  intros W W' m m' ps h sw ol vt vid vt' vid' pad (P1 & P2 & P3 & P4 & P5 & P6 & P7) K V4 V5. unfold nx_ps_at.
  unfold PS_LEN, PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
  split; [eapply fa_vm_keep; [|exact P1]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply fa_vm_keep; [|exact P2]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [eapply fa_vm_keep; [|exact P3]; intros x Hx; apply K; cbn in Hx; lia|].
  split; [exact V4|]. split; [exact V5|].
  split; [eapply fa_garr8_keep; [|exact P6]; intros x Hx; apply K; rewrite P7 in Hx; cbn in Hx; lia|].
  exact P7.
Qed.

(* The windows of this phase's region lists: empty, or the struct's tag fields at s5. *)
Definition fa_win_ok (w : option nat * Z * Z) : bool :=
  match w with (b, lo, hi) => (hi <=? lo) || (YP09.obase_eqb b (Some 21%nat) && (lo =? PS_VT_OFF) && (hi =? PS_VID_OFF + 2)) end.

Lemma fa_kept_ps : forall E rs (H : word -> bool) (m m' : word -> option byte) ps,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> forallb fa_win_ok (windows rs) = true ->
  bv_unsigned (ew E 21) = ps ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (ps + PS_VT_OFF <= a < ps + PS_VID_OFF + 2) ->
  aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' ps HF Hw U21 a Ha Hn.
  apply (kept_of_frame E rs H m m' (fun a => ps + PS_VT_OFF <= a < ps + PS_VID_OFF + 2) HF); [|exact Ha | exact Hn].
  intros b wlo whi x Hin Hx. pose proof (proj1 (forallb_forall _ _) Hw _ Hin) as Hb. cbn in Hb.
  apply orb_true_iff in Hb as [Hb | Hb]; [apply Z.leb_le in Hb; lia|].
  apply andb_true_iff in Hb as [Hb Hhi]. apply andb_true_iff in Hb as [Hb Hlo].
  apply YP09.obase_eqb_eq in Hb. subst b. apply Z.eqb_eq in Hlo, Hhi. subst wlo whi.
  cbn [base_val] in Hx. rewrite U21 in Hx. lia.
Qed.

Lemma fa_chunk_val : forall E ss (ms : machine_state) i r off (w : N) e v,
  st_ok_pi SEGS VAL E ss ms -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (ms_mem ms) (base_val E (YP09.r_base r) + off) (N.to_nat w) v.
Proof.
  intros E ss ms i r off w e v HS Hi Hin He Hv Hw.
  pose proof (st_ok_pi_region_nth E ss ms i r HS Hi) as (_ & _ & _ & Hck).
  exact (val_of_chunk_ok SEGS E (ms_mem ms) _ off w e v (proj1 (Forall_forall _ _) Hck _ Hin) He Hv Hw).
Qed.

Lemma fa_grows_present : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
  intros H m m' a HG (HH & b & Hb). split; [exact HH|].
  specialize (HG (Z_to_bv 64 a)). unfold mrestrict in HG. rewrite HH in HG.
  destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  exfalso. apply HG; [rewrite Hb; discriminate | reflexivity].
Qed.

Lemma fa_sr_val : forall Ex ss (ms : machine_state) (H : word -> bool) (r : bv 5) e v,
  st_ok_pi SEGS VAL Ex ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot Ex e = v -> getr (ms_regs ms) r = v.
Proof. intros Ex ss ms H r e v HS He Hv. pose proof (st_ok_pi_restrict_reg H Ex ss ms r HS) as X. rewrite He, Hv in X. exact X. Qed.

Lemma fa_ew_xt : forall regs h buf F ts secw b12 b13 b14 b15 (j : nat) v,
  (j < 10)%nat -> nth j [SHADOW_OFF; h; buf; F; ts; secw; b12; b13; b14; b15] 0 = v ->
  ew (Eimg (Ereg regs (fa_extra h buf F ts secw b12 b13 b14 b15))) (32 + j) = Z_to_bv 64 v.
Proof.
  intros regs h buf F ts secw b12 b13 b14 b15 j v Hj Hv.
  rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. unfold fa_extra.
  change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth, Hv. reflexivity.
Qed.

Lemma fa_untagged_lt : forall sw F q, PSN.incl sw F q < 18 -> PSN.tagged sw F q = false.
Proof. intros sw F q H. unfold PSN.tagged. destruct (Z.leb_spec 18 (PSN.incl sw F q)); [lia | reflexivity]. Qed.

Ltac fa_rv HS r X :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss (restrict ?H ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    pose proof (fa_sr_val Ex ss msx H r e _ HS ltac:(clear; vm_compute; reflexivity) eq_refl) as X;
    cbn [sv_denot] in X; rewrite ?ew_ewset_other in X by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in X
  end.

(* The record's bytes 12 .. 15 in the buffer. *)
Lemma fa_buf_ok : forall E H mem buf b12 b13 b14 b15,
  bv_unsigned (ew E 34) = buf -> ew E 38 = Z_to_bv 64 b12 -> ew E 39 = Z_to_bv 64 b13 ->
  ew E 40 = Z_to_bv 64 b14 -> ew E 41 = Z_to_bv 64 b15 ->
  0 <= b12 < 256 -> 0 <= b13 < 256 -> 0 <= b14 < 256 -> 0 <= b15 < 256 -> 0 <= buf -> buf + 16 <= 2 ^ 64 ->
  val_mem SEGS (mrestrict H mem) (buf + 12) 1 b12 -> val_mem SEGS (mrestrict H mem) (buf + 13) 1 b13 ->
  val_mem SEGS (mrestrict H mem) (buf + 14) 1 b14 -> val_mem SEGS (mrestrict H mem) (buf + 15) 1 b15 ->
  YP09.region_ok SEGS E (mrestrict H mem) fa_buf.
Proof.
  intros E H mem buf b12 b13 b14 b15 U34 E38 E39 E40 E41 R12 R13 R14 R15 Hb0 Hb1 V12 V13 V14 V15.
  unfold YP09.region_ok, fa_buf. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  - apply (chunk_ok_val SEGS E (mrestrict H mem) buf 12 1%N (SOff 38 0) b12);
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V12].
  - apply (chunk_ok_val SEGS E (mrestrict H mem) buf 13 1%N (SOff 39 0) b13);
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V13].
  - apply (chunk_ok_val SEGS E (mrestrict H mem) buf 14 1%N (SOff 40 0) b14);
      [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V14].
  - apply (chunk_ok_val SEGS E (mrestrict H mem) buf 15 1%N (SOff 41 0) b15);
      [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia | exact V15].
Qed.

(* A shadow-table entry of [v, v + len) at atom n. *)
Lemma fa_shent_gen : forall E (m : word -> option byte) (n : nat) v len,
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E n = Z_to_bv 64 v -> 0 <= v -> 0 <= len -> v + len <= 2 ^ 47 ->
  amem_range v len ->
  range_addressable (rd_of SEGS m) SHADOW_OFF v len ->
  shent_ok SEGS fa_Bx E m (mkSHE n 0 len).
Proof.
  intros E m n v len E32 En Hv0 Hl0 Hv1 Hamr Hra. unfold shent_ok, app_apart. cbn [she_m she_lo she_hi]. unfold fa_Bx.
  rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia).
  rewrite (U_atom E n v En) by lia. split.
  - rewrite Z.add_0_r, Z.sub_0_r. exact Hra.
  - intros a Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, SHADOW_OFF in *. cbn in Ha. lia.
Qed.

Lemma fa_regs_ok2 : forall regs extra ps buf,
  nth 0 extra (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF -> nth 2 extra (Z_to_bv 64 0) = Z_to_bv 64 buf ->
  getr regs 21 = w64 ps -> getr regs 26 = w64 (shadow_of_addr SHADOW_OFF ps) -> getr regs 20 = w64 buf ->
  0 <= ps < 2 ^ 47 -> 0 <= buf < 2 ^ 64 ->
  regs_ok (Eimg (Ereg regs extra)) fa_sr2 regs.
Proof.
  intros regs extra ps buf H32 H34 R21 R26 R20 Hps Hbuf r.
  destruct (decide (r = 20%bv)) as [->|Hne].
  - change fa_sr2 with (sr_set fa_sr 20%bv (SOff 34 0)). rewrite sr_get_set_same by reflexivity.
    cbn [sv_denot]. rewrite Eimg_low by (unfold A_TEXT; lia). change 34%nat with (32 + 2)%nat.
    rewrite ew_Ereg_extra, H34, unsigned_lit_small by lia. rewrite Z.add_0_r, R20. reflexivity.
  - change fa_sr2 with (sr_set fa_sr 20%bv (SOff 34 0)). rewrite sr_get_set_other by exact Hne.
    exact (fa_regs_ok regs extra ps H32 R21 R26 Hps r).
Qed.

Lemma fa_ps0_ok : forall E H mem ps h,
  bv_unsigned (ew E 21) = ps -> ew E 33 = Z_to_bv 64 h -> 0 <= h < 2 ^ 64 -> 0 <= ps -> ps + PS_LEN <= 2 ^ 64 ->
  val_mem SEGS (mrestrict H mem) ps 8 h ->
  (forall a, ps + PS_VT_OFF <= a < ps + PS_VID_OFF + 2 -> apresent H mem a) ->
  val_mem SEGS (mrestrict H mem) (ps + PS_VT_OFF) 4 0 -> val_mem SEGS (mrestrict H mem) (ps + PS_VID_OFF) 2 0 ->
  YP09.region_ok SEGS E (mrestrict H mem) fa_ps0.
Proof.
  intros E H mem ps h U21 E33 Hh Hp0 Hp1 Hv Hw V16 V20.
  unfold YP09.region_ok, fa_ps0. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U21. unfold PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
  split; [lia|]. split; [lia|]. split.
  { intros o Ho. apply (apresent_writable SEGS). apply Hw. lia. }
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - apply (chunk_ok_val SEGS E (mrestrict H mem) ps 0 8%N (SOff 33 0) h).
    + cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
    + cbn [Z.of_N]. change (8 * 8) with 64. exact Hh.
    + cbn [Z.of_N]. lia.
    + rewrite Z.add_0_r. exact Hv.
  - apply (chunk_ok_val SEGS E (mrestrict H mem) ps 16 4%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V16].
  - apply (chunk_ok_val SEGS E (mrestrict H mem) ps 20 2%N (SLit 0) 0); [reflexivity | cbn; lia | cbn; lia | exact V20].
Qed.

Lemma fa_untagged_12 : forall sw F q, PSN.fb F (q + 28) <> 129 -> PSN.tagged sw F q = false.
Proof. intros sw F q H. unfold PSN.tagged. destruct (Z.eqb_spec (PSN.fb F (q + 28)) 129); [lia|]. destruct (_ <=? _); reflexivity. Qed.
Lemma fa_untagged_13 : forall sw F q, PSN.fb F (q + 29) <> 0 -> PSN.tagged sw F q = false.
Proof. intros sw F q H. unfold PSN.tagged. destruct (Z.eqb_spec (PSN.fb F (q + 29)) 0); [lia|]. apply andb_false_r. Qed.
Lemma fa_tagged : forall sw F q, 18 <= PSN.incl sw F q -> PSN.fb F (q + 28) = 129 -> PSN.fb F (q + 29) = 0 ->
  PSN.tagged sw F q = true.
Proof. intros sw F q H1 H2 H3. unfold PSN.tagged. rewrite H2, H3. destruct (Z.leb_spec 18 (PSN.incl sw F q)); [reflexivity | lia]. Qed.

Lemma fa_regs_ok3 : forall regs extra ps buf,
  nth 0 extra (Z_to_bv 64 0) = Z_to_bv 64 SHADOW_OFF -> nth 2 extra (Z_to_bv 64 0) = Z_to_bv 64 buf ->
  getr regs 21 = w64 ps -> getr regs 26 = w64 (shadow_of_addr SHADOW_OFF ps) -> getr regs 20 = w64 buf ->
  getr regs 10 = w64 (ps + 20) -> getr regs 12 = w64 (ps + 16) ->
  getr regs 14 = w64 (shadow_of_addr SHADOW_OFF (ps + 20)) -> getr regs 15 = w64 (shadow_of_addr SHADOW_OFF (ps + 16)) ->
  0 <= ps < 2 ^ 47 - 24 -> 0 <= buf < 2 ^ 64 ->
  regs_ok (Eimg (Ereg regs extra)) fa_sr3 regs.
Proof.
  intros regs extra ps buf H32 H34 R21 R26 R20 R10 R12 R14 R15 Hps Hbuf r.
  assert (E21 : ew (Eimg (Ereg regs extra)) 21 = Z_to_bv 64 ps)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs extra 21 21%bv eq_refl); exact R21).
  assert (E32 : ew (Eimg (Ereg regs extra)) 32 = Z_to_bv 64 SHADOW_OFF)
    by (rewrite Eimg_low by (unfold A_TEXT; lia); rewrite <- H32; exact (ew_Ereg_extra regs extra 0)).
  destruct (decide (r = 10%bv)) as [->|N10].
  { change (sr_get fa_sr3 10%bv) with (SOff 21 20). rewrite R10, denot_lit_U.
    rewrite U_off by (rewrite E21, unsigned_lit_small by lia; unfold M64; lia). rewrite E21, unsigned_lit_small by lia.
    reflexivity. }
  destruct (decide (r = 12%bv)) as [->|N12].
  { change (sr_get fa_sr3 12%bv) with (SOff 21 16). rewrite R12, denot_lit_U.
    rewrite U_off by (rewrite E21, unsigned_lit_small by lia; unfold M64; lia). rewrite E21, unsigned_lit_small by lia.
    reflexivity. }
  destruct (decide (r = 14%bv)) as [->|N14].
  { change (sr_get fa_sr3 14%bv) with (fa_shx 20). rewrite denot_lit_U, (fa_U_shx_k _ ps 20 E21 E32) by lia. exact R14. }
  destruct (decide (r = 15%bv)) as [->|N15].
  { change (sr_get fa_sr3 15%bv) with (fa_shx 16). rewrite denot_lit_U, (fa_U_shx_k _ ps 16 E21 E32) by lia. exact R15. }
  change fa_sr3 with
    (sr_set (sr_set (sr_set (sr_set fa_sr2 10%bv (SOff 21 20)) 12%bv (SOff 21 16)) 14%bv (fa_shx 20)) 15%bv (fa_shx 16)).
  rewrite (sr_get_set_other _ 15%bv) by exact N15. rewrite (sr_get_set_other _ 14%bv) by exact N14.
  rewrite (sr_get_set_other _ 12%bv) by exact N12. rewrite (sr_get_set_other _ 10%bv) by exact N10.
  exact (fa_regs_ok2 regs extra ps buf H32 H34 R21 R26 R20 ltac:(lia) Hbuf r).
Qed.

Lemma fa_chunk_val_st : forall E ss (ms : machine_state) i r off (w : N) e v,
  st_ok SEGS E ss ms -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal w e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
  val_mem SEGS (ms_mem ms) (base_val E (YP09.r_base r) + off) (N.to_nat w) v.
Proof.
  intros E ss ms i r off w e v HS Hi Hin He Hv Hw.
  pose proof (st_ok_region_nth E ss ms i r HS Hi) as (_ & _ & _ & Hck).
  exact (val_of_chunk_ok SEGS E (ms_mem ms) _ off w e v (proj1 (Forall_forall _ _) Hck _ Hin) He Hv Hw).
Qed.

Lemma fa_aview_present : forall (H : word -> bool) (m : word -> option byte) a,
  apresent H m a -> aview SEGS H m a <> None.
Proof.
  intros H m a (HH & b & Hb). unfold aview. unfold YP09.mbyte, mrestrict. rewrite HH, Hb. discriminate.
Qed.

(* A run whose regions carry no write window keeps every byte. *)
Lemma fa_kept_all : forall E rs (H : word -> bool) (m m' : word -> option byte),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  forallb (fun w => match w with (_, lo, hi) => hi <=? lo end) (windows rs) = true ->
  forall a, 0 <= a < 2 ^ 64 -> aview SEGS H m' a = aview SEGS H m a.
Proof.
  intros E rs H m m' HF Hw a Ha.
  apply (kept_of_frame E rs H m m' (fun _ => False) HF); [|exact Ha | intros []].
  intros b wlo whi x Hin Hx. pose proof (proj1 (forallb_forall _ _) Hw _ Hin) as Hb. cbn in Hb.
  apply Z.leb_le in Hb. lia.
Qed.

Lemma fa_sr_val_st : forall Ex ss (ms : machine_state) (H : word -> bool) (r : bv 5) e v,
  st_ok SEGS Ex ss (restrict H ms) -> sr_get (ss_regs ss) r = e -> sv_denot Ex e = v -> getr (ms_regs ms) r = v.
Proof. intros Ex ss ms H r e v HS He Hv. pose proof (st_ok_restrict_reg SEGS H Ex ss ms r HS) as X. rewrite He, Hv in X. exact X. Qed.

Ltac fa_rv_st HS r X :=
  lazymatch type of HS with st_ok _ ?Ex ?ss (restrict ?H ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    pose proof (fa_sr_val_st Ex ss msx H r e _ HS ltac:(clear; vm_compute; reflexivity) eq_refl) as X;
    cbn [sv_denot] in X; rewrite ?ew_ewset_other in X by lia; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in X
  end.

Lemma fa_U_len16 : forall E s6v, ew E 22 = Z_to_bv 64 s6v -> 16 <= s6v < 2 ^ 32 ->
  U E (SAlu ALU_SRL (SAlu ALU_ADD (SAlu ALU_SLL (SOff 22 0) (SLit 32)) (SLit (-68719476736))) (SLit 32)) = s6v - 16.
Proof.
  intros E s6v H22 Hs. rewrite !U_SAlu. rewrite (U_atom E 22 s6v H22) by lia. rewrite !U_SLit.
  cbn [zalu_raw]. unfold zcanon, M64 in *.
  change (Z.land (32 mod 2 ^ 64) 63) with 32. change (-68719476736 mod 2 ^ 64) with (2 ^ 64 - 2 ^ 36).
  rewrite Z.shiftl_mul_pow2 by lia. rewrite Z.shiftr_div_pow2 by lia.
  rewrite (Z.mod_small (s6v * 2 ^ 32)) by (split; [lia | apply (Z.lt_le_trans _ (2 ^ 32 * 2 ^ 32)); [nia | lia]]).
  replace (s6v * 2 ^ 32 + (2 ^ 64 - 2 ^ 36)) with ((s6v - 16) * 2 ^ 32 + 1 * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia.
  rewrite (Z.mod_small ((s6v - 16) * 2 ^ 32)) by (split; [lia | apply (Z.lt_le_trans _ (2 ^ 32 * 2 ^ 32)); [nia | lia]]).
  rewrite Z.div_mul by lia. apply Z.mod_small. lia.
Qed.

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASIL : @asource_img_laws SK SEGS B KS.
Hypothesis H_fread :
  afread_spec SK SEGS B KS (SIGMA PS___interceptor_trampoline_fread).        (* 0x819a4 *)
Hypothesis H_memmove : amemmove_realizes SEGS B (SIGMA PS___asan_memmove).  (* 0x81af4 *)
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* ---------------------------------------------------------------------------------------------- *)
(* Where the bytes the call may write lie, against this call's own frame and the stack             *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma fa_E_apart : forall cx fp ly3 S3 W3 mem3 md3,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  AR SEGS B ly3 S3 W3 mem3 md3 -> frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) ->
  forall a, nx_E cx a ->
    4096 <= a < alloc_ceiling /\ ~ (nF cx fp <= a < nF cx fp + 64) /\
    ~ (kLowMemEnd <= a < kHighShadowEnd) /\ ~ in_img SEGS a.
Proof.
  intros cx fp ly3 S3 W3 mem3 md3 HB Hh HAR3 HFR Hab EFA a HE.
  pose proof (fa_E_low B KS cx LAWS HB Hh a HE) as Hlow.
  pose proof HB as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hps4 & _ & _ & Hpsown
    & Hpsf1 & Hpsf2 & _ & _ & _ & _ & _ & HBUFB & HTSB & HSTR & _).
  pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HFB : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
  (* a frame of the caller and this call's frame are apart *)
  assert (Dfr : forall c p, In (c, p) (n_own cx) ->
     frame_addr (n_lyc cx) c p + fs_frame_bytes c <= nF cx fp \/ nF cx fp + 64 <= frame_addr (n_lyc cx) c p).
  { intros c p Hin. apply in_split in Hin as (o1 & o2 & Eo).
    assert (Hfr : frames S3 = [] ++ (NX_CID, fp) :: o1 ++ (c, p) :: (o2 ++ frames (n_S cx))).
    { rewrite HFR, Hfrsc, Eo. cbn. rewrite <- app_assoc. reflexivity. }
    pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 mem3 md3 _ _ _ _ _ HAR3 Hfr) as D.
    unfold zdisjoint, frame_rng in D. cbn [fst snd] in D. rewrite !EFA, HFB in D. unfold nF. lia. }
  (* a block and this call's frame are apart *)
  assert (Dbl : forall p n, In (p, n) (ablocks B (n_lyc cx) (n_Sc cx)) ->
     p + req_size n <= nF cx fp \/ nF cx fp + 64 <= p).
  { intros p n Hin. rewrite <- Hab in Hin.
    assert (HinF : In (NX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
    pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 mem3 md3 p n NX_CID fp HAR3 Hin HinF) as D.
    unfold zdisjoint in D. cbn [fst snd] in D. rewrite EFA, HFB in D. unfold nF. lia. }
  unfold nx_E, nx_wrset in HE. destruct HE as [Ha | [Ha | [(Ht & Ha) | (_ & Ha)]]].
  - assert (Hin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hpsown).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & Happ).
    pose proof (frm_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Hoff.
    pose proof (Dfr _ _ Hpsown) as D. clear Dfr Dbl HBUFB HTSB HSTR HB HJc.
    unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP, PS_LEN in *.
    split; [exact Hlow|]. split; [lia|]. split; [lia|].
    intros Hi. pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
  - destruct (HBUFB Hh) as (Hin & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & _ & Happ & _).
    pose proof (blk_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Hoff.
    pose proof (Dbl _ _ Hin) as D. clear Dfr Dbl HBUFB HTSB HSTR HB HJc.
    pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hq].
    unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    split; [exact Hlow|]. split; [lia|]. split; [lia|].
    intros Hi. pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
  - destruct (HTSB Hh Ht) as (_ & _ & _ & _ & _ & (tcid & tpos & Htin & Ht1 & Ht2) & _).
    assert (Hin : In (tcid, tpos) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Htin).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & Happ).
    pose proof (frm_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Hoff.
    pose proof (Dfr _ _ Htin) as D. clear Dfr Dbl HBUFB HTSB HSTR HB HJc.
    unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    split; [exact Hlow|]. split; [lia|]. split; [lia|].
    intros Hi. pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
  - destruct (HSTR Hh) as (Hin & _).
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & _ & _ & Happ & _).
    pose proof (blk_off_imgP B _ _ _ _ _ _ _ HARc Hin) as Hoff.
    pose proof (Dbl _ _ Hin) as D. clear Dfr Dbl HBUFB HTSB HSTR HB HJc.
    change (req_size SRC_FILE_BLOCK) with 1304 in *. unfold SRC_FILE_BLOCK in Ha.
    unfold in_app, off_img, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, YImgTop.IMG_LO, YImgTop.IMG_TOP in *.
    split; [exact Hlow|]. split; [lia|]. split; [lia|].
    intros Hi. pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr. lia.
Qed.

(* The bytes a step must keep for the middle state to move: the stack from the heap ceiling up, the
   image bytes the caller's journal keeps, the shadow band, the caller's blocks, and the frames of the
   state (this call's and the caller's). *)
Definition fa_zone (ly : alayout) (S : astate) (a : Z) : Prop :=
  alloc_ceiling <= a \/
  (in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) \/
  (kLowMemEnd <= a < kHighShadowEnd) \/
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= a < b + req_size m) \/
  (exists cid pos, In (cid, pos) (frames S) /\ in_zr a (frame_rng ly (cid, pos))).

(* ---------------------------------------------------------------------------------------------- *)
(* Moving the middle state across a step that kept the body and wrote only bytes of nx_E           *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma fa_body_move : forall cx fp pc pc' (W W' : world SEGS) (ms ms' : machine_state) sh,
  nx_body cx fp pc W ms sh ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  (forall r, In r [2; 3; 4; 8; 9; 25]%bv -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  0 <= n_sp1 cx -> n_sp1 cx + 256 <= spZ (n_regs cx) ->
  (forall a, (n_sp1 cx <= a < spZ (n_regs cx)) \/ (nF cx fp <= a < nF cx fp + 64) \/
             (nSH cx fp <= a < nSH cx fp + 8) ->
     aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  nx_body cx fp pc' W' ms' sh.
Proof.
  intros cx fp pc pc' W W' ms ms' sh
    ((Hpc & Hrv & Hsv & Hrom & Hfr & Hfc & (G2 & G8 & G9 & G3 & G4) & (SV1 & SV2) & (H0 & H8 & H16) & HFL & HSH
      & Hlen & G25 & HFK) & HSL) Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' KR Hs0 Hs1 KM.
  assert (RW : forall a v, (forall k, 0 <= k < 8 -> (n_sp1 cx <= a + k < spZ (n_regs cx)) \/
                 (nF cx fp <= a + k < nF cx fp + 64) \/ (nSH cx fp <= a + k < nSH cx fp + 8)) ->
     rdword (aview SEGS (w_H W) (ms_mem ms)) a = Some v -> rdword (aview SEGS (w_H W') (ms_mem ms')) a = Some v).
  { intros a v Ha Hv. rewrite <- Hv. apply rdword_ext. intros k Hk. apply KM. apply Ha. exact Hk. }
  assert (RS : forall off v, 0 <= off <= 120 -> nslot cx W ms off v -> nslot cx W' ms' off v).
  { intros off v Ho Hv. unfold nslot in *. apply (RW _ v); [intros k Hk; left; lia | exact Hv]. }
  assert (RF : forall off v, 0 <= off <= 56 -> rdword (aview SEGS (w_H W) (ms_mem ms)) (nF cx fp + off) = Some v ->
     rdword (aview SEGS (w_H W') (ms_mem ms')) (nF cx fp + off) = Some v).
  { intros off v Ho Hv. apply (RW _ v); [intros k Hk; right; left; lia | exact Hv]. }
  split.
  - split; [exact Hpc'|]. split; [exact Hrv'|]. split; [exact Hsv'|]. split; [exact Hrom'|].
    split; [exact Hfr'|]. split; [exact Hfc'|].
    split.
    { unfold nregs. rewrite !KR by (cbn; tauto). repeat split; assumption. }
    split.
    { split.
      - apply (RW _ _); [intros k Hk; left; lia | exact SV1].
      - intros j Hj. apply (RW _ _); [intros k Hk; left; lia | exact (SV2 j Hj)]. }
    split.
    { unfold nheader. split; [|split].
      - rewrite <- (Z.add_0_r (nF cx fp)). apply RF; [lia|]. rewrite Z.add_0_r. exact H0.
      - apply RF; [lia | exact H8].
      - apply RF; [lia | exact H16]. }
    split; [unfold nflagw in *; apply RF; [unfold NX_FLAGPTR; lia | exact HFL]|].
    split.
    { unfold nshadow in *. intros i Hi. rewrite KM; [exact (HSH i Hi)|]. right; right.
      rewrite Hlen in Hi. unfold NX_NSH in Hi. lia. }
    split; [exact Hlen|].
    split; [rewrite KR by (cbn; tauto); exact G25|].
    apply RS; [unfold NS_FK; lia | exact HFK].
  - unfold nslots in *.
    destruct HSL as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12).
    unfold NS_FK, NS_F0, NS_BUF, NS_TS, NS_SB, NS_PS12, NS_SH12, NS_OFF8, NS_OFF12, NS_PH4, NS_PH8, NS_PH12 in *.
    repeat split; (apply RS; [lia | assumption]).
Qed.

Lemma fa_kept_step : forall cx ly3 S3 (W1 : world SEGS) m1 (W2 : world SEGS) m2 (E Wr : Z -> Prop) lo hi,
  nx_base SK B KS cx ->
  (forall c p, In (c, p) (frames (n_Sc cx)) -> In (c, p) (frames S3)) ->
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) ->
  ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W1 m1 (spZ (n_regs cx)) E ->
  spZ (n_regs cx) - NX_STK_B <= lo -> hi <= spZ (n_regs cx) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ Wr a -> fa_zone ly3 S3 a ->
     aview SEGS (w_H W2) m2 a = aview SEGS (w_H W1) m1 a) ->
  (forall a, Wr a -> a < alloc_ceiling /\ ~ in_img SEGS a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     apresent (w_H W1) m1 a -> apresent (w_H W2) m2 a) ->
  (forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) -> apresent (w_H W2) m2 a) ->
  nx_kept SEGS NX_STK_B B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W2 m2 (spZ (n_regs cx)) (fun a => E a \/ Wr a).
Proof.
  intros cx ly3 S3 W1 m1 W2 m2 E Wr lo hi HB HSF EFA Hab (K1 & K2 & K3 & K4 & K5 & K6) Hlo Hhi HUN HWr HP1 HP2.
  pose proof HB as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hwlo & Hwhi & _).
  pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
  pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK_B = 8464) by reflexivity.
  split.
  { intros a Ha Hw Hn. rewrite (HUN a ltac:(lia) ltac:(lia) ltac:(intros X; apply Hn; right; exact X) ltac:(left; lia)).
    apply K1; [exact Ha | exact Hw | intros X; apply Hn; left; exact X]. }
  split.
  { intros b m i Hb Hi Hn.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hb) as (_ & Hb4 & Hbc & _).
    rewrite (HUN (b + i) ltac:(lia) ltac:(lia) ltac:(intros X; apply Hn; right; exact X)
      ltac:(right; right; right; left; exists b, m; split; [rewrite Hab; exact Hb | lia])).
    apply (K2 b m i); [exact Hb | exact Hi | intros X; apply Hn; left; exact X]. }
  split.
  { intros a Hi Ho He. pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
    rewrite (HUN a ltac:(lia) ltac:(lia) ltac:(intros X; exact (proj2 (HWr a X) Hi)) ltac:(right; left; tauto)).
    exact (K3 a Hi Ho He). }
  split.
  { intros cid pos a Hin Hr Hn.
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ cid pos HARc Hin) as (Hf4 & Hfc & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hnn.
    pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) cid pos) ltac:(lia)) as Hsb1.
    pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) cid pos + fs_frame_bytes cid) ltac:(lia)) as Hsb2.
    pose proof (shadow_range_end (frame_addr (n_lyc cx) cid pos) (fs_frame_bytes cid) Hnn) as Hse.
    assert (Ha : 0 <= a < alloc_ceiling) by (unfold frame_rng, in_zr in Hr; cbn [fst snd] in Hr; destruct Hr; lia).
    assert (Hz : fa_zone ly3 S3 a).
    { destruct Hr as [Hr | Hr].
      - right; right; right; right. exists cid, pos. split; [exact (HSF _ _ Hin)|].
        unfold frame_rng, in_zr in *. cbn [fst snd] in *. rewrite EFA. exact Hr.
      - right; right; left. unfold in_zr in Hr. cbn [fst snd] in Hr. lia. }
    rewrite (HUN a ltac:(lia) ltac:(lia) ltac:(intros X; apply Hn; right; exact X) Hz).
    apply (K4 cid pos a Hin Hr); intros X; apply Hn; left; exact X. }
  split.
  { intros a Ha Hw Hp. apply HP1; [exact Ha | lia | exact (K5 a Ha Hw Hp)]. }
  exact HP2.
Qed.

Lemma fa_mid_step : forall cx fp pc pc' sh (E E' : Z -> Prop) q q' ol ol' vt vt' vid vid' tv k2 ly3 S3
  (W : world SEGS) (ms : machine_state) md (W' : world SEGS) (ms' : machine_state) md' lo hi (Wr : Z -> Prop),
  nx_base SK B KS cx ->
  nx_mid B MT KS cx fp pc sh E q ol vt vid tv k2 ly3 S3 W ms md ->
  AR SEGS B ly3 S3 W (ms_mem ms) md -> frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  (forall r, In r [2; 3; 4; 8; 9; 21; 23; 25; 26; 27]%bv -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  n_sp1 cx - AFREAD_STK <= lo -> hi <= n_sp1 cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> ~ Wr a -> fa_zone ly3 S3 a ->
     aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  (forall a, Wr a -> nx_E cx a) ->
  (forall a, E a \/ Wr a -> E' a) -> (forall a, E' a -> nx_E cx a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     apresent (w_H W) (ms_mem ms) a -> apresent (w_H W') (ms_mem ms') a) ->
  (forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) -> apresent (w_H W') (ms_mem ms') a) ->
  nx_jbk B MT cx k2 ly3 S3 md' ->
  nx_ps_at SEGS (rdW W' (ms_mem ms')) (n_ps cx) (n_h cx) (n_sw cx) ol' vt' vid' (n_pad cx) ->
  asource_at SEGS KS (rdW W' (ms_mem ms')) (n_h cx) (n_b cx) (n_C cx) q' ->
  n_p cx <= q' <= Z.of_nat (length (n_C cx)) ->
  (exists bj', garr8 SEGS (rdW W' (ms_mem ms')) (n_buf cx) bj' /\ length bj' = length (n_bj cx)) ->
  (n_ts cx <> 0 -> val_mem SEGS (rdW W' (ms_mem ms')) (n_ts cx) 8 tv) ->
  nx_mid B MT KS cx fp pc' sh E' q' ol' vt' vid' tv k2 ly3 S3 W' ms' md'.
Proof.
  intros cx fp pc pc' sh E E' q q' ol ol' vt vt' vid vid' tv k2 ly3 S3 W ms md W' ms' md' lo hi Wr
    HB HM HAR3 HFR EFA Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' KR Hlo Hhi HUN HWr HEE' HE'n HP1 HP2 HJBK' HPS' HSRC' Hq' HBUF' HTS'.
  destruct HM as (HBD & R21 & R23 & R26 & R27 & HJBK & HK & HEs & Hh & HPS & HRA & HSRC & Hq & HBUF & HTS).
  pose proof HB as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & _ & _ & Hps4 & Hps47 & _).
  pose proof HJc as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
  pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK_B = 8464) by reflexivity.
  pose proof (NX_STK_B_frame (spZ (n_regs cx)) Hal16) as ((Hsp1lo & Hsp1hi) & _).
  change (nx_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1lo, Hsp1hi. unfold NX_MFRAME in Hsp1hi.
  unfold AFREAD_STK in Hlo.
  pose proof HJBK as (_ & Hab & _).
  pose proof (fa_E_apart cx fp ly3 S3 W (ms_mem ms) md HB Hh HAR3 HFR Hab EFA) as HAP.
  (* this call's frame and its shadow lie in [4096, alloc_ceiling) *)
  assert (HinF : In (NX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds SEGS B LAWS ly3 S3 W (ms_mem ms) md NX_CID fp HAR3 HinF) as (HF4096 & HFceil & _).
  assert (HFB : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
  rewrite EFA in HF4096. rewrite EFA, HFB in HFceil.
  change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in HF4096, HFceil.
  assert (HSHa : nSH cx fp = SHADOW_OFF + nF cx fp / 8) by reflexivity.
  assert (HSHr : kLowMemEnd <= nSH cx fp /\ nSH cx fp + 8 <= kHighShadowEnd).
  { rewrite HSHa. assert (nF cx fp / 8 + 8 <= 2 ^ 44) by (apply (Z.le_trans _ ((nF cx fp + 64) / 8)); [apply (Z.le_trans _ (nF cx fp / 8 + 8)); [lia|];
      replace (nF cx fp + 64) with (nF cx fp + 8 * 8) by lia; rewrite Z.div_add by lia; lia | apply Z.div_le_upper_bound; lia]).
    unfold SHADOW_OFF in *. pose proof (Z.div_pos (nF cx fp) 8 ltac:(lia) ltac:(lia)). lia. }
  assert (KM : forall a, 0 <= a < 2 ^ 64 -> a < lo \/ hi <= a -> (alloc_ceiling <= a \/ (kLowMemEnd <= a < kHighShadowEnd) \/
     (nF cx fp <= a < nF cx fp + 64)) ->
     aview SEGS (w_H W') (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a).
  { intros a Ha Hlh Hz. apply HUN; [exact Ha | lia | |].
    - intros X. destruct (HAP a (HWr a X)) as (Ha1 & Ha2 & Ha3 & _). destruct Hz as [Hz | [Hz | Hz]]; lia.
    - destruct Hz as [Hz | [Hz | Hz]]; [left; exact Hz | right; right; left; exact Hz |].
      right; right; right; right. exists NX_CID, fp. split; [exact HinF|]. unfold in_zr, frame_rng. cbn [fst snd].
      rewrite HFB, EFA. exact Hz. }
  split.
  { apply (fa_body_move cx fp pc pc' W W' ms ms' sh HBD Hpc' Hrv' Hsv' Hrom' Hfr' Hfc');
      [intros r Hr; apply KR; cbn in Hr |- *; tauto | lia | lia |].
    intros a [Ha | [Ha | Ha]]; apply KM; lia. }
  split; [rewrite KR by (cbn; tauto); exact R21|]. split; [rewrite KR by (cbn; tauto); exact R23|].
  split; [rewrite KR by (cbn; tauto); exact R26|]. split; [rewrite KR by (cbn; tauto); exact R27|].
  split; [exact HJBK'|].
  split.
  { apply (nx_kept_mono SEGS NX_STK_B B _ _ _ _ _ _ _ (fun a => E a \/ Wr a) E' HEE').
    apply (fa_kept_step cx ly3 S3 W (ms_mem ms) W' (ms_mem ms') E Wr lo hi HB); [ | exact EFA | exact Hab | exact HK | lia | lia | exact HUN | | exact HP1 | exact HP2].
    { intros c p Hin. rewrite HFR. right. exact Hin. }
    intros a X. destruct (HAP a (HWr a X)) as (Ha1 & _ & _ & Ha4). split; [lia | exact Ha4]. }
  split; [exact HE'n|]. split; [exact Hh|]. split; [exact HPS'|].
  assert (KSH : forall x, 0 <= x < 2 ^ 47 ->
     aview SEGS (w_H W') (ms_mem ms') (shadow_of_addr SHADOW_OFF x) = aview SEGS (w_H W) (ms_mem ms) (shadow_of_addr SHADOW_OFF x)).
  { intros x Hx. assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
    apply KM; unfold shadow_of_addr, SHADOW_OFF in *; lia. }
  split.
  { apply (range_addressable_agree (aview SEGS (w_H W) (ms_mem ms))); [|exact HRA].
    intros x Hx. apply KSH. unfold PS_LEN in *. lia. }
  split; [exact HSRC'|]. split; [exact Hq'|]. split; [exact HBUF'|].
  intros T0. destruct (HTS T0) as (_ & HRAt). split; [exact (HTS' T0)|].
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTSB & _).
  destruct (HTSB Hh T0) as (_ & _ & Ht4 & Ht47 & _).
  apply (range_addressable_agree (aview SEGS (w_H W) (ms_mem ms))); [|exact HRAt].
  intros x Hx. apply KSH. lia.
Qed.

(* NP_exit from the middle state there: the post's memory and result for a record that does not fit. *)
Lemma fa_exit_of_mid : forall cx fp k2 ly3 S3 (W3 : world SEGS) (ms3 : machine_state) md3 (E : Z -> Prop) pos ol vt vid tv,
  nx_mid B MT KS cx fp NP_exit NSH_ph E pos ol vt vid tv k2 ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) 19 = w64 (nF cx fp) -> getr (ms_regs ms3) 16 = w64 (nF cx fp) ->
  pos = nx_pos (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) ->
  ol = nx_orig (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lol cx) ->
  vt = nx_vtag (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvt cx) ->
  vid = nx_vid (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvid cx) ->
  tv = nx_tsv (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_tsv cx) ->
  nx_fit (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = false ->
  getr (ms_regs ms3) 11 = w64 (nx_res (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)) ->
  nx_exit_inv B MT KS cx fp k2 ly3 S3 W3 ms3 md3.
Proof.
  intros cx fp k2 ly3 S3 W3 ms3 md3 E pos ol vt vid tv HM R19 R16 Epos Eol Evt Evid Etv Hnf R11.
  destruct HM as (HBD & _ & _ & _ & _ & HJBK & HK & HEs & Hh & HPS & _ & HSRC & _ & (bj' & Hg & Hlb) & HTS).
  unfold nx_exit_inv. split; [exact HBD|]. split; [exact R19|]. split; [exact R16|]. split; [exact HJBK|].
  unfold nx_fin_at, nx_fin. right.
  split; [exact Hh|]. split; [exact R11|].
  split; [exact (nx_kept_mono SEGS NX_STK_B B _ _ _ _ _ _ _ E _ HEs HK)|].
  split; [rewrite <- Epos; exact HSRC|].
  split; [rewrite <- Eol, <- Evt, <- Evid; exact HPS|].
  split; [exists bj'; split; [exact Hg|]; split; [exact Hlb | intros X; rewrite Hnf in X; discriminate X]|].
  intros T0. rewrite <- Etv. exact (proj1 (HTS T0)).
Qed.

(* The symbolic state of a cut of this phase, from the middle state there. *)
Lemma fa_seat : forall cx fp pc sh E qq ol vt vid tv k2 ly3 S3 (W : world SEGS) (ms : machine_state) md
    secw b12 b13 b14 b15 (pw : bool),
  nx_base SK B KS cx ->
  nx_mid B MT KS cx fp pc sh E qq ol vt vid tv k2 ly3 S3 W ms md ->
  nslot cx W ms NS_SEC secw ->
  0 <= b12 < 256 -> 0 <= b13 < 256 -> 0 <= b14 < 256 -> 0 <= b15 < 256 ->
  (pw = true -> forall a, n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2 -> apresent (w_H W) (ms_mem ms) a) ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) (fa_extra (n_h cx) (n_buf cx) (nF cx fp) (n_ts cx) secw b12 b13 b14 b15)))
    (mkSS pc fa_sr [fa_spill; fa_ps pw] None fa_G) (restrict (w_H W) ms) /\
  sh_ok SEGS fa_Bx fa_SH1 (Eimg (Ereg (ms_regs ms) (fa_extra (n_h cx) (n_buf cx) (nF cx fp) (n_ts cx) secw b12 b13 b14 b15)))
    (rdW W (ms_mem ms)).
Proof.
  intros cx fp pc sh E qq ol vt vid tv k2 ly3 S3 W ms md secw b12 b13 b14 b15 pw HB HM HSEC Hb12 Hb13 Hb14 Hb15 HW.
  destruct HM as (HBD & R21 & R23 & R26 & R27 & HJBK & HK & HEs & Hh & HPS & HRA & HSRC & Hqr & HBUF & HTS).
  destruct HBD as (HBD0 & HSL).
  destruct HBD0 as (Hpc & Hresv & Hpend & Hrom & Hfr & Hfcsr & HREGS & HSAV & HHDR & HFLW & HSH & Hlen & R25 & HFK0).
  destruct HREGS as (R2 & R8 & R9 & R3 & R4).
  pose proof HSL as (S_FK & S_F0 & S_BUF & S_TS & S_SB & S_PS12 & S_SH12 & S_OFF8 & S_OFF12 & S_PH4 & S_PH8 & S_PH12).
  pose proof HB as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & Hh64 & Hps8 & Hps4
    & Hps47 & Hpsamr & Hpsown & Hpsf1 & Hpsf2 & _ & _ & _ & _ & _ & HBUFB & _).
  pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
  assert (Hpsceil : n_ps cx + PS_LEN <= alloc_ceiling).
  { assert (Hin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hpsown).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hc & _). lia. }
  pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK_B = 8464) by reflexivity.
  pose proof (NX_STK_B_frame (spZ (n_regs cx)) Hal16) as ((Hsp1lo & Hsp1hi) & _).
  change (nx_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1lo, Hsp1hi. unfold NX_MFRAME in Hsp1hi.
  destruct (HBUFB Hh) as (Hbufin & Hbuf4 & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hbufin) as (_ & _ & Hbceil & _).
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrq].
  set (XTe := fa_extra (n_h cx) (n_buf cx) (nF cx fp) (n_ts cx) secw b12 b13 b14 b15).
  set (Ee := Eimg (Ereg (ms_regs ms) XTe)).
  assert (EXe : forall j, (j < 10)%nat -> ew Ee (32 + j) = nth j XTe (Z_to_bv 64 0))
    by (intros j Hj; unfold Ee; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (Ee_32 : ew Ee 32 = Z_to_bv 64 SHADOW_OFF) by exact (EXe 0%nat ltac:(lia)).
  assert (Ee_33 : ew Ee 33 = Z_to_bv 64 (n_h cx)) by exact (EXe 1%nat ltac:(lia)).
  assert (Ee_34 : ew Ee 34 = Z_to_bv 64 (n_buf cx)) by exact (EXe 2%nat ltac:(lia)).
  assert (Ee_35 : ew Ee 35 = Z_to_bv 64 (nF cx fp)) by exact (EXe 3%nat ltac:(lia)).
  assert (Ee_36 : ew Ee 36 = Z_to_bv 64 (n_ts cx)) by exact (EXe 4%nat ltac:(lia)).
  assert (Ee_37 : ew Ee 37 = Z_to_bv 64 secw) by exact (EXe 5%nat ltac:(lia)).
  assert (Ee_38 : ew Ee 38 = Z_to_bv 64 b12) by exact (EXe 6%nat ltac:(lia)).
  assert (Ee_39 : ew Ee 39 = Z_to_bv 64 b13) by exact (EXe 7%nat ltac:(lia)).
  assert (Ee_40 : ew Ee 40 = Z_to_bv 64 b14) by exact (EXe 8%nat ltac:(lia)).
  assert (Ee_41 : ew Ee 41 = Z_to_bv 64 b15) by exact (EXe 9%nat ltac:(lia)).
  assert (Eer : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ee n = getr (ms_regs ms) r)
    by (intros n r Hn; exact (ew_Eimg_Ereg_nat (ms_regs ms) XTe n r Hn)).
  assert (Hms : restrict (w_H W) ms =
                mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (rdW W (ms_mem ms)) (seg_rom SEGS)).
  { destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0' rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfr, Hfcsr.
    subst. reflexivity. }
  split.
  { rewrite Hms. apply pa_entry_st_ok_full.
    - apply (fa_regs_ok _ _ (n_ps cx)); [reflexivity | exact R21 | exact R26 | unfold PS_LEN in *; lia].
    - destruct pw; vm_compute; reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      + apply (fa_spill_ok Ee _ _ (n_sp1 cx) (n_buf cx) (nF cx fp) (n_ts cx) secw);
          [ rewrite (Eer 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia
          | exact Ee_32 | exact Ee_34 | exact Ee_35 | exact Ee_36 | exact Ee_37 | lia | lia
          | exact S_SB | exact S_TS | exact HSEC | exact S_F0 | exact S_BUF | exact S_FK ].
      + apply (fa_ps_ok Ee _ _ (n_ps cx) (n_h cx) pw);
          [ rewrite (Eer 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; unfold PS_LEN in *; lia
          | exact Ee_33 | exact Hh64 | lia | unfold PS_LEN in *; lia
          | destruct HPS as (P1 & _); rewrite Z.add_0_r in P1; exact P1
          | exact HW ].
    - apply pairwise_disjoint_of_extents. unfold extent_of_region.
      cbn [map fa_spill fa_ps YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite (Eer 9%nat 9%bv eq_refl), (Eer 21%nat 21%bv eq_refl), R9, R21. unfold w64.
      rewrite !unsigned_lit_small by (unfold PS_LEN in *; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold PS_LEN, NS_SB, NS_FK in *.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [fa_G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (Eer 21%nat 21%bv eq_refl), R21, Ee_32, Ee_34, Ee_38, Ee_39, Ee_40, Ee_41. unfold w64.
      rewrite !unsigned_lit_small by (unfold PS_LEN, SHADOW_OFF in *; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold PS_LEN, SHADOW_OFF, nx_bufn in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  unfold sh_ok, fa_SH1. apply Forall_cons; [|apply Forall_nil].
  apply (fa_shent_ps Ee _ (n_ps cx));
    [ exact Ee_32 | rewrite (Eer 21%nat 21%bv eq_refl); exact R21 | lia | exact Hps47 | exact Hpsamr
    | rewrite <- (aview_rd_of SEGS); exact HRA ].
Qed.

(* The same, with the record's bytes 12 .. 15 in the buffer and incl >= 18 (after `bltu s6,18` not taken). *)
Lemma fa_seat_buf : forall cx fp pc sh E qq ol vt vid tv k2 ly3 S3 (W : world SEGS) (ms : machine_state) md
    secw b12 b13 b14 b15 s6v,
  nx_base SK B KS cx ->
  nx_mid B MT KS cx fp pc sh E qq ol vt vid tv k2 ly3 S3 W ms md ->
  AR SEGS B ly3 S3 W (ms_mem ms) md ->
  nslot cx W ms NS_SEC secw ->
  0 <= b12 < 256 -> 0 <= b13 < 256 -> 0 <= b14 < 256 -> 0 <= b15 < 256 ->
  (forall a, n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2 -> apresent (w_H W) (ms_mem ms) a) ->
  getr (ms_regs ms) 22 = w64 s6v -> 18 <= s6v <= n_cap cx -> getr (ms_regs ms) 11 = w64 18 ->
  getr (ms_regs ms) 20 = w64 (n_buf cx) ->
  getr (ms_regs ms) 10 = w64 (n_ps cx + 20) -> getr (ms_regs ms) 12 = w64 (n_ps cx + 16) ->
  getr (ms_regs ms) 14 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + 20)) ->
  getr (ms_regs ms) 15 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + 16)) ->
  val_mem SEGS (rdW W (ms_mem ms)) (n_ps cx + PS_VT_OFF) 4 0 -> val_mem SEGS (rdW W (ms_mem ms)) (n_ps cx + PS_VID_OFF) 2 0 ->
  val_mem SEGS (rdW W (ms_mem ms)) (n_buf cx + 12) 1 b12 -> val_mem SEGS (rdW W (ms_mem ms)) (n_buf cx + 13) 1 b13 ->
  val_mem SEGS (rdW W (ms_mem ms)) (n_buf cx + 14) 1 b14 -> val_mem SEGS (rdW W (ms_mem ms)) (n_buf cx + 15) 1 b15 ->
  st_ok_pi SEGS VAL (Eimg (Ereg (ms_regs ms) (fa_extra (n_h cx) (n_buf cx) (nF cx fp) (n_ts cx) secw b12 b13 b14 b15)))
    (mkSS pc fa_sr3 [fa_spill; fa_ps0; fa_buf] None fa_G2) (restrict (w_H W) ms) /\
  sh_ok SEGS fa_Bx fa_SH2 (Eimg (Ereg (ms_regs ms) (fa_extra (n_h cx) (n_buf cx) (nF cx fp) (n_ts cx) secw b12 b13 b14 b15)))
    (rdW W (ms_mem ms)).
Proof.
  intros cx fp pc sh E qq ol vt vid tv k2 ly3 S3 W ms md secw b12 b13 b14 b15 s6v HB HM HAR HSEC Hb12 Hb13 Hb14 Hb15 HW
    HR22 Hs6 HR11 HR20 HR10 HR12 HR14 HR15 V16 V20 V12 V13 V14 V15.
  destruct HM as (HBD & R21 & R23 & R26 & R27 & HJBK & HK & HEs & Hh & HPS & HRA & HSRC & Hqr & HBUF & HTS).
  destruct HBD as (HBD0 & HSL).
  destruct HBD0 as (Hpc & Hresv & Hpend & Hrom & Hfr & Hfcsr & HREGS & HSAV & HHDR & HFLW & HSH & Hlen & R25 & HFK0).
  destruct HREGS as (R2 & R8 & R9 & R3 & R4).
  pose proof HSL as (S_FK & S_F0 & S_BUF & S_TS & S_SB & S_PS12 & S_SH12 & S_OFF8 & S_OFF12 & S_PH4 & S_PH8 & S_PH12).
  pose proof HB as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & Hh64 & Hps8 & Hps4
    & Hps47 & Hpsamr & Hpsown & Hpsf1 & Hpsf2 & _ & _ & _ & _ & _ & HBUFB & _).
  pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
  assert (Hpsceil : n_ps cx + PS_LEN <= alloc_ceiling).
  { assert (Hin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hpsown).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hc & _). lia. }
  pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK_B = 8464) by reflexivity.
  pose proof (NX_STK_B_frame (spZ (n_regs cx)) Hal16) as ((Hsp1lo & Hsp1hi) & _).
  change (nx_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1lo, Hsp1hi. unfold NX_MFRAME in Hsp1hi.
  destruct (HBUFB Hh) as (Hbufin & Hbuf4 & _ & _ & Hlbj & Hcap & _ & Hbufps).
  assert (Hbuf3 : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite (proj1 (proj2 HJBK)); exact Hbufin).
  unfold NX_CAP_MAX in Hcap.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hbufin) as (_ & _ & Hbceil & _).
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrq].
  set (XTe := fa_extra (n_h cx) (n_buf cx) (nF cx fp) (n_ts cx) secw b12 b13 b14 b15).
  set (Ee := Eimg (Ereg (ms_regs ms) XTe)).
  assert (EXe : forall j, (j < 10)%nat -> ew Ee (32 + j) = nth j XTe (Z_to_bv 64 0))
    by (intros j Hj; unfold Ee; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
  assert (Ee_32 : ew Ee 32 = Z_to_bv 64 SHADOW_OFF) by exact (EXe 0%nat ltac:(lia)).
  assert (Ee_33 : ew Ee 33 = Z_to_bv 64 (n_h cx)) by exact (EXe 1%nat ltac:(lia)).
  assert (Ee_34 : ew Ee 34 = Z_to_bv 64 (n_buf cx)) by exact (EXe 2%nat ltac:(lia)).
  assert (Ee_35 : ew Ee 35 = Z_to_bv 64 (nF cx fp)) by exact (EXe 3%nat ltac:(lia)).
  assert (Ee_36 : ew Ee 36 = Z_to_bv 64 (n_ts cx)) by exact (EXe 4%nat ltac:(lia)).
  assert (Ee_37 : ew Ee 37 = Z_to_bv 64 secw) by exact (EXe 5%nat ltac:(lia)).
  assert (Ee_38 : ew Ee 38 = Z_to_bv 64 b12) by exact (EXe 6%nat ltac:(lia)).
  assert (Ee_39 : ew Ee 39 = Z_to_bv 64 b13) by exact (EXe 7%nat ltac:(lia)).
  assert (Ee_40 : ew Ee 40 = Z_to_bv 64 b14) by exact (EXe 8%nat ltac:(lia)).
  assert (Ee_41 : ew Ee 41 = Z_to_bv 64 b15) by exact (EXe 9%nat ltac:(lia)).
  assert (Eer : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew Ee n = getr (ms_regs ms) r)
    by (intros n r Hn; exact (ew_Eimg_Ereg_nat (ms_regs ms) XTe n r Hn)).
  assert (Hms : restrict (w_H W) ms =
                mkst (ms_regs ms) (Z_to_bv 64 (BASE + pc)) (rdW W (ms_mem ms)) (seg_rom SEGS)).
  { destruct ms as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0' rom0].
    cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfr, Hfcsr.
    subst. reflexivity. }
  split.
  { rewrite Hms. apply pa_entry_st_ok_full.
    - apply (fa_regs_ok3 _ _ (n_ps cx) (n_buf cx)); [reflexivity | reflexivity | exact R21 | exact R26 | exact HR20
        | exact HR10 | exact HR12 | exact HR14 | exact HR15 | unfold PS_LEN in *; lia | unfold nx_bufn in *; lia].
    - vm_compute; reflexivity.
    - apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      + apply (fa_spill_ok Ee _ _ (n_sp1 cx) (n_buf cx) (nF cx fp) (n_ts cx) secw);
          [ rewrite (Eer 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia
          | exact Ee_32 | exact Ee_34 | exact Ee_35 | exact Ee_36 | exact Ee_37 | lia | lia
          | exact S_SB | exact S_TS | exact HSEC | exact S_F0 | exact S_BUF | exact S_FK ].
      + apply (fa_ps0_ok Ee _ _ (n_ps cx) (n_h cx));
          [ rewrite (Eer 21%nat 21%bv eq_refl), R21; unfold w64; apply unsigned_lit_small; unfold PS_LEN in *; lia
          | exact Ee_33 | exact Hh64 | lia | unfold PS_LEN in *; lia
          | destruct HPS as (P1 & _); rewrite Z.add_0_r in P1; exact P1
          | exact HW | exact V16 | exact V20 ].
      + apply (fa_buf_ok Ee _ _ (n_buf cx) b12 b13 b14 b15);
          [ rewrite Ee_34; unfold w64; apply unsigned_lit_small; unfold nx_bufn in *; lia
          | exact Ee_38 | exact Ee_39 | exact Ee_40 | exact Ee_41 | exact Hb12 | exact Hb13 | exact Hb14 | exact Hb15
          | lia | unfold nx_bufn in *; lia | exact V12 | exact V13 | exact V14 | exact V15 ].
    - apply pairwise_disjoint_of_extents. unfold extent_of_region.
      cbn [map fa_spill fa_ps0 fa_buf YP09.r_base YP09.r_lo YP09.r_hi base_val].
      rewrite (Eer 9%nat 9%bv eq_refl), (Eer 21%nat 21%bv eq_refl), R9, R21, Ee_34. unfold w64.
      rewrite !unsigned_lit_small by (unfold PS_LEN, nx_bufn in *; lia).
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold PS_LEN, NS_SB, NS_FK, nx_bufn in *.
      repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [fa_G2 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite (Eer 11%nat 11%bv eq_refl), (Eer 21%nat 21%bv eq_refl), (Eer 22%nat 22%bv eq_refl), HR11, R21, HR22, Ee_32, Ee_34, Ee_38, Ee_39, Ee_40, Ee_41. unfold w64.
      rewrite !unsigned_lit_small by (unfold PS_LEN, SHADOW_OFF, nx_bufn in *; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      unfold PS_LEN, SHADOW_OFF, nx_bufn in *.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
  unfold sh_ok, fa_SH2. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (fa_shent_ps Ee _ (n_ps cx));
      [ exact Ee_32 | rewrite (Eer 21%nat 21%bv eq_refl); exact R21 | lia | exact Hps47 | exact Hpsamr
      | rewrite <- (aview_rd_of SEGS); exact HRA ].
  - apply (fa_shent_gen Ee _ 34 (n_buf cx) 18);
      [ exact Ee_32 | exact Ee_34 | lia | lia | unfold nx_bufn in *; lia
      | apply (amem_range_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md (n_buf cx) (nx_bufn (n_cap cx)));
          [exact HAR | exact Hbuf3 | unfold nx_bufn in *; lia | unfold nx_bufn in *; lia]
      | rewrite <- (aview_rd_of SEGS);
        exact (range_addressable_of_block SEGS B LAWS ly3 S3 W (ms_mem ms) md (n_buf cx) (nx_bufn (n_cap cx)) (n_buf cx) 18
                 HAR Hbuf3 ltac:(unfold nx_bufn in *; lia) ltac:(unfold nx_bufn in *; lia)) ].
Qed.

(* The middle state across a step that wrote only the struct's tag fields, the buffer, and a window below sp1
   (the memmove's), with the tag fields now vt' and vid'. *)
Lemma fa_mid_tag : forall cx fp pc pc' q vt0 vid0 k2 ly3 S3 (W : world SEGS) (ms : machine_state) md
    (ms' : machine_state) md' lo hi vt' vid',
  nx_base SK B KS cx ->
  nx_mid B MT KS cx fp pc NSH_ph (nx_E cx) (q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q)
    (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) vt0 vid0 (n_tsv cx) k2 ly3 S3 W ms md ->
  AR SEGS B ly3 S3 W (ms_mem ms) md -> AR SEGS B ly3 S3 W (ms_mem ms') md' ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) ->
  ms_pc_val ms' = w64 (BASE + pc') -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  (forall r, In r [2; 3; 4; 8; 9; 21; 23; 25; 26; 27]%bv -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  n_sp1 cx - AFREAD_STK <= lo -> hi <= n_sp1 cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     ~ ((n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) \/ (n_buf cx <= a < n_buf cx + nx_bufn (n_cap cx))) ->
     fa_zone ly3 S3 a -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms') a) ->
  (forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) -> apresent (w_H W) (ms_mem ms') a) ->
  nx_jbk B MT cx k2 ly3 S3 md' ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_VT_OFF) 4 vt' ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_VID_OFF) 2 vid' ->
  nx_mid B MT KS cx fp pc' NSH_ph (nx_E cx) (q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q)
    (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) vt' vid' (n_tsv cx) k2 ly3 S3 W ms' md'.
Proof.
  intros cx fp pc pc' q vt0 vid0 k2 ly3 S3 W ms md ms' md' lo hi vt' vid' HB HM HAR HAR' HFR EFA
    Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' KR Hlo Hhi HUN HP1 HP2 HJBK' Vvt Vvid.
  set (sw := n_sw cx =? 1) in *. set (FF := nxF (n_C cx)) in *. set (incl := PSN.incl sw FF q) in *.
  pose proof HM as (HBD & R21 & R23 & R26 & R27 & HJBK & HK & HEs & Hh & HPS & HRA & HSRC & Hqr & HBUF & HTS).
  pose proof HB as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _ & _ & _ & _ & _ & Hps4 & Hps47
    & _ & Hpsown & Hpsf1 & Hpsf2 & _ & _ & _ & _ & _ & HBUFB & HTSB & HSTR & _).
  pose proof HJc as (HARc & _ & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
  pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HNX : NX_STK_B = 8464) by reflexivity.
  pose proof (NX_STK_B_frame (spZ (n_regs cx)) Hal16) as ((Hsp1lo & Hsp1hi) & _).
  change (nx_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1lo, Hsp1hi. unfold NX_MFRAME in Hsp1hi.
  unfold AFREAD_STK in Hlo.
  pose proof HJBK as (_ & Hab & _).
  assert (HCb : bytes_ok (n_C cx)) by exact (fa_src_bytes KS _ _ _ _ _ HSRC).
  assert (Hpsin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hpsown).
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hpsin) as (_ & Hpsfc & _).
  destruct (HBUFB Hh) as (Hbufin & Hbuf4 & _ & _ & Hlbj & Hcap & _ & Hbufps).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hbufin) as (_ & _ & Hbceil & _).
  destruct (HSTR Hh) as (Hinh & Hinb & _ & HClen & Hpr & Hbh & Hbb & Hpsh & Hpsb & Htsr & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hinh) as (_ & Hh4 & Hhceil & _).
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hinb) as (_ & Hb4 & Hbceil' & _).
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrq].
  pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as [_ HreqC].
  clear HBUFB HSTR.
  assert (Hwin : alloc_ceiling <= lo) by lia.
  (* the bytes the step may have written are the struct's tag fields and the buffer *)
  set (Wr := fun a => (n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) \/ (n_buf cx <= a < n_buf cx + nx_bufn (n_cap cx))).
  assert (HWrE : forall a, Wr a -> nx_E cx a).
  { intros a [Ha | Ha]; unfold nx_E, nx_wrset; [left | right; left]; unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia. }
  (* a frame byte of the caller, outside Wr and the window, is kept *)
  assert (Kfr : forall c p x, In (c, p) (n_own cx) ->
     frame_addr (n_lyc cx) c p <= x < frame_addr (n_lyc cx) c p + fs_frame_bytes c -> ~ Wr x ->
     aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) (ms_mem ms) x).
  { intros c p x Hin Hx Hn.
    assert (HinC : In (c, p) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hin).
    destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc HinC) as (Hf4 & Hfc & _).
    apply HUN; [lia | lia | exact Hn |]. right; right; right; right. exists c, p.
    split; [rewrite HFR; right; exact HinC|]. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. lia. }
  (* a block byte, outside Wr, is kept *)
  assert (Kbl : forall bb nn x, In (bb, nn) (ablocks B (n_lyc cx) (n_Sc cx)) -> bb <= x < bb + req_size nn -> ~ Wr x ->
     aview SEGS (w_H W) (ms_mem ms') x = aview SEGS (w_H W) (ms_mem ms) x).
  { intros bb nn x Hin Hx Hn. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hb4' & Hbc & _).
    apply HUN; [lia | lia | exact Hn |]. right; right; right; left. exists bb, nn. split; [rewrite Hab; exact Hin | lia]. }
    apply (fa_mid_step cx fp pc pc' NSH_ph (nx_E cx) (nx_E cx) (q + 16 + incl) (q + 16 + incl)
      (PSN.orig sw FF q) (PSN.orig sw FF q) vt0 vt' vid0 vid' (n_tsv cx) k2 ly3 S3 W ms md W ms' md'
      lo hi Wr HB HM HAR HFR EFA Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' KR); try assumption.
    - intros a [Ha | Ha]; [exact Ha | exact (HWrE a Ha)].
    - apply (fa_ps_new W W (ms_mem ms) (ms_mem ms') (n_ps cx) (n_h cx) (n_sw cx) (PSN.orig sw FF q) vt0 vid0);
        [exact HPS | | exact Vvt | exact Vvid].
      intros x Hx Hn. apply (Kfr (n_cid cx) (n_pos cx) x Hpsown); [unfold PS_LEN in *; lia|].
      unfold Wr. unfold PS_LEN, PS_VT_OFF, PS_VID_OFF, nx_bufn in *. intros [X | X]; [lia|].
      destruct Hbufps; lia.
    - apply (PcapSourceCloseSpec.asource_at_frame_segs _ KS (rdW W (ms_mem ms)) (rdW W (ms_mem ms'))); [|exact HSRC].
      intros a Ha. apply (mbyte_of_aview SEGS).
      destruct Ha as [Ha | [Ha | Ha]].
      + apply (Kbl (n_h cx) SRC_FILE_BLOCK a Hinh); [change (req_size SRC_FILE_BLOCK) with 1304; unfold SRC_FILE_BLOCK in Ha; lia|].
        unfold Wr. unfold PS_LEN, PS_VT_OFF, PS_VID_OFF, nx_bufn, SRC_FILE_BLOCK in *. intros [X | X];
          [destruct Hpsh; lia | destruct Hbh; lia].
      + apply (Kbl (n_b cx) (Z.of_nat (length (n_C cx))) a Hinb); [lia|].
        unfold Wr. unfold PS_LEN, PS_VT_OFF, PS_VID_OFF, nx_bufn in *. intros [X | X];
          [destruct Hpsb; lia | destruct Hbb; lia].
      + destruct (asil_env _ _ _ _ ASIL a Ha) as (Hi & Ho & He).
        pose proof (pa_img_range a Hi) as Hr. unfold pcap_img_end, YImgTop.IMG_TOP in Hr.
        apply HUN; [lia | lia | |right; left; tauto].
        pose proof (frm_off_imgP B _ _ _ _ _ _ _ HARc Hpsin) as Hoff1.
        pose proof (blk_off_imgP B _ _ _ _ _ _ _ HARc Hbufin) as Hoff2.
        unfold off_img, YImgTop.IMG_LO, YImgTop.IMG_TOP in Hoff1, Hoff2.
        unfold Wr. unfold PS_LEN, PS_VT_OFF, PS_VID_OFF, nx_bufn in *. intros [X | X];
          [destruct Hoff1; lia | destruct Hoff2; lia].
    - destruct (fa_buf_exists (w_H W) (ms_mem ms') (n_buf cx) (length (n_bj cx))) as (bj' & Hg & Hl).
      { intros i Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR' (ltac:(rewrite Hab; exact Hbufin) :
          In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3))) as (_ & _ & _ & _ & Hpres & _).
        assert (Z.of_nat i < nx_bufn (n_cap cx)) by (rewrite <- Hlbj; lia).
        exact (proj1 (Hpres (n_buf cx + Z.of_nat i) ltac:(lia))). }
      exists bj'. split; [exact Hg | exact Hl].
    - intros T0. destruct (HTS T0) as (Hv & _).
      destruct (HTSB Hh T0) as (_ & _ & Ht4 & _ & _ & (tcid & tpos & Htin & Ht1 & Ht2) & _ & _ & Htps & Htbuf).
      apply (fa_vm_keep W W (ms_mem ms) (ms_mem ms')); [|exact Hv].
      intros x Hx. cbn [Z.of_nat] in Hx. apply (Kfr tcid tpos x Htin); [lia|].
      unfold Wr. unfold PS_LEN, PS_VT_OFF, PS_VID_OFF, nx_bufn in *. intros [X | X];
        [destruct Htps; lia | destruct Htbuf; lia].
Qed.

(* NP_ts from the middle state of a cut of this phase (pc, ms) and a step that wrote only the struct's tag
   fields, the buffer, and (the memmove) its window below sp1: nx_ts_inv. *)
Lemma fa_land_ts : forall cx fp pc q vt0 vid0 k2 ly3 S3 (W : world SEGS) (ms : machine_state) md (ms' : machine_state) md'
    lo hi vt' vid' (rec : list Z),
  nx_base SK B KS cx ->
  nx_mid B MT KS cx fp pc NSH_ph (nx_E cx) (q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q)
    (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q) vt0 vid0 (n_tsv cx) k2 ly3 S3 W ms md ->
  AR SEGS B ly3 S3 W (ms_mem ms) md -> AR SEGS B ly3 S3 W (ms_mem ms') md' ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  (forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p) ->
  nx_q (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = q ->
  nx_lh (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = Some q ->
  0 <= q -> 0 < PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <= n_cap cx ->
  q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q <= Z.of_nat (length (n_C cx)) ->
  ms_pc_val ms' = w64 (BASE + NP_ts) -> ms_resv ms' = None -> ms_svc_pending ms' = None ->
  ms_rom ms' = seg_rom SEGS -> ms_fregs ms' = fp_regs -> ms_fcsr ms' = fp_csr ->
  (forall r, In r [2; 3; 4; 8; 9; 21; 23; 25; 26; 27]%bv -> getr (ms_regs ms') r = getr (ms_regs ms) r) ->
  n_sp1 cx - AFREAD_STK <= lo -> hi <= n_sp1 cx ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     ~ ((n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) \/ (n_buf cx <= a < n_buf cx + nx_bufn (n_cap cx))) ->
     fa_zone ly3 S3 a -> aview SEGS (w_H W) (ms_mem ms') a = aview SEGS (w_H W) (ms_mem ms) a) ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (lo <= a < hi) ->
     apresent (w_H W) (ms_mem ms) a -> apresent (w_H W) (ms_mem ms') a) ->
  (forall a, spZ (n_regs cx) - NX_STK_B <= a < spZ (n_regs cx) -> apresent (w_H W) (ms_mem ms') a) ->
  nx_jbk B MT cx k2 ly3 S3 md' ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_VT_OFF) 4 vt' ->
  val_mem SEGS (rdW W (ms_mem ms')) (n_ps cx + PS_VID_OFF) 2 vid' ->
  vt' = nx_vtag (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvt cx) ->
  vid' = nx_vid (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvid cx) ->
  garr8 SEGS (rdW W (ms_mem ms')) (n_buf cx) rec ->
  rec = nx_rec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) ->
  (length rec <= length (n_bj cx))%nat ->
  getr (ms_regs ms') 16 = w64 (nF cx fp) -> getr (ms_regs ms') 19 = w64 (nF cx fp) ->
  getr (ms_regs ms') 17 = w64 (n_ts cx) -> getr (ms_regs ms') 5 = w64 SHADOW_OFF ->
  bv_unsigned (getr (ms_regs ms') 22) mod 2 ^ 32 = nx_reclen (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) ->
  bv_unsigned (getr (ms_regs ms') 18) mod 2 ^ 32 = nx_tsec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) ->
  bv_unsigned (getr (ms_regs ms') 24) mod 2 ^ 32 = nx_tusec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) ->
  nx_ts_inv B MT KS cx fp k2 ly3 S3 W ms' md'.
Proof.
  intros cx fp pc q vt0 vid0 k2 ly3 S3 W ms md ms' md' lo hi vt' vid' rec HB HM HAR HAR' HFR EFA Hq Hlh Hq0 Hincl Hfit
    Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' KR Hlo Hhi HUN HP1 HP2 HJBK' Vvt Vvid Evt Evid Hrec Erec Hlrec R16 R19 R17 R5 R22 R18 R24.
  pose proof (fa_mid_tag cx fp pc NP_ts q vt0 vid0 k2 ly3 S3 W ms md ms' md' lo hi vt' vid' HB HM HAR HAR' HFR EFA
    Hpc' Hrv' Hsv' Hrom' Hfr' Hfc' KR Hlo Hhi HUN HP1 HP2 HJBK' Vvt Vvid) as HM'.
  set (sw := n_sw cx =? 1) in *. set (FF := nxF (n_C cx)) in *. set (incl := PSN.incl sw FF q) in *.
  pose proof HM as (_ & _ & _ & _ & _ & HJBK & _ & _ & Hh & _ & _ & HSRC & _ & _ & _).
  pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & _ & _ & _ & _ & _ & _ & _ & _ & _ & HBUFB & _).
  pose proof HJBK as (_ & Hab & _).
  assert (HCb : bytes_ok (n_C cx)) by exact (fa_src_bytes KS _ _ _ _ _ HSRC).
  destruct (HBUFB Hh) as (Hbufin & _ & _ & _ & Hlbj & Hcap & _).
  clear HBUFB.
  pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [_ Hrq].
  pose proof (fa_fit_pos sw (n_C cx) (n_cap cx) (n_p cx) q) as Fpos. fa_inst Fpos.
  pose proof (fa_fit_fit sw (n_C cx) (n_cap cx) (n_p cx) q) as Ffit. fa_inst Ffit.
  unfold nx_ts_inv. change (n_sw cx =? 1) with sw.
  split.
  { rewrite <- Evt, <- Evid, Fpos.
    replace (nx_orig sw (n_C cx) (n_cap cx) (n_p cx) (n_lol cx)) with (PSN.orig sw FF q)
      by (unfold nx_orig; rewrite Hlh; reflexivity).
    exact HM'. }
  split; [exact Ffit|].
  split.
  { destruct (fa_buf_exists (w_H W) (ms_mem ms') (n_buf cx) (length (n_bj cx))) as (bj' & Hg & Hl).
    { intros i Hi. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR' (ltac:(rewrite Hab; exact Hbufin) :
        In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3))) as (_ & _ & _ & _ & Hpres & _).
      assert (Z.of_nat i < nx_bufn (n_cap cx)) by (rewrite <- Hlbj; lia).
      exact (proj1 (Hpres (n_buf cx + Z.of_nat i) ltac:(lia))). }
    exists bj'. split; [exact Hg|]. split; [exact Hl|].
    rewrite <- Erec. apply (fa_garr8_prefix _ _ _ _ Hrec Hg). rewrite Hl. exact Hlrec. }
  split; [exact R16|]. split; [exact R19|]. split; [exact R17|]. split; [exact R5|].
  split; [exact R22|]. split; [exact R18 | exact R24].
Qed.

Theorem pb_nx_fitA : forall POST : ncx -> world SEGS -> config -> Prop,
  nx_from SK B KS POST (nx_ts_inv B MT KS) -> nx_from SK B KS POST (nx_exit_inv B MT KS) ->
  nx_from SK B KS POST (nx_fit_inv B MT KS).
Proof.
intros POST HTS HEX cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFR HFI.
destruct HFI as (q & HM & Hq & Hlh & Hpq & Hincl & R18 & R22 & R24 & (secw & HSEC & Hsec)).
pose proof HM as HM0.
destruct HM as (HBD & R21 & R23 & R26 & R27 & HJBK & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqr & HBUF & HTSm).
destruct HBD as (HBD0 & HSL).
destruct HBD0 as (Hpc & Hresv & Hpend & Hrom & Hfr & Hfcsr & HREGS & HSAV & HHDR & HFLW & HSH & Hlen & R25 & HFK0).
destruct HREGS as (R2 & R8 & R9 & R3 & R4).
pose proof HSL as (S_FK & S_F0 & S_BUF & S_TS & S_SB & S_PS12 & S_SH12 & S_OFF8 & S_OFF12 & S_PH4 & S_PH8 & S_PH12).
pose proof HB as (HJc & HROD & Hraw & Hra4 & Hgp & Htp & H10 & H11 & H12 & H13 & Hal16 & Hwlo & Hwhi & Hch
  & Hroom & Hpsf & Hh64 & Hps8 & Hps4 & Hps47 & Hpsamr & Hpsown & Hpsf1 & Hpsf2 & HpsRA & HPS0 & Hsw & Hrng
  & HpsWR & HBUFB & HTSB & HSTR & HMETA & HE0 & HE02).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR3 & Hly3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HNX : NX_STK_B = 8464) by reflexivity.
assert (Hsp : alloc_ceiling + NX_STK_B <= spZ (n_regs cx) <= 2 ^ 47) by lia.
pose proof (NX_STK_B_frame (spZ (n_regs cx)) Hal16) as ((Hsp1lo & Hsp1hi) & Hsp1al).
change (nx_sp1 (spZ (n_regs cx))) with (n_sp1 cx) in Hsp1lo, Hsp1hi, Hsp1al.
unfold NX_MFRAME in Hsp1hi. rewrite HNX in Hsp.
(* this call's frame *)
assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
{ intros c p. unfold frame_addr.
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _). destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _).
  rewrite EF3, EFc. reflexivity. }
assert (HFB : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
assert (HinF : In (NX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms3) md3 NX_CID fp HAR3 HinF) as (HF4096 & HFceil & _).
rewrite EFA in HF4096. rewrite EFA, HFB in HFceil.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in HF4096, HFceil.
(* the struct's frame *)
assert (Hpsin : In (n_cid cx, n_pos cx) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Hpsown).
destruct (frames_bounds SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hpsin)
  as (Hpsf4096 & Hpsfceil & _).
(* the buffer *)
destruct (HBUFB Hh) as (Hbufin & Hbuf4 & Hbuf63 & Hgbj & Hlbj & Hcap & HbufWR & Hbufps).
box Hbufps. box HBUFB. box HTSB. box HPS0. box Hsw. box Hrng. box HpsWR. box HMETA. box HTSm.
destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hbufin)
  as (_ & Hb4096 & Hbceil & _).
pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as [Hrq1 Hrq2].
(* the model *)
set (sw := n_sw cx =? 1) in *.
set (FF := nxF (n_C cx)) in *.
set (incl := PSN.incl sw FF q) in *.
assert (Hfb : forall i, 0 <= PSN.fb FF i < 256).
{ intros i. unfold PSN.fb. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) FF (Z_to_bv 8 0))) as Hy.
  change (bv_modulus 8) with 256 in Hy. lia. }
pose proof (fa_rdword_range _ _ _ _ HSEC) as Hsecw.
(* ---- the symbolic state at NP_fit ---- *)
set (XT := fa_extra (n_h cx) (n_buf cx) (nF cx fp) (n_ts cx) secw
             (PSN.fb FF (q + 28)) (PSN.fb FF (q + 29)) (PSN.fb FF (q + 30)) (PSN.fb FF (q + 31))).
set (E1 := Eimg (Ereg (ms_regs ms3) XT)).
assert (HEI1 : img_env VAL A_LIM E1) by apply Eimg_env.
assert (EX1 : forall j, (j < 10)%nat -> ew E1 (32 + j) = nth j XT (Z_to_bv 64 0)).
{ intros j Hj. unfold E1. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (E1_32 : ew E1 32 = Z_to_bv 64 SHADOW_OFF) by exact (EX1 0%nat ltac:(lia)).
assert (E1_33 : ew E1 33 = Z_to_bv 64 (n_h cx)) by exact (EX1 1%nat ltac:(lia)).
assert (E1_34 : ew E1 34 = Z_to_bv 64 (n_buf cx)) by exact (EX1 2%nat ltac:(lia)).
assert (E1_35 : ew E1 35 = Z_to_bv 64 (nF cx fp)) by exact (EX1 3%nat ltac:(lia)).
assert (E1_36 : ew E1 36 = Z_to_bv 64 (n_ts cx)) by exact (EX1 4%nat ltac:(lia)).
assert (E1_37 : ew E1 37 = Z_to_bv 64 secw) by exact (EX1 5%nat ltac:(lia)).
assert (E1_38 : ew E1 38 = Z_to_bv 64 (PSN.fb FF (q + 28))) by exact (EX1 6%nat ltac:(lia)).
assert (E1_39 : ew E1 39 = Z_to_bv 64 (PSN.fb FF (q + 29))) by exact (EX1 7%nat ltac:(lia)).
assert (E1_40 : ew E1 40 = Z_to_bv 64 (PSN.fb FF (q + 30))) by exact (EX1 8%nat ltac:(lia)).
assert (E1_41 : ew E1 41 = Z_to_bv 64 (PSN.fb FF (q + 31))) by exact (EX1 9%nat ltac:(lia)).
assert (E1r : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr (ms_regs ms3) r)
  by (intros n r Hn; exact (ew_Eimg_Ereg_nat (ms_regs ms3) XT n r Hn)).
assert (HAE1 : env_agree 32 (Ereg (ms_regs ms3) XT) E1)
  by (split; [intros n Hn; unfold E1; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (Hms : restrict (w_H W3) ms3 =
              mkst (ms_regs ms3) (Z_to_bv 64 (BASE + NP_fit)) (rdW W3 (ms_mem ms3)) (seg_rom SEGS)).
{ destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0' rom0].
  cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in Hpc, Hresv, Hpend, Hrom, Hfr, Hfcsr.
  subst. reflexivity. }
assert (HS : st_ok_pi SEGS VAL E1 (mkSS NP_fit fa_sr [fa_spill; fa_ps false] None fa_G) (restrict (w_H W3) ms3)).
{ rewrite Hms. apply pa_entry_st_ok_full.
  - apply (fa_regs_ok _ _ (n_ps cx)); [reflexivity | exact R21 | exact R26 | unfold PS_LEN in *; lia].
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    + apply (fa_spill_ok E1 _ _ (n_sp1 cx) (n_buf cx) (nF cx fp) (n_ts cx) secw).
      * rewrite (E1r 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia.
      * exact E1_32.
      * exact E1_34.
      * exact E1_35.
      * exact E1_36.
      * exact E1_37.
      * lia.
      * lia.
      * exact S_SB.
      * exact S_TS.
      * exact HSEC.
      * exact S_F0.
      * exact S_BUF.
      * exact S_FK.
    + apply (fa_ps_ok E1 _ _ (n_ps cx) (n_h cx) false).
      * rewrite (E1r 21%nat 21%bv eq_refl), R21. unfold w64. apply unsigned_lit_small. unfold PS_LEN in *. lia.
      * exact E1_33.
      * exact Hh64.
      * lia.
      * unfold PS_LEN in *. lia.
      * destruct HPS as (P1 & _). rewrite Z.add_0_r in P1. exact P1.
      * intros D. discriminate D.
  - apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map fa_spill fa_ps YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite (E1r 9%nat 9%bv eq_refl), (E1r 21%nat 21%bv eq_refl), R9, R21. unfold w64.
    rewrite !unsigned_lit_small by (unfold PS_LEN in *; lia).
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold PS_LEN, NS_SB, NS_FK in *.
    repeat split; lia.
  - split; [|split; [exact I | exact I]].
    cbn [fa_G f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite (E1r 21%nat 21%bv eq_refl), R21, E1_32, E1_34, E1_38,
      E1_39, E1_40, E1_41.
    unfold XT, fa_extra. cbn [map nth]. unfold w64.
    rewrite !unsigned_lit_small by (first [pose proof (Hfb (q + 28)); pose proof (Hfb (q + 29));
      pose proof (Hfb (q + 30)); pose proof (Hfb (q + 31)); lia | unfold PS_LEN, SHADOW_OFF in *; lia]).
    change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    pose proof (Hfb (q + 28)). pose proof (Hfb (q + 29)). pose proof (Hfb (q + 30)). pose proof (Hfb (q + 31)).
    unfold PS_LEN, SHADOW_OFF in *.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia]. }
assert (SHOK : sh_ok SEGS fa_Bx fa_SH1 E1 (rdW W3 (ms_mem ms3))).
{ unfold sh_ok, fa_SH1. apply Forall_cons; [|apply Forall_nil].
  apply (fa_shent_ps E1 _ (n_ps cx)).
  - exact E1_32.
  - rewrite (E1r 21%nat 21%bv eq_refl). exact R21.
  - lia.
  - exact Hps47.
  - exact Hpsamr.
  - rewrite <- (aview_rd_of SEGS). exact HRAps. }
clearbody E1.
paj_run_tok RUN HS HJ SHOK fa_span.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
(* ---- the record fread 0x819a4 ---- *)
rename ms into ms1.
lazymatch goal with H : frame_of _ _ (ms_mem ms3) (ms_mem ms1) |- _ => rename H into HFm1 end.
assert (Hm1 : ms_mem ms1 = ms_mem ms3).
{ apply functional_extensionality. intros x. apply HFm1. intros (r & Hin & Hr). cbn in Hin.
  destruct Hin as [<-|[<-|[]]]; cbn in Hr; lia. }
clear HFm1.
lazymatch goal with H : frame_of _ _ _ _ |- _ => clear H end.
lazymatch goal with H : mem_grows _ _ |- _ => clear H end.
assert (Q26 : getr (ms_regs ms1) 26 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx))).
{ pose proof (st_ok_restrict_reg SEGS (w_H W3) E1 _ ms1 26%bv HS) as H. cbn [restrict ms_regs] in H.
  lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
  rewrite H, denot_lit_U, (fa_U_shx E1 (n_ps cx)); [reflexivity | | exact E1_32 | unfold PS_LEN in *; lia].
  rewrite (E1r 21%nat 21%bv eq_refl). exact R21. }
pose proof (regs_kept_of_st_ok SEGS E1 _ (restrict (w_H W3) ms1) (ms_regs ms3) XT
  [2; 3; 4; 8; 9; 18; 20; 21; 22; 23; 24; 25; 27]%bv HS HAE1 ltac:(vm_compute; reflexivity)) as K1.
assert (K26 : getr (ms_regs ms1) 26 = getr (ms_regs ms3) 26) by (rewrite Q26, R26; reflexivity).
cbn [restrict ms_regs] in K1.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (19%bv : bv 5) Q19.
rewrite E1_34 in Q10. rewrite E1_33 in Q13. rewrite E1_35 in Q19.
rewrite (E1r 18%nat 18%bv eq_refl), R18 in Q12.
pmkst HS.
set (md1 := with_vm_backing (m_vm_lazy md3) mat md3) in *.
assert (U2 : spZ (ms_regs ms1) = n_sp1 cx).
{ unfold spZ. rewrite (K1 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
(* where the blocks of the stream lie *)
destruct (HSTR Hh) as (Hinh & Hinb & _ & HClen & Hpr & Hbh & Hbb & Hpsh & Hpsb & Htsr & HFPh).
box Hbh. box Hbb. box Hpsh. box Hpsb. box Htsr. box HSTR.
destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hinh)
  as (_ & Hh4096 & Hhceil & _).
destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hinb)
  as (_ & Hb4096' & Hbceil' & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
pose proof (req_size_pos (Z.of_nat (length (n_C cx))) ltac:(lia)) as [_ HreqC].
destruct HJBK as (Hk2 & Hab3 & Hmo3 & Hfd3 & Hfs3).
assert (HAR1 : AR SEGS B ly3 S3 W3 (ms_mem ms1) md1) by exact (proj1 HJ).
assert (Hbuf3 : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite Hab3; exact Hbufin).
assert (Hincl8 : 0 < incl <= n_cap cx /\ n_cap cx <= 2040) by (unfold NX_CAP_MAX in Hcap; lia).
assert (Hbn : incl <= nx_bufn (n_cap cx)) by (unfold nx_bufn; lia).
eapply SRr_bind.
{ apply (H_fread (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms1) md1 k2 (ms_regs ms1) (nx_ch cx)
    (n_buf cx) incl (n_h cx) (n_b cx) (q + 16) (n_C cx)).
  unfold afread_pre, rread_call, rread_dest, rread_wr_ok, rread_at.
  split; [|split; [exact Q10 |]]; [|split; [exact Q11 |]]; [|split; [exact Q12 |]]; [|split; [exact Q13 |]].
  - split; [exact HJ|].
    split; [rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]|].
    split; [unfold raZ; rewrite Q1; pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)); pose proof pa_B_ok as (_ & HB40 & _);
            rewrite unsigned_lit_small by lia; lia|].
    split; [rewrite (K1 3%bv ltac:(cbn; tauto)), R3; exact Hgp|].
    split; [rewrite (K1 4%bv ltac:(cbn; tauto)), R4; exact Htp|].
    rewrite U2. split; [apply Z.mod_divide in Hsp1al; [|lia]; apply Z.mod_divide; [lia|];
                        destruct Hsp1al as [z Hz]; exists (2 * z); lia|].
    split; [unfold AFREAD_STK; lia|]. split; [lia|].
    unfold s0Z. rewrite (K1 8%bv ltac:(cbn; tauto)), R8. unfold w64. rewrite unsigned_lit_small by lia.
    rewrite Hm1. eapply (fa_achain B KS cx W3 ms3 ly3 (nx_E cx)); try eassumption; lia.
  - rewrite U2. split; [rewrite Hab3; exact Hinh|]. split; [rewrite Hab3; exact Hinb|].
    split; [left; unfold AFREAD_STK; lia|].
    split; [rewrite Hm1; exact HSRC|].
    split.
    { intros a Ha. split; [|unfold SRC_FILE_BLOCK, AFREAD_STK in *; lia].
      assert (Hfp : inFP (asource_fp (n_h cx)) a) by (exists (n_h cx, n_h cx + SRC_FILE_BLOCK); split; [left; reflexivity | cbn; lia]).
      destruct (HFPh a Hfp) as [Hf | Ht].
      - right. left. split; [exact Hf|]. exists (n_h cx), SRC_FILE_BLOCK. split; [rewrite Hab3; exact Hinh|].
        change (req_size SRC_FILE_BLOCK) with 1304. unfold SRC_FILE_BLOCK in Ha. lia.
      - right. right. left. rewrite Hab3. exact Ht. }
    split; [unfold NX_CAP_MAX in *; lia|].
    split; [unfold boxed in Hbh; unfold nx_bufn in Hbh, Hbn; destruct Hbh; [left | right]; lia|].
    split; [unfold boxed in Hbb; unfold nx_bufn in Hbb, Hbn; destruct Hbb; [left | right]; lia|]. split; [lia|].
    split; [apply (amem_range_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) md1 (n_buf cx) (nx_bufn (n_cap cx))); [exact HAR1 | exact Hbuf3 | lia | lia]|].
    split; [right; right; exists (n_buf cx), (nx_bufn (n_cap cx)); split; [exact Hbuf3 | lia]|].
    split.
    { intros a Ha. destruct (HbufWR a ltac:(lia)) as (Hw & Hnw). split; [|unfold AFREAD_STK in *; lia].
      apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
      - intros x Hx. rewrite Hab3. exact Hx.
      - intros x Hx. right. exact Hx.
      - exact EFA. }
    split; [exact (range_addressable_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) md1 (n_buf cx) (nx_bufn (n_cap cx)) (n_buf cx) incl HAR1 Hbuf3 ltac:(lia) ltac:(lia))|].
    intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W3 (ms_mem ms1) md1 (n_buf cx) (nx_bufn (n_cap cx)) (n_buf cx) incl HAR1 Hbuf3 ltac:(lia) ltac:(lia) Hpos). }
cbv beta. intros W2 c2 Hwle (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HK2 & HPOST).
destruct HPOST as (-> & -> & R10' & HGB & HSRC2 & _ & _ & HFD & HFS & HSB).
rewrite Q1. let a := eval unfold NP_fit_ra in NP_fit_ra in change (BASE + a) with (BASE + NP_fit_ra).

set (j := rread_k incl (Z.of_nat (length (n_C cx))) (q + 16)) in *.
assert (Hj0 : 0 <= j <= incl /\ j <= Z.of_nat (length (n_C cx)) - (q + 16)) by (unfold j, rread_k; lia).
assert (Hm1fd : m_fds md1 = m_fds md3 /\ m_fs md1 = m_fs md3) by (unfold md1; destruct md3; split; reflexivity).
assert (KR2 : forall r, In r [2; 3; 4; 8; 9; 21; 23; 25; 26; 27]%bv -> getr regs2 r = getr (ms_regs ms3) r).
{ intros r Hr. cbn in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
    (rewrite (fa_pres _ _ _ HP2) by (match goal with |- acallee_saved (bv_unsigned ?r) => let z := eval vm_compute in (bv_unsigned r) in change (acallee_saved z) end; unfold acallee_saved; lia));
    first [ exact K26 | (apply K1; cbn; tauto) ]. }
assert (U2' : spZ regs2 = n_sp1 cx).
{ unfold spZ. rewrite (KR2 2%bv ltac:(cbn; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
(* what fread kept *)
assert (HUNf : forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx - AFREAD_STK <= a < n_sp1 cx) ->
  ~ rread_wrset (n_h cx) (n_buf cx) incl a -> fa_zone ly3 S3 a ->
  aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hw Hn Hz. rewrite <- Hm1. destruct HK2 as (F1 & F2 & F3 & F4 & F5 & F6). rewrite U2 in *.
  destruct Hz as [Hz | [(Hi & Ho & He) | [Hz | [(bb & mm & Hin & Hr) | (cid & pos & Hin & Hr)]]]].
  - apply F1; [lia | exact Hw | exact Hn].
  - apply F3; assumption.
  - apply HSB; lia.
  - replace a with (bb + (a - bb)) by lia. apply (F2 bb mm (a - bb)); [exact Hin | lia |].
    replace (bb + (a - bb)) with a by lia. exact Hn.
  - apply (F4 cid pos a Hin); [left; exact Hr | exact Hn]. }
box HUNf.

(* the caller's bytes this call has written so far: nx_E of the record fread *)
assert (Hsp1c : alloc_ceiling <= n_sp1 cx - AFREAD_STK) by (unfold AFREAD_STK; lia).
assert (HWrE : forall a, rread_wrset (n_h cx) (n_buf cx) incl a -> nx_E cx a).
{ intros a [Ha | Ha]; unfold nx_E, nx_wrset.
  - right; right; right. split; [exact Hh | exact Ha].
  - right; left. unfold nx_bufn in *. lia. }
assert (HbufP : forall i, (i < length (n_bj cx))%nat -> apresent (w_H W2) mem2 (n_buf cx + Z.of_nat i)).
{ intros i Hi. pose proof (proj1 HJ2) as HAR2.
  destruct (al_blocks _ _ LAWS ly3 S3 W2 mem2 md2 _ _ HAR2 Hbuf3) as (_ & _ & _ & _ & Hpres & _).
  assert (Z.of_nat i < nx_bufn (n_cap cx)) by (rewrite <- Hlbj; lia).
  exact (proj1 (Hpres (n_buf cx + Z.of_nat i) ltac:(lia))). }
destruct (fa_buf_exists (w_H W2) mem2 (n_buf cx) (length (n_bj cx)) HbufP) as (bj2 & Hbj2 & Hbj2len).
assert (M1 : nx_mid B MT KS cx fp NP_fit_ra NSH_ph (nx_E cx) (q + 16 + j)
  (PSN.orig sw FF q) (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W2
  (mkst regs2 (w64 (BASE + NP_fit_ra)) mem2 (seg_rom SEGS)) md2).
{ unfold boxed in HUNf.
  apply (fa_mid_step cx fp NP_fit NP_fit_ra NSH_ph (nx_E cx) (nx_E cx) (q + 16) (q + 16 + j)
    (PSN.orig sw FF q) (PSN.orig sw FF q) (n_lvt cx) (n_lvt cx) (n_lvid cx) (n_lvid cx) (n_tsv cx)
    k2 ly3 S3 W3 ms3 md3 W2 _ md2 (n_sp1 cx - AFREAD_STK) (n_sp1 cx) (rread_wrset (n_h cx) (n_buf cx) incl));
    try exact HB; try exact HM0.
  - exact HAR3.
  - exact HFR.
  - exact EFA.
  - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity. - reflexivity.
  - intros r Hr. cbn [ms_regs mkst]. exact (KR2 r Hr).
  - lia.
  - lia.
  - cbn [ms_mem mkst]. exact HUNf.
  - exact HWrE.
  - intros a [Ha | Ha]; [exact Ha | exact (HWrE a Ha)].
  - intros a Ha. exact Ha.
  - cbn [ms_mem mkst]. intros a Ha Hw Hp. destruct HK2 as (_ & _ & _ & _ & F5 & _). rewrite U2 in F5.
    apply F5; [lia | lia | rewrite <- Hm1 in Hp; exact Hp].
  - cbn [ms_mem mkst]. intros a Ha. destruct HK2 as (_ & _ & _ & _ & _ & F6). rewrite U2 in F6.
    pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 HJ2)))))))))))) ) as _.
    destruct HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _). apply HpresJ. lia.
  - unfold nx_jbk. split; [exact Hk2|]. split; [exact Hab3|]. split; [exact Hmo3|].
    split; [rewrite HFD; rewrite (proj1 Hm1fd); exact Hfd3 | rewrite HFS; rewrite (proj2 Hm1fd); exact Hfs3].
  - cbn [ms_mem mkst]. apply (fa_ps_keep W3 W2 (ms_mem ms3) mem2); [|exact HPS].
    intros x Hx. unfold PS_LEN in Hx.
    assert (Hps24 : 4096 <= n_ps cx /\ n_ps cx + 24 <= alloc_ceiling).
    { unfold PS_LEN in Hpsf2. split; [lia | lia]. }
    pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
    apply HUNf; [lia | lia | | ].
    + unfold boxed in Hpsh, Hbufps. unfold SRC_FILE_BLOCK, PS_LEN in Hpsh. unfold nx_bufn, PS_LEN in Hbufps.
      intros [Hw | Hw]; [unfold SRC_FILE_BLOCK in Hw; lia | unfold nx_bufn in Hw, Hbn; lia].
    + right; right; right; right. exists (n_cid cx), (n_pos cx). split; [rewrite HFR; right; rewrite Hfrsc; apply in_or_app; left; exact Hpsown|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. unfold PS_LEN in Hpsf2. lia.
  - cbn [ms_mem mkst]. exact HSRC2.
  - lia.
  - cbn [ms_mem mkst]. exists bj2. split; [exact Hbj2 | exact Hbj2len].
  - cbn [ms_mem mkst]. intros T0.
    unfold boxed in HTSB. destruct (HTSB Hh T0) as (Hval & Hts8 & Hts4 & Hts47 & Hamr & (tcid & tpos & Htin & Ht1 & Ht2) & _ & _ & _ & Htbuf).
    unfold boxed in Htsr.
    destruct (Htsr T0) as (Hth & Htb).
    apply (fa_vm_keep W3 W2 (ms_mem ms3) mem2); [|exact (proj1 (HTSm T0))].
    intros x Hx. cbn [Z.of_nat] in Hx. pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
    assert (Htsceil : n_ts cx + 8 <= alloc_ceiling).
    { assert (Hin : In (tcid, tpos) (frames (n_Sc cx))) by (rewrite Hfrsc; apply in_or_app; left; exact Htin).
      destruct (frames_bounds SEGS B LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hc & _). lia. }
    apply HUNf; [lia | lia | |].
    + unfold SRC_FILE_BLOCK in Hth. unfold nx_bufn in Htbuf, Hbn.
      intros [Hw | Hw]; [unfold SRC_FILE_BLOCK in Hw; lia | lia].
    + right; right; right; right. exists tcid, tpos. split; [rewrite HFR; right; rewrite Hfrsc; apply in_or_app; left; exact Htin|].
      unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFA. lia. }
assert (HSEC2 : nslot cx W2 (mkst regs2 (w64 (BASE + NP_fit_ra)) mem2 (seg_rom SEGS)) NS_SEC secw).
{ unfold nslot. cbn [ms_mem mkst]. unfold boxed in HUNf.
  apply (fa_rdword_keep W3 W2 (ms_mem ms3) mem2); [|exact HSEC].
  intros k Hk. apply HUNf; [unfold NS_SEC in *; lia | unfold NS_SEC, AFREAD_STK in *; lia | |].
  - intros [Hw | Hw]; [unfold SRC_FILE_BLOCK in Hw; unfold NS_SEC in *; lia
                      | unfold nx_bufn in Hw, Hbn; unfold NS_SEC in *; lia].
  - left. unfold NS_SEC in *. lia. }
set (XTe := fa_extra (n_h cx) (n_buf cx) (nF cx fp) (n_ts cx) secw
       (PSN.fb FF (q + 28)) (PSN.fb FF (q + 29)) (PSN.fb FF (q + 30)) (PSN.fb FF (q + 31))) in *.

destruct (fa_seat cx fp NP_fit_ra NSH_ph (nx_E cx) (q + 16 + j) (PSN.orig sw FF q) (n_lvt cx) (n_lvid cx)
  (n_tsv cx) k2 ly3 S3 W2 (mkst regs2 (w64 (BASE + NP_fit_ra)) mem2 (seg_rom SEGS)) md2 secw
  (PSN.fb FF (q + 28)) (PSN.fb FF (q + 29)) (PSN.fb FF (q + 30)) (PSN.fb FF (q + 31)) false
  HB M1 HSEC2 (Hfb (q + 28)) (Hfb (q + 29)) (Hfb (q + 30)) (Hfb (q + 31)) ltac:(intros D; discriminate D))
  as (HS2 & SHOK2).
lazymatch type of HS2 with st_ok_pi _ _ ?Ex _ _ => assert (HEIb : img_env VAL A_LIM Ex) by apply Eimg_env end.
assert (HJ2' : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
  ((NX_CID, fp) :: n_own cx) ly3 S3 W2 (ms_mem (mkst regs2 (w64 (BASE + NP_fit_ra)) mem2 (seg_rom SEGS))) md2 k2)
  by exact HJ2.
paj_run_tok RUN HS2 HJ2' SHOK2 fa_span.
{ cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }

lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => is_var msx; rename msx into ms2 end.
rename HS2 into HS2b. rename SHOK2 into SHOK2b. rename HJ2' into HJ2b.
lazymatch goal with H : frame_of _ _ (rdW W2 mem2) _ |- _ => rename H into HFr2 end.
assert (Hmem2 : ms_mem ms2 = mem2).
{ lazymatch goal with H : frame_of _ _ mem2 (ms_mem ms2) |- _ =>
    apply functional_extensionality; intros x; apply H; intros (r & Hin & Hr); cbn in Hin;
    destruct Hin as [<-|[<-|[]]]; cbn in Hr; lia end. }
assert (R18' : getr regs2 18 = w64 incl).
{ rewrite (fa_pres _ _ _ HP2) by (match goal with |- acallee_saved (bv_unsigned ?r) =>
    let z := eval vm_compute in (bv_unsigned r) in change (acallee_saved z) end; unfold acallee_saved; lia).
  rewrite (K1 18%bv ltac:(cbn; tauto)). exact R18. }
assert (R19' : getr regs2 19 = w64 (nF cx fp)).
{ rewrite (fa_pres _ _ _ HP2) by (match goal with |- acallee_saved (bv_unsigned ?r) =>
    let z := eval vm_compute in (bv_unsigned r) in change (acallee_saved z) end; unfold acallee_saved; lia).
  exact Q19. }
psrr_branch_tok RUN BR HS2b SHOK2b fa_span.
- (* a0 <> incl: the record was cut (KCutFit), to NP_exit with a1 = -1 *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 10%nat j) in Hc by
    (first [ lazymatch goal with |- ew _ 10 = _ => rewrite (ew_Eimg_Ereg_nat regs2 XTe 10 10%bv eq_refl); exact R10' end
           | unfold j, rread_k; lia ]).
  rewrite (U_atom _ 18%nat incl) in Hc by
    (first [ lazymatch goal with |- ew _ 18 = _ => rewrite (ew_Eimg_Ereg_nat regs2 XTe 18 18%bv eq_refl); exact R18' end
           | lia ]).
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hcut : Z.of_nat (length (n_C cx)) < q + 16 + incl) by (unfold j, rread_k in Hc, Hj0; lia).
  (* run to NP_exit *)
  paj_run_to_tok RUNTO HS2b HJ2b SHOK2b fa_span NP_exit.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => is_var msx; rename msx into ms3b end.
  lazymatch goal with H : frame_of _ _ (ms_mem ms2) (ms_mem ms3b) |- _ => rename H into HFm3 end.
  assert (Hmem3 : ms_mem ms3b = ms_mem ms2).
  { apply functional_extensionality. intros x. apply HFm3. intros (r & Hin & Hr). cbn in Hin.
    destruct Hin as [<-|[<-|[]]]; cbn in Hr; lia. }
  assert (HAE2 : env_agree 32 (Ereg regs2 XTe) (Eimg (Ereg regs2 XTe)))
    by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok SEGS _ _ (restrict (w_H W2) ms3b) regs2 XTe
    [2; 3; 4; 8; 9; 18; 19; 21; 23; 25; 27]%bv HS2b HAE2 ltac:(vm_compute; reflexivity)) as K3.
  cbn [restrict ms_regs] in K3.
  assert (K3_26 : getr (ms_regs ms3b) 26 = getr regs2 26).
  { pose proof (st_ok_restrict_reg SEGS (w_H W2) _ _ ms3b 26%bv HS2b) as H. cbn [restrict ms_regs] in H.
    lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
    rewrite H, denot_lit_U, (fa_U_shx _ (n_ps cx));
      [ rewrite (KR2 26%bv ltac:(cbn; tauto)); symmetry; exact R26
      | rewrite (ew_Eimg_Ereg_nat regs2 XTe 21 21%bv eq_refl); rewrite (KR2 21%bv ltac:(cbn; tauto)); exact R21
      | exact (ew_Ereg_extra regs2 XTe 0)
      | unfold PS_LEN in *; lia ]. }
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md3b := mdx) in * end.
  assert (Hmd3 : m_fds md3b = m_fds md2 /\ m_fs md3b = m_fs md2)
    by (unfold md3b; destruct md2; split; reflexivity).
  pose proof M1 as M1c.
  destruct M1c as (HBD1 & R21a & R23a & R26a & R27a & HJBK1 & HK1 & HEs1 & Hh1 & HPS1 & HRA1 & HSRC1 & Hq1 & HBUF1 & HTS1).
  cbn [ms_mem mkst] in HPS1, HRA1, HSRC1, HBUF1, HTS1, HK1.
  assert (M2 : nx_mid B MT KS cx fp NP_exit NSH_ph (nx_E cx) (q + 16 + j) (PSN.orig sw FF q)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W2 ms3b md3b).
  { apply (fa_mid_step cx fp NP_fit_ra NP_exit NSH_ph (nx_E cx) (nx_E cx) (q + 16 + j) (q + 16 + j)
      (PSN.orig sw FF q) (PSN.orig sw FF q) (n_lvt cx) (n_lvt cx) (n_lvid cx) (n_lvid cx) (n_tsv cx)
      k2 ly3 S3 W2 (mkst regs2 (w64 (BASE + NP_fit_ra)) mem2 (seg_rom SEGS)) md2 W2 ms3b md3b
      (n_sp1 cx) (n_sp1 cx) (fun _ => False));
      try exact HB; try exact M1.
    - cbn [ms_mem mkst]. exact (proj1 HJ2).
    - exact HFR.
    - exact EFA.
    - lazymatch type of HS2b with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms3b HS2b eq_refl) as Hsh3 end.
      rewrite Hsh3. reflexivity.
    - lazymatch type of HS2b with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms3b HS2b eq_refl) as Hsh3 end.
      rewrite Hsh3. reflexivity.
    - lazymatch type of HS2b with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms3b HS2b eq_refl) as Hsh3 end.
      rewrite Hsh3. reflexivity.
    - lazymatch type of HS2b with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms3b HS2b eq_refl) as Hsh3 end.
      rewrite Hsh3. reflexivity.
    - lazymatch type of HS2b with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms3b HS2b eq_refl) as Hsh3 end.
      rewrite Hsh3. reflexivity.
    - lazymatch type of HS2b with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms3b HS2b eq_refl) as Hsh3 end.
      rewrite Hsh3. reflexivity.
    - intros r Hr. cbn [ms_regs mkst]. cbn in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
        first [ exact K3_26 | apply K3; cbn; tauto ].
    - unfold AFREAD_STK; lia.
    - lia.
    - intros a Ha Hw Hn Hz. rewrite Hmem3. cbn [ms_mem mkst]. rewrite Hmem2. reflexivity.
    - intros a [].
    - intros a [Ha | []]. exact Ha.
    - intros a Ha. exact Ha.
    - intros a Ha Hw Hp. rewrite Hmem3, Hmem2. cbn [ms_mem mkst] in Hp. exact Hp.
    - intros a Ha. destruct HJ2b as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
      apply HpresJ. lia.
    - unfold nx_jbk. destruct HJBK1 as (Hk2a & Haba & Hmoa & Hfda & Hfsa).
      split; [exact Hk2a|]. split; [exact Haba|]. split; [exact Hmoa|].
      split; [rewrite (proj1 Hmd3); exact Hfda | rewrite (proj2 Hmd3); exact Hfsa].
    - rewrite Hmem3, Hmem2. exact HPS1.
    - rewrite Hmem3, Hmem2. exact HSRC1.
    - exact Hq1.
    - rewrite Hmem3, Hmem2. exact HBUF1.
    - rewrite Hmem3, Hmem2. intros T0. exact (proj1 (HTS1 T0)). }
  pose proof (fa_src_bytes KS _ _ _ _ _ HSRC) as HCb.
  assert (Hq0' : 0 <= q) by (unbox; lia).
  assert (Hroom16 : q + 16 <= Z.of_nat (length (n_C cx))) by lia.
  pose proof (fa_cut_pos sw (n_C cx) (n_cap cx) (n_p cx) q) as Cpos. fa_inst Cpos.
  pose proof (fa_cut_res sw (n_C cx) (n_cap cx) (n_p cx) q) as Cres. fa_inst Cres.
  pose proof (fa_cut_fit sw (n_C cx) (n_cap cx) (n_p cx) q) as Cfit. fa_inst Cfit.
  pose proof (fa_cut_vtag sw (n_C cx) (n_cap cx) (n_p cx) q) as Cvt. fa_inst Cvt.
  pose proof (fa_cut_vid sw (n_C cx) (n_cap cx) (n_p cx) q) as Cvid. fa_inst Cvid.
  pose proof (fa_cut_tsv sw (n_C cx) (n_cap cx) (n_p cx) q) as Ctsv. fa_inst Ctsv.
  Ltac fa_reg HS r X :=
    lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict ?H ?msx) =>
      pose proof (st_ok_pi_restrict_reg H E ss msx r HS) as X;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in X;
      cbn [restrict ms_regs] in X
    end.
  fa_reg HS2b (11%bv : bv 5) X11. fa_reg HS2b (16%bv : bv 5) X16.
  apply (HEX cx fp k2 ly3 S3 W2 ms3b md3b HB HJ2b HFR).
  apply (fa_exit_of_mid cx fp k2 ly3 S3 W2 ms3b md3b (nx_E cx) (q + 16 + j) (PSN.orig sw FF q)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) M2).
  all: try change (n_sw cx =? 1) with sw.
  + rewrite (K3 19%bv ltac:(cbn; tauto)). exact R19'.
  + rewrite X16. exact (fa_denot_extra regs2 _ _ _ _ _ _ _ _ _ 3 (nF cx fp) eq_refl ltac:(lia) ltac:(lia)).
  + rewrite Cpos. unfold j, rread_k in *. lia.
  + unfold nx_orig. rewrite Hlh. reflexivity.
  + rewrite (Cvt (n_lvt cx)). reflexivity.
  + rewrite (Cvid (n_lvid cx)). reflexivity.
  + rewrite (Ctsv (n_tsv cx)). reflexivity.
  + exact Cfit.
  + rewrite X11, Cres. cbn [sv_denot]. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. vm_compute. reflexivity.



- (* a0 = incl: the record fits *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 10%nat j) in Hc by
    (first [ lazymatch goal with |- ew _ 10 = _ => rewrite (ew_Eimg_Ereg_nat regs2 XTe 10 10%bv eq_refl); exact R10' end
           | unfold j, rread_k; lia ]).
  rewrite (U_atom _ 18%nat incl) in Hc by
    (first [ lazymatch goal with |- ew _ 18 = _ => rewrite (ew_Eimg_Ereg_nat regs2 XTe 18 18%bv eq_refl); exact R18' end
           | lia ]).
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Hfitq : q + 16 + incl <= Z.of_nat (length (n_C cx))) by (unfold j, rread_k in Hc, Hj0; lia).
  (* the same state, seated again with ps->vtag and ps->vid writable *)
  lazymatch type of HS2b with st_ok_pi _ _ _ ?ss _ =>
    pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms2 HS2b eq_refl) as Hsh2 end.
  cbn [ss_pc] in Hsh2.
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md2b := mdx) in * end.
  assert (Hmd2 : m_fds md2b = m_fds md2 /\ m_fs md2b = m_fs md2)
    by (unfold md2b; destruct md2; split; reflexivity).
  assert (HAE2 : env_agree 32 (Ereg regs2 XTe) (Eimg (Ereg regs2 XTe)))
    by (split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  pose proof (regs_kept_of_st_ok_pi _ _ (restrict (w_H W2) ms2) regs2 XTe
    [2; 3; 4; 8; 9; 10; 18; 19; 21; 22; 23; 24; 25; 27]%bv HS2b HAE2 ltac:(vm_compute; reflexivity)) as K2.
  cbn [restrict ms_regs] in K2.
  assert (K2_26 : getr (ms_regs ms2) 26 = getr regs2 26).
  { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms2 26%bv HS2b) as H. cbn [restrict ms_regs] in H.
    lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
    rewrite H, denot_lit_U, (fa_U_shx _ (n_ps cx));
      [ rewrite (KR2 26%bv ltac:(cbn; tauto)); symmetry; exact R26
      | rewrite (ew_Eimg_Ereg_nat regs2 XTe 21 21%bv eq_refl); rewrite (KR2 21%bv ltac:(cbn; tauto)); exact R21
      | exact (ew_Ereg_extra regs2 XTe 0)
      | unfold PS_LEN in *; lia ]. }
  fa_rv HS2b (16%bv : bv 5) G16. fa_rv HS2b (17%bv : bv 5) G17.
  change 35%nat with (32 + 3)%nat in G16. change 36%nat with (32 + 4)%nat in G17.
  rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 3 (nF cx fp) ltac:(lia) eq_refl) in G16.
  rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 4 (n_ts cx) ltac:(lia) eq_refl) in G17.
  pose proof M1 as M1c.
  destruct M1c as (HBD1 & R21a & R23a & R26a & R27a & HJBK1 & HK1 & HEs1 & Hh1 & HPS1 & HRA1 & HSRC1 & Hq1 & HBUF1 & HTS1).
  cbn [ms_mem mkst] in HPS1, HRA1, HSRC1, HBUF1, HTS1, HK1.
  assert (Mb : nx_mid B MT KS cx fp (NP_fit_ra + 12) NSH_ph (nx_E cx) (q + 16 + j) (PSN.orig sw FF q)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W2 ms2 md2b).
  { apply (fa_mid_step cx fp NP_fit_ra (NP_fit_ra + 12) NSH_ph (nx_E cx) (nx_E cx) (q + 16 + j) (q + 16 + j)
      (PSN.orig sw FF q) (PSN.orig sw FF q) (n_lvt cx) (n_lvt cx) (n_lvid cx) (n_lvid cx) (n_tsv cx)
      k2 ly3 S3 W2 (mkst regs2 (w64 (BASE + NP_fit_ra)) mem2 (seg_rom SEGS)) md2 W2 ms2 md2b
      (n_sp1 cx) (n_sp1 cx) (fun _ => False));
      try exact HB; try exact M1.
    - cbn [ms_mem mkst]. exact (proj1 HJ2).
    - exact HFR.
    - exact EFA.
    - rewrite Hsh2. reflexivity.
    - rewrite Hsh2. reflexivity.
    - rewrite Hsh2. reflexivity.
    - rewrite Hsh2. reflexivity.
    - rewrite Hsh2. reflexivity.
    - rewrite Hsh2. reflexivity.
    - intros r Hr. cbn [ms_regs mkst]. cbn in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
        first [ exact K2_26 | apply K2; cbn; tauto ].
    - unfold AFREAD_STK; lia.
    - lia.
    - intros a Ha Hw Hn Hz. rewrite Hmem2. reflexivity.
    - intros a [].
    - intros a [Ha | []]. exact Ha.
    - intros a Ha. exact Ha.
    - intros a Ha Hw Hp. rewrite Hmem2. cbn [ms_mem mkst] in Hp. exact Hp.
    - intros a Ha. destruct HJ2b as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
      apply HpresJ. lia.
    - unfold nx_jbk. destruct HJBK1 as (Hk2a & Haba & Hmoa & Hfda & Hfsa).
      split; [exact Hk2a|]. split; [exact Haba|]. split; [exact Hmoa|].
      split; [rewrite (proj1 Hmd2); exact Hfda | rewrite (proj2 Hmd2); exact Hfsa].
    - rewrite Hmem2. exact HPS1.
    - rewrite Hmem2. exact HSRC1.
    - exact Hq1.
    - rewrite Hmem2. exact HBUF1.
    - rewrite Hmem2. intros T0. exact (proj1 (HTS1 T0)). }

  (* reseat with the struct's tag fields writable *)
  assert (HSECb : nslot cx W2 ms2 NS_SEC secw) by (unfold nslot; rewrite Hmem2; exact HSEC2).
  assert (HPw : forall a, n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2 -> apresent (w_H W2) (ms_mem ms2) a).
  { intros a Ha. unfold boxed in HpsWR. destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
    refine (proj1 (awr_byte_present SEGS B LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ2b _)).
    apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
    - intros x Hx. rewrite Hab3. exact Hx.
    - intros x Hx. right. exact Hx.
    - exact EFA. }
  destruct (fa_seat cx fp (NP_fit_ra + 12) NSH_ph (nx_E cx) (q + 16 + j) (PSN.orig sw FF q) (n_lvt cx) (n_lvid cx)
    (n_tsv cx) k2 ly3 S3 W2 ms2 md2b secw
    (PSN.fb FF (q + 28)) (PSN.fb FF (q + 29)) (PSN.fb FF (q + 30)) (PSN.fb FF (q + 31)) true
    HB Mb HSECb (Hfb (q + 28)) (Hfb (q + 29)) (Hfb (q + 30)) (Hfb (q + 31)) (fun _ => HPw)) as (HS3 & SHOK3).
  pose proof (proj1 HJ2b) as HAR2b.
  clear HS2b SHOK2b.
  lazymatch type of HS3 with st_ok_pi _ _ ?Ex _ _ => assert (HEIc : img_env VAL A_LIM Ex) by apply Eimg_env end.
  set (regs3 := ms_regs ms2) in *.
  paj_run_tok RUN HS3 HJ2b SHOK3 fa_span.
  { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
    eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_nil].
    - rewrite (ew_Eimg_Ereg_nat regs3 _ 21 21%bv eq_refl). rewrite (K2 21%bv ltac:(cbn; tauto)).
      rewrite (KR2 21%bv ltac:(cbn; tauto)), R21. unfold w64. apply unsigned_lit_small. unfold PS_LEN in *. lia.
    - cbn [YP09.r_wlo YP09.r_whi fa_ps]. intros a Ha. unfold boxed in HpsWR.
      destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
      apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
      + intros x Hx. rewrite Hab3. exact Hx.
      + intros x Hx. right. exact Hx.
      + exact EFA. }
  (* the same branch again: decided by the cond j = incl *)

  lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => is_var msx; rename msx into ms4 end.
  assert (U21c : bv_unsigned (ew (Eimg (Ereg regs3 XTe)) 21) = n_ps cx).
  { rewrite (ew_Eimg_Ereg_nat regs3 XTe 21 21%bv eq_refl), (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)), R21.
    unfold w64. apply unsigned_lit_small. unfold PS_LEN in *. lia. }
  lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
    pose proof (fa_kept_ps _ _ _ _ _ (n_ps cx) H) as KM4;
    specialize (KM4 ltac:(clear; vm_compute; reflexivity) U21c); clear H end.
  lazymatch goal with H : mem_grows _ _ |- _ => rename H into HG4 end.
  psrr_branch_tok RUN BR HS3 SHOK3 fa_span.
  + (* taken: contradicts j = incl *)
    exfalso. rewrite branch_ne_U in Hc0.
    rewrite (U_atom _ 10%nat j) in Hc0 by
      (first [ lazymatch goal with |- ew _ 10 = _ => rewrite (ew_Eimg_Ereg_nat regs3 _ 10 10%bv eq_refl);
                 rewrite (K2 10%bv ltac:(cbn; tauto)); exact R10' end
             | unfold j, rread_k; lia ]).
    rewrite (U_atom _ 18%nat incl) in Hc0 by
      (first [ lazymatch goal with |- ew _ 18 = _ => rewrite (ew_Eimg_Ereg_nat regs3 _ 18 18%bv eq_refl);
                 rewrite (K2 18%bv ltac:(cbn; tauto)); exact R18' end
             | lia ]).
    rewrite Hc, Z.eqb_refl in Hc0. discriminate Hc0.
  + (* not taken: the tag fields, then `bltu s6,18` *)
    paj_run_tok RUN HS3 HJ2b SHOK3 fa_span.
    { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
      eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_nil].
      - rewrite (ew_Eimg_Ereg_nat regs3 _ 21 21%bv eq_refl). rewrite (K2 21%bv ltac:(cbn; tauto)).
        rewrite (KR2 21%bv ltac:(cbn; tauto)), R21. unfold w64. apply unsigned_lit_small. unfold PS_LEN in *. lia.
      - cbn [YP09.r_wlo YP09.r_whi fa_ps]. intros a Ha. unfold boxed in HpsWR.
        destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
        apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
        * intros x Hx. rewrite Hab3. exact Hx.
        * intros x Hx. right. exact Hx.
        * exact EFA. }
    lazymatch goal with |- SRr _ _ (mkCfg ?msx _) _ => is_var msx; rename msx into ms5 end.

    pose proof (proj1 HJ2b) as HAR5.
    assert (KM5 : forall a, 0 <= a < 2 ^ 64 -> ~ (n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) ->
      aview SEGS (w_H W2) (ms_mem ms5) a = aview SEGS (w_H W2) (ms_mem ms2) a).
    { lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
        pose proof (fa_kept_ps _ _ _ _ _ (n_ps cx) H) as K;
        specialize (K ltac:(clear; vm_compute; reflexivity) U21c); clear H end.
      intros a Ha Hn. rewrite (K a Ha Hn). exact (KM4 a Ha Hn). }
    lazymatch goal with H : mem_grows _ (rdW W2 (ms_mem ms5)) |- _ => rename H into HG5' end.
    pose proof (mem_grows_trans _ _ _ HG4 HG5') as HG5. clear HG5'.

    (* the middle state at 0x819f8 (`bltu s6,18`): ps->vtag and ps->vid are 0 *)
    lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ => set (md5 := mdx) in * end.
    lazymatch type of HS3 with st_ok_pi _ _ ?Ex ?ss _ =>
      let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
      lazymatch r with Some ?rr =>
        pose proof (fa_chunk_val Ex ss _ 1 rr 16 4 (SLit 0) 0 HS3 ltac:(clear; vm_compute; reflexivity)
          ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as V16;
        pose proof (fa_chunk_val Ex ss _ 1 rr 20 2 (SLit 0) 0 HS3 ltac:(clear; vm_compute; reflexivity)
          ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as V20
      end end.
    cbn [restrict ms_mem base_val YP09.r_base] in V16, V20.
    assert (U21d : forall X, bv_unsigned (ew (Eimg (Ereg regs3 X)) 21) = n_ps cx).
    { intros X. rewrite (ew_Eimg_Ereg_nat regs3 X 21 21%bv eq_refl), (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)), R21.
      unfold w64. apply unsigned_lit_small. unfold PS_LEN in *. lia. }
    rewrite !ew_ewset_other in V16, V20 by lia. rewrite U21d in V16, V20.
    change (N.to_nat 4) with 4%nat in V16. change (N.to_nat 2) with 2%nat in V20.
    change 16 with PS_VT_OFF in V16. change 20 with PS_VID_OFF in V20.


    assert (Hmd5 : m_fds md5 = m_fds md2b /\ m_fs md5 = m_fs md2b).
    { unfold md5. split; reflexivity. }
    lazymatch type of HS3 with st_ok_pi _ _ _ ?ss _ =>
      pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms5 HS3 eq_refl) as Hsh5 end.
    fa_kept HS3 regs3 XTe ([2; 3; 4; 8; 9; 21; 22; 23; 24; 25; 27]%bv : list (bv 5)) K5.
    assert (K5_26 : getr (ms_regs ms5) 26 = getr regs3 26).
    { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms5 26%bv HS3) as H. cbn [restrict ms_regs] in H.
      lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
      rewrite H, denot_lit_U, (fa_U_shx _ (n_ps cx)).
      - rewrite K2_26, (KR2 26%bv ltac:(cbn; tauto)). symmetry; exact R26.
      - rewrite !ew_ewset_other by lia. rewrite (ew_Eimg_Ereg_nat regs3 XTe 21 21%bv eq_refl).
        rewrite (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)). exact R21.
      - rewrite !ew_ewset_other by lia. exact (ew_Ereg_extra regs3 XTe 0).
      - unfold PS_LEN in *. lia. }
    assert (M5 : nx_mid B MT KS cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x440) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) NSH_ph (nx_E cx) (q + 16 + incl) (PSN.orig sw FF q) 0 0 (n_tsv cx)
      k2 ly3 S3 W2 ms5 md5).
    { rewrite Hc in Mb.
      apply (fa_mid_tag cx fp (NP_fit_ra + 12) (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x440) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) q (n_lvt cx) (n_lvid cx) k2 ly3 S3 W2 ms2 md2b ms5 md5
        (n_sp1 cx) (n_sp1 cx) 0 0 HB Mb HAR2b HAR5 HFR EFA).
      - rewrite Hsh5. reflexivity.
      - rewrite Hsh5. reflexivity.
      - rewrite Hsh5. reflexivity.
      - rewrite Hsh5. reflexivity.
      - rewrite Hsh5. reflexivity.
      - rewrite Hsh5. reflexivity.
      - intros r Hr. cbn in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
          first [ exact K5_26 | apply K5; cbn; tauto ].
      - unfold AFREAD_STK. lia.
      - lia.
      - intros a Ha _ Hn _. apply KM5; [exact Ha | intros X; apply Hn; left; exact X].
      - intros a _ _ Hp. exact (fa_grows_present _ _ _ a HG5 Hp).
      - intros a Ha. destruct HJ2b as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
        apply HpresJ. lia.
      - unfold nx_jbk. destruct HJBK1 as (Hk2a & Haba & Hmoa & Hfda & Hfsa).
        split; [exact Hk2a|]. split; [exact Haba|]. split; [exact Hmoa|].
        split; [rewrite (proj1 Hmd5), (proj1 Hmd2); exact Hfda | rewrite (proj2 Hmd5), (proj2 Hmd2); exact Hfsa].
      - exact V16.
      - exact V20. }

    assert (R22_2 : getr regs2 22 = w64 incl).
    { rewrite (fa_pres _ _ _ HP2) by (match goal with |- acallee_saved (bv_unsigned ?r) =>
        let z := eval vm_compute in (bv_unsigned r) in change (acallee_saved z) end; unfold acallee_saved; lia).
      rewrite (K1 22%bv ltac:(cbn; tauto)). exact R22. }
    assert (R24_2 : getr regs2 24 = getr (ms_regs ms3) 24).
    { rewrite (fa_pres _ _ _ HP2) by (match goal with |- acallee_saved (bv_unsigned ?r) =>
        let z := eval vm_compute in (bv_unsigned r) in change (acallee_saved z) end; unfold acallee_saved; lia).
      exact (K1 24%bv ltac:(cbn; tauto)). }
    assert (HCb : bytes_ok (n_C cx)) by exact (fa_src_bytes KS _ _ _ _ _ HSRC).
    assert (Hq0' : 0 <= q) by (unfold boxed in *; lia).
    rewrite Hc in HGB.
    pose proof (fa_raw_length sw (n_C cx) (n_cap cx) q) as Frl2. fa_inst Frl2.

    assert (G10_5 : getr (ms_regs ms5) 10 = w64 (n_ps cx + 20)).
    { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms5 10%bv HS3) as H. cbn [restrict ms_regs] in H.
      lazymatch type of H with _ = sv_denot _ ?e => change e with (SOff 21 20) in H end.
      rewrite H, denot_lit_U, U_off by (rewrite !ew_ewset_other by lia; rewrite U21d; unfold PS_LEN, M64 in *; lia).
      rewrite !ew_ewset_other by lia. rewrite U21d. reflexivity. }
    assert (G12_5 : getr (ms_regs ms5) 12 = w64 (n_ps cx + 16)).
    { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms5 12%bv HS3) as H. cbn [restrict ms_regs] in H.
      lazymatch type of H with _ = sv_denot _ ?e => change e with (SOff 21 16) in H end.
      rewrite H, denot_lit_U, U_off by (rewrite !ew_ewset_other by lia; rewrite U21d; unfold PS_LEN, M64 in *; lia).
      rewrite !ew_ewset_other by lia. rewrite U21d. reflexivity. }
    assert (G14_5 : getr (ms_regs ms5) 14 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + 20))).
    { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms5 14%bv HS3) as H. cbn [restrict ms_regs] in H.
      lazymatch type of H with _ = sv_denot _ ?e => change e with (fa_shx 20) in H end.
      rewrite H, denot_lit_U, (fa_U_shx_k _ (n_ps cx) 20).
      - reflexivity.
      - rewrite !ew_ewset_other by lia. rewrite (ew_Eimg_Ereg_nat regs3 _ 21 21%bv eq_refl).
        rewrite (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)). exact R21.
      - rewrite !ew_ewset_other by lia. exact (ew_Ereg_extra regs3 XTe 0).
      - lia.
      - lia.
      - unfold PS_LEN in *. lia. }
    assert (G15_5 : getr (ms_regs ms5) 15 = w64 (shadow_of_addr SHADOW_OFF (n_ps cx + 16))).
    { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms5 15%bv HS3) as H. cbn [restrict ms_regs] in H.
      lazymatch type of H with _ = sv_denot _ ?e => change e with (fa_shx 16) in H end.
      rewrite H, denot_lit_U, (fa_U_shx_k _ (n_ps cx) 16).
      - reflexivity.
      - rewrite !ew_ewset_other by lia. rewrite (ew_Eimg_Ereg_nat regs3 _ 21 21%bv eq_refl).
        rewrite (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)). exact R21.
      - rewrite !ew_ewset_other by lia. exact (ew_Ereg_extra regs3 XTe 0).
      - lia.
      - lia.
      - unfold PS_LEN in *. lia. }
    fa_rv HS3 (11%bv : bv 5) G11_5. fa_rv HS3 (18%bv : bv 5) G18_5. fa_rv HS3 (20%bv : bv 5) G20_5.
    change 34%nat with (32 + 2)%nat in G20_5.
    rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 2 (n_buf cx) ltac:(lia) eq_refl) in G20_5. change 37%nat with (32 + 5)%nat in G18_5.
    rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 5 secw ltac:(lia) eq_refl) in G18_5.
    psrr_branch_tok RUN BR HS3 SHOK3 fa_span.

    * (* s6 < 18: no tag, `bltu` to NP_ts *)
      rewrite branch_ltu_U in Hc1.
      rewrite (U_atom _ 22%nat incl) in Hc1 by
        (first [ rewrite !ew_ewset_other by lia; rewrite (ew_Eimg_Ereg_nat regs3 _ 22 22%bv eq_refl), (K2 22%bv ltac:(cbn; tauto)); exact R22_2
               | lia ]).
      rewrite U_SLit in Hc1. apply Z.ltb_lt in Hc1.
      paj_run_to_tok RUNTO HS3 HJ2b SHOK3 fa_span NP_ts.
      { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
        eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_nil].
        - rewrite !ew_ewset_other by lia. apply U21d.
        - cbn [YP09.r_wlo YP09.r_whi fa_ps]. intros a Ha. unfold boxed in HpsWR.
          destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
          apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
          + intros x Hx. rewrite Hab3. exact Hx.
          + intros x Hx. right. exact Hx.
          + exact EFA. }
      lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => is_var msx; rename msx into ms6; set (md6 := mdx) in * end.
      (* what the run kept *)
      lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
        pose proof (fa_kept_ps _ _ _ _ _ (n_ps cx) H) as KM6;
        specialize (KM6 ltac:(clear; vm_compute; reflexivity) ltac:(rewrite !ew_ewset_other by lia; apply U21d)); clear H end.
      lazymatch goal with H : mem_grows _ (rdW W2 (ms_mem ms6)) |- _ => rename H into HG6 end.
      pose proof (proj1 HJ2b) as HAR6.
      assert (Hmd6 : m_fds md6 = m_fds md5 /\ m_fs md6 = m_fs md5) by (unfold md6; split; reflexivity).
      lazymatch type of HS3 with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms6 HS3 eq_refl) as Hsh6 end.
      fa_kept HS3 regs3 XTe ([2; 3; 4; 8; 9; 21; 23; 25; 27]%bv : list (bv 5)) K6.
      assert (K6_26 : getr (ms_regs ms6) 26 = getr regs3 26).
      { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms6 26%bv HS3) as H. cbn [restrict ms_regs] in H.
        lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
        rewrite H, denot_lit_U, (fa_U_shx _ (n_ps cx)).
        - rewrite K2_26, (KR2 26%bv ltac:(cbn; tauto)). symmetry; exact R26.
        - rewrite !ew_ewset_other by lia. rewrite (ew_Eimg_Ereg_nat regs3 XTe 21 21%bv eq_refl).
          rewrite (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)). exact R21.
        - rewrite !ew_ewset_other by lia. exact (ew_Ereg_extra regs3 XTe 0).
        - unfold PS_LEN in *. lia. }
      lazymatch type of HS3 with st_ok_pi _ _ ?Ex ?ss _ =>
        let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
        lazymatch r with Some ?rr =>
          pose proof (fa_chunk_val Ex ss _ 1 rr 16 4 (SLit 0) 0 HS3 ltac:(clear; vm_compute; reflexivity)
            ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as V16b;
          pose proof (fa_chunk_val Ex ss _ 1 rr 20 2 (SLit 0) 0 HS3 ltac:(clear; vm_compute; reflexivity)
            ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as V20b
        end end.
      cbn [restrict ms_mem base_val YP09.r_base] in V16b, V20b.
      rewrite !ew_ewset_other in V16b, V20b by lia. rewrite U21d in V16b, V20b.
      change (N.to_nat 4) with 4%nat in V16b. change (N.to_nat 2) with 2%nat in V20b.
      change 16 with PS_VT_OFF in V16b. change 20 with PS_VID_OFF in V20b.
      (* the registers at NP_ts *)
      fa_rv HS3 (16%bv : bv 5) X16. fa_rv HS3 (19%bv : bv 5) X19. fa_rv HS3 (17%bv : bv 5) X17.
      fa_rv HS3 (5%bv : bv 5) X5. fa_rv HS3 (18%bv : bv 5) X18. fa_rv HS3 (24%bv : bv 5) X24. fa_rv HS3 (22%bv : bv 5) X22.
      rewrite (ew_Eimg_Ereg_nat regs3 _ 16 16%bv eq_refl), G16 in X16.
      rewrite (ew_Eimg_Ereg_nat regs3 _ 19 19%bv eq_refl), (K2 19%bv ltac:(cbn; tauto)), R19' in X19.
      rewrite (ew_Eimg_Ereg_nat regs3 _ 17 17%bv eq_refl), G17 in X17.
      change 32%nat with (32 + 0)%nat in X5. rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 0 SHADOW_OFF ltac:(lia) eq_refl) in X5.
      change 37%nat with (32 + 5)%nat in X18. rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 5 secw ltac:(lia) eq_refl) in X18.
      rewrite (ew_Eimg_Ereg_nat regs3 _ 24 24%bv eq_refl), (K2 24%bv ltac:(cbn; tauto)), R24_2 in X24.
      rewrite (ew_Eimg_Ereg_nat regs3 _ 22 22%bv eq_refl), (K2 22%bv ltac:(cbn; tauto)), R22_2 in X22.
      (* the model *)
      assert (Htf : PSN.tagged sw FF q = false) by (apply fa_untagged_lt; exact Hc1).
      assert (Htf' : PSN.tagged sw (nxF (n_C cx)) q = false) by exact Htf.
      pose proof (fa_fit_vtag sw (n_C cx) (n_cap cx) (n_p cx) q) as Fvt. fa_inst Fvt.
      pose proof (fa_fit_vid sw (n_C cx) (n_cap cx) (n_p cx) q) as Fvid. fa_inst Fvid.
      pose proof (fa_fit_reclen sw (n_C cx) (n_cap cx) (n_p cx) q) as Frl. fa_inst Frl.
      pose proof (fa_rec_untagged sw (n_C cx) (n_cap cx) (n_p cx) q) as Frec. fa_inst Frec.

      assert (Hrawb : forall x, n_buf cx <= x < n_buf cx + incl ->
         aview SEGS (w_H W2) (ms_mem ms6) x = aview SEGS (w_H W2) mem2 x).
      { intros x Hx. unfold boxed in Hbufps. unfold nx_bufn, PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
        rewrite (KM6 x ltac:(lia) ltac:(destruct Hbufps; lia)), (KM5 x ltac:(lia) ltac:(destruct Hbufps; lia)), Hmem2.
        reflexivity. }
      apply (HTS cx fp k2 ly3 S3 W2 ms6 md6 HB HJ2b HFR).
      apply (fa_land_ts cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x440) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) q 0 0 k2 ly3 S3 W2 ms5 md5 ms6 md6 (n_sp1 cx) (n_sp1 cx) 0 0
        (fa_raw sw (n_C cx) q) HB M5 HAR5 HAR6 HFR EFA Hq Hlh Hq0' Hincl Hfitq).
      -- rewrite Hsh6. reflexivity.
      -- rewrite Hsh6. reflexivity.
      -- rewrite Hsh6. reflexivity.
      -- rewrite Hsh6. reflexivity.
      -- rewrite Hsh6. reflexivity.
      -- rewrite Hsh6. reflexivity.
      -- intros r Hr. cbn in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
          first [ rewrite K6_26, K5_26; reflexivity | rewrite K6, K5; [reflexivity | cbn; tauto | cbn; tauto] ].
      -- unfold AFREAD_STK. lia.
      -- lia.
      -- intros a Ha _ Hn _. apply KM6; [exact Ha | intros X; apply Hn; left; exact X].
      -- intros a _ _ Hp. exact (fa_grows_present _ _ _ a HG6 Hp).
      -- intros a Ha. destruct HJ2b as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
        apply HpresJ. lia.
      -- unfold nx_jbk. destruct HJBK1 as (Hk2a & Haba & Hmoa & Hfda & Hfsa).
        split; [exact Hk2a|]. split; [exact Haba|]. split; [exact Hmoa|].
        split; [rewrite (proj1 Hmd6), (proj1 Hmd5), (proj1 Hmd2); exact Hfda
               | rewrite (proj2 Hmd6), (proj2 Hmd5), (proj2 Hmd2); exact Hfsa].
      -- exact V16b.
      -- exact V20b.
      -- change (n_sw cx =? 1) with sw. rewrite (Fvt (n_lvt cx)), ?Htf, ?Htf'. reflexivity.
      -- change (n_sw cx =? 1) with sw. rewrite (Fvid (n_lvid cx)), ?Htf, ?Htf'. reflexivity.
      -- apply (fa_garr8_keep W2 W2 mem2 (ms_mem ms6)); [|exact HGB].
        intros x Hx. rewrite Frl2 in Hx. rewrite Z2Nat.id in Hx by lia. exact (Hrawb x Hx).
      -- change (n_sw cx =? 1) with sw. symmetry. exact Frec.
      -- rewrite Frl2. change (PSN.incl sw (nxF (n_C cx)) q) with incl. unfold boxed in Hlbj. apply Nat2Z.inj_le.
        rewrite Hlbj, Z2Nat.id by lia. unfold nx_bufn. lia.
      -- exact X16.
      -- exact X19.
      -- exact X17.
      -- exact X5.
      -- change (n_sw cx =? 1) with sw. rewrite X22, Frl. unfold PSN.rec_len. rewrite ?Htf, ?Htf'.
        try change (PSN.incl sw (nxF (n_C cx)) q) with incl. unfold w64. rewrite unsigned_lit_small by lia.
        apply Z.mod_small. lia.
      -- change (n_sw cx =? 1) with sw. rewrite X18. unfold nx_tsec. rewrite Hq. unfold w64. rewrite unsigned_lit_small by lia. exact Hsec.
      -- change (n_sw cx =? 1) with sw. rewrite X24. unfold nx_tusec. rewrite Hq. exact R24.

    * (* s6 >= 18 *)
      rewrite branch_ltu_U in Hc1.
      rewrite (U_atom _ 22%nat incl) in Hc1 by
        (first [ rewrite !ew_ewset_other by lia; rewrite (ew_Eimg_Ereg_nat regs3 _ 22 22%bv eq_refl), (K2 22%bv ltac:(cbn; tauto)); exact R22_2
               | lia ]).
      rewrite U_SLit in Hc1. apply Z.ltb_ge in Hc1. rewrite (zcanon_id 18) in Hc1 by (unfold M64; lia).
      (* the record's bytes 12 .. 15 at ms5 *)
      assert (HGB5 : garr8 SEGS (rdW W2 (ms_mem ms5)) (n_buf cx) (fa_raw sw (n_C cx) q)).
      { apply (fa_garr8_keep W2 W2 mem2 (ms_mem ms5)); [|exact HGB].
        intros x Hx. rewrite Frl2 in Hx. change (PSN.incl sw (nxF (n_C cx)) q) with incl in Hx.
        rewrite Z2Nat.id in Hx by lia.
        unfold boxed in Hbufps. unfold nx_bufn, PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
        rewrite (KM5 x ltac:(lia) ltac:(destruct Hbufps; lia)), Hmem2. reflexivity. }
      assert (VB : forall k, 0 <= k < 4 ->
         val_mem SEGS (rdW W2 (ms_mem ms5)) (n_buf cx + (12 + k)) 1 (PSN.fb FF (q + 28 + k))).
      { intros k Hk. destruct (HGB5 (Z.to_nat (12 + k)) ltac:(rewrite Frl2; change (PSN.incl sw (nxF (n_C cx)) q) with incl; lia)) as (V & _).
        rewrite Z2Nat.id in V by lia.
        rewrite (fa_raw_nth sw (n_C cx) (n_cap cx) q (12 + k) HCb Hq0' ltac:(change (PSN.incl sw (nxF (n_C cx)) q) with incl; lia) Hincl Hfitq) in V.
        replace (q + 16 + (12 + k)) with (q + 28 + k) in V by lia. exact V. }
      pose proof (VB 0 ltac:(lia)) as VB0. pose proof (VB 1 ltac:(lia)) as VB1.
      pose proof (VB 2 ltac:(lia)) as VB2. pose proof (VB 3 ltac:(lia)) as VB3.
      replace (n_buf cx + (12 + 0)) with (n_buf cx + 12) in VB0 by lia.
      replace (n_buf cx + (12 + 1)) with (n_buf cx + 13) in VB1 by lia.
      replace (n_buf cx + (12 + 2)) with (n_buf cx + 14) in VB2 by lia.
      replace (n_buf cx + (12 + 3)) with (n_buf cx + 15) in VB3 by lia.
      replace (q + 28 + 0) with (q + 28) in VB0 by lia. replace (q + 28 + 1) with (q + 29) in VB1 by lia.
      replace (q + 28 + 2) with (q + 30) in VB2 by lia. replace (q + 28 + 3) with (q + 31) in VB3 by lia.
      assert (HSEC5 : nslot cx W2 ms5 NS_SEC secw).
      { unfold nslot. apply (fa_rdword_keep W2 W2 (ms_mem ms2) (ms_mem ms5)); [|exact HSECb].
        intros k Hk. apply KM5; [unfold NS_SEC in *; lia|].
        unfold NS_SEC, PS_VT_OFF, PS_VID_OFF, PS_LEN in *. lia. }
      assert (HPw5 : forall a, n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2 -> apresent (w_H W2) (ms_mem ms5) a).
      { intros a Ha. exact (fa_grows_present _ _ _ a HG5 (HPw a Ha)). }
      assert (R22_5 : getr (ms_regs ms5) 22 = w64 incl).
      { rewrite (K5 22%bv ltac:(cbn; tauto)), (K2 22%bv ltac:(cbn; tauto)). exact R22_2. }
      destruct (fa_seat_buf cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x440) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) NSH_ph (nx_E cx) (q + 16 + incl) (PSN.orig sw FF q) 0 0 (n_tsv cx)
        k2 ly3 S3 W2 ms5 md5 secw (PSN.fb FF (q + 28)) (PSN.fb FF (q + 29)) (PSN.fb FF (q + 30)) (PSN.fb FF (q + 31)) incl
        HB M5 HAR5 HSEC5 (Hfb _) (Hfb _) (Hfb _) (Hfb _) HPw5 R22_5 ltac:(lia) G11_5 G20_5 G10_5 G12_5 G14_5 G15_5 V16 V20 VB0 VB1 VB2 VB3) as (HS5 & SHOK5).
      clear HS3 SHOK3.
      lazymatch type of HS5 with st_ok_pi _ _ ?Ex _ _ => assert (HEId : img_env VAL A_LIM Ex) by apply Eimg_env end.
      set (regs5 := ms_regs ms5) in *.
      assert (U21e : forall X, bv_unsigned (ew (Eimg (Ereg regs5 X)) 21) = n_ps cx).
      { intros X. rewrite (ew_Eimg_Ereg_nat regs5 X 21 21%bv eq_refl), (K5 21%bv ltac:(cbn; tauto)), (K2 21%bv ltac:(cbn; tauto)),
          (KR2 21%bv ltac:(cbn; tauto)), R21.
        unfold w64. apply unsigned_lit_small. unfold PS_LEN in *. lia. }
      paj_run_tok RUN HS5 HJ2b SHOK5 fa_span.
      { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
        eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
        - rewrite ?ew_ewset_other by lia. apply U21e.
        - cbn [YP09.r_wlo YP09.r_whi fa_ps0]. intros a Ha. unfold boxed in HpsWR.
          destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
          apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
          + intros x Hx. rewrite Hab3. exact Hx.
          + intros x Hx. right. exact Hx.
          + exact EFA. }

      lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => is_var msx; rename msx into ms7; set (md7 := mdx) in * end.
      lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
        pose proof (fa_kept_ps _ _ _ _ _ (n_ps cx) H) as Kx;
        specialize (Kx ltac:(clear; vm_compute; reflexivity) ltac:(rewrite ?ew_ewset_other by lia; apply U21e)); clear H end.
      lazymatch goal with H : mem_grows _ (rdW W2 (ms_mem ms7)) |- _ => rename H into HGx end.
      rename Kx into KM_ms7. rename HGx into HG_ms7.
      assert (Hmd_ms7 : m_fds md7 = m_fds md5 /\ m_fs md7 = m_fs md5) by (unfold md7; split; reflexivity).

      psrr_branch_tok RUN BR HS5 SHOK5 fa_span.
      -- (* buf[12] <> 0x81: no tag *)
         rewrite branch_ne_U in Hc2.
         rewrite (U_atom _ 38%nat (PSN.fb FF (q + 28))) in Hc2 by
           (first [ rewrite ?ew_ewset_other by lia; change 38%nat with (32 + 6)%nat;
                    exact (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 6 (PSN.fb FF (q + 28)) ltac:(lia) eq_refl)
                  | pose proof (Hfb (q + 28)); lia ]).
         rewrite U_SLit, (zcanon_id 129) in Hc2 by (unfold M64; lia).
         apply negb_true_iff, Z.eqb_neq in Hc2.

         paj_run_to_tok RUNTO HS5 HJ2b SHOK5 fa_span NP_ts.
      { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
        eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
        - rewrite ?ew_ewset_other by lia. apply U21e.
        - cbn [YP09.r_wlo YP09.r_whi fa_ps0]. intros a Ha. unfold boxed in HpsWR.
          destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
          apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
          + intros x Hx. rewrite Hab3. exact Hx.
          + intros x Hx. right. exact Hx.
          + exact EFA. }

      lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => is_var msx; rename msx into ms8; set (md8 := mdx) in * end.
      lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
        pose proof (fa_kept_ps _ _ _ _ _ (n_ps cx) H) as Kx;
        specialize (Kx ltac:(clear; vm_compute; reflexivity) ltac:(rewrite ?ew_ewset_other by lia; apply U21e)); clear H end.
      lazymatch goal with H : mem_grows _ (rdW W2 (ms_mem ms8)) |- _ => rename H into HGx end.
      assert (KM_ms8 : forall a, 0 <= a < 2 ^ 64 -> ~ (n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) ->
        aview SEGS (w_H W2) (ms_mem ms8) a = aview SEGS (w_H W2) (ms_mem ms5) a)
        by (intros a Ha Hn; rewrite (Kx a Ha Hn); exact (KM_ms7 a Ha Hn)).
      clear Kx.
      pose proof (mem_grows_trans _ _ _ HG_ms7 HGx) as HG_ms8. clear HGx.
      assert (Hmd_ms8 : m_fds md8 = m_fds md5 /\ m_fs md8 = m_fs md5).
      { split; [transitivity (m_fds md7); [unfold md8; reflexivity | exact (proj1 Hmd_ms7)]
               | transitivity (m_fs md7); [unfold md8; reflexivity | exact (proj2 Hmd_ms7)]]. }

      pose proof (proj1 HJ2b) as HAR_ms8.
      lazymatch type of HS5 with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms8 HS5 eq_refl) as Hsh_ms8 end.
      fa_kept HS5 regs5 XTe ([2; 3; 4; 8; 9; 21; 23; 25; 27]%bv : list (bv 5)) K_ms8.
      assert (K_ms8_26 : getr (ms_regs ms8) 26 = getr regs5 26).
      { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms8 26%bv HS5) as H. cbn [restrict ms_regs] in H.
        lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
        rewrite H, denot_lit_U, (fa_U_shx _ (n_ps cx)).
        - rewrite K5_26, K2_26, (KR2 26%bv ltac:(cbn; tauto)). symmetry; exact R26.
        - rewrite ?ew_ewset_other by lia. rewrite (ew_Eimg_Ereg_nat regs5 XTe 21 21%bv eq_refl).
          rewrite (K5 21%bv ltac:(cbn; tauto)), (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)). exact R21.
        - rewrite ?ew_ewset_other by lia. exact (ew_Ereg_extra regs5 XTe 0).
        - unfold PS_LEN in *. lia. }
      lazymatch type of HS5 with st_ok_pi _ _ ?Ex ?ss _ =>
        let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
        lazymatch r with Some ?rr =>
          pose proof (fa_chunk_val Ex ss _ 1 rr 16 4 (SLit 0) 0 HS5 ltac:(clear; vm_compute; reflexivity)
            ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as V16_ms8;
          pose proof (fa_chunk_val Ex ss _ 1 rr 20 2 (SLit 0) 0 HS5 ltac:(clear; vm_compute; reflexivity)
            ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as V20_ms8
        end end.
      cbn [restrict ms_mem base_val YP09.r_base] in V16_ms8, V20_ms8.
      rewrite ?ew_ewset_other in V16_ms8, V20_ms8 by lia. rewrite U21e in V16_ms8, V20_ms8.
      change (N.to_nat 4) with 4%nat in V16_ms8. change (N.to_nat 2) with 2%nat in V20_ms8.
      change 16 with PS_VT_OFF in V16_ms8. change 20 with PS_VID_OFF in V20_ms8.
      fa_rv HS5 (16%bv : bv 5) X16. fa_rv HS5 (19%bv : bv 5) X19. fa_rv HS5 (17%bv : bv 5) X17.
      fa_rv HS5 (5%bv : bv 5) X5. fa_rv HS5 (18%bv : bv 5) X18. fa_rv HS5 (24%bv : bv 5) X24. fa_rv HS5 (22%bv : bv 5) X22.
      change 35%nat with (32 + 3)%nat in X16, X19. change 36%nat with (32 + 4)%nat in X17. change 32%nat with (32 + 0)%nat in X5.
      rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 3 (nF cx fp) ltac:(lia) eq_refl) in X16.
      rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 3 (nF cx fp) ltac:(lia) eq_refl) in X19.
      rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 4 (n_ts cx) ltac:(lia) eq_refl) in X17.
      rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 0 SHADOW_OFF ltac:(lia) eq_refl) in X5.
      rewrite (ew_Eimg_Ereg_nat regs5 _ 18 18%bv eq_refl), G18_5 in X18.
      rewrite (ew_Eimg_Ereg_nat regs5 _ 24 24%bv eq_refl), (K5 24%bv ltac:(cbn; tauto)), (K2 24%bv ltac:(cbn; tauto)), R24_2 in X24.
      rewrite (ew_Eimg_Ereg_nat regs5 _ 22 22%bv eq_refl), R22_5 in X22.
      assert (Htf : PSN.tagged sw FF q = false) by (apply fa_untagged_12; exact Hc2).
      assert (Htf' : PSN.tagged sw (nxF (n_C cx)) q = false) by exact Htf.
      pose proof (fa_fit_vtag sw (n_C cx) (n_cap cx) (n_p cx) q) as Fvt. fa_inst Fvt.
      pose proof (fa_fit_vid sw (n_C cx) (n_cap cx) (n_p cx) q) as Fvid. fa_inst Fvid.
      pose proof (fa_fit_reclen sw (n_C cx) (n_cap cx) (n_p cx) q) as Frl. fa_inst Frl.
      pose proof (fa_rec_untagged sw (n_C cx) (n_cap cx) (n_p cx) q) as Frec. fa_inst Frec.
      apply (HTS cx fp k2 ly3 S3 W2 ms8 md8 HB HJ2b HFR).
      apply (fa_land_ts cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x440) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) q 0 0 k2 ly3 S3 W2 ms5 md5 ms8 md8 (n_sp1 cx) (n_sp1 cx) 0 0
        (fa_raw sw (n_C cx) q) HB M5 HAR5 HAR_ms8 HFR EFA Hq Hlh Hq0' Hincl Hfitq).
      ++ rewrite Hsh_ms8. reflexivity.
      ++ rewrite Hsh_ms8. reflexivity.
      ++ rewrite Hsh_ms8. reflexivity.
      ++ rewrite Hsh_ms8. reflexivity.
      ++ rewrite Hsh_ms8. reflexivity.
      ++ rewrite Hsh_ms8. reflexivity.
      ++ intros r Hr. cbn in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
          first [ exact K_ms8_26 | apply K_ms8; cbn; tauto ].
      ++ unfold AFREAD_STK. lia.
      ++ lia.
      ++ intros a Ha _ Hn _. apply KM_ms8; [exact Ha | intros X; apply Hn; left; exact X].
      ++ intros a _ _ Hp. exact (fa_grows_present _ _ _ a HG_ms8 Hp).
      ++ intros a Ha. destruct HJ2b as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
        apply HpresJ. lia.
      ++ unfold nx_jbk. destruct HJBK1 as (Hk2a & Haba & Hmoa & Hfda & Hfsa).
        split; [exact Hk2a|]. split; [exact Haba|]. split; [exact Hmoa|].
        split; [rewrite (proj1 Hmd_ms8), (proj1 Hmd5), (proj1 Hmd2); exact Hfda
               | rewrite (proj2 Hmd_ms8), (proj2 Hmd5), (proj2 Hmd2); exact Hfsa].
      ++ exact V16_ms8.
      ++ exact V20_ms8.
      ++ change (n_sw cx =? 1) with sw. rewrite (Fvt (n_lvt cx)), ?Htf, ?Htf'. reflexivity.
      ++ change (n_sw cx =? 1) with sw. rewrite (Fvid (n_lvid cx)), ?Htf, ?Htf'. reflexivity.
      ++ apply (fa_garr8_keep W2 W2 (ms_mem ms5) (ms_mem ms8)); [|exact HGB5].
        intros x Hx. rewrite Frl2 in Hx. change (PSN.incl sw (nxF (n_C cx)) q) with incl in Hx.
        rewrite Z2Nat.id in Hx by lia.
        unfold boxed in Hbufps. unfold nx_bufn, PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
        apply KM_ms8; [lia | destruct Hbufps; lia].
      ++ change (n_sw cx =? 1) with sw. symmetry. exact Frec.
      ++ rewrite Frl2. change (PSN.incl sw (nxF (n_C cx)) q) with incl. unfold boxed in Hlbj. apply Nat2Z.inj_le.
        rewrite Hlbj, Z2Nat.id by lia. unfold nx_bufn. lia.
      ++ exact X16.
      ++ exact X19.
      ++ exact X17.
      ++ exact X5.
      ++ change (n_sw cx =? 1) with sw. rewrite X22, Frl. unfold PSN.rec_len. rewrite ?Htf, ?Htf'.
        try change (PSN.incl sw (nxF (n_C cx)) q) with incl. unfold w64. rewrite unsigned_lit_small by lia.
        apply Z.mod_small. lia.
      ++ change (n_sw cx =? 1) with sw. rewrite X18. unfold nx_tsec. rewrite Hq. rewrite unsigned_lit_small by lia. exact Hsec.
      ++ change (n_sw cx =? 1) with sw. rewrite X24. unfold nx_tusec. rewrite Hq. exact R24.

      -- (* buf[12] = 0x81 *)
         paj_run_tok RUN HS5 HJ2b SHOK5 fa_span.
      { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
        eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
        - rewrite ?ew_ewset_other by lia. apply U21e.
        - cbn [YP09.r_wlo YP09.r_whi fa_ps0]. intros a Ha. unfold boxed in HpsWR.
          destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
          apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
          + intros x Hx. rewrite Hab3. exact Hx.
          + intros x Hx. right. exact Hx.
          + exact EFA. }

      lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => is_var msx; rename msx into ms9; set (md9 := mdx) in * end.
      lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
        pose proof (fa_kept_ps _ _ _ _ _ (n_ps cx) H) as Kx;
        specialize (Kx ltac:(clear; vm_compute; reflexivity) ltac:(rewrite ?ew_ewset_other by lia; apply U21e)); clear H end.
      lazymatch goal with H : mem_grows _ (rdW W2 (ms_mem ms9)) |- _ => rename H into HGx end.
      assert (KM_ms9 : forall a, 0 <= a < 2 ^ 64 -> ~ (n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) ->
        aview SEGS (w_H W2) (ms_mem ms9) a = aview SEGS (w_H W2) (ms_mem ms5) a)
        by (intros a Ha Hn; rewrite (Kx a Ha Hn); exact (KM_ms7 a Ha Hn)).
      clear Kx.
      pose proof (mem_grows_trans _ _ _ HG_ms7 HGx) as HG_ms9. clear HGx.
      assert (Hmd_ms9 : m_fds md9 = m_fds md5 /\ m_fs md9 = m_fs md5).
      { split; [transitivity (m_fds md7); [unfold md9; reflexivity | exact (proj1 Hmd_ms7)]
               | transitivity (m_fs md7); [unfold md9; reflexivity | exact (proj2 Hmd_ms7)]]. }

         psrr_branch_tok RUN BR HS5 SHOK5 fa_span.
         ** (* buf[13] <> 0: no tag *)
            rewrite branch_ne_U in Hc3.
            rewrite (U_atom _ 39%nat (PSN.fb FF (q + 29))) in Hc3 by
              (first [ rewrite ?ew_ewset_other by lia; change 39%nat with (32 + 7)%nat;
                       exact (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 7 (PSN.fb FF (q + 29)) ltac:(lia) eq_refl)
                     | pose proof (Hfb (q + 29)); lia ]).
            rewrite U_SLit, (zcanon_id 0) in Hc3 by (unfold M64; lia).
            apply negb_true_iff, Z.eqb_neq in Hc3.

            paj_run_to_tok RUNTO HS5 HJ2b SHOK5 fa_span NP_ts.
      { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
        eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
        - rewrite ?ew_ewset_other by lia. apply U21e.
        - cbn [YP09.r_wlo YP09.r_whi fa_ps0]. intros a Ha. unfold boxed in HpsWR.
          destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
          apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
          + intros x Hx. rewrite Hab3. exact Hx.
          + intros x Hx. right. exact Hx.
          + exact EFA. }

      lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => is_var msx; rename msx into ms10; set (md10 := mdx) in * end.
      lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
        pose proof (fa_kept_ps _ _ _ _ _ (n_ps cx) H) as Kx;
        specialize (Kx ltac:(clear; vm_compute; reflexivity) ltac:(rewrite ?ew_ewset_other by lia; apply U21e)); clear H end.
      lazymatch goal with H : mem_grows _ (rdW W2 (ms_mem ms10)) |- _ => rename H into HGx end.
      assert (KM_ms10 : forall a, 0 <= a < 2 ^ 64 -> ~ (n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) ->
        aview SEGS (w_H W2) (ms_mem ms10) a = aview SEGS (w_H W2) (ms_mem ms5) a)
        by (intros a Ha Hn; rewrite (Kx a Ha Hn); exact (KM_ms9 a Ha Hn)).
      clear Kx.
      pose proof (mem_grows_trans _ _ _ HG_ms9 HGx) as HG_ms10. clear HGx.
      assert (Hmd_ms10 : m_fds md10 = m_fds md5 /\ m_fs md10 = m_fs md5).
      { split; [transitivity (m_fds md9); [unfold md10; reflexivity | exact (proj1 Hmd_ms9)]
               | transitivity (m_fs md9); [unfold md10; reflexivity | exact (proj2 Hmd_ms9)]]. }

      pose proof (proj1 HJ2b) as HAR_ms10.
      lazymatch type of HS5 with st_ok_pi _ _ _ ?ss _ =>
        pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss ms10 HS5 eq_refl) as Hsh_ms10 end.
      fa_kept HS5 regs5 XTe ([2; 3; 4; 8; 9; 21; 23; 25; 27]%bv : list (bv 5)) K_ms10.
      assert (K_ms10_26 : getr (ms_regs ms10) 26 = getr regs5 26).
      { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ ms10 26%bv HS5) as H. cbn [restrict ms_regs] in H.
        lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
        rewrite H, denot_lit_U, (fa_U_shx _ (n_ps cx)).
        - rewrite K5_26, K2_26, (KR2 26%bv ltac:(cbn; tauto)). symmetry; exact R26.
        - rewrite ?ew_ewset_other by lia. rewrite (ew_Eimg_Ereg_nat regs5 XTe 21 21%bv eq_refl).
          rewrite (K5 21%bv ltac:(cbn; tauto)), (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)). exact R21.
        - rewrite ?ew_ewset_other by lia. exact (ew_Ereg_extra regs5 XTe 0).
        - unfold PS_LEN in *. lia. }
      lazymatch type of HS5 with st_ok_pi _ _ ?Ex ?ss _ =>
        let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
        lazymatch r with Some ?rr =>
          pose proof (fa_chunk_val Ex ss _ 1 rr 16 4 (SLit 0) 0 HS5 ltac:(clear; vm_compute; reflexivity)
            ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as V16_ms10;
          pose proof (fa_chunk_val Ex ss _ 1 rr 20 2 (SLit 0) 0 HS5 ltac:(clear; vm_compute; reflexivity)
            ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as V20_ms10
        end end.
      cbn [restrict ms_mem base_val YP09.r_base] in V16_ms10, V20_ms10.
      rewrite ?ew_ewset_other in V16_ms10, V20_ms10 by lia. rewrite U21e in V16_ms10, V20_ms10.
      change (N.to_nat 4) with 4%nat in V16_ms10. change (N.to_nat 2) with 2%nat in V20_ms10.
      change 16 with PS_VT_OFF in V16_ms10. change 20 with PS_VID_OFF in V20_ms10.
      fa_rv HS5 (16%bv : bv 5) X16. fa_rv HS5 (19%bv : bv 5) X19. fa_rv HS5 (17%bv : bv 5) X17.
      fa_rv HS5 (5%bv : bv 5) X5. fa_rv HS5 (18%bv : bv 5) X18. fa_rv HS5 (24%bv : bv 5) X24. fa_rv HS5 (22%bv : bv 5) X22.
      change 35%nat with (32 + 3)%nat in X16, X19. change 36%nat with (32 + 4)%nat in X17. change 32%nat with (32 + 0)%nat in X5.
      rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 3 (nF cx fp) ltac:(lia) eq_refl) in X16.
      rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 3 (nF cx fp) ltac:(lia) eq_refl) in X19.
      rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 4 (n_ts cx) ltac:(lia) eq_refl) in X17.
      rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 0 SHADOW_OFF ltac:(lia) eq_refl) in X5.
      rewrite (ew_Eimg_Ereg_nat regs5 _ 18 18%bv eq_refl), G18_5 in X18.
      rewrite (ew_Eimg_Ereg_nat regs5 _ 24 24%bv eq_refl), (K5 24%bv ltac:(cbn; tauto)), (K2 24%bv ltac:(cbn; tauto)), R24_2 in X24.
      rewrite (ew_Eimg_Ereg_nat regs5 _ 22 22%bv eq_refl), R22_5 in X22.
      assert (Htf : PSN.tagged sw FF q = false) by (apply fa_untagged_13; exact Hc3).
      assert (Htf' : PSN.tagged sw (nxF (n_C cx)) q = false) by exact Htf.
      pose proof (fa_fit_vtag sw (n_C cx) (n_cap cx) (n_p cx) q) as Fvt. fa_inst Fvt.
      pose proof (fa_fit_vid sw (n_C cx) (n_cap cx) (n_p cx) q) as Fvid. fa_inst Fvid.
      pose proof (fa_fit_reclen sw (n_C cx) (n_cap cx) (n_p cx) q) as Frl. fa_inst Frl.
      pose proof (fa_rec_untagged sw (n_C cx) (n_cap cx) (n_p cx) q) as Frec. fa_inst Frec.
      apply (HTS cx fp k2 ly3 S3 W2 ms10 md10 HB HJ2b HFR).
      apply (fa_land_ts cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x440) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) q 0 0 k2 ly3 S3 W2 ms5 md5 ms10 md10 (n_sp1 cx) (n_sp1 cx) 0 0
        (fa_raw sw (n_C cx) q) HB M5 HAR5 HAR_ms10 HFR EFA Hq Hlh Hq0' Hincl Hfitq).
      *** rewrite Hsh_ms10. reflexivity.
      *** rewrite Hsh_ms10. reflexivity.
      *** rewrite Hsh_ms10. reflexivity.
      *** rewrite Hsh_ms10. reflexivity.
      *** rewrite Hsh_ms10. reflexivity.
      *** rewrite Hsh_ms10. reflexivity.
      *** intros r Hr. cbn in Hr.
        destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
          first [ exact K_ms10_26 | apply K_ms10; cbn; tauto ].
      *** unfold AFREAD_STK. lia.
      *** lia.
      *** intros a Ha _ Hn _. apply KM_ms10; [exact Ha | intros X; apply Hn; left; exact X].
      *** intros a _ _ Hp. exact (fa_grows_present _ _ _ a HG_ms10 Hp).
      *** intros a Ha. destruct HJ2b as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
        apply HpresJ. lia.
      *** unfold nx_jbk. destruct HJBK1 as (Hk2a & Haba & Hmoa & Hfda & Hfsa).
        split; [exact Hk2a|]. split; [exact Haba|]. split; [exact Hmoa|].
        split; [rewrite (proj1 Hmd_ms10), (proj1 Hmd5), (proj1 Hmd2); exact Hfda
               | rewrite (proj2 Hmd_ms10), (proj2 Hmd5), (proj2 Hmd2); exact Hfsa].
      *** exact V16_ms10.
      *** exact V20_ms10.
      *** change (n_sw cx =? 1) with sw. rewrite (Fvt (n_lvt cx)), ?Htf, ?Htf'. reflexivity.
      *** change (n_sw cx =? 1) with sw. rewrite (Fvid (n_lvid cx)), ?Htf, ?Htf'. reflexivity.
      *** apply (fa_garr8_keep W2 W2 (ms_mem ms5) (ms_mem ms10)); [|exact HGB5].
        intros x Hx. rewrite Frl2 in Hx. change (PSN.incl sw (nxF (n_C cx)) q) with incl in Hx.
        rewrite Z2Nat.id in Hx by lia.
        unfold boxed in Hbufps. unfold nx_bufn, PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
        apply KM_ms10; [lia | destruct Hbufps; lia].
      *** change (n_sw cx =? 1) with sw. symmetry. exact Frec.
      *** rewrite Frl2. change (PSN.incl sw (nxF (n_C cx)) q) with incl. unfold boxed in Hlbj. apply Nat2Z.inj_le.
        rewrite Hlbj, Z2Nat.id by lia. unfold nx_bufn. lia.
      *** exact X16.
      *** exact X19.
      *** exact X17.
      *** exact X5.
      *** change (n_sw cx =? 1) with sw. rewrite X22, Frl. unfold PSN.rec_len. rewrite ?Htf, ?Htf'.
        try change (PSN.incl sw (nxF (n_C cx)) q) with incl. unfold w64. rewrite unsigned_lit_small by lia.
        apply Z.mod_small. lia.
      *** change (n_sw cx =? 1) with sw. rewrite X18. unfold nx_tsec. rewrite Hq. rewrite unsigned_lit_small by lia. exact Hsec.
      *** change (n_sw cx =? 1) with sw. rewrite X24. unfold nx_tusec. rewrite Hq. exact R24.

         ** (* the tag *)
            rewrite branch_ne_U in Hc2.
            rewrite (U_atom _ 38%nat (PSN.fb FF (q + 28))) in Hc2 by
              (first [ rewrite ?ew_ewset_other by lia; change 38%nat with (32 + 6)%nat;
                       exact (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 6 (PSN.fb FF (q + 28)) ltac:(lia) eq_refl)
                     | pose proof (Hfb (q + 28)); lia ]).
            rewrite U_SLit, (zcanon_id 129) in Hc2 by (unfold M64; lia).
            apply negb_false_iff, Z.eqb_eq in Hc2.
            rewrite branch_ne_U in Hc3.
            rewrite (U_atom _ 39%nat (PSN.fb FF (q + 29))) in Hc3 by
              (first [ rewrite ?ew_ewset_other by lia; change 39%nat with (32 + 7)%nat;
                       exact (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 7 (PSN.fb FF (q + 29)) ltac:(lia) eq_refl)
                     | pose proof (Hfb (q + 29)); lia ]).
            rewrite U_SLit, (zcanon_id 0) in Hc3 by (unfold M64; lia).
            apply negb_false_iff, Z.eqb_eq in Hc3.
            assert (Htt : PSN.tagged sw FF q = true) by (apply fa_tagged; [exact Hc1 | exact Hc2 | exact Hc3]).
            paj_run_tok RUN HS5 HJ2b SHOK5 fa_span.
            { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|].
              eapply awr_ok_cons_gen; [reflexivity | | | apply awr_ok_cons_ro; [cbn; lia | apply awr_ok_nil]].
              - rewrite ?ew_ewset_other by lia. apply U21e.
              - cbn [YP09.r_wlo YP09.r_whi fa_ps0]. intros a Ha. unfold boxed in HpsWR.
                destruct (HpsWR Hh a ltac:(unfold PS_VT_OFF, PS_VID_OFF, PS_LEN in *; lia)) as (Hw & _).
                apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
                + intros x Hx. rewrite Hab3. exact Hx.
                + intros x Hx. right. exact Hx.
                + exact EFA. }

            lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => is_var msx; rename msx into msC; set (mdC := mdx) in * end.
            lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
              pose proof (fa_kept_ps _ _ _ _ _ (n_ps cx) H) as Kx;
              specialize (Kx ltac:(clear; vm_compute; reflexivity) ltac:(rewrite ?ew_ewset_other by lia; apply U21e)); clear H end.
            lazymatch goal with H : mem_grows _ (rdW W2 (ms_mem msC)) |- _ => rename H into HGx end.
            assert (KM_msC : forall a, 0 <= a < 2 ^ 64 -> ~ (n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) ->
              aview SEGS (w_H W2) (ms_mem msC) a = aview SEGS (w_H W2) (ms_mem ms5) a)
              by (intros a Ha Hn; rewrite (Kx a Ha Hn); exact (KM_ms9 a Ha Hn)).
            clear Kx.
            pose proof (mem_grows_trans _ _ _ HG_ms9 HGx) as HG_msC. clear HGx.
            assert (Hmd_msC : m_fds mdC = m_fds md5 /\ m_fs mdC = m_fs md5).
            { split; [transitivity (m_fds md9); [unfold mdC; reflexivity | exact (proj1 Hmd_ms9)]
                     | transitivity (m_fs md9); [unfold mdC; reflexivity | exact (proj2 Hmd_ms9)]]. }

            (* the call of __asan_memmove at 0x81af4 *)
            assert (HAE5 : env_agree 32 (Ereg regs5 XTe)
              (ewset (ewset (ewset (ewset (ewset (ewset (ewset (ewset (ewset (ewset
                (Eimg (Ereg regs5 XTe)) 512 w1) 513 w2) 512 w3) 513 w4) 512 w5) 513 w6) 514 w7) 515 w8) 516 w9) 517 w10))
              by (split; [intros n Hn; rewrite !ew_ewset_other by lia; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
            pose proof (regs_kept_of_st_ok SEGS _ _ (restrict (w_H W2) msC) regs5 XTe
              [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 27]%bv HS5 HAE5 ltac:(clear; vm_compute; reflexivity)) as KC.
            cbn [restrict ms_regs] in KC.

            (* the registers and the struct's tag fields at the call *)
            fa_rv_st HS5 (1%bv : bv 5) QC1. rewrite (img_env_codeptr _ HEId) in QC1.
            fa_rv_st HS5 (10%bv : bv 5) QC10. fa_rv_st HS5 (11%bv : bv 5) QC11.
            change 34%nat with (32 + 2)%nat in QC10, QC11.
            rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 2 (n_buf cx) ltac:(lia) eq_refl), unsigned_lit_small in QC10 by (unfold nx_bufn in *; lia).
            rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 2 (n_buf cx) ltac:(lia) eq_refl), unsigned_lit_small in QC11 by (unfold nx_bufn in *; lia).
            assert (QC12 : getr (ms_regs msC) 12 = w64 (incl - 16)).
            { pose proof (st_ok_restrict_reg SEGS (w_H W2) _ _ msC 12%bv HS5) as H. cbn [restrict ms_regs] in H.
              lazymatch type of H with _ = sv_denot _ ?e =>
                let e' := eval vm_compute in e in change e with e' in H end.
              rewrite H, denot_lit_U, (fa_U_len16 _ incl); [reflexivity | | unfold NX_CAP_MAX in *; lia].
              rewrite !ew_ewset_other by lia. rewrite (ew_Eimg_Ereg_nat regs5 _ 22 22%bv eq_refl). exact R22_5. }
            lazymatch type of HS5 with st_ok _ ?Ex ?ss _ =>
              let r := eval vm_compute in (nth_error (ss_mem ss) 1) in
              lazymatch r with Some ?rr =>
                pose proof (fa_chunk_val_st Ex ss _ 1 rr 16 4 (SLit 1) 1 HS5 ltac:(clear; vm_compute; reflexivity)
                  ltac:(clear; cbn; tauto) eq_refl ltac:(lia) ltac:(lia)) as VC16;
                assert (DV : sv_denot Ex (SAlu ALU_OR (SAlu ALU_AND (SAlu ALU_SLL (SOff 40 0) (SLit 8)) (SLit 3840)) (SOff 41 0))
                             = Z_to_bv 64 (PSN.rec_vid FF q))
                  by (rewrite denot_lit_U, (fa_U_vid _ (PSN.fb FF (q + 30)) (PSN.fb FF (q + 31)));
                      [ reflexivity
                      | rewrite !ew_ewset_other by lia; change 40%nat with (32 + 8)%nat;
                        exact (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 8 _ ltac:(lia) eq_refl)
                      | rewrite !ew_ewset_other by lia; change 41%nat with (32 + 9)%nat;
                        exact (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 9 _ ltac:(lia) eq_refl)
                      | exact (Hfb (q + 30)) | exact (Hfb (q + 31)) ]);
                pose proof (fa_chunk_val_st Ex ss _ 1 rr 20 2 _ (PSN.rec_vid FF q) HS5 ltac:(clear; vm_compute; reflexivity)
                  ltac:(clear; cbn; tauto) DV ltac:(unfold PSN.rec_vid; cbn; pose proof (Z.mod_pos_bound (256 * PSN.fb FF (q + 30) + PSN.fb FF (q + 31)) 4096 ltac:(lia)); lia) ltac:(lia)) as VC20
              end end.
            cbn [restrict ms_mem base_val YP09.r_base] in VC16, VC20.
            rewrite !ew_ewset_other in VC16, VC20 by lia. rewrite U21e in VC16, VC20.
            change (N.to_nat 4) with 4%nat in VC16. change (N.to_nat 2) with 2%nat in VC20.
            change 16 with PS_VT_OFF in VC16. change 20 with PS_VID_OFF in VC20.
            pmkst HS5.

            assert (HspC : spZ (ms_regs msC) = n_sp1 cx).
            { unfold spZ in *. rewrite (KC 2%bv ltac:(cbn; tauto)), (K5 2%bv ltac:(cbn; tauto)), (K2 2%bv ltac:(cbn; tauto)). exact U2'. }
            pose proof HJ2b as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HstJ & _).
            pose proof HstJ as (Hal0 & _).
            pose proof (proj1 HJ2b) as HARC.
            destruct (al_blocks _ _ LAWS ly3 S3 W2 (ms_mem msC) mdC _ _ HARC Hbuf3) as (_ & _ & _ & _ & HpresC & _).
            pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
            eapply SRr_bind.
            { apply (aj_memmove_atS SEGS B LAWS pa_segs_low (SIGMA PS___asan_memmove) H_memmove W2 (ms_regs msC) (ms_mem msC)
                (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
                ((NX_CID, fp) :: n_own cx) ly3 S3 mdC k2 (n_buf cx + 12) (n_buf cx + 16) (incl - 16)
                (n_sp1 cx - n_sp0 cx) (getr (ms_regs msC) 1)).
              - exact HJ2b.
              - exact QC10.
              - exact QC11.
              - exact QC12.
              - unfold NX_CAP_MAX in *. lia.
              - lia.
              - unfold nx_bufn in *. lia.
              - rewrite HspC. lia.
              - clear - Hal0 Hsp1al. apply Z.mod_divide in Hal0; [|lia]. apply Z.mod_divide in Hsp1al; [|lia].
                destruct Hal0 as [k0 Hk0]. destruct Hsp1al as [k1 Hk1]. apply Z.mod_divide; [lia|].
                exists (2 * k1 - k0). lia.
              - lia.
              - change ESTACK with 4096. unfold AFREAD_STK in *. lia.
              - rewrite (KC 3%bv ltac:(cbn; tauto)), (K5 3%bv ltac:(cbn; tauto)), (K2 3%bv ltac:(cbn; tauto)),
                  (KR2 3%bv ltac:(cbn; tauto)), R3. exact Hgp.
              - rewrite (KC 4%bv ltac:(cbn; tauto)), (K5 4%bv ltac:(cbn; tauto)), (K2 4%bv ltac:(cbn; tauto)),
                  (KR2 4%bv ltac:(cbn; tauto)), R4. exact Htp.
              - reflexivity.
              - rewrite QC1. apply ret_ok_codeptr_v; [lia | reflexivity].
              - intros a Ha. destruct (HbufWR a ltac:(unfold nx_bufn in *; lia)) as (Hw & Hnw).
                split; [|change ESTACK with 4096; unfold nx_bufn in *; lia].
                apply (awr_byte_weaken _ _ _ _ (ablocks B (n_lyc cx) (n_Sc cx)) _ (n_lyc cx) _ (n_own cx)); [| | |exact Hw].
                + intros x Hx. rewrite Hab3. exact Hx.
                + intros x Hx. right. exact Hx.
                + exact EFA.
              - apply (amem_range_of_block SEGS B LAWS ly3 S3 W2 (ms_mem msC) mdC (n_buf cx) (nx_bufn (n_cap cx)));
                  [exact HARC | exact Hbuf3 | lia | unfold nx_bufn in *; lia].
              - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W2 (ms_mem msC) mdC (n_buf cx) (nx_bufn (n_cap cx))
                  (n_buf cx + 12) (incl - 16) HARC Hbuf3 ltac:(lia) ltac:(unfold nx_bufn in *; lia)).
              - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W2 (ms_mem msC) mdC (n_buf cx) (nx_bufn (n_cap cx))
                  (n_buf cx + 12) (incl - 16) HARC Hbuf3 ltac:(lia) ltac:(unfold nx_bufn in *; lia) Hpos).
              - lia.
              - unfold nx_bufn in *. lia.
              - intros a Ha. split; [|rewrite HspC; change ESTACK with 4096; unfold nx_bufn in *; lia].
                apply fa_aview_present. exact (proj1 (HpresC a ltac:(unfold nx_bufn in *; lia))).
              - apply (amem_range_of_block SEGS B LAWS ly3 S3 W2 (ms_mem msC) mdC (n_buf cx) (nx_bufn (n_cap cx)));
                  [exact HARC | exact Hbuf3 | lia | unfold nx_bufn in *; lia].
              - exact (range_addressable_of_block SEGS B LAWS ly3 S3 W2 (ms_mem msC) mdC (n_buf cx) (nx_bufn (n_cap cx))
                  (n_buf cx + 16) (incl - 16) HARC Hbuf3 ltac:(lia) ltac:(unfold nx_bufn in *; lia)).
              - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly3 S3 W2 (ms_mem msC) mdC (n_buf cx) (nx_bufn (n_cap cx))
                  (n_buf cx + 16) (incl - 16) HARC Hbuf3 ltac:(lia) ltac:(unfold nx_bufn in *; lia) Hpos). }
            cbv beta. intros W3' c3 Hwle3 (-> & regsR & memR & mdR & -> & HJR & HPR & R10R & HMV & HKR & HPRES & HSBM).

            rewrite QC1.
            assert (K_C26 : getr (ms_regs msC) 26 = getr regs5 26).
            { pose proof (st_ok_restrict_reg SEGS (w_H W2) _ _ msC 26%bv HS5) as H. cbn [restrict ms_regs] in H.
              lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
              rewrite H, denot_lit_U, (fa_U_shx _ (n_ps cx)).
              - rewrite K5_26, K2_26, (KR2 26%bv ltac:(cbn; tauto)). symmetry; exact R26.
              - rewrite ?ew_ewset_other by lia. rewrite (ew_Eimg_Ereg_nat regs5 XTe 21 21%bv eq_refl).
                rewrite (K5 21%bv ltac:(cbn; tauto)), (K2 21%bv ltac:(cbn; tauto)), (KR2 21%bv ltac:(cbn; tauto)). exact R21.
              - rewrite ?ew_ewset_other by lia. exact (ew_Ereg_extra regs5 XTe 0).
              - unfold PS_LEN in *. lia. }
            assert (KRR : forall r, In r [2; 3; 4; 8; 9; 18; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regsR r = getr regs5 r).
            { intros r Hr. cbn in Hr.
              destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]];
                (rewrite (fa_pres _ _ _ HPR) by (match goal with |- acallee_saved (bv_unsigned ?r) =>
                   let z := eval vm_compute in (bv_unsigned r) in change (acallee_saved z) end; unfold acallee_saved; lia));
                first [ exact K_C26 | apply KC; cbn; tauto ]. }
            assert (HmdR : m_fds mdR = m_fds md5 /\ m_fs mdR = m_fs md5).
            { rewrite HSBM. split; [transitivity (m_fds mdC); [reflexivity | exact (proj1 Hmd_msC)]
                                   | transitivity (m_fs mdC); [reflexivity | exact (proj2 Hmd_msC)]]. }
            assert (KMR : forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx - 4096 <= a < n_sp1 cx) ->
               ~ (n_ps cx + PS_VT_OFF <= a < n_ps cx + PS_VID_OFF + 2) -> ~ (n_buf cx + 12 <= a < n_buf cx + incl - 4) ->
               aview SEGS (w_H W2) memR a = aview SEGS (w_H W2) (ms_mem ms5) a).
            { intros a Ha Hw Ht Hb. rewrite (HKR a Ha ltac:(lia) ltac:(change ESTACK with 4096; lia)). exact (KM_msC a Ha Ht). }
            assert (VR16 : val_mem SEGS (rdW W2 memR) (n_ps cx + PS_VT_OFF) 4 1).
            { apply (fa_vm_keep W2 W2 (ms_mem msC) memR); [|exact VC16]. intros x Hx. cbn [Z.of_nat] in Hx.
              unfold boxed in Hbufps. unfold nx_bufn, PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
              apply HKR; [lia | destruct Hbufps; lia | change ESTACK with 4096; lia]. }
            assert (VR20 : val_mem SEGS (rdW W2 memR) (n_ps cx + PS_VID_OFF) 2 (PSN.rec_vid FF q)).
            { apply (fa_vm_keep W2 W2 (ms_mem msC) memR); [|exact VC20]. intros x Hx. cbn [Z.of_nat] in Hx.
              unfold boxed in Hbufps. unfold nx_bufn, PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
              apply HKR; [lia | destruct Hbufps; lia | change ESTACK with 4096; lia]. }
            assert (MR : nx_mid B MT KS cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) NSH_ph (nx_E cx) (q + 16 + incl) (PSN.orig sw FF q) 1 (PSN.rec_vid FF q)
              (n_tsv cx) k2 ly3 S3 W2 (mkst regsR (Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z))) memR (seg_rom SEGS)) mdR).
            { apply (fa_mid_tag cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x440) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) q 0 0 k2 ly3 S3 W2 ms5 md5 (mkst regsR (Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z))) memR (seg_rom SEGS)) mdR
                (n_sp1 cx - 4096) (n_sp1 cx) 1 (PSN.rec_vid FF q)
                HB M5 HAR5 (proj1 HJR) HFR EFA).
              - reflexivity.
              - reflexivity.
              - reflexivity.
              - reflexivity.
              - reflexivity.
              - reflexivity.
              - intros r Hr. cbn [ms_regs mkst]. rewrite (KRR r ltac:(cbn in Hr |- *; tauto)). reflexivity.
              - unfold AFREAD_STK. lia.
              - lia.
              - cbn [ms_mem mkst]. intros a Ha Hw Hn _. apply KMR; [exact Ha | exact Hw | intros X; apply Hn; left; exact X
                | intros X; apply Hn; right; unfold nx_bufn in *; lia].
              - cbn [ms_mem mkst]. intros a _ _ Hp. exact (HPRES a (fa_grows_present _ _ _ a HG_msC Hp)).
              - cbn [ms_mem mkst]. intros a Ha. destruct HJR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
                apply HpresJ. lia.
              - unfold nx_jbk. destruct HJBK1 as (Hk2a & Haba & Hmoa & Hfda & Hfsa).
                split; [exact Hk2a|]. split; [exact Haba|]. split; [exact Hmoa|].
                split; [rewrite (proj1 HmdR), (proj1 Hmd5), (proj1 Hmd2); exact Hfda
                       | rewrite (proj2 HmdR), (proj2 Hmd5), (proj2 Hmd2); exact Hfsa].
              - exact VR16.
              - exact VR20. }

            assert (HSECR : nslot cx W2 (mkst regsR (Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z))) memR (seg_rom SEGS)) NS_SEC secw).
            { unfold nslot. cbn [ms_mem mkst]. apply (fa_rdword_keep W2 W2 (ms_mem ms5) memR); [|exact HSEC5].
              intros k Hk. unfold boxed in Hbufps. apply KMR; unfold NS_SEC, PS_VT_OFF, PS_VID_OFF, PS_LEN, nx_bufn in *; lia. }
            destruct (fa_seat cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) NSH_ph (nx_E cx) (q + 16 + incl) (PSN.orig sw FF q) 1 (PSN.rec_vid FF q) (n_tsv cx)
              k2 ly3 S3 W2 (mkst regsR (Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z))) memR (seg_rom SEGS)) mdR secw
              (PSN.fb FF (q + 28)) (PSN.fb FF (q + 29)) (PSN.fb FF (q + 30)) (PSN.fb FF (q + 31)) false
              HB MR HSECR (Hfb _) (Hfb _) (Hfb _) (Hfb _) ltac:(intros D; discriminate D)) as (HSR & SHOKR).
            clear HS5 SHOK5.
            lazymatch type of HSR with st_ok_pi _ _ ?Ex _ _ => assert (HEIr : img_env VAL A_LIM Ex) by apply Eimg_env end.
            assert (HJR' : ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
              ((NX_CID, fp) :: n_own cx) ly3 S3 W2 (ms_mem (mkst regsR (Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z))) memR (seg_rom SEGS))) mdR k2)
              by exact HJR.
            clear HJR.
            pose proof (proj1 HJR') as HAR_R.
            paj_run_to_tok RUNTO HSR HJR' SHOKR fa_span NP_ts.
            { cbn [ss_mem]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }

            lazymatch goal with |- SRr _ _ (mkCfg ?msx ?mdx) _ => is_var msx; rename msx into msT; set (mdT := mdx) in * end.
            lazymatch goal with H : frame_of _ ?rs _ _ |- _ =>
              pose proof (fa_kept_all _ _ _ _ _ H ltac:(clear; vm_compute; reflexivity)) as KM_T; clear H end.
            lazymatch goal with H : mem_grows _ (rdW W2 (ms_mem msT)) |- _ => rename H into HG_T end.
            pose proof (proj1 HJR') as HAR_T.
            assert (Hmd_T : m_fds mdT = m_fds mdR /\ m_fs mdT = m_fs mdR) by (unfold mdT; split; reflexivity).
            lazymatch type of HSR with st_ok_pi _ _ _ ?ss _ =>
              pose proof (st_ok_pi_restrict_mkst (w_H W2) _ ss msT HSR eq_refl) as Hsh_T end.
            fa_kept HSR (ms_regs (mkst regsR (Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z))) memR (seg_rom SEGS))) XTe
              ([2; 3; 4; 8; 9; 21; 23; 25; 27]%bv : list (bv 5)) K_T.
            assert (K_T26 : getr (ms_regs msT) 26 = getr regsR 26).
            { pose proof (st_ok_pi_restrict_reg (w_H W2) _ _ msT 26%bv HSR) as H. cbn [restrict ms_regs] in H.
              lazymatch type of H with _ = sv_denot _ ?e => change e with fa_shps in H end.
              rewrite H, denot_lit_U, (fa_U_shx _ (n_ps cx)).
              - rewrite (KRR 26%bv ltac:(cbn; tauto)), K5_26, K2_26, (KR2 26%bv ltac:(cbn; tauto)). symmetry; exact R26.
              - rewrite (ew_Eimg_Ereg_nat _ XTe 21 21%bv eq_refl). cbn [ms_regs mkst].
                rewrite (KRR 21%bv ltac:(cbn; tauto)), (K5 21%bv ltac:(cbn; tauto)), (K2 21%bv ltac:(cbn; tauto)),
                  (KR2 21%bv ltac:(cbn; tauto)). exact R21.
              - exact (ew_Ereg_extra _ XTe 0).
              - unfold PS_LEN in *. lia. }
            fa_rv HSR (16%bv : bv 5) X16. fa_rv HSR (19%bv : bv 5) X19. fa_rv HSR (17%bv : bv 5) X17.
            fa_rv HSR (5%bv : bv 5) X5. fa_rv HSR (18%bv : bv 5) X18. fa_rv HSR (24%bv : bv 5) X24. fa_rv HSR (22%bv : bv 5) X22.
            change 35%nat with (32 + 3)%nat in X16, X19. change 36%nat with (32 + 4)%nat in X17. change 32%nat with (32 + 0)%nat in X5.
            rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 3 (nF cx fp) ltac:(lia) eq_refl) in X16.
            rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 3 (nF cx fp) ltac:(lia) eq_refl) in X19.
            rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 4 (n_ts cx) ltac:(lia) eq_refl) in X17.
            rewrite (fa_ew_xt _ _ _ _ _ _ _ _ _ _ 0 SHADOW_OFF ltac:(lia) eq_refl) in X5.
            rewrite (ew_Eimg_Ereg_nat _ _ 18 18%bv eq_refl) in X18. cbn [ms_regs mkst] in X18.
            rewrite (KRR 18%bv ltac:(cbn; tauto)), G18_5 in X18.
            rewrite (ew_Eimg_Ereg_nat _ _ 24 24%bv eq_refl) in X24. cbn [ms_regs mkst] in X24.
            rewrite (KRR 24%bv ltac:(cbn; tauto)), (K5 24%bv ltac:(cbn; tauto)), (K2 24%bv ltac:(cbn; tauto)), R24_2 in X24.
            rewrite (ew_Eimg_Ereg_nat _ _ 22 22%bv eq_refl) in X22. cbn [ms_regs mkst] in X22.
            rewrite (KRR 22%bv ltac:(cbn; tauto)), R22_5 in X22.
            (* the record after the move *)
            set (rawl := fa_raw sw (n_C cx) q) in *.
            assert (HGBC : garr8 SEGS (rdW W2 (ms_mem msC)) (n_buf cx) rawl).
            { apply (fa_garr8_keep W2 W2 (ms_mem ms5) (ms_mem msC)); [|exact HGB5].
              intros x Hx. rewrite Frl2 in Hx. change (PSN.incl sw (nxF (n_C cx)) q) with incl in Hx.
              rewrite Z2Nat.id in Hx by lia.
              unfold boxed in Hbufps. unfold nx_bufn, PS_LEN, PS_VT_OFF, PS_VID_OFF in *.
              apply KM_msC; [lia | destruct Hbufps; lia]. }
            assert (Hrawl : length rawl = Z.to_nat incl) by exact Frl2.
            pose proof (fa_mm_bytes SEGS W2 (ms_mem msC) memR (n_buf cx) rawl (Z.to_nat incl) ltac:(lia) Hrawl HGBC) as HMM.
            assert (HrecR : garr8 SEGS (rdW W2 memR) (n_buf cx)
              (firstn 12 rawl ++ firstn (Z.to_nat incl - 16) (skipn 16 rawl) ++ skipn (Z.to_nat incl - 4) rawl)).
            { apply HMM.
              - intros i Hi. rewrite Z2Nat.id in Hi by lia. exact (HMV i ltac:(lia)).
              - intros a Ha Hn. rewrite Z2Nat.id in Ha, Hn by lia.
                apply HKR; [unfold nx_bufn in *; lia | lia | change ESTACK with 4096; unfold nx_bufn in *; lia]. }
            pose proof (fa_fit_vtag sw (n_C cx) (n_cap cx) (n_p cx) q) as Fvt. fa_inst Fvt.
            pose proof (fa_fit_vid sw (n_C cx) (n_cap cx) (n_p cx) q) as Fvid. fa_inst Fvid.
            pose proof (fa_fit_reclen sw (n_C cx) (n_cap cx) (n_p cx) q) as Frl. fa_inst Frl.
            pose proof (fa_rec_tagged sw (n_C cx) (n_cap cx) (n_p cx) q) as Frec. fa_inst Frec.
            assert (Htt' : PSN.tagged sw (nxF (n_C cx)) q = true) by exact Htt.
            apply (HTS cx fp k2 ly3 S3 W2 msT mdT HB HJR' HFR).
            apply (fa_land_ts cx fp (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z) q 1 (PSN.rec_vid FF q) k2 ly3 S3 W2
              (mkst regsR (Z_to_bv 64 (BASE + (symaddr ((Symbols.AsanUbsan.s_pcap_source_next + 0x540) - Symbols.AsanUbsan.s_libreac_fuzz_fopen)%Z))) memR (seg_rom SEGS)) mdR msT mdT (n_sp1 cx) (n_sp1 cx) 1 (PSN.rec_vid FF q)
              (firstn 12 rawl ++ firstn (Z.to_nat incl - 16) (skipn 16 rawl) ++ skipn (Z.to_nat incl - 4) rawl)
              HB MR HAR_R HAR_T HFR EFA Hq Hlh Hq0' Hincl Hfitq).
            ++ rewrite Hsh_T. reflexivity.
            ++ rewrite Hsh_T. reflexivity.
            ++ rewrite Hsh_T. reflexivity.
            ++ rewrite Hsh_T. reflexivity.
            ++ rewrite Hsh_T. reflexivity.
            ++ rewrite Hsh_T. reflexivity.
            ++ intros r Hr. cbn in Hr.
               destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]];
                 first [ exact K_T26 | apply K_T; cbn; tauto ].
            ++ unfold AFREAD_STK. lia.
            ++ lia.
            ++ intros a Ha _ _ _. exact (KM_T a Ha).
            ++ intros a _ _ Hp. exact (fa_grows_present _ _ _ a HG_T Hp).
            ++ intros a Ha. destruct HJR' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ & _).
               apply HpresJ. lia.
            ++ unfold nx_jbk. destruct HJBK1 as (Hk2a & Haba & Hmoa & Hfda & Hfsa).
               split; [exact Hk2a|]. split; [exact Haba|]. split; [exact Hmoa|].
               split; [rewrite (proj1 Hmd_T), (proj1 HmdR), (proj1 Hmd5), (proj1 Hmd2); exact Hfda
                      | rewrite (proj2 Hmd_T), (proj2 HmdR), (proj2 Hmd5), (proj2 Hmd2); exact Hfsa].
            ++ apply (fa_vm_keep W2 W2 memR (ms_mem msT)); [|exact VR16]. intros x Hx. apply KM_T. unfold PS_LEN, PS_VT_OFF in *. cbn [Z.of_nat] in Hx. lia.
            ++ apply (fa_vm_keep W2 W2 memR (ms_mem msT)); [|exact VR20]. intros x Hx. apply KM_T. unfold PS_LEN, PS_VID_OFF in *. cbn [Z.of_nat] in Hx. lia.
            ++ change (n_sw cx =? 1) with sw. rewrite (Fvt (n_lvt cx)), Htt'. reflexivity.
            ++ change (n_sw cx =? 1) with sw. rewrite (Fvid (n_lvid cx)), Htt'. reflexivity.
            ++ apply (fa_garr8_keep W2 W2 memR (ms_mem msT)); [|exact HrecR]. intros x Hx. apply KM_T.
               rewrite !length_app, !length_firstn, !length_skipn, Hrawl in Hx. unfold nx_bufn in *. lia.
            ++ change (n_sw cx =? 1) with sw. rewrite Frec. unfold rawl.
               rewrite !Z2Nat.inj_sub by lia. reflexivity.
            ++ rewrite !length_app, !length_firstn, !length_skipn, Hrawl. unfold boxed in Hlbj. apply Nat2Z.inj_le.
               rewrite Hlbj. unfold nx_bufn. lia.
            ++ exact X16.
            ++ exact X19.
            ++ exact X17.
            ++ exact X5.
            ++ change (n_sw cx =? 1) with sw. rewrite X22, Frl. unfold PSN.rec_len. rewrite Htt'.
               try change (PSN.incl sw (nxF (n_C cx)) q) with incl. unfold w64.
               assert (Hu : bv_unsigned (Z_to_bv 64 incl) = incl) by (apply unsigned_lit_small; unfold NX_CAP_MAX in *; lia).
               rewrite Hu. rewrite unsigned_lit_small by (unfold NX_CAP_MAX in *; lia). apply Z.mod_small. unfold NX_CAP_MAX in *. lia.
            ++ change (n_sw cx =? 1) with sw. rewrite X18. unfold nx_tsec. rewrite Hq. rewrite unsigned_lit_small by lia. exact Hsec.
            ++ change (n_sw cx =? 1) with sw. rewrite X24. unfold nx_tusec. rewrite Hq. exact R24.


Qed.

End c.

End b.
End a.

(* SK is explicit at every use (as in lib/B/Prog/PcapSourceNextDefs.v): the closure's only global sink_head
   instance is the PLAIN build's (lib/Reusable/YI5b.v:12), so an inferred SK would make the stream facts vacuous. *)
Arguments pb_nx_fitA {fx rc} SK {PI}.

(* GUARD: SK is passed by position; were it implicit again, this line would stop compiling. *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (PI : PAImg pcap_listing) (B : asyms)
  (MT : ameter_ops) (KS : asource_syms) (LAWS : AR_laws pa_segs B) (ASIL : asource_img_laws SK pa_segs B KS) =>
  pb_nx_fitA (fx:=fx) (rc:=rc) SK (PI:=PI) B MT KS LAWS ASIL).
