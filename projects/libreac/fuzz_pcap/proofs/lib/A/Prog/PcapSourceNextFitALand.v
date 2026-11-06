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
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/B/Prog/PcapSourceNextFitA.v, with its module paths and module names changed; 383 of its 436 lines of code are new or changed and 2618 lines of the source are left out. *)
(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the landing of the FitA phase at
   NP_ts (listing offset 0x15ac, address 0x81ce4). The phase walks 0x81b40 .. 0x81ce4
   (lib/A/Prog/PcapSourceNextFitA.v); from the cut at NP_fit_ra (0x81bd8, the record's fread
   returned) to NP_ts it writes only

     - the struct's tag fields ps->vtag (`sw a3,0(a2)` 0x81c6c, `sw zero,0x10(s5)` 0x81bf4) and
       ps->vid (`sh a2,0(a0)` 0x81ccc, `sh zero,0(a0)` 0x81c14), that is [ps + 16, ps + 22);
     - the caller's record buffer (the fread of the record 0x81bd4 and the __asan_memmove 0x81cdc),
       that is [buf, buf + nx_bufn cap);
     - the ESTACK bytes below s1 that the two calls use ([sp1 - ESTACK, sp1), YG0d.v:19).

   fa_land_ts turns that machine-level step into the entry predicate of the next phase, nx_ts_inv
   (lib/A/Prog/PcapSourceNextFitBDefs.v): every fact nx_ts_inv states over other bytes -- the saved
   registers and the spill slots of the machine frame, the class-0 frame on the side stack with its
   header, flag word and 8 shadow bytes, the struct's other fields, the stream's FILE block and
   data, the timestamp cell, the caller's blocks and frames and the image -- is kept, because each
   of those lies outside those three ranges; and the model's values of the record come from
   lib/A/Prog/PcapSourceNextFitAModel.v (fa_fit_fit / fa_fit_pos / fa_fit_vtag / fa_fit_vid, owner
   a Theorem Labs lane).

   THE STATEMENT is a Theorem Labs lane's (the consumer): the FitA walk supplies the machine facts, this file
   supplies the landing. It takes the caller journal at the LATER state (ms4, md4), since the walk
   reaches NP_ts with it, and the nx_mid of the cut at NP_fit_ra for the earlier one (ms3, md3).

   ASIL (asource_img_laws) is a Section hypothesis here, as in PcapSourceNextFitB.v (pb_nx_ts),
   PcapSourceNextHdrB.v (hb_mid_step) and PcapSourceNextExit.v: nx_ts_inv asks for asource_at at
   ms4, and the stream's environment bytes (asrc_env_addr) are abstract addresses of KS that only
   asil_env puts in the image, hence off the three written ranges.

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...; symbols from its unstripped twin, capstone 5 disassembly
   next.dis (sha256 06286410ee55; internal record)). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05 PcapImgEnd.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import YC1h PcapFrame.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceClose.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import
PcapSourceNextDefs PcapSourceNextFitBDefs PcapSourceNextFitAModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* A register this phase does not write. *)
Ltac inkeep := cbn [In]; repeat (first [left; reflexivity | right]).

(* The realigned stack pointer (`addi sp,sp,-0xe0` 0x8181c, `andi sp,sp,-0x20` 0x8185c).
   Same statement and proof as PcapSourceNextFitB.v's nx_sp1_range (owner a Theorem Labs lane), restated so that
   this file does not Require that phase. *)
Lemma fl_sp1_range : forall sp, sp - 256 < nx_sp1 sp <= sp - 224.
Proof.
  intros sp. unfold nx_sp1, NX_MFRAME.
  pose proof (Z.div_mod (sp - 224) 32 ltac:(lia)).
  pose proof (Z.mod_pos_bound (sp - 224) 32 ltac:(lia)). lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Notation SEGS := (pa_segs).
#[local] Notation BASE := (pa_val A_TEXT).
#[local] Notation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis ASIL : asource_img_laws SK SEGS B KS.

(* THE LANDING at NP_ts. *)
Lemma fa_land_ts : forall cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 q bj4,
  let sw := n_sw cx =? 1 in let F := nxF (n_C cx) in let incl := PSN.incl sw F q in
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms4) md4 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp NP_fit_ra NSH_ph (nx_E cx) (q + 16 + incl) (PSN.orig sw F q)
    (n_lvt cx) (n_lvid cx) (n_tsv cx) k2 ly3 S3 W3 ms3 md3 ->
  nx_q sw (n_C cx) (n_cap cx) (n_p cx) = q ->
  nx_lh sw (n_C cx) (n_cap cx) (n_p cx) = Some q ->
  n_p cx <= q -> 0 < incl <= n_cap cx -> q + 16 + incl <= Z.of_nat (length (n_C cx)) ->
  ms_pc_val ms4 = w64 (BASE + NP_ts) -> ms_resv ms4 = None -> ms_svc_pending ms4 = None ->
  ms_rom ms4 = seg_rom SEGS -> ms_fregs ms4 = fp_regs -> ms_fcsr ms4 = fp_csr ->
  (forall r : bv 5, In r [2;3;4;8;9;18;19;24]%bv -> getr (ms_regs ms4) r = getr (ms_regs ms3) r) ->
  getr (ms_regs ms4) 21 = w64 (n_ts cx) ->
  bv_unsigned (getr (ms_regs ms4) 25) mod 2 ^ 32 = PSN.rec_len sw F q ->
  bv_unsigned (getr (ms_regs ms4) 26) mod 2 ^ 32 = PSN.hw sw F q 0 ->
  bv_unsigned (getr (ms_regs ms4) 23) mod 2 ^ 32 = PSN.hw sw F q 4 ->
  m_fds md4 = m_fds md3 -> m_fs md4 = m_fs md3 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (n_ps cx + 16 <= a < n_ps cx + 22) ->
     ~ (n_buf cx <= a < n_buf cx + nx_bufn (n_cap cx)) -> ~ (n_sp1 cx - ESTACK <= a < n_sp1 cx) ->
     aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  (forall a, apresent (w_H W3) (ms_mem ms3) a -> apresent (w_H W3) (ms_mem ms4) a) ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (n_ps cx + 16) 4 (if PSN.tagged sw F q then 1 else 0) ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (n_ps cx + 20) 2 (if PSN.tagged sw F q then PSN.rec_vid F q else 0) ->
  garr8 SEGS (rdW W3 (ms_mem ms4)) (n_buf cx) bj4 -> length bj4 = length (n_bj cx) ->
  firstn (length (nx_rec sw (n_C cx) (n_cap cx) (n_p cx))) bj4 = nx_rec sw (n_C cx) (n_cap cx) (n_p cx) ->
  nx_ts_inv B MT KS cx fp k2 ly3 S3 W3 ms4 md4.
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 ms4 md4 q bj4. cbv zeta.
intros HB HJ HFR HM Hq Hlh Hpq Hincl Hfit Hpc Hresv Hpend Hrom Hfregs Hfcsr KR R21 R25 R26 R23
  Hfds Hfs HUN HPR Vvt Vvid Hgbj Hlbj Hpre.
(* ---- what the cut at NP_fit_ra gives ---- *)
destruct HM as (HBD & R24 & HJBK & HKEPT & HEsub & Hh & HPS & HRAps & HSRC & Hqr & _ & HTSm).
destruct HBD as (HBD0 & HSL).
destruct HBD0 as (_ & _ & _ & _ & _ & _ & HREGS & HSAV & HHDR & HFLW & HSH & Hshlen & R18 & R19 & HF0).
destruct HREGS as (R2 & R8 & R9 & R3 & R4).
(* ---- what nx_base gives ---- *)
pose proof HB as (HJc & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hal16 & Hwlo & Hwhi & _
  & _ & _ & _ & _ & Hps4 & Hps47 & _ & Hpsown & Hpsf1 & Hpsf2 & _ & _ & _ & _
  & _ & HBUFB & HTSB & HSTR & _ & _ & _).
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & _ & _ & _ & _ & _ & _ & Hstkc & _).
pose proof Hstkc as (_ & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof HJ as (HAR3 & Hly3 & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HNX : NX_STK = 8496) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hsp : alloc_ceiling + NX_STK <= spZ (n_regs cx) <= 2 ^ 47)
  by (clear - Hceil Hslo Hshi H47 Hwlo Hwhi; lia).
(* The realigned stack pointer s1 lies 224 to 255 bytes below the entry sp (0x8181c `addi sp,sp,-0xe0`,
   0x8185c `andi sp,sp,-0x20`). Restated from PcapSourceNextFitB.v's nx_sp1_range (owner a Theorem Labs lane); this
   file does not Require that phase. *)
assert (Hsp1 : spZ (n_regs cx) - 256 < n_sp1 cx <= spZ (n_regs cx) - 224)
  by (unfold n_sp1; apply fl_sp1_range).
(* ---- this call's own frame on the side stack ---- *)
assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
{ intros c p. unfold frame_addr.
  destruct Hly3 as (_ & _ & _ & _ & _ & EF3 & _). destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _).
  rewrite EF3, EFc. reflexivity. }
assert (HFB : fs_frame_bytes NX_CID = 64) by (vm_compute; reflexivity).
assert (HinF : In (NX_CID, fp) (frames S3)) by (rewrite HFR; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 (ms_mem ms4) md4 NX_CID fp HAR3 HinF)
  as (HF4096 & HFceil & _).
rewrite EFA in HF4096, HFceil. rewrite HFB in HFceil.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in HF4096, HFceil.
assert (HSHa : nSH cx fp = SHADOW_OFF + nF cx fp / 8) by reflexivity.
assert (HD8 : 512 <= nF cx fp / 8 <= 0xFFFFFFF0000).
{ clear - HF4096 HFceil C1. split; [apply Z.div_le_lower_bound | apply Z.div_le_upper_bound]; lia. }
assert (HSHr : SHADOW_OFF + 512 <= nSH cx fp <= SHADOW_OFF + 0xFFFFFFF0000)
  by (rewrite HSHa; clear - HD8; lia).
(* ---- the caller's struct: its frame, and where it lies ---- *)
assert (Hpsin : In (n_cid cx, n_pos cx) (frames (n_Sc cx)))
  by (rewrite Hfrsc; apply in_or_app; left; exact Hpsown).
destruct (frames_bounds SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
  (n_cid cx) (n_pos cx) HARc Hpsin) as (Hpf4096 & Hpfceil & Hpfapp).
pose proof (frm_off_imgP B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx)
  (n_cid cx) (n_pos cx) HARc Hpsin) as Hpsoff.
unfold off_img in Hpsoff.
pose proof (fs_frame_bytes_nonneg (n_cid cx)) as Hcidnn.
assert (Hpsceil : n_ps cx + PS_LEN <= alloc_ceiling) by (clear - Hpsf2 Hpfceil; lia).
assert (Hpsapp : in_app (n_ps cx) PS_LEN)
  by (exact (in_app_sub (frame_addr (n_lyc cx) (n_cid cx) (n_pos cx)) (fs_frame_bytes (n_cid cx))
       (n_ps cx) PS_LEN Hpfapp Hpsf1 ltac:(unfold PS_LEN; lia) Hpsf2)).
assert (Hpsimg : n_ps cx + PS_LEN <= YImgTop.IMG_LO \/ YImgTop.IMG_TOP <= n_ps cx)
  by (clear - Hpsoff Hpsf1 Hpsf2; lia).
(* ---- the record buffer ---- *)
destruct (HBUFB Hh) as (Hbufin & Hbuf4 & _ & _ & Hlbj0 & _ & _ & Hbufps).
destruct (al_blocks _ _ LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) _ _ HARc Hbufin)
  as (_ & Hb4096 & Hbceil & Hbapp & _).
pose proof (blk_off_imgP B _ _ _ _ _ _ _ HARc Hbufin) as Hbufoff. unfold off_img in Hbufoff.
pose proof (req_size_pos (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & Hbreq).
(* ---- the stream's FILE block and data buffer ---- *)
destruct (HSTR Hh) as (Hinh & Hinb & _ & _ & Hp0 & Hbufh & Hbufb & Hpsh & Hpsb & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hinh) as (_ & Hh4096 & Hhceil & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhceil.
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hinb) as (_ & Hb4096' & Hbceil' & _).
pose proof (req_size_pos (Z.of_nat (length (n_C cx))) (Zle_0_nat _)) as (_ & HreqC).
(* ---- the model at this record ---- *)
assert (Hq0 : 0 <= q) by (clear - Hpq Hp0; lia).
assert (Hroom16 : q + 16 <= Z.of_nat (length (n_C cx))) by (clear - Hfit Hincl; lia).
assert (Efit : nx_fit (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = true)
  by (eapply fa_fit_fit; eassumption).
assert (Epos : nx_pos (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)
               = q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q)
  by (eapply fa_fit_pos; eassumption).
assert (Evt : nx_vtag (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvt cx)
              = (if PSN.tagged (n_sw cx =? 1) (nxF (n_C cx)) q then 1 else 0))
  by (eapply fa_fit_vtag; eassumption).
assert (Evid : nx_vid (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvid cx)
               = (if PSN.tagged (n_sw cx =? 1) (nxF (n_C cx)) q
                  then PSN.rec_vid (nxF (n_C cx)) q else 0))
  by (eapply fa_fit_vid; eassumption).
assert (Eorig : nx_orig (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lol cx)
                = PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q)
  by (unfold nx_orig; rewrite Hlh; reflexivity).
assert (Ereclen : nx_reclen (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)
                  = PSN.rec_len (n_sw cx =? 1) (nxF (n_C cx)) q)
  by (unfold nx_reclen; rewrite Hq; reflexivity).
assert (Etsec : nx_tsec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)
                = PSN.hw (n_sw cx =? 1) (nxF (n_C cx)) q 0)
  by (unfold nx_tsec; rewrite Hq; reflexivity).
assert (Etusec : nx_tusec (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx)
                 = PSN.hw (n_sw cx =? 1) (nxF (n_C cx)) q 4)
  by (unfold nx_tusec; rewrite Hq; reflexivity).

(* ------------------------------------------------------------------------------------------- *)
(* What the step keeps                                                                           *)
(* ------------------------------------------------------------------------------------------- *)

(* the stack bytes the two calls use lie inside this call's own window *)
assert (WINDOW : forall a, n_sp1 cx - ESTACK <= a < n_sp1 cx ->
  spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx)) by (clear - Hsp1 Hsp HNX HES; lia).
(* a shadow byte of the application's memory is apart from the three ranges *)
assert (PSOUT : forall y, SHADOW_OFF <= y < kHighMemBeg -> ~ (n_ps cx + 16 <= y < n_ps cx + 22)).
{ intros y Hy. destruct Hpsapp as (Hp1 & [Hp2 | (Hp3 & Hp4)]).
  - clear - Hy Hp2. unfold kLowShadowBeg, SHADOW_OFF, PS_LEN in *. lia.
  - clear - Hy Hp3. unfold kHighMemBeg, SHADOW_OFF in *. lia. }
assert (BUFOUT : forall y, SHADOW_OFF <= y < kHighMemBeg ->
  ~ (n_buf cx <= y < n_buf cx + nx_bufn (n_cap cx))).
{ intros y Hy. destruct Hbapp as (Hb1 & [Hb2 | (Hb3 & Hb4)]).
  - clear - Hy Hb2 Hbreq. unfold kLowShadowBeg, SHADOW_OFF in *. lia.
  - clear - Hy Hb3. unfold kHighMemBeg, SHADOW_OFF in *. lia. }
assert (SHOUT : forall y, SHADOW_OFF <= y < kHighMemBeg ->
  aview SEGS (w_H W3) (ms_mem ms4) y = aview SEGS (w_H W3) (ms_mem ms3) y).
{ intros y Hy. apply HUN.
  - clear - Hy; unfold SHADOW_OFF, kHighMemBeg in *; lia.
  - exact (PSOUT y Hy).
  - exact (BUFOUT y Hy).
  - clear - Hy Hsp Hsp1 HNX HES C1; unfold kHighMemBeg, SHADOW_OFF in *; lia. }
(* the shadow address of an application byte *)
assert (SHADDR : forall x, 0 <= x -> x < 2 ^ 47 ->
  SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighMemBeg).
{ intros x Hx0 Hx1. unfold shadow_of_addr.
  assert (Hd0 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hd1 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  clear - Hd0 Hd1. unfold SHADOW_OFF, kHighMemBeg. lia. }
(* everything at or above the allocator's ceiling but outside the two calls' stack bytes *)
assert (KEEP_up : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (n_sp1 cx - ESTACK <= a < n_sp1 cx) ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hw. apply HUN.
  - clear - Ha C1; lia.
  - clear - Ha Hpsceil; unfold PS_LEN in *; lia.
  - clear - Ha Hbceil Hbreq; lia.
  - exact Hw. }
(* a word of this call's machine frame (saved registers, spill slots): above s1, kept *)
assert (RDW : forall a v, alloc_ceiling <= a -> a + 8 <= spZ (n_regs cx) -> n_sp1 cx <= a ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v ->
  rdword (aview SEGS (w_H W3) (ms_mem ms4)) a = Some v).
{ intros a v Ha Ha8 Hsa Hr.
  rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms4)) a);
    [exact Hr|].
  intros kk Hk. apply KEEP_up; [clear - Ha Ha8 Hk Hsp; lia | clear - Hsa Hk; lia]. }
(* the class-0 frame on the side stack: apart from the struct's frame and from the buffer *)
assert (Eab : ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx)) by (destruct HJBK as (_ & E & _); exact E).
destruct (in_split _ _ Hpsin) as (l2 & l3 & El).
pose proof (sep_frames_pos SEGS B LAWS ly3 S3 W3 (ms_mem ms4) md4 (NX_CID, fp) (n_cid cx, n_pos cx)
  [] l2 l3 HAR3 ltac:(rewrite HFR, El; reflexivity)) as Dff.
unfold zdisjoint, frame_rng in Dff. cbn [fst snd] in Dff. rewrite !EFA, HFB in Dff.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Dff.
assert (Hbufin3 : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite Eab; exact Hbufin).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 (ms_mem ms4) md4 (n_buf cx) (nx_bufn (n_cap cx))
  NX_CID fp HAR3 Hbufin3 HinF) as Dbf.
unfold zdisjoint in Dbf. cbn [fst snd] in Dbf. rewrite EFA, HFB in Dbf.
change (frame_addr (n_lyc cx) NX_CID fp) with (nF cx fp) in Dbf.
assert (KEEP_F : forall a, nF cx fp <= a < nF cx fp + 64 ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply HUN.
  - clear - Ha HF4096 HFceil C1; lia.
  - clear - Ha Dff Hpsf1 Hpsf2; unfold PS_LEN in *; lia.
  - clear - Ha Dbf Hbreq; lia.
  - clear - Ha HFceil Hsp Hsp1 HNX HES C1; lia. }
assert (RDW_F : forall a v, nF cx fp <= a -> a + 8 <= nF cx fp + 64 ->
  rdword (aview SEGS (w_H W3) (ms_mem ms3)) a = Some v ->
  rdword (aview SEGS (w_H W3) (ms_mem ms4)) a = Some v).
{ intros a v Ha Ha8 Hr.
  rewrite (rdword_ext (aview SEGS (w_H W3) (ms_mem ms3)) (aview SEGS (w_H W3) (ms_mem ms4)) a);
    [exact Hr|].
  intros kk Hk. apply KEEP_F. clear - Ha Ha8 Hk. lia. }
(* a byte of a block of the caller, outside the post's set *)
assert (KEEP_blk : forall b m a, In (b, m) (ablocks B (n_lyc cx) (n_Sc cx)) ->
  b <= a < b + req_size m -> ~ nx_E cx a ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros b m a Hin Hr HnE.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HARc Hin) as (_ & Hb4 & Hbc & _).
  apply HUN.
  - clear - Hr Hb4 Hbc C1; lia.
  - intros Hx. apply HnE. unfold nx_E, nx_wrset. left. clear - Hx. unfold PS_LEN. lia.
  - intros Hx. apply HnE. unfold nx_E, nx_wrset. right; left. exact Hx.
  - clear - Hr Hb4 Hbc Hsp Hsp1 HNX HES C1; lia. }
(* a byte of a frame of the caller, outside the post's set *)
assert (KEEP_frm : forall c p a, In (c, p) (frames (n_Sc cx)) ->
  frame_addr (n_lyc cx) c p <= a < frame_addr (n_lyc cx) c p + fs_frame_bytes c -> ~ nx_E cx a ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros c p a Hin Hr HnE.
  destruct (frames_bounds SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) c p HARc Hin)
    as (Hf4 & Hfc & _).
  apply HUN.
  - clear - Hr Hf4 Hfc C1; lia.
  - intros Hx. apply HnE. unfold nx_E, nx_wrset. left. clear - Hx. unfold PS_LEN. lia.
  - intros Hx. apply HnE. unfold nx_E, nx_wrset. right; left. exact Hx.
  - clear - Hr Hf4 Hfc Hsp Hsp1 HNX HES C1; lia. }
(* a byte of the image *)
assert (KEEP_img : forall a, in_img SEGS a ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Hi.
  pose proof (pa_segs_low a Hi) as Hlo. pose proof (pa_img_range a Hi) as Hrg.
  unfold kLowMemEnd in Hlo. unfold pcap_img_end, YImgTop.IMG_TOP in Hrg.
  apply HUN.
  - clear - Hlo; lia.
  - clear - Hrg Hpsimg; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP, PS_LEN in *; lia.
  - clear - Hrg Hbufoff Hbreq; unfold YImgTop.IMG_LO, YImgTop.IMG_TOP in *; lia.
  - clear - Hlo Hsp Hsp1 HNX HES C1; lia. }

(* ------------------------------------------------------------------------------------------- *)
(* The state at NP_ts                                                                            *)
(* ------------------------------------------------------------------------------------------- *)

assert (Keep2 : getr (ms_regs ms4) 2 = getr (ms_regs ms3) 2) by (apply KR; inkeep).
assert (Keep3 : getr (ms_regs ms4) 3 = getr (ms_regs ms3) 3) by (apply KR; inkeep).
assert (Keep4 : getr (ms_regs ms4) 4 = getr (ms_regs ms3) 4) by (apply KR; inkeep).
assert (Keep8 : getr (ms_regs ms4) 8 = getr (ms_regs ms3) 8) by (apply KR; inkeep).
assert (Keep9 : getr (ms_regs ms4) 9 = getr (ms_regs ms3) 9) by (apply KR; inkeep).
assert (Keep18 : getr (ms_regs ms4) 18 = getr (ms_regs ms3) 18) by (apply KR; inkeep).
assert (Keep19 : getr (ms_regs ms4) 19 = getr (ms_regs ms3) 19) by (apply KR; inkeep).
assert (Keep24 : getr (ms_regs ms4) 24 = getr (ms_regs ms3) 24) by (apply KR; inkeep).
(* the machine frame: the saved registers at sp0 - 8 .. sp0 - 104 and the spill slots at s1 + 16
   .. s1 + 120, all above s1 and under the caller's sp *)
assert (BODY : nx_body cx fp NP_ts W3 ms4 NSH_ph).
{ split.
  - unfold nx_body0.
    split; [exact Hpc|]. split; [exact Hresv|]. split; [exact Hpend|]. split; [exact Hrom|].
    split; [exact Hfregs|]. split; [exact Hfcsr|].
    split.
    { unfold nregs. split; [rewrite Keep2; exact R2|]. split; [rewrite Keep8; exact R8|].
      split; [rewrite Keep9; exact R9|]. split; [rewrite Keep3; exact R3|].
      rewrite Keep4; exact R4. }
    split.
    { destruct HSAV as (SV1 & SV2). split.
      - apply RDW; [clear - Hsp HNX; lia | clear - Hsp; lia | clear - Hsp Hsp1; lia | exact SV1].
      - intros j Hj. apply RDW;
          [clear - Hsp HNX Hj; lia | clear - Hsp Hj; lia | clear - Hsp Hsp1 Hj; lia | exact (SV2 j Hj)]. }
    split.
    { destruct HHDR as (HD1 & HD2 & HD3).
      split; [apply RDW_F; [clear; lia | clear; lia | exact HD1]|].
      split; [apply RDW_F; [clear; lia | clear; lia | exact HD2]|].
      apply RDW_F; [clear; lia | clear; lia | exact HD3]. }
    split.
    { unfold nflagw in *. apply RDW_F; [unfold NX_FLAGPTR; clear; lia | unfold NX_FLAGPTR; clear; lia
        | exact HFLW]. }
    split.
    { intros i Hi.
      assert (Hi8 : Z.of_nat i < 8) by (rewrite Hshlen in Hi; unfold NX_NSH in Hi; clear - Hi; lia).
      rewrite (SHOUT (nSH cx fp + Z.of_nat i) ltac:(clear - Hi8 HSHr C1; unfold SHADOW_OFF, kHighMemBeg in *; lia)).
      exact (HSH i Hi). }
    split; [exact Hshlen|].
    split; [rewrite Keep18; exact R18|].
    split; [rewrite Keep19; exact R19|].
    unfold nslot in *. apply RDW;
      [clear - Hsp Hsp1 HNX; unfold NS_F0; lia | clear - Hsp Hsp1; unfold NS_F0; lia
       | clear - Hsp1; unfold NS_F0; lia | exact HF0].
  - destruct HSL as (S1 & S2 & S3' & S4 & S5 & S6 & S7 & S8' & S9 & S10 & S11).
    unfold nslots, nslot in *.
    assert (SLK : forall off v, 0 <= off <= 112 ->
      rdword (aview SEGS (w_H W3) (ms_mem ms3)) (n_sp1 cx + off) = Some v ->
      rdword (aview SEGS (w_H W3) (ms_mem ms4)) (n_sp1 cx + off) = Some v).
    { intros off v Hoff Hr. apply RDW;
        [clear - Hsp Hsp1 Hoff HNX; lia | clear - Hsp Hsp1 Hoff; lia | clear - Hoff; lia | exact Hr]. }
    split; [apply SLK; [unfold NS_F0; clear; lia | exact S1]|].
    split; [apply SLK; [unfold NS_FK; clear; lia | exact S2]|].
    split; [apply SLK; [unfold NS_TS; clear; lia | exact S3']|].
    split; [apply SLK; [unfold NS_SB; clear; lia | exact S4]|].
    split; [apply SLK; [unfold NS_PS8; clear; lia | exact S5]|].
    split; [apply SLK; [unfold NS_PS12; clear; lia | exact S6]|].
    split; [apply SLK; [unfold NS_SH8; clear; lia | exact S7]|].
    split; [apply SLK; [unfold NS_SH12; clear; lia | exact S8']|].
    split; [apply SLK; [unfold NS_OFF8; clear; lia | exact S9]|].
    split; [apply SLK; [unfold NS_OFF12; clear; lia | exact S10]|].
    apply SLK; [unfold NS_MASK; clear; lia | exact S11]. }
(* the caller's memory *)
assert (KEPT4 : nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 (ms_mem ms4)
  (spZ (n_regs cx)) (nx_E cx)).
{ destruct HKEPT as (K1 & K2 & K3 & K4 & K5 & K6).
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw HnE.
    rewrite (KEEP_up a ltac:(clear - Ha; lia) ltac:(intros Hx; exact (Hw (WINDOW a Hx)))).
    exact (K1 a Ha Hw HnE).
  - intros b m i Hin Hi HnE.
    rewrite (KEEP_blk b m (b + i) Hin ltac:(clear - Hi; lia) HnE). exact (K2 b m i Hin Hi HnE).
  - intros a Hi Ho He. rewrite (KEEP_img a Hi). exact (K3 a Hi Ho He).
  - intros c p a Hin Hr HnE.
    destruct (frames_bounds SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) c p HARc Hin)
      as (Hf4 & Hfc & _).
    pose proof (fs_frame_bytes_nonneg c) as Hcn.
    assert (Hkeep : aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
    { pose proof Hr as Hr'. unfold in_zr, frame_rng, shadow_addr in Hr'. cbn [fst snd] in Hr'.
      destruct Hr' as [Hr' | Hr'].
      - exact (KEEP_frm c p a Hin ltac:(clear - Hr'; lia) HnE).
      - pose proof (shadow_range_end (frame_addr (n_lyc cx) c p) (fs_frame_bytes c) Hcn) as Hse.
        pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c p)
          ltac:(clear - Hf4 Hfc Hcn C1 C4; unfold kHighMemEnd; lia)) as Hsb1.
        pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c p + fs_frame_bytes c)
          ltac:(clear - Hf4 Hfc Hcn C1 C4; unfold kHighMemEnd; lia)) as Hsb2.
        unfold shadow_addr in Hse, Hsb1, Hsb2.
        apply SHOUT. clear - Hr' Hse Hsb1 Hsb2 C2 C3 C5.
        unfold kLowMemEnd, kHighShadowEnd, kHighMemBeg, SHADOW_OFF in *. lia. }
    rewrite Hkeep. exact (K4 c p a Hin Hr HnE).
  - intros a Ha Hw Hp. apply HPR. exact (K5 a Ha Hw Hp).
  - intros a Ha. apply HPR. exact (K6 a Ha). }
(* the struct, field by field: only [ps + 16, ps + 22) changed *)
assert (KPS : forall x, n_ps cx <= x < n_ps cx + 24 -> ~ (n_ps cx + 16 <= x < n_ps cx + 22) ->
  mbyte SEGS (rdW W3 (ms_mem ms4)) x = mbyte SEGS (rdW W3 (ms_mem ms3)) x).
{ intros x Hx Hn. apply (mbyte_of_aview SEGS). apply HUN.
  - clear - Hx Hps4 Hps47; unfold PS_LEN in *; lia.
  - exact Hn.
  - clear - Hx Hbufps; unfold PS_LEN in *; lia.
  - clear - Hx Hpsceil Hsp Hsp1 HNX HES C1; unfold PS_LEN in *; lia. }
assert (PSAT : nx_ps_at SEGS (rdW W3 (ms_mem ms4)) (n_ps cx) (n_h cx) (n_sw cx)
  (PSN.orig (n_sw cx =? 1) (nxF (n_C cx)) q)
  (if PSN.tagged (n_sw cx =? 1) (nxF (n_C cx)) q then 1 else 0)
  (if PSN.tagged (n_sw cx =? 1) (nxF (n_C cx)) q then PSN.rec_vid (nxF (n_C cx)) q else 0)
  (n_pad cx)).
{ destruct HPS as (P1 & P2 & P3 & _ & _ & P6 & P7).
  unfold nx_ps_at. unfold PS_F_OFF, PS_SW_OFF, PS_OL_OFF, PS_VT_OFF, PS_VID_OFF in *.
  split; [eapply vm_frame; [|exact P1]; intros x Hx; apply KPS; cbn in Hx; clear - Hx; lia|].
  split; [eapply vm_frame; [|exact P2]; intros x Hx; apply KPS; cbn in Hx; clear - Hx; lia|].
  split; [eapply vm_frame; [|exact P3]; intros x Hx; apply KPS; cbn in Hx; clear - Hx; lia|].
  split; [exact Vvt|].
  split; [exact Vvid|].
  split; [|exact P7].
  apply (garr8_frame SEGS _ _ _ _ P6). intros x Hx. rewrite P7 in Hx. cbn in Hx.
  apply KPS; clear - Hx; lia. }
(* the struct's shadow *)
assert (RAPS : range_addressable (aview SEGS (w_H W3) (ms_mem ms4)) SHADOW_OFF (n_ps cx) PS_LEN).
{ apply (ra_frame _ _ (n_ps cx) PS_LEN HRAps). intros x Hx.
  apply SHOUT. apply SHADDR; clear - Hx Hps4 Hps47; unfold PS_LEN in *; lia. }
(* the stream: its FILE block and its data buffer are apart from the struct, from the record buffer
   and from the stack, and its environment bytes are in the image (asil_env) *)
assert (KEEP_h : forall a, n_h cx <= a < n_h cx + SRC_FILE_BLOCK ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. unfold SRC_FILE_BLOCK in Ha. apply HUN.
  - clear - Ha Hh4096 Hhceil C1; lia.
  - clear - Ha Hpsh; unfold PS_LEN, SRC_FILE_BLOCK in *; lia.
  - clear - Ha Hbufh; unfold SRC_FILE_BLOCK in *; lia.
  - clear - Ha Hh4096 Hhceil Hsp Hsp1 HNX HES C1; lia. }
assert (KEEP_b : forall a, n_b cx <= a < n_b cx + Z.of_nat (length (n_C cx)) ->
  aview SEGS (w_H W3) (ms_mem ms4) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha. apply HUN.
  - clear - Ha Hb4096' Hbceil' HreqC C1; lia.
  - clear - Ha Hpsb; unfold PS_LEN in *; lia.
  - clear - Ha Hbufb; lia.
  - clear - Ha Hb4096' Hbceil' HreqC Hsp Hsp1 HNX HES C1; lia. }
assert (SRC4 : asource_at SEGS KS (rdW W3 (ms_mem ms4)) (n_h cx) (n_b cx) (n_C cx)
  (q + 16 + PSN.incl (n_sw cx =? 1) (nxF (n_C cx)) q)).
{ apply (asource_at_frame KS (rdW W3 (ms_mem ms3)) (rdW W3 (ms_mem ms4))); [|exact HSRC].
  intros a [Ha | [Ha | Ha]]; apply (mbyte_of_aview SEGS).
  - exact (KEEP_h a Ha).
  - exact (KEEP_b a Ha).
  - apply KEEP_img. exact (proj1 (asil_env _ _ _ _ ASIL a Ha)). }
(* the timestamp cell *)
assert (TS4 : n_ts cx <> 0 ->
  val_mem SEGS (rdW W3 (ms_mem ms4)) (n_ts cx) 8 (n_tsv cx) /\
  range_addressable (aview SEGS (w_H W3) (ms_mem ms4)) SHADOW_OFF (n_ts cx) 8).
{ intros T0. destruct (HTSm T0) as (Hv & Hra).
  destruct (HTSB Hh T0) as (_ & _ & Hts4 & Hts47 & _ & (tcid & tpos & Htin & Ht1 & Ht2) & _ & _ & Htps & Htbuf).
  assert (Htin' : In (tcid, tpos) (frames (n_Sc cx)))
    by (rewrite Hfrsc; apply in_or_app; left; exact Htin).
  destruct (frames_bounds SEGS B LAWS (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) (n_mdc cx) tcid tpos
    HARc Htin') as (Htf4 & Htfc & _).
  assert (KTS : forall x, n_ts cx <= x < n_ts cx + 8 ->
    aview SEGS (w_H W3) (ms_mem ms4) x = aview SEGS (w_H W3) (ms_mem ms3) x).
  { intros x Hx. apply HUN.
    - clear - Hx Hts4 Hts47; lia.
    - clear - Hx Htps; unfold PS_LEN in *; lia.
    - clear - Hx Htbuf; lia.
    - clear - Hx Ht2 Htfc Hsp Hsp1 HNX HES C1; lia. }
  split.
  - eapply vm_frame; [|exact Hv]. intros x Hx. apply (mbyte_of_aview SEGS). apply KTS.
    cbn in Hx. clear - Hx. lia.
  - apply (ra_frame _ _ (n_ts cx) 8 Hra). intros x Hx. apply SHOUT.
    apply SHADDR; clear - Hx Hts4 Hts47; lia. }

(* ------------------------------------------------------------------------------------------- *)
(* nx_ts_inv                                                                                     *)
(* ------------------------------------------------------------------------------------------- *)

unfold nx_ts_inv. cbv zeta.
rewrite Epos, Eorig, Evt, Evid, Efit, Ereclen, Etsec, Etusec.
split.
{ unfold nx_mid.
  split; [exact BODY|].
  split; [rewrite Keep24; exact R24|].
  split.
  { destruct HJBK as (Hk & Hbl & Hmo & Hfd0 & Hfs0).
    split; [exact Hk|]. split; [exact Hbl|]. split; [exact Hmo|].
    split; [rewrite Hfds; exact Hfd0 | rewrite Hfs; exact Hfs0]. }
  split; [exact KEPT4|].
  split; [exact HEsub|].
  split; [exact Hh|].
  split; [exact PSAT|].
  split; [exact RAPS|].
  split; [exact SRC4|].
  split; [exact Hqr|].
  split; [exists bj4; split; [exact Hgbj | exact Hlbj]|].
  exact TS4. }
split; [reflexivity|].
split; [exists bj4; split; [exact Hgbj|]; split; [exact Hlbj | exact Hpre]|].
split; [exact R21|].
split; [exact R25|].
split; [exact R26 | exact R23].
Qed.

End c.
End b.
End a.
