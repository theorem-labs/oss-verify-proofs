(* pcap_source_open (fuzz_pcap.asan 0x8145c, listing offset AF_pcap_source_open = 0xd24, 240 instructions) on
   libreac v1.9.0's ASan build: the contract of the code, in cgif_file's caller-journal form
   (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365 at origin/ossv/recipes c8557374ad2e), and the constants its walk
   (PcapSourceOpen.v) shares. Every number is read from the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0017d...;
   capstone 5 disassembly of 0x8145c..0x8181c); the comment beside a number names its instruction.

   What the code does (the C source is libreac src/pcap_source.c):
   - prologue: a 96-byte machine frame (0x8145c `addi sp,sp,-0x60`; ra, s0..s9 saved at sp0-8 .. sp0-88,
     0x81464..0x8148c), s0 := sp0 (0x81490), sp realigned down to 32 (0x81494) and s1 := sp (0x81498);
   - a frame for the 24-byte header buffer: when the use-after-return flag (object 16 through its GOT word, object
     0: 0x814a4, 0x814a8, 0x814b0) is not 0, `__asan_stack_malloc_1(0x60)` (0x814c0, 0x814c4) gives the class-1
     side-stack frame F in s2 = s6; otherwise (or on a 0 result) F is taken on the machine stack (0x814dc..0x814f4).
     The header (0x814fc..0x81528: magic 0x41b58ab3, object 10, object 11) and 12 shadow bytes (0x81534..0x81560:
     0xf1 x4, 0xf8 x3 for the buffer out of scope, 0xf3 x5) are written;
   - f := libreac_fuzz_fopen(path, "rb") (0x8156c, 0x81570; "rb" is object 12), then ps->f = f (0x81588),
     ps->field12 = 0 (0x815a0), ps->field16 = 0 (0x815b8), ps->field20 = 0 (16 bits, 0x815d0), each store after its
     shadow check (0x8157c, 0x81598, 0x815b0, 0x815c8; error paths 0x817a4..0x81818);
   - f == NULL (0x815d4): return -1;
   - otherwise the buffer is put in scope (0x815dc..0x815e4) and fread(F + 32, 1, 24, f) (0x815f8); a short read
     (0x815fc), or a magic (le32 of the first 4 bytes, 0x81600..0x81620) that is neither 0xd4c3b2a1 (0x81630:
     ps->swapped = 1, 0x816a4) nor 0xa1b2c3d4 (0x8163c: ps->swapped = 0, 0x81658), closes the stream
     (fclose 0x81674 / 0x816b8), stores ps->f = NULL (0x816c4) and returns -1; a good magic returns 0;
   - epilogue: buffer out of scope again (0x816d0..0x816d8, not on the NULL path), retired magic 0x45e0360e at F
     (0x816e4), the frame's 16 shadow bytes set to 0xf5 and its flag byte cleared (side-stack frame, 0x816ec..0x81734)
     or the 12 shadow bytes cleared (machine frame, 0x8173c..0x81768), registers restored, `ret` (0x817a0).

   The four stores write 24-byte `struct pcap_source` bytes of the CALLER (the harness keeps ps in its own class-1
   side-stack frame), so the contract takes the caller's journal and extends it (PcapSourceClose.v's form): the
   frame holding ps is one the caller's journal took (`own`). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05 PcapImgEnd YC5d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapBase PcapFuzzFopenDefs.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFmemopenISpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the stack and the events -------------------------------------------- *)

(* The machine frame (0x8145c `addi sp,sp,-0x60`) and the realignment (0x81494 `andi sp,sp,-0x20`): with sp0 mod 16 = 0
   the calls run at s1 = 32 * ((sp0 - 96) / 32) >= sp0 - 112. *)
Definition OPEN_FRAME : Z := 96.
Definition OPEN_SPAN : Z := 112.
(* The stack the call needs: the span above s1 and the deepest callee window below it, libreac_fuzz_fopen's
   (PcapFuzzFopenDefs.v LIBREAC_FUZZ_FOPEN_STK = AFMEMOPEN_STK = 18624 >= PFCLOSE_STK = 16528 >= AFREAD_STK = 8192
   >= ESTACK = 4096). *)
Definition TPCAP_SOURCE_OPEN_STK : Z := OPEN_SPAN + LIBREAC_FUZZ_FOPEN_STK.
Lemma TPCAP_SOURCE_OPEN_STK_val : TPCAP_SOURCE_OPEN_STK = 18736.
Proof. reflexivity. Qed.
(* The allocator events of the worst path: fmemopen's malloc (EV_FUZZ_FOPEN = 1) and fclose's free and free(NULL)
   (2). The frame takes none (__asan_stack_malloc_1 is not an allocator event). *)
Definition EV_OPEN : Z := EV_FUZZ_FOPEN + 2.

(* ---- the header test ------------------------------------------------------ *)

(* The first four bytes of the file, little-endian (0x81600..0x81628), as lib/Prog/pcap_source_struct.v's pcap_magic
   states it over bytes; the stream predicate (PSource.v) holds the file as a list of Z. *)
Definition pcap_magicZ (C : list Z) : Z :=
  nth 0 C 0 + 256 * nth 1 C 0 + 65536 * nth 2 C 0 + 16777216 * nth 3 C 0.
(* The file opens when it holds the 24-byte global header (0x815fc) and one of the two classic magics
   (0x81630, 0x8163c); pcap_source_struct.v's pcap_good / pcap_sw over Z. *)
Definition pcap_goodZ (C : list Z) : bool :=
  (24 <=? Z.of_nat (length C)) && ((pcap_magicZ C =? 0xA1B2C3D4) || (pcap_magicZ C =? 0xD4C3B2A1)).
Definition pcap_swZ (C : list Z) : Z := if pcap_magicZ C =? 0xD4C3B2A1 then 1 else 0.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
(* Every image datum is a parameter (shared-statement rule, a Theorem Labs lane 22:2xZ, for the asan-ubsan twin):
   the segments, the read-only range of the relocations (rlo, rhi), the three addresses the call reads (the
   "<fuzz-input>" literal, g_file_len and g_file), and the predicate on memory that the read-only image holds (the
   strcmp premise of libreac_fuzz_fopen). On the ASan pin, PcapSourceOpen.v takes segs := pa_segs,
   rlo := pa_relro_lo, rhi := pa_relro_hi, apath / alen / afile := the listing's objects 3 / 4 / 2
   (0x20d00 / 0x5d3f40 / 0x5d3f60) and roimg := ro_img. *)
Variable segs : list Segment.
Variables rlo rhi : Z.
Variables apath alen afile : Z.
Variable roimg : (word -> option byte) -> Prop.
#[local] Abbreviation SEGS := segs.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section e.
Variable B : asyms.
Variable K : asource_syms.
Variable MT : ameter_ops.
(* libreac_fuzz_fopen's statement variables (PcapFuzzFopenDefs.v): the return address of the malloc call
   inside the C library's fmemopen, and the call spines the call of libreac_fuzz_fopen may run under. *)
Variable FM_RA : Z.
Variable CTX : list (list Z).

(* The meter the call may spend: fmemopen's malloc and fclose's two frees. *)
Definition OPEN_METER : Z := mo_malloc MT SRC_FILE_BLOCK + (mo_free MT + mo_free MT).

(* What a call keeps (PcapSourceClose.v's tclose_kept; the kit's acall_kept, YCbq.v:823-834, without the open-file
   list head, which fmemopen sets and fclose clears): every byte above the allocator's ceiling outside the call's
   stack window, every byte of a heap block and of a frame that is not in E, every image byte but the runtime's own
   statics, errno and the list head, and the presence of the window. *)
Definition topen_kept (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte)
  (W2 : world SEGS) (mem2 : word -> option byte) (slo shi : Z) (E : Z -> Prop) : Prop :=
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) ->
     aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall b m i, In (b, m) (ablocks B lyc Sc) -> 0 <= i < req_size m -> ~ E (b + i) ->
     aview SEGS (w_H W2) mem2 (b + i) = aview SEGS (w_H W) memc (b + i)) /\
  (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
     ~ (AOFL_HEAD <= a < AOFL_HEAD + 8) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall cid pos a, In (cid, pos) (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos)) \/ in_zr a (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8)) ->
     ~ E a -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) memc a) /\
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (slo <= a < shi) -> apresent (w_H W) memc a -> apresent (w_H W2) mem2 a) /\
  (forall a, slo <= a < shi -> apresent (w_H W2) mem2 a).

(* ---- the contract -------------------------------------------------------- *)

(* The post: back at the caller's return address, the callee-saved registers and the frame list kept, the
   descriptors and the file system kept (no callee touches them; the journal alone would allow it, its footprint
   being sink-open), only ps[0..22) written among the caller's bytes, the meter within OPEN_METER, the three zeroed
   fields; then either the accepted file or the refused one, each with the caller's journal extended by its own
   bound on allocator events (ajournal's index is an upper bound: st_nev S' <= st_nev S + k, YCbq.v:354):
   - accepted (a0 = 0): k + EV_FUZZ_FOPEN = k + 1: fmemopen's malloc inside libreac_fuzz_fopen (0x81570); the fread
     wrapper (0x815f8) makes none (PFreadISpec.v: its journal has 0 events); no fclose on this path. The FILE block
     is appended to the blocks, ps->f = f, ps->swapped = pcap_swZ C, the stream is past its 24-byte global header.
   - refused (a0 = -1): k + EV_OPEN = k + 3: the empty input makes none (libreac_fuzz_fopen returns NULL at 0x8078c
     without calling fmemopen), the short read and the bad magic make three (the malloc, and fclose's free of the FILE
     block and free of NULL, 0x81674 / 0x816b8). ps->f = NULL, ps->swapped untouched, the blocks the caller had, no
     stream open. *)
Definition tpcap_source_open_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (ps b : Z) (C : list Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
  c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
  aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
  topen_kept lyc Sc W memc W2 mem2 (spZ regs - TPCAP_SOURCE_OPEN_STK) (spZ regs) (fun a => ps <= a < ps + 22) /\
  mo_le MT Sc S2 OPEN_METER /\
  val_mem SEGS (rdW W2 mem2) (ps + 12) 4 0 /\ val_mem SEGS (rdW W2 mem2) (ps + 16) 4 0 /\
  val_mem SEGS (rdW W2 mem2) (ps + 20) 2 0 /\
  ((* accepted *)
   (ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_FUZZ_FOPEN) /\
    getr regs2 10 = w64 0 /\ pcap_goodZ C = true /\
    (exists f, 4096 <= f /\ f mod 16 = 0 /\
       ablocks B ly2 S2 = ablocks B lyc Sc ++ [(f, SRC_FILE_BLOCK)] /\
       val_mem SEGS (rdW W2 mem2) ps 8 f /\ val_mem SEGS (rdW W2 mem2) (ps + 8) 4 (pcap_swZ C) /\
       asource_at SEGS K (rdW W2 mem2) f b C 24 /\
       mo_le MT Sc S2 (mo_malloc MT SRC_FILE_BLOCK)))
   \/
   (* refused *)
   (ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_OPEN) /\
    getr regs2 10 = w64 (-1) /\ pcap_goodZ C = false /\
    val_mem SEGS (rdW W2 mem2) ps 8 0 /\
    (forall i, 8 <= i < 12 -> aview SEGS (w_H W2) mem2 (ps + i) = aview SEGS (w_H W) memc (ps + i)) /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    asource_none SEGS K (rdW W2 mem2))).

Definition tpcap_source_open_specX (a : Z) : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) ch
    (ps n b M : Z) (C : list Z) (cid pos : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  arodata_okP SEGS rlo rhi B (aview SEGS (w_H W) memc) ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 ps -> getr regs 11 = w64 apath ->
  (* the call chain, whose spine libreac_fuzz_fopen's CTX must hold once this function's frame record is on it *)
  achain lyc (aview SEGS (w_H W) memc) (spZ regs) (s0Z regs) ch -> In (raZ regs :: spine ch) CTX ->
  (* the stack: this call's window lies in the caller's journal window, below the layout's top *)
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TPCAP_SOURCE_OPEN_STK -> spZ regs <= sp0 ->
  spZ regs + 32 <= ly_top lyc -> Z.of_nat (length (frames Sc)) <= 7 ->
  (* the struct: 24 bytes in a side-stack frame the caller took, its shadow marked usable *)
  In (cid, pos) own -> frame_addr lyc cid pos <= ps -> ps + 24 <= frame_addr lyc cid pos + fs_frame_bytes cid ->
  ps <> 0 -> ps mod 8 = 0 ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF ps 24 ->
  (* the callees' footprints name the open-file list head (the sink token); the caller's journal must spare it *)
  inFP FP 0 ->
  (* what libreac_fuzz_fopen reads: the path literal, the two globals, the input bytes; no stream open *)
  roimg (rdW W memc) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF apath 13 ->
  shadow_hull_vis (aview SEGS (w_H W) memc) apath 13 ->
  val_mem SEGS (rdW W memc) alen 8 n -> val_mem SEGS (rdW W memc) afile 8 b ->
  0 <= b < 2 ^ 64 ->
  asource_none SEGS K (rdW W memc) ->
  n = Z.of_nat (length C) -> n < 2 ^ 26 ->
  (1 <= n -> In (b, n) (ablocks B lyc Sc) /\ garr8 SEGS (rdW W memc) b C /\ bytes_ok C) ->
  (* what fclose reads on the refused paths: the meta region *)
  asrc_meta_inv SEGS K lyc (rdW W memc) M ->
  (* room *)
  st_nev Sc + EV_OPEN <= EV_MAX -> blocks_bytes Sc + SRC_FILE_BLOCK <= LIVE_MAX ->
  mo_ok MT Sc (mo_malloc MT SRC_FILE_BLOCK) ->
  (* the call traces of fmemopen's malloc *)
  In [pc_malloc_ra0 (as_code B)] (as_universe B) ->
  (forall c, In c CTX -> In (firstn kUnwindMax (pc_malloc_ra0 (as_code B) ::
     flat_map (fun r => if r =? pc_malloc_ra0 (as_code B) then [] else [r]) (FM_RA :: c))) (as_universe B)) ->
  SRr SEGS W (cfg_at SEGS a regs memc mdc)
    (tpcap_source_open_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps b C).

End e.
End d.
End b.

(* The open-file list head that every journal and stream premise names is the sink-head instance's (YI16.sk_ofl_head,
   YCbq.AOFL_HEAD). No global sink_head instance is in scope here (the check below), so every use inside the Sections
   is the Section's own SK; and SK is an explicit argument of the exported names, so no caller obtains it by
   inference (a Theorem Labs lane ruling 21:57Z: the only global instance, lib/Reusable/YI5b.v src0_sink_head, is
   the plain build's head 0x4f3b0, not the ASan pin's 0x5f4f88). *)
Fail Definition sink_head_probe : YI16.sink_head := _.
Arguments tpcap_source_open_specX {fx rc} SK segs rlo rhi apath alen afile roimg B K MT FM_RA CTX a.
Arguments tpcap_source_open_post {fx rc} SK segs B K MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps b C _ _.
Arguments topen_kept {rc} SK segs B lyc Sc W memc W2 mem2 slo shi E.
(* Guards: each fails to typecheck if SK ever becomes implicit again, or if an image datum stops being an explicit
   parameter (full positional argument lists). *)
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment)
           (rlo rhi apath alen afile : Z) (roimg : (word -> option byte) -> Prop) (B : asyms) (K : asource_syms)
           (MT : ameter_ops) (FM_RA : Z) (CTX : list (list Z)) (a : Z) =>
         tpcap_source_open_specX (fx := fx) (rc := rc) SK segs rlo rhi apath alen afile roimg B K MT FM_RA CTX a : Prop).
Check (fun (fx : YK11.FPState) (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment) (B : asyms)
           (K : asource_syms) (MT : ameter_ops) STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ps b C =>
         tpcap_source_open_post (fx := fx) (rc := rc) SK segs B K MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc
           k regs ps b C).
Check (fun (rc : YM05.RunCeil) (SK : YI16.sink_head) (segs : list Segment) (B : asyms) lyc Sc W memc W2 mem2 slo shi E =>
         topen_kept (rc := rc) SK segs B lyc Sc W memc W2 mem2 slo shi E : Prop).
