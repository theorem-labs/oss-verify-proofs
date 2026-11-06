(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/RepIFcf.v (commit 4d286b2e618d, file sha256 6ed977bcb965) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 16 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 14 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepIFcf.v (commit f01d79f3fb5, cf refill round 3; file sha256 b8fc87cc008a) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 16 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 11 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 2 pair(s) carry a BY-HAND acceptance (the internal file accept.tsv, re-measured each run): _ZN11__sanitizer20SizeClassAllocator64IN6__asan4AP64INS_21LocalAddressSpaceViewEEEE17PopulateFreeArrayEPNS_14AllocatorStatsEmPNS5_10RegionInfoEm+0xb0 (lui-in-section: CONSTANT (size; enters a store base only as a scaled count into a runtime array): kUserMapSize = 0x40000), _ZN11__sanitizer9VSNPrintfEPciPKcPv+0x1c0 (data-differs: ACCEPTED by hand: jump table (33 entries, each the same VSNPrintf+off on both images))), and 21 pcs named in comments; 5 hand maps (the internal file resolve-run-f01d79f3fb5.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a prior worker, a Theorem Labs lane's class-full report walk): the INTERFACE of the report walk at
   cgif_file_fuzzer's asan-ubsan image (pin 1c29845fe605), so its slices can be written in parallel against a fixed
   text.  This file states; it proves nothing about the machine.
   rule 24: no function proved here (kind: statement heads; the lane's reuse search is
   a Theorem Labs lane's internal file LOOKUP-refill-report.txt, `proof-index PopulateFreeArray
   AppendToErrorMessageBuffer MapWithCallbackOrDie ReportMmapFailureAndDie` 2026-10-30T00:36:25Z, 0 named walks).

   The walk concludes MnRefillSeamcf.refill_B3_classfull_cf: PopulateFreeArray's class-full arm (0x370b0: lbu
   0x44(s0); 0x37100 sb 1; the two Printfs at 0x37110 / 0x37184) realizes the cf tree's
   `errb_report_cf c ;; set_exh_cf c` (YG00cf.v:147-150, :177).  Every number below was read from the image bytes
   (a prior worker's internal file rvdis.py over a prior worker's recovered-symbol cache the internal file 1c29845fe6058de6.978e0a064c5a4c6e.v4.json).

   The slices and their heads:
   - F3 [vsn_spec_cf]: __sanitizer::VSNPrintf (0x6795c, with AppendNumber 0x6891c) for the two formats of the arm,
     into Printf's 400-byte stack buffer.  Pure machine run (SRr), no model event.
   - F4+F5 [append_spec_cf]: __asan::AppendToErrorMessageBuffer (0x55df8): the Mutex lock / unlock on the object's
     state word, InternalMmapVector<char> resize (InternalMmapVectorNoCtor<char,true>::Realloc 0x5981c ->
     MmapOrDie 0x66a74 -> GetNamedMappingFd / internal_mmap / IncreaseTotalMmap; UnmapOrDie of the old buffer),
     internal_strlen / internal_memset / internal_memcpy.  It realizes the model's errb_append_cf (YG00cf.v:133):
     the KMmapSec ask of each (re)map is the machine's mmap node, and the grant is forced there (a Theorem Labs lane's
     errb_map_fits_cf, a named hypothesis of the slice until a Theorem Labs lane proves it), so the machine's refused
     branch is vacuous.
   - F2 [printf_spec_cf]: __sanitizer::Printf (0x67f24) -> SharedPrintfCode (0x68628, internal_memset of the
     400-byte buffer to 0xaa) -> SharedPrintfCodeNoBuffer (0x6852c, append_pid = false): VSNPrintf (F3), RawWrite
     (0x61a58: internal_strlen + ReportFile::Write 0x67628, which returns at once since the RELRO word 0xa3418 is 1:
     no write syscall), RemoveANSIEscapeSequencesFromString (0x60f2c), __sanitizer_on_print (0x685d8, ret), the
     callback *0x137f90 = AppendToErrorMessageBuffer (F4+F5, taken as a hypothesis), LogMessageOnPrintf (0x6e064:
     log_to_syslog = common_flags + 0x40 = 0), UnmapOrDie(0, 0) of the unused vector (0x66bf4).
   - F1 + top (a prior worker): the arm, the two Printf calls, the return to the populate-false join 0x37038, and
     the leaf.

   Relation facts this text takes by NAME (a Theorem Labs lane 2026-10-30 01:59Z / 02:01Z; their text is a Theorem Labs lane's, as
   conjuncts of ARX_cf): [exh_cell_cf] (the class's RI+68 byte is 1 iff exh_mem_cf) and [errb_cells_cf] (the
   error-message buffer's object cells and buffer per errb_e), a Theorem Labs lane's text (YG0ncf.v since field round 2, which
   moved them unchanged from YGcfInstBase.v and made them ARmcf's fields amc_exh_cell / amc_errb_cells too).
   Image facts not in TfibSyms' as_const (a Theorem Labs lane's decision (b), 01:59Z): the tool-name pointer, the Printf
   callback cell and the RELRO silent word, the record [rep_img_facts]. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBase.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseAG AGif0n. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfInstBase YGcfInstRefill.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfXs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require MemnormT.
Import ListNotations.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. The image's numbers (cgif_file_fuzzer.asan-ubsan).                                                            *)
Definition A_PRINTF : Z := 0x67f24.        (* __sanitizer::Printf *)
Definition A_VSNPRINTF : Z := 0x6795c.     (* __sanitizer::VSNPrintf *)
(* __asan::AppendToErrorMessageBuffer = 347116 *)
Definition A_APPEND : Z := 0x55df8.
Definition FMT_OOM1 : Z := 0x1ea32.        (* "%s: Out of memory. " *)
Definition FMT_OOM2 : Z := 0x202fd.        (* "The process has exhausted %zu MB for size class %zu (%zu bytes).\n" *)
Definition A_TOOLNAME : Z := 0x20449.      (* "AddressSanitizer" *)
(* __sanitizer::SanitizerToolName (YB01.v:14 / YB03.v:12: 655584 -> 131783) *)
Definition C_TOOLNAME : Z := 0xa4718.
(* PrintfAndReportCallback (YB03: 1277840 -> 347116) *)
Definition C_PFCB : Z := 0x13d410.
(* the RELRO word ReportFile::Write tests (= 1) *)
Definition C_SILENT : Z := 0xa3418.
Definition C_ERRBUF : Z := 0xaaf68.        (* __asan::error_message_buffer (the vector pointer) *)
(* its Mutex state word (C_ERRBUF + 0x10) *)
Definition C_ERRBUF_MU : Z := 0xaaf78.
Definition C_ERRBUF_VEC : Z := 0xaaf88.    (* error_message_buffer_placeholder: data / capacity / size *)
(* kRegionSize >> 20, the arm's `lui a1, 1` at 0x37180 *)
Definition REGION_MB : Z := 4096.

(* Stack windows (bytes below the callee's entry sp), from the prologues: Printf 0x50, SharedPrintfCode 0x1b0,
   SharedPrintfCodeNoBuffer 0x80 (together 640; PR_STK keeps 720), VSNPrintf 0x80 + AppendNumber 0x150 (464), Append 0x60 + Realloc
   0x20 + MmapOrDie 0x30 + GetNamedMappingFd 0x110 (448).  The MmapOrDie refusal branch is vacuous at the errbuf map
   (a Theorem Labs lane 2026-10-30 02:35Z: the grant is forced under ARX_cf's room invariant; errb_map_fits_cf), so no window covers
   ReportMmapFailureAndDie.  The refill's REP_STACK (YGcfInstRefill.v) must be at least 0xe0 (Refill 0x20 +
   GetFromAllocator 0x80 + PopulateFreeArray 0x40) + PR_STK = 1456. *)
Definition VSN_STK : Z := 512.
Definition APP_STK : Z := 512.
Definition PR_STK : Z := 720 + APP_STK.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The two rendered lines.                                                                                       *)
Definition str_z (s : string) : list Z := map (fun a => Z.of_nat (nat_of_ascii a)) (list_ascii_of_string s).
Fixpoint dec_rev (fuel : nat) (x : Z) : list Z :=
  match fuel with
  | O => []
  | S f => (48 + x mod 10) :: (if x <? 10 then [] else dec_rev f (x / 10))
  end.
(* the decimal digits of x >= 0, as VSNPrintf's %zu writes them (no padding) *)
Definition dec_z (x : Z) : list Z := rev (dec_rev 20 x).
Definition render1 : list Z := str_z "AddressSanitizer" ++ str_z ": Out of memory. ".
Definition render2 (c sz : Z) : list Z :=
  str_z "The process has exhausted " ++ dec_z REGION_MB ++ str_z " MB for size class " ++ dec_z c ++
  str_z " (" ++ dec_z sz ++ str_z " bytes)." ++ [10].
(* The lines have the model's lengths (YGcfNames.v:134-135), checked over the arm's 31 classes. *)
Lemma len_render1 : Z.of_nat (length render1) = exh_len1.
Proof. vm_compute. reflexivity. Qed.
Lemma len_render2_all :
  forallb (fun c => Z.of_nat (length (render2 c (class_size c))) =? exh_len2 c) (map Z.of_nat (seq 1 31)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma len_render2 : forall c, 1 <= c <= 31 -> Z.of_nat (length (render2 c (class_size c))) = exh_len2 c.
Proof.
intros c Hc. pose proof len_render2_all as A. rewrite forallb_forall in A.
apply Z.eqb_eq, A. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The formats and their arguments: which format, what the va_list's 8-byte slots hold, which line it renders.  *)
Definition fmt_case (m : word -> option byte) (fmt va : Z) (out : list Z) : Prop :=
  (fmt = FMT_OOM1 /\ val_mem tfibsegs m va 8 A_TOOLNAME /\ out = render1) \/
  (exists c sz, fmt = FMT_OOM2 /\ 1 <= c <= 31 /\ sz = class_size c /\
     val_mem tfibsegs m va 8 REGION_MB /\ val_mem tfibsegs m (va + 8) 8 c /\ val_mem tfibsegs m (va + 16) 8 sz /\
     out = render2 c sz).

(* The read-only image bytes VSNPrintf reads.  A data load reads mem before seg_rom (YK11.v:193-201), so they are
   facts of the state, like rep_img_facts below (RepF3Vsn 02:4xZ): the two formats with their NULs, the tool name, and
   the switch's jump-table words for 's' and 'u' (0x67b24: lw t3, 0(t3); table 0x20c68, index char - 0x58). *)
Definition ro_bytes (m : word -> option byte) (a : Z) (s : list Z) : Prop :=
  forall i, (i < length s)%nat -> val_mem tfibsegs m (a + Z.of_nat i) 1 (nth i s 0).
Definition FMT1_BYTES : list Z := str_z "%s: Out of memory. " ++ [0].
Definition FMT2_BYTES : list Z :=
  str_z "The process has exhausted %zu MB for size class %zu (%zu bytes)." ++ [10; 0].
Record vsn_img_facts (m : word -> option byte) : Prop := {
  vif_fmt1 : ro_bytes m FMT_OOM1 FMT1_BYTES;
  vif_fmt2 : ro_bytes m FMT_OOM2 FMT2_BYTES;
  vif_tool : ro_bytes m A_TOOLNAME (str_z "AddressSanitizer" ++ [0]);
  vif_jt_s : val_mem tfibsegs m 0x20cd4 4 0x46ef0;
  vif_jt_u : val_mem tfibsegs m 0x20cdc 4 0x46ec8
}.

(* F3: VSNPrintf(buf, 400, fmt, va) for the arm's two formats. *)
Definition vsn_spec_cf : Prop :=
forall (W : world tfibsegs) (ly : alayout) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
  (buf fmt va : Z) (out : list Z),
let H := w_H W in let m := mrestrict H mem in let sp := bv_unsigned (getr regs 2) in
layout_ok ly -> img_cover ly ->
getr regs 10 = w64 buf -> getr regs 11 = w64 400 -> getr regs 12 = w64 fmt -> getr regs 13 = w64 va ->
getr regs 4 = w64 TFIB_TP -> YK0s.ret_ok (getr regs 1) ->
fmt_case m fmt va out -> vsn_img_facts m -> Z.of_nat (length out) < 400 ->
sp mod 16 = 0 -> ly_stk_lo ly <= sp - VSN_STK -> (forall a, sp - VSN_STK <= a < sp -> apresent H mem a) ->
sp <= buf -> buf + 400 <= ly_stk_hi ly -> (forall a, buf <= a < buf + 400 -> apresent H mem a) ->
(va + 24 <= buf \/ buf + 400 <= va) -> sp <= va -> va + 24 <= ly_stk_hi ly ->
SRr tfibsegs W (mkCfg (mkst regs (w64 A_VSNPRINTF) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists regs' mem' mat,
  c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
  regs_preserved regs regs' /\ getr regs' 10 = w64 (Z.of_nat (length out)) /\
  (forall x : word, ~ (sp - VSN_STK <= bv_unsigned x < sp) ->
     ~ (buf <= bv_unsigned x <= buf + Z.of_nat (length out)) -> mem' x = mem x) /\
  (forall a, apresent H mem a -> apresent H mem' a) /\
  (forall i, (i < length out)%nat -> val_mem tfibsegs (mrestrict H mem') (buf + Z.of_nat i) 1 (nth i out 0)) /\
  val_mem tfibsegs (mrestrict H mem') (buf + Z.of_nat (length out)) 1 0).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The errbuf calls (F2, F4+F5): one append of [len] bytes, model step errb_append_cf len.                      *)
Variable B : asyms.
(* a Theorem Labs lane's two relation facts, by name: YG0ncf.v exh_cell_cf / errb_cells_cf (commit 24612d340b06's text, agreed with
   a prior worker 2026-10-30 02:13Z; moved unchanged from YGcfInstBase.v by field round 2, dd8e46fd954). *)
(* The image facts at the call state: the three cells and VSNPrintf's read-only bytes. *)
Record rep_img_facts (W : world tfibsegs) (mem : word -> option byte) : Prop := {
  rif_toolname : val_mem tfibsegs (mrestrict (w_H W) mem) C_TOOLNAME 8 A_TOOLNAME;
  rif_callback : val_mem tfibsegs (mrestrict (w_H W) mem) C_PFCB 8 A_APPEND;
  rif_silent : val_mem tfibsegs (mrestrict (w_H W) mem) C_SILENT 8 1;
  rif_vsn : vsn_img_facts (mrestrict (w_H W) mem)
}.

(* A HELD region lock (a Theorem Labs lane's decision (B), 2026-10-30 03:42Z; RepF1Top's gap: the class-full arm calls Printf with
   class c's RegionInfo mutex word at 2^60, the __sanitizer::Mutex writer bit (YFk8cf.v:33 R3_P .. R3_M4), and ARcf pins
   that word to 0 (YG0ncf.v:44, region_cells' first cell z8 (ASp (kRegionInfoOff + 128 * c)) 0, YG0n.v:33-36)).  The
   relation is stated over the memory with the held word reset to 0; the word itself is 2^60.  The layer is unchanged.
   [lk = None] is the unlocked call.  exh_cell_cf and errb_cells_cf read other cells (RegionInfo + 68 and the errbuf
   object, YG0ncf.v), so they stay over the machine memory. *)
Definition region_lock_addr (ly : alayout) (c : Z) : Z := ly_space ly + kRegionInfoOff + 128 * c.
Definition in8 (a : Z) (x : word) : bool := (a <=? bv_unsigned x) && (bv_unsigned x <? a + 8).
Definition held_mem (lk : option Z) (mem : word -> option byte) : word -> option byte :=
  match lk with
  | None => mem
  | Some a => fun x => if in8 a x then Some (Z_to_bv 8 0) else mem x
  end.
Definition lk_ok (ly : alayout) (lk : option Z) : Prop :=
  lk = None \/ exists c, 1 <= c <= 31 /\ lk = Some (region_lock_addr ly c).
Definition ARcf_locked (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) : Prop :=
  lk_ok ly lk /\ ARcf tfibsegs B ly S Hp W (held_mem lk mem) md /\
  match lk with None => True | Some a => val_mem tfibsegs (mrestrict (w_H W) mem) a 8 (2 ^ 60) end.

(* Taking the lock: a memory that is the unlocked one except on the 8 lock bytes, which were 0, resets to it. *)
Lemma held_mem_lock : forall a (mem mem' : word -> option byte),
  (forall x, in8 a x = false -> mem' x = mem x) -> (forall x, in8 a x = true -> mem x = Some (Z_to_bv 8 0)) ->
  held_mem (Some a) mem' = mem.
Proof.
intros a mem mem' K Z0. apply functional_extensionality. intros x. cbn [held_mem].
destruct (in8 a x) eqn:E; [symmetry; apply Z0; exact E | apply K; exact E].
Qed.
(* Releasing it: writing 0 to the 8 lock bytes gives the reset memory back, so ARcf holds unlocked. *)
Lemma held_mem_unlock : forall a (mem mem'' : word -> option byte),
  (forall x, in8 a x = false -> mem'' x = mem x) -> (forall x, in8 a x = true -> mem'' x = Some (Z_to_bv 8 0)) ->
  mem'' = held_mem (Some a) mem.
Proof.
intros a mem mem'' K Z0. apply functional_extensionality. intros x. cbn [held_mem].
destruct (in8 a x) eqn:E; [apply Z0; exact E | apply K; exact E].
Qed.
Lemma ARcf_unlock : forall a Hp ly S W mem mem'' md,
  ARcf tfibsegs B ly S Hp W (held_mem (Some a) mem) md ->
  (forall x, in8 a x = false -> mem'' x = mem x) -> (forall x, in8 a x = true -> mem'' x = Some (Z_to_bv 8 0)) ->
  ARcf tfibsegs B ly S Hp W mem'' md.
Proof. intros a Hp ly S W mem mem'' md H K Z0. rewrite (held_mem_unlock a mem mem'' K Z0). exact H. Qed.
Lemma ARcf_locked_none : forall Hp ly S W mem md,
  ARcf_locked None Hp ly S W mem md <-> ARcf tfibsegs B ly S Hp W mem md.
Proof. intros. unfold ARcf_locked, lk_ok. cbn [held_mem]. split; [tauto | intros H; split; [left; reflexivity | tauto]]. Qed.

(* The event slack one append needs (RepF4Append's 6th finding): the FIRST append adds the capacity entry with one
   tick (errb_map_cf, YG00cf.v:122-127) AND the size entry with none (errb_set_size, :91-96, find_sz = None), so the
   entry count gains one more than the event count; every later append updates the size entry in place.  This is
   errb_append_cf_ok's premise (YG06bcf.v:321-323) in the model's slack vocabulary. *)
Definition errb_slack (S : astate) : Z := match find_sz (st_secs S) 0 with None => 1 | Some _ => 0 end.

(* qloose S (YG01.v:339) is the quarantine bound the layer's room of record needs (room_rec_cf_of_live,
   YGcfRoomCf.v:322; RepF4Append's 9th finding); the refill state carries it (YGcfInstRefill.v:485) and the errbuf
   steps keep it (they touch only st_secs). *)
(* The state premises an errbuf call needs, re-established by its post: the relation and its two named conjuncts.
   The room of the call is a separate premise (errb_room_for, YG06bcf.v:322's errb_append_cf_ok premise): one
   report's ERRB_ROOM (YG00cf.v:107) gives it for both of the arm's appends, 33 + at most 67 bytes.
   cf_hull_ok S (CfParams' hull admission, YGcfNames.v) is the room of record's other premise
   (YGcfRoomCf.room_rec_cf_of_live; a Theorem Labs lane 2026-10-30 11:31Z). *)
Definition errb_call_pre (lk : option Z) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs)
  (mem : word -> option byte) (md : Model) : Prop :=
  cf_errbuf_obj = C_ERRBUF /\ cf_exh_off = 68 /\
  layout_ok ly /\ img_cover ly /\ TfibSyms B /\ ly_tsd ly = TFIB_TSD /\
  ARcf_locked lk Hp ly S W mem md /\ xs_mapped_cf ly S md /\ WfP_cf (as_universe B) 0 (errb_slack S) 0 S /\ qloose S /\
  YG0ncf.exh_cell_cf B ly S (aview tfibsegs (w_H W) mem) /\ YG0ncf.errb_cells_cf B ly S (aview tfibsegs (w_H W) mem) /\
  rep_img_facts W mem /\ cf_hull_ok S.

(* The post of a call that entered at [regs] (sp = spZ regs) with a STK-byte window and model state S, and returns
   at the model state S' (the result of errb_append_cf len; its size grew by at most len): the relation rebuilt over a grown layout and world, the
   callee-saved registers, the frame (writes only in the window or the allocator's owned sets), the memnorm keep. *)
Definition errb_room_for (S : astate) (len : Z) : Prop := errb_size_cf S + len + kPage <= cf_nob.
Definition errb_call_post (lk : option Z) (STK len : Z) (Hp : list Z) (ly : alayout) (S S' : astate) (W : world tfibsegs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (W' : world tfibsegs) (c' : config) : Prop :=
  exists ly' regs' mem' md',
  c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
  errb_call_pre lk Hp ly' S' W' mem' md' /\ errb_size_cf S' <= errb_size_cf S + len /\
  layout_le (length (st_secs S)) ly ly' /\ wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ AOX_cf B ly S a -> ~ AOX_cf B ly' S' a -> ~ (spZ regs - STK <= a < spZ regs) ->
     aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a) /\
  (forall x : word, ~ AOX_cf B ly S (bv_unsigned x) -> ~ AOX_cf B ly' S' (bv_unsigned x) ->
     ~ (spZ regs - STK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
  MemnormT.memnorm_keep tfibsegs mem mem' /\
  (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W') mem' a).

(* The call-site premises shared by both errbuf calls: gp, tp, a returning ra, the window present and aligned. *)
Definition errb_call_regs (STK : Z) (ly : alayout) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) : Prop :=
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 TFIB_TP /\ YK0s.ret_ok (getr regs 1) /\
  4096 <= bv_unsigned (getr regs 1) /\ spZ regs mod 16 = 0 /\ ly_stk_lo ly <= spZ regs - STK /\
  spZ regs <= ly_stk_hi ly /\ (forall a, spZ regs - STK <= a < spZ regs -> apresent (w_H W) mem a).

(* F4+F5: AppendToErrorMessageBuffer(p), p a NUL-terminated string s (no NUL inside) in the caller's frame.
   s is at most ERRB_INIT bytes (RepF4Append's 8th finding): a longer FIRST append maps the 64 KiB buffer and at once
   remaps it, so the first buffer is in AOX_cf at neither end and the raw frame of errb_call_post fails on it.  The
   only caller, Printf, appends < 400 bytes. *)
Definition append_spec_cf : Prop :=
forall (R : Type) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (p : Z) (s : list Z) (lk : option Z)
  (K : astate -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop),
errb_call_pre lk Hp ly S W mem md -> errb_room_for S (Z.of_nat (length s)) -> errb_call_regs APP_STK ly W regs mem ->
getr regs 10 = w64 p -> spZ regs <= p -> p + Z.of_nat (length s) + 1 <= ly_stk_hi ly ->
Z.of_nat (length s) <= ERRB_INIT ->
(forall i, (i < length s)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat i) 1 (nth i s 0) /\ 0 < nth i s 0 < 256) ->
val_mem tfibsegs (mrestrict (w_H W) mem) (p + Z.of_nat (length s)) 1 0 ->
(forall S' W' c', errb_call_post lk APP_STK (Z.of_nat (length s)) Hp ly S S' W regs mem md W' c' -> amreal tfibsegs (K S') W' c' Q) ->
amreal tfibsegs (ibind (errb_append_cf (Z.of_nat (length s)) S) (fun r => K (snd r)))
  W (cfg_at tfibsegs A_APPEND regs mem md) Q.

(* F2: Printf(fmt, a1, a2, a3) for the arm's two formats (the arguments in a1 .. a3 as fmt_case's slots). *)
Definition printf_spec_cf : Prop :=
forall (R : Type) (Hp : list Z) (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (fmt : Z) (out : list Z) (lk : option Z)
  (K : astate -> itree astate R) (Q : R -> world tfibsegs -> config -> Prop),
errb_call_pre lk Hp ly S W mem md -> errb_room_for S (Z.of_nat (length out)) -> errb_call_regs PR_STK ly W regs mem ->
getr regs 10 = w64 fmt ->
((fmt = FMT_OOM1 /\ getr regs 11 = w64 A_TOOLNAME /\ out = render1) \/
 (exists c sz, fmt = FMT_OOM2 /\ 1 <= c <= 31 /\ sz = class_size c /\ getr regs 11 = w64 REGION_MB /\
    getr regs 12 = w64 c /\ getr regs 13 = w64 sz /\ out = render2 c sz)) ->
Z.of_nat (length out) < 400 ->
(forall S' W' c', errb_call_post lk PR_STK (Z.of_nat (length out)) Hp ly S S' W regs mem md W' c' -> amreal tfibsegs (K S') W' c' Q) ->
amreal tfibsegs (ibind (errb_append_cf (Z.of_nat (length out)) S) (fun r => K (snd r)))
  W (cfg_at tfibsegs A_PRINTF regs mem md) Q.

(* The composition F2 proves: Printf from F3 and F4+F5. *)
Definition printf_of_parts_t : Prop := vsn_spec_cf -> append_spec_cf -> printf_spec_cf.

End a.
