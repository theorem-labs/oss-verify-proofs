(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/RepVsnD.v (commit f01d79f3fb5, cf refill round 3; file sha256 a796390fc9bd) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 5 image addresses moved by function pairs the comparison kit cmpkit 86da41d3ef68 calls the same code except at the by-hand acceptances named below (strictcmp3 65688e94214a, by funcpair_reply 6963bc4a94fc on the cgif twin ce511d541cda; 0 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the pair, each data one a pc-relative target of both paired functions; 0 code pcs the tool read as sizes, by the pair; 1 pair(s) carry a BY-HAND acceptance (accept.tsv, re-measured each run): _ZN11__sanitizer9VSNPrintfEPciPKcPv+0x1c0 (data-differs: ACCEPTED by hand: jump table (33 entries, each the same VSNPrintf+off on both images))), and 6 pcs named in comments; 5 hand maps (resolve-run-f01d79f3fb5.tsv (sha256 ba54f3af32ab; internal record), each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Theorem Labs, 2026-10-30 (a Theorem Labs lane, the class-full report walk, slice F3): the seed states and the run checks
   of __sanitizer::VSNPrintf (0x68014, with AppendNumber 0x6891c and internal_memset 0x6525c) for the two formats of
   PopulateFreeArray's class-full arm.  RepVsncf.v proves RepIFcf.vsn_spec_cf from them.
   rule 24: no function proved here (kind: seed states and boolean run checks; the lane's reuse search is
   `proof-index VSNPrintf Printf SharedPrintfCode AppendNumber AppendToErrorMessageBuffer MmapOrDie`
   2026-10-30T02:25:54Z, index v5: no VSNPrintf contract to reuse).

   One seed per case: the format string, the tool name and the switch's jump-table words as read-only regions
   (RepIFcf.vsn_img_facts gives their bytes), the va_list's slots as a read-only region on a3's atom, Printf's buffer
   as a region on a0's atom whose writable window is exactly the line and its NUL, VSNPrintf's 512-byte stack window
   on sp's atom.  The run is concrete per case (the second format's arguments are 4096, c, class_size c), so each
   case is ONE boolean [vchk] that runs the engine to the [ret] at 0x684a4 and checks the final state: the
   callee-saved registers and ra restored, a0 = the line's length, the windows unchanged, and the buffer's bytes.
   The only branch the engine cannot decide alone is internal_memset's alignment test (0x65264: (240 | p) & 15 with
   p = sp - 456, AppendNumber's digit array); the seed's alias fact [MS_AL] = 8 decides it (sp mod 16 = 0). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0m YF0x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RepIFcf.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Regions.                                                                                                       *)
(* a read-only image string: one 1-byte chunk per byte *)
Definition vrom (a : Z) (bs : list Z) : YP09.region :=
  YP09.mkRegion None a (a + Z.of_nat (length bs)) 0 0
    (map (fun i => YP09.mkChunk (a + Z.of_nat i) (CVal 1 (SLit (nth i bs 0)))) (seq 0 (length bs))).
Definition vlit4 (a v : Z) : YP09.region := YP09.mkRegion None a (a + 4) 0 0 [YP09.mkChunk a (CVal 4 (SLit v))].
Definition TOOL_BYTES : list Z := str_z "AddressSanitizer" ++ [0].
Definition JT_S : Z := 0x20bf4.
Definition JT_U : Z := 0x20bfc.
Definition ROM_JT : smem := [vlit4 JT_S 0x47688; vlit4 JT_U 0x47660].
Definition ROM1 : smem := vrom FMT_OOM1 FMT1_BYTES :: vrom A_TOOLNAME TOOL_BYTES :: ROM_JT.
Definition ROM2 : smem := vrom FMT_OOM2 FMT2_BYTES :: ROM_JT.
(* VSNPrintf's frame 0x80 + AppendNumber's 0x150 lie in sp - 512 .. sp *)
Definition R_S : YP09.region := YP09.mkRegion (Some 2%nat) (- VSN_STK) 0 (- VSN_STK) 0 [].
(* Printf's buffer: n writable bytes at a0 *)
Definition R_B (n : Z) : YP09.region := YP09.mkRegion (Some 10%nat) 0 n 0 n [].
(* the va_list's 8-byte slots at a3 *)
Definition R_VA (vs : list Z) : YP09.region :=
  YP09.mkRegion (Some 13%nat) 0 (8 * Z.of_nat (length vs)) 0 0
    (map (fun i => YP09.mkChunk (8 * Z.of_nat i) (CVal 8 (SLit (nth i vs 0)))) (seq 0 (length vs))).

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. The seed.                                                                                                      *)
(* internal_memset's alignment word at 0x65260 for AppendNumber's digit array (sp' + 8, sp' = sp - 0x80 - 0x150) *)
Definition MS_AL : sv := SAlu ALU_AND (SAlu ALU_OR (SLit 240) (SOff 2 (-456))) (SLit 15).
Definition VFACTS : facts := mkFacts
  [ (2%nat, mkAF (kHighMemBeg + VSN_STK) kHighMemEnd 4);
    (10%nat, mkAF kHighMemBeg kHighMemEnd 0); (13%nat, mkAF kHighMemBeg kHighMemEnd 0) ] [] [(MS_AL, SLit 8)].
Definition VREGS (fmt : Z) : list sv := sr_set (sr_set sr_atoms 11%bv (SLit 400)) 12%bv (SLit fmt).
Definition vmem (n : Z) (vs : list Z) (rom : smem) : smem := R_S :: R_B n :: R_VA vs :: rom.
Definition vseed (fmt n : Z) (vs : list Z) (rom : smem) : sstate := mkSS A_VSNPRINTF (VREGS fmt) (vmem n vs rom) None VFACTS.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. The checks.                                                                                                    *)
Definition A_VSN_RET : Z := 0x684a4.
Definition zdisjb (a b : Z * Z) : bool := (snd a <=? fst b) || (snd b <=? fst a).
Fixpoint zpw_disjb (l : list (Z * Z)) : bool :=
  match l with [] => true | a :: l' => forallb (zdisjb a) l' && zpw_disjb l' end.
(* the read-only regions: image-based, inside the image, no writable window, pairwise apart *)
Definition rom_ok (rom : smem) : bool :=
  forallb (fun r => YP09.obase_eqb (YP09.r_base r) None && (TFIB_IMG_LO <=? YP09.r_lo r) &&
    (YP09.r_hi r <=? TFIB_IMG_END) && (YP09.r_whi r <=? YP09.r_wlo r)) rom &&
  zpw_disjb (map (fun r => (YP09.r_lo r, YP09.r_hi r)) rom).
Definition chunk_has (cs : list YP09.chunk) (off v : Z) : bool :=
  existsb (fun c => (YP09.c_off c =? off) &&
    match YP09.c_val c with CVal w (SLit x) => (w =? 1)%N && (x =? v) && (0 <=? v) && (v <? 256) | _ => false end) cs.
Fixpoint wins_eqb (l l' : list (option nat * Z * Z)) : bool :=
  match l, l' with
  | [], [] => true
  | t :: l1, u :: l1' => win_eqb t u && wins_eqb l1 l1'
  | _, _ => false
  end.
Definition vfin_ok (seed ssF : sstate) (out : list Z) : bool :=
  (ss_pc ssF =? A_VSN_RET) && match ss_resv ssF with None => true | Some _ => false end &&
  forallb (fun r : reg => sv_eqb (sr_get (ss_regs ssF) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED &&
  sv_eqb (sr_get (ss_regs ssF) 1%bv) (SOff 1 0) &&
  sv_eqb (sr_get (ss_regs ssF) 10%bv) (SLit (Z.of_nat (length out))) &&
  wins_eqb (windows (ss_mem ssF)) (windows (ss_mem seed)) &&
  match nth_error (ss_mem ssF) 1 with
  | Some r => YP09.obase_eqb (YP09.r_base r) (Some 10%nat) &&
      forallb (fun i => chunk_has (YP09.r_chunks r) (Z.of_nat i) (nth i (out ++ [0]) 0)) (seq 0 (S (length out)))
  | None => false
  end.
Definition vrun (seed : sstate) : sstate * run_status := sym_run_toN_sh tfibsegs tfibtbl_rtD YP03.FUEL A_VSN_RET seed.
Definition vchk (fmt : Z) (out vs : list Z) (rom : smem) : bool :=
  let seed := vseed fmt (Z.of_nat (length out) + 1) vs rom in
  regions_wf (ss_mem seed) && rom_ok rom &&
  match vrun seed with
  | (ssF, RS_running) => vfin_ok seed ssF out
  | _ => false
  end.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The runs, checked.                                                                                             *)
Lemma vchk1 : vchk FMT_OOM1 render1 [A_TOOLNAME] ROM1 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma vchk2_all :
  forallb (fun c => vchk FMT_OOM2 (render2 c (class_size c)) [REGION_MB; c; class_size c] ROM2) (map Z.of_nat (seq 1 31))
  = true.
Proof. vm_compute. reflexivity. Qed.
Lemma vchk2 : forall c, 1 <= c <= 31 -> vchk FMT_OOM2 (render2 c (class_size c)) [REGION_MB; c; class_size c] ROM2 = true.
Proof.
intros c Hc. pose proof vchk2_all as A. rewrite forallb_forall in A.
apply A. apply in_map_iff. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
(* the read-only bytes are bytes; the arguments are words *)
Lemma rom_bytes_range :
  forallb (fun v => (0 <=? v) && (v <? 256)) (FMT1_BYTES ++ FMT2_BYTES ++ TOOL_BYTES) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ret_word : clookup tfibtbl_rtD A_VSN_RET = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
