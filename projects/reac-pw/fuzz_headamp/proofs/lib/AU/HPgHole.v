(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCbq.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: off_img's image bounds cite fuzz_knock's image (YImgTop.IMG_LO, YImgTop.IMG_TOP = 0x5f3000, both knock ASan builds) in place of cgif's 0x10000 and 0x5fb000. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YCbq.v at origin/ossv/recipes 6ebe35ba632 (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_headamp. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/Reusable/YCbq.v, with its module paths and module names changed; 986 of its 1333 lines of code are new or changed and 2813 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: the journal lemmas rdp_aj_write_U, rdp_ecall_preU_k and rdp_aj_roU of
   proofs/omx-clap-core/fuzz_manifest/lib/A/FMW_rd_pre_k.v (lines 494-584 at origin/ossv/recipes 09c6822d886), the
   frame law ARU_frame of lib/A/FMupoison.v (lines 166-187) and the post rt_post_roU of lib/A/FMH_Rt.v (lines 97-104)
   of the same tree, restated for a hole in the shadow of a real-stack frame in place of fuzz_manifest's user-poisoned
   heap granules; the chunk runners SRr_chain_tok_AJ / SRr_run_tok_AJ / SRr_run_to_tok_AJ / SRr_chain_AJ /
   SRr_run_AJ / SRr_run_to_AJ of lib/Reusable/YCbq.v (lines 2408-2546) restated with the journal over the unpoisoned
   memory. The rest is new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_headamp/lib/A/HPgHole.v, with its module paths, module names and addresses changed; 27 of its 55 lines of code are new or changed and 1305 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; addresses measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are byte-equal to the pin's except .note.gnu.build-id):
   THE FRAME HOLE of reac_headamp_prop_parse_result at image B's pcs. Proves no function (kind: segment lemma).

   Every definition and lemma of the hole is image-independent and lives in lib/A/HPgHole.v (hU, hstack_ok, hpat, ARH,
   hjournal, ecall_preH; the entry / exit / pattern steps; the AJH chunk runners and aj_run_tokH; the three wrapper
   contracts in hole form; hj_strncmp_at, hj_strcmp_at, hj_strtol_at; hd_dot_ok, hd_site_pre, hd_hole_sat_A). Image B's
   parse has the same frame as image A's: `addi sp,sp,-0x100` (B 0x849ac), `andi sp,sp,-0x20` (B 0x849ec), the frame
   object at sp' + 0x40 (B 0x84a0c), the end pointer at sp' + 0x60 (B 0x84dd8), the same eight shadow bytes and
   patterns; only the pcs differ:
     open   B 0x84a40 .. 0x84a60 (PAT_KEY); strncmp call B 0x84d94 (jal 0x41c24, PAT_KEY);
     dot in B 0x84dc8 (PAT_DOT); strtol call B 0x84ddc (jal 0x41ca8, PAT_DOT); strcmp calls B 0x84e34, 0x84e48, 0x84e5c
     (jal 0x41c20, PAT_DOT); dot out B 0x84ec0, 0x84f08 (PAT_KEY); close B 0x84b44 .. 0x84b60; ret B 0x84ba8.
   The trampolines are the ones HPgCSpec's header names for image B. Every (pc, instruction word) below is checked
   against image B's loaded segments (lib/AU/Img0U.v) by computation. hd_hole_sat_A of lib/A/HPgHole.v is stated for
   every image; hd_hole_sat_B below is its use at image B's segments. *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YM05 YI16 YG0f YG0n YG0d YO0f.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgCSpec HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require HPgSat.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Img0U.
Import ListNotations.
Local Open Scope Z_scope.

Definition B_PARSE_RESULT : Z := 0x849ac.
Definition B_TRAMP_STRNCMP : Z := 0x41c24.
Definition B_TRAMP_STRTOL : Z := 0x41ca8.
Definition B_TRAMP_STRCMP : Z := 0x41c20.
(* The five calls inside the hole: strncmp (pattern PAT_KEY), strtol and the three strcmp (pattern PAT_DOT). *)
Definition B_CALL_STRNCMP : Z := 0x84d94.
Definition B_CALL_STRTOL : Z := 0x84ddc.
Definition B_CALLS_STRCMP : list Z := [0x84e34; 0x84e48; 0x84e5c].
(* The open's eight stores, the dot stores, the close's eight stores and the parse's one return. *)
Definition B_OPEN : list Z := [0x84a40; 0x84a44; 0x84a48; 0x84a4c; 0x84a54; 0x84a58; 0x84a5c; 0x84a60].
Definition B_DOT_IN : Z := 0x84dc8.
Definition B_DOT_OUT : list Z := [0x84ec0; 0x84f08].
Definition B_CLOSE : list Z := [0x84b44; 0x84b48; 0x84b4c; 0x84b50; 0x84b54; 0x84b58; 0x84b5c; 0x84b60].
Definition B_RET : Z := 0x84ba8.

Definition headamp_B_hole_insns : list (Z * Z) :=
  [(0x849ac, 0xf0010113) (* addi sp,sp,-256 *); (0x849ec, 0xfe017113) (* andi sp,sp,-32 *);
   (0x84a0c, 0x04010793) (* addi a5,sp,64: fr *); (0x84a38, 0x0037d793) (* srli a5,a5,3 *);
   (0x84a3c, 0x01b78d33) (* add s10,a5,s11: shadow_addr fr *);
   (0x84a40, 0x00bd0223); (0x84a44, 0x010d02a3); (0x84a48, 0x010d0323); (0x84a4c, 0x010d03a3);
   (0x84a54, 0x00bd0023); (0x84a58, 0x00bd00a3); (0x84a5c, 0x00bd0123); (0x84a60, 0x00bd01a3) (* open: f8 f3 f3 f3, f1 x4 *);
   (0x84d94, 0xe91bc0ef) (* jal 0x41c24 *); (0x84dc8, 0x000d0223) (* sb zero,4(s10) *);
   (0x84dcc, 0x06013023) (* sd zero,96(sp) *); (0x84dd8, 0x06010593) (* addi a1,sp,96: e = fr + 32 *);
   (0x84ddc, 0xecdbc0ef) (* jal 0x41ca8 *); (0x84e34, 0xdedbc0ef); (0x84e48, 0xdd9bc0ef); (0x84e5c, 0xdc5bc0ef) (* jal 0x41c20 *);
   (0x84ec0, 0x00ad0223); (0x84f08, 0x00ad0223) (* sb a0,4(s10), a0 = -8 *);
   (0x84b44, 0x000d0223); (0x84b48, 0x000d02a3); (0x84b4c, 0x000d0323); (0x84b50, 0x000d03a3);
   (0x84b54, 0x000d0023); (0x84b58, 0x000d00a3); (0x84b5c, 0x000d0123); (0x84b60, 0x000d01a3) (* close *);
   (0x84ba8, 0x00008067) (* ret *)].
Lemma headamp_B_hole_insns_chk : HPgSat.entries_chk Img0U.rsegs headamp_B_hole_insns = true.
Proof. vm_compute. reflexivity. Qed.
Lemma headamp_B_hole_insns_ok : forall a w, In (a, w) headamp_B_hole_insns ->
  forall k, (k < 4)%nat -> seg_rom Img0U.rsegs (Z_to_bv 64 (a + Z.of_nat k)) = Some (Z_to_bv 8 (le_byte w 4 k)).
Proof.
intros a w Hin k Hk. refine (HPgSat.img_val_chk_ok Img0U.rsegs a 4 w _ k Hk).
pose proof headamp_B_hole_insns_chk as E. unfold HPgSat.entries_chk in E. rewrite List.forallb_forall in E.
exact (E (a, w) Hin).
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis segs_low : forall a, in_img Img0U.rsegs a -> 0 <= a < kLowMemEnd.

(* ARH at image B's parse entry: from the caller's hd_pre at B 0x849ac, the memory after the open's stores
   (B 0x84a40 .. 0x84a60, PAT_KEY) satisfies the cut-state form. *)
Lemma hd_hole_sat_B : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc,
hd_pre Img0U.rsegs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
hjournal Img0U.rsegs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
  (hset memc (shadow_addr (hd_fr (Z.land (spZ regs - 0x100) (-32)))) PAT_KEY) mdc k
  (hd_fr (Z.land (spZ regs - 0x100) (-32))) PAT_KEY.
Proof. exact (hd_hole_sat_A Img0U.rsegs B segs_low). Qed.
End b.

Print Assumptions headamp_B_hole_insns_ok.
Print Assumptions hd_hole_sat_B.
