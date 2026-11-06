(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 366 of its 406 lines of code are new or changed and 664 lines of the source are left out. *)
(* fuzz_preset, image B' (#102 pins: asan-ubsan sha256 d663f82d7f488d30, unstripped twin c90d4fa54d43160b): the walk of
   padded (new fuzz_preset.c:509-521, git blob fa3e8966; B' 0x830a8, 148 bytes, 37 instructions; slot B_prog_slot
   AS_padded = 1655 of the whole-program listing). B' only: image A' inlines padded into check_no_overread.
   rule 24: proves function padded (reuse search: the internal file REWALK-102-PLAN.md section D3: none exists).
   INPUTS (by path; the commit that adds this file names its base):
     base: the fuzz_preset tree preset-tree-at-2026-10-29T13-46-39Z.tsv (sha256 73925d76b3d8; internal record) (the engine set of preset-tree-at-2026-10-29T12-55-44Z.tsv (sha256 7967f42d1cd6; internal record))
     + the kit by path (lib/A/PRH_Base.v (sha256 427856c3ea51; internal record),
     PRH_FnAlloc.v f668aebf57c4, PRH_FnCheck.v 6f6bc83d7420, PRH_FnReader.v 66e11f202508, PRH_Reader.v 91d2dbd40054,
     lib/B/PRH_ImgB.v (sha256 4f84cb33fb52; internal record)) + the listings
     (lib/B/Listing_prog.v 8bcc2c9e7809, lib/B/PAImg_prog.v 4392ab2c09ba, lib/Reusable/YPsym.v b6f5a85d234d)
     + the three proof.yaml of facts preset-tree-at-2026-10-29T12-03-17Z.tsv (sha256 43b6000a63b5; internal record)
     + lib/Reusable/YImgTop.v (sha256 66e2a85770a0; internal record) (IMG_TOP_B = 0x601000).
  THE TEXT: the kit's tpadded_specX (lib/A/PRH_FnCheck.v blob de94d3f3a7f1: the kit cut's text, blob c40cf3fdcd2a, plus
   the hull premise hull_budget S [HMal (size + 16)] and the post's hull_used conjunct, lib/Spec/PresetHullBudget.v;
   before it, blob 9ecd8eb167c6, which adopted the internal file REWALK-102-PLAN.md D4's outcome list). It does NOT depend on the kit's
   Batch-2 fuzz_malloc arms:
   padded's allocation is `noted (malloc (size + FUZZ_PAD))` (new:512), and B' 0x830d0 `jal 0x53824` is
   Listing_prog.v :1680 `PCall AS___wrap_malloc` (B_prog_sigma AS___wrap_malloc = 0x53824, PAImg_prog.v :79), the RAW
   allocator wrapper (the one fuzz_malloc itself calls, alloc.c:85), so alloc.c's statics (g_live, g_peak, g_count,
   g_fail_at, g_ran_out, g_most) are untouched on both arms; the only flag write is g_own_ran_out := 1 (0x83114).
   THE ARMS (D4): REFUSED, the wrapper's NULL: g_own_ran_out := 1, return 0, the blocks unchanged, errno 12; OK, the
   wrapper's block b: if size <> 0 __asan_memcpy (b, data, size); __asan_memset (b + size, fill, 16); return b, the
   block (b, size + 16) appended to the allocator's blocks (a RUNTIME block: not in Lam, its base not in Hp), its bytes
   x ++ 16 copies of fill mod 256, writable, addressable, its hull visible. The UBSan check of b + size (0x830f0
   `not`, 0x830f4 `bltu` -> 0x83138 `unimp`) is refuted from b + size + 16 <= alloc_ceiling.
   THE SEGMENTS (the internal file REWALK-102-PLAN.md D5): S1 prologue + the malloc wrapper (pd_s1); S2 the NULL test (pd_s2); S3 the
   size test + __asan_memcpy (pd_s3); S4 the UBSan check + __asan_memset (pd_s4); S5 the NULL arm's byte store
   (pd_s5); S6 the epilogue (pd_s6). Each is a lemma from a cut to the post; they compose by citation.
   Numerals: 48 (LENGTH: the frame, `addi sp, sp, -48`); 16 (LENGTH: FUZZ_PAD, fuzz.h); 8 / 1 (LENGTH: word, the
   one-byte g_own_ran_out cell); offsets 44 / 52 / 72 / 96 / 100 / 112 (DERIVED: 4 * slot inside padded, read off
   the internal file padded.asan-ubsan.new.s and Listing_prog.v :1670-1706); atom indices (DERIVED: the engine's numbering);
   2 ^ 44 / 2 ^ 46 / 2 ^ 47 (DERIVED: shadow and stack bounds); 256 (WORD: byte modulus). No ADDRESS literal:
   addresses are pa_val / pa_sigma of the listing class, PrhImg fields of PRH_ImgB.v, or computed from them. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcallx YGcallcf YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG01cf YG00cf YG0ncf YG0dcf YG0sshcf YGcfRoomPre YG0lawscf YGcfApath.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcfRoomKeep YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetLiveBounds PresetRoomPos PresetRun
  PresetReqAt PresetRoomPosKeep PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnAlloc PRH_FnReader
  PRH_FnCheck CfParamsPreset.
(* lib/A/CfRoomLivePreset.v is NOT Required: it pulls lib/Spec/PresetLiveSec.v and PresetGate.v, whose closure reaches
   lib/Prog/SlotSizes.v -> PjWriteHyp -> lib/Contract -> lib/ZImage.v, which did not build on the #102 facts
   preset-tree-at-2026-10-29T12-03-17Z.tsv (sha256 43b6000a63b5; internal record) (ZImage.v:38 pins the PLAIN image
   entry; measured by the tx_put A' walk, log of a build of those facts). At the kit cut preset-tree-at-2026-10-30T04-57-22Z.tsv
   (sha256 652fe98064b9; internal record) ZImage.v builds again (S1 Requires lib/A/PRH_Refute.v, whose closure holds
   it), but the text names the room counts in the leaf's words, so the live-set bounds the malloc keep needs stay ONE
   named entry argument in the kit's spelling over the LEAF lib/Spec/PresetLiveBounds.v (it Requires only PresetReqAt). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Listing_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S1Ledger.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

(* THE TEXT IS the tree's tpadded_specX (lib/A/PRH_FnCheck.v:1639-1697, its code as in blob de94d3f3a7f1), the conclusion of
   pd_s1 VERBATIM (Padded102B_S1.v:261-262). Against the text this walk proved before (blob 9ecd8eb167c6) it has FOUR changes,
   (1) and (4) already in the kit cut's text (blob c40cf3fdcd2a): (1) no run-word list DW (no DW parameter, none in
   prh_univ_closure: DW-SPLIT superseded); (2) the premise hull_budget (PRH_FnCheck.v:1648); and TWO new post conjuncts, (3)
   hull_used (:1658) and (4) the OUTCOME clause (:1660-1668, pd_outc below: at a consumer position whose next event is the copy's
   raw malloc, it was granted). The cuts below are stated over the kit's words; pd_post is the kit's post by conversion. *)

(* ======== image B': the offsets inside padded, and the seats ======== *)
(* padded's slot in the listing: DERIVED, = B_prog_slot AS_padded (PAImg_prog.v 4392ab2c09ba :426, B_entry_padded:
   sigma 0x830a8, slot 1655); the image record's pdi_entry ties it to pa_sigma *)
Definition PD_SLOT : nat := 1655%nat.
Definition PD_OFF : Z := 4 * Z.of_nat PD_SLOT.
(* the cuts: DERIVED byte offsets inside padded (4 * slot), read off the internal file padded.asan-ubsan.new.s *)
Definition PD_RETM : Z := 44.   (* the malloc wrapper's return site, B' 0x830d4 (`mv s0, a0`) *)
Definition PD_TEST : Z := 48.   (* S2's cut: the NULL test, 0x830d8 (`beqz a0`), s0 = a0 = b *)
Definition PD_OK : Z := 52.     (* b <> 0: the size test, 0x830dc (`beqz s2`) *)
Definition PD_SET : Z := 72.    (* both OK arms meet: the UBSan check, 0x830f0 (`not a0, s0`); = __asan_memcpy's
                                   return site *)
Definition PD_RETS : Z := 96.   (* __asan_memset's return site, 0x83108 (`j 0x83118`) *)
Definition PD_NULL : Z := 100.  (* b = 0: the g_own_ran_out store, 0x8310c (`auipc a0`) *)
Definition PD_EPI : Z := 112.   (* the epilogue, 0x83118 (`mv a0, s0`) *)
Definition PD_TRAP : Z := 144.  (* the UBSan trap, 0x83138 (`unimp`), refuted by pd_ovf_false *)
(* the registers padded uses (RISC-V numbers): s0 = x8 = b, s1 = x9 = fill, s2 = x18 = size, s3 = x19 = data *)
Definition PD_Bx : sv := SLit SHADOW_OFF.
Definition PD_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* the 48-byte frame, written once by the prologue and read once by the epilogue: the write window is empty from the
   malloc call on, and the five saved words are the extra atoms 32 (ra), 33 (s0), 34 (s1), 35 (s2), 36 (s3) *)
Definition pd_frame : YP09.region :=
  YP09.mkRegion (Some 2%nat) 0 48 0 0
    [YP09.mkChunk 8 (CVal 8 (SOff 36 0)); YP09.mkChunk 16 (CVal 8 (SOff 35 0));
     YP09.mkChunk 24 (CVal 8 (SOff 34 0)); YP09.mkChunk 32 (CVal 8 (SOff 33 0));
     YP09.mkChunk 40 (CVal 8 (SOff 32 0))].
(* the one-byte g_own_ran_out cell the NULL arm stores to (A_OBJ 13 of the listing; its hi/lo pair is the
   B_alias_hints row (SOff (A_HI 39) (-908), SOff (A_OBJ 13) 0), Listing_prog.v 8bcc2c9e7809 :7756) *)
Definition pd_own_region : YP09.region := YP09.mkRegion (Some (A_OBJ 13)) 0 1 0 1 [].
Definition pd_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46 - 48) (2 ^ 47) 4); (8%nat, mkAF 0 CEIL_MAX 0); (18%nat, mkAF 0 (2 ^ 40) 0);
           (A_OBJ 13, mkAF IMG_LO_B IMG_TOP_B 0)]
    [] B_alias_hints.
(* THE SEAT'S pc IS THE LISTING OFFSET (YC1fP.v pa_entry_st_ok_full builds the machine pc as BASE + ss_pc), so a cut
   at the byte offset `off` inside padded seats at pd_koff off; its machine pc is pd_pc off. *)
Definition pd_koff (off : Z) : Z := PD_OFF + off.
(* the seat at a cut: the frame alone; and, on the NULL arm, the g_own_ran_out cell beside it *)
Definition pd_ss (k : Z) : sstate := mkSS k sr_atoms [pd_frame] None pd_facts.
Definition pd_ssn (k : Z) : sstate := mkSS k sr_atoms [pd_own_region; pd_frame] None pd_facts.
(* the ENTRY seat (offset 0): the frame is not written yet, so the own frame is one stack region with the write
   window [-48, 0); a1 = size is the only argument the engine needs bounded (the UBSan check reads it at atom 18
   after `mv s2, a1`) *)
Definition pd_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (11%nat, mkAF 0 (2 ^ 40) 0)] [] B_alias_hints.
Definition pd_ss0 : sstate := mkSS PD_OFF sr_atoms [stack_region 48] None pd_facts0.

(* ---- the UBSan check's arithmetic, COPIED body for body from lib/Reusable/YE2y.v (lxor_ones :419, U_not :430,
   br_ovf_false :449) and NOT Required: YE2y.v pulls YImgCellsB.v and eight more engine files this walk does not
   use. Same statements, same proofs, renamed pd_*. ---- *)
Lemma pd_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
intros a n Hn Ha.
assert (Hlog : Z.log2 a < n).
{ destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|]. apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
rewrite <- (Z.ldiff_ones_l_low a n) by lia.
rewrite Z.ldiff_land.
assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm. rewrite E.
rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma pd_U_not : forall E v, U E (SAlu ALU_XOR v (SLit (-1))) = 2 ^ 64 - 1 - U E v.
Proof.
intros E v. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit. change (zcanon (-1)) with (Z.ones 64).
pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite pd_lxor_ones by lia.
change (Z.ones 64) with (2 ^ 64 - 1). apply zcanon_id. unfold M64. lia.
Qed.
(* the UBSan trap at PD_TRAP is not taken: b <= alloc_ceiling < 2 ^ 47 and size < 2 ^ 32, so ~ b >= size *)
Lemma pd_ovf_false : forall E (pa pn : nat) d n, ew E pa = Z_to_bv 64 d -> ew E pn = Z_to_bv 64 n ->
  0 <= d <= 2 ^ 47 -> 0 <= n < 2 ^ 32 ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff pa 0) (SLit (-1)))) (sv_denot E (SOff pn 0)) = false.
Proof.
intros E pa pn d n Hd Hn Rd Rn. rewrite branch_ltu_U, pd_U_not, (U_atom E pa d Hd), (U_atom E pn n Hn) by lia.
apply Z.ltb_ge. lia.
Qed.

(* ======== THE FROZEN SEGMENT INTERFACE (owner request 14:33Z): the cuts, and one Prop per segment ========
   Each pd_sN_stmt is the segment's whole obligation: from its cut, the function's post. A segment's owner proves
   `Lemma pd_sN : pd_sN_stmt.` and nothing else of this file changes. The seats are NOT shared: a segment builds its
   own st_ok_pi at its cut from pd_base (the frame region pd_frame over the atoms 32..36, the facts pd_facts, and -
   on the NULL arm only - pd_own_region), by YC1fP.v's pa_entry_st_ok_full, as FuzzStrdupB.v:288 sd_entry does. *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Existing Instance prh_img_B.
#[local] Notation CP := CfParams_preset.
#[local] Notation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Notation VAL := (@pa_val _ B_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ B_prog_listing PA).
#[local] Notation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
#[local] Notation PST := (@prh_pst prh_img_B).
Variable B : asyms.
(* the allocator relation of the S1 theorems: ARcf with the error-buffer extents placed (YGcallcf.v) *)
#[local] Notation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
#[local] Notation AJ := (ajournal_x (SK := SK) SEGS B PST ARc).
(* ---- the two RUNTIME ROWS this walk crosses, as named Section hypotheses (the lead's rule, 15:2xZ, on
   the S3 row owner's finding; FuzzStrdupB.v:272-277 is the form): the rows have their own owner, the walk cites them. They are
   the m-forms, so each carries its memnorm keep (YGcallMxmn.v:162 aintrin_realizes_xm) and S3 / S4 can thread
   pd_mn across the call. ---- *)
Hypothesis AI_cpy : aintrin_realizes_xm SEGS B ARc OCpy (SIGMA AS___asan_memcpy).
Hypothesis AI_set : aintrin_realizes_xm SEGS B ARc OSet (SIGMA AS___asan_memset).

(* ---- the image facts the walk reads of PA, each proved at the instance by computation (PAImg_prog.v 4392ab2c09ba:
   B_prog_val, B_entry_padded :426; the object pin 13 = g_own_ran_out of PRH_ImgB.v 3216eca68342; the hi atom 39 of
   the `auipc a0, 0x55b` / `sb a1, -908(a0)` pair at the slots PD_NULL / PD_NULL + 8) ---- *)
Record pd_img : Prop := {
  pdi_base : BASE = B_prog_base;
  pdi_entry : SIGMA AS_padded = BASE + PD_OFF;
  pdi_own : VAL (A_OBJ 13) = @pi_g_own_ran_out prh_img_B;
  pdi_own_img : IMG_LO_B <= VAL (A_OBJ 13) /\ VAL (A_OBJ 13) + 1 <= IMG_TOP_B;
  pdi_alias : forall E, img_env VAL A_LIM E -> alias_ok E B_alias_hints;
  (* the program statics are writable data, not read-only bytes (Cno102B_Base.v cnbi_pst_rw) *)
  pdi_pst_rw : forall a, Exists (in_zr a) PST -> ~ in_roP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) a;
  (* a store to a program static is a store to an image byte the runtime does not own (S1ImgB.v pst_in_img_B); the
     runner's PST_ok (YCbqG.v c3b5d0111037 :259) is exactly this pair *)
  pdi_pst_ok : forall a, Exists (in_zr a) PST -> in_img SEGS a;
  pdi_pst_owned : forall a, Exists (in_zr a) PST -> ~ Exists (in_zr a) (as_owned_static B);
  (* AND PST IS APART FROM errno (the row owner's finding on PDB-S5, with its counter-model as_errno B =
     g_own_ran_out - 1: without this the NULL arm's `sb 1` could be read as a write of errno, and the errno 12 the
     wrapper left would not survive to the post). TxPut102B_Base.v 418e51c4acc4 states the pair this way. *)
  pdi_pst_errno : forall a, Exists (in_zr a) PST -> ~ (as_errno B <= a < as_errno B + 4);
  (* THE TWO FACTS OF THE UNIT'S BINDING OF B the walk reads (narrowed 16:5xZ from the whole PALib B, owner ruling
     16:45Z): PALib's other fields (as_got_shadow / as_shadow_cell / as_got_uar) are read by no padded segment, and the
     B' TfibSyms (YF0m f82202ebccdf) gives none of them, while it gives both of these by computation (ts_code; ts_errno
     and ts_universe_drv). pdi_malloc is S1's wrapper entry (YC1fP.v:337 pal_malloc's statement); pdi_env is api_env
     (YCbq.v:809, YC1fP.v:335 pal_env's statement): errno's four bytes do not wrap (the row owner's gap on PDB-S5), they
     are image bytes, and the wrapper's return traces are in the universe (aj_malloc_x_m's HENV). *)
  pdi_malloc : SIGMA AS___wrap_malloc = pc_wrap_malloc (as_code B);
  pdi_env : api_env SEGS B;
  (* the program statics are WRITABLE in any memory (a finding on pd_seat_null_stmt, 15:4xZ): the NULL
     seat's g_own_ran_out region has the write window [0, 1), and over the abstract PA nothing else says that byte is
     writable (pdi_pst_ok / pdi_pst_rw give the range and not-read-only, not the segment's bytes). Appended LAST;
     discharged at the instance by S1ImgB.v:27 pst_writable_B. *)
  pdi_pst_wr : forall (m : word -> option byte) a, Exists (in_zr a) PST -> writable_at SEGS m a
}.

(* ---- THE ENTRY DATA: every variable the text binds ---- *)
Record pd_in : Type := mkPdIn {
  din_ly : alayout; din_S : astate; din_Hp : list Z; din_W : world SEGS;
  din_regs : bvmap 5 word; din_mem : word -> option byte; din_md : Model; din_ch : list (Z * Z * Z);
  din_data : Z; din_fill : Z; din_x : list Z;
  din_Lam : list (Z * Z); din_peak : Z; din_cnt : Z; din_fail : Z; din_ran : Z; din_most : Z; din_own : Z
}.
Definition pd_sp0 (D : pd_in) : Z := spZ (din_regs D).
Definition pd_size (D : pd_in) : Z := Z.of_nat (length (din_x D)).
Definition pd_pc (off : Z) : Z := BASE + PD_OFF + off.

(* ---- what every cut carries ---- *)
(* the journal from the entry; padded takes no fake frame, so `own` is empty *)
Definition pd_J (D : pd_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (mem : word -> option byte) (md : Model) (k : Z) : Prop :=
  AJ STK_padded (pd_sp0 D) [] (din_ly D) (din_S D) (din_Hp D) (din_W D) (din_mem D) (din_md D) []
    ly S Hp W mem md k.
(* the five saved words at the body sp (entry sp - 48): ra 40, s0 32, s1 24, s2 16, s3 8 *)
Definition pd_saved (D : pd_in) (W : world SEGS) (mem : word -> option byte) : Prop :=
  Forall (fun p : Z * bv 5 =>
            rdword (aview SEGS (w_H W) mem) (pd_sp0 D - 48 + fst p) = Some (bv_unsigned (getr (din_regs D) (snd p))))
    [(40, 1%bv); (32, 8%bv); (24, 9%bv); (16, 18%bv); (8, 19%bv)].
(* the registers every cut from PD_TEST on holds: sp = the body sp, s0 = b, s1 = fill, s2 = size, s3 = data, and
   gp / tp and x20..x27 as at the entry. x20..x27 ARE LOAD-BEARING (the row owner's finding on PDB-S6, 15:0xZ): the
   post's aregs_preserved is over acallee_saved = {2, 3, 4, 8, 9} u [18, 27] (YG0d.v:20-21), padded saves and
   restores only x1 / x8 / x9 / x18 / x19, and the eight it never touches must be carried by the cut. *)
Definition pd_regsat (D : pd_in) (regs : bvmap 5 word) (b : Z) : Prop :=
  getr regs 2 = w64 (pd_sp0 D - 48) /\ getr regs 8 = w64 b /\ getr regs 9 = w64 (din_fill D) /\
  getr regs 18 = w64 (pd_size D) /\ getr regs 19 = w64 (din_data D) /\
  getr regs 3 = getr (din_regs D) 3 /\ getr regs 4 = getr (din_regs D) 4 /\
  (forall r, 20 <= r <= 27 -> getr regs (Z_to_bv 5 r) = getr (din_regs D) (Z_to_bv 5 r)).
(* the memory invariant the post's keep needs (YSRrMemnorm.v srr_inv_laws_imp at the entry memory) *)
Definition pd_mn (D : pd_in) (m : word -> option byte) : Prop :=
  YAkMemnorm.memnorm SEGS (din_mem D) -> YAkMemnorm.memnorm SEGS m.
(* `ow` is the g_own_ran_out cell AT THIS CUT: the kit's prh_ledger carries it (and g_most) since
   lib/A/PRH_Base.v 3004a98fe2d9, so no cut states prh_own beside the ledger any more. Every cut before the NULL
   arm's store passes din_own D; the epilogue's cut passes the arm's own'. *)
Definition pd_base (D : pd_in) (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (k : Z) (b : Z) (ow : Z) : Prop :=
  (* paj_ret_at jumps through the entry ra, so every cut carries its ret_ok (YK0s.v:193; afn_pre_x has it at the
     entry and S1 hands it on) - the row owner's second finding on PDB-S6 *)
  YK0s.ret_ok (getr (din_regs D) 1) /\
  pd_J D ly S Hp W mem md k /\ pd_saved D W mem /\ pd_regsat D regs b /\
  (* the runtime registers every call rule asks of its call state (ecall_pre_x, FCiface.v:48; aj_intrin_at_xm's
     premises, YGcallMxmn.v:274): pd_regsat keeps x3 / x4 from the entry, and THESE tie the entry's to the image's
     - the row owner's finding on PDB-S4, which blocks PDB-S3 too. S1 pays them from afn_pre_x. *)
  getr (din_regs D) 3 = w64 (as_gp B) /\ getr (din_regs D) 4 = w64 (as_tp B) /\
  arodata_okP SEGS (@pa_relro_lo _ _ PA) (@pa_relro_hi _ _ PA) B (aview SEGS (w_H W) mem) /\
  pd_mn D mem /\ Hp = din_Hp D /\
  prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly S Hp W mem (din_Lam D) (din_peak D) (din_cnt D)
    (din_fail D) (din_ran D) (din_most D) ow /\
  room_live_cf S /\
  (* THE MEMCPY SOURCE, at THIS state, not merely its bytes (my own audit, 15:1xZ): aj_intrin_at_xm's OCpy arm asks
     src_ok, amem_range, range_addressable and the hull of [data, data + size) at the CALL state, and bare bytes_at
     gives none of them. S1 moves the entry's src_rd across the wrapper call once (Padded102B_Home.v pdh_src_rd_at
     over pdh_home_place / pdh_home_shadow and the home premise below); S2..S4 then only carry it. *)
  src_rd W mem (din_data D) (din_x D) /\
  (* at the ENTRY state (a Theorem Labs finding on PDB-S3): the apart-from-b derivation compares data's home with the
     block the wrapper appended, so it needs the block list BEFORE the call; S1 takes it straight from the
     premise and every cut carries it unchanged *)
  (0 < pd_size D ->
     PRH_FnReader.prhReader_home B (din_ly D) (din_S D) (din_Hp D) (din_Lam D) (din_data D) (pd_size D)) /\
  (* The text's own bound on the input (PRH_FnCheck.v 9ecd8eb167c6 :840), carried so that the seat's atom fact on
     x18 = size holds at every cut *)
  pd_size D <= 3 * 2 ^ 20 /\
  (* THE HULL USE so far (the text's post conjunct, PresetHullBudget.v hull_used): the wrapper's one call at the entry
     state is the only allocator step, so S1 pays it from the call's path (hull_used_of_call) and S2..S6 carry it *)
  PresetHullBudget.hull_used (din_S D) S [PresetReqAt.HMal (pd_size D + 16)].
(* the OK arm's block facts at the cuts, the kit's P1 (PRH_FnCheck.v c40cf3fdcd2a :995-1007) MINUS the bytes the copy
   and the pad write: the wrapper's RAW block, fresh, in neither Lam nor Hp, its bytes writable and its shadow visible,
   and the run position's advance *)
Definition pd_okblk (D : pd_in) (ly : alayout) (S : astate) (W : world SEGS)
  (mem : word -> option byte) (res own' : Z) : Prop :=
  (* the ceiling conjunct is the P1 of PRH_FnCheck.v (sha256 f4fcb5e7465e; internal record), which ADOPTED this walk's fix: `+ 8` dropped *)
  res <> 0 /\ own' = din_own D /\ 4096 <= res /\ res + pd_size D + 16 <= YM05.alloc_ceiling /\
  ~ In res (map fst (ablocks B (din_ly D) (din_S D))) /\
  Permutation (ablocks B ly S) ((res, pd_size D + 16) :: ablocks B (din_ly D) (din_S D)) /\
  (forall a k, In (a, k) (din_Lam D) -> a - @cf_head CP <> res) /\
  (forall a, res <= a < res + pd_size D + 16 -> writable_at SEGS (mrestrict (w_H W) mem) a) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF res (pd_size D + 16) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) res (pd_size D + 16) /\
  (* the position, in the POST-IMPLICATION form of the text (PRH_Base.v (sha256 da55cb740765; internal record), prh_run_at): from any
     position the caller holds at the ENTRY state, the run's next event being the copy's raw malloc, the position
     advances by that one event *)
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
   PresetRoomPos.iface_room_pos sm x0 os i H0 hist (din_S D) ->
   prh_run_at sm x0 os i [PresetReqAt.HMal (pd_size D + 16)] ->
   exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (pd_size D + 16)])%nat H0 hist' S).
(* the REFUSED arm's facts, the P0 (PRH_FnCheck.v:1669-1678) MINUS the g_own_ran_out byte the NULL arm stores *)
Definition pd_nullblk (D : pd_in) (ly : alayout) (S : astate) (W : world SEGS) (mem : word -> option byte) : Prop :=
  ablocks B ly S = ablocks B (din_ly D) (din_S D) /\
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
   PresetRoomPos.iface_room_pos sm x0 os i H0 hist (din_S D) -> prh_run_at sm x0 os i (@nil PresetReqAt.hev) ->
   exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S) /\
  rd32 (aview SEGS (w_H W) mem) (as_errno B) 12 /\
  (exists ly1 S0 Hp1 W1 regsc memc mdc Wc cc,
     YG0dcf.malloc_cf_null_post (cp := CP) SEGS B ly1 S0 Hp1 W1 regsc memc mdc (pd_size D + 16) (PNull, S) Wc cc).
(* the kit's P1 IN ITS ORDER (the bytes sit between the Lam conjunct and the writable conjunct), so that pd_Q is the kit's
   body by conversion: pd_okblk plus the bytes the copy and the pad wrote *)
Definition pd_okfull (D : pd_in) (ly : alayout) (S : astate) (W : world SEGS)
  (mem : word -> option byte) (res own' : Z) : Prop :=
  res <> 0 /\ own' = din_own D /\ 4096 <= res /\ res + pd_size D + 16 <= YM05.alloc_ceiling /\
  ~ In res (map fst (ablocks B (din_ly D) (din_S D))) /\
  Permutation (ablocks B ly S) ((res, pd_size D + 16) :: ablocks B (din_ly D) (din_S D)) /\
  (forall a k, In (a, k) (din_Lam D) -> a - @cf_head CP <> res) /\
  bytes_at (PA := PA) W mem res (din_x D ++ repeat (din_fill D mod 256) 16) /\
  (forall a, res <= a < res + pd_size D + 16 -> writable_at SEGS (mrestrict (w_H W) mem) a) /\
  range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF res (pd_size D + 16) /\
  shadow_hull_vis (aview SEGS (w_H W) mem) res (pd_size D + 16) /\
  (forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
   PresetRoomPos.iface_room_pos sm x0 os i H0 hist (din_S D) ->
   prh_run_at sm x0 os i [PresetReqAt.HMal (pd_size D + 16)] ->
   exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (pd_size D + 16)])%nat H0 hist' S).
Lemma pd_okfull_of : forall D ly S W mem res own',
  pd_okblk D ly S W mem res own' -> bytes_at (PA := PA) W mem res (din_x D ++ repeat (din_fill D mod 256) 16) ->
  pd_okfull D ly S W mem res own'.
Proof.
intros D ly S W mem res own' (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11) HB.
exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj HB (conj H8 (conj H9 (conj H10 H11))))))))))).
Qed.
(* the kit's two arms, in its words and order *)
Definition pd_arms (D : pd_in) (ly' : alayout) (S' : astate) (W' : world SEGS) (mem' : word -> option byte)
  (res own' : Z) : Prop :=
  (res = 0 /\ own' = 1 /\ pd_nullblk D ly' S' W' mem')
  \/
  pd_okfull D ly' S' W' mem' res own'.
(* the kit's OUTCOME clause (PRH_FnCheck.v c40cf3fdcd2a, tpadded_specX's new conjunct), in these words: at a model run and
   position the caller holds at the ENTRY state whose next event is the copy's raw malloc, a CONSUMER event
   (prh_cons_from), the malloc was GRANTED and S' is the position after it *)
Definition pd_outc (D : pd_in) (S' : astate) (res : Z) : Prop :=
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist (din_S D) ->
  prh_run_at sm x0 os i [PresetReqAt.HMal (pd_size D + 16)] ->
  prh_cons_from sm x0 os i (length [PresetReqAt.HMal (pd_size D + 16)]) ->
  res <> 0 /\
  exists hist', PresetRoomPos.iface_room_pos sm x0 os (i + length [PresetReqAt.HMal (pd_size D + 16)])%nat H0 hist' S'.
(* THE REFUSED ARM IS DEAD AT SUCH A POSITION: the wrapper's NULL cannot happen there. S1 proves it at the call, where
   the wrapper's text hands over the granted path (PRH_Refute.prh_refute_at: a NULL on a granted path at a consumer
   allocation contradicts P8); the NULL arm's cuts carry it to the epilogue, which closes pd_outc with it *)
Definition pd_dead (D : pd_in) : Prop :=
  forall (sm : list Z -> Z * Z) (x0 : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
  PresetRoomPos.iface_room_pos sm x0 os i H0 hist (din_S D) ->
  prh_run_at sm x0 os i [PresetReqAt.HMal (pd_size D + 16)] ->
  prh_cons_from sm x0 os i (length [PresetReqAt.HMal (pd_size D + 16)]) -> False.
(* the outcome clause from the arm: P1 is granted and its position conjunct is the advance; P0 is dead *)
Lemma pd_outc_of_arms : forall D ly' S' W' mem' res own',
  pd_arms D ly' S' W' mem' res own' -> (res = 0 -> pd_dead D) -> pd_outc D S' res.
Proof.
intros D ly' S' W' mem' res own' HA HD sm x0 os i H0 hist Hpos Hrun Hcons.
destruct HA as [(Hr & _) | HOK].
- exfalso. exact (HD Hr sm x0 os i H0 hist Hpos Hrun Hcons).
- destruct HOK as (Hr & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hadv).
  split; [exact Hr|]. exact (Hadv sm x0 os i H0 hist Hpos Hrun).
Qed.

(* ---- THE CUTS (DERIVED offset: B' pc, what holds there) ----
     PD_TEST 48  0x830d8  S2 start: s0 = a0 = b, the wrapper's two outcomes still joined
     PD_OK   52  0x830dc  S3 start: b <> 0, the size test
     PD_SET  72  0x830f0  S4 start: b <> 0 and the first size bytes already hold x (the copy, or size = 0)
     PD_NULL 100 0x8310c  S5 start: b = 0, the g_own_ran_out store
     PD_EPI  112 0x83118  S6 start: both arms, the outcome already established *)
(* the SOURCE IS APART FROM THE WHOLE PADDED BLOCK, and below the ceiling (the S4 row owner's third point): what keeps
   bytes_at data x across __asan_memcpy (which writes [b, b + size)) and __asan_memset (which writes
   [b + size, b + size + 16)), and what memcpy's own `d + n <= x \/ x + n <= d` (YGcallMxmn.v:280) needs. The
   range form and the pointwise form are both here: the range form is the copy rule's premise word for word, the
   pointwise form is what the two keeps consume. S1 pays both once, from src_rd, the ENTRY prhReader_home and the
   freshness of the wrapper's block (FuzzStrdupB.v:480 sd_src_disj is the model). *)
Definition pd_src_apart (D : pd_in) (b : Z) : Prop :=
  (* the range form is memcpy's own premise word for word (d := b, x := data, n := size; YGcallMxmn.v:280). It was
     `b + size + 16 <= data` on its right arm until 16:2xZ: that arm is not derivable at size = 0 (no home premise
     then), while this form is trivially true at size = 0 and follows from the pointwise form at size > 0 *)
  (din_data D + pd_size D <= b \/ b + pd_size D <= din_data D) /\
  (forall a, din_data D <= a < din_data D + pd_size D ->
     0 <= a < YM05.alloc_ceiling /\ ~ (b <= a < b + pd_size D + 16)).
Definition pd_at_test (D : pd_in) ly S Hp W regs mem md k b : Prop :=
  pd_base D ly S Hp W regs mem md k b (din_own D) /\ getr regs 10 = w64 b /\
  ((b = 0 /\ pd_nullblk D ly S W mem /\ pd_dead D) \/
   (pd_okblk D ly S W mem b (din_own D) /\ ~ In b Hp /\ pd_src_apart D b)).
Definition pd_at_ok (D : pd_in) ly S Hp W regs mem md k b : Prop :=
  pd_base D ly S Hp W regs mem md k b (din_own D) /\
  pd_okblk D ly S W mem b (din_own D) /\ ~ In b Hp /\ pd_src_apart D b.
Definition pd_at_set (D : pd_in) ly S Hp W regs mem md k b : Prop :=
  pd_base D ly S Hp W regs mem md k b (din_own D) /\
  pd_okblk D ly S W mem b (din_own D) /\ ~ In b Hp /\ pd_src_apart D b /\
  bytes_at (PA := PA) W mem b (din_x D).
Definition pd_at_null (D : pd_in) ly S Hp W regs mem md k : Prop :=
  pd_base D ly S Hp W regs mem md k 0 (din_own D) /\ pd_nullblk D ly S W mem /\ pd_dead D.
Definition pd_at_epi (D : pd_in) ly S Hp W regs mem md k b : Prop :=
  exists own', pd_base D ly S Hp W regs mem md k b own' /\ pd_arms D ly S W mem b own' /\ (b = 0 -> pd_dead D).

(* ---- the post every segment ends in: the kit's post at this entry (PRH_FnCheck.v de94d3f3a7f1) ---- *)
Definition pd_Q (D : pd_in) : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word ->
  (word -> option byte) -> Model -> Prop :=
  fun ly' S' Hp' W' regs' mem' md' =>
    exists res own', getr regs' 10 = w64 res /\ room_live_cf S' /\ Hp' = din_Hp D /\
    PresetHullBudget.hull_used (din_S D) S' [PresetReqAt.HMal (pd_size D + 16)] /\
    prh_ledger (cp := CP) (PI := prh_img_B) (PA := PA) B ly' S' Hp' W' mem' (din_Lam D) (din_peak D) (din_cnt D)
      (din_fail D) (din_ran D) (din_most D) own' /\
    bytes_at (PA := PA) W' mem' (din_data D) (din_x D) /\
    pd_outc D S' res /\
    pd_arms D ly' S' W' mem' res own'.
Definition pd_post (D : pd_in) : world SEGS -> config -> Prop :=
  fpostm (PI := prh_img_B) (PA := PA) B ARc SK STK_padded [] (din_regs D) (din_ly D) (din_S D)
    (din_Hp D) (din_W D) (din_mem D) (din_md D) (pd_Q D).

(* ---- ONE Prop PER SEGMENT: the whole obligation of the segment that starts at its cut.
   pd_img HEADS EVERY STATEMENT (the lead's question, 15:1xZ; the S4 row owner's second point): it is a fact of the
   IMAGE, one for the whole walk, not of a state, so it does not belong in pd_base, which a cut re-states at every
   state. A segment that cites another passes it on: `Lemma pd_s4 : pd_s6_stmt -> pd_s4_stmt.` with pd_img intro'd
   first inside. The instance file discharges pd_img once, by computation. ---- *)
Definition pd_s6_stmt : Prop := pd_img -> forall D ly S Hp W regs mem md k b,
  pd_at_epi D ly S Hp W regs mem md k b ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pd_pc PD_EPI)) mem (seg_rom SEGS)) md) (pd_post D).
Definition pd_s5_stmt : Prop := pd_img -> forall D ly S Hp W regs mem md k,
  pd_at_null D ly S Hp W regs mem md k ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pd_pc PD_NULL)) mem (seg_rom SEGS)) md) (pd_post D).
Definition pd_s4_stmt : Prop := pd_img -> forall D ly S Hp W regs mem md k b,
  pd_at_set D ly S Hp W regs mem md k b ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pd_pc PD_SET)) mem (seg_rom SEGS)) md) (pd_post D).
Definition pd_s3_stmt : Prop := pd_img -> forall D ly S Hp W regs mem md k b,
  pd_at_ok D ly S Hp W regs mem md k b ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pd_pc PD_OK)) mem (seg_rom SEGS)) md) (pd_post D).

(* ---- THE SHARED SEAT (the S2 row owner's question, 15:2xZ): ONE lemma takes a cut to the engine's st_ok_pi, so the
   five rows do not write five copies of pa_entry_st_ok_full. pd_E is the cut's environment: the machine registers
   below 32, then the five words the prologue saved, as the extra atoms 32 (ra), 33 (s0), 34 (s1), 35 (s2),
   36 (s3) - the epilogue reads them back, which is what makes aregs_preserved provable at the ret. ---- *)
Definition pd_E (D : pd_in) (regs : bvmap 5 word) : env :=
  @Eimg _ B_prog_listing PA (Ereg regs (map (getr (din_regs D)) [1%bv; 8%bv; 9%bv; 18%bv; 19%bv])).
Definition pd_seat_stmt : Prop := pd_img -> forall D off ly S Hp W regs mem md k b ow,
  pd_base D ly S Hp W regs mem md k b ow -> 0 <= b <= CEIL_MAX ->
  st_ok_pi SEGS VAL (pd_E D regs) (pd_ss (pd_koff off))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (pd_pc off)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PD_Bx [] (pd_E D regs) (mrestrict (w_H W) mem) /\
  img_env VAL A_LIM (pd_E D regs) /\
  env_agree 32 (Ereg regs (map (getr (din_regs D)) [1%bv; 8%bv; 9%bv; 18%bv; 19%bv])) (pd_E D regs).
(* the NULL arm's seat: the same, with the one-byte g_own_ran_out cell beside the frame (YC1fP.v:116
   st_ok_pi_add_region over pd_own_region; its base atom A_OBJ 13 is bounded inside the image by pd_facts, so it is
   disjoint from the frame, which astk_ok puts above alloc_ceiling) *)
Definition pd_seat_null_stmt : Prop := pd_img -> forall D off ly S Hp W regs mem md k ow,
  pd_base D ly S Hp W regs mem md k 0 ow ->
  st_ok_pi SEGS VAL (pd_E D regs) (pd_ssn (pd_koff off))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (pd_pc off)) mem (seg_rom SEGS))) /\
  sh_ok SEGS PD_Bx [] (pd_E D regs) (mrestrict (w_H W) mem).
Definition pd_s2_stmt : Prop := pd_img -> forall D ly S Hp W regs mem md k b,
  pd_at_test D ly S Hp W regs mem md k b ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (pd_pc PD_TEST)) mem (seg_rom SEGS)) md) (pd_post D).

(* ---- S1: the prologue and the malloc wrapper's call. THE TRACE: padded never writes s0 before the call
   (B' 0x830a8-0x830d0), so at the wrapper the frame chain is the CALLER's, not empty, and
   call_trace = prh_trace (pc_malloc_ra0 ..) 0x830d4 (spine ch). It is a FIXED trace by prh_univ_closure's FIFTH
   clause (an fp-less callee of a frame-pointer caller, over the caller's context; PRH_Base.v
   (sha256 e6f3bd981ae0; internal record) :1225-1226), which the kit's two premises reach at padded's observed context:
   PRH_Witness.v c5_padded_trace_B, from prh_univ_closure B CTX0 and prh_ctx CTX0 F_padded (raZ regs :: spine ch).
   S1 turns the fixed trace into the admission at the call by YG01.v admits_fix. No premise beyond the kit's text. ---- *)


(* ======== THE SHARED SEAT, PROVED (rule 24: no function proved; kind: engine seat lemmas) ========
   pd_seat builds st_ok_pi at any cut from pd_base by YC1fP.v pa_entry_st_ok_full (FuzzFreeB.v ff_entry1 is the
   form). The facts it reads, in order: of pd_base, pd_J's astk_ok (sp0 mod 16 = 0, alloc_ceiling <= ly_stk_lo,
   ly_stk_lo + STK <= sp0, 0 <= STK, sp0 <= ly_stk_hi <= 2 ^ 47), pd_regsat's x2 / x8 / x18, pd_saved's five words,
   the bound pd_size D <= 3 * 2 ^ 20; of pd_img, pdi_alias and pdi_own_img; the premise 0 <= b <= CEIL_MAX; the
   engine's YM05.alloc_ceiling_value.
   pd_seat_null_stmt IS NOT PROVED: its pd_own_region has the write window [0, 1), so region_ok asks
   writable_at SEGS (mrestrict (w_H W) mem) (VAL (A_OBJ 13)). wview gives that only when the memory holds the byte or
   the byte's WRITABLE segment has it among its seg_bytes (segment_byte_at), and over the Section's abstract PA
   nothing bounds seg_bytes (pdi_pst_ok / pdi_pst_rw give the range and not-read-only only) and pd_base carries no
   presence of g_own_ran_out (prh_glob does not read it; prh_own is in pd_at_null, not in pd_base). The one missing
   fact is pd_pst_wr below, an image fact that S1ImgB.v pst_writable_B proves at PI_prog_B (pa_segs = rsegs) by
   computation; pd_seat_null_of_wr proves the statement from it. *)
(* the cut's environment at the registers pd_regsat fixes *)
Lemma pd_E_low : forall D regs n, (n < A_TEXT)%nat ->
  ew (pd_E D regs) n = ew (Ereg regs (map (getr (din_regs D)) [1%bv; 8%bv; 9%bv; 18%bv; 19%bv])) n.
Proof. intros D regs n Hn. unfold pd_E. apply Eimg_low. exact Hn. Qed.
(* the stack band at a cut: astk_ok of pd_J (sp0 >= ly_stk_lo >= alloc_ceiling >= CEIL_MIN > 2 ^ 46) *)
Lemma pd_sp_band : forall D ly S Hp W regs mem md k b ow, pd_base D ly S Hp W regs mem md k b ow ->
  2 ^ 46 <= pd_sp0 D <= 2 ^ 47 /\ (pd_sp0 D - 48) mod 16 = 0 /\
  bv_unsigned (ew (pd_E D regs) 2) = pd_sp0 D - 48.
Proof.
intros D ly S Hp W regs mem md k b ow HB.
destruct HB as (_ & HJ & _ & HRG & _).
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
destruct HRG as (R2 & _).
pose proof YM05.alloc_ceiling_value as ((Cmin & Cmax) & _).
assert (Rsp : 2 ^ 46 <= pd_sp0 D <= 2 ^ 47) by lia.
split; [exact Rsp|]. split.
- replace (pd_sp0 D - 48) with (pd_sp0 D + (-3) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- rewrite (pd_E_low D regs 2 ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2.
  unfold w64. apply unsigned_lit_small. lia.
Qed.

Lemma pd_seat : pd_seat_stmt.
Proof.
intros HI D off ly S Hp W regs mem md k b ow HB Hb.
destruct (pd_sp_band D ly S Hp W regs mem md k b ow HB) as (Rsp & Hmod & Usp).
destruct HB as (_ & _ & HSV & HRG & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsz).
destruct HRG as (_ & R8 & _ & R18 & _).
pose proof (proj1 (Forall_forall _ _) HSV) as SV. cbv beta in SV.
pose proof (SV (40, 1%bv) ltac:(left; reflexivity)) as S40.
pose proof (SV (32, 8%bv) ltac:(right; left; reflexivity)) as S32.
pose proof (SV (24, 9%bv) ltac:(do 2 right; left; reflexivity)) as S24.
pose proof (SV (16, 18%bv) ltac:(do 3 right; left; reflexivity)) as S16.
pose proof (SV (8, 19%bv) ltac:(do 4 right; left; reflexivity)) as S8.
cbn [fst snd] in S40, S32, S24, S16, S8. clear SV HSV.
assert (Hsz0 : 0 <= pd_size D) by (unfold pd_size; lia).
assert (HEI : img_env VAL A_LIM (pd_E D regs)) by (unfold pd_E; apply Eimg_env).
assert (U8 : bv_unsigned (ew (pd_E D regs) 8) = b).
{ rewrite (pd_E_low D regs 8 ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 8 8%bv eq_refl), R8.
  unfold w64. apply unsigned_lit_small. lia. }
assert (U18 : bv_unsigned (ew (pd_E D regs) 18) = pd_size D).
{ rewrite (pd_E_low D regs 18 ltac:(unfold A_TEXT; lia)), (ew_Ereg_nat regs _ 18 18%bv eq_refl), R18.
  unfold w64. apply unsigned_lit_small. lia. }
assert (Uown : bv_unsigned (ew (pd_E D regs) (A_OBJ 13)) = VAL (A_OBJ 13))
  by (apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia).
(* the saved words: extra atom 32 + j is the j-th of the entry's x1 / x8 / x9 / x18 / x19 *)
assert (Dx : forall (n : nat) (r : bv 5), ew (pd_E D regs) n = getr (din_regs D) r ->
  sv_denot (pd_E D regs) (SOff n 0) = Z_to_bv 64 (bv_unsigned (getr (din_regs D) r))).
{ intros n r Hn. cbn [sv_denot]. rewrite Hn, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (Rx : forall r : bv 5, 0 <= bv_unsigned (getr (din_regs D) r) < 2 ^ (8 * Z.of_N 8)).
{ intros r. pose proof (bv_unsigned_in_range 64 (getr (din_regs D) r)) as R. unfold bv_modulus in R.
  cbn in R |- *. lia. }
assert (E32 : ew (pd_E D regs) 32 = getr (din_regs D) 1%bv)
  by (rewrite (pd_E_low D regs 32 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (E33 : ew (pd_E D regs) 33 = getr (din_regs D) 8%bv)
  by (rewrite (pd_E_low D regs 33 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (E34 : ew (pd_E D regs) 34 = getr (din_regs D) 9%bv)
  by (rewrite (pd_E_low D regs 34 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (E35 : ew (pd_E D regs) 35 = getr (din_regs D) 18%bv)
  by (rewrite (pd_E_low D regs 35 ltac:(unfold A_TEXT; lia)); reflexivity).
assert (E36 : ew (pd_E D regs) 36 = getr (din_regs D) 19%bv)
  by (rewrite (pd_E_low D regs 36 ltac:(unfold A_TEXT; lia)); reflexivity).
split; [|split; [|split]].
- rewrite restrict_mkst_fx.
  replace (pd_pc off) with (BASE + pd_koff off) by (unfold pd_pc, pd_koff; lia).
  unfold pd_ss. apply pa_entry_st_ok_full.
  + unfold pd_E. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold pd_frame. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite Usp.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * exact (chunk_ok_val SEGS _ _ _ 8 8 (SOff 36 0) _ (Dx 36%nat 19%bv E36) (Rx 19%bv) ltac:(lia)
        (val_mem_of_rdword SEGS (w_H W) mem _ _ S8)).
    * exact (chunk_ok_val SEGS _ _ _ 16 8 (SOff 35 0) _ (Dx 35%nat 18%bv E35) (Rx 18%bv) ltac:(lia)
        (val_mem_of_rdword SEGS (w_H W) mem _ _ S16)).
    * exact (chunk_ok_val SEGS _ _ _ 24 8 (SOff 34 0) _ (Dx 34%nat 9%bv E34) (Rx 9%bv) ltac:(lia)
        (val_mem_of_rdword SEGS (w_H W) mem _ _ S24)).
    * exact (chunk_ok_val SEGS _ _ _ 32 8 (SOff 33 0) _ (Dx 33%nat 8%bv E33) (Rx 8%bv) ltac:(lia)
        (val_mem_of_rdword SEGS (w_H W) mem _ _ S32)).
    * exact (chunk_ok_val SEGS _ _ _ 40 8 (SOff 32 0) _ (Dx 32%nat 1%bv E32) (Rx 1%bv) ltac:(lia)
        (val_mem_of_rdword SEGS (w_H W) mem _ _ S40)).
  + cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
  + split; [|split; [exact I | exact (pdi_alias HI _ HEI)]].
    unfold pd_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite Usp, U8, U18, Uown. change (2 ^ 4) with 16. rewrite Hmod, !Z.pow_0_r, !Z.mod_1_r.
    pose proof (pdi_own_img HI) as Hown.
    repeat match goal with |- _ /\ _ => split end; try exact I; try reflexivity; lia.
- unfold sh_ok. apply Forall_nil.
- unfold pd_E. apply Eimg_env.
- split; [intros n Hn; apply pd_E_low; unfold A_TEXT; lia | reflexivity].
Qed.

(* the NULL arm's seat from the one image fact pd_seat_null_stmt lacks (see the header above): the statement is
   pd_img's planned last field pdi_pst_wr, word for word, so pd_seat_null is `pd_seat_null_of_wr (pdi_pst_wr HI)`
   once pd_img carries it. The own cell sits beside the frame by YC1fP.v st_ok_pi_add_region. *)
Lemma pd_seat_null_of_wr :
  (forall (m : word -> option byte) a, Exists (in_zr a) PST -> writable_at SEGS m a) -> pd_seat_null_stmt.
Proof.
intros Hwr HI D off ly S Hp W regs mem md k ow HB.
destruct (pd_sp_band D ly S Hp W regs mem md k 0 ow HB) as (Rsp & _ & Usp).
destruct (pd_seat HI D off ly S Hp W regs mem md k 0 ow HB ltac:(lia)) as (HS & HSH & HEI & _).
split; [|exact HSH].
assert (Uown : bv_unsigned (ew (pd_E D regs) (A_OBJ 13)) = VAL (A_OBJ 13))
  by (apply HEI; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pdi_own_img HI) as Hown.
apply (st_ok_pi_add_region _ (pd_ss (pd_koff off)) _ pd_own_region HS).
- vm_compute. reflexivity.
- rewrite restrict_mkst_fx. unfold pd_own_region, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem mkst]. rewrite Uown.
  split; [unfold IMG_LO_B in Hown; lia|]. split; [unfold IMG_TOP_B in Hown; lia|]. split; [|apply Forall_nil].
  intros o Ho. assert (o = 0) by lia. subst o. rewrite Z.add_0_r.
  apply Hwr.
  rewrite (pdi_own HI). unfold prh_pst. do 6 apply Exists_cons_tl. apply Exists_cons_hd.
  unfold in_zr. cbn [fst snd]. change (Z.of_nat (@pi_gz_own_ran_out prh_img_B)) with 1. lia.
- unfold pd_ss, pd_own_region, pd_frame. cbn [ss_mem all_disjoint]. split; [|exact I].
  unfold extent_disjoint. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Uown, Usp.
  left. unfold IMG_TOP_B in Hown. lia.
Qed.

(* the listing's own tables, closed, for the engine's vm_compute (Cno102B_Base.v:116-120 PL_cno_B, the same terms as
   PAImg_prog.v 4392ab2c09ba :177-181; PAImg_prog.v is the instance and is not Required here) *)
Definition B_prog_tpi_pd : ptree asym := ptree_of_list B_prog_listing.
Definition B_prog_tw_pd : ctable := Eval vm_compute in (tw_of 0 B_prog_listing).
Definition PL_pd_B : PAListing B_prog_listing :=
{| pl_tpi := B_prog_tpi_pd; pl_tpi_eq := eq_refl; pl_tw := B_prog_tw_pd; pl_tw_eq := ltac:(vm_compute; reflexivity);
pl_lim := ltac:(vm_compute; reflexivity); pl_len := ltac:(vm_compute; discriminate); pl_slot0 := ltac:(vm_compute; exact I) |}.

Lemma pd_seat_null : pd_seat_null_stmt.
Proof. intros HI. exact (pd_seat_null_of_wr (pdi_pst_wr HI) HI). Qed.

End d.
