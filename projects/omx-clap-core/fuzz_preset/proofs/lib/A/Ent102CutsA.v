(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Ent102CutsA.v, with its module paths and module names changed; 541 of its 801 lines of code are new or changed and 79 lines of the source are left out. *)
(* omx-clap-core/fuzz_preset, image A' (asan, harness fix #102 pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44, unstripped twin bff8519bbe3ea0e4): THE CUT FILE of
   the harness entry LLVMFuzzerTestOneInput (A' 0x815e0, 804 bytes, 201 instructions, one `ret` at +0x2c4, no jalr).
   STATEMENTS ONLY: every segment is a `Definition seg_<Lk>_stmt : Prop`; there is no Admitted, no Axiom and no
   Parameter in this file. rule 24: proves no function (kind: statements of the walk of LLVMFuzzerTestOneInput).

   SOURCES (record keys).
   - Program text: src-102/new/fuzz_preset.c (the #102 harness source) (sha256 c7b4007bba7bab3e,
     836 lines; `sha256sum -c SHA256SUMS` OK), LLVMFuzzerTestOneInput at :800-836.
   - LISTING: a Theorem Labs lane's whole-program listing of A' (lib/A/Listing_prog.v 1ab147923c5d, symbol-pinned A_OBJ,
     a working branch d42e123915ae; on this branch by path). The offsets below were measured on
     the capstone listing of the twin (the lane's note, the internal file llvm-plan.md appendix A) and CHECKED on
     the generated listing: every one of the 19 call sites is a `PCall AS_<callee>` slot at the offset of section 1,
     slot 73 (+0x124) is the `PHi` of g_own_ran_out's base, slots 19 / 20 / 21 / 22 / 28 / 48 / 49 are the GOT loads,
     the frame call and the descriptor / pc pairs. This file is GENERIC over the listing class ({L} {PA : PAImg L})
     and reads no slot, no A_OBJ index and no generated table; the segment proofs instantiate L := A_prog_listing
     with the PAListing of lib/A/Ent102PLA.v (blob cited in each of them).
   - THE KIT'S TEXTS: a working branch by path: lib/A/PRH_FnCheck.v 37d8e4d0072e and PRH_Base.v
     016934fdc1af (3438f3406f33: the flags-clear / g_most / request-bound premises and the r <-> flags return
     condition on the check_* texts; prh_ledger's named projections), on the kit BATCH 1 (1bba49fd7ac5: int-return check_no_overread / check_as_written / check_round_trip,
     3-argument parse_noting, prh_pst with the two #102 statics pi_g_most / pi_g_own_ran_out, prh_fn with
     F_read_members / F_fuzz_alloc_most, STK_LLVMFuzzerTestOneInput on the #102 callee list), PRH_FnAlloc.v
     025bb30f5117 and PRH_FnPj.v 43642538e741 (b076aa8be5e1).
   - B' (asan-ubsan pin d663f82d7f488d30, entry 0x816cc) has the same mnemonic and register sequence (elfdis --diff:
     identical except pc-relative fields), so every LENGTH below is B''s too; port/a2b.py makes lib/AU's twin.

   THE SEAM WITH THE INTERFACE. The interface (lib/A/PresetCfnA.v, the parent's) is stated over `tfibsegs` and over
   the OLD pins' callee list and literals; under the build route the parent fixed (13:0xZ, "(b)"), the walk is
   parametric over `{PA : PAImg L}` and so over `world pa_segs`. This file therefore does NOT restate or cite
   preset_lib_pre_x / preset_lib_post_x: `ec_pre` is the walk's own entry premise (the conjuncts of the interface's
   pre that the walk reads, over pa_segs) and `cut_ret` its own return state; the instantiation file (PA := PI_prog_A
   at the re-pin) proves preset_lib_pre_x -> ec_pre and cut_ret -> preset_lib_post_x against the RE-CUT interface.
   Program constants (LLVMF_STK, LLVMF_FS_CLASS, LCNT, SIZE_MAX, LIVE_LIB) carry the interface's values (section 0).

   GAPS this statement carries (each is a named premise or a pending field, never a guessed text):
   - Every callee has its kit text in ec_texts (the kit 99f596897b85: PRH_FnCheck.v 1b4213c5f76f with
     tfuzz_alloc_most_specX and tread_members_specX; PRH_FnAlloc.v 006c7e1ef8e6). The nine accessor / check /
     parse_noting posts KEEP prh_own / prh_most (both PST cells, which the journal's image clause exempts).
     Still to come from the kit (the ledger-field half of the E sweep: most / own in prh_glob, PEAK' / RAN'); a segment that
     needs it names it as its one open premise.
   - parse_noting's text (the kit BATCH 1) carries the OLD harness's prh_oks / peak conjuncts until the kit's BATCH 2: the
     segments that cross parse_noting (L2) wait for it. The kit's next texts add the g_own_ran_out = 0 / ran = 0 /
     request <= g_most premises to the check_* texts; the cuts from L1 on then carry the two cells' values
     (pi_g_own_ran_out, pi_g_most, by name).
   - The kit's 3438f3406f33 check_* texts take g_own_ran_out = 0 (prh_own), ran = 0, g_most (prh_most) and a request
     bound; the cuts from cut_cno on carry ec_most / ec_own_is (by name); the request bound ec_req_bound is PROVED
     (lib/A/Ent102ReqA.v, from a Theorem Labs lane's lib/Spec/PjReqBoundW.v), not a premise. Accessor texts and parse_noting do
     not yet keep g_most / g_own_ran_out in their posts (both cells are PST, which the journal's image clause exempts):
     the kit's E sweep / Batch 2 adds them; L2 / L3 wait for it.
   - check_round_trip's text takes the two literal addresses a_mod_at / a_stamp: Section variables EC_A_MOD_AT /
     EC_A_STAMP until a generated name exists.

   THE RE-HIDING MOVE (free / realloc re-hide shadow; the primed callee texts in PRH_*.v, the engine's R forms in
   YA0nH.v / YSRrG.v / YCbqG.v / YCbqGwild.v). check_no_overread
   is the first callee that frees a live block, so: cut_frame / cut_s1 keep ec_inv (the journal at wle); cut_cno ..
   cut_crs1, and cut_ret, carry the journal at wle' segs RZ_cf (ec_invR WLE'); cut_exit, reached on both sides, keeps
   its wle body (L0b's size-guard arm) with cut_exitR beside it (the later arms reach cut_exitR WLE'); L0a / L0b stay
   ec_lane (SRr) and every lane from L1 on is ec_laneR WLE' (SRr' segs RZ_cf). ec_inv / ec_lane / cut_exit keep their
   names and bodies as the instances at wle (ec_inv_R_wle, ec_lane_R_wle, cut_exit_R_wle: by reflexivity), and each
   journal helper keeps its body with an R form beside it. THE HULL (route (b)): ec_pre carries the interface's
   `length os <= 3` and ec_hyps the hull budget at a position (ech_hull_pay), discharged at the composition. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallStackUp.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG01cf YG00cf YGcfRoom.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSite17.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetReqAt PresetRun.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetSecTotal PresetHullBudget.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnPj PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_PjOrder.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. Program constants (LENGTHs, the same in both images), with the VALUES of the interface's section 2
      (lib/A/PresetCfnA.v, the #102 interface, iface-102 4672b2ce764d: LLVMF_STK 32768,
      LLVMF_FS_CLASS 1, SIZE_MAX 2^64 - 1, LCNT 2^32, LIVE_LIB 3 * 2^32; the owner raised the last two at 15:3xZ so
      that the whole call's counts and live bytes fit). They are written here, not imported: the interface's closure reaches
      lib/ZTraceSpec.v -> lib/ZImage.v, which is red on the #102 facts (ZImage.v:38, the old plain image's entry pc;
      pins102 build 20261029T132036Z), and the walk needs only these numbers. The instantiation file proves each equal
      to the re-cut interface's constant by reflexivity. *)
Definition LLVMF_STK : Z := 32768.
Definition LLVMF_FS_CLASS : Z := 1.
Definition LCNT : Z := 2 ^ 32.
Definition SIZE_MAX : Z := 2 ^ 64 - 1.
Definition LIVE_LIB : Z := 3 * 2 ^ 32.

(* LENGTHs of this body, read on the listing (fuzz_preset.c:806 PRESET_FILE_MAX_BYTES = `lui a0,0x300` at +0x10c;
   the prologue's `addi sp,sp,-0x80`; the ASan frame `addi a0,zero,0x80` at +0x6c; struct pj = 56 bytes) *)
Definition EC_NMAX : Z := 0x300000.
Definition EC_SAVE : Z := 128.
Definition EC_FRAME_BYTES : Z := 128.
Definition EC_PJ_BYTES : Z := 56.
(* WORDs the body writes (never relocatable): the frame header magic (+0xa8 / +0xbc) and the free magic (+0x1e4 /
   +0x1e8) *)
Definition EC_HDR : Z := 0x41b58ab3.
Definition EC_FREE_MAGIC : Z := 0x45e0360e.
(* the 16 shadow bytes of the frame while the body runs (+0xd4 .. +0x11c): f1 x4 | 00 x7 | f3 x5; the exit lane's
   0xf8 over bytes 4 .. 10 (+0x1c4 .. +0x1e0) and the release's 0xf5 x16 (+0x1f4 .. +0x234) *)
Definition ec_frame_shadow : list Z := repeat 0xf1 4 ++ repeat 0 7 ++ repeat 0xf3 5.


(* check_no_overread's events in one call (a Theorem Labs lane's l1_cno_evs; the same list as Ent102Win.cno_part and ec_cno_evs's
   body), used by GrantA's tcheck_no_overread_grantedX *)
Definition l1_cno_evs (sm : list Z -> Z * Z) (x : list Z) (o1 o2 o0 : option nat) : list PresetReqAt.hev :=
  let n := Z.of_nat (length x) in
  let copy3 := [PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD);
                PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)] in
  let free3 := [PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD);
                PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD)] in
  if PresetReqAt.MAXB <? n then []
  else if PresetRun.ranout sm x o1 then copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ free3
  else if PresetRun.ranout sm x o2 then
    copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
    PresetRun.p1_tfree sm x o1 ++ free3
  else
    copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
    PresetReqAt.parse_evs sm x (PresetRun.okof o0) ++
    PresetRun.p1_tfree sm x o1 ++ PresetRun.p1_tfree sm x o2 ++ PresetRun.p1_tfree sm x o0 ++ free3.

Section E.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg} {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : @PAImg rc L}.
Local Notation segs := (@pa_segs rc L PA).
(* THE WORLD RELATION AFTER A FREE (the re-hiding move): check_no_overread, the first
   callee that frees a live block, re-hides shadow, so from cut_cno on the journal's world conjunct and every lane's
   continuation are at wle' over the fixed zone RZ_cf (YA0nH.v:147, YGcfRehidePost.v:151), not at wle. *)
Local Notation WLE' := (wle' segs (@YGcfRehidePost.RZ_cf rc)).
Variable B : asyms.
Variable SK : YI16.sink_head.
(* the return site of this call in target_run (the generated RA_LLVMF; A' 0x814dc, B' 0x815c8 - MOVED from the old
   pins' 0x81448 / 0x814cc) and the empty payload's address (the generated A_EMPTY; A' 0x5dd520, B' 0x5ddd60): image
   values the instantiation supplies *)
Variable EC_RA : Z.
Variable EC_EMPTY : Z.
(* check_round_trip's two literal addresses (the kit's tcheck_round_trip_specX arguments a_mod_at / a_stamp) *)
Variables EC_A_MOD_AT EC_A_STAMP : Z.
(* the musl stdio half of PINV (the interface's pinv_stdio at the instance) and the bytes it reads *)
Variable EC_SIO : reader -> Prop.
Variable EC_SIO_IMG : Z -> Prop.

(* ---------------------------------------------------------------------- *)
(* 1. The pcs of this body. EC_BASE is the listing's base, which IS LLVMFuzzerTestOneInput (slot 0 of the
      whole-program listing; ec_img's ei_entry); every other pc is EC_BASE + a LENGTH measured on the listing. *)
Definition EC_BASE : Z := @pa_val rc L PA A_TEXT.
Definition EC_AR_FRAME : Z := EC_BASE + 0x74.      (* __asan_stack_malloc_1 returns *)
Definition EC_S1 : Z := EC_BASE + 0x124.           (* past the size guard: `auipc s9` of g_own_ran_out *)
Definition EC_AR_RORESET : Z := EC_BASE + 0x130.   (* fuzz_alloc_ran_out_reset returns *)
Definition EC_AR_MOST : Z := EC_BASE + 0x140.      (* fuzz_alloc_most returns *)
Definition EC_AR_CNO : Z := EC_BASE + 0x14c.       (* check_no_overread returns; `bnez a0` -> EXIT *)
Definition EC_AR_LIVE : Z := EC_BASE + 0x158.      (* fuzz_alloc_live returns *)
Definition EC_AR_COUNT0 : Z := EC_BASE + 0x160.    (* fuzz_alloc_count returns (first) *)
Definition EC_AR_PRESET : Z := EC_BASE + 0x168.    (* fuzz_alloc_peak_reset returns *)
Definition EC_AR_PNO : Z := EC_BASE + 0x178.       (* parse_noting returns *)
Definition EC_AR_PEAK : Z := EC_BASE + 0x180.      (* fuzz_alloc_peak returns *)
Definition EC_AR_CBA : Z := EC_BASE + 0x18c.       (* check_bounded_alloc returns *)
Definition EC_AR_COUNT1 : Z := EC_BASE + 0x190.    (* fuzz_alloc_count returns (second) *)
Definition EC_AR_RANOUT : Z := EC_BASE + 0x1a0.    (* fuzz_alloc_ran_out returns; `bnez a0` -> FREE *)
Definition EC_AR_CAW : Z := EC_BASE + 0x1b8.       (* check_as_written returns; `beqz a0` -> +0x2c8, else FREE *)
Definition EC_FREE : Z := EC_BASE + 0x1bc.         (* `mv a0,s5; jal pj_free` *)
Definition EC_EXIT : Z := EC_BASE + 0x1c4.         (* pj_free returns = the exit lane *)
Definition EC_RET : Z := EC_BASE + 0x2c4.          (* the one `ret` *)
Definition EC_REJ : Z := EC_BASE + 0x2c8.          (* `sub s7,s9,s7; beqz s8` *)
Definition EC_AR_CRC : Z := EC_BASE + 0x2e0.       (* check_reject_clean returns *)
Definition EC_AR_CRS0 : Z := EC_BASE + 0x2f4.      (* check_reject_clean_starved (.., NULL) returns; `j` EXIT *)
Definition EC_ACC : Z := EC_BASE + 0x2f8.          (* rc = 0: `mv a0,s5; jal read_members` *)
Definition EC_AR_RM : Z := EC_BASE + 0x300.        (* read_members returns *)
Definition EC_AR_CRT : Z := EC_BASE + 0x308.       (* check_round_trip returns; `bnez a0` -> FREE *)
Definition EC_AR_CRS1 : Z := EC_BASE + 0x320.      (* check_reject_clean_starved (.., &doc) returns; `j` FREE *)

(* ---------------------------------------------------------------------- *)
(* 2. The frame geometry (listing +0x000 .. +0x0a4), as FUNCTIONS of the incoming sp and of the fake frame fk.
      `addi sp,sp,-0x80`, `andi sp,sp,-32`, `mv s1,sp`: A = (sp0 - 128) & -32. The fake frame is always obtained
      (the kit's F-DEAD; the use-after-return cell is 1 and frames S = [] at entry), so s11 = s2 = fk and sp stays A. *)
Definition ec_A (sp0 : Z) : Z := Z.land (sp0 - EC_SAVE) (-32).
Definition ec_doc (fk : Z) : Z := fk + 32.

(* the pure document model (PjGrammar at the plain strtod oracle, the kit's ck_read) *)
Definition ec_bytes (pl : list byte) : list Z := map (fun b : byte => bv_unsigned b) pl.

Definition ec_ARx (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (mem : word -> option byte)
  (md : Model) : Prop :=
  ARcf (cp := cp) segs B ly S Hp W mem md /\ xs_placed_cf ly S.
Local Notation ARx := ec_ARx.
Local Notation PST := (@prh_pst PI).
Local Notation rdW W mem := (aview segs (w_H W) mem).
Local Notation mrW W mem := (mrestrict (w_H W) mem).

(* 3. THE FLOAT STATE OF A CUT: after the first fpostF callee the config is at an existential float state with
      frm = 0 and fs0 .. fs11 kept (EntryCutsB section 3b). *)
Definition ec_at (pc : Z) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (c : config) : Prop :=
  exists fy : YK11.FPState,
    YK0o.frm_zero (@YK11.fp_csr fy) /\ fregs_kept_x fx fy /\ c = @cfg_at fy segs pc regs mem md.

(* ---------------------------------------------------------------------- *)
(* 4. The entry context, fixed for the whole call. e_sm / e_os / e_i0 / e_H0 / e_hist0 are the run position of
      P8's room (the rp_ binders of the kit's PresetRoomPos.iface_room_pos): the interface's iface_room_at at entry gives them
      by iface_room_pos_entry. *)
Record ecx : Type := MkEcx {
  e_ly : alayout; e_S : astate; e_W : world segs; e_regs : bvmap 5 word;
  e_mem : word -> option byte; e_md : Model;
  e_p : Z; e_n : Z; e_pl : list byte;
  e_cnt : Z; e_ran : Z;
  e_sm : list Z -> Z * Z; e_os : list (option nat * option nat * option nat); e_i0 : nat;
  e_H0 : list Z; e_hist0 : list YG00.chunk }.
Definition e_sp0 (E : ecx) : Z := spZ (e_regs E).
Definition e_A (E : ecx) : Z := ec_A (e_sp0 E).
Definition e_x (E : ecx) : list Z := ec_bytes (e_pl E).

(* THE CALL'S MODEL EVENTS (exact room position, the kit owner's form of 16:16Z; design port/exact-pos-design.md). The events of
   this call are a Theorem Labs lane's PresetRun.call_evs on the bytes for the grant triple of check_no_overread's three
   readings; the triple is set by the environment's refusals inside check_no_overread, so it is BOUND from cut_cno on
   (ec_trip), and the cuts before it are at the entry index over the earlier calls' grants e_os. *)
Definition ec_trip : Type := (option nat * option nat * option nat)%type.
Definition ec_call_evs (E : ecx) (tr : ec_trip) : list PresetReqAt.hev :=
  let '(o1, o2, o0) := tr in PresetRun.call_evs (e_sm E) (e_x E) o1 o2 o0.
(* check_no_overread's piece: call_evs up to its three frees, without call_rest *)
Definition ec_cno_evs (E : ecx) (tr : ec_trip) : list PresetReqAt.hev :=
  let '(o1, o2, o0) := tr in
  let x := e_x E in let sm := e_sm E in let n := Z.of_nat (length x) in
  let copy3 := [PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD);
                PresetReqAt.HMal (n + PresetReqAt.FUZZ_PAD)] in
  let free3 := [PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD); PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD);
                PresetReqAt.HFr (n + PresetReqAt.FUZZ_PAD)] in
  if PresetReqAt.MAXB <? n then []
  else if PresetRun.ranout sm x o1 then copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ free3
  else if PresetRun.ranout sm x o2 then
    copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
    PresetRun.p1_tfree sm x o1 ++ free3
  else
    copy3 ++ PresetReqAt.parse_evs sm x (PresetRun.okof o1) ++ PresetReqAt.parse_evs sm x (PresetRun.okof o2) ++
    PresetReqAt.parse_evs sm x (PresetRun.okof o0) ++
    PresetRun.p1_tfree sm x o1 ++ PresetRun.p1_tfree sm x o2 ++ PresetRun.p1_tfree sm x o0 ++ free3.
(* the triple RAN OUT: one of check_no_overread's three readings met a refusal; then call_evs has nothing after the CNO
   piece (the call ends: check_no_overread returns 1), else call_rest follows. cut_cno ties check_no_overread's return
   value r to it (r = 1 <-> ec_ranout = true, the kit's exact text's return condition), and every later cut on the r = 0
   path carries ec_ranout = false (a Theorem Labs lane's F1 / F2, owner 17:2xZ). The two call_evs equations it gives
   are lemmas of lib/A/Ent102PosA.v (ec_call_evs_ranout_true / _false), not cut conjuncts. *)
Definition ec_ranout (E : ecx) (tr : ec_trip) : bool :=
  let '(o1, o2, o0) := tr in
  (PresetRun.ranout (e_sm E) (e_x E) o1 || PresetRun.ranout (e_sm E) (e_x E) o2 ||
   PresetRun.ranout (e_sm E) (e_x E) o0)%bool.
(* the pieces after it (PresetRun.call_rest / call_tail): parse_noting's reading, expected()'s scratch, the refused
   tail's starved reading, the accepted tail's rewrite, starved reading + writes and pj_free (&doc) *)
Definition ec_pn (E : ecx) : list PresetReqAt.hev := PresetReqAt.parse_evs (e_sm E) (e_x E) [].
Definition ec_sc (E : ecx) : list PresetReqAt.hev :=
  [PresetReqAt.HMal (Z.of_nat (length (e_x E)) + 1); PresetReqAt.HFr (Z.of_nat (length (e_x E)) + 1)].
Definition ec_rej (E : ecx) : list PresetReqAt.hev :=
  PresetReqAt.starved_parse (e_sm E) (e_x E) (calls (PresetReqAt.rtr (e_sm E) [] (e_x E))).
Definition ec_rt (E : ecx) (t : jv) : list PresetReqAt.hev := PresetReqAt.round_trip (e_sm E) t.
Definition ec_sw (E : ecx) (t : jv) : list PresetReqAt.hev := PresetReqAt.starved_writes (e_x E) t.

(* THE ENTRY PREMISE: the interface pre's conjuncts the walk reads, over pa_segs (header, "THE SEAM") *)
Definition ec_pre (E : ecx) : Prop :=
  afn_pre_x segs B ARx LLVMF_STK (e_ly E) (e_S E) [] (e_W E) (e_regs E) (e_mem E) (e_md E) [] /\
  s0Z (e_regs E) < YM05.alloc_ceiling /\
  YK0o.frm_zero (@YK11.fp_csr fx) /\
  raZ (e_regs E) = EC_RA /\
  getr (e_regs E) 10 = w64 (e_p E) /\ getr (e_regs E) 11 = w64 (e_n E) /\
  ((e_n E = 0 /\ e_p E = EC_EMPTY) \/ (0 < e_n E < 2 ^ 26 /\ In (e_p E, e_n E) (ablocks B (e_ly E) (e_S E)))) /\
  e_n E = Z.of_nat (length (e_pl E)) /\ garr8 segs (mrW (e_W E) (e_mem E)) (e_p E) (e_x E) /\
  frames (e_S E) = [] /\
  @room_live_cf RL (e_S E) /\
  PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E) (e_i0 E) (e_H0 E) (e_hist0 E) (e_S E) /\
  (* the entry index is the end of the earlier calls' model events (iface_room_pos_entry's index) *)
  e_i0 E = length (PresetRun.hruns (e_sm E) (e_x E) (e_os E)) /\
  (* the run model's strtod is the reader's (ck_read reads at ReaderRes.jr_strtod): without it the model's reading
     fst (jr_run (e_sm E) (e_x E) []) - which picks call_tail's arm - is not the program's ck_read (e_x E). The slot pre
     gives the harness's sm; the seam instantiates the interface's sm := ReaderRes.jr_strtod (owner 17:5xZ) *)
  e_sm E = ReaderRes.jr_strtod /\
  blocks_bytes (e_S E) + LIVE_LIB <= LIVE_MAX /\
  arodata_okP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) B (rdW (e_W E) (e_mem E)) /\
  (exists peak most own, @prh_ledger rc cp PI L PA B (e_ly E) (e_S E) [] (e_W E) (e_mem E) [] peak (e_cnt E) SIZE_MAX (e_ran E) most own) /\
  EC_SIO (rdW (e_W E) (e_mem E)) /\
  e_cnt E + LCNT <= SIZE_MAX /\
  (* the count headroom the kit's check texts take (cnt < 2 ^ 62 - 2 ^ 30, PRH_FnCheck.v:552 / :799), which the
     interface's pre gives only as cnt + LCNT <= SIZE_MAX; the old cut file carried it the same way
     (EntryCutsB.v:390). L4Lane's G2, 15:0xZ. *)
  e_cnt E + LCNT < 2 ^ 62 - 2 ^ 30 /\
  (* THE HULL CLOSED SET at the entry (the slot pre's run room, PresetCfnA.v preset_lib_pre_x): the earlier
     calls' grant list has at most 3 entries, so a cut's position e_os E ++ [trp] has at most 4 (the hull budget at
     a run position). Read BY TYPE; inserted after every conjunct a walk file names by position, and not last *)
  (length (e_os E) <= 3)%nat /\
  YAkMemnorm.memnorm segs (e_mem E) /\
  (* THE LIVE REAL STACK at the entry (the slot pre's last conjunct, PresetCfnA.v header item (13); the kit 4b8f95c0455c),
     at e_sp0 E: segment L5b carries it by the journal to check_round_trip's call (tcheck_round_trip_specX's last
     premise). Read BY TYPE (ec_conj_pick); not the last conjunct, so ec_room_at's projection of the wild room stays *)
  YGcallStackUp.astack_up_x segs (e_ly E) (e_W E) (e_sp0 E) (e_mem E) /\
  (* the payload plus 8 bytes is below the allocator ceiling. SINCE THE KIT'S + 8 RELAXATION (the batch kit's freeze,
     2026-10-29; the batch kit's correction of the B' twin's comment, e935f720dae, carried here so a2b keeps it) src_rd asks ONLY
     `p + len <= YM05.alloc_ceiling`, which this conjunct implies, so the + 8 here is stronger than any kit text needs
     (droppable at a later rebind). The block law gives `p + req_size n <= YM05.alloc_ceiling` (the old file's G19 /
     EntS3B's es3_pay8). The instantiation proves it by the interface's preset_lib_pre_pay8. Needed by L1
     (check_no_overread), L3 (check_as_written) and L4 / L5c (check_reject_clean_starved). *)
  (0 < e_n E -> e_p E + e_n E + 8 <= YM05.alloc_ceiling) /\
  (* THE WILD ROOM at entry (the slot pre's, at YCbqGwild.K_LLVMF; the kit owner 02:00Z): with the journal's spent budget it gives
     each budgeted callee its room (ec_room_at below) *)
  YCbqGwild.wild_room (as_universe B) [] YCbqGwild.K_LLVMF (st_depot (e_S E)).

(* ---------------------------------------------------------------------- *)
(* 5. The image facts this body reads that no text gives (discharged at the instantiation by the generated
      PAImg_prog lemmas and a Theorem Labs lane's PALib discharge, lib/A/PALibA.v). *)
(* THE CONTEXT SET the kit's texts take is the TOP's OWN, not a callee's: prh_reach's only base case types
   F_LLVMFuzzerTestOneInput (prh_reach_top, PRH_Base.v:359), and a callee's context is DERIVED from it by
   prh_reach_call at the call's return site (pi_call_rets). So CTX0 = this body's own entry context, and the walk
   hands each text the SAME CTX0; `prh_ctx CTX0 G (raZ regs :: spine ch)` at a call site is then discharged from
   prh_reach_call with ei_fp and ei_rets below. A per-callee `ec_ctxs [return site]` (this file's earlier form) is
   NOT reachable in prh_reach and would make those premises unprovable at the instance too (L4Lane's G6, 15:2xZ).
   This body's entry context is [EC_RA]: ra = EC_RA (ec_pre) and the spine is empty (ec_pre's
   s0Z regs < YM05.alloc_ceiling cuts achain's chain at the entry). *)
Definition ec_ctx0 : list (list Z) := [[EC_RA]].
(* the body's own call sites, callee by return site (the 19 `jal` of section 1), as the facts ei_rets names *)
Definition ec_call_rets : list (prh_fn * Z) :=
  [(F_fuzz_alloc_ran_out_reset, EC_AR_RORESET); (F_fuzz_alloc_most, EC_AR_MOST);
   (F_check_no_overread, EC_AR_CNO); (F_fuzz_alloc_live, EC_AR_LIVE); (F_fuzz_alloc_count, EC_AR_COUNT0);
   (F_fuzz_alloc_peak_reset, EC_AR_PRESET); (F_parse_noting, EC_AR_PNO); (F_fuzz_alloc_peak, EC_AR_PEAK);
   (F_check_bounded_alloc, EC_AR_CBA); (F_fuzz_alloc_count, EC_AR_COUNT1); (F_fuzz_alloc_ran_out, EC_AR_RANOUT);
   (F_check_as_written, EC_AR_CAW); (F_pj_free, EC_EXIT); (F_check_reject_clean, EC_AR_CRC);
   (F_check_reject_clean_starved, EC_AR_CRS0); (F_read_members, EC_AR_RM); (F_check_round_trip, EC_AR_CRT);
   (F_check_reject_clean_starved, EC_AR_CRS1)].

Definition ec_static_free (a : Z) : Prop :=
  ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4).
Record ec_img : Prop := MkEcImg {
  (* the listing's slot 0 is this function (A_entry_LLVMFuzzerTestOneInput) *)
  ei_entry : @pa_sigma rc L PA AS_LLVMFuzzerTestOneInput = EC_BASE;
  (* the class-1 frame-area entry is the listing's __asan_stack_malloc_1 (+0x070) *)
  ei_sm1 : pc_stack_malloc (as_code B) LLVMF_FS_CLASS = @pa_sigma rc L PA AS___asan_stack_malloc_1;
  (* the GOT words of +0x054 / +0x058, the shadow cell, the allocator entries (YC1fP's record) *)
  ei_pal : PALib (L := L) (PI := PA) B;
  (* the musl stdio bytes: not runtime-owned, not errno, not a ledger cell, inside the image; EC_SIO reads only them *)
  ei_sio : forall a, EC_SIO_IMG a -> ec_static_free a /\ in_img segs a /\ ~ Exists (in_zr a) PST;
  ei_sio_frame : forall rd rd' : reader, (forall a, EC_SIO_IMG a -> rd' a = rd a) -> EC_SIO rd -> EC_SIO rd';
  (* the ledger cells are not runtime-owned and not errno (the journal's image clause leaves them to PST) *)
  ei_pst : forall a, Exists (in_zr a) PST -> ec_static_free a /\ in_img segs a;
  (* The kit's generated own-frame size of this function covers the drop from sp0 to a callee's sp (A >= sp0 - 144):
     pi_frame F_LLVMFuzzerTestOneInput = 128 + 32 - 16 = 144 on both #102 pins (PRH_Base.v pi_frame's rule;
     lib/A/PRH_Img.v 934516a622e8:33, the kit Batch 1). Every call site's stack window (STK_callee - (A - sp0) <=
     LLVMF_STK) follows from it and et_stk (L6Lane, 13:5xZ). *)
  ei_frame : EC_SAVE + 16 <= @pi_frame PI F_LLVMFuzzerTestOneInput;
  (* the ledger cells are writable data, off the read-only bytes (the statics are RW: PRH_Base's image-fact note), so
     a callee that writes one keeps arodata_okP (L6Lane, 14:0xZ; every lane crossing a ledger-writing callee) *)
  ei_pst_ro : forall a, Exists (in_zr a) PST -> ~ in_roP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) a;
  (* THE EMPTY PAYLOAD'S ADDRESS is a registered datum of the image, well inside it: at n = 0 the call is made with
     p = EC_EMPTY (the generated oft_aligned_copy.empty; A' 0x5dd520, B' 0x5ddd60), and the texts of
     check_no_overread and check_reject_clean_starved ask `0 < data`, src_rd's range facts and prhReader_home of
     (data, 0) UNCONDITIONALLY - a payload-free call reaches them (ck_read [] = None). Nothing else in this file or
     in PresetCfnA's pre says anything about EC_EMPTY. EntryCutsB's open item ei_empty (EntryCutsB.v:90-91);
     L4Lane's finding, 14:5xZ. *)
  (* stated over the INSTANCE's image bounds since the kit decff67d721f: kept_at / kept_img (PRH_Base.v:1020-1047) bound an
     image string by pa_lo + 64 <= p /\ p + n + 64 <= pa_hi, and with PA generic nothing relates pa_lo / pa_hi to
     YImgTop's IMG_LO / IMG_TOP (L4Lane, 18:2xZ). At A' PAImg_prog sets them to IMG_LO / IMG_TOP; B' has its own. *)
  (* BOTH bounds: the YImgTop half for src_rd's own facts (4096 <= EC_EMPTY, EC_EMPTY + 8 <= YM05.alloc_ceiling,
     amem_range), which a generic PA gives only through pa_img_cover and a full ALedger, and the instance half for
     the kit's kept_img (L4Lane's refinement, 18:3xZ). At A' the two are the same fact; B''s 0x5ddd60 satisfies both. *)
  ei_empty : (YImgTop.IMG_LO + 64 <= EC_EMPTY /\ EC_EMPTY + 64 <= YImgTop.IMG_TOP) /\
             (@pa_lo rc L PA + 64 <= EC_EMPTY /\ EC_EMPTY + 64 <= @pa_hi rc L PA);
  (* A PARAMETER FACT of this unit's CfParams (not an image fact, but of the same kind: the walk cannot derive it,
     and at CfParams_preset it is 2 ^ 28 + 16 < 2 ^ 29 - 2 ^ 20). The request premises of the check texts
     (`RQ_crcs tb + cf_head < cf_malloc_max`, PRH_FnCheck.v:815; parse_noting's `RQ_pj_parse + cf_head <
     cf_malloc_max`, :496) follow from it with PjReqBoundW.rq_read_bound_56 (a reading's largest request is at most
     56 |x| + 448 < 2 ^ 28 for |x| <= EC_NMAX). L4Lane's G4, 15:0xZ. *)
  ei_malloc_max : PRH_FnWriter.prhWriter_WMAX + cf_head < cf_malloc_max;
  (* CFHEAD-16: the harness HEAD is the model's (16 = 16 at CfParams_preset); the kit's reader texts state their tree
     conjuncts under it, and the cut's ec_pjf is supplied through it (LL2) *)
  ei_head : cf_head = PresetReqAt.HEAD;
  (* THE ONE STATIC THIS BODY TOUCHES BY A LISTING ADDRESS: g_own_ran_out, through `auipc s9` (slot 73 = +0x124,
     PHi 4) and `sb zero,-0x1c4(s9)` (+0x128) / `lbu a1,-0x1c4(s9)` (+0x190). The listing's hi value and the kit's
     generated cell are independent parameters here ({PA : PAImg L} and {PI : PrhImg}), so the walk cannot relate
     them: this field does (A_prog_hi 4 = 0x5dd704, pi_g_own_ran_out = 0x5dd540 on A', width 1 on both pins; at the
     instance it is vm_compute / reflexivity). a Theorem Labs lane's finding on LL1, owner's decision 15:2xZ. The body touches
     no other static by a listing address: its remaining auipc / PHi slots are the two GOT words (A_OBJ 0 / 1, slots
     19-22), the frame descriptor (A_OBJ 2, slots 43 / 48) and its own entry pc (A_TEXT, slots 46 / 49); g_most is
     written inside fuzz_alloc_most, not here. B' has its own hi index: lib/B's twin states it for B_prog_hi. *)
  ei_own : @pa_val rc L PA (A_HI 4) - 0x1c4 = @pi_g_own_ran_out PI /\ @pi_gz_own_ran_out PI = 1%nat;
  (* g_most's WIDTH (the twin of ei_own's width conjunct): a row that rebuilds the ledger from the cells' readings needs
     it, and pi_gz_most is abstract in PrhImg (a Theorem Labs lane, owner 19:1xZ); at both pins the generated value is 8 *)
  ei_most_w : @pi_gz_most PI = 8%nat;
  (* the call graph the kit's contexts are derived along (section 8): this body keeps a frame pointer, and each of its 19
     call sites is a return site of the generated table. With ec_ctx0 they give every callee's observed context by
     prh_reach_call (L4Lane's G6). *)
  ei_fp : @pi_fp PI F_LLVMFuzzerTestOneInput = true;
  ei_rets : forall G r, In (G, r) ec_call_rets -> In r (@pi_call_rets PI F_LLVMFuzzerTestOneInput G);
  (* the seven PST statics are distinct globals: every row that moves one of them (the own_ran_out store at +0x128,
     and every callee that writes the ledger) needs their extents pairwise disjoint, and nothing else says it
     (a Theorem Labs lane's (3) on LL1; the instance proves it by vm_compute on the generated table. B' states the same form over
     its own prh_img_B). *)
  ei_pst_sep : pairwise zdisjoint PST;
  (* the two literals check_round_trip's text takes (a_mod_at / a_stamp): their bytes are image bytes the run keeps
     (tcheck_round_trip_specX asks kept_img of each; owner 15:2xZ) *)
  ei_lits : kept_img B EC_A_MOD_AT (Z.of_nat (length ck_MOD_AT) + 1) /\
            kept_img B EC_A_STAMP (Z.of_nat (length ck_STAMP) + 1);
  (* the statics are WRITABLE BYTES, not merely image bytes of a writable segment: the `sb zero` to g_own_ran_out at
     +0x128 (and every ledger write of a callee) needs writable_at, and segment_byte_at is None past a segment's hex
     chunks, which ei_pst (in_img) and ei_pst_ro (the segment carries 'w') do not exclude (a Theorem Labs lane on LL1 against
     LPS RiscvSemantics.v:530-542 / :298-308; owner's decision 15:3xZ). Stated at the EMPTY overlay, so it is a fact
     of the image alone; the instance proves it by vm_compute on rsegs. *)
  ei_pst_w : forall a, Exists (in_zr a) PST -> writable_at segs (fun _ => None) a
}.

(* ---------------------------------------------------------------------- *)
(* 6. What every cut after the frame call carries. *)
(* the call's own frame area: one class-1 fake frame fk, with the flag word the inline release reads at
   [fk + 120] (`ld a0,0x78(s2)` at +0x238; pcc_stack_malloc's post writes it at frame_addr + 128 - 8) *)
Definition ec_own (fk : Z) (ly : alayout) (W : world segs) (mem : word -> option byte) (own : list (Z * Z))
  : Prop :=
  exists pos, own = [(LLVMF_FS_CLASS, pos)] /\ fk = frame_addr ly LLVMF_FS_CLASS pos /\ fk <> 0 /\
    rd64 (rdW W mem) (fk + EC_FRAME_BYTES - 8) (flag_addr ly LLVMF_FS_CLASS pos).

(* the saved block (offsets from sp0): ra at sp0 - 8, s0 .. s11 at sp0 - 16 .. sp0 - 104 *)
Definition ec_saved (E : ecx) (W : world segs) (mem : word -> option byte) : Prop :=
  rd64 (rdW W mem) (e_sp0 E - 8) (raZ (e_regs E)) /\
  rd64 (rdW W mem) (e_sp0 E - 16) (bv_unsigned (getr (e_regs E) 8)) /\
  rd64 (rdW W mem) (e_sp0 E - 24) (bv_unsigned (getr (e_regs E) 9)) /\
  rd64 (rdW W mem) (e_sp0 E - 32) (bv_unsigned (getr (e_regs E) 18)) /\
  rd64 (rdW W mem) (e_sp0 E - 40) (bv_unsigned (getr (e_regs E) 19)) /\
  rd64 (rdW W mem) (e_sp0 E - 48) (bv_unsigned (getr (e_regs E) 20)) /\
  rd64 (rdW W mem) (e_sp0 E - 56) (bv_unsigned (getr (e_regs E) 21)) /\
  rd64 (rdW W mem) (e_sp0 E - 64) (bv_unsigned (getr (e_regs E) 22)) /\
  rd64 (rdW W mem) (e_sp0 E - 72) (bv_unsigned (getr (e_regs E) 23)) /\
  rd64 (rdW W mem) (e_sp0 E - 80) (bv_unsigned (getr (e_regs E) 24)) /\
  rd64 (rdW W mem) (e_sp0 E - 88) (bv_unsigned (getr (e_regs E) 25)) /\
  rd64 (rdW W mem) (e_sp0 E - 96) (bv_unsigned (getr (e_regs E) 26)) /\
  rd64 (rdW W mem) (e_sp0 E - 104) (bv_unsigned (getr (e_regs E) 27)).

(* the frame while the body runs: the saved block, the 16 shadow bytes of +0xd4 .. +0x11c, the alignment *)
Definition ec_frame (E : ecx) (fk : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  ec_saved E W mem /\ garr8 segs (mrW W mem) (shadow_addr fk) ec_frame_shadow /\ fk mod 32 = 0.

(* THE COUNT BUDGET (the old cut file's eb_Ccut, EntryCutsB.v:84-86 / :375-379, ported on the owner's decision
   15:1xZ). MARKED: one opaque function, the allocator calls the run may still add to g_count from cut i on, until
   the per-callee counts are stated. Each cut carries `cnt + ec_ccut E i <= e_cnt E + LCNT`, so a lane can pay its
   end cut's count bound from its callee's own growth; without it a cut that allows cnt = e_cnt E + LCNT makes the
   next cut's bound false (L4Lane's G3 on the refused arm: check_reject_clean_starved adds ck_pick x took + 1). *)
Variable ec_ccut : ecx -> nat -> Z.
(* at doc = 0 the starved check's count does not depend on the tree (PRH_FnCheck.v:203-205) *)
Lemma ec_crcs_max_doc0 : forall x took (t : jv), ck_crcs_max x took 0 t = ck_crcs_max x took 0 PjTree.JNull.
Proof. intros x took t. unfold ck_crcs_max. reflexivity. Qed.

Definition ec_ccut_ok : Prop :=
  (* the upper bound mirrors ec_lcut_ok's: without it `ec_ccut E 0 <= LCNT` is not derivable at cut_frame / cut_s1,
     where the lane calls nothing that counts and the budget itself is the only thing to bound (L0Lane, 15:4xZ) *)
  forall E i j, 0 <= ec_ccut E i <= LCNT /\ ((i <= j)%nat -> ec_ccut E j <= ec_ccut E i).
(* THE LIVE-BYTES BUDGET, the same shape (a Theorem Labs lane's O3 on LL2, owner's decision 15:1xZ): the flat conjunct
   `blocks_bytes S + LIVE_LIB <= LIVE_MAX` of the old ec_inv is FALSE at a cut after an allocating callee (the
   reading's live trees are in blocks_bytes S), so the live clause leaves ec_inv and each cut carries
   `blocks_bytes S + ec_lcut E i <= LIVE_MAX`: the bytes the rest of the call may still hold live. ec_lcut E 0 is
   LIVE_LIB (the entry's own budget, ec_pre's conjunct). MARKED, one opaque function, like ec_ccut. *)
Variable ec_lcut : ecx -> nat -> Z.
Definition ec_lcut_ok : Prop :=
  forall E i j, 0 <= ec_lcut E i <= LIVE_LIB /\ ((i <= j)%nat -> ec_lcut E j <= ec_lcut E i).

(* THE PAY FACTS of the two budgets (a Theorem Labs lane's G-A, owner's decision 15:5xZ, on top of L4Lane's edge laws): both
   ec_ccut and ec_lcut are opaque antitone functions, so nothing in their _ok laws makes the DROP between two cuts
   PAY for the callees of the lane between them (ec_ccut E i = 0 satisfies ec_ccut_ok and then cut_pno's count
   conjunct fails after parse_noting's calls; ec_lcut E i = LIVE_LIB likewise). One pay pair per ALLOCATING lane,
   each against the callee's own measure from the kit's post:
     L1  cut_s1 1 -> cut_cno 2:   check_no_overread, at most three readings; it keeps Lam and ablocks, so the live
                                  side is the monotone drop;
     L2  cut_cno 2 -> cut_pno 3:  parse_noting, keyed on the RUN'S OWN TRACE (the post's calls tr and
                                  hpeak tr / nlive tr; its bound hpeak tr <= 224 * len + 16384 is in the post too);
     L4  cut_caw 4 -> cut_crs0 5: check_reject_clean_starved at doc = 0 (ck_crcs_max; check_reject_clean counts none);
     L5b cut_rm 7 -> cut_crt 8:   check_round_trip, ck_crt_count t cset with cset <= 3;
     L5c cut_crt 8 -> cut_crs1 9: check_reject_clean_starved at doc <> 0.
   Every OTHER lane calls nothing that counts or holds (L0b, L3, L4's accepted arm, L4j, L5a, L5d, L6f, L6x), so the
   _ok laws' monotonicity pays it, and the index order is topological, so i <= j holds on each of those edges.
   SATISFIABILITY (the instance picks ec_ccut / ec_lcut as the remaining worst case to the exit; |x| <= 0x300000):
   counts 3 * ck_ncalls + ck_ncalls + (ck_ncalls + 1) + ck_crt_count + ck_crcs_max, each reading at most 2 |x| + 2
   = 6.29e6 calls and each write family a small multiple of it, so under 1e8 << LCNT = 2 ^ 32 = 4.29e9 (a factor of
   about 40); live hpeak tr <= 224 |x| + 16384 = 7.04e8 plus cf_head * nlive, under 1e9 << LIVE_LIB = 3 * 2 ^ 32 =
   1.29e10 (a factor of about 13). Both are satisfiable with the headroom ec_pre gives. *)
Record ec_pay : Prop := MkEcPay {
  (* EVERY field is guarded by the input's length and, where it speaks of a tree, by `ck_read (e_x E) = Some t`:
     without the guards the record is REFUTABLE and so every segment statement vacuous (a Theorem Labs lane's witness
     t_n := JArr (repeat (JStr []) n), whose ck_crt_count t_n 0 grows without bound; owner's decision 15:2xZ). The
     length guard is the cuts' own `e_n E <= EC_NMAX` with ec_pre's `e_n E = Z.of_nat (length (e_pl E))`; ecx itself
     bounds nothing, so each field asks it. *)
  epay_cno : forall E : ecx, Z.of_nat (length (e_x E)) <= EC_NMAX ->
    3 * ck_ncalls (e_x E) + ec_ccut E 2 <= ec_ccut E 1 /\ ec_lcut E 2 <= ec_lcut E 1;
  (* the run's own trace, at ANY failure oracle ok: calls tr and hpeak tr are bounded for every ok (a refused run
     makes fewer calls than the granted one, and parse_noting's post carries hpeak tr <= 224 * len + 16384), so the
     length guard is what makes this satisfiable *)
  epay_pno : forall (E : ecx) ok res tr, Z.of_nat (length (e_x E)) <= EC_NMAX ->
    jr_run ReaderRes.jr_strtod (e_x E) ok = (res, tr) ->
    Z.of_nat (calls tr) + ec_ccut E 3 <= ec_ccut E 2 /\
    ReaderRes.hpeak tr + cf_head * ReaderRes.nlive tr + ec_lcut E 3 <= ec_lcut E 2;
  (* NO tree guard on the two crs0 fields: that call is reached ONLY on the REFUSED arm (cut_caw's r = 0 case gives
     res = ck_read (e_x E), and the arm runs when rc <> 0, so res = None), which makes `ck_read (e_x E) = Some t`
     false exactly where they are needed (L4Lane, 15:4xZ). Both are stated WITHOUT t, at ONE fixed tree (JNull):
     tcheck_reject_clean_starved_specX binds t universally (PRH_FnCheck.v:783) and at doc = 0 asks nothing of it but
     its LIVE premise (:814), so the caller picks t := JNull there. ck_crcs_max at doc = 0 does not read t at all
     (ec_crcs_max_doc0 below), so a row that instantiates the text at another t gets the same count. *)
  epay_crs0 : forall E : ecx, Z.of_nat (length (e_x E)) <= EC_NMAX ->
    ck_crcs_max (e_x E) (ck_ncalls (e_x E)) 0 PjTree.JNull + ec_ccut E 5 <= ec_ccut E 4 /\
    ec_lcut E 5 <= ec_lcut E 4;
  epay_crt : forall (E : ecx) (t : jv) (cset : Z), Z.of_nat (length (e_x E)) <= EC_NMAX ->
    ck_read (e_x E) = Some t -> 0 <= cset <= 3 ->
    ck_crt_count t cset + ec_ccut E 8 <= ec_ccut E 7 /\ ec_lcut E 8 <= ec_lcut E 7;
  epay_crs1 : forall (E : ecx) (t : jv), Z.of_nat (length (e_x E)) <= EC_NMAX -> ck_read (e_x E) = Some t ->
    ck_crcs_max (e_x E) (ck_ncalls (e_x E)) 1 t + ec_ccut E 9 <= ec_ccut E 8 /\ ec_lcut E 9 <= ec_lcut E 8;
  (* THE COVER half: at the CALL the callee's own entry premise `blocks_bytes S + LIVE_<f> .. <= LIVE_MAX` must follow
     from the cut's `blocks_bytes S + ec_lcut E i <= LIVE_MAX`, so the budget at that cut covers the callee's live
     need. Same guards. With them these also DISCHARGE the G5 premises (LIVE_<f> <= LIVE_LIB by ec_lcut_ok). *)
  ecov_cno : forall E : ecx, Z.of_nat (length (e_x E)) <= EC_NMAX ->
    LIVE_check_no_overread (e_x E) <= ec_lcut E 1;
  ecov_pno : forall E : ecx, Z.of_nat (length (e_x E)) <= EC_NMAX ->
    PRH_FnPj.LIVE_pj_parse (e_x E) <= ec_lcut E 2;
  (* this one also needs `e_n E <= EC_NMAX`: it speaks of e_n, which ecx leaves free (only ec_pre ties it to
     length (e_pl E)), and LIVE_check_as_written is increasing, so without it E with e_n := LIVE_LIB refutes the
     record at ANY choice of the budgets - PaySatLane's second refutation, 15:4xZ. The cut L3 starts from (cut_pno)
     carries e_n E <= EC_NMAX. *)
  ecov_caw : forall E : ecx, Z.of_nat (length (e_x E)) <= EC_NMAX -> e_n E <= EC_NMAX ->
    LIVE_check_as_written (e_n E) <= ec_lcut E 3;
  ecov_crs0 : forall E : ecx, Z.of_nat (length (e_x E)) <= EC_NMAX ->
    LIVE_check_reject_clean_starved (e_x E) PjTree.JNull <= ec_lcut E 4;
  ecov_crt : forall (E : ecx) (t : jv), Z.of_nat (length (e_x E)) <= EC_NMAX -> ck_read (e_x E) = Some t ->
    LIVE_check_round_trip t <= ec_lcut E 7;
  ecov_crs1 : forall (E : ecx) (t : jv), Z.of_nat (length (e_x E)) <= EC_NMAX -> ck_read (e_x E) = Some t ->
    LIVE_check_reject_clean_starved (e_x E) t <= ec_lcut E 8
}.


(* #102's two harness cells (the kit's PRH_Base.v prh_most / prh_own, by name): g_most = PJ_ALLOC_BOUND (n) once
   fuzz_alloc_most has run (+0x13c), g_own_ran_out = own *)
Definition ec_most (E : ecx) (W : world segs) (mem : word -> option byte) : Prop :=
  @prh_most rc PI L PA W mem (PJ_ALLOC_BOUND (e_n E)).
Definition ec_own_is (W : world segs) (mem : word -> option byte) (o : Z) : Prop := @prh_own rc PI L PA W mem o.

(* THE WILD BUDGET SPENT up to each cut (the batch kit's prh_wk per callee, the listing's call order; a cut reached by several
   arms takes the largest): frame / s1 0; cno 6; pno 8; caw 8 (check_as_written 0); crs0 10 (check_reject_clean 0 +
   check_reject_clean_starved 2); acc 8; rm 8 (read_members 0); crt 74 (check_round_trip 66); crs1 76; free 76 (reached
   from caw / ranout at 8, from crt at 74, from crs1 at 76); exit 76 (pj_free 0; from crs0 at 10 too). All <= K_LLVMF *)
Definition ec_wk_cno : nat := prh_wk F_check_no_overread.
Definition ec_wk_pno : nat := ec_wk_cno + prh_wk F_parse_noting.
Definition ec_wk_caw : nat := ec_wk_pno + prh_wk F_check_as_written.
Definition ec_wk_crs0 : nat := ec_wk_caw + prh_wk F_check_reject_clean + prh_wk F_check_reject_clean_starved.
Definition ec_wk_rm : nat := ec_wk_caw + prh_wk F_read_members.
Definition ec_wk_crt : nat := ec_wk_rm + prh_wk F_check_round_trip.
Definition ec_wk_crs1 : nat := ec_wk_crt + prh_wk F_check_reject_clean_starved.
Definition ec_wk_free : nat := ec_wk_crs1.
Definition ec_wk_exit : nat := ec_wk_free + prh_wk F_pj_free.
Lemma ec_wk_values : ec_wk_cno = 6%nat /\ ec_wk_pno = 8%nat /\ ec_wk_caw = 8%nat /\ ec_wk_crs0 = 10%nat /\
  ec_wk_rm = 8%nat /\ ec_wk_crt = 74%nat /\ ec_wk_crs1 = 76%nat /\ ec_wk_free = 76%nat /\ ec_wk_exit = 76%nat /\
  YCbqGwild.K_LLVMF = 140%nat.
Proof. vm_compute. repeat split. Qed.

Definition ec_inv (E : ecx) (fk : Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (mem : word -> option byte) (md : Model) (own : list (Z * Z)) (Lam : list (Z * Z)) (peak cnt ran k : Z)
  (os_c : list ec_trip) (i_c : nat) (wk : nat) : Prop :=
  (* the journal from entry at a WILD BUDGET: its fresh wild traces WS are at most wk (the cut's spent budget) *)
  (exists WS, ajournal_xw (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
     (e_md E) own ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS) /\
  ec_own fk ly W mem own /\
  (exists most own, @prh_ledger rc cp PI L PA B ly S Hp W mem Lam peak cnt SIZE_MAX ran most own) /\
  EC_SIO (rdW W mem) /\
  arodata_okP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) B (rdW W mem) /\
  @room_live_cf RL S /\
  (* THE EXACT ROOM POSITION of this cut (os_c, i_c given by the cut) *)
  (exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os_c i_c (e_H0 E) hist S) /\
  e_cnt E <= cnt <= e_cnt E + LCNT /\
  ec_pre E /\
  (e_n E = 0 \/ In (e_p E, e_n E) (ablocks B ly S)) /\
  Permutation (ablocks B ly S) (ck_hblks Lam ++ ablocks B (e_ly E) (e_S E)) /\
  (forall i, 0 <= i < e_n E -> rdW W mem (e_p E + i) = rdW (e_W E) (e_mem E) (e_p E + i)) /\
  YAkMemnorm.memnorm segs mem.
(* ec_inv OVER A WORLD RELATION R (the re-hiding move): a COPY of ec_inv's body with the journal at R
   (YCbqG.ajournal_xwR R). ec_inv is used at cuts on BOTH sides of a free (cut_frame / cut_s1 before check_no_overread,
   every later cut after it), so it keeps its old name and body as the instance at wle - proof lines unfold ec_inv and
   read its conjuncts - and the cuts after a free take ec_invR at wle' (WLE'). ec_inv_R_wle (by reflexivity) checks
   that ec_inv IS ec_invR at wle, so the two copies cannot drift. *)
Definition ec_invR (R : world segs -> world segs -> Prop) (E : ecx) (fk : Z) (ly : alayout) (S : astate)
  (Hp : list Z) (W : world segs) (mem : word -> option byte) (md : Model) (own : list (Z * Z)) (Lam : list (Z * Z))
  (peak cnt ran k : Z) (os_c : list ec_trip) (i_c : nat) (wk : nat) : Prop :=
  (exists WS, ajournal_xwR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
     (e_md E) own ly S Hp W mem md k WS /\ YCbqGwild.wbudget [] wk WS) /\
  ec_own fk ly W mem own /\
  (exists most own, @prh_ledger rc cp PI L PA B ly S Hp W mem Lam peak cnt SIZE_MAX ran most own) /\
  EC_SIO (rdW W mem) /\
  arodata_okP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) B (rdW W mem) /\
  @room_live_cf RL S /\
  (exists hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os_c i_c (e_H0 E) hist S) /\
  e_cnt E <= cnt <= e_cnt E + LCNT /\
  ec_pre E /\
  (e_n E = 0 \/ In (e_p E, e_n E) (ablocks B ly S)) /\
  Permutation (ablocks B ly S) (ck_hblks Lam ++ ablocks B (e_ly E) (e_S E)) /\
  (forall i, 0 <= i < e_n E -> rdW W mem (e_p E + i) = rdW (e_W E) (e_mem E) (e_p E + i)) /\
  YAkMemnorm.memnorm segs mem.
Lemma ec_inv_R_wle : forall E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk,
  ec_inv E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk =
  ec_invR (@wle segs) E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk.
Proof. reflexivity. Qed.
(* only the journal's world conjunct reads R: an invariant at R1 is one at every R2 containing R1 *)
Lemma ec_invR_mono : forall (R1 R2 : world segs -> world segs -> Prop), (forall W W', R1 W W' -> R2 W W') ->
  forall E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk,
  ec_invR R1 E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  ec_invR R2 E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk.
Proof.
  intros R1 R2 H12 E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk [(WS & HJ & HB) H].
  split; [|exact H]. exists WS. split; [|exact HB].
  eapply YCbqG.ajournal_xwR_mono; [exact H12 | exact HJ].
Qed.
(* THE LIFT ACROSS THE FIRST FREE: a cut before check_no_overread (at wle) read at wle' (YA0nH.wle_wle') *)
Lemma ec_inv_wle' : forall E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk,
  ec_inv E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk ->
  ec_invR WLE' E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk.
Proof.
  intros E fk ly S Hp W mem md own Lam peak cnt ran k os_c i_c wk H.
  apply (ec_invR_mono (@wle segs) WLE' (wle_wle' segs _)). exact H.
Qed.

(* the registers the prologue sets and every later piece reads (+0x03c .. +0x0b4): sp = A, gp, tp, s0 = sp0,
   s1 = A, s2 = fk, s3 = n, s4 = p, s10 = shadow (fk), s11 = fk *)
Definition ec_rk (E : ecx) (fk : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (e_A E) /\
  getr regs 3 = getr (e_regs E) 3 /\ getr regs 4 = getr (e_regs E) 4 /\
  getr regs 8 = w64 (e_sp0 E) /\ getr regs 9 = w64 (e_A E) /\
  getr regs 18 = w64 fk /\ getr regs 19 = w64 (e_n E) /\ getr regs 20 = w64 (e_p E) /\
  getr regs 26 = w64 (shadow_addr fk) /\ getr regs 27 = w64 fk.
(* from +0x150 on, s5 = &doc *)
Definition ec_rkd (E : ecx) (fk : Z) (regs : bvmap 5 word) : Prop :=
  ec_rk E fk regs /\ getr regs 21 = w64 (ec_doc fk).

(* the reading the harness made (parse_noting's post): ok list, result, trace, the doc's blocks *)
(* THE READING THE HARNESS MADE. The two trace conjuncts hold on the ACCEPTED arm only (a Theorem Labs lane's G-B, with a
   counterexample: x = "[1] x" gives res = None with a trace that allocated, while a refused parse_noting FREES
   everything it took - the kit's post on None is `Permutation Lam' Lam /\ Permutation (ablocks ..) (ablocks ..) /\
   pj_zeroR`, so D = [] there and `map snd D = map .. (lsz tr)` would be false). On the None arm the cut keeps only
   the run itself; ec_doc_state's None arm carries D = [] and the zeroed node, which is what the kit's post gives. *)
Definition ec_parsed (E : ecx) (ok : list bool) (res : option jv) (tr : list ev) (D : list (Z * Z)) : Prop :=
  jr_run ReaderRes.jr_strtod (e_x E) ok = (res, tr) /\
  match res with
  | Some _ => Permutation (map snd D) (map Z.of_nat (ReaderRes.lsz tr)) /\ Z.of_nat (length D) = ReaderRes.nlive tr
  | None => True
  end.

(* the document at &doc: a tree t over the harness blocks D (rc = 0), or the zeroed node (rc = -1) *)
Definition ec_doc_state (fk : Z) (W : world segs) (mem : word -> option byte) (Lam : list (Z * Z))
  (res : option jv) (D : list (Z * Z)) : Prop :=
  match res with
  | Some t => Permutation Lam D /\ pj_nodeR segs (mrW W mem) (prh_lin Lam) (ec_doc fk) t D
  | None => Lam = [] /\ D = [] /\ pj_zeroR segs (mrW W mem) (ec_doc fk)
  end.

(* THE FREE ORDER (PJF-TIE; the model owner, 20:20Z: TRUE on both arms): pj_free's order list F of
   the reading's blocks D - pj_free's post-order over the tree at &doc (PRH_PjOrder.pj_foR at cut_free's depth
   DOC_D) - has, IN ORDER, the model's reader-side bulk sizes: pj_frees is jfv over the TEXT with the READER's block
   sizes (escaped-span strings, PjGrammar jr_string, preset_file.c:127). Not derivable from ec_doc_state (a tree's
   blocks are fixed there only up to Permutation of their sizes, ec_parsed). SUPPLIED by parse_noting's post (the kit's
   lemma, owner ruling 20:15Z: the kit owner owns it), KEPT by every row from cut_pno to cut_free exactly as ec_doc_state
   (PRH_PjOrder.pj_foR_frame over the tree's footprint), CONSUMED at cut_free by pj_free's position transfer
   (PRH_FnPj.prhPj_free_evs_supply_pjf). Aligned to the kit's texts (lib/A/PRH_PjOrder.v, lib/A/PRH_FnPj.v). *)
Definition ec_pjf (E : ecx) (fk : Z) (W : world segs) (mem : word -> option byte) (Lam D : list (Z * Z)) (t : jv)
  : Prop :=
  forall n, (PjTree.depth t <= n)%nat ->
    exists F, PRH_PjOrder.pj_foR segs (mrW W mem) (prh_lin Lam) n (ec_doc fk) D F /\
      map (fun b => snd b + cf_head) F = PresetReqAt.pj_frees (e_sm E) [] (e_x E).
(* on the reading's two arms: the accepted tree carries it; the zeroed node (D = []) carries nothing *)
Definition ec_pjf_res (E : ecx) (fk : Z) (W : world segs) (mem : word -> option byte) (Lam : list (Z * Z))
  (res : option jv) (D : list (Z * Z)) : Prop :=
  match res with Some t => ec_pjf E fk W mem Lam D t | None => True end.

(* ---------------------------------------------------------------------- *)
(* 7. THE CUT POINTS. *)
Definition cut_start (E : ecx) : world segs -> config -> Prop := fun W c =>
  ec_pre E /\ W = e_W E /\ c = cfg_at segs (@pa_sigma rc L PA AS_LLVMFuzzerTestOneInput) (e_regs E) (e_mem E) (e_md E).

(* +0x074: __asan_stack_malloc_1 has returned the fake frame fk in a0 (s2 not yet set). The frame is zero-shadowed
   and present (pcc_stack_malloc's post); the saved block and the GOT values are in place. *)
Definition cut_frame (E : ecx) (fk : Z) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own peak k,
  ec_at EC_AR_FRAME regs mem md c /\
  ec_inv E fk ly S Hp W mem md own [] peak (e_cnt E) (e_ran E) k (e_os E) (e_i0 E) 0%nat /\ Hp = [] /\
  e_cnt E + ec_ccut E 0 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 0 <= LIVE_MAX /\
  ec_saved E W mem /\
  zero_shadow (rdW W mem) SHADOW_OFF fk EC_FRAME_BYTES /\
  (forall a, fk <= a < fk + EC_FRAME_BYTES -> apresent (w_H W) mem a) /\
  getr regs 10 = w64 fk /\ getr regs 2 = w64 (e_A E) /\
  getr regs 3 = getr (e_regs E) 3 /\ getr regs 4 = getr (e_regs E) 4 /\
  getr regs 8 = w64 (e_sp0 E) /\ getr regs 9 = w64 (e_A E) /\
  getr regs 19 = w64 (e_n E) /\ getr regs 20 = w64 (e_p E) /\ getr regs 26 = w64 SHADOW_OFF.

(* +0x124: past the size guard (n <= 0x300000), the frame built, nothing taken *)
Definition cut_s1 (E : ecx) (fk : Z) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own peak k,
  ec_at EC_S1 regs mem md c /\
  ec_inv E fk ly S Hp W mem md own [] peak (e_cnt E) (e_ran E) k (e_os E) (e_i0 E) 0%nat /\ Hp = [] /\
  e_cnt E + ec_ccut E 1 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 1 <= LIVE_MAX /\
  ec_rk E fk regs /\ ec_frame E fk W mem /\ e_n E <= EC_NMAX.

(* +0x14c: check_no_overread has returned r (1 = memory ran out, the call ends: `bnez a0` -> EXIT) *)
Definition cut_cno (E : ecx) (fk : Z) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own peak cnt ran k r trp,
  ec_at EC_AR_CNO regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own [] peak cnt ran k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp))%nat ec_wk_cno /\ Hp = [] /\
  (r = 1 <-> ec_ranout E trp = true) /\
  cnt + ec_ccut E 2 <= e_cnt E + LCNT /\
  (* s9 holds g_own_ran_out's hi base from +0x124 on: the `lbu a1,-0x1c4(s9)` at +0x190 reads the cell through it,
     and ec_rk does not name x25 (a Theorem Labs lane's (1)) *)
  getr regs 25 = w64 (@pa_val rc L PA (A_HI 4)) /\
  blocks_bytes S + ec_lcut E 2 <= LIVE_MAX /\
  ec_rk E fk regs /\ ec_frame E fk W mem /\ e_n E <= EC_NMAX /\
  ec_most E W mem /\
  getr regs 10 = w64 r /\
  exists o, ec_own_is W mem o /\ ((r = 1 /\ (o = 1 \/ ran = 1)) \/ (r = 0 /\ o = 0 /\ ran = 0)).

(* +0x178: parse_noting has returned rc. s6 = live (0: nothing was live), s7 = the count before the reading *)
Definition cut_pno (E : ecx) (fk : Z) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own Lam peak cnt0 cnt k ok res tr D trp,
  ec_at EC_AR_PNO regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own Lam peak cnt 0 k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E))%nat ec_wk_pno /\
  ec_ranout E trp = false /\
  cnt + ec_ccut E 3 <= e_cnt E + LCNT /\
  getr regs 25 = w64 (@pa_val rc L PA (A_HI 4)) /\
  blocks_bytes S + ec_lcut E 3 <= LIVE_MAX /\
  ec_rkd E fk regs /\ ec_frame E fk W mem /\ e_n E <= EC_NMAX /\
  getr regs 22 = w64 0 /\ getr regs 23 = w64 cnt0 /\
  cnt = cnt0 + Z.of_nat (calls tr) /\
  ec_parsed E ok res tr D /\ ec_doc_state fk W mem Lam res D /\
  ec_pjf_res E fk W mem Lam res D /\
  getr regs 10 = w64 (match res with Some _ => 0 | None => -1 end) /\
  (* check_bounded_alloc's text takes `held <= PJ_ALLOC_BOUND size` and the ledger bounds the peak only below 2 ^ 64:
     the peak after the reset and the reading is within the input's bound (a Theorem Labs lane's (2)) *)
  peak <= PJ_ALLOC_BOUND (e_n E) /\
  (* the result is the model's reading when nothing ran out (parse_noting's post at g_fail_at = SIZE_MAX;
     a Theorem Labs lane's (3)) *)
  (res = ck_read (e_x E) /\ Z.of_nat (calls tr) = ck_ncalls (e_x E)) /\
  ec_most E W mem /\ ec_own_is W mem 0.

(* +0x1b8: check_as_written has returned r (1: memory ran out -> FREE; 0: -> +0x2c8). s8 = rc, s9 = the count
   after the reading, s7 = the count before it *)
Definition cut_caw (E : ecx) (fk : Z) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own Lam peak cnt0 cnt ran k ok res tr D r trp,
  ec_at EC_AR_CAW regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own Lam peak cnt ran k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))%nat ec_wk_caw /\
  ec_ranout E trp = false /\
  cnt + ec_ccut E 4 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 4 <= LIVE_MAX /\
  ec_rkd E fk regs /\ ec_frame E fk W mem /\ e_n E <= EC_NMAX /\
  getr regs 22 = w64 0 /\ getr regs 23 = w64 cnt0 /\
  getr regs 24 = w64 (match res with Some _ => 0 | None => -1 end) /\
  getr regs 25 = w64 (cnt0 + Z.of_nat (calls tr)) /\
  ec_parsed E ok res tr D /\ ec_doc_state fk W mem Lam res D /\
  ec_pjf_res E fk W mem Lam res D /\
  ec_most E W mem /\
  getr regs 10 = w64 r /\
  exists o, ec_own_is W mem o /\
    (r = 0 /\ o = 0 /\ ran = 0 /\ res = ck_read (e_x E) /\ Z.of_nat (calls tr) = ck_ncalls (e_x E)).

(* +0x1bc: FREE. Every live harness block is the document's; pj_free (&doc) frees them (D = [] on a zeroed node) *)
Definition cut_free (E : ecx) (fk : Z) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own Lam peak cnt k D trp t,
  ec_at EC_FREE regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own Lam peak cnt 0 k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t ++ ec_rej E ++ ec_sw E t))%nat ec_wk_free /\
  ec_ranout E trp = false /\
  cnt + ec_ccut E 10 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 10 <= LIVE_MAX /\
  ec_rkd E fk regs /\ ec_frame E fk W mem /\
  Permutation Lam D /\ pj_fdR segs (mrW W mem) (prh_lin Lam) DOC_D (ec_doc fk) D /\
  ec_pjf E fk W mem Lam D t /\
  (* the ACCEPTED arm of call_tail at THE SAME tree t as the index, and the size bound (L6Port's G1 / G2, owner 17:5xZ):
     with them the event after cut_free's index is call_tail's last piece [HBulk (pj_frees (e_sm E) [] (e_x E))] *)
  e_n E <= EC_NMAX /\ fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = Some t.

(* +0x2f4: check_reject_clean_starved (data, size, took, NULL) has returned on the refused arm; nothing is live and
   the node is zero; `j` EXIT *)
Definition cut_crs0 (E : ecx) (fk : Z) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own peak cnt k trp,
  ec_at EC_AR_CRS0 regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own [] peak cnt 0 k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rej E))%nat ec_wk_crs0 /\ Hp = [] /\
  ec_ranout E trp = false /\
  cnt + ec_ccut E 5 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 5 <= LIVE_MAX /\
  ec_rkd E fk regs /\ ec_frame E fk W mem /\
  (* the REFUSED arm of call_tail, and the size bound the arm equations need (a Theorem Labs lane on LL4j / LL4jB, owner
     17:5xZ: without it cut_crs0's index equals cut_exit's only on this arm) *)
  e_n E <= EC_NMAX /\ fst (PjGrammar.jr_run (e_sm E) (e_x E) []) = None.

(* +0x2f8: the accepted arm (rc = 0, check_as_written returned 0): the tree t is at &doc, s7 = took *)
Definition cut_acc (E : ecx) (fk : Z) (t : jv) (D : list (Z * Z)) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own Lam peak cnt k tk trp,
  ec_at EC_ACC regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own Lam peak cnt 0 k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))%nat ec_wk_caw /\
  ec_ranout E trp = false /\
  cnt + ec_ccut E 6 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 6 <= LIVE_MAX /\
  ec_rkd E fk regs /\ ec_frame E fk W mem /\ e_n E <= EC_NMAX /\
  getr regs 23 = w64 tk /\ tk = ck_ncalls (e_x E) /\ getr regs 24 = w64 0 /\
  ck_read (e_x E) = Some t /\ Permutation Lam D /\ pj_nodeR segs (mrW W mem) (prh_lin Lam) (ec_doc fk) t D /\
  ec_pjf E fk W mem Lam D t /\
  ec_most E W mem /\ ec_own_is W mem 0.

(* +0x300: read_members (&doc) has returned (its text: the kit, pending) *)
Definition cut_rm (E : ecx) (fk : Z) (t : jv) (D : list (Z * Z)) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own Lam peak cnt k tk trp,
  ec_at EC_AR_RM regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own Lam peak cnt 0 k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E))%nat ec_wk_rm /\
  ec_ranout E trp = false /\
  cnt + ec_ccut E 7 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 7 <= LIVE_MAX /\
  ec_rkd E fk regs /\ ec_frame E fk W mem /\ e_n E <= EC_NMAX /\
  getr regs 23 = w64 tk /\ tk = ck_ncalls (e_x E) /\
  ck_read (e_x E) = Some t /\ Permutation Lam D /\ pj_nodeR segs (mrW W mem) (prh_lin Lam) (ec_doc fk) t D /\
  ec_pjf E fk W mem Lam D t /\
  ec_most E W mem /\ ec_own_is W mem 0.

(* +0x308: check_round_trip (&doc) has returned r (1: memory ran out -> FREE, the starved check skipped) *)
Definition cut_crt (E : ecx) (fk : Z) (t : jv) (D : list (Z * Z)) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own Lam peak cnt ran k tk r trp,
  ec_at EC_AR_CRT regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own Lam peak cnt ran k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t))%nat ec_wk_crt /\
  ec_ranout E trp = false /\
  cnt + ec_ccut E 8 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 8 <= LIVE_MAX /\
  ec_rkd E fk regs /\ ec_frame E fk W mem /\ e_n E <= EC_NMAX /\
  getr regs 23 = w64 tk /\ tk = ck_ncalls (e_x E) /\
  ck_read (e_x E) = Some t /\ Permutation Lam D /\ pj_nodeR segs (mrW W mem) (prh_lin Lam) (ec_doc fk) t D /\
  ec_pjf E fk W mem Lam D t /\
  ec_most E W mem /\
  getr regs 10 = w64 r /\
  exists o, ec_own_is W mem o /\ (r = 0 /\ o = 0 /\ ran = 0).

(* +0x320: check_reject_clean_starved (data, size, took, &doc) has returned; `j` FREE.
   It carries `ck_read (e_x E) = Some t` as cut_acc / cut_rm / cut_crt do: without it the `j` to FREE cannot pay
   cut_free's pj_fdR at DOC_D - a tree of depth >= 34 at &doc makes that conjunct false, and nothing else in this cut
   bounds the depth (a Theorem Labs lane's counterexample on LL5d, 14:5xZ; the fix was decided by the owner). *)
Definition cut_crs1 (E : ecx) (fk : Z) (t : jv) (D : list (Z * Z)) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own Lam peak cnt k trp,
  ec_at EC_AR_CRS1 regs mem md c /\
  ec_invR WLE' E fk ly S Hp W mem md own Lam peak cnt 0 k (e_os E ++ [trp]) (e_i0 E + length (ec_cno_evs E trp ++ ec_pn E ++ ec_sc E ++ ec_rt E t ++ ec_rej E ++ ec_sw E t))%nat ec_wk_crs1 /\
  ec_ranout E trp = false /\
  cnt + ec_ccut E 9 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 9 <= LIVE_MAX /\
  ec_rkd E fk regs /\ ec_frame E fk W mem /\
  ck_read (e_x E) = Some t /\
  Permutation Lam D /\ pj_nodeR segs (mrW W mem) (prh_lin Lam) (ec_doc fk) t D /\
  ec_pjf E fk W mem Lam D t /\
  e_n E <= EC_NMAX.

(* +0x1c4: EXIT. Three predecessors: the size guard (+0x120), check_no_overread's r = 1 (+0x14c), pj_free's return
   (+0x1c4 is its return site) and the refused tail's `j` (+0x2f4). Nothing taken is live (Lam = [], Hp = []). *)
Definition cut_exit (E : ecx) (fk : Z) : world segs -> config -> Prop := fun W c =>
  exists ly S Hp regs mem md own peak cnt ran k trp,
  ec_at EC_EXIT regs mem md c /\
  ec_inv E fk ly S Hp W mem md own [] peak cnt ran k (e_os E ++ [trp]) (e_i0 E + length (ec_call_evs E trp))%nat ec_wk_exit /\ Hp = [] /\
  cnt + ec_ccut E 11 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 11 <= LIVE_MAX /\
  ec_rk E fk regs /\ ec_frame E fk W mem.
(* cut_exit OVER A WORLD RELATION R: reached on BOTH sides of a free (the size guard before check_no_overread; the
   r = 1 arm, the refused tail and pj_free after it), so cut_exit keeps its name and body at wle (L0b's arm) and the
   lanes after a free reach cut_exitR WLE' (a COPY of the body at ec_invR R; cut_exit_R_wle by reflexivity).
   cut_exit_wle' lifts L0b's arm across the first free. *)
Definition cut_exitR (R : world segs -> world segs -> Prop) (E : ecx) (fk : Z) : world segs -> config -> Prop :=
  fun W c =>
  exists ly S Hp regs mem md own peak cnt ran k trp,
  ec_at EC_EXIT regs mem md c /\
  ec_invR R E fk ly S Hp W mem md own [] peak cnt ran k (e_os E ++ [trp]) (e_i0 E + length (ec_call_evs E trp))%nat ec_wk_exit /\ Hp = [] /\
  cnt + ec_ccut E 11 <= e_cnt E + LCNT /\
  blocks_bytes S + ec_lcut E 11 <= LIVE_MAX /\
  ec_rk E fk regs /\ ec_frame E fk W mem.
Lemma cut_exit_R_wle : forall E fk, cut_exit E fk = cut_exitR (@wle segs) E fk.
Proof. reflexivity. Qed.
Lemma cut_exit_wle' : forall E fk W c, cut_exit E fk W c -> cut_exitR WLE' E fk W c.
Proof.
  intros E fk W c (ly & S & Hp & regs & mem & md & own & peak & cnt & ran & k & trp & Hat & Hinv & H).
  exists ly, S, Hp, regs, mem, md, own, peak, cnt, ran, k, trp. split; [exact Hat|]. split; [|exact H].
  exact (ec_inv_wle' E fk ly S Hp W mem md own [] peak cnt ran k _ _ _ Hinv).
Qed.

(* THE RETURN (+0x2c4 `ret` executed: pc = the caller's ra): the call's journal from the entry at the EMPTY
   footprint, the fake frame released (own = []), every callee-saved register back, a0 = 0, the blocks as at entry,
   the ledger at rest (Lam = [], g_fail_at = SIZE_MAX) with the count moved by at most LCNT, the stdio half kept,
   the payload bytes kept, P8's room one model call later, memnorm kept *)
Definition cut_ret (E : ecx) : world segs -> config -> Prop := fun W' c =>
  exists ly' S' regs' mem' md' k peak' cnt' ran',
  ec_at (raZ (e_regs E)) regs' mem' md' c /\
  (* the call's journal at its WILD BUDGET (<= K_LLVMF, the slot post's), at wle' (the call frees: WLE') *)
  (exists WS, ajournal_xwR (SK := SK) segs B PST ARx WLE' LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
     (e_md E) [] ly' S' [] W' mem' md' k WS /\ YCbqGwild.wbudget [] ec_wk_exit WS) /\
  aregs_preserved (e_regs E) regs' /\ getr regs' 10 = w64 0 /\
  Permutation (ablocks B ly' S') (ablocks B (e_ly E) (e_S E)) /\
  (exists most' own', @prh_ledger rc cp PI L PA B ly' S' [] W' mem' [] peak' cnt' SIZE_MAX ran' most' own') /\
  e_cnt E <= cnt' <= e_cnt E + LCNT /\
  EC_SIO (rdW W' mem') /\
  @room_live_cf RL S' /\
  (* the exact position at the end of this call's model events: iface_room_post_of_pos_end's premise *)
  (exists (trp : ec_trip) hist, PresetRoomPos.iface_room_pos (e_sm E) (e_x E) (e_os E ++ [trp])
     (e_i0 E + length (ec_call_evs E trp))%nat (e_H0 E) hist S') /\
  (forall i, 0 <= i < e_n E -> rdW W' mem' (e_p E + i) = rdW (e_W E) (e_mem E) (e_p E + i)) /\
  YAkMemnorm.memnorm segs mem'.

(* ---------------------------------------------------------------------- *)
(* 8. THE CALLEE TEXTS THIS BODY CALLS (the kit's, at every float state), at this body's call-site contexts: the site
      alone, or the site over the entry's own return address (the frame chain s0 = sp0 gives). No run data words: the kit's
      batch removed DW (owner 22:03Z). *)
Record ec_texts : Prop := MkEcTexts {
  et_fuzz_alloc_ran_out_reset : forall fy : YK11.FPState,
    @tfuzz_alloc_ran_out_reset_specX fy rc cp PI RL L PA B ARx SK;
  et_fuzz_alloc_most : forall fy : YK11.FPState, @tfuzz_alloc_most_specX fy rc cp PI RL L PA B ARx SK;
  (* The batch kit's text (the walk's entry-keyed granted form is DERIVED from it: Ent102OfPost.v) *)
  et_check_no_overread : forall fy : YK11.FPState,
    @tcheck_no_overread_specX fy rc ci cp PI RL L PA B ARx SK ec_ctx0;
  et_fuzz_alloc_live : forall fy : YK11.FPState, @tfuzz_alloc_live_specX fy rc cp PI RL L PA B ARx SK;
  et_fuzz_alloc_count : forall fy : YK11.FPState, @tfuzz_alloc_count_specX fy rc cp PI RL L PA B ARx SK;
  et_fuzz_alloc_peak_reset : forall fy : YK11.FPState, @tfuzz_alloc_peak_reset_specX fy rc cp PI RL L PA B ARx SK;
  (* The batch kit's text (the walk's entry-keyed granted form is DERIVED from it: Ent102OfPost.v) *)
  et_parse_noting : forall fy : YK11.FPState,
    @tparse_noting_specX fy rc ci cp PI RL L PA B ARx SK ec_ctx0;
  et_fuzz_alloc_peak : forall fy : YK11.FPState, @tfuzz_alloc_peak_specX fy rc cp PI RL L PA B ARx SK;
  et_check_bounded_alloc : forall fy : YK11.FPState, @tcheck_bounded_alloc_specX fy rc cp PI RL L PA B ARx SK;
  et_fuzz_alloc_ran_out : forall fy : YK11.FPState, @tfuzz_alloc_ran_out_specX fy rc cp PI RL L PA B ARx SK;
  et_check_as_written : forall fy : YK11.FPState,
    @tcheck_as_written_specX fy rc ci cp PI RL L PA B ARx SK ec_ctx0;
  et_pj_free : forall fy : YK11.FPState,
    @tpj_free_specX fy rc ci cp PI RL L PA B ARx SK ec_ctx0 DOC_D;
  et_check_reject_clean : forall fy : YK11.FPState, @tcheck_reject_clean_specX fy rc cp PI RL L PA B ARx SK;
  et_check_reject_clean_starved : forall fy : YK11.FPState,
    @tcheck_reject_clean_starved_specX fy rc ci cp PI RL L PA B ARx SK ec_ctx0;
  et_read_members : forall fy : YK11.FPState, @tread_members_specX fy rc cp PI RL L PA B ARx SK;
  et_check_round_trip : forall fy : YK11.FPState,
    @tcheck_round_trip_specX fy rc ci cp PI RL L PA B ARx SK ec_ctx0 EC_A_MOD_AT EC_A_STAMP;
  (* the stack the interface budgets for this call covers the kit's table for this body (the kit BATCH 1: the #102 callees) *)
  et_stk : @STK_LLVMFuzzerTestOneInput PI <= LLVMF_STK
}.

(* the frame-area half: __asan_stack_malloc_1 of class 1 and its inline release (the interface's pcc_stack_malloc
   / pcc_stack_free at the instance), at every float state. The malloc half is stated in the unit's MEMNORM-KEEPING
   form (the convention in the released file lib/Reusable/YCbqGmn.v, deleted in this series, whose list names __asan_stack_malloc_1): astack_malloc_realizes_cf (YG0dcf.v:556)
   word for word, plus the keep implication (memnorm segs mem -> memnorm segs mem') in its post. Without it memnorm
   after the frame call is not derivable (the cf post constrains mem' only through aview; SRr is a CPS predicate, so
   a separate keep fact cannot be conjoined; L0Lane, 13:3xZ). ec_stack_malloc_cfm -> astack_malloc_realizes_cf by
   SRr_mono. The release half is the walk's own store (`sb zero,0(a0)` at +0x23c): astack_free_law_cf keeps the
   relation and the walk's own memnorm_store keeps memnorm. *)
Definition ec_stack_malloc_cfm (fy : YK11.FPState) (cid : Z) : Prop :=
  forall ly S Hp (W : world segs) regs mem md pos S',
    ecall_pre_cf (cp := cp) segs B ly S Hp W regs mem md ->
    count_cid cid (frames S) < fs_frames cid ->
    apath (stack_malloc cid S) [] (PFake cid pos, S') ->
    SRr segs W (@cfg_at fy segs (pc_stack_malloc (as_code B) cid) regs mem md)
      (fun W' c' => W' = W /\
         exists regs' mem' md',
           c' = @cfg_at fy segs (raZ regs) regs' mem' md' /\
           ARcf (cp := cp) segs B ly S' Hp W mem' md' /\
           aregs_preserved regs regs' /\ same_but_materialized md md' /\
           getr regs' 10 = w64 (frame_addr ly cid pos) /\
           zero_shadow (aview segs (w_H W) mem') SHADOW_OFF (frame_addr ly cid pos) (fs_frame_bytes cid) /\
           rdword (aview segs (w_H W) mem') (frame_addr ly cid pos + fs_frame_bytes cid - 8) =
             Some (flag_addr ly cid pos) /\
           (forall a, frame_addr ly cid pos <= a < frame_addr ly cid pos + fs_frame_bytes cid ->
              apresent (w_H W) mem' a) /\
           (forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a ->
              ~ spZ regs - ESTACK <= a < spZ regs -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) /\
           (forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a) /\
           (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem')).
Definition ec_frame_area : Prop :=
  (forall fy : YK11.FPState, ec_stack_malloc_cfm fy LLVMF_FS_CLASS) /\
  astack_free_law_cf (rc := rc) (cp := cp) segs B.

(* the m-form implies the interface's form (the keep conjunct dropped) *)
Lemma ec_stack_malloc_cfm_cf : forall fy cid, ec_stack_malloc_cfm fy cid ->
  astack_malloc_realizes_cf (fx := fy) (rc := rc) (cp := cp) segs B cid.
Proof.
intros fy cid H ly S Hp W regs mem md pos S' Hpre Hc Hp'.
eapply SRr_mono; [exact (H ly S Hp W regs mem md pos S' Hpre Hc Hp')|].
intros W' c' _ (HW & regs' & mem' & md' & Hc' & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & _).
split; [exact HW|]. exists regs', mem', md'. repeat (split; [eassumption|]). exact H9.
Qed.

(* ---------------------------------------------------------------------- *)
(* 9. THE SEGMENT STATEMENTS ("from this cut, SRr to the next"; from cut_s1 on, SRr' over the re-hiding zone). *)
Definition ec_lane (P Q : world segs -> config -> Prop) : Prop := forall W c, P W c -> SRr segs W c Q.
(* ec_lane OVER A WORLD RELATION R (YA0nH.SRrG): used on BOTH sides of a free (L0a / L0b before check_no_overread,
   every later lane across or after it), so ec_lane keeps its name and body as the instance at wle (YA0n.SRr IS SRrG at
   wle: ec_lane_R_wle, by reflexivity) and every lane from L1 on is ec_laneR at wle' (WLE'), i.e. SRr' segs RZ_cf
   (YA0nH.v:163). ec_lane_wle' lifts a plain lane into it (YA0nH.SRr_SRr'). *)
Definition ec_laneR (R : world segs -> world segs -> Prop) (P Q : world segs -> config -> Prop) : Prop :=
  forall W c, P W c -> SRrG segs R W c Q.
Lemma ec_lane_R_wle : forall P Q, ec_lane P Q = ec_laneR (@wle segs) P Q.
Proof. reflexivity. Qed.
Lemma ec_lane_wle' : forall P Q, ec_lane P Q -> ec_laneR WLE' P Q.
Proof. intros P Q H W c HP. exact (SRr_SRr' segs (@YGcfRehidePost.RZ_cf rc) W c Q (H W c HP)). Qed.
(* THE REQUEST BOUND: every ledger request of the check_* subtrees on an input of at most PRESET_FILE_MAX_BYTES is
   within g_most = PJ_ALLOC_BOUND (size). The kit's check texts take it per call (check_no_overread: RQ_pj_parse x <= most;
   check_reject_clean_starved: RQ_pj_parse x and, for the tree, RQW t p; check_round_trip: RQA_crt t). A pure
   statement about the input; NOT a premise: lib/A/Ent102ReqA.v ec_req_bound_holds proves it from a Theorem Labs lane's
   lib/Spec/PjReqBoundW.v, and the segments cite that lemma at the call sites. *)
Definition ec_req_bound : Prop :=
  forall x : list Z, Z.of_nat (length x) <= EC_NMAX ->
  PRH_FnPj.RQ_pj_parse x <= PJ_ALLOC_BOUND (Z.of_nat (length x)) /\
  (forall t, ck_read x = Some t ->
     RQW t true <= PJ_ALLOC_BOUND (Z.of_nat (length x)) /\ RQW t false <= PJ_ALLOC_BOUND (Z.of_nat (length x)) /\
     RQA_crt t <= PJ_ALLOC_BOUND (Z.of_nat (length x)) /\
     (* check_round_trip's own request premise (PRH_FnCheck.v:944): the largest single request of its subtree is
        below the allocator's per-request ceiling. a Theorem Labs lane on LL5b, owner's decision 15:4xZ: a conjunct of
        this pure statement, NOT an ec_img field. The margin is thin at MAXB (about 5.28e8 against
        cf_malloc_max - cf_head = 5.36e8) and RQ_crt's TX_req part has no bound in lib yet, so Ent102ReqA.v carries
        it as a NAMED premise until a Theorem Labs lane's measurement and lemma land. If it is FALSE at MAXB, the refusal
        arm of check_round_trip becomes reachable and cut_crt gains that case. *)
     RQ_crt t + cf_head < cf_malloc_max).
(* THE UNIVERSE (the kit's prh_univ_closure, one per call-site context this body offers; no DW since the kit's batch, owner
   22:03Z: clause 4 is the fixed code word (4a) or inU of the instance universe (4b)): every text that reaches an
   allocator takes it as a premise at its own CTX0. It is a fact of the instance's trace universe, not of a callee:
   the instance discharges it (owners a Theorem Labs lane / a Theorem Labs lane's univcore / a Theorem Labs lane). *)
Record ec_univ : Prop := MkEcUniv {
  eu_cno : @prh_univ_closure PI B ci ec_ctx0;
  eu_pno : @prh_univ_closure PI B ci ec_ctx0;
  eu_caw : @prh_univ_closure PI B ci ec_ctx0;
  eu_pjf : @prh_univ_closure PI B ci ec_ctx0;
  eu_crs : @prh_univ_closure PI B ci ec_ctx0;
  eu_crt : @prh_univ_closure PI B ci ec_ctx0
}.
(* A RECORD, so that adding a part never breaks a row: every lane takes its parts by NAME (ech_texts, ech_img, ...),
   never by position (owner's decision 15:3xZ, after a row destructured the conjunction positionally). *)
(* NO REFUSAL at a consumer allocation of the run (owner 17:5xZ; G1-G3 of a Theorem Labs lane, A / B of L4Lane): after
   cut_cno the walk keeps only the no-refusal arms, and the kit's refusal arms (check_as_written r = 1 with own = 1,
   check_round_trip r = 1, check_reject_clean_starved ran' = 1, parse_noting ran <> 0) are closed by this ONE shared
   fact in the ALLOCATOR-CONTRACT form - never a state invariant (which ec_inv's satisfiable states would refute).
   It IS the interface's preset_no_refusal (lib/A/PresetCfnA.v:666-680, a proved lemma: P8's no_null_preset over
   YGcfRoom.malloc_cf_null_full), word for word, at this call's model (e_sm E) (e_x E) (e_H0 E): a primary malloc_cf
   made at a consumer allocation of the run returns NULL only on an environment refusal (grant flag false). On a
   realized path every kernel ask is granted (amalloc_realizes_cf, YG0dcf.v:132-133), so together: no NULL at a
   consumer allocation. ec_allocs_follow is the interface's run_allocs_follow (PresetCfnA.v:536-538) verbatim (this
   file cannot Require the interface). Satisfiable: the seam discharges ec_noref by preset_no_refusal itself. It
   reaches a callee's refusal arm through that callee's kit text, which must take it (or the kit's prh_granted on its
   oracle, discharged from it) and give ran' = ran / r = 0. *)
Definition ec_allocs_follow (E : ecx) (S : astate) : Prop :=
  exists (os : list ec_trip) (i : nat) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos (e_sm E) (e_x E) os i (e_H0 E) hist S /\
    List.nth i (PresetRun.hcons (e_sm E) (e_x E) os) false = true /\
    PresetSite17.alloc_at (PresetRun.hruns (e_sm E) (e_x E) os) i.
Definition ec_noref : Prop :=
  forall (E : ecx) U (S : astate) (n : Z) (tr : list Z) (ns : bool),
    YG01cf.Wf_cf U S -> Z.of_nat (length (e_x E)) <= PresetReqAt.MAXB -> ec_allocs_follow E S ->
    YG00.from_primary n = true ->
    YGcfRoom.rpost ns (YG00cf.malloc_cf n tr S) (fun g r => fst r = PNull -> g = false).

Record ec_hyps : Prop := MkEcHyps {
  ech_frame_area : ec_frame_area;
  ech_texts : ec_texts;
  ech_img : ec_img;
  ech_univ : ec_univ;
  ech_ccut_ok : ec_ccut_ok;
  ech_lcut_ok : ec_lcut_ok;
  ech_pay : ec_pay;
  ech_noref : ec_noref;
  (* THE HULL BUDGET AT A POSITION (route (b) of the allocator hull premise; the Step-1 texts take
     `PresetHullBudget.hull_budget S Eg` at check_no_overread / parse_noting / check_as_written): at any run position of
     at most 4 calls, a granted list of at most one call's sections is within the cf layer's hull. Stated at this
     Section's generic cp; the composition discharges it ONCE at cp := CfParams_preset by
     PresetHullPay.hull_budget_of_room_pos (lib/A/PresetHullPay.v:73). The segments cite it with PresetHullPay's
     hull_nt_* bounds (:91-123) and the cut's position (ec_inv's iface_room_pos, length (e_os E ++ [trp]) <= 4 from
     ec_pre's `length (e_os E) <= 3`). *)
  ech_hull_pay : forall sm x os i H0 hist S Eg, (length os <= 4)%nat ->
    PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
    Z.of_nat (PresetSecTotal.nsec Eg) <= PresetSecTotal.NCALL -> PresetSecTotal.tsec Eg <= PresetSecTotal.TCALL ->
    @PresetHullBudget.hull_budget cp S Eg
}.

(* L0a: +0x000 .. +0x070 (the prologue, the GOT loads, the use-after-return test) and the class-1 frame call *)
Definition seg_L0a_stmt : Prop :=
  forall E, ec_hyps -> ec_lane (cut_start E) (fun W c => exists fk, cut_frame E fk W c).
(* L0b: +0x074 .. +0x120: s2 = s11 = fk, the slot [A+16], the frame header, the shadow, the size guard *)
Definition seg_L0b_stmt : Prop :=
  forall E fk, ec_hyps -> ec_lane (cut_frame E fk) (fun W c => cut_s1 E fk W c \/ cut_exit E fk W c).
(* L1: +0x124 .. +0x148: g_own_ran_out := 0, fuzz_alloc_ran_out_reset, fuzz_alloc_most (PJ_ALLOC_BOUND n),
   check_no_overread. WAITS for the kit's tfuzz_alloc_most_specX and the g_own_ran_out / g_most PST cells. *)
Definition seg_L1_stmt : Prop :=
  forall E fk, ec_hyps -> ec_laneR WLE' (cut_s1 E fk) (cut_cno E fk).
(* L2: +0x14c .. +0x174: the r = 1 arm to EXIT; fuzz_alloc_live, fuzz_alloc_count, fuzz_alloc_peak_reset,
   parse_noting *)
Definition seg_L2_stmt : Prop :=
  forall E fk, ec_hyps -> ec_laneR WLE' (cut_cno E fk) (fun W c => cut_pno E fk W c \/ cut_exitR WLE' E fk W c).
(* L3: +0x178 .. +0x1b4: fuzz_alloc_peak, check_bounded_alloc, fuzz_alloc_count, the inlined out_of_memory (two
   arms to FREE), check_as_written *)
Definition seg_L3_stmt : Prop :=
  forall E fk, ec_hyps -> ec_laneR WLE' (cut_pno E fk) (fun W c => cut_caw E fk W c \/ cut_free E fk W c).
(* L4: +0x1b8 .. +0x2f0: r = 1 -> FREE; rc != 0 -> check_reject_clean, check_reject_clean_starved (.., NULL);
   rc = 0 -> the accepted arm *)
Definition seg_L4_stmt : Prop :=
  forall E fk, ec_hyps ->
  ec_laneR WLE' (cut_caw E fk) (fun W c => cut_free E fk W c \/ cut_crs0 E fk W c \/ exists t D, cut_acc E fk t D W c).
(* L4j: +0x2f4 `j` EXIT *)
Definition seg_L4j_stmt : Prop :=
  forall E fk, ec_hyps -> ec_laneR WLE' (cut_crs0 E fk) (cut_exitR WLE' E fk).
(* L5a: read_members (&doc). WAITS for the kit's tread_members_specX. *)
Definition seg_L5a_stmt : Prop :=
  forall E fk t D, ec_hyps -> ec_laneR WLE' (cut_acc E fk t D) (cut_rm E fk t D).
(* L5b: check_round_trip (&doc) *)
Definition seg_L5b_stmt : Prop :=
  forall E fk t D, ec_hyps -> ec_laneR WLE' (cut_rm E fk t D) (cut_crt E fk t D).
(* L5c: r = 1 -> FREE; r = 0 -> check_reject_clean_starved (data, size, took, &doc) *)
Definition seg_L5c_stmt : Prop :=
  forall E fk t D, ec_hyps ->
  ec_laneR WLE' (cut_crt E fk t D) (fun W c => cut_free E fk W c \/ cut_crs1 E fk t D W c).
(* L5d: +0x320 `j` FREE *)
Definition seg_L5d_stmt : Prop :=
  forall E fk t D, ec_hyps -> ec_laneR WLE' (cut_crs1 E fk t D) (cut_free E fk).
(* L6f: FREE: pj_free (&doc) *)
Definition seg_L6f_stmt : Prop :=
  forall E fk, ec_hyps -> ec_laneR WLE' (cut_free E fk) (cut_exitR WLE' E fk).
(* L6x: EXIT +0x1c4 .. +0x2c4: shadow 0xf8 over doc, the free magic, the inline release (0xf5 x16, the flag byte
   := 0), a0 = 0, the epilogue, `ret` *)
Definition seg_L6x_stmt : Prop :=
  forall E fk, ec_hyps -> ec_laneR WLE' (cut_exitR WLE' E fk) (cut_ret E).

(* ---------------------------------------------------------------------- *)
(* 10. THE COMPOSITION (L7): the lanes chained are the walk from the entry to the return. The instantiation file
       turns it into the RE-CUT interface's preset_lib_x_stmt (header, "THE SEAM"). *)
Definition entry_A_of_segs_stmt : Prop :=
  seg_L0a_stmt -> seg_L0b_stmt -> seg_L1_stmt -> seg_L2_stmt -> seg_L3_stmt -> seg_L4_stmt -> seg_L4j_stmt ->
  seg_L5a_stmt -> seg_L5b_stmt -> seg_L5c_stmt -> seg_L5d_stmt -> seg_L6f_stmt -> seg_L6x_stmt ->
  forall E, ec_hyps -> ec_laneR WLE' (cut_start E) (cut_ret E).

(* THE JOURNAL HELPERS BELOW, OVER A WORLD RELATION R (suffix R): the cuts before check_no_overread carry the journal at
   wle, every later cut at wle' (WLE'), so each helper has an R form (the engine's R forms, YCbqG.v / YCbqGwild.v),
   a COPY of the plain helper's proof over them, beside the plain helper, which keeps its body. *)
(* THE ROOM OF A BUDGETED CALL (for the rows; the kit owner 02:00Z): from ec_pre's entry room at K_LLVMF and the cut's journal at
   its spent budget wk, the callee F has its room prh_wk F whenever wk + prh_wk F <= K_LLVMF (ec_wk_values). *)
Lemma ec_room_atR : forall (R : world segs -> world segs -> Prop) (E : ecx) own ly S Hp W mem md k WS (wk : nat)
  (F : prh_fn),
  ec_pre E ->
  ajournal_xwR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  YCbqGwild.wbudget [] wk WS -> (wk + prh_wk F <= YCbqGwild.K_LLVMF)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F) (st_depot S).
Proof.
  intros R E own ly S Hp W mem md k WS wk F Hpre HJ Hwb Hle.
  assert (Hr : YCbqGwild.wild_room (as_universe B) [] YCbqGwild.K_LLVMF (st_depot (e_S E))).
  { unfold ec_pre in Hpre. repeat (match type of Hpre with _ /\ _ => apply proj2 in Hpre end). exact Hpre. }
  unfold YCbqGwild.wbudget in Hwb.
  assert (Hk : (YCbqGwild.wfresh [] WS <= YCbqGwild.K_LLVMF)%nat) by lia.
  pose proof (YCbqGwild.ajournal_xw_roomR (SK := SK) segs B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hr Hk)
    as Hr'.
  eapply YCbqGwild.wild_room_le; [|exact Hr'].
  revert Hwb Hle. generalize (YCbqGwild.wfresh [] WS) (prh_wk F) YCbqGwild.K_LLVMF. intros a b c H1 H2. lia.
Qed.
Lemma ec_room_at : forall (E : ecx) own ly S Hp W mem md k WS (wk : nat) (F : prh_fn),
  ec_pre E ->
  ajournal_xw (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  YCbqGwild.wbudget [] wk WS -> (wk + prh_wk F <= YCbqGwild.K_LLVMF)%nat ->
  YCbqGwild.wild_room (as_universe B) [] (prh_wk F) (st_depot S).
Proof.
  intros E own ly S Hp W mem md k WS wk F Hpre HJ Hwb Hle.
  assert (Hr : YCbqGwild.wild_room (as_universe B) [] YCbqGwild.K_LLVMF (st_depot (e_S E))).
  { unfold ec_pre in Hpre. repeat (match type of Hpre with _ /\ _ => apply proj2 in Hpre end). exact Hpre. }
  unfold YCbqGwild.wbudget in Hwb.
  assert (Hk : (YCbqGwild.wfresh [] WS <= YCbqGwild.K_LLVMF)%nat) by lia.
  pose proof (YCbqGwild.ajournal_xw_room (SK := SK) segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hr Hk)
    as Hr'.
  eapply YCbqGwild.wild_room_le; [|exact Hr'].
  revert Hwb Hle. generalize (YCbqGwild.wfresh [] WS) (prh_wk F) YCbqGwild.K_LLVMF. intros a b c H1 H2. lia.
Qed.

(* THE PLAIN JOURNAL AT A ZERO BUDGET (for the rows: a cut whose spent budget is 0, and any step that composes with an
   empty-budget call rule): a journal at a budget WS with wfresh [] WS = 0 is the plain journal. *)
Lemma ec_journal_plainR : forall (R : world segs -> world segs -> Prop) (E : ecx) own ly S Hp W mem md k WS,
  ajournal_xwR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  YCbqGwild.wbudget [] 0 WS ->
  ajournal_xR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k.
Proof.
  intros R E own ly S Hp W mem md k WS HJ Hwb.
  unfold ajournal_xR, ajournal_xwR in *.
  apply (YCbqG.ajx_budgetR (B := B) (PST := PST) (ARx := ARx) (R := R) (WS := WS) []); [exact HJ|].
  unfold YCbqGwild.wbudget in Hwb.
  pose proof (YCbqGwild.wfresh_zero_incl [] WS ltac:(lia)) as Hnil.
  intros a Ha. apply in_app_iff. pose proof (YCbqG.ajxR_wild HJ a Ha) as Hin.
  apply in_app_iff in Hin as [Hin | Hin]; [left; exact Hin | destruct (Hnil _ Hin)].
Qed.
Lemma ec_journal_plain : forall (E : ecx) own ly S Hp W mem md k WS,
  ajournal_xw (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  YCbqGwild.wbudget [] 0 WS ->
  ajournal_x (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k.
Proof.
  intros E own ly S Hp W mem md k WS HJ Hwb.
  unfold ajournal_x, ajournal_xw in *.
  apply (YCbqG.ajx_budget (B := B) (PST := PST) (ARx := ARx) (WS := WS) []); [exact HJ|].
  unfold YCbqGwild.wbudget in Hwb.
  pose proof (YCbqGwild.wfresh_zero_incl [] WS ltac:(lia)) as Hnil.
  intros a Ha. apply in_app_iff. pose proof (YCbqG.ajx_wild HJ a Ha) as Hin.
  apply in_app_iff in Hin as [Hin | Hin]; [left; exact Hin | destruct (Hnil _ Hin)].
Qed.

(* THE BUDGET ADAPTER for a row whose own code makes no wild trace (the engine's rebase / unbase0, YCbqGwild.v:387,
   :440): take the cut's budgeted journal to the PLAIN journal with the entry depot moved to the cut's (every other
   conjunct is unchanged; set_depot is a record literal, so a projection of it reduces by cbn), run the row's own
   plain steps, and give the next cut's journal at the SAME budget. *)
Lemma ec_journal_rebaseR : forall (R : world segs -> world segs -> Prop) (E : ecx) own ly S Hp W mem md k WS,
  ajournal_xwR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  ajournal_xR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (YG00.set_depot (st_depot S) (e_S E)) []
    (e_W E) (e_mem E) (e_md E) own ly S Hp W mem md k.
Proof.
  intros R E own ly S Hp W mem md k WS HJ.
  exact (YCbqGwild.ajournal_xw_rebaseR segs B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
Qed.
Lemma ec_journal_rebase : forall (E : ecx) own ly S Hp W mem md k WS,
  ajournal_xw (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  ajournal_x (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (YG00.set_depot (st_depot S) (e_S E)) []
    (e_W E) (e_mem E) (e_md E) own ly S Hp W mem md k.
Proof. intros E own ly S Hp W mem md k WS HJ. exact (YCbqGwild.ajournal_xw_rebase segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ). Qed.

Lemma ec_journal_unbaseR : forall (R : world segs -> world segs -> Prop) (E : ecx) own ly S Hp W mem md k WS
  ly' S' Hp' W' mem' md' k' own',
  ajournal_xwR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  ajournal_xR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (YG00.set_depot (st_depot S) (e_S E)) []
    (e_W E) (e_mem E) (e_md E) own' ly' S' Hp' W' mem' md' k' ->
  ajournal_xwR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own'
    ly' S' Hp' W' mem' md' k' WS.
Proof.
  intros R E own ly S Hp W mem md k WS ly' S' Hp' W' mem' md' k' own' HJ HJ'.
  exact (YCbqGwild.ajournal_xw_unbase0R segs B PST ARx R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ'
    (YCbqG.ajxR_wild HJ)).
Qed.
Lemma ec_journal_unbase : forall (E : ecx) own ly S Hp W mem md k WS ly' S' Hp' W' mem' md' k' own',
  ajournal_xw (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  ajournal_x (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (YG00.set_depot (st_depot S) (e_S E)) []
    (e_W E) (e_mem E) (e_md E) own' ly' S' Hp' W' mem' md' k' ->
  ajournal_xw (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own'
    ly' S' Hp' W' mem' md' k' WS.
Proof.
  intros E own ly S Hp W mem md k WS ly' S' Hp' W' mem' md' k' own' HJ HJ'.
  exact (YCbqGwild.ajournal_xw_unbase0 segs B PST ARx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ'
    (YCbqG.ajx_wild HJ)).
Qed.

(* ONE HOME for the no-call step every segment repeats (parent 02:4xZ, after a Theorem Labs lane wrote it twice): the cut's
   budgeted journal across a stretch with NO call - materialize the model, keep the budget, and grow the spent budget to
   the next cut's (the engine's rebase / materialize / unbase0, YCbqG.v:850 and YCbqGwild.v:387 / :440). *)
Lemma ec_inv_wk_growR : forall (R : world segs -> world segs -> Prop) {hl : Z} (LAWS : AR_laws_x segs B ARx hl)
  (E : ecx) own ly S Hp W mem md k WS (wk wk' : nat) X,
  ajournal_xwR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  YCbqGwild.wbudget [] wk WS -> (wk <= wk')%nat ->
  exists WS', ajournal_xwR (SK := SK) segs B PST ARx R LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
    (e_md E) own ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) k WS' /\ YCbqGwild.wbudget [] wk' WS'.
Proof.
  intros R hl LAWS E own ly S Hp W mem md k WS wk wk' X HJ Hwb Hle.
  exists WS. split; [|unfold YCbqGwild.wbudget in *; lia].
  apply (ec_journal_unbaseR R E own ly S Hp W mem md k WS); [exact HJ|].
  eapply (YCbqG.ajournal_x_materializeR segs B PST ARx LAWS (@pa_segs_low rc L PA) R).
  exact (ec_journal_rebaseR R E own ly S Hp W mem md k WS HJ).
Qed.
Lemma ec_inv_wk_grow : forall {hl : Z} (LAWS : AR_laws_x segs B ARx hl)
  (E : ecx) own ly S Hp W mem md k WS (wk wk' : nat) X,
  ajournal_xw (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E) (e_md E) own
    ly S Hp W mem md k WS ->
  YCbqGwild.wbudget [] wk WS -> (wk <= wk')%nat ->
  exists WS', ajournal_xw (SK := SK) segs B PST ARx LLVMF_STK (e_sp0 E) [] (e_ly E) (e_S E) [] (e_W E) (e_mem E)
    (e_md E) own ly S Hp W mem (with_vm_backing (m_vm_lazy md) X md) k WS' /\ YCbqGwild.wbudget [] wk' WS'.
Proof.
  intros hl LAWS E own ly S Hp W mem md k WS wk wk' X HJ Hwb Hle.
  exists WS. split; [|unfold YCbqGwild.wbudget in *; lia].
  apply (ec_journal_unbase E own ly S Hp W mem md k WS); [exact HJ|].
  eapply (YCbqG.ajournal_x_materialize segs B PST ARx LAWS (@pa_segs_low rc L PA)). exact (ec_journal_rebase E own ly S Hp W mem md k WS HJ).
Qed.

End E.
