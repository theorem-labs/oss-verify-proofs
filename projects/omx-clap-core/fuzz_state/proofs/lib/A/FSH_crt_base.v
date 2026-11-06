(* check_round_trip (fs.asan 0x81a9c, 667 insns), build A: the ONE interface the four segment files of its walk share
   (lib/A/FSH_crt_segA.v .. FSH_crt_segD.v). Definitions only, plus the glue lemma that ties them to the statement:
   - crt_cx, the walk's context record (cgif's flcx, A/ACj6.v:42-48): the statement's universally bound values and the
     position of the class-3 fake frame __asan_stack_malloc_3 grants at 0x81b10;
   - crt_base cx, check_round_trip_spec's premises (lib/A/FSH_Fn_crt.v) verbatim over the record's fields;
   - crt_E cx E, what every boundary env holds (the donor's fl_E, A/ACj6.v:68-72, in FSW_K's ATOM CONVENTION);
   - crt_post cx, the statement's post over the record's fields;
   - crt_from ss INV, generic in the symbolic state and the boundary invariant (the donor's fl_fromX0, A/ACid.v:99-108;
     cgif AChf.v:76 hands off to it, ACic.v:95 chains its segment lemmas backwards). Every segment lemma of the walk reads
     `crt_from ss_next INV_next -> crt_from ss_cur INV_cur`.
   own and FP are the walk's own values, not generic: own = [(3, pos)] (the class-3 frame, live from 0x81b10 to the
   epilogue flag store) and FP = FS_PSTAT_FP (the statement's post).
   crt_ss_ret is the walk's after-call boundary state (FSW_K's fss_ret_s0 plus the s1 slot region and the frame's two
   regions, in the order YI0n.st_ok_add_region' / FSW_frame.fsw_readd_frame_regions put them); crt_spec_of_base checks
   that crt_base / crt_post state exactly check_round_trip_spec.

   Port-from: cgif origin/ossv/recipes proofs/cgif/cgif_file_fuzzer/lib/A/ACj6.v:42-90 (flcx, fl_base, fl_E, fl_post,
   fl_from) and lib/A/ACid.v:57-118 (fl_baseX, fl_EX, fl_postX, fl_fromX0): the shape only; the content is crt's
   (FSH_Fn_crt.v) and the env layout is a Theorem Labs lane's crcs_extra (a working branch c4bfd3bc057,
   lib/A/FSH_check_reject_clean_starved.v:210-218). A new file: no licence lines (internal).
   rule 24: proves no function (kind: segment-walk interface of check_round_trip, build A), PORTED from
   a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_*.v - the
   bespoke ASan proof of THIS function on the SAME fs.asan bytes (0x81a9c), Qed, Require closure 334 files with 0
   Admitted / Axiom / Parameter: its stage cuts (stdefs.v St0..St25), its carried invariant CR (calls.v:142, crt_shadow
   :96, crt_unsh :98, crt_fake :104) and its FP lemmas (sdglue.v) are the template for crt_base / crt_INV_* / crt_from;
   its a_call_pre / a_call_post statement is not importable, so only the S0 forms are stated here. Checker verdict
   (a Theorem Labs lane, role check, 2026-10-29): first SEND BACK at 04:26Z because this hit was not cited, then CONFIRM at
   04:3xZ on the lane head (internal path), whose lines 6-21 carry the full
   reuse search (index v5 built 2026-10-29T01:50:18Z). An earlier version of this paragraph said "written new for A";
   that was false - the exact hit above existed.

   SK is an EXPLICIT variable (as lib/A/FSH_Fn_entry.v:71-74): build A's instance AE2k.tfib_sink_head is passed by
   whoever instantiates crt_base / crt_post / crt_from; nothing here infers it. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_K3 FSW_rres FSW_frame FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt.
(* FSH_Fn_crt.v's own import list last, so every short name below resolves as it does in the statement *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec HState B64Canon ReaderRes pj_set_c
  PjStruct check_round_trip_st8 check_round_trip_stages_b WriterValue WriterApp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- the context record: the statement's bound values (FSH_Fn_crt.v check_round_trip_spec, in its order), the
   granted frame's position, and the two blocks the walk keeps in s1 slots from before its first boundary to its last
   frees: c_text (preset_base64_encode's result, slot 0x30, stored at 0x81c84, freed at 0x82340) and c_want (malloc's
   result, slot 0x38, stored at 0x81cc8, freed at 0x82348). crt_base fixes none of the last three: the walk's entry
   theorem picks them when it hands off (as cgif's c_fpos, A/ACj6.v:46). ---- *)
Record crt_cx := mkCRT {
  c_ly : alayout; c_S : astate; c_U : list (Z * Z); c_W : world tfibsegs; c_regs : bvmap 5 word;
  c_mem : word -> option byte; c_md : Model; c_ch : list (Z * Z * Z);
  c_t : Z; c_bd : Z; c_tb : list byte; c_bs : list Z; c_live : Z; c_cnt : Z;
  c_pos : Z; c_text : Z; c_want : Z }.
(* the record with the walk's three picks replaced *)
Definition crt_with (cx : crt_cx) (pos text want : Z) : crt_cx :=
  mkCRT (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) (c_t cx) (c_bd cx) (c_tb cx)
    (c_bs cx) (c_live cx) (c_cnt cx) pos text want.

(* ---- the walk's constants, read off the record (MEASURED on the pinned fs.asan, 0x81a9c..0x81b7c):
   0x81a9c `addi sp, sp, -0xc0`; 0x81ad8 `addi s0, sp, 0xc0` (s0 = the entry sp); 0x81adc `andi sp, sp, -0x20` and
   0x81ae0 `mv s1, sp` (s1 = the re-aligned sp, kept to the epilogue); 0x81b10 __asan_stack_malloc_3 (class 3, 512 bytes);
   0x81b58 / 0x81b7c `s3 := (F >> 3) + shadow base` (s3 = the frame's shadow address, kept to the epilogue). s0, s1 and s3
   are written nowhere else before the epilogue's restores (0x82480-0x8248c). ---- *)
Definition crt_sp1 (cx : crt_cx) : Z := 32 * ((spZ (c_regs cx) - 192) / 32).
Definition crt_F (cx : crt_cx) : Z := frame_addr (c_ly cx) 3 (c_pos cx).
Definition crt_FL (cx : crt_cx) : Z := flag_addr (c_ly cx) 3 (c_pos cx).
Definition crt_SF (cx : crt_cx) : Z := shadow_addr (crt_F cx).
(* the thirteen registers the prologue saves, in slot order: ra at s0 - 8, s0 at s0 - 16, s1 at s0 - 24, s2 .. s11 at
   s0 - 32 .. s0 - 104 (0x81aa4-0x81ad4) *)
Definition crt_saved : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* ---- the boundary env's extra atoms (FSW_K ATOM CONVENTION, T form; a Theorem Labs lane's crcs_extra layout): atom 32 the shadow
   base, atoms 33 .. 45 the entry values of crt_saved, atom 46 the flag address FL, atom 47 the frame address F, atom 48
   c_text, atom 49 c_want. A segment that needs more extra atoms puts them from crt_xatom 0 = 50 on. ---- *)
Definition crt_extra (cx : crt_cx) : list word :=
  [Z_to_bv 64 SHADOW_OFF] ++ map (YK11.getr (c_regs cx)) crt_saved ++
  [Z_to_bv 64 (crt_FL cx); Z_to_bv 64 (crt_F cx); Z_to_bv 64 (c_text cx); Z_to_bv 64 (c_want cx)].
Definition crt_nextra : nat := 18.
Definition crt_xatom (i : nat) : nat := 50 + i.
(* the saved words as chunks of the s0 region (atom 8): slot -8 (k + 1) holds atom 33 + k *)
Definition crt_sv_chunks : list YP09.chunk :=
  map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0))) (seq 0 13).
(* the s1 slots every boundary from 0x81f9c on holds (MEASURED stores: 0x81b40 0x10 := F, 0x81b44 0x50 := F,
   0x81c84 0x30 := text, 0x81cc0 0x28 := F, 0x81cc8 0x38 := want, 0x81f94 0x18 := F + 0x140 (&back),
   0x81f9c 0x20 := F + 0x1a0 (&n of round_trip_document); no slot store after 0x81f9c) *)
Definition crt_cs1 : list YP09.chunk :=
  [YP09.mkChunk 0x10 (CVal 8 (SOff 47 0)); YP09.mkChunk 0x18 (CVal 8 (SOff 47 0x140));
   YP09.mkChunk 0x20 (CVal 8 (SOff 47 0x1a0)); YP09.mkChunk 0x28 (CVal 8 (SOff 47 0));
   YP09.mkChunk 0x30 (CVal 8 (SOff 48 0)); YP09.mkChunk 0x38 (CVal 8 (SOff 49 0));
   YP09.mkChunk 0x50 (CVal 8 (SOff 47 0))].
(* the frame chunk every boundary holds: the flag word (crt_frame_ok; fsw_resume_after_stack_mallocU's frame chunk).
   The objects' bytes change in the callees, so a segment that reads one adds its chunk locally. *)
Definition crt_csF : list YP09.chunk := [YP09.mkChunk (fs_frame_bytes 3 - 8) (CVal 8 (SOff 46 0))].
(* the s1 slots the boundaries before 0x81f94 hold (crt_cs1 without 0x18 / 0x20, which are stored at 0x81f94 /
   0x81f9c): the boundary states are crt_ss_ret pc crt_cs1e crt_csF at 0x81d0c / 0x81f58 and crt_ss_ret pc crt_cs1
   crt_csF at 0x81fb8 / 0x82028 / 0x82068 (a Theorem Labs lane, agreed by a Theorem Labs lane) *)
Definition crt_cs1e : list YP09.chunk :=
  [YP09.mkChunk 0x10 (CVal 8 (SOff 47 0)); YP09.mkChunk 0x28 (CVal 8 (SOff 47 0));
   YP09.mkChunk 0x30 (CVal 8 (SOff 48 0)); YP09.mkChunk 0x38 (CVal 8 (SOff 49 0));
   YP09.mkChunk 0x50 (CVal 8 (SOff 47 0))].

(* ---- the after-call boundary state at return address r, in the shape a Theorem Labs lane's runtime resume builds
   (FSW_rres.v fss_ret_s0_args): the saved words [s0 - 104, s0) at atom 8 FIRST, then the extra regions - the s1 slots
   [s1 + 0x10, s1 + 0x58) at atom 9 with chunks cs1, the frame [F, F + 512) at atom 47 with chunks csF, and the frame's
   shadow [SF, SF + 64) at atom 19 (s3) - and the extra atom facts crt_ret_facts. fsw_resume_after_rtU_s0 builds exactly
   this state after a runtime call; after a program call the frame and shadow regions come back through
   FSW_frame.fsw_readd_frame_regions and are moved into this order. ---- *)
Definition crt_frame_region (csF : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 47%nat) 0 (fs_frame_bytes 3) 0 (fs_frame_bytes 3) csF.
Definition crt_shadow_region : YP09.region :=
  YP09.mkRegion (Some 19%nat) 0 (fs_frame_bytes 3 / 8) 0 (fs_frame_bytes 3 / 8) [].
Definition crt_slot_region (cs1 : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 0x10 0x58 0x10 0x58 cs1.
Definition crt_s0_region : YP09.region := fs_ret_s0_region (-104) 0 crt_sv_chunks.
(* the extra atom facts every boundary carries, so the engine can decide the walk's pointer tests and alignment checks:
   atom 9 = sp1 (32-aligned, at most 192 below sp0, as cgif AChf.v:140-163's realigned sp), atom 47 = F (32-aligned and
   at least 4096, YG0d's AR_frames_law through YCbq.frames_bounds, as a Theorem Labs lane's crcs_resume_ss). Atom 8's (sp0,
   16-aligned, [2^46, 2^47]) is fss_ret_s0_args' own first fact. *)
Definition crt_ret_facts : list (nat * afact) :=
  [(9%nat, mkAF (2 ^ 46 - 512) (2 ^ 47) 5); (47%nat, mkAF 4096 (2 ^ 47) 5)].
Definition crt_ret_regions (cs1 csF : list YP09.chunk) : list YP09.region :=
  [crt_slot_region cs1; crt_frame_region csF; crt_shadow_region].
Definition crt_ss_ret (r : Z) (cs1 csF : list YP09.chunk) : sstate :=
  fss_ret_s0_args r (-104) 0 crt_sv_chunks (crt_ret_regions cs1 csF) crt_ret_facts.

(* ---- what every boundary env holds: sp = s1 = the re-aligned sp, gp / tp the entry's (never written by crt, kept by
   every callee; afn_pre_at / ecall_pre_at ask them at each call), s0 = the entry sp, s3 = the frame's shadow address,
   and the eighteen extra atoms of crt_extra ---- *)
Definition crt_E (cx : crt_cx) (E : env) : Prop :=
  bv_unsigned (ew E 2) = crt_sp1 cx /\ ew E 3 = YK11.getr (c_regs cx) 3%bv /\ ew E 4 = YK11.getr (c_regs cx) 4%bv /\
  bv_unsigned (ew E 8) = spZ (c_regs cx) /\ bv_unsigned (ew E 9) = crt_sp1 cx /\ bv_unsigned (ew E 19) = crt_SF cx /\
  (forall j, (j < crt_nextra)%nat -> ew E (32 + j) = nth j (crt_extra cx) (Z_to_bv 64 0)).

(* ---- the callee contracts are the walk's Section hypotheses, in EVERY segment file with exactly these names (no call
   context: the CTX premise and binder were dropped from crt's statement and from every callee spec in one S0 commit,
   owner 05:05Z; the allocator calls rely on C5's trace-universe disjunct instead; the sink head is the file's explicit
   SK, AE2k.tfib_sink_head at instantiation):
     ENCODE (encode_spec), DECODE (decode_spec_ff), PJ_WRITE (pj_write_spec), PJ_STRING (pj_string_spec),
     PJ_SET (pj_set_spec), PJ_PARSE (pj_parse_spec), PJ_FREE (pj_free_spec .. 0), PJ_OBJECT (pj_object_spec),
     PJ_GET (pj_get_spec), PJ_GET_STR (pj_get_str_spec), FUZZ_FREE (fuzz_free_spec), RT (CrtRt, below),
   each applied to fx rc SK and tfibsegs / B in the order `About` prints on the current S0. ---- *)

(* ---- the runtime contracts the walk calls: seven of S0's FsRt fields (lib/A/FSH_Rt.v:115-129), each with FsRt's own
   type at segs := tfibsegs. The walk calls strlen, strcmp, bcmp, __asan_set_shadow_f5, __wrap_malloc, __wrap_free and
   the class-3 fake-frame grant. No walk of check_round_trip calls memchr, snprintf, memcpy, memset or the class-0 /
   class-1 grants, so fr_memchr, fr_snprintf, fr_memcpy, fr_memset, fr_stack_malloc_0 and fr_stack_malloc_1 are not
   fields here. The record exists so that the image-A top (FSH_crt_chain.v check_round_trip_holds) takes as runtime
   premises only these seven contracts, not the whole FsRt (a Theorem Labs lane 10:26Z: the image-A top must not need FsRt fields
   no walk uses). crt_rt_of_fsrt gives the record from FsRt. ---- *)
Section rt. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Record CrtRt : Prop := {
  crt_fr_strlen : astrlen_realizesU tfibsegs B PC_strlen;
  crt_fr_strcmp : astrcmp_realizesU tfibsegs B PC_strcmp;
  crt_fr_bcmp : FSupoisonU.abcmp_realizesU tfibsegs B PC_bcmp;
  crt_fr_set_shadow_f5 : SetShadowDefU.aset_shadow_realizesU tfibsegs B PC_set_shadow_f5 0xf5;
  crt_fr_malloc : pc_wrap_malloc (as_code B) = PC_malloc /\ FSupoisonU.amalloc_realizesU tfibsegs B;
  crt_fr_free : pc_wrap_free (as_code B) = PC_free /\ FSupoisonU.afree_realizesU tfibsegs B;
  crt_fr_stack_malloc_3 : pc_stack_malloc (as_code B) 3 = PC_stack_malloc_3 /\ FSupoisonU.astack_malloc_realizesU tfibsegs B 3
}.
(* the seven projections of FsRt *)
Lemma crt_rt_of_fsrt : @FsRt fx rc tfibsegs B -> CrtRt.
Proof.
intros RT.
exact (Build_CrtRt (fr_strlen tfibsegs B RT) (fr_strcmp tfibsegs B RT) (fr_bcmp tfibsegs B RT)
  (fr_set_shadow_f5 tfibsegs B RT) (fr_malloc tfibsegs B RT) (fr_free tfibsegs B RT) (fr_stack_malloc_3 tfibsegs B RT)).
Qed.
End rt.

(* ---- the frame facts every boundary carries: the class-3 frame is on top of the entry's frames and was not live
   before (fsw_stack_malloc_atU), and its last word still holds the flag address (the epilogue's `ld a0, 0x1f8(s2)`,
   0x8237c) ---- *)
Definition crt_frame_ok (cx : crt_cx) (S3 : astate) (W3 : world tfibsegs) (ms3 : machine_state) : Prop :=
  frames S3 = (3, c_pos cx) :: frames (c_S cx) /\ ~ In (3, c_pos cx) (frames (c_S cx)) /\
  rdword (aview tfibsegs (w_H W3) (ms_mem ms3)) (crt_F cx + fs_frame_bytes 3 - 8) = Some (crt_FL cx).

(* the boundary invariant's type: the donor's INV (cx E k ly3 S3 W3 ms3 md3) with the boundary's poison set U3 *)
Definition crt_inv : Type :=
  crt_cx -> env -> Z -> alayout -> astate -> list (Z * Z) -> world tfibsegs -> machine_state -> Model -> Prop.

(* check_round_trip's journal window as a COMPUTED numeral, so no file pins a literal STK value: a budget change
   (e.g. STK_RT_REALLOC, owner 08:04Z) changes this one definition's value and no proof text. Use
   `pose proof crt_STK_eq as H; unfold crt_STK in H` where a numeral is needed. *)
Definition crt_STK : Z := Eval vm_compute in STK_check_round_trip.
Lemma crt_STK_eq : STK_check_round_trip = crt_STK.
Proof. reflexivity. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.

(* check_round_trip_spec's premises, verbatim, at segs := tfibsegs *)
Definition crt_base (cx : crt_cx) : Prop :=
  fpreU tfibsegs B STK_check_round_trip (c_ly cx) (c_S cx) (c_U cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) (c_ch cx) /\
  FSupoisonU.fs_heads B (c_ly cx) (c_S cx) (c_U cx) /\
  spZ (c_regs cx) + 32 <= ly_top (c_ly cx) /\
  Z.of_nat (length (frames (c_S cx))) <= FRL_CHECK /\
  getr (c_regs cx) 10 = w64 (c_t cx) /\ getr (c_regs cx) 11 = w64 (c_bd cx) /\
  getr (c_regs cx) 12 = w64 (Z.of_nat (length (c_bs cx))) /\
  zbytes_at tfibsegs (c_W cx) (c_mem cx) (c_t cx) (HState.zs (c_tb cx ++ [Z_to_bv 8 0])) /\ ~ In (Z_to_bv 8 0) (c_tb cx) /\
  Z.of_nat (length (c_tb cx)) <= 3 * 2 ^ 20 /\
  (forall a, c_t cx <= a < c_t cx + Z.of_nat (length (c_tb cx)) + 1 ->
     ~ HState.in_window (spZ (c_regs cx)) STK_check_round_trip a) /\
  (exists pt kt, In (pt, kt) (ablocks B (c_ly cx) (c_S cx)) /\ pt <= c_t cx /\
     c_t cx + Z.of_nat (length (c_tb cx)) + 1 <= pt + kt) /\
  WriterSpec.b64_dec (HState.zs (c_tb cx)) = Some (c_bs cx) /\ c_bd cx <> 0 /\
  zbytes_at tfibsegs (c_W cx) (c_mem cx) (c_bd cx) (HState.zs (HState.bz (c_bs cx))) /\
  (exists k, fs_rblock tfibsegs B (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_bd cx) k /\ Z.of_nat (length (c_bs cx)) <= k) /\
  fs_stat tfibsegs (c_W cx) (c_mem cx) (c_live cx) (c_cnt cx) /\ quiet (c_cnt cx) SIZE_MAXZ EV_check_round_trip /\
  c_live cx + LIVE_check_round_trip < 2 ^ 64 /\
  rd_cells tfibsegs (c_W cx) (c_mem cx) /\ spZ (c_regs cx) <= 2 ^ 47 /\
  st_nev (c_S cx) + EV_check_round_trip <= EV_MAX /\ blocks_bytes (c_S cx) + LIVE_check_round_trip <= LIVE_MAX /\
  (* the input overlaps no user-poisoned head (check_round_trip_spec's premise next to the input block clause; LAST
     here so no positional destruct of crt_base moves; a Theorem Labs lane 07:4xZ, ENTRY pays it) *)
  Forall (fun q => c_t cx + Z.of_nat (length (c_tb cx)) + 1 <= fst q \/ fst q + snd q <= c_t cx) (c_U cx).

(* the post's Q over the record's fields, in the stream owner's restated count form (a Theorem Labs lane 23:58Z): g_count is
   bumped by allocations only, never by a free, so the increment is at most the released CRT_ALLOCS = 68
   (lib/Prog/check_round_trip_c.v:17, :54 `cnt <= cnt' <= cnt + CRT_ALLOCS`), not EV_check_round_trip = 78, which counts
   the frees too. S0 carries that form since a working branch 88f2996f1ce, so crt_allocs IS FSH_Fn_crt.CRT_ALLOCS
   and crt_post is check_round_trip_spec's post (crt_spec_of_base below). *)
Definition crt_allocs : Z := CRT_ALLOCS.
Definition crt_Q (cx : crt_cx) : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  fun ly' S' W' regs' mem' md' =>
    Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
    (exists cnt', c_cnt cx <= cnt' <= c_cnt cx + crt_allocs /\ fs_stat tfibsegs W' mem' (c_live cx) cnt') /\
    rom_view tfibsegs W' mem'.
Definition crt_post (cx : crt_cx) : world tfibsegs -> config -> Prop :=
  apost_baseU tfibsegs B STK_check_round_trip FS_PSTAT_FP (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    EV_check_round_trip (c_U cx) (c_U cx) (crt_Q cx).

(* the walk from symbolic state ss under boundary invariant INV: the frame (3, pos) is live (own), FP = FS_PSTAT_FP, the
   journal and ARU run over the boundary's poison set U3 *)
Definition crt_from (ss : sstate) (INV : crt_inv) : Prop :=
  forall (cx : crt_cx) (E : env) (k : Z) ly3 S3 (U3 : list (Z * Z)) (W3 : world tfibsegs) (ms3 : machine_state) md3,
  crt_base cx -> crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  crt_frame_ok cx S3 W3 ms3 ->
  INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) (crt_post cx).

(* crt_base / crt_post ARE check_round_trip_spec's premises and post (S0 88f2996f1ce): the walk's entry theorem is the
   statement. The walk's picks are free in both. *)
Lemma crt_spec_of_base :
  (forall cx, crt_base cx ->
     SRr tfibsegs (c_W cx) (cfg_at tfibsegs A_check_round_trip (c_regs cx) (c_mem cx) (c_md cx)) (crt_post cx)) ->
  @check_round_trip_spec fx rc SK tfibsegs B.
Proof.
intros H. unfold check_round_trip_spec.
intros ly S U W regs mem md ch t bd tb bs live cnt. intros.
apply (H (mkCRT ly S U W regs mem md ch t bd tb bs live cnt 0 0 0)). unfold crt_base; cbn [c_ly c_S c_U c_W c_regs c_mem
  c_md c_ch c_t c_bd c_tb c_bs c_live c_cnt].
repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

(* neither the premises nor the post depend on the walk's picks *)
Lemma crt_post_with : forall cx pos text want, crt_post (crt_with cx pos text want) = crt_post cx.
Proof. intros cx pos text want. reflexivity. Qed.
Lemma crt_base_with : forall cx pos text want, crt_base (crt_with cx pos text want) <-> crt_base cx.
Proof. intros cx pos text want. reflexivity. Qed.
(* ================= the walk's boundary invariants (owner: a Theorem Labs lane, by a Theorem Labs lane's decision 00:4xZ) =================
   One `crt_INV_<pc>` per call boundary, of type crt_inv. Each is the document / buffer state the program holds at that
   pc - the ASan twin of the released plain proof's St_k (lib/Prog/check_round_trip_stdefs.v St0..St7 on
   origin/ossv/recipes). The text of each is the PROVING group's, sent to me and taken verbatim:
     0x82068 (A -> B) and 0x821ac (B -> C): a Theorem Labs lane, 00:41Z.
     0x82268 (C -> D): a Theorem Labs lane, 23:5xZ (its register list, with s9 = back and s8 = same corrected from the
       disassembly: 0x8207c `mv s9, a0` after the first decode, 0x81cd0 `mv s8, a0` after the second malloc).
     0x81d0c (seg 5's loop entry) and 0x81fb8 / 0x82028 (seg 7's loop): a Theorem Labs lane, 00:3xZ.
     0x81f58 (seg 5's exit, the join with the l = 0 bypass): a Theorem Labs lane, 05:3xZ.
  Budgets are per boundary (below): a global prefix bound cannot discharge a callee's room premise
  `st_nev S + EV_callee <= EV_MAX`, since crt_base gives only `st_nev (c_S cx) + EV_check_round_trip <= EV_MAX`. The
  prefix budgets are stated BY TRACE over the callee posts S0 already gives (pj_write's wev0 / wcalls / w_cap of
  crt_wst, pj_parse's rd_ev / trlen / rd_live of crt_TR; a Theorem Labs lane 09:5xZ), and lib/A/FSH_crt_room.v proves the two
  room predicates crt_room_D1 / crt_room_C2 from crt_base, so no lane premise is left open. ---- *)
(* ---- per-boundary prefix budgets (owner decision 01:1xZ, a Theorem Labs lane's finding): each boundary carries the journal ticks
   K_<pc>, the g_count bumps CNT_<pc> and the blocks_bytes growth LIVE_<pc> of the callees BEFORE it, as closed
   expressions in the callee specs' own terms (a Theorem Labs lane's per-call table, (internal path)),
   so they follow the callee specs when those are restated by trace. Pure arithmetic of cx. ---- *)
(* the interceptor malloc / free event (one st_nev tick, YG01.v:450 / :458; amalloc / afree_realizesU state no st_nev
   premise of their own) *)
Definition CRT_EV_WRAP : Z := 1.
Definition crt_len (cx : crt_cx) : Z := Z.of_nat (length (c_bs cx)).
Definition crt_es (cx : crt_cx) : list Z := WriterSpec.b64_enc (c_bs cx).
(* the parsed document's allocation trace (pj_parse, row 26) *)
Definition crt_TR (cx : crt_cx) : list PjGrammar.ev :=
  PjRoundTrip.ttrace (PjTree.JObj (check_round_trip_stages_b.crt_doc (crt_es cx))).
Abbreviation st := pj_set_c.set_trace.
Definition crt_trlen (tr : list PjGrammar.ev) : Z := Z.of_nat (length tr).
(* journal ticks: rows 2-8 (encode, two interceptor mallocs), 9-18 (decode, pj_string x3, pj_set doc.format /
   doc.carries / state.encoding), 19-26 (pj_string preset, pj_set state.context, pj_string es, pj_set state.bytes /
   doc.state, pj_write, pj_parse) *)
Definition K_82068 (cx : crt_cx) : Z := EV_preset_base64_encode + 2 * CRT_EV_WRAP.
Definition K_821ac (cx : crt_cx) : Z :=
  K_82068 cx + 1 + 3 * EV_pj_string + rd_ev (st 0 0 6) + rd_ev (st 1 8 7) + rd_ev (st 0 0 8).
(* g_count bumps (frees and the interceptor mallocs never touch it; pj_write's is its own wcalls, CNT_82268 below) *)
Definition CNT_82068 (cx : crt_cx) : Z := 1.
Definition CNT_821ac (cx : crt_cx) : Z :=
  CNT_82068 cx + 1 + 3 + crt_trlen (st 0 0 6) + crt_trlen (st 1 8 7) + crt_trlen (st 0 0 8).
(* blocks_bytes growth: encode's block, want, same, the first decode's block, the strings and pj_set's events
   (pj_write's buffer and the parsed document: LIVE_82268 below) *)
Definition LIVE_82068 (cx : crt_cx) : Z :=
  (FSH_Fn_writer.enc_size (crt_len cx) + HEAD) + FSH_Fn_writer.enc_size (crt_len cx) +
  (Z.of_nat (length (c_tb cx)) + 1).
Definition LIVE_821ac (cx : crt_cx) : Z :=
  LIVE_82068 cx + (FSH_Fn_writer.dec_size (crt_es cx) + HEAD) +
  (23 + HEAD) + (6 + HEAD) + (7 + HEAD) + rd_live (st 0 0 6) + rd_live (st 1 8 7) + rd_live (st 0 0 8).

(* ---- 0x82068, the return of the second strcmp (A -> B): the text and its two plain malloc buffers, no document
   object yet (segment 12 makes the frame's objects addressable) ---- *)
Definition crt_INV_82068 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 10 = Z_to_bv 64 0 /\ ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 22 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1c0) /\
  (exists same live peak cnt,
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 (c_t cx + Z.of_nat (length (c_tb cx))) /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD);
         (c_want cx, (len + 2) / 3 * 4 + 1); (same, Z.of_nat (length (c_tb cx)) + 1)]) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD)]) /\ FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
     zbytes_at tfibsegs W3 mem (c_want cx) (tb2 ++ [0]) /\
     zbytes_at tfibsegs W3 mem same (B64Canon.b64_strip (HState.zs (c_tb cx)) ++ [0]) /\
     (* the n cell's granule F + 0x1c0 is addressable (0x81cbc `sb zero, 0x38(s3)` unpoisons it; nothing re-poisons it
        before 0x82074), which decode_ff's lenp-shadow premise asks at that call (a Theorem Labs lane, 08:1xZ) *)
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1c0) 8 /\
     Z.of_nat (length tb2) = (len + 2) / 3 * 4 /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\ live = c_live cx + FSH_Fn_writer.enc_size len /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82068 cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82068 cx /\ k <= K_82068 cx).

(* ================= crt_INV_8212c, the lane boundary B1 -> B2 (a Theorem Labs lane's text, a working branch 20330e6b385 FSH_crt_segB.v:435-484) =================
   0x8212c is the return of the second pj_object (0x82128). Since 0x82068: the second decode (0x82074) made `dec`, a
   live reader block of dec_size tb2 bytes holding bs (its head joins U), and wrote |bs| at F + 0x1c0; bcmp (0x82098)
   found dec = bd; segment 12's 29 shadow stores (0x820a0-0x82110) made the five frame objects addressable, s11 became
   F + 0x1a0 (0x82114 `ld s11, 0x20(s1)`) and 0x82118 zeroed that cell; the two pj_object calls built the empty object
   at doc = F + 0x20 and at state = F + 0x80: type 6, str = kids = keys = n = cap = 0 (cap = 0 makes B2's first
   pj_set on each object the no-grow-from-0 event `st 0 0 _`), PjTree.JObj [] with no blocks. num stays existential:
   pj_object_spec's post gives `rtree v (JObj []) []`, and PjStruct.pj_node's JObj arm pins str, n, and (with D = [])
   cap, kids and keys to 0, but not num. Nothing else allocated or freed, so the block list, U and g_live are those
   of 0x82068 plus dec. The forms of the want / same blocks and of the n cell are crt_INV_821ac's, so B2's transport
   is the identity on them. Ported from d25a984c903 lib/A/Prog/check_round_trip_stdefs.v St4 (:315, crt_obj_stage
   at 0x8213c with (JObj []) (JObj []) [] [] []) and check_round_trip_sd3.v crt_obj_hdr (:693), restated over the S0
   predicates. a0 is not stated: pj_object returns void. *)
Definition K_8212c (cx : crt_cx) : Z := K_82068 cx + FSH_Fn_writer.dec_ev (crt_es cx).
Definition CNT_8212c (cx : crt_cx) : Z := CNT_82068 cx + 1.
Definition LIVE_8212c (cx : crt_cx) : Z := LIVE_82068 cx + (FSH_Fn_writer.dec_size (crt_es cx) + HEAD).
Definition crt_INV_8212c : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 22 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists same nsame dec live peak cnt,
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 dec /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)]) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (dec - HEAD, HEAD)]) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem dec (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem dec (c_bs cx) /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj []) [] /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x80) (PjTree.JObj []) [] /\
     (exists num, PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem) (F + 0x20) 6 num 0 0 0 0 0) /\
     (exists num, PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem) (F + 0x80) 6 num 0 0 0 0 0) /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_8212c cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_8212c cx /\ k <= K_8212c cx).

(* ---- 0x821ac, the return of the third pj_set (B -> C): the document and the state object built so far, the
   second decode's block, and the two n cells of round_trip_document ---- *)
Definition crt_INV_821ac : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 10 = Z_to_bv 64 0 /\ ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 22 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists same nsame dec Ddoc Dst live peak cnt,
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 dec /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)] ++ rd_hblocks (Ddoc ++ Dst)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (dec - HEAD, HEAD)] ++ rd_heads (Ddoc ++ Dst)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem dec (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem dec (c_bs cx) /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj check_round_trip_st8.crt_doc8) Ddoc /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x80) (PjTree.JObj check_round_trip_stages_b.crt_s1) Dst /\
     (* the state's blocks by size, so a later pj_set can read cap = 8 back off pj_node's kids block (pj_set's post has
        no pj_hdr): grow from cap 0 gives kids 56 * 8 and keys 8 * 8, the key "encoding" + NUL 9, pj_string's "base64"
        + NUL 7 (a Theorem Labs lane 05:0xZ, sizes as a Theorem Labs lane has them) *)
     (exists sk sy se sv, Permutation Dst [(sk, 56 * 8); (sy, 8 * 8); (se, 9); (sv, 7)]) /\
     (* cap = 8 exactly, not cap <= 2 ^ 54: the first pj_set on each object grows it from cap 0 to ReaderRes.cap2 0 = 8,
        and with cap free pj_set's grow arm stays open at 0x821d4 / 0x821fc / 0x82214, whose ticks K_82268 (no grow,
        zero slack) cannot pay (a Theorem Labs lane 04:5xZ) *)
     (exists num str kids keys cap, PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem) (F + 0x20) 6 num str kids keys 2 cap /\
        cap = 8 /\ incl (rd_heads (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap)) U3) /\
     (exists num str kids keys cap, PjStruct.pj_hdr tfibsegs (mrestrict (w_H W3) mem) (F + 0x80) 6 num str kids keys 1 cap /\
        cap = 8 /\ incl (rd_heads (ReaderRes.kids_blk kids cap ++ ReaderRes.keys_blk 6 keys cap)) U3) /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\
     PjStruct.pj_zero tfibsegs (mrestrict (w_H W3) mem) (F + 0xe0) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum (Ddoc ++ Dst) /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_821ac cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_821ac cx /\ k <= K_821ac cx).

(* ---- 0x82218, the return of the sixth pj_set (C1 -> C2, a Theorem Labs lane's text, 05:0xZ): the complete document (its "state"
   member holds the three strings; the state's and v's blocks are now the document's), the second decode's block, the
   state and v nodes zeroed by their pj_set, and the two n cells of round_trip_document. Budgets: K_821ac plus
   pj_string (preset), pj_set state.context, pj_string (es), pj_set state.bytes, pj_set doc.state. K / CNT / LIVE_82268
   (below) add pj_write's and pj_parse's own by-trace terms to these. ---- *)
Definition K_82218 (cx : crt_cx) : Z :=
  K_821ac cx + 2 * EV_pj_string + rd_ev (st 1 8 7) + 2 * rd_ev (st 2 8 5).
Definition CNT_82218 (cx : crt_cx) : Z :=
  CNT_821ac cx + 2 + crt_trlen (st 1 8 7) + 2 * crt_trlen (st 2 8 5).
Definition LIVE_82218 (cx : crt_cx) : Z :=
  LIVE_821ac cx + (7 + HEAD) + rd_live (st 1 8 7) + (Z.of_nat (length (crt_es cx)) + 1 + HEAD) +
  2 * rd_live (st 2 8 5).
Definition crt_INV_82218 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 10 = Z_to_bv 64 0 /\ ew E 18 = Z_to_bv 64 (c_text cx) /\ ew E 20 = Z_to_bv 64 len /\
  ew E 21 = Z_to_bv 64 (c_bd cx) /\ ew E 22 = Z_to_bv 64 (F + 0xe0) /\ ew E 23 = Z_to_bv 64 (F + 0x80) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists same nsame dec Ddoc live peak cnt,
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 dec /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (dec - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)] ++ rd_hblocks Ddoc) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (dec - HEAD, HEAD)] ++ rd_heads Ddoc) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\ cstr_ok tfibsegs W3 mem (c_text cx) tb2 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem dec (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem dec (c_bs cx) /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x80) /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0xe0) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\
     PjStruct.pj_zero tfibsegs (mrestrict (w_H W3) mem) (F + 0x80) /\
     PjStruct.pj_zero tfibsegs (mrestrict (w_H W3) mem) (F + 0xe0) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum Ddoc /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82218 cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82218 cx /\ k <= K_82218 cx).

(* ---- the 0x82268 prefix budgets, BY THE CALLS' OWN TRACES (base restatement authorised by a Theorem Labs lane 09:28Z): the
   0x82218 budgets plus pj_write's post terms over its own writer state crt_wst (ticks wev0, g_count bumps wcalls, the
   one buffer it leaves of w_cap + HEAD bytes, FSH_Fn_writer.v pj_write_spec) and pj_parse's over its own trace crt_TR
   (rd_ev, |tr|, rd_live; FSH_Fn_reader.v pj_parse_spec). The failure arm's EV_fuzz_free is not charged: crt_wst never
   fails. crt_wst is WriterAppFacts.putN_ok's result at g_count 0 (pj_write's st' at any g_count has the same
   failed / cap / calls). ---- *)
Definition crt_wpieces (cx : crt_cx) : list (list Z) :=
  WriterValue.wdpieces (PjTree.JObj (check_round_trip_stages_b.crt_doc (crt_es cx))) true.
Definition crt_wst (cx : crt_cx) : WriterApp.wst :=
  let ls := WriterSpec.piece_lens (crt_wpieces cx) in
  WriterApp.mkW 0 (concat (crt_wpieces cx)) (WriterSpec.grow_cap 0 0 ls)
    (Z.of_nat (length (WriterSpec.grow_calls 0 0 ls))) SIZE_MAXZ (WriterSpec.grow_calls 0 0 ls).
Definition K_82268 (cx : crt_cx) : Z :=
  K_82218 cx + FSH_Fn_writer.wev0 (crt_wst cx) + rd_ev (crt_TR cx).
Definition CNT_82268 (cx : crt_cx) : Z :=
  CNT_82218 cx + FSH_Fn_writer.wcalls (crt_wst cx) + crt_trlen (crt_TR cx).
Definition LIVE_82268 (cx : crt_cx) : Z :=
  LIVE_82218 cx + (WriterApp.w_cap (crt_wst cx) + HEAD) + rd_live (crt_TR cx).

(* ---- 0x82268, the return of pj_get_str (C -> D): the written file, the parsed document `back`, and the string
   a0 that the second decode consumes ---- *)
Definition crt_INV_82268 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (F + 0x140) /\ ew E 20 = Z_to_bv 64 len /\ ew E 21 = Z_to_bv 64 (c_bd cx) /\
  ew E 23 = Z_to_bv 64 (F + 0x80) /\ ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame file nfile back z : Z) (zs : list Z) (Dback Ddoc : list (Z * Z))
          (tback : PjTree.jv) (live peak cnt : Z),
     ew E 22 = Z_to_bv 64 file /\ ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     ew E 10 = Z_to_bv 64 z /\ z <> 0 /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD); (file - HEAD, nfile + HEAD)] ++
        rd_hblocks (Ddoc ++ Dback)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD); (file - HEAD, HEAD)] ++
        rd_heads (Ddoc ++ Dback)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
     zbytes_at tfibsegs W3 mem back (c_bs cx) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem file nfile /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
     (* rnode's UL is the list of USER pointers of the trees' own blocks, not ablocks (block BASES): rnode carries
        rd_blocks_ok UL, i.e. every (a, k) in UL is an fs_rblock, which needs (a - HEAD, k + HEAD) in ablocks, so
        UL := ablocks is unsatisfiable as soon as one block is held and made every use of this invariant vacuous (found
        by a Theorem Labs lane, 04:46Z). Ddoc ++ Dback is what pj_get / pj_get_str ask and pj_parse's post gives. *)
     rnode tfibsegs B ly3 S3 W3 mem (Ddoc ++ Dback) (F + 0x140) tback Dback /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\
     cstr_ok tfibsegs W3 mem z zs /\ WriterSpec.b64_dec zs = Some (c_bs cx) /\
     (* what D1's calls read (a Theorem Labs lane 05:0xZ), all from C2's own posts: the "bytes" string read back IS the text written
        (decode's |tb| <= 2 ^ 28 and its got-block size), z lies in one of back's blocks (decode's R1 wsrc_kept, second
        arm), back's depth (D2's pj_free needs pj_fd at depth 2), and the live equation (fuzz_free (file)'s nfile <= live
        and D2's way back to c_live) *)
     zs = tb2 /\ (exists nz, In (z, nz) Dback /\ Z.of_nat (length zs) + 1 <= nz) /\ (PjTree.depth tback <= 2)%nat /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + nfile + rd_sum (Ddoc ++ Dback) /\
     val_mem tfibsegs (mrestrict (w_H W3) mem) (F + 0x1a0) 8 0 /\
     range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (F + 0x1a0) 8 /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82268 cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_82268 cx /\ k <= K_82268 cx /\
     (* the REMAINING allowance for groups D1 and D2 over this invariant's own lists (a Theorem Labs lane 06:3xZ): D1 adds
        EV_fuzz_malloc + 2 * EV_fuzz_free, D2 then the two pj_free over Dback / Ddoc, two fuzz_free and two interceptor
        frees. Owed by C2 at 0x82268, where Dback / Ddoc are its own lists (pj_parse's `(length D <= length tr)%nat`) *)
     k + EV_fuzz_malloc + 2 * EV_fuzz_free + EV_pj_free Dback + EV_pj_free Ddoc + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP
       <= EV_check_round_trip).

(* ---- 0x822ac, the return of fuzz_free (file) (D1 -> D2, a Theorem Labs lane's text 05:0xZ): the second decode's block (got) and
   pj_write's file are freed; text / want / same / back and the two trees are still live. U holds exactly the heads of
   text and back and of the trees' blocks: want and same are interceptor-malloc blocks and carry no head (D2's two
   `free` thunks need that). Budgets: decode adds EV_fuzz_malloc ticks and one g_count bump, each fuzz_free
   EV_fuzz_free ticks; the two frees give back more block bytes than decode took, so the LIVE prefix bound is
   crt_INV_82268's. Registers: s2 = &back, s4 = len, s5 = bd, s8 = same, s9 = back, s10 = &doc, s11 = &n. ---- *)
Definition K_822ac (cx : crt_cx) : Z := K_82268 cx + EV_fuzz_malloc + 2 * EV_fuzz_free.
Definition CNT_822ac (cx : crt_cx) : Z := CNT_82268 cx + 1.
Definition LIVE_822ac (cx : crt_cx) : Z := LIVE_82268 cx.
Definition crt_INV_822ac : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let mem := ms_mem ms3 in let F := crt_F cx in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in
  ew E 18 = Z_to_bv 64 (F + 0x140) /\ ew E 20 = Z_to_bv 64 len /\ ew E 21 = Z_to_bv 64 (c_bd cx) /\
  ew E 26 = Z_to_bv 64 (F + 0x20) /\ ew E 27 = Z_to_bv 64 (F + 0x1a0) /\
  (exists (same nsame back : Z) (Dback Ddoc : list (Z * Z)) (tback : PjTree.jv) (live peak cnt : Z),
     ew E 24 = Z_to_bv 64 same /\ ew E 25 = Z_to_bv 64 back /\
     Permutation (ablocks B ly3 S3)
       (ablocks B (c_ly cx) (c_S cx) ++
        [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, FSH_Fn_writer.enc_size len);
         (same, nsame); (back - HEAD, FSH_Fn_writer.dec_size tb2 + HEAD)] ++ rd_hblocks (Ddoc ++ Dback)) /\
     Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD); (back - HEAD, HEAD)] ++ rd_heads (Ddoc ++ Dback)) /\
     FSupoisonU.fs_heads B ly3 S3 U3 /\
     fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
     fs_rblock tfibsegs B ly3 S3 W3 mem back (FSH_Fn_writer.dec_size tb2) /\
     rtree tfibsegs B ly3 S3 W3 mem (F + 0x20) (PjTree.JObj (check_round_trip_stages_b.crt_doc tb2)) Ddoc /\
     rnode tfibsegs B ly3 S3 W3 mem (Ddoc ++ Dback) (F + 0x140) tback Dback /\ (PjTree.depth tback <= 2)%nat /\
     pobj tfibsegs B ly3 S3 W3 mem (F + 0x140) /\ pobj tfibsegs B ly3 S3 W3 mem (F + 0x20) /\
     fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len + FSH_Fn_writer.dec_size tb2 + rd_sum (Ddoc ++ Dback) /\
     blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_822ac cx /\
     c_cnt cx <= cnt <= c_cnt cx + CNT_822ac cx /\ k <= K_822ac cx /\
     (* the REMAINING allowance over this invariant's own lists (a Theorem Labs lane 06:2xZ): D2's two pj_free calls tick
        EV_pj_free Dback + EV_pj_free Ddoc, which no cx-only premise can bound (a room premise over the existential lists
        would be unsatisfiable); D1 pays it at 0x822ac, where Dback / Ddoc are known *)
     k + EV_pj_free Dback + EV_pj_free Ddoc + 2 * EV_fuzz_free + 2 * CRT_EV_WRAP <= EV_check_round_trip).
(* D1's and D2's room: decode's and the frees' room premises follow from crt_base + the journal under this. With
   K / CNT / LIVE_82268 stated by pj_write's and pj_parse's own traces (WRITER's and READER's posts are by trace on S0)
   it holds for every cx that satisfies crt_base: lib/A/FSH_crt_room.v crt_room_D1_holds discharges a lane's Section
   hypothesis HROOM (`forall cx, crt_base cx -> crt_room_D1 cx`). It is never discharged by enlarging
   EV_check_round_trip. *)
Definition crt_room_D1 (cx : crt_cx) : Prop :=
  K_822ac cx <= EV_check_round_trip /\
  LIVE_82268 cx + (FSH_Fn_writer.dec_size (WriterSpec.b64_enc (c_bs cx)) + HEAD) <= LIVE_check_round_trip.
(* C2's room (a Theorem Labs lane, a working branch 0bdfefed3be FSH_crt_segC2.v Section roomC2, verbatim): the
   by-trace pj_write count at 0x82224 and pj_parse's trace at 0x82244, over crt_wst / crt_TR (above). Its terms are
   WRITER's and READER's by-trace posts on S0, so no restatement is needed: lib/A/FSH_crt_room.v crt_room_C2_holds
   discharges a lane's `HROOM2 : forall cx, crt_base B cx -> crt_room_C2 cx`. *)
(* clause 1 also carries the D groups' allowance, which C2 pays at 0x82268 into crt_INV_82268 (c2_chain, a working branch
   ebb2a46b8f3): 15 doc blocks, length Dback <= length crt_TR by pj_parse's post. By trace the
   worst case is exactly 78 = EV_check_round_trip (tight at 18 text sizes, a Theorem Labs lane's measure) *)
Definition crt_room_C2 (cx : crt_cx) : Prop :=
  K_82218 cx + FSH_Fn_writer.wev0 (crt_wst cx) + rd_ev (crt_TR cx) +
    (EV_fuzz_malloc + 2 * EV_fuzz_free + 2 * (EV_fuzz_free * crt_trlen (crt_TR cx)) + 2 * EV_fuzz_free +
     2 * CRT_EV_WRAP) <= EV_check_round_trip /\
  CNT_82218 cx + FSH_Fn_writer.wcalls (crt_wst cx) + crt_trlen (crt_TR cx) <= EV_check_round_trip /\
  LIVE_82218 cx + 2 * (WriterApp.w_cap (crt_wst cx) + HEAD) + rd_live (crt_TR cx) <= LIVE_check_round_trip.

(* ---- the loop entry of segment 5 (expected_text's encode loop, 0x81d0c .. 0x81f54, whose exit is the join 0x81f58,
   crt_INV_81f58 below), a Theorem Labs lane's text (00:3xZ, agreed with a Theorem Labs lane). The loop is no call boundary, so its registers
   are stated on the MACHINE (ms_regs) rather than on env atoms; sp gp tp s0 s1 s3 are crt_E's atoms.
   bd = c_bd, want = c_want, l = |bs|,
   En = (l + 2) / 3 * 4. What the loop gives back that relates the two ends (registers it does not write, memory outside
   [want, want + En), mem_grows) is the loop lemma's own transition, not a one-state invariant. ---- *)
Definition crt_l5_mem (cx : crt_cx) (ly3 : alayout) (S3 : astate) (W3 : world tfibsegs) (mem : word -> option byte) : Prop :=
  let bd := c_bd cx in let want := c_want cx in let l := Z.of_nat (length (c_bs cx)) in let En := (l + 2) / 3 * 4 in
  garr8 tfibsegs (mrestrict (w_H W3) mem) bd (c_bs cx) /\
  range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF bd l /\
  range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF want (En + 1) /\
  (forall a, want <= a < want + En + 1 -> writable_at tfibsegs (mrestrict (w_H W3) mem) a) /\
  (forall a, want <= a < want + En + 1 ->
     awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
       (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) a) /\
  1 <= l <= 3145728 /\ 4096 <= bd /\ bd + l <= alloc_ceiling /\ 4096 <= want /\ want + En + 1 <= alloc_ceiling /\
  (want + En + 1 <= bd \/ bd + l <= want) /\
  (forall a, bd <= a < bd + l -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) /\
  (forall a, want <= a < want + En + 1 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) /\
  (* the loop's write range [want, want + En] misses the class-3 frame, so crt_frame_ok's flag word survives the loop
     (a Theorem Labs lane 04:4xZ). Static: want is a live heap block and F a live fake frame (YCbq.sep_block_frame), discharged
     once by A0 at 0x81d0c and carried unchanged *)
  (want + En + 1 <= crt_F cx \/ crt_F cx + fs_frame_bytes 3 <= want) /\
  (* and misses crt's own stack window, so the saved words and s1 slots of crt_ss_ret survive it (a Theorem Labs lane 05:0xZ; the
     same shape crt_base carries for c_t). Static, from want being a live heap block; A0 discharges it at 0x81d0c *)
  (forall a, want <= a < want + En + 1 -> ~ HState.in_window (spZ (c_regs cx)) STK_check_round_trip a).

(* ---- what crosses the two loops unchanged (a Theorem Labs lane's text, 05:0xZ). No call lies in 0x81d0c .. 0x82068, so ly3 S3 U3
   W3 k md3 do not move there: only registers and memory. These are NOT conjuncts of the loop INVs. Each loop lemma is
   FRAME-GENERIC (a Theorem Labs lane's design): for any R its stability predicate accepts, INV_out /\ R -> INV_in /\ R. The walk
   instantiates R := crt_R5 across segment 5 and R := crt_R7 across segment 7; A23 proves the two stability facts, A0
   proves crt_INV_81d0c /\ crt_R5 at its exit. ---- *)
Definition crt_keepA (cx : crt_cx) (same k : Z) (ly3 : alayout) (S3 : astate) (U3 : list (Z * Z))
    (W3 : world tfibsegs) (ms3 : machine_state) : Prop :=
  let r := ms_regs ms3 in let mem := ms_mem ms3 in let len := Z.of_nat (length (c_bs cx)) in
  let tb2 := WriterSpec.b64_enc (c_bs cx) in let n := Z.of_nat (length (c_tb cx)) in
  YK11.getr r 20%bv = w64 len /\ YK11.getr r 21%bv = w64 (c_bd cx) /\ YK11.getr r 24%bv = w64 same /\
  Permutation (ablocks B ly3 S3)
    (ablocks B (c_ly cx) (c_S cx) ++
     [(c_text cx - HEAD, FSH_Fn_writer.enc_size len + HEAD); (c_want cx, (len + 2) / 3 * 4 + 1); (same, n + 1)]) /\
  Permutation U3 (c_U cx ++ [(c_text cx - HEAD, HEAD)]) /\ FSupoisonU.fs_heads B ly3 S3 U3 /\
  fs_rblock tfibsegs B ly3 S3 W3 mem (c_text cx) (FSH_Fn_writer.enc_size len) /\
  (* no cstr_ok (c_text) here: its last clause reads up to 7 bytes PAST text's block, which may lie in want's window, so
     it is not loop-stable (a Theorem Labs lane 05:2xZ); a consumer rebuilds it from the zbytes_at below + text's block in ablocks
     (fsw_block_body_addressable / shadow_hull_vis_of_block' / block_word_tail_vis) *)
  zbytes_at tfibsegs W3 mem (c_text cx) (tb2 ++ [0]) /\
  zbytes_at tfibsegs W3 mem (c_t cx) (HState.zs (c_tb cx ++ [Z_to_bv 8 0])) /\
  4096 <= same /\ same + n + 1 <= alloc_ceiling /\
  (* the same bounds for text's block and the input t, so a stability proof can use the loops' memory equality (stated
     on bv_unsigned x) at their bytes (a Theorem Labs lane 05:5xZ); A0 pays them with fsw_ablock_low on text's block and on crt_base's
     entry block of c_t *)
  4096 <= c_text cx - HEAD /\ c_text cx + FSH_Fn_writer.enc_size len <= alloc_ceiling /\
  4096 <= c_t cx /\ c_t cx + n + 1 <= alloc_ceiling /\
  (* the frame's bounds, so the n cell's shadow (the last conjunct) is known to lie in the shadow band, outside both
     loop windows (a Theorem Labs lane 08:2xZ; A0 pays them from crt_F_facts) *)
  4096 <= crt_F cx /\ crt_F cx + 512 <= alloc_ceiling /\
  (forall a, same <= a < same + n + 1 ->
     writable_at tfibsegs (mrestrict (w_H W3) mem) a /\
     awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
       (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) a) /\
  (exists live peak cnt, fs_glob tfibsegs W3 mem live peak cnt SIZE_MAXZ /\
     live = c_live cx + FSH_Fn_writer.enc_size len /\ c_cnt cx <= cnt <= c_cnt cx + CNT_82068 cx) /\
  blocks_bytes S3 <= blocks_bytes (c_S cx) + LIVE_82068 cx /\ k <= K_82068 cx /\
  (* the pure separations that carry the memory clauses above across the write windows [want, want + En] (L5) and
     [same, same + |tb|] (L7); A0 proves them once at 0x81d0c from AR's block separation, and the image statics
     fs_glob reads lie below every heap block *)
  (c_want cx + (len + 2) / 3 * 4 + 1 <= same \/ same + n + 1 <= c_want cx) /\
  (c_want cx + (len + 2) / 3 * 4 + 1 <= c_text cx - HEAD \/ c_text cx + FSH_Fn_writer.enc_size len <= c_want cx) /\
  (same + n + 1 <= c_text cx - HEAD \/ c_text cx + FSH_Fn_writer.enc_size len <= same) /\
  (c_want cx + (len + 2) / 3 * 4 + 1 <= c_t cx \/ c_t cx + n + 1 <= c_want cx) /\
  (same + n + 1 <= c_t cx \/ c_t cx + n + 1 <= same) /\
  (* want and same lie below the image or above it (FSW_rd.fsw_ablock_off_img; AR allows heap blocks in [4096, 0x10000),
     so `0x5fd000 <= _` was not provable - a Theorem Labs lane 08:3xZ); the statics are image bytes in [0x10000, 0x5fd000) *)
  (c_want cx + (len + 2) / 3 * 4 + 1 <= 0x10000 \/ FS_IMG_END <= c_want cx) /\
  (same + n + 1 <= 0x10000 \/ FS_IMG_END <= same) /\
  (* want's upper bound (crt_l5_mem's own conjunct), so crt_keep7's want bytes are machine addresses (a Theorem Labs lane 06:0xZ) *)
  4096 <= c_want cx /\ c_want cx + (len + 2) / 3 * 4 + 1 <= alloc_ceiling /\
  (* neither loop window holds a shadow byte, so cstr_ok (c_text)'s shadow reads survive both loops (a Theorem Labs lane 05:1xZ;
     the want one is crt_l5_mem's own conjunct). A0 pays them at 0x81d0c from AR + the block (fsw_ablock_off_shadow) *)
  (forall a, c_want cx <= a < c_want cx + (len + 2) / 3 * 4 + 1 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) /\
  (forall a, same <= a < same + n + 1 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) /\
  (* the n cell's granule stays addressable across both loops (their windows are heap bytes, outside the shadow band
     by the two lines above); A0 pays it at 0x81cbc, crt_INV_82068 carries it on (a Theorem Labs lane 08:1xZ) *)
  range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (crt_F cx + 0x1c0) 8.
(* from 0x81fb8 on: the four frame-object registers segment 6 sets (0x81f84 s10 := F + 0x20, 0x81f88 s7 := F + 0x80,
   0x81f8c s6 := F + 0xe0, 0x81fa0 s11 := F + 0x1c0) and want's NUL (0x81f68) *)
Definition crt_keep7 (cx : crt_cx) (ms3 : machine_state) (W3 : world tfibsegs) : Prop :=
  let r := ms_regs ms3 in let F := crt_F cx in
  YK11.getr r 22%bv = w64 (F + 0xe0) /\ YK11.getr r 23%bv = w64 (F + 0x80) /\
  YK11.getr r 26%bv = w64 (F + 0x20) /\ YK11.getr r 27%bv = w64 (F + 0x1c0) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) (c_want cx) (WriterSpec.b64_enc (c_bs cx) ++ [0]).
(* the frame predicates the walk passes to the two loop lemmas *)
Definition crt_R5 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  exists same, YK11.getr (ms_regs ms3) 25%bv = w64 (c_t cx) /\ crt_keepA cx same k ly3 S3 U3 W3 ms3.
Definition crt_R7 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  exists same, crt_keepA cx same k ly3 S3 U3 W3 ms3 /\ crt_keep7 cx ms3 W3.
(* ---- segment 7's frame (a Theorem Labs lane's text, 05:1xZ): the copy loop's measured footprint. The body writes a0 a1 a2 a5 a6
   a7 s9 (x10 x11 x12 x15 x16 x17 x25) and nothing else (x0 left out: its value is SLit 0, not an atom), and memory
   only in [same, same + |tb| + 1), which stays writable (crt_keepA's writable_at covers the window the loop writes
   into). s8 = same names the window and is kept. The L7 lemma is
     forall R, crt_stable7E R -> crt_from ss_82028 (INV_82028 /\ R) -> crt_from ss_81fb8 (INV_81fb8 /\ R).
   Two envs: a boundary state has every register as an atom, so the exit is read under a new env E' (a Theorem Labs lane 06:3xZ;
   the one-env crt_stable7 of 05:2xZ could not be met and is replaced). ---- *)
Definition crt_kept7 : list (bv 5) :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 19; 20; 21; 22; 23; 24; 26; 27; 28; 29; 30; 31]%bv.
Definition crt_win7 (cx : crt_cx) (same : Z) (W3 : world tfibsegs) (ms ms' : machine_state) : Prop :=
  (forall r : bv 5, In r crt_kept7 -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms) r) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (same <= a < same + Z.of_nat (length (c_tb cx)) + 1) ->
     ms_mem ms' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a)) /\
  (forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
     writable_at tfibsegs (mrestrict (w_H W3) (ms_mem ms')) a).
Definition crt_stable7E (R : crt_inv) : Prop :=
  forall cx E E' k ly3 S3 U3 (W3 : world tfibsegs) ms3 md3 ms3' md3' same,
    crt_E cx E -> crt_E cx E' -> YK11.getr (ms_regs ms3) 24%bv = w64 same ->
    R cx E k ly3 S3 U3 W3 ms3 md3 -> crt_win7 cx same W3 ms3 ms3' -> R cx E' k ly3 S3 U3 W3 ms3' md3'.
(* ---- segment 5's frame (a Theorem Labs lane's text, 05:1xZ): the encode loop's whole transition. It writes ra a0 a1 a2 a3 s7 s10
   s11 t4 t5 t6 (MEASURED, 0x81d0c .. 0x81f54), memory only in [want, want + En) (NOT En + 1: the NUL at want + En is
   0x81f54's store, A23's first instruction), env atoms only from 50 on; ly3 S3 U3 W3 k do not move, and md / md' are
   UNRELATED (the token run returns a fresh Model), so R must not read md. The L5 lemma is
     forall R, crt5_stable R -> crt_from ss_81f58 (INV_81f58 /\ R) -> crt_from ss_81d0c (INV_81d0c /\ R)
   (FSH_crt_loop5.v crt5_seg5). ---- *)
Definition crt5_clob : list (bv 5) := [1; 10; 11; 12; 13; 23; 26; 27; 29; 30; 31]%bv.
Definition crt5_stable (R : crt_inv) : Prop :=
  forall cx E E' k ly3 S3 U3 W3 ms ms' md md',
    (* only the extra atoms 32..49 (crt_E's): at a crt_ss_ret boundary atoms 1..31 ARE the registers, which the loop
       changes, so `n < 50` could not be met (a Theorem Labs lane 08:4xZ) *)
    (forall n, (32 <= n < 50)%nat -> ew E' n = ew E n) ->
    (forall r : bv 5, ~ In r crt5_clob -> YK11.getr (ms_regs ms') r = YK11.getr (ms_regs ms) r) ->
    (forall x : word,
       ~ (c_want cx <= bv_unsigned x < c_want cx + (Z.of_nat (length (c_bs cx)) + 2) / 3 * 4) ->
       ms_mem ms' x = ms_mem ms x) ->
    mem_grows (mrestrict (w_H W3) (ms_mem ms)) (mrestrict (w_H W3) (ms_mem ms')) ->
    R cx E k ly3 S3 U3 W3 ms md -> R cx E' k ly3 S3 U3 W3 ms' md'.
Definition crt_INV_81d0c : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let r := ms_regs ms3 in let bd := c_bd cx in let want := c_want cx in let l := Z.of_nat (length (c_bs cx)) in
  YK11.getr r 10%bv = w64 want /\ YK11.getr r 12%bv = w64 want /\ YK11.getr r 13%bv = w64 0 /\
  YK11.getr r 14%bv = w64 (bd + 1) /\ YK11.getr r 20%bv = w64 l /\ YK11.getr r 21%bv = w64 bd /\
  YK11.getr r 18%bv = w64 SHADOW_OFF /\ YK11.getr r 22%bv = w64 ((l + 2) / 3 * 4) /\
  YK11.getr r 15%bv = w64 103 /\ YK11.getr r 16%bv = w64 25 /\ YK11.getr r 17%bv = w64 51 /\
  YK11.getr r 5%bv = w64 61 /\ YK11.getr r 6%bv = w64 62 /\ YK11.getr r 7%bv = w64 207 /\ YK11.getr r 28%bv = w64 247 /\
  crt_l5_mem cx ly3 S3 W3 (ms_mem ms3).
(* ---- 0x81f58, the join of the encode loop's exit (0x81f54) and the l = 0 bypass (0x81cdc `beqz s4`): the NUL store
   `sb zero, 0(a0)` at 0x81f68 is about to run, a0 = want + En. a Theorem Labs lane proves the l = 0 arm into this; a Theorem Labs lane's
   crt5_seg5 runs the loop arm (0x81d0c .. 0x81f54) into it, and a Theorem Labs lane runs on from here (a Theorem Labs lane's text, 05:3xZ).
   No `1 <= l`: at l = 0, En = 0, a0 = want and b64_enc [] = []. Every clause is one of crt_l5_mem's at the single
   address want + En, plus the three registers 0x81f58 .. 0x81fb4 read. Boundary state: crt_ss_ret 0x81f58 crt_cs1e
   crt_csF; crt_R5 rides beside it. ---- *)
Definition crt_INV_81f58 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let r := ms_regs ms3 in let mem := ms_mem ms3 in let want := c_want cx in
  let l := Z.of_nat (length (c_bs cx)) in let En := (l + 2) / 3 * 4 in
  YK11.getr r 10%bv = w64 (want + En) /\ YK11.getr r 18%bv = w64 SHADOW_OFF /\
  YK11.getr r 22%bv = w64 En /\
  zbytes_at tfibsegs W3 mem want (WriterSpec.b64_enc (c_bs cx)) /\
  4096 <= want /\ want + En + 1 <= alloc_ceiling /\
  (forall a, want <= a < want + En + 1 -> ~ (SHADOW_OFF <= a < SHADOW_OFF + 2 ^ 44)) /\
  (forall a, want <= a < want + En + 1 -> ~ HState.in_window (spZ (c_regs cx)) STK_check_round_trip a) /\
  (want + En + 1 <= crt_F cx \/ crt_F cx + fs_frame_bytes 3 <= want) /\
  range_addressable (aview tfibsegs (w_H W3) mem) SHADOW_OFF (want + En) 1 /\
  writable_at tfibsegs (mrestrict (w_H W3) mem) (want + En) /\
  awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
    (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) (want + En).

(* ---- the two loop boundaries of segment 7 (canonical's copy loop, 0x81fb8 .. 0x82028), a Theorem Labs lane's text (00:3xZ).
   same = the 0x81cb8 malloc block (crt's `same`), t = c_t, tb = c_tb; the loop's block / disjointness / outside-U
   facts are its file's premises, which a Theorem Labs lane supplies at the call; the ones stated here are the program's state.
   As for segment 5, the cross-end relation (memory outside [same, same + |tb| + 1)) is the loop lemma's transition. *)
Definition crt_INV_81fb8 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let r := ms_regs ms3 in
  exists same : Z,
  YK11.getr r 25%bv = w64 (c_t cx) /\ YK11.getr r 10%bv = w64 (c_t cx) /\ YK11.getr r 12%bv = w64 0 /\
  YK11.getr r 24%bv = w64 same /\ YK11.getr r 18%bv = w64 SHADOW_OFF /\ YK11.getr r 13%bv = w64 32 /\
  YK11.getr r 14%bv = w64 0x100002600 /\
  zbytes_at tfibsegs W3 (ms_mem ms3) (c_t cx) (HState.zs (c_tb cx ++ [Z_to_bv 8 0])) /\
  4096 <= same /\ same + Z.of_nat (length (c_tb cx)) + 1 <= alloc_ceiling /\
  (forall a, same <= a < same + Z.of_nat (length (c_tb cx)) + 1 ->
     writable_at tfibsegs (mrestrict (w_H W3) (ms_mem ms3)) a /\
     awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
       (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) a) /\
  (* what the loop body's two ASan shadow checks and its NUL test read (a Theorem Labs lane 05:0xZ): the text and output bytes
     lie in live CURRENT blocks (range_addressable_of_block, YCbq.v:2723; shent_ok_of_range :2732), are disjoint, the
     text has no inner NUL (the released invariant's premise, check_round_trip_loops.v:806-809), and neither buffer
     overlaps a user-poisoned head, so the machine's shadow reads as `unpoison U3` does *)
  (exists pt kt, In (pt, kt) (ablocks B ly3 S3) /\ pt <= c_t cx /\ c_t cx + Z.of_nat (length (c_tb cx)) + 1 <= pt + kt) /\
  (exists ps ks, In (ps, ks) (ablocks B ly3 S3) /\ ps <= same /\ same + Z.of_nat (length (c_tb cx)) + 1 <= ps + ks) /\
  (same + Z.of_nat (length (c_tb cx)) + 1 <= c_t cx \/ c_t cx + Z.of_nat (length (c_tb cx)) + 1 <= same) /\
  ~ In (Z_to_bv 8 0) (c_tb cx) /\
  Forall (fun q => c_t cx + Z.of_nat (length (c_tb cx)) + 1 <= fst q \/ fst q + snd q <= c_t cx) U3 /\
  Forall (fun q => same + Z.of_nat (length (c_tb cx)) + 1 <= fst q \/ fst q + snd q <= same) U3.
Definition crt_INV_82028 : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  let r := ms_regs ms3 in let n := Z.of_nat (length (c_tb cx)) in
  exists same : Z,
  YK11.getr r 25%bv = w64 (c_t cx + n) /\ YK11.getr r 10%bv = w64 (c_t cx + n) /\
  YK11.getr r 12%bv = w64 (Z.of_nat (length (B64Canon.b64_strip (HState.zs (c_tb cx))))) /\
  YK11.getr r 24%bv = w64 same /\ YK11.getr r 18%bv = w64 SHADOW_OFF /\ YK11.getr r 13%bv = w64 32 /\
  YK11.getr r 14%bv = w64 0x100002600 /\
  zbytes_at tfibsegs W3 (ms_mem ms3) same (B64Canon.b64_strip (HState.zs (c_tb cx))) /\
  zbytes_at tfibsegs W3 (ms_mem ms3) (c_t cx) (HState.zs (c_tb cx ++ [Z_to_bv 8 0])) /\
  4096 <= same /\ same + n + 1 <= alloc_ceiling.

(* ---- 0x82354, the return of free (same) (the tail, a Theorem Labs lane): every block the walk allocated is freed, so the
   user-poisoned heads are back at the entry's U, and the statement's Q already holds at the current memory - the tail
   (the frame's last shadow byte and magic, __asan_set_shadow_f5, the flag store, the epilogue) allocates nothing and
   writes no image byte. No register fact is needed: crt_E and the boundary state carry them. The journal's tick count
   within the statement's budget is the named obligation crt_budget_T: it closes only once WRITER / READER restate their
   fixed terms by trace (a Theorem Labs lane, crt-budget-audit.md), so the group that hands off to the tail states it. ---- *)
Definition crt_budget_T (k : Z) : Prop := k <= EV_check_round_trip.
Definition crt_INV_T : crt_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
  U3 = c_U cx /\ crt_budget_T k /\ crt_Q cx ly3 S3 W3 (ms_regs ms3) (ms_mem ms3) md3.

End b.

(* ---- reading crt_E ---- *)
Lemma crt_E_extra : forall cx E j, crt_E cx E -> (j < crt_nextra)%nat -> ew E (32 + j) = nth j (crt_extra cx) (Z_to_bv 64 0).
Proof. intros cx E j (_ & _ & _ & _ & _ & _ & H) Hj. exact (H j Hj). Qed.
Lemma crt_E_F : forall cx E, crt_E cx E -> ew E 47 = Z_to_bv 64 (crt_F cx).
Proof. intros cx E H. exact (crt_E_extra cx E 15 H ltac:(unfold crt_nextra; lia)). Qed.
Lemma crt_E_FL : forall cx E, crt_E cx E -> ew E 46 = Z_to_bv 64 (crt_FL cx).
Proof. intros cx E H. exact (crt_E_extra cx E 14 H ltac:(unfold crt_nextra; lia)). Qed.
Lemma crt_E_text : forall cx E, crt_E cx E -> ew E 48 = Z_to_bv 64 (c_text cx).
Proof. intros cx E H. exact (crt_E_extra cx E 16 H ltac:(unfold crt_nextra; lia)). Qed.
Lemma crt_E_want : forall cx E, crt_E cx E -> ew E 49 = Z_to_bv 64 (c_want cx).
Proof. intros cx E H. exact (crt_E_extra cx E 17 H ltac:(unfold crt_nextra; lia)). Qed.
Lemma crt_E_shadow : forall cx E, crt_E cx E -> ew E 32 = Z_to_bv 64 SHADOW_OFF.
Proof. intros cx E H. exact (crt_E_extra cx E 0 H ltac:(unfold crt_nextra; lia)). Qed.
Lemma crt_E_saved : forall cx E k, crt_E cx E -> (k < 13)%nat ->
  ew E (33 + k) = YK11.getr (c_regs cx) (nth k crt_saved 0%bv).
Proof.
intros cx E k H Hk. replace (33 + k)%nat with (32 + S k)%nat by lia.
rewrite (crt_E_extra cx E (S k) H ltac:(unfold crt_nextra; lia)). unfold crt_extra. cbn [app nth].
rewrite app_nth1 by (rewrite length_map; cbn; lia).
rewrite (nth_indep _ _ (YK11.getr (c_regs cx) 0%bv)) by (rewrite length_map; cbn; lia).
apply map_nth.
Qed.
(* an env built over a register file that agrees with the boundary registers satisfies crt_E *)
Lemma crt_E_Ereg : forall cx regs,
  bv_unsigned (YK11.getr regs 2%bv) = crt_sp1 cx ->
  YK11.getr regs 3%bv = YK11.getr (c_regs cx) 3%bv -> YK11.getr regs 4%bv = YK11.getr (c_regs cx) 4%bv ->
  bv_unsigned (YK11.getr regs 8%bv) = spZ (c_regs cx) ->
  bv_unsigned (YK11.getr regs 9%bv) = crt_sp1 cx -> bv_unsigned (YK11.getr regs 19%bv) = crt_SF cx ->
  crt_E cx (Ereg regs (crt_extra cx)).
Proof.
intros cx regs H2 H3 H4 H8 H9 H19. unfold crt_E.
rewrite (ew_Ereg_nat regs (crt_extra cx) 2 2%bv eq_refl), (ew_Ereg_nat regs (crt_extra cx) 3 3%bv eq_refl),
  (ew_Ereg_nat regs (crt_extra cx) 4 4%bv eq_refl), (ew_Ereg_nat regs (crt_extra cx) 8 8%bv eq_refl),
  (ew_Ereg_nat regs (crt_extra cx) 9 9%bv eq_refl), (ew_Ereg_nat regs (crt_extra cx) 19 19%bv eq_refl).
split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H8|]. split; [exact H9|]. split; [exact H19|].
intros j _. apply ew_Ereg_extra.
Qed.

(* ================= shared facts about crt's class-3 frame (from a Theorem Labs lane's FSH_crt_segC.v:61-128, by path) ========= *)
Lemma crt_frame3 : fs_frame_bytes 3 = 512.
Proof. reflexivity. Qed.
(* the statics of FS_PSTAT_FP are image bytes (the last RW segment [0xa1000, 0x5fd000) of tfibsegs) *)
Lemma crt_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
intros a (r & Hr & Ha). unfold FS_PSTAT_FP in Hr.
assert (Hx : existsb (fun s => (Z.of_N (seg_base s) <=? 0xa1000) && (0x5fd000 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s)))
  tfibsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in Hx as (sg & Hin & Hc). apply andb_prop in Hc as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hin|].
cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Ha; lia|]). destruct Hr.
Qed.

Section fp. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SKfp : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.
(* ---- the FP of a pj_set call from check_round_trip, against crt's class-3 frame ----
   pj_set_spec's footprint at obj o and val w is [(o + 24, o + 56); (w, w + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++
   FS_PSTAT_FP (FSH_Fn_reader.v pj_set_spec). Of what ajournal's frame clause protects (YCbq.v ajournal: the frame
   [F, F + 512) and its shadow [shadow_addr F, + 64)) it covers ONLY obj's bytes [24, 56) and val's 56 bytes: the heap
   blocks are apart from every live frame (YCbq.sep_block_frame) and are application bytes (AR_blocks_law's in_app),
   which no shadow byte is; the statics are image bytes, which no frame holds (YCbq.frm_img) and which lie below the
   shadow. Both object ranges are in the frame, so they are the own-frame arm `in_frames lyc [(3, pos)]` of the
   after-call FP relation. a Theorem Labs lane's crtC_pjset_fp_gen, renamed. *)
Lemma crt_pjset_fp_gen : forall ly S W mem md pos Dold0 oo ow,
  AR tfibsegs B ly S W mem md -> In (3, pos) (frames S) ->
  (forall bk, In bk (rd_hblocks Dold0) -> In bk (ablocks B ly S)) ->
  0 <= oo -> oo + 56 <= 512 -> 0 <= ow -> ow + 56 <= 512 ->
  let F := frame_addr ly 3 pos in
  (forall a, inFP ([(F + oo + 24, F + oo + 56); (F + ow, F + ow + 56)] ++ ablocks_fp (rd_hblocks Dold0) ++ FS_PSTAT_FP) a ->
     in_zr a (frame_rng ly (3, pos)) \/ in_zr a (shadow_addr F, fs_frame_bytes 3 / 8) ->
     F + oo + 24 <= a < F + oo + 56 \/ F + ow <= a < F + ow + 56) /\
  (forall a, F + oo + 24 <= a < F + oo + 56 \/ F + ow <= a < F + ow + 56 -> in_frames ly [(3, pos)] a).
Proof.
intros ly S W mem md pos Dold0 oo ow HAR Hin Hblk H0 H1 H2 H3 F.
destruct (frames_bounds tfibsegs B LAWS ly S W mem md 3 pos HAR Hin) as (HF4096 & HFc & HFapp).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5). rewrite crt_frame3 in HFc, HFapp. fold F in HF4096, HFc, HFapp.
assert (HSh : forall a, in_zr a (shadow_addr F, fs_frame_bytes 3 / 8) -> kLowMemEnd <= a < kHighShadowEnd).
{ intros a Ha. unfold in_zr in Ha. cbn [fst snd] in Ha. rewrite crt_frame3 in Ha.
  pose proof (shadow_addr_bounds F ltac:(lia)) as (S1 & _).
  pose proof (shadow_addr_bounds (F + 511) ltac:(lia)) as (_ & S2).
  assert (shadow_addr F + 512 / 8 <= shadow_addr (F + 511) + 1) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
  lia. }
split.
- intros a Ha Hf. apply inFP_app in Ha as [Ha|Ha].
  + apply inFP_cons in Ha as [Ha|Ha]; [left; exact Ha|].
    apply inFP_cons in Ha as [Ha|Ha]; [right; exact Ha | exfalso; exact (inFP_nil a Ha)].
  + exfalso. apply inFP_app in Ha as [Ha|Ha].
    * destruct Ha as (r & Hr & Hra). unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([b n] & <- & Hbn).
      cbn [fst snd] in Hra. pose proof (Hblk _ Hbn) as Hbn'.
      destruct Hf as [Hf | Hf].
      -- pose proof (sep_block_frame tfibsegs B LAWS ly S W mem md b n 3 pos HAR Hbn' Hin) as Hd.
         unfold in_zr, frame_rng in Hf. cbn [fst snd] in Hf. rewrite crt_frame3 in Hd, Hf.
         unfold zdisjoint in Hd. cbn [fst snd] in Hd. fold F in Hd, Hf. lia.
      -- destruct (al_blocks _ _ LAWS ly S W mem md b n HAR Hbn') as (_ & _ & _ & Happ & _).
         pose proof (in_app_addr _ _ a Happ ltac:(lia)) as Ha. pose proof (HSh a Hf) as Hs.
         unfold app_addr, kLowShadowBeg, ASAN_CEIL in Ha. lia.
    * pose proof (crt_pstat_img a Ha) as Hi. destruct Hf as [Hf | Hf].
      -- unfold in_zr, frame_rng in Hf. cbn [fst snd] in Hf. rewrite crt_frame3 in Hf. fold F in Hf.
         exact (frm_img tfibsegs B LAWS ly S W mem md 3 pos a HAR Hin ltac:(rewrite crt_frame3; lia) Hi).
      -- pose proof (HSh a Hf) as Hs. destruct Ha as (r & Hr & Hra). unfold FS_PSTAT_FP in Hr.
         cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [cbn [fst snd] in Hra; lia|]). destruct Hr.
- intros a Ha. exists 3, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
  rewrite crt_frame3. fold F. lia.
Qed.
(* ================= the walk's program-call step and its helpers, from a Theorem Labs lane's FSH_crt_segC.v:128-218 and
   :220-424 by path (a working branch head 17f9e8967d2), renamed crt_ -> crt_ so the four segment
   files share one copy (owner decision 00:3xZ). Its proof route: FSW_K3.fsw_ajournal_sub4 for the journal,
   FSW_rres.fsw_resume_after_rtU_s0 for the state. ================= *)
(* ---- a chunk whose value is an atom offset reads the same under two envs that agree on that atom ---- *)
Lemma crt_chunk_env : forall E E' m base d w v,
  sv_denot E' v = sv_denot E v ->
  YP09.chunk_ok tfibsegs E m base (YP09.mkChunk d (CVal w v)) ->
  YP09.chunk_ok tfibsegs E' m base (YP09.mkChunk d (CVal w v)).
Proof.
intros E E' m base d w v Hv H i Hi. destruct (H i Hi) as (b & Hb & Hm). exists b. split; [|exact Hm].
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb |- *. rewrite Hv. exact Hb.
Qed.
Definition crt_atom_chunks (cs : list YP09.chunk) : Prop :=
  Forall (fun c => exists d w n off, c = YP09.mkChunk d (CVal w (SOff n off)) /\ (32 <= n < 50)%nat) cs.
Lemma crt_chunks_env : forall E E' m base cs,
  (forall n, (32 <= n < 50)%nat -> ew E' n = ew E n) -> crt_atom_chunks cs ->
  Forall (YP09.chunk_ok tfibsegs E m base) cs -> Forall (YP09.chunk_ok tfibsegs E' m base) cs.
Proof.
intros E E' m base cs Hag Hsh H. unfold crt_atom_chunks in Hsh. rewrite Forall_forall in Hsh, H |- *. intros c Hc.
destruct (Hsh c Hc) as (d & w & n & off & -> & Hn).
apply (crt_chunk_env E E' m base d w (SOff n off)); [|exact (H _ Hc)].
cbn [sv_denot]. rewrite (Hag n Hn). reflexivity.
Qed.
(* the two chunk lists the boundary state always carries are atom chunks *)
Lemma crt_sv_atoms : crt_atom_chunks crt_sv_chunks.
Proof.
unfold crt_atom_chunks, crt_sv_chunks. cbn [seq map].
repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | cbn; lia]|]). apply Forall_nil.
Qed.
Lemma crt_cs1_atoms : crt_atom_chunks crt_cs1.
Proof.
unfold crt_atom_chunks, crt_cs1.
repeat (apply Forall_cons; [do 4 eexists; split; [reflexivity | cbn; lia]|]). apply Forall_nil.
Qed.
(* two boundary envs of the same context agree on the extra atoms 32 .. 49 *)
Lemma crt_env_agree : forall cx E E', crt_E cx E -> crt_E cx E' -> forall n, (32 <= n < 50)%nat -> ew E' n = ew E n.
Proof.
intros cx E E' H H' n Hn. replace n with (32 + (n - 32))%nat by lia.
rewrite (crt_E_extra cx E (n - 32) H ltac:(unfold crt_nextra; lia)),
        (crt_E_extra cx E' (n - 32) H' ltac:(unfold crt_nextra; lia)).
reflexivity.
Qed.

(* ---- what a callee's journal keeps: a stack byte above the callee's window, and a frame byte outside its footprint
   (ajournal's stack clause and frames clause, YCbq.v:357-358 and :363-365) ---- *)
Lemma crt_kept_stack : forall lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc a,
  ARU tfibsegs B lyc Sc Uc W memC mdC -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  ajournal tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  alloc_ceiling <= a < 2 ^ 64 -> ~ (sp1 - STKc <= a < sp1) ->
  mbyte tfibsegs (mrestrict (w_H W') mem') a = mbyte tfibsegs (mrestrict (w_H W) memC) a.
Proof.
intros lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc a HARUc HARU' HJ Ha Hw.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
apply (mbyte_of_aview tfibsegs (w_H W) (w_H W')).
rewrite <- (fsw_aview_unpoison_high B ly' S' U' W' mem' md' a HARU') by lia.
rewrite <- (fsw_aview_unpoison_high B lyc Sc Uc W memC mdC a HARUc) by lia.
apply F1; [lia | exact Hw].
Qed.
Lemma crt_kept_frame : forall lyc Sc Uc (W : world tfibsegs) memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc cid pos a,
  ARU tfibsegs B lyc Sc Uc W memC mdC -> ARU tfibsegs B ly' S' U' W' mem' md' ->
  ajournal tfibsegs B STKc sp1 FPc lyc Sc W (unpoison Uc memC) mdC [] ly' S' W' (unpoison U' mem') md' kc ->
  In (cid, pos) (frames Sc) ->
  frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid -> ~ inFP FPc a ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) memC a.
Proof.
intros lyc Sc Uc W memC mdC ly' S' U' W' mem' md' STKc sp1 FPc kc cid pos a HARUc HARU' HJ Hin Hr Hnf.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR' & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & F4 & _).
pose proof (ARU_AR tfibsegs B lyc Sc Uc W memC mdC HARUc) as HARc.
destruct (frames_bounds tfibsegs B LAWS lyc Sc W (unpoison Uc memC) mdC cid pos HARc Hin) as (H4096 & Hceil & _).
destruct (al_frames _ _ LAWS lyc Sc W (unpoison Uc memC) mdC cid pos HARc Hin) as (_ & _ & Hfp & _).
assert (HinS' : In (cid, pos) (frames S')) by (rewrite Hfrs; cbn [app]; exact Hin).
assert (Efr : frame_addr ly' cid pos = frame_addr lyc cid pos).
{ unfold frame_addr. destruct Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' cid pos HAR' HinS') as (_ & _ & Hfp' & _).
rewrite Efr in Hfp'.
assert (N1 : in_ush U' (bv_unsigned (Z_to_bv 64 a)) = false).
{ rewrite (wz a ltac:(lia)). destruct (in_ush U' a) eqn:E; [|reflexivity]. exfalso.
  exact (proj2 (Hfp' a Hr) (proj1 (ush_facts tfibsegs B ly' S' U' W' mem' md' a HARU' E))). }
assert (N2 : in_ush Uc (bv_unsigned (Z_to_bv 64 a)) = false).
{ rewrite (wz a ltac:(lia)). destruct (in_ush Uc a) eqn:E; [|reflexivity]. exfalso.
  exact (proj2 (Hfp a Hr) (proj1 (ush_facts tfibsegs B lyc Sc Uc W memC mdC a HARUc E))). }
rewrite <- (aview_unpoison_out tfibsegs (w_H W') U' mem' a N1).
rewrite <- (aview_unpoison_out tfibsegs (w_H W) Uc memC a N2).
apply F4 with (cid := cid) (pos := pos); [exact Hin | left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact Hnf].
Qed.

(* the two chunk lists of the boundary state, read off their concrete definitions *)
Lemma crt_cs1_in : Forall (fun c => 0x10 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= 0x58)
  crt_cs1.
Proof. unfold crt_cs1. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.
Lemma crt_sv_in : Forall (fun c => -104 <= YP09.c_off c /\ YP09.c_off c + YP09.c_len c <= 0) crt_sv_chunks.
Proof. unfold crt_sv_chunks. cbn [seq map]. repeat (apply Forall_cons; [cbn; lia|]). apply Forall_nil. Qed.

(* ---- one program call of the walk: the boundary state at the return address r ----
   The kit step rebuilds the saved words at atom 8; the three regions beside them are added back here: the s1 slots
   (kept because they lie ABOVE the callee's stack window, ajournal's stack clause), the frame's shadow and the frame
   (present and not runtime-owned by AR_frames_law; their bytes kept outside the callee's footprint by ajournal's
   frames clause). crt_frame_ok's flag word rides on the same clause. *)
Lemma crt_after_call : forall cx E k ly3 S3 U3 W3 ms3 md3 STKc FPc ly' S' U' W' regs' mem' md' kc r csF,
  crt_E cx E ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  crt_frame_ok cx S3 W3 ms3 ->
  YK11.getr (ms_regs ms3) 2%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr (ms_regs ms3) 3%bv = YK11.getr (c_regs cx) 3%bv ->
  YK11.getr (ms_regs ms3) 4%bv = YK11.getr (c_regs cx) 4%bv ->
  YK11.getr (ms_regs ms3) 8%bv = Z_to_bv 64 (spZ (c_regs cx)) ->
  YK11.getr (ms_regs ms3) 9%bv = Z_to_bv 64 (crt_sp1 cx) ->
  YK11.getr (ms_regs ms3) 19%bv = Z_to_bv 64 (crt_SF cx) ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (spZ (c_regs cx))) crt_sv_chunks ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (crt_sp1 cx)) crt_cs1 ->
  Forall (YP09.chunk_ok tfibsegs E (mrestrict (w_H W3) (ms_mem ms3)) (crt_F cx)) csF ->
  Forall (fun c => 0 <= YP09.c_off c /\ 0 <= YP09.c_len c /\ YP09.c_off c + YP09.c_len c <= fs_frame_bytes 3) csF ->
  crt_atom_chunks csF ->
  (forall c, In c csF -> forall i, 0 <= i < YP09.c_len c -> ~ inFP FPc (crt_F cx + YP09.c_off c + i)) ->
  (forall i, 0 <= i < 8 -> ~ inFP FPc (crt_F cx + fs_frame_bytes 3 - 8 + i)) ->
  ajournal tfibsegs B STKc (crt_sp1 cx) FPc ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 []
    ly' S' W' (unpoison U' mem') md' kc ->
  upoison_ok B ly' S' U' -> upoisoned tfibsegs W' mem' U' ->
  fsw_fp_sub B (c_ly cx) (c_S cx) ly3 S3 [(3, c_pos cx)] FS_PSTAT_FP FPc ->
  aregs_preserved (ms_regs ms3) regs' -> 0 <= STKc -> STKc + 208 <= STK_check_round_trip ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U' mem') md' (k + kc) /\
  ARU tfibsegs B ly' S' U' W' mem' md' /\
  crt_frame_ok cx S' W' (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)) /\
  crt_E cx (Ereg regs' (crt_extra cx)) /\
  st_ok tfibsegs (Ereg regs' (crt_extra cx)) (crt_ss_ret r crt_cs1 csF)
    (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs))).
Proof.
intros cx E k ly3 S3 U3 W3 ms3 md3 STKc FPc ly' S' U' W' regs' mem' md' kc r csF
  HE HJ HARU3 HFR R2 R3 R4 R8 R9 R19 HSV HCS1 HCSF HcsFin HcsFat HcsFnf HflagNF HJc OK' PO' HFP HP HSTKc HSTK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTKv : 208 <= STK_check_round_trip) by (apply Z.leb_le; vm_compute; reflexivity).
destruct HFR as (Hfrs & Hnotin & Hflag).
assert (Hin3 : In (3, c_pos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof HJ as (HARj & Hly3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
assert (Hsp0 : alloc_ceiling + STK_check_round_trip <= spZ (c_regs cx)) by lia.
pose proof (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia)
  ltac:(rewrite Zminus_mod, Hal16; reflexivity)) as ((Flo & Fhi) & Fm32 & Fm16).
assert (Hsp1lo : spZ (c_regs cx) - 208 <= crt_sp1 cx) by (unfold crt_sp1; lia).
assert (Hsp1hi : crt_sp1 cx <= spZ (c_regs cx) - 192) by (unfold crt_sp1; lia).
(* the frame's address and shadow, with the layout stable under the journals *)
assert (Efr3 : frame_addr ly3 3 (c_pos cx) = crt_F cx).
{ unfold crt_F, frame_addr. destruct Hly3 as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
pose proof (ARU_AR tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 HARU3) as HAR3.
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 3 (c_pos cx) HAR3 Hin3)
  as (HF0 & HFc & HFapp).
rewrite Efr3 in HF0, HFc, HFapp.
rewrite crt_frame3 in HFc, HFapp.
assert (HFrng : 0 <= crt_F cx < kHighMemEnd) by (rewrite C4; lia).
pose proof (shadow_addr_bounds (crt_F cx) HFrng) as (HS1b & HS2b).
(* the resumed env *)
set (E' := Ereg regs' (crt_extra cx)) in *.
assert (P2 : YK11.getr regs' 2%bv = YK11.getr (ms_regs ms3) 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
assert (P3 : YK11.getr regs' 3%bv = YK11.getr (ms_regs ms3) 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
assert (P4 : YK11.getr regs' 4%bv = YK11.getr (ms_regs ms3) 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
assert (P8 : YK11.getr regs' 8%bv = YK11.getr (ms_regs ms3) 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
assert (P9 : YK11.getr regs' 9%bv = YK11.getr (ms_regs ms3) 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
assert (P19 : YK11.getr regs' 19%bv = YK11.getr (ms_regs ms3) 19%bv) by exact (HP 19 ltac:(unfold acallee_saved; lia)).
assert (HE' : crt_E cx E').
{ subst E'. apply crt_E_Ereg.
  - rewrite P2, R2. apply wz. lia.
  - rewrite P3. exact R3.
  - rewrite P4. exact R4.
  - rewrite P8, R8. apply wz. unfold spZ. apply u64_range.
  - rewrite P9, R9. apply wz. lia.
  - rewrite P19, R19. apply wz.
    unfold crt_SF. lia. }
assert (Hag : forall n, (32 <= n < 50)%nat -> ew E' n = ew E n) by exact (crt_env_agree cx E E' HE HE').
(* the composed journal: FSW_K3.fsw_ajournal_sub5, whose FP relation is exactly fsw_fp_sub's five arms (the fifth, an
   entry-frame byte, came with S0 b04db294041's kit update), so HFP fits as given *)
assert (HJ2 : ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' W' (unpoison U' mem') md' (k + kc)).
{ eapply (fsw_ajournal_sub5 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k
    STKc (crt_sp1 cx) FPc [] ly' S' W' (unpoison U' mem') md' kc);
  first [ solve [exact HJ] | solve [exact HJc] | solve [lia] | solve [exact HFP] ]. }
assert (HARU' : ARU tfibsegs B ly' S' U' W' mem' md')
  by (split; [exact (proj1 HJ2) | split; [exact OK' | exact PO']]).
pose proof HJ2 as (HAR' & Hly' & _ & _ & _ & Hfrs' & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
assert (Efr' : frame_addr ly' 3 (c_pos cx) = crt_F cx).
{ unfold crt_F, frame_addr. destruct Hly' as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
assert (Hin3' : In (3, c_pos cx) (frames S')).
{ pose proof HJc as (_ & _ & _ & _ & _ & HfrsC & _). rewrite HfrsC. cbn [app]. exact Hin3. }
destruct (al_frames _ _ LAWS ly' S' W' (unpoison U' mem') md' 3 (c_pos cx) (proj1 HJ2) Hin3')
  as (Hal32' & Happ' & Hfp' & Hsp').
rewrite Efr' in Hal32', Hfp', Hsp'. rewrite crt_frame3 in Hfp', Hsp'. change (512 / 8) with 64 in Hsp'.
assert (HSFlo : 2147450880 <= crt_SF cx) by (unfold crt_SF; rewrite C5 in HS1b; lia).
assert (HSFhi : crt_SF cx < 17594333495296) by (unfold crt_SF; rewrite C2 in HS2b; lia).
(* the resumed env's atom values *)
assert (E9v : bv_unsigned (ew E' 9) = crt_sp1 cx) by (destruct HE' as (_ & _ & _ & _ & H & _); exact H).
assert (E8v : bv_unsigned (ew E' 8) = spZ (c_regs cx)) by (destruct HE' as (_ & _ & _ & H & _); exact H).
assert (E19v : bv_unsigned (ew E' 19) = crt_SF cx) by (destruct HE' as (_ & _ & _ & _ & _ & H & _); exact H).
assert (E47v : bv_unsigned (ew E' 47) = crt_F cx) by (rewrite (crt_E_F cx E' HE'); apply wz; lia).
(* the three extra regions of the boundary state, on the memory after the call *)
assert (ROslot : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_slot_region crt_cs1)).
{ unfold region_ok, crt_slot_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9v.
  split; [lia|]. split; [lia|]. split.
  - intros o Ho. apply (apresent_writable tfibsegs).
    apply (fsw_apresent_unpoison B ly' S' U' W' mem' md' _ HARU'); [lia|]. apply Hpres2. lia.
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms3)) (crt_sp1 cx)) crt_cs1)
      by (eapply crt_chunks_env; [exact Hag | exact crt_cs1_atoms | exact HCS1]).
    pose proof crt_cs1_in as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) (ms_mem ms3))); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3).
    eapply (crt_kept_stack ly3 S3 U3 W3 (ms_mem ms3) md3 ly' S' U' W' mem' md' STKc (crt_sp1 cx) FPc kc);
      [exact HARU3 | exact HARU' | exact HJc | lia | lia]. }
assert (ROshadow : region_ok tfibsegs E' (mrestrict (w_H W') mem') crt_shadow_region).
{ unfold region_ok, crt_shadow_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E19v.
  split; [lia|]. split; [rewrite crt_frame3; cbn [Z.div]; lia|].
  split; [|apply Forall_nil].
  intros o Ho. rewrite crt_frame3 in Ho. change (512 / 8) with 64 in Ho.
  apply (apresent_writable tfibsegs). destruct (Hsp' o ltac:(lia)) as (Hp & Hno).
  apply (fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp]. }
assert (ROframe : region_ok tfibsegs E' (mrestrict (w_H W') mem') (crt_frame_region csF)).
{ unfold region_ok, crt_frame_region.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E47v.
  split; [lia|]. split; [rewrite crt_frame3; lia|]. split.
  - intros o Ho. rewrite crt_frame3 in Ho.
    apply (apresent_writable tfibsegs). destruct (Hfp' (crt_F cx + o) ltac:(lia)) as (Hp & Hno).
    apply (fsw_apresent_notowned B ly' S' U' W' mem' md' _ HARU'); [lia | exact Hno | exact Hp].
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms3)) (crt_F cx)) csF)
      by (eapply crt_chunks_env; [exact Hag | exact HcsFat | exact HCSF]).
    pose proof HcsFin as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) (ms_mem ms3))); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3).
    apply (mbyte_of_aview tfibsegs (w_H W3) (w_H W')).
    eapply (crt_kept_frame ly3 S3 U3 W3 (ms_mem ms3) md3 ly' S' U' W' mem' md' STKc (crt_sp1 cx) FPc kc 3 (c_pos cx));
      [exact HARU3 | exact HARU' | exact HJc | exact Hin3 | rewrite Efr3; rewrite crt_frame3 in *; lia
       | exact (HcsFnf c Hc i Hi)]. }
(* the frame's region is well formed: its chunks lie inside [0, 512) *)
assert (WFframe : YP09.region_wf (crt_frame_region csF) = true).
{ unfold YP09.region_wf, crt_frame_region. cbn [YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite !andb_true_iff. split; [split|].
  - apply Z.leb_le. rewrite crt_frame3. lia.
  - apply orb_true_iff. right. rewrite !andb_true_iff. split; apply Z.leb_le; lia.
  - apply forallb_forall. intros c Hc. pose proof HcsFin as Hin1. rewrite Forall_forall in Hin1.
    destruct (Hin1 c Hc) as (Ho1 & Ho2 & Ho3). unfold YP09.chunk_inside.
    cbn [YP09.r_lo YP09.r_hi]. rewrite !andb_true_iff. split; [split|]; apply Z.leb_le; lia. }
(* the four regions never meet: the frame is application memory below alloc_ceiling, its shadow is in the shadow band,
   the slots and the saved words are stack, at or above alloc_ceiling *)
assert (Hceil1 : alloc_ceiling <= crt_sp1 cx) by lia.
assert (Dfs : crt_F cx + 512 <= crt_SF cx \/ crt_SF cx + 64 <= crt_F cx).
{ unfold in_app in HFapp. destruct HFapp as (_ & [Hlow | (Hhigh & _)]).
  - left. unfold kLowShadowBeg in *. lia.
  - right. unfold crt_SF, shadow_addr, SHADOW_OFF, kHighMemBeg in *.
    Z.div_mod_to_equations. lia. }
(* the boundary state itself (FSW_rres.fsw_resume_after_rtU_s0 over the composed journal) *)
assert (HS4 : st_ok tfibsegs E' (crt_ss_ret r crt_cs1 csF)
  (restrict (w_H W') (mkst regs' (Z_to_bv 64 r) mem' (seg_rom tfibsegs)))).
{ unfold crt_ss_ret.
  eapply (fsw_resume_after_rtU_s0 B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly' S' U' W' mem' md' (k + kc) regs' mem'
    (crt_extra cx) crt_sv_chunks (crt_ret_regions crt_cs1 csF) crt_ret_facts r (-104) 0).
  - exact HJ2.
  - exact HARU'.
  - rewrite P8, R8. reflexivity.
  - lia.
  - lia.
  - lia.
  - unfold fss_ret_s0_regs, crt_ret_regions, regions_wf. cbn [forallb andb].
    rewrite WFframe. cbn [andb]. vm_compute (YP09.region_wf crt_s0_region).
    rewrite !andb_true_r. vm_compute (YP09.region_wf (crt_slot_region crt_cs1)).
    vm_compute (YP09.region_wf crt_shadow_region). reflexivity.
  - exact crt_sv_in.
  - assert (H1 : Forall (YP09.chunk_ok tfibsegs E' (mrestrict (w_H W3) (ms_mem ms3)) (spZ (c_regs cx))) crt_sv_chunks)
      by (eapply crt_chunks_env; [exact Hag | exact crt_sv_atoms | exact HSV]).
    pose proof crt_sv_in as Hin1. rewrite Forall_forall in H1, Hin1 |- *. intros c Hc.
    apply (chunk_ok_mbyte E' (mrestrict (w_H W3) (ms_mem ms3))); [|exact (H1 c Hc)].
    intros i Hi. destruct (Hin1 c Hc) as (Ho1 & Ho2).
    eapply (crt_kept_stack ly3 S3 U3 W3 (ms_mem ms3) md3 ly' S' U' W' mem' md' STKc (crt_sp1 cx) FPc kc);
      [exact HARU3 | exact HARU' | exact HJc | lia | lia].
  - intros a Ha. reflexivity.
  - unfold crt_ret_regions. constructor; [exact ROslot|]. constructor; [exact ROframe|].
    constructor; [exact ROshadow | apply Forall_nil].
  - apply pairwise_disjoint_of_extents.
    unfold fss_ret_s0_regs, crt_ret_regions, crt_slot_region, crt_frame_region, crt_shadow_region, crt_s0_region,
      fs_ret_s0_region.
    cbn [map]. unfold extent_of_region, base_val. cbn [YP09.r_base YP09.r_lo YP09.r_hi].
    fold E'. rewrite E8v, E9v, E47v, E19v. rewrite !crt_frame3. change (512 / 8) with 64.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; try exact I;
      first [right; lia | left; lia | destruct Dfs as [Hd|Hd]; [left; lia | right; lia]].
  - unfold crt_ret_facts. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E'.
    rewrite E9v, E47v. change (2 ^ 5) with 32.
    split; [split; [lia | split; [exact Fm32 | lia]]|].
    split; [|exact I]. split; [lia | split; [exact Hal32' | lia]]. }
split; [exact HJ2|]. split; [exact HARU'|]. split.
- split; [rewrite Hfrs'; cbn [app]; reflexivity|]. split; [exact Hnotin|].
  cbn [ms_mem mkst]. rewrite <- Hflag. apply rdword_ext. intros kk Hk.
  eapply (crt_kept_frame ly3 S3 U3 W3 (ms_mem ms3) md3 ly' S' U' W' mem' md' STKc (crt_sp1 cx) FPc kc 3 (c_pos cx));
    [exact HARU3 | exact HARU' | exact HJc | exact Hin3 | rewrite Efr3; rewrite crt_frame3 in *; lia
     | exact (HflagNF kk Hk)].
- split; [exact HE' | exact HS4].
Qed.
(* ================= shared walk steps moved from FSH_crt_segD.v (a Theorem Labs lane's request, so the groups use one copy):
   crt_sp1_facts / crt_F_ly / crt_awr_ok (the write window of a boundary state), crt_unpoison_keep /
   crt_unpoison_present (a raw callee post read through U), and crt_bcmp_call - the bcmp thunk call, generic in the
   run state ss, its return address r and a0's atom na (a Theorem Labs lane's segment 31: na = 10, r = 0x82298; a Theorem Labs lane's
   segment 11: na = 25, r = 0x8209c). ================= *)
(* the re-aligned sp of the walk sits between 208 and 192 below the entry sp, and is 32-aligned
   (FSW_K.fsw_realign_facts at x = sp0 - 192; the prologue's `addi sp, sp, -0xc0` then `andi sp, sp, -0x20`) *)
Lemma crt_sp1_facts : forall cx, spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  spZ (c_regs cx) - 208 <= crt_sp1 cx <= spZ (c_regs cx) - 192 /\ crt_sp1 cx mod 32 = 0 /\ crt_sp1 cx mod 16 = 0.
Proof.
intros cx H16 H0. unfold crt_sp1.
assert (Hx : (spZ (c_regs cx) - 192) mod 16 = 0) by (rewrite Zminus_mod, H16; reflexivity).
destruct (fsw_realign_facts (spZ (c_regs cx) - 192) ltac:(lia) Hx) as (F1 & F2 & F3).
split; [lia | split; [exact F2 | exact F3]].
Qed.
(* the frame's address does not move along the walk: ajournal's layout_le keeps ly_F (YG0f.layout_le) *)
Lemma crt_F_ly : forall cx n ly3, layout_le n (c_ly cx) ly3 -> frame_addr ly3 3 (c_pos cx) = crt_F cx.
Proof.
intros cx n ly3 Hle. unfold crt_F, frame_addr.
destruct Hle as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity.
Qed.

(* ---- the write window of a boundary state: the four regions of crt_ss_ret are the stack window (the saved words and
   the s1 slots) and the live class-3 frame with its shadow, which is awr_byte's own-frame arm ---- *)
Lemma crt_awr_ok : forall cx E ly3 S3 cs1 csF,
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) ->
  frame_addr ly3 3 (c_pos cx) = crt_F cx -> 0 <= crt_F cx < 2 ^ 64 ->
  awr_ok tfibsegs B E (ss_mem (crt_ss_ret 0 cs1 csF)) STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP
    (ablocks B (c_ly cx) (c_S cx)) (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)).
Proof.
intros cx E ly3 S3 cs1 csF HE H16 H0 HF HFr.
assert (E47 : bv_unsigned (ew E 47) = crt_F cx).
{ rewrite (crt_E_F cx E HE), Z_to_bv_unsigned, bv_wrap_small by (change (bv_modulus 64) with (2 ^ 64); lia).
  reflexivity. }
destruct HE as (E2 & E3 & E4 & E8 & E9 & E19 & Eex).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1 & _ & _).
assert (HSTK : 208 <= STK_check_round_trip) by (unfold STK_check_round_trip; vm_compute; discriminate).
unfold crt_ss_ret, fss_ret_s0_args, fss_ret_s0_regs, crt_ret_regions, crt_s0_region, fs_ret_s0_region,
  crt_slot_region, crt_frame_region, crt_shadow_region.
cbn [ss_mem].
assert (HFarm : forall a, crt_F cx <= a < crt_F cx + 512 ->
  awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
    (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) a).
{ intros a Ha. left. right. right. right. exists 3, (c_pos cx). split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. rewrite HF, crt_frame3. exact Ha. }
assert (HSarm : forall a, crt_SF cx <= a < crt_SF cx + 64 ->
  awr_byte tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (ablocks B (c_ly cx) (c_S cx))
    (ablocks B ly3 S3) ly3 [(3, c_pos cx)] (frames (c_S cx)) a).
{ intros a Ha. left. right. right. right. exists 3, (c_pos cx). split; [left; reflexivity|]. right.
  unfold in_zr, crt_SF in *. cbn [fst snd]. rewrite HF, crt_frame3. cbn. exact Ha. }
(* the saved words at the s0 atom *)
apply awr_ok_cons_stack with (n := 8%nat); [reflexivity | exact E8 | cbn; lia | cbn; lia|].
(* the s1 slots at the re-aligned sp *)
apply awr_ok_cons_stack_off with (n := 9%nat) (d := crt_sp1 cx - spZ (c_regs cx));
  [reflexivity | cbn; rewrite E9; lia | cbn; lia | cbn; lia|].
(* the frame itself: the own-frame arm *)
apply awr_ok_cons_gen with (k := 47%nat) (b := crt_F cx); [reflexivity | exact E47 | | ].
{ cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HFarm. rewrite crt_frame3 in Ha. lia. }
(* the frame's shadow granules: the same arm, through in_frames' shadow disjunct *)
apply awr_ok_cons_gen with (k := 19%nat) (b := crt_SF cx); [reflexivity | exact E19 | | ].
{ cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. apply HSarm. rewrite crt_frame3 in Ha. cbn in Ha. lia. }
apply awr_ok_nil.
Qed.

(* ================= runtime calls: a raw-memory callee post read through the walk's U =================
   FSW_K's fsw_intrin_atU wants the callee's frame and presence clauses over `unpoison U mem`; the runtime contracts
   (FSupoisonU's abcmp_realizesU, the fixed aset_shadow_realizesU) state them over the raw memory. unpoison only
   rewrites U's shadow bytes, and does so the same way on both memories, so both clauses carry over. *)
Lemma crt_unpoison_keep : forall (H : word -> bool) U (m m' : word -> option byte) (Wr : Z -> Prop),
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H m' a = aview tfibsegs H m a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs H (unpoison U m') a = aview tfibsegs H (unpoison U m) a.
Proof.
intros H U m m' Wr K a Ha Hw. destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
- exact (aview_unpoison_in tfibsegs H U m' m a E).
- rewrite !(aview_unpoison_out tfibsegs H U _ a E). exact (K a Ha Hw).
Qed.
Lemma crt_unpoison_present : forall (H : word -> bool) U (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) ->
  forall a, apresent H (unpoison U m) a -> apresent H (unpoison U m') a.
Proof.
intros H U m m' K a (Hh & b & Hb). split; [exact Hh|].
destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:E.
- exists (Z_to_bv 8 0). exact (unpoison_in U m' _ E).
- rewrite (unpoison_out U m _ E) in Hb. destruct (K a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb').
  exists b'. rewrite (unpoison_out U m' _ E). exact Hb'.
Qed.

(* ---- segment 31's call: bcmp (got, bd, len) through the __wrap_bcmp thunk 0x42668 (RUNTIME's FsRt.fr_bcmp, the
   abcmp_realizesU contract). Its data premises about the two byte ranges are the second decode's post (got) and
   crt_base (bd), so they are premises here; the walk part - the registers, ecall_preU, the stack the contract asks,
   and the journal put back over the call (FSW_K fsw_intrin_atU, write set = the callee's 2 * ESTACK window) - is
   proved. ---- *)
Lemma crt_bcmp_call : forall (ss : sstate) (r : Z) (na : nat) cx E k ly3 S3 U3 (W3 : world tfibsegs) regsT memT mdT got
  (Q : world tfibsegs -> config -> Prop),
  sr_get (ss_regs ss) 1%bv = SLit r -> 0 <= r < 2 ^ 64 -> sr_get (ss_regs ss) 10%bv = SOff na 0 ->
  sr_get (ss_regs ss) 11%bv = SOff 21 0 -> sr_get (ss_regs ss) 12%bv = SOff 20 0 ->
  sr_get (ss_regs ss) 2%bv = SOff 2 0 -> sr_get (ss_regs ss) 3%bv = SOff 3 0 -> sr_get (ss_regs ss) 4%bv = SOff 4 0 ->
  YK0s.ret_ok (Z_to_bv 64 r) ->
  CrtRt B ->
  crt_E cx E -> spZ (c_regs cx) mod 16 = 0 -> 192 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  YK11.getr (c_regs cx) 3%bv = w64 (as_gp B) -> YK11.getr (c_regs cx) 4%bv = w64 (as_tp B) ->
  st_ok tfibsegs E ss (restrict (w_H W3) (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs))) ->
  let len := Z.of_nat (length (c_bs cx)) in
  bv_unsigned (ew E na) = got -> bv_unsigned (ew E 21) = c_bd cx -> bv_unsigned (ew E 20) = len ->
  0 <= len < 2 ^ 32 -> 0 <= got -> got + len <= 2 ^ 63 -> 0 <= c_bd cx -> c_bd cx + len <= 2 ^ 63 ->
  src_ok tfibsegs W3 regsT memT got len -> src_ok tfibsegs W3 regsT memT (c_bd cx) len ->
  (forall a, got <= a < got + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  (forall a, c_bd cx <= a < c_bd cx + len -> ~ (spZ regsT - 2 * ESTACK <= a < spZ regsT)) ->
  amem_range got len -> amem_range (c_bd cx) len ->
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF got len ->
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) got len) ->
  range_addressable (aview tfibsegs (w_H W3) memT) SHADOW_OFF (c_bd cx) len ->
  (0 < len -> shadow_hull_vis (aview tfibsegs (w_H W3) memT) (c_bd cx) len) ->
  ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 memT) mdT k ->
  ARU tfibsegs B ly3 S3 U3 W3 memT mdT ->
  (forall regs2 mem2 md2 (v : word),
     ajournal tfibsegs B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
       (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 W3 (unpoison U3 mem2) md2 k ->
     ARU tfibsegs B ly3 S3 U3 W3 mem2 md2 ->
     aregs_preserved regsT regs2 -> YK11.getr regs2 10%bv = v ->
     (v = w64 0 <-> forall i, 0 <= i < len ->
        aview tfibsegs (w_H W3) memT (got + i) = aview tfibsegs (w_H W3) memT (c_bd cx + i)) ->
     SRr tfibsegs W3 (mkCfg (mkst regs2 (YK11.getr regsT 1%bv) mem2 (seg_rom tfibsegs)) md2) Q) ->
  SRr tfibsegs W3 (mkCfg (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) mdT) Q.
Proof.
intros ss r na cx E k ly3 S3 U3 W3 regsT memT mdT got Q Sr1 Hr Sr10 Sr11 Sr12 Sr2 Sr3 Sr4 HRet RT HE H16 H0 H47 Hgp Htp HS len Eg Ebd Elen Hl Hg0 Hg1 Hb0 Hb1
  Hsg Hsb Hwg Hwb Hmg Hmb Hag Hhg Hab Hhb HJ HARU K.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct (crt_sp1_facts cx H16 H0) as (Hsp1b & Hsp1_32 & Hsp1_16).
pose proof HE as (E2 & E3 & E4 & E8 & E9 & E19 & Eex).
assert (HSTK : 17000 <= STK_check_round_trip) by (vm_compute; discriminate).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
destruct Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & Hh47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Eslo & _).
(* the registers at the call: a0 = got, a1 = bd, a2 = len (atoms 10 / 21 / 20), ra = 0x82298, sp / gp / tp *)
assert (Rd : forall (q : bv 5) n, sr_get (ss_regs ss) q = SOff n 0 -> YK11.getr regsT q = ew E n).
{ intros q n Hq. pose proof (st_ok_restrict_reg tfibsegs (w_H W3) E ss
    (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) q HS) as X.
  cbn [ms_regs mkst] in X. rewrite X, Hq. apply fsw_SOff0. }
assert (G10 : YK11.getr regsT 10%bv = w64 got).
{ rewrite (Rd 10%bv na Sr10). unfold w64. rewrite <- Eg. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G11 : YK11.getr regsT 11%bv = w64 (c_bd cx)).
{ rewrite (Rd 11%bv _ Sr11). unfold w64. rewrite <- Ebd. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G12 : YK11.getr regsT 12%bv = w64 len).
{ rewrite (Rd 12%bv _ Sr12). unfold w64. rewrite <- Elen. symmetry. apply Z_to_bv_bv_unsigned. }
assert (G3 : YK11.getr regsT 3%bv = w64 (as_gp B)) by (rewrite (Rd 3%bv _ Sr3), E3; exact Hgp).
assert (G4 : YK11.getr regsT 4%bv = w64 (as_tp B)) by (rewrite (Rd 4%bv _ Sr4), E4; exact Htp).
assert (GSP : spZ regsT = crt_sp1 cx) by (unfold spZ; rewrite (Rd 2%bv _ Sr2); exact E2).
assert (G1 : YK11.getr regsT 1%bv = Z_to_bv 64 r).
{ exact (fsw_reg_lit (w_H W3) E ss (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) 1%bv r HS Sr1 Hr). }
assert (Hra : YK0s.ret_ok (YK11.getr regsT 1%bv)) by (rewrite G1; exact HRet).
(* the callee's pre, and the 2 * ESTACK of present stack the contract asks *)
assert (HPRE : FSupoison.ecall_preU tfibsegs B ly3 S3 U3 W3 regsT memT mdT).
{ eapply (fsw_ecall_preU_at B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k regsT
    (crt_sp1 cx - spZ (c_regs cx)) HJ HARU);
  [lia | rewrite Zminus_mod, H16, Hsp1_16; reflexivity | lia | unfold ESTACK; lia | exact Hra | exact G3
  | exact G4]. }
assert (HSK1 : ly_stk_lo ly3 + 2 * ESTACK <= spZ regsT) by (rewrite Eslo, GSP; unfold ESTACK; lia).
assert (HSK2 : forall a, spZ regsT - 2 * ESTACK <= a < spZ regsT -> apresent (w_H W3) memT a).
{ intros a Ha. rewrite GSP in Ha. unfold ESTACK in Ha.
  apply (fsw_apresent_unpoison B ly3 S3 U3 W3 memT mdT a HARU); [unfold kHighMemBeg in *; lia|].
  apply Hpres. lia. }
(* the contract *)
pose proof (crt_fr_bcmp B RT ly3 S3 U3 W3 regsT memT mdT got (c_bd cx) len HPRE HSK1 HSK2 G10 G11 G12 Hl Hg0 Hg1 Hb0 Hb1
  Hsg Hsb Hwg Hwb Hmg Hmb Hag Hhg Hab Hhb) as HC.
change (cfg_at tfibsegs PC_bcmp regsT memT mdT) with
  (mkCfg (mkst regsT (Z_to_bv 64 PC_bcmp) memT (seg_rom tfibsegs)) mdT) in HC.
(* the journal back over the call: the write set is the callee's own stack window *)
eapply SRr_bind.
{ eapply (fsw_intrin_atU B STK_check_round_trip (spZ (c_regs cx)) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx)
    (unpoison (c_U cx) (c_mem cx)) (c_md cx) [(3, c_pos cx)] ly3 S3 U3 W3 memT mdT k U3
    (fun a => spZ regsT - 2 * ESTACK <= a < spZ regsT) (YK11.getr regsT 1%bv) _
    (fun regs' mem' md' => aregs_preserved regsT regs' /\ exists v : word, YK11.getr regs' 10%bv = v /\
       (v = w64 0 <-> forall i, 0 <= i < len ->
          aview tfibsegs (w_H W3) memT (got + i) = aview tfibsegs (w_H W3) memT (c_bd cx + i))) HJ).
  - eapply SRr_mono; [exact HC|].
    intros W' c' _ (-> & regs' & mem' & md' & v & Ec & HARU' & HP & Hsame & Hv & Hres & Hfr & Hgr).
    split; [reflexivity|]. exists regs', mem', md'.
    split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity|].
    split; [exact HARU'|]. split; [exact Hsame|].
    split; [exact (crt_unpoison_keep (w_H W3) U3 memT mem' _ Hfr)|].
    split; [exact (crt_unpoison_present (w_H W3) U3 memT mem' Hgr)|].
    split; [exact HP|]. exists v. split; [exact Hv | exact Hres].
  - intros a Ha. left. left. rewrite GSP in Ha. unfold ESTACK in Ha. lia. }
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP2 & v & Hv & Hres).
exact (K regs2 mem2 md2 v HJ2 HARU2 HP2 Hv Hres).
Qed.

End fp.
