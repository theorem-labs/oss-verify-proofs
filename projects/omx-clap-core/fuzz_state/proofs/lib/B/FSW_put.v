(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 1266 of its 1332 lines of code are new or changed and 1014 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_dec_E.v, with its module paths, module names and numbers changed; 1247 of its 1346 lines of code are new or changed and 1233 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): the FAILED and the FAST arm of put (preset_file.c:454-476, A_put 0x8449c,
   612 bytes, FRAME_put 112), the image-B twin of lib/A/FSW_put.v, and their composition into the two arms of
   lib/B/FSH_Fn_writer.v `put_spec` (the CTX-drop text, by path from a working branch dda8331bd25).
   FAILED arm: `put` reads o->failed first; when it is set the function returns at once. The run is the prologue,
   UBSan's alignment check of o, the inline ASan shadow check of o + 24, the branch, the epilogue, and ends at the
   `ret` 0x84668. It makes no runtime and no allocator call, so it needs only FSW_K's entry state and the U-form
   token run: the shadow check of the out-object is the token engine's business (Reusable/YCbn.v tok_load /
   tok_branch under FSW_K.fsw_run_tok_AJU, Bx := FSW_K.fs_Bx, Bspan := FSW_K.fs_Bspan), discharged by ONE shadow
   entry (shent) covering o's 32 bytes, so no error-path branch is reached and no obligation is left.
   FAST arm (failed = 0, the text fits): to the cap test 0x8454c, the fast side, the pointer-overflow check of
   buf + len at 0x845c0, the call of __asan_memcpy (PC_memcpy 0x51d90, ra 0x845e0), the length store at o + 8, the
   pointer-overflow check of buf + len + n at 0x84604, the store of the terminating 0, and the `ret` 0x84668.
   The statements are A's: put_spec's conclusion under its own premises plus the arm's premise, with the journal
   count `3 * wcalls st'` (0 on both arms: put1 makes no request); put_close_failed / put_close_fast at the end
   restate them in put_spec's count `wevk cap st'`, as lib/A/FSW_put_close.v does for image A.

   B IS NOT A's CODE (96 bytes more of instrumented checks), so every cut, branch and offset below is re-measured on
   the B excerpt (a Theorem Labs lane's neutral per-function excerpt put.fuzz_state.asan-ubsan.s) and by the token engine over
   the pinned fs.asan-ubsan (lane scratch probe, 2026-10-29). The B-only checks:
   - 0x844d8 / 0x844dc `andi a0, o, 7; bnez -> 0x84680`: the alignment check of o. The token run does not stop there
     on either arm (MEASURED); its entry state carries atom 10's alignment fact (af_al2 = 3, from wout_ok's o mod 8 = 0).
   - 0x845bc / 0x845c0 `add a0, len, buf; bltu a0, buf -> 0x84680`: refuted at the branch (fast arm, put_fast_run
     `run 2`), from buf + len < 2 ^ 64 (al_blocks' bound on the buffer block and wout_ok's length bound).
     0x845c4 .. 0x845d0 `(buf != 0) xor (sum == 0)`, beqz -> 0x84680: the token run does not stop there (MEASURED).
   - 0x84600 / 0x84604 `add a0, buf, len + n; bltu a0, buf -> 0x84680`: refuted at the branch (put_fast_run
     `run 4`), from d + n = buf + len + n >= buf. 0x84608 .. 0x84614 (xor check) and 0x84618 `beqz buf`: the token run
     does not stop there (MEASURED).
   - after the call, s8 / s11 hold the shadow addresses of o + 8 and o (`ADD (SRL x 3) Bx`), which the token
     engine must read as shadow addresses: the resume state re-seats them (and s7, as A does) to those shapes
     over the resumed atoms.
   UBSan's trap `unimp` 0x84680 has NO A twin; its guards are the six branches above, each refuted or passed by the run.

   Kit used by path, never copied: lib/B/FSW_K.v (the B twin of a Theorem Labs lane's kit: fss0T_args / fsw_entryT_args /
   fsw_entryT_argsX, fsw_ajournal_init_ot, fsw_aj_run_tokU, fsw_preserved, fsw_reg_atom, fsw_SOff0, fsw_got_shadow,
   fsw_ecall_preU_at, fsw_intrin_atU, the same_below lemmas), lib/B/FSW_ret.v (fsw_retU, fsT_ret_regions),
   lib/A/FSupoisonStack.v (fsw_ARU_stack_ra, image-agnostic). The decoded code is this file's own table of put's
   153 words (fsw_put_tbl, built like lib/A/FSW_writer_tbl.v over YB1w's tfib_A_put .. tfib_E_put).
   TAKEN FROM: lib/A/FSW_put.v at a working branch 3cd58aafb9b (the lane's named template) with the one later
   change of e78287af146 (RT_memcpy, the single interceptor field instead of the whole FsRt record): the definitions,
   the helper section `pf`, put_failed_run and put_fast_run, re-measured as above; lib/A/FSW_put_close.v at
   a working branch 14dd44c5348: put_pf_wevk0, put_pf_calls_failed / _fast, put_post, put_close_failed /
   _fast. The old-line image-B walk lib/B/Prog/put.v (a working branch) was not used.

   RULE-24: proves function put (omx-clap-core/fuzz_state, image B = asan-ubsan, entry 0x8449c, failed + fast arms)
   (reuse search: proof-index put / put_spec / put_failed_run / put_fast_run / 0x8449c, index v5 built
   2026-10-29T04:26:29Z and 06:12:16Z, plus a git grep with a passing control (A_put) of the 559 cold lib/B trees:
   no FSW-form image-B walk of put; checker a Theorem Labs lane CONFIRM 07:0xZ). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSW_K FSW_ret.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- put's decoded code: the 153 words [tfib_A_put, tfib_E_put) of fs.asan-ubsan, in the donor's form
   (lib/A/FSW_writer_tbl.v: build_table over the image's own bytes, table_ok by build_table_ok0) ---- *)
Definition FSW_PUT_N : nat := 153%nat.          (* (tfib_E_put - tfib_A_put) / 4 = 612 / 4 *)
Lemma fsw_put_extent : tfib_A_put + 4 * Z.of_nat FSW_PUT_N = tfib_E_put.
Proof. unfold FSW_PUT_N. cbv. reflexivity. Qed.
Definition fsw_put_tbl_build : ctable := build_table tfibsegs tfib_A_put FSW_PUT_N TEmpty.
Definition fsw_put_tbl : ctable := Eval vm_compute in fsw_put_tbl_build.
Lemma fsw_put_tbl_eq : fsw_put_tbl = fsw_put_tbl_build.
Proof. vm_cast_no_check (eq_refl fsw_put_tbl). Qed.
Lemma fsw_put_tbl_ok : table_ok tfibsegs fsw_put_tbl.
Proof.
  rewrite fsw_put_tbl_eq. unfold fsw_put_tbl_build.
  apply build_table_ok0. cbv. discriminate.
Qed.

(* ---- the walk's entry state: FSW_K's fss0T_args at A_put with put's own frame and ONE extra region, the
   caller's out-object o (a0, atom 10): 32 bytes, not writable by this arm, with the only field the arm reads -
   o->failed at offset 24, 4 bytes - as a chunk holding 1 (wout_ok's `failed = 0 \/ failed = 1` and the arm's
   `failed <> 0`). The object's SHADOW is not a region: it is the token run's, through fsw_put_SH below. ---- *)
Definition fsw_put_o_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 32 0 0 [YP09.mkChunk 24 (CVal 4 (SLit 1))].
(* atom 10 = o: above the entry sp (so at least 2 ^ 46 by afn_pre's astk_ok), 8-aligned, and o + 32 <= ly_top ly
   <= 2 ^ 47. The top is 2 ^ 47 - 32, not 2 ^ 47: the token engine's static check (Reusable/YCbn.v shent_in_span)
   asks that the SHADOW of the whole entry, (af_hi + she_hi - 1) / 8, still lie in Bspan = [SHADOW_OFF,
   SHADOW_OFF + 2 ^ 44), which 2 ^ 47 overruns by one cell (MEASURED: sh_static_ok false at 2 ^ 47). *)
Definition fsw_put_gf : list (nat * afact) := [(10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3)].
Definition fsw_put_ss0 : sstate := fss0T_args A_put FRAME_put [fsw_put_o_region] fsw_put_gf.
(* the one shadow entry the inline check at 0x84500 needs: o's 32 bytes (donor: lib/A/ACes.v:28-43) *)
Definition fsw_put_SH : list shent := [mkSHE 10 0 32].

(* `wview` reads the memory only at the address asked (LPS's definition; the same step is taken in A/AB13.v:27-29
   and A/ACep.v:68), so a byte that keeps its value keeps its writability. The core's `writable_iff_of`
   (Reusable/YI04.v:545) says this, but inside the malloc section, where `segs` is `ms_segs B` of a
   `malloc_syms`, so it does not apply at tfibsegs; this is the one-line form for the image's own segments.
   Rule 24, by the final lookup rule's parts (a Theorem Labs lane 02:12Z): `git grep -n -w -E 'fsw_put_writable_eq|writable_eq'
   <ref> -- 'proofs/*'`, one ref per run, exit code from the command and output to a file, returned exit=1 (no
   match, empty hit file) on part (1)'s four released refs and on nine part (2) working branches.
   NOT searched: five other working branches
   (the sweep hit its 3000 s cap),
   the SHARED-WALKS.md registry, part (3)'s working-branch heads with the stem `state` or a hand
   prefix, and part (4)'s blob scan (waits on a Theorem Labs lane's lift). So: no donor found in the
   thirteen refs searched, NOT `no donor`. *)
Lemma fsw_put_writable_eq : forall (m m' : word -> option byte) a,
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  (writable_at tfibsegs m a <-> writable_at tfibsegs m' a).
Proof. intros m m' a H. unfold writable_at, wview. rewrite H. reflexivity. Qed.

(* ================= the FAST arm of put (failed = 0, the text fits): definitions ================= *)
(* The walk (MEASURED with the token engine over the pinned fs.asan-ubsan, lane scratch probe 2026-10-29): the entry
   state is FSW_K's fss0T_args at A_put with the out-object o (a0, atom 10) as an `rs` region whose three words are the
   walk's extra atoms buf / len / cap (xatom 0..2 = 33 / 34 / 35), and o's `failed` field a chunk holding 0. Run 1
   stops at the cap test 0x8454c (`cap >=u n + 1 + len`); on the FAST side (YA0p.srr_branch_tok) run 2 stops at
   UBSan's pointer-overflow check 0x845c0 (`buf + len <u buf`, its taken side is the trap 0x84680); on the other side
   run 3 reaches the call of __asan_memcpy (PC_memcpy 0x51d90) with a0 = buf + len, a1 = s, a2 = n; the runtime contract
   (FSH_Rt.fr_memcpy's field RT_memcpy) does the copy and FSW_K.fsw_intrin_atU puts the caller's journal back. The
   resume state at 0x845e0 is fss_retT's shape, with s7 re-seated to the shadow base (atom 32), s8 / s11 re-seated to
   the shadow addresses of o + 8 and o over the resumed o (atom 8), and an ALIAS fact for `n + buf + len` -> atom 36
   (the donor's rd_alias, lib/A/ACes.v:30-36), since the store of the terminating 0 is at an address the code
   computes as a sum (the engine's normal form of B's `buf + (len + n)` is A's `(n + buf) + len`, MEASURED). Its
   shents are o's 32 bytes and that one byte, so again no obligation and no error-path branch. Run 4 stores the new
   length at o + 8 and stops at UBSan's pointer-overflow check 0x84604 (`d + n <u buf`, taken side the trap); run 5
   stores the 0 at buf + len + n and returns at 0x84668 (FSW_ret.fsw_retU). *)
Definition fsw_pf_CEIL : Z := 0x7fffff800000.       (* the top of YCbq.asan_consts' alloc_ceiling range *)
Definition fsw_pf_o_region : YP09.region :=
  YP09.mkRegion (Some 10%nat) 0 32 0 0
    [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
     YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SLit 0))].
(* atom 10 = o: hi is 2 ^ 47 - 32, not 2 ^ 47 (YCbn.v:120-127 shent_in_span; MEASURED: sh_static_ok false at 2 ^ 47) *)
Definition fsw_pf_gf : list (nat * afact) :=
  [(10%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (33%nat, mkAF 4096 fsw_pf_CEIL 4); (34%nat, mkAF 0 (2 ^ 27) 0);
   (35%nat, mkAF 0 (2 ^ 27) 0); (12%nat, mkAF 0 (2 ^ 27) 0)].
Definition fsw_pf_ss0 : sstate := fss0T_args A_put FRAME_put [fsw_pf_o_region] fsw_pf_gf.
(* the thirteen words put's prologue saved, as the resume state reads them off the frame [sp - 112, sp) *)
Definition fsw_pf_cs : list YP09.chunk :=
  [YP09.mkChunk 8 (CVal 8 (SOff 49 0)); YP09.mkChunk 16 (CVal 8 (SOff 48 0)); YP09.mkChunk 24 (CVal 8 (SOff 47 0));
   YP09.mkChunk 32 (CVal 8 (SOff 46 0)); YP09.mkChunk 40 (CVal 8 (SOff 45 0)); YP09.mkChunk 48 (CVal 8 (SOff 44 0));
   YP09.mkChunk 56 (CVal 8 (SOff 43 0)); YP09.mkChunk 64 (CVal 8 (SOff 42 0)); YP09.mkChunk 72 (CVal 8 (SOff 41 0));
   YP09.mkChunk 80 (CVal 8 (SOff 40 0)); YP09.mkChunk 88 (CVal 8 (SOff 39 0)); YP09.mkChunk 96 (CVal 8 (SOff 38 0));
   YP09.mkChunk 104 (CVal 8 (SOff 37 0))].
(* after the call o is at atom 8 (s0); its length field is the only window the rest of the walk writes *)
Definition fsw_pf_o2 : YP09.region :=
  YP09.mkRegion (Some 8%nat) 0 32 8 16
    [YP09.mkChunk 0 (CVal 8 (SOff 33 0)); YP09.mkChunk 8 (CVal 8 (SOff 34 0));
     YP09.mkChunk 16 (CVal 8 (SOff 35 0)); YP09.mkChunk 24 (CVal 4 (SLit 0))].
(* the byte that takes the terminating 0, at atom 36 = buf + len + n *)
Definition fsw_pf_z2 : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 1 [].
Definition fsw_pf_gf2 : list (nat * afact) :=
  [(8%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 3); (33%nat, mkAF 4096 fsw_pf_CEIL 4); (34%nat, mkAF 0 (2 ^ 27) 0);
   (35%nat, mkAF 0 (2 ^ 27) 0); (9%nat, mkAF 0 (2 ^ 27) 0); (36%nat, mkAF 4096 fsw_pf_CEIL 0)].
Definition fsw_pf_al2 : list (sv * sv) :=
  [(SAlu ALU_ADD (SAlu ALU_ADD (SOff 9 0) (SOff 33 0)) (SOff 34 0), SOff 36 0)].
(* the resume state at the return address 0x845e0 = 542176, over a register file rs *)
Definition fsw_pf_ssk (rs : list sv) : sstate :=
  mkSS 542176 rs (fsT_ret_regions 112 fsw_pf_cs [fsw_pf_o2; fsw_pf_z2]) None
    (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: fsw_pf_gf2) [] fsw_pf_al2).
(* s8 (x24) and s11 (x27) hold the shadow addresses of o + 8 and o, which put computed before the call
   (0x84514 .. 0x84518 and 0x845a0) and reads after it (0x845e0, 0x845f4) *)
Definition fsw_pf_s8 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 8) (SLit 3)) (SOff 32 0).
Definition fsw_pf_s11 : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 8 0) (SLit 3)) (SOff 32 0).
Definition fsw_pf_rs1 : list sv := sr_set sr_atoms 23%bv (SOff 32 0).
Definition fsw_pf_rs2 : list sv := sr_set fsw_pf_rs1 24%bv fsw_pf_s8.
Definition fsw_pf_ssr : sstate := fsw_pf_ssk (sr_set fsw_pf_rs2 27%bv fsw_pf_s11).
Definition fsw_pf_SH : list shent := [mkSHE 10 0 32].
Definition fsw_pf_SH2 : list shent := [mkSHE 8 0 32; mkSHE 36 0 1].

(* ---- the FAST arm's helpers (lib/A/FSW_put.v's section pf, over fs.asan-ubsan's segments). The STACK shadow
   transfer is NOT re-proved here: it is FSupoisonStack.fsw_ARU_stack_ra by path. ---- *)
Section pf. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* the image's four segments cover [0x10000, 0x5fd000) without a gap (the pinned fs.asan-ubsan's program headers:
   MEASURED (0x10000, +0x20000), (0x30000, +0x6f000), (0x9f000, +0x2000), (0xa1000, +0x55c000)) *)
Lemma fsw_pf_in_img : forall a, 0x10000 <= a < 0x5fd000 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img.
change tfibsegs with [AsanUbsan.AsanUbsan_segment_000; AsanUbsan.AsanUbsan_segment_001;
  AsanUbsan.AsanUbsan_segment_002; AsanUbsan.AsanUbsan_segment_003].
destruct (Z.lt_ge_cases a 0x30000); [exists AsanUbsan.AsanUbsan_segment_000; split; [cbn; tauto | cbn; lia]|].
destruct (Z.lt_ge_cases a 0x9f000); [exists AsanUbsan.AsanUbsan_segment_001; split; [cbn; tauto | cbn; lia]|].
destruct (Z.lt_ge_cases a 0xa1000); [exists AsanUbsan.AsanUbsan_segment_002; split; [cbn; tauto | cbn; lia]|].
exists AsanUbsan.AsanUbsan_segment_003. split; [cbn; tauto | cbn; lia].
Qed.
(* every read-only literal of FS_RO_STRS, its terminating 0 included, lies in the image *)
Lemma fsw_pf_ro_strs_img : forall s l, In (s, l) FS_RO_STRS -> 0x10000 <= s /\ s + Z.of_nat (length l) + 1 <= 0x5fd000.
Proof.
intros s l H.
assert (HB : forallb (fun e => (0x10000 <=? fst e) && (fst e + Z.of_nat (length (snd e)) + 1 <=? 0x5fd000)) FS_RO_STRS
  = true) by (vm_compute; reflexivity).
rewrite forallb_forall in HB. specialize (HB _ H). cbn [fst snd] in HB.
apply andb_prop in HB as [H1 H2]. apply Z.leb_le in H1, H2. lia.
Qed.
(* the read-only image (segments and relro) lies below the shadow *)
Lemma fsw_pf_roP_low : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> 0 <= a < SHADOW_OFF.
Proof.
intros a [(sg & Hin & _ & Hr) | Hr]; [|unfold FS_RLO, FS_RHI, SHADOW_OFF in *; lia].
change tfibsegs with [AsanUbsan.AsanUbsan_segment_000; AsanUbsan.AsanUbsan_segment_001;
  AsanUbsan.AsanUbsan_segment_002; AsanUbsan.AsanUbsan_segment_003] in Hin.
unfold SHADOW_OFF. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hr; lia.
Qed.
Lemma fsw_pf_mbyte_aview2 : forall (H : word -> bool) (m m' : word -> option byte) a b,
  aview tfibsegs H m' a = aview tfibsegs H m b -> mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) b.
Proof.
intros H m m' a b E. unfold aview in E.
destruct (mbyte tfibsegs (mrestrict H m') a) as [b'|], (mbyte tfibsegs (mrestrict H m) b) as [b0|];
  cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* a chunk read at one base and env is the same chunk at another base and env, over memory that agrees there *)
Lemma fsw_pf_chunk_move : forall E E' (m m' : word -> option byte) b b' o o' (w : N) e e',
  YP09.chunk_ok tfibsegs E m b (YP09.mkChunk o (CVal w e)) -> sv_denot E' e' = sv_denot E e -> b' + o' = b + o ->
  (forall i, 0 <= i < Z.of_N w -> mbyte tfibsegs m' (b + o + i) = mbyte tfibsegs m (b + o + i)) ->
  YP09.chunk_ok tfibsegs E' m' b' (YP09.mkChunk o' (CVal w e')).
Proof.
intros E E' m m' b b' o o' w e e' Hc He Hb Hk i Hi.
unfold YP09.c_len in Hi. cbn [YP09.c_val YP09.cv_len] in Hi.
destruct (Hc i ltac:(unfold YP09.c_len; cbn [YP09.c_val YP09.cv_len]; exact Hi)) as (x & Hx & Hm).
exists x. cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hx |- *. rewrite He. split; [exact Hx|].
cbn [YP09.c_off] in Hm. rewrite Hb, Hk by lia. exact Hm.
Qed.
(* a shadow byte of an address outside every range of U is not user-poisoned *)
Lemma fsw_pf_ush_out : forall B ly S U x, upoison_ok B ly S U -> 0 <= x ->
  (forall r, In r U -> ~ (fst r <= x < fst r + snd r)) -> in_ush U (shadow_addr x) = false.
Proof.
intros B ly S U x OK Hx Hout.
destruct (in_ush U (shadow_addr x)) eqn:E; [exfalso|reflexivity].
apply in_ush_spec in E as (r & Hr & Hs).
destruct (upoison_ok_In B ly S U r OK Hr) as (Hr8 & Hr8' & Hrs8 & _).
apply (Hout r Hr). unfold shadow_addr in Hs. lia.
Qed.
Lemma fsw_pf_ra_raw : forall (H : word -> bool) U mem a n, 0 <= a -> a + n <= 2 ^ 63 ->
  (forall x, a <= x < a + n -> in_ush U (shadow_addr x) = false) ->
  range_addressable (aview tfibsegs H (unpoison U mem)) SHADOW_OFF a n ->
  range_addressable (aview tfibsegs H mem) SHADOW_OFF a n.
Proof.
intros H U mem a n Ha Hn Hu HR. eapply range_addressable_agree; [|exact HR].
intros x Hx. symmetry. apply aview_unpoison_out.
rewrite wz; [exact (Hu x Hx)|]. unfold shadow_of_addr, SHADOW_OFF. lia.
Qed.
Lemma fsw_pf_hull_raw : forall (W : world tfibsegs) U mem x n, upoisoned tfibsegs W mem U -> 0 <= x -> x + n <= 2 ^ 63 ->
  shadow_hull_vis (aview tfibsegs (w_H W) (unpoison U mem)) x n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) x n.
Proof.
intros W U mem x n PO Hx Hn HH t Ht.
destruct (in_ush U t) eqn:E.
- rewrite (PO t E). discriminate.
- rewrite <- (aview_unpoison_out tfibsegs (w_H W) U mem t); [exact (HH t Ht)|].
  rewrite wz; [exact E|]. unfold shadow_addr, SHADOW_OFF in Ht. lia.
Qed.
Variable B : asyms.
Lemma fsw_pf_blk_disj : forall ly S (W : world tfibsegs) mem md p1 m1 p2 m2, AR tfibsegs B ly S W mem md ->
  In (p1, m1) (ablocks B ly S) -> In (p2, m2) (ablocks B ly S) -> p1 <> p2 ->
  p1 + req_size m1 <= p2 \/ p2 + req_size m2 <= p1.
Proof.
intros ly S W mem md p1 m1 p2 m2 HAR H1 H2 Hne.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof (al_blocks _ _ LAWS ly S W mem md p1 m1 HAR H1) as (_ & _ & _ & _ & _ & PW & _).
assert (I1 : In (p1, req_size m1) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (p1, m1)); exact H1).
assert (I2 : In (p2, req_size m2) (map (fun b => (fst b, req_size (snd b))) (ablocks B ly S)))
  by (apply (in_map (fun b => (fst b, req_size (snd b))) _ (p2, m2)); exact H2).
destruct (pairwise_In2 zdisjoint _ _ _ PW I1 I2 ltac:(intros E; injection E; intros _ E'; exact (Hne E')))
  as [D|D]; unfold zdisjoint in D; cbn [fst snd] in D; lia.
Qed.
(* the user bytes of a reader block hold no range of U: U's ranges are block heads (fs_heads) *)
Lemma fsw_pf_heads_out : forall ly S U (W : world tfibsegs) mem md q m x, AR tfibsegs B ly S W mem md ->
  fs_heads B ly S U -> In (q - HEAD, m + HEAD) (ablocks B ly S) -> 0 < m -> q <= x < q + m ->
  forall r, In r U -> ~ (fst r <= x < fst r + snd r).
Proof.
intros ly S U W mem md q m x HAR FH Hb Hm Hx r Hr Hin.
destruct (FH r Hr) as (E16 & m' & Hm' & M16).
pose proof (req_size_pos (m + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
destruct (Z.eq_dec (fst r) (q - HEAD)) as [Eq|Ne]; [unfold HEAD in *; lia|].
destruct (fsw_pf_blk_disj ly S W mem md (fst r) m' (q - HEAD) (m + HEAD) HAR Hm' Hb Ne) as [D|D];
  unfold HEAD in *; lia.
Qed.
(* nor does an image byte or a byte at or above alloc_ceiling: U's ranges lie in live blocks *)
Lemma fsw_pf_img_out : forall ly S U (W : world tfibsegs) mem md x, AR tfibsegs B ly S W mem md ->
  upoison_ok B ly S U -> in_img tfibsegs x -> forall r, In r U -> ~ (fst r <= x < fst r + snd r).
Proof.
intros ly S U W mem md x HAR OK Hi r Hr Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (upoison_ok_In B ly S U r OK Hr) as (_ & _ & _ & p & k & Hb & Hp & Hq).
apply (blk_img tfibsegs B LAWS ly S W mem md p k x HAR Hb); [lia | exact Hi].
Qed.
Lemma fsw_pf_high_out : forall ly S U (W : world tfibsegs) mem md x, AR tfibsegs B ly S W mem md ->
  upoison_ok B ly S U -> alloc_ceiling <= x -> forall r, In r U -> ~ (fst r <= x < fst r + snd r).
Proof.
intros ly S U W mem md x HAR OK Hx r Hr Hin.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
destruct (upoison_ok_In B ly S U r OK Hr) as (_ & _ & _ & p & k & Hb & Hp & Hq).
destruct (al_blocks _ _ LAWS ly S W mem md p k HAR Hb) as (_ & _ & Hpc & _). lia.
Qed.
(* an address below the shadow or at / above kHighMemBeg is no user-poisoned shadow byte *)
Lemma fsw_pf_unp : forall ly S U (W : world tfibsegs) mem md a, ARU tfibsegs B ly S U W mem md -> 0 <= a < 2 ^ 64 ->
  (a < SHADOW_OFF \/ kHighMemBeg <= a) -> unpoison U mem (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros ly S U W mem md a H Ha Hlo. apply unpoison_out. rewrite (wz a Ha).
destruct (in_ush U a) eqn:E; [exfalso|reflexivity].
assert (UF : aowned B ly S a /\ SHADOW_OFF <= a < kHighMemBeg) by (eapply ush_facts; eassumption). lia.
Qed.
End pf.
Ltac pf_reg HS :=
  rewrite (st_ok_restrict_reg tfibsegs _ _ _ _ _ HS);
  lazymatch goal with |- context [sr_get ?sr ?q] =>
    let e := eval vm_compute in (sr_get sr q) in change (sr_get sr q) with e end.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* the dynamic shadow base's two cells, as FSW_K's entry asks them: S0's one named hypothesis
   (lib/B/FSH_Base.v:112-114 FsShadowSyms, as lib/A/FSW_put.v takes lib/A/FSH_Base.v's).
   put_spec does not carry it, see the lane report. *)
Hypothesis HSS : FsShadowSyms B.
(* the runtime contracts (lib/B/FSH_Rt.v:111) and the image facts (:76): the FAST arm calls __asan_memcpy
   (fr_memcpy) and reads fs's read-only literals through fs_img_facts' cstr_ok. put_failed_run uses neither. *)
(* only the PC_memcpy interceptor's contract, FSH_Rt.v's FsRt field fr_memcpy (:117): the walk projects nothing else
   from the runtime record, so it takes just this field (lib/A/FSW_put.v at e78287af146 does the same). *)
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis IMG : fs_img_facts tfibsegs B.

Lemma put_failed_run :
  forall ly S U W regs mem md ch ot o s n buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  0 <= s /\ s + n <= alloc_ceiling ->
  cap <= WMAX ->
  failed <> 0 ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
    (fun W' c' => exists (st' : WriterApp.wst) buf' U',
       st' = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs /\
       uswap U U' buf buf' cap /\
       wpost B tfibsegs STK_put ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
         regs ly S U W mem md (3 * wcalls st') U'
         (fun ly' S' W' regs' mem' md' =>
            wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st')
              (WriterApp.w_text st') /\
            wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
            bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
            wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
            (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
               fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st' - cap) peak'
                 (WriterApp.w_cnt st') (WriterApp.w_fail st')) /\
            (forall i, 0 <= i < n -> mbyte tfibsegs (mrestrict (w_H W') mem') (s + i)
                                   = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)))
         W' c').
Proof.
intros ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
  HPRE G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HSRC HCAP HFAIL.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold w64 in G10, G11, G12.
destruct HSRC as [Hs0 Hsn].
assert (HF112 : 112 <= STK_put) by (vm_compute; discriminate).
assert (HFPv : FRAME_put = 112) by reflexivity.
(* ---- the entry facts ---- *)
destruct HPRE as (HPREU & HRO).
pose proof (fsw_ARU B STK_put ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
assert (Hfail1 : failed = 1) by lia. subst failed.
assert (Ho47 : o + 32 <= 2 ^ 47) by lia.
assert (Hoceil : alloc_ceiling + 112 <= o) by lia.
assert (Hceil0 : 0 < alloc_ceiling) by lia.
(* ---- the entry environment ---- *)
set (E := Ereg regs fs_extraT) in *.
assert (E2 : bv_unsigned (ew E 2) = spZ regs)
  by (unfold E; rewrite (ew_Ereg_nat regs fs_extraT 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 o)
  by (unfold E; rewrite (ew_Ereg_nat regs fs_extraT 10 10%bv eq_refl); exact G10).
assert (E10u : bv_unsigned (ew E 10) = o) by (rewrite E10; apply wz; lia).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF)
  by (unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
(* ---- the entry symbolic state ---- *)
assert (HS : st_ok tfibsegs E fsw_put_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_put) mem (seg_rom tfibsegs)))).
{ unfold fsw_put_ss0.
  apply (fsw_entryT_args B STK_put FRAME_put ly S U W regs mem md ch A_put [fsw_put_o_region] fsw_put_gf
    (proj1 HSS) (proj2 HSS) HPREU).
  - split; vm_compute; discriminate.
  - vm_compute; reflexivity.
  - fold E. constructor; [|constructor].
    unfold fsw_put_o_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10u. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val tfibsegs E _ o 24 4 (SLit 1) 1);
      [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
      | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vfail].
  - fold E. apply pairwise_disjoint_of_extents.
    unfold fsT_regions_args, fsT_regions, fstk, fs_got_region, fs_bcell_region, fsw_put_o_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E10u.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FRAME_put.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - fold E. unfold fsw_put_gf. cbn [atoms_ok]. split; [|exact I].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10u.
    change (2 ^ 3) with 8. split; [lia | split; [exact Ho8 | lia]]. }
(* ---- the journal, window top raised to ot (FSH_Fn_FORM.md 3a) ---- *)
assert (HJ0 : ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
                ly S W (unpoison U mem) md [] ly S W (unpoison U mem) md 0).
{ apply (fsw_ajournal_init_ot B STK_put (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W regs mem md ch ot HPREU);
    [lia | exact Hot16 | exact Hottop | exact HPRESENT]. }
(* ---- the shadow entry of o's 32 bytes, on the MACHINE's memory ---- *)
assert (HLO : layout_ok ly) by exact (am_layout _ _ _ _ (proj1 HAR)).
pose proof (lo_top ly HLO) as LTOP.
assert (Hlo8 : ly_stk_lo ly mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & L5 & _). unfold page_aligned in L5.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L5]]. }
assert (Hhi8 : ly_stk_hi ly mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & _ & L6 & _). unfold page_aligned in L6.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L6]]. }
assert (HRA32 : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF o 32).
{ assert (HZS : zero_shadow (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF
                  (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)).
  { exact (al_zshadow _ _ LAWS ly S W (unpoison U mem) md
             (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) HAR (or_introl eq_refl)). }
  assert (HRAU : range_addressable (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF o 32).
  { eapply range_addressable_sub;
      [ apply (zero_shadow_range (aview tfibsegs (w_H W) (unpoison U mem)) SHADOW_OFF
                 (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) Hlo8
                 ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS)
      | lia | lia]. }
  (* the stack's shadow does not depend on U (a Theorem Labs lane's lib/A/FSupoisonStack.v, taken by path) *)
  exact (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly S U W mem md (w_H W) o 32 HARU0 ltac:(lia) ltac:(lia)) HRAU). }
assert (SHOK : sh_ok tfibsegs fs_Bx fsw_put_SH E (mrestrict (w_H W) mem)).
{ unfold fsw_put_SH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 10%nat o 32 o 0 32 HRA32).
  - unfold fs_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 10 o E10). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. lia. }
(* ---- the run and the return. The post is put_spec's, with st' = put1 ... bs already read off: on this arm put1
   is the identity, so w_failed = 1, w_text = text, w_cap = cap, w_cnt = cnt, w_fail = fail, and the journal's
   k = 3 * wcalls st' = 0 (put1 records no allocator call on this arm) ---- *)
assert (MAIN : SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
  (fpostU tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md 0 U
     (fun (ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word)
          (mem' : word -> option byte) (md' : Model) =>
        wout_ok B tfibsegs ly' S' W' mem' o buf cap 1 text /\
        wbudget_kept S S' 1 cap cnt 1 cap cnt /\
        bswap (ablocks B ly S) (ablocks B ly' S') buf buf cap cap /\
        wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
        (exists peak', peak <= peak' <= Z.max peak (live - cap + cap) /\
           fs_glob tfibsegs W' mem' (live + cap - cap) peak' cnt fail) /\
        (forall i, 0 <= i < n -> mbyte tfibsegs (mrestrict (w_H W') mem') (s + i)
                               = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i))))).
{ unfold cfg_at.
  fsw_aj_run_tokU fsw_put_tbl_ok HS HJ0 HARU0 SHOK fs_Bspan.
  - (* the writes of the run: only put's own frame, inside the journal's window *)
    cbv [fsw_put_ss0 fss0T_args fsT_regions_args fsT_regions ss_mem app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
      [reflexivity | rewrite E2; lia | cbv [fstk YP09.r_wlo]; unfold FRAME_put; lia
      | cbv [fstk YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fsw_put_o_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil.
  - (* at the return instruction *)
    (* every byte outside put's own frame is the entry byte *)
    assert (MEQ : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FRAME_put <= a < spZ regs) ->
      ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hin & Hr).
      cbv [fsw_put_ss0 fss0T_args fsT_regions_args fsT_regions ss_mem app In] in Hin.
      destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
        cbv [fstk fs_got_region fs_bcell_region fsw_put_o_region
             YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        try (rewrite E2 in Hr); lia. }
    assert (MWE : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FRAME_put <= a < spZ regs) ->
      mrestrict (w_H W) (ms_mem ms) (Z_to_bv 64 a) = mrestrict (w_H W) mem (Z_to_bv 64 a))
      by (intros a Ha Hna; unfold mrestrict; rewrite (MEQ a Ha Hna); reflexivity).
    assert (MB : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - FRAME_put <= a < spZ regs) ->
      mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a)
      by (intros a Ha Hna; unfold mbyte; rewrite (MWE a Ha Hna); reflexivity).
    assert (SB : same_below mem (ms_mem ms) alloc_ceiling)
      by (intros x Hx; apply MEQ; unfold FRAME_put; lia).
    assert (MVH : forall a k v, spZ regs <= a -> a + Z.of_nat k <= 2 ^ 64 ->
      val_mem tfibsegs (mrestrict (w_H W) mem) a k v ->
      val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms)) a k v)
      by (intros a k v Ha Hk Hv i Hi; rewrite (MB (a + Z.of_nat i) ltac:(lia) ltac:(lia)); exact (Hv i Hi)).
    (* the out-object is unchanged *)
    assert (HOUT' : wout_ok B tfibsegs ly S W (ms_mem ms) o buf cap 1 text).
    { unfold wout_ok. split; [exact Ho8|]. split; [exact Ho0|]. split; [exact Hotop|]. split.
      { intros i Hi. destruct (HOW i Hi) as [Hw Hp]. split.
        - exact (proj1 (fsw_put_writable_eq (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) (o + i)
                   (MWE (o + i) ltac:(lia) ltac:(lia))) Hw).
        - destruct Hp as (Hh & b & Hb). split; [exact Hh|]. exists b.
          rewrite (MEQ (o + i) ltac:(lia) ltac:(lia)). exact Hb. }
      split; [exact Hbuf64|]. split; [exact Hcap64|].
      split; [exact (MVH o 8%nat buf ltac:(lia) ltac:(lia) Vbuf)|].
      split; [exact (MVH (o + 8) 8%nat (Z.of_nat (length text)) ltac:(lia) ltac:(lia) Vlen)|].
      split; [exact (MVH (o + 16) 8%nat cap ltac:(lia) ltac:(lia) Vcap)|].
      split; [exact (MVH (o + 24) 4%nat 1 ltac:(lia) ltac:(lia) Vfail)|].
      split; [exact Hf01|]. split; [exact Htok|].
      destruct Hcase as [Hz | (Hj & HRB & Hlt & HZB)]; [left; exact Hz | right].
      pose proof HRB as (Hin & Hb16 & Hcap0 & Vhead).
      destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin)
        as (_ & Hb4096 & Hbceil & _ & _ & _ & _).
      pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (RQ1 & RQ2).
      split; [exact Hj|]. split; [|split; [exact Hlt|]].
      - unfold fs_rblock. split; [exact Hin|]. split; [exact Hb16|]. split; [exact Hcap0|].
        exact (val_mem_below (w_H W) mem (ms_mem ms) alloc_ceiling (buf - HEAD) 8%nat cap SB
                 ltac:(unfold HEAD in *; lia) ltac:(unfold HEAD in *; lia) Vhead).
      - unfold zbytes_at in HZB |- *. apply (garr8_frame tfibsegs _ _ buf (text ++ [0]) HZB).
        intros a Ha. rewrite length_app in Ha. cbn [length] in Ha.
        apply (mbyte_below (w_H W) mem (ms_mem ms) alloc_ceiling a SB). unfold HEAD in *. lia. }
    (* the window slack outside the object *)
    assert (HKEEP : wkeep tfibsegs W W mem (ms_mem ms) (spZ regs) ot o 32).
    { intros a Ha Hno. split.
      - apply MB; lia.
      - exact (fsw_put_writable_eq (mrestrict (w_H W) mem) (mrestrict (w_H W) (ms_mem ms)) a
                 (MWE a ltac:(lia) ltac:(lia))). }
    (* the globals and the source bytes *)
    assert (HGLOB' : fs_glob tfibsegs W (ms_mem ms) live peak cnt fail)
      by exact (fs_glob_below W mem (ms_mem ms) live peak cnt fail SB HGLOB).
    assert (HSRCB : forall i, 0 <= i < n ->
      mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms)) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i))
      by (intros i Hi; apply (mbyte_below (w_H W) mem (ms_mem ms) alloc_ceiling (s + i) SB); lia).
    (* the callee-saved registers and the return address *)
    assert (R1 : getr (ms_regs ms) 1%bv = getr regs 1%bv).
    { lazymatch type of HS with
      | st_ok _ _ ?ssf _ =>
        exact (fsw_reg_atom (w_H W) regs fs_extraT ssf ms 1%bv 1%bv 1%nat HS
                 ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity))
      end. }
    eapply (fsw_retU B fsw_put_tbl fsw_put_tbl_ok).
    + exact HS.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
    + rewrite R1. exact Hra.
    + exact HJ0.
    + exact HARU0.
    + lazymatch type of HS with
      | st_ok _ _ ?ssf _ =>
        apply (fsw_preserved (w_H W) E ssf ms regs (fun r : bv 5 => sr_get (ss_regs ssf) r) HS);
        [vm_compute; reflexivity|];
        let r := fresh "r" in let Hr := fresh "Hr" in
        intros r Hr; cbv [CALLEE_SAVED In] in Hr;
        repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
      end;
      cbv beta;
      lazymatch goal with
      | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
      end;
      rewrite fsw_SOff0; apply ew_Ereg_nat; vm_compute; reflexivity.
    + intros matq. split; [exact HOUT'|].
      split; [unfold wbudget_kept; split; [exact HCAP|]; split; lia|].
      split; [left; split; [reflexivity | split; reflexivity]|].
      split; [exact HKEEP|].
      split; [exists peak; split; [split; [lia | apply Z.le_max_l]|];
              replace (live + cap - cap) with live by lia; exact HGLOB'|].
      exact HSRCB. }
(* ---- the spec's post: on this arm put1 is the identity, U and the buffer do not move ---- *)
eapply SRr_mono; [exact MAIN|].
cbv beta. intros W2 c2 Hle HP.
exists (WriterApp.mkW 1 text cap cnt fail []), buf, U.
split; [reflexivity|].
split; [left; split; reflexivity|].
unfold wpost. exact HP.
Qed.
Lemma put_fast_run :
  forall ly S U W regs mem md ch ot o s n buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  zbytes_at tfibsegs W mem s bs -> wsrc_kept B tfibsegs ly S U W mem buf s bs -> Z.of_nat (length bs) = n ->
  WriterSpec.bytes_ok bs ->
  0 <= s /\ s + n <= alloc_ceiling -> (s + n <= o \/ ot <= s) ->
  Z.of_nat (length text) + n + 1 <= WMAX ->
  cap <= WMAX ->
  wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) ->
  failed = 0 -> Z.of_nat (length text) + n + 1 <= cap ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
    (fun W' c' => exists (st' : WriterApp.wst) buf' U',
       st' = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs /\
       uswap U U' buf buf' cap /\
       wpost B tfibsegs STK_put ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
         regs ly S U W mem md (3 * wcalls st') U'
         (fun ly' S' W' regs' mem' md' =>
            wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st')
              (WriterApp.w_text st') /\
            wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
            bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
            wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
            (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
               fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st' - cap) peak'
                 (WriterApp.w_cnt st') (WriterApp.w_fail st')) /\
            (forall i, 0 <= i < n -> mbyte tfibsegs (mrestrict (w_H W') mem') (s + i)
                                   = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)))
         W' c').
Proof.
intros ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
  HPRE FH G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj HWM HCAP
  HBUD HF0 HFAST.
subst failed.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold w64 in G10, G11, G12.
destruct HSRC as [Hs0 Hsn].
assert (HSTK : 4208 <= STK_put) by (vm_compute; discriminate).
unfold WMAX in HWM, HCAP.
(* ---- the entry facts ---- *)
destruct HPRE as (HPREU & HRO).
pose proof (fsw_ARU B STK_put ly S U W regs mem md ch HPREU) as HARU0.
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hsp16 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch HPREU) as (Hal16 & Hspc & Hsp47 & _).
destruct HOUT as (Ho8 & Ho0 & Hotop & HOW & Hbuf64 & Hcap64 & Vbuf & Vlen & Vcap & Vfail & Hf01 & Htok & Hcase).
destruct Hcase as [(Hc0 & _) | (Hj & HRB & Hlt & HZB)]; [lia|].
pose proof HRB as (Hin & Hb16 & Hcap0 & Vhead).
destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin)
  as (_ & Hb4096 & Hbceil & Hbapp & _ & _ & HbM).
assert (RQB : req_size (cap + HEAD) = cap + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (cap + 16) 0); lia).
rewrite RQB in Hbceil, Hbapp. unfold in_app, kLowShadowBeg, ASAN_CEIL, HEAD in Hbapp. unfold HEAD in Hbceil, Hb4096.
set (len := Z.of_nat (length text)) in *.
assert (Hlen0 : 0 <= len) by (unfold len; lia).
assert (Hn0 : 0 <= n) by lia.
assert (Ho47 : o + 32 <= 2 ^ 47) by lia.
assert (Hoc : alloc_ceiling + STK_put <= o) by lia.
(* the bytes [d, d + n] put writes below alloc_ceiling are buffer bytes, so no image byte *)
assert (BNI : forall t, buf <= t < buf + cap -> ~ in_img tfibsegs t).
{ intros t Ht. apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) t HAR Hin).
  rewrite RQB. unfold HEAD. lia. }
(* ---- the source range: addressable, visible, in the application ranges, outside the buffer's block ---- *)
assert (SRC : range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF s n /\
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) mem) s n) /\ amem_range s n /\
  (forall x, s <= x < s + n -> ~ (buf - HEAD <= x < buf + cap))).
{ destruct HSK as [[Hbs Ham] | [(p & k & Hpb & Hrb & Hps & Hpk) | [(p & k & Hpb & Hin2 & Hps & Hpk & HU) | (l & Hl & Hll)]]].
  - (* nothing read *)
    subst bs. cbn in Hlen. subst n.
    split; [apply range_addressable_nil; lia|]. split; [lia|]. split; [exact Ham | intros x Hx; lia].
  - (* the user bytes of another reader block *)
    rewrite Hlen in Hpk. pose proof Hrb as (Hin2 & Hp16 & Hk0 & _).
    destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) HAR Hin2) as (_ & Hp4096 & Hpceil & Hpapp & _).
    assert (RQ : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
    rewrite RQ in Hpceil, Hpapp. unfold in_app, kLowShadowBeg, ASAN_CEIL, HEAD in Hpapp. unfold HEAD in Hpceil, Hp4096.
    assert (OUT : forall x, s <= x < s + n -> in_ush U (shadow_addr x) = false).
    { intros x Hx. apply (fsw_pf_ush_out B ly S U x HUOK); [lia|].
      exact (fsw_pf_heads_out B ly S U W (unpoison U mem) md p k x HAR FH Hin2 Hk0 ltac:(lia)). }
    split.
    { apply (fsw_pf_ra_raw (w_H W) U mem s n); [lia | lia | exact OUT |].
      apply (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) s n HAR Hin2);
        rewrite ?RQ; unfold HEAD; lia. }
    split.
    { intros Hn1. apply (fsw_pf_hull_raw W U mem s n HUPO); [lia | lia |].
      apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) s n HAR Hin2);
        rewrite ?RQ; unfold HEAD; lia. }
    split; [unfold amem_range; lia|].
    intros x Hx Hxb.
    destruct (fsw_pf_blk_disj B ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) (buf - HEAD) (cap + HEAD) HAR Hin2 Hin
      ltac:(unfold HEAD; lia)) as [D|D]; rewrite ?RQ, ?RQB in D; unfold HEAD in *; lia.
  - (* any other live block, the range avoiding U *)
    rewrite Hlen in Hpk, HU.
    destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p k HAR Hin2) as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & HkM).
    pose proof (req_size_pos k ltac:(lia)) as (RQ1 & RQ2).
    unfold in_app, kLowShadowBeg, ASAN_CEIL in Hpapp.
    assert (OUT : forall x, s <= x < s + n -> in_ush U (shadow_addr x) = false).
    { intros x Hx. apply (fsw_pf_ush_out B ly S U x HUOK); [lia|].
      intros r Hr Hxr. destruct (HU r Hr); lia. }
    split.
    { apply (fsw_pf_ra_raw (w_H W) U mem s n); [lia | lia | exact OUT |].
      apply (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem) md p k s n HAR Hin2); lia. }
    split.
    { intros Hn1. apply (fsw_pf_hull_raw W U mem s n HUPO); [lia | lia |].
      apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (unpoison U mem) md p k s n HAR Hin2); lia. }
    split; [unfold amem_range; lia|].
    intros x Hx Hxb.
    destruct (fsw_pf_blk_disj B ly S W (unpoison U mem) md p k (buf - HEAD) (cap + HEAD) HAR Hin2 Hin Hpb) as [D|D];
      rewrite ?RQB in D; unfold HEAD in *; lia.
  - (* a prefix of a read-only literal: fs_img_facts' cstr_ok, on the image *)
    destruct (fsw_pf_ro_strs_img s l Hl) as (Hl0 & Hl1).
    assert (Hnl : n <= Z.of_nat (length l) + 1).
    { pose proof (proj1 (Nat2Z.inj_le _ _) Hll) as H'. rewrite Nat2Z.inj_succ in H'. lia. }
    assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem))).
    { intros a Ha Hno Hne. pose proof (fsw_pf_roP_low a Ha) as Ha'.
      rewrite (aview_at tfibsegs (w_H W) (unpoison U mem) mem a); [exact (HRO a Ha Hno Hne)|].
      apply (fsw_pf_unp B ly S U W mem md a HARU0); unfold SHADOW_OFF in *; lia. }
    pose proof IMG as (_ & IMG2).
    destruct (IMG2 ly S W (unpoison U mem) md HAR HRO') as (_ & _ & HSTRS & _).
    destruct (proj1 (Forall_forall _ _) HSTRS (s, l) Hl) as (Hcs & _). cbn [fst snd] in Hcs.
    destruct Hcs as (_ & Hs4096 & Hsl & Hl32 & Hamr & HRA & HHULL & _).
    assert (OUT : forall x, s <= x < s + n -> in_ush U (shadow_addr x) = false).
    { intros x Hx. apply (fsw_pf_ush_out B ly S U x HUOK); [lia|].
      apply (fsw_pf_img_out B ly S U W (unpoison U mem) md x HAR HUOK). apply fsw_pf_in_img. lia. }
    split.
    { apply (fsw_pf_ra_raw (w_H W) U mem s n); [lia | lia | exact OUT |].
      eapply range_addressable_sub; [exact HRA | lia | lia]. }
    split.
    { intros Hn1. apply (fsw_pf_hull_raw W U mem s n HUPO); [lia | lia |].
      intros t Ht. apply HHULL. unfold shadow_addr in *. lia. }
    split; [unfold amem_range in *; lia|].
    intros x Hx Hxb. apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) x HAR Hin);
      [rewrite RQB; unfold HEAD in *; lia|]. apply fsw_pf_in_img. lia. }
destruct SRC as (SRA & SHULL & SAMR & SDISJ).

(* ---- the entry environment: atoms 33 / 34 / 35 are o's buf / len / cap (FSW_K xatom 0..2) ---- *)
set (xs := [Z_to_bv 64 buf; Z_to_bv 64 len; Z_to_bv 64 cap]).
set (E := Ereg regs (fs_extraT ++ xs)).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); reflexivity).
assert (E10 : ew E 10 = Z_to_bv 64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 s) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact G11).
assert (E12 : ew E 12 = Z_to_bv 64 n) by (unfold E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact G12).
assert (E32 : ew E 32 = Z_to_bv 64 SHADOW_OFF) by (unfold E; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E33 : ew E 33 = Z_to_bv 64 buf) by (unfold E; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E34 : ew E 34 = Z_to_bv 64 len) by (unfold E; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E35 : ew E 35 = Z_to_bv 64 cap) by (unfold E; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
assert (E10u : bv_unsigned (ew E 10) = o) by (rewrite E10; apply wz; lia).
assert (E12u : bv_unsigned (ew E 12) = n) by (rewrite E12; apply wz; lia).
assert (E33u : bv_unsigned (ew E 33) = buf) by (rewrite E33; apply wz; lia).
assert (E34u : bv_unsigned (ew E 34) = len) by (rewrite E34; apply wz; lia).
assert (E35u : bv_unsigned (ew E 35) = cap) by (rewrite E35; apply wz; lia).
(* ---- the entry symbolic state ---- *)
assert (HS : st_ok tfibsegs E fsw_pf_ss0
  (restrict (w_H W) (mkst regs (Z_to_bv 64 A_put) mem (seg_rom tfibsegs)))).
{ unfold fsw_pf_ss0.
  apply (fsw_entryT_argsX B STK_put FRAME_put ly S U W regs mem md ch A_put [fsw_pf_o_region] fsw_pf_gf xs
    (proj1 HSS) (proj2 HSS) HPREU).
  - split; vm_compute; discriminate.
  - vm_compute; reflexivity.
  - fold E. constructor; [|constructor].
    unfold fsw_pf_o_region, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E10u. split; [lia|]. split; [lia|]. split; [intros q Hq; lia|].
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (chunk_ok_val tfibsegs E _ o 0 8 (SOff 33 0) buf);
        [rewrite fsw_SOff0; exact E33 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | rewrite Z.add_0_r; exact Vbuf].
    + apply (chunk_ok_val tfibsegs E _ o 8 8 (SOff 34 0) len);
        [rewrite fsw_SOff0; exact E34 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Vlen].
    + apply (chunk_ok_val tfibsegs E _ o 16 8 (SOff 35 0) cap);
        [rewrite fsw_SOff0; exact E35 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia | exact Vcap].
    + apply (chunk_ok_val tfibsegs E _ o 24 4 (SLit 0) 0);
        [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
        | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact Vfail].
  - fold E. apply pairwise_disjoint_of_extents.
    unfold fsT_regions_args, fsT_regions, fstk, fs_got_region, fs_bcell_region, fsw_pf_o_region, extent_of_region.
    cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E2, E10u.
    unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address, FRAME_put.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat match goal with |- _ /\ _ => split end; try exact I; first [right; lia | left; lia].
  - fold E. unfold fsw_pf_gf. cbn [atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E10u, E33u, E34u, E35u, E12u. unfold fsw_pf_CEIL.
    change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; lia. }
(* ---- the journal, window top raised to ot (FSH_Fn_FORM.md 3a); the run costs no tick ---- *)
assert (HJ0 : ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
                ly S W (unpoison U mem) md [] ly S W (unpoison U mem) md 0).
{ apply (fsw_ajournal_init_ot B STK_put (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S U W regs mem md ch ot HPREU);
    [lia | exact Hot16 | exact Hottop | exact HPRESENT]. }
(* ---- the shadow entry of o's 32 bytes, on the MACHINE's memory (as put_failed_run) ---- *)
assert (HLO : layout_ok ly) by exact (am_layout _ _ _ _ (proj1 HAR)).
pose proof (lo_top ly HLO) as LTOP.
assert (Hlo8 : ly_stk_lo ly mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & L5 & _). unfold page_aligned in L5.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L5]]. }
assert (Hhi8 : ly_stk_hi ly mod 8 = 0).
{ destruct LTOP as (_ & _ & _ & _ & _ & L6 & _). unfold page_aligned in L6.
  apply Z.mod_divide; [lia|]. apply (Z.divide_trans 8 4096);
    [exists 512; reflexivity | apply Z.mod_divide; [lia | exact L6]]. }
(* o's 32 bytes are addressable on any memory where AR holds over U: the stack's shadow is 0 and no range of U is
   above alloc_ceiling *)
assert (RAO : forall (m : word -> option byte) md',
  ARU tfibsegs B ly S U W m md' -> range_addressable (aview tfibsegs (w_H W) m) SHADOW_OFF o 32).
{ intros m md' HARm.
  assert (HZS0 : zero_shadow (aview tfibsegs (w_H W) (unpoison U m)) SHADOW_OFF
                  (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly)).
  { exact (al_zshadow _ _ LAWS ly S W (unpoison U m) md'
             (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) (proj1 HARm) (or_introl eq_refl)). }
  (* the stack's shadow does not depend on U (FSupoisonStack, a Theorem Labs lane) *)
  apply (proj1 (fsw_ARU_stack_ra tfibsegs B LAWS ly S U W m md' (w_H W) o 32 HARm ltac:(lia) ltac:(lia))).
  eapply range_addressable_sub;
    [ apply (zero_shadow_range (aview tfibsegs (w_H W) (unpoison U m)) SHADOW_OFF
               (ly_stk_lo ly) (ly_stk_hi ly - ly_stk_lo ly) Hlo8
               ltac:(rewrite Zminus_mod, Hlo8, Hhi8; reflexivity) HZS0)
    | lia | lia]. }
assert (SHOK : sh_ok tfibsegs fs_Bx fsw_pf_SH E (mrestrict (w_H W) mem)).
{ unfold fsw_pf_SH. constructor; [|constructor].
  apply (shent_ok_of_range tfibsegs (w_H W) mem E fs_Bx 10%nat o 32 o 0 32 (RAO mem md HARU0)).
  - unfold fs_Bx. apply (U_atom E 32 SHADOW_OFF E32). unfold SHADOW_OFF; lia.
  - apply (U_atom E 10 o E10). lia.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. lia. }

(* ---- the run: prologue, the shadow check of o, the cap test, UBSan's overflow check of buf + len, the memcpy call,
   the length store, UBSan's overflow check of buf + len + n, the 0 store, the epilogue. The post is put_spec's, with
   st' = put1 ... bs read off: on this arm put1 appends bs, the buffer and U do not move, and the journal count
   3 * (wbud 0 cap - wbud 0 cap) is 0 ---- *)
assert (MAIN : SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
  (fpostU tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) regs ly S U W mem md 0 U
     (fun (ly' : alayout) (S' : astate) (W' : world tfibsegs) (regs' : bvmap 5 word)
          (mem' : word -> option byte) (md' : Model) =>
        wout_ok B tfibsegs ly' S' W' mem' o buf cap 0 (text ++ bs) /\
        wbudget_kept S S' 0 cap cnt 0 cap cnt /\
        bswap (ablocks B ly S) (ablocks B ly' S') buf buf cap cap /\
        wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
        (exists peak', peak <= peak' <= Z.max peak (live - cap + cap) /\
           fs_glob tfibsegs W' mem' (live + cap - cap) peak' cnt fail) /\
        (forall i, 0 <= i < n -> mbyte tfibsegs (mrestrict (w_H W') mem') (s + i)
                               = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i))))).
{ unfold cfg_at.
  (* run 1: to the cap test 0x8454c *)
  fsw_aj_run_tokU fsw_put_tbl_ok HS HJ0 HARU0 SHOK fs_Bspan.
  - cbv [fsw_pf_ss0 fss0T_args fsT_regions_args fsT_regions ss_mem app].
    eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
      [reflexivity | rewrite E2; lia | cbv [fstk YP09.r_wlo]; unfold FRAME_put; lia
      | cbv [fstk YP09.r_whi]; lia |].
    apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_cons_ro; [cbv [fsw_pf_o_region YP09.r_wlo YP09.r_whi]; lia|].
    apply awr_ok_nil.
  - (* the run wrote only put's frame *)
    assert (M1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
      ms_mem ms (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
    { intros a Ha Hna. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
      vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E2 in Hr; lia. }
    pose proof (fun a => apresent_grows _ _ _ a HG) as PR1.
    clear HF HFr HG.
    (* the cap test 0x8454c: the fast side *)
    srr_branch_tok fsw_put_tbl_ok HS SHOK fs_Bspan.
    2: { exfalso. rewrite branch_geu_U in Hc.
         assert (UA : YP0e.U E (SOff 35 0) = cap) by (apply (U_atom E 35 cap E35); lia).
         assert (UB : YP0e.U E (SAlu ALU_ADD (SOff 12 1) (SOff 34 0)) = n + 1 + len).
         { rewrite U_SAlu, (U_atom E 34 len E34) by lia. rewrite U_SOff, E12u. cbn [zalu_raw].
           rewrite (zcanon_id (n + 1)) by (unfold M64; lia). apply zcanon_id. unfold M64; lia. }
         rewrite UA, UB in Hc. apply negb_false_iff in Hc. apply Z.ltb_lt in Hc. lia. }
    clear Hc.
    (* run 2: to UBSan's pointer-overflow check of buf + len, 0x845c0 *)
    fsw_aj_run_tokU fsw_put_tbl_ok HS HJ0 HARU0 SHOK fs_Bspan.
    + lazymatch goal with |- context C [ss_mem ?ssx] =>
        let rs' := eval vm_compute in (ss_mem ssx) in
        let g := context C [rs'] in change g end.
      eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
        [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |].
      apply awr_ok_cons_ro; [cbn; lia|].
      apply awr_ok_cons_ro; [cbn; lia|].
      apply awr_ok_cons_ro; [cbn; lia|].
      apply awr_ok_nil.
    + lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => first [rename m into msB | idtac] end.
      assert (M2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
        ms_mem msB (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
      { intros a Ha Hna. rewrite <- (M1 a Ha Hna). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
        vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E2 in Hr; lia. }
      pose proof (fun a Ha => apresent_grows _ _ _ a HG (PR1 a Ha)) as PR2.
      clear M1 PR1 HF HFr HG.
      (* 0x845c0 `bltu buf + len, buf`: the taken side is UBSan's trap 0x84680, refuted at the branch: buf + len does
         not wrap (buf < alloc_ceiling, len < 2 ^ 27) *)
      srr_branch_tok fsw_put_tbl_ok HS SHOK fs_Bspan.
      1: { exfalso. rewrite branch_ltu_U in Hc.
           assert (UA : YP0e.U E (SAlu ALU_ADD (SOff 33 0) (SOff 34 0)) = buf + len).
           { rewrite U_SAlu, (U_atom E 33 buf E33), (U_atom E 34 len E34) by lia. cbn [zalu_raw].
             apply zcanon_id. unfold M64; lia. }
           rewrite UA, (U_atom E 33 buf E33) in Hc by lia. apply Z.ltb_lt in Hc. lia. }
      clear Hc.
      (* run 3: to the call of __asan_memcpy *)
      fsw_aj_run_tokU fsw_put_tbl_ok HS HJ0 HARU0 SHOK fs_Bspan.
      * lazymatch goal with |- context C [ss_mem ?ssx] =>
          let rs' := eval vm_compute in (ss_mem ssx) in
          let g := context C [rs'] in change g end.
        eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - ot);
          [reflexivity | rewrite E2; lia | cbn; lia | cbn; lia |].
        apply awr_ok_cons_ro; [cbn; lia|].
        apply awr_ok_cons_ro; [cbn; lia|].
        apply awr_ok_cons_ro; [cbn; lia|].
        apply awr_ok_nil.
      * lazymatch type of HS with st_ok _ _ _ (restrict _ ?m) => first [rename m into ms0 | idtac] end.
        assert (MT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
          ms_mem ms0 (Z_to_bv 64 a) = mem (Z_to_bv 64 a)).
        { intros a Ha Hna. rewrite <- (M2 a Ha Hna). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
          vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
            cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?E2 in Hr; lia. }
        pose proof (fun a Ha => apresent_grows _ _ _ a HG (PR2 a Ha)) as PRT.
        clear M2 PR2 HF HFr HG.

      (* ---- the call of __asan_memcpy (PC_memcpy 0x51d90, ra = 0x845e0): its registers ---- *)
      assert (Ems : ms0 = mkst (ms_regs ms0) (Z_to_bv 64 PC_memcpy) (ms_mem ms0) (seg_rom tfibsegs))
        by exact (st_ok_restrict_mkst tfibsegs (w_H W) E _ ms0 HS eq_refl).
      assert (RT1 : getr (ms_regs ms0) 1%bv = Z_to_bv 64 542176) by (pf_reg HS; reflexivity).
      assert (RT2 : spZ (ms_regs ms0) = spZ regs - 112).
      { unfold spZ at 1. pf_reg HS. change (bv_unsigned (sv_denot E (SOff 2 (-112)))) with (YP0e.U E (SOff 2 (-112))).
        rewrite U_SOff, E2. apply zcanon_id. unfold M64. lia. }
      assert (RT3 : getr (ms_regs ms0) 3%bv = getr regs 3%bv)
        by (pf_reg HS; rewrite fsw_SOff0; unfold E; apply ew_Ereg_nat; reflexivity).
      assert (RT4 : getr (ms_regs ms0) 4%bv = getr regs 4%bv)
        by (pf_reg HS; rewrite fsw_SOff0; unfold E; apply ew_Ereg_nat; reflexivity).
      assert (RT8 : getr (ms_regs ms0) 8%bv = Z_to_bv 64 o) by (pf_reg HS; rewrite fsw_SOff0; exact E10).
      assert (RT9 : getr (ms_regs ms0) 9%bv = Z_to_bv 64 n) by (pf_reg HS; rewrite fsw_SOff0; exact E12).
      assert (RT10 : getr (ms_regs ms0) 10%bv = w64 (buf + len)).
      { pf_reg HS. rewrite denot_lit_U. unfold w64. f_equal.
        rewrite U_SAlu, (U_atom E 33 buf E33), (U_atom E 34 len E34) by lia. cbn [zalu_raw].
        apply zcanon_id. unfold M64. lia. }
      assert (RT11 : getr (ms_regs ms0) 11%bv = w64 s) by (pf_reg HS; rewrite fsw_SOff0; exact E11).
      assert (RT12 : getr (ms_regs ms0) 12%bv = w64 n) by (pf_reg HS; rewrite fsw_SOff0; exact E12).
      assert (RT23 : getr (ms_regs ms0) 23%bv = Z_to_bv 64 SHADOW_OFF) by (pf_reg HS; rewrite fsw_SOff0; exact E32).
      (* s8 / s11: the shadow addresses of o + 8 and o, as the run left them (B only; re-seated at the resume) *)
      assert (RT24 : getr (ms_regs ms0) 24%bv = sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0)))
        by (pf_reg HS; reflexivity).
      assert (RT27 : getr (ms_regs ms0) 27%bv = sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)))
        by (pf_reg HS; reflexivity).
      (* the saved words of the frame at the call *)
      pose proof (st_ok_mem_ok tfibsegs E _ _ HS) as (_ & HRS & _).
      cbn [ms_mem restrict] in HRS. apply Forall_inv in HRS.
      destruct HRS as (_ & _ & _ & HCS). cbn [YP09.r_base YP09.r_chunks base_val] in HCS. rewrite E2 in HCS.
      rewrite Forall_forall in HCS.
      (* the call's premises *)
      set (d := buf + len) in *.
      assert (LOWT : forall t, 0 <= t < alloc_ceiling -> ms_mem ms0 (Z_to_bv 64 t) = mem (Z_to_bv 64 t))
        by (intros t Ht; apply MT; lia).
      assert (AVT : forall t, 0 <= t < alloc_ceiling ->
        aview tfibsegs (w_H W) (ms_mem ms0) t = aview tfibsegs (w_H W) mem t)
        by (intros t Ht; apply (aview_at tfibsegs); exact (LOWT t Ht)).
      lazymatch type of HARU0 with ARU _ _ _ _ _ _ _ ?mdT =>
        assert (HPREc : ecall_preU tfibsegs B ly S U W (ms_regs ms0) (ms_mem ms0) mdT) end.
      { eapply (fsw_ecall_preU_at B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (ms_regs ms0) (spZ regs - 112 - ot) HJ0 HARU0).
        - rewrite RT2. lia.
        - lia.
        - lia.
        - unfold ESTACK. lia.
        - unfold YK0s.ret_ok. rewrite RT1. apply bv_eq. vm_compute. reflexivity.
        - rewrite RT3. exact Hgp.
        - rewrite RT4. exact Htp. }

      assert (HDEST : dest_ok tfibsegs B ly S W (ms_regs ms0) (ms_mem ms0) d n).
      { intros a Ha.
        destruct (al_blocks _ _ LAWS ly S W (unpoison U (ms_mem ms0)) _ (buf - HEAD) (cap + HEAD) (proj1 HARU0) Hin)
          as (_ & _ & _ & _ & Hbp & _).
        destruct (Hbp a ltac:(rewrite RQB; unfold HEAD, d in *; lia)) as (Hpa & Hno).
        split; [|split; [exact Hno | rewrite RT2; unfold ESTACK, d in *; lia]].
        apply (apresent_writable tfibsegs). destruct Hpa as (Hh & b & Hb). split; [exact Hh|]. exists b.
        rewrite <- (fsw_pf_unp B ly S U W (ms_mem ms0) _ a HARU0); [exact Hb | unfold d in *; lia | unfold d, SHADOW_OFF in *; lia]. }
      assert (HAMRd : amem_range d n) by (unfold amem_range, d in *; lia).
      assert (HRAd : range_addressable (aview tfibsegs (w_H W) (ms_mem ms0)) SHADOW_OFF d n).
      { apply (fsw_pf_ra_raw (w_H W) U (ms_mem ms0) d n); [unfold d in *; lia | unfold d in *; lia | |].
        - intros x Hx. apply (fsw_pf_ush_out B ly S U x HUOK); [unfold d in *; lia|].
          exact (fsw_pf_heads_out B ly S U W (unpoison U mem) md buf cap x HAR FH Hin Hcap0 ltac:(unfold d in *; lia)).
        - apply (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U (ms_mem ms0)) _ (buf - HEAD) (cap + HEAD) d n
            (proj1 HARU0) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
      assert (HHULLd : 0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms0)) d n).
      { intros Hn1. apply (fsw_pf_hull_raw W U (ms_mem ms0) d n (proj2 (proj2 HARU0))); [unfold d in *; lia | unfold d in *; lia |].
        apply (shadow_hull_vis_of_block tfibsegs B LAWS ly S W (unpoison U (ms_mem ms0)) _ (buf - HEAD) (cap + HEAD) d n
          (proj1 HARU0) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
      assert (HCPY : 0 <= s /\ s + n <= 2 ^ 63 /\ src_ok tfibsegs W (ms_regs ms0) (ms_mem ms0) s n /\
        (d + n <= s \/ s + n <= d) /\ amem_range s n /\
        range_addressable (aview tfibsegs (w_H W) (ms_mem ms0)) SHADOW_OFF s n /\
        (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms0)) s n)).
      { split; [lia|]. split; [lia|]. split.
        { intros a Ha. split; [|rewrite RT2; unfold ESTACK; lia].
          rewrite AVT by lia. unfold zbytes_at in HZS.
          destruct (HZS (Z.to_nat (a - s)) ltac:(lia)) as (Hv & _). specialize (Hv 0%nat ltac:(lia)).
          replace (s + Z.of_nat (Z.to_nat (a - s)) + Z.of_nat 0) with a in Hv by lia.
          unfold aview. rewrite Hv. discriminate. }
        split.
        { destruct (Z_le_gt_dec (d + n) s); [left; lia|]. destruct (Z_le_gt_dec (s + n) d); [right; lia|].
          exfalso. apply (SDISJ (Z.max s d)); unfold d, HEAD in *; lia. }
        split; [exact SAMR|]. split.
        { eapply range_addressable_agree; [|exact SRA]. intros x Hx. apply AVT. unfold shadow_of_addr, SHADOW_OFF. lia. }
        intros Hn1 t Ht. rewrite AVT; [exact (SHULL Hn1 t Ht)|]. unfold shadow_addr, SHADOW_OFF in Ht. lia. }
      (* the call: __asan_memcpy (d, s, n) by the runtime contract, the journal put back on the memory after it *)
      rewrite Ems.
      eapply SRr_bind.
      { apply (fsw_intrin_atU B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap) ly S W (unpoison U mem) md []
          ly S U W (ms_mem ms0) _ 0 U
          (fun a => d <= a < d + n \/ spZ (ms_regs ms0) - ESTACK <= a < spZ (ms_regs ms0)) (w64 (raZ (ms_regs ms0))) _
          (fun regs' mem' md' => aregs_preserved (ms_regs ms0) regs' /\
             (forall i, 0 <= i < n -> aview tfibsegs (w_H W) mem' (d + i) = aview tfibsegs (w_H W) (ms_mem ms0) (s + i)) /\
             (forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ (ms_regs ms0) - ESTACK <= a < spZ (ms_regs ms0)) ->
                aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) (ms_mem ms0) a) /\
             (forall a, apresent (w_H W) (ms_mem ms0) a -> apresent (w_H W) mem' a)) HJ0).
        - eapply SRr_mono.
          { exact (RT_memcpy ly S U W (ms_regs ms0) (ms_mem ms0) _ d s n HPREc RT10 RT11 RT12
              ltac:(lia) ltac:(unfold d in *; lia) ltac:(unfold d in *; lia) HDEST HAMRd HRAd HHULLd HCPY). }
          cbv beta. intros W' c' _ (-> & regs' & mem' & md' & -> & HARU' & HP' & Hsame & H10 & Hcp & Hfr & Hpr).
          split; [reflexivity|]. exists regs', mem', md'.
          split; [reflexivity|]. split; [exact HARU'|]. split; [exact Hsame|].
          split.
          { intros a Ha HnW.
            destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
            - apply (aview_unpoison_in tfibsegs). exact EU.
            - rewrite !(aview_unpoison_out tfibsegs) by exact EU.
              apply Hfr; [exact Ha | intros Hx; apply HnW; left; exact Hx | intros Hx; apply HnW; right; exact Hx]. }
          split.
          { intros a (Hh & b & Hb). split; [exact Hh|].
            destruct (in_ush U (bv_unsigned (Z_to_bv 64 a))) eqn:EU.
            - exists (Z_to_bv 8 0). apply unpoison_in. exact EU.
            - rewrite (unpoison_out U mem' (Z_to_bv 64 a) EU). rewrite (unpoison_out U (ms_mem ms0) (Z_to_bv 64 a) EU) in Hb.
              destruct (Hpr a (conj Hh (ex_intro _ b Hb))) as (_ & b' & Hb'). exists b'. exact Hb'. }
          split; [exact HP'|]. split; [exact Hcp|]. split; [exact Hfr | exact Hpr].
        - intros a [Ha | Ha].
          + left. right. left. split.
            * exists (buf - HEAD, buf + cap). split.
              -- apply in_or_app. right. unfold wbuf_fp. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity.
              -- cbn [fst snd]. unfold d, HEAD in *. lia.
            * exists (buf - HEAD), (cap + HEAD). split; [exact Hin|]. rewrite RQB. unfold d, HEAD in *. lia.
          + left. left. rewrite RT2 in Ha. unfold ESTACK in Ha. lia. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & HP & HCP & HFR & HPR).

      (* ---- the resume at 0x845e0 ---- *)
      assert (ERA : w64 (raZ (ms_regs ms0)) = Z_to_bv 64 542176) by (unfold w64, raZ; rewrite RT1, wz; [reflexivity | lia]).
      rewrite ERA.
      assert (S2 : getr regs2 2%bv = getr (ms_regs ms0) 2%bv) by exact (HP 2 ltac:(unfold acallee_saved; lia)).
      assert (S3 : getr regs2 3%bv = getr (ms_regs ms0) 3%bv) by exact (HP 3 ltac:(unfold acallee_saved; lia)).
      assert (S4 : getr regs2 4%bv = getr (ms_regs ms0) 4%bv) by exact (HP 4 ltac:(unfold acallee_saved; lia)).
      assert (S8 : getr regs2 8%bv = getr (ms_regs ms0) 8%bv) by exact (HP 8 ltac:(unfold acallee_saved; lia)).
      assert (S9 : getr regs2 9%bv = getr (ms_regs ms0) 9%bv) by exact (HP 9 ltac:(unfold acallee_saved; lia)).
      assert (S23 : getr regs2 23%bv = getr (ms_regs ms0) 23%bv) by exact (HP 23 ltac:(unfold acallee_saved; lia)).
      assert (S24 : getr regs2 24%bv = getr (ms_regs ms0) 24%bv) by exact (HP 24 ltac:(unfold acallee_saved; lia)).
      assert (S27 : getr regs2 27%bv = getr (ms_regs ms0) 27%bv) by exact (HP 27 ltac:(unfold acallee_saved; lia)).
      (* the bytes the call kept, and the chain from the entry memory *)
      assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (d <= a < d + n) -> ~ (spZ regs - 112 - ESTACK <= a < spZ regs - 112) ->
        mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms0)) a).
      { intros a Ha H1 H2. apply (mbyte_of_aview tfibsegs). apply HFR; [exact Ha | exact H1 | rewrite RT2; exact H2]. }
      assert (KH2 : forall a, spZ regs <= a < 2 ^ 64 ->
        mbyte tfibsegs (mrestrict (w_H W) mem2) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
      { intros a Ha. rewrite (KC a) by (unfold ESTACK, d in *; lia).
        unfold mbyte, mrestrict. rewrite (MT a ltac:(lia) ltac:(lia)). reflexivity. }
      assert (PR2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) by (intros a Ha; exact (HPR a (PRT a Ha))).
      (* the resume env: 33 / 34 / 35 buf / len / cap, 36 the end of the new text, 37 .. 49 the saved words *)
      set (xs2 := [Z_to_bv 64 buf; Z_to_bv 64 len; Z_to_bv 64 cap; Z_to_bv 64 (d + n);
                   ew E 1; ew E 8; ew E 9; ew E 18; ew E 19; ew E 20; ew E 21; ew E 22; ew E 23; ew E 24; ew E 25;
                   ew E 26; ew E 27]).
      set (Er := Ereg regs2 (fs_extraT ++ xs2)).
      assert (F2 : bv_unsigned (ew Er 2) = spZ regs - 112).
      { unfold Er. rewrite (ew_Ereg_nat regs2 _ 2 2%bv eq_refl), S2. exact RT2. }
      assert (F8 : ew Er 8 = Z_to_bv 64 o) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 8 8%bv eq_refl), S8; exact RT8).
      assert (F9 : ew Er 9 = Z_to_bv 64 n) by (unfold Er; rewrite (ew_Ereg_nat regs2 _ 9 9%bv eq_refl), S9; exact RT9).
      assert (F32 : ew Er 32 = Z_to_bv 64 SHADOW_OFF) by (unfold Er; change 32%nat with (32 + 0)%nat; rewrite ew_Ereg_extra; reflexivity).
      assert (F33 : ew Er 33 = Z_to_bv 64 buf) by (unfold Er; change 33%nat with (32 + 1)%nat; rewrite ew_Ereg_extra; reflexivity).
      assert (F34 : ew Er 34 = Z_to_bv 64 len) by (unfold Er; change 34%nat with (32 + 2)%nat; rewrite ew_Ereg_extra; reflexivity).
      assert (F35 : ew Er 35 = Z_to_bv 64 cap) by (unfold Er; change 35%nat with (32 + 3)%nat; rewrite ew_Ereg_extra; reflexivity).
      assert (F36 : ew Er 36 = Z_to_bv 64 (d + n)) by (unfold Er; change 36%nat with (32 + 4)%nat; rewrite ew_Ereg_extra; reflexivity).
      assert (F8u : bv_unsigned (ew Er 8) = o) by (rewrite F8; apply wz; lia).
      assert (F9u : bv_unsigned (ew Er 9) = n) by (rewrite F9; apply wz; lia).
      assert (F32u : bv_unsigned (ew Er 32) = SHADOW_OFF) by (rewrite F32; apply wz; unfold SHADOW_OFF; lia).
      assert (F33u : bv_unsigned (ew Er 33) = buf) by (rewrite F33; apply wz; lia).
      assert (F34u : bv_unsigned (ew Er 34) = len) by (rewrite F34; apply wz; lia).
      assert (F35u : bv_unsigned (ew Er 35) = cap) by (rewrite F35; apply wz; lia).
      assert (F36u : bv_unsigned (ew Er 36) = d + n) by (rewrite F36; apply wz; unfold d in *; lia).
      (* a saved word of the call's frame is the resume frame's chunk *)
      assert (CM : forall o0 (k j : nat), ew Er j = ew E k ->
        YP09.chunk_ok tfibsegs E (mrestrict (w_H W) (ms_mem ms0)) (spZ regs) (YP09.mkChunk o0 (CVal 8 (SOff k 0))) ->
        -112 <= o0 -> o0 + 8 <= 0 ->
        YP09.chunk_ok tfibsegs Er (mrestrict (w_H W) mem2) (spZ regs - 112) (YP09.mkChunk (o0 + 112) (CVal 8 (SOff j 0)))).
      { intros o0 k j Hjk Hck Ho1 Ho2.
        apply (fsw_pf_chunk_move E Er _ _ (spZ regs) (spZ regs - 112) o0 (o0 + 112) 8 (SOff k 0) (SOff j 0) Hck).
        - rewrite !fsw_SOff0. exact Hjk.
        - lia.
        - intros i Hi. cbn [Z.of_N] in Hi. apply KC; [lia | unfold d in *; lia | unfold ESTACK; lia]. }
      (* the shadow-base cells on the memory after the call (FSW_rres.fsw_resume_after_rtU_args_chunks' steps) *)
      destruct (fsw_got_shadow B ly S W (unpoison U mem2) md2 (proj1 HSS) (proj2 HSS) (proj1 HARU2)) as [Kgot Kcell].
      assert (MB : forall x, 0 <= x < SHADOW_OFF ->
        mbyte tfibsegs (mrestrict (w_H W) mem2) x = mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem2)) x).
      { intros x Hx. unfold mbyte, mrestrict.
        rewrite (ARU_mem_low tfibsegs B ly S U W mem2 md2 (Z_to_bv 64 x) HARU2
          ltac:(rewrite (wz x ltac:(unfold SHADOW_OFF in *; lia)); unfold SHADOW_OFF in *; lia)).
        reflexivity. }
      assert (VM : forall a v, 0 <= a -> a + 8 <= SHADOW_OFF ->
        val_mem tfibsegs (mrestrict (w_H W) (unpoison U mem2)) a 8 v -> val_mem tfibsegs (mrestrict (w_H W) mem2) a 8 v).
      { intros a v Ha Hb Hv k0 Hk0. rewrite (MB (a + Z.of_nat k0) ltac:(lia)). exact (Hv k0 Hk0). }
      assert (Vgot : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_GOT_asan_shadow_memory_dynamic_address 8
        tfib_D_asan_shadow_memory_dynamic_address).
      { apply VM; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia
        | unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
        | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U mem2) _ _ Kgot)]. }
      assert (Vcell : val_mem tfibsegs (mrestrict (w_H W) mem2) tfib_D_asan_shadow_memory_dynamic_address 8 SHADOW_OFF).
      { apply VM; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia
        | unfold tfib_D_asan_shadow_memory_dynamic_address, SHADOW_OFF; lia
        | exact (val_mem_of_rdword tfibsegs (w_H W) (unpoison U mem2) _ _ Kcell)]. }
      (* the end of the new text is a buffer byte, so no image byte *)
      assert (ZG : d + n + 1 <= tfib_D_GOT_asan_shadow_memory_dynamic_address \/
                   tfib_D_GOT_asan_shadow_memory_dynamic_address + 8 <= d + n).
      { destruct (Z_le_gt_dec (d + n + 1) tfib_D_GOT_asan_shadow_memory_dynamic_address); [left; lia|].
        destruct (Z_le_gt_dec (tfib_D_GOT_asan_shadow_memory_dynamic_address + 8) (d + n)); [right; lia|].
        exfalso. apply (BNI (d + n)); [unfold d in *; lia|]. apply fsw_pf_in_img.
        unfold tfib_D_GOT_asan_shadow_memory_dynamic_address in *; lia. }
      assert (ZC : d + n + 1 <= tfib_D_asan_shadow_memory_dynamic_address \/
                   tfib_D_asan_shadow_memory_dynamic_address + 8 <= d + n).
      { destruct (Z_le_gt_dec (d + n + 1) tfib_D_asan_shadow_memory_dynamic_address); [left; lia|].
        destruct (Z_le_gt_dec (tfib_D_asan_shadow_memory_dynamic_address + 8) (d + n)); [right; lia|].
        exfalso. apply (BNI (d + n)); [unfold d in *; lia|]. apply fsw_pf_in_img.
        unfold tfib_D_asan_shadow_memory_dynamic_address in *; lia. }
      (* the end of the new text is present after the call: a block byte of AR, outside the shadow *)
      assert (PZ : apresent (w_H W) mem2 (d + n)).
      { destruct (al_blocks _ _ LAWS ly S W (unpoison U mem2) md2 (buf - HEAD) (cap + HEAD) (proj1 HARU2) Hin)
          as (_ & _ & _ & _ & Hbp & _).
        destruct (Hbp (d + n) ltac:(rewrite RQB; unfold HEAD, d in *; lia)) as ((Hh & b & Hb) & _).
        split; [exact Hh|]. exists b.
        rewrite <- (fsw_pf_unp B ly S U W mem2 md2 (d + n) HARU2); [exact Hb | unfold d in *; lia | unfold d, SHADOW_OFF in *; lia]. }
      pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
      assert (HSR0 : st_ok tfibsegs Er
          (mkSS 542176 sr_atoms (fsT_ret_regions 112 fsw_pf_cs [fsw_pf_o2; fsw_pf_z2]) None
            (mkFacts ((2%nat, mkAF (2 ^ 46) (2 ^ 47) 4) :: (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0) :: fsw_pf_gf2) []
               fsw_pf_al2))
          (restrict (w_H W) (mkst regs2 (Z_to_bv 64 542176) mem2 (seg_rom tfibsegs)))).
      { rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); fold Er.
        - apply regs_ok_Ereg.
        - vm_compute. reflexivity.
        - unfold fsT_ret_regions. cbn [app].
          constructor; [|constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]].
          + (* the frame, its saved words *)
            unfold region_ok, fstk_ret. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
            rewrite F2. split; [lia|]. split; [lia|]. split.
            * intros q Hq. apply (apresent_writable tfibsegs).
              apply (fsw_apresent_unpoison B ly S U W mem2 md2 _ HARU2); [lia|]. apply Hpres2. lia.
            * unfold fsw_pf_cs.
              repeat constructor.
              all: lazymatch goal with |- YP09.chunk_ok _ _ _ _ (YP09.mkChunk ?o2 (CVal 8 (SOff ?j 0))) =>
                let o0 := eval vm_compute in (o2 - 112) in
                let k := eval vm_compute in (if Nat.eqb j 37 then 1%nat else if Nat.eqb j 38 then 8%nat
                                             else if Nat.eqb j 39 then 9%nat else (j - 22)%nat) in
                exact (CM o0 k j eq_refl (HCS (YP09.mkChunk o0 (CVal 8 (SOff k 0))) ltac:(repeat (first [left; reflexivity | right]))) ltac:(lia) ltac:(lia))
              end.
          + (* the GOT word of the shadow base *)
            unfold fs_got_region, region_ok.
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
            split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|].
            split; [unfold tfib_D_GOT_asan_shadow_memory_dynamic_address; lia|]. split; [intros q Hq; lia|].
            constructor; [|constructor].
            apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_GOT_asan_shadow_memory_dynamic_address 8
              (SLit tfib_D_asan_shadow_memory_dynamic_address) tfib_D_asan_shadow_memory_dynamic_address);
              [reflexivity | unfold tfib_D_asan_shadow_memory_dynamic_address; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
              | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vgot].
          + (* the shadow-base cell *)
            unfold fs_bcell_region, region_ok.
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
            split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|].
            split; [unfold tfib_D_asan_shadow_memory_dynamic_address; lia|]. split; [intros q Hq; lia|].
            constructor; [|constructor].
            apply (chunk_ok_val tfibsegs _ _ 0 tfib_D_asan_shadow_memory_dynamic_address 8 (SOff 32 0) SHADOW_OFF);
              [rewrite fsw_SOff0, F32; reflexivity | unfold SHADOW_OFF; cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
              | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; rewrite Z.add_0_l; exact Vcell].
          + (* o, its length field writable *)
            unfold fsw_pf_o2, region_ok.
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
            rewrite F8u. split; [lia|]. split; [lia|]. split.
            { intros q Hq. apply (apresent_writable tfibsegs). apply PR2. apply HPRESENT. lia. }
            assert (VH2 : forall a k v, spZ regs <= a -> a + Z.of_nat k <= 2 ^ 64 ->
              val_mem tfibsegs (mrestrict (w_H W) mem) a k v -> val_mem tfibsegs (mrestrict (w_H W) mem2) a k v)
              by (intros a k v Ha Hk Hv i Hi; rewrite (KH2 (a + Z.of_nat i) ltac:(lia)); exact (Hv i Hi)).
            constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
            * apply (chunk_ok_val tfibsegs Er _ o 0 8 (SOff 33 0) buf);
                [rewrite fsw_SOff0; exact F33 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
                | rewrite Z.add_0_r; exact (VH2 o 8%nat buf ltac:(lia) ltac:(lia) Vbuf)].
            * apply (chunk_ok_val tfibsegs Er _ o 8 8 (SOff 34 0) len);
                [rewrite fsw_SOff0; exact F34 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
                | exact (VH2 (o + 8) 8%nat len ltac:(lia) ltac:(lia) Vlen)].
            * apply (chunk_ok_val tfibsegs Er _ o 16 8 (SOff 35 0) cap);
                [rewrite fsw_SOff0; exact F35 | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
                | exact (VH2 (o + 16) 8%nat cap ltac:(lia) ltac:(lia) Vcap)].
            * apply (chunk_ok_val tfibsegs Er _ o 24 4 (SLit 0) 0);
                [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia
                | cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add]; exact (VH2 (o + 24) 4%nat 0 ltac:(lia) ltac:(lia) Vfail)].
          + (* the byte after the new text, writable *)
            unfold fsw_pf_z2, region_ok.
            cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
            rewrite F36u. split; [unfold d in *; lia|]. split; [unfold d in *; lia|]. split; [|constructor].
            intros q Hq. replace (d + n + q) with (d + n) by lia. apply (apresent_writable tfibsegs). exact PZ.
        - apply pairwise_disjoint_of_extents.
          unfold fsT_ret_regions, fstk_ret, fs_got_region, fs_bcell_region, fsw_pf_o2, fsw_pf_z2, extent_of_region.
          cbn [map app YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite F2, F8u, F36u.
          cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
          unfold tfib_D_GOT_asan_shadow_memory_dynamic_address, tfib_D_asan_shadow_memory_dynamic_address in *.
          unfold d in *. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
        - split; [|split; [exact I|]].
          + cbn [f_atoms atoms_ok fsw_pf_gf2]. unfold afact_ok. cbn [af_lo af_hi af_al2].
            rewrite F2, F32u, F8u, F33u, F34u, F35u, F9u, F36u. unfold fsw_pf_CEIL.
            change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
            unfold d in *. repeat split; lia.
          + cbn [f_alias alias_ok fsw_pf_al2]. split; [|exact I].
            apply U_inj. rewrite !U_SAlu, (U_atom Er 9 n F9), (U_atom Er 33 buf F33), (U_atom Er 34 len F34),
              (U_atom Er 36 (d + n) F36) by (unfold d in *; lia).
            cbn [zalu_raw]. rewrite (zcanon_id (n + buf)) by (unfold M64; lia).
            rewrite zcanon_id by (unfold M64; lia). unfold d. lia. }
      (* the resume state's three re-seated registers: s7 the shadow base (as A), s8 / s11 the shadow addresses of
         o + 8 and o over the resumed o (atom 8), which the token engine reads at 0x845e0 / 0x845f4 *)
      assert (E32u : bv_unsigned (ew E 32) = SHADOW_OFF) by (rewrite E32; apply wz; unfold SHADOW_OFF; lia).
      assert (HSR1 : st_ok tfibsegs Er (fsw_pf_ssk fsw_pf_rs1)
                       (restrict (w_H W) (mkst regs2 (Z_to_bv 64 542176) mem2 (seg_rom tfibsegs)))).
      { refine (st_ok_set_reg tfibsegs Er _ _ 23%bv (SOff 32 0) HSR0 _ _).
        - intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
        - change (ms_regs (restrict (w_H W) (mkst regs2 (Z_to_bv 64 542176) mem2 (seg_rom tfibsegs)))) with regs2.
          rewrite fsw_SOff0, F32, S23. exact RT23. }
      assert (HSR2 : st_ok tfibsegs Er (fsw_pf_ssk fsw_pf_rs2)
                       (restrict (w_H W) (mkst regs2 (Z_to_bv 64 542176) mem2 (seg_rom tfibsegs)))).
      { refine (st_ok_set_reg tfibsegs Er _ _ 24%bv fsw_pf_s8 HSR1 _ _).
        - intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
        - change (ms_regs (restrict (w_H W) (mkst regs2 (Z_to_bv 64 542176) mem2 (seg_rom tfibsegs)))) with regs2.
          rewrite S24, RT24. apply bv_eq.
          change (YP0e.U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 8) (SLit 3)) (SOff 32 0)) = YP0e.U Er fsw_pf_s8).
          unfold fsw_pf_s8. rewrite !U_SAlu, !U_SOff, !U_SLit, E10u, F8u, E32u, F32u. reflexivity. }
      assert (HSR : st_ok tfibsegs Er fsw_pf_ssr (restrict (w_H W) (mkst regs2 (Z_to_bv 64 542176) mem2 (seg_rom tfibsegs)))).
      { refine (st_ok_set_reg tfibsegs Er _ _ 27%bv fsw_pf_s11 HSR2 _ _).
        - intros Hz. apply (f_equal (@bv_unsigned 5)) in Hz. vm_compute in Hz. discriminate Hz.
        - change (ms_regs (restrict (w_H W) (mkst regs2 (Z_to_bv 64 542176) mem2 (seg_rom tfibsegs)))) with regs2.
          rewrite S27, RT27. apply bv_eq.
          change (YP0e.U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 10 0) (SLit 3)) (SOff 32 0)) = YP0e.U Er fsw_pf_s11).
          unfold fsw_pf_s11. rewrite !U_SAlu, !U_SOff, !U_SLit, E10u, F8u, E32u, F32u. reflexivity. }
      clear HSR0 HSR1 HSR2.

      assert (SHOK2 : sh_ok tfibsegs fs_Bx fsw_pf_SH2 Er (mrestrict (w_H W) mem2)).
      { unfold fsw_pf_SH2. constructor; [|constructor; [|constructor]].
        - apply (shent_ok_of_range tfibsegs (w_H W) mem2 Er fs_Bx 8%nat o 32 o 0 32 (RAO mem2 md2 HARU2)).
          + unfold fs_Bx. apply (U_atom Er 32 SHADOW_OFF F32). unfold SHADOW_OFF; lia.
          + apply (U_atom Er 8 o F8). lia.
          + lia.
          + lia.
          + intros x Hx. unfold SHADOW_OFF. lia.
        - assert (HRAz : range_addressable (aview tfibsegs (w_H W) mem2) SHADOW_OFF (d + n) 1).
          { apply (fsw_pf_ra_raw (w_H W) U mem2 (d + n) 1); [unfold d in *; lia | unfold d in *; lia | |].
            - intros x Hx. apply (fsw_pf_ush_out B ly S U x HUOK); [unfold d in *; lia|].
              exact (fsw_pf_heads_out B ly S U W (unpoison U mem) md buf cap x HAR FH Hin Hcap0 ltac:(unfold d in *; lia)).
            - apply (range_addressable_of_block tfibsegs B LAWS ly S W (unpoison U mem2) md2 (buf - HEAD) (cap + HEAD)
                (d + n) 1 (proj1 HARU2) Hin); rewrite ?RQB; unfold HEAD, d in *; lia. }
          apply (shent_ok_of_range tfibsegs (w_H W) mem2 Er fs_Bx 36%nat (d + n) 1 (d + n) 0 1 HRAz).
          + unfold fs_Bx. apply (U_atom Er 32 SHADOW_OFF F32). unfold SHADOW_OFF; lia.
          + apply (U_atom Er 36 (d + n) F36). unfold d in *; lia.
          + lia.
          + lia.
          + intros x Hx. unfold SHADOW_OFF, d in *. lia. }
      (* run 4: the length store o + 8, to UBSan's pointer-overflow check of buf + len + n, 0x84604 *)
      fsw_aj_run_tokU fsw_put_tbl_ok HSR HJ2 HARU2 SHOK2 fs_Bspan.
      -- cbv [fsw_pf_ssr fsw_pf_ssk fsT_ret_regions ss_mem app].
         eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
           [reflexivity | rewrite F2; lia | cbv [fstk_ret YP09.r_wlo]; lia | cbv [fstk_ret YP09.r_whi]; lia |].
         apply awr_ok_cons_ro; [cbv [fs_got_region YP09.r_wlo YP09.r_whi]; lia|].
         apply awr_ok_cons_ro; [cbv [fs_bcell_region YP09.r_wlo YP09.r_whi]; lia|].
         eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
           [reflexivity | rewrite F8u; lia | cbv [fsw_pf_o2 YP09.r_wlo]; lia | cbv [fsw_pf_o2 YP09.r_whi]; lia |].
         eapply awr_ok_cons_gen with (k := 36%nat) (b := d + n); [reflexivity | exact F36u | | apply awr_ok_nil].
         intros a Ha. cbv [fsw_pf_z2 YP09.r_wlo YP09.r_whi] in Ha. left. right. left. split.
         { exists (buf - HEAD, buf + cap). split.
           - apply in_or_app. right. unfold wbuf_fp. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity.
           - cbn [fst snd]. unfold d, HEAD in *. lia. }
         { exists (buf - HEAD), (cap + HEAD). split; [exact Hin|]. rewrite RQB. unfold d, HEAD in *. lia. }
      -- lazymatch type of HSR with st_ok _ _ _ (restrict _ ?m) => first [rename m into msD | idtac] end.
         (* the run wrote only the frame, o's length field and the 0 after the new text (in fact only the field) *)
         assert (MD : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o + 8 <= a < o + 16) ->
           a <> d + n -> ms_mem msD (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
         { intros a Ha H1 H2 H3. apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
           cbv [fsw_pf_ssr fsw_pf_ssk fsT_ret_regions ss_mem app In] in Hri.
           destruct Hri as [<-|[<-|[<-|[<-|[<-|[]]]]]];
             cbv [fstk_ret fs_got_region fs_bcell_region fsw_pf_o2 fsw_pf_z2 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
             rewrite ?F2, ?F8u, ?F36u in Hr; lia. }
         pose proof (fun a Ha => apresent_grows _ _ _ a HG (PR2 a Ha)) as PRD.
         clear HF HFr HG.
         (* 0x84604 `bltu d + n, buf`: the taken side is UBSan's trap 0x84680, refuted at the branch: d + n =
            buf + len + n >= buf *)
         srr_branch_tok fsw_put_tbl_ok HSR SHOK2 fs_Bspan.
         1: { exfalso. rewrite branch_ltu_U in Hc.
              rewrite (U_atom Er 36 (d + n) F36), (U_atom Er 33 buf F33) in Hc by (unfold d in *; lia).
              apply Z.ltb_lt in Hc. unfold d in *. lia. }
         (* run 5: the 0 after the new text, the epilogue, to the ret 0x84668 *)
         fsw_aj_run_tokU fsw_put_tbl_ok HSR HJ2 HARU2 SHOK2 fs_Bspan.
         ++ lazymatch goal with |- context C [ss_mem ?ssx] =>
              let rs' := eval vm_compute in (ss_mem ssx) in
              let g := context C [rs'] in change g end.
            eapply awr_ok_cons_stack_off with (n := 2%nat) (d := spZ regs - 112 - ot);
              [reflexivity | rewrite F2; lia | cbn; lia | cbn; lia |].
            apply awr_ok_cons_ro; [cbn; lia|].
            apply awr_ok_cons_ro; [cbn; lia|].
            eapply awr_ok_cons_stack_off with (n := 8%nat) (d := o - ot);
              [reflexivity | rewrite F8u; lia | cbn; lia | cbn; lia |].
            eapply awr_ok_cons_gen with (k := 36%nat) (b := d + n); [reflexivity | exact F36u | | apply awr_ok_nil].
            intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. left. right. left. split.
            { exists (buf - HEAD, buf + cap). split.
              - apply in_or_app. right. unfold wbuf_fp. rewrite (proj2 (Z.eqb_neq cap 0)) by lia. left. reflexivity.
              - cbn [fst snd]. unfold d, HEAD in *. lia. }
            { exists (buf - HEAD), (cap + HEAD). split; [exact Hin|]. rewrite RQB. unfold d, HEAD in *. lia. }
         ++ lazymatch type of HSR with st_ok _ _ _ (restrict _ ?m) => first [rename m into ms1 | idtac] end.
            (* the two runs wrote only the frame, o's length field and the 0 after the new text *)
            assert (MF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o + 8 <= a < o + 16) ->
              a <> d + n -> ms_mem ms1 (Z_to_bv 64 a) = mem2 (Z_to_bv 64 a)).
            { intros a Ha H1 H2 H3. rewrite <- (MD a Ha H1 H2 H3). apply HF. rewrite (wz a Ha). intros (r & Hri & Hr).
              vm_compute in Hri. repeat destruct Hri as [<-|Hri]; try destruct Hri;
                cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?F2, ?F8u, ?F36u in Hr; lia. }
            pose proof (fun a Ha => apresent_grows _ _ _ a HG (PRD a Ha)) as PRF.
            clear MD PRD.
        lazymatch type of HSR with st_ok _ ?Ef _ _ => assert (HAG : env_agree 50 Er Ef) end.
        { lazymatch goal with |- env_agree _ _ (ewset (ewset _ _ ?w1) _ ?w2) => exact (env_agree_extK Er 50 [w1; w2]) end. }
        assert (FR1 : getr (ms_regs ms1) 1%bv = getr regs 1%bv).
        { pf_reg HSR. lazymatch goal with |- context [sv_denot ?Ef ?e] => lazymatch Ef with Er => fail | _ => rewrite (sv_denot_agree 50 Er Ef e HAG eq_refl) end end. rewrite fsw_SOff0.
          transitivity (ew E 1); [reflexivity | unfold E; apply ew_Ereg_nat; reflexivity]. }
        (* the length field and the 0 after the new text, read off the final state *)
        pose proof (st_ok_mem_ok tfibsegs _ _ _ HSR) as (_ & HRSF & _).
        cbn [ms_mem restrict ss_mem] in HRSF.
        apply Forall_inv_tail, Forall_inv_tail, Forall_inv_tail in HRSF.
        pose proof (Forall_inv HRSF) as RO. apply Forall_inv_tail, Forall_inv in HRSF. rename HRSF into RZ.
        destruct RO as (_ & _ & _ & HCO). cbn [YP09.r_base YP09.r_chunks base_val] in HCO.
        rewrite (proj1 HAG 8%nat ltac:(lia)), F8u in HCO. apply Forall_inv in HCO.
        destruct RZ as (_ & _ & _ & HCZ). cbn [YP09.r_base YP09.r_chunks base_val] in HCZ.
        rewrite (proj1 HAG 36%nat ltac:(lia)), F36u in HCZ. apply Forall_inv in HCZ.
        assert (VLEN : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (o + 8) 8 (len + n)).
        { apply (val_of_chunk_ok tfibsegs _ _ o 8 8 _ (len + n) HCO).
          - lazymatch goal with |- context [sv_denot ?Ef ?e] => lazymatch Ef with Er => fail | _ => rewrite (sv_denot_agree 50 Er Ef e HAG eq_refl) end end. rewrite denot_lit_U. f_equal.
            rewrite U_SAlu, (U_atom Er 9 n F9), (U_atom Er 34 len F34) by lia. cbn [zalu_raw].
            rewrite zcanon_id by (unfold M64; lia). lia.
          - cbn [Z.of_N]. lia.
          - cbn [Z.of_N]. lia. }
        assert (VZ : val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (d + n + 0) 1 0).
        { apply (val_of_chunk_ok tfibsegs _ _ (d + n) 0 1 (SLit 0) 0 HCZ); [reflexivity | cbn [Z.of_N]; lia | cbn [Z.of_N]; lia]. }
        (* every other byte: kept *)
        assert (KF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) -> ~ (o + 8 <= a < o + 16) ->
          a <> d + n -> mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a = mbyte tfibsegs (mrestrict (w_H W) mem2) a)
          by (intros a H0 H1 H2 H3; unfold mbyte, mrestrict; rewrite (MF a H0 H1 H2 H3); reflexivity).
        assert (KH : forall a, spZ regs <= a < 2 ^ 64 -> ~ (o + 8 <= a < o + 16) ->
          mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a)
          by (intros a Ha Ho; rewrite (KF a) by (unfold d in *; lia); apply KH2; lia).
        assert (KL : forall a, 0 <= a < alloc_ceiling -> ~ (d <= a < d + n + 1) ->
          mbyte tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a = mbyte tfibsegs (mrestrict (w_H W) mem) a).
        { intros a Ha Hd. rewrite (KF a) by (unfold d in *; lia). rewrite (KC a) by (unfold ESTACK, d in *; lia).
          unfold mbyte, mrestrict. rewrite (LOWT a Ha). reflexivity. }
        assert (VH : forall a k v, spZ regs <= a -> a + Z.of_nat k <= 2 ^ 64 ->
          (forall i, 0 <= i < Z.of_nat k -> ~ (o + 8 <= a + i < o + 16)) ->
          val_mem tfibsegs (mrestrict (w_H W) mem) a k v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a k v).
        { intros a k v Ha Hk Ho Hv i Hi. rewrite (KH (a + Z.of_nat i) ltac:(lia) (Ho (Z.of_nat i) ltac:(lia))). exact (Hv i Hi). }
        assert (VL : forall a k v, 0 <= a -> a + Z.of_nat k <= alloc_ceiling ->
          (forall i, 0 <= i < Z.of_nat k -> ~ (d <= a + i < d + n + 1)) ->
          val_mem tfibsegs (mrestrict (w_H W) mem) a k v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) a k v).
        { intros a k v Ha Hk Ho Hv i Hi. rewrite (KL (a + Z.of_nat i) ltac:(lia) (Ho (Z.of_nat i) ltac:(lia))). exact (Hv i Hi). }
        (* the return *)
        eapply (fsw_retU B fsw_put_tbl fsw_put_tbl_ok).
        ** exact HSR.
        ** vm_compute; reflexivity.
        ** vm_compute; reflexivity.
        ** rewrite FR1. exact Hra.
        ** exact HJ2.
        ** exact HARU2.
        ** lazymatch type of HSR with
           | st_ok _ ?Ef ?ssf _ =>
             apply (fsw_preserved (w_H W) Ef ssf _ regs (fun r : bv 5 => sr_get (ss_regs ssf) r) HSR);
             [vm_compute; reflexivity|];
             let r := fresh "r" in let Hr := fresh "Hr" in
             intros r Hr; cbv [CALLEE_SAVED In] in Hr;
             repeat (destruct Hr as [<-|Hr]); [..|destruct Hr]
           end;
           cbv beta;
           lazymatch goal with
           | |- sv_denot _ ?e = _ => let e' := eval vm_compute in e in change e with e'
           end;
           lazymatch goal with |- context [sv_denot ?Ef ?e] => lazymatch Ef with Er => fail | _ => rewrite (sv_denot_agree 50 Er Ef e HAG eq_refl) end end;
           first
           [ rewrite denot_lit_U, U_SOff, F2, zcanon_id by (unfold M64; lia);
             replace (spZ regs - 112 + 112) with (spZ regs) by lia; unfold spZ; apply Z_to_bv_bv_unsigned
           | rewrite fsw_SOff0; unfold Er; rewrite (ew_Ereg_nat regs2 _ 3 3%bv eq_refl), S3; exact RT3
           | rewrite fsw_SOff0; unfold Er; rewrite (ew_Ereg_nat regs2 _ 4 4%bv eq_refl), S4; exact RT4
           | lazymatch goal with |- sv_denot _ (SOff ?j 0) = _ =>
               let k := eval vm_compute in (if Nat.eqb j 37 then 1%nat else if Nat.eqb j 38 then 8%nat
                                            else if Nat.eqb j 39 then 9%nat else (j - 22)%nat) in
               rewrite fsw_SOff0; change (ew Er j) with (ew E k); unfold E; apply ew_Ereg_nat; vm_compute; reflexivity
             end ].
        ** intros matq.
           split.
           { unfold wout_ok. split; [exact Ho8|]. split; [exact Ho0|]. split; [exact Hotop|]. split.
             { intros i Hi. destruct (HOW i Hi) as [_ Hp]. pose proof (PRF _ Hp) as Hp'.
               split; [exact (apresent_writable tfibsegs _ _ _ Hp') | exact Hp']. }
             split; [exact Hbuf64|]. split; [exact Hcap64|].
             split; [exact (VH o 8%nat buf ltac:(lia) ltac:(lia) ltac:(intros i Hi; lia) Vbuf)|].
             split; [rewrite length_app, Nat2Z.inj_add; fold len; rewrite Hlen; exact VLEN|].
             split; [exact (VH (o + 16) 8%nat cap ltac:(lia) ltac:(lia) ltac:(intros i Hi; lia) Vcap)|].
             split; [exact (VH (o + 24) 4%nat 0 ltac:(lia) ltac:(lia) ltac:(intros i Hi; lia) Vfail)|].
             split; [left; reflexivity|].
             split; [unfold WriterSpec.bytes_ok in *; apply Forall_app; split; assumption|].
             right. split; [exact Hj|]. split; [|split].
             - unfold fs_rblock. split; [exact Hin|]. split; [exact Hb16|]. split; [exact Hcap0|].
               apply (VL (buf - HEAD) 8%nat cap); [unfold HEAD; lia | unfold HEAD; lia
                 | intros i Hi; unfold d, HEAD in *; lia | exact Vhead].
             - rewrite length_app, Nat2Z.inj_add. fold len. lia.
             - unfold zbytes_at in HZB, HZS |- *. intros j Hjl. rewrite !length_app in Hjl. cbn [length] in Hjl.
               destruct (Nat.lt_ge_cases j (length text)) as [Hj1|Hj1].
               + rewrite <- app_assoc, app_nth1 by exact Hj1.
                 destruct (HZB j ltac:(rewrite length_app; cbn [length]; lia)) as (Hv & Hr).
                 rewrite app_nth1 in Hv, Hr by exact Hj1.
                 split; [|exact Hr].
                 apply (VL (buf + Z.of_nat j) 1%nat); [lia | cbn [Z.of_nat Pos.of_succ_nat]; unfold d, len in *; lia
                   | intros i Hi; cbn [Z.of_nat Pos.of_succ_nat] in Hi; unfold d, len in *; lia | exact Hv].
               + destruct (Nat.lt_ge_cases j (length text + length bs)) as [Hj2|Hj2].
                 * rewrite <- app_assoc, app_nth2 by exact Hj1. rewrite app_nth1 by lia.
                   destruct (HZS (j - length text)%nat ltac:(lia)) as (Hv & Hr). split; [|exact Hr].
                   intros k Hk. assert (k = 0%nat) by lia. subst k. specialize (Hv 0%nat Hk). rewrite <- Hv.
                   replace (buf + Z.of_nat j + Z.of_nat 0) with (d + Z.of_nat (j - length text)) by (unfold d, len; lia).
                   replace (s + Z.of_nat (j - length text) + Z.of_nat 0) with (s + Z.of_nat (j - length text)) by lia.
                   rewrite (KF (d + Z.of_nat (j - length text))) by (unfold d, len in *; lia).
                   rewrite (fsw_pf_mbyte_aview2 (w_H W) (ms_mem ms0) mem2 _ _ (HCP (Z.of_nat (j - length text)) ltac:(lia))).
                   unfold mbyte, mrestrict. rewrite (LOWT (s + Z.of_nat (j - length text))) by lia. reflexivity.
                 * assert (Ej : j = (length text + length bs)%nat) by lia. subst j.
                   rewrite <- app_assoc, app_nth2 by lia. rewrite app_nth2 by lia.
                   replace (length text + length bs - length text - length bs)%nat with 0%nat by lia. cbn [nth].
                   split; [|lia].
                   replace (buf + Z.of_nat (length text + length bs)) with (d + n + 0) by (unfold d, len; lia). exact VZ. }
           split; [unfold wbudget_kept, WMAX; split; [lia|]; split; lia|].
           split; [left; split; [reflexivity | split; reflexivity]|].
           split.
           { intros a Ha Hno. split; [apply KH; lia|].
             split; intros _.
             - apply (apresent_writable tfibsegs). apply PRF. apply HPRESENT. lia.
             - apply (apresent_writable tfibsegs). apply HPRESENT. lia. }
           split.
           { exists peak. split; [split; [lia | apply Z.le_max_l]|].
             replace (live + cap - cap) with live by lia.
             assert (GI : forall g v, 0x10000 <= g -> g + 8 <= 0x5fd000 ->
               val_mem tfibsegs (mrestrict (w_H W) mem) g 8 v -> val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) g 8 v).
             { intros g v Hg1 Hg2 Hv. apply VL; [lia | lia | | exact Hv].
               intros i Hi Hx. apply (BNI (g + i)); [unfold d in *; lia|]. apply fsw_pf_in_img. lia. }
             unfold fs_glob, fs_glob_at in HGLOB |- *. destruct HGLOB as (GL1 & GL2 & GL3 & GL4 & GR).
             split; [apply GI; [unfold G_LIVE; lia | unfold G_LIVE; lia | exact GL1]|].
             split; [apply GI; [unfold G_PEAK; lia | unfold G_PEAK; lia | exact GL2]|].
             split; [apply GI; [unfold G_COUNT; lia | unfold G_COUNT; lia | exact GL3]|].
             split; [apply GI; [unfold G_FAIL; lia | unfold G_FAIL; lia | exact GL4]|].
             exact GR. }
           intros i Hi. apply KL; [lia|]. intros Hx. apply (SDISJ (s + i)); [lia | unfold d, HEAD in *; lia]. }
(* ---- the spec's post: on this arm put1 appends bs; U and the buffer do not move; the count is 0 ---- *)
eapply SRr_mono; [exact MAIN|].
cbv beta. intros W2 c2 Hle HP.
exists (WriterApp.mkW 0 (text ++ bs) cap cnt fail []), buf, U.
split.
{ unfold WriterApp.put1.
  cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls negb Z.eqb].
  rewrite (proj2 (Z.leb_le _ _)) by (fold len; lia). reflexivity. }
split; [left; split; reflexivity|].
unfold wpost, wcalls. cbn [WriterApp.w_calls length Z.of_nat]. rewrite Z.mul_0_r. exact HP.
Qed.

(* ================= the two arms in put_spec's form =================
   lib/A/FSW_put_close.v (a working branch 14dd44c5348) over image B. The run lemmas above state the
   journal count as `3 * wcalls st'`, the count put_spec had when lib/A/FSW_put.v was proved; lib/B/FSH_Fn_writer.v
   put_spec (:240) reports `wevk cap st'` (:120), and on both arms put1 makes no request, so the two are the same
   number, 0 (put_pf_wevk0). put_close_failed / put_close_fast are put_spec's conclusion, verbatim (put_post), on the
   failed arm and on the fast arm; each takes a subset of put_spec's premises plus the arm's own premise. *)
Lemma put_pf_wevk0 : forall cap (st : WriterApp.wst), WriterApp.w_calls st = [] -> wevk cap st = 3 * wcalls st.
Proof.
intros cap st H. unfold wevk, wev0, wcalls. rewrite H. cbn [length Z.of_nat]. destruct (cap =? 0); reflexivity.
Qed.
Lemma put_pf_calls_failed : forall failed text cap cnt fail (bs : list Z), failed <> 0 ->
  WriterApp.w_calls (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) = [].
Proof.
intros failed text cap cnt fail bs Hf. unfold WriterApp.put1. cbn [WriterApp.w_failed].
destruct (Z.eqb_spec failed 0) as [Ef|_]; [contradiction | reflexivity].
Qed.
Lemma put_pf_calls_fast : forall text cap cnt fail (bs : list Z),
  Z.of_nat (length text) + Z.of_nat (length bs) + 1 <= cap ->
  WriterApp.w_calls (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs) = [].
Proof.
intros text cap cnt fail bs Hle. unfold WriterApp.put1.
cbn [WriterApp.w_failed WriterApp.w_text WriterApp.w_cap WriterApp.w_cnt WriterApp.w_fail WriterApp.w_calls negb Z.eqb].
rewrite (proj2 (Z.leb_le _ _) Hle). reflexivity.
Qed.

(* put_spec's post, as a predicate of the call's data (lib/B/FSH_Fn_writer.v put_spec, verbatim) *)
Definition put_post ly S U W regs mem md ot o s n buf cap failed (text bs : list Z) live peak cnt fail :
  world tfibsegs -> config -> Prop :=
  fun W' c' => exists (st' : WriterApp.wst) buf' U',
    st' = WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs /\
    uswap U U' buf buf' cap /\
    wpost B tfibsegs STK_put ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
      regs ly S U W mem md (wevk cap st') U'
      (fun ly' S' W' regs' mem' md' =>
         wout_ok B tfibsegs ly' S' W' mem' o buf' (WriterApp.w_cap st') (WriterApp.w_failed st') (WriterApp.w_text st') /\
         wbudget_kept S S' failed cap cnt (WriterApp.w_failed st') (WriterApp.w_cap st') (WriterApp.w_cnt st') /\
         bswap (ablocks B ly S) (ablocks B ly' S') buf buf' cap (WriterApp.w_cap st') /\
         wkeep tfibsegs W W' mem mem' (spZ regs) ot o 32 /\
         (exists peak', peak <= peak' <= Z.max peak (live - cap + WriterApp.w_cap st') /\
            fs_glob tfibsegs W' mem' (live + WriterApp.w_cap st' - cap) peak'
              (WriterApp.w_cnt st') (WriterApp.w_fail st')) /\
         (forall i, 0 <= i < n -> mbyte tfibsegs (mrestrict (w_H W') mem') (s + i)
                                = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)))
      W' c'.

(* the FAILED arm in put_spec's count *)
Lemma put_close_failed :
  forall ly S U W regs mem md ch ot o s n buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text ->
  fs_glob tfibsegs W mem live peak cnt fail ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  0 <= s /\ s + n <= alloc_ceiling ->
  cap <= WMAX ->
  failed <> 0 ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
    (put_post ly S U W regs mem md ot o s n buf cap failed text bs live peak cnt fail).
Proof.
intros ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
  HPRE G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HSRC HCAP HFAIL.
eapply SRr_mono.
{ exact (put_failed_run ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
           HPRE G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HSRC HCAP HFAIL). }
intros W' c' _ (st' & buf' & U' & Hst & Hu & HP).
exists st', buf', U'. split; [exact Hst|]. split; [exact Hu|].
rewrite (put_pf_wevk0 cap st') by (rewrite Hst; apply put_pf_calls_failed; exact HFAIL). exact HP.
Qed.

(* the FAST arm in put_spec's count *)
Lemma put_close_fast :
  forall ly S U W regs mem md ch ot o s n buf cap failed (text bs : list Z) live peak cnt fail,
  fpreU tfibsegs B STK_put ly S U W regs mem md ch -> fs_heads B ly S U ->
  getr regs 10 = w64 o -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  wout_ok B tfibsegs ly S W mem o buf cap failed text -> fs_glob tfibsegs W mem live peak cnt fail ->
  spZ regs <= o -> o + 32 <= ot -> ot mod 16 = 0 -> ot <= ly_top ly ->
  (forall a, spZ regs <= a < ot -> apresent (w_H W) mem a) ->
  zbytes_at tfibsegs W mem s bs -> wsrc_kept B tfibsegs ly S U W mem buf s bs -> Z.of_nat (length bs) = n ->
  WriterSpec.bytes_ok bs ->
  0 <= s /\ s + n <= alloc_ceiling -> (s + n <= o \/ ot <= s) ->
  Z.of_nat (length text) + n + 1 <= WMAX ->
  cap <= WMAX ->
  wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW failed text cap cnt fail []) bs) ->
  failed = 0 -> Z.of_nat (length text) + n + 1 <= cap ->
  SRr tfibsegs W (cfg_at tfibsegs A_put regs mem md)
    (put_post ly S U W regs mem md ot o s n buf cap failed text bs live peak cnt fail).
Proof.
intros ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
  HPRE FH G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj HWM HCAP HBUD HF0
  HFAST.
eapply SRr_mono.
{ exact (put_fast_run ly S U W regs mem md ch ot o s n buf cap failed text bs live peak cnt fail
           HPRE FH G10 G11 G12 HOUT HGLOB Hspo Hoot Hot16 Hottop HPRESENT HZS HSK Hlen Hbok HSRC Hsdisj HWM HCAP HBUD
           HF0 HFAST). }
intros W' c' _ (st' & buf' & U' & Hst & Hu & HP).
exists st', buf', U'. split; [exact Hst|]. split; [exact Hu|].
rewrite (put_pf_wevk0 cap st') by (rewrite Hst, HF0; apply put_pf_calls_fast; rewrite Hlen; exact HFAST). exact HP.
Qed.
End w.

(* REPORT SITES of put on image B: a Theorem Labs lane's CFG table (reloc-check/report-sites-B.tsv, row `put`, 06:33Z) lists
   13 sites. For each, its `deciding` branch and where this file passes it with no open shadow obligation or refutes it
   (FA = put_failed_run, FS = put_fast_run; every token run here ends with sh_obls = [], closed by srr_obls):
   0x84680 unimp (B only): 0x844dc bne - FA's run (:464) and FS run 1 (:821) pass it, from atom 10's af_al2 = 3
     (wout_ok's o mod 8 = 0); 0x845c0 bltu - refuted by FS at :868-873, from buf + len < 2 ^ 64; 0x845d0 beq - FS
     run 3 (:876) passes it; 0x84604 bltu - refuted by FS at :1267-1270, from d + n = buf + len + n >= buf; 0x84614 beq
     and 0x84618 beq - FS run 5 (:1272) passes them.
   0x84694 load4: 0x84504 bne (slow block 0x84684, compare 0x8468c) - FA's run (:464) and FS run 1 (:821) read the shadow
     of o + 24 as 0 from the shent of o's 32 bytes (fsw_put_SH / fsw_pf_SH, SHOK from RA32 / RAO).
   0x846a0 store1: 0x84628 bne into the slow block 0x84698, compare 0x8469c blt - FS run 5 (:1272) follows the
     partial-granule slow block and passes 0x8469c, from the shent [36, 0, 1] of the byte d + n (SHOK2's HRAz, the
     buffer block's range_addressable_of_block); FA never reaches it.
   0x846b4 store4: 0x84670 bne, reached only after 0x84580 beq (fuzz_realloc refused): the grow arm; FA and FS never
     reach it (FA returns at 0x8450c, FS takes 0x8454c's taken side to 0x845a0).
   0x846bc load8: 0x84520 bne - FS run 1 (:821), shadow of o + 8 from fsw_pf_SH; FA never reaches it.
   0x846c4 load8: 0x84534 bne - FS run 1 (:821), shadow of o + 16 from fsw_pf_SH; FA never reaches it.
   0x846cc load8: 0x845a8 bne - FS run 2 (:848), shadow of o (s11) from fsw_pf_SH; FA never reaches it.
   0x846d4 load8: 0x845b0 bne - FS run 2 (:848), shadow of o + 8 (s8) from fsw_pf_SH; FA never reaches it.
   0x846dc load8: 0x845e4 bne - FS run 4 (:1240), shadow of o + 8 through the re-seated s8, from fsw_pf_SH2 (SHOK2).
   0x846e4 load8: 0x845f8 bne - FS run 4 (:1240), shadow of o through the re-seated s11, from fsw_pf_SH2 (SHOK2).
   0x846ec load8, 0x846f4 store8, 0x846fc store8: 0x84570 / 0x84588 / 0x84594 bne, inside 0x84550 .. 0x8459c, the
     grow arm only; FA and FS never reach them.
   No row is OPEN for the failed and fast arms. The grow arm (not proved here) must place 0x846b4, 0x846ec, 0x846f4,
   0x846fc and its own passes of 0x845a8 .. 0x84618. *)
