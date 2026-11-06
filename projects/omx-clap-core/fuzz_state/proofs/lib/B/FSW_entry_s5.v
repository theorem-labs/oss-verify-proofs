(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/ACer.v, with its module paths and module names changed; 1338 of its 1373 lines of code are new or changed and 261 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_K.v, with its module paths and module names changed; 958 of its 1043 lines of code are new or changed and 1288 lines of the source are left out. *)
(* fs program part, lane ENTRY, IMAGE B (fs.asan-ubsan, pinned 5ac5ce0954f8): segment S5 of the LLVMFuzzerTestOneInput
   walk (0x810bc-0x8110c, fs.c:324-326, fuzz_copy inlined), the B twin of lib/A/FSW_entry_s5.v with the same lemma
   names and argument order: `text = malloc(n + 1)` (0x810c0, __wrap_malloc 0x530e4, ra 0x810c4), `beqz a0` to the
   abort 0x81234 (dead: the block is granted), `memcpy(text, data, n)` if n > 0 (0x810dc, __asan_memcpy 0x51d90, ra
   0x810e0), the UBSan pointer-overflow check of text + n (0x810e0 `not a0, s5`, 0x810e4 `bltu a0, s3` to the trap
   0x8123c), the inline ASan check of text[n] (0x810e8-0x810f8, slow path 0x81240-0x81244 back to 0x810fc; the report
   0x81248 is dead: text[n] is the last byte of the n + 1 byte block), `sb zero, 0(a0)` (text[n] = 0, 0x81100), the
   second UBSan check 0x81104 `beq a0, a1 (= -1)` to the trap, and `addi s4, s8, 32` (0x81108). From the boundary C2
   (fe_ss RA_cno [fe_len_lit (-1)], INV_C2, 0x810bc) to the boundary C5 (fe_ss PC_C5 [fe_len_lit (-1)], INV_C5, 0x8110c),
   in the segment form fe_from of lib/B/FSW_entry_defs.v, through two boundaries of this file: A at 0x810c4 (RA_malloc,
   INV_A5: malloc returned) and M at 0x810e0 (PC_M5, INV_M5: the text holds the payload's first n bytes).
   fe_seg5 = fe_s5_malloc (C2 -> A) . fe_s5_mid (A -> M) . fe_s5_tail (M -> C5).
   rule 24: proves function LLVMFuzzerTestOneInput (segment S5; reuse search: proof-index LLVMFuzzerTestOneInput,
   ported from a working branch 08ad70da3bf).
   Ported from: lib/A/FSW_entry_s5.v on a working branch 0d34d65d2b7 (itself from the donor
   cgif_file_fuzzer lib/A/ACev.v:227-262 and lib/A/ACfi.v:120), every address from the B listing; the B-only steps from
   the old bespoke B proof lib/B/Prog/ASlotStgMemcpy.v on a working branch 179c25520a7 (its argument:
   s5 + s3 = text + n and text + n + 1 <= alloc_ceiling < 2^64, so neither UBSan check traps), restated in the walk form.
   Decisions (A's, at B's numerals, and the B-only point (5)):
   (1) the malloc: U = [] at the call, so the S form composes: FsEntryRt's fe_malloc (U form) gives the plain contract by
       FSupoisonU.amalloc_realizes_of_U, YCbp.amalloc04_rule_triv makes it the journal rule, and YC85.amalloc04_sub
       composes it into the walk's journal; its acall_kept keeps fs's statics (fs_stat), the closed footprint keeps the
       io (fe_same_io). The call chain chain_pre asks is the entry sp's record (YCbq.achain_push of the entry's empty
       chain) or empty. The rule asks no trace; tl_code gives the malloc / __asan_memcpy pcs of as_code B (PC_malloc,
       PC_memcpy) by computation.
   (2) n = 0: s3 is re-expressed as the literal 0 (YI08.st_ok_set_reg), so the run takes `beqz s3`; n > 0: the run
       stops at __asan_memcpy, FsEntryRt's fe_memcpy contract composes by FSW_K.fsw_intrin_atU.
   (3) the shadow byte load and the store text[n] (addresses text + n, no region of symbolic size): a0 = text + n is
       re-seated on a fresh atom 46 with the one-byte region [0, 1) (FSW_K.fsw_reseat_atom); the frame's two regions are
       dropped (YP06.st_ok_submem), and the token run (FSW_K fsw_aj_run_to_tokU) with the shadow entry (46, [0, 1)) reads
       the shadow byte and takes the slow path's `blt` back, then stores text[n] in the region; atom 46's fact
       [4096, 2^47 - 1] decides 0x81104 `beq a0, -1` not taken.
   (4) cstr_ok of text: the bytes from __asan_memcpy's post and the store, the shadow and the tail word from AR at the
       end (AR_shadow_law, FSW_strkit.block_word_tail_vis), the room past the NUL from FSW_entry_ar.fe_block_room.
   (5) B only, 0x810e4 `bltu a0, s3, 0x8123c` after a0 = not s5 = 2^64 - 1 - text: the run stops at 0x810e4, a0 is
       re-expressed as the difference (2^64 - 1) - s5 (YI08.U_not, st_ok_set_reg), and the facts s5 = text in
       [4096, 2^47], s3 = n in [0, 3 * 2^20] make the run's range test decide the branch not taken.
   (6) `len`'s shadow byte (fe_lensh, the ENTRY owner's 06:48Z ruling: last conjunct of INV_C2 / INV_A5 / INV_M5 /
       INV_C5): each run over the canonical regions starts from fe_ss_z (FSW_entry_canon.fe_ss_z_ok) and reads the byte
       back from the chunk (fe_lensh_of; the frame by fe_frame_z, the write windows by fe_awr_z); across malloc by the
       callee's journal (fe_lensh_journal), across __asan_memcpy by its post (the byte is outside its window), across
       the token run by the frame (the byte is outside r46 and the stack region).
   Every boundary state is rebuilt by fe_canon (fe_rebuild) from the journal and the memory facts fe_mem_ok.
   Section hypotheses: errno_low, ML, IMG (the A file's), tl_code, fe_ma, fe_mc (the entry's own runtime uses:
   FsEntryRt's malloc and __asan_memcpy, at the pcs lib/B/YF0l.v's Tfib_code names), discharged by the top file from
   the goal's premises (tl_code by YCeg.tl_code from TfibLib B). RELOC-B hypotheses: none (this segment takes no
   start-up or TfibSyms-B fact). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp YC85.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSW_K FSW_strkit FSW_pstat_store.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YCfn FSH_Harness FSH_Fn_entry FSW_entry_defs FSW_entry_canon.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YCem FSW_entry_ar YF0l.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Hypothesis errno_low : api_env tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis IMG : fs_img_facts tfibsegs B.
(* the entry's own runtime uses: FsEntryRt's malloc and __asan_memcpy, at the pcs TfibLib's code table names *)
Hypothesis tl_code : as_code B = YF0l.Tfib_code.
Hypothesis fe_ma : FSupoisonU.amalloc_realizesU tfibsegs B.
Hypothesis fe_mc : FSupoisonU.aintrin_realizesU tfibsegs B OCpy (pc_asan_memcpy (as_code B)).
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

(* ---- the walk's journal (fe_from's, U = []) ---- *)
Definition fe_J (cx : fecx) ly3 S3 (W3 : world tfibsegs) mem3 md3 (k : Z) : Prop :=
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 mem3 md3 k.

Lemma fe_sp_facts : forall cx, fe_base B cx ->
  fe_sp0 cx mod 16 = 0 /\ alloc_ceiling + LLVMF_STK <= fe_sp0 cx /\ fe_sp0 cx <= 2 ^ 47 /\
  fe_sp0 cx - 112 <= fe_sp1 cx <= fe_sp0 cx - 96 /\ fe_sp1 cx mod 32 = 0.
Proof.
intros cx ((HPRE & _) & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (H16 & _ & Hc & Hlo & Hhi & H47 & _). fold (fe_sp0 cx) in *.
unfold fe_sp1. pose proof (Z.div_mod (fe_sp0 cx - 96) 32 ltac:(lia)) as D.
pose proof (Z.mod_pos_bound (fe_sp0 cx - 96) 32 ltac:(lia)) as M.
pose proof (Z.div_mod (fe_sp0 cx) 16 ltac:(lia)) as D16.
split; [exact H16|]. split; [unfold LLVMF_STK in *; lia|]. split; [lia|].
split; [lia|]. rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

Lemma fe_jf : forall cx ly3 S3 W3 mem3 md3 k, fe_base B cx -> fe_J cx ly3 S3 W3 mem3 md3 k ->
  AR tfibsegs B ly3 S3 W3 mem3 md3 /\ In (0, c_fpos cx) (frames S3) /\ ly_F ly3 = ly_F (c_ly cx) /\
  frame_addr ly3 0 (c_fpos cx) = fe_F cx /\ flag_addr ly3 0 (c_fpos cx) = fe_FL cx /\
  ly_top ly3 = ly_top (c_ly cx) /\ fe_F cx mod 32 = 0 /\ 4096 <= fe_F cx /\ fe_F cx + 64 <= alloc_ceiling /\
  in_app (fe_F cx) 64 /\ 4096 <= fe_FL cx < alloc_ceiling.
Proof.
intros cx ly3 S3 W3 mem3 md3 k Hb HJ.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
assert (Hin : In (0, c_fpos cx) (frames S3)) by (rewrite Hfrs; left; reflexivity).
pose proof Hly as (_ & _ & _ & _ & _ & ELY & _ & _ & Etop & _).
assert (EF : frame_addr ly3 0 (c_fpos cx) = fe_F cx) by (unfold fe_F, frame_addr; rewrite ELY; reflexivity).
assert (EFL : flag_addr ly3 0 (c_fpos cx) = fe_FL cx) by (unfold fe_FL, flag_addr; rewrite ELY; reflexivity).
destruct (al_frames _ _ LAWS ly3 S3 W3 mem3 md3 0 (c_fpos cx) HAR Hin) as (Hal32 & Happ & _).
destruct (frames_bounds tfibsegs B LAWS ly3 S3 W3 mem3 md3 0 (c_fpos cx) HAR Hin) as (H4096 & Hfc & _).
destruct (al_flag _ _ LAWS ly3 S3 W3 mem3 md3 0 (c_fpos cx) HAR Hin) as (_ & _ & Hflapp & Hflc).
rewrite EF in Hal32, Happ, H4096, Hfc. rewrite EFL in Hflapp, Hflc.
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in Happ, Hfc.
unfold in_app in Hflapp.
repeat (split; [first [assumption | lia]|]). lia.
Qed.

(* ---- the memory the canonical state reads: the eleven saved words, the flag word, `len` = -1 ---- *)
Definition fe_sv_val (cx : fecx) (j : nat) : Z := bv_unsigned (nth (S j) (fe_extra cx) (Z_to_bv 64 0)).
Definition fe_mem_ok (cx : fecx) (m : word -> option byte) : Prop :=
  (forall j, (j < 11)%nat -> val_mem tfibsegs m (fe_sp0 cx - 8 * (Z.of_nat j + 1)) 8 (fe_sv_val cx j)) /\
  val_mem tfibsegs m (fe_F cx + 56) 8 (fe_FL cx) /\
  val_mem tfibsegs m (fe_F cx + 32) 8 (2 ^ 64 - 1).

Lemma fe_mem_kept : forall cx m m', fe_mem_ok cx m ->
  (forall a, fe_sp0 cx - 88 <= a < fe_sp0 cx \/ fe_F cx <= a < fe_F cx + 64 -> mbyte tfibsegs m' a = mbyte tfibsegs m a) ->
  fe_mem_ok cx m'.
Proof.
intros cx m m' (Hs & Hf & Hl) Hk. split; [|split].
- intros j Hj kk Hkk. rewrite Hk; [exact (Hs j Hj kk Hkk)|]. left. lia.
- intros kk Hkk. rewrite Hk; [exact (Hf kk Hkk)|]. right. lia.
- intros kk Hkk. rewrite Hk; [exact (Hl kk Hkk)|]. right. lia.
Qed.

Lemma fe_lit_m1 : forall E, sv_denot E (SLit (-1)) = Z_to_bv 64 (2 ^ 64 - 1).
Proof.
intros E. apply bv_eq. rewrite (wz (2 ^ 64 - 1)) by lia.
change (bv_unsigned (sv_denot E (SLit (-1)))) with (U E (SLit (-1))). rewrite U_SLit. reflexivity.
Qed.

Lemma fe_mem_of_regions : forall cx E m,
  fe_E cx E -> bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> 0 <= fe_FL cx < 2 ^ 64 ->
  region_ok tfibsegs E m (fe_frame_region [fe_len_lit (-1)]) ->
  region_ok tfibsegs E m (fs_ret_s0_region (-88) 0 fe_sv_chunks) ->
  fe_mem_ok cx m.
Proof.
intros cx E m HE E8 E24 HFL Hfr Hsv. split; [|split].
- intros j Hj.
  replace (fe_sp0 cx - 8 * (Z.of_nat j + 1)) with (fe_sp0 cx + - 8 * (Z.of_nat j + 1)) by lia.
  apply (fsw_field E m 8 (fe_sp0 cx) fe_sv_chunks (-88) 0 (-88) 0 (- 8 * (Z.of_nat j + 1)) 8 (SOff (33 + j) 0)
    (fe_sv_val cx j) Hsv E8).
  + unfold fe_sv_chunks. apply in_map_iff. exists j. split; [reflexivity|]. apply in_seq. lia.
  + rewrite fsw_SOff0. replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite (HE (S j)) by lia.
    unfold fe_sv_val. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + unfold fe_sv_val. pose proof (u64_range (nth (S j) (fe_extra cx) (Z_to_bv 64 0))) as R. unfold M64 in R.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + lia.
- apply (fsw_field E m 24 (fe_F cx) (YP09.mkChunk 56 (CVal 8 (SOff 44 0)) :: [fe_len_lit (-1)]) 0 64 0 64 56 8
    (SOff 44 0) (fe_FL cx) Hfr E24).
  + left. reflexivity.
  + rewrite fsw_SOff0. change 44%nat with (32 + 12)%nat. rewrite (HE 12%nat) by lia. reflexivity.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + lia.
- apply (fsw_field E m 24 (fe_F cx) (YP09.mkChunk 56 (CVal 8 (SOff 44 0)) :: [fe_len_lit (-1)]) 0 64 0 64 32 8
    (SLit (-1)) (2 ^ 64 - 1) Hfr E24).
  + right. left. reflexivity.
  + apply fe_lit_m1.
  + change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + lia.
Qed.

Lemma fe_sv_of_region : forall cx E m,
  fe_E cx E -> bv_unsigned (ew E 8) = fe_sp0 cx -> region_ok tfibsegs E m (fs_ret_s0_region (-88) 0 fe_sv_chunks) ->
  forall j, (j < 11)%nat -> val_mem tfibsegs m (fe_sp0 cx - 8 * (Z.of_nat j + 1)) 8 (fe_sv_val cx j).
Proof.
intros cx E m HE E8 Hsv j Hj.
replace (fe_sp0 cx - 8 * (Z.of_nat j + 1)) with (fe_sp0 cx + - 8 * (Z.of_nat j + 1)) by lia.
apply (fsw_field E m 8 (fe_sp0 cx) fe_sv_chunks (-88) 0 (-88) 0 (- 8 * (Z.of_nat j + 1)) 8 (SOff (33 + j) 0)
  (fe_sv_val cx j) Hsv E8).
- unfold fe_sv_chunks. apply in_map_iff. exists j. split; [reflexivity|]. apply in_seq. lia.
- rewrite fsw_SOff0. replace (33 + j)%nat with (32 + S j)%nat by lia. rewrite (HE (S j)) by lia.
  unfold fe_sv_val. rewrite Z_to_bv_bv_unsigned. reflexivity.
- unfold fe_sv_val. pose proof (u64_range (nth (S j) (fe_extra cx) (Z_to_bv 64 0))) as R. unfold M64 in R.
  change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
- lia.
Qed.

(* the canonical boundary state from the journal and the memory facts (fe_canon at U = []) *)
Lemma fe_rebuild : forall cx ly3 S3 W3 ms md3 k xs r,
  fe_base B cx -> fe_J cx ly3 S3 W3 (ms_mem ms) md3 k ->
  ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 r) (ms_mem ms) (YK11.seg_rom tfibsegs) ->
  YK11.getr (ms_regs ms) 8%bv = Z_to_bv 64 (fe_sp0 cx) -> YK11.getr (ms_regs ms) 24%bv = Z_to_bv 64 (fe_F cx) ->
  YK11.getr (ms_regs ms) 18%bv = Z_to_bv 64 (fe_F cx) -> YK11.getr (ms_regs ms) 25%bv = Z_to_bv 64 (fe_SF cx) ->
  fe_mem_ok cx (mrestrict (w_H W3) (ms_mem ms)) ->
  st_ok tfibsegs (Ereg (ms_regs ms) (fe_extra cx ++ xs)) (fe_ss r [fe_len_lit (-1)]) (restrict (w_H W3) ms).
Proof.
intros cx ly3 S3 W3 ms md3 k xs r Hb HJ Hms R8 R24 R18 R25 (Hsv & Hfl & Hln).
rewrite Hms at 2. set (regs' := ms_regs ms) in *. set (mem3 := ms_mem ms) in *.
destruct (fe_sp_facts cx Hb) as (Sp16 & Spc & Sp47 & _).
destruct (fe_jf cx ly3 S3 W3 mem3 md3 k Hb HJ) as (HAR & Hin & ELY & _ & _ & _ & _ & _ & _ & _ & HFL).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof asan_consts as (C1 & _).
apply (fe_canon B cx ly3 S3 [] W3 mem3 md3 regs' xs r [fe_len_lit (-1)]).
- apply ARU_nil. exact HAR.
- exact Hin.
- exact ELY.
- exact R8.
- exact R24.
- exact R18.
- exact R25.
- exact Sp16.
- unfold LLVMF_STK in Spc. lia.
- exact Sp47.
- intros a Ha. apply Hpres. unfold LLVMF_STK. lia.
- unfold fe_sv_chunks. apply Forall_map. apply Forall_forall. intros j Hj. apply in_seq in Hj.
  apply (chunk_ok_val tfibsegs _ _ (fe_sp0 cx) (- 8 * (Z.of_nat j + 1)) 8 (SOff (33 + j) 0) (fe_sv_val cx j)).
  + rewrite fsw_SOff0. replace (33 + j)%nat with (32 + S j)%nat by lia.
    rewrite (fe_extra_atom cx regs' xs (S j)) by lia. unfold fe_sv_val. rewrite Z_to_bv_bv_unsigned. reflexivity.
  + unfold fe_sv_val. pose proof (u64_range (nth (S j) (fe_extra cx) (Z_to_bv 64 0))) as R. unfold M64 in R.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  + lia.
  + replace (fe_sp0 cx + - 8 * (Z.of_nat j + 1)) with (fe_sp0 cx - 8 * (Z.of_nat j + 1)) by lia. apply Hsv. lia.
- apply YCem.rdword_of_val_mem; [exact Hfl | lia].
- apply fe_regions_wf_len_lit.
- constructor; [cbn; lia | constructor].
- constructor; [|constructor].
  apply (chunk_ok_val tfibsegs _ _ (fe_F cx) 32 8 (SLit (-1)) (2 ^ 64 - 1)); [apply fe_lit_m1 | lia | lia | exact Hln].
Qed.

(* the write windows of the canonical state's regions (and of extra regions in front) *)
Lemma fe_awr : forall cx E ly3 S3 W3 mem3 md3 k bl0 cs rs fr0,
  fe_base B cx -> fe_J cx ly3 S3 W3 mem3 md3 k ->
  bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx ->
  awr_ok tfibsegs B E rs LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP bl0 (ablocks B ly3 S3) ly3 [(0, c_fpos cx)] fr0 ->
  awr_ok tfibsegs B E (fe_regions cs ++ rs) LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP bl0 (ablocks B ly3 S3) ly3 [(0, c_fpos cx)] fr0.
Proof.
intros cx E ly3 S3 W3 mem3 md3 k bl0 cs rs fr0 Hb HJ E8 E24 E25 Hrs.
destruct (fe_jf cx ly3 S3 W3 mem3 md3 k Hb HJ) as (_ & _ & _ & EF & _).
unfold fe_regions. cbn [app].
eapply (awr_ok_cons_gen tfibsegs B E (fe_frame_region cs)); [reflexivity | exact E24 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi fe_frame_region] in Ha. left. right. right. right.
  exists 0, (c_fpos cx). split; [left; reflexivity|]. left. unfold in_zr, frame_rng. cbn [fst snd].
  rewrite EF. change (fs_frame_bytes 0) with 64. lia. }
eapply (awr_ok_cons_gen tfibsegs B E fe_shadow_region); [reflexivity | exact E25 | |].
{ intros a Ha. cbn [YP09.r_wlo YP09.r_whi fe_shadow_region] in Ha. left. right. right. right.
  exists 0, (c_fpos cx). split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd].
  rewrite EF. change (fs_frame_bytes 0 / 8) with 8. unfold fe_SF in Ha. lia. }
eapply (awr_ok_cons_stack tfibsegs B E (fs_ret_s0_region (-88) 0 fe_sv_chunks)); [reflexivity | exact E8 | cbn; unfold LLVMF_STK; lia | cbn; lia |].
exact Hrs.
Qed.

(* the closed footprint keeps the io *)
Lemma fe_closed : ~ YI16.sink_open_fp FS_PSTAT_FP.
Proof. unfold YI16.sink_open_fp. intros (r & Hr & Hb). cbn in Hr. repeat destruct Hr as [<-|Hr]; cbn in Hb; lia. Qed.
Lemma fe_same_io : forall cx ly3 S3 W3 mem3 md3 k, fe_J cx ly3 S3 W3 mem3 md3 k -> same_io (c_md cx) md3.
Proof. intros cx ly3 S3 W3 mem3 md3 k (_ & _ & _ & _ & Hio & _). exact (aos_step_closed_same_io _ _ _ fe_closed Hio). Qed.

(* the payload's bytes, kept by the journal while its block is live (a heap block is no static) *)
Lemma fe_payload : forall cx ly3 S3 W3 mem3 md3 k, fe_base B cx -> fe_J cx ly3 S3 W3 mem3 md3 k ->
  (forall b, In b (ablocks B (c_ly cx) (c_S cx)) -> In b (ablocks B ly3 S3)) ->
  forall i, 0 <= i < c_n cx -> aview tfibsegs (w_H W3) mem3 (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i).
Proof.
intros cx ly3 S3 W3 mem3 md3 k Hb HJ Hinc i Hi.
pose proof Hb as ((HPRE & _ & _ & _ & Hpn & _) & _). pose proof HPRE as (HAR0 & _).
destruct Hpn as [(Hn0 & _) | (_ & Hin)]; [lia|].
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
apply (F2 (c_p cx) (c_n cx) i Hin (Hinc _ Hin)).
- unfold req_size. destruct (Z.eqb_spec (c_n cx) 0); lia.
- intros Hf. pose proof (pstat_bounds _ Hf) as Hbd.
  apply (blk_img tfibsegs B LAWS _ _ _ _ _ (c_p cx) (c_n cx) (c_p cx + i) HAR0 Hin).
  + unfold req_size. destruct (Z.eqb_spec (c_n cx) 0); lia.
  + exact (fs_rw3_img _ Hbd).
Qed.

(* fs's counters read the four static words of FS_PSTAT_FP *)
Lemma fs_stat_kept : forall (W W' : world tfibsegs) m m' live cnt,
  (forall a, inFP FS_PSTAT_FP a -> mbyte tfibsegs (mrestrict (w_H W') m') a = mbyte tfibsegs (mrestrict (w_H W) m) a) ->
  fs_stat tfibsegs W m live cnt -> fs_stat tfibsegs W' m' live cnt.
Proof.
intros W W' m m' live cnt Hk (peak & G1 & G2 & G3 & G4 & R). exists peak.
assert (VB : forall g v, In (g, g + 8) FS_PSTAT_FP -> val_mem tfibsegs (mrestrict (w_H W) m) g 8 v ->
  val_mem tfibsegs (mrestrict (w_H W') m') g 8 v).
{ intros g v Hg Hv kk Hkk. rewrite Hk; [exact (Hv kk Hkk)|]. apply (inFP_FS_PSTAT_FP g Hg). lia. }
unfold fs_glob, fs_glob_at in *. unfold G_LIVE, G_PEAK, G_COUNT, G_FAIL in *.
split; [apply VB; [unfold FS_PSTAT_FP; simpl; tauto | exact G1]|].
split; [apply VB; [unfold FS_PSTAT_FP; simpl; tauto | exact G2]|].
split; [apply VB; [unfold FS_PSTAT_FP; simpl; tauto | exact G3]|].
split; [apply VB; [unfold FS_PSTAT_FP; simpl; tauto | exact G4]|].
exact R.
Qed.

(* the block a malloc appended is not one of the older blocks *)
Lemma fe_fresh : forall ly S (W : world tfibsegs) mem md l t n,
  AR tfibsegs B ly S W mem md -> ablocks B ly S = l ++ [(t, n)] -> ~ In (t, n) l.
Proof.
intros ly S W mem md l t n HAR E Hin. apply in_split in Hin as (l1 & l2 & ->).
pose proof (sep_blocks_pos tfibsegs B LAWS ly S W mem md (t, n) (t, n) l1 l2 [] HAR
  ltac:(rewrite E, <- app_assoc; reflexivity)) as D.
assert (Hin : In (t, n) (ablocks B ly S)) by (rewrite E; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [Hq _].
unfold zdisjoint, block_rng in D. cbn [fst snd] in D. lia.
Qed.


(* ---- the strnlen n and the text ---- *)
Lemma zfind_some : forall c l j, zfind c l = Some j -> (j < length l)%nat /\ (forall i, (i < j)%nat -> nth i l 0 <> c).
Proof.
intros c l. induction l as [|x t IH]; intros j H; [discriminate H|]. cbn in H.
destruct (Z.eqb_spec x c) as [->|Hx].
- injection H as <-. split; [cbn; lia | intros i Hi; lia].
- destruct (zfind c t) as [j'|] eqn:E; [|discriminate H]. cbn in H. injection H as <-.
  destruct (IH j' eq_refl) as [H1 H2]. split; [cbn; lia|].
  intros i Hi. destruct i as [|i]; [exact Hx|]. cbn. apply H2. lia.
Qed.
Lemma zfind_none : forall c l, zfind c l = None -> forall i, (i < length l)%nat -> nth i l 0 <> c.
Proof.
intros c l. induction l as [|x t IH]; intros H i Hi; [cbn in Hi; lia|]. cbn in H.
destruct (Z.eqb_spec x c) as [->|Hx]; [discriminate H|].
destruct (zfind c t) eqn:E; [discriminate H|].
destruct i as [|i]; [exact Hx|]. cbn. apply IH; [reflexivity | cbn in Hi; lia].
Qed.
Lemma fe_bytes_len : forall cx, fe_base B cx -> length (fe_bytes cx) = Z.to_nat (c_n cx).
Proof.
intros cx ((_ & _ & _ & _ & _ & Hlen & _) & _). unfold fe_bytes. rewrite length_map, Hlen, Nat2Z.id. reflexivity.
Qed.
Lemma fe_bytes_byte : forall cx i, 0 <= nth i (fe_bytes cx) 0 < 256.
Proof.
intros cx i. unfold fe_bytes. destruct (Nat.lt_ge_cases i (length (c_pl cx))) as [Hi|Hi].
- rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hi).
  rewrite map_nth. pose proof (bv_unsigned_in_range 8 (nth i (c_pl cx) (Z_to_bv 8 0))) as R. unfold bv_modulus in R.
  change (2 ^ Z.of_N 8) with 256 in R. lia.
- rewrite nth_overflow by (rewrite length_map; exact Hi). lia.
Qed.
Lemma fe_n_bounds : forall cx, fe_base B cx -> 0 <= fe_n cx <= c_n cx.
Proof.
intros cx Hb. pose proof (fe_bytes_len cx Hb) as Hl. pose proof Hb as ((_ & _ & _ & _ & _ & Hlen & _) & _).
unfold fe_n. destruct (zfind 0 (fe_bytes cx)) as [j|] eqn:E; [|lia].
destruct (zfind_some 0 _ j E) as [Hj _]. lia.
Qed.
Lemma fe_tb_len : forall cx, fe_base B cx -> Z.of_nat (length (fe_tb cx)) = fe_n cx.
Proof.
intros cx Hb. pose proof (fe_bytes_len cx Hb) as Hl. pose proof (fe_n_bounds cx Hb) as Hn.
unfold fe_tb. rewrite length_firstn, Hl. lia.
Qed.
Lemma fe_tb_nth : forall cx j, (j < length (fe_tb cx))%nat -> nth j (fe_tb cx) 0 = nth j (fe_bytes cx) 0.
Proof.
intros cx j Hj. unfold fe_tb in *. rewrite length_firstn in Hj. rewrite nth_firstn.
destruct (Nat.ltb_spec j (Z.to_nat (fe_n cx))); [reflexivity | lia].
Qed.
Lemma fe_tb_nz : forall cx, fe_base B cx -> Forall (fun c => c <> 0) (fe_tb cx).
Proof.
intros cx Hb. apply Forall_forall. intros x Hx. apply (In_nth _ _ 0) in Hx as (j & Hj & <-).
rewrite fe_tb_nth by exact Hj. pose proof (fe_bytes_len cx Hb) as Hl. pose proof (fe_tb_len cx Hb) as Ht.
unfold fe_n in Ht. destruct (zfind 0 (fe_bytes cx)) as [j0|] eqn:E.
- destruct (zfind_some 0 _ j0 E) as [_ H2]. apply H2. lia.
- apply (zfind_none 0 _ E). pose proof (fe_n_bounds cx Hb). unfold fe_n in H. rewrite E in H. lia.
Qed.

(* ---- frames of runs ---- *)
Lemma mbyte_frame : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  mbyte tfibsegs (mrestrict H m') a = mbyte tfibsegs (mrestrict H m) a.
Proof.
intros E rs m m' H a HF Ha Hn. unfold mbyte, mrestrict.
rewrite (HF (Z_to_bv 64 a)) by (rewrite wz by exact Ha; exact Hn). reflexivity.
Qed.
Lemma aview_frame : forall E rs (m m' : word -> option byte) (H : word -> bool) a,
  frame_of E rs m m' -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview tfibsegs H m' a = aview tfibsegs H m a.
Proof. intros E rs m m' H a HF Ha Hn. unfold aview. rewrite (mbyte_frame E rs m m' H a HF Ha Hn). reflexivity. Qed.
Lemma fe_wrange : forall E cs rs a, in_wrange E (fe_regions cs ++ rs) a ->
  bv_unsigned (ew E 24) <= a < bv_unsigned (ew E 24) + 64 \/ bv_unsigned (ew E 25) <= a < bv_unsigned (ew E 25) + 8 \/
  bv_unsigned (ew E 8) - 88 <= a < bv_unsigned (ew E 8) \/ in_wrange E rs a.
Proof.
intros E cs rs a (r & Hr & Ha). unfold fe_regions in Hr. cbn [app] in Hr.
destruct Hr as [<-|[<-|[<-|Hr]]]; cbn in Ha; [lia | lia | lia |]. right. right. right. exists r. auto.
Qed.
Lemma val_mem1_of_aview : forall (H : word -> bool) m a v, aview tfibsegs H m a = Some v ->
  val_mem tfibsegs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv kk Hkk. destruct (aview_byte tfibsegs H m a v Hv) as (b & Hb & -> & Hr).
replace kk with 0%nat by lia. rewrite Z.add_0_r, Hb. f_equal.
unfold YO0f.le_byte. cbn. rewrite Z.shiftr_0_r, !Z.mod_small by lia. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* cstr_ok of an n + 1 byte block holding l and its NUL (the room past it is the premise Hroom) *)
Lemma fe_cstr_new : forall ly S W mem md text (l : list Z),
  AR tfibsegs B ly S W mem md -> In (text, Z.of_nat (length l) + 1) (ablocks B ly S) -> Z.of_nat (length l) < 2 ^ 32 ->
  text + (Z.of_nat (length l) + 1) + 8 <= alloc_ceiling ->
  garr8 tfibsegs (mrestrict (w_H W) mem) text (l ++ [0]) -> Forall (fun c => c <> 0) l ->
  cstr_ok tfibsegs W mem text l.
Proof.
intros ly S W mem md text l HAR Hin H32 Hroom Hg Hnz. set (n := Z.of_nat (length l)) in *.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
assert (Hrq : req_size (n + 1) = n + 1) by (unfold req_size; destruct (Z.eqb_spec (n + 1) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & H4096 & Hceil & Happ & _).
destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (Hbs & Hhv). rewrite Hrq in Happ, Hceil, Hbs, Hhv.
split; [split; [exact Hg | exact Hnz]|]. split; [exact H4096|]. split; [lia|]. split; [(destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & _ & _ & _ & _ & HmxL); unfold MALLOC_MAX in HmxL; lia)|].
split.
{ unfold amem_range. unfold in_app in Happ. unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
split; [exact (block_shadow_range _ _ text (n + 1) text (n + 1) Hbs ltac:(lia) ltac:(lia))|].
split; [exact Hhv|].
intros a Ha. apply (block_word_tail_vis B ly S W mem md text (n + 1) HAR Hin ltac:(lia)).
replace (text + (n + 1) - 1) with (text + n) by lia. lia.
Qed.

Lemma fe_SF_bounds : forall cx, 4096 <= fe_F cx -> fe_F cx + 64 <= alloc_ceiling ->
  kLowMemEnd <= fe_SF cx /\ fe_SF cx + 8 <= kHighMemBeg.
Proof.
intros cx H1 H2. pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (shadow_addr_bounds (fe_F cx) ltac:(unfold kHighMemEnd in *; lia)) as (Hs1 & _).
pose proof (shadow_addr_bounds (fe_F cx + 63) ltac:(unfold kHighMemEnd in *; lia)) as (_ & Hs4).
assert (Hs5 : shadow_addr (fe_F cx) + 7 <= shadow_addr (fe_F cx + 63)) by (unfold shadow_addr; Z.div_mod_to_equations; lia).
unfold fe_SF. lia.
Qed.

(* heap blocks and fs's statics lie outside the canonical state's write windows *)
Lemma fe_blk_nw : forall cx E ly3 S3 W3 mem3 md3 k cs b m a,
  fe_base B cx -> fe_J cx ly3 S3 W3 mem3 md3 k ->
  bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx ->
  In (b, m) (ablocks B ly3 S3) -> b <= a < b + req_size m -> ~ in_wrange E (fe_regions cs) a.
Proof.
intros cx E ly3 S3 W3 mem3 md3 k cs b m a Hb HJ B8 B24 B25 Hin Ha Hw.
destruct (fe_sp_facts cx Hb) as (_ & Spc & _). unfold LLVMF_STK in Spc.
destruct (fe_jf cx _ _ _ _ _ _ Hb HJ) as (HAR & Hfin & _ & EF & _ & _ & _ & F4096 & Fceil & _).
pose proof (fe_SF_bounds cx F4096 Fceil) as SFb. pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & _ & Bceil & Bapp & _).
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin Hfin) as Bsep.
rewrite EF in Bsep. unfold zdisjoint in Bsep. cbn [fst snd] in Bsep. change (fs_frame_bytes 0) with 64 in Bsep.
unfold in_app in Bapp.
rewrite <- (app_nil_r (fe_regions cs)) in Hw. apply fe_wrange in Hw. rewrite B8, B24, B25 in Hw.
destruct Hw as [Hw|[Hw|[Hw|(r & [] & _)]]]; unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, ASAN_CEIL in *; lia.
Qed.
Lemma fe_pstat_nw : forall cx E ly3 S3 W3 mem3 md3 k cs a,
  fe_base B cx -> fe_J cx ly3 S3 W3 mem3 md3 k ->
  bv_unsigned (ew E 8) = fe_sp0 cx -> bv_unsigned (ew E 24) = fe_F cx -> bv_unsigned (ew E 25) = fe_SF cx ->
  inFP FS_PSTAT_FP a -> ~ in_wrange E (fe_regions cs) a.
Proof.
intros cx E ly3 S3 W3 mem3 md3 k cs a Hb HJ B8 B24 B25 Ha Hw.
destruct (fe_sp_facts cx Hb) as (_ & Spc & _). unfold LLVMF_STK in Spc.
destruct (fe_jf cx _ _ _ _ _ _ Hb HJ) as (HAR & Hfin & _ & EF & _ & _ & _ & F4096 & Fceil & _).
pose proof (fe_SF_bounds cx F4096 Fceil) as SFb. pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (pstat_bounds a Ha) as Hab.
rewrite <- (app_nil_r (fe_regions cs)) in Hw. apply fe_wrange in Hw. rewrite B8, B24, B25 in Hw.
destruct Hw as [Hw|[Hw|[Hw|(r & [] & _)]]]; [| unfold kLowMemEnd in *; lia | lia].
destruct (al_client_img _ _ LAWS _ _ _ _ _ a HAR) as [_ Himg];
  [right; left; exists 0, (c_fpos cx); rewrite EF; change (fs_frame_bytes 0) with 64; split; [exact Hfin | lia]|].
exact (Himg (fs_rw3_img a Hab)).
Qed.
(* the payload's bytes at the entry *)
Lemma fe_pl_byte : forall cx, fe_base B cx -> forall i, 0 <= i < c_n cx ->
  aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i) = Some (nth (Z.to_nat i) (fe_bytes cx) 0).
Proof.
intros cx Hb i Hi. pose proof (fe_bytes_len cx Hb) as Hl.
pose proof Hb as ((_ & _ & _ & _ & _ & _ & Hg & _) & _).
destruct (Hg (Z.to_nat i) ltac:(change (map (fun b : byte => bv_unsigned b) (c_pl cx)) with (fe_bytes cx); lia))
  as (Hv & Hr).
rewrite Z2Nat.id in Hv by lia.
exact (YCem.aview_of_val_mem1 tfibsegs _ _ _ _ Hv Hr).
Qed.
Ltac fe_cs := unfold acallee_saved; lazymatch goal with |- context [bv_unsigned ?q] =>
  let z := eval vm_compute in (bv_unsigned q) in change (bv_unsigned q) with z end; lia.

(* ---- the boundary M at 0x810e0 (the return of __asan_memcpy and the target of `beqz s3`): after __asan_memcpy (n > 0)
   or the `beqz s3` (n = 0); the text block is allocated and holds the payload's first n bytes, `len`'s shadow byte is
   0 (fe_lensh); the state is fe_ss PC_M5 [fe_len_lit (-1)] ---- *)
Definition PC_M5 : Z := 0x810e0.
Definition INV_M5 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text,
    U3 = [] /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(text, fe_n cx + 1)] /\
    fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1) /\ fe_regs_core cx E /\
    fe_n cx <= 3 * 2 ^ 20 /\ ew E 19 = Z_to_bv 64 (fe_n cx) /\ ew E 21 = Z_to_bv 64 text /\
    ew E 22 = Z_to_bv 64 SHADOW_OFF /\
    (forall i, 0 <= i < fe_n cx ->
       aview tfibsegs (w_H W3) (ms_mem ms3) (text + i) = Some (nth (Z.to_nat i) (fe_bytes cx) 0)) /\
    fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx + 3) /\ fe_lensh cx W3 (ms_mem ms3).

(* the address text + n on the fresh atom 46, its one-byte region, and the token run's shadow entry *)
Definition r46 : YP09.region := YP09.mkRegion (Some 46%nat) 0 1 0 1 [].
Definition SH5 : list shent := [mkSHE 46 0 1].
Definition Bx5 : sv := SOff 22 0.

Lemma subregion_refl : forall r, subregion r r.
Proof. intros r. split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; lia | auto]. Qed.
Lemma reg_at : forall (H : word -> bool) E ss ms (r : bv 5) j,
  st_ok tfibsegs E ss (restrict H ms) -> sr_get (ss_regs ss) r = SOff j 0 -> YK11.getr (ms_regs ms) r = ew E j.
Proof. intros H E ss ms r j HS Hr. rewrite (st_ok_restrict_reg tfibsegs H E ss ms r HS), Hr, fsw_SOff0. reflexivity. Qed.
Lemma denot_lit0 : forall E, sv_denot E (SLit 0) = Z_to_bv 64 0.
Proof. intros E. apply bv_eq. rewrite (wz 0) by lia. change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)). rewrite U_SLit. reflexivity. Qed.


Lemma fe_s5_tail : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss PC_C5 [fe_len_lit (-1)]) (INV_C5 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss PC_M5 [fe_len_lit (-1)]) INV_M5.
Proof.
intros POST HC5 cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (text & -> & Hbl & (Hk & Hio & Hpay & Hbb) & Hcore & Hn3 & E19 & E21 & E22 & Htxt & Hst & Hlsh).
pose proof Hcore as (C8 & C9 & C2 & C18 & C24 & C25 & C3 & C4 & C26 & C27).
destruct (fe_sp_facts cx Hb) as (Sp16 & Spc & Sp47 & Sp1 & Sp132). unfold LLVMF_STK in Spc.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (fe_n_bounds cx Hb) as Hnb. pose proof (fe_tb_len cx Hb) as Htl.
set (n := fe_n cx) in *.
assert (HJ0 : fe_J cx ly3 S3 W3 (ms_mem ms3) md3 k) by (unfold fe_J; rewrite <- (unpoison_nil (ms_mem ms3)); exact HJ).
destruct (fe_jf cx _ _ _ _ _ _ Hb HJ0) as (HAR & Hfin & ELY & EF & EFL & Etop & F32 & F4096 & Fceil & Fapp & HFL).
pose proof (fe_SF_bounds cx F4096 Fceil) as SFb.
assert (Hin : In (text, n + 1) (ablocks B ly3 S3)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (n + 1) = n + 1) by (unfold req_size; destruct (Z.eqb_spec (n + 1) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (T16 & T4096 & Tceil & Tapp & _ & _ & Tn).
rewrite Hrq in Tceil, Tapp. unfold in_app in Tapp.
pose proof (FSW_entry_ar.fe_block_room B _ _ _ _ _ _ _ HAR Hin) as Troom. rewrite Hrq in Troom.
pose proof (fe_fresh _ _ _ _ _ _ _ _ HAR Hbl) as Tfresh.
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin Hfin) as Tsep.
rewrite Hrq, EF in Tsep. unfold zdisjoint in Tsep. cbn [fst snd] in Tsep. change (fs_frame_bytes 0) with 64 in Tsep.
assert (B8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite C8; apply wz; lia).
assert (B24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite C24; apply wz; lia).
assert (B25 : bv_unsigned (ew E 25) = fe_SF cx) by (rewrite C25; apply wz; unfold kHighMemBeg in SFb; lia).
assert (NWt : forall a, text <= a < text + n + 1 -> ~ in_wrange E (fe_regions [fe_len_lit (-1)]) a).
{ intros a Ha. apply (fe_blk_nw cx E ly3 S3 W3 _ md3 k _ text (n + 1) a Hb HJ0 B8 B24 B25 Hin). rewrite Hrq. lia. }
assert (NWs : forall a, inFP FS_PSTAT_FP a -> ~ in_wrange E (fe_regions [fe_len_lit (-1)]) a)
  by exact (fun a Ha => fe_pstat_nw cx E ly3 S3 W3 _ md3 k _ a Hb HJ0 B8 B24 B25 Ha).
(* `len`'s shadow byte as a chunk (fe_ss_z), the facts on the shadow base, the text (s5) and n (s3), then run
   `not a0, s5` (0x810e0) *)
pose proof (fe_ss_z_ok cx E PC_M5 [fe_len_lit (-1)] (w_H W3) ms3 HS B25 Hlsh) as HSz.
clear HS.
pose proof (st_ok_add_fact tfibsegs E _ _ 22%nat (mkAF SHADOW_OFF SHADOW_OFF 0) HSz) as HSf1.
specialize (HSf1 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E22, wz by (unfold SHADOW_OFF; lia);
  change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia)).
clear HSz.
pose proof (st_ok_add_fact tfibsegs E _ _ 21%nat (mkAF 4096 (2 ^ 47) 0) HSf1) as HSf2.
specialize (HSf2 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E21, wz by lia;
  change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia)).
clear HSf1.
pose proof (st_ok_add_fact tfibsegs E _ _ 19%nat (mkAF 0 (3 * 2 ^ 20) 0) HSf2) as HSa.
specialize (HSa ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E19, wz by lia;
  change (2 ^ 0) with 1; rewrite Z.mod_1_r; lia)).
clear HSf2.
fsw_aj_run_toU entry_tbl_ok HSa HJ HARU 0x810e4.
{ cbn [ss_mem add_atom fe_ss_z]. apply fe_awr_z. rewrite <- (app_nil_r (fe_regions _)).
  apply (fe_awr cx E ly3 S3 W3 _ md3 k _ _ [] _ Hb HJ0 B8 B24 B25). apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ => rename m into msA; set (mdA := d) in * end.
lazymatch type of HF with frame_of ?Ef _ ?m1 ?m2 => change (frame_of Ef (fe_regions_z [fe_len_lit (-1)]) m1 m2) in HF end.
apply fe_frame_z in HF.
clear HFr HG.
assert (HtxtA : forall i, 0 <= i < n ->
  aview tfibsegs (w_H W3) (ms_mem msA) (text + i) = Some (nth (Z.to_nat i) (fe_bytes cx) 0)).
{ intros i Hi. rewrite (aview_frame E _ (ms_mem ms3) (ms_mem msA) (w_H W3) (text + i) HF); [exact (Htxt i Hi) | lia |].
  apply NWt. lia. }
assert (HstA : fs_stat tfibsegs W3 (ms_mem msA) (c_live cx) (c_cnt cx + 3)).
{ apply (fs_stat_kept W3 W3 (ms_mem ms3) (ms_mem msA)); [|exact Hst]. intros a Ha.
  apply (mbyte_frame E _ _ _ _ a HF); [pose proof (pstat_bounds a Ha); lia | exact (NWs a Ha)]. }
clear HF Htxt Hst.
(* B only (0x810e4 `bltu a0, s3` to the UBSan trap 0x8123c): a0 = not s5 = 2^64 - 1 - text, re-expressed as the
   difference (2^64 - 1) - s5, whose range [2^64 - 1 - 2^47, 2^64 - 4097] lies above s3's [0, 3 * 2^20]: the run then
   decides the branch not taken (text + n does not wrap) *)
assert (R10n : YK11.getr (ms_regs msA) 10%bv = Z_to_bv 64 (2 ^ 64 - 1 - text)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E _ msA 10%bv HSa).
  change (sr_get (ss_regs _) 10%bv) with (SAlu ALU_XOR (SOff 21 0) (SLit (-1))).
  rewrite denot_lit_U, (U_not E 21 text E21) by lia. reflexivity. }
pose proof (st_ok_set_reg tfibsegs E _ _ 10%bv (SAlu ALU_SUB (SLit (-1)) (SOff 21 0)) HSa) as HS1.
specialize (HS1 ltac:(intros Heq; apply (f_equal bv_unsigned) in Heq; vm_compute in Heq; discriminate Heq)).
specialize (HS1 ltac:(change (YK11.getr (ms_regs (restrict (w_H W3) msA)) 10%bv) with (YK11.getr (ms_regs msA) 10%bv);
  rewrite R10n, denot_lit_U, U_SAlu; cbn [zalu_raw]; rewrite U_SLit, (U_atom_off E 21 text 0 E21) by lia;
  f_equal; change (zcanon (-1)) with (2 ^ 64 - 1); rewrite Z.add_0_r; symmetry; apply zcanon_id; unfold M64; lia)).
clear HSa.
(* run `bltu a0, s3` (not taken) and `add a0, s5, s3` *)
fsw_aj_run_toU entry_tbl_ok HS1 HJ HARU 0x810ec.
{ lazymatch goal with |- awr_ok _ _ _ ?rs _ _ _ _ _ _ _ _ => change rs with (fe_regions_z [fe_len_lit (-1)]) end.
  apply fe_awr_z. rewrite <- (app_nil_r (fe_regions _)).
  apply (fe_awr cx E ly3 S3 W3 _ md3 k _ _ [] _ Hb HJ0 B8 B24 B25). apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ => try rename m into ms; set (md4 := d) in * end.
lazymatch type of HF with frame_of ?Ef _ ?m1 ?m2 => change (frame_of Ef (fe_regions_z [fe_len_lit (-1)]) m1 m2) in HF end.
apply fe_frame_z in HF.
pose proof (fe_lensh_of cx E _ (w_H W3) ms HS1 eq_refl B25) as Hlsh1.
clear HFr HG.
assert (HJ1 : fe_J cx ly3 S3 W3 (ms_mem ms) md4 k) by (unfold fe_J; rewrite <- (unpoison_nil (ms_mem ms)); exact HJ).
pose proof (proj1 HJ1) as HAR1.
assert (Htxt1 : forall i, 0 <= i < n ->
  aview tfibsegs (w_H W3) (ms_mem ms) (text + i) = Some (nth (Z.to_nat i) (fe_bytes cx) 0)).
{ intros i Hi. rewrite (aview_frame E _ (ms_mem msA) (ms_mem ms) (w_H W3) (text + i) HF); [exact (HtxtA i Hi) | lia |].
  apply NWt. lia. }
assert (Hst1 : fs_stat tfibsegs W3 (ms_mem ms) (c_live cx) (c_cnt cx + 3)).
{ apply (fs_stat_kept W3 W3 (ms_mem msA) (ms_mem ms)); [|exact HstA]. intros a Ha.
  apply (mbyte_frame E _ _ _ _ a HF); [pose proof (pstat_bounds a Ha); lia | exact (NWs a Ha)]. }
assert (HM1 : fe_mem_ok cx (mrestrict (w_H W3) (ms_mem ms))).
{ apply (fe_mem_of_regions cx E); [exact HE | exact B8 | exact B24 | lia | |].
  - exact (fsw_region_nth E _ (restrict (w_H W3) ms) 0 _ HS1 eq_refl).
  - exact (fsw_region_nth E _ (restrict (w_H W3) ms) 2 _ HS1 eq_refl). }
clear HF HtxtA HstA.
(* a0 = text + n on the fresh atom 46 *)
assert (R10 : YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 (text + n)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 10%bv HS1).
  change (sr_get (ss_regs _) 10%bv) with (SAlu ALU_ADD (SOff 19 0) (SOff 21 0)).
  rewrite denot_lit_U, U_SAlu. cbn [zalu_raw].
  rewrite (U_atom_off E 19 n 0 E19), (U_atom_off E 21 text 0 E21) by lia.
  f_equal. replace (n + 0 + (text + 0)) with (text + n) by lia. apply zcanon_id. unfold M64. lia. }
pose proof (fsw_reseat_atom E _ (restrict (w_H W3) ms) 10%bv 46 0 1 (mkAF 4096 (2 ^ 47 - 1) 0) HS1 eq_refl) as HS2.
change (YK11.getr (ms_regs (restrict (w_H W3) ms)) 10%bv) with (YK11.getr (ms_regs ms) 10%bv) in HS2.
rewrite R10 in HS2.
set (E46 := ewset E 46 (Z_to_bv 64 (text + n))) in HS2.
assert (Hv46 : bv_unsigned (ew E46 46) = text + n) by (unfold E46; rewrite ew_ewset_same; apply wz; lia).
assert (E46o : forall j, j <> 46%nat -> ew E46 j = ew E j) by (intros j Hj; unfold E46; apply ew_ewset_other; exact Hj).
assert (Tp1 : forall a, text <= a < text + (n + 1) -> apresent (w_H W3) (ms_mem ms) a).
{ intros a Ha. destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR1 Hin) as (_ & _ & _ & _ & Hp & _).
  rewrite Hrq in Hp. exact (proj1 (Hp a Ha)). }
specialize (HS2 ltac:(intros Heq; apply (f_equal bv_unsigned) in Heq; vm_compute in Heq; discriminate Heq) eq_refl).
specialize (HS2 ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
  rewrite Hv46; split; [lia|]; split; [lia|]; split; [|apply Forall_nil];
  intros o Ho; apply (apresent_writable tfibsegs (w_H W3) (ms_mem ms)); apply Tp1; lia)).
specialize (HS2 ltac:(cbn [ss_mem all_disjoint]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Hv46, !E46o by discriminate; rewrite B24, B25, B8;
  unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, ASAN_CEIL in *; repeat split; lia)).
specialize (HS2 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Hv46; change (2 ^ 0) with 1;
  rewrite Z.mod_1_r; lia)).
pose proof (st_ok_submem tfibsegs E46 _ _ [r46; fs_ret_s0_region (-88) 0 fe_sv_chunks] HS2) as HS3.
specialize (HS3 ltac:(cbn [ss_mem add_atom]; apply submem_keep; [apply subregion_refl|];
  apply submem_drop; apply submem_drop; apply submem_keep; [apply subregion_refl | apply submem_nil]) eq_refl).
clear HS2 HS1.
assert (SHOK : sh_ok tfibsegs Bx5 SH5 E46 (mrestrict (w_H W3) (ms_mem ms))).
{ unfold sh_ok, SH5. constructor; [|constructor]. unfold shent_ok, app_apart, Bx5. cbn [she_m she_lo she_hi].
  assert (U22 : U E46 (SOff 22 0) = SHADOW_OFF)
    by (unfold U; rewrite fsw_SOff0, E46o by discriminate; rewrite E22; apply wz; unfold SHADOW_OFF; lia).
  assert (U46 : U E46 (SOff 46 0) = text + n) by (unfold U; rewrite fsw_SOff0; exact Hv46).
  rewrite U22, U46. split.
  - change (rd_of tfibsegs (mrestrict (w_H W3) (ms_mem ms))) with (aview tfibsegs (w_H W3) (ms_mem ms)).
    destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR1 Hin) as (Hbs & _). rewrite Hrq in Hbs.
    apply (block_shadow_range _ _ text (n + 1) _ _ Hbs); lia.
  - intros a Ha. unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF, ASAN_CEIL in *. lia. }
fsw_aj_run_to_tokU entry_tbl_ok HS3 HJ HARU SHOK fs_Bspan 0x8110c.
- cbn [ss_mem].
  eapply (awr_ok_cons_gen tfibsegs B E46 r46); [reflexivity | exact Hv46 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi r46] in Ha. left. right. right. left.
    exists text, (n + 1). split; [exact Hin|]. split; [exact Tfresh|]. rewrite Hrq. lia. }
  eapply (awr_ok_cons_stack tfibsegs B E46 (fs_ret_s0_region (-88) 0 fe_sv_chunks));
    [reflexivity | rewrite E46o by discriminate; exact B8 | cbn; unfold LLVMF_STK; lia | cbn; lia |].
  apply awr_ok_nil.
- lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ => rename m into ms5; set (md5 := d) in * end.
  lazymatch type of HS3 with st_ok _ ?Ex _ _ => set (E5 := Ex) in HS3 end.
  lazymatch type of HF with frame_of _ ?rs _ _ => set (rs5 := rs) in HF end.
  clear HFr HG SHOK.
  assert (Eo : forall j, (j < 46)%nat -> ew E5 j = ew E j).
  { intros j Hj. unfold E5, E46. rewrite !ew_ewset_other by lia. reflexivity. }
  assert (Ev46 : bv_unsigned (ew E5 46) = text + n) by (unfold E5; rewrite !ew_ewset_other by lia; exact Hv46).
  assert (NW5 : forall a, a <> text + n -> ~ (fe_sp0 cx - 88 <= a < fe_sp0 cx) -> ~ in_wrange E46 rs5 a).
  { intros a H1 H2 (r & Hr & Ha). unfold rs5 in Hr. cbn [ss_mem] in Hr.
    destruct Hr as [<-|[<-|[]]]; cbn [r46 fs_ret_s0_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha;
    [rewrite Hv46 in Ha | rewrite E46o, B8 in Ha by discriminate]; lia. }
  assert (HJ5 : fe_J cx ly3 S3 W3 (ms_mem ms5) md5 k) by (unfold fe_J; rewrite <- (unpoison_nil (ms_mem ms5)); exact HJ).
  assert (Ems5 : ms5 = YK11.mkst (ms_regs ms5) (Z_to_bv 64 PC_C5) (ms_mem ms5) (YK11.seg_rom tfibsegs))
    by exact (st_ok_restrict_mkst tfibsegs (w_H W3) E5 _ ms5 HS3 eq_refl).
  assert (RG : forall (r : bv 5) j, sr_get (ss_regs (sh_ss
      ltac:(lazymatch type of HS3 with st_ok _ _ ?ss _ => exact (mkSH ss 0 [] true []) end))) r = SOff j 0 ->
      (j < 46)%nat -> YK11.getr (ms_regs ms5) r = ew E j).
  { intros r j Hr Hj. rewrite <- (Eo j Hj). exact (reg_at (w_H W3) E5 _ ms5 r j HS3 Hr). }
  pose proof (RG 8%bv 8%nat eq_refl ltac:(lia)) as R8. pose proof (RG 9%bv 9%nat eq_refl ltac:(lia)) as R9.
  pose proof (RG 2%bv 2%nat eq_refl ltac:(lia)) as R2. pose proof (RG 18%bv 18%nat eq_refl ltac:(lia)) as R18.
  pose proof (RG 24%bv 24%nat eq_refl ltac:(lia)) as R24. pose proof (RG 25%bv 25%nat eq_refl ltac:(lia)) as R25.
  pose proof (RG 3%bv 3%nat eq_refl ltac:(lia)) as R3. pose proof (RG 4%bv 4%nat eq_refl ltac:(lia)) as R4.
  pose proof (RG 26%bv 26%nat eq_refl ltac:(lia)) as R26. pose proof (RG 27%bv 27%nat eq_refl ltac:(lia)) as R27.
  pose proof (RG 19%bv 19%nat eq_refl ltac:(lia)) as R19. pose proof (RG 21%bv 21%nat eq_refl ltac:(lia)) as R21.
  pose proof (RG 22%bv 22%nat eq_refl ltac:(lia)) as R22. clear RG.
  assert (R20 : YK11.getr (ms_regs ms5) 20%bv = Z_to_bv 64 (fe_F cx + 32)).
  { rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E5 _ ms5 20%bv HS3).
    change (sr_get (ss_regs _) 20%bv) with (SOff 24 32). apply bv_eq. rewrite denot_SOff, Eo, B24 by lia.
    rewrite wz by lia. apply zcanon_id. unfold M64. lia. }
  assert (HM5 : fe_mem_ok cx (mrestrict (w_H W3) (ms_mem ms5))).
  { destruct HM1 as (_ & Hfl1 & Hln1). split; [|split].
    - apply (fe_sv_of_region cx E5); [intros j Hj; rewrite Eo by lia; apply HE; lia | rewrite Eo by lia; exact B8 |].
      exact (fsw_region_nth E5 _ (restrict (w_H W3) ms5) 1 _ HS3 eq_refl).
    - intros kk Hkk. rewrite (mbyte_frame E46 rs5 (ms_mem ms) (ms_mem ms5) (w_H W3) _ HF); [exact (Hfl1 kk Hkk) | lia |].
      apply NW5; lia.
    - intros kk Hkk. rewrite (mbyte_frame E46 rs5 (ms_mem ms) (ms_mem ms5) (w_H W3) _ HF); [exact (Hln1 kk Hkk) | lia |].
      apply NW5; lia. }
  apply (HC5 cx (Ereg (ms_regs ms5) (fe_extra cx ++ [])) k ly3 S3 [] W3 ms5 md5 Hb (fe_E_Ereg cx _ _) HJ HARU).
  + assert (EW : forall (r : bv 5) j, Z.of_nat j = bv_unsigned r ->
      ew (Ereg (ms_regs ms5) (fe_extra cx ++ [])) j = YK11.getr (ms_regs ms5) r) by (intros r j Hj; apply ew_Ereg_nat; exact Hj).
    exists text. split; [reflexivity|].
    split; [rewrite Hbl; apply Permutation_app_comm|].
    split.
    { split; [lia|]. split; [exact (fe_same_io cx _ _ _ _ _ _ HJ5)|]. split; [|exact Hbb].
      apply (fe_payload cx _ _ _ _ _ _ Hb HJ5). intros b' Hb'. rewrite Hbl. apply in_or_app. left. exact Hb'. }
    split.
    { unfold fe_regs_core. rewrite (EW 8%bv 8%nat eq_refl), (EW 9%bv 9%nat eq_refl), (EW 2%bv 2%nat eq_refl), (EW 18%bv 18%nat eq_refl),
        (EW 24%bv 24%nat eq_refl), (EW 25%bv 25%nat eq_refl), (EW 3%bv 3%nat eq_refl), (EW 4%bv 4%nat eq_refl),
        (EW 26%bv 26%nat eq_refl), (EW 27%bv 27%nat eq_refl).
      rewrite R8, R9, R2, R18, R24, R25, R3, R4, R26, R27. exact Hcore. }
    split; [exact Hn3|].
    split; [rewrite (EW 19%bv 19%nat eq_refl), R19; exact E19|].
    split; [rewrite (EW 20%bv 20%nat eq_refl), R20; reflexivity|].
    split; [rewrite (EW 21%bv 21%nat eq_refl), R21; exact E21|].
    split; [rewrite (EW 22%bv 22%nat eq_refl), R22; exact E22|].
    split.
    { apply (fe_cstr_new ly3 S3 W3 (ms_mem ms5) md5 text (fe_tb cx) (proj1 HJ5)).
      - rewrite Htl. exact Hin.
      - rewrite Htl. lia.
      - rewrite Htl. lia.
      - intros j Hj. rewrite length_app in Hj. cbn [length] in Hj.
        destruct (Nat.lt_ge_cases j (length (fe_tb cx))) as [Hj1|Hj1].
        + rewrite app_nth1 by exact Hj1. rewrite fe_tb_nth by exact Hj1.
          split; [|apply fe_bytes_byte]. apply val_mem1_of_aview.
          rewrite (aview_frame E46 rs5 (ms_mem ms) (ms_mem ms5) (w_H W3) _ HF); [| lia | apply NW5; lia].
          rewrite (Htxt1 (Z.of_nat j)) by lia. rewrite Nat2Z.id. reflexivity.
        + assert (Ej : j = length (fe_tb cx)) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag.
          cbn [nth]. split; [|lia]. rewrite Htl.
          pose proof (fsw_region_nth E5 _ (restrict (w_H W3) ms5) 0
            (YP09.mkRegion (Some 46%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))]) HS3 eq_refl) as R46.
          replace (text + n) with (text + n + 0) by lia.
          apply (fsw_field E5 _ 46 (text + n) [YP09.mkChunk 0 (CVal 1 (SLit 0))] 0 1 0 1 0 1 (SLit 0) 0 R46 Ev46).
          * left. reflexivity.
          * apply denot_lit0.
          * lia.
          * lia.
      - exact (fe_tb_nz cx Hb). }
    split.
    { apply (fs_stat_kept W3 W3 (ms_mem ms) (ms_mem ms5)); [|exact Hst1]. intros a Ha.
      pose proof (pstat_bounds a Ha) as Hab.
      apply (mbyte_frame E46 rs5 _ _ _ a HF); [lia|]. apply NW5; [|lia].
      intros ->. apply (blk_img tfibsegs B LAWS _ _ _ _ _ text (n + 1) (text + n) HAR1 Hin); [rewrite Hrq; lia|].
      exact (fs_rw3_img _ Hab). }
    (* `len`'s shadow byte: outside the token run's two write windows (a shadow byte, neither text[n] nor the stack) *)
    unfold fe_lensh.
    assert (SL : fe_SF cx + 4 <> text + n /\ ~ (fe_sp0 cx - 88 <= fe_SF cx + 4 < fe_sp0 cx) /\ 0 <= fe_SF cx + 4 < 2 ^ 64)
      by (unfold kLowShadowBeg, kHighMemBeg, kLowMemEnd, ASAN_CEIL in *; lia).
    rewrite (aview_frame E46 rs5 (ms_mem ms) (ms_mem ms5) (w_H W3) _ HF); [exact Hlsh1 | lia | apply NW5; lia].
  + apply (fe_rebuild cx ly3 S3 W3 ms5 md5 k [] PC_C5 Hb HJ5 Ems5 (eq_trans R8 C8) (eq_trans R24 C24) (eq_trans R18 C18)
    (eq_trans R25 C25) HM5).
Qed.

(* ---- the boundary A at 0x810c4 (RA_malloc): malloc returned the text block in a0, `len`'s shadow byte is 0
   (fe_lensh); the state is fe_ss RA_malloc [fe_len_lit (-1)] ---- *)
Definition INV_A5 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text,
    U3 = [] /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) ++ [(text, fe_n cx + 1)] /\
    fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1) /\ fe_regs_core cx E /\
    fe_n cx <= 3 * 2 ^ 20 /\ ew E 19 = Z_to_bv 64 (fe_n cx) /\ ew E 20 = Z_to_bv 64 (c_p cx) /\
    ew E 22 = Z_to_bv 64 SHADOW_OFF /\ ew E 10 = Z_to_bv 64 text /\
    fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx + 3) /\ fe_lensh cx W3 (ms_mem ms3).

Lemma fe_s5_mid : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss PC_M5 [fe_len_lit (-1)]) INV_M5 ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_malloc [fe_len_lit (-1)]) INV_A5.
Proof.
intros POST HM cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (text & -> & Hbl & (Hk & Hio & Hpay & Hbb) & Hcore & Hn3 & E19 & E20 & E22 & E10 & Hst & Hlsh).
pose proof Hcore as (C8 & C9 & C2 & C18 & C24 & C25 & C3 & C4 & C26 & C27).
destruct (fe_sp_facts cx Hb) as (Sp16 & Spc & Sp47 & Sp1 & Sp132). unfold LLVMF_STK in Spc.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (fe_n_bounds cx Hb) as Hnb.
set (n := fe_n cx) in *.
assert (HJ0 : fe_J cx ly3 S3 W3 (ms_mem ms3) md3 k) by (unfold fe_J; rewrite <- (unpoison_nil (ms_mem ms3)); exact HJ).
destruct (fe_jf cx _ _ _ _ _ _ Hb HJ0) as (HAR & Hfin & ELY & EF & EFL & Etop & F32 & F4096 & Fceil & Fapp & HFL).
pose proof (fe_SF_bounds cx F4096 Fceil) as SFb.
assert (Hin : In (text, n + 1) (ablocks B ly3 S3)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (n + 1) = n + 1) by (unfold req_size; destruct (Z.eqb_spec (n + 1) 0); lia).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (T16 & T4096 & Tceil & Tapp & _ & _ & Tn).
rewrite Hrq in Tceil, Tapp. unfold in_app in Tapp.
pose proof (FSW_entry_ar.fe_block_room B _ _ _ _ _ _ _ HAR Hin) as Troom. rewrite Hrq in Troom.
pose proof (fe_fresh _ _ _ _ _ _ _ _ HAR Hbl) as Tfresh.
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin Hfin) as Tsep.
rewrite Hrq, EF in Tsep. unfold zdisjoint in Tsep. cbn [fst snd] in Tsep. change (fs_frame_bytes 0) with 64 in Tsep.
assert (Hsb : forall b', In b' (ablocks B (c_ly cx) (c_S cx)) -> In b' (ablocks B ly3 S3))
  by (intros b' Hb'; rewrite Hbl; apply in_or_app; left; exact Hb').
assert (B8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite C8; apply wz; lia).
assert (B24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite C24; apply wz; lia).
assert (B25 : bv_unsigned (ew E 25) = fe_SF cx) by (rewrite C25; apply wz; unfold kHighMemBeg in SFb; lia).
(* `len`'s shadow byte as a chunk (fe_ss_z) for the runs below *)
pose proof (fe_ss_z_ok cx E RA_malloc [fe_len_lit (-1)] (w_H W3) ms3 HS B25 Hlsh) as HSz.
clear HS. rename HSz into HS.
pose proof (st_ok_add_fact tfibsegs E _ _ 10%nat (mkAF 4096 (2 ^ 47) 4) HS) as HS1.
specialize (HS1 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E10, wz by lia; change (2 ^ 4) with 16; lia)).
clear HS.
destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
- (* n = 0: `beqz s3` (0x810cc) jumps to 0x810e0 *)
  pose proof (st_ok_set_reg tfibsegs E _ _ 19%bv (SLit 0) HS1) as HS2.
  specialize (HS2 ltac:(intros Heq; apply (f_equal bv_unsigned) in Heq; vm_compute in Heq; discriminate Heq)).
  specialize (HS2 ltac:(change (YK11.getr (ms_regs (restrict (w_H W3) ms3)) 19%bv) with (YK11.getr (ms_regs ms3) 19%bv);
    rewrite (reg_at (w_H W3) E _ ms3 19%bv 19 HS1 eq_refl), denot_lit0, E19, Hn0; reflexivity)).
  clear HS1.
  fsw_aj_run_toU entry_tbl_ok HS2 HJ HARU PC_M5.
  { cbn [ss_mem add_atom fe_ss_z]. apply fe_awr_z. rewrite <- (app_nil_r (fe_regions _)).
    apply (fe_awr cx E ly3 S3 W3 _ md3 k _ _ [] _ Hb HJ0 B8 B24 B25). apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ => set (md5 := d) in * end.
  lazymatch type of HF with frame_of ?Ef _ ?m1 ?m2 => change (frame_of Ef (fe_regions_z [fe_len_lit (-1)]) m1 m2) in HF end.
  apply fe_frame_z in HF.
  pose proof (fe_lensh_of cx E _ (w_H W3) ms HS2 eq_refl B25) as Hlsh5.
  clear HFr HG.
  assert (HJ5 : fe_J cx ly3 S3 W3 (ms_mem ms) md5 k) by (unfold fe_J; rewrite <- (unpoison_nil (ms_mem ms)); exact HJ).
  assert (Ems : ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_M5) (ms_mem ms) (YK11.seg_rom tfibsegs))
    by exact (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS2 eq_refl).
  assert (EW : forall (r : bv 5) j, Z.of_nat j = bv_unsigned r ->
    ew (Ereg (ms_regs ms) (fe_extra cx ++ [])) j = YK11.getr (ms_regs ms) r) by (intros r j Hj; apply ew_Ereg_nat; exact Hj).
  pose proof (reg_at (w_H W3) E _ ms 8%bv 8 HS2 eq_refl) as R8. pose proof (reg_at (w_H W3) E _ ms 9%bv 9 HS2 eq_refl) as R9.
  pose proof (reg_at (w_H W3) E _ ms 2%bv 2 HS2 eq_refl) as R2. pose proof (reg_at (w_H W3) E _ ms 18%bv 18 HS2 eq_refl) as R18.
  pose proof (reg_at (w_H W3) E _ ms 24%bv 24 HS2 eq_refl) as R24. pose proof (reg_at (w_H W3) E _ ms 25%bv 25 HS2 eq_refl) as R25.
  pose proof (reg_at (w_H W3) E _ ms 3%bv 3 HS2 eq_refl) as R3. pose proof (reg_at (w_H W3) E _ ms 4%bv 4 HS2 eq_refl) as R4.
  pose proof (reg_at (w_H W3) E _ ms 26%bv 26 HS2 eq_refl) as R26. pose proof (reg_at (w_H W3) E _ ms 27%bv 27 HS2 eq_refl) as R27.
  pose proof (reg_at (w_H W3) E _ ms 21%bv 10 HS2 eq_refl) as R21. pose proof (reg_at (w_H W3) E _ ms 22%bv 22 HS2 eq_refl) as R22.
  pose proof (fsw_reg_lit (w_H W3) E _ ms 19%bv 0 HS2 eq_refl ltac:(lia)) as R19.
  apply (HM cx (Ereg (ms_regs ms) (fe_extra cx ++ [])) k ly3 S3 [] W3 ms md5 Hb (fe_E_Ereg cx _ _) HJ HARU).
  + exists text. split; [reflexivity|]. split; [exact Hbl|].
    split.
    { split; [lia|]. split; [exact (fe_same_io cx _ _ _ _ _ _ HJ5)|]. split; [|exact Hbb].
      exact (fe_payload cx _ _ _ _ _ _ Hb HJ5 Hsb). }
    split.
    { unfold fe_regs_core. rewrite (EW 8%bv 8%nat eq_refl), (EW 9%bv 9%nat eq_refl), (EW 2%bv 2%nat eq_refl),
        (EW 18%bv 18%nat eq_refl), (EW 24%bv 24%nat eq_refl), (EW 25%bv 25%nat eq_refl), (EW 3%bv 3%nat eq_refl),
        (EW 4%bv 4%nat eq_refl), (EW 26%bv 26%nat eq_refl), (EW 27%bv 27%nat eq_refl).
      rewrite R8, R9, R2, R18, R24, R25, R3, R4, R26, R27. exact Hcore. }
    split; [exact Hn3|].
    split; [rewrite (EW 19%bv 19%nat eq_refl), R19; fold n; rewrite Hn0; reflexivity|].
    split; [rewrite (EW 21%bv 21%nat eq_refl), R21; exact E10|].
    split; [rewrite (EW 22%bv 22%nat eq_refl), R22; exact E22|].
    split; [intros i Hi; fold n in Hi; lia|].
    split.
    { apply (fs_stat_kept W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hst]. intros a Ha.
      apply (mbyte_frame E _ _ _ _ a HF); [pose proof (pstat_bounds a Ha); lia|].
      exact (fe_pstat_nw cx E ly3 S3 W3 _ md3 k _ a Hb HJ0 B8 B24 B25 Ha). }
    exact Hlsh5.
  + apply (fe_rebuild cx ly3 S3 W3 ms md5 k [] PC_M5 Hb HJ5 Ems (eq_trans R8 C8) (eq_trans R24 C24) (eq_trans R18 C18)
      (eq_trans R25 C25)).
    apply (fe_mem_of_regions cx E); [exact HE | exact B8 | exact B24 | lia | |].
    * exact (fsw_region_nth E _ (restrict (w_H W3) ms) 0 _ HS2 eq_refl).
    * exact (fsw_region_nth E _ (restrict (w_H W3) ms) 2 _ HS2 eq_refl).
- (* n > 0: memcpy(text, data, n) *)
  pose proof Hb as ((HPRE0 & _ & _ & _ & Hpn & _) & _). pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & _).
  destruct Hpn as [(Hcn0 & _) | (Hcn & Hpin)]; [lia|].
  assert (Hpin3 : In (c_p cx, c_n cx) (ablocks B ly3 S3)) by exact (Hsb _ Hpin).
  assert (Hrqp : req_size (c_n cx) = c_n cx) by (unfold req_size; destruct (Z.eqb_spec (c_n cx) 0); lia).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hpin3) as (_ & P4096 & Pceil & Papp & _).
  rewrite Hrqp in Pceil, Papp. unfold in_app in Papp.
  assert (Hdj : text + n <= c_p cx \/ c_p cx + n <= text).
  { apply in_split in Hpin as (l1 & l2 & El).
    pose proof (sep_blocks_pos tfibsegs B LAWS _ _ _ _ _ (c_p cx, c_n cx) (text, n + 1) l1 l2 [] HAR
      ltac:(rewrite Hbl, El, <- app_assoc; reflexivity)) as D.
    unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Hrqp, Hrq in D. lia. }
  pose proof (st_ok_add_fact tfibsegs E _ _ 19%nat (mkAF 1 (3 * 2 ^ 20) 0) HS1) as HS2.
  specialize (HS2 ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite E19, wz by lia; change (2 ^ 0) with 1;
    rewrite Z.mod_1_r; lia)).
  clear HS1.
  fsw_aj_runU entry_tbl_ok HS2 HJ HARU.
  { cbn [ss_mem add_atom fe_ss_z]. apply fe_awr_z. rewrite <- (app_nil_r (fe_regions _)).
    apply (fe_awr cx E ly3 S3 W3 _ md3 k _ _ [] _ Hb HJ0 B8 B24 B25). apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ => set (md4 := d) in * end.
  lazymatch type of HF with frame_of ?Ef _ ?m1 ?m2 => change (frame_of Ef (fe_regions_z [fe_len_lit (-1)]) m1 m2) in HF end.
  apply fe_frame_z in HF.
  pose proof (fe_lensh_of cx E _ (w_H W3) ms HS2 eq_refl B25) as HlshT.
  clear HFr HG.
  assert (HJ4 : fe_J cx ly3 S3 W3 (ms_mem ms) md4 k) by (unfold fe_J; rewrite <- (unpoison_nil (ms_mem ms)); exact HJ).
  pose proof (proj1 HJ4) as HAR4.
  pose proof (reg_at (w_H W3) E _ ms 10%bv 10 HS2 eq_refl) as R10. pose proof (reg_at (w_H W3) E _ ms 11%bv 20 HS2 eq_refl) as R11.
  pose proof (reg_at (w_H W3) E _ ms 12%bv 19 HS2 eq_refl) as R12.
  pose proof (fsw_reg_lit (w_H W3) E _ ms 1%bv 0x810e0 HS2 eq_refl ltac:(lia)) as R1.
  pose proof (reg_at (w_H W3) E _ ms 8%bv 8 HS2 eq_refl) as R8. pose proof (reg_at (w_H W3) E _ ms 9%bv 9 HS2 eq_refl) as R9.
  pose proof (reg_at (w_H W3) E _ ms 2%bv 2 HS2 eq_refl) as R2. pose proof (reg_at (w_H W3) E _ ms 18%bv 18 HS2 eq_refl) as R18.
  pose proof (reg_at (w_H W3) E _ ms 24%bv 24 HS2 eq_refl) as R24. pose proof (reg_at (w_H W3) E _ ms 25%bv 25 HS2 eq_refl) as R25.
  pose proof (reg_at (w_H W3) E _ ms 3%bv 3 HS2 eq_refl) as R3. pose proof (reg_at (w_H W3) E _ ms 4%bv 4 HS2 eq_refl) as R4.
  pose proof (reg_at (w_H W3) E _ ms 26%bv 26 HS2 eq_refl) as R26. pose proof (reg_at (w_H W3) E _ ms 27%bv 27 HS2 eq_refl) as R27.
  pose proof (reg_at (w_H W3) E _ ms 19%bv 19 HS2 eq_refl) as R19. pose proof (reg_at (w_H W3) E _ ms 21%bv 10 HS2 eq_refl) as R21.
  pose proof (reg_at (w_H W3) E _ ms 22%bv 22 HS2 eq_refl) as R22.
  assert (Ems : ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_memcpy) (ms_mem ms) (YK11.seg_rom tfibsegs))
    by exact (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS2 eq_refl).
  assert (HM4 : fe_mem_ok cx (mrestrict (w_H W3) (ms_mem ms))).
  { apply (fe_mem_of_regions cx E); [exact HE | exact B8 | exact B24 | lia | |].
    - exact (fsw_region_nth E _ (restrict (w_H W3) ms) 0 _ HS2 eq_refl).
    - exact (fsw_region_nth E _ (restrict (w_H W3) ms) 2 _ HS2 eq_refl). }
  assert (Hst4 : fs_stat tfibsegs W3 (ms_mem ms) (c_live cx) (c_cnt cx + 3)).
  { apply (fs_stat_kept W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hst]. intros a Ha.
    apply (mbyte_frame E _ _ _ _ a HF); [pose proof (pstat_bounds a Ha); lia|].
    exact (fe_pstat_nw cx E ly3 S3 W3 _ md3 k _ a Hb HJ0 B8 B24 B25 Ha). }
  assert (Hpl4 : forall i, 0 <= i < n ->
    aview tfibsegs (w_H W3) (ms_mem ms) (c_p cx + i) = Some (nth (Z.to_nat i) (fe_bytes cx) 0)).
  { intros i Hi. rewrite (aview_frame E _ (ms_mem ms3) (ms_mem ms) (w_H W3) _ HF); [| lia |].
    - rewrite (Hpay i) by lia. apply fe_pl_byte; [exact Hb | lia].
    - apply (fe_blk_nw cx E ly3 S3 W3 _ md3 k _ (c_p cx) (c_n cx) _ Hb HJ0 B8 B24 B25 Hpin3). rewrite Hrqp. lia. }
  clear HF HS2.
  rewrite Ems. set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
  assert (Rsp : spZ regsT = fe_sp1 cx) by (unfold spZ; rewrite R2, C2; apply wz; lia).
  set (Wr := fun a => text <= a < text + n \/ fe_sp1 cx - ESTACK <= a < fe_sp1 cx).
  set (Q := fun (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) =>
    aregs_preserved regsT regs' /\
    (forall i, 0 <= i < n -> aview tfibsegs (w_H W3) mem' (text + i) = aview tfibsegs (w_H W3) memT (c_p cx + i)) /\
    (forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W3) mem' a = aview tfibsegs (w_H W3) memT a)).
  assert (HPRE : ecall_preU tfibsegs B ly3 S3 [] W3 regsT memT md4).
  { apply (fsw_ecall_preU_at B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(0, c_fpos cx)] ly3 S3 [] W3 memT md4 k regsT (fe_sp1 cx - fe_sp0 cx) HJ HARU).
    - rewrite Rsp. lia.
    - lia.
    - lia.
    - unfold ESTACK, LLVMF_STK. lia.
    - rewrite R1. vm_compute. reflexivity.
    - rewrite R3, C3. exact Hgp.
    - rewrite R4, C4. exact Htp. }
  assert (HD : dest_ok tfibsegs B ly3 S3 W3 regsT memT text n).
  { pose proof (fsw_dest_okU B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(0, c_fpos cx)] ly3 S3 [] W3 memT md4 k regsT text n HJ HARU) as H.
    rewrite unpoison_nil in H. apply H. intros a Ha. split.
    - right. right. left. exists text, (n + 1). split; [exact Hin|]. split; [exact Tfresh|]. rewrite Hrq. lia.
    - rewrite Rsp. unfold ESTACK. lia. }
  destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR4 Hin) as (Tbs & _). rewrite Hrq in Tbs.
  destruct (al_shadow _ _ LAWS _ _ _ _ _ _ _ HAR4 Hpin3) as (Pbs & _). rewrite Hrqp in Pbs.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR4 Hpin3) as (_ & _ & _ & _ & Ppres & _). rewrite Hrqp in Ppres.
  assert (MC : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy)
    by (replace PC_memcpy with (pc_asan_memcpy (as_code B)) by (rewrite tl_code; reflexivity); exact fe_mc).
  pose proof (MC ly3 S3 [] W3 regsT memT md4 text (c_p cx) n HPRE) as HMC.
  specialize (HMC ltac:(rewrite R10, E10; reflexivity) ltac:(rewrite R11, E20; reflexivity)
    ltac:(rewrite R12, E19; reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) HD).
  specialize (HMC ltac:(unfold amem_range; unfold kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia)).
  specialize (HMC (block_shadow_range _ _ text (n + 1) text n Tbs ltac:(lia) ltac:(lia))).
  specialize (HMC (fun Hp => shadow_hull_vis_of_block tfibsegs B LAWS _ _ _ _ _ text (n + 1) text n HAR4 Hin
    ltac:(lia) ltac:(rewrite Hrq; lia) Hp)).
  specialize (HMC ltac:(split; [lia|]; split; [lia|]; split;
    [intros a Ha; split; [apply (aview_some_of_apresent tfibsegs); exact (proj1 (Ppres a ltac:(lia)))
                         | rewrite Rsp; unfold ESTACK; lia]|];
    split; [lia|]; split; [unfold amem_range; unfold kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *; lia|];
    split; [exact (block_shadow_range _ _ (c_p cx) (c_n cx) (c_p cx) n Pbs ltac:(lia) ltac:(lia))|];
    intros Hp; exact (shadow_hull_vis_of_block tfibsegs B LAWS _ _ _ _ _ (c_p cx) (c_n cx) (c_p cx) n HAR4 Hpin3
      ltac:(lia) ltac:(rewrite Hrqp; lia) Hp))).
  eapply SRr_bind.
  { apply (fsw_intrin_atU B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
      [(0, c_fpos cx)] ly3 S3 [] W3 memT md4 k [] Wr (Z_to_bv 64 0x810e0) _ Q HJ).
    - eapply SRr_mono; [exact HMC|]. cbv beta.
      intros W' c' _ (-> & regs' & mem' & md' & Ec & HARU' & HP & Hsm & H10 & Hcp & Hun & Hpr).
      split; [reflexivity|]. exists regs', mem', md'.
      split; [rewrite Ec; unfold cfg_at, raZ, w64; rewrite R1, wz by lia; reflexivity|].
      split; [exact HARU'|]. split; [exact Hsm|].
      assert (HU : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview tfibsegs (w_H W3) mem' a = aview tfibsegs (w_H W3) memT a).
      { intros a Ha HnW. apply Hun; [exact Ha | intros Hd; apply HnW; left; exact Hd |].
        rewrite Rsp. intros Hs; apply HnW; right; exact Hs. }
      split; [intros a Ha HnW; rewrite !unpoison_nil; exact (HU a Ha HnW)|].
      split; [intros a; rewrite !unpoison_nil; apply Hpr|].
      split; [exact HP|]. split; [intros i Hi; exact (Hcp i Hi) | exact HU].
    - intros a [Ha|Ha].
      + left. right. right. left. exists text, (n + 1). split; [exact Hin|]. split; [exact Tfresh|]. rewrite Hrq. lia.
      + left. left. unfold ESTACK in Ha. unfold LLVMF_STK. lia. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HARU2 & (HP2 & Hcp2 & Hun2)).
  assert (HJ5 : fe_J cx ly3 S3 W3 mem2 md2 k) by (unfold fe_J; rewrite <- (unpoison_nil mem2); exact HJ2).
  assert (P : forall (r : bv 5), acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regsT r)
    by (intros r Hr; exact (fsw_pres regsT regs2 r HP2 Hr)).
  assert (EW : forall (r : bv 5) j, Z.of_nat j = bv_unsigned r ->
    ew (Ereg regs2 (fe_extra cx ++ [])) j = YK11.getr regs2 r) by (intros r j Hj; apply ew_Ereg_nat; exact Hj).
  assert (NWr : forall a, (fe_sp0 cx - 88 <= a < fe_sp0 cx \/ fe_F cx <= a < fe_F cx + 64) -> ~ Wr a).
  { intros a Ha [Hw|Hw]; [|unfold ESTACK in Hw]; lia. }
  apply (HM cx (Ereg regs2 (fe_extra cx ++ [])) k ly3 S3 [] W3
    (YK11.mkst regs2 (Z_to_bv 64 PC_M5) mem2 (YK11.seg_rom tfibsegs)) md2 Hb (fe_E_Ereg cx _ _) HJ2 HARU2).
  + exists text. split; [reflexivity|]. split; [exact Hbl|].
    split.
    { split; [lia|]. split; [exact (fe_same_io cx _ _ _ _ _ _ HJ5)|]. split; [|exact Hbb].
      exact (fe_payload cx _ _ _ _ _ _ Hb HJ5 Hsb). }
    split.
    { unfold fe_regs_core. rewrite (EW 8%bv 8%nat eq_refl), (EW 9%bv 9%nat eq_refl), (EW 2%bv 2%nat eq_refl),
        (EW 18%bv 18%nat eq_refl), (EW 24%bv 24%nat eq_refl), (EW 25%bv 25%nat eq_refl), (EW 3%bv 3%nat eq_refl),
        (EW 4%bv 4%nat eq_refl), (EW 26%bv 26%nat eq_refl), (EW 27%bv 27%nat eq_refl).
      rewrite !P by fe_cs. rewrite R8, R9, R2, R18, R24, R25, R3, R4, R26, R27. exact Hcore. }
    split; [exact Hn3|].
    split; [rewrite (EW 19%bv 19%nat eq_refl), P, R19 by fe_cs; exact E19|].
    split; [rewrite (EW 21%bv 21%nat eq_refl), P, R21 by fe_cs; exact E10|].
    split; [rewrite (EW 22%bv 22%nat eq_refl), P, R22 by fe_cs; exact E22|].
    split; [intros i Hi; fold n in Hi; cbn [ms_mem YK11.mkst]; rewrite (Hcp2 i Hi); exact (Hpl4 i Hi)|].
    split.
    { apply (fs_stat_kept W3 W3 memT mem2); [|exact Hst4]. intros a Ha. pose proof (pstat_bounds a Ha) as Hab.
      apply (mbyte_of_aview tfibsegs). apply Hun2; [lia|]. intros [Hw|Hw]; [|unfold ESTACK in Hw; lia].
      apply (blk_img tfibsegs B LAWS _ _ _ _ _ text (n + 1) a HAR4 Hin); [rewrite Hrq; lia | exact (fs_rw3_img _ Hab)]. }
    (* `len`'s shadow byte: outside __asan_memcpy's write window Wr (a shadow byte, neither the text nor the stack) *)
    unfold fe_lensh. cbn [ms_mem YK11.mkst].
    assert (SL : ~ Wr (fe_SF cx + 4) /\ 0 <= fe_SF cx + 4 < 2 ^ 64)
      by (unfold Wr; unfold ESTACK, kLowShadowBeg, kHighMemBeg, kLowMemEnd, ASAN_CEIL in *; lia).
    rewrite Hun2; [exact HlshT | exact (proj2 SL) | exact (proj1 SL)].
  + apply (fe_rebuild cx ly3 S3 W3 (YK11.mkst regs2 (Z_to_bv 64 PC_M5) mem2 (YK11.seg_rom tfibsegs)) md2 k [] PC_M5
      Hb HJ5 eq_refl).
    * cbn [ms_regs YK11.mkst]. rewrite P, R8 by fe_cs. exact C8.
    * cbn [ms_regs YK11.mkst]. rewrite P, R24 by fe_cs. exact C24.
    * cbn [ms_regs YK11.mkst]. rewrite P, R18 by fe_cs. exact C18.
    * cbn [ms_regs YK11.mkst]. rewrite P, R25 by fe_cs. exact C25.
    * apply (fe_mem_kept cx (mrestrict (w_H W3) memT)); [exact HM4|]. intros a Ha.
      apply (mbyte_of_aview tfibsegs). apply Hun2; [|exact (NWr a Ha)].
      destruct Ha; unfold kHighMemEnd in *; lia.
Qed.

(* ---- from C2 (0x810bc) to A (0x810c4): `addi a0, s3, 1; jal __wrap_malloc` (0x810c0), the malloc ---- *)
Lemma fe_s5_malloc : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss RA_malloc [fe_len_lit (-1)]) INV_A5 ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_cno [fe_len_lit (-1)]) (INV_C2 B).
Proof.
intros POST HA cx E k ly3 S3 U3 W3 ms3 md3 Hb HE HJ HARU HINV HS.
destruct HINV as (-> & Hbl & (Hk & Hio & Hpay & Hbb) & Hcore & Hn3 & E19 & E20 & E22 & Hst & Hlsh).
pose proof Hcore as (C8 & C9 & C2 & C18 & C24 & C25 & C3 & C4 & C26 & C27).
destruct (fe_sp_facts cx Hb) as (Sp16 & Spc & Sp47 & Sp1 & Sp132). unfold LLVMF_STK in Spc.
pose proof asan_consts as (AC1 & AC2 & AC3 & AC4 & AC5).
pose proof (fe_n_bounds cx Hb) as Hnb.
set (n := fe_n cx) in *.
assert (HJ0 : fe_J cx ly3 S3 W3 (ms_mem ms3) md3 k) by (unfold fe_J; rewrite <- (unpoison_nil (ms_mem ms3)); exact HJ).
destruct (fe_jf cx _ _ _ _ _ _ Hb HJ0) as (HAR & Hfin & ELY & EF & EFL & Etop & F32 & F4096 & Fceil & Fapp & HFL).
pose proof (fe_SF_bounds cx F4096 Fceil) as SFb.
assert (B8 : bv_unsigned (ew E 8) = fe_sp0 cx) by (rewrite C8; apply wz; lia).
assert (B24 : bv_unsigned (ew E 24) = fe_F cx) by (rewrite C24; apply wz; lia).
assert (B25 : bv_unsigned (ew E 25) = fe_SF cx) by (rewrite C25; apply wz; unfold kHighMemBeg in SFb; lia).
pose proof Hb as ((HPRE0 & Hra0 & _ & _ & _ & _ & _ & Hfr0 & Hnev0 & Hlive0 & _) & _).
pose proof HPRE0 as (_ & _ & _ & Hgp & Htp & Hstk0 & _ & Hach0 & _).
pose proof Hstk0 as (_ & _ & _ & _ & _ & H47 & _ & Htop0 & Htop1).
(* `len`'s shadow byte as a chunk (fe_ss_z) for the run to the call *)
pose proof (fe_ss_z_ok cx E RA_cno [fe_len_lit (-1)] (w_H W3) ms3 HS B25 Hlsh) as HSz.
clear HS. rename HSz into HS.
fsw_aj_runU entry_tbl_ok HS HJ HARU.
{ cbn [ss_mem fe_ss_z]. apply fe_awr_z. rewrite <- (app_nil_r (fe_regions _)).
  apply (fe_awr cx E ly3 S3 W3 _ md3 k _ _ [] _ Hb HJ0 B8 B24 B25). apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := ?m; cfg_model := ?d |} _ => set (md4 := d) in * end.
lazymatch type of HF with frame_of ?Ef _ ?m1 ?m2 => change (frame_of Ef (fe_regions_z [fe_len_lit (-1)]) m1 m2) in HF end.
apply fe_frame_z in HF.
pose proof (fe_lensh_of cx E _ (w_H W3) ms HS eq_refl B25) as HlshT.
clear HFr HG.
assert (HJ4 : fe_J cx ly3 S3 W3 (ms_mem ms) md4 k) by (unfold fe_J; rewrite <- (unpoison_nil (ms_mem ms)); exact HJ).
pose proof HJ4 as (HAR4 & _ & _ & _ & _ & _ & Hnev4 & _ & Fk4 & _).
assert (R10 : YK11.getr (ms_regs ms) 10%bv = Z_to_bv 64 (n + 1)).
{ rewrite (st_ok_restrict_reg tfibsegs (w_H W3) E _ ms 10%bv HS). change (sr_get (ss_regs _) 10%bv) with (SOff 19 1).
  apply bv_eq. rewrite denot_SOff, E19, !wz by lia. apply zcanon_id. unfold M64. lia. }
pose proof (fsw_reg_lit (w_H W3) E _ ms 1%bv 0x810c4 HS eq_refl ltac:(lia)) as R1.
pose proof (reg_at (w_H W3) E _ ms 8%bv 8 HS eq_refl) as R8. pose proof (reg_at (w_H W3) E _ ms 9%bv 9 HS eq_refl) as R9.
pose proof (reg_at (w_H W3) E _ ms 2%bv 2 HS eq_refl) as R2. pose proof (reg_at (w_H W3) E _ ms 18%bv 18 HS eq_refl) as R18.
pose proof (reg_at (w_H W3) E _ ms 24%bv 24 HS eq_refl) as R24. pose proof (reg_at (w_H W3) E _ ms 25%bv 25 HS eq_refl) as R25.
pose proof (reg_at (w_H W3) E _ ms 3%bv 3 HS eq_refl) as R3. pose proof (reg_at (w_H W3) E _ ms 4%bv 4 HS eq_refl) as R4.
pose proof (reg_at (w_H W3) E _ ms 26%bv 26 HS eq_refl) as R26. pose proof (reg_at (w_H W3) E _ ms 27%bv 27 HS eq_refl) as R27.
pose proof (reg_at (w_H W3) E _ ms 19%bv 19 HS eq_refl) as R19. pose proof (reg_at (w_H W3) E _ ms 20%bv 20 HS eq_refl) as R20.
pose proof (reg_at (w_H W3) E _ ms 22%bv 22 HS eq_refl) as R22.
assert (Ems : ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 PC_malloc) (ms_mem ms) (YK11.seg_rom tfibsegs))
  by exact (st_ok_restrict_mkst tfibsegs (w_H W3) E _ ms HS eq_refl).
assert (HM4 : fe_mem_ok cx (mrestrict (w_H W3) (ms_mem ms))).
{ apply (fe_mem_of_regions cx E); [exact HE | exact B8 | exact B24 | lia | |].
  - exact (fsw_region_nth E _ (restrict (w_H W3) ms) 0 _ HS eq_refl).
  - exact (fsw_region_nth E _ (restrict (w_H W3) ms) 2 _ HS eq_refl). }
assert (Hst4 : fs_stat tfibsegs W3 (ms_mem ms) (c_live cx) (c_cnt cx + 3)).
{ apply (fs_stat_kept W3 W3 (ms_mem ms3) (ms_mem ms)); [|exact Hst]. intros a Ha.
  apply (mbyte_frame E _ _ _ _ a HF); [pose proof (pstat_bounds a Ha); lia|].
  exact (fe_pstat_nw cx E ly3 S3 W3 _ md3 k _ a Hb HJ0 B8 B24 B25 Ha). }
clear HF HS.
assert (EPCm : pc_wrap_malloc (as_code B) = PC_malloc) by (rewrite tl_code; reflexivity).
rewrite Ems. rewrite <- EPCm.
set (regsT := ms_regs ms) in *. set (memT := ms_mem ms) in *.
assert (Rsp : spZ regsT = fe_sp1 cx) by (unfold spZ; rewrite R2, C2; apply wz; lia).
assert (Rs0 : s0Z regsT = fe_sp0 cx) by (unfold s0Z; rewrite R8, C8; apply wz; lia).
assert (Rra : raZ regsT = RA_malloc) by (unfold raZ; rewrite R1; apply wz; unfold RA_malloc; lia).
pose proof (amalloc04_rule_triv tfibsegs B fs_segs_low errno_low LAWS ML
  (amalloc_realizes_of_U tfibsegs B fe_ma)) as AM4.
(* the call chain: s0 = the entry sp, whose record holds the entry's ra and s0 *)
assert (HCH : exists ch, chain_pre ly3 (aview tfibsegs (w_H W3) memT) regsT ch).
{ destruct (Z_lt_le_dec (fe_sp0 cx) (ly_top (c_ly cx) - 16)) as [Htop | Htop].
  - exists [(fe_sp0 cx, RA_LLVMF, s0Z (c_regs cx))].
    apply (achain_chain_pre ly3 _ (fe_sp1 cx) (fe_sp0 cx)); [| rewrite Rsp; lia | exact Rs0 | rewrite Rra; unfold RA_malloc; lia].
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ Etop).
    destruct HM4 as (Hsv & _).
    apply (achain_push (c_ly cx) (aview tfibsegs (w_H (c_W cx)) (c_mem cx)) _ (fe_sp0 cx) (s0Z (c_regs cx)) RA_LLVMF []
      (fe_sp1 cx) Hach0).
    * lia.
    * intros a Ha. apply Fk4; [lia | lia].
    * assert (V0 : fe_sv_val cx 0 = RA_LLVMF) by exact Hra0.
      pose proof (Hsv 0%nat ltac:(lia)) as H0. rewrite V0 in H0.
      replace (fe_sp0 cx - 8 * (Z.of_nat 0 + 1)) with (fe_sp0 cx - 8) in H0 by lia.
      apply YCem.rdword_of_val_mem; [exact H0 | unfold RA_LLVMF; lia].
    * replace (s0Z (c_regs cx)) with (fe_sv_val cx 1) by reflexivity.
      pose proof (Hsv 1%nat ltac:(lia)) as H1.
      replace (fe_sp0 cx - 8 * (Z.of_nat 1 + 1)) with (fe_sp0 cx - 16) in H1 by lia.
      apply YCem.rdword_of_val_mem; [exact H1 |].
      unfold fe_sv_val. pose proof (u64_range (nth 2 (fe_extra cx) (Z_to_bv 64 0))) as Ru. unfold M64 in Ru. lia.
    * unfold RA_LLVMF. lia.
    * lia.
    * apply Z.mod_divide; [lia|]. apply Z.mod_divide in Sp16; [|lia]. destruct Sp16 as [q Hq]. exists (2 * q). lia.
    * exact Htop.
    * lia.
  - exists [].
    apply (achain_chain_pre ly3 _ (fe_sp1 cx) (fe_sp0 cx)); [| rewrite Rsp; lia | exact Rs0 | rewrite Rra; unfold RA_malloc; lia].
    left. split; [right; left; rewrite Etop; exact Htop | reflexivity]. }
destruct HCH as (ch & Hch).
assert (Hbb3 : blocks_bytes S3 = blocks_bytes (c_S cx))
  by (rewrite (blocks_bytes_bsum B ly3 S3), (blocks_bytes_bsum B (c_ly cx) (c_S cx)), Hbl; reflexivity).
eapply SRr_bind.
{ apply (amalloc04_sub tfibsegs B LAWS fs_segs_low ameter_triv AM4 W3 regsT memT LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(0, c_fpos cx)] ly3 S3 md4 k (n + 1) (fe_sp1 cx - fe_sp0 cx)
    (Z_to_bv 64 RA_malloc) ch HJ4 R10).
  - unfold MALLOC_MAX. lia.
  - rewrite Hbb3. unfold LIVE_LIB in Hlive0. lia.
  - rewrite Rsp. lia.
  - lia.
  - lia.
  - unfold ASTACK, LLVMF_STK. lia.
  - rewrite R3, C3. exact Hgp.
  - rewrite R4, C4. exact Htp.
  - exact R1.
  - vm_compute. reflexivity.
  - unfold EV_check_no_overread, EV_LIB in *. lia.
  - exact Hch.
  - exact I. }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & res & -> & HJ2 & HP2 & Ha02 & Hfrs2 & Hr4096 & Ebl & HK & _ & HJc).
assert (HJ5 : fe_J cx ly2 S2 W2 mem2 md2 (k + 1)) by exact HJ2.
assert (HJ5u : ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FS_PSTAT_FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
  [(0, c_fpos cx)] ly2 S2 W2 (unpoison [] mem2) md2 (k + 1)) by (rewrite unpoison_nil; exact HJ2).
destruct (fe_jf cx _ _ _ _ _ _ Hb HJ5) as (HAR2 & Hfin2 & _ & EF2 & _).
assert (Ebl2 : ablocks B ly2 S2 = ablocks B (c_ly cx) (c_S cx) ++ [(res, n + 1)]) by (rewrite Ebl, Hbl; reflexivity).
assert (Hin2 : In (res, n + 1) (ablocks B ly2 S2)) by (rewrite Ebl2; apply in_or_app; right; left; reflexivity).
assert (Hrq : req_size (n + 1) = n + 1) by (unfold req_size; destruct (Z.eqb_spec (n + 1) 0); lia).
pose proof (sep_block_frame tfibsegs B LAWS _ _ _ _ _ _ _ _ _ HAR2 Hin2 Hfin2) as Rsep.
rewrite Hrq, EF2 in Rsep. unfold zdisjoint in Rsep. cbn [fst snd] in Rsep. change (fs_frame_bytes 0) with 64 in Rsep.
destruct HK as (K1 & _ & K3 & K4 & _).
assert (P : forall (r : bv 5), acallee_saved (bv_unsigned r) -> YK11.getr regs2 r = YK11.getr regsT r)
  by (intros r Hr; exact (fsw_pres regsT regs2 r HP2 Hr)).
assert (EW : forall (r : bv 5) j, Z.of_nat j = bv_unsigned r ->
  ew (Ereg regs2 (fe_extra cx ++ [])) j = YK11.getr regs2 r) by (intros r j Hj; apply ew_Ereg_nat; exact Hj).
apply (HA cx (Ereg regs2 (fe_extra cx ++ [])) (k + 1) ly2 S2 [] W2
  (YK11.mkst regs2 (Z_to_bv 64 RA_malloc) mem2 (YK11.seg_rom tfibsegs)) md2 Hb (fe_E_Ereg cx _ _) HJ5u
  (proj2 (ARU_nil _ _ _ _ _ _ _) HAR2)).
- exists res. split; [reflexivity|]. split; [exact Ebl2|].
  split.
  { split; [unfold EV_check_no_overread in *; lia|]. split; [exact (fe_same_io cx _ _ _ _ _ _ HJ5)|]. split.
    - apply (fe_payload cx _ _ _ _ _ _ Hb HJ5). intros b' Hb'. rewrite Ebl2. apply in_or_app. left. exact Hb'.
    - rewrite (blocks_bytes_bsum B ly2 S2), Ebl2, bsum_app, <- (blocks_bytes_bsum B (c_ly cx) (c_S cx)). cbn. lia. }
  split.
  { unfold fe_regs_core. rewrite (EW 8%bv 8%nat eq_refl), (EW 9%bv 9%nat eq_refl), (EW 2%bv 2%nat eq_refl),
      (EW 18%bv 18%nat eq_refl), (EW 24%bv 24%nat eq_refl), (EW 25%bv 25%nat eq_refl), (EW 3%bv 3%nat eq_refl),
      (EW 4%bv 4%nat eq_refl), (EW 26%bv 26%nat eq_refl), (EW 27%bv 27%nat eq_refl).
    rewrite !P by fe_cs. rewrite R8, R9, R2, R18, R24, R25, R3, R4, R26, R27. exact Hcore. }
  split; [exact Hn3|].
  split; [rewrite (EW 19%bv 19%nat eq_refl), P, R19 by fe_cs; exact E19|].
  split; [rewrite (EW 20%bv 20%nat eq_refl), P, R20 by fe_cs; exact E20|].
  split; [rewrite (EW 22%bv 22%nat eq_refl), P, R22 by fe_cs; exact E22|].
  split; [rewrite (EW 10%bv 10%nat eq_refl), Ha02; reflexivity|].
  split.
  { apply (fs_stat_kept W3 W2 memT mem2); [|exact Hst4]. intros a Ha.
    apply (mbyte_of_aview tfibsegs). apply K3; [exact (fs_rw3_img _ (pstat_bounds a Ha)) | exact (proj1 (proj1 IMG a Ha))
      | exact (proj2 (proj1 IMG a Ha))]. }
  (* `len`'s shadow byte: the malloc's journal keeps the live frame's shadow (frames clause, empty footprint) *)
  unfold fe_lensh. cbn [ms_mem YK11.mkst].
  apply (fe_lensh_journal B cx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJc Hfin EF); [intros (r & [] & _) | exact HlshT].
- apply (fe_rebuild cx ly2 S2 W2 (YK11.mkst regs2 (Z_to_bv 64 RA_malloc) mem2 (YK11.seg_rom tfibsegs)) md2 (k + 1) []
    RA_malloc Hb HJ5 eq_refl).
  + cbn [ms_regs YK11.mkst]. rewrite P, R8 by fe_cs. exact C8.
  + cbn [ms_regs YK11.mkst]. rewrite P, R24 by fe_cs. exact C24.
  + cbn [ms_regs YK11.mkst]. rewrite P, R18 by fe_cs. exact C18.
  + cbn [ms_regs YK11.mkst]. rewrite P, R25 by fe_cs. exact C25.
  + apply (fe_mem_kept cx (mrestrict (w_H W3) memT)); [exact HM4|]. intros a [Ha|Ha]; apply (mbyte_of_aview tfibsegs).
    * apply K1; lia.
    * apply (K4 0 (c_fpos cx) a Hfin).
      -- left. unfold in_zr, frame_rng. cbn [fst snd]. rewrite EF. change (fs_frame_bytes 0) with 64. lia.
      -- rewrite Hrq. lia.
Qed.

Lemma fe_seg5 : forall POST,
  fe_from B FS_PSTAT_FP POST (fe_ss PC_C5 [fe_len_lit (-1)]) (INV_C5 B) ->
  fe_from B FS_PSTAT_FP POST (fe_ss RA_cno [fe_len_lit (-1)]) (INV_C2 B).
Proof. intros POST H. exact (fe_s5_malloc POST (fe_s5_mid POST (fe_s5_tail POST H))). Qed.
End s.
