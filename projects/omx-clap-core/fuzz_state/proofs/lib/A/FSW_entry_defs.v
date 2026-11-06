(* fs program part, lane ENTRY: the shared definitions of the walk of LLVMFuzzerTestOneInput (fs.asan 0x80f1c-0x811c4,
   171 instructions, fs.c:316-341) against FSH_Fn_entry.v fs_entry_goal. rule 24: no function proved here (fs's own
   harness entry, written in the donor cgif_file_fuzzer's form; `proof-index LLVMFuzzerTestOneInput` covers other
   units' harnesses only).
   Definitions only: the decode table, the walk context fecx (the entry's state plus the fake frame's position), the
   entry facts fe_base, the post fe_post, the segment form fe_from (one invariant per segment boundary), and the
   symbolic states and invariants at the segment boundaries. Each segment is proved in its own file
   FSW_entry_<seg>.v as `fe_from ... ss_next INV_next -> fe_from ... ss_this INV_this` (or, for the first segment, from
   the entry configuration); FSW_entry.v chains them.
   Port-from: donor cgif_file_fuzzer lib/A/ACf5.v:44-107 (rtcx, rt_base, rt_E, rt_from, rt_postP: the walk context, the
   segment form and the post), A/ACfj.v:230-257 (tfib_lib_x_body: srz_enter, then the segments), A/ACfi.v:103-141
   (closed under the callee contracts), A/AChf.v:140-163 (the fake frame's realign through s0). Walk kit: lib/A/FSW_K.v
   (a working branch), FSW_frame.v (a working branch), FSW_ret.v (a working branch).
   Atom convention (FSW_K.v:265-274): atom 2 = sp, atom 8 = s0; extra atoms from 32 under the env's extra list
   fe_extra: 32 = the shadow base, 33..43 = the eleven values the prologue saves (ra, s0, s1, s2 .. s9 of the entry, at
   s0 - 8 .. s0 - 88), 44 = the fake frame's flag address, 45 = the fake frame's shadow address. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q YC5d YCbp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSW_K FSW_ret FSW_frame3.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import ACfn FSH_Harness FSH_Fn_entry.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
FSH_Fn_alloc FSH_Fn_checks FSH_Fn_cno FSH_Fn_crt FSH_Fn_writer.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---- the code: 171 words from FS_LLVMF (0x80f1c .. 0x811c8). MEASURED on the pinned fs.asan (sha256 64b53ff8...,
   capstone 5.0.7, RISCV64 + C): the 684 bytes decode to exactly 171 four-byte instructions, so the function has no
   compressed instruction; build_table steps pc + 4 (Reusable/YP02.v). Its calls leave the range. ---- *)
Definition entry_tbl : ctable := Eval vm_compute in build_table tfibsegs FS_LLVMF 171 TEmpty.
Lemma entry_tbl_eq : entry_tbl = build_table tfibsegs FS_LLVMF 171 TEmpty.
Proof. vm_cast_no_check (eq_refl entry_tbl). Qed.
Lemma entry_tbl_ok : table_ok tfibsegs entry_tbl.
Proof. rewrite entry_tbl_eq. apply build_table_ok0. unfold FS_LLVMF. lia. Qed.

(* return addresses of the entry's calls (dis fs.asan: the instruction after each `jal`) *)
Definition RA_stack_malloc : Z := 0x80f88.
Definition RA_memchr : Z := 0x81024.
Definition RA_cno : Z := 0x8104c.
Definition RA_malloc : Z := 0x81054.
Definition RA_memcpy : Z := 0x81070.
Definition RA_alloc_live : Z := 0x81090.
Definition RA_peak_reset : Z := 0x81098.
Definition RA_decode : Z := 0x810a4.
Definition RA_peak : Z := 0x810ac.
Definition RA_bounded : Z := 0x810b8.
Definition RA_caw : Z := 0x810c8.
Definition RA_crt : Z := 0x810dc.
Definition RA_crc : Z := 0x810f0.
Definition RA_starved : Z := 0x81100.
Definition RA_fuzz_free : Z := 0x81108.
Definition RA_free : Z := 0x81110.
(* the epilogue's first instruction: the return of free, and the target of the `n > 3 MiB` branch at 0x8103c *)
Definition PC_epi : Z := 0x81110.

(* ---- the walk context (donor ACf5.v:47-50 rtcx): the entry's state and arguments, fs_stat's two values, and the
   position of the class-0 fake frame __asan_stack_malloc_0 grants at 0x80f84 ---- *)
Record fecx := mkFECX {
  c_ly : alayout; c_S : astate; c_W : world tfibsegs; c_regs : bvmap 5 word; c_mem : word -> option byte; c_md : Model;
  c_p : Z; c_n : Z; c_pl : list byte; c_M : Z; c_live : Z; c_cnt : Z; c_fpos : Z }.

Definition fe_sp0 (cx : fecx) : Z := spZ (c_regs cx).
(* the re-aligned sp (`addi sp, sp, -96; andi sp, sp, -32`, 0x80f1c / 0x80f54): s1 and sp from 0x80f58 on *)
Definition fe_sp1 (cx : fecx) : Z := 32 * ((fe_sp0 cx - 96) / 32).
Definition fe_F (cx : fecx) : Z := frame_addr (c_ly cx) 0 (c_fpos cx).
Definition fe_FL (cx : fecx) : Z := flag_addr (c_ly cx) 0 (c_fpos cx).
Definition fe_SF (cx : fecx) : Z := shadow_addr (fe_F cx).
(* the payload as numbers (tfib_lib_pre_x's garr8) *)
Definition fe_bytes (cx : fecx) : list Z := map (fun b : byte => bv_unsigned b) (c_pl cx).

(* the extra atoms 32 .. 45 (header) *)
Definition fe_saved_regs : list (bv 5) := [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25]%bv.
Definition fe_extra (cx : fecx) : list word :=
  Z_to_bv 64 SHADOW_OFF :: map (fun r => YK11.getr (c_regs cx) r) fe_saved_regs ++
  [Z_to_bv 64 (fe_FL cx); Z_to_bv 64 (fe_SF cx)].
Definition fe_E (cx : fecx) (E : env) : Prop :=
  forall j, (j < 14)%nat -> ew E (32 + j) = nth j (fe_extra cx) (Z_to_bv 64 0).

(* the most g_count grows in one call, from the callee posts on the accepted path: check_no_overread 3
   (FSH_Fn_cno.v), preset_base64_decode 1 (decode_spec_ff), check_round_trip at most CRT_ALLOCS = 68 (FSH_Fn_crt.v),
   check_reject_clean_starved 2 (bd <> 0); the others 0. fs_lib_contract_x's post bounds it by FS_CNT_LIB (96,
   FSH_Gen.v): FSW_entry.v uses FE_CNT_MAX <= FS_CNT_LIB *)
Definition FE_CNT_MAX : Z := 3 + 1 + CRT_ALLOCS + 2.

(* ---- the entry facts (donor ACf5.v:52-66 rt_base): fs_lib_contract_x's premises, without AI and the continuation;
   the count's room is the goal's c_cnt + FS_CNT_LIB < 2^63 (FS_CNT_LIB = 96 covers check_round_trip's quiet room
   4 + EV_check_round_trip = 82 and FE_CNT_MAX = 74); the live count's room c_live + ACfn.LIVE_LIB < 2^64 (2^33: decode_spec_ff's
   live + dec_size tb, check_reject_clean_starved_spec's live + dec_size / enc_size, check_round_trip_spec's
   live + LIVE_check_round_trip) is fs_lib_contract_x's ---- *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

Definition fe_base (cx : fecx) : Prop :=
  tfib_lib_pre_x B ameter_triv XL0 FS_RLO FS_RHI (c_regs cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    (c_p cx) (c_n cx) (c_pl cx) (c_M cx) /\
  fs_stat tfibsegs (c_W cx) (c_mem cx) (c_live cx) (c_cnt cx) /\ 0 <= c_cnt cx /\ c_cnt cx + FS_CNT_LIB < 2 ^ 63 /\
  c_live cx + ACfn.LIVE_LIB < 2 ^ 64.

(* ---- the post (donor ACf5.v:92-101 rt_postP): what fs_lib_contract_x's continuation takes, without the leaf: the
   journal from the entry state (own = [], the fake frame released), the tick bound, the callee-saved registers, a0 = 0,
   no leak, the model's io unchanged, the payload unchanged, fs_stat at the same live with the count grown by at most
   FS_CNT_LIB. FSW_entry.v turns it into tfib_lib_post_x at the leaf LL 0 (m_fs md) []. ---- *)
Definition fe_post (FP : list (Z * Z)) (cx : fecx) : world tfibsegs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' k cnt',
    c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
    ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [] ly' S' W' mem' md' k /\
    k <= EV_LIB /\ aregs_preserved (c_regs cx) regs' /\ YK11.getr regs' 10%bv = w64 0 /\
    Permutation (ablocks B ly' S') (ablocks B (c_ly cx) (c_S cx)) /\
    same_io (c_md cx) md' /\
    (forall i, 0 <= i < c_n cx ->
       aview tfibsegs (w_H W') mem' (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
    fs_stat tfibsegs W' mem' (c_live cx) cnt' /\ c_cnt cx <= cnt' <= c_cnt cx + FE_CNT_MAX.

(* ---- the segment form (donor ACf5.v:73-84 rt_from), U form: from any machine state at which the symbolic state ss holds
   under an env E carrying fe_extra, with the journal from the entry over the unpoisoned memory holding the fake frame
   (own = [(0, fpos)]), ARU, and the segment's invariant INV, the run reaches POST. ---- *)
Definition fe_inv : Type :=
  fecx -> env -> Z -> alayout -> astate -> list (Z * Z) -> world tfibsegs -> machine_state -> Model -> Prop.
Definition fe_from (FP : list (Z * Z)) (POST : fecx -> world tfibsegs -> config -> Prop) (ss : sstate) (INV : fe_inv)
  : Prop :=
  forall (cx : fecx) (E : env) (k : Z) ly3 S3 U3 (W3 : world tfibsegs) (ms3 : machine_state) md3,
  fe_base cx -> fe_E cx E ->
  ajournal tfibsegs B LLVMF_STK (fe_sp0 cx) FP (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(0, c_fpos cx)] ly3 S3 W3 (unpoison U3 (ms_mem ms3)) md3 k ->
  ARU tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) md3 ->
  INV cx E k ly3 S3 U3 W3 ms3 md3 ->
  st_ok tfibsegs E ss (restrict (w_H W3) ms3) ->
  SRr tfibsegs W3 (mkCfg ms3 md3) (POST cx).

(* the first segment's form: from the entry configuration, for any POST that takes every granted frame position *)
Definition fe_enter (FP : list (Z * Z)) (POST : fecx -> world tfibsegs -> config -> Prop) (ss : sstate) (INV : fe_inv)
  : Prop :=
  forall ly S (W : world tfibsegs) regs mem md p n pl M live cnt,
  (forall fpos, fe_base (mkFECX ly S W regs mem md p n pl M live cnt fpos)) ->
  fe_from FP POST ss INV ->
  SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md)
    (fun W' c' => exists fpos, POST (mkFECX ly S W regs mem md p n pl M live cnt fpos) W' c').
End d.

(* ---- symbolic states at the segment boundaries ---- *)
(* the eleven words the prologue saves (0x80f24-0x80f4c), at s0 - 8 (ra) .. s0 - 88 (s9), as extra atoms 33 .. 43 *)
Definition fe_sv_chunks : list YP09.chunk :=
  map (fun k => YP09.mkChunk (- 8 * (Z.of_nat k + 1)) (CVal 8 (SOff (33 + k) 0))) (seq 0 11).
(* (B2) right after __asan_stack_malloc_0 returns (0x80f88): the kit's resume state (FSW_frame3.v fsw_resume_ss,
   a working branch 3c98d842174, from a Theorem Labs lane's crcs_resume_sm): the saved words at the s0 atom 8 in
   [-88, 0), the slot 0(s1) at atom 9 in [0, 8), the granted frame at atom 10 (a0) in [0, 64) with its flag word at 56
   holding the flag address (atom 44). *)
Definition ss_B2 : sstate := fsw_resume_ss RA_stack_malloc (-88) 0 fe_sv_chunks 9 0 8 10 (SOff 44 0) 0.

(* (C) the canonical boundary state from the end of the frame set-up (0x81014) on: every register an atom (sr_atoms),
   the fake frame at the s8 atom 24 in [0, 64) with its flag word at 56 (atom 44) and the chunks cs (e.g. `len` at 32),
   its 8 shadow bytes at the s9 atom 25, the saved words at the s0 atom 8; s0 16-aligned, s8 and s2 the frame
   (32-aligned, at least 4096). A segment that needs a register as an address re-expresses it (YI08.st_ok_set_reg),
   e.g. s4 := SOff 24 32 once s4 = &len (0x81084). *)
Definition fe_frame_region (cs : list YP09.chunk) : YP09.region :=
  YP09.mkRegion (Some 24%nat) 0 64 0 64 (YP09.mkChunk 56 (CVal 8 (SOff 44 0)) :: cs).
Definition fe_shadow_region : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 8 [].
Definition fe_regions (cs : list YP09.chunk) : list YP09.region :=
  [fe_frame_region cs; fe_shadow_region; fs_ret_s0_region (-88) 0 fe_sv_chunks].
Definition fe_ss (r : Z) (cs : list YP09.chunk) : sstate :=
  mkSS r sr_atoms (fe_regions cs) None
    (mkFacts [(8%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (24%nat, mkAF 4096 (2 ^ 47) 5); (18%nat, mkAF 4096 (2 ^ 47) 5)] [] []).
(* `len` (the 8-byte local at frame + 32, decode's *lenp) holding the atom n, or the literal v *)
Definition fe_len_atom (n : nat) : YP09.chunk := YP09.mkChunk 32 (CVal 8 (SOff n 0)).
Definition fe_len_lit (v : Z) : YP09.chunk := YP09.mkChunk 32 (CVal 8 (SLit v)).
(* `len`'s shadow byte (s9 + 4, the frame's granule 32..40): the prologue poisons it 0xf8 at 0x80ff0 and `sb zero, 4(s9)`
   at 0x8102c unpoisons it, so from the bltu at 0x8103c to preset_base64_decode's call at 0x810a0 the walk keeps it 0
   (decode_spec_ff's range_addressable premise on *lenp). fe_lensh is that fact; fe_ss_z is the canonical state with
   the byte as a chunk of the shadow region, the form a run starts from so that its end state still records it. *)
Definition fe_shadow_region_z : YP09.region := YP09.mkRegion (Some 25%nat) 0 8 0 8 [YP09.mkChunk 4 (CVal 1 (SLit 0))].
Definition fe_regions_z (cs : list YP09.chunk) : list YP09.region :=
  [fe_frame_region cs; fe_shadow_region_z; fs_ret_s0_region (-88) 0 fe_sv_chunks].
Definition fe_ss_z (r : Z) (cs : list YP09.chunk) : sstate :=
  mkSS r sr_atoms (fe_regions_z cs) None (ss_facts (fe_ss r cs)).
Definition fe_lensh {fx : YK11.FPState} {rc : YM05.RunCeil} (cx : fecx) (W : world tfibsegs) (m : word -> option byte)
  : Prop :=
  aview tfibsegs (w_H W) m (fe_SF cx + 4) = Some 0.

(* ---- invariants at the boundaries ---- *)
Section i. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.

(* the registers every canonical boundary has: s0 = the entry sp, s1 = sp = the re-aligned sp, s2 = s8 = the frame,
   s9 = its shadow address, gp / tp and s10 / s11 the entry's (the function never saves or writes s10 / s11, and
   aregs_preserved covers them: YG0d.v:19-20) *)
Definition fe_regs_core (cx : fecx) (E : env) : Prop :=
  ew E 8 = Z_to_bv 64 (fe_sp0 cx) /\ ew E 9 = Z_to_bv 64 (fe_sp1 cx) /\ ew E 2 = Z_to_bv 64 (fe_sp1 cx) /\
  ew E 18 = Z_to_bv 64 (fe_F cx) /\ ew E 24 = Z_to_bv 64 (fe_F cx) /\ ew E 25 = Z_to_bv 64 (fe_SF cx) /\
  ew E 3 = YK11.getr (c_regs cx) 3%bv /\ ew E 4 = YK11.getr (c_regs cx) 4%bv /\
  ew E 26 = YK11.getr (c_regs cx) 26%bv /\ ew E 27 = YK11.getr (c_regs cx) 27%bv.
(* the facts every boundary after the grant has (besides the journal and ARU of fe_from) *)
Definition fe_common (cx : fecx) (k : Z) (S3 : astate) (W3 : world tfibsegs) (ms3 : machine_state) (md3 : Model) (KB : Z) : Prop :=
  0 <= k <= KB /\ same_io (c_md cx) md3 /\
  (forall i, 0 <= i < c_n cx ->
     aview tfibsegs (w_H W3) (ms_mem ms3) (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
  blocks_bytes S3 <= blocks_bytes (c_S cx) + 2 ^ 32.

(* (B2) 0x80f88: nothing allocated yet; a0 = the frame, s3 = n, s4 = p, s6 = the shadow base; the frame's 8 shadow
   bytes are 0 (__asan_stack_malloc_0's post) *)
Definition INV_B2 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
    U3 = [] /\ k = 0 /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\ st_nev S3 = st_nev (c_S cx) /\
    blocks_bytes S3 = blocks_bytes (c_S cx) /\ same_io (c_md cx) md3 /\
    ew E 8 = Z_to_bv 64 (fe_sp0 cx) /\ ew E 9 = Z_to_bv 64 (fe_sp1 cx) /\ ew E 2 = Z_to_bv 64 (fe_sp1 cx) /\
    ew E 10 = Z_to_bv 64 (fe_F cx) /\ ew E 19 = YK11.getr (c_regs cx) 11%bv /\ ew E 20 = YK11.getr (c_regs cx) 10%bv /\
    ew E 22 = Z_to_bv 64 SHADOW_OFF /\ ew E 3 = YK11.getr (c_regs cx) 3%bv /\ ew E 4 = YK11.getr (c_regs cx) 4%bv /\
    ew E 26 = YK11.getr (c_regs cx) 26%bv /\ ew E 27 = YK11.getr (c_regs cx) 27%bv /\
    zero_shadow (aview tfibsegs (w_H W3) (ms_mem ms3)) SHADOW_OFF (fe_F cx) (fs_frame_bytes 0) /\
    (forall i, 0 <= i < c_n cx ->
       aview tfibsegs (w_H W3) (ms_mem ms3) (c_p cx + i) = aview tfibsegs (w_H (c_W cx)) (c_mem cx) (c_p cx + i)) /\
    fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx).

(* (C1) 0x81024, memchr(data, 0, size) returned: a0 = its result, s3 = size, s4 = data, s6 = the shadow base; the
   state is fe_ss RA_memchr [] *)
Definition fe_memchr_res (cx : fecx) : Z :=
  match zfind 0 (fe_bytes cx) with None => 0 | Some j => c_p cx + Z.of_nat j end.
Definition INV_C1 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
    U3 = [] /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\ st_nev S3 = st_nev (c_S cx) /\
    blocks_bytes S3 = blocks_bytes (c_S cx) /\ fe_common cx k S3 W3 ms3 md3 0 /\ fe_regs_core cx E /\
    ew E 10 = Z_to_bv 64 (fe_memchr_res cx) /\ ew E 19 = Z_to_bv 64 (c_n cx) /\ ew E 20 = Z_to_bv 64 (c_p cx) /\
    ew E 22 = Z_to_bv 64 SHADOW_OFF /\ fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx).

(* the strnlen n of fs.c:322 (fuzz_strnlen(data, size), compiled to memchr + sub, 0x81020-0x81028) *)
Definition fe_n (cx : fecx) : Z :=
  match zfind 0 (fe_bytes cx) with None => c_n cx | Some j => Z.of_nat j end.

(* (C2) 0x8104c, check_no_overread(data, n) returned (n <= 3 MiB): s3 = n, s4 = data, s6 = the shadow base, len (frame +
   32) = -1 (0x81038) with its shadow byte 0 (fe_lensh), g_count + 3 (check_no_overread_spec's post); the state is
   fe_ss RA_cno [fe_len_lit (-1)] *)
Definition INV_C2 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
    U3 = [] /\ ablocks B ly3 S3 = ablocks B (c_ly cx) (c_S cx) /\
    fe_common cx k S3 W3 ms3 md3 EV_check_no_overread /\ fe_regs_core cx E /\
    fe_n cx <= 3 * 2 ^ 20 /\ ew E 19 = Z_to_bv 64 (fe_n cx) /\ ew E 20 = Z_to_bv 64 (c_p cx) /\
    ew E 22 = Z_to_bv 64 SHADOW_OFF /\ fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx + 3) /\
    fe_lensh cx W3 (ms_mem ms3).

(* the text the harness copies (fs.c:324-326): the payload's first n bytes, NUL-free *)
Definition fe_tb (cx : fecx) : list Z := firstn (Z.to_nat (fe_n cx)) (fe_bytes cx).
(* the pc of the first call of the six (fuzz_alloc_live, 0x8108c): the boundary after the text copy *)
Definition PC_C5 : Z := 0x8108c.

(* (C5) 0x8108c, after `text = malloc(n + 1); memcpy(text, data, n); text[n] = 0` (0x8104c-0x81088): s3 = n, s4 = &len
   (frame + 32, 0x81084, its shadow byte 0), s5 = text, s6 = the shadow base; the text is a plain ASan block of n + 1
   bytes holding the C string fe_tb; nothing else allocated, U = []; the state is fe_ss PC_C5 [fe_len_lit (-1)] *)
Definition INV_C5 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text,
    U3 = [] /\ Permutation (ablocks B ly3 S3) ((text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) /\
    fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1) /\ fe_regs_core cx E /\
    fe_n cx <= 3 * 2 ^ 20 /\ ew E 19 = Z_to_bv 64 (fe_n cx) /\ ew E 20 = Z_to_bv 64 (fe_F cx + 32) /\
    ew E 21 = Z_to_bv 64 text /\ ew E 22 = Z_to_bv 64 SHADOW_OFF /\
    cstr_ok tfibsegs W3 (ms_mem ms3) text (fe_tb cx) /\
    fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) (c_cnt cx + 3) /\ fe_lensh cx W3 (ms_mem ms3).

(* (C6) 0x810c8, check_as_written(text, body, len) returned: s3 = n, s4 = &len, s5 = text, s6 = body, s7 = the live
   count fuzz_alloc_live read (fs.c:328); len holds the extra atom 46 = l; decode's answer is caw_answerA (body = 0 and
   l = SIZE_MAX, or body = the decoded block with its head in U); the state is fe_ss RA_caw [fe_len_atom 46] under an
   env whose extra atom 46 is l *)
Definition fe_body_blocks (cx : fecx) (body : Z) : list (Z * Z) :=
  if body =? 0 then [] else [(body - HEAD, dec_size (fe_tb cx) + HEAD)].
Definition fe_body_U (body : Z) : list (Z * Z) := if body =? 0 then [] else [(body - HEAD, HEAD)].
Definition fe_live6 (cx : fecx) (body : Z) : Z := c_live cx + (if body =? 0 then 0 else dec_size (fe_tb cx)).
Definition fe_after_decode (cx : fecx) (E : env) ly3 S3 U3 (W3 : world tfibsegs) (ms3 : machine_state)
  (text body l : Z) : Prop :=
  U3 = fe_body_U body /\
  Permutation (ablocks B ly3 S3) (fe_body_blocks cx body ++ (text, fe_n cx + 1) :: ablocks B (c_ly cx) (c_S cx)) /\
  caw_answerA tfibsegs B ly3 S3 U3 W3 (ms_mem ms3) (fe_tb cx) body l /\
  fe_regs_core cx E /\ fe_n cx <= 3 * 2 ^ 20 /\
  ew E 19 = Z_to_bv 64 (fe_n cx) /\ ew E 20 = Z_to_bv 64 (fe_F cx + 32) /\ ew E 21 = Z_to_bv 64 text /\
  ew E 22 = Z_to_bv 64 body /\ ew E 23 = Z_to_bv 64 (c_live cx) /\ ew E 46 = Z_to_bv 64 l /\
  cstr_ok tfibsegs W3 (ms_mem ms3) text (fe_tb cx).
Definition INV_C6 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text body l,
    fe_after_decode cx E ly3 S3 U3 W3 ms3 text body l /\
    fe_common cx k S3 W3 ms3 md3 (EV_check_no_overread + 1 + EV_preset_base64_decode + EV_check_as_written) /\
    fs_stat tfibsegs W3 (ms_mem ms3) (fe_live6 cx body) (c_cnt cx + 4).

(* (C7) 0x810f0, check_round_trip (body <> 0, ra 0x810dc, then `j 0x810f0`) or check_reject_clean (body = 0) returned:
   as C6, with g_count grown by at most CRT_ALLOCS on the first path (check_round_trip_spec's bound); the state is
   fe_ss RA_crc [fe_len_atom 46] *)
Definition INV_C7 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 => exists text body l,
    fe_after_decode cx E ly3 S3 U3 W3 ms3 text body l /\
    fe_common cx k S3 W3 ms3 md3
      (EV_check_no_overread + 1 + EV_preset_base64_decode + EV_check_as_written + EV_check_round_trip) /\
    (exists cnt7, fs_stat tfibsegs W3 (ms_mem ms3) (fe_live6 cx body) cnt7 /\
       c_cnt cx + 4 <= cnt7 <= c_cnt cx + 4 + (if body =? 0 then 0 else CRT_ALLOCS)).

(* (C9) 0x81110, at the epilogue: every block of the entry back (none of the walk's left), U = []; reached by
   free(text) (0x8110c) or by the `n > 3 MiB` branch (0x8103c); the state is fe_ss PC_epi [] *)
Definition INV_C9 : fe_inv :=
  fun cx E k ly3 S3 U3 W3 ms3 md3 =>
    U3 = [] /\ Permutation (ablocks B ly3 S3) (ablocks B (c_ly cx) (c_S cx)) /\
    fe_common cx k S3 W3 ms3 md3
      (EV_check_no_overread + 1 + EV_preset_base64_decode + EV_check_as_written + EV_check_round_trip + 2) /\
    fe_regs_core cx E /\
    (exists cnt3, fs_stat tfibsegs W3 (ms_mem ms3) (c_live cx) cnt3 /\ c_cnt cx <= cnt3 <= c_cnt cx + FE_CNT_MAX).

End i.
