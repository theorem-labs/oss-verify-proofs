(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: (image A's header, kept from lib/A/RT_asan_stack_malloc_0.v for provenance; image B's own is the header below) the runtime site contract of __asan_stack_malloc_0 (FakeStack class 0) on
   fuzz_reply.asan at 0x3d168, YG0d.v's astack_malloc_realizes at class 0, which W_frame.v (palf_sm0) and the core
   consume.  Relocated from libreac/fuzz_grant's walk of the same code, a working branch c8e8b0fa5ec
   proofs/libreac/fuzz_grant/lib/A/Rt/StackMalloc0Tbl.v (module SM0Tbl below) and StackMalloc0.v (the rest),
   themselves ported from proofs/cgif/cgif_rgb_fuzzer/lib/YF9p.v + YF9q.v (trb_stack_malloc_0) into
   cgif_file_fuzzer's vocabulary.  fuzz_grant's 93 words at 0x3cda4 equal fuzz_reply's at 0x3d168 except the eight
   pc-relative words at +0x18/+0x1c, +0x20, +0xa8/+0xac, +0xb8, +0x12c, +0x164, whose targets pair by code bytes
   (TLS descriptor 0x9d550 -> 0x9e6b0, the __tls_get_addr trampoline 0x4218c -> 0x421f8, GetCurrentThread
   0x5c00c -> 0x5d688, MemToShadow 0x3d410 -> 0x3d46c, AsyncSignalSafeLazyInitFakeStack 0x5c280 -> 0x5d8fc).
   Moved: the code addresses (0x3cda4+k -> 0x3d168+k), the FS_FOUND literal 249504 -> 250468 (0x3d264), TP/TSD
   and the T+48/T+56 cells (generated AF0m.v), fsA_rodata (RelocA's AF0r.v, checked by fsA_rodata_chk), the image
   end 6266880 -> 6270976 (TFIB_IMG_END 0x5fb000) in the low-zone bounds, GrantSyms -> TfibSyms, module paths;
   the code table adds class 0's range on top of AF0r.tbl_fs, which (unlike fuzz_grant's) does not hold it. *)
(* Modified by Theorem Labs, 2026-10-30 (a Theorem Labs lane): copied from lib/A/RT_asan_stack_malloc_0.v (a working branch dac32c4fd94) for fuzz_reply.asan-ubsan (image B): the code addresses, the FS_FOUND literal, TP / TSD, the T+48 / T+56 cells, fsA_rodata's .got slots, TFIB_IMG_END and the module paths changed (lib.A -> lib.B; AB1v / AF0m / AF0x / AE34 / AE2y / AE2k -> YB1v / YF0m / YF0x / YE34 / YE2y / YE2k), and the code table is built on YE34.tbl_icpt with class 1's ranges in place of AF0r.tbl_fs. *)
(* Port notes (a Theorem Labs lane): the runtime site contract of __asan_stack_malloc_0 (FakeStack
   class 0) on fuzz_reply.asan-ubsan (image B) at 0x3d1c0, YG0d.v's astack_malloc_realizes at class 0.
   RULE 24: `proof-index __asan_stack_malloc_0 0x3d1c0`: 0 released lemmas for either key; no released FUNCTION proof found. Second-agent
   check: CONFIRM (the 25 unreleased hits are all statements or symbols; in the lemma index over 17316 refs, no lib/B class-0 walk declaration, and every stack_malloc0_contract / tfib_stack_malloc_at / asm0 / ASM0 declaration is lib/A). REUSE = this port of the image-A walk of the same function.
   SOURCE: lib/A/RT_asan_stack_malloc_0.v at dac32c4fd94 (sha256 d1b6fdcac23c; internal record, the
   same at meet c653c819019 and prep 1f58d4146b4), image A's walk at 0x3d168 (itself relocated from libreac/fuzz_grant's
   StackMalloc0Tbl.v / StackMalloc0.v, from cgif_rgb_fuzzer YF9p.v / YF9q.v). The walk's text is A's; only the items
   below move, and module paths lib.A -> lib.B (AB1v AE34 AF0l AF0m AF0x AE2y AE2k W_syms W_place -> YB1v YE34 YF0l
   YF0m YF0x YE2y YE2k W_syms W_place).
   BYTES: bytecmp.py (sha256 1480ca2faea0; internal record) on the pinned binaries (A sha256 42c58610e125, B
   10ffb5f9202a): A 0x3d168 vs B 0x3d1c0, 93 words, EQUAL-mod-pcrel (3 pc-relative, 0 real, 0 unmeasured): +0x18/+0x1c
   (TLS descriptor of fake_stack_tls, .got 0x9e6b0 -> 0x9ec30) and +0xac (.got slot of
   __asan_option_detect_stack_use_after_return 0x9da28 -> 0x9dfa8); every jal pairs by symbol (the __tls_get_addr
   trampoline 0x42250, FakeStack::GC 0x3cd74, GetCurrentThread 0x5d6e0, MemToShadow 0x3d4c4,
   AsyncSignalSafeLazyInitFakeStack 0x5d954). Each callee range of the code table compares EQUAL or EQUAL-mod-pcrel,
   its targets paired by symbol.
   RELOCATED, A -> B (class; source: B's symbol table, B's disassembly, lib/B tables):
   - code: FS_ENTRY 0x3d168 -> 0x3d1c0 (__asan_stack_malloc_0+0; = YF0l.Tfib_code class 0 = W_place
     WS_asan_stack_malloc_0), FS_LOOP 0x3d1ec -> 0x3d244 (+0x84), FS_FOUND 0x3d264 -> 0x3d2bc (+0xfc; its decimal
     250468 -> 250556 in probe_loop), FS_SDFF 0x3d288 -> 0x3d2e0 (+0x120), FS_SDSH 0x3d2a4 -> 0x3d2fc (+0x13c);
     fs0_ranges (0x3d168, 93) -> (0x3d1c0, 93);
   - the code table: AF0r.tbl_fs (lib/A only) -> fs1_ranges on YE34.tbl_icpt, AF0r's ranges by symbol + offset:
     __asan_stack_malloc_1 0x3d2dc -> 0x3d334, RegisterCommonFlags+0x358 0x63348 -> 0x633a0,
     ___interceptor___tls_get_addr 0x47958 -> 0x479b0, __tls_get_addr 0x971ec -> 0x9776c, GetCurrentThread 0x5d688 ->
     0x5d6e0, AsanTSDGet 0x5613c -> 0x56194, __pthread_getspecific 0x982a0 -> 0x98820, DTLS_on_tls_get_addr 0x6ad9c ->
     0x6adf4, MemToShadow (sm0's jal target) 0x3d46c -> 0x3d4c4; the word counts stay;
   - TP 0x5d9470 -> 0x5d99f0 (builtin_tls+0xc8, YF0m TFIB_TP), TSD 0x5fa818 -> 0x5fad98 (__pthread_tsd_main, YF0m
     TFIB_TSD); the T+48 / T+56 cells 0x5d9ba8 -> 0x5da128 (builtin_tls+0x800), 0x5d9c84 -> 0x5da204 (builtin_tls+0x8dc)
     (YF0m Tfib_const_sym AT 48 / AT 56);
   - fsA_rodata (each cell in YF0m's Tfib_const, checked by fsA_rodata_chk): .got TLS slot of fake_stack_tls 0x9e6b0 ->
     0x9ec30, real___tls_get_addr 0x9f7a8 -> 0x9fd28 holding __tls_get_addr 0x971ec -> 0x9776c, .got slot of
     common_flags_dont_use 0x9d9c0 -> 0x9df40 holding 0x137be8 -> 0x138168, common_flags_dont_use+0x89 0x137c71 ->
     0x1381f1, .got slot of current_verbosity 0x9da20 -> 0x9dfa0 holding 0x135b58 -> 0x1360d8 (and its own cell),
     .got TLS slot of dtls 0x9e6c0 -> 0x9ec40, tsd_key_inited 0xa5920 -> 0xa5ea0, builtin_tls+0xe8 0x5d9490 -> 0x5d9a10,
     builtin_tls+0xf0 0x5d9498 -> 0x5d9a18 holding builtin_tls+0x8c8 0x5d9c70 -> 0x5da1f0; the values 1,
     0xfffffffffffff800, 0x8 (module id, DTPREL offset, TLS offset) and 0 stay;
   - the image end 6270976 -> 6275072 (YF0x.TFIB_IMG_END 0x5fc000, page-rounded PT_LOAD end) in the low-zone bounds,
     and its eighth 783872 -> 784384;
   - build identity: ofl_head 0x5f9b68 -> 0x5fa0e8 (YE2k.A_ofl_head), main 0x81e4c -> 0x81ea4,
     LLVMFuzzerTestOneInput 0x840b0 -> 0x84408 (their first words stay).
   KEPT (no address): instruction words, sizes, counts, offsets, flag values, the ASan constants (17594333495296,
   140737479966720, 2147446784, 2147450880, 11571200) and 2148213760 (a lower bound on the low shadow, still below
   B's kLowShadowBeg + 0x5fc000 / 8). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0t YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YE2k W_syms W_place.
Module SM0Tbl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition CID : Z := 0.
Definition FS_ENTRY : Z := 0x3d1c0.
Definition FS_LOOP : Z := 0x3d244.
Definition FS_FOUND : Z := 0x3d2bc.
Definition FS_SDFF : Z := 0x3d2e0.
Definition FS_SDSH : Z := 0x3d2fc.
Definition FS_WIN : Z := 208.
Definition FS_N : Z := 16384.
Definition FS_FLOFF : Z := 0x1000.
Definition FS_B : Z := 64.
Definition FS_FROFF : Z := 0x9000.
Definition FS_HOFF : Z := 0.
Definition TP : Z := 0x5d99f0.
Definition TSD : Z := 0x5fad98.
(* image B has no class-1 table (lib/A/AF0r.v has no lib/B twin): AF0r.v's fs_ranges at B's addresses (symbol +
   offset, header) on lib/B/YE34.v's tbl_icpt, as AF0r.v builds its table on lib/A/AE34.v's; then class 0's 93 words,
   0x3d1c0 .. 0x3d330, on top of it, as lib/A builds its class-0 table on AF0r.tbl_fs. *)
Definition fs1_ranges : list (Z * nat) :=
[(0x3d334, 100%nat); (0x633a0, 2%nat); (0x479b0, 31%nat); (0x9776c, 9%nat); (0x5d6e0, 8%nat);
(0x56194, 6%nat); (0x98820, 7%nat); (0x6adf4, 140%nat); (0x3d4c4, 28%nat)].
Definition fs0_ranges : list (Z * nat) := [(0x3d1c0, 93%nat)].
Definition tbl_fs : ctable := Eval vm_compute in build_ranges fs0_ranges (build_ranges fs1_ranges tbl_icpt).
Lemma tbl_fs_eq : tbl_fs = build_ranges fs0_ranges (build_ranges fs1_ranges tbl_icpt). Proof. vm_cast_no_check (eq_refl tbl_fs). Qed.
Lemma tbl_fs_ok : table_ok tfibsegs tbl_fs.
Proof.
rewrite tbl_fs_eq. apply build_ranges_ok; [unfold fs0_ranges; repeat constructor; cbn; discriminate|].
apply build_ranges_ok; [unfold fs1_ranges; repeat constructor; cbn; discriminate | exact tbl_icpt_ok].
Qed.
Lemma fs_phase : forall (W : world tfibsegs) E ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_runN tfibsegs tbl_fs FUEL ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E ss ss' st ms md HS Hrun.
eapply (SRr_run_gen tfibsegs tbl_fs tbl_fs_ok YF0x.Hwx_tfa W FUEL E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Lemma fs_phase_to : forall (W : world tfibsegs) E stop ss ss' st ms md,
st_ok tfibsegs E ss (restrict (w_H W) ms) -> sym_run_toN tfibsegs tbl_fs FUEL stop ss = (ss', st) ->
SRr tfibsegs W (mkCfg ms md)
(fun W' c' => W' = W /\ exists ms1 mat1, c' = mkCfg ms1 (with_vm_backing (m_vm_lazy md) mat1 md) /\
match st with RS_ecall => st_ok_ecall tfibsegs E ss' (restrict (w_H W) ms1) | _ => st_ok tfibsegs E ss' (restrict (w_H W) ms1) end /\
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms1) /\ frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms1))).
Proof.
intros W E stop ss ss' st ms md HS Hrun.
eapply (SRr_run_to_gen tfibsegs tbl_fs tbl_fs_ok YF0x.Hwx_tfa W FUEL stop E ss ss' st ms md _ HS Hrun).
intros ms1 mat1 HS1 HF HFr. apply SRr_ret. split; [reflexivity|]. exists ms1, mat1. split; [reflexivity|]. split; [exact HS1|]. split; [exact HF | exact HFr].
Qed.
Definition fsA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++
[(0x9ec30, 16, [(0, 8%N, 1); (8, 8%N, 0xfffffffffffff800)]); (0x9fd28, 8, [(0, 8%N, 0x9776c)]); (0x9df40, 8, [(0, 8%N, 0x138168)]);
(0x1381f1, 1, [(0, 1%N, 1)]); (0x9dfa0, 8, [(0, 8%N, 0x1360d8)]); (0x1360d8, 4, [(0, 4%N, 0)]); (0x9ec40, 8, [(0, 8%N, 0x8)]);
(0xa5ea0, 8, [(0, 1%N, 1); (4, 4%N, 0)]); (TP - 88, 8, [(0, 8%N, TSD)]); (TP - 8, 8, [(0, 8%N, 0x5d9a10)]); (0x5d9a18, 8, [(0, 8%N, 0x5da1f0)])].
Lemma fsA_rodata_chk : forall ly, rodata_chk ly fsA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Definition aT : nat := 32. Definition aC : nat := 33. Definition aD : nat := 34. Definition aF : nat := 35. Definition aH : nat := 36.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- FS_WIN) 0 (- FS_WIN) 0 [].
Definition rTSD : YP09.region := YP09.mkRegion None TSD (TSD + 8) TSD TSD [YP09.mkChunk TSD (CVal 8 (SOff aC 0))].
Definition rTP0 : YP09.region := YP09.mkRegion None TP (TP + 8) TP TP [YP09.mkChunk TP (CVal 8 (SOff aF 0))].
Definition rTP8 : YP09.region := YP09.mkRegion None (TP + 8) (TP + 16) (TP + 8) (TP + 8) [YP09.mkChunk (TP + 8) (CVal 8 (SOff aD 0))]    .
Definition rT : YP09.region := YP09.mkRegion (Some aT) 48 64 48 48 [YP09.mkChunk 48 (CVal 8 (SLit 0x5da128)); YP09.mkChunk 56 (CVal 8 (SLit 0x5da204))].
Definition rC : YP09.region := YP09.mkRegion (Some aC) 152 160 152 152 [YP09.mkChunk 152 (CVal 8 (SOff aT 0))].
Definition rD : YP09.region := YP09.mkRegion (Some aD) 24 32 24 24 [YP09.mkChunk 24 (CVal 8 (SLit TP))].
Definition rF : YP09.region := YP09.mkRegion (Some aF) FS_HOFF 97 FS_HOFF (FS_HOFF + 8)
[YP09.mkChunk FS_HOFF (CVal 8 (SOff aH 0)); YP09.mkChunk 88 (CVal 8 (SLit 20)); YP09.mkChunk 96 (CVal 1 (SLit 0))].
Definition memA : smem := stkA :: rTSD :: rTP0 :: rTP8 :: rT :: rC :: rD :: rF :: map ro_region fsA_rodata.
Definition factsA : list (nat * afact) :=
[(2%nat, mkAF (kHighMemBeg + FS_WIN) kHighMemEnd 4);
(aT, mkAF 4096 (CEIL_MAX - 4096) 12)              ;
(aC, mkAF 4096 (CEIL_MAX - 256) 3)                ;
(aD, mkAF 4096 (CEIL_MAX - 4096) 12)              ;
(aF, mkAF 4096 (CEIL_MAX - kFakeStackSize) 12)    ;
(aH, mkAF 0 (2^64 - 1) 0)].
Definition regsA : list sv := Eval vm_compute in (firstn 4 sr_atoms ++ [SLit TP] ++ skipn 5 sr_atoms).
Definition ssA : sstate := mkSS FS_ENTRY regsA memA None (mkFacts factsA [] []).
Definition RUNTO (stop : Z) (s : sstate) := sym_run_toN tfibsegs tbl_fs FUEL stop s.
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_fs FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition eA : sstate := Eval vm_compute in fst (RUNTO FS_LOOP ssA).
Definition add_fact (ss : sstate) (n : nat) (f : afact) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
Lemma st_ok_add_fact : forall E ss ms n lo hi,
st_ok tfibsegs E ss ms -> ss_resv ss = None -> lo <= bv_unsigned (ew E n) <= hi ->
st_ok tfibsegs E (add_fact ss n (mkAF lo hi 0)) ms.
Proof.
intros E ss ms n lo hi HS Hrv Hr.
destruct HS as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & (HA & HC & HL)).
unfold st_ok, add_fact. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts f_atoms f_conds f_alias].
rewrite Hrv in H4 |- *.
repeat (split; [assumption|]). split; [|split; assumption].
cbn [atoms_ok]. split; [|exact HA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
split; [exact Hr|]. split; [rewrite Z.pow_0_r; apply Z.mod_1_r | lia].
Qed.
Definition aH2 : nat := 37. Definition aPOS : nat := 38. Definition aFLG : nat := 39. Definition aCNT : nat := 40. Definition aFF : nat := 41. Definition aSH : nat := 42.
Definition rFLG : YP09.region := YP09.mkRegion (Some aFLG) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition rFF : YP09.region := YP09.mkRegion (Some aFF) 0 FS_B 0 FS_B [].
Definition rSH : YP09.region := YP09.mkRegion (Some aSH) 0 (FS_B / 8) 0 (FS_B / 8) [].
Definition updC1 : list (bv 5 * sv) := [((12%bv : bv 5), SOff aH2 0); ((16%bv : bv 5), SOff aPOS 0); ((15%bv : bv 5), SOff aFLG 0); ((17%bv : bv 5), SLit 0); ((10%bv : bv 5), SOff aCNT 0)].
Definition idxC1 : list nat := [7; 8; 9; 10; 11; 12; 13; 14]%nat.
Definition memC1 : smem := nth 0 (ss_mem eA) stkA :: rFLG :: map (fun i => nth i (ss_mem eA) stkA) idxC1.
Definition preC1 : sstate := add_fact (mkSS FS_FOUND (sr_sets (ss_regs eA) updC1) memC1 None (ss_facts eA)) aPOS (mkAF 0 (FS_N - 1) 0).
Definition ssC1 : sstate := Eval vm_compute in preC1.
Lemma ssC1_eq : preC1 = ssC1. Proof. vm_compute. reflexivity. Qed.
Definition eC1 : sstate := Eval vm_compute in fst (RUN ssC1).
Definition stC1 : run_status := Eval vm_compute in snd (RUN ssC1).
Definition s1C1 : sv := Eval vm_compute in RG eC1 9.
Definition ffLO (hi : bool) : Z := if hi then kHighMemBeg else 4096.
Definition ffHI (hi : bool) : Z := if hi then CEIL_MAX - FS_B else kLowShadowBeg - FS_B.
Definition shLO (hi : bool) : Z := if hi then kHighShadowBeg else kLowShadowBeg + TFIB_IMG_END / 8.
Definition shHI (hi : bool) : Z := if hi then kHighShadowEnd - FS_B / 8 else kLowShadowEnd - FS_B / 8.
Definition memC2 : smem := nth 0 (ss_mem eC1) stkA :: rFF :: tl (ss_mem eC1).
Definition preC2 (hi : bool) : sstate := add_fact (mkSS (ss_pc eC1) (sr_sets (ss_regs eC1) [((9%bv : bv 5), SOff aFF 0)]) memC2 None (ss_facts eC1)) aFF (mkAF (ffLO hi) (ffHI hi) 0).
Definition ssC2H : sstate := Eval vm_compute in preC2 true.
Definition ssC2L : sstate := Eval vm_compute in preC2 false.
Definition ssC2 (hi : bool) : sstate := if hi then ssC2H else ssC2L.
Lemma ssC2_eq : forall hi, preC2 hi = ssC2 hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition eC2H : sstate := Eval vm_compute in fst (RUN ssC2H).
Definition stC2H : run_status := Eval vm_compute in snd (RUN ssC2H).
Definition eC2L : sstate := Eval vm_compute in fst (RUN ssC2L).
Definition stC2L : run_status := Eval vm_compute in snd (RUN ssC2L).
Definition eC2 (hi : bool) : sstate := if hi then eC2H else eC2L.
Definition stC2 (hi : bool) : run_status := if hi then stC2H else stC2L.
Definition a1C2 : sv := Eval vm_compute in RG eC2H 11.
Definition memC2e : smem := Eval vm_compute in ss_mem eC2H.
Lemma eC2_mem : forall hi, ss_mem (eC2 hi) = memC2e. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition memC3 : smem := nth 0 memC2e stkA :: rSH :: tl memC2e.
Definition preC3 (hi : bool) : sstate := add_fact (mkSS (ss_pc (eC2 hi)) (sr_sets (ss_regs (eC2 hi)) [((11%bv : bv 5), SOff aSH 0)]) memC3 None (ss_facts (eC2 hi))) aSH (mkAF (shLO hi) (shHI hi) 0).
Definition ssC3H : sstate := Eval vm_compute in preC3 true.
Definition ssC3L : sstate := Eval vm_compute in preC3 false.
Definition ssC3 (hi : bool) : sstate := if hi then ssC3H else ssC3L.
Lemma ssC3_eq : forall hi, preC3 hi = ssC3 hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition eC3H : sstate := Eval vm_compute in fst (RUN ssC3H).
Definition stC3H : run_status := Eval vm_compute in snd (RUN ssC3H).
Definition eC3L : sstate := Eval vm_compute in fst (RUN ssC3L).
Definition stC3L : run_status := Eval vm_compute in snd (RUN ssC3L).
Definition eC3 (hi : bool) : sstate := if hi then eC3H else eC3L.
Definition stC3 (hi : bool) : run_status := if hi then stC3H else stC3L.
Definition FS_RET : Z := Eval vm_compute in ss_pc eC3H.
Lemma eC3_pc : forall hi, ss_pc (eC3 hi) = FS_RET. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma fetch_lit_fs : forall (p : word) (w : bv 32), clookup tbl_fs (bv_unsigned p) = Some (bv_unsigned w) -> fetch_word tfibsegs p = Some w.
Proof. intros p w H. rewrite <- (Z_to_bv_bv_unsigned 64 p), <- (Z_to_bv_bv_unsigned 32 w). apply tbl_fs_ok. exact H. Qed.
Lemma fs_frames_cid : fs_frames CID = FS_N. Proof. vm_compute. reflexivity. Qed.
Lemma land_mask_N : forall h, 0 <= h -> Z.land (h mod 2 ^ 64) (FS_N - 1) = h mod FS_N.
Proof.
intros h Hh. replace (FS_N - 1) with (Z.ones 14) by reflexivity. rewrite Z.land_ones by lia.
change FS_N with (2 ^ 14). rewrite <- (Z.mod_mod_divide h (2 ^ 64) (2 ^ 14)) by (first [lia | exists (2 ^ (64 - 14)); reflexivity]). reflexivity.
Qed.
Lemma v_and_mask : forall h, 0 <= h -> v_and (Z_to_bv 64 h) (Z_to_bv 64 (FS_N - 1)) = Z_to_bv 64 (h mod FS_N).
Proof.
intros h Hh. unfold v_and. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite (Z.mod_small (FS_N - 1)) by (unfold FS_N; lia). rewrite land_mask_N by exact Hh. reflexivity.
Qed.
Lemma step_and_at : forall segs regs pc mem rom w rd rs1 rs2 v,
fetch_word segs pc = Some w -> is_ecall w = false ->
decode_any w = Some (Op ALU_AND rd rs1 rs2, 4%Z) ->
bv_eqb rd 0 = false ->
v_and (getr regs rs1) (getr regs rs2) = v ->
RiscvSemantics.step segs (mkst regs pc mem rom) = MachineOk (mkst (regupd regs rd v) (v_addi pc 4) mem rom).
Proof.
intros segs regs pc mem rom w rd rs1 rs2 v Hf He Hd Hrd Hv. rewrite (step_and segs regs pc mem rom w rd rs1 rs2 Hf He Hd). rewrite Hrd, Hv. reflexivity.
Qed.
Lemma v_addiw_dec : forall c, 1 <= c < 2 ^ 31 -> v_addiw (Z_to_bv 64 c) (-1) = Z_to_bv 64 (c - 1).
Proof.
intros c Hc. unfold v_addiw. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia.
unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296. f_equal.
change (2 ^ 31)%Z with 2147483648 in Hc. rewrite Z.mod_small by lia. lia.
Qed.
End e.
Ltac ftac := apply fetch_lit_fs; vm_compute; reflexivity.
Ltac steplb1 F0 D RD := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_lbu; [ exact F | reflexivity | exact D | gr; imm_norm; rewrite v_addi_lit, Z.add_0_r; exact RD ]
| step_simpl ].
Ltac svand F0 D vv := let F := litF F0 in
chain_step;
[ reflexivity
| eapply step_and_at with (v := vv); [ exact F | reflexivity | exact D | reflexivity | val ]
| step_simpl ].
Section g. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma F_L0 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x0)) = Some (0x00d67833%bv : bv 32). Proof. ftac. Qed.
Lemma D_L0 : decode_any (0x00d67833%bv : bv 32) = Some (Op ALU_AND 16 12 13, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L4 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x4)) = Some (0x010587b3%bv : bv 32). Proof. ftac. Qed.
Lemma D_L4 : decode_any (0x010587b3%bv : bv 32) = Some (Op ALU_ADD 15 11 16, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L8 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x8)) = Some (0x0007c883%bv : bv 32). Proof. ftac. Qed.
Lemma D_L8 : decode_any (0x0007c883%bv : bv 32) = Some (Load SZ1 false 17 15 0, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_Lc : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0xc)) = Some (0x06088663%bv : bv 32). Proof. ftac. Qed.
Lemma D_Lc : decode_any (0x06088663%bv : bv 32) = Some (Branch BC_EQ 17 0 108, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L10 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x10)) = Some (0xfff5051b%bv : bv 32). Proof. ftac. Qed.
Lemma D_L10 : decode_any (0xfff5051b%bv : bv 32) = Some (OpImm32 10 10 4095, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L14 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x14)) = Some (0x00160613%bv : bv 32). Proof. ftac. Qed.
Lemma D_L14 : decode_any (0x00160613%bv : bv 32) = Some (OpImm ALU_ADD 12 12 1, 4%Z). Proof. vm_refl_bv. Qed.
Lemma F_L18 : fetch_word tfibsegs (Z_to_bv 64 (FS_LOOP + 0x18)) = Some (0xfe0514e3%bv : bv 32). Proof. ftac. Qed.
Lemma D_L18 : decode_any (0xfe0514e3%bv : bv 32) = Some (Branch BC_NE 10 0 8168, 4%Z). Proof. vm_refl_bv. Qed.
Section o.
Variables (live : list (Z * Z)) (FL : Z) (mem rom : word -> option byte).
Hypothesis HFL : 0 <= FL /\ FL + FS_N < 2 ^ 64.
Hypothesis Hflags : forall p, 0 <= p < FS_N -> rdn tfibsegs mem (Z_to_bv 64 (FL + p)) 1 = Some [Z_to_bv 8 (if mem_pos live CID p then 1 else 0)].
Definition lkeep (x : bv 5) : Prop := x <> 10%bv /\ x <> 12%bv /\ x <> 15%bv /\ x <> 16%bv /\ x <> 17%bv.
Definition lfin (regs : bvmap 5 word) (pc : word) (pos hint' : Z) : Prop :=
exists regs' c', msteps tfibsegs (mkst regs pc mem rom) (mkst regs' (Z_to_bv 64 FS_FOUND) mem rom)
/\ getr regs' 12 = Z_to_bv 64 (hint' - 1) /\ getr regs' 16 = Z_to_bv 64 pos /\ getr regs' 15 = Z_to_bv 64 (FL + pos)
/\ getr regs' 17 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 c' /\ 1 <= c' <= FS_N
/\ forall x, lkeep x -> getr regs' x = getr regs x.
Lemma lfin_steps : forall regs pc regs2 pc2 pos hint',
msteps tfibsegs (mkst regs pc mem rom) (mkst regs2 pc2 mem rom) -> (forall x, lkeep x -> getr regs2 x = getr regs x) ->
lfin regs2 pc2 pos hint' -> lfin regs pc pos hint'.
Proof.
intros regs pc regs2 pc2 pos hint' Hms Hfr (regs' & c' & Hms' & A & Bq & C & D & E & G & K).
exists regs', c'. split; [eapply msteps_trans; [exact Hms | exact Hms']|]. split; [exact A|]. split; [exact Bq|]. split; [exact C|]. split; [exact D|]. split; [exact E|]. split; [exact G|].
intros x Hx. rewrite (K x Hx). apply Hfr. exact Hx.
Qed.
Lemma lfin_pc : forall regs (pc pc' : word) pos hint', bv_unsigned pc = bv_unsigned pc' -> lfin regs pc' pos hint' -> lfin regs pc pos hint'.
Proof. intros regs pc pc' pos hint' H Hf. replace pc with pc' by (apply bv_eq; symmetry; exact H). exact Hf. Qed.
Ltac frame :=
let x := fresh "x" in let Hx := fresh "Hkeep" in
intros x Hx; unfold lkeep in Hx; destruct Hx as (?&?&?&?&?); rewrite ?getr_other by assumption; reflexivity.
Lemma probe_loop : forall fuel h regs pos hint',
fs_probe fuel live CID h = Some (pos, hint') ->
getr regs 12 = Z_to_bv 64 h -> getr regs 13 = Z_to_bv 64 (FS_N - 1) -> getr regs 11 = Z_to_bv 64 FL ->
getr regs 10 = Z_to_bv 64 (Z.of_nat fuel) -> Z.of_nat fuel <= FS_N -> 0 <= h ->
lfin regs (Z_to_bv 64 (FS_LOOP + 0x0)) pos hint'.
Proof.
induction fuel as [|f IH]; intros h regs pos hint' Hp H12 H13 H11 H10 Hfuel Hh; [discriminate Hp|].
destruct HFL as [HFL0 HFL1]. assert (HN : FS_N = 16384) by reflexivity.
pose proof (Z.mod_pos_bound h FS_N ltac:(lia)) as Hm.
cbn [fs_probe] in Hp. rewrite fs_frames_cid in Hp.
pose proof (Hflags (h mod FS_N) Hm) as RD.
destruct (mem_pos live CID (h mod FS_N)) eqn:Hmp.
-
assert (Hf1 : (1 <= f)%nat) by (destruct f; [cbn in Hp; discriminate Hp | lia]).
eapply lfin_steps.
+ norm_pc.
svand F_L0 D_L0 (Z_to_bv 64 (h mod FS_N)); [rewrite (v_and_mask h Hh); reflexivity|].
sv F_L4 D_L4 (Z_to_bv 64 (FL + h mod FS_N)).
steplb1 F_L8 D_L8 RD.
stepbf F_Lc D_Lc.
stepiwv F_L10 D_L10 (Z_to_bv 64 (Z.of_nat f)) ltac:(gr; rwH; imm_norm; rewrite v_addiw_dec by lia; f_equal; lia).
sv F_L14 D_L14 (Z_to_bv 64 (h + 1)).
stepbt F_L18 D_L18.
apply mst_refl.
+ frame.
+ eapply lfin_pc; [| eapply (IH (h + 1))]; [vm_compute; reflexivity | exact Hp | gr; reflexivity | gr; exact H13 | gr; exact H11 | gr; reflexivity | lia | lia].
-
injection Hp as <- <-.
eexists _, (Z.of_nat (S f)). split.
+ norm_pc.
svand F_L0 D_L0 (Z_to_bv 64 (h mod FS_N)); [rewrite (v_and_mask h Hh); reflexivity|].
sv F_L4 D_L4 (Z_to_bv 64 (FL + h mod FS_N)).
steplb1 F_L8 D_L8 RD.
stepbt F_Lc D_Lc.
replace (Z_to_bv 64 FS_FOUND) with (250556%bv : bv 64) by (apply bv_eq; reflexivity). apply mst_refl.
+ split; [gr; rewrite H12; f_equal; lia|]. split; [gr; reflexivity|]. split; [gr; reflexivity|]. split; [gr; reflexivity|].
split; [gr; exact H10|]. split; [lia | frame].
Qed.
End o.
Lemma r_A : RUNTO FS_LOOP ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.
Lemma r_C1 : RUN ssC1 = (eC1, stC1). Proof. vm_compute. reflexivity. Qed.
Lemma r_C2 : forall hi, RUN (ssC2 hi) = (eC2 hi, stC2 hi). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma r_C3 : forall hi, RUN (ssC3 hi) = (eC3 hi, stC3 hi). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma stack_malloc_inv : forall cid S pos S',
apath (stack_malloc cid S) [] (PFake cid pos, S') ->
exists hint', fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S))) = Some (pos, hint') /\
S' = set_fs (mkFS (zupd cid hint' (fs_hint (st_fs S))) ((cid, pos) :: fs_live (st_fs S))) S.
Proof.
intros cid S pos S' H. unfold stack_malloc, bind, get, put, ret in H. cbn [ibind] in H.
destruct (fs_probe (Z.to_nat (fs_frames cid)) (fs_live (st_fs S)) cid (znth 0 cid (fs_hint (st_fs S)))) as [[p h']|] eqn:Hp.
- cbn [ibind apath] in H. injection H as <- <-. exists h'. split; reflexivity.
- cbn [apath] in H. discriminate H.
Qed.
Lemma fs_probe_facts : forall fuel live cid h pos hint',
fs_probe fuel live cid h = Some (pos, hint') -> 0 < fs_frames cid ->
mem_pos live cid pos = false /\ 0 <= pos < fs_frames cid /\ h < hint' /\ pos = (hint' - 1) mod fs_frames cid.
Proof.
induction fuel as [|f IH]; intros live cid h pos hint' Hp HN; [discriminate Hp|].
cbn [fs_probe] in Hp. destruct (mem_pos live cid (h mod fs_frames cid)) eqn:Hm.
- destruct (IH _ _ _ _ _ Hp HN) as (A & Bq & C & D). repeat split; first [assumption | lia].
- injection Hp as <- <-. pose proof (Z.mod_pos_bound h (fs_frames cid) HN). replace (h + 1 - 1) with h by lia. repeat split; first [exact Hm | lia].
Qed.
Lemma combine_seq_nth : forall {X} (l : list X) (d : X) s n, (n < length l)%nat -> In ((s + n)%nat, nth n l d) (combine (seq s (length l)) l).
Proof.
induction l as [|x l IH]; intros d s n Hn; cbn in Hn; [lia|]. cbn [length seq combine].
destruct n as [|n]; [left; rewrite Nat.add_0_r; reflexivity | right]. replace (s + S n)%nat with (S s + n)%nat by lia. apply IH. lia.
Qed.
Lemma In_fs_cells_acells : forall (B : asyms) ly S c, In c (fs_cells S) -> In c (acells B ly S).
Proof. intros B ly S c H. unfold acells. rewrite !in_app_iff. right; right; right; right; right; left. exact H. Qed.
Lemma env_agree_Ereg_app : forall regs l1 l2 k, (k <= 32 + length l1)%nat -> env_agree k (Ereg regs l1) (Ereg regs (l1 ++ l2)).
Proof.
intros regs l1 l2 k Hk. split; [|reflexivity]. intros n Hn.
destruct (Nat.lt_ge_cases n 32) as [L|L].
- unfold Ereg. cbn [ew]. destruct (n <? 32)%nat eqn:E; [reflexivity | apply Nat.ltb_ge in E; lia].
- replace n with (32 + (n - 32))%nat by lia. rewrite !ew_Ereg_extra. rewrite app_nth1 by lia. reflexivity.
Qed.
Lemma val_mem_mod64 : forall (m : word -> option byte) a x, val_mem tfibsegs m a 8 x -> val_mem tfibsegs m a 8 (x mod 2 ^ 64).
Proof.
intros m a x Hv k Hk. rewrite (Hv k Hk). f_equal. f_equal. unfold le_byte, YG0f.le_byte, YO0f.le_byte.
change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma fs_probe_shift : forall fuel live cid h h2 pos hint',
0 < fs_frames cid -> h2 mod fs_frames cid = h mod fs_frames cid ->
fs_probe fuel live cid h = Some (pos, hint') -> fs_probe fuel live cid h2 = Some (pos, h2 + (hint' - h)).
Proof.
induction fuel as [|f IH]; intros live cid h h2 pos hint' HN Hc Hp; [discriminate Hp|].
cbn [fs_probe] in Hp |- *. rewrite Hc. destruct (mem_pos live cid (h mod fs_frames cid)).
- rewrite (IH live cid (h + 1) (h2 + 1) pos hint' HN); [f_equal; f_equal; lia | | exact Hp].
rewrite (Z.add_mod h2 1), (Z.add_mod h 1) by lia. rewrite Hc. reflexivity.
- injection Hp as <- <-. f_equal. f_equal. lia.
Qed.
Lemma memA_windows : forall E a, in_wrange E memA a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
vm_compute in Ht. repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; exact Hw | exfalso; lia] |]). destruct Ht.
Qed.
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? FS_LOOP) && reg_is ss 12 (SOff aH 0) && reg_is ss 13 (SLit (FS_N - 1)) && reg_is ss 11 (SOff aF FS_FLOFF) && reg_is ss 10 (SLit FS_N)
&& reg_is ss 9 (SOff aF 0) && reg_is ss 8 (SOff 2 0) && reg_is ss 2 (SOff 2 (-32)).
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma eA_atoms : ss_atoms_lt 37 eA = true. Proof. vm_compute. reflexivity. Qed.
Lemma C1_facts : ss_pc eC1 = FS_SDFF /\ reg_is eC1 9 s1C1 = true /\ ss_atoms_lt 43 eC1 = true /\ ss_resv eC1 = None /\
match stC1 with RS_stopped (SR_addr _) => True | _ => False end.
Proof. vm_compute. repeat split; reflexivity || exact I. Qed.
Lemma C2_facts : forall hi, ss_pc (eC2 hi) = FS_SDSH /\ reg_is (eC2 hi) 11 a1C2 = true /\ ss_atoms_lt 43 (eC2 hi) = true /\ ss_resv (eC2 hi) = None /\
match stC2 hi with RS_stopped (SR_addr _) => True | _ => False end.
Proof. intros [|]; vm_compute; repeat split; reflexivity || exact I. Qed.
Lemma stC2_match : forall hi (A : Type) (x y : A), match stC2 hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma stC3_match : forall hi (A : Type) (x y : A), match stC3 hi with RS_ecall => x | _ => y end = y. Proof. intros [|] A x y; reflexivity. Qed.
Lemma eC2_split : forall hi, ss_mem (eC2 hi) = nth 0 (ss_mem (eC2 hi)) stkA :: tl (ss_mem (eC2 hi)). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma C3_facts : forall hi, stC3 hi = RS_stopped (SR_jalr (SOff 1 0)) /\ ss_resv (eC3 hi) = None /\
forallb (fun r => reg_is (eC3 hi) r (SOff (Z.to_nat r) 0)) [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] = true /\
reg_is (eC3 hi) 10 (SOff aFF 0) = true /\ reg_is (eC3 hi) 4 (SLit TP) = true.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma s1C1_eq : s1C1 = SAlu ALU_ADD (SOff aF 36864) (SAlu ALU_SLL (SOff aPOS 0) (SLit 6)). Proof. vm_compute. reflexivity. Qed.
Lemma a1C2_eq : a1C2 = SAlu ALU_ADD (SAlu ALU_ADD (SLit SHADOW_OFF) (SAlu ALU_SRL (SOff aFF 0) (SLit 3))) (SLit 0). Proof. vm_compute. reflexivity. Qed.
Lemma s1C1_denot : forall E F pos, bv_unsigned (ew E aF) = F -> bv_unsigned (ew E aPOS) = pos -> 0 <= F -> 0 <= pos ->
F + FS_FROFF + pos * FS_B < 2 ^ 64 -> sv_denot E s1C1 = Z_to_bv 64 (F + FS_FROFF + pos * FS_B).
Proof.
intros E F pos HF Hp HF0 Hp0 Hhi. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E s1C1)). f_equal.
change (bv_unsigned (sv_denot E s1C1)) with (U E s1C1). rewrite (U_zev E s1C1) by (vm_compute; reflexivity).
rewrite s1C1_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HF, Hp, Z.add_0_r. change (Z.land (zcanon 6) 63) with 6.
unfold FS_FROFF, FS_B in *. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 6) with 64.
rewrite (zcanon_small pos) by lia. rewrite (zcanon_small (pos * 64)) by lia. rewrite (zcanon_small (F + 36864)) by lia. apply zcanon_small. lia.
Qed.
Lemma a1C2_denot : forall E FF, bv_unsigned (ew E aFF) = FF -> 0 <= FF < 2 ^ 64 -> sv_denot E a1C2 = Z_to_bv 64 (SHADOW_OFF + FF / 8).
Proof.
intros E FF HFF Hr. rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E a1C2)). f_equal.
change (bv_unsigned (sv_denot E a1C2)) with (U E a1C2). rewrite (U_zev E a1C2) by (vm_compute; reflexivity).
rewrite a1C2_eq. cbn [zev zalu_raw]. unfold rho_of. rewrite HFF, !Z.add_0_r. change (Z.land (zcanon 3) 63) with 3. change (zcanon SHADOW_OFF) with SHADOW_OFF.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold SHADOW_OFF.
pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound FF 8 (2 ^ 61) ltac:(lia) ltac:(lia)).
rewrite (zcanon_small FF) by lia. rewrite (zcanon_small (FF / 8)) by lia. rewrite (zcanon_small (2147450880 + FF / 8)) by lia. apply zcanon_small. lia.
Qed.
Lemma memC1_windows : forall E a, in_wrange E (ss_mem ssC1) a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 39) + 0 <= a < bv_unsigned (ew E 39) + 1) \/
(bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
vm_compute in Ht. repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; exact Hw | exfalso; lia] |]). destruct Ht.
Qed.
Lemma memC2_windows : forall hi E a, in_wrange E (ss_mem (ssC2 hi)) a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 41) + 0 <= a < bv_unsigned (ew E 41) + FS_B) \/
(bv_unsigned (ew E 39) + 0 <= a < bv_unsigned (ew E 39) + 1) \/ (bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
destruct zhi; vm_compute in Ht; repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw | right; right; right; exact Hw | exfalso; lia] |]); destruct Ht.
Qed.
Lemma memC3_windows : forall hi E a, in_wrange E (ss_mem (ssC3 hi)) a ->
(bv_unsigned (ew E 2) + - FS_WIN <= a < bv_unsigned (ew E 2) + 0) \/ (bv_unsigned (ew E 42) + 0 <= a < bv_unsigned (ew E 42) + FS_B / 8) \/
(bv_unsigned (ew E 41) + 0 <= a < bv_unsigned (ew E 41) + FS_B) \/
(bv_unsigned (ew E 39) + 0 <= a < bv_unsigned (ew E 39) + 1) \/ (bv_unsigned (ew E 35) + FS_HOFF <= a < bv_unsigned (ew E 35) + (FS_HOFF + 8)).
Proof.
intros zhi E a Hin. destruct (in_wrange_windows E _ _ Hin) as (b & lo & hi & Ht & Hw).
destruct zhi; vm_compute in Ht; repeat (destruct Ht as [Hq | Ht]; [injection Hq as <- <- <-; cbn [base_val] in Hw; first [left; exact Hw | right; left; exact Hw | right; right; left; exact Hw | right; right; right; left; exact Hw | right; right; right; right; exact Hw | exfalso; lia] |]); destruct Ht.
Qed.
Definition rSTK3 : YP09.region := Eval vm_compute in nth 0 (ss_mem eC3H) stkA.
Definition rSH3 : YP09.region := Eval vm_compute in nth 1 (ss_mem eC3H) stkA.
Definition rFF3 : YP09.region := Eval vm_compute in nth 2 (ss_mem eC3H) stkA.
Definition rFLG3 : YP09.region := Eval vm_compute in nth 3 (ss_mem eC3H) stkA.
Definition rF3 : YP09.region := Eval vm_compute in nth 4 (ss_mem eC3H) stkA.
Lemma eC3_regions : forall hi, nth_error (ss_mem (eC3 hi)) 0 = Some rSTK3 /\ nth_error (ss_mem (eC3 hi)) 1 = Some rSH3 /\ nth_error (ss_mem (eC3 hi)) 2 = Some rFF3 /\
nth_error (ss_mem (eC3 hi)) 3 = Some rFLG3 /\ nth_error (ss_mem (eC3 hi)) 4 = Some rF3.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma rSTK3_shape : YP09.r_base rSTK3 = Some 2%nat /\ YP09.r_wlo rSTK3 = - FS_WIN /\ YP09.r_whi rSTK3 = 0. Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rSH3_shape : YP09.r_base rSH3 = Some aSH /\ YP09.r_wlo rSH3 = 0 /\ YP09.r_whi rSH3 = FS_B / 8 /\
forall j, (j < 1)%nat -> nth_error (YP09.r_chunks rSH3) j = Some (YP09.mkChunk (FS_B / 8 - 8 - 8 * Z.of_nat j) (CVal 8 (SLit 0))).
Proof. vm_compute. repeat split; try reflexivity. intros j Hj. do 1 (destruct j as [|j]; [reflexivity|]). lia. Qed.
Lemma rFF3_shape : YP09.r_base rFF3 = Some aFF /\ YP09.r_wlo rFF3 = 0 /\ YP09.r_whi rFF3 = FS_B /\
nth_error (YP09.r_chunks rFF3) 0 = Some (YP09.mkChunk (FS_B - 8) (CVal 8 (SOff aFLG 0))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rFLG3_shape : YP09.r_base rFLG3 = Some aFLG /\ YP09.r_wlo rFLG3 = 0 /\ YP09.r_whi rFLG3 = 1 /\
nth_error (YP09.r_chunks rFLG3) 0 = Some (YP09.mkChunk 0 (CVal 1 (SLit 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rF3_shape : YP09.r_base rF3 = Some aF /\ YP09.r_wlo rF3 = FS_HOFF /\ YP09.r_whi rF3 = FS_HOFF + 8 /\
nth_error (YP09.r_chunks rF3) 0 = Some (YP09.mkChunk FS_HOFF (CVal 8 (SOff aH2 1))).
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma rSH3_chunk : forall q, 0 <= q < 1 -> In (YP09.mkChunk (8 * q) (CVal 8 (SLit 0))) (YP09.r_chunks rSH3).
Proof.
intros q Hq.
assert (Hc : exists j, (j < 1)%nat /\ q = 1 - 1 - Z.of_nat j) by (exists (Z.to_nat (1 - 1 - q)); split; lia).
destruct Hc as (j & Hj & ->). pose proof (proj2 (proj2 (proj2 rSH3_shape)) j Hj) as X.
replace (8 * (1 - 1 - Z.of_nat j)) with (FS_B / 8 - 8 - 8 * Z.of_nat j) by (change (FS_B / 8) with 8; lia).
exact (nth_error_In _ _ X).
Qed.
Lemma aview_of_val_mem : forall (H : word -> bool) mem a (n : nat) v k, val_mem tfibsegs (mrestrict H mem) a n v -> (k < n)%nat ->
aview tfibsegs H mem (a + Z.of_nat k) = Some (YG0f.le_byte v n k).
Proof.
intros H mem a n v k Hv Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal. rewrite Z_to_bv_unsigned. change (YG0f.le_byte v n k) with (YO0f.le_byte v n k).
unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. unfold YO0f.le_byte. apply Z.mod_pos_bound. lia.
Qed.
Lemma hs_kept_gen : forall (H : word -> bool) (mem mem' : word -> option byte) (P : Z -> Prop),
(forall z : word, ~ P (bv_unsigned z) -> mem' z = mem z) ->
(forall a, P a -> exists m0, apresent H m0 a) ->
forall a, in_band_rw a -> H (Z_to_bv 64 a) = true -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Proof.
intros H mem mem' P MEQ PRES a Ha Hh. rewrite MEQ; [reflexivity|]. intros HP.
rewrite unsigned_lit_small in HP by (unfold in_band_rw, kLowShadowBeg, kLowShadowEnd, kHighShadowBeg, kHighShadowEnd in Ha; lia).
destruct (PRES a HP) as (m0 & Hf & _). rewrite Hh in Hf. discriminate Hf.
Qed.
Lemma frame_addr_cid : forall ly pos, frame_addr ly CID pos = ly_F ly + FS_FROFF + pos * FS_B.
Proof. intros ly pos. unfold frame_addr, fs_frame_off, FS_FROFF, kFakeFramesOff, CID. change (Z.shiftl 1 kStackSizeLog) with 1048576. change (fs_frame_bytes 0) with FS_B. unfold FS_B. lia. Qed.
Lemma flag_addr_cid : forall ly pos, flag_addr ly CID pos = ly_F ly + FS_FLOFF + pos.
Proof. intros ly pos. unfold flag_addr, fs_flag_off, FS_FLOFF, kFakeFlagsOff, CID. change (fs_flags_off 0) with (4096 - 4096). lia. Qed.
End g.
End SM0Tbl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG0s YG0t YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YE34 YF0l YF0m YF0x YE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN32 YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YF0v.
Import SM0Tbl.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Theorem tfib_stack_malloc_at : forall ly S (W : world tfibsegs) regs mem md pos S',
ecall_pre tfibsegs B ly S W regs mem md ->
count_cid CID (frames S) < fs_frames CID ->
apath (stack_malloc CID S) [] (PFake CID pos, S') ->
SRr tfibsegs W (cfg_at tfibsegs FS_ENTRY regs mem md)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = cfg_at tfibsegs (raZ regs) regs' mem' md' /\
AR tfibsegs B ly S' W mem' md' /\ aregs_preserved regs regs' /\ same_but_materialized md md' /\
getr regs' 10 = w64 (frame_addr ly CID pos) /\
zero_shadow (aview tfibsegs (w_H W) mem') SHADOW_OFF (frame_addr ly CID pos) (fs_frame_bytes CID) /\
rdword (aview tfibsegs (w_H W) mem') (frame_addr ly CID pos + fs_frame_bytes CID - 8) = Some (flag_addr ly CID pos) /\
(forall a, frame_addr ly CID pos <= a < frame_addr ly CID pos + fs_frame_bytes CID -> apresent (w_H W) mem' a) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ aowned B ly S a -> ~ aowned B ly S' a -> ~ (spZ regs - ESTACK <= a < spZ regs) ->
aview tfibsegs (w_H W) mem' a = aview tfibsegs (w_H W) mem a) /\
(forall a, spZ regs - ESTACK <= a < spZ regs -> apresent (w_H W) mem' a)).
Proof.
intros ly S W regs mem md pos S' HPRE Hcnt Hpath.
pose proof HPRE as (HAR & Hra & Hal16 & Hslo & Htop & HpresE & Hgp & Htp). unfold ESTACK in Hslo, HpresE.
pose proof YF0x.Hwx_tfa as Hwx.
destruct (stack_malloc_inv CID S pos S' Hpath) as (hint' & Hprobe & HS'eq).
set (hints := fs_hint (st_fs S)) in *. set (live := fs_live (st_fs S)) in *. set (hint := znth 0 CID hints) in *.
assert (HNN : fs_frames CID = FS_N) by exact fs_frames_cid. assert (HN : FS_N = 16384) by reflexivity.
pose proof (proj1 HAR) as M.
pose proof (wfs_hints _ (wf_fakestack _ _ _ _ _ (am_wf _ _ _ _ M))) as [Hlen Hpos0]. fold hints in Hlen, Hpos0.
assert (Hh0 : 0 <= hint).
{ unfold hint, znth. destruct (Nat.lt_ge_cases (Z.to_nat CID) (length hints)) as [L|L]; [exact (proj1 (Forall_forall _ _) Hpos0 _ (nth_In _ 0 L)) | rewrite nth_overflow by exact L; lia]. }
destruct (fs_probe_facts _ _ _ _ _ _ Hprobe ltac:(rewrite HNN, HN; lia)) as (Hfree & Hposr & Hhh & Hposeq). rewrite HNN in Hposr, Hposeq.
pose proof (am_layout B ly S _ M) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg). unfold kHighMemBeg, kHighMemEnd in Lbeg, Lhi.
pose proof (img_cover_of_ledger ly _ _ (proj1 (proj2 HAR))) as IMG.
assert (ZI : forall e, In e (owned_extents ly) -> zone3 (fst e) (snd e)).
{ intros e Hex. pose proof (proj1 (Forall_forall _ _) (lo_app ly HLY) e Hex) as IA. cbv beta in IA.
assert (D9 : zdisjoint e (ly_img ly)).
{ pose proof (lo_disj ly HLY) as PD.
exact (pairwise_In zdisjoint (static_extents ly) e (ly_img ly) (owned_extents ly ++ [(ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)]) [ly_img ly]
ltac:(unfold static_extents; rewrite <- app_assoc; reflexivity) PD ltac:(apply in_app_iff; left; exact Hex) ltac:(left; reflexivity)). }
assert (SZ : 0 <= snd e).
{ unfold owned_extents in Hex. cbn [In] in Hex. decompose [or] Hex; subst; cbn [snd];
unfold kPrimResvSize, kPtrArrayResv, kThreadObjSize, kFakeStackSize, kNodesBlockSize, kStoreBlockSize; lia. }
exact (zone3_intro ly (fst e) (snd e) IMG SZ IA ltac:(destruct e; exact D9)). }
pose proof (ZI (ly_T ly, kThreadObjSize) ltac:(unfold owned_extents; cbn; tauto)) as (HT1 & HT2 & HTz).
pose proof (ZI (ly_F ly, kFakeStackSize) ltac:(unfold owned_extents; cbn; tauto)) as (HF1 & HF2 & HFz).
pose proof (ZI (ly_C ly, 256) ltac:(unfold owned_extents; cbn; tauto)) as (HC1 & HC2 & HCz).
pose proof (ZI (ly_D ly, 4096) ltac:(unfold owned_extents; cbn; tauto)) as (HD1 & HD2 & HDz).
cbn [fst snd] in HT1, HT2, HTz, HF1, HF2, HFz, HC1, HC2, HCz, HD1, HD2, HDz.
ceil; unfold ASAN_CEIL, kThreadObjSize, kFakeStackSize in HT1, HT2, HF1, HF2, HC1, HC2, HD1, HD2.
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, kThreadObjSize, kFakeStackSize in HTz, HFz, HCz, HDz.
assert (ZONE : exists hi : bool, if hi then 17594333495296 <= ly_F ly /\ ly_F ly + 11571200 <= alloc_ceiling else 6275072 <= ly_F ly /\ ly_F ly + 11571200 <= 2147446784).
{ destruct HFz as [X|[X|X]]; [exfalso; clear - X HF1; lia | exists false; exact X | exists true; exact X]. }
destruct ZONE as [hi HZ].
clear HF1 HF2. assert (HF1 : 6275072 <= ly_F ly) by (clear - HZ; destruct hi; lia).
assert (HF2 : ly_F ly + 11571200 <= 140737479966720) by (clear - HZ; destruct hi; [ceil; lia | lia]).
assert (CE : alloc_ceiling <= 140737479966720) by (ceil; lia).
apply (fun X => Z.le_trans _ _ _ X CE) in HT2. apply (fun X => Z.le_trans _ _ _ X CE) in HC2. apply (fun X => Z.le_trans _ _ _ X CE) in HD2.
pose proof (lo_T_al ly HLY) as HTal. pose proof (lo_F_al ly HLY) as HFal. pose proof (lo_D_al ly HLY) as HDal. pose proof (lo_C_al ly HLY) as HCal.
unfold page_aligned in HTal, HFal, HDal.
pose proof (lo_disj ly HLY) as PW. unfold static_extents, owned_extents in PW. cbn [app pairwise] in PW.
destruct PW as (_ & _ & PWT & PWF & _ & _ & PWC & PWD & _).
assert (DTF : zdisjoint (ly_T ly, kThreadObjSize) (ly_F ly, kFakeStackSize)) by (exact (Forall_inv PWT)).
assert (DTC : zdisjoint (ly_T ly, kThreadObjSize) (ly_C ly, 256)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT))))).
assert (DTD : zdisjoint (ly_T ly, kThreadObjSize) (ly_D ly, 4096)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT)))))).
assert (DTS : zdisjoint (ly_T ly, kThreadObjSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWT))))))).
assert (DFC : zdisjoint (ly_F ly, kFakeStackSize) (ly_C ly, 256)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail PWF)))).
assert (DFD : zdisjoint (ly_F ly, kFakeStackSize) (ly_D ly, 4096)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWF))))).
assert (DFS : zdisjoint (ly_F ly, kFakeStackSize) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail (Forall_inv_tail PWF)))))).
assert (DCD : zdisjoint (ly_C ly, 256) (ly_D ly, 4096)) by (exact (Forall_inv PWC)).
assert (DCS : zdisjoint (ly_C ly, 256) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv (Forall_inv_tail PWC))).
assert (DDS : zdisjoint (ly_D ly, 4096) (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly)) by (exact (Forall_inv PWD)).
clear PWT PWF PWC PWD. unfold zdisjoint, kThreadObjSize, kFakeStackSize in DTF, DTC, DTD, DTS, DFC, DFD, DFS, DCD, DCS, DDS. cbn [fst snd] in DTF, DTC, DTD, DTS, DFC, DFD, DFS, DCD, DCS, DDS.
set (T := ly_T ly) in *. set (C := ly_C ly) in *. set (D := ly_D ly) in *. set (F := ly_F ly) in *.
set (sp0 := spZ regs) in *. set (H := w_H W) in *.
assert (Hsp44 : 2 ^ 44 <= sp0 <= 2 ^ 47) by (clear - Hslo Htop Lbeg Lhi; lia).
assert (HTPv : as_tp B = TP) by (rewrite (ts_tp B TB); reflexivity).
assert (HTSDv : ly_tsd ly = TSD) by (rewrite (am_tsd B ly S _ M), (ts_tsd B TB); reflexivity).
assert (VT0 : val_mem tfibsegs (mrestrict H mem) TP 8 F).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (ATp 0) 8 (AF 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VT8 : val_mem tfibsegs (mrestrict H mem) (TP + 8) 8 D).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (ATp 8) 8 (AD 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VD24 : val_mem tfibsegs (mrestrict H mem) (D + 24) 8 TP).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (AD 24) 8 (ATp 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTPv, !Z.add_0_r in V. exact V. }
assert (VTSD : val_mem tfibsegs (mrestrict H mem) TSD 8 C).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (ATsd 0) 8 (AC 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite HTSDv, !Z.add_0_r in V. exact V. }
assert (VC152 : val_mem tfibsegs (mrestrict H mem) (C + 152) 8 T).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (AC 152) 8 (AT 0) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. rewrite !Z.add_0_r in V. exact V. }
assert (VT48 : val_mem tfibsegs (mrestrict H mem) (T + 48) 8 0x5da128).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (AT 48) 8 (ANum 0x5da128) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. exact V. }
assert (VT56 : val_mem tfibsegs (mrestrict H mem) (T + 56) 8 0x5da204).
{ pose proof (tfib_const_lookup_sym B TB ly S H mem (AT 56) 8 (ANum 0x5da204) M ltac:(vm_compute; reflexivity)) as V. cbn [aeval] in V. exact V. }
assert (CELL : forall e (ww : nat) z, In (ACell e ww (AV (ANum z))) (fs_cells S) -> val_mem tfibsegs (mrestrict H mem) (aeval B ly e) ww z).
{ intros e ww z Hin. pose proof (cell_holds_val_mem B ly H mem e ww (ANum z) (proj1 (Forall_forall _ _) (am_cells B ly S _ M) _ (In_fs_cells_acells B ly S _ Hin))) as V. exact V. }
assert (VF88 : val_mem tfibsegs (mrestrict H mem) (F + 88) 8 20) by (exact (CELL (AF 88) 8%nat 20 ltac:(left; reflexivity))).
assert (VF96 : val_mem tfibsegs (mrestrict H mem) (F + 96) 1 0) by (exact (CELL (AF 96) 1%nat 0 ltac:(right; left; reflexivity))).
assert (VFH : val_mem tfibsegs (mrestrict H mem) (F + FS_HOFF) 8 hint).
{ refine (CELL (AF FS_HOFF) 8%nat hint _). right; right. unfold fs_cells.
change (AF FS_HOFF) with (AF (8 * Z.of_nat 0%nat)). unfold hint, znth. change (Z.to_nat CID) with 0%nat.
apply (in_map (fun iv : nat * Z => z8 (AF (8 * Z.of_nat (fst iv))) (snd iv)) _ (0%nat, nth 0 hints 0)).
fold hints. rewrite <- Hlen. apply (combine_seq_nth hints 0 0 0). lia. }
set (hm := hint mod 2 ^ 64). assert (Hhm : 0 <= hm < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
assert (VFH' : val_mem tfibsegs (mrestrict H mem) (F + FS_HOFF) 8 hm) by (exact (val_mem_mod64 _ _ _ VFH)).
assert (Hprobe' : fs_probe (Z.to_nat FS_N) live CID hm = Some (pos, hm + (hint' - hint))).
{ rewrite <- HNN. apply (fs_probe_shift _ _ _ hint); [rewrite HNN; lia | | exact Hprobe].
rewrite HNN. subst hm. change FS_N with (2 ^ 14). rewrite <- (Z.mod_mod_divide hint (2 ^ 64) (2 ^ 14)) by (first [exists (2 ^ (64 - 14)); reflexivity | lia]). reflexivity. }
set (E := Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm]).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r) by (intros; subst E; apply ew_Ereg_nat; assumption).
assert (E2 : bv_unsigned (ew E 2) = sp0) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (E32 : ew E 32 = w64 T) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 C) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 D) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 F) by (subst E; exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = w64 hm) by (subst E; exact (ew_Ereg_extra regs _ 4)).
assert (U32 : bv_unsigned (ew E 32) = T) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = C) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = D) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = F) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = hm) by (rewrite E36; apply unsigned_lit_small; lia).
assert (DEN : forall n c z, bv_unsigned (ew E n) = z -> 0 <= z + c < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (z + c)).
{ intros n c z Hn Hr. cbn [sv_denot]. rewrite Hn. reflexivity. }
assert (DEN0 : forall n z, bv_unsigned (ew E n) = z -> 0 <= z < 2 ^ 64 -> sv_denot E (SOff n 0) = Z_to_bv 64 z).
{ intros n z Hn Hr. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (HS0 : st_ok tfibsegs E ssA (restrict H (mkst regs (Z_to_bv 64 FS_ENTRY) mem (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA.
apply (st_ok_regs tfibsegs E (mkSS FS_ENTRY sr_atoms memA None (mkFacts factsA [] [])) _ regsA).
2:{ apply reg_cases_lit. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [
match goal with |- sv_denot _ (sr_get ?a ?r) = sv_denot _ (sr_get ?b ?r2) =>
let v := eval vm_compute in (sr_get a r) in change (sr_get a r) with v;
let v2 := eval vm_compute in (sr_get b r2) in change (sr_get b r2) with v2 end;
first [ reflexivity
| (cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; rewrite (EEreg 4%nat 4%bv eq_refl), Htp, HTPv; reflexivity) ] |]).
destruct Hr. }
unfold memA. apply (entry_st_ok_full tfibsegs); change (Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm]) with E.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- assert (RO : Forall (region_ok tfibsegs E (mrestrict H mem)) (map ro_region fsA_rodata)) by (exact (rodata_ok B TB fsA_rodata ly S H mem E (fsA_rodata_chk ly) M)).
assert (CK : forall base off (nn : N) e v, sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N nn) -> Z.of_N nn <= 8 ->
val_mem tfibsegs (mrestrict H mem) (base + off) (N.to_nat nn) v -> YP09.chunk_ok tfibsegs E (mrestrict H mem) base (YP09.mkChunk off (CVal nn e))).
{ intros. eapply (chunk_ok_val tfibsegs E); eassumption. }
change (stkA :: rTSD :: rTP0 :: rTP8 :: rT :: rC :: rD :: rF :: map ro_region fsA_rodata) with ([stkA; rTSD; rTP0; rTP8; rT; rC; rD; rF] ++ map ro_region fsA_rodata).
apply Forall_app. split; [|exact RO]. repeat apply Forall_cons; try apply Forall_nil.
+ unfold stkA, FS_WIN. apply (region_ok_stack tfibsegs E _ 2 sp0 (- 208)); [exact E2 | lia | lia |].
intros a Ha. apply (YCe5.apresent_writable tfibsegs). apply HpresE. subst sp0. lia.
+ unfold rTSD, aC, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold TSD.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ C); [apply (DEN0 _ C U33); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VTSD].
+ unfold rTP0, aF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold TP.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ F); [apply (DEN0 _ F U35); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VT0].
+ unfold rTP8, aD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. unfold TP.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK 0 _ 8%N _ D); [apply (DEN0 _ D U34); lia | cbn; lia | cbn; lia | rewrite Z.add_0_l; exact VT8].
+ unfold rT, aT, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [apply (CK T _ 8%N _ 0x5da128); [reflexivity | cbn; lia | cbn; lia | exact VT48]|].
apply Forall_cons; [apply (CK T _ 8%N _ 0x5da204); [reflexivity | cbn; lia | cbn; lia | exact VT56] | apply Forall_nil].
+ unfold rC, aC, aT, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U33.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK C _ 8%N _ T); [apply (DEN0 _ T U32); lia | cbn; lia | cbn; lia | exact VC152].
+ unfold rD, aD, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U34.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (CK D _ 8%N _ TP); [reflexivity | cbn; unfold TP; lia | cbn; lia | exact VD24].
+ unfold rF, aF, aH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U35. unfold FS_HOFF.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (YF0x.apresent_writable H mem); [unfold TFIB_IMG_END; lia|].
replace (F + o) with (F + 0 + Z.of_nat (Z.to_nat (o - 0))) by lia.
eapply (YF0x.mbyte_high_apresent H mem); [unfold TFIB_IMG_END; lia|]. apply VFH'. lia. }
apply Forall_cons; [apply (CK F _ 8%N _ hm); [apply (DEN0 _ hm U36); lia | cbn; lia | cbn; lia | exact VFH']|].
apply Forall_cons; [apply (CK F _ 8%N _ 20); [reflexivity | cbn; lia | cbn; lia | exact VF88]|].
apply Forall_cons; [apply (CK F _ 1%N _ 0); [reflexivity | cbn; lia | cbn; lia | exact VF96] | apply Forall_nil].
- apply pairwise_disjoint_of_extents. unfold stkA, rTSD, rTP0, rTP8, rT, rC, rD, rF, aT, aC, aD, aF, aH, fsA_rodata, icpt_rodata, ro_region, extent_of_region, FS_WIN, FS_HOFF, TSD, TP.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, U32, U33, U34, U35.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; first [ clear - HT1 HTz; lia | clear - HC1 HCz; lia | clear - HD1 HDz; lia | clear - HF1 HFz; lia
| clear DTF DTC DTD DTS DFC DFD DFS DCD DCS DDS HTz HFz HCz HDz; lia | clear HTz HFz HCz HDz; lia ].
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok, aT, aC, aD, aF, aH. cbn [af_lo af_hi af_al2].
rewrite E2, U32, U33, U34, U35, U36. ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kFakeStackSize, FS_WIN.
change (2 ^ 4) with 16. change (2 ^ 12) with 4096. change (2 ^ 3) with 8. change (2 ^ 0) with 1.
repeat split; first [exact Hal16 | exact HTal | exact HCal | exact HDal | exact HFal | apply Z.mod_1_r | clear HTz HFz HCz HDz; lia]. }
idtac "CHECKPOINT-1b".
clear DTF DTC DTD DTS DFC DFD DCD DCS DDS.
eapply SRr_bind; [apply (fs_phase_to W E FS_LOOP _ _ _ _ _ HS0 r_A)|].
cbv beta. intros Wa ca _ (-> & msA & matA & -> & HSA & HFA & HFrA).
assert (MEQA : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> ~ (F + 0 <= bv_unsigned z < F + 0 + 8) -> ms_mem msA z = mem z).
{ intros z Hz1 Hz2. apply HFA. intros Hin. destruct (memA_windows E _ Hin) as [Hw|Hw]; [rewrite E2 in Hw; unfold FS_WIN in Hw; lia | rewrite U35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFA HFrA.
pose proof shapeA_ok as SH. unfold shapeA in SH.
apply andb_prop in SH as [SH R2]. apply andb_prop in SH as [SH R8]. apply andb_prop in SH as [SH R9]. apply andb_prop in SH as [SH R10].
apply andb_prop in SH as [SH R11]. apply andb_prop in SH as [SH R13]. apply andb_prop in SH as [Rpc R12]. apply Z.eqb_eq in Rpc.
assert (RD : forall (r : bv 5) v, reg_is eA (bv_unsigned r) v = true -> getr (ms_regs msA) r = sv_denot E v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H E eA msA r HSA). }
pose proof (st_ok_restrict_mkst tfibsegs H E _ _ HSA eq_refl) as HshapeA. rewrite Rpc in HshapeA.
assert (FLAGS : forall p, 0 <= p < FS_N -> rdn tfibsegs (mrestrict H (ms_mem msA)) (Z_to_bv 64 (F + FS_FLOFF + p)) 1 = Some [Z_to_bv 8 (if mem_pos live CID p then 1 else 0)]).
{ intros p Hp. pose proof (am_flags B ly S _ M CID p ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hp)) as Hf.
unfold flag_addr, fs_flag_off in Hf. change (fs_flags_off CID) with (4096 - kFakeFlagsOff) in Hf. unfold kFakeFlagsOff in Hf. fold F in Hf.
apply (proj2 (rdn_mbytes tfibsegs _ 1 _ _)). split; [reflexivity|]. intros i Hi. replace i with 0%nat by lia. cbn [nth_error Z.of_nat]. rewrite Z.add_0_r.
unfold FS_FLOFF. replace (F + 4096 + p) with (F + (4096 + (4096 - 4096) + p)) by lia.
apply (YF0x.aview_byte H). rewrite (aview_same H mem (ms_mem msA)); [exact Hf | apply MEQA; rewrite unsigned_lit_small by lia; unfold sp0 in *; lia]. }
destruct (probe_loop live (F + FS_FLOFF) (mrestrict H (ms_mem msA)) (seg_rom tfibsegs) ltac:(unfold FS_FLOFF, FS_N; lia) FLAGS
(Z.to_nat FS_N) hm (ms_regs msA) pos (hm + (hint' - hint)) Hprobe'
ltac:(rewrite (RD 12%bv _ R12); apply (DEN0 _ hm U36); lia) ltac:(rewrite (RD 13%bv _ R13); reflexivity)
ltac:(rewrite (RD 11%bv _ R11); unfold FS_FLOFF; apply (DEN _ _ F U35); lia) ltac:(rewrite (RD 10%bv _ R10); rewrite Z2Nat.id by (unfold FS_N; lia); reflexivity)
ltac:(rewrite Z2Nat.id by (unfold FS_N; lia); lia) ltac:(lia))
as (regsL & cL & HmsL & L12 & L16 & L15 & L17 & L10 & HcL & LK).
rewrite HshapeA. eapply (SRr_msteps tfibsegs Hwx W); [rewrite restrict_mkst_fx; exact HmsL|].
intros mdL HsbmL _. cbn [ms_mem mkst]. rewrite unrestrict_mkst_mrestrict.
rewrite (same_but_materialized_wvb _ mdL HsbmL), wvb_collapse. clear HsbmL.
set (dlt := hint' - hint) in *. assert (Hdlt : 1 <= dlt) by (subst dlt; lia).
set (FLG := F + FS_FLOFF + pos). set (FF := frame_addr ly CID pos). set (SH := shadow_addr FF).
assert (HFF : FF = F + 36864 + pos * 64) by (subst FF; rewrite frame_addr_cid; reflexivity).
assert (HB : FS_B = 64) by reflexivity. assert (HFLO : FS_FLOFF = 4096) by reflexivity.
assert (HFLG : FLG = F + 4096 + pos) by (subst FLG; reflexivity).
assert (HFFr : 6275072 <= FF /\ FF + 64 <= F + kFakeStackSize /\ FF mod 64 = 0).
{ rewrite HFF. unfold kFakeStackSize. split; [lia|]. split; [lia|].
replace (F + 36864 + pos * 64) with ((F / 4096 * 64 + 576 + pos * 1) * 64); [apply Z_mod_mult|].
pose proof (Z.div_mod F 4096 ltac:(lia)). lia. }
pose proof (Z.div_mod FF 8 ltac:(lia)) as HFF8. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as HFF8'.
assert (HF8m : F mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (F / 4096 * 512); pose proof (Z.div_mod F 4096 ltac:(lia)); lia).
pose proof (Z.div_mod F 8 ltac:(lia)) as HF8. rewrite HF8m, Z.add_0_r in HF8. clear HF8m.
assert (HSH : SH = SHADOW_OFF + FF / 8) by reflexivity. unfold SHADOW_OFF in HSH.
assert (HSHr : SM0Tbl.shLO hi <= SH /\ SH + 8 <= SM0Tbl.shHI hi + 8).
{ rewrite HSH. unfold SM0Tbl.shLO, SM0Tbl.shHI, SM0Tbl.FS_B, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFIB_IMG_END.
clear - HZ HFF HFFr HFF8 HFF8' Hposr HN. ceil. unfold kFakeStackSize in *. change (64 / 8) with 8. change (6275072 / 8) with 784384. destruct hi; cbn -[Z.div Z.add Z.sub Z.mul]; lia. }
assert (HSHe : 2148213760 <= SH /\ SH + 8 <= 17594333495296).
{ clear - HSHr. unfold SM0Tbl.shLO, SM0Tbl.shHI, SM0Tbl.FS_B, kHighShadowBeg, kHighShadowEnd, kLowShadowBeg, kLowShadowEnd, TFIB_IMG_END in HSHr. change (64 / 8) with 8 in HSHr. change (6275072 / 8) with 784384 in HSHr. destruct hi; cbn -[Z.div Z.add Z.sub Z.mul] in HSHr; lia. }
assert (HSHF : SH + 8 <= F \/ F + 11571200 <= SH).
{ rewrite HSH. clear - HZ HFF HFFr HFF8 HFF8' Hposr HN. unfold kFakeStackSize in *. destruct hi; [left | right]; lia. }
set (EC := Ereg regs [w64 T; w64 C; w64 D; w64 F; w64 hm; Z_to_bv 64 (hm + dlt - 1); w64 pos; w64 FLG; Z_to_bv 64 cL; w64 FF; w64 SH]).
assert (AGR : env_agree 37 E EC).
{ subst E EC. apply (env_agree_Ereg_app regs [w64 T; w64 C; w64 D; w64 F; w64 hm] [Z_to_bv 64 (hm + dlt - 1); w64 pos; w64 FLG; Z_to_bv 64 cL; w64 FF; w64 SH] 37). cbn. lia. }
assert (ECreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EC i = getr regs r) by (intros; subst EC; apply ew_Ereg_nat; assumption).
assert (EC2 : bv_unsigned (ew EC 2) = sp0) by (rewrite (ECreg 2%nat 2%bv eq_refl); reflexivity).
assert (V35 : bv_unsigned (ew EC 35) = F) by (subst EC; rewrite (ew_Ereg_extra regs _ 3); cbn [nth]; apply unsigned_lit_small; lia).
assert (V37 : ew EC 37 = Z_to_bv 64 (hm + dlt - 1)) by (subst EC; exact (ew_Ereg_extra regs _ 5)).
assert (V38 : bv_unsigned (ew EC 38) = pos) by (subst EC; rewrite (ew_Ereg_extra regs _ 6); cbn [nth]; apply unsigned_lit_small; lia).
assert (V39 : bv_unsigned (ew EC 39) = FLG) by (subst EC; rewrite (ew_Ereg_extra regs _ 7); cbn [nth]; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (V40 : ew EC 40 = Z_to_bv 64 cL) by (subst EC; exact (ew_Ereg_extra regs _ 8)).
assert (V41 : bv_unsigned (ew EC 41) = FF) by (subst EC; rewrite (ew_Ereg_extra regs _ 9); cbn [nth]; apply unsigned_lit_small; unfold kFakeStackSize in *; lia).
assert (V42 : bv_unsigned (ew EC 42) = SH) by (subst EC; rewrite (ew_Ereg_extra regs _ 10); cbn [nth]; apply unsigned_lit_small; lia).
assert (DC0 : forall n z, bv_unsigned (ew EC n) = z -> 0 <= z < 2 ^ 64 -> sv_denot EC (SOff n 0) = Z_to_bv 64 z).
{ intros n z Hn Hr. cbn [sv_denot]. rewrite Hn, Z.add_0_r. reflexivity. }
assert (INA : forall x l1 l2 l3 (l4 : list (aexp * Z)), In x l4 -> In x (l1 ++ l2 ++ l3 ++ l4)) by (intros; rewrite !in_app_iff; tauto).
assert (PRF : forall a, F <= a < F + kFakeStackSize -> apresent H mem a).
{ intros a Ha. pose proof (proj1 (Forall_forall _ _) (am_areas B ly S _ M) (AF 0, kFakeStackSize) ltac:(unfold aareas; apply INA; left; reflexivity)) as V.
specialize (V (a - F) ltac:(cbn [snd]; clear - Ha; lia)). cbn [fst aeval] in V. replace (ly_F ly + 0 + (a - F)) with a in V by (subst F; lia).
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [| exfalso; apply V; unfold aview; rewrite Hb; reflexivity].
eapply (YF0x.mbyte_high_apresent H mem a); [clear - Ha HF1 HF2; unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hb]. }
assert (PRS : forall a, shadow_addr (F + kFakeFramesOff) <= a < shadow_addr (F + kFakeFramesOff) + 1441792 -> apresent H mem a).
{ intros a Ha. pose proof (proj1 (Forall_forall _ _) (am_areas B ly S _ M) (ASh (AF kFakeFramesOff), (kFakeStackSize - kFakeFramesOff) / 8) ltac:(unfold aareas; apply INA; do 5 right; left; reflexivity)) as V.
change ((kFakeStackSize - kFakeFramesOff) / 8) with 1441792 in V.
specialize (V (a - shadow_addr (F + kFakeFramesOff)) ltac:(cbn [snd]; clear - Ha; lia)). cbn [fst aeval] in V.
replace (shadow_addr (ly_F ly + kFakeFramesOff) + (a - shadow_addr (F + kFakeFramesOff))) with a in V by (subst F; lia).
destruct (mbyte tfibsegs (mrestrict H mem) a) as [b|] eqn:Hb; [| exfalso; apply V; unfold aview; rewrite Hb; reflexivity].
unfold shadow_addr, kFakeFramesOff, SHADOW_OFF in Ha. replace ((F + (4096 + 32768)) / 8) with (F / 8 + 4608) in Ha by (replace (F + (4096 + 32768)) with ((F / 8 + 4608) * 8) by (clear - HF8; lia); rewrite Z_div_mult by lia; reflexivity).
eapply (YF0x.mbyte_high_apresent H mem a); [clear - Ha HF1 HF2 HF8; unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hb]. }
clear INA.
rewrite HshapeA in HSA. rewrite restrict_mkst_fx in HSA.
assert (HSC1 : st_ok tfibsegs EC ssC1 (restrict H (mkst regsL (Z_to_bv 64 FS_FOUND) (ms_mem msA) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- ssC1_eq. unfold preC1. apply st_ok_add_fact; [| reflexivity | unfold aPOS; rewrite V38; unfold FS_N; lia].
apply (st_ok_set_regs_mem tfibsegs 37 E EC eA (ms_regs msA) regsL (Z_to_bv 64 FS_LOOP) FS_FOUND
(mrestrict H (ms_mem msA)) (mrestrict H (ms_mem msA)) memC1 updC1 HSA AGR eA_atoms).
- vm_compute. reflexivity.
- intros r Hr. apply LK. unfold lkeep. repeat split; intros ->; vm_compute in Hr; discriminate Hr.
- unfold updC1, aH2, aPOS, aFLG, aCNT. repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; (split; [reflexivity|]).
+ rewrite L12, (DC0 _ ((hm + dlt - 1) mod 2 ^ 64)); [symmetry; apply Z_to_bv64_of_mod | rewrite V37, Z_to_bv_unsigned; reflexivity | apply Z.mod_pos_bound; lia].
+ rewrite L16. symmetry. apply DC0; [exact V38 | lia].
+ rewrite L15. rewrite (DC0 _ FLG V39); [subst FLG; reflexivity | unfold kFakeStackSize in *; lia].
+ rewrite L17. reflexivity.
+ rewrite L10. cbn [sv_denot]. rewrite V40, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
-
pose proof (st_ok_agree tfibsegs 37 E EC eA _ HSA AGR eA_atoms) as HSA'.
pose proof (st_ok_mem_ok tfibsegs EC eA _ HSA') as (WFA & ROKA & PDA).
split; [vm_compute; reflexivity|]. split.
+ unfold memC1. apply Forall_cons; [refine (proj1 (Forall_forall _ _) ROKA (nth 0 (ss_mem eA) stkA) _); apply nth_In; vm_compute; repeat constructor|].
apply Forall_cons.
{ unfold rFLG, aFLG, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V39.
assert (Hfb : mbyte tfibsegs (mrestrict H (ms_mem msA)) FLG = Some (Z_to_bv 8 0)).
{ pose proof (FLAGS pos Hposr) as X. rewrite Hfree in X. apply (proj1 (rdn_mbytes tfibsegs _ 1 _ _)) in X as [_ X]. specialize (X 0%nat ltac:(lia)).
cbn [nth_error Z.of_nat] in X. rewrite Z.add_0_r in X. subst FLG. exact X. }
split; [unfold kFakeStackSize in *; lia|]. split; [unfold kFakeStackSize in *; lia|]. split.
{ intros o Ho. replace (FLG + o) with FLG by lia. eapply YF0x.mbyte_high_writable; [unfold TFIB_IMG_END, kFakeStackSize in *; lia | exact Hfb]. }
apply Forall_cons; [|apply Forall_nil]. intros i Hi. cbn [YP09.c_len YP09.cv_len YP09.c_off YP09.c_val Z.of_N] in Hi |- *.
exists (Z_to_bv 8 0). split; [cbn; replace i with 0 by lia; reflexivity | replace (FLG + 0 + i) with FLG by lia; exact Hfb]. }
apply Forall_forall. intros r Hr. apply in_map_iff in Hr as (i & <- & Hi). refine (proj1 (Forall_forall _ _) ROKA _ _). apply nth_In.
assert (Hi15 : (i < 15)%nat) by (clear - Hi; cbn in Hi; lia). eapply Nat.lt_le_trans; [exact Hi15|]. vm_compute. repeat constructor.
+ apply pairwise_disjoint_of_extents. let l' := eval vm_compute in memC1 in change memC1 with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EC2, ?V35, ?V39.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hsp44 HF1 HF2 Lbeg Hslo Htop Hposr HN HFLG DFS. unfold kFakeStackSize in *. repeat split; lia. }
idtac "CHECKPOINT-3".
eapply SRr_bind; [apply (fs_phase W EC ssC1 _ _ _ _ HSC1 r_C1)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HFm1 & HFrm1). rewrite ?wvb_wvb in *. cbn [stC1] in HS1.
assert (MEQ1 : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> bv_unsigned z <> FLG -> ~ (F + 0 <= bv_unsigned z < F + 0 + 8) -> ms_mem ms1 z = ms_mem msA z).
{ intros z Hz1 Hz2 Hz3. apply HFm1. intros Hin. destruct (memC1_windows EC _ Hin) as [Hw|[Hw|Hw]]; [rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm1 HFrm1.
pose proof C1_facts as (PC1 & R9C1 & AT1 & RV1 & _).
pose proof (st_ok_restrict_mkst tfibsegs H EC _ _ HS1 RV1) as Hshape1. rewrite PC1 in Hshape1. rewrite Hshape1. rewrite Hshape1 in HS1. clear Hshape1.
assert (RD1 : forall (r : bv 5) v, reg_is eC1 (bv_unsigned r) v = true -> getr (ms_regs ms1) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H EC eC1 (mkst (ms_regs ms1) (Z_to_bv 64 FS_SDFF) (ms_mem ms1) (seg_rom tfibsegs)) r HS1). }
pose proof (RD1 9%bv s1C1 R9C1) as G9. rewrite (s1C1_denot EC F pos V35 V38 ltac:(lia) ltac:(lia) ltac:(unfold FS_FROFF, FS_B, kFakeStackSize in *; lia)) in G9.
unfold FS_FROFF, FS_B in G9. rewrite <- HFF in G9.
rewrite restrict_mkst_fx in HS1.
assert (HSC2 : st_ok tfibsegs EC (ssC2 hi) (restrict H (mkst (ms_regs ms1) (Z_to_bv 64 FS_SDFF) (ms_mem ms1) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- (ssC2_eq hi). unfold preC2. rewrite PC1.
apply st_ok_add_fact; [| reflexivity | unfold aFF; rewrite V41; unfold SM0Tbl.ffLO, SM0Tbl.ffHI, SM0Tbl.FS_B, kHighMemBeg, kLowShadowBeg; clear - HZ HFF Hposr HN CE; unfold kFakeStackSize in *; destruct hi; cbn -[Z.add Z.sub Z.mul]; lia].
apply (st_ok_set_regs_mem tfibsegs 43 EC EC eC1 (ms_regs ms1) (ms_regs ms1) (Z_to_bv 64 FS_SDFF) FS_SDFF (mrestrict H (ms_mem ms1)) (mrestrict H (ms_mem ms1)) memC2 [((9%bv : bv 5), SOff aFF 0)] HS1).
- split; [intros; reflexivity | reflexivity].
- exact AT1.
- vm_compute. reflexivity.
- intros r Hr. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G9. symmetry. apply (DC0 _ FF V41). unfold kFakeStackSize in *; lia.
- pose proof (st_ok_mem_ok tfibsegs EC eC1 _ HS1) as (WF1 & ROK1 & PD1).
assert (SPL1 : ss_mem eC1 = nth 0 (ss_mem eC1) stkA :: tl (ss_mem eC1)) by (vm_compute; reflexivity).
rewrite SPL1 in ROK1.
split; [vm_compute; reflexivity|]. split.
+ unfold memC2. apply Forall_cons; [exact (Forall_inv ROK1)|]. apply Forall_cons; [|exact (Forall_inv_tail ROK1)].
unfold rFF, aFF, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V41.
split; [lia|]. split; [unfold FS_B; unfold kFakeStackSize in *; lia|]. split; [|apply Forall_nil].
intros o Ho. unfold FS_B in Ho. apply (YF0x.apresent_writable H); [unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia|].
apply (apresent_same H (ms_mem msA)); [apply MEQ1; rewrite unsigned_lit_small by (unfold kFakeStackSize in *; lia); lia |].
apply (apresent_same H mem); [apply MEQA; rewrite unsigned_lit_small by (unfold kFakeStackSize in *; lia); lia|]. apply PRF. lia.
+ apply pairwise_disjoint_of_extents. let l' := eval vm_compute in memC2 in change memC2 with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EC2, ?V35, ?V39, ?V41.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hsp44 HF1 HF2 Lbeg Hslo Htop Hposr HN HFLG HFF DFS. unfold kFakeStackSize in *. repeat split; lia. }
idtac "CHECKPOINT-4".
eapply SRr_bind; [apply (fs_phase W EC (ssC2 hi) _ _ _ _ HSC2 (r_C2 hi))|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HFm2 & HFrm2). rewrite ?wvb_wvb in *. rewrite (stC2_match hi) in HS2.
assert (MEQ2 : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> ~ (FF <= bv_unsigned z < FF + 64) -> bv_unsigned z <> FLG -> ~ (F + 0 <= bv_unsigned z < F + 0 + 8) ->
ms_mem ms2 z = ms_mem ms1 z).
{ intros z Hz1 Hz2 Hz3 Hz4. apply HFm2. intros Hin. destruct (memC2_windows hi EC _ Hin) as [Hw|[Hw|[Hw|Hw]]];
[rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V41 in Hw; unfold FS_B in Hw; lia | rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm2 HFrm2.
pose proof (C2_facts hi) as (PC2 & R11C2 & AT2 & RV2 & _).
pose proof (st_ok_restrict_mkst tfibsegs H EC _ _ HS2 RV2) as Hshape2. rewrite PC2 in Hshape2. rewrite Hshape2. rewrite Hshape2 in HS2. clear Hshape2.
assert (RD2 : forall (r : bv 5) v, reg_is (eC2 hi) (bv_unsigned r) v = true -> getr (ms_regs ms2) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr.
apply (st_ok_reg_denot H EC (eC2 hi) (mkst (ms_regs ms2) (Z_to_bv 64 FS_SDSH) (ms_mem ms2) (seg_rom tfibsegs)) r HS2). }
pose proof (RD2 11%bv a1C2 R11C2) as G11. rewrite (a1C2_denot EC FF V41 ltac:(unfold kFakeStackSize in *; lia)) in G11. unfold SHADOW_OFF in G11. rewrite <- HSH in G11.
rewrite restrict_mkst_fx in HS2.
assert (HSC3 : st_ok tfibsegs EC (ssC3 hi) (restrict H (mkst (ms_regs ms2) (Z_to_bv 64 FS_SDSH) (ms_mem ms2) (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx, <- (ssC3_eq hi). unfold preC3. rewrite PC2.
apply st_ok_add_fact; [| reflexivity | unfold aSH; rewrite V42; change (FS_B / 8) with 8; clear - HSHr; lia].
apply (st_ok_set_regs_mem tfibsegs 43 EC EC (eC2 hi) (ms_regs ms2) (ms_regs ms2) (Z_to_bv 64 FS_SDSH) FS_SDSH (mrestrict H (ms_mem ms2)) (mrestrict H (ms_mem ms2)) memC3 [((11%bv : bv 5), SOff aSH 0)] HS2).
- split; [intros; reflexivity | reflexivity].
- exact AT2.
- vm_compute. reflexivity.
- intros r Hr. reflexivity.
- apply Forall_cons; [|apply Forall_nil]. cbn [fst snd]. split; [reflexivity|]. rewrite G11. symmetry. apply (DC0 _ SH V42). lia.
- pose proof (st_ok_mem_ok tfibsegs EC (eC2 hi) _ HS2) as (WF2 & ROK2 & PD2).
assert (SPL2 : ss_mem (eC2 hi) = nth 0 memC2e stkA :: tl memC2e) by (rewrite (eC2_mem hi); vm_compute; reflexivity).
rewrite SPL2 in ROK2.
split; [vm_compute; reflexivity|]. split.
+ unfold memC3. apply Forall_cons; [exact (Forall_inv ROK2)|]. apply Forall_cons; [|exact (Forall_inv_tail ROK2)].
unfold rSH, aSH, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite V42.
change (FS_B / 8) with 8. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply (YF0x.apresent_writable H); [unfold TFIB_IMG_END; lia|].
apply (apresent_same H (ms_mem ms1)); [apply MEQ2; rewrite unsigned_lit_small by lia; unfold kFakeStackSize, kHighMemBeg in *; lia |].
apply (apresent_same H (ms_mem msA)); [apply MEQ1; rewrite unsigned_lit_small by lia; unfold kFakeStackSize, kHighMemBeg in *; lia |].
apply (apresent_same H mem); [apply MEQA; rewrite unsigned_lit_small by lia; unfold kFakeStackSize, kHighMemBeg in *; lia|].
apply PRS. unfold shadow_addr, kFakeFramesOff, SHADOW_OFF. replace ((F + (4096 + 32768)) / 8) with (F / 8 + 4608) by (replace (F + (4096 + 32768)) with ((F / 8 + 4608) * 8) by (clear - HF8; lia); rewrite Z_div_mult by lia; reflexivity). lia.
+ apply pairwise_disjoint_of_extents. let l' := eval vm_compute in memC3 in change memC3 with l'.
unfold extent_of_region. cbn [map fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite ?EC2, ?V35, ?V39, ?V41, ?V42.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
clear - Hsp44 HF1 HF2 Lbeg Hslo Htop Hposr HN HFLG HFF HSHe HSHF DFS. unfold kFakeStackSize, kHighMemBeg in *. repeat split; lia. }
idtac "CHECKPOINT-5".
eapply SRr_bind; [apply (fs_phase W EC (ssC3 hi) _ _ _ _ HSC3 (r_C3 hi))|].
cbv beta. intros W3 c3 _ (-> & ms3 & mat3 & -> & HS3 & HFm3 & HFrm3). rewrite ?wvb_wvb in *. rewrite (stC3_match hi) in HS3.
assert (MEQ3 : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 8) -> ~ (FF <= bv_unsigned z < FF + 64) ->
bv_unsigned z <> FLG -> ~ (F + 0 <= bv_unsigned z < F + 0 + 8) -> ms_mem ms3 z = ms_mem ms2 z).
{ intros z Hz1 Hz2 Hz3 Hz4 Hz5. apply HFm3. intros Hin. destruct (memC3_windows hi EC _ Hin) as [Hw|[Hw|[Hw|[Hw|Hw]]]];
[rewrite EC2 in Hw; unfold FS_WIN in Hw; lia | rewrite V42 in Hw; change (FS_B / 8) with 8 in Hw; lia | rewrite V41 in Hw; unfold FS_B in Hw; lia
| rewrite V39 in Hw; lia | rewrite V35 in Hw; unfold FS_HOFF in Hw; lia]. }
clear HFm3 HFrm3.
pose proof (C3_facts hi) as (ST3 & RV3 & FB3 & R10C3 & R4C3).
assert (MEQ : forall z : word, ~ (sp0 - 208 <= bv_unsigned z < sp0) -> ~ (SH <= bv_unsigned z < SH + 8) -> ~ (FF <= bv_unsigned z < FF + 64) ->
bv_unsigned z <> FLG -> ~ (F + 0 <= bv_unsigned z < F + 0 + 8) -> ms_mem ms3 z = mem z).
{ intros z Hz1 Hz2 Hz3 Hz4 Hz5. rewrite (MEQ3 z Hz1 Hz2 Hz3 Hz4 Hz5), (MEQ2 z Hz1 Hz3 Hz4 Hz5), (MEQ1 z Hz1 Hz4 Hz5). exact (MEQA z Hz1 Hz5). }
clear MEQ1 MEQ2 MEQ3.
eapply (SRr_ret_at tfibsegs tbl_fs tbl_fs_ok Hwx W EC); [exact HS3 | exact RV3 | rewrite (eC3_pc hi); vm_compute; reflexivity |].
intros mat'. rewrite wvb_wvb.
assert (RD3 : forall (r : bv 5) v, reg_is (eC3 hi) (bv_unsigned r) v = true -> getr (ms_regs ms3) r = sv_denot EC v).
{ intros r v Hr. unfold reg_is, RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. apply (st_ok_reg_denot H EC (eC3 hi) ms3 r HS3). }
assert (RK3 : forall rz, In rz [1; 2; 3; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr (ms_regs ms3) (Z_to_bv 5 rz) = getr regs (Z_to_bv 5 rz)).
{ intros rz Hrz. rewrite forallb_forall in FB3. specialize (FB3 rz Hrz). cbn beta in FB3.
assert (Hr32 : 0 <= rz < 32) by (clear - Hrz; cbn in Hrz; lia).
assert (U5 : bv_unsigned (Z_to_bv 5 rz) = rz) by (rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 5) with 32; apply Z.mod_small; exact Hr32).
rewrite (RD3 (Z_to_bv 5 rz) (SOff (Z.to_nat rz) 0)); [| rewrite U5; exact FB3].
cbn [sv_denot]. rewrite (ECreg (Z.to_nat rz) (Z_to_bv 5 rz)) by (rewrite U5; lia). rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
pose proof (RK3 1 ltac:(cbn; tauto)) as Q1. replace (Z_to_bv 5 1) with (1%bv : bv 5) in Q1 by (apply bv_eq; reflexivity).
replace (v_jalr (getr (ms_regs ms3) 1) 0) with (w64 (raZ regs)) by (rewrite Q1, Hra; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
split; [reflexivity|]. exists (ms_regs ms3), (ms_mem ms3), (with_vm_backing (m_vm_lazy md) mat' md).
pose proof (same_but_materialized_frame md _ (with_vm_backing_same md mat')) as MF.
split; [reflexivity|].
pose proof (st_ok_mem_ok tfibsegs EC (eC3 hi) _ HS3) as (_ & ROK3 & _). change (ms_mem (restrict H ms3)) with (mrestrict H (ms_mem ms3)) in ROK3.
destruct (eC3_regions hi) as (NR0 & NR1 & NR2 & NR3 & NR4).
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR1)) as OKSH.
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR2)) as OKFF.
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR3)) as OKFLG.
pose proof (proj1 (Forall_forall _ _) ROK3 _ (nth_error_In _ _ NR4)) as OKF.
unfold region_ok in OKSH, OKFF, OKFLG, OKF.
destruct rSH3_shape as (BSH & WSH1 & WSH2 & _). destruct rFF3_shape as (BFF & WFF1 & WFF2 & CFF). destruct rFLG3_shape as (BFL & WFL1 & WFL2 & CFL). destruct rF3_shape as (BF & WF1' & WF2' & CF).
rewrite BSH in OKSH. rewrite BFF in OKFF. rewrite BFL in OKFLG. rewrite BF in OKF. cbn [base_val] in OKSH, OKFF, OKFLG, OKF.
unfold aSH in OKSH. unfold aFF in OKFF. unfold aFLG in OKFLG. unfold aF in OKF. rewrite V42 in OKSH. rewrite V41 in OKFF. rewrite V39 in OKFLG. rewrite V35 in OKF.
destruct OKSH as (_ & _ & _ & CHSH). destruct OKFF as (_ & _ & _ & CHFF). destruct OKFLG as (_ & _ & _ & CHFL). destruct OKF as (_ & _ & _ & CHF).
assert (DH : sv_denot EC (SOff aH2 1) = Z_to_bv 64 (hint' mod 2 ^ 64)).
{ cbn [sv_denot]. unfold aH2. rewrite V37. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
subst dlt hm. rewrite Zplus_mod_idemp_l. replace (hint mod 2 ^ 64 + (hint' - hint) - 1 + 1) with (hint mod 2 ^ 64 + (hint' - hint)) by lia.
rewrite Zplus_mod_idemp_l, Z.mod_mod by lia. f_equal. lia. }
assert (VMH : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (F + FS_HOFF) 8 (hint' mod 2 ^ 64)).
{ apply (val_of_chunk_ok tfibsegs EC _ F FS_HOFF 8%N (SOff aH2 1) _ (proj1 (Forall_forall _ _) CHF _ (nth_error_In _ _ CF)) DH); [apply Z.mod_pos_bound; cbn; lia | cbn; lia]. }
assert (VMFL : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (FLG + 0) 1 1).
{ apply (val_of_chunk_ok tfibsegs EC _ FLG 0 1%N (SLit 1) 1 (proj1 (Forall_forall _ _) CHFL _ (nth_error_In _ _ CFL)) eq_refl); cbn; lia. }
assert (VMTR : val_mem tfibsegs (mrestrict H (ms_mem ms3)) (FF + (FS_B - 8)) 8 FLG).
{ apply (val_of_chunk_ok tfibsegs EC _ FF (FS_B - 8) 8%N (SOff aFLG 0) FLG (proj1 (Forall_forall _ _) CHFF _ (nth_error_In _ _ CFF))); [apply (DC0 _ FLG V39); unfold kFakeStackSize in *; lia | cbn; unfold kFakeStackSize in *; lia | cbn; lia]. }
assert (ZSH : forall i, 0 <= i < 8 -> aview tfibsegs H (ms_mem ms3) (SH + i) = Some 0).
{ intros i Hi. pose proof (Z.div_mod i 8 ltac:(lia)) as Hd. pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
pose proof (rSH3_chunk (i / 8) ltac:(split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia])) as HC.
pose proof (val_of_chunk_ok tfibsegs EC _ SH (8 * (i / 8)) 8%N (SLit 0) 0 (proj1 (Forall_forall _ _) CHSH _ HC) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as VM.
pose proof (aview_of_val_mem H (ms_mem ms3) _ 8 0 (Z.to_nat (i mod 8)) VM ltac:(lia)) as X.
rewrite Z2Nat.id in X by lia. replace (SH + 8 * (i / 8) + i mod 8) with (SH + i) in X by lia. rewrite X.
unfold YG0f.le_byte. rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia). reflexivity. }
assert (PW : forall b, (sp0 - 208 <= b < sp0 \/ SH <= b < SH + 8 \/ FF <= b < FF + 64 \/ FLG <= b < FLG + 1 \/ F + 0 <= b < F + 0 + 8) -> apresent H (ms_mem ms3) b).
{ intros b Hb. destruct rSTK3_shape as (BS0 & WS01 & WS02).
destruct Hb as [Hb|[Hb|[Hb|[Hb|Hb]]]].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 0 rSTK3 b HS3 NR0); [rewrite BS0, WS01, WS02; cbn [base_val]; rewrite EC2; unfold FS_WIN; lia | unfold TFIB_IMG_END; lia].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 1 rSH3 b HS3 NR1); [rewrite BSH, WSH1, WSH2; cbn [base_val]; unfold aSH; rewrite V42; change (FS_B / 8) with 8; lia | unfold TFIB_IMG_END; lia].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 2 rFF3 b HS3 NR2); [rewrite BFF, WFF1, WFF2; cbn [base_val]; unfold aFF; rewrite V41; unfold FS_B; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 3 rFLG3 b HS3 NR3); [rewrite BFL, WFL1, WFL2; cbn [base_val]; unfold aFLG; rewrite V39; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia].
- apply (st_ok_window_apresent H EC (eC3 hi) ms3 4 rF3 b HS3 NR4); [rewrite BF, WF1', WF2'; cbn [base_val]; unfold aF; rewrite V35; unfold FS_HOFF; lia | unfold TFIB_IMG_END; unfold kFakeStackSize in *; lia]. }
assert (AVQ : forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - 208 <= a < sp0 \/ SH <= a < SH + 8 \/ FF <= a < FF + 64 \/ FLG <= a < FLG + 1 \/ F + 0 <= a < F + 0 + 8) ->
aview tfibsegs H (ms_mem ms3) a = aview tfibsegs H mem a).
{ intros a Ha Hn. apply aview_same. apply MEQ; rewrite unsigned_lit_small by exact Ha; clear - Hn; lia. }
assert (NINF : ~ In (CID, pos) (frames S)) by (unfold frames; fold live; apply YG05.mem_pos_false; exact Hfree).
assert (HAR' : AR tfibsegs B ly S' W (ms_mem ms3) (with_vm_backing (m_vm_lazy md) mat' md)).
{ rewrite HS'eq. apply (astack_malloc_law_ok tfibsegs B ly S W mem md (ms_mem ms3) _ CID pos hint' HAR ltac:(unfold CID; lia) Hprobe).
all: change (w_H W) with H.
- intros k Hk. replace (ly_F ly + 8 * CID + Z.of_nat k) with (F + FS_HOFF + Z.of_nat k) by (unfold CID, FS_HOFF; subst F; lia).
rewrite (aview_of_val_mem H (ms_mem ms3) _ 8 _ k VMH Hk). unfold YG0f.le_byte. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity.
- rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. pose proof (aview_of_val_mem H (ms_mem ms3) _ 1 _ 0 VMFL ltac:(lia)) as X.
rewrite !Z.add_0_r in X. exact X.
- intros a Ha Hown Nh Nf Nfr Nsh. apply AVQ; [exact Ha|]. intros [Hs|[Hs|[Hs|[Hs|Hs]]]].
+ exact (al_stack _ _ LAWS ly S W mem md a HAR ltac:(clear - Hs Hslo Htop; lia) Hown).
+ apply Nsh. unfold in_zr. cbn [fst snd]. change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID / 8) with 8. fold SH. lia.
+ apply Nfr. unfold in_zr. cbn [fst snd]. change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID) with 64. lia.
+ apply Nf. rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. lia.
+ apply Nh. replace (ly_F ly) with F by reflexivity. unfold CID. lia.
- intros a Hv. rewrite (YE2y.aview_mod _ (ms_mem ms3) a). rewrite (YE2y.aview_mod _ mem a) in Hv.
pose proof (Z.mod_pos_bound a (2 ^ 64) ltac:(lia)) as Hr. set (a' := a mod 2 ^ 64) in *. clearbody a'.
assert (CS : (sp0 - 208 <= a' < sp0 \/ SH <= a' < SH + 8 \/ FF <= a' < FF + 64 \/ FLG <= a' < FLG + 1 \/ F + 0 <= a' < F + 0 + 8) \/
~ (sp0 - 208 <= a' < sp0 \/ SH <= a' < SH + 8 \/ FF <= a' < FF + 64 \/ FLG <= a' < FLG + 1 \/ F + 0 <= a' < F + 0 + 8)) by (clear; lia).
destruct CS as [CS|CS]; [apply aview_some_of_apresent; apply PW; exact CS | rewrite (AVQ a' Hr CS); exact Hv].
- apply MF. - apply MF. - apply MF.
- refine (hs_kept_gen H mem (ms_mem ms3) (fun b => sp0 - 208 <= b < sp0 \/ SH <= b < SH + 8 \/ FF <= b < FF + 64 \/ FLG <= b < FLG + 1 \/ F + 0 <= b < F + 0 + 8) _ _).
+ intros z Hz. apply MEQ; clear - Hz; lia.
+ intros b Hb. exists (ms_mem ms3). exact (PW b Hb). }
split; [exact HAR'|].
split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
-
intros r Hr. unfold acallee_saved in Hr.
destruct (Z.eq_dec r 4) as [->|Hr4].
+ replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite (RD3 4%bv (SLit TP) R4C3). cbn [sv_denot]. rewrite Htp, HTPv. reflexivity.
+ apply RK3. clear - Hr Hr4. cbn. lia.
- apply with_vm_backing_same.
- rewrite (RD3 10%bv (SOff aFF 0) R10C3). apply (DC0 _ FF V41). unfold kFakeStackSize in *; lia.
- intros i Hi. change (fs_frame_bytes CID / 8) with 8 in Hi. change (shadow_of_addr SHADOW_OFF FF) with SH. exact (ZSH i Hi).
- replace (FF + fs_frame_bytes CID - 8) with (FF + (FS_B - 8)) by (change (fs_frame_bytes CID) with 64; unfold FS_B; lia).
rewrite flag_addr_cid. change (ly_F ly + FS_FLOFF + pos) with FLG. apply (YF0x.val_mem_rdword H (ms_mem ms3) _ FLG); [unfold kFakeStackSize in *; lia | exact VMTR].
- intros a Ha. apply PW. change (fs_frame_bytes CID) with 64 in Ha. lia.
- intros a Ha NS NS' Nstk. apply AVQ; [exact Ha|]. unfold ESTACK in Nstk. intros [Hs|[Hs|[Hs|[Hs|Hs]]]].
+ clear - Hs Nstk. lia.
+ apply NS. apply (own_free_frame_shadow B ly S _ CID pos a M ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hposr) NINF).
change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID / 8) with 8. fold SH. lia.
+ apply NS. apply (own_free_frame B ly S _ CID pos a M ltac:(unfold CID; lia) ltac:(rewrite HNN; exact Hposr) NINF).
change (frame_addr ly CID pos) with FF. change (fs_frame_bytes CID) with 64. lia.
+ apply NS. apply (own_F_low B ly S _ a M). fold F. unfold kFakeFramesOff. lia.
+ apply NS. apply (own_F_low B ly S _ a M). fold F. unfold kFakeFramesOff. lia.
- intros a Ha. unfold ESTACK in Ha. destruct (Z_lt_le_dec a (sp0 - 208)) as [L|L].
+ apply (apresent_same H mem); [apply MEQ; rewrite unsigned_lit_small by (clear - Ha Hsp44; lia); clear - Ha L Hsp44 HSHe HF1 HF2 HFFr HFF HFLG Hposr HN Lbeg Hslo Htop DFS; unfold kFakeStackSize, kHighMemBeg in *; lia | apply HpresE; clear - Ha L; lia].
+ apply PW. lia.
Qed.
End f.
(* Build identity: ofl_head of the ASan+UBSan build (YE2k), the first words of main (0x81ea4, addi sp,sp,-80) and of
   LLVMFuzzerTestOneInput (0x84408, addi sp,sp,-320) in tfibsegs (= W_tbl.frsegs), the site address of W_place and
   of the core's Tfib_code at class 0, and the first word of the entry (addi sp,sp,-32). *)
Lemma rt_stack_malloc_0_build_id :
(YE2k.A_ofl_head, clookup (build_table tfibsegs 0x81ea4 1 TEmpty) 0x81ea4,
 clookup (build_table tfibsegs 0x84408 1 TEmpty) 0x84408,
 W_place.fr_sigma W_syms.WS_asan_stack_malloc_0, pc_stack_malloc Tfib_code 0, clookup tbl_fs FS_ENTRY)
= (0x5fa0e8, Some 0xfb010113, Some 0xec010113, FS_ENTRY, FS_ENTRY, Some 0xfe010113).
Proof. vm_compute. reflexivity. Qed.
Corollary stack_malloc0_contract : forall B, AR_laws tfibsegs B -> TfibSyms B -> astack_malloc_realizes tfibsegs B 0.
Proof.
intros B LAWS TB ly S W regs mem md pos S' HPRE Hcnt Hpath. rewrite (ts_code B TB).
exact (tfib_stack_malloc_at B LAWS TB ly S W regs mem md pos S' HPRE Hcnt Hpath).
Qed.
End d.
