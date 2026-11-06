(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjc.v (cold/c-asan-realloc-c5 84ee52cd012, file sha256 ef40d313555f) onto omx-clap-core/fuzz_preset's lib/AU (asan-ubsan image B', pin d663f82d7f48); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* cgif_file's view facts for the hit-k walk (requests 0..48 bytes): from ARm of the allocator state at the memory mem0,
   the machine facts of the cached chunk at the top of the per-thread cache of class cl.
   The k path reuses AGiy unchanged: the cached-chunk facts do not depend on the size range (AGiy needs only
   0 <= n and from_primary n = true). Each lemma below is AGiy's lemma with AGiy's name, section variables and
   hypotheses in AGiy's order, and its statement is AGiy's text over the k hub's names (AGj6.Pv, PVv, Kv, SHBv, SKv,
   SSLOTv). These are definitionally equal to AGis's (the same bodies), so each proof is the AGiy lemma itself, and
   the k files see AGj6's constants in the statements. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a YB1w YE3d YFhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGhy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require AGj6 AGiy.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Lemma In_combine_seq_last : forall (l0 : list Z) (x : Z) s, In ((s + length l0)%nat, x) (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof. exact AGiy.In_combine_seq_last. Qed.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order (the
   argument lists are fixed by the section headers, as in AGiy). *)
Set Default Proof Using "All".
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
(* The cached chunk's offset is 32-aligned (class sizes are multiples of 32). *)
Lemma off_aligned : forall B ly S rd n l off, ARm B ly S rd -> 0 <= n -> from_primary n = true ->
pc_chunks (cache S (chunk_class n)) = l ++ [off] -> off mod 32 = 0.
Proof. exact AGiy.off_aligned. Qed.
Section h.
Variables (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte).
Variables (n cl cnt v : Z) (S : astate) (l : list Z) (off : Z).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pv := (@AGj6.Pv ly cl).
Local Abbreviation PVv := (@AGj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation SHBv := (@AGj6.SHBv).
Local Abbreviation SKv := (@AGj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGj6.SSLOTv ly cl).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis HARm : ARm B ly S (aview tfibsegs (w_H W) mem0).
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let m0 := mrestrict (w_H W) mem0.
Lemma cl_range : 1 <= cl <= 30.
Proof. exact (AGiy.cl_range B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma cls_geom : 0 < class_size cl /\ class_size cl mod 32 = 0 /\ class_size cl <= kMaxSize /\ 2 <= max_cached cl <= 16.
Proof. exact (AGiy.cls_geom B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma cls_wf : cls_ok cl (reg S cl) (cache S cl) (st_cache_inited S) (chunk_offs S cl) (batch_offs S cl).
Proof. exact (AGiy.cls_wf B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma off_facts :
0 <= off /\ off + class_size cl <= rg_alloc_user (reg S cl) /\ off mod class_size cl = 0 /\ off mod 16 = 0 /\
rg_alloc_user (reg S cl) <= rg_mapped_user (reg S cl) <= 2 ^ 32 - 2 ^ 29 /\
~ In off ((fa_elems (class_size cl) (rg_free (reg S cl)) ++ l) ++ (chunk_offs S cl ++ batch_offs S cl)) /\
1 <= cnt <= 16 /\ cnt = Z.of_nat (length l) + 1 /\ pc_max (cache S cl) = max_cached cl.
Proof. exact (AGiy.off_facts B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma off32 : off mod 32 = 0.
Proof. exact (AGiy.off32 B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma Kv_base : Kv = region_base ly cl + off.
Proof. exact (AGiy.Kv_base B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma Kv_geom : kHighMemBeg <= Kv /\ Kv + class_size cl <= ASAN_CEIL /\ Kv mod 16 = 0 /\
ly_prim ly <= Kv /\ Kv + class_size cl <= ly_prim ly + kPrimResvSize.
Proof. exact (AGiy.Kv_geom B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma Hcl' : 1 <= cl <= 31.
Proof. exact (AGiy.Hcl' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma Hcnt' : 1 <= cnt <= 16.
Proof. exact (AGiy.Hcnt' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma Hv' : 0 <= v /\ 16 * v + 2 ^ 16 <= 2 ^ 32.
Proof. exact (AGiy.Hv' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma Hv2' : v mod 2 = 0.
Proof. exact (AGiy.Hv2' B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma cached_vs_chunk : forall k, In k (st_chunks S) -> ck_base B ly k + ck_extent k <= Kv \/ Kv + class_size cl <= ck_base B ly k.
Proof. exact (AGiy.cached_vs_chunk B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma find_chunk_at_none : forall lst g, (forall k, In k lst -> ~ (ck_base B ly k <= g < ck_base B ly k + ck_extent k)) -> find_chunk_at B ly lst g = None.
Proof. exact (AGiy.find_chunk_at_none B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma shadow250 : forall g, g mod 8 = 0 -> Kv <= g < Kv + class_size cl -> rd0 (shadow_addr g) = Some 250.
Proof. exact (AGiy.shadow250 B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
(* The shadow of the chunk lies in the high-shadow band, below kHighMemBeg. *)
Lemma SK_range : 0x2008fff7000 <= SKv /\ SKv + class_size cl / 8 <= kHighMemBeg.
Proof. exact (AGiy.SK_range B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma shadow_present : forall s, SKv <= s < SKv + class_size cl / 8 -> rd0 s = Some 250 /\ apresent (w_H W) mem0 s.
Proof. exact (AGiy.shadow_present B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma vis_present : forall e len a, In (e, len) (ajunk B ly S) \/ In (e, len) (aareas S) ->
aeval B ly e <= a < aeval B ly e + len -> off_img a -> apresent (w_H W) mem0 a.
Proof. exact (AGiy.vis_present B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
(* The whole cached chunk is present (YFiy.KPRES over the class size). *)
Lemma chunk_present : forall a, Kv <= a < Kv + class_size cl -> apresent (w_H W) mem0 a.
Proof. exact (AGiy.chunk_present B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma in_thread_junk : forall r, In r thread_junk -> In r (ajunk B ly S).
Proof. exact (AGiy.in_thread_junk B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma T_zone : zone3 T kThreadObjSize.
Proof. exact (AGiy.T_zone B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
(* The thread's junk words (cache stats, stats) are present. *)
Lemma junk_present : forall a, T + t_cache_stats <= a < T + t_unwinding -> apresent (w_H W) mem0 a.
Proof. exact (AGiy.junk_present B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof. exact (AGiy.cell_sym B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof. exact (AGiy.cell_lit B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma cell_state : forall c e (w : nat) x, In c (acells B ly S) -> c = ACell e w (AV (ANum x)) -> val_mem tfibsegs m0 (aeval B ly e) w x.
Proof. exact (AGiy.cell_state B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma In_acells_cache : forall c, In c (cache_cells S cl) -> In c (acells B ly S).
Proof. exact (AGiy.In_acells_cache B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma cache_vals : val_mem tfibsegs m0 Pv 4 cnt /\ val_mem tfibsegs m0 (Pv + 8) 8 (class_size cl) /\ val_mem tfibsegs m0 PVv 4 v.
Proof. exact (AGiy.cache_vals B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma unwinding_val : val_mem tfibsegs m0 (T + t_unwinding) 1 0.
Proof. exact (AGiy.unwinding_val B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
(* The instance's fields the seed reads: primary.space at +0x20 and the two words at +0xe20 (constant cells). *)
Lemma inst_cells : val_mem tfibsegs m0 (TFIB_INST + 0x20) 8 (ly_space ly) /\
val_mem tfibsegs m0 (TFIB_INST + 0xe20) 8 0x10000000000 /\ val_mem tfibsegs m0 (TFIB_INST + 0xe28) 8 0x108000010.
Proof. exact (AGiy.inst_cells B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma v_facts : 0 <= v /\ v mod 2 = 0 /\ 16 * v + 2 ^ 16 <= 2 ^ 32.
Proof. exact (AGiy.v_facts B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
Lemma shadow_vals : forall s, SKv <= s < SKv + class_size cl / 8 -> apresent (w_H W) mem0 s /\ val_mem tfibsegs m0 s 1 250.
Proof. exact (AGiy.shadow_vals B W ly mem0 n cl cnt v S l off TS LY IMG HARm Hn0 FP Hinited Hcache Hcl_class Hcnt_def Hoff_def). Qed.
End h.
End f.
