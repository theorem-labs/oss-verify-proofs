(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AE6z.v (ent2L, ent2H, finishR, path2L, path2H): __asan_region_is_poisoned of plugin-hostd/fuzz_command's ASan build (cgif_file_fuzzer's copy of the function) walked on its own from its entry to its return, for every size 0 < n < 2^32 whose start rounds up inside its memory band, through both ways of the first and last shadow bytes and of the shadow_end <= shadow_beg test, with a scratch window of any stk >= 72 and the art_post conclusion of lib/A/Rt/RtDefs.v; module paths. *)
(* ported from proofs/plugin-hostd/fuzz_command/lib/A/Rt/RtSRegion.v
   (origin/ossv/recipes, sha256 d547441964ce, the same blob as a working branch 8aaeb29ab7b2; its theorem
   cmd_region_zero_stk) to plugin-hostd/fuzz_reply's ASan image (fuzz_reply.asan, __asan_region_is_poisoned at
   0x5595c): the addresses relocated by alreloc frozen-56664a20986eb62e (29 numerals by symbol; the cgif address in
   the header comment above taken out by hand), and the statements restated over fuzz_reply's cf allocator invariant
   (Reusable/YG0dcf.v): AR -> ARcf with the ghost head set Hp, AR_laws -> AR_laws_cf, CmdBSyms -> TfibSyms,
   art_post -> art_post_cf (RtDStrndupCfRt.v; its raw-memory frame is proved from the walk's invariant INV), the
   rt_rom_view premise dropped (the walk reads the image's read-only words from the invariant's const cells,
   AE2y.icpt_rodata_ok_x). The walk itself is unchanged. *)
(* a SECOND walk of __asan_region_is_poisoned in this harness. The first is
   lib/A/Bz/A/R_isPoisoned.v rip_proof (rip_stmt, an evt walk over the normalized memory). It does not serve the
   strndup wrapper: its bridge to an allocator-invariant post, RT_post.bz_transport, needs NM.ro_agree, which comes
   only from rom_view, and astrndup_realizes_cf (Reusable/YG0dcf.v:542-557) has no rom_view premise. This walk reads
   the read-only words it needs from the invariant's const cells instead, so it needs no rom_view. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG01cf YG00cf YG0ncf YG0dcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Rt Require Import RtDStrndupCfRt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* The walk starts at the entry 0x5595c with the caller's own ra and ends at the `ret` 0x55afc, which returns to it.
   Measured on the pinned image (the disassembly of __asan_region_is_poisoned, and MemToShadow 0x554d0 with
   the disassembler): with a0 = x, a1 = n,
     0x5597c  beqz a1                    not taken (n > 0; decided by the atom facts)
     0x559a4..0x559e4  AddrIsInMem(x)     decided by the atom facts of the band (x <= 0x7fff7ff8, or
                                          kHighMemBeg <= x <= 2^47 - 8) and the record cells 0xa6da0/8/0xa6db0
     0x559ec / 0x55a28  AddrIsInMem(x+n)  one stop each band, decided by amem_range (the rest by the facts)
     0x55a30  bgeu s0,s2 (CHECK x < x+n) not taken
     0x55a40, 0x55a4c  MemToShadow on RoundUp(x, 8) and RoundDown(x+n, 8): its AddrIsInMem test is decided by the
                                          facts of du and de; RoundUp(x, 8) stays in the band because x + 8 is at most
                                          the band's end (the premise that the contract states as 64 < n)
     0x55a60/0x55a68, 0x55a7c/0x55a84  AddressIsPoisoned(x), (x+n-1): false by range_addressable (saddr_ok)
     0x55ac0  bgeu s3,a0 (shadow_end <= shadow_beg): both ways
     0x55acc  jal mem_is_zero 0x65734 (AE2y.icpt_memisz; every shadow byte of a granule fully inside the range is 0)
     0x55ad0  beqz a0 not taken (mem_is_zero returned 1); 0x55ad4 li s0,0; 0x55afc ret with a0 = 0.
   Frame: 64 bytes (0x5595c) and mem_is_zero's ra at 72 below the entry sp, so the walk writes only
   [sp - 72, sp). Case A: the first and the last byte of the range lie in different granules (then the first
   granule's shadow byte is 0); case B: one granule holds the whole range. *)

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Definition RG_ENTRY : Z := 0x5595c.
Definition RG_RET : Z := 0x55afc.
Definition RG_MZRET : Z := 0x55ad0.
Definition RG_STK : Z := 64.
Definition stkR : YP09.region := YP09.mkRegion (Some 2%nat) (- RG_STK) 0 (- RG_STK) 0 [].
Definition shA : smem :=
[ YP09.mkRegion (Some 32%nat) SB (SB + 1) SB SB [YP09.mkChunk SB (CZero 1)];
YP09.mkRegion (Some 33%nat) SB (SB + 1) SB SB [YP09.mkChunk SB (CVal 1 (SOff 34 0))] ].
Definition shB : smem := [ YP09.mkRegion (Some 32%nat) SB (SB + 1) SB SB [YP09.mkChunk SB (CVal 1 (SOff 34 0))] ].
Definition aliasA : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 10 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-1)) (SOff 11 0)) (SLit 3), SOff 33 0);
(SAlu ALU_AND (SOff 10 7) (SLit (-8)), SOff 35 0);
(SAlu ALU_AND (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (SLit (-8)), SOff 36 0);
(SAlu ALU_SRL (SOff 35 0) (SLit 3), SOff 37 0);
(SAlu ALU_SRL (SOff 36 0) (SLit 3), SOff 38 0) ].
Definition aliasB : list (sv * sv) :=
[ (SAlu ALU_SRL (SOff 10 0) (SLit 3), SOff 32 0);
(SAlu ALU_SRL (SAlu ALU_ADD (SOff 10 (-1)) (SOff 11 0)) (SLit 3), SOff 32 0);
(SAlu ALU_AND (SOff 10 7) (SLit (-8)), SOff 35 0);
(SAlu ALU_AND (SAlu ALU_ADD (SOff 10 0) (SOff 11 0)) (SLit (-8)), SOff 36 0);
(SAlu ALU_SRL (SOff 35 0) (SLit 3), SOff 37 0);
(SAlu ALU_SRL (SOff 36 0) (SLit 3), SOff 38 0) ].
(* atoms: 10 x, 11 n, 32 x/8, 33 (x+n-1)/8, 34 the shadow byte of the last granule, 35 RoundUp(x,8), 36 RoundDown(x+n,8),
   37 and 38 their granule numbers *)
Definition factsL : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 1 0x7fff7ff8 0); (11%nat, mkAF 1 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(35%nat, mkAF 0 0x7fff7ff8 3); (36%nat, mkAF 0 0x7fff7ff8 3); (37%nat, mkAF 0 (2^44) 0); (38%nat, mkAF 0 (2^44) 0)].
Definition factsH : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0x10007fff8000 (2^47 - 8) 0); (11%nat, mkAF 1 (2^32 - 1) 0);
(32%nat, mkAF 0 (2^44) 0); (33%nat, mkAF 0 (2^44) 0); (34%nat, mkAF 0 7 0);
(35%nat, mkAF 0x10007fff8000 (2^47 - 8) 3); (36%nat, mkAF 0x10007fff8000 (2^47 - 8) 3); (37%nat, mkAF 0 (2^44) 0); (38%nat, mkAF 0 (2^44) 0)].
Definition ssA (F : list (nat * afact)) : sstate := mkSS RG_ENTRY sr_atoms (stkR :: shA ++ map ro_region icpt_rodata) None (mkFacts F [] aliasA).
Definition ssB (F : list (nat * afact)) : sstate := mkSS RG_ENTRY sr_atoms (stkR :: shB ++ map ro_region icpt_rodata) None (mkFacts F [] aliasB).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_icpt FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition AC (s : sstate) (c : branch_cond) (a b : sv) : sstate := YP06.add_cond s (mkAC c a b).
Definition C0L (e : sstate) : sstate := AC e BC_GEU (SLit 2147450879) (RG e 18).
Definition C0H (e : sstate) : sstate := AC e BC_GEU (SLit 140737488355327) (RG e 18).
Definition C1 (e : sstate) : sstate := AC e BC_LTU (RG e 8) (RG e 18).
Definition CAz (e : sstate) : sstate := AC e BC_EQ (RG e 11) (SLit 0).
Definition CAn (e : sstate) : sstate := AC e BC_NE (RG e 11) (SLit 0).
Definition CAl (e : sstate) : sstate := AC e BC_LT (RG e 12) (RG e 11).
Definition CBz (e : sstate) : sstate := AC e BC_EQ (RG e 12) (SLit 0).
Definition CBn (e : sstate) : sstate := AC e BC_NE (RG e 12) (SLit 0).
Definition CBg (e : sstate) : sstate := AC e BC_LT (RG e 13) (RG e 12).
Definition CBl (e : sstate) : sstate := AC e BC_LT (RG e 12) (RG e 11).
Definition SGU : sv := SOff 37 SB.
Definition SGE : sv := SOff 38 SB.
Definition SLEN : sv := SAlu ALU_ADD (SMd M_MUL (SOff 37 0) (SLit (-1))) (SOff 38 0).
Definition TL (e : sstate) := RUN (AC e BC_LTU SGU SGE).
Definition TG (e : sstate) := RUN (AC e BC_GEU SGU SGE).
Definition TM (p : sstate * run_status) := RUN (ss_after_mz (fst p) (ss_mem (fst p)) 56 RG_MZRET).
Definition wins_ok (rs : smem) : bool :=
forallb (fun t => win_eqb t (Some 2%nat, - RG_STK, 0) || (snd t <=? snd (fst t))) (windows rs).
Definition noecall (st : run_status) : bool := match st with RS_ecall => false | _ => true end.
Definition resv_none (ss : sstate) : bool := match ss_resv ss with None => true | _ => false end.
Definition okreg (r : YP09.region) : bool :=
(obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_lo r =? - RG_STK) && (YP09.r_hi r =? 0) && (YP09.r_wlo r =? - RG_STK) && (YP09.r_whi r =? 0)) ||
((obase_eqb (YP09.r_base r) (Some 32%nat) || obase_eqb (YP09.r_base r) (Some 33%nat)) && (YP09.r_lo r =? SB) && (YP09.r_hi r =? SB + 1) &&
(YP09.r_wlo r =? SB) && (YP09.r_whi r =? SB)) ||
(obase_eqb (YP09.r_base r) None && (0 <=? YP09.r_lo r) && (YP09.r_hi r <=? 0x200000) && (YP09.r_lo r <=? YP09.r_wlo r) && (YP09.r_whi r <=? YP09.r_hi r)).
Definition chkMZ (ss : sstate) : bool :=
(ss_pc ss =? MZ_PC) && resv_none ss && ss_atoms_lt 56 ss && regions_wf (ss_mem ss) && no_cdata (ss_mem ss) &&
mem_atoms_lt 56 (ss_mem ss) && sv_eqb (RG ss 10) SGU && sv_eqb (RG ss 11) SLEN && sv_eqb (RG ss 2) (SOff 2 (- RG_STK)) &&
sv_eqb (RG ss 1) (SLit RG_MZRET) && forallb okreg (ss_mem ss).
Definition head_ok (ss : sstate) : bool :=
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - RG_STK) && (YP09.r_whi r =? 0) | [] => false end.
Definition chkF (ss : sstate) : bool :=
(ss_pc ss =? RG_RET) && resv_none ss && head_ok ss && sv_eqb (RG ss 10) (SLit 0) && sv_eqb (RG ss 1) (SOff 1 0) &&
forallb (fun r : bv 5 => sv_eqb (sr_get (ss_regs ss) r) (SOff (Z.to_nat (bv_unsigned r)) 0)) CALLEE_SAVED.
Definition tail_chk (e : sstate) (pl pm pg : sstate * run_status) : bool :=
wins_ok (ss_mem e) && chkMZ (fst pl) && noecall (snd pl) && wins_ok (ss_mem (fst pl)) &&
chkF (fst pm) && noecall (snd pm) && chkF (fst pg) && noecall (snd pg).
Lemma probe_ret : clookup tbl_icpt RG_RET = Some RET_WORD_r. Proof. vm_compute. reflexivity. Qed.
(* band L, case A: the first and the last byte lie in different granules *)
Definition pLA0 : sstate * run_status := Eval vm_compute in RUN (ssA factsL).
Lemma rLA0 : RUN (ssA factsL) = pLA0. Proof. vm_compute. reflexivity. Qed.
Definition pLA1 : sstate * run_status := Eval vm_compute in RUN (C0L (fst pLA0)).
Lemma rLA1 : RUN (C0L (fst pLA0)) = pLA1. Proof. vm_compute. reflexivity. Qed.
Definition pLA2 : sstate * run_status := Eval vm_compute in RUN (C1 (fst pLA1)).
Lemma rLA2 : RUN (C1 (fst pLA1)) = pLA2. Proof. vm_compute. reflexivity. Qed.
Definition pLA3z : sstate * run_status := Eval vm_compute in RUN (CAz (fst pLA2)).
Lemma rLA3z : RUN (CAz (fst pLA2)) = pLA3z. Proof. vm_compute. reflexivity. Qed.
Definition pLA3z_l : sstate * run_status := Eval vm_compute in TL (fst pLA3z).
Lemma rLA3z_l : TL (fst pLA3z) = pLA3z_l. Proof. vm_compute. reflexivity. Qed.
Definition pLA3z_m : sstate * run_status := Eval vm_compute in TM pLA3z_l.
Lemma rLA3z_m : TM pLA3z_l = pLA3z_m. Proof. vm_compute. reflexivity. Qed.
Definition pLA3z_g : sstate * run_status := Eval vm_compute in TG (fst pLA3z).
Lemma rLA3z_g : TG (fst pLA3z) = pLA3z_g. Proof. vm_compute. reflexivity. Qed.
Lemma cLA3z : tail_chk (fst pLA3z) pLA3z_l pLA3z_m pLA3z_g = true. Proof. vm_compute. reflexivity. Qed.
Definition pLA3n : sstate * run_status := Eval vm_compute in RUN (CAn (fst pLA2)).
Lemma rLA3n : RUN (CAn (fst pLA2)) = pLA3n. Proof. vm_compute. reflexivity. Qed.
Definition pLA4n : sstate * run_status := Eval vm_compute in RUN (CAl (fst pLA3n)).
Lemma rLA4n : RUN (CAl (fst pLA3n)) = pLA4n. Proof. vm_compute. reflexivity. Qed.
Definition pLA4n_l : sstate * run_status := Eval vm_compute in TL (fst pLA4n).
Lemma rLA4n_l : TL (fst pLA4n) = pLA4n_l. Proof. vm_compute. reflexivity. Qed.
Definition pLA4n_m : sstate * run_status := Eval vm_compute in TM pLA4n_l.
Lemma rLA4n_m : TM pLA4n_l = pLA4n_m. Proof. vm_compute. reflexivity. Qed.
Definition pLA4n_g : sstate * run_status := Eval vm_compute in TG (fst pLA4n).
Lemma rLA4n_g : TG (fst pLA4n) = pLA4n_g. Proof. vm_compute. reflexivity. Qed.
Lemma cLA4n : tail_chk (fst pLA4n) pLA4n_l pLA4n_m pLA4n_g = true. Proof. vm_compute. reflexivity. Qed.
(* band L, case B: one granule holds the whole range *)
Definition pLB0 : sstate * run_status := Eval vm_compute in RUN (ssB factsL).
Lemma rLB0 : RUN (ssB factsL) = pLB0. Proof. vm_compute. reflexivity. Qed.
Definition pLB1 : sstate * run_status := Eval vm_compute in RUN (C0L (fst pLB0)).
Lemma rLB1 : RUN (C0L (fst pLB0)) = pLB1. Proof. vm_compute. reflexivity. Qed.
Definition pLB2 : sstate * run_status := Eval vm_compute in RUN (C1 (fst pLB1)).
Lemma rLB2 : RUN (C1 (fst pLB1)) = pLB2. Proof. vm_compute. reflexivity. Qed.
Definition pLB3z : sstate * run_status := Eval vm_compute in RUN (CBz (fst pLB2)).
Lemma rLB3z : RUN (CBz (fst pLB2)) = pLB3z. Proof. vm_compute. reflexivity. Qed.
Definition pLB3z_l : sstate * run_status := Eval vm_compute in TL (fst pLB3z).
Lemma rLB3z_l : TL (fst pLB3z) = pLB3z_l. Proof. vm_compute. reflexivity. Qed.
Definition pLB3z_m : sstate * run_status := Eval vm_compute in TM pLB3z_l.
Lemma rLB3z_m : TM pLB3z_l = pLB3z_m. Proof. vm_compute. reflexivity. Qed.
Definition pLB3z_g : sstate * run_status := Eval vm_compute in TG (fst pLB3z).
Lemma rLB3z_g : TG (fst pLB3z) = pLB3z_g. Proof. vm_compute. reflexivity. Qed.
Lemma cLB3z : tail_chk (fst pLB3z) pLB3z_l pLB3z_m pLB3z_g = true. Proof. vm_compute. reflexivity. Qed.
Definition pLB3n : sstate * run_status := Eval vm_compute in RUN (CBn (fst pLB2)).
Lemma rLB3n : RUN (CBn (fst pLB2)) = pLB3n. Proof. vm_compute. reflexivity. Qed.
Definition pLB4n : sstate * run_status := Eval vm_compute in RUN (CBg (fst pLB3n)).
Lemma rLB4n : RUN (CBg (fst pLB3n)) = pLB4n. Proof. vm_compute. reflexivity. Qed.
Definition pLB5n : sstate * run_status := Eval vm_compute in RUN (CBl (fst pLB4n)).
Lemma rLB5n : RUN (CBl (fst pLB4n)) = pLB5n. Proof. vm_compute. reflexivity. Qed.
Definition pLB5n_l : sstate * run_status := Eval vm_compute in TL (fst pLB5n).
Lemma rLB5n_l : TL (fst pLB5n) = pLB5n_l. Proof. vm_compute. reflexivity. Qed.
Definition pLB5n_m : sstate * run_status := Eval vm_compute in TM pLB5n_l.
Lemma rLB5n_m : TM pLB5n_l = pLB5n_m. Proof. vm_compute. reflexivity. Qed.
Definition pLB5n_g : sstate * run_status := Eval vm_compute in TG (fst pLB5n).
Lemma rLB5n_g : TG (fst pLB5n) = pLB5n_g. Proof. vm_compute. reflexivity. Qed.
Lemma cLB5n : tail_chk (fst pLB5n) pLB5n_l pLB5n_m pLB5n_g = true. Proof. vm_compute. reflexivity. Qed.
(* band H, case A: the first and the last byte lie in different granules *)
Definition pHA0 : sstate * run_status := Eval vm_compute in RUN (ssA factsH).
Lemma rHA0 : RUN (ssA factsH) = pHA0. Proof. vm_compute. reflexivity. Qed.
Definition pHA1 : sstate * run_status := Eval vm_compute in RUN (C0H (fst pHA0)).
Lemma rHA1 : RUN (C0H (fst pHA0)) = pHA1. Proof. vm_compute. reflexivity. Qed.
Definition pHA2 : sstate * run_status := Eval vm_compute in RUN (C1 (fst pHA1)).
Lemma rHA2 : RUN (C1 (fst pHA1)) = pHA2. Proof. vm_compute. reflexivity. Qed.
Definition pHA3z : sstate * run_status := Eval vm_compute in RUN (CAz (fst pHA2)).
Lemma rHA3z : RUN (CAz (fst pHA2)) = pHA3z. Proof. vm_compute. reflexivity. Qed.
Definition pHA3z_l : sstate * run_status := Eval vm_compute in TL (fst pHA3z).
Lemma rHA3z_l : TL (fst pHA3z) = pHA3z_l. Proof. vm_compute. reflexivity. Qed.
Definition pHA3z_m : sstate * run_status := Eval vm_compute in TM pHA3z_l.
Lemma rHA3z_m : TM pHA3z_l = pHA3z_m. Proof. vm_compute. reflexivity. Qed.
Definition pHA3z_g : sstate * run_status := Eval vm_compute in TG (fst pHA3z).
Lemma rHA3z_g : TG (fst pHA3z) = pHA3z_g. Proof. vm_compute. reflexivity. Qed.
Lemma cHA3z : tail_chk (fst pHA3z) pHA3z_l pHA3z_m pHA3z_g = true. Proof. vm_compute. reflexivity. Qed.
Definition pHA3n : sstate * run_status := Eval vm_compute in RUN (CAn (fst pHA2)).
Lemma rHA3n : RUN (CAn (fst pHA2)) = pHA3n. Proof. vm_compute. reflexivity. Qed.
Definition pHA4n : sstate * run_status := Eval vm_compute in RUN (CAl (fst pHA3n)).
Lemma rHA4n : RUN (CAl (fst pHA3n)) = pHA4n. Proof. vm_compute. reflexivity. Qed.
Definition pHA4n_l : sstate * run_status := Eval vm_compute in TL (fst pHA4n).
Lemma rHA4n_l : TL (fst pHA4n) = pHA4n_l. Proof. vm_compute. reflexivity. Qed.
Definition pHA4n_m : sstate * run_status := Eval vm_compute in TM pHA4n_l.
Lemma rHA4n_m : TM pHA4n_l = pHA4n_m. Proof. vm_compute. reflexivity. Qed.
Definition pHA4n_g : sstate * run_status := Eval vm_compute in TG (fst pHA4n).
Lemma rHA4n_g : TG (fst pHA4n) = pHA4n_g. Proof. vm_compute. reflexivity. Qed.
Lemma cHA4n : tail_chk (fst pHA4n) pHA4n_l pHA4n_m pHA4n_g = true. Proof. vm_compute. reflexivity. Qed.
(* band H, case B: one granule holds the whole range *)
Definition pHB0 : sstate * run_status := Eval vm_compute in RUN (ssB factsH).
Lemma rHB0 : RUN (ssB factsH) = pHB0. Proof. vm_compute. reflexivity. Qed.
Definition pHB1 : sstate * run_status := Eval vm_compute in RUN (C0H (fst pHB0)).
Lemma rHB1 : RUN (C0H (fst pHB0)) = pHB1. Proof. vm_compute. reflexivity. Qed.
Definition pHB2 : sstate * run_status := Eval vm_compute in RUN (C1 (fst pHB1)).
Lemma rHB2 : RUN (C1 (fst pHB1)) = pHB2. Proof. vm_compute. reflexivity. Qed.
Definition pHB3z : sstate * run_status := Eval vm_compute in RUN (CBz (fst pHB2)).
Lemma rHB3z : RUN (CBz (fst pHB2)) = pHB3z. Proof. vm_compute. reflexivity. Qed.
Definition pHB3z_l : sstate * run_status := Eval vm_compute in TL (fst pHB3z).
Lemma rHB3z_l : TL (fst pHB3z) = pHB3z_l. Proof. vm_compute. reflexivity. Qed.
Definition pHB3z_m : sstate * run_status := Eval vm_compute in TM pHB3z_l.
Lemma rHB3z_m : TM pHB3z_l = pHB3z_m. Proof. vm_compute. reflexivity. Qed.
Definition pHB3z_g : sstate * run_status := Eval vm_compute in TG (fst pHB3z).
Lemma rHB3z_g : TG (fst pHB3z) = pHB3z_g. Proof. vm_compute. reflexivity. Qed.
Lemma cHB3z : tail_chk (fst pHB3z) pHB3z_l pHB3z_m pHB3z_g = true. Proof. vm_compute. reflexivity. Qed.
Definition pHB3n : sstate * run_status := Eval vm_compute in RUN (CBn (fst pHB2)).
Lemma rHB3n : RUN (CBn (fst pHB2)) = pHB3n. Proof. vm_compute. reflexivity. Qed.
Definition pHB4n : sstate * run_status := Eval vm_compute in RUN (CBg (fst pHB3n)).
Lemma rHB4n : RUN (CBg (fst pHB3n)) = pHB4n. Proof. vm_compute. reflexivity. Qed.
Definition pHB5n : sstate * run_status := Eval vm_compute in RUN (CBl (fst pHB4n)).
Lemma rHB5n : RUN (CBl (fst pHB4n)) = pHB5n. Proof. vm_compute. reflexivity. Qed.
Definition pHB5n_l : sstate * run_status := Eval vm_compute in TL (fst pHB5n).
Lemma rHB5n_l : TL (fst pHB5n) = pHB5n_l. Proof. vm_compute. reflexivity. Qed.
Definition pHB5n_m : sstate * run_status := Eval vm_compute in TM pHB5n_l.
Lemma rHB5n_m : TM pHB5n_l = pHB5n_m. Proof. vm_compute. reflexivity. Qed.
Definition pHB5n_g : sstate * run_status := Eval vm_compute in TG (fst pHB5n).
Lemma rHB5n_g : TG (fst pHB5n) = pHB5n_g. Proof. vm_compute. reflexivity. Qed.
Lemma cHB5n : tail_chk (fst pHB5n) pHB5n_l pHB5n_m pHB5n_g = true. Proof. vm_compute. reflexivity. Qed.

Lemma ra_first : forall (rd : Z -> option Z) d n, range_addressable rd SHADOW_OFF d n -> 0 < n ->
exists b0, rd (SB + d / 8) = Some b0 /\ saddr_ok d b0.
Proof. intros rd d n Hra Hn. destruct (Hra d ltac:(lia)) as (s & Hs & Hok). exists s. rewrite AE2y.SB_eq. exact (conj Hs Hok). Qed.
Lemma rp_blt_first : forall E (pa pb : nat) d b, ew E pa = Z_to_bv 64 d -> ew E pb = Z_to_bv 64 b -> 0 <= d < 2 ^ 64 -> d mod 8 < b < 8 ->
branch_taken BC_LT (sv_denot E (SAlu ALU_AND (SOff pa 0) (SLit 7))) (sv_denot E (SOff pb 0)) = true.
Proof.
intros E pa pb d b Ha Hb Hd Hlt.
cbn [branch_taken]. unfold bv_lts. rewrite !signed_is_swrap_unsigned. fold (U E (SOff pb 0)).
fold (U E (SAlu ALU_AND (SOff pa 0) (SLit 7))).
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E pa d Ha), U_SLit, (U_atom E pb b Hb) by lia.
change (zcanon 7) with 7.
rewrite (zcanon_small (Z.land d 7)) by (pose proof (Z_land_upper d 7 ltac:(lia)); lia).
change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
pose proof (Z.mod_pos_bound d 8 ltac:(lia)) as Hm.
rewrite !swrap64_id by (unfold half64; lia). apply Z.ltb_lt. lia.
Qed.
Lemma br_sbeg_ge_send : forall E (pu pe : nat) gu ge, ew E pu = Z_to_bv 64 gu -> ew E pe = Z_to_bv 64 ge -> 0 <= ge <= gu -> gu + SB < 2 ^ 64 ->
branch_taken BC_GEU (sv_denot E (SOff pu SB)) (sv_denot E (SOff pe SB)) = true.
Proof.
intros E pu pe gu ge Hu He R1 R2. unfold SB in *.
rewrite branch_geu_U, (U_atom_off E pu gu 2147450880 Hu), (U_atom_off E pe ge 2147450880 He) by lia.
rewrite (proj2 (Z.ltb_ge _ _)) by lia. reflexivity.
Qed.

Section f.
Variable B : asyms.
Hypothesis LAWS : AR_laws_cf tfibsegs B.
Hypothesis TB : TfibSyms B.
Variable stk : Z.
Hypothesis Hstk : RGN_SCR <= stk.
Variables (ly : alayout) (S : astate) (Hp : list Z) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (x n : Z).
Hypothesis HAR : ARcf tfibsegs B ly S Hp W mem md.
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hslo : ly_stk_lo ly + stk <= spZ regs.
Hypothesis Hshi : spZ regs <= ly_stk_hi ly.
Hypothesis Hpres : forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis G10 : getr regs 10 = w64 x.
Hypothesis G11 : getr regs 11 = w64 n.
Hypothesis Hn : 0 < n < 2 ^ 32.
Hypothesis Hx : 0 < x.
Hypothesis HRD : aread_ok tfibsegs stk W regs mem x n.
Hypothesis HRU : x + 8 <= kLowMemEnd \/ (kHighMemBeg <= x /\ x + 8 <= kHighMemEnd).
Local Notation HH := (w_H W).
Local Notation g0 := (x / 8).
Local Notation g1 := ((x + n - 1) / 8).
Local Notation du := ((x + 7) / 8 * 8).
Local Notation de := ((x + n) / 8 * 8).
Local Notation gu := ((x + 7) / 8).
Local Notation ge := ((x + n) / 8).
Local Notation POST := (art_post_cf tfibsegs B stk ly S Hp W regs mem md (fun _ => False) (fun regs' _ => getr regs' 10 = w64 0)).
Definition INV (ms : machine_state) : Prop :=
(forall z : word, ~ (spZ regs - 72 <= bv_unsigned z < spZ regs) -> ms_mem ms z = mem z) /\
(forall a, spZ regs - 72 <= a < spZ regs - 64 -> ms_mem ms (Z_to_bv 64 a) <> None).
Definition ENVOK (E : env) : Prop := YP06.env_agree 32 (Ereg regs []) E.
Definition EV (E : env) : Prop :=
ew E 32 = Z_to_bv 64 g0 /\ ew E 33 = Z_to_bv 64 g1 /\ ew E 35 = Z_to_bv 64 du /\ ew E 36 = Z_to_bv 64 de /\
ew E 37 = Z_to_bv 64 gu /\ ew E 38 = Z_to_bv 64 ge.
Definition EnvX (b : Z) : env := AE2y.Env regs [g0; g1; b; du; de; gu; ge].

Lemma rdf : 0 <= x /\ x + n <= 2 ^ 63 /\ amem_range x n /\ range_addressable (aview tfibsegs HH mem) SHADOW_OFF x n.
Proof. pose proof HRD as (A & B1 & _ & _ & C & D & _). repeat split; assumption. Qed.
Lemma basics : 2 ^ 44 <= spZ regs <= 2 ^ 47 /\ kHighMemBeg + 72 <= spZ regs /\ spZ regs mod 16 = 0 /\ x + n <= 2 ^ 47 - 1 /\
(forall a, spZ regs - 72 <= a < spZ regs -> apresent HH mem a) /\ Forall (cell_holds B ly (aview tfibsegs HH mem)) (as_const B ly).
Proof.
pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof rdf as (Hx0 & Hxn & HAM & _). pose proof Hstk as Hstk'.
unfold RGN_SCR, amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *.
split; [lia|]. split; [lia|]. split; [exact Hal|]. split; [lia|]. split; [intros a Ha; apply Hpres; lia | exact (amc_const _ _ _ _ _ (proj1 HAR))].
Qed.
Lemma grains : 0 <= g0 /\ 8 * g0 <= x < 8 * g0 + 8 /\ 8 * g1 <= x + n - 1 < 8 * g1 + 8 /\ g0 <= g1 /\ g1 < 2 ^ 44 /\
du = 8 * gu /\ x <= 8 * gu <= x + 7 /\ de = 8 * ge /\ x + n - 7 <= 8 * ge <= x + n /\ 0 <= gu /\ ge < 2 ^ 44.
Proof.
pose proof basics as (_ & _ & _ & Bpn & _). pose proof rdf as (Hx0 & _).
pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)).
pose proof (Z.div_mod (x + n - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)).
pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + 7) 8 ltac:(lia)).
pose proof (Z.div_mod (x + n) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (x + n) 8 ltac:(lia)).
repeat split; lia.
Qed.
Lemma inv0 : INV (mkst regs (Z_to_bv 64 RG_ENTRY) mem (seg_rom tfibsegs)).
Proof.
pose proof basics as (_ & _ & _ & _ & Bpres & _). split; [intros z _; reflexivity|].
intros a Ha. cbn [ms_mem mkst]. destruct (Bpres a ltac:(lia)) as [_ [b Hb]]. rewrite Hb. discriminate.
Qed.
Lemma envok_reg : forall E, ENVOK E -> forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew E i = getr regs r.
Proof. intros E [HA _] i r Hi. pose proof (u5_range r). rewrite HA by lia. apply ew_Ereg_nat. exact Hi. Qed.
Lemma envok_Env : forall extra, ENVOK (AE2y.Env regs extra).
Proof.
intros extra. split; [|reflexivity]. intros i Hi. unfold AE2y.Env, Ereg. cbn [ew].
replace (i <? 32)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hi). reflexivity.
Qed.
Lemma env_facts : forall b, ew (EnvX b) 34 = Z_to_bv 64 b /\ EV (EnvX b) /\ ENVOK (EnvX b).
Proof.
intros b. unfold EnvX. split; [reflexivity|]. split; [|apply envok_Env].
unfold EV. repeat split; reflexivity.
Qed.

(* One symbolic run from a state whose only written window is the 64-byte frame. *)
Lemma rphase : forall E ss p ms md0 Q,
st_ok tfibsegs E ss (restrict HH ms) -> RUN ss = p -> noecall (snd p) = true -> wins_ok (ss_mem ss) = true ->
ENVOK E -> INV ms -> same_but_materialized md md0 ->
(forall ms1 md1, st_ok tfibsegs E (fst p) (restrict HH ms1) -> INV ms1 -> same_but_materialized md md1 -> SRr tfibsegs W (mkCfg ms1 md1) Q) ->
SRr tfibsegs W (mkCfg ms md0) Q.
Proof.
intros E ss [ss' st] ms md0 Q HS Hrun Hne Hwin HE [MEQ PSL] SBM K. cbn [fst snd] in *.
pose proof basics as (Bsp & _).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (envok_reg E HE 2 2%bv eq_refl); reflexivity).
eapply SRr_bind; [apply (icpt_phase W E ss ss' st ms md0 HS Hrun)|].
cbv beta. intros W1 c1 _ (-> & ms1 & mat1 & -> & HS1 & HF & _).
apply K.
- destruct st; try discriminate; exact HS1.
- split.
+ intros z Hz. rewrite (HF z); [apply MEQ; exact Hz|]. intros Hin.
pose proof (in_wrange_single_b E _ (bv_unsigned z) 2 (- RG_STK) 0 (spZ regs) Hwin E2 Hin) as X. unfold RG_STK in X. lia.
+ intros a Ha. rewrite (HF (Z_to_bv 64 a)); [apply PSL; exact Ha|]. intros Hin.
pose proof (in_wrange_single_b E _ _ 2 (- RG_STK) 0 (spZ regs) Hwin E2 Hin) as X.
rewrite unsigned_lit_small in X by lia. unfold RG_STK in X. lia.
- exact (same_but_materialized_trans _ _ _ SBM (with_vm_backing_same md0 mat1)).
Qed.
Ltac rph HS R := eapply (rphase _ _ _ _ _ _ HS R eq_refl eq_refl); [assumption | assumption | assumption |].

(* The call of mem_is_zero (AE2y.icpt_memisz): it reads the shadow of the granules fully inside the range, all 0, and
   writes only its ra slot, 72 bytes below the entry sp. *)
Lemma rmz : forall E ss ms md0 Q,
st_ok tfibsegs E ss (restrict HH ms) -> chkMZ ss = true -> ENVOK E -> EV E -> INV ms -> same_but_materialized md md0 -> gu < ge ->
(forall ms2 md2, st_ok tfibsegs (havoc E 56 (map (getr (ms_regs ms2)) MZ_CLOB)) (ss_after_mz ss (ss_mem ss) 56 RG_MZRET) (restrict HH ms2) ->
INV ms2 -> same_but_materialized md md2 -> SRr tfibsegs W (mkCfg ms2 md2) Q) ->
SRr tfibsegs W (mkCfg ms md0) Q.
Proof.
intros E ss ms md0 Q HS HC HE (E32 & E33 & E35 & E36 & E37 & E38) [MEQ PSL] SBM Hgg K.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
unfold chkMZ in HC. repeat rewrite andb_true_iff in HC.
destruct HC as ((((((((((Kpc & Krv) & Kat) & Kwf) & Knc) & Kma) & K10) & K11) & K2) & K1) & Kok).
apply Z.eqb_eq in Kpc.
assert (Hrv : ss_resv ss = None) by (unfold resv_none in Krv; destruct (ss_resv ss); [discriminate | reflexivity]).
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (envok_reg E HE 2 2%bv eq_refl); reflexivity).
assert (RD : forall (r : bv 5) v, sv_eqb (RG ss (bv_unsigned r)) v = true -> sv_denot E (sr_get (ss_regs ss) r) = sv_denot E v).
{ intros r v Hr. unfold RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite Hr. reflexivity. }
assert (R10 : sv_denot E (sr_get (ss_regs ss) 10) = Z_to_bv 64 (gu + SB)).
{ rewrite (RD 10%bv SGU K10). unfold SGU. cbn [sv_denot]. rewrite E37, unsigned_lit_small by lia. reflexivity. }
assert (R11 : sv_denot E (sr_get (ss_regs ss) 11) = Z_to_bv 64 (ge - gu)).
{ rewrite (RD 11%bv SLEN K11). exact (AE2y.U_mz_len E 37 38 gu ge E37 E38 ltac:(lia) ltac:(lia)). }
assert (R2 : sv_denot E (sr_get (ss_regs ss) 2) = Z_to_bv 64 (spZ regs - 64)).
{ rewrite (RD 2%bv (SOff 2 (- RG_STK)) K2). cbn [sv_denot]. rewrite E2. unfold RG_STK. f_equal; lia. }
assert (R1 : sv_denot E (sr_get (ss_regs ss) 1) = Z_to_bv 64 RG_MZRET) by (rewrite (RD 1%bv (SLit RG_MZRET) K1); reflexivity).
assert (SLW : forall z, spZ regs - 64 - 8 <= z < spZ regs - 64 -> writable_at tfibsegs (mrestrict HH (ms_mem ms)) z).
{ intros z Hz. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|].
destruct (ms_mem ms (Z_to_bv 64 z)) as [b|] eqn:Eb; [| exfalso; exact (PSL z ltac:(lia) Eb)].
split; [exact (proj1 (Bpres z ltac:(lia))) | exists b; exact Eb]. }
assert (SZERO : forall a, gu + SB <= a < gu + SB + (ge - gu) -> aview tfibsegs HH (ms_mem ms) a = Some 0).
{ intros a Ha.
rewrite (aview_same HH mem (ms_mem ms) a) by (apply MEQ; rewrite unsigned_lit_small by (unfold SB, kHighMemBeg in *; lia); unfold SB, kHighMemBeg in *; lia).
replace a with (SB + (a - SB)) by lia. apply (AE2y.ra_granule_zero (aview tfibsegs HH mem) x n (a - SB) HRA); [unfold SB in *; lia | lia]. }
assert (HOFF : Forall (fun r => 0 <= base_val E (YP09.r_base r) + YP09.r_lo r /\ base_val E (YP09.r_base r) + YP09.r_hi r <= 2 ^ 64 /\
(base_val E (YP09.r_base r) + YP09.r_hi r <= spZ regs - 64 - 8 \/ spZ regs - 64 <= base_val E (YP09.r_base r) + YP09.r_lo r) /\
YP09.r_lo r <= YP09.r_wlo r /\ YP09.r_whi r <= YP09.r_hi r) (ss_mem ss)).
{ apply Forall_forall. intros r Hr. rewrite forallb_forall in Kok. specialize (Kok r Hr). unfold okreg in Kok.
repeat rewrite orb_true_iff in Kok. repeat rewrite andb_true_iff in Kok.
destruct Kok as [[K0|K0]|K0]; destruct K0 as ((((Kb & Kl) & Kh) & Kwl) & Kwh).
- apply obase_eqb_eq in Kb. apply Z.eqb_eq in Kl, Kh, Kwl, Kwh. rewrite Kb. cbn [base_val]. rewrite E2, Kl, Kh, Kwl, Kwh. unfold RG_STK. lia.
- apply Z.eqb_eq in Kl, Kh, Kwl, Kwh. rewrite Kl, Kh, Kwl, Kwh. apply orb_true_iff in Kb.
destruct Kb as [Kb|Kb]; apply obase_eqb_eq in Kb; rewrite Kb; cbn [base_val]; [rewrite E32 | rewrite E33];
rewrite unsigned_lit_small by lia; unfold SB, kHighMemBeg in *; lia.
- apply obase_eqb_eq in Kb. apply Z.leb_le in Kl, Kh, Kwl, Kwh. rewrite Kb. cbn [base_val]. unfold kHighMemBeg in *. lia. }
eapply SRr_bind; [exact (AE2y.icpt_memisz W E ss ms md0 56 (ss_mem ss) (gu + SB) (ge - gu) (spZ regs - 64) RG_MZRET HS Hrv Kpc Kat Kwf Knc Kma (submem_refl _)
R10 R11 R2 R1 ltac:(lia) ltac:(unfold SB; lia) ltac:(unfold SB; lia) ltac:(unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia) ltac:(unfold RG_MZRET; lia)
(AE2y.ret_ok_lit RG_MZRET ltac:(unfold RG_MZRET; lia) eq_refl) ltac:(left; unfold SB, kHighMemBeg in *; lia) SLW SZERO HOFF)|].
cbv beta. intros W2 c2 _ (-> & ms2 & mat2 & -> & HS2 & HM & HP).
apply K.
- exact HS2.
- split.
+ intros z Hz. rewrite (HM z) by lia. apply MEQ. exact Hz.
+ intros a Ha. apply HP. rewrite unsigned_lit_small by lia. lia.
- exact (same_but_materialized_trans _ _ _ SBM (with_vm_backing_same md0 mat2)).
Qed.

(* The `ret` at 0x55afc, and the art_post_cf conclusion. *)
Lemma fin : forall E ss ms md0,
st_ok tfibsegs E ss (restrict HH ms) -> chkF ss = true -> ENVOK E -> INV ms -> same_but_materialized md md0 ->
SRr tfibsegs W (mkCfg ms md0) POST.
Proof.
intros E ss ms md0 HS HC HE [MEQ PSL] SBM.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof (amc_layout _ _ _ _ _ (proj1 HAR)) as HLY. pose proof (lo_top ly HLY) as (Lbot & Ltop & _ & Lhi & _ & _ & Lbeg).
pose proof Hstk as Hstk'. unfold RGN_SCR in Hstk'.
unfold chkF in HC. repeat rewrite andb_true_iff in HC.
destruct HC as (((((Kpc & Krv) & Khd) & K10) & K1) & Kcs).
apply Z.eqb_eq in Kpc.
assert (Hrv : ss_resv ss = None) by (unfold resv_none in Krv; destruct (ss_resv ss); [discriminate | reflexivity]).
unfold head_ok in Khd. destruct (ss_mem ss) as [|r0 rest] eqn:Hmem; [discriminate|].
repeat rewrite andb_true_iff in Khd. destruct Khd as ((Hbase & Hwlo) & Hwhi).
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi.
assert (E2 : bv_unsigned (ew E 2) = spZ regs) by (rewrite (envok_reg E HE 2 2%bv eq_refl); reflexivity).
assert (RD : forall (r : bv 5) v, sv_eqb (RG ss (bv_unsigned r)) v = true -> getr (ms_regs ms) r = sv_denot E v).
{ intros r v Hr. unfold RG in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr. rewrite <- Hr. exact (st_ok_restrict_reg tfibsegs HH E ss ms r HS). }
assert (Q1 : getr (ms_regs ms) 1 = getr regs 1).
{ rewrite (RD 1%bv (SOff 1 0) K1). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact (envok_reg E HE 1 1%bv eq_refl). }
assert (Q10 : getr (ms_regs ms) 10 = w64 0) by (rewrite (RD 10%bv (SLit 0) K10); reflexivity).
assert (AV : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 72 <= a < spZ regs) -> aview tfibsegs HH (ms_mem ms) a = aview tfibsegs HH mem a).
{ intros a Hr Ha. apply aview_same. apply MEQ. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PW : forall a, spZ regs - 64 <= a < spZ regs -> apresent HH (ms_mem ms) a).
{ intros a Ha. apply (AF0x.st_ok_window_apresent HH E ss ms 0 r0 a HS ltac:(rewrite Hmem; reflexivity)); [| unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia].
rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite E2. unfold RG_STK. lia. }
assert (PS : forall a, spZ regs - 72 <= a < spZ regs - 64 -> apresent HH (ms_mem ms) a).
{ intros a Ha. split; [exact (proj1 (Bpres a ltac:(lia)))|].
destruct (ms_mem ms (Z_to_bv 64 a)) as [b|] eqn:Eb; [exists b; reflexivity | exfalso; exact (PSL a Ha Eb)]. }
assert (PM : forall a, apresent HH mem a -> apresent HH (ms_mem ms) a).
{ intros a Hpa. rewrite (AE2y.apresent_mod _ (ms_mem ms) a). rewrite (AE2y.apresent_mod _ mem a) in Hpa.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (spZ regs - 72)) as [L1|L1]; [apply (apresent_same HH mem (ms_mem ms) a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hpa]|].
destruct (Z_lt_le_dec a' (spZ regs - 64)) as [L2|L2]; [apply PS; lia|].
destruct (Z_lt_le_dec a' (spZ regs)) as [L3|L3]; [apply PW; lia|].
apply (apresent_same HH mem (ms_mem ms) a'); [apply MEQ; rewrite unsigned_lit_small by lia; lia | exact Hpa]. }
eapply (SRr_ret_at tfibsegs tbl_icpt tbl_icpt_ok AF0x.Hwx_tfa W E ss ms md0 _ HS Hrv); [rewrite Kpc; exact probe_ret|].
intros mat'.
assert (HSBM : same_but_materialized md (with_vm_backing (m_vm_lazy md0) mat' md0))
by exact (same_but_materialized_trans _ _ _ SBM (with_vm_backing_same md0 mat')).
pose proof (same_but_materialized_frame md _ HSBM) as MF.
replace (v_jalr (getr (ms_regs ms) 1) 0) with (w64 (raZ regs)) by (rewrite Q1; unfold raZ, w64; rewrite Z_to_bv_bv_unsigned; symmetry; exact Hra).
unfold art_post_cf. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), (with_vm_backing (m_vm_lazy md0) mat' md0).
split; [reflexivity|].
split; [|split; [|split; [exact HSBM|split; [exact Q10|split; [|split; [|split]]]]]].
- apply (alc_frame _ _ LAWS ly S Hp W mem md (ms_mem ms) _ HAR).
+ intros a Hr Hown. apply AV; [exact Hr|]. intros Hs. exact (alc_stack _ _ LAWS ly S Hp W mem md a HAR ltac:(lia) Hown).
+ intros a Hv. rewrite (AE2y.aview_mod _ (ms_mem ms) a). rewrite (AE2y.aview_mod _ mem a) in Hv.
assert (Hr : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (spZ regs - 72)) as [L1|L1]; [rewrite AV by lia; exact Hv|].
destruct (Z_lt_le_dec a' (spZ regs)) as [L3|L3]; [| rewrite AV by lia; exact Hv].
apply AE2y.aview_some_of_apresent. destruct (Z_lt_le_dec a' (spZ regs - 64)); [apply PS; lia | apply PW; lia].
+ apply MF. + apply MF. + apply MF.
+ exact (AE2y.hs_kept_win _ _ _ _ _ _ _ _ MEQ Bpres ltac:(lia) ltac:(lia)).
- exact (AE2y.aregs_preserved_of_st_ok HH E ss ms regs [] HS HE Kcs).
- intros a Hr Hs _. apply AV; [exact Hr|]. unfold ascratch_stk in Hs. lia.
- exact PM.
- intros a Ha. unfold ascratch_stk in Ha.
destruct (Z_lt_le_dec a (spZ regs - 72)) as [L1|L1]; [|destruct (Z_lt_le_dec a (spZ regs - 64)) as [L2|L2]; [apply PS; lia | apply PW; lia]].
apply (apresent_same HH mem (ms_mem ms) a); [apply MEQ; rewrite unsigned_lit_small by (unfold kHighMemBeg in *; lia); lia | apply Hpres; lia].
- (* the raw-memory frame: the walk writes only [sp - 72, sp), inside the scratch window *)
intros z Hs _. apply MEQ. unfold ascratch_stk in Hs. lia.
Qed.

(* The test 0x55ac0 (shadow_end <= shadow_beg) both ways, the call of mem_is_zero, and the return. *)
Lemma tail : forall E e ms md0 pl pm pg,
st_ok tfibsegs E e (restrict HH ms) -> ENVOK E -> EV E -> INV ms -> same_but_materialized md md0 ->
TL e = pl -> TM pl = pm -> TG e = pg -> tail_chk e pl pm pg = true ->
SRr tfibsegs W (mkCfg ms md0) POST.
Proof.
intros E e ms md0 pl pm pg HS HE HV I0 SBM Rl Rm Rg HC.
pose proof HV as (E32 & E33 & E35 & E36 & E37 & E38).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
unfold tail_chk in HC. repeat rewrite andb_true_iff in HC.
destruct HC as (((((((Kw & Kmz) & Kel) & Kwl) & Kfm) & Kem) & Kfg) & Keg).
destruct (Z_lt_le_dec gu ge) as [Hlt|Hge].
- pose proof (st_ok_add_cond_neg tfibsegs E _ _ BC_GEU SGU SGE HS (AE2y.br_sbeg_lt_send E 37 38 gu ge E37 E38 ltac:(lia) ltac:(unfold SB; lia))) as HS'.
change (neg_bc BC_GEU) with BC_LTU in HS'.
apply (rphase E _ pl ms md0 POST HS' Rl Kel Kw HE I0 SBM). intros ms1 md1 HS1 I1 S1.
apply (rmz E (fst pl) ms1 md1 POST HS1 Kmz HE HV I1 S1 Hlt). intros ms2 md2 HS2 I2 S2.
assert (HE' : ENVOK (havoc E 56 (map (getr (ms_regs ms2)) MZ_CLOB))) by (apply env_agree_havoc_ge; [lia | exact HE]).
apply (rphase _ _ pm ms2 md2 POST HS2 Rm Kem Kwl HE' I2 S2). intros ms3 md3 HS3 I3 S3.
exact (fin _ (fst pm) ms3 md3 HS3 Kfm HE' I3 S3).
- pose proof (st_ok_add_cond tfibsegs E _ _ BC_GEU SGU SGE HS (br_sbeg_ge_send E 37 38 gu ge E37 E38 ltac:(lia) ltac:(unfold SB; lia))) as HS'.
apply (rphase E _ pg ms md0 POST HS' Rg Keg Kw HE I0 SBM). intros ms1 md1 HS1 I1 S1.
exact (fin E (fst pg) ms1 md1 HS1 Kfg HE I1 S1).
Qed.

(* The entry states. *)
Lemma atomsL : forall b, x + 8 <= kLowMemEnd -> 0 <= b < 8 -> atoms_ok (EnvX b) factsL.
Proof.
intros b BL Hb.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
destruct (env_facts b) as (E34 & (E32 & E33 & E35 & E36 & E37 & E38) & HE).
assert (E2 : bv_unsigned (ew (EnvX b) 2) = spZ regs) by (rewrite (envok_reg _ HE 2 2%bv eq_refl); reflexivity).
assert (E10 : ew (EnvX b) 10 = Z_to_bv 64 x) by (rewrite (envok_reg _ HE 10 10%bv eq_refl), G10; reflexivity).
assert (E11 : ew (EnvX b) 11 = Z_to_bv 64 n) by (rewrite (envok_reg _ HE 11 11%bv eq_refl), G11; reflexivity).
assert (Hxn' : x + n <= kLowMemEnd - 1) by (destruct HAM as [A|[A _]]; [exact A | unfold kLowMemEnd, kHighMemBeg in *; lia]).
unfold kLowMemEnd in *.
cbn [atoms_ok factsL]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E32, E33, E34, E35, E36, E37, E38, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8.
repeat split; try lia; try apply Z.mod_1_r.
all: try (first [rewrite Gdu | rewrite Gde]; rewrite Z.mul_comm; apply Z_mod_mult).
Qed.
Lemma atomsH : forall b, kHighMemBeg <= x -> x + 8 <= kHighMemEnd -> 0 <= b < 8 -> atoms_ok (EnvX b) factsH.
Proof.
intros b BH1 BH2 Hb.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
destruct (env_facts b) as (E34 & (E32 & E33 & E35 & E36 & E37 & E38) & HE).
assert (E2 : bv_unsigned (ew (EnvX b) 2) = spZ regs) by (rewrite (envok_reg _ HE 2 2%bv eq_refl); reflexivity).
assert (E10 : ew (EnvX b) 10 = Z_to_bv 64 x) by (rewrite (envok_reg _ HE 10 10%bv eq_refl), G10; reflexivity).
assert (E11 : ew (EnvX b) 11 = Z_to_bv 64 n) by (rewrite (envok_reg _ HE 11 11%bv eq_refl), G11; reflexivity).
unfold kHighMemBeg, kHighMemEnd in *.
cbn [atoms_ok factsH]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E2, E10, E11, E32, E33, E34, E35, E36, E37, E38, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 3) with 8.
repeat split; try lia; try apply Z.mod_1_r.
all: try (first [rewrite Gdu | rewrite Gde]; rewrite Z.mul_comm; apply Z_mod_mult).
Qed.
Lemma entA : forall F b1, g0 < g1 -> aview tfibsegs HH mem (SB + g1) = Some b1 -> 0 <= b1 < 8 -> atoms_ok (EnvX b1) F ->
st_ok tfibsegs (EnvX b1) (ssA F) (restrict HH (mkst regs (Z_to_bv 64 RG_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros F b1 Hg Hb1 Hb8 HAt.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
destruct (env_facts b1) as (E34 & (E32 & E33 & E35 & E36 & E37 & E38) & HE).
assert (E2 : bv_unsigned (ew (EnvX b1) 2) = spZ regs) by (rewrite (envok_reg _ HE 2 2%bv eq_refl); reflexivity).
assert (E10 : ew (EnvX b1) 10 = Z_to_bv 64 x) by (rewrite (envok_reg _ HE 10 10%bv eq_refl), G10; reflexivity).
assert (E11 : ew (EnvX b1) 11 = Z_to_bv 64 n) by (rewrite (envok_reg _ HE 11 11%bv eq_refl), G11; reflexivity).
set (EE := EnvX b1) in *.
rewrite restrict_mkst_fx. unfold ssA.
unfold EE, EnvX, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b1; du; de; gu; ge])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|exact (icpt_rodata_ok_x B TB ly HH mem EE BM)]]].
+ unfold stkR. apply (region_ok_stack tfibsegs EE _ 2 (spZ regs) (- RG_STK)); [exact E2 | unfold RG_STK; lia | lia |].
intros a Ha. unfold RG_STK in Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply Bpres. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil]. apply chunk_ok_zero. intros i Hi. rewrite (AF0x.aview_byte HH mem _ 0); [reflexivity|].
rewrite <- (AE2y.ra_granule_zero (aview tfibsegs HH mem) x n g0 HRA ltac:(lia) Hx0). unfold SB. f_equal. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 33%nat)) with (bv_unsigned (ew EE 33)). rewrite E33, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g1 _ 1 (SOff 34 0) b1); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply AE2y.val_mem1_of_aview. rewrite <- Hb1. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkR, shA, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, E33, !unsigned_lit_small by lia. unfold RG_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [exact HAt|]. split; [exact I|].
cbn [f_alias aliasA alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
+ apply U_inj. rewrite U_srl3, (U_atom EE 10 x E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
+ apply U_inj. rewrite U_srl3, (AE2y.U_dn1 EE 10 11 x n E10 E11), (U_atom EE 33 g1 E33) by lia. reflexivity.
+ apply U_inj. rewrite AE2y.U_and_m8, (U_atom_off EE 10 x 7 E10), (U_atom EE 35 du E35) by lia. pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). lia.
+ apply U_inj. rewrite AE2y.U_and_m8, (AE2y.U_add2 EE 10 11 x n E10 E11), (U_atom EE 36 de E36) by lia. pose proof (Z.div_mod (x + n) 8 ltac:(lia)). lia.
+ apply U_inj. rewrite U_srl3, (U_atom EE 35 du E35), (U_atom EE 37 gu E37) by lia. rewrite Z.div_mul by lia. reflexivity.
+ apply U_inj. rewrite U_srl3, (U_atom EE 36 de E36), (U_atom EE 38 ge E38) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma entB : forall F b, g0 = g1 -> aview tfibsegs HH mem (SB + g0) = Some b -> 0 <= b < 8 -> atoms_ok (EnvX b) F ->
st_ok tfibsegs (EnvX b) (ssB F) (restrict HH (mkst regs (Z_to_bv 64 RG_ENTRY) mem (seg_rom tfibsegs))).
Proof.
intros F b Hg Hb Hb8 HAt.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
destruct (env_facts b) as (E34 & (E32 & E33 & E35 & E36 & E37 & E38) & HE).
assert (E2 : bv_unsigned (ew (EnvX b) 2) = spZ regs) by (rewrite (envok_reg _ HE 2 2%bv eq_refl); reflexivity).
assert (E10 : ew (EnvX b) 10 = Z_to_bv 64 x) by (rewrite (envok_reg _ HE 10 10%bv eq_refl), G10; reflexivity).
assert (E11 : ew (EnvX b) 11 = Z_to_bv 64 n) by (rewrite (envok_reg _ HE 11 11%bv eq_refl), G11; reflexivity).
set (EE := EnvX b) in *.
rewrite restrict_mkst_fx. unfold ssB.
unfold EE, EnvX, AE2y.Env. apply (entry_st_ok_full tfibsegs); change (Ereg regs (map (Z_to_bv 64) [g0; g1; b; du; de; gu; ge])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|exact (icpt_rodata_ok_x B TB ly HH mem EE BM)]].
+ unfold stkR. apply (region_ok_stack tfibsegs EE _ 2 (spZ regs) (- RG_STK)); [exact E2 | unfold RG_STK; lia | lia |].
intros a Ha. unfold RG_STK in Ha. apply AF0x.apresent_writable; [unfold AF0x.TFIB_IMG_END, kHighMemBeg in *; lia|]. apply Bpres. lia.
+ unfold region_ok, SB. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
change (base_val EE (Some 32%nat)) with (bv_unsigned (ew EE 32)). rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
apply Forall_cons; [|apply Forall_nil].
eapply (chunk_ok_val tfibsegs EE _ g0 _ 1 (SOff 34 0) b); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
apply AE2y.val_mem1_of_aview. rewrite <- Hb. unfold SB. f_equal. lia.
- apply pairwise_disjoint_of_extents. unfold stkR, shB, icpt_rodata, ro_region, extent_of_region, SB.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite E2, E32, !unsigned_lit_small by lia. unfold RG_STK.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in Bhi. repeat split; lia.
- split; [exact HAt|]. split; [exact I|].
cbn [f_alias aliasB alias_ok]. split; [|split; [|split; [|split; [|split; [|split; [|exact I]]]]]].
+ apply U_inj. rewrite U_srl3, (U_atom EE 10 x E10), (U_atom EE 32 g0 E32) by lia. reflexivity.
+ apply U_inj. rewrite U_srl3, (AE2y.U_dn1 EE 10 11 x n E10 E11), (U_atom EE 32 g0 E32) by lia. symmetry. exact Hg.
+ apply U_inj. rewrite AE2y.U_and_m8, (U_atom_off EE 10 x 7 E10), (U_atom EE 35 du E35) by lia. pose proof (Z.div_mod (x + 7) 8 ltac:(lia)). lia.
+ apply U_inj. rewrite AE2y.U_and_m8, (AE2y.U_add2 EE 10 11 x n E10 E11), (U_atom EE 36 de E36) by lia. pose proof (Z.div_mod (x + n) 8 ltac:(lia)). lia.
+ apply U_inj. rewrite U_srl3, (U_atom EE 35 du E35), (U_atom EE 37 gu E37) by lia. rewrite Z.div_mul by lia. reflexivity.
+ apply U_inj. rewrite U_srl3, (U_atom EE 36 de E36), (U_atom EE 38 ge E38) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma pathLA : x + 8 <= kLowMemEnd -> g0 < g1 -> SRr tfibsegs W (cfg_at tfibsegs RG_ENTRY regs mem md) POST.
Proof.
intros BL Hg.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
assert (Hxn' : x + n <= kLowMemEnd - 1) by (destruct HAM as [A|[A _]]; [exact A | unfold kLowMemEnd, kHighMemBeg in *; lia]).
destruct (AE2y.ra_last (aview tfibsegs HH mem) x n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (entA factsL b1 Hg Hb1 Hb8 (atomsL b1 BL Hb8)) as HS0.
destruct (env_facts b1) as (E34 & HV & HE). pose proof HV as (E32 & E33 & E35 & E36 & E37 & E38).
set (EE := EnvX b1) in *.
assert (E10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (envok_reg EE HE 10 10%bv eq_refl), G10; reflexivity).
assert (E11 : ew EE 11 = Z_to_bv 64 n) by (rewrite (envok_reg EE HE 11 11%bv eq_refl), G11; reflexivity).
pose proof inv0 as I0. pose proof (same_but_materialized_refl md) as S0.
unfold cfg_at. change (w64 RG_ENTRY) with (Z_to_bv 64 RG_ENTRY).
rph HS0 rLA0. intros ms1 md1 HS1 I1 S1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (SLit 2147450879) (RG (fst pLA0) 18) HS1 (AE2y.br_end_low EE 10 11 x n E10 E11 ltac:(lia) ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS1'.
rph HS1' rLA1. intros ms2 md2 HS2 I2 S2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG (fst pLA1) 8) (RG (fst pLA1) 18) HS2 (AE2y.br_beg_lt_end EE 10 11 x n E10 E11 ltac:(lia) ltac:(lia) ltac:(lia))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'.
rph HS2' rLA2. intros ms3 md3 HS3 I3 S3.
destruct (Z.eq_dec b1 0) as [Hz|Hnz].
- pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG (fst pLA2) 11) (SLit 0) HS3 (AE2y.rp_b1_zero EE 34 ltac:(rewrite E34, Hz; reflexivity))) as HS3'.
rph HS3' rLA3z. intros ms4 md4 HS4 I4 S4.
exact (tail EE _ ms4 md4 _ _ _ HS4 HE HV I4 S4 rLA3z_l rLA3z_m rLA3z_g cLA3z).
- assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hnz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG (fst pLA2) 11) (SLit 0) HS3 (AE2y.rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS3'.
change (neg_bc BC_EQ) with BC_NE in HS3'.
rph HS3' rLA3n. intros ms4 md4 HS4 I4 S4.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG (fst pLA3n) 12) (RG (fst pLA3n) 11) HS4 (AE2y.rp_blt_last EE 10 11 34 x n b1 E10 E11 E34 Hx0 ltac:(lia) Hxn Hlt)) as HS4'.
rph HS4' rLA4n. intros ms5 md5 HS5 I5 S5.
exact (tail EE _ ms5 md5 _ _ _ HS5 HE HV I5 S5 rLA4n_l rLA4n_m rLA4n_g cLA4n).
Qed.
Lemma pathLB : x + 8 <= kLowMemEnd -> g0 = g1 -> SRr tfibsegs W (cfg_at tfibsegs RG_ENTRY regs mem md) POST.
Proof.
intros BL Hg.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
assert (Hxn' : x + n <= kLowMemEnd - 1) by (destruct HAM as [A|[A _]]; [exact A | unfold kLowMemEnd, kHighMemBeg in *; lia]).
destruct (AE2y.ra_last (aview tfibsegs HH mem) x n HRA ltac:(lia)) as (b & Hb1 & Hok1).
destruct (ra_first (aview tfibsegs HH mem) x n HRA ltac:(lia)) as (b0 & Hb0 & Hok0).
assert (Eb : b0 = b) by (pose proof Hb0 as X0; rewrite Hg, Hb1 in X0; injection X0 as X0; lia). subst b0.
assert (Hb8 : 0 <= b < 8) by (destruct Hok1 as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (entB factsL b Hg Hb0 Hb8 (atomsL b BL Hb8)) as HS0.
destruct (env_facts b) as (E34 & HV & HE). pose proof HV as (E32 & E33 & E35 & E36 & E37 & E38).
set (EE := EnvX b) in *.
assert (E10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (envok_reg EE HE 10 10%bv eq_refl), G10; reflexivity).
assert (E11 : ew EE 11 = Z_to_bv 64 n) by (rewrite (envok_reg EE HE 11 11%bv eq_refl), G11; reflexivity).
pose proof inv0 as I0. pose proof (same_but_materialized_refl md) as S0.
unfold cfg_at. change (w64 RG_ENTRY) with (Z_to_bv 64 RG_ENTRY).
rph HS0 rLB0. intros ms1 md1 HS1 I1 S1.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_GEU (SLit 2147450879) (RG (fst pLB0) 18) HS1 (AE2y.br_end_low EE 10 11 x n E10 E11 ltac:(lia) ltac:(lia) ltac:(unfold kLowMemEnd in *; lia))) as HS1'.
rph HS1' rLB1. intros ms2 md2 HS2 I2 S2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG (fst pLB1) 8) (RG (fst pLB1) 18) HS2 (AE2y.br_beg_lt_end EE 10 11 x n E10 E11 ltac:(lia) ltac:(lia) ltac:(lia))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'.
rph HS2' rLB2. intros ms3 md3 HS3 I3 S3.
destruct (Z.eq_dec b 0) as [Hz|Hnz].
- pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG (fst pLB2) 12) (SLit 0) HS3 (AE2y.rp_b1_zero EE 34 ltac:(rewrite E34, Hz; reflexivity))) as HS3'.
rph HS3' rLB3z. intros ms4 md4 HS4 I4 S4.
exact (tail EE _ ms4 md4 _ _ _ HS4 HE HV I4 S4 rLB3z_l rLB3z_m rLB3z_g cLB3z).
- assert (Hlt0 : x mod 8 < b < 8) by (destruct Hok0 as [Hz0 | [Hlt Hb']]; [exfalso; exact (Hnz Hz0) | lia]).
assert (Hlt1 : (x + n - 1) mod 8 < b < 8) by (destruct Hok1 as [Hz0 | [Hlt Hb']]; [exfalso; exact (Hnz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG (fst pLB2) 12) (SLit 0) HS3 (AE2y.rp_b1_nonzero EE 34 b E34 ltac:(lia))) as HS3'.
change (neg_bc BC_EQ) with BC_NE in HS3'.
rph HS3' rLB3n. intros ms4 md4 HS4 I4 S4.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG (fst pLB3n) 13) (RG (fst pLB3n) 12) HS4 (rp_blt_first EE 10 34 x b E10 E34 ltac:(lia) Hlt0)) as HS4'.
rph HS4' rLB4n. intros ms5 md5 HS5 I5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG (fst pLB4n) 12) (RG (fst pLB4n) 11) HS5 (AE2y.rp_blt_last EE 10 11 34 x n b E10 E11 E34 Hx0 ltac:(lia) Hxn Hlt1)) as HS5'.
rph HS5' rLB5n. intros ms6 md6 HS6 I6 S6.
exact (tail EE _ ms6 md6 _ _ _ HS6 HE HV I6 S6 rLB5n_l rLB5n_m rLB5n_g cLB5n).
Qed.
Lemma pathHA : kHighMemBeg <= x -> x + 8 <= kHighMemEnd -> g0 < g1 -> SRr tfibsegs W (cfg_at tfibsegs RG_ENTRY regs mem md) POST.
Proof.
intros BH1 BH2 Hg.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
assert (Hxn' : x + n <= kHighMemEnd - 1) by (unfold kHighMemEnd; lia).
destruct (AE2y.ra_last (aview tfibsegs HH mem) x n HRA ltac:(lia)) as (b1 & Hb1 & Hok).
assert (Hb8 : 0 <= b1 < 8) by (destruct Hok as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (entA factsH b1 Hg Hb1 Hb8 (atomsH b1 BH1 BH2 Hb8)) as HS0.
destruct (env_facts b1) as (E34 & HV & HE). pose proof HV as (E32 & E33 & E35 & E36 & E37 & E38).
set (EE := EnvX b1) in *.
assert (E10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (envok_reg EE HE 10 10%bv eq_refl), G10; reflexivity).
assert (E11 : ew EE 11 = Z_to_bv 64 n) by (rewrite (envok_reg EE HE 11 11%bv eq_refl), G11; reflexivity).
pose proof inv0 as I0. pose proof (same_but_materialized_refl md) as S0.
unfold cfg_at. change (w64 RG_ENTRY) with (Z_to_bv 64 RG_ENTRY).
rph HS0 rHA0. intros ms1 md1 HS1 I1 S1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (SLit 140737488355327) (RG (fst pHA0) 18) HS1 (AE2y.br_end_high EE 10 11 x n E10 E11 ltac:(lia) ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
rph HS1' rHA1. intros ms2 md2 HS2 I2 S2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG (fst pHA1) 8) (RG (fst pHA1) 18) HS2 (AE2y.br_beg_lt_end EE 10 11 x n E10 E11 ltac:(lia) ltac:(lia) ltac:(lia))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'.
rph HS2' rHA2. intros ms3 md3 HS3 I3 S3.
destruct (Z.eq_dec b1 0) as [Hz|Hnz].
- pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG (fst pHA2) 11) (SLit 0) HS3 (AE2y.rp_b1_zero EE 34 ltac:(rewrite E34, Hz; reflexivity))) as HS3'.
rph HS3' rHA3z. intros ms4 md4 HS4 I4 S4.
exact (tail EE _ ms4 md4 _ _ _ HS4 HE HV I4 S4 rHA3z_l rHA3z_m rHA3z_g cHA3z).
- assert (Hlt : (x + n - 1) mod 8 < b1 < 8) by (destruct Hok as [Hz0 | [Hlt Hb]]; [exfalso; exact (Hnz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG (fst pHA2) 11) (SLit 0) HS3 (AE2y.rp_b1_nonzero EE 34 b1 E34 ltac:(lia))) as HS3'.
change (neg_bc BC_EQ) with BC_NE in HS3'.
rph HS3' rHA3n. intros ms4 md4 HS4 I4 S4.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG (fst pHA3n) 12) (RG (fst pHA3n) 11) HS4 (AE2y.rp_blt_last EE 10 11 34 x n b1 E10 E11 E34 Hx0 ltac:(lia) Hxn Hlt)) as HS4'.
rph HS4' rHA4n. intros ms5 md5 HS5 I5 S5.
exact (tail EE _ ms5 md5 _ _ _ HS5 HE HV I5 S5 rHA4n_l rHA4n_m rHA4n_g cHA4n).
Qed.
Lemma pathHB : kHighMemBeg <= x -> x + 8 <= kHighMemEnd -> g0 = g1 -> SRr tfibsegs W (cfg_at tfibsegs RG_ENTRY regs mem md) POST.
Proof.
intros BH1 BH2 Hg.
pose proof basics as (Bsp & Bhi & Bal & Bpn & Bpres & BM).
pose proof grains as (Gg0 & Gx0 & Gx1 & G01 & G1hi & Gdu & Ggu & Gde & Gge & Ggu0 & Gge1).
pose proof rdf as (Hx0 & Hxn & HAM & HRA).
assert (Hxn' : x + n <= kHighMemEnd - 1) by (unfold kHighMemEnd; lia).
destruct (AE2y.ra_last (aview tfibsegs HH mem) x n HRA ltac:(lia)) as (b & Hb1 & Hok1).
destruct (ra_first (aview tfibsegs HH mem) x n HRA ltac:(lia)) as (b0 & Hb0 & Hok0).
assert (Eb : b0 = b) by (pose proof Hb0 as X0; rewrite Hg, Hb1 in X0; injection X0 as X0; lia). subst b0.
assert (Hb8 : 0 <= b < 8) by (destruct Hok1 as [-> | [Hlt Hb]]; [lia|]; pose proof (Z.mod_pos_bound (x + n - 1) 8 ltac:(lia)); lia).
pose proof (entB factsH b Hg Hb0 Hb8 (atomsH b BH1 BH2 Hb8)) as HS0.
destruct (env_facts b) as (E34 & HV & HE). pose proof HV as (E32 & E33 & E35 & E36 & E37 & E38).
set (EE := EnvX b) in *.
assert (E10 : ew EE 10 = Z_to_bv 64 x) by (rewrite (envok_reg EE HE 10 10%bv eq_refl), G10; reflexivity).
assert (E11 : ew EE 11 = Z_to_bv 64 n) by (rewrite (envok_reg EE HE 11 11%bv eq_refl), G11; reflexivity).
pose proof inv0 as I0. pose proof (same_but_materialized_refl md) as S0.
unfold cfg_at. change (w64 RG_ENTRY) with (Z_to_bv 64 RG_ENTRY).
rph HS0 rHB0. intros ms1 md1 HS1 I1 S1.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_LTU (SLit 140737488355327) (RG (fst pHB0) 18) HS1 (AE2y.br_end_high EE 10 11 x n E10 E11 ltac:(lia) ltac:(lia) ltac:(unfold kHighMemEnd in *; lia))) as HS1'.
change (neg_bc BC_LTU) with BC_GEU in HS1'.
rph HS1' rHB1. intros ms2 md2 HS2 I2 S2.
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_GEU (RG (fst pHB1) 8) (RG (fst pHB1) 18) HS2 (AE2y.br_beg_lt_end EE 10 11 x n E10 E11 ltac:(lia) ltac:(lia) ltac:(lia))) as HS2'.
change (neg_bc BC_GEU) with BC_LTU in HS2'.
rph HS2' rHB2. intros ms3 md3 HS3 I3 S3.
destruct (Z.eq_dec b 0) as [Hz|Hnz].
- pose proof (st_ok_add_cond tfibsegs EE _ _ BC_EQ (RG (fst pHB2) 12) (SLit 0) HS3 (AE2y.rp_b1_zero EE 34 ltac:(rewrite E34, Hz; reflexivity))) as HS3'.
rph HS3' rHB3z. intros ms4 md4 HS4 I4 S4.
exact (tail EE _ ms4 md4 _ _ _ HS4 HE HV I4 S4 rHB3z_l rHB3z_m rHB3z_g cHB3z).
- assert (Hlt0 : x mod 8 < b < 8) by (destruct Hok0 as [Hz0 | [Hlt Hb']]; [exfalso; exact (Hnz Hz0) | lia]).
assert (Hlt1 : (x + n - 1) mod 8 < b < 8) by (destruct Hok1 as [Hz0 | [Hlt Hb']]; [exfalso; exact (Hnz Hz0) | lia]).
pose proof (st_ok_add_cond_neg tfibsegs EE _ _ BC_EQ (RG (fst pHB2) 12) (SLit 0) HS3 (AE2y.rp_b1_nonzero EE 34 b E34 ltac:(lia))) as HS3'.
change (neg_bc BC_EQ) with BC_NE in HS3'.
rph HS3' rHB3n. intros ms4 md4 HS4 I4 S4.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG (fst pHB3n) 13) (RG (fst pHB3n) 12) HS4 (rp_blt_first EE 10 34 x b E10 E34 ltac:(lia) Hlt0)) as HS4'.
rph HS4' rHB4n. intros ms5 md5 HS5 I5 S5.
pose proof (st_ok_add_cond tfibsegs EE _ _ BC_LT (RG (fst pHB4n) 12) (RG (fst pHB4n) 11) HS5 (AE2y.rp_blt_last EE 10 11 34 x n b E10 E11 E34 Hx0 ltac:(lia) Hxn Hlt1)) as HS5'.
rph HS5' rHB5n. intros ms6 md6 HS6 I6 S6.
exact (tail EE _ ms6 md6 _ _ _ HS6 HE HV I6 S6 rHB5n_l rHB5n_m rHB5n_g cHB5n).
Qed.

Lemma walk : SRr tfibsegs W (cfg_at tfibsegs RG_ENTRY regs mem md) POST.
Proof.
pose proof grains as (_ & _ & _ & G01 & _).
pose proof HRU as [BL | [BH1 BH2]].
- destruct (Z.eq_dec g0 g1) as [Hg|Hg]; [exact (pathLB BL Hg) | exact (pathLA BL ltac:(lia))].
- destruct (Z.eq_dec g0 g1) as [Hg|Hg]; [exact (pathHB BH1 BH2 Hg) | exact (pathHA BH1 BH2 ltac:(lia))].
Qed.
End f.

(* The range check for every size 0 < n < 2^32 whose start rounds up inside its memory band; with n > 64 (the form
   the contract states) the band premise follows from amem_range. *)
Theorem reply_region_band_cf : forall (B : asyms), AR_laws_cf tfibsegs B -> TfibSyms B ->
forall stk, RGN_SCR <= stk ->
forall ly S Hp W regs mem md x n,
ARcf tfibsegs B ly S Hp W mem md -> YK0s.ret_ok (getr regs 1) ->
spZ regs mod 16 = 0 -> ly_stk_lo ly + stk <= spZ regs -> spZ regs <= ly_stk_hi ly ->
(forall a, spZ regs - stk <= a < spZ regs -> apresent (w_H W) mem a) ->
getr regs 10 = w64 x -> getr regs 11 = w64 n -> 0 < n < 2 ^ 32 -> 0 < x ->
aread_ok tfibsegs stk W regs mem x n ->
x + 8 <= kLowMemEnd \/ (kHighMemBeg <= x /\ x + 8 <= kHighMemEnd) ->
SRr tfibsegs W (cfg_at tfibsegs PC_region_is_poisoned regs mem md)
(art_post_cf tfibsegs B stk ly S Hp W regs mem md (fun _ => False) (fun regs' _ => getr regs' 10 = w64 0)).
Proof.
intros B LAWS TB stk Hstk ly S Hp W regs mem md x n HAR Hra Hal Hslo Hshi Hpres G10 G11 Hn Hx HRD HRU.
exact (walk B LAWS TB stk Hstk ly S Hp W regs mem md x n HAR Hra Hal Hslo Hshi Hpres G10 G11 Hn Hx HRD HRU).
Qed.

Theorem reply_region_zero_stk_cf : forall B, AR_laws_cf tfibsegs B -> TfibSyms B ->
  aregion_zero_stk_cf tfibsegs B PC_region_is_poisoned.
Proof.
intros B LAWS TB stk Hstk ly S Hp W regs mem md x n HAR Hra Hal Hslo Hshi Hpres G10 G11 Hn Hx HRD.
apply (reply_region_band_cf B LAWS TB stk Hstk ly S Hp W regs mem md x n HAR Hra Hal Hslo Hshi Hpres G10 G11 ltac:(lia) Hx HRD).
pose proof HRD as (_ & _ & _ & _ & HAM & _ & _). unfold amem_range in HAM.
unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
Qed.
End c.
