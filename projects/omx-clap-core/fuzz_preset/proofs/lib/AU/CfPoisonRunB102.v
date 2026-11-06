(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the symbolic runs of __asan_poison_memory_region (p, 16) and
   __asan_unpoison_memory_region (p, 16) of omx-clap-core/fuzz_preset's ASan+UBSan image B' (the #102 pin: stripped
   fuzz_preset.asan-ubsan sha256 d663f82d7f488d30f8e8d7496cb814e595a2f3cbbf16bde81a65cb3ea9af0994, unstripped twin
   c90d4fa54d43160b, PAU pau-preset-102). The twin of lib/A/CfPoisonRun102.v for image B', and the RE-PIN of
   lib/AU/CfPoisonRunB.v (the old pin B, f8f98a95 / twin 3b5e1a09). Same bodies: the shared tools repository 153d7bc1ad5
   tools/bytecmp/8ed351b56fbe on the donor fuzz_manifest.asan vs B' gives poison EQUAL-mod-pcrel 17 / 0, unpoison
   19 / 0, musl memset EQUAL (the internal file RESULT-20261029.txt). The numerals below are
   ADDRESSES of image B', read from the twin and checked by the build (tbl_po through table_ok, every rodata cell by
   rodata_chk against Reusable/YF0m.v Tfib_const), so a wrong numeral cannot survive.
     PO_ENTRY / UP_ENTRY   0x55044 / 0x551e4: __asan_poison_memory_region / __asan_unpoison_memory_region
                           (the #102 AU/CfImgB.v cf_pc_poison, cf_pc_unpoison; symtab entries, sizes 416 and 384)
     0x9bf08, 62 words     musl memset (symtab `memset`, size 248; YImgCellsB B_MEMSET_PC)
     0xa28a0 -> 0x13b198   the GOT slot of __sanitizer::current_verbosity and its cell (YImgCellsB B_GOT_0XB0,
                           B_CURRENT_VERBOSITY_CELL; 0: below the 3 the print gate needs)
     0xa8f30               the 8-byte cell of __asan::asan_flags_dont_use_directly (0xa8ef8,
                           B_ASAN_FLAGS_DONT_USE_DIRECTLY_CELL) that holds the user-poisoning flag byte at +0x3c
                           (cell value 0x100000055: the byte is 1)
     0xa2870 -> 0xa46d0    the GOT slot of __interception::real_memset (B_GOT_0X80 -> B_REAL_MEMSET_CELL); the
                           object cell -> 0x9bf08 is already in Reusable/YE2y.v icpt_rodata (B_REAL_MEMCPY_CELL + 8),
                           and MemToShadow (0x54f08, 79 words, B_MEMTOSHADOW_ASAN_POISONING_PC) and the shadow-layout
                           cells are already in Reusable/YE34.v icpt_ranges / Reusable/YE2y.v icpt_rodata.
   P_LDA / P_LDB / P_RET and U_LDA / U_LDB / U_RET are PO_ENTRY / UP_ENTRY plus the donor's offsets
   (0x60, 0x78, 0x120 and 0x60, 0x74, 0xc4), which the vm_compute'd runs below check.
   No proof text is taken from any image: this file only runs the engine. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YG0t YCe5.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YE34 YF0l YF0m YF0x YE2y.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN32.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
(* Both functions use a 64-byte frame; MemToShadow and musl memset use none. *)
Definition PO_WIN : Z := 64.
Definition PO_ENTRY : Z := 0x55044.
Definition UP_ENTRY : Z := 0x551e4.
Definition po_ranges : list (Z * nat) := [(0x55044, 104%nat); (0x551e4, 96%nat); (0x9bf08, 62%nat)].
Definition tbl_po : ctable := Eval vm_compute in build_ranges po_ranges tbl_icpt.
Lemma tbl_po_eq : tbl_po = build_ranges po_ranges tbl_icpt. Proof. vm_cast_no_check (eq_refl tbl_po). Qed.
Lemma tbl_po_ok : table_ok tfibsegs tbl_po.
Proof. rewrite tbl_po_eq. apply build_ranges_ok; [unfold po_ranges; repeat constructor; cbn; discriminate | exact tbl_icpt_ok]. Qed.
(* allow_user_poisoning (flags + 0x3c, in the cell at 0xa8f30), current_verbosity and its GOT slot, REAL(memset)'s
   GOT slot; icpt_rodata has the rest (flags' GOT slot, the shadow offset, kHighMemEnd/kMidMem*, REAL(memset)). *)
Definition po_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [(0xa28a0, 8, [(0, 8%N, 0x13b198)]); (0x13b198, 4, [(0, 4%N, 0)]); (0xa8f30, 8, [(0, 8%N, 0x100000055)]);
(0xa2870, 8, [(0, 8%N, 0xa46d0)])].
Lemma po_rodata_chk : forall ly, rodata_chk ly po_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.
Lemma po_rodata_low : forallb (fun r => forallb (fun c => (0 <=? fst (fst r) + fst (fst c)) && (fst (fst r) + fst (fst c) + 8 <=? TFIB_IMG_END)) (snd r)) po_rodata = true.
Proof. vm_compute. reflexivity. Qed.
Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- PO_WIN) 0 (- PO_WIN) 0 [].
Definition memA : smem := stkA :: map ro_region po_rodata.
Definition hLO (hi : bool) : Z := if hi then kHighMemBeg else 4096.
Definition hHI (hi : bool) : Z := if hi then kHighMemEnd - 24 else kLowShadowBeg - 16.
Definition factsA (hi : bool) : list (nat * afact) := [(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF (hLO hi) (hHI hi) 3)].
Definition ssA0 (e : Z) (hi : bool) : sstate := mkSS e sr_atoms memA None (mkFacts (factsA hi) [] []).
Definition ssA (e : Z) (hi : bool) : sstate := mkSS e (sr_set sr_atoms 11%bv (SLit 16)) memA None (mkFacts (factsA hi) [] []).
Definition RUN (s : sstate) := sym_runN tfibsegs tbl_po FUEL s.
Definition RG (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).
Definition reg_is (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RG ss r) v.
Definition add_fact (ss : sstate) (n : nat) (f : afact) : sstate :=
mkSST (ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss)
(mkFacts ((n, f) :: f_atoms (ss_facts ss)) (f_conds (ss_facts ss)) (f_alias (ss_facts ss))).
(* the shadow address MemToShadow computes for p + d, as the run writes it *)
Definition XS (d : Z) : sv := SAlu ALU_ADD (SLit 2147450880) (SAlu ALU_SRL (SOff 10 d) (SLit 3)).
Definition XS0 (d : Z) : sv := SAlu ALU_ADD (XS d) (SLit 0).
Definition aSH : nat := 32. Definition aV : nat := 33. Definition aHV : nat := 34.
(* The three shadow bytes the run reads: the head's two (atom aHV - 0 while the head is not hidden,
   shUserPoison once it is; neither run branches on them, so one atom covers both) and the end granule's
   (atom aV). The run writes only the first two, so r_whi is 2. *)
Definition rSH : YP09.region := YP09.mkRegion (Some aSH) 0 3 0 2
[YP09.mkChunk 0 (CVal 1 (SOff aHV 0)); YP09.mkChunk 1 (CVal 1 (SOff aHV 0)); YP09.mkChunk 2 (CVal 1 (SOff aV 0))].
Definition shLO (hi : bool) : Z := if hi then kHighShadowBeg else kLowShadowBeg.
Definition shHI (hi : bool) : Z := if hi then kHighShadowEnd - 3 else kLowShadowEnd - 3.
Definition memB (e : sstate) : smem := nth 0 (ss_mem e) stkA :: rSH :: tl (ss_mem e).
Definition V1 : sv := SExt true 8 (SOff aV 0).
Definition condD (tk : bool) : acond := if tk then mkAC BC_GE (SLit 0) V1 else mkAC (neg_bc BC_GE) (SLit 0) V1.
Definition KEPT : list Z := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].
Definition final_ok (ss : sstate) : bool :=
match ss_resv ss with None => true | _ => false end && forallb (fun r => reg_is ss r (SOff (Z.to_nat r) 0)) KEPT.
(* ---- __asan_poison_memory_region ---- *)
Definition pA (hi : bool) : sstate := ssA PO_ENTRY hi.
Definition pAH : sstate := Eval vm_compute in fst (RUN (pA true)).
Definition pAL : sstate := Eval vm_compute in fst (RUN (pA false)).
Definition peA (hi : bool) : sstate := if hi then pAH else pAL.
Definition P_LDA : Z := 0x550a4.
Lemma pr_A : forall hi, RUN (pA hi) = (peA hi, RS_stopped (SR_addr (XS0 0))). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma pA_facts : forall hi, ss_pc (peA hi) = P_LDA /\ ss_resv (peA hi) = None /\ ss_atoms_lt 32 (peA hi) = true /\
reg_is (peA hi) 9 (XS0 0) = true /\ reg_is (peA hi) 10 (XS 0) = true /\ ss_mem (peA hi) = nth 0 (ss_mem (peA hi)) stkA :: tl (ss_mem (peA hi)).
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Definition updB : list (bv 5 * sv) := [((9%bv : bv 5), SOff aSH 0); ((10%bv : bv 5), SOff aSH 0)].
Definition ppB (hi : bool) : sstate :=
add_fact (add_fact (add_fact (mkSS (ss_pc (peA hi)) (sr_sets (ss_regs (peA hi)) updB) (memB (peA hi)) None (ss_facts (peA hi)))
aSH (mkAF (shLO hi) (shHI hi) 0)) aV (mkAF 0 255 0)) aHV (mkAF 0 255 0).
Definition pBH : sstate := Eval vm_compute in ppB true.
Definition pBL : sstate := Eval vm_compute in ppB false.
Definition pB (hi : bool) : sstate := if hi then pBH else pBL.
Lemma pB_eq : forall hi, ppB hi = pB hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition peBH : sstate := Eval vm_compute in fst (RUN pBH).
Definition peBL : sstate := Eval vm_compute in fst (RUN pBL).
Definition peB (hi : bool) : sstate := if hi then peBH else peBL.
Definition P_LDB : Z := 0x550bc.
Lemma pr_B : forall hi, RUN (pB hi) = (peB hi, RS_stopped (SR_addr (SAlu ALU_ADD (XS0 16) (SLit 0)))).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma pB_facts : forall hi, ss_pc (peB hi) = P_LDB /\ ss_resv (peB hi) = None /\ ss_atoms_lt 35 (peB hi) = true /\
reg_is (peB hi) 18 (XS0 16) = true.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Definition ppC (hi : bool) : sstate := mkSS (ss_pc (peB hi)) (sr_sets (ss_regs (peB hi)) [((18%bv : bv 5), SOff aSH 2)]) (ss_mem (peB hi)) None (ss_facts (peB hi)).
Definition pCH : sstate := Eval vm_compute in ppC true.
Definition pCL : sstate := Eval vm_compute in ppC false.
Definition pC (hi : bool) : sstate := if hi then pCH else pCL.
Lemma pC_eq : forall hi, ppC hi = pC hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition peCH : sstate := Eval vm_compute in fst (RUN pCH).
Definition peCL : sstate := Eval vm_compute in fst (RUN pCL).
Definition peC (hi : bool) : sstate := if hi then peCH else peCL.
Lemma pr_C : forall hi, RUN (pC hi) = (peC hi, RS_stopped (SR_branch BC_GE (SLit 0) V1)).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma pC_facts : forall hi, ss_resv (peC hi) = None /\ ss_atoms_lt 35 (peC hi) = true.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Definition pD (hi tk : bool) : sstate := add_cond (peC hi) (condD tk).
Definition peDHT : sstate := Eval vm_compute in fst (RUN (pD true true)).
Definition peDHF : sstate := Eval vm_compute in fst (RUN (pD true false)).
Definition peDLT : sstate := Eval vm_compute in fst (RUN (pD false true)).
Definition peDLF : sstate := Eval vm_compute in fst (RUN (pD false false)).
Definition peD (hi tk : bool) : sstate := match hi, tk with true, true => peDHT | true, false => peDHF | false, true => peDLT | false, false => peDLF end.
Definition P_RET : Z := 0x55164.
Lemma pr_D : forall hi tk, RUN (pD hi tk) = (peD hi tk, RS_stopped (SR_jalr (SOff 1 0))).
Proof. intros [|] [|]; vm_compute; reflexivity. Qed.
Definition pSTK : YP09.region := Eval vm_compute in nth 0 (ss_mem peDHT) stkA.
Definition pSH : YP09.region := Eval vm_compute in nth 1 (ss_mem peDHT) stkA.
Lemma pD_facts : forall hi tk, ss_pc (peD hi tk) = P_RET /\ final_ok (peD hi tk) = true /\
nth_error (ss_mem (peD hi tk)) 0 = Some pSTK /\ nth_error (ss_mem (peD hi tk)) 1 = Some pSH.
Proof. intros [|] [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma pSTK_shape : YP09.r_base pSTK = Some 2%nat /\ YP09.r_wlo pSTK = - PO_WIN /\ YP09.r_whi pSTK = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma pSH_shape : YP09.r_base pSH = Some aSH /\ YP09.r_wlo pSH = 0 /\ YP09.r_whi pSH = 2 /\
In (YP09.mkChunk 0 (CVal 1 (SLit 247))) (YP09.r_chunks pSH) /\ In (YP09.mkChunk 1 (CVal 1 (SLit 247))) (YP09.r_chunks pSH).
Proof. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; vm_compute; auto 10. Qed.
Lemma po_ret_word : clookup tbl_po P_RET = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
Definition memBc : smem := Eval vm_compute in memB pAH.
Lemma memB_eq : forall hi, memB (peA hi) = memBc. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma pB_mem : forall hi, ss_mem (pB hi) = memBc. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition Wins : list (option nat * Z * Z) := Eval vm_compute in windows memBc.
Definition WinsA : list (option nat * Z * Z) := Eval vm_compute in windows memA.
Lemma pA_win : forall hi, windows (ss_mem (pA hi)) = WinsA. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma pB_win : forall hi, windows (ss_mem (pB hi)) = Wins. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma pC_win : forall hi, windows (ss_mem (pC hi)) = Wins. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma pD_win : forall hi tk, windows (ss_mem (pD hi tk)) = Wins. Proof. intros [|] [|]; vm_compute; reflexivity. Qed.
Lemma pD_resv : forall hi tk, ss_resv (peD hi tk) = None. Proof. intros [|] [|]; vm_compute; reflexivity. Qed.
(* ---- __asan_unpoison_memory_region ---- *)
Definition uA (hi : bool) : sstate := ssA UP_ENTRY hi.
Definition uAH : sstate := Eval vm_compute in fst (RUN (uA true)).
Definition uAL : sstate := Eval vm_compute in fst (RUN (uA false)).
Definition ueA (hi : bool) : sstate := if hi then uAH else uAL.
Definition U_LDA : Z := 0x55244.
Lemma ur_A : forall hi, RUN (uA hi) = (ueA hi, RS_stopped (SR_addr (XS0 0))). Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma uA_facts : forall hi, ss_pc (ueA hi) = U_LDA /\ ss_resv (ueA hi) = None /\ ss_atoms_lt 32 (ueA hi) = true /\ reg_is (ueA hi) 19 (XS0 0) = true /\ reg_is (ueA hi) 10 (XS 0) = true /\ ss_mem (ueA hi) = nth 0 (ss_mem (ueA hi)) stkA :: tl (ss_mem (ueA hi)).
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Definition updUB : list (bv 5 * sv) := [((19%bv : bv 5), SOff aSH 0); ((10%bv : bv 5), SOff aSH 0)].
Definition upB (hi : bool) : sstate :=
add_fact (add_fact (add_fact (mkSS (ss_pc (ueA hi)) (sr_sets (ss_regs (ueA hi)) updUB) (memB (ueA hi)) None (ss_facts (ueA hi)))
aSH (mkAF (shLO hi) (shHI hi) 0)) aV (mkAF 0 255 0)) aHV (mkAF 0 255 0).
Definition uBH : sstate := Eval vm_compute in upB true.
Definition uBL : sstate := Eval vm_compute in upB false.
Definition uB (hi : bool) : sstate := if hi then uBH else uBL.
Lemma uB_eq : forall hi, upB hi = uB hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition ueBH : sstate := Eval vm_compute in fst (RUN uBH).
Definition ueBL : sstate := Eval vm_compute in fst (RUN uBL).
Definition ueB (hi : bool) : sstate := if hi then ueBH else ueBL.
Definition U_LDB : Z := 0x55258.
Lemma ur_B : forall hi, RUN (uB hi) = (ueB hi, RS_stopped (SR_addr (SAlu ALU_ADD (XS0 16) (SLit 0)))).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma uB_facts : forall hi, ss_pc (ueB hi) = U_LDB /\ ss_resv (ueB hi) = None /\ ss_atoms_lt 35 (ueB hi) = true /\ reg_is (ueB hi) 9 (XS0 16) = true.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Definition upC (hi : bool) : sstate := mkSS (ss_pc (ueB hi)) (sr_sets (ss_regs (ueB hi)) [((9%bv : bv 5), SOff aSH 2)]) (ss_mem (ueB hi)) None (ss_facts (ueB hi)).
Definition uCH : sstate := Eval vm_compute in upC true.
Definition uCL : sstate := Eval vm_compute in upC false.
Definition uC (hi : bool) : sstate := if hi then uCH else uCL.
Lemma uC_eq : forall hi, upC hi = uC hi. Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition ueCH : sstate := Eval vm_compute in fst (RUN uCH).
Definition ueCL : sstate := Eval vm_compute in fst (RUN uCL).
Definition ueC (hi : bool) : sstate := if hi then ueCH else ueCL.
Definition U_RET : Z := 0x552a8.
Lemma ur_C : forall hi, RUN (uC hi) = (ueC hi, RS_stopped (SR_jalr (SOff 1 0))).
Proof. intros [|]; vm_compute; reflexivity. Qed.
Definition uSTK : YP09.region := Eval vm_compute in nth 0 (ss_mem ueCH) stkA.
Definition uSH : YP09.region := Eval vm_compute in nth 1 (ss_mem ueCH) stkA.
Lemma uC_facts : forall hi, ss_pc (ueC hi) = U_RET /\ final_ok (ueC hi) = true /\ ss_resv (ueC hi) = None /\ nth_error (ss_mem (ueC hi)) 0 = Some uSTK /\ nth_error (ss_mem (ueC hi)) 1 = Some uSH.
Proof. intros [|]; vm_compute; repeat split; reflexivity. Qed.
Lemma uSTK_shape : YP09.r_base uSTK = Some 2%nat /\ YP09.r_wlo uSTK = - PO_WIN /\ YP09.r_whi uSTK = 0.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma uSH_shape : YP09.r_base uSH = Some aSH /\ YP09.r_wlo uSH = 0 /\ YP09.r_whi uSH = 2 /\ In (YP09.mkChunk 0 (CVal 1 (SLit 0))) (YP09.r_chunks uSH) /\ In (YP09.mkChunk 1 (CVal 1 (SLit 0))) (YP09.r_chunks uSH).
Proof. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; vm_compute; auto 10. Qed.
Lemma up_ret_word : clookup tbl_po U_RET = Some RET_WORD_r.
Proof. vm_compute. reflexivity. Qed.
Definition memUBc : smem := Eval vm_compute in memB uAH.
Lemma memUB_eq : forall hi, memB (ueA hi) = memUBc. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma uA_win : forall hi, windows (ss_mem (uA hi)) = WinsA. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma uB_win : forall hi, windows (ss_mem (uB hi)) = Wins. Proof. intros [|]; vm_compute; reflexivity. Qed.
Lemma uC_win : forall hi, windows (ss_mem (uC hi)) = Wins. Proof. intros [|]; vm_compute; reflexivity. Qed.
