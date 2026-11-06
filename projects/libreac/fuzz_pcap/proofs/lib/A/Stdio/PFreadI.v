From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Written by Theorem Labs, 2026-10 (a Theorem Labs lane), for libreac/fuzz_pcap's v1.9.0 ASan build.

   THE WALK of the memory-checking runtime's fread wrapper, from the trampoline 0x41580 through
   ___interceptor_fread 0x43500 and back to the caller: it proves a Theorem Labs lane's `afread_spec`
   (lib/A/Stdio/PFreadISpec.v) UNCHANGED, taking this worker's musl contract `rfread_contract`
   (lib/A/Stdio/PFreadM.v) as a Section hypothesis at the REAL call.

   SHAPE PORTED from cgif_file_fuzzer's ONE-walk fwrite interceptor proof at origin/ossv/recipes
   c8557374ad2e: lib/A/AE26.v:178 `tfib_afwrite` (trampoline + interceptor + range check + epilogue in
   one walk), lib/A/AE27.v:82 `tfib_afwrite_spec` (the journal rebuild), lib/A/AE2b.v `fwr_check_srr`
   (the check walk, ported in lib/A/Stdio/PFreadIChk.v). EVERY ADDRESS WAS RE-DERIVED on pcap's own
   image, never taken from a donor label.

   ADDRESSES, all MEASURED on fuzz_pcap.objdump.txt (sha256 bf9d80d6e30f; internal record)
   (the unstripped twin of the pin fuzz_pcap.asan (sha256 b7a91d9b1fb0)), objdump lines 20271-20428:
     FR_ENTRY 0x41580  the trampoline, one instruction, raw word 0x7810106f = `j 0x43500`
     FR_REAL  0x8ee5c  musl fread, the value of the cell __interception::real_fread 0x9b570
     FR_RET   0x4355c  the return address of `jalr a4` at 0x43558
     FR_B     0x43568  the ACCESS_MEMORY_RANGE check's entry  (= PFreadIChk.RC_ENTRY)
     FR_END   0x435c0  the epilogue / join                     (= PFreadIChk.RC_END)
     frame 2128 = 2032 + 96 (0x43500 and 0x43524); window 2144 for the symbolic run.

   THE THREE INSTRUCTIONS AFTER THE REAL CALL, with their raw words, which are the same words cgif's
   fwrite interceptor has at 0x438e8 / 0x438ec / 0x438f0:
     0x4355c  0x060a8263  beqz s5,0x435c0      s5 = TryAsanInitFromRtl's result
     0x43560  0x06050063  beqz a0,0x435c0      k = 0 SKIPS the check
     0x43564  0x029504b3  mul  s1,a0,s1        s1 = k, because s1 = size = 1
   cgif's `fw_mid3n` (AE26.v:79) may assume 1 <= n, because fwrite's caller always writes at least one
   item. fread may return 0, and pcap reaches that case (PFreadISpec.v:18-22: at pcap_source_next
   0x81bd4 the count is the record's incl_len, with no incl_len >= 1 test). So the walk SPLITS here:
   `fr_mid3n` for k <> 0 and `fr_mid2z` for k = 0, and both join at FR_END, where the epilogue runs.

   THE ASan ERROR AND REPORT PATHS ARE PROVED DEAD, not budgeted. AFREAD_STK is an upper bound on the
   NORMAL path only (PFreadISpec.v:30-36 says so, and pcap-stk-upper.md (sha256 8c59d6f9be5c; internal record) measures 4416 B against 8192).
   Every call the interceptor can make, with the reason the walk never reaches it:
     0x59894 TryAsanInitFromRtl   REACHED. Returns 1 at once: it loads asan_inited (0xa2598, pinned to
                                  1 by AE2y's `icpt_rodata`) and `bne a1,a0` at 0x598b4 is not taken,
                                  so AsanInitInternal 0x595e0 is NOT entered.
     0x8ee5c  REAL fread          REACHED, through `jalr a4` on the cell 0x9b570. Discharged by the
                                  Section hypothesis RFR, never fetched (PFreadITbl's `tbl_fr_probe`).
     0x54400 region_is_poisoned   REACHED on the k > 64 paths only, inside PFreadIChk.
     0x730dc GetCurrentPc, 0x5a62c UnwindImpl, 0x573e4 ReportStringFunctionSizeOverflow,
     0x5b5d8 IsInterceptorSuppressed, 0x5b640 HaveStackTraceBasedSuppressions,
     0x5b948 IsStackTraceSuppressed, 0x5793c ReportGenericError
                                  NEVER REACHED, by two forced branches:
       (a) the size-overflow report at 0x435e8-0x4365c is guarded by `bltu a1,s1` at 0x43574 with
           a1 = ~d and s1 = k. The premises give 0 <= d, d + nm <= 2^47 and k <= nm, so
           d + k <= 2^47 - 1 < 2^64 - 1 - d, and the branch is not taken. In the walk this is the
           `br_ovf_false` step inside PFreadIChk (AE2y.v:449), which is where the run of
           `fread_check_srr` begins;
       (b) the poisoning report at 0x436b0-0x43768 is guarded by `beqz a0,0x4376c` at 0x436ac on
           __asan_region_is_poisoned's result. `range_addressable` and `shadow_hull_vis` of (d, k)
           force every shadow granule of the range to admit its bytes, so the result is 0 and the
           branch IS taken, straight to `mv a0,s5` at 0x4376c and `j 0x435c0`.
     There are NO __asan_report_* calls in this interceptor (MEASURED: the only report entry is
     ReportGenericError). So no report path is left, and none is covered by a stack constant.

   THE COMPOSITION, `pcap_afread_spec` (2026-10-29), follows the donor's pattern
   for a callee stated in the caller-journal form (cgif AC9u.v:313-345, origin/ossv/recipes
   c8557374ad2e): the callee's contract is instantiated at the CALLER'S journal, and the frame record
   the callee sees is pushed with achain_push. aj_call_tok (lib/A/AjCallTok.v) does not fit this
   call and is not used: its callee premise is the fresh-journal form (AjCallTok.v:39-44) and it
   needs the symbolic sp atom to be the journal's sp0 (AjCallTok.v:34), while rfread_contract
   extends the caller's journal (PFreadM.v:365-376, :421-427). The steps:
     1. the entry state ssA (entry_st_ok_full, from fr_entry_facts) and the front run 0x41580 ->
        0x8ee5c by YCbq's SRr_run_to_AJ, which carries the caller's journal across the 2144-byte
        window the run writes;
     2. the frame record at fp = sp (ra at sp - 8, s0 at sp - 16; shapeA_s0: s0 = the caller's sp)
        by achain_push, or the empty chain when sp >= ly_top - 16 (achain's first disjunct);
     3. RFR at the caller's journal;
     4. k = 0: fr_mid2z; k <> 0: fr_mid3n, then fread_check_srr;
     5. the epilogue r_epi from the seven saved words, SRr_ret_at, and the post: the journal by
        ajournal_after_write over the check's 72-byte scratch, rread_kept and afread_post from
        rfread_post's kept, band and fd clauses.
   NO MARGIN past d + k is needed: fread_check_srr asks amem_range, range_addressable and
   shadow_hull_vis exactly over (d, k) (PFreadIChk.v, Section f), and shadow_hull_vis
   (YG0d.v:310-311) already covers the 8-byte granule hull of the range.
   TAKEN FROM, per callee and lemma:
     REAL fread             this worker's rfread_contract (PFreadM.v, a working branch 8e0ae3045e4);
     the range check        cgif AE2b.v fwr_check_srr, through a Theorem Labs lane's relocation (PFreadIChk.v);
     mem_is_zero            AE2y.icpt_memisz (the relocated core, a working branch);
     TryAsanInitFromRtl     walked symbolically inside r_A (tbl_fr), no contract;
     memcpy                 none: the interceptor makes no memcpy call; musl's is inside RFR;
     asource_at_frame_segs  a Theorem Labs lane, lib/A/Prog/PcapSourceCloseSpec.v:117 (the image-free statement file split
                           out of PcapSourceClose.v; a working branch fac0ef2953a), over any segs;
     rdword_of_val_mem      a Theorem Labs lane, lib/A/Prog/PcapFrame.v:115, the same ref;
     the journal lemmas     the relocated core, lib/Reusable/YCbq.v.

   WHAT THIS FILE TAKES ON TRUST, and from whom:
     RFR   `rfread_contract` at FR_REAL -- this worker's own statement, lib/A/Stdio/PFreadM.v.
     ASIL  `asource_img_laws SK segs B K` -- a Theorem Labs lane's record, lib/A/Stdio/PSourceMeta.v, carried
           exactly as lib/A/Stdio/PFclose.v:91 carries it, discharged once at instantiation.
     LAWS / TB / the core's own rules -- the relocated cgif core.
   NO AddrHashMap / metadata premise is needed and none is taken: the interceptor reaches no metadata
   lookup. Every call it can make is listed above; TryAsanInitFromRtl reaches only AsanInitInternal
   (dead), and __asan_region_is_poisoned reaches only MemToShadow 0x53f74, mem_is_zero 0x64140 and
   two CheckFailed calls 0x54720 / 0x54740, which are AddrIsInMem assertions discharged by
   `range_addressable`. This is why `afread_spec` carries no (M : Z) and no `asrc_meta_inv`:
   measured absence, not omission. (MEASURED: objdump lines 20271-20428, 37777-37986, 43352-43392.)

   AF0m IS WIP on a working branch and some of its cells are marked E-PEND. The cells
   this walk's symbolic runs read are the ones AE2y's `icpt_rodata` pins plus the REAL cell:
     0x9b570 -> 0x8ee5c  M-IMG pcrel   (REAL fread; this file's `frA_rodata`)
     0x9a398 -> 0xa2599  M-IMG pcrel
     0x99828 + 8 -> 0xa18b8, 0x99820 -> 0x1333e8   M-IMG pcrel
     0xa2598 / 0xa2599 = 1   E-PEND pcrel/RT and E-PEND run2/RT  <-- asan_inited and its lock byte
     0xa18b8 -> 0x7fff8000   E-PEND measured/RT                  <-- the shadow base
     0xa25a0 -> 0x7fffffffffff, 0xa25a8, 0xa25b0 -> 0   E-PEND run2/RT
   So this walk DOES rest on E-PEND cell values, through AE2y's `icpt_rodata`, exactly as every other
   interceptor walk on this core does. Named here as the WIP core's push requires.

   RULE 24. SEND BACK: hit is an archived Theorem Labs lane input, not a released proof at ossv/recipes 25e3d17bdb50 (2026-10-29); walk kept (route
   ruling 19:27Z). The lookup and both passes are recorded in
   pcapreadi-fread-icpt.txt (sha256 82d195c482ff; internal record). The hit is
   a working branch f2159272960 (I_freadw.v (sha256 e2b8ec5651ce; internal record), fread_wrap.v (sha256 c77a1af38f33; internal record)
   `fread_wrap_holds`), which walks the same path on the same image but states
   `fread_wrap_contract` in the SR / a_call_post / AsanAllocAPI vocabulary over a
   different Reusable tree, parameterised over five opaque predicates, and is unbuilt at v1.9.0. It
   is used here ONLY as a map of pcs (0x41580 -> 0x43500 -> 0x8ee5c -> 0x4355c -> check -> 0x435c0),
   never as an import; every pc below is this worker's own measurement.
   the proof index could not see it: for libreac/fuzz_pcap it searches by the addresses the proofs'
   CONTRACTS name, with no symbol table, and reads only the four released refs. fread_wrap_c.v (sha256 102a8cbbf0cb; internal record) names
   the trampoline 0x41580 and never 0x43500. An index exit 1 for this unit means "not in the
   released set", NOT "does not exist". *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0k YK0s YK0n YP0n YK1d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP04 YP0g YP01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v YO0f.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q YA0m.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YCbq YC20.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import AB1v AE34 AF0l AF0m AF0x AB1w AE20 AE2y.
(* ACeg: `tfib_segs_low`, the side condition of YCbq's journal-carrying run lemmas. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Import ACeg.
(* lib/A/Prog, a Theorem Labs lane's files, used QUALIFIED and for one lemma each: PcapFrame's
   `rdword_of_val_mem` (the val_mem -> rdword direction achain_push's frame-record premises need)
   and PcapSourceCloseSpec's `asource_at_frame_segs` (moved there from PcapSourceClose.v on a working branch). *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapFrame PcapSourceCloseSpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PcapImgEnd YImgTop.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PFreadITbl PFreadIChk.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* MEASURED, see the header. *)
Definition FR_ENTRY : Z := (symaddr Symbols.Asan.s___wrap_fread).
Definition FR_REAL  : Z := (symaddr Symbols.Asan.s_fread_unlocked).
Definition FR_RET   : Z := (symaddr (Symbols.Asan.s___interceptor_fread + 0x5c)%Z).
Definition FR_B     : Z := (symaddr (Symbols.Asan.s___interceptor_fread + 0x68)%Z).
Definition FR_END   : Z := (symaddr (Symbols.Asan.s___interceptor_fread + 0xc0)%Z).
Definition FR_FRAME : Z := 2128.
Definition FR_WIN   : Z := 2144.

Lemma FR_B_is_check : FR_B = PFreadIChk.RC_ENTRY. Proof. reflexivity. Qed.
Lemma FR_END_is_check : FR_END = PFreadIChk.RC_END. Proof. reflexivity. Qed.

(* The one rodata cell the interceptor reads beyond AE2y's: __interception::real_fread. *)
Definition frA_rodata : list (Z * Z * list (Z * BinNums.N * Z)) :=
icpt_rodata ++ [((symaddr Symbols.Asan.s__ZN14__interception10real_freadE), 8, [(0, 8%N, (symaddr Symbols.Asan.s_fread_unlocked))])].
Lemma frA_rodata_chk : forall ly, rodata_chk ly frA_rodata = true.
Proof. intros ly. vm_compute. reflexivity. Qed.

Definition stkA : YP09.region := YP09.mkRegion (Some 2%nat) (- FR_WIN) 0 (- FR_WIN) 0 [].
(* a0 = d (0 .. 2^47), a1 = 1, a2 = nm (0 .. 2^26: fread may be called with 0), a3 = f (a live block). *)
Definition factsA : list (nat * afact) :=
[(2%nat, mkAF (2^44) (2^47) 4); (10%nat, mkAF 0 (2^47) 0); (11%nat, mkAF 1 1 0);
 (12%nat, mkAF 0 (2^26) 0); (13%nat, mkAF 4096 (2^47) 4)].
Definition ssA : sstate := mkSS FR_ENTRY sr_atoms (stkA :: map ro_region frA_rodata) None (mkFacts factsA [] []).
Definition RUNTOR (s : sstate) := sym_run_toN tfibsegs tbl_fr FUEL FR_REAL s.
Definition eA : sstate := Eval vm_compute in fst (RUNTOR ssA).
Lemma r_A : RUNTOR ssA = (eA, RS_running). Proof. vm_compute. reflexivity. Qed.

Definition RUNI (s : sstate) := sym_runN tfibsegs tbl_fr FUEL s.
Definition RGA (s : sstate) (r : Z) : sv := sr_get (ss_regs s) (Z_to_bv 5 r).

(* ra, s0, s1, s2, s3, s4, s5 saved at sp0-8 .. sp0-56 (0x43504-0x4351c). *)
Definition epi_chunks : list YP09.chunk :=
[YP09.mkChunk 2120 (CVal 8 (SOff 32 0)); YP09.mkChunk 2112 (CVal 8 (SOff 33 0)); YP09.mkChunk 2104 (CVal 8 (SOff 34 0));
YP09.mkChunk 2096 (CVal 8 (SOff 35 0)); YP09.mkChunk 2088 (CVal 8 (SOff 36 0)); YP09.mkChunk 2080 (CVal 8 (SOff 37 0));
YP09.mkChunk 2072 (CVal 8 (SOff 38 0))].
Definition ss_epi : sstate := mkSS FR_END sr_atoms [YP09.mkRegion (Some 2%nat) 0 2128 0 0 epi_chunks] None (mkFacts [(2%nat, mkAF (2^43) (2^47) 4)] [] []).
Definition epi_e : sstate := Eval vm_compute in fst (RUNI ss_epi).
Lemma r_epi : RUNI ss_epi = (epi_e, RS_stopped (SR_jalr (SOff 32 0))). Proof. vm_compute. reflexivity. Qed.

Definition reg_isA (ss : sstate) (r : Z) (v : sv) : bool := sv_eqb (RGA ss r) v.
Definition chunk_isA (off : Z) (v : sv) (c : YP09.chunk) : bool :=
(YP09.c_off c =? off) && match YP09.c_val c with CVal n e => N.eqb n 8 && sv_eqb e v | _ => false end.
Definition has_chunkA (ss : sstate) (off : Z) (v : sv) : bool :=
match ss_mem ss with r :: _ => existsb (chunk_isA off v) (YP09.r_chunks r) | [] => false end.
Definition SAVEDA : list (Z * Z) := [(1, -8); (8, -16); (9, -24); (18, -32); (19, -40); (20, -48); (21, -56)].
Definition KEPTA : list Z := [3; 4; 22; 23; 24; 25; 26; 27].
Definition shapeA (ss : sstate) : bool :=
(ss_pc ss =? FR_REAL) &&
match ss_mem ss with r :: _ => obase_eqb (YP09.r_base r) (Some 2%nat) && (YP09.r_wlo r =? - FR_WIN) && (YP09.r_whi r =? 0) | [] => false end &&
reg_isA ss 10 (SOff 10 0) && reg_isA ss 11 (SOff 11 0) && reg_isA ss 12 (SOff 12 0) && reg_isA ss 13 (SOff 13 0) &&
reg_isA ss 1 (SLit FR_RET) && reg_isA ss 2 (SOff 2 (-2128)) &&
reg_isA ss 9 (SOff 11 0) && reg_isA ss 18 (SOff 10 0) && reg_isA ss 19 (SOff 13 0) && reg_isA ss 20 (SOff 12 0) && reg_isA ss 21 (SLit 1) &&
forallb (fun r => reg_isA ss r (SOff (Z.to_nat r) 0)) KEPTA &&
forallb (fun p => has_chunkA ss (snd p) (SOff (Z.to_nat (fst p)) 0)) SAVEDA.
Lemma shapeA_ok : shapeA eA = true. Proof. vm_compute. reflexivity. Qed.

Lemma chunk_isA_sound : forall off v c, chunk_isA off v c = true -> c = YP09.mkChunk off (CVal 8 v).
Proof.
intros off v [o cv] Hc. unfold chunk_isA in Hc. cbn [YP09.c_off YP09.c_val] in Hc. apply andb_prop in Hc as [Ho Hv].
apply Z.eqb_eq in Ho. destruct cv as [nn e| | |]; try discriminate. apply andb_prop in Hv as [Hn He].
apply N.eqb_eq in Hn. apply sv_eqb_eq in He. subst. reflexivity.
Qed.

(* The three instructions between the REAL return and the check (raw words MEASURED). *)
Lemma lk_ret0 : clookup tbl_fr (symaddr (Symbols.Asan.s___interceptor_fread + 0x5c)%Z) = Some 0x060a8263. Proof. vm_compute. reflexivity. Qed.
Lemma lk_ret1 : clookup tbl_fr (symaddr (Symbols.Asan.s___interceptor_fread + 0x60)%Z) = Some 0x06050063. Proof. vm_compute. reflexivity. Qed.
Lemma lk_ret2 : clookup tbl_fr (symaddr (Symbols.Asan.s___interceptor_fread + 0x64)%Z) = Some 0x029504b3. Proof. vm_compute. reflexivity. Qed.

(* k <> 0: `beqz s5` not taken, `beqz a0` not taken, `mul s1,a0,s1` with s1 = 1. Cf. AE26.v:79. *)
Lemma fr_mid3n : forall (W : world tfibsegs) regs mem md k,
getr regs 21 = w64 1 -> getr regs 10 = w64 k -> getr regs 9 = w64 1 -> 1 <= k < 2 ^ 32 ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 FR_RET) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists md', c' = mkCfg (mkst (regupd regs 9%bv (getr regs 10%bv)) (Z_to_bv 64 FR_B) mem (seg_rom tfibsegs)) md' /\
same_but_materialized md md').
Proof.
intros W regs mem md k G21 G10 G9 Hk. pose proof AF0x.Hwx_tfa as Hwx.
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_beq_ft tfibsegs _ _ _ _ _ _ _ _ (tbl_fr_ok _ _ lk_ret0) eq_refl ltac:(vm_compute; reflexivity)).
match goal with |- c_eq (getr _ ?r) (getr _ ?r0) = false =>
replace r with (21%bv : bv 5) by (apply bv_eq; reflexivity); replace r0 with (0%bv : bv 5) by (apply bv_eq; reflexivity) end.
rewrite G21. vm_compute. reflexivity. }
intros md1 Hs1. rewrite unrestrict_mkst_mrestrict.
replace (v_addi (Z_to_bv 64 FR_RET) 4) with (Z_to_bv 64 (symaddr (Symbols.Asan.s___interceptor_fread + 0x60)%Z) : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_beq_ft tfibsegs _ _ _ _ _ _ _ _ (tbl_fr_ok _ _ lk_ret1) eq_refl ltac:(vm_compute; reflexivity)).
match goal with |- c_eq (getr _ ?r) (getr _ ?r0) = false =>
replace r with (10%bv : bv 5) by (apply bv_eq; reflexivity); replace r0 with (0%bv : bv 5) by (apply bv_eq; reflexivity) end.
rewrite G10, getr_zero. unfold c_eq. apply Bool.not_true_is_false. intros E. apply bv_eqb_eq in E.
apply (f_equal bv_unsigned) in E. unfold w64 in E. rewrite !unsigned_lit_small in E by lia. lia. }
intros md2 Hs2. rewrite unrestrict_mkst_mrestrict.
replace (v_addi (Z_to_bv 64 (symaddr (Symbols.Asan.s___interceptor_fread + 0x60)%Z)) 4) with (Z_to_bv 64 (symaddr (Symbols.Asan.s___interceptor_fread + 0x64)%Z) : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_mul tfibsegs _ _ _ _ _ _ _ _ (tbl_fr_ok _ _ lk_ret2) eq_refl ltac:(vm_compute; reflexivity)). }
intros md3 Hs3. rewrite unrestrict_mkst_mrestrict.
match goal with |- SRr _ _ (mkCfg (mkst (if bv_eqb ?rd _ then _ else regupd _ _ (v_mul (getr _ ?a) (getr _ ?b))) _ _ _) _) _ =>
replace rd with (9%bv : bv 5) by (apply bv_eq; reflexivity); replace a with (10%bv : bv 5) by (apply bv_eq; reflexivity);
replace b with (9%bv : bv 5) by (apply bv_eq; reflexivity) end.
replace (bv_eqb (9%bv : bv 5) 0) with false by reflexivity. cbn iota.
replace (v_addi (Z_to_bv 64 (symaddr (Symbols.Asan.s___interceptor_fread + 0x64)%Z)) 4) with (Z_to_bv 64 FR_B : word) by (apply bv_eq; vm_compute; reflexivity).
assert (EM : v_mul (getr regs 10) (getr regs 9) = getr regs 10).
{ unfold v_mul. rewrite G9, G10. unfold w64. rewrite !unsigned_lit_small by lia. rewrite Z.mul_1_r. reflexivity. }
rewrite EM.
apply SRr_ret. split; [reflexivity|]. exists md3. split; [reflexivity|].
eapply same_but_materialized_trans; [exact Hs1|]. eapply same_but_materialized_trans; [exact Hs2 | exact Hs3].
Qed.

(* k = 0: `beqz s5` not taken, `beqz a0` TAKEN -- the check is skipped and the epilogue runs.
   NEW for fread: fwrite cannot take this branch, so cgif has no counterpart. *)
Lemma fr_mid2z : forall (W : world tfibsegs) regs mem md,
getr regs 21 = w64 1 -> getr regs 10 = w64 0 ->
SRr tfibsegs W (mkCfg (mkst regs (Z_to_bv 64 FR_RET) mem (seg_rom tfibsegs)) md)
(fun W' c' => W' = W /\ exists md', c' = mkCfg (mkst regs (Z_to_bv 64 FR_END) mem (seg_rom tfibsegs)) md' /\
same_but_materialized md md').
Proof.
intros W regs mem md G21 G10. pose proof AF0x.Hwx_tfa as Hwx.
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_beq_ft tfibsegs _ _ _ _ _ _ _ _ (tbl_fr_ok _ _ lk_ret0) eq_refl ltac:(vm_compute; reflexivity)).
match goal with |- c_eq (getr _ ?r) (getr _ ?r0) = false =>
replace r with (21%bv : bv 5) by (apply bv_eq; reflexivity); replace r0 with (0%bv : bv 5) by (apply bv_eq; reflexivity) end.
rewrite G21. vm_compute. reflexivity. }
intros md1 Hs1. rewrite unrestrict_mkst_mrestrict.
replace (v_addi (Z_to_bv 64 FR_RET) 4) with (Z_to_bv 64 (symaddr (Symbols.Asan.s___interceptor_fread + 0x60)%Z) : word) by (apply bv_eq; vm_compute; reflexivity).
eapply (SRr_step tfibsegs Hwx W); [reflexivity | |].
{ rewrite restrict_mkst_fx. apply (step_beq_tk tfibsegs _ _ _ _ _ _ _ _ (tbl_fr_ok _ _ lk_ret1) eq_refl ltac:(vm_compute; reflexivity)).
match goal with |- c_eq (getr _ ?r) (getr _ ?r0) = true =>
replace r with (10%bv : bv 5) by (apply bv_eq; reflexivity); replace r0 with (0%bv : bv 5) by (apply bv_eq; reflexivity) end.
rewrite G10, getr_zero. unfold c_eq. apply bv_eqb_eq. apply bv_eq. vm_compute. reflexivity. }
intros md2 Hs2. rewrite unrestrict_mkst_mrestrict.
replace (btgt (Z_to_bv 64 (symaddr (Symbols.Asan.s___interceptor_fread + 0x60)%Z)) (bv_signed (Z_to_bv 13 96))) with (Z_to_bv 64 FR_END : word)
by (apply bv_eq; vm_compute; reflexivity).
apply SRr_ret. split; [reflexivity|]. exists md2. split; [reflexivity|].
eapply same_but_materialized_trans; [exact Hs1 | exact Hs2].
Qed.

(* ---------------------------------------------------------------------------------------------- *)
(* THE FRONT PHASE: the trampoline 0x41580, the prologue, TryAsanInitFromRtl, the load of the REAL  *)
(* cell 0x9b570 and the `jalr a4` at 0x43558, ending at REAL fread 0x8ee5c with the musl contract's *)
(* OWN precondition in hand. This is cgif's AE26.v:197-281 (its `HS0` / `icpt_phase_to` / `HAR1`    *)
(* block), restated over the caller's journal instead of over AR, because the musl contract is now  *)
(* in the donor's caller-journal form (cgif YC20.v:349-356).                                        *)
(* ---------------------------------------------------------------------------------------------- *)
Section g.
Context (SK : YI16.sink_head).
Variable B : asyms.
Variable K : asource_syms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.
(* a Theorem Labs lane's record (lib/A/Stdio/PSourceMeta.v), carried as lib/A/Stdio/PFclose.v:91 carries it:
   discharged ONCE at instantiation, never per walk. *)
Hypothesis ASIL : asource_img_laws SK tfibsegs B K.

Local Notation ajournal := (YCbq.ajournal tfibsegs B).
Local Notation rread_k := PFreadM.rread_k.

(* The stream predicate moves across a run that writes only outside the FILE block, the data buffer
   and the stdio environment: a Theorem Labs lane's `asource_at_frame_segs` (lib/A/Prog/PcapSourceCloseSpec.v:117,
   a working branch fac0ef2953a), which is stated over an arbitrary `segs`. *)
Local Notation asrc_kept := (PcapSourceCloseSpec.asource_at_frame_segs tfibsegs).

(* s0 is the caller's sp: `addi s0,sp,2032` at 0x43520 after `addi sp,sp,-2032` at 0x43500. *)
Lemma shapeA_s0 : reg_isA eA 8 (SOff 2 0) = true. Proof. vm_compute. reflexivity. Qed.

Lemma fr_entry_facts :
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch d nm f b p C,
PFreadISpec.afread_pre SK tfibsegs B K STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch d nm f b p C ->
(* the facts the symbolic entry state asks of the four arguments and of sp *)
2 ^ 44 <= spZ regs <= 2 ^ 47 /\ 0 <= d <= 2 ^ 47 /\ 0 <= nm <= 2 ^ 26 /\ 4096 <= f <= 2 ^ 47 /\
(forall a, spZ regs - FR_WIN <= a < spZ regs -> apresent (w_H W) memc a).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch d nm f b p C PRE.
pose proof PRE as (CALL & G10 & G11 & G12 & G13 & Hfblk & Hbblk & Hbstk & HSRC & HFwr & Hnm & HDEST).
pose proof CALL as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hslo & Hshi & Hch).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : PFreadISpec.AFREAD_STK = 8192) by reflexivity.
assert (HWIN : FR_WIN = 2144) by reflexivity.
pose proof HDEST as (Hdf & Hdb & Hd0 & Hdam & Hdat & Hdwr & Hdra & Hdhull).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hfblk) as (Hf16 & Hf0 & Hfceil & Hfapp & _).
assert (RQ : req_size SRC_FILE_BLOCK = SRC_FILE_BLOCK) by reflexivity. rewrite RQ in *.
split.
{ rewrite HSTK in Hslo. clear - Hslo Hlo Hhi Hshi Hceil C1 H47. lia. }
split.
{ split; [exact Hd0|]. clear - Hdam Hd0 Hnm. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hdam. lia. }
split; [exact Hnm|].
split.
{ split; [exact Hf0|]. pose proof alloc_ceiling_val as (AC1 & _). clear - Hfceil AC1. unfold SRC_FILE_BLOCK in Hfceil. lia. }
intros a Ha. apply Hpres. rewrite HSTK in Hslo. rewrite HWIN in Ha. clear - Ha Hslo Hshi. lia.
Qed.

(* This worker's musl-level statement at the REAL call (lib/A/Stdio/PFreadM.v, a working branch
   8e0ae3045e4). SK is passed explicitly: sink_head is a CLASS with a global instance for the PLAIN
   image (lib/Reusable/YI5b.v:12), so an inferred SK would be the wrong head. *)
Hypothesis RFR : PFreadM.rfread_contract (SK:=SK) tfibsegs B K FR_REAL.

Theorem pcap_afread_spec : PFreadISpec.afread_spec SK tfibsegs B K FR_ENTRY.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch d nm f b p C PRE.
pose proof PRE as (CALL & G10 & G11 & G12 & G13 & Hfblk & Hbblk & Hbstk & HSRC & HFwr & Hnm & HDEST).
pose proof CALL as (HJ & Hra & Hra4 & Hgp & Htp & Hal16 & Hslo & Hshi & Hch).
pose proof HJ as (HAR & HLY & Hsecs & Hwle & Hios & Hfrs & Hnev & Hk0 & F1 & F2 & F3 & F4 & Hgone & Hpres & Hstk & F5 & HQT).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hlo & Hhi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HDEST as (Hdf & Hdb & Hd0 & Hdam & Hdat & Hdwr & Hdra & Hdhull).
pose proof (fr_entry_facts STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch d nm f b p C PRE)
as (Hsp44 & Hdr & Hnm26 & Hfr & HpresW).
assert (HSTK : PFreadISpec.AFREAD_STK = 8192) by reflexivity.
rewrite HSTK in Hslo, Hbstk, HFwr, Hdwr.
(* f's alignment, f and b non-null, |C| and b's bounds: from the stream predicate. *)
assert (HSRCF : f mod 16 = 0 /\ 0 < f /\ 0 < b /\ Z.of_nat (length C) < 2 ^ 63 /\
b + Z.of_nat (length C) <= 2 ^ 64 /\ 0 <= p <= Z.of_nat (length C)).
{ destruct HSRC as (Wn & cpos & fl & mo & Hq). cbv zeta in Hq.
destruct Hq as (Hp0s & Hp1s & Hp2s & Hn63 & Hwrap & _ & _ & _ & _ & Hst & _).
destruct Hst as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&_&Hf0s&Hfals&Hb0s&_).
repeat split; [exact Hfals | exact Hf0s | exact Hb0s | exact Hn63 | exact Hwrap | exact Hp0s | clear - Hp1s Hp2s; lia]. }
destruct HSRCF as (Hfmod & Hfpos & Hbpos & Hn63 & Hbwrap & HpC0 & HpC).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc f SRC_FILE_BLOCK HAR Hfblk) as (Hf16 & Hf0 & Hfceil & Hfapp & _).
assert (RQF : req_size SRC_FILE_BLOCK = SRC_FILE_BLOCK) by reflexivity. rewrite RQF in Hfceil.
pose proof alloc_ceiling_val as (AC1 & AC2).
assert (HTOPC : ly_top lyc = ly_top ly /\ ly_stk_lo lyc = ly_stk_lo ly /\ ly_stk_hi lyc = ly_stk_hi ly)
by (destruct HLY as (_&_&_&_&_&_&_&_&LT&LL&LH&_); auto).
destruct HTOPC as (ETOP & ELO & EHI).
(* ---- the entry state -------------------------------------------------------------------------- *)
unfold cfg_at. change (w64 FR_ENTRY) with (Z_to_bv 64 FR_ENTRY).
set (EE := AE2y.Env regs []).
assert (EEreg : forall i (r : bv 5), Z.of_nat i = bv_unsigned r -> ew EE i = getr regs r)
by (intros; apply AE2y.Env_reg; assumption).
assert (EE2 : bv_unsigned (ew EE 2) = spZ regs) by (rewrite (EEreg 2%nat 2%bv eq_refl); reflexivity).
assert (EE10 : ew EE 10 = Z_to_bv 64 d) by (rewrite (EEreg 10%nat 10%bv eq_refl); exact G10).
assert (EE11 : ew EE 11 = Z_to_bv 64 1) by (rewrite (EEreg 11%nat 11%bv eq_refl); exact G11).
assert (EE12 : ew EE 12 = Z_to_bv 64 nm) by (rewrite (EEreg 12%nat 12%bv eq_refl); exact G12).
assert (EE13 : ew EE 13 = Z_to_bv 64 f) by (rewrite (EEreg 13%nat 13%bv eq_refl); exact G13).
assert (HS0 : st_ok tfibsegs EE ssA (restrict (w_H W) (mkst regs (Z_to_bv 64 FR_ENTRY) memc (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ssA. unfold EE, AE2y.Env. apply (entry_st_ok_full tfibsegs);
change (Ereg regs (map (Z_to_bv 64) [])) with EE.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [| exact (AE2y.rodata_ok B TB frA_rodata lyc Sc (w_H W) memc EE (frA_rodata_chk lyc) (proj1 HAR))].
unfold stkA, FR_WIN. apply (region_ok_stack tfibsegs EE _ 2 (spZ regs) (-2144)); [exact EE2 | lia | lia |].
intros a Ha. apply AE2y.apresent_writable. apply HpresW. unfold FR_WIN. lia.
- apply pairwise_disjoint_of_extents. unfold stkA, frA_rodata, icpt_rodata, ro_region, extent_of_region, FR_WIN.
cbn [map app fst snd YP09.r_base YP09.r_lo YP09.r_hi base_val Z.of_N]. rewrite EE2.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I]. cbn [f_atoms atoms_ok factsA]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite EE2, EE10, EE11, EE12, EE13, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; try lia; try exact Hal16; try exact Hfmod. }
(* ---- the front run, carrying the CALLER'S journal (YCbq.v:2256) ------------------------------- *)
eapply (SRr_run_to_AJ (SK:=SK) tfibsegs B LAWS ACeg.tfib_segs_low tbl_fr tbl_fr_ok AF0x.Hwx_tfa
W FUEL FR_REAL EE ssA eA RS_running _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc mdc k _).
- exact HS0.
- exact r_A.
- exact I.
- exact HJ.
- assert (ROW : forall rs, Forall (fun r => YP09.r_whi r <= YP09.r_wlo r) rs ->
awr_ok EE rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own).
{ intros rs. induction rs as [|r0 rs IH]; intros HFa; [apply awr_ok_nil|].
inversion HFa as [|? ? Hh Ht]; subst. apply awr_ok_cons_ro; [exact Hh | exact (IH Ht)]. }
unfold ssA. cbn [ss_mem].
apply (awr_ok_cons_stack_off EE _ _ STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own 2%nat (spZ regs - sp0)).
+ reflexivity.
+ rewrite EE2. lia.
+ unfold stkA, FR_WIN. cbn [YP09.r_wlo]. lia.
+ unfold stkA. cbn [YP09.r_whi]. lia.
+ apply ROW. apply Forall_map. apply Forall_forall. intros x Hx. unfold ro_region.
cbn [YP09.r_whi YP09.r_wlo]. lia.
- intros ms1 mat1 HS1 HJ1 HF1 HFr1 HG1.
cbn [ms_mem mkst] in HF1, HFr1, HG1.
assert (MEQ1 : forall z : word, ~ (spZ regs - 2144 <= bv_unsigned z < spZ regs) -> ms_mem ms1 z = memc z).
{ intros z Hz. apply (HF1 z). intros Hin.
unshelve epose proof (in_wrange_single_b EE _ (bv_unsigned z) 2 (- FR_WIN) 0 (spZ regs) _ EE2 Hin) as X0;
[vm_compute; reflexivity|]. unfold FR_WIN in *. lia. }
(* ---- the register and frame shape at REAL (shapeA_ok, shapeA_s0) ------------------------------ *)
pose proof shapeA_ok as Hsh. unfold shapeA in Hsh.
apply andb_prop in Hsh as [Hsh HSV]. apply andb_prop in Hsh as [Hsh HK'].
apply andb_prop in Hsh as [Hsh R21]. apply andb_prop in Hsh as [Hsh R20]. apply andb_prop in Hsh as [Hsh R19].
apply andb_prop in Hsh as [Hsh R18]. apply andb_prop in Hsh as [Hsh R9].
apply andb_prop in Hsh as [Hsh R2]. apply andb_prop in Hsh as [Hsh R1].
apply andb_prop in Hsh as [Hsh R13]. apply andb_prop in Hsh as [Hsh R12]. apply andb_prop in Hsh as [Hsh R11].
apply andb_prop in Hsh as [Hsh R10]. apply andb_prop in Hsh as [Hpc Smem].
destruct (ss_mem eA) as [|r0 rest] eqn:Hmem; [discriminate|].
apply andb_prop in Smem as [Smem Hwhi]. apply andb_prop in Smem as [Hbase Hwlo].
apply obase_eqb_eq in Hbase. apply Z.eqb_eq in Hwlo. apply Z.eqb_eq in Hwhi. apply Z.eqb_eq in Hpc.
set (regs1 := ms_regs ms1) in *.
assert (RD : forall (r : bv 5) v, reg_isA eA (bv_unsigned r) v = true -> getr regs1 r = sv_denot EE v).
{ intros r v Hr. unfold reg_isA, RGA in Hr. apply sv_eqb_eq in Hr. rewrite Z_to_bv_bv_unsigned in Hr.
rewrite <- Hr. apply (st_ok_reg_denot (w_H W) EE eA ms1 r HS1). }
assert (RK : forall (r : bv 5) i, Z.of_nat i = bv_unsigned r -> In (Z.of_nat i) KEPTA -> getr regs1 r = getr regs r).
{ intros r i Hi Hin. rewrite forallb_forall in HK'. rewrite Hi in Hin. specialize (HK' _ Hin). cbn beta in HK'.
rewrite <- Hi, Nat2Z.id in HK'. rewrite (RD r (SOff i 0)); [| rewrite <- Hi; exact HK'].
cbn [sv_denot]. rewrite (EEreg i r Hi), Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
assert (CK : forall j rz off, nth_error SAVEDA j = Some (rz, off) ->
val_mem tfibsegs (mrestrict (w_H W) (ms_mem ms1)) (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros j rz off Hj. rewrite forallb_forall in HSV. specialize (HSV (rz, off) (nth_error_In _ _ Hj)).
cbn [fst snd] in HSV.
assert (Hrz : 0 <= rz < 32) by (do 7 (destruct j as [|j]; [cbn in Hj; injection Hj as <- <-; lia|]); destruct j; discriminate).
unfold has_chunkA in HSV. rewrite Hmem in HSV. apply existsb_exists in HSV as (c & Hin & Hc).
apply chunk_isA_sound in Hc. subst c.
pose proof (st_ok_mem_ok tfibsegs EE eA _ HS1) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs. rewrite Hmem in Hrs.
pose proof (Forall_inv Hrs) as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. rewrite Hbase in Hck. cbn [base_val] in Hck.
rewrite EE2 in Hck.
apply (val_of_chunk_ok tfibsegs EE _ _ off 8 (SOff (Z.to_nat rz) 0) _ Hck).
- cbn [sv_denot]. rewrite (EEreg (Z.to_nat rz) (Z_to_bv 5 rz)), Z.add_0_r, Z_to_bv_bv_unsigned; [reflexivity|].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- pose proof (u64_range (getr regs (Z_to_bv 5 rz))). zside.
- zside. }
assert (Q10 : getr regs1 10 = w64 d) by (rewrite (RD 10%bv (SOff 10 0) R10); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q11 : getr regs1 11 = w64 1) by (rewrite (RD 11%bv (SOff 11 0) R11); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; reflexivity).
assert (Q12 : getr regs1 12 = w64 nm) by (rewrite (RD 12%bv (SOff 12 0) R12); cbn [sv_denot]; rewrite EE12, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q13 : getr regs1 13 = w64 f) by (rewrite (RD 13%bv (SOff 13 0) R13); cbn [sv_denot]; rewrite EE13, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q1 : getr regs1 1 = w64 FR_RET) by (rewrite (RD 1%bv (SLit FR_RET) R1); reflexivity).
assert (Q2 : getr regs1 2 = w64 (spZ regs - 2128)) by (rewrite (RD 2%bv (SOff 2 (-2128)) R2); cbn [sv_denot]; rewrite EE2; reflexivity).
assert (Q8 : getr regs1 8 = w64 (spZ regs)) by (rewrite (RD 8%bv (SOff 2 0) shapeA_s0); cbn [sv_denot]; rewrite EE2, Z.add_0_r; reflexivity).
assert (Q9 : getr regs1 9 = w64 1) by (rewrite (RD 9%bv (SOff 11 0) R9); cbn [sv_denot]; rewrite EE11, unsigned_lit_small by lia; reflexivity).
assert (Q18 : getr regs1 18 = w64 d) by (rewrite (RD 18%bv (SOff 10 0) R18); cbn [sv_denot]; rewrite EE10, unsigned_lit_small by lia; rewrite Z.add_0_r; reflexivity).
assert (Q21 : getr regs1 21 = w64 1) by (rewrite (RD 21%bv (SLit 1) R21); reflexivity).
assert (Q3 : getr regs1 3 = getr regs 3) by (exact (RK 3%bv 3%nat eq_refl ltac:(cbn; lia))).
assert (Q4 : getr regs1 4 = getr regs 4) by (exact (RK 4%bv 4%nat eq_refl ltac:(cbn; lia))).
assert (R1sp : spZ regs1 = spZ regs - 2128).
{ unfold spZ at 1. rewrite Q2. unfold w64. apply unsigned_lit_small. clear - Hsp44. lia. }
assert (R1ra : raZ regs1 = FR_RET).
{ unfold raZ. rewrite Q1. unfold w64. apply unsigned_lit_small. unfold FR_RET. lia. }
assert (R1s0 : s0Z regs1 = spZ regs).
{ unfold s0Z. rewrite Q8. unfold w64. apply unsigned_lit_small. clear - Hsp44. lia. }
(* ---- the machine state at REAL, and what the front run kept ----------------------------------- *)
pose proof (st_ok_restrict_mkst tfibsegs (w_H W) EE _ _ HS1 eq_refl) as Hshape.
rewrite Hpc in Hshape. fold regs1 in Hshape. rewrite Hshape.
set (md1 := with_vm_backing (m_vm_lazy mdc) mat1 mdc) in *.
assert (MF1 : same_but_materialized mdc md1) by (subst md1; apply with_vm_backing_same).
assert (AV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2144 <= a < spZ regs) ->
aview tfibsegs (w_H W) (ms_mem ms1) a = aview tfibsegs (w_H W) memc a).
{ intros a Hr Ha. apply aview_same. apply MEQ1. rewrite unsigned_lit_small by lia. exact Ha. }
assert (PRS1 : forall a, spZ regs - 2144 <= a < spZ regs -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. apply (st_ok_window_apresent_off (w_H W) EE eA ms1 0 r0 a HS1 ltac:(rewrite Hmem; reflexivity)).
- rewrite Hbase, Hwlo, Hwhi. cbn [base_val]. rewrite EE2. unfold FR_WIN. clear - Ha. lia.
- apply off_img_high. unfold AF0x.TFIB_IMG_END, pcap_img_end, IMG_TOP. clear - Ha Hsp44. lia. }
assert (PM1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Hpa. pose proof Hpa as [Hh [bq Hbq]].
rewrite (AE2y.apresent_mod _ (ms_mem ms1) a). rewrite (AE2y.apresent_mod _ memc a) in Hpa.
assert (Ha : 0 <= a mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia). set (a' := a mod 2 ^ 64) in *.
destruct (Z_lt_le_dec a' (spZ regs - 2144)) as [L1|L1];
[apply (apresent_same (w_H W) memc (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hpa]|].
destruct (Z_lt_le_dec a' (spZ regs)) as [L3|L3]; [apply PRS1; lia|].
apply (apresent_same (w_H W) memc (ms_mem ms1) a'); [apply MEQ1; rewrite unsigned_lit_small by lia; lia | exact Hpa]. }
assert (SPC : alloc_ceiling + 8192 <= spZ regs) by (clear - Hslo Hlo Hceil; lia).
assert (AVband1 : forall s, kLowMemEnd <= s < kHighShadowEnd ->
aview tfibsegs (w_H W) (ms_mem ms1) s = aview tfibsegs (w_H W) memc s).
{ intros s Hs. unfold kLowMemEnd, kHighShadowEnd in Hs. apply AV1; clear - Hs SPC AC1; lia. }
assert (RAX : forall (Wa Wb : world tfibsegs) (ma mb : word -> option byte) a len,
(forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs (w_H Wb) mb s = aview tfibsegs (w_H Wa) ma s) ->
0 <= a -> a + len <= kHighMemEnd -> range_addressable (aview tfibsegs (w_H Wa) ma) SHADOW_OFF a len ->
range_addressable (aview tfibsegs (w_H Wb) mb) SHADOW_OFF a len).
{ intros Wa Wb ma mb a len AVB Ha Hl HR. eapply range_addressable_agree; [|exact HR]. intros z Hz.
change (shadow_of_addr SHADOW_OFF z) with (shadow_addr z). apply AVB. apply AE2y.shadow_addr_bounds. lia. }
assert (HVX : forall (Wa Wb : world tfibsegs) (ma mb : word -> option byte) a len,
(forall s, kLowMemEnd <= s < kHighShadowEnd -> aview tfibsegs (w_H Wb) mb s = aview tfibsegs (w_H Wa) ma s) ->
0 <= a -> 1 <= len -> a + len <= kHighMemEnd -> shadow_hull_vis (aview tfibsegs (w_H Wa) ma) a len ->
shadow_hull_vis (aview tfibsegs (w_H Wb) mb) a len).
{ intros Wa Wb ma mb a len AVB Ha Hl1 Hl HVS s Hs. rewrite AVB; [exact (HVS s Hs)|].
pose proof (AE2y.shadow_addr_bounds a ltac:(lia)) as [B1 B2].
pose proof (AE2y.shadow_addr_bounds (a + len - 1) ltac:(lia)) as [T1 T2].
pose proof (Z.div_mod (shadow_addr a) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr a) 8 ltac:(lia)).
pose proof (Z.div_mod (shadow_addr (a + len - 1)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (shadow_addr (a + len - 1)) 8 ltac:(lia)).
unfold kLowMemEnd, kHighShadowEnd in *. lia. }
assert (HamS : d + nm <= kHighMemEnd) by (clear - Hdam Hnm; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
(* ---- the frame record the callee sees (YCbq.v:293 achain_push) -------------------------------- *)
assert (Qal8 : spZ regs mod 8 = 0).
{ pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D. rewrite Hal16, Z.add_0_r in D. rewrite D.
replace (16 * (spZ regs / 16)) with ((2 * (spZ regs / 16)) * 8) by lia. apply Z_mod_mult. }
assert (HCH : exists ch1, achain lyc (aview tfibsegs (w_H W) (ms_mem ms1)) (spZ regs1) (s0Z regs1) ch1).
{ rewrite R1s0, R1sp. destruct (Z_le_gt_dec (ly_top lyc - 16) (spZ regs)) as [Htk|Htk].
- exists []. left. split; [right; left; exact Htk | reflexivity].
- exists ((spZ regs, raZ regs, s0Z regs) :: ch).
apply (achain_push lyc (aview tfibsegs (w_H W) memc) (aview tfibsegs (w_H W) (ms_mem ms1))
(spZ regs) (s0Z regs) (raZ regs) ch (spZ regs - 2128) Hch).
+ rewrite ETOP. clear - Htop Hhi H47. lia.
+ intros a Ha. apply AV1; [lia | lia].
+ apply (PcapFrame.rdword_of_val_mem tfibsegs (w_H W) (ms_mem ms1) (spZ regs - 8) (raZ regs));
[replace (spZ regs - 8) with (spZ regs + (-8)) by lia; exact (CK 0%nat 1%Z (-8)%Z eq_refl)
| unfold raZ; apply u64_range].
+ apply (PcapFrame.rdword_of_val_mem tfibsegs (w_H W) (ms_mem ms1) (spZ regs - 16) (s0Z regs));
[replace (spZ regs - 16) with (spZ regs + (-16)) by lia; exact (CK 1%nat 8%Z (-16)%Z eq_refl)
| unfold s0Z; apply u64_range].
+ exact Hra4.
+ clear - SPC; lia.
+ exact Qal8.
+ lia.
+ lia. }
destruct HCH as (ch1 & Hch1).
(* ---- REAL fread: this worker's contract at the CALLER'S journal ------------------------------- *)
change (mkCfg (mkst regs1 (Z_to_bv 64 FR_REAL) (ms_mem ms1) (seg_rom tfibsegs)) md1)
with (cfg_at tfibsegs FR_REAL regs1 (ms_mem ms1) md1).
assert (HSRC1 : asource_at tfibsegs K (mrestrict (w_H W) (ms_mem ms1)) f b C p).
{ apply (asrc_kept K (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms1)) f b C p); [|exact HSRC].
intros a Ha. apply mbyte_of_aview. apply AV1.
- destruct Ha as [Hq | [Hq | Hq]].
+ clear - Hq Hf0 Hfceil AC1. unfold SRC_FILE_BLOCK in *. lia.
+ clear - Hq Hbpos Hbwrap. lia.
+ destruct (asil_env _ _ _ _ ASIL a Hq) as (Himg & _). pose proof (tfib_segs_low a Himg).
clear - H. unfold kLowMemEnd in H. lia.
- destruct Ha as [Hq | [Hq | Hq]].
+ clear - Hq Hfceil Hslo Hlo Hceil. unfold SRC_FILE_BLOCK in *. lia.
+ clear - Hq Hbstk Hbpos. lia.
+ destruct (asil_env _ _ _ _ ASIL a Hq) as (Himg & _). pose proof (tfib_segs_low a Himg).
clear - H SPC AC1. unfold kLowMemEnd in H. lia. }
eapply SRr_bind.
{ apply (RFR STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem ms1) md1 k regs1 ch1 d nm f b p C).
split.
{ split; [exact HJ1|].
split; [rewrite Q1; apply (AE2y.ret_ok_lit FR_RET); [unfold FR_RET; lia | reflexivity]|].
split; [rewrite R1ra; unfold FR_RET; lia|].
split; [rewrite Q3; exact Hgp|]. split; [rewrite Q4; exact Htp|].
split; [rewrite R1sp; replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by lia;
rewrite Z_mod_plus_full; exact Hal16|].
split; [rewrite R1sp; unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK;
clear - Hslo; lia|].
split; [rewrite R1sp; clear - Hshi; lia|]. exact Hch1. }
split; [exact Q10|]. split; [exact Q11|]. split; [exact Q12|]. split; [exact Q13|].
split; [exact Hfblk|]. split; [exact Hbblk|].
split; [rewrite R1sp; unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK;
clear - Hbstk; lia|].
split; [exact HSRC1|].
split.
{ intros a Ha. destruct (HFwr a Ha) as (Hw & Hns). split; [exact Hw|].
rewrite R1sp. unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK. clear - Hns. lia. }
split; [exact Hnm|].
split; [exact Hdf|]. split; [exact Hdb|]. split; [exact Hd0|]. split; [exact Hdam|]. split; [exact Hdat|].
split.
{ intros a Ha. destruct (Hdwr a Ha) as (Hw & Hns). split; [exact Hw|].
rewrite R1sp. unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK. clear - Hns. lia. }
split.
{ apply (RAX W W memc (ms_mem ms1)); [exact AVband1 | clear - Hd0; lia | clear - HamS; lia | exact Hdra]. }
intros Hpos. apply (HVX W W memc (ms_mem ms1)); [exact AVband1 | clear - Hd0; lia | clear - Hpos; lia | clear - HamS; lia |].
exact (Hdhull Hpos). }
cbv beta. intros W2 c2 _ (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ2 & AP2 & HK2 & HQ2).
cbv zeta in HQ2.
destruct HQ2 as (ELY2 & ES2 & A10_2 & HGAR & HSRC2 & HMODE2 & HZERO2 & HFDS2 & HFS2 & HBAND2).
pose proof HK2 as (K1 & K2b & K3 & K4 & K5 & K6).
subst ly2 S2.
assert (K2r : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> getr regs2 rr = getr regs1 rr)
by (intros rr z -> Hcs; exact (AP2 z Hcs)).
assert (G21_2 : getr regs2 21 = w64 1)
by (rewrite (K2r 21%bv 21 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q21).
assert (G9_2 : getr regs2 9 = w64 1)
by (rewrite (K2r 9%bv 9 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q9).
assert (G18_2 : getr regs2 18 = w64 d)
by (rewrite (K2r 18%bv 18 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q18).
assert (G2_2 : getr regs2 2 = w64 (spZ regs - 2128))
by (rewrite (K2r 2%bv 2 ltac:(apply bv_eq; reflexivity)) by (unfold acallee_saved; lia); exact Q2).
assert (R2sp : spZ regs2 = spZ regs - 2128)
by (unfold spZ at 1; rewrite G2_2; unfold w64; apply unsigned_lit_small; clear - Hsp44; lia).
assert (Hj0 : 0 <= rread_k nm (Z.of_nat (length C)) p <= nm)
by (unfold PFreadM.rread_k; clear - Hnm HpC HpC0; lia).
unfold cfg_at. rewrite Q1. change (w64 FR_RET) with (Z_to_bv 64 FR_RET).
(* ---- the three instructions after REAL: k <> 0 runs the check, k = 0 skips it ----------------- *)
eapply SRr_bind with (R := fun W3 c3 => W3 = W2 /\ exists regs4 mem4 md4,
c3 = cfg_at tfibsegs FR_END regs4 mem4 md4 /\
AR tfibsegs B lyc Sc W2 mem4 md4 /\
getr regs4 10 = getr regs2 10 /\
(forall r, acallee_saved r -> r <> 9 -> r <> 20 -> r <> 21 -> getr regs4 (Z_to_bv 5 r) = getr regs2 (Z_to_bv 5 r)) /\
same_but_materialized md2 md4 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2128 - 72 <= a < spZ regs - 2128) ->
aview tfibsegs (w_H W2) mem4 a = aview tfibsegs (w_H W2) mem2 a) /\
(forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mem4 a)).
{ destruct (Z.eq_dec (rread_k nm (Z.of_nat (length C)) p) 0) as [Hz|Hnz].
- (* k = 0: `beqz a0` is taken and the epilogue runs at once *)
eapply SRr_mono; [exact (fr_mid2z W2 regs2 mem2 md2 G21_2 ltac:(rewrite A10_2, Hz; reflexivity))|].
cbv beta. intros W3 c3 _ (-> & md3 & -> & Hsbm3). split; [reflexivity|].
exists regs2, mem2, md3. split; [reflexivity|].
split.
{ pose proof (same_but_materialized_frame md2 md3 Hsbm3) as (_ & Z3maps & Z3lazy & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
apply (al_frame _ _ LAWS lyc Sc W2 mem2 md2 mem2 md3 (proj1 HJ2));
[intros; reflexivity | intros a Hv; exact Hv | exact Z3maps | exact Z3lazy
| apply (same_but_materialized_frame md2 _ Hsbm3) | exact (AE2y.hs_kept_refl _ _)]. }
split; [reflexivity|].
split; [intros r _ _ _ _; reflexivity|]. split; [exact Hsbm3|].
split; [intros a _ _; reflexivity | intros a Hp; exact Hp].
- (* k <> 0: `mul s1,a0,s1` then the ACCESS_MEMORY_RANGE check *)
assert (Hk1 : 1 <= rread_k nm (Z.of_nat (length C)) p < 2 ^ 32) by (clear - Hj0 Hnm Hnz; lia).
eapply SRr_bind; [exact (fr_mid3n W2 regs2 mem2 md2 _ G21_2 A10_2 G9_2 Hk1)|].
cbv beta. intros W3 c3 _ (-> & md3 & -> & Hsbm3).
set (regs3 := regupd regs2 9%bv (getr regs2 10%bv)).
assert (R3 : forall rr : bv 5, rr <> 9%bv -> getr regs3 rr = getr regs2 rr)
by (intros rr Hne; subst regs3; apply getr_other; exact Hne).
assert (R3_9 : getr regs3 9 = w64 (rread_k nm (Z.of_nat (length C)) p))
by (subst regs3; rewrite getr_same by (intros X0; discriminate X0); exact A10_2).
assert (R3sp : spZ regs3 = spZ regs - 2128)
by (unfold spZ; rewrite R3 by (intros X0; discriminate X0); exact R2sp).
pose proof (same_but_materialized_frame md2 md3 Hsbm3) as (_ & F3maps & F3lazy & _ & _ & _ & _ & _ & F3fds & _ & _ & F3fs & _).
assert (HAR3 : AR tfibsegs B lyc Sc W2 mem2 md3).
{ apply (al_frame _ _ LAWS lyc Sc W2 mem2 md2 mem2 md3 (proj1 HJ2));
[intros; reflexivity | intros a Hv; exact Hv | exact F3maps | exact F3lazy
| apply (same_but_materialized_frame md2 _ Hsbm3) | exact (AE2y.hs_kept_refl _ _)]. }
eapply SRr_mono.
{ apply (fread_check_srr B LAWS TB lyc Sc W2 regs3 mem2 md3 d (rread_k nm (Z.of_nat (length C)) p) HAR3).
- rewrite R3sp. replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by lia.
rewrite Z_mod_plus_full. exact Hal16.
- rewrite R3sp. unfold PFreadIChk.RC_SCR. rewrite ELO. clear - Hslo Hlo Hceil; lia.
- rewrite R3sp. rewrite EHI. clear - Hshi Hhi Hlo Hslo; lia.
- intros a Ha. rewrite R3sp in Ha. unfold PFreadIChk.RC_SCR in Ha.
apply K6. rewrite R1sp. unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK.
clear - Ha; lia.
- exact R3_9.
- rewrite R3 by (intros X0; discriminate X0). exact G18_2.
- exact Hk1.
- exact Hd0.
- clear - Hdam Hj0 Hnm Hd0. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hdam. lia.
- clear - Hdam Hj0 Hnm Hd0. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia.
- assert (HRA2 : range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF d nm).
{ apply (RAX W W2 (ms_mem ms1) mem2 d nm);
[intros s Hs; exact (HBAND2 s Hs) | clear - Hd0; lia | clear - HamS; lia |].
apply (RAX W W memc (ms_mem ms1)); [exact AVband1 | clear - Hd0; lia | clear - HamS; lia | exact Hdra]. }
intros x Hx. apply HRA2. clear - Hx Hj0; lia.
- apply (HVX W W2 (ms_mem ms1) mem2 d (rread_k nm (Z.of_nat (length C)) p));
[intros s Hs; exact (HBAND2 s Hs) | clear - Hd0; lia | clear - Hk1; lia | clear - HamS Hj0; lia |].
assert (HH1 : shadow_hull_vis (aview tfibsegs (w_H W) (ms_mem ms1)) d nm)
by (apply (HVX W W memc (ms_mem ms1)); [exact AVband1 | clear - Hd0; lia | clear - Hk1 Hj0; lia | clear - HamS; lia
| exact (Hdhull ltac:(clear - Hk1 Hj0; lia))]).
intros s Hs. apply HH1. pose proof (shadow_mono (d + rread_k nm (Z.of_nat (length C)) p - 1) (d + nm - 1)
ltac:(clear - Hj0; lia)) as Hm. clear - Hs Hm Hj0 Hk1.
pose proof (Z.div_mod (shadow_addr (d + rread_k nm (Z.of_nat (length C)) p - 1)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (shadow_addr (d + rread_k nm (Z.of_nat (length C)) p - 1)) 8 ltac:(lia)).
pose proof (Z.div_mod (shadow_addr (d + nm - 1)) 8 ltac:(lia)).
pose proof (Z.mod_pos_bound (shadow_addr (d + nm - 1)) 8 ltac:(lia)). lia. }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & KCS4 & Hsbm4 & A10_4 & Hfr4 & Hpm4).
split; [reflexivity|]. exists regs4, mem4, md4. split; [reflexivity|]. split; [exact HAR4|].
split; [rewrite A10_4; apply R3; intros X0; discriminate X0|].
assert (RNE : forall z, acallee_saved z -> z <> 9 -> (Z_to_bv 5 z : bv 5) <> 9%bv).
{ intros z Hcs Hz9 X0. apply Hz9. apply (f_equal bv_unsigned) in X0.
rewrite Z_to_bv_unsigned in X0. unfold bv_wrap in X0. change (bv_modulus 5) with 32 in X0.
rewrite Z.mod_small in X0 by (unfold acallee_saved in Hcs; lia).
replace (bv_unsigned (9%bv : bv 5)) with 9 in X0 by reflexivity. exact X0. }
split; [intros r Hcs H9 H20 H21; rewrite (KCS4 r Hcs H9 H20 H21); apply R3; exact (RNE r Hcs H9)|].
split; [eapply same_but_materialized_trans; [exact Hsbm3 | exact Hsbm4]|].
split; [intros a Hr Ha; apply Hfr4; [exact Hr|]; rewrite R3sp; unfold PFreadIChk.RC_SCR; clear - Ha; lia|].
intros a Hp. apply Hpm4. exact Hp. }
(* ---- the epilogue 0x435c0-0x435e4 and the return ---------------------------------------------- *)
cbv beta. intros W3 c3 _ (-> & regs4 & mem4 & md4 & -> & TAR & T10 & TCS & TSBM & TAV & TPM).
pose proof (same_but_materialized_frame md2 md4 TSBM) as (_ & F4maps & F4lazy & _ & _ & _ & _ & _ & F4fds & _ & _ & F4fs & _).
set (E4 := Ereg regs4 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]).
assert (TCSb : forall (rr : bv 5) z, rr = Z_to_bv 5 z -> acallee_saved z -> z <> 9 -> z <> 20 -> z <> 21 ->
getr regs4 rr = getr regs2 rr)
by (intros rr z -> Hcs H9 H20 H21; exact (TCS z Hcs H9 H20 H21)).
assert (T2sp : getr regs4 2 = w64 (spZ regs - 2128)).
{ rewrite (TCSb 2%bv 2 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)
ltac:(lia) ltac:(lia) ltac:(lia)). exact G2_2. }
assert (E4_2 : bv_unsigned (ew E4 2) = spZ regs - 2128).
{ subst E4. rewrite (ew_Ereg_nat regs4 _ 2 2%bv eq_refl), T2sp. unfold w64. apply unsigned_lit_small.
clear - Hsp44; lia. }
assert (WS : forall jj rz off, nth_error SAVEDA jj = Some (rz, off) ->
val_mem tfibsegs (mrestrict (w_H W2) mem4) (spZ regs + off) 8 (bv_unsigned (getr regs (Z_to_bv 5 rz)))).
{ intros jj rz off Hjj.
assert (Hoff : -56 <= off <= -8)
by (do 7 (destruct jj as [|jj]; [cbn in Hjj; injection Hjj as <- <-; lia|]); destruct jj; discriminate).
apply (AF0x.val_mem_ext (mrestrict (w_H W2) mem2)).
- intros kk Hk. apply mbyte_of_aview. apply TAV; [clear - Hoff Hsp44 Hk; cbn in Hk; lia|].
clear - Hoff Hk; cbn in Hk; lia.
- apply (AF0x.val_mem_ext (mrestrict (w_H W) (ms_mem ms1))); [|exact (CK jj rz off Hjj)].
intros kk Hk. apply mbyte_of_aview. apply K1.
+ clear - Hoff Hk Hsp44 SPC AC1; cbn in Hk; lia.
+ rewrite R1sp. unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK.
clear - Hoff Hk; cbn in Hk; lia.
+ unfold PFreadM.rread_wrset. intros [Hq|Hq].
* clear - Hq Hoff Hk Hfceil Hslo Hlo Hceil Hsp44. unfold SRC_FILE_BLOCK in *. cbn in Hk. lia.
* destruct (Hdwr _ Hq) as (_ & Hns). clear - Hns Hoff Hk. cbn in Hk. lia. }
pose proof (WS 0%nat 1%Z (-8)%Z eq_refl) as WS0. replace (spZ regs + -8) with (spZ regs - 8) in WS0 by lia.
pose proof (WS 1%nat 8%Z (-16)%Z eq_refl) as WS1. replace (spZ regs + -16) with (spZ regs - 16) in WS1 by lia.
pose proof (WS 2%nat 9%Z (-24)%Z eq_refl) as WS2. replace (spZ regs + -24) with (spZ regs - 24) in WS2 by lia.
pose proof (WS 3%nat 18%Z (-32)%Z eq_refl) as WS3. replace (spZ regs + -32) with (spZ regs - 32) in WS3 by lia.
pose proof (WS 4%nat 19%Z (-40)%Z eq_refl) as WS4. replace (spZ regs + -40) with (spZ regs - 40) in WS4 by lia.
pose proof (WS 5%nat 20%Z (-48)%Z eq_refl) as WS5. replace (spZ regs + -48) with (spZ regs - 48) in WS5 by lia.
pose proof (WS 6%nat 21%Z (-56)%Z eq_refl) as WS6. replace (spZ regs + -56) with (spZ regs - 56) in WS6 by lia.
assert (HSe : st_ok tfibsegs E4 ss_epi (restrict (w_H W2) (mkst regs4 (w64 FR_END) mem4 (seg_rom tfibsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_epi. apply (entry_st_ok_full tfibsegs);
change (Ereg regs4 [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]) with E4.
- apply regs_ok_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
replace (base_val E4 (Some 2%nat)) with (spZ regs - 2128) by (symmetry; exact E4_2).
split; [clear - Hsp44; lia|]. split; [clear - Hsp44; lia|]. split; [intros o Ho; exfalso; clear - Ho; lia|].
unfold epi_chunks.
assert (CK4 : forall (jj : nat) (r : bv 5) off,
nth jj [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21] (Z_to_bv 64 0) = getr regs r ->
off = 2120 - 8 * Z.of_nat jj -> Z.of_nat jj < 7 ->
val_mem tfibsegs (mrestrict (w_H W2) mem4) (spZ regs - 8 - 8 * Z.of_nat jj) 8 (bv_unsigned (getr regs r)) ->
YP09.chunk_ok tfibsegs E4 (mrestrict (w_H W2) mem4) (spZ regs - 2128) (YP09.mkChunk off (CVal 8 (SOff (32 + jj) 0)))).
{ intros jj r off Hnth Hoff Hj8 Hv.
eapply (chunk_ok_val tfibsegs E4 _ (spZ regs - 2128) off 8 _ (bv_unsigned (getr regs r))).
- cbn [sv_denot]. subst E4. rewrite (ew_Ereg_extra regs4 _ jj), Hnth, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr regs r)). zside.
- zside.
- subst off. replace (spZ regs - 2128 + (2120 - 8 * Z.of_nat jj)) with (spZ regs - 8 - 8 * Z.of_nat jj) by lia.
exact Hv. }
repeat apply Forall_cons; try apply Forall_nil.
+ apply (CK4 0%nat 1%bv); [reflexivity | reflexivity | cbn; lia |
replace (spZ regs - 8 - 8 * Z.of_nat 0) with (spZ regs - 8) by (cbn; lia); exact WS0].
+ apply (CK4 1%nat 8%bv); [reflexivity | reflexivity | cbn; lia |
replace (spZ regs - 8 - 8 * Z.of_nat 1) with (spZ regs - 16) by (cbn; lia); exact WS1].
+ apply (CK4 2%nat 9%bv); [reflexivity | reflexivity | cbn; lia |
replace (spZ regs - 8 - 8 * Z.of_nat 2) with (spZ regs - 24) by (cbn; lia); exact WS2].
+ apply (CK4 3%nat 18%bv); [reflexivity | reflexivity | cbn; lia |
replace (spZ regs - 8 - 8 * Z.of_nat 3) with (spZ regs - 32) by (cbn; lia); exact WS3].
+ apply (CK4 4%nat 19%bv); [reflexivity | reflexivity | cbn; lia |
replace (spZ regs - 8 - 8 * Z.of_nat 4) with (spZ regs - 40) by (cbn; lia); exact WS4].
+ apply (CK4 5%nat 20%bv); [reflexivity | reflexivity | cbn; lia |
replace (spZ regs - 8 - 8 * Z.of_nat 5) with (spZ regs - 48) by (cbn; lia); exact WS5].
+ apply (CK4 6%nat 21%bv); [reflexivity | reflexivity | cbn; lia |
replace (spZ regs - 8 - 8 * Z.of_nat 6) with (spZ regs - 56) by (cbn; lia); exact WS6].
- apply pairwise_disjoint_of_extents. cbn. repeat split.
- split; [|split; exact I]. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E4_2. change (2 ^ 4) with 16. repeat split; try (clear - Hsp44; lia).
replace (spZ regs - 2128) with (spZ regs + (-133) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16. }
unfold cfg_at.
eapply SRr_bind; [exact (fr_phase W2 E4 ss_epi epi_e _ _ _ HSe r_epi)|].
cbv beta. intros W5 c5 _ (-> & ms5 & mat5 & -> & HS5 & HF5 & HFr5). rewrite ?wvb_wvb in *.
assert (MEQ5 : forall z, ms_mem ms5 z = mem4 z).
{ intros z. apply HF5. intros Hin. destruct (in_wrange_windows E4 _ _ Hin) as (bb & lo & hi & Ht & Hw).
cbn in Ht. destruct Ht as [Hq|[]]. injection Hq as <- <- <-. cbn [base_val] in Hw. clear - Hw. lia. }
eapply SRr_bind.
{ eapply (SRr_ret_at tfibsegs tbl_fr tbl_fr_ok AF0x.Hwx_tfa W2 E4); [exact HS5 | reflexivity | vm_compute; reflexivity |].
intros mat'. instantiate (1 := fun W' c' => W' = W2 /\ exists mat',
c' = mkCfg (mkst (ms_regs ms5) (v_jalr (getr (ms_regs ms5) 1) 0) (ms_mem ms5) (seg_rom tfibsegs))
(with_vm_backing (m_vm_lazy md4) mat' md4)).
cbv beta. rewrite wvb_wvb. split; [reflexivity|]. exists mat'. reflexivity. }
cbv beta. intros W6 c6 _ (-> & mat6 & ->).
rreg HS5 (1%bv : bv 5) P1. rreg HS5 (2%bv : bv 5) P2. rreg HS5 (3%bv : bv 5) P3. rreg HS5 (4%bv : bv 5) P4.
rreg HS5 (8%bv : bv 5) P8. rreg HS5 (9%bv : bv 5) P9. rreg HS5 (10%bv : bv 5) P10.
rreg HS5 (18%bv : bv 5) P18. rreg HS5 (19%bv : bv 5) P19. rreg HS5 (20%bv : bv 5) P20. rreg HS5 (21%bv : bv 5) P21.
rreg HS5 (22%bv : bv 5) P22. rreg HS5 (23%bv : bv 5) P23. rreg HS5 (24%bv : bv 5) P24. rreg HS5 (25%bv : bv 5) P25.
rreg HS5 (26%bv : bv 5) P26. rreg HS5 (27%bv : bv 5) P27.
assert (EX : forall jj rr, nth jj [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20; getr regs 21]
(Z_to_bv 64 0) = getr regs rr -> ew E4 (32 + jj) = getr regs rr)
by (intros jj rr Hnth; subst E4; rewrite (ew_Ereg_extra regs4 _ jj); exact Hnth).
assert (EY : forall i (rr : bv 5), Z.of_nat i = bv_unsigned rr -> ew E4 i = getr regs4 rr)
by (intros ii rr Hnth; subst E4; exact (ew_Ereg_nat regs4 _ ii rr Hnth)).
assert (X32 : ew E4 32 = getr regs 1) by (subst E4; exact (ew_Ereg_extra regs4 _ 0)).
rewrite X32 in P1.
replace (v_jalr (getr (ms_regs ms5) 1) 0) with (getr regs 1) by (rewrite P1; symmetry; exact Hra).
set (md6 := with_vm_backing (m_vm_lazy md4) mat6 md4) in *.
assert (MF46 : same_but_materialized md4 md6) by (subst md6; apply with_vm_backing_same).
pose proof (same_but_materialized_frame _ _ MF46) as (_ & F6maps & F6lazy & _ & _ & _ & _ & _ & F6fds & _ & _ & F6fs & _).
assert (AV5 : forall a, aview tfibsegs (w_H W2) (ms_mem ms5) a = aview tfibsegs (w_H W2) mem4 a)
by (intros a; apply aview_same; apply MEQ5).
assert (SBM26 : same_but_materialized md2 md6)
by (eapply same_but_materialized_trans; [exact TSBM | exact MF46]).
(* every byte outside the caller's window and the write set is as it was at the call *)
assert (AVfin : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - 8192 <= a < spZ regs) ->
~ PFreadM.rread_wrset f d nm a ->
aview tfibsegs (w_H W2) (ms_mem ms5) a = aview tfibsegs (w_H W) memc a).
{ intros a H1 H2 H3. rewrite AV5. rewrite TAV by (clear - H1 H2 AC1; lia).
rewrite (K1 a H1 ltac:(rewrite R1sp; unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK; clear - H2; lia) H3).
apply AV1; [clear - H1 AC1; lia | clear - H2; lia]. }
assert (AVband : forall s, kLowMemEnd <= s < kHighShadowEnd ->
aview tfibsegs (w_H W2) (ms_mem ms5) s = aview tfibsegs (w_H W) memc s).
{ intros s Hs. rewrite AV5. rewrite TAV by (clear - Hs SPC AC1; unfold kLowMemEnd, kHighShadowEnd in Hs; lia).
rewrite (HBAND2 s Hs). apply AVband1. exact Hs. }
assert (PMfin : forall a, apresent (w_H W) memc a -> alloc_ceiling <= a < 2 ^ 64 ->
~ (spZ regs - 8192 <= a < spZ regs) -> apresent (w_H W2) (ms_mem ms5) a).
{ intros a Hp H1 H2. apply (apresent_same (w_H W2) mem4 (ms_mem ms5) a (MEQ5 _)). apply TPM.
apply (K5 a H1 ltac:(rewrite R1sp; unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK; clear - H2; lia)).
apply PM1. exact Hp. }
assert (PMwin : forall a, spZ regs - 8192 <= a < spZ regs -> apresent (w_H W2) (ms_mem ms5) a).
{ intros a Ha. apply (apresent_same (w_H W2) mem4 (ms_mem ms5) a (MEQ5 _)). apply TPM.
destruct (Z_lt_le_dec a (spZ regs - 2128 - 4224)) as [L|L].
- apply (K5 a ltac:(clear - Ha SPC AC1 Hsp44; lia)
ltac:(rewrite R1sp; unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK; clear - L; lia)).
apply PM1. apply Hpres. clear - Ha Hslo Hshi; lia.
- destruct (Z_lt_le_dec a (spZ regs - 2128)) as [L2|L2].
+ apply K6. rewrite R1sp. unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK.
clear - L L2; lia.
+ apply (K5 a ltac:(clear - Ha SPC AC1 Hsp44; lia)
ltac:(rewrite R1sp; unfold PFreadM.RFREAD_STK, PFreadM.RTOREAD_STK, PFreadM.RMREAD_STK, ESTACK; clear - L2; lia)).
apply PM1. apply Hpres. clear - Ha Hslo Hshi; lia. }
(* ---- the post ---------------------------------------------------------------------------------- *)
apply SRr_ret. exists lyc, Sc, (ms_regs ms5), (ms_mem ms5), md6.
split; [reflexivity|].
split.
{ eapply (ajournal_after_write tfibsegs B LAWS tfib_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 k
(ms_mem ms5) md6 (fun a => spZ regs - 2128 - 72 <= a < spZ regs - 2128) Sc own HJ2).
- intros a Hr HW. rewrite AV5. apply TAV; [exact Hr | exact HW].
- intros a Hp. apply (apresent_same (w_H W2) mem4 (ms_mem ms5) a (MEQ5 _)). apply TPM. exact Hp.
- exact SBM26.
- intros a HW. left. left. clear - HW Hslo Hshi Hsp44. lia.
- apply (al_frame _ _ LAWS lyc Sc W2 mem4 md4 (ms_mem ms5) md6 TAR).
+ intros a Hr Hown. apply AV5.
+ intros a Hv. rewrite AV5. exact Hv.
+ exact F6maps.
+ exact F6lazy.
+ apply (same_but_materialized_frame md4 _ MF46).
+ exact (AE2y.hs_kept_eq _ _ _ MEQ5).
- reflexivity.
- reflexivity.
- lia.
- exact Hfrs.
- exact HQT. }
(* the bytes the whole call may have changed, as addresses outside the epilogue's reach *)
assert (MB54 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 2128 - 72 <= a < spZ regs - 2128) ->
mbyte tfibsegs (mrestrict (w_H W2) (ms_mem ms5)) a = mbyte tfibsegs (mrestrict (w_H W2) mem2) a)
by (intros a H1 H2; apply mbyte_of_aview; rewrite AV5; apply TAV; assumption).
assert (OUTWIN : forall a, (f <= a < f + SRC_FILE_BLOCK) \/ (b <= a < b + Z.of_nat (length C)) \/ asrc_env_addr K a ->
0 <= a < 2 ^ 64 /\ ~ (spZ regs - 2128 - 72 <= a < spZ regs - 2128)).
{ intros a [Hq | [Hq | Hq]].
- split; [clear - Hq Hf0 Hfceil AC1; unfold SRC_FILE_BLOCK in *; lia
| clear - Hq Hfceil Hslo Hlo Hceil; unfold SRC_FILE_BLOCK in *; lia].
- split; [clear - Hq Hbpos Hbwrap; lia | clear - Hq Hbstk Hbpos; lia].
- destruct (asil_env _ _ _ _ ASIL a Hq) as (Himg & _). pose proof (tfib_segs_low a Himg).
split; [clear - H; unfold kLowMemEnd in H; lia | clear - H SPC AC1; unfold kLowMemEnd in H; lia]. }
(* ---- the callee-saved registers the epilogue restored ------------------------------------------ *)
split.
{ intros rr Hr. unfold acallee_saved in Hr.
destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
* replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P2. apply bv_eq.
rewrite Z_to_bv_unsigned, E4_2. unfold spZ, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
pose proof (u64_range (getr regs 2)). rewrite Z.mod_small by lia. lia.
* replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite P3, (EY 3%nat 3%bv eq_refl), (TCSb 3%bv 3 ltac:(apply bv_eq; reflexivity)
ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)),
(K2r 3%bv 3 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)). exact Q3.
* replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite P4, (EY 4%nat 4%bv eq_refl), (TCSb 4%bv 4 ltac:(apply bv_eq; reflexivity)
ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)),
(K2r 4%bv 4 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)). exact Q4.
* replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P8.
exact (EX 1%nat 8%bv eq_refl).
* replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P9.
exact (EX 2%nat 9%bv eq_refl).
* assert (Hc : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27)
by lia.
destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]].
-- replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P18.
exact (EX 3%nat 18%bv eq_refl).
-- replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P19.
exact (EX 4%nat 19%bv eq_refl).
-- replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P20.
exact (EX 5%nat 20%bv eq_refl).
-- replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite P21.
exact (EX 6%nat 21%bv eq_refl).
-- replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite P22, (EY 22%nat 22%bv eq_refl), (TCSb 22%bv 22 ltac:(apply bv_eq; reflexivity)
ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)),
(K2r 22%bv 22 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
exact (RK 22%bv 22%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite P23, (EY 23%nat 23%bv eq_refl), (TCSb 23%bv 23 ltac:(apply bv_eq; reflexivity)
ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)),
(K2r 23%bv 23 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
exact (RK 23%bv 23%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite P24, (EY 24%nat 24%bv eq_refl), (TCSb 24%bv 24 ltac:(apply bv_eq; reflexivity)
ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)),
(K2r 24%bv 24 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
exact (RK 24%bv 24%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite P25, (EY 25%nat 25%bv eq_refl), (TCSb 25%bv 25 ltac:(apply bv_eq; reflexivity)
ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)),
(K2r 25%bv 25 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
exact (RK 25%bv 25%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite P26, (EY 26%nat 26%bv eq_refl), (TCSb 26%bv 26 ltac:(apply bv_eq; reflexivity)
ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)),
(K2r 26%bv 26 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
exact (RK 26%bv 26%nat eq_refl ltac:(cbn; lia)).
-- replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity).
rewrite P27, (EY 27%nat 27%bv eq_refl), (TCSb 27%bv 27 ltac:(apply bv_eq; reflexivity)
ltac:(unfold acallee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia)),
(K2r 27%bv 27 ltac:(apply bv_eq; reflexivity) ltac:(unfold acallee_saved; lia)).
exact (RK 27%bv 27%nat eq_refl ltac:(cbn; lia)). }
(* ---- what the whole call kept, against the state at the call ---------------------------------- *)
split.
{ split; [exact AVfin|].
split.
{ intros bb m i Hin Hi HE. rewrite AV5.
destruct (al_blocks _ _ LAWS lyc Sc W2 mem2 md2 bb m (proj1 HJ2) Hin) as (_ & Hb0 & Hbceil & _).
rewrite TAV by (clear - Hb0 Hbceil Hi Hslo Hlo Hceil AC1; lia).
rewrite (K2b bb m i Hin Hi HE). apply AV1; clear - Hb0 Hbceil Hi Hslo Hlo Hceil AC1; lia. }
split.
{ intros a Himg Hown Herr. pose proof (tfib_segs_low a Himg) as Hlow. rewrite AV5.
rewrite TAV by (clear - Hlow SPC AC1; unfold kLowMemEnd in Hlow; lia).
rewrite (K3 a Himg Hown Herr). apply AV1; clear - Hlow SPC AC1; unfold kLowMemEnd in Hlow; lia. }
split.
{ intros cid pos a Hin Hr HE.
destruct (frames_bounds tfibsegs B LAWS lyc Sc W2 mem2 md2 cid pos (proj1 HJ2) Hin) as (Hf0' & Hfc & _).
pose proof (fs_frame_bytes_nonneg cid) as Hnn.
assert (HA : 0 <= a < 2 ^ 64 /\ ~ (spZ regs - 2128 - 72 <= a < spZ regs - 2128) /\
~ (spZ regs - 2144 <= a < spZ regs)).
{ unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr. destruct Hr as [Hr | Hr].
- repeat split; clear - Hr Hf0' Hfc Hnn SPC AC1; lia.
- pose proof (AE2y.shadow_addr_bounds (frame_addr lyc cid pos)
ltac:(clear - Hf0' Hfc AC1 Hnn; unfold kHighMemEnd; lia)) as [B1 B2].
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hnn) as Hse.
pose proof (AE2y.shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid)
ltac:(clear - Hf0' Hfc AC1 Hnn; unfold kHighMemEnd; lia)) as [T1 T2].
repeat split; clear - Hr B1 T2 Hse SPC AC1; unfold kLowMemEnd, kHighShadowEnd in *; lia. }
destruct HA as (HA1 & HA2 & HA3). rewrite AV5. rewrite TAV by assumption.
rewrite (K4 cid pos a Hin Hr HE). apply AV1; assumption. }
split; [intros a H1 H2 Hp; exact (PMfin a Hp H1 H2) | exact PMwin]. }
(* ---- the post of the call ---------------------------------------------------------------------- *)
split; [reflexivity|]. split; [reflexivity|].
split.
{ replace (Z_to_bv 5 10) with (10%bv : bv 5) in * by (apply bv_eq; reflexivity).
rewrite P10, (EY 10%nat 10%bv eq_refl), T10. exact A10_2. }
assert (HLEN : Z.of_nat (length (firstn (Z.to_nat (rread_k nm (Z.of_nat (length C)) p)) (skipn (Z.to_nat p) C)))
<= rread_k nm (Z.of_nat (length C)) p) by (rewrite length_firstn; clear - Hj0; lia).
split.
{ apply (garr8_frame tfibsegs (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms5)) _ _ HGAR).
intros a Ha. apply MB54.
- clear - Ha HLEN Hj0 Hnm Hd0 Hdam. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hdam. lia.
- destruct (Hdwr a ltac:(clear - Ha HLEN Hj0; lia)) as (_ & Hns). clear - Hns. lia. }
split.
{ apply (asrc_kept K (mrestrict (w_H W2) mem2) (mrestrict (w_H W2) (ms_mem ms5)) f b C
(p + rread_k nm (Z.of_nat (length C)) p)); [|exact HSRC2].
intros a Ha. destruct (OUTWIN a Ha) as (HA1 & HA2). apply MB54; assumption. }
split.
{ destruct HMODE2 as (HM1 & HM2). split; [|exact HM2].
apply (AF0x.val_mem_ext (mrestrict (w_H W2) mem2)); [|exact HM1].
intros kk Hk. apply MB54.
- clear - Hk Hf0 Hfceil AC1; cbn in Hk; unfold SRC_FILE_BLOCK in *; lia.
- clear - Hk Hfceil Hslo Hlo Hceil; cbn in Hk; unfold SRC_FILE_BLOCK in *; lia. }
split.
{ intros Hnm0 a Ha Hnot. destruct (OUTWIN a ltac:(left; exact Ha)) as (HA1 & HA2).
rewrite AV5. rewrite TAV by assumption.
rewrite (HZERO2 Hnm0 a Ha Hnot). apply AV1;
[exact HA1 | clear - Ha Hfceil Hslo Hlo Hceil; unfold SRC_FILE_BLOCK in *; lia]. }
split; [rewrite F6fds, F4fds, HFDS2; subst md1; symmetry;
apply (same_but_materialized_frame mdc _ MF1)|].
split; [rewrite F6fs, F4fs, HFS2; subst md1; symmetry;
apply (same_but_materialized_frame mdc _ MF1)|].
exact AVband.
Qed.

End g.

End d.
