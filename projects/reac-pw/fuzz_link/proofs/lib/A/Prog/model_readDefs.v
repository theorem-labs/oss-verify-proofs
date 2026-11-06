(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8v.v:120-122
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:518-584, 622-634 [Apache-2.0 OR MIT];
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:110-141, 221-225, 227-235, 264-270 [Apache-2.0 OR MIT], for
   libreac/fuzz_identity's ASan build (lib/A). The [Apache-2.0 OR MIT] text is used under Apache-2.0. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/A/Prog/LLVMFuzzerTestOneInput_L.v, with its module paths, module names and numbers changed; 297 of its 339 lines of code are new or changed and 1038 lines of the source are left out. *)
(* model_read (fuzz_link.asan 0x8642c, 728 bytes; listing
   (internal path) (internal record, sha256 5070c0eed28b), listing offset
   AF_model_read = 0x4260): the symbolic states of its image-A walk, the entry lemma, and the statements the walk's
   segment lemmas share (the Post MR_POST of lib/A/Prog/model_read_c.v `model_read_acontract`, the premises MR_ENTRY of
   its aleaf_rd, and the state MR_AT120 at the branch on kind, +0x120).
   The atoms: 0..31 are the entry registers (10 = m, 11 = name, 12 = kind, 13 = kind_n, 14 = alias, 15 = alias_n),
   32 = the shadow base, 40.. = the junk of the first call (44 = its a0 = the frame F), 60 = the realigned sp,
   61 = the frame's flag, 62 = SB + F / 8 (the frame's shadow, through the alias YP0i.v shadow_decl_ok).
   Proves no function (kind: segment lemma of model_read's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YN3v YI04 YI16 YG0s YA0d YA0j.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkSyms LinkList LinkAddr LinkPa LinkPaLib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import W_journalG.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem LinkWalk link_ajkit.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkWalkPi LinkWalkSide LinkWalkCall.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import model_read_c index_of_c talk_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YN2j.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* ==========================================================================
   The symbolic data
   ========================================================================== *)
Definition MR_SB : Z := 0x7fff8000.
Lemma MR_SB_eq : MR_SB = SHADOW_OFF. Proof. reflexivity. Qed.
Definition MRBx : sv := SOff 32 0.
Definition MRspan : Z * Z := (MR_SB, MR_SB + 2 ^ 44 - 1).
Definition MR_extra : list word := [Z_to_bv 64 MR_SB].

Definition mr_stack : YP09.region := YP09.mkRegion (Some 2%nat) (-128) 0 (-128) 0 [].
Definition mr_got : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 1)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 64) 0))].
Definition mr_cell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 64)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition mr_ugot : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 0)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff (A_OBJ 65) 0))].
Definition mr_ucell : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 65)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SLit 1))].
Definition mr_regions : smem := [mr_stack; mr_got; mr_cell; mr_ugot; mr_ucell].
Definition mr_facts : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF MR_SB MR_SB 0)] [] [].
Definition mr_ss : sstate := mkSS AF_model_read sr_atoms mr_regions None mr_facts.

(* the state at +0x208 (the exit, where every path joins): the frame F (its flag word at 120), its shadow, the flag
   byte, the thirteen saved words; the caller-saved registers, s8 and s9 forgotten to atoms 1000..1017 (CLOB208); s2 = s11
   = F, s10 = SB + F / 8, s0 = the entry sp *)
Definition CLOB208 : list (bv 5) := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 24; 25; 28; 29; 30; 31]%bv.
Definition mr_regs208 : list sv :=
  [SLit 0; SOff 1000 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 1001 0; SOff 1002 0; SOff 1003 0; SOff 2 0; SOff 60 0;
   SOff 1004 0; SOff 1005 0; SOff 1006 0; SOff 1007 0; SOff 1008 0; SOff 1009 0; SOff 1010 0; SOff 1011 0;
   SOff 44 0; SOff 14 0; SOff 15 0; SOff 12 0; SOff 13 0; SOff 10 0; SOff 1012 0; SOff 1013 0; SOff 62 0;
   SOff 44 0; SOff 1014 0; SOff 1015 0; SOff 1016 0; SOff 1017 0].
Definition mr_stk104 : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition mr_flag : YP09.region := YP09.mkRegion (Some 61%nat) 0 1 0 1 [].
Definition mr_facts208 : facts :=
  mkFacts [(62%nat, mkAF MR_SB (MR_SB + 2 ^ 44) 3); (44%nat, mkAF 4096 (2 ^ 47) 6);
           (60%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF MR_SB MR_SB 0);
           (61%nat, mkAF 4096 (2 ^ 47) 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 44 0) (SLit 3)) (SOff 32 0), SOff 62 0)].
(* the same state with the frame's three regions and the flag's fact set aside (the checks segment and the calls
   run without them) *)
Definition mr_facts208d : facts :=
  mkFacts [(62%nat, mkAF MR_SB (MR_SB + 2 ^ 44) 3); (44%nat, mkAF 4096 (2 ^ 47) 6);
           (60%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (32%nat, mkAF MR_SB MR_SB 0)] []
    [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 44 0) (SLit 3)) (SOff 32 0), SOff 62 0)].
Definition mr_ss208d : sstate := mkSS (AF_model_read + 0x208) mr_regs208 [mr_stk104] None mr_facts208d.
Definition mr_ss208 : sstate :=
  mkSS (AF_model_read + 0x208) mr_regs208
    [mr_flag; fshadow_region 62 1 0 16 []; fframe_region 44 61 1 []; mr_stk104] None mr_facts208.

(* the all_disjoint obligation of st_ok_pi_add_region, with the region list computed and the extents opened *)
Ltac mr_disj :=
  lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy =>
    let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
  cbn [all_disjoint]; unfold extent_disjoint, fframe_region, fshadow_region;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  try change (fs_frame_bytes 1) with 128; try change (fs_frame_bytes 1 / 8) with 16.

(* a segment of the PLAIN engine over ajournal_gx (LinkWalkSide.v paj_run_plain_x) *)
Ltac mr_run_plain RUNP HS HJ :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
    let r := eval vm_compute in (sym_runN_pi link_tpi FUEL ss) in
    lazymatch r with
    | (?ss', ?st) =>
      let Hrun := fresh "Hrun" in
      assert (Hrun : sym_runN_pi link_tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
      let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI end in
      eapply (RUNP W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
      [ clear Hrun
      | clear Hrun HS HJ;
        let ms' := fresh "ms" in let mat := fresh "mat" in
        let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
        intros ms' mat HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ ]
    end
  end.

(* the state at +0x120 (the branch on kind): the head's end state (lib/A/Prog/model_readHead.v), as the engine
   computes it *)
Definition mr_ss120 : sstate :=
  (mkSS 17280 [SLit 0; SOff 40 0; SOff 60 0; SOff 3 0; SOff 4 0; SOff 41 0; SOff 42 0; SOff 43 0; SOff 2 0; SOff 60 0; SLit 18446744073709551603; SOff 264 0; SOff 265 0; SOff 47 0; SOff 48 0; SOff 49 0; SOff 50 0; SOff 51 0; SOff 44 0; SOff 14 0; SOff 15 0; SOff 12 0; SOff 13 0; SOff 10 0; SOff 11 0; SOff 32 0; SOff 62 0; SOff 44 0; SOff 52 0; SOff 53 0; SOff 54 0; SOff 55 0] [{| r_base := Some 62%nat; r_lo := 0; r_hi := 16; r_wlo := 0; r_whi := 16; r_chunks := [{| c_off := 11; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 10; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 9; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 8; YP09.c_val := CVal 1 (SLit 18446744073709551603) |}; {| c_off := 3; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 2; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 1; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 0; YP09.c_val := CVal 1 (SLit 18446744073709551601) |}; {| c_off := 7; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 6; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 5; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 4; YP09.c_val := CVal 1 (SLit 18446744073709551608) |}; {| c_off := 12; YP09.c_val := CZero 4 |}] |}; {| r_base := Some 44%nat; r_lo := 0; r_hi := 128; r_wlo := 0; r_whi := 128; r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 265 0) |}; {| c_off := 8; YP09.c_val := CVal 8 (SOff 264 0) |}; {| c_off := 0; YP09.c_val := CVal 8 (SLit 1102416563) |}; {| c_off := 120; YP09.c_val := CVal 8 (SOff 61 0) |}] |}; {| r_base := Some 60%nat; r_lo := 0; r_hi := 24; r_wlo := 0; r_whi := 24; r_chunks := [{| c_off := 16; YP09.c_val := CVal 8 (SOff 44 0) |}] |}; {| r_base := Some 2%nat; r_lo := -104; r_hi := 0; r_wlo := -104; r_whi := 0; r_chunks := [{| c_off := -104; YP09.c_val := CVal 8 (SOff 27 0) |}; {| c_off := -96; YP09.c_val := CVal 8 (SOff 26 0) |}; {| c_off := -88; YP09.c_val := CVal 8 (SOff 25 0) |}; {| c_off := -80; YP09.c_val := CVal 8 (SOff 24 0) |}; {| c_off := -72; YP09.c_val := CVal 8 (SOff 23 0) |}; {| c_off := -64; YP09.c_val := CVal 8 (SOff 22 0) |}; {| c_off := -56; YP09.c_val := CVal 8 (SOff 21 0) |}; {| c_off := -48; YP09.c_val := CVal 8 (SOff 20 0) |}; {| c_off := -40; YP09.c_val := CVal 8 (SOff 19 0) |}; {| c_off := -32; YP09.c_val := CVal 8 (SOff 18 0) |}; {| c_off := -24; YP09.c_val := CVal 8 (SOff 9 0) |}; {| c_off := -16; YP09.c_val := CVal 8 (SOff 8 0) |}; {| c_off := -8; YP09.c_val := CVal 8 (SOff 1 0) |}] |}] None {| f_atoms := [(62%nat, {| af_lo := 2147450880; af_hi := 17594333495296; af_al2 := 3 |}); (44%nat, {| af_lo := 4096; af_hi := 140737488355328; af_al2 := 6 |}); (60%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 5 |}); (2%nat, {| af_lo := 70368744177664; af_hi := 140737488355328; af_al2 := 4 |}); (32%nat, {| af_lo := 2147450880; af_hi := 2147450880; af_al2 := 0 |})]; f_conds := []; f_alias := [(SAlu ALU_ADD (SAlu ALU_SRL (SOff 44 0) (SLit 3)) (SOff 32 0), SOff 62 0)] |}).

(* +0x120 .. +0x17c run with the frame's two regions set aside (their windows may meet the shadow span, which the
   instrumented checks need clear): the state without them, and the two joins (+0x13c after the kind test and its
   guarded NUL store, +0x15c after alias's), a0 and a1 forgotten to fresh atoms, the branch conditions dropped *)
Definition mr_ss120d : sstate := Eval vm_compute in
  mkSS (ss_pc mr_ss120) (ss_regs mr_ss120) (YP03.pick (ss_mem mr_ss120) [2; 3]%nat) (ss_resv mr_ss120)
    (ss_facts mr_ss120).
Definition mr_join (k : nat) (pc : Z) (s : sstate) : sstate :=
  let t := ss_after_stretch s (ss_mem s) k [10%bv; 11%bv] (AF_model_read + pc) in
  mkSS (ss_pc t) (ss_regs t) (ss_mem t) None (mkFacts (f_atoms (ss_facts t)) [] (f_alias (ss_facts t))).
Definition mr_ss13c : sstate := Eval vm_compute in
  mr_join 600 0x13c (fst (sym_runN_pi link_tpi FUEL (add_cond mr_ss120d (mkAC BC_EQ (SOff 12 0) (SLit 0))))).
Definition mr_join1 (k : nat) (pc : Z) (s : sstate) : sstate :=
  let t := ss_after_stretch s (ss_mem s) k [11%bv] (AF_model_read + pc) in
  mkSS (ss_pc t) (ss_regs t) (ss_mem t) None (mkFacts (f_atoms (ss_facts t)) [] (f_alias (ss_facts t))).
(* +0x15c (the branch on name, a0 = -22 set at +0x158): a1 forgotten *)
Definition mr_ss15c : sstate := Eval vm_compute in
  mr_join1 602 0x15c (fst (sym_runN_pi link_tpi FUEL (add_cond mr_ss13c (mkAC BC_EQ (SOff 14 0) (SLit 0))))).
(* the range fact of an argument pointer the instrumented checks cover *)
Definition MR_PF : afact := mkAF 0 (2 ^ 47 - 1) 0.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context (SK : YI16.sink_head).
#[local] Existing Instance SK.
Section b.
Context {PI : PAImg link_listing}.
#[local] Notation SEGS := (@pa_segs _ link_listing PI).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
Hypothesis TL : PALib B.
Hypothesis LV : LinkVals.
(* the segment computations the walk needs (g_nl writable, the relro window): the link PAImg instance discharges
   this by reflexivity *)
Hypothesis HSEGS : pa_segs = tfibsegs.
(* frame_alloc_1 (0x3da88): lib/A/AF0s.v stack_malloc1_contract *)
Hypothesis ASM1 : astack_malloc_realizes pa_segs B 1.
Hypothesis HSM1 : pc_stack_malloc (as_code B) 1 = pa_sigma LS___asan_stack_malloc_1.
(* checked_memset (0x53214): lib/A/AE2r.v asan_memset_realizes *)
Hypothesis AMSET : aintrin_realizes pa_segs B OSet (pa_sigma LS___asan_memset).
(* the two own callees *)
Hypothesis IDX : forall rlo rhi, index_of_acontract SK pa_segs rlo rhi B.
Hypothesis TALK : forall rlo rhi, talk_acontract SK pa_segs rlo rhi B.
(* the aleaf_rd premises of model_read_acontract at one call *)
Definition MR_ENTRY (rlo rhi : Z) G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) : Prop :=
  apre SK pa_segs rlo rhi B MODEL_READ_AK 0 MODEL_READ_ASIDE (model_read_awr regs (rdW W memc))
    G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs /\
  (forall a, model_read_ard pa_segs regs (rdW W memc) a ->
     akb pa_segs B lyc Sc (spZ regs - MODEL_READ_AK) (spZ regs) a) /\
  model_read_apre pa_segs B regs (rdW W memc).

(* its conclusion *)
Definition MR_POST G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) : world pa_segs -> config -> Prop :=
  apost SK pa_segs B MODEL_READ_AK 0 (fun a => inFP (model_read_awr regs (rdW W memc)) a) G XO OUT STK sp0 FP
    ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       S2 = set_fs (st_fs S2) Sc /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
       model_read_apost pa_segs regs (rdW W memc) regs2 (rdW W2 mem2)).

(* the state at +0x120: the frame F = frame_addr lyc 1 pos taken (its header and shadow written), on the caller's
   journal at own (1, pos) :: own; the kept clause from the call excepts only the frame's bytes *)
Definition MR_AT120 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) (E : env) (ms : machine_state) (md1 : Model) (S1 : astate) (pos : Z) : Prop :=
  img_env pa_val A_LIM E /\ env_agree 32 (Ereg regs MR_extra) E /\
  ew E 32 = Z_to_bv 64 MR_SB /\ ew E 44 = Z_to_bv 64 (frame_addr lyc 1 pos) /\
  ew E 60 = Z_to_bv 64 (32 * ((spZ regs - 128) / 32)) /\ ew E 61 = Z_to_bv 64 (flag_addr lyc 1 pos) /\
  ew E 62 = Z_to_bv 64 (MR_SB + frame_addr lyc 1 pos / 8) /\
  st_ok_pi pa_segs pa_val E mr_ss120 (restrict (w_H W) ms) /\
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W (ms_mem ms) md1 k /\
  frames S1 = (1, pos) :: frames Sc /\ ablocks B lyc S1 = ablocks B lyc Sc /\ ~ In (1, pos) (frames Sc) /\
  (exists f, S1 = set_fs f Sc) /\
  akept pa_segs B lyc Sc W memc W (ms_mem ms) (spZ regs - MODEL_READ_AK) (spZ regs) (aside_rng lyc 1 pos) /\
  same_but_materialized mdc md1.

(* the state at +0x15c (the branch on name, a0 = -22), the frame's regions set aside: the facts of +0x120 the rest
   of the walk needs (the AR of the frame's call at m120, the frame's flag word there, the write set writable there),
   and what the checks segment kept: every byte but the frame's, kind[0] and alias[0] (now 0), and the frame's bytes
   as at m120 *)
Definition MR_AT15C G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) (E : env) (ms : machine_state) (md : Model) (S1 : astate) (pos : Z)
    (m120 : word -> option byte) (md1 : Model) : Prop :=
  img_env pa_val A_LIM E /\ env_agree 32 (Ereg regs MR_extra) E /\
  ew E 32 = Z_to_bv 64 MR_SB /\ ew E 44 = Z_to_bv 64 (frame_addr lyc 1 pos) /\
  ew E 60 = Z_to_bv 64 (32 * ((spZ regs - 128) / 32)) /\ ew E 61 = Z_to_bv 64 (flag_addr lyc 1 pos) /\
  ew E 62 = Z_to_bv 64 (MR_SB + frame_addr lyc 1 pos / 8) /\
  st_ok_pi pa_segs pa_val E mr_ss15c (restrict (w_H W) ms) /\
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) lyc S1 W (ms_mem ms) md k /\
  same_but_materialized mdc md /\
  AR pa_segs B lyc S1 W m120 md1 /\ frames S1 = (1, pos) :: frames Sc /\ ablocks B lyc S1 = ablocks B lyc Sc /\
  ~ In (1, pos) (frames Sc) /\ (exists f, S1 = set_fs f Sc) /\
  val_mem pa_segs (rdW W m120) (frame_addr lyc 1 pos + 120) 8 (flag_addr lyc 1 pos) /\
  (forall a, inFP (model_read_awr regs (rdW W memc)) a -> writable_at pa_segs (rdW W memc) a ->
     writable_at pa_segs (rdW W m120) a) /\
  mem_grows (rdW W m120) (rdW W (ms_mem ms)) /\
  akept pa_segs B lyc Sc W memc W (ms_mem ms) (spZ regs - MODEL_READ_AK) (spZ regs)
    (fun a => aside_rng lyc 1 pos a \/ (aarg regs 2 <> 0 /\ 1 <= aarg regs 3 /\ a = aarg regs 2)
              \/ (aarg regs 4 <> 0 /\ 1 <= aarg regs 5 /\ a = aarg regs 4)) /\
  (forall a, in_zr a (frame_rng lyc (1, pos)) \/ in_zr a (shadow_addr (frame_addr lyc 1 pos), 16) ->
     aview pa_segs (w_H W) (ms_mem ms) a = aview pa_segs (w_H W) m120 a) /\
  (aarg regs 2 <> 0 -> 1 <= aarg regs 3 -> aview pa_segs (w_H W) (ms_mem ms) (aarg regs 2) = Some 0) /\
  (aarg regs 4 <> 0 -> 1 <= aarg regs 5 -> aview pa_segs (w_H W) (ms_mem ms) (aarg regs 4) = Some 0).

(* the Post's body at a memory, with the answer rc in place of a0 *)
Definition MR_QM (regs : bvmap 5 word) (W : world pa_segs) memc (rcv : Z) (m' : word -> option byte) : Prop :=
  forall regs' : bvmap 5 word, getr regs' 10 = w64 rcv -> model_read_apost pa_segs regs (rdW W memc) regs' m'.

(* the state at +0x208: the frame still taken, the journal at own (1, pos) :: own at any later layout, the kept
   clause from the call, a0 = rcv, and the Post's body already holding *)
Definition MR_AT208 G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc (W : world pa_segs) memc mdc k
    (regs : bvmap 5 word) (E : env) (ms : machine_state) (md2 : Model) (ly2 : alayout) (S2 : astate)
    (W2 : world pa_segs) (k2 pos rcv : Z) : Prop :=
  img_env pa_val A_LIM E /\ env_agree 32 (Ereg regs MR_extra) E /\
  ew E 32 = Z_to_bv 64 MR_SB /\ ew E 44 = Z_to_bv 64 (frame_addr lyc 1 pos) /\
  ew E 60 = Z_to_bv 64 (32 * ((spZ regs - 128) / 32)) /\ ew E 61 = Z_to_bv 64 (flag_addr lyc 1 pos) /\
  ew E 62 = Z_to_bv 64 (MR_SB + frame_addr lyc 1 pos / 8) /\
  st_ok_pi pa_segs pa_val E mr_ss208 (restrict (w_H W2) ms) /\
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 ((1, pos) :: own) ly2 S2 W2 (ms_mem ms) md2 k2 /\
  k2 <= k /\ (exists f, S2 = set_fs f Sc) /\ Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
  (exists S1 W1 mem1 md1, AR pa_segs B lyc S1 W1 mem1 md1 /\ frames S1 = (1, pos) :: frames Sc /\
     ablocks B lyc S1 = ablocks B lyc Sc) /\ ~ In (1, pos) (frames Sc) /\
  akept pa_segs B lyc Sc W memc W2 (ms_mem ms) (spZ regs - MODEL_READ_AK) (spZ regs)
    (fun a => inFP (model_read_awr regs (rdW W memc)) a \/ aside_rng lyc 1 pos a) /\
  m_fds md2 = m_fds mdc /\ m_fs md2 = m_fs mdc /\
  getr (ms_regs ms) 10 = w64 rcv /\ MR_QM regs W memc rcv (rdW W2 (ms_mem ms)).

(* a byte of the write set: an application byte, outside the window, not errno, and one the caller's journal lets
   its callee write *)
Lemma mr_wr_facts : forall rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs,
  MR_ENTRY rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ->
  forall a, inFP (model_read_awr regs (rdW W memc)) a ->
    (a < kLowMemEnd \/ kHighMemBeg <= a) /\ ~ (spZ regs - MODEL_READ_AK <= a < spZ regs) /\
    ~ (as_errno B <= a < as_errno B + 4) /\ ajw B G XO OUT STK sp0 FP ly S lyc Sc own a /\ 0 <= a < 2 ^ 64.
Proof.
intros rlo rhi G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (HPRE & HRD & HP) a Ha.
destruct HPRE as (HJ & HGok & HROD & Hraw & Hra4 & Hgp & Htp & Hal16 & Hwlo & Hwhi & Hev & Hside & Hajw & Hnro).
destruct HP as (mbs & kbs & tab & nm & PMOD & PMWF & PNLK & PNWF & PTAB & PNM & PBK & PBA & PRAN & PRAI & PSCN
  & PSCT & PRAM & PHUM & PMR & PRAC & PHUC & PGNM & PFRM & PFRK & PFRA & PERM & PERK & PERA & PKB & PAB & PNSEP
  & PKA).
pose proof (Hajw a Ha) as HW.
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (A0 : 0 <= aarg regs 0) by (unfold aarg, argZ; apply u64_range).
assert (A2 : 0 <= aarg regs 2) by (unfold aarg, argZ; apply u64_range).
assert (A4 : 0 <= aarg regs 4) by (unfold aarg, argZ; apply u64_range).
destruct Ha as (r & Hin & Hr). cbn [model_read_awr In] in Hin. unfold aivl in Hin.
destruct Hin as [<- | [<- | [<- | []]]]; cbn [fst snd] in Hr.
- unfold amem_range in PMR. unfold apart_frame in PFRM. unfold apart in PERM.
  refine (conj _ (conj _ (conj _ (conj HW _)))); lia.
- destruct (aarg regs 2 =? 0) eqn:E0; [lia | apply Z.eqb_neq in E0].
  destruct (PKB E0 ltac:(lia)) as (_ & _ & _ & PMRk & _).
  pose proof (PFRK E0) as PF. pose proof (PERK E0 ltac:(lia)) as PE.
  unfold amem_range in PMRk. unfold apart_frame in PF. unfold apart in PE.
  refine (conj _ (conj _ (conj _ (conj HW _)))); lia.
- destruct (aarg regs 4 =? 0) eqn:E0; [lia | apply Z.eqb_neq in E0].
  destruct (PAB E0 ltac:(lia)) as (_ & _ & _ & PMRk & _).
  pose proof (PFRA E0) as PF. pose proof (PERA E0 ltac:(lia)) as PE.
  unfold amem_range in PMRk. unfold apart_frame in PF. unfold apart in PE.
  refine (conj _ (conj _ (conj _ (conj HW _)))); lia.
Qed.

(* a join: a state at a listing-relative pc holds any state it merges into (YN2j.v st_ok_merge, listing-relative) *)
Lemma mr_st_ok_pi_merge : forall E ss' ss ms,
  st_ok_pi pa_segs pa_val E ss ms -> YN2j.mergeb ss' ss = true -> st_ok_pi pa_segs pa_val E ss' ms.
Proof.
intros E ss' ss ms HS H. unfold st_ok_pi, abs_ss in *. apply (YN2j.st_ok_merge pa_segs E _ _ ms HS).
destruct ss' as [p' r' m' v' f'], ss as [p r m v f]. unfold YN2j.mergeb in *. unfold setpc.
cbn -[Z.eqb YN2j.submemb regions_wf YN2j.facts_subb forallb combine Nat.eqb length] in *.
apply andb_true_iff in H as [H H7]. apply andb_true_iff in H as [H H6]. apply andb_true_iff in H as [H H5].
apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
apply Z.eqb_eq in H1. subst p'.
rewrite Z.eqb_refl, H2, H3, H4, H5, H6, H7. reflexivity.
Qed.

Lemma mr_region_kept_same : forall E m r, region_kept pa_segs E m m r.
Proof. intros E m r. split; intros a Ha; [reflexivity | intros H; exact H]. Qed.

Let errno_low := pal_env B TL.
Let HBgot := pal_got_shadow B TL.
Let HBcell := pal_cell B TL.
Let HBguar := pal_got_uar B TL.
Let HBuar := pal_uar_cell B TL.

Lemma mr_obj_val : forall i, (i < link_nobj)%nat -> pa_val (A_OBJ i) = link_obj i.
Proof. intros i Hi. exact (lv_obj LV i Hi). Qed.

(* THE ENTRY STATE *)
Lemma mr_entry : forall G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word),
  ajournal_gx pa_segs B G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - MODEL_READ_AK -> spZ regs <= sp0 ->
  st_ok_pi pa_segs pa_val (Eimg (Ereg regs MR_extra)) mr_ss
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (pa_val A_TEXT + AF_model_read)) memc (seg_rom pa_segs))).
Proof.
intros G XO OUT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs HJX Hal16 Hwlo Hwhi.
destruct HJX as (HSTK & HXO & (memS & HJ & Hag) & Hout).
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as ((C1a & C1b) & C2 & C3 & C4 & C5).
assert (HK : MODEL_READ_AK = 8416) by reflexivity.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite HBguar, HBuar in Kguar. rewrite HBuar in Kuar.
pose proof (mr_obj_val 0%nat ltac:(unfold link_nobj; lia)) as V0.
pose proof (mr_obj_val 1%nat ltac:(unfold link_nobj; lia)) as V1.
pose proof (mr_obj_val 64%nat ltac:(unfold link_nobj; lia)) as V64.
pose proof (mr_obj_val 65%nat ltac:(unfold link_nobj; lia)) as V65.
cbv [link_obj] in V0, V1, V64, V65.
set (E := Eimg (Ereg regs MR_extra)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs MR_extra) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 MR_SB)
  by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs MR_extra 0)).
assert (EIMG : forall i, (i < 66)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (pa_val (A_OBJ i)))
  by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VBI : forall i, (i < 66)%nat -> base_val E (Some (A_OBJ i)) = pa_val (A_OBJ i)).
{ intros i Hi. cbn [base_val]. rewrite (EIMG i Hi). apply unsigned_lit_small.
  pose proof (pa_val_range (A_OBJ i)). lia. }
rewrite restrict_mkst_fx. unfold mr_ss. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold mr_regions, mr_stack, mr_got, mr_cell, mr_ugot, mr_ucell.
  repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  + cbn [base_val]. fold E. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable pa_segs). cbn [ms_mem restrict mkst]. apply Hpres. lia.
  + fold E. rewrite (VBI 1%nat ltac:(lia)).
    split; [rewrite V1; lia|]. split; [rewrite V1; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 1)) 0 8 (SOff (A_OBJ 64) 0) (pa_val (A_OBJ 64)));
      [ cbn [sv_denot]; rewrite (EIMG 64%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 64)); zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kgot).
  + fold E. rewrite (VBI 64%nat ltac:(lia)).
    split; [rewrite V64; lia|]. split; [rewrite V64; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 64)) 0 8 (SOff 32 0) MR_SB);
      [ cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | unfold MR_SB; zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kcell).
  + fold E. rewrite (VBI 0%nat ltac:(lia)).
    split; [rewrite V0; lia|]. split; [rewrite V0; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 0)) 0 8 (SOff (A_OBJ 65) 0) (pa_val (A_OBJ 65)));
      [ cbn [sv_denot]; rewrite (EIMG 65%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 65)); zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rdword pa_segs (w_H W) memc _ _ Kguar).
  + fold E. rewrite (VBI 65%nat ltac:(lia)).
    split; [rewrite V65; lia|]. split; [rewrite V65; lia|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val pa_segs E _ (pa_val (A_OBJ 65)) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
    rewrite Z.add_0_r. cbn [ms_mem restrict mkst].
    exact (val_mem_of_rd32 pa_segs (w_H W) memc _ _ Kuar).
- apply pairwise_disjoint_of_extents.
  unfold mr_regions, mr_stack, mr_got, mr_cell, mr_ugot, mr_ucell, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
  fold E. rewrite !VBI by lia. cbn [base_val]. rewrite Usp.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  rewrite V0, V1, V64, V65.
  revert Hslo Hshi H47 Hceil C1a C1b C3 HK Hstk0 Hwlo Hwhi. clear. intros. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [mr_facts f_atoms atoms_ok]. split; [|split; [|exact I]].
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E. rewrite Usp. change (2 ^ 4) with 16.
    revert Hal16 Hslo Hshi H47 Hceil C1a C1b C3 HK Hstk0 Hwlo Hwhi HSTK HXO. clear. intros.
    repeat split; lia.
  + unfold afact_ok. cbn [af_lo af_hi af_al2]. fold E.
    rewrite E32, unsigned_lit_small by (unfold MR_SB; lia).
    rewrite Z.pow_0_r, Z.mod_1_r. repeat split; lia.
Qed.

End b.
End a.
