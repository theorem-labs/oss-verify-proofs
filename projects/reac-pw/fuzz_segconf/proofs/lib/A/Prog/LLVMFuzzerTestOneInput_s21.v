(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the first stretch of the inlined words_of of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86760 .. 0x867b4: strnlen of the message, the three mallocs stored at 120/128/136(sp) and their NULL tests reloaded from the frame), the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s41.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v (a call and back, the caller's facts carried past it) and A/ACh6.v (a segment from one point of the function to the next, the next point's statement a premise). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s41.v, with its module paths, module names and numbers changed; 2758 of its 2894 lines of code are new or changed and 886 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/LLVMFuzzerTestOneInput_s20.v, with its module paths and module names changed; 1679 of its 1815 lines of code are new or changed and 2758 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan image A (fuzz_segconf.asan, pin sha256 48c5355bdacb): file group _s21, segment S13
   (0x857cc .. 0x858f0) of the test harness's entry function LLVMFuzzerTestOneInput (0x84d34).

   proves function LLVMFuzzerTestOneInput (reuse search: origin/main@6e24fa4d602c origin/ossv/recipes@3abc3740de97
   origin/ossv/candidates@ee89628c9971 origin/release/pau-projects-recipes@b6a0088adcb4 / the stream's proof index
   LLVMFuzzerTestOneInput + four-ref git grep; output pasted verbatim in
   the walk's shared brief; checker (fresh, read-only): CONFIRM; none: written new)

   The statement proved: lt_seg_S13_stmt of LLVMFuzzerTestOneInput_defs.v (Theorem lt_seg_S13), from the cuts
   K858f4 0 and K85bd0 at every FP state. The stages, one lemma each, from K857cc (calloc(cap + 1, 20) returned mt):
     A 0x857cc .. 0x857f0  s5 := SH(FR); the NULL tests of tab and mt (the engine refutes them from tab, mt >= 4096);
                           checked_memset(&tab[cap], 0x5a, 18)                                      (s21_stageA)
     B 0x857f4 .. 0x85830  120(s1) := 0, n in scope (its shadow byte SH(FR) + 32 := 4), n := 0, s6 := mt + 16;
                           the test flags & 1; flags & 1 = 0: a6 := m, to 0x85894;
                           flags & 1 <> 0: a6 := m, the test cap = 0; cap = 0: to 0x85894;
                           cap <> 0: checked_memcpy(tab, "enp1s0", 7)                               (s21_stageB)
     C 0x85834 .. 0x85864  tab[0].vid := 33 (check 27); checked_memcpy(mt, "enp1s0", 7)             (s21_stageC)
     D 0x85868 .. 0x85890  mt[0].vid := 33 (check 28); 120(s1) := 1; n := 1; a6 := m                (s21_stageD)
     T 0x85894 .. 0x858ac  m->n (check 29); 112(s1) := mt; a5 := the shadow base; the test m->n <= 0;
                           m->n = 0: 104(s1) := 0, to K85bd0;
                           m->n > 0: the slots 96 .. 136 and the registers of m_declared's turn 0, to K858f4 0
                                                                                                    (s21_tail)
   The point 0x85894 is this file's own cut (S21_T_stmt): the three arrivals (flags & 1 = 0; cap = 0; the two
   entries written) meet there. The three instrumented checks read shadow bytes that the blocks' shadow entries
   cover (tab + 16 and mt + 16 inside their blocks, m + 0x2000 inside m), so their error paths are never entered. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q YO0c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot PaSB
PaLibG SegGlob SegObj.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibF PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import LLVMFuzzerTestOneInput_c SegInstA
  LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s21k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ============================================ the symbolic states ============================================ *)
(* every seed: registers as their own atoms (atoms 0 .. 31), the extra atoms from 32; s1 (atom 9) the base of the
   real frame, a 32-aligned address above 2 ^ 46; the shadow band (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1) *)
Definition S21_S1F : afact := mkAF 70368744177664 140737488355328 5.
Definition S21_span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition S21_PB : Z := 0xac0.  (* 0x857f4, memset returned *)
Definition S21_PC : Z := 0xb00.  (* 0x85834, memcpy(tab) returned *)
Definition S21_PD : Z := 0xb34.  (* 0x85868, memcpy(mt) returned *)
Definition S21_PT : Z := 0xb60.  (* 0x85894, this file's cut *)
(* the shadow byte's address of x, as the code forms it: (x >> 3) + the base *)
Definition s21_shw (x bx : sv) : sv := SAlu ALU_ADD (SAlu ALU_SRL x (SLit 3)) bx.

(* T, at 0x85894: atom 32 the shadow base, atom 33 m->n, atom 34 the entries seeded (120(s1)); s10 the shadow
   address of m + 0x2000; the s1 slots 120, 176 (the base) and 184 (m + 0x2000) and the write window 96 .. 143;
   m's 4-byte count *)
Definition rT1 : YP09.region := YP09.mkRegion (Some 9%nat) 0 192 96 144
  [YP09.mkChunk 120 (CVal 8 (SOff 34 0)); YP09.mkChunk 176 (CVal 8 (SOff 32 0)); YP09.mkChunk 184 (CVal 8 (SOff 16 8192))].
Definition rT2 : YP09.region := YP09.mkRegion (Some 16%nat) 8192 8196 0 0 [YP09.mkChunk 8192 (CVal 4 (SOff 33 0))].
Definition fT : facts :=
  mkFacts [(9%nat, S21_S1F); (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (16%nat, HPTR 4); (33%nat, mkAF 0 32 0)] [] [].
Definition ssT0 : sstate := mkSS S21_PT sr_atoms [rT1; rT2] None fT.
Definition SHT : list shent := [mkSHE 16 8192 8200].

(* D, at 0x85868 (memcpy(mt) returned): atom 32 = n's address (48(s1)), atom 33 = m (168(s1)); the s1 window
   120 .. 127, mt[0].vid (s6 = mt + 16), n; the shadow base in s3; shadow entries for mt + 16 .. 23 and n *)
Definition rD1 : YP09.region := YP09.mkRegion (Some 9%nat) 0 192 120 128
  [YP09.mkChunk 48 (CVal 8 (SOff 32 0)); YP09.mkChunk 168 (CVal 8 (SOff 33 0))].
Definition rD2 : YP09.region := YP09.mkRegion (Some 22%nat) 0 8 0 4 [].
Definition rD3 : YP09.region := YP09.mkRegion (Some 32%nat) 0 4 0 4 [].
Definition fD : facts :=
  mkFacts [(9%nat, S21_S1F); (19%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (22%nat, mkAF 4112 140737479966736 4);
           (32%nat, mkAF 4352 140737479966720 5)] [] [].
Definition ssD0 : sstate := mkSS S21_PD sr_atoms [rD1; rD2; rD3] None fD.
Definition SHD : list shent := [mkSHE 22 0 8; mkSHE 32 0 4].

(* C, at 0x85834 (memcpy(tab) returned): atom 32 the shadow base (176(s1)); tab[0].vid's 2 bytes; the shadow entry
   tab + 16 .. 23 *)
Definition rC1 : YP09.region := YP09.mkRegion (Some 9%nat) 0 192 0 0 [YP09.mkChunk 176 (CVal 8 (SOff 32 0))].
Definition rC2 : YP09.region := YP09.mkRegion (Some 24%nat) 0 24 16 18 [].
Definition fC : facts := mkFacts [(32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, HPTR 4)] [] [].
Definition ssC0 : sstate := mkSS S21_PC sr_atoms [rC1; rC2] None fC.
Definition SHC : list shent := [mkSHE 24 16 24].

(* B, at 0x857f4 (memset returned): atom 32 = flags (16(s1)), atom 33 = n's address (48(s1)), atom 34 = m (168(s1));
   the s1 window 120 .. 127, n's shadow byte SH(FR) + 32 (s5 + 32), n *)
Definition rB1 : YP09.region := YP09.mkRegion (Some 9%nat) 0 192 120 128
  [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 168 (CVal 8 (SOff 34 0))].
Definition rB2 : YP09.region := YP09.mkRegion (Some 21%nat) 0 36 32 33 [].
Definition rB3 : YP09.region := YP09.mkRegion (Some 33%nat) 0 4 0 4 [].
Definition ssB0 : sstate := mkSS S21_PB sr_atoms [rB1; rB2; rB3] None (mkFacts [] [] []).

(* A, at 0x857cc (calloc returned mt): atom 32 = SH(FR) (144(s1)); tab and mt heap pointers *)
Definition rA : YP09.region := YP09.mkRegion (Some 9%nat) 0 192 0 0 [YP09.mkChunk 144 (CVal 8 (SOff 32 0))].
Definition fA : facts := mkFacts [(9%nat, S21_S1F); (24%nat, HPTR 4); (10%nat, HPTR 4)] [] [].
Definition ssA0 : sstate := mkSS LO_K857cc sr_atoms [rA] None fA.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition ET (regs : bvmap 5 word) (nl l0 : Z) : env := Eimg (Ereg regs [w64 SHADOW_OFF; w64 nl; w64 l0]).
Definition ED (regs : bvmap 5 word) (frn m : Z) : env := Eimg (Ereg regs [w64 frn; w64 m]).
Definition EC (regs : bvmap 5 word) : env := Eimg (Ereg regs [w64 SHADOW_OFF]).
Definition EB (regs : bvmap 5 word) (fl frn m : Z) : env := Eimg (Ereg regs [w64 fl; w64 frn; w64 m]).
Definition EA (regs : bvmap 5 word) (sh : Z) : env := Eimg (Ereg regs [w64 sh]).
Lemma s21_pres : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.
Lemma s21_o16 : forall a b, a mod 32 = 0 -> b mod 16 = 0 -> (a - b) mod 16 = 0.
Proof.
intros a b Ha Hb. pose proof (Z_div_mod_eq_full a 32). pose proof (Z_div_mod_eq_full b 16).
replace (a - b) with ((2 * (a / 32) - b / 16) * 16) by lia. apply Z_mod_mult.
Qed.
Lemma s21_lit_enp : seg_litA_fz LLVMFuzzerTestOneInput_c.LIT_ENP = 0x21060.
Proof. vm_compute. reflexivity. Qed.
Lemma s21_lit_enp_in : In LLVMFuzzerTestOneInput_c.LIT_ENP LLVMFuzzerTestOneInput_c.LTOI_FZ_LITS.
Proof. unfold LLVMFuzzerTestOneInput_c.LTOI_FZ_LITS, LLVMFuzzerTestOneInput_c.LTOI_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.

(* ============================================ environments and chunks ============================================ *)
Lemma s21_EE : forall regs extra n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (Eimg (Ereg regs extra)) n = getr regs r.
Proof. intros regs extra n r Hn Hr. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hr. Qed.
Lemma s21_EX : forall regs extra j n, n = (32 + j)%nat -> (n < A_TEXT)%nat ->
  ew (Eimg (Ereg regs extra)) n = nth j extra (Z_to_bv 64 0).
Proof. intros regs extra j n -> Hn. rewrite Eimg_low by exact Hn. apply ew_Ereg_extra. Qed.
Lemma s21_Uw : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z.
Proof. intros z Hz. unfold w64. apply unsigned_lit_small. exact Hz. Qed.
Lemma s21_val_of_sa : forall H (mem : word -> option byte) a n v,
  sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv. f_equal.
first [ rewrite <- Hv
| change (YG0f.le_byte v n k) with (YO0f.le_byte v n k); rewrite <- Hv
| change (YO0f.le_byte v n k) with (YG0f.le_byte v n k); rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma s21_sa_of_val : forall H (mem : word -> option byte) a n v,
  val_mem SEGS (mrestrict H mem) a n v -> sa_val (aview SEGS H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
try unfold YG0f.le_byte; try unfold YO0f.le_byte. apply Zmod_mod.
Qed.
(* a chunk of a seed from a word, or from n bytes, of the reader *)
Lemma s21_chunk8 : forall E H (mem : word -> option byte) base off e v,
  sv_denot E e = Z_to_bv 64 v -> rdword (aview SEGS H mem) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal 8 e)).
Proof.
intros E H mem base off e v He Hw. apply (chunk_ok_val SEGS E _ base off 8 e v He).
- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact (s21_rdword_rng H mem _ _ Hw).
- lia.
- exact (val_mem_of_rdword SEGS H mem _ _ Hw).
Qed.
Lemma s21_chunkv : forall E H (mem : word -> option byte) base off (n : N) e v,
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  sa_val (aview SEGS H mem) (base + off) (N.to_nat n) v ->
  YP09.chunk_ok SEGS E (mrestrict H mem) base (YP09.mkChunk off (CVal n e)).
Proof.
intros E H mem base off n e v He Hv Hn Hs. apply (chunk_ok_val SEGS E _ base off n e v He Hv Hn).
exact (s21_val_of_sa H mem _ _ _ Hs).
Qed.
(* a chunk of a state the engine reached, read back *)
Lemma s21_chunk_rd : forall E ss (ms : machine_state) H r off (n : N) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> In r (ss_mem ss) -> In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem SEGS (mrestrict H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E ss ms H r off n e v HS Hr Hc He Hv Hn.
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [abs_ss setpc ss_mem restrict ms_mem] in HM.
pose proof (mem_ok_region SEGS _ _ _ _ HM Hr) as HR.
pose proof (region_ok_chunk SEGS _ _ _ _ HR Hc) as HC.
exact (val_of_chunk_ok SEGS _ _ _ off n e v HC He Hv Hn).
Qed.
Ltac s21_in := cbn [ss_mem YP09.r_chunks]; repeat (first [left; reflexivity | right]).
(* the same, the region named by its place in the state's list *)
Lemma s21_chunk_rdc : forall E ss pc (ms : machine_state) H i r off (n : N) e v,
  st_ok SEGS E (setpc ss pc) (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  sa_val (aview SEGS H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E ss pc ms H i r off n e v HS Hi Hc He Hv Hn. apply s21_sa_of_val.
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [setpc ss_mem restrict ms_mem] in HM.
pose proof (mem_ok_region SEGS _ _ _ _ HM (nth_error_In _ _ Hi)) as HR.
pose proof (region_ok_chunk SEGS _ _ _ _ HR Hc) as HC.
exact (val_of_chunk_ok SEGS _ _ _ off n e v HC He Hv Hn).
Qed.
Lemma s21_chunk_rdo : forall E ss (ms : machine_state) H i r off (n : N) e v,
  st_ok SEGS E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  sa_val (aview SEGS H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E ss ms H i r off n e v HS Hi Hc He Hv Hn. apply s21_sa_of_val.
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as HM. cbn [ss_mem restrict ms_mem] in HM.
pose proof (mem_ok_region SEGS _ _ _ _ HM (nth_error_In _ _ Hi)) as HR.
pose proof (region_ok_chunk SEGS _ _ _ _ HR Hc) as HC.
exact (val_of_chunk_ok SEGS _ _ _ off n e v HC He Hv Hn).
Qed.
Lemma s21_chunk_rdi : forall E ss (ms : machine_state) H i r off (n : N) e v,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> nth_error (ss_mem ss) i = Some r ->
  In (YP09.mkChunk off (CVal n e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  sa_val (aview SEGS H (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat n) v.
Proof.
intros E ss ms H i r off n e v HS Hi Hc He Hv Hn. apply s21_sa_of_val.
exact (s21_chunk_rd E ss ms H r off n e v HS (nth_error_In _ _ Hi) Hc He Hv Hn).
Qed.
(* a word of the s1 region of a state the engine reached *)
Lemma s21_slot_rd : forall E ss (ms : machine_state) H r off e v s1,
  st_ok_pi SEGS VAL E ss (restrict H ms) -> In r (ss_mem ss) -> YP09.r_base r = Some 9%nat ->
  bv_unsigned (ew E 9) = s1 -> In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) ->
  sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H (ms_mem ms)) (s1 + off) = Some v.
Proof.
intros E ss ms H r off e v s1 HS Hr Hb U9 Hc He Hv.
pose proof (s21_chunk_rd E ss ms H r off 8 e v HS Hr Hc He ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact Hv)
  ltac:(lia)) as HV.
rewrite Hb in HV. cbn [base_val] in HV. rewrite U9 in HV. exact (rdword_of_val_mem SEGS H _ _ _ HV Hv).
Qed.
(* a register of a state the engine reached, as the symbolic value *)
Ltac s21_reg HS r P :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as P;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in P
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as P;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in P
  end.
(* the imported lia fails on some linear goals; fall back to the plain one *)
Ltac zl := first [ lia | Zify.zify; xlia zchecker ].

(* the n bytes of a u32 field of an encoding *)
Lemma s21_nth_firstn : forall (l : list byte) L i d, (i < L)%nat -> nth i (firstn L l) d = nth i l d.
Proof.
induction l as [|b l IH]; intros [|L] [|i] d Hi; cbn [firstn nth]; try reflexivity; try lia. apply IH. lia.
Qed.
Lemma s21_nth_skipn : forall (l : list byte) n i d, nth i (skipn n l) d = nth (n + i) l d.
Proof. intros l n. revert l. induction n as [|n IH]; intros [|b l] i d; cbn; try reflexivity; [destruct i; reflexivity | apply IH]. Qed.
Lemma s21_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) ZB0) = le_byte v 4 k.
Proof.
intros v k Hv Hk. unfold Mem.le4. rewrite unsigned_lit_small by lia. unfold le_byte.
change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by lia.
destruct k as [|[|[|[|k]]]]; [| | | | lia]; cbn [Z_to_le_bytes nth]; rewrite Z_to_bv_unsigned; unfold bv_wrap;
change (bv_modulus 8) with 256; rewrite ?Z.shiftr_shiftr by lia; reflexivity.
Qed.
Lemma s21_u32_at : forall (rd : reader) a bs off v, sa_bytes rd a bs -> 0 <= off -> off + 4 <= Z.of_nat (length bs) ->
  seg_spec.u32_enc v (seg_spec.fldz off 4 bs) -> sa_val rd (a + off) 4 v.
Proof.
intros rd a bs off v Hb Ho Hl [Hv Hf] k Hk. unfold seg_spec.fldz, seg_spec.fld in Hf.
assert (Hn : nth k (firstn (Z.to_nat 4) (skipn (Z.to_nat off) bs)) ZB0 = nth (Z.to_nat off + k) bs ZB0).
{ rewrite s21_nth_firstn by (cbn; lia). apply s21_nth_skipn. }
rewrite Hf in Hn.
replace (a + off + Z.of_nat k) with (a + Z.of_nat (Z.to_nat off + k)) by lia.
rewrite (Hb (Z.to_nat off + k)%nat) by lia. rewrite <- Hn. f_equal. apply s21_le4_byte; [exact Hv | exact Hk].
Qed.
(* m->n from the model's encoding *)
Lemma s21_mn : forall (rd : reader) m mc, sa_mconf rd m mc ->
  sa_val rd (m + 8192) 4 (Z.of_nat (length (SegModel.mc_seg mc))) /\ (length (SegModel.mc_seg mc) <= 32)%nat.
Proof.
intros rd m mc (bs & Hbs & Hlen & Hle & _ & Hn & _). split; [|exact Hle].
exact (s21_u32_at rd m bs 8192 _ Hbs ltac:(lia) ltac:(unfold seg_spec.SEG_M_SIZE in Hlen; lia) Hn).
Qed.

(* ============================================ the walk ============================================ *)
Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the memory-checking runtime's memset and memcpy entries, at every FP state *)
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (SIG SS___asan_memset).
Hypothesis AMEMCPY : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OCpy (SIG SS___asan_memcpy).
(* the listing's object atoms are the image's addresses ("enp1s0" is A_OBJ 9) *)
Hypothesis VOBJS : seg_val_objs.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

(* ---------------------------------- the seed of the tail, at 0x85894 ---------------------------------- *)
Lemma s21_seedT : forall (W : world SEGS) regs mem s1 m nl l0,
  getr regs 9 = w64 s1 -> 70368744177664 <= s1 -> s1 + 192 <= 140737488355328 -> s1 mod 32 = 0 ->
  (forall o, 96 <= o < 144 -> apresent (w_H W) mem (s1 + o)) ->
  rdword (rdW W mem) (s1 + 120) = Some l0 ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF -> rdword (rdW W mem) (s1 + 184) = Some (m + 8192) ->
  getr regs 16 = w64 m -> 4096 <= m -> m mod 16 = 0 -> m + 9236 <= 140737479966720 -> in_app m 9236 ->
  m + 9236 <= s1 -> sa_val (rdW W mem) (m + 8192) 4 nl -> 0 <= nl <= 32 ->
  range_addressable (rdW W mem) SHADOW_OFF (m + 8192) 8 ->
  st_ok_pi SEGS VAL (ET regs nl l0) ssT0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S21_PT)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 32 0) SHT (ET regs nl l0) (mrestrict (w_H W) mem).
Proof.
intros W regs mem s1 m nl l0 R9 Hs1a Hs1b Hs132 Hpr H120 H176 H184 R16 Hm1 Hm16 Hm2 Happ Hms1 Hnl Hnlr HRA.
set (E := ET regs nl l0).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (subst E; unfold ET; rewrite (s21_EE regs _ 9 9%bv) by (lia || reflexivity); rewrite R9; apply s21_Uw; lia).
assert (U16 : bv_unsigned (ew E 16) = m)
  by (subst E; unfold ET; rewrite (s21_EE regs _ 16 16%bv) by (lia || reflexivity); rewrite R16; apply s21_Uw; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF)
  by (subst E; unfold ET; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew E 33) = nl)
  by (subst E; unfold ET; rewrite (s21_EX regs _ 1 33) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; lia).
assert (U34 : bv_unsigned (ew E 34) = l0)
  by (subst E; unfold ET; rewrite (s21_EX regs _ 2 34) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; exact (s21_rdword_rng _ _ _ _ H120)).
split.
- unfold ssT0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold ET. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rT1, rT2. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpr. lia. }
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (s21_chunk8 E (w_H W) mem s1 120 (SOff 34 0) l0); [|exact H120].
         cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
      -- apply (s21_chunk8 E (w_H W) mem s1 176 (SOff 32 0) SHADOW_OFF); [|exact H176].
         cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
      -- apply (s21_chunk8 E (w_H W) mem s1 184 (SOff 16 8192) (m + 8192)); [|exact H184].
         cbn [sv_denot]. rewrite U16. reflexivity.
    * rewrite U16. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (s21_chunkv E (w_H W) mem m 8192 4 (SOff 33 0) nl).
      -- cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
      -- change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
      -- lia.
      -- exact Hnl.
  + apply pairwise_disjoint_of_extents. unfold rT1, rT2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U16.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; zl.
  + split; [|split; [exact I | exact I]].
    cbn [fT f_atoms atoms_ok]. unfold afact_ok, S21_S1F, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U9, U32, U16, U33. unfold SHADOW_OFF.
    change (2 ^ 0) with 1. change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia].
- unfold sh_ok, SHT. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E (SOff 32 0) 16 (m + 8192) 8 m 8192 8200).
  + exact HRA.
  + unfold U. cbn [sv_denot]. rewrite U32, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + unfold U. cbn [sv_denot]. rewrite U16, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    unfold SHADOW_OFF. lia.
Qed.


(* ---------------------------------- what the tail keeps ---------------------------------- *)
(* the tables, n and the guard, as lt_tabs states them, over a reader that agrees on their bytes *)
Lemma s21_tabs_keep : forall cx (rd rd' : reader) tab mt t,
  lt_tabs cx rd tab mt t ->
  (forall a, tab <= a < tab + x_tabn cx -> rd' a = rd a) ->
  (forall a, mt <= a < mt + x_mtn cx -> rd' a = rd a) ->
  (forall a, x_fr cx + FO_N <= a < x_fr cx + FO_N + 4 -> rd' a = rd a) ->
  lt_tabs cx rd' tab mt t.
Proof.
intros cx rd rd' tab mt t (H1 & (bs & Hb & Hre) & Hg & Hn & (bs2 & Hb2 & Hme) & H2) Kt Km Kn.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
pose proof (proj1 Hre) as L1. pose proof (proj1 Hme) as L2.
split; [exact H1|]. split.
{ exists bs. split; [|exact Hre]. apply (s21_bytes_keep _ _ _ _ Hb). intros i Hi. apply Kt. zl. }
split.
{ apply (s21_bytes_keep _ _ _ _ Hg). intros i Hi. apply Kt. unfold seg_spec.GUARD_BYTES in Hi.
  rewrite repeat_length in Hi. unfold seg_spec.RVLAN_SIZE. zl. }
split.
{ apply (s21_val_keep _ _ _ _ _ Hn). intros i Hi. apply Kn. cbn in Hi. zl. }
split; [|exact H2].
exists bs2. split; [|exact Hme]. apply (s21_bytes_keep _ _ _ _ Hb2). intros i Hi. apply Km. zl.
Qed.
(* the offsets of the slots m_declared's head keeps from the file loop's list *)
Lemma s21_LV_off : forall cx c m o v, In (o, v) (LT_LV cx c m ++ [(152, shadow_addr (m + seg_spec.MC_N))]) ->
  8 <= o <= 56 \/ 144 <= o <= 184.
Proof.
intros cx c m o v Hin. unfold LT_LV in *. cbn [app In] in *.
repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). destruct Hin.
Qed.
Lemma s21_bge0 : forall E v, 0 <= U E v < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E (SLit 0)) (sv_denot E v) = (U E v <=? 0).
Proof.
intros E v Hv. rewrite YO0c.branch_ge. change (bv_unsigned (sv_denot E v)) with (U E v).
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)). rewrite U_SLit. change (zcanon 0) with 0.
unfold YO0b.s64. replace (0 <? 2 ^ 63) with true by reflexivity.
replace (U E v <? 2 ^ 63) with true by (symmetry; apply Z.ltb_lt; lia).
destruct (Z.ltb_spec 0 (U E v)); destruct (Z.leb_spec (U E v) 0); cbn; lia.
Qed.

(* the tail's state after its runs: the s1 slots 96 .. 143 changed, the rest as at 0x85894 *)
Lemma s21_keepT : forall cx ly S W regs mem md k acc (c m tab mt : Z) regs2 mem2 md2,
  lt_base B MT cx ->
  lt_core B MT cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk B ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk B ly S (rdW W mem) mt (x_mtn cx) ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++
    [(120, Z.of_nat (length (x_tab0 cx))); (152, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (x_tab0 cx) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem2 md2 k ->
  getr regs2 2 = getr regs 2 -> getr regs2 3 = getr regs 3 -> getr regs2 4 = getr regs 4 ->
  getr regs2 8 = getr regs 8 -> getr regs2 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 96 <= a < x_s1 cx + 144) -> rdW W mem2 a = rdW W mem a) ->
  lt_core B MT cx ly S W regs2 mem2 md2 k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem2) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem2) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem2) tab (x_tabn cx) /\ lt_hblk B ly S (rdW W mem2) mt (x_mtn cx) /\
  lt_slots cx (rdW W mem2) (LT_LV cx c m ++ [(152, shadow_addr (m + seg_spec.MC_N))]) /\
  lt_cm (rdW W mem2) c m (x_run cx) /\ lt_tabs cx (rdW W mem2) tab mt (x_tab0 cx).
Proof.
intros cx ly S W regs mem md k acc c m tab mt regs2 mem2 md2 HB HC Hc Hm Ht Hmt HSL HCM HTB HJ2 E2 E3 E4 E8 E9 HK.
pose proof HC as (HF & _).
destruct (s21_nums cx ly S W regs mem md k LFO_N HB HF) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSH).
pose proof (proj1 HJ2) as HAR2.
pose proof Hc as (HcIn & _). pose proof Hm as (HmIn & _). pose proof Ht as (HtIn & _). pose proof Hmt as (HmtIn & _).
pose proof (proj1 HF) as HJ. pose proof (proj1 HJ) as HAR.
destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HcIn) as (_ & Cc0 & Cc & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HmIn) as (_ & Cm0 & Cm & _).
destruct (al_blocks _ _ LAWS ly S W mem md tab _ HAR HtIn) as (_ & Ct0 & Ct & _).
destruct (al_blocks _ _ LAWS ly S W mem md mt _ HAR HmtIn) as (_ & Cmt0 & Cmt & _).
pose proof (s21_xcap_rng cx) as Hcap.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt].
pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Rm].
change (req_size seg_spec.SEG_C_SIZE) with 16616 in Cc. change (req_size seg_spec.SEG_M_SIZE) with 9236 in Cm.
assert (Hsh : SHADOW_OFF <= x_sh cx < 0x10007fff8000 - 64)
  by (rewrite N9; unfold SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)); lia).
assert (KL : forall a, 0 <= a < x_s1 cx -> rdW W mem2 a = rdW W mem a) by (intros a Ha; apply HK; lia).
split.
{ apply (s21_core_keep cx ly S W regs mem md k acc 4 LFO_N _ regs2 mem2 md2 LFO_N tab mt HB HC HtIn HmtIn HJ2
    E2 E3 E4 E8 E9).
  - intros a Ha Hx. apply HK; [exact Ha|]. intros Hw. apply Hx. unfold s21_X. right; right; right; right; right. exact Hw.
  - apply (s21_zs_keep _ _ _ _ HSH). intros i Hi. rewrite lt_fsh_len in Hi. apply KL. unfold SHADOW_OFF in Hsh. lia. }
split; [exact (s21_hblk_of_AR ly S W mem2 md2 c _ HAR2 HcIn ltac:(unfold seg_spec.SEG_C_SIZE; lia))|].
split; [exact (s21_hblk_of_AR ly S W mem2 md2 m _ HAR2 HmIn ltac:(unfold seg_spec.SEG_M_SIZE; lia))|].
split; [exact (s21_hblk_of_AR ly S W mem2 md2 tab _ HAR2 HtIn ltac:(lia))|].
split; [exact (s21_hblk_of_AR ly S W mem2 md2 mt _ HAR2 HmtIn ltac:(lia))|].
split.
{ intros o v Hin. pose proof (s21_LV_off cx c m o v Hin) as Ho.
  assert (Hin3 : In (o, v) (LT_LV cx c m ++ [(120, Z.of_nat (length (x_tab0 cx))); (152, shadow_addr (m + seg_spec.MC_N))])).
  { apply in_app_or in Hin as [H|H]; apply in_or_app; [left; exact H | right; right; exact H]. }
  apply (s21_rdword_keep _ _ _ _ (HSL o v Hin3)). intros j Hj. apply HK; lia. }
split.
{ apply (s21_cm_keep _ _ c m _ HCM); intros i Hi; apply KL; unfold seg_spec.SEG_C_SIZE, seg_spec.SEG_M_SIZE in *; lia. }
apply (s21_tabs_keep cx _ _ tab mt _ HTB); intros a Ha; apply KL; unfold FO_N in *; lia.
Qed.

(* ---------------------------------- the tail: 0x85894 to K858f4 0 or K85bd0 ---------------------------------- *)
Definition S21_T_stmt : Prop :=
  forall cx ly S W regs mem md k acc (c m tab mt : Z),
  lt_base B MT cx -> sa_frm0 ->
  lt_core B MT cx ly S W regs mem md k acc 4 LFO_N
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] ->
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE -> lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE ->
  lt_hblk B ly S (rdW W mem) tab (x_tabn cx) -> lt_hblk B ly S (rdW W mem) mt (x_mtn cx) ->
  getr regs 16 = w64 m -> getr regs 20 = w64 mt -> getr regs 21 = w64 (x_sh cx) -> getr regs 22 = w64 (mt + 16) ->
  getr regs 24 = w64 tab -> getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  lt_slots cx (rdW W mem) (LT_LV cx c m ++
    [(120, Z.of_nat (length (x_tab0 cx))); (152, shadow_addr (m + seg_spec.MC_N))]) ->
  lt_cm (rdW W mem) c m (x_run cx) ->
  lt_tabs cx (rdW W mem) tab mt (x_tab0 cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + S21_PT) regs mem md) (lt_post B MT cx).

Lemma s21_tail : LTA_K858f4 B MT 0 -> LTA_K85bd0 B MT -> S21_T_stmt.
Proof.
intros HK0 HBD. unfold S21_T_stmt.
intros cx ly S W regs mem md k acc c m tab mt HB HFRM HC Hbc Hbm Hbt Hbmt R16 R20 R21 R22 R24 R26 HSL HCM HTB.
pose proof HC as (HF & HI & HBL & HBUD).
destruct (s21_nums cx ly S W regs mem md k LFO_N HB HF) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HD0 & HD8 & HD16 & HFL & H176 & HSH).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
pose proof Hbm as (HmIn & Hm4096 & Hm16 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HmIn) as (_ & _ & Hmceil & Hmapp & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hmceil, Hmapp.
assert (Hsl : forall o v, In (o, v) (LT_LV cx c m) -> rdword (rdW W mem) (x_s1 cx + o) = Some v)
  by (intros o v Hin; apply HSL; apply in_or_app; left; exact Hin).
pose proof (proj2 HCM) as HMC.
destruct (s21_mn (rdW W mem) m _ HMC) as [Hnl Hnl32].
set (nl := Z.of_nat (length (SegModel.mc_seg (seg_spec.seg_mc (x_run cx))))) in *.
assert (Hnlr : 0 <= nl <= 32) by (subst nl; lia).
pose proof (range_addressable_of_block SEGS B LAWS ly S W mem md m _ (m + 8192) 8 HAR HmIn ltac:(lia) ltac:(change (req_size seg_spec.SEG_M_SIZE) with 9236; lia)) as HRA.
assert (Hstk : forall o, 96 <= o < 144 -> apresent (w_H W) mem (x_s1 cx + o)).
{ intros o Ho. apply Hpres. unfold STK_LLVMFuzzerTestOneInput. lia. }
assert (H184 : rdword (rdW W mem) (x_s1 cx + 184) = Some (m + 8192))
  by (apply Hsl; unfold LT_LV; cbn [In]; tauto).
pose proof (s21_xcap_rng cx) as Hcap.
assert (Rmt : 0 <= mt < 2 ^ 63)
  by (pose proof Hbmt as (_ & _ & _ & Hq0 & Hq1 & _); assert (x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity; lia).
assert (Rtab : 0 <= tab < 2 ^ 63)
  by (pose proof Hbt as (_ & _ & _ & Hq0 & Hq1 & _); assert (x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity; lia).
set (l0 := Z.of_nat (length (x_tab0 cx))) in *.
assert (Hl0 : 0 <= l0 < 40) by (pose proof HTB as (Hq & _); subst l0; lia).
assert (H120 : rdword (rdW W mem) (x_s1 cx + 120) = Some l0)
  by (apply HSL; apply in_or_app; right; left; reflexivity).
destruct (s21_seedT W regs mem (x_s1 cx) m nl l0 R9 ltac:(lia) ltac:(lia) N3 Hstk H120 H176 H184
  R16 Hm4096 Hm16 ltac:(lia) Hmapp ltac:(lia) Hnl Hnlr HRA) as [HS0 SHOK].
(* the environment: the registers of 0x85894 and the three extra atoms *)
assert (EV : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (ET regs nl l0) n = getr regs r)
  by (intros n r Hn Hr; unfold ET; apply s21_EE; assumption).
assert (E32 : ew (ET regs nl l0) 32 = w64 SHADOW_OFF)
  by (unfold ET; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); reflexivity).
assert (E33 : ew (ET regs nl l0) 33 = w64 nl)
  by (unfold ET; rewrite (s21_EX regs _ 1 33) by (reflexivity || (unfold A_TEXT; lia)); reflexivity).
assert (E34 : ew (ET regs nl l0) 34 = w64 l0)
  by (unfold ET; rewrite (s21_EX regs _ 2 34) by (reflexivity || (unfold A_TEXT; lia)); reflexivity).
assert (HEI : img_env VAL A_LIM (ET regs nl l0)) by (unfold ET; apply Eimg_env).
assert (U9 : bv_unsigned (ew (ET regs nl l0) 9) = x_s1 cx)
  by (rewrite (EV 9%nat 9%bv) by (lia || reflexivity); rewrite R9; apply s21_Uw; lia).
assert (U16 : bv_unsigned (ew (ET regs nl l0) 16) = m)
  by (rewrite (EV 16%nat 16%bv) by (lia || reflexivity); rewrite R16; apply s21_Uw; lia).
assert (U32 : bv_unsigned (ew (ET regs nl l0) 32) = SHADOW_OFF) by (rewrite E32; apply s21_Uw; unfold SHADOW_OFF; lia).
assert (U33 : bv_unsigned (ew (ET regs nl l0) 33) = nl) by (rewrite E33; apply s21_Uw; lia).
assert (U34 : bv_unsigned (ew (ET regs nl l0) 34) = l0)
  by (rewrite E34; apply s21_Uw; lia).
assert (U9s : bv_unsigned (ew (ET regs nl l0) 9) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (rewrite U9; lia).
(* s10 as the code reads it at 0x85894: the shadow address of m + 0x2000 *)
assert (Hden : sv_denot (ET regs nl l0) (s21_shw (SOff 16 8192) (SOff 32 0)) = getr regs 26).
{ rewrite R26. change (w64 (shadow_addr (m + seg_spec.MC_N))) with (sv_denot (ET regs nl l0) (SLit (shadow_addr (m + seg_spec.MC_N)))).
  apply U_inj. unfold s21_shw. rewrite !U_SAlu, !U_SOff, !U_SLit. cbn [zalu_raw]. rewrite U16, U32.
  change (Z.land (zcanon 3) 63) with 3.
  rewrite (zcanon_small (m + 8192)) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  rewrite (zcanon_small ((m + 8192) / 8)) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite Z.add_0_r, (zcanon_small SHADOW_OFF) by (unfold SHADOW_OFF; lia).
  unfold shadow_addr, seg_spec.MC_N. f_equal. lia. }
pose proof (ast_ok_pi_set_reg_fp _ _ _ 26%bv _ HS0 eq_refl Hden) as HS. clear HS0.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
set (E := ET regs nl l0) in *. clearbody E.
unfold cfg_at. change (w64 (BASE + S21_PT)) with (Z_to_bv 64 (BASE + S21_PT)).
(* 0x85894 .. 0x858ac: m->n's shadow (check 29, covered), 112(s1) := mt, a0 := m->n, a5 := the base; blez a0 *)
paj_run_tok RUN HS HJ SHOK S21_span.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  eapply awr_ok_cons_stack_off; [reflexivity | exact U9s | cbn; unfold STK_LLVMFuzzerTestOneInput; lia | cbn; lia |].
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 96 <= a < x_s1 cx + 144) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => x_s1 cx + 96 <= a < x_s1 cx + 144) HFr); [|exact Ha | exact Hna].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr; [rewrite U9 in Hrr|]; lia. }
clear HF HFr HG.
rename ms into ms1.
psrr_branch_tok RUN BR HS SHOK S21_span.
- (* m->n = 0: 0x85bcc 104(s1) := 0, on to K85bd0 *)
  assert (Hn0 : nl = 0).
  { rewrite s21_bge0 in Hc by (rewrite (U_atom E 33 nl) by (first [exact E33 | lia]); lia).
    rewrite (U_atom E 33 nl) in Hc by (first [exact E33 | lia]). apply Z.leb_le in Hc. lia. }
  assert (Hnil : SegModel.mc_seg (x_mcF cx) = []).
  { apply length_zero_iff_nil. unfold x_mcF. subst nl. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK S21_span LO_K85bd0.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
    eapply awr_ok_cons_stack_off; [reflexivity | exact U9s | cbn; unfold STK_LLVMFuzzerTestOneInput; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 96 <= a < x_s1 cx + 144) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha Hna. rewrite <- (K1 a Ha Hna).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => x_s1 cx + 96 <= a < x_s1 cx + 144) HFr); [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr; [rewrite U9 in Hrr|]; lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  prreg HS (16%bv : bv 5) P16. prreg HS (21%bv : bv 5) P21. prreg HS (24%bv : bv 5) P24.
  rewrite (EV 2%nat 2%bv) in P2 by (lia || reflexivity). rewrite (EV 3%nat 3%bv) in P3 by (lia || reflexivity).
  rewrite (EV 4%nat 4%bv) in P4 by (lia || reflexivity). rewrite (EV 8%nat 8%bv) in P8 by (lia || reflexivity).
  rewrite (EV 9%nat 9%bv) in P9 by (lia || reflexivity). rewrite (EV 16%nat 16%bv) in P16 by (lia || reflexivity).
  rewrite (EV 21%nat 21%bv) in P21 by (lia || reflexivity). rewrite (EV 24%nat 24%bv) in P24 by (lia || reflexivity).
  destruct (s21_keepT cx ly S W regs mem md k acc c m tab mt (ms_regs ms) (ms_mem ms) md2 HB HC Hbc Hbm Hbt Hbmt HSL HCM HTB
    HJ P2 P3 P4 P8 P9 K2) as (HC2 & Hc2 & Hm2 & Ht2 & Hmt2 & HSL2 & HCM2 & HTB2).
  (* 104(s1) = 0, the chunk the run wrote; 112(s1) = mt, 120(s1) = the entries seeded *)
  assert (W104 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 104) = Some 0).
  { apply rdword_of_val_mem; [|lia]. rewrite <- U9.
    exact (s21_chunk_rd E _ ms (w_H W) _ 104 8 (SLit 0) 0 HS ltac:(s21_in) ltac:(s21_in) eq_refl ltac:(cbn; lia) ltac:(lia)). }
  assert (W112 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 112) = Some mt).
  { apply rdword_of_val_mem; [|lia]. rewrite <- U9.
    apply (s21_chunk_rd E _ ms (w_H W) _ 112 8 (SOff 20 0) mt HS ltac:(s21_in) ltac:(s21_in)).
    - cbn [sv_denot]. rewrite (EV 20%nat 20%bv) by (lia || reflexivity). rewrite R20, Z.add_0_r. unfold w64.
      apply Z_to_bv_bv_unsigned.
    - change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
    - lia. }
  assert (W120 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 120) = Some l0).
  { eapply (s21_slot_rd E _ ms (w_H W) _ 120 (SOff 34 0) l0 (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | |].
    - cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
    - lia. }
  assert (HSLb : lt_slots cx (rdW W (ms_mem ms))
    [(8, x_fr cx); (24, x_fr cx); (32, x_cap cx); (48, x_fr cx + FO_N);
     (104, fst (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx)) mod 2 ^ 64); (112, mt);
     (120, Z.of_nat (length (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))))); (160, c); (168, m)]).
  { rewrite (s21_declared_nil cx Hnil). cbn [fst snd]. rewrite Z.mod_0_l by lia.
    intros o v Hin. cbn [In] in Hin.
    destruct Hin as [Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[]]]]]]]]]]; injection Eq as <- <-;
      first [ exact W104 | exact W112 | exact W120
            | apply HSL2; apply in_or_app; left; unfold LT_LV; cbn [In]; tauto ]. }
  assert (P16' : getr (ms_regs ms) 16 = w64 m) by (rewrite P16; exact R16).
  assert (P21' : getr (ms_regs ms) 21 = w64 (x_sh cx)) by (rewrite P21; exact R21).
  assert (P24' : getr (ms_regs ms) 24 = w64 tab) by (rewrite P24; exact R24).
  replace (x_tab0 cx) with (snd (SegModel.m_declared (x_mcF cx) (x_tab0 cx) (x_cap cx))) in HTB2
    by (rewrite (s21_declared_nil cx Hnil); reflexivity).
  exact (HBD fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m tab mt HB HFRM HC2 Hc2 Hm2 Ht2 Hmt2
    P16' P21' P24' HSLb HCM2 HTB2).
- (* m->n > 0: 0x858b0 .. 0x858f0, the registers and slots of m_declared's turn 0 *)
  assert (Hnp : 0 < nl).
  { rewrite s21_bge0 in Hc by (rewrite (U_atom E 33 nl) by (first [exact E33 | lia]); lia).
    rewrite (U_atom E 33 nl) in Hc by (first [exact E33 | lia]). apply Z.leb_gt in Hc. exact Hc. }
  paj_run_to_tok RUNTO HS HJ SHOK S21_span LO_K858f4.
  { lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
      let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
    eapply awr_ok_cons_stack_off; [reflexivity | exact U9s | cbn; unfold STK_LLVMFuzzerTestOneInput; lia | cbn; lia |].
    apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 96 <= a < x_s1 cx + 144) -> rdW W (ms_mem ms) a = rdW W mem a).
  { intros a Ha Hna. rewrite <- (K1 a Ha Hna).
    apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => x_s1 cx + 96 <= a < x_s1 cx + 144) HFr); [|exact Ha | exact Hna].
    intros b wlo whi a' Hin Hrr. vm_compute in Hin.
    destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr; [rewrite U9 in Hrr|]; lia. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9.
  rewrite (EV 2%nat 2%bv) in P2 by (lia || reflexivity). rewrite (EV 3%nat 3%bv) in P3 by (lia || reflexivity).
  rewrite (EV 4%nat 4%bv) in P4 by (lia || reflexivity). rewrite (EV 8%nat 8%bv) in P8 by (lia || reflexivity).
  rewrite (EV 9%nat 9%bv) in P9 by (lia || reflexivity).
  destruct (s21_keepT cx ly S W regs mem md k acc c m tab mt (ms_regs ms) (ms_mem ms) md2 HB HC Hbc Hbm Hbt Hbmt HSL HCM HTB
    HJ P2 P3 P4 P8 P9 K2) as (HC2 & Hc2 & Hm2 & Ht2 & Hmt2 & HSL2 & HCM2 & HTB2).
  s21_reg HS (15%bv : bv 5) P15. s21_reg HS (16%bv : bv 5) P16. s21_reg HS (20%bv : bv 5) P20.
  s21_reg HS (21%bv : bv 5) P21. s21_reg HS (22%bv : bv 5) P22. s21_reg HS (23%bv : bv 5) P23.
  s21_reg HS (24%bv : bv 5) P24. s21_reg HS (25%bv : bv 5) P25. s21_reg HS (26%bv : bv 5) P26.
  s21_reg HS (27%bv : bv 5) P27.
  assert (Em : sv_denot E (SOff 16 0) = w64 m).
  { cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. rewrite (EV 16%nat 16%bv) by (lia || reflexivity). exact R16. }
  assert (Ema : seg_spec.mseg_addr m 0 = m) by (unfold seg_spec.mseg_addr; lia).
  assert (P15' : getr (ms_regs ms) 15 = w64 SHADOW_OFF)
    by (rewrite P15; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; exact E32).
  assert (P16' : getr (ms_regs ms) 16 = w64 m) by (rewrite P16; exact Em).
  assert (P20' : getr (ms_regs ms) 20 = w64 4) by (rewrite P20; reflexivity).
  assert (P21' : getr (ms_regs ms) 21 = w64 (x_sh cx))
    by (rewrite P21; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 21%nat 21%bv) by (lia || reflexivity); exact R21).
  assert (P22' : getr (ms_regs ms) 22 = w64 (seg_spec.mseg_addr m 0)) by (rewrite P22, Ema; exact Em).
  assert (P23' : getr (ms_regs ms) 23 = w64 (-8)) by (rewrite P23; apply bv_eq; reflexivity).
  assert (P24' : getr (ms_regs ms) 24 = w64 tab)
    by (rewrite P24; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 24%nat 24%bv) by (lia || reflexivity); exact R24).
  assert (P25' : getr (ms_regs ms) 25 = w64 (Z.of_nat 0)) by (rewrite P25; reflexivity).
  assert (P26' : getr (ms_regs ms) 26 = w64 (- seg_spec.mseg_addr m 0)).
  { rewrite P26, Ema. change (w64 (- m)) with (sv_denot E (SLit (- m))). apply U_inj.
    rewrite U_SAlu, !U_SLit, U_SOff. cbn [zalu_raw].
    rewrite (EV 16%nat 16%bv) by (lia || reflexivity). rewrite R16, s21_Uw by lia.
    change (zcanon 0) with 0. rewrite (zcanon_small (m + 0)) by lia. f_equal. lia. }
  assert (P27' : getr (ms_regs ms) 27 = w64 (seg_spec.mseg_addr m 0)) by (rewrite P27, Ema; exact Em).
  assert (HSLn : lt_slots cx (rdW W (ms_mem ms)) (LT_LV cx c m ++
    [(96, mt + 16); (104, fst (x_decl cx 0)); (112, mt); (120, Z.of_nat (length (snd (x_decl cx 0))));
     (128, LT_VIDMAX); (136, LT_MASK); (152, shadow_addr (m + seg_spec.MC_N))])).
  { rewrite s21_decl0. cbn [fst snd].
    intros o v Hin. apply in_app_or in Hin as [Hin|Hin]; [apply HSL2; apply in_or_app; left; exact Hin|].
    cbn [In] in Hin. destruct Hin as [Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[Eq|[]]]]]]]]; injection Eq as <- <-.
    - eapply (s21_slot_rd E _ ms (w_H W) _ 96 (SOff 22 0) (mt + 16) (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | |].
      + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 22%nat 22%bv) by (lia || reflexivity). exact R22.
      + lia.
    - eapply (s21_slot_rd E _ ms (w_H W) _ 104 (SLit 0) 0 (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | reflexivity | lia].
    - eapply (s21_slot_rd E _ ms (w_H W) _ 112 (SOff 20 0) mt (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | |].
      + cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EV 20%nat 20%bv) by (lia || reflexivity). exact R20.
      + lia.
    - eapply (s21_slot_rd E _ ms (w_H W) _ 120 (SOff 34 0) l0 (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | |].
      + cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
      + lia.
    - eapply (s21_slot_rd E _ ms (w_H W) _ 128 (SLit 4094) LT_VIDMAX (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | reflexivity | unfold LT_VIDMAX; lia].
    - eapply (s21_slot_rd E _ ms (w_H W) _ 136 (SLit 1125899906850819) LT_MASK (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | reflexivity | unfold LT_MASK; lia].
    - apply HSL2. apply in_or_app. right. left. reflexivity. }
  assert (Hlen : (0 < length (SegModel.mc_seg (x_mcF cx)))%nat) by (unfold x_mcF; subst nl; lia).
  assert (Hd0 : 0 <= fst (x_decl cx 0)) by (rewrite s21_decl0; cbn; lia).
  replace (x_tab0 cx) with (snd (x_decl cx 0)) in HTB2 by (rewrite s21_decl0; reflexivity).
  exact (HK0 fx cx ly S W (ms_regs ms) (ms_mem ms) md2 k acc c m tab mt HB HFRM Hlen HC2 Hc2 Hm2 Ht2 Hmt2
    P15' P16' P20' P21' P22' P23' P24' P25' P26' P27' Hd0 HSLn HCM2 HTB2).
Qed.



(* ======================================== the head: 0x857cc .. 0x85894 ======================================== *)
(* the bytes the head writes: the guard tab[cap], the runtime's window below sp, 120(s1), n's shadow byte, n, the
   two seeded entries' parents and vids *)
Definition s21_Xh (cx : lcx) (tab mt : Z) (a : Z) : Prop :=
  (tab + 18 * x_cap cx <= a < tab + 18 * x_cap cx + 18) \/ (x_s1 cx - 4096 <= a < x_s1 cx) \/
  (x_s1 cx + 120 <= a < x_s1 cx + 128) \/ a = x_sh cx + 32 \/ (x_fr cx + 256 <= a < x_fr cx + 260) \/
  (tab <= a < tab + 7) \/ (tab + 16 <= a < tab + 18) \/ (mt <= a < mt + 7) \/ (mt + 16 <= a < mt + 20).
Lemma s21_Xh_X : forall cx tab mt a, s21_Xh cx tab mt a -> s21_X cx tab mt a.
Proof.
intros cx tab mt a H. pose proof (s21_xcap_rng cx) as Hc.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt]. pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Rm].
unfold s21_Xh, s21_X in *.
destruct H as [H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]].
- left. lia.
- right; right; right; right; left. exact H.
- right; right; right; right; right. lia.
- right; right; left. exact H.
- right; right; right; left. exact H.
- left. lia.
- left. lia.
- right; left. lia.
- right; left. lia.
Qed.

(* the three windows of the stretch 0x857f4 .. 0x85830: 120(s1), n's shadow byte, n *)
Definition s21_WB (cx : lcx) (a : Z) : Prop :=
  (x_s1 cx + 120 <= a < x_s1 cx + 128) \/ a = x_sh cx + 32 \/ (x_fr cx + FO_N <= a < x_fr cx + FO_N + 4).
Lemma s21_WB_Xh : forall cx tab mt a, s21_WB cx a -> s21_Xh cx tab mt a.
Proof.
intros cx tab mt a H. unfold s21_WB, s21_Xh, FO_N in *.
destruct H as [H|[H|H]]; [right; right; left; exact H | right; right; right; left; exact H | right; right; right; right; left; lia].
Qed.
Lemma s21_beq_and1 : forall E fl, bv_unsigned (ew E 32) = fl -> 0 <= fl < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 1))) (sv_denot E (SLit 0)) = (Z.land fl 1 =? 0).
Proof.
intros E fl H Hr. rewrite YO0c.branch_eq.
change (bv_unsigned (sv_denot E (SAlu ALU_AND (SOff 32 0) (SLit 1)))) with (U E (SAlu ALU_AND (SOff 32 0) (SLit 1))).
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)).
rewrite U_SAlu, U_SOff, !U_SLit, H, Z.add_0_r. cbn [zalu_raw].
rewrite (zcanon_small fl) by lia. change (zcanon 1) with 1. change (zcanon 0) with 0.
pose proof (Z.land_ones fl 1 ltac:(lia)) as L. change (Z.ones 1) with 1 in L. change (2 ^ 1) with 2 in L.
pose proof (Z.mod_pos_bound fl 2 ltac:(lia)) as L1.
rewrite (zcanon_small (Z.land fl 1)) by lia. reflexivity.
Qed.
Lemma s21_beq_atom : forall E n v, bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (sv_denot E (SOff n 0)) (sv_denot E (SLit 0)) = (v =? 0).
Proof.
intros E n v H Hr. rewrite YO0c.branch_eq.
change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)).
change (bv_unsigned (sv_denot E (SLit 0))) with (U E (SLit 0)).
rewrite U_SOff, U_SLit, H, Z.add_0_r, (zcanon_small v) by lia. reflexivity.
Qed.

(* ---------------------------------- the seed of D, at 0x85868 ---------------------------------- *)
Lemma s21_seedD : forall (W : world SEGS) regs mem s1 frn m mt,
  getr regs 9 = w64 s1 -> 70368744177664 <= s1 -> s1 + 192 <= 140737488355328 -> s1 mod 32 = 0 ->
  (forall o, 120 <= o < 128 -> apresent (w_H W) mem (s1 + o)) ->
  rdword (rdW W mem) (s1 + 48) = Some frn -> rdword (rdW W mem) (s1 + 168) = Some m ->
  getr regs 19 = w64 SHADOW_OFF -> getr regs 22 = w64 (mt + 16) ->
  4096 <= mt -> mt mod 16 = 0 -> mt + 40 <= s1 -> mt <= 140737479966720 ->
  (forall o, 0 <= o < 4 -> apresent (w_H W) mem (mt + 16 + o)) ->
  4352 <= frn -> frn + 4 <= s1 -> frn mod 32 = 0 -> frn <= 140737479966720 ->
  (forall o, 0 <= o < 4 -> apresent (w_H W) mem (frn + o)) ->
  (mt + 20 <= frn \/ frn + 4 <= mt + 16) ->
  range_addressable (rdW W mem) SHADOW_OFF (mt + 16) 8 -> (mt + 24 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= mt) ->
  range_addressable (rdW W mem) SHADOW_OFF frn 4 -> (frn + 4 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= frn) ->
  st_ok_pi SEGS VAL (ED regs frn m) ssD0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S21_PD)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 19 0) SHD (ED regs frn m) (mrestrict (w_H W) mem).
Proof.
intros W regs mem s1 frn m mt R9 Hs1a Hs1b Hs132 Hpr H48 H168 R19 R22 Hmt1 Hmt16 Hmt2 Hmt3 Hmtp Hf1 Hf2 Hf32 Hf3 Hfp
  Hd HRA1 Hb1 HRA2 Hb2.
set (E := ED regs frn m).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (subst E; unfold ED; rewrite (s21_EE regs _ 9 9%bv) by (lia || reflexivity); rewrite R9; apply s21_Uw; lia).
assert (U19 : bv_unsigned (ew E 19) = SHADOW_OFF)
  by (subst E; unfold ED; rewrite (s21_EE regs _ 19 19%bv) by (lia || reflexivity); rewrite R19; apply s21_Uw;
      unfold SHADOW_OFF; lia).
assert (U22 : bv_unsigned (ew E 22) = mt + 16)
  by (subst E; unfold ED; rewrite (s21_EE regs _ 22 22%bv) by (lia || reflexivity); rewrite R22; apply s21_Uw; lia).
assert (U32 : bv_unsigned (ew E 32) = frn)
  by (subst E; unfold ED; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; lia).
assert (U33 : bv_unsigned (ew E 33) = m)
  by (subst E; unfold ED; rewrite (s21_EX regs _ 1 33) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; exact (s21_rdword_rng _ _ _ _ H168)).
split.
- unfold ssD0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold ED. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rD1, rD2, rD3. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split.
      { intros o Ho. apply (apresent_writable SEGS). apply Hpr. lia. }
      repeat apply Forall_cons; try apply Forall_nil.
      -- apply (s21_chunk8 E (w_H W) mem s1 48 (SOff 32 0) frn); [|exact H48].
         cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
      -- apply (s21_chunk8 E (w_H W) mem s1 168 (SOff 33 0) m); [|exact H168].
         cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
    * rewrite U22. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). replace (mt + 16 + o) with (mt + 16 + o) by lia. apply Hmtp. lia.
    * rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply Hfp. lia.
  + apply pairwise_disjoint_of_extents. unfold rD1, rD2, rD3, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U22, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; zl.
  + split; [|split; [exact I | exact I]].
    cbn [fD f_atoms atoms_ok]. unfold afact_ok, S21_S1F. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U22, U32. unfold SHADOW_OFF.
    change (2 ^ 0) with 1. change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
    replace (mt + 16) with (mt + 1 * 16) by lia. rewrite Z.mod_add by lia.
    repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia].
- unfold sh_ok, SHD. constructor; [|constructor; [|constructor]].
  + apply (shent_ok_of_range SEGS (w_H W) mem E (SOff 19 0) 22 (mt + 16) 8 (mt + 16) 0 8).
    * exact HRA1.
    * unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
    * unfold U. cbn [sv_denot]. rewrite U22, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
  + apply (shent_ok_of_range SEGS (w_H W) mem E (SOff 19 0) 32 frn 4 frn 0 4).
    * exact HRA2.
    * unfold U. cbn [sv_denot]. rewrite U19, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
    * unfold U. cbn [sv_denot]. rewrite U32, Z.add_0_r. apply unsigned_lit_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
Qed.

(* the cut K857cc, at the segment's entry state *)
Definition s21_K0 (cx : lcx) ly S (W : world SEGS) regs0 mem0 md0 k acc (c m tab mt : Z) : Prop :=
  lt_base B MT cx /\ sa_frm0 /\
  lt_core B MT cx ly S W regs0 mem0 md0 k acc 4 LFO0
    [(mt, x_mtn cx); (tab, x_tabn cx); (m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem0) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem0) m seg_spec.SEG_M_SIZE /\
  lt_hblk B ly S (rdW W mem0) tab (x_tabn cx) /\ lt_hblk B ly S (rdW W mem0) mt (x_mtn cx) /\
  zero_atA (rdW W mem0) tab (x_tabn cx) /\ zero_atA (rdW W mem0) mt (x_mtn cx) /\
  getr regs0 26 = w64 (shadow_addr (m + seg_spec.MC_N)) /\
  lt_slots cx (rdW W mem0) (LT_L cx c m ++ [(152, shadow_addr (m + seg_spec.MC_N))]) /\
  lt_cm (rdW W mem0) c m (x_run cx).

Lemma s21_EF : forall cx ly S (W : world SEGS) regs mem md k o,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx.
Proof.
intros cx ly S W regs mem md k o HB HF. pose proof HB as (HPRE & _). pose proof HF as (HJ & _). unfold x_fr.
destruct (al_layout _ _ LAWS (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) ly (proj1 HPRE) (proj1 (proj2 HJ)))
  as (_ & Efa & _).
apply Efa.
Qed.
(* the frame's shadow bytes but n's are not written by the head *)
Lemma s21_X_sh : forall cx ly S (W : world SEGS) regs mem md k o tab mt i,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o ->
  In (tab, x_tabn cx) (ablocks B ly S) -> In (mt, x_mtn cx) (ablocks B ly S) ->
  0 <= i < 64 -> i <> 32 -> ~ s21_X cx tab mt (x_sh cx + i).
Proof.
intros cx ly S W regs mem md k o tab mt i HB HF Htab Hmt Hi Hne.
destruct (s21_nums cx ly S W regs mem md k o HB HF) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HF as (HJ & _). pose proof (proj1 HJ) as HAR.
pose proof (s21_xcap_rng cx) as Hcap.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem md tab _ HAR Htab) as (T1 & T2 & T3 & T4 & _).
destruct (al_blocks _ _ LAWS ly S W mem md mt _ HAR Hmt) as (M1 & M2 & M3 & M4 & _).
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt]. pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Rm].
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in T4, M4, N8.
assert (Hsh : SHADOW_OFF <= x_sh cx < 0x10007fff8000 - 64)
  by (rewrite N9; unfold SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)); lia).
unfold SHADOW_OFF in Hsh. unfold s21_X. intros Hx.
destruct Hx as [H|[H|[H|[H|[H|H]]]]]; lia.
Qed.
Lemma s21_fshN : forall (rd rd' : reader) a, sa_zs rd a (lt_fsh LFO0) ->
  (forall i, 0 <= i < 36 -> i <> 32 -> rd' (a + i) = rd (a + i)) -> rd' (a + 32) = Some 4 ->
  sa_zs rd' a (lt_fsh LFO_N).
Proof.
intros rd rd' a H HK H32 i Hi. rewrite lt_fsh_len in Hi.
destruct (Nat.eq_dec i 32) as [->|Hne].
- change (Z.of_nat 32) with 32. rewrite H32. reflexivity.
- rewrite HK by lia. rewrite (H i ltac:(rewrite lt_fsh_len; exact Hi)). f_equal.
  do 36 (destruct i as [|i]; [first [reflexivity | exfalso; lia] |]). lia.
Qed.
(* n's 4 bytes addressable once its shadow byte is 4 *)
Lemma s21_ra_n : forall (rd : reader) fr, fr mod 32 = 0 -> rd (SHADOW_OFF + fr / 8 + 32) = Some 4 ->
  range_addressable rd SHADOW_OFF (fr + 256) 4.
Proof.
intros rd fr Hf H x Hx.
assert (Hq : fr = 32 * (fr / 32)) by (pose proof (Z_div_mod_eq_full fr 32); lia).
set (q := fr / 32) in *.
assert (H8 : fr / 8 = 4 * q) by (rewrite Hq; replace (32 * q) with ((4 * q) * 8) by lia; apply Z.div_mul; lia).
pose proof (Z_div_mod_eq_full x 8) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
assert (Hx8 : x / 8 = 4 * q + 32) by lia.
exists 4. split.
- unfold shadow_of_addr. rewrite Hx8. rewrite H8 in H. replace (SHADOW_OFF + (4 * q + 32)) with (SHADOW_OFF + 4 * q + 32) by lia.
  exact H.
- unfold saddr_ok. right. lia.
Qed.

(* from the head's end state to the tail's cut *)
Lemma s21_toT : S21_T_stmt -> forall cx ly S W regs0 mem0 md0 k acc (c m tab mt : Z) regs mem md,
  s21_K0 cx ly S W regs0 mem0 md0 k acc c m tab mt ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 2 = getr regs0 2 -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 8 = getr regs0 8 -> getr regs 9 = getr regs0 9 ->
  getr regs 16 = w64 m -> getr regs 20 = w64 mt -> getr regs 21 = w64 (x_sh cx) -> getr regs 22 = w64 (mt + 16) ->
  getr regs 24 = w64 tab -> getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_X cx tab mt a -> rdW W mem a = rdW W mem0 a) ->
  rdW W mem (x_sh cx + 32) = Some 4 ->
  rdword (rdW W mem) (x_s1 cx + 120) = Some (Z.of_nat (length (x_tab0 cx))) ->
  lt_tabs cx (rdW W mem) tab mt (x_tab0 cx) ->
  SRr SEGS W (cfg_at SEGS (BASE + S21_PT) regs mem md) (lt_post B MT cx).
Proof.
intros HT cx ly S W regs0 mem0 md0 k acc c m tab mt regs mem md
  (HB & HFRM & HC0 & Hc0 & Hm0 & Ht0 & Hmt0 & _ & _ & _ & HSL0 & HCM0) HJ E2 E3 E4 E8 E9 R16 R20 R21 R22 R24 R26 HK
  H32 H120 HTB.
pose proof HC0 as (HF0 & _).
pose proof (proj1 HJ) as HAR.
pose proof Hc0 as (HcIn & _). pose proof Hm0 as (HmIn & _). pose proof Ht0 as (HtIn & _). pose proof Hmt0 as (HmtIn & _).
destruct (s21_X_apart cx ly S W regs0 mem0 md0 k LFO0 tab mt HB HF0 HtIn HmtIn) as (A1 & A2 & A3 & A4 & A5).
destruct (s21_nums cx ly S W regs0 mem0 md0 k LFO0 HB HF0) as (N1 & N2 & N3 & N4 & _).
pose proof asan_consts as (C1 & _).
pose proof (s21_xcap_rng cx) as Hcap.
apply (HT cx ly S W regs mem md k acc c m tab mt HB HFRM).
- apply (s21_core_keep cx ly S W regs0 mem0 md0 k acc 4 LFO0 _ regs mem md LFO_N tab mt HB HC0 HtIn HmtIn HJ
    E2 E3 E4 E8 E9 HK).
  pose proof HF0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSH).
  apply (s21_fshN _ _ _ HSH); [|exact H32].
  intros i Hi Hne. apply HK.
  + destruct (s21_nums cx ly S W regs0 mem0 md0 k LFO0 HB HF0) as (_ & _ & _ & _ & _ & N5 & N6 & _ & _ & N9 & _).
    rewrite N9. unfold SHADOW_OFF. pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)). lia.
  + exact (s21_X_sh cx ly S W regs0 mem0 md0 k LFO0 tab mt i HB HF0 HtIn HmtIn ltac:(lia) Hne).
- exact (s21_hblk_of_AR ly S W mem md c _ HAR HcIn ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
- exact (s21_hblk_of_AR ly S W mem md m _ HAR HmIn ltac:(unfold seg_spec.SEG_M_SIZE; lia)).
- exact (s21_hblk_of_AR ly S W mem md tab _ HAR HtIn ltac:(assert (x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity; lia)).
- exact (s21_hblk_of_AR ly S W mem md mt _ HAR HmtIn ltac:(assert (x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity; lia)).
- exact R16.
- exact R20.
- exact R21.
- exact R22.
- exact R24.
- exact R26.
- intros o v Hin. apply in_app_or in Hin as [Hin|Hin].
  + assert (Ho : 8 <= o <= 56 \/ 144 <= o <= 184)
      by (apply (s21_LV_off cx c m o v); apply in_or_app; left; exact Hin).
    assert (Hin2 : In (o, v) (LT_L cx c m ++ [(152, shadow_addr (m + seg_spec.MC_N))]))
      by (apply in_or_app; left; unfold LT_LV, LT_L in *; cbn [In] in *; tauto).
    apply (s21_rdword_keep _ _ _ _ (HSL0 o v Hin2)). intros j Hj. apply HK; [lia|]. apply A4. lia.
  + cbn [In] in Hin. destruct Hin as [Eq|[Eq|[]]]; injection Eq as <- <-; [exact H120|].
    apply (s21_rdword_keep _ _ _ _ (HSL0 152 _ ltac:(apply in_or_app; right; left; reflexivity))).
    intros j Hj. apply HK; [lia|]. apply A4. lia.
- apply (s21_cm_keep _ _ c m _ HCM0); intros i Hi; apply HK.
  + pose proof Hc0 as (_ & Hc4096 & _). destruct (al_blocks _ _ LAWS ly S W mem md c _ HAR HcIn) as (_ & _ & Hq & _).
    change (req_size seg_spec.SEG_C_SIZE) with 16616 in Hq. unfold seg_spec.SEG_C_SIZE in Hi. lia.
  + apply (A5 c seg_spec.SEG_C_SIZE); [exact HcIn | intros Heq; injection Heq; intros; assert (x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity; unfold seg_spec.SEG_C_SIZE in *; lia
      | intros Heq; injection Heq; intros; assert (x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity; unfold seg_spec.SEG_C_SIZE in *; lia
      | change (req_size seg_spec.SEG_C_SIZE) with 16616; unfold seg_spec.SEG_C_SIZE in Hi; lia].
  + pose proof Hm0 as (_ & Hm4096 & _). destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HmIn) as (_ & _ & Hq & _).
    change (req_size seg_spec.SEG_M_SIZE) with 9236 in Hq. unfold seg_spec.SEG_M_SIZE in Hi. lia.
  + apply (A5 m seg_spec.SEG_M_SIZE); [exact HmIn | intros Heq; injection Heq; intros; assert (x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity; unfold seg_spec.SEG_M_SIZE in *; lia
      | intros Heq; injection Heq; intros; assert (x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity; unfold seg_spec.SEG_M_SIZE in *; lia
      | change (req_size seg_spec.SEG_M_SIZE) with 9236; unfold seg_spec.SEG_M_SIZE in Hi; lia].
- exact HTB.
Qed.

(* a block's bytes are none of the three windows *)
Lemma s21_WB_blk : forall cx ly S (W : world SEGS) regs mem md k o p n a,
  lt_base B MT cx -> lt_frame B cx ly S W regs mem md k o -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n -> ~ s21_WB cx a.
Proof.
intros cx ly S W regs mem md k o p n a HB HF Hpn Ha.
destruct (s21_nums cx ly S W regs mem md k o HB HF) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HF as (HJ & _). pose proof (proj1 HJ) as HAR.
assert (Hin3 : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Nfr; left; reflexivity).
destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hpn) as (P1 & P2 & P3 & P4 & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md p n _ _ HAR Hpn Hin3) as D3.
rewrite (s21_EF cx ly S W regs mem md k o HB HF) in D3. unfold zdisjoint in D3. cbn [fst snd] in D3.
change (fs_frame_bytes LT_FCLS) with 512 in D3.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in P4, N8.
assert (Hsh : SHADOW_OFF <= x_sh cx < 0x10007fff8000 - 64)
  by (rewrite N9; unfold SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)); lia).
unfold s21_WB, FO_N, SHADOW_OFF in *. intros [H|[H|H]]; lia.
Qed.
(* from the stretch 0x857f4 .. 0x85894 with no entry seeded (flags & 1 = 0, or cap = 0) to the tail's cut *)
Lemma s21_BtoT : S21_T_stmt -> forall cx ly S W regs0 mem0 md0 k acc (c m tab mt : Z) memB regs mem md,
  s21_K0 cx ly S W regs0 mem0 md0 k acc c m tab mt ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 2 = getr regs0 2 -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 8 = getr regs0 8 -> getr regs 9 = getr regs0 9 ->
  getr regs 16 = w64 m -> getr regs 20 = w64 mt -> getr regs 21 = w64 (x_sh cx) -> getr regs 22 = w64 (mt + 16) ->
  getr regs 24 = w64 tab -> getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  x_tab0 cx = [] ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_Xh cx tab mt a -> rdW W memB a = rdW W mem0 a) ->
  (forall i, 0 <= i < 18 -> rdW W memB (tab + 18 * x_cap cx + i) = Some (90 mod 256)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_WB cx a -> rdW W mem a = rdW W memB a) ->
  rdW W mem (x_sh cx + 32) = Some 4 -> rdword (rdW W mem) (x_s1 cx + 120) = Some 0 ->
  sa_val (rdW W mem) (x_fr cx + FO_N) 4 0 ->
  SRr SEGS W (cfg_at SEGS (BASE + S21_PT) regs mem md) (lt_post B MT cx).
Proof.
intros HT cx ly S W regs0 mem0 md0 k acc c m tab mt memB regs mem md HK0 HJ E2 E3 E4 E8 E9 R16 R20 R21 R22 R24 R26
  Ht0e HKB Hg KW H32 H120 Hn.
pose proof HK0 as (HB & HFRM & HC0 & Hc0 & Hm0 & Ht0 & Hmt0 & _).
pose proof HC0 as (HF0 & _). pose proof HF0 as (HJ0 & _). pose proof (proj1 HJ0) as HAR0.
pose proof Ht0 as (HtIn & _).
pose proof (s21_xcap_rng cx) as Hcap.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
destruct (al_blocks _ _ LAWS ly S W mem0 md0 tab _ HAR0 HtIn) as (T1 & T2 & T3 & _).
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt].
pose proof asan_consts as (C1 & _).
apply (s21_toT HT cx ly S W regs0 mem0 md0 k acc c m tab mt regs mem md HK0 HJ E2 E3 E4 E8 E9 R16 R20 R21 R22 R24 R26).
- intros a Ha Hx. assert (Hh : ~ s21_Xh cx tab mt a) by (intros Hq; exact (Hx (s21_Xh_X _ _ _ _ Hq))).
  rewrite KW; [exact (HKB a Ha Hh) | exact Ha | intros Hw; exact (Hh (s21_WB_Xh _ _ _ _ Hw))].
- exact H32.
- rewrite Ht0e. exact H120.
- unfold lt_tabs. rewrite Ht0e. split; [cbn; lia|]. split; [apply s21_rtab_nil|]. split.
  + apply s21_guard. intros i Hi. rewrite KW; [exact (Hg i Hi) | lia |].
    apply (s21_WB_blk cx ly S W regs0 mem0 md0 k LFO0 tab (x_tabn cx)); [exact HB | exact HF0 | exact HtIn | lia].
  + split; [exact Hn|]. split; [apply s21_mtab_nil | cbn; lia].
Qed.

(* ---------------------------------- stage D: 0x85868 .. 0x85894 ---------------------------------- *)
Definition S21_D_stmt : Prop :=
  forall cx ly S W regs0 mem0 md0 k acc (c m tab mt : Z) regs mem md,
  s21_K0 cx ly S W regs0 mem0 md0 k acc c m tab mt ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 2 = getr regs0 2 -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 8 = getr regs0 8 -> getr regs 9 = getr regs0 9 ->
  getr regs 18 = w64 33 -> getr regs 19 = w64 SHADOW_OFF -> getr regs 20 = w64 mt -> getr regs 21 = w64 (x_sh cx) ->
  getr regs 22 = w64 (mt + 16) -> getr regs 24 = w64 tab -> getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_Xh cx tab mt a -> rdW W mem a = rdW W mem0 a) ->
  (forall i, 0 <= i < 18 -> rdW W mem (tab + 18 * x_cap cx + i) = Some (90 mod 256)) ->
  rdW W mem (x_sh cx + 32) = Some 4 ->
  sa_zs (rdW W mem) tab (SegModel.S_enp ++ [0]) -> sa_val (rdW W mem) (tab + 16) 2 33 ->
  sa_zs (rdW W mem) mt (SegModel.S_enp ++ [0]) ->
  SRr SEGS W (cfg_at SEGS (BASE + S21_PD) regs mem md) (lt_post B MT cx).

Lemma s21_stageD : S21_T_stmt -> S21_D_stmt.
Proof.
intros HT. unfold S21_D_stmt.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt regs mem md HK0 HJ E2 E3 E4 E8 E9 R18 R19 R20 R21 R22 R24 R26
  Hfl Hcp HK Hg H32 Htl Htv Hml.
pose proof HK0 as (HB & HFRM & HC0 & Hc0 & Hm0 & Ht0 & Hmt0 & Hz1 & Hz2 & R26_0 & HSL0 & HCM0).
pose proof HC0 as (HF0 & _ & HBL0 & _).
destruct (s21_nums cx ly S W regs0 mem0 md0 k LFO0 HB HF0) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HF0 as (HJ0 & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & H176 & _).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ0) as HAR0.
pose proof (s21_EF cx ly S W regs0 mem0 md0 k LFO0 HB HF0) as EF.
pose proof Ht0 as (HtIn & _). pose proof Hmt0 as (HmtIn & _). pose proof Hm0 as (HmIn & Hm4096 & _).
destruct (s21_X_apart cx ly S W regs0 mem0 md0 k LFO0 tab mt HB HF0 HtIn HmtIn) as (A1 & A2 & A3 & A4 & A5).
pose proof (s21_xcap_rng cx) as Hcap.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt]. pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Rm].
destruct (al_blocks _ _ LAWS ly S W mem md tab _ HAR HtIn) as (T1 & T2 & T3 & T4 & _).
destruct (al_blocks _ _ LAWS ly S W mem md mt _ HAR HmtIn) as (M1 & M2 & M3 & M4 & M5 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m _ HAR HmIn) as (_ & _ & Mm3 & _).
change (req_size seg_spec.SEG_M_SIZE) with 9236 in Mm3.
assert (Hin3 : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Nfr; left; reflexivity).
destruct (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin3) as (_ & _ & F3 & _).
rewrite EF in F3. change (fs_frame_bytes LT_FCLS) with 512 in F3.
pose proof (sep_blocks SEGS B LAWS ly S W mem md tab _ mt _ HAR HtIn HmtIn ltac:(intros Heq; injection Heq; lia)) as Dtm.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md tab _ _ _ HAR HtIn Hin3) as DtF.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md mt _ _ _ HAR HmtIn Hin3) as DmF.
rewrite EF in DtF, DmF. unfold zdisjoint in Dtm, DtF, DmF. cbn [fst snd] in Dtm, DtF, DmF.
change (fs_frame_bytes LT_FCLS) with 512 in DtF, DmF.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in T4, M4, N8.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hsh : SHADOW_OFF <= x_sh cx < 0x10007fff8000 - 64)
  by (rewrite N9; unfold SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)); lia).
unfold SHADOW_OFF in Hsh.
assert (Hmtnew : ~ In (mt, x_mtn cx) (x_bl0 B cx))
  by exact (proj2 (s21_blk_new cx ly S W mem0 md0 _ mt (x_mtn cx) HAR0 HBL0 ltac:(cbn [In]; tauto))).
(* the slots this stretch reads, at the current state *)
assert (KS : forall o v, In (o, v) (LT_L cx c m) -> o <= 88 \/ 144 <= o ->
  rdword (rdW W mem) (x_s1 cx + o) = Some v).
{ intros o v Hin Ho.
  assert (Hb : 8 <= o <= 184) by (unfold LT_L in Hin; cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); destruct Hin).
  apply (s21_rdword_keep _ _ _ _ (HSL0 o v ltac:(apply in_or_app; left; exact Hin))).
  intros j Hj. apply HK; [lia|]. intros Hx. apply (A4 (x_s1 cx + o + j)); [lia | exact (s21_Xh_X _ _ _ _ Hx)]. }
assert (H48 : rdword (rdW W mem) (x_s1 cx + 48) = Some (x_fr cx + FO_N))
  by (apply KS; [unfold LT_L; cbn [In]; tauto | lia]).
assert (H168 : rdword (rdW W mem) (x_s1 cx + 168) = Some m) by (apply KS; [unfold LT_L; cbn [In]; tauto | lia]).
assert (HRA1 : range_addressable (rdW W mem) SHADOW_OFF (mt + 16) 8)
  by exact (range_addressable_of_block SEGS B LAWS ly S W mem md mt _ (mt + 16) 8 HAR HmtIn ltac:(lia) ltac:(lia)).
assert (HRA2 : range_addressable (rdW W mem) SHADOW_OFF (x_fr cx + FO_N) 4).
{ unfold FO_N. apply s21_ra_n; [exact N7|]. rewrite <- N9. exact H32. }
destruct (s21_seedD W regs mem (x_s1 cx) (x_fr cx + FO_N) m mt ltac:(rewrite E9; exact R9) ltac:(lia) ltac:(lia) N3
  ltac:(intros o Ho; apply Hpres; unfold STK_LLVMFuzzerTestOneInput; lia) H48 H168 R19 R22 M2 M1 ltac:(lia) ltac:(lia)
  ltac:(intros o Ho; exact (proj1 (M5 (mt + 16 + o) ltac:(lia)))) ltac:(unfold FO_N; lia) ltac:(unfold FO_N; lia)
  ltac:(unfold FO_N; rewrite Z.add_mod by lia; rewrite N7; reflexivity) ltac:(unfold FO_N; lia)
  ltac:(intros o Ho; exact (proj1 (F3 (x_fr cx + FO_N + o) ltac:(unfold FO_N; lia))))
  ltac:(unfold FO_N; lia) HRA1 ltac:(unfold SHADOW_OFF; lia) HRA2 ltac:(unfold FO_N, SHADOW_OFF; lia)) as [HS0 SHOK].
pose proof (st_ok_pi_pin_reg' _ _ _ 18%bv 33 HS0 R18 eq_refl) as HS. clear HS0.
lazymatch type of HS with st_ok_pi ?a ?b ?c ?ssx ?d => let v := eval vm_compute in ssx in change ssx with v in HS end.
assert (EV : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (ED regs (x_fr cx + FO_N) m) n = getr regs r) by (intros n r Hn Hr; unfold ED; apply s21_EE; assumption).
assert (HEI : img_env VAL A_LIM (ED regs (x_fr cx + FO_N) m)) by (unfold ED; apply Eimg_env).
assert (U9 : bv_unsigned (ew (ED regs (x_fr cx + FO_N) m) 9) = x_s1 cx)
  by (rewrite (EV 9%nat 9%bv) by (lia || reflexivity); rewrite E9, R9; apply s21_Uw; lia).
assert (U9s : bv_unsigned (ew (ED regs (x_fr cx + FO_N) m) 9) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (rewrite U9; lia).
assert (U22 : bv_unsigned (ew (ED regs (x_fr cx + FO_N) m) 22) = mt + 16)
  by (rewrite (EV 22%nat 22%bv) by (lia || reflexivity); rewrite R22; apply s21_Uw; lia).
assert (U32 : bv_unsigned (ew (ED regs (x_fr cx + FO_N) m) 32) = x_fr cx + FO_N)
  by (unfold ED; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth]; apply s21_Uw;
      unfold FO_N; lia).
assert (E33 : ew (ED regs (x_fr cx + FO_N) m) 33 = w64 m)
  by (unfold ED; rewrite (s21_EX regs _ 1 33) by (reflexivity || (unfold A_TEXT; lia)); reflexivity).
set (E := ED regs (x_fr cx + FO_N) m) in *. clearbody E.
unfold cfg_at. change (w64 (BASE + S21_PD)) with (Z_to_bv 64 (BASE + S21_PD)).
(* 0x85868 .. 0x85894: mt + 16's shadow (check 28, covered), mt[0].vid := 33, n := 1, 120(s1) := 1, a6 := m *)
paj_run_to_tok RUNTO HS HJ SHOK S21_span S21_PT.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  eapply awr_ok_cons_stack_off; [reflexivity | exact U9s | cbn; unfold STK_LLVMFuzzerTestOneInput; lia | cbn; lia |].
  eapply awr_ok_cons_gen; [reflexivity | exact U22 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left. exists mt, (x_mtn cx).
    split; [exact HmtIn | split; [exact Hmtnew | lia]]. }
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists LT_FCLS, (x_fpos cx).
  split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite EF. change (fs_frame_bytes LT_FCLS) with 512.
  unfold FO_N in Ha. lia. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (KD : forall a, 0 <= a < 2 ^ 64 ->
  ~ ((x_s1 cx + 120 <= a < x_s1 cx + 128) \/ (mt + 16 <= a < mt + 20) \/ (x_fr cx + 256 <= a < x_fr cx + 260)) ->
  rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _
    (fun a => (x_s1 cx + 120 <= a < x_s1 cx + 128) \/ (mt + 16 <= a < mt + 20) \/ (x_fr cx + 256 <= a < x_fr cx + 260))
    HFr); [|exact Ha | exact Hna].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq0 | [Hq0 | [Hq0 | []]]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
    [rewrite U9 in Hrr | rewrite U22 in Hrr | rewrite U32 in Hrr; unfold FO_N in Hrr]; lia. }
clear HF HFr HG.
pmkst HS.
prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (16%bv : bv 5) P16.
prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
rewrite (EV 2%nat 2%bv) in P2 by (lia || reflexivity). rewrite (EV 3%nat 3%bv) in P3 by (lia || reflexivity).
rewrite (EV 4%nat 4%bv) in P4 by (lia || reflexivity). rewrite (EV 8%nat 8%bv) in P8 by (lia || reflexivity).
rewrite (EV 9%nat 9%bv) in P9 by (lia || reflexivity). rewrite E33 in P16.
rewrite (EV 20%nat 20%bv) in P20 by (lia || reflexivity). rewrite (EV 21%nat 21%bv) in P21 by (lia || reflexivity).
rewrite (EV 22%nat 22%bv) in P22 by (lia || reflexivity). rewrite (EV 24%nat 24%bv) in P24 by (lia || reflexivity).
rewrite (EV 26%nat 26%bv) in P26 by (lia || reflexivity).
(* what the run wrote *)
assert (W120 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 120) = Some 1)
  by (eapply (s21_slot_rd E _ ms (w_H W) _ 120 (SLit 1) 1 (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | reflexivity | lia]).
assert (Wvid : sa_val (rdW W (ms_mem ms)) (mt + 16) 4 33).
{ pose proof (s21_chunk_rdi E _ ms (w_H W) 1 _ 0 4 (SLit 33) 33 HS eq_refl ltac:(s21_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as H.
  cbn [YP09.r_base base_val] in H. rewrite U22, Z.add_0_r in H. exact H. }
assert (Wn : sa_val (rdW W (ms_mem ms)) (x_fr cx + FO_N) 4 1).
{ pose proof (s21_chunk_rdi E _ ms (w_H W) 2 _ 0 4 (SLit 1) 1 HS eq_refl ltac:(s21_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as H.
  cbn [YP09.r_base base_val] in H. rewrite U32, Z.add_0_r in H. exact H. }
apply (s21_toT HT cx ly S W regs0 mem0 md0 k acc c m tab mt (ms_regs ms) (ms_mem ms) md1 HK0 HJ).
- rewrite P2. exact E2.
- rewrite P3. exact E3.
- rewrite P4. exact E4.
- rewrite P8. exact E8.
- rewrite P9. exact E9.
- exact P16.
- rewrite P20. exact R20.
- rewrite P21. exact R21.
- rewrite P22. exact R22.
- rewrite P24. exact R24.
- rewrite P26. exact R26.
- intros a Ha Hx. rewrite KD; [| exact Ha |].
  + apply HK; [exact Ha|]. intros Hh. exact (Hx (s21_Xh_X _ _ _ _ Hh)).
  + intros Hw. apply Hx. unfold s21_X. destruct Hw as [Hw|[Hw|Hw]].
    * right; right; right; right; right. lia.
    * right; left. lia.
    * right; right; right; left. exact Hw.
- rewrite KD; [exact H32 | lia | lia].
- rewrite (s21_tab0_one cx Hfl Hcp). exact W120.
- unfold lt_tabs. rewrite (s21_tab0_one cx Hfl Hcp).
  split; [cbn; lia|]. split.
  { apply s21_rtab_one.
    - apply (s21_zs_keep _ _ _ _ Htl). intros i Hi. cbn in Hi. apply KD; lia.
    - intros i Hi. rewrite KD by lia. rewrite HK by (try lia; unfold s21_Xh; lia). apply Hz1. lia.
    - apply (s21_val_keep _ _ _ _ _ Htv). intros i Hi. cbn in Hi. apply KD; lia. }
  split.
  { apply s21_guard. intros i Hi. rewrite KD by lia. apply Hg. exact Hi. }
  split.
  { change (Z.of_nat (length [(SegModel.S_enp, 33)])) with 1. exact Wn. }
  split; [|cbn; lia].
  apply s21_mtab_one.
  + apply (s21_zs_keep _ _ _ _ Hml). intros i Hi. cbn in Hi. apply KD; lia.
  + intros i Hi. rewrite KD by lia. rewrite HK by (try lia; unfold s21_Xh; lia). apply Hz2. lia.
  + exact Wvid.
Qed.

(* the write permission of B's three windows: 120(s1), n's shadow byte, n *)
Ltac s21_awrB cx U9s U21 U33 EF :=
  lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end;
  eapply awr_ok_cons_stack_off; [reflexivity | exact U9s | cbn; unfold STK_LLVMFuzzerTestOneInput; lia | cbn; lia |];
  eapply awr_ok_cons_gen; [reflexivity | exact U21 | |];
  [ intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists LT_FCLS, (x_fpos cx);
    split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd]; rewrite EF;
    change (shadow_addr (x_fr cx)) with (x_sh cx); change (fs_frame_bytes LT_FCLS / 8) with 64; lia
  | eapply awr_ok_cons_gen; [reflexivity | exact U33 | | apply awr_ok_nil];
    intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; right; right; right; left; exists LT_FCLS, (x_fpos cx);
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; rewrite EF;
    change (fs_frame_bytes LT_FCLS) with 512; unfold FO_N in Ha; lia ].

(* ---------------------------------- the seed of B, at 0x857f4 ---------------------------------- *)
Lemma s21_seedB : forall (W : world SEGS) regs mem s1 fl frn m sh,
  getr regs 9 = w64 s1 -> 70368744177664 <= s1 -> s1 + 192 <= 140737488355328 ->
  (forall o, 120 <= o < 128 -> apresent (w_H W) mem (s1 + o)) ->
  rdword (rdW W mem) (s1 + 16) = Some fl -> rdword (rdW W mem) (s1 + 48) = Some frn ->
  rdword (rdW W mem) (s1 + 168) = Some m ->
  getr regs 21 = w64 sh -> 0 <= sh -> sh + 36 <= s1 -> apresent (w_H W) mem (sh + 32) ->
  0 <= frn -> frn + 4 <= s1 -> (forall o, 0 <= o < 4 -> apresent (w_H W) mem (frn + o)) ->
  (sh + 36 <= frn \/ frn + 4 <= sh) ->
  st_ok_pi SEGS VAL (EB regs fl frn m) ssB0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S21_PB)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 fl frn m sh R9 Hs1a Hs1b Hpr H16 H48 H168 R21 Hsh0 Hsh1 Hshp Hf0 Hf1 Hfp Hd.
set (E := EB regs fl frn m).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (subst E; unfold EB; rewrite (s21_EE regs _ 9 9%bv) by (lia || reflexivity); rewrite R9; apply s21_Uw; lia).
assert (U21 : bv_unsigned (ew E 21) = sh)
  by (subst E; unfold EB; rewrite (s21_EE regs _ 21 21%bv) by (lia || reflexivity); rewrite R21; apply s21_Uw; lia).
assert (U32 : bv_unsigned (ew E 32) = fl)
  by (subst E; unfold EB; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; exact (s21_rdword_rng _ _ _ _ H16)).
assert (U33 : bv_unsigned (ew E 33) = frn)
  by (subst E; unfold EB; rewrite (s21_EX regs _ 1 33) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; exact (s21_rdword_rng _ _ _ _ H48)).
assert (U34 : bv_unsigned (ew E 34) = m)
  by (subst E; unfold EB; rewrite (s21_EX regs _ 2 34) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; exact (s21_rdword_rng _ _ _ _ H168)).
unfold ssB0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold EB. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rB1, rB2, rB3. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split.
    { intros o Ho. apply (apresent_writable SEGS). apply Hpr. lia. }
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (s21_chunk8 E (w_H W) mem s1 16 (SOff 32 0) fl); [|exact H16]. cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
    * apply (s21_chunk8 E (w_H W) mem s1 48 (SOff 33 0) frn); [|exact H48]. cbn [sv_denot]. rewrite U33, Z.add_0_r. reflexivity.
    * apply (s21_chunk8 E (w_H W) mem s1 168 (SOff 34 0) m); [|exact H168]. cbn [sv_denot]. rewrite U34, Z.add_0_r. reflexivity.
  + rewrite U21. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). replace (sh + o) with (sh + 32) by lia. exact Hshp.
  + rewrite U33. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hfp. lia.
- apply pairwise_disjoint_of_extents. unfold rB1, rB2, rB3, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U21, U33.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; zl.
- split; [exact I | split; exact I].
Qed.

(* ---------------------------------- the seed of C, at 0x85834 ---------------------------------- *)
Lemma s21_seedC : forall (W : world SEGS) regs mem s1 tab,
  getr regs 9 = w64 s1 -> 70368744177664 <= s1 -> s1 + 192 <= 140737488355328 ->
  rdword (rdW W mem) (s1 + 176) = Some SHADOW_OFF ->
  getr regs 24 = w64 tab -> 4096 <= tab -> tab mod 16 = 0 -> tab + 24 <= s1 -> tab <= 140737479966720 ->
  (forall o, 16 <= o < 18 -> apresent (w_H W) mem (tab + o)) ->
  range_addressable (rdW W mem) SHADOW_OFF (tab + 16) 8 -> (tab + 24 <= SHADOW_OFF \/ SHADOW_OFF + 2 ^ 44 <= tab) ->
  st_ok_pi SEGS VAL (EC regs) ssC0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + S21_PC)) mem (seg_rom SEGS))) /\
  sh_ok SEGS (SOff 32 0) SHC (EC regs) (mrestrict (w_H W) mem).
Proof.
intros W regs mem s1 tab R9 Hs1a Hs1b H176 R24 Ht1 Ht16 Ht2 Ht3 Htp HRA Hb.
set (E := EC regs).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (subst E; unfold EC; rewrite (s21_EE regs _ 9 9%bv) by (lia || reflexivity); rewrite R9; apply s21_Uw; lia).
assert (U24 : bv_unsigned (ew E 24) = tab)
  by (subst E; unfold EC; rewrite (s21_EE regs _ 24 24%bv) by (lia || reflexivity); rewrite R24; apply s21_Uw; lia).
assert (U32 : bv_unsigned (ew E 32) = SHADOW_OFF)
  by (subst E; unfold EC; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; unfold SHADOW_OFF; lia).
split.
- unfold ssC0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + subst E. unfold EC. apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + unfold rC1, rC2. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      apply (s21_chunk8 E (w_H W) mem s1 176 (SOff 32 0) SHADOW_OFF); [|exact H176].
      cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
    * rewrite U24. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply (apresent_writable SEGS). apply Htp. lia.
  + apply pairwise_disjoint_of_extents. unfold rC1, rC2, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9, U24.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; zl.
  + split; [|split; [exact I | exact I]].
    cbn [fC f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U32, U24. unfold SHADOW_OFF.
    change (2 ^ 0) with 1. change (2 ^ 4) with 16. rewrite !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia].
- unfold sh_ok, SHC. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W) mem E (SOff 32 0) 24 (tab + 16) 8 tab 16 24).
  + exact HRA.
  + unfold U. cbn [sv_denot]. rewrite U32, Z.add_0_r. apply unsigned_lit_small. unfold SHADOW_OFF. lia.
  + unfold U. cbn [sv_denot]. rewrite U24, Z.add_0_r. apply unsigned_lit_small. lia.
  + lia.
  + lia.
  + intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF in *. lia.
Qed.

(* ---------------------------------- stage C: 0x85834 .. memcpy(mt) ---------------------------------- *)
Definition S21_C_stmt : Prop :=
  forall cx ly S W regs0 mem0 md0 k acc (c m tab mt : Z) regs mem md,
  s21_K0 cx ly S W regs0 mem0 md0 k acc c m tab mt ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 2 = getr regs0 2 -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 8 = getr regs0 8 -> getr regs 9 = getr regs0 9 ->
  getr regs 20 = w64 mt -> getr regs 21 = w64 (x_sh cx) -> getr regs 22 = w64 (mt + 16) ->
  getr regs 24 = w64 tab -> getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  Z.land (x_flags cx) 1 <> 0 -> x_cap cx <> 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_Xh cx tab mt a -> rdW W mem a = rdW W mem0 a) ->
  (forall i, 0 <= i < 18 -> rdW W mem (tab + 18 * x_cap cx + i) = Some (90 mod 256)) ->
  rdW W mem (x_sh cx + 32) = Some 4 ->
  sa_zs (rdW W mem) tab (SegModel.S_enp ++ [0]) ->
  SRr SEGS W (cfg_at SEGS (BASE + S21_PC) regs mem md) (lt_post B MT cx).

Lemma s21_stageC : S21_D_stmt -> S21_C_stmt.
Proof.
intros HD. unfold S21_C_stmt.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt regs mem md HK0 HJ E2 E3 E4 E8 E9 R20 R21 R22 R24 R26
  Hfl Hcp HK Hg H32 Htl.
pose proof pa_segs_low as Hsegs.
pose proof HK0 as (HB & HFRM & HC0 & Hc0 & Hm0 & Ht0 & Hmt0 & Hz1 & Hz2 & R26_0 & HSL0 & HCM0).
pose proof HC0 as (HF0 & HI0 & HBL0 & _).
destruct (s21_nums cx ly S W regs0 mem0 md0 k LFO0 HB HF0) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HF0 as (HJ0 & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & H176 & _).
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ0) as HAR0.
pose proof Ht0 as (HtIn & _). pose proof Hmt0 as (HmtIn & _).
destruct (s21_X_apart cx ly S W regs0 mem0 md0 k LFO0 tab mt HB HF0 HtIn HmtIn) as (A1 & A2 & A3 & A4 & A5).
pose proof (s21_xcap_rng cx) as Hcap.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt]. pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Rm].
destruct (al_blocks _ _ LAWS ly S W mem md tab _ HAR HtIn) as (T1 & T2 & T3 & T4 & T5 & _).
destruct (al_blocks _ _ LAWS ly S W mem md mt _ HAR HmtIn) as (M1 & M2 & M3 & M4 & _).
pose proof (blk_off_imgP B ly S W mem md mt _ HAR HmtIn) as Mo. unfold off_img in Mo.
pose proof (sep_blocks SEGS B LAWS ly S W mem md tab _ mt _ HAR HtIn HmtIn ltac:(intros Heq; injection Heq; lia)) as Dtm.
unfold zdisjoint in Dtm. cbn [fst snd] in Dtm.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in T4, M4, N8.
assert (Hsh : SHADOW_OFF <= x_sh cx < 0x10007fff8000 - 64)
  by (rewrite N9; unfold SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)); lia).
unfold SHADOW_OFF in Hsh.
assert (Hmtnew : ~ In (mt, x_mtn cx) (x_bl0 B cx))
  by exact (proj2 (s21_blk_new cx ly S W mem0 md0 _ mt (x_mtn cx) HAR0 HBL0 ltac:(cbn [In]; tauto))).
(* the image at the current state: the literal "enp1s0" *)
assert (HI : lt_img B cx (rdW W mem)).
{ apply (s21_img_keep cx (w_H W) mem0 (w_H W) mem HI0). intros x Hx. apply HK; [unfold kImgEnd in Hx; lia|].
  intros Hh. exact (A1 x Hx (s21_Xh_X _ _ _ _ Hh)). }
assert (HRA1 : range_addressable (rdW W mem) SHADOW_OFF (tab + 16) 8)
  by exact (range_addressable_of_block SEGS B LAWS ly S W mem md tab _ (tab + 16) 8 HAR HtIn ltac:(lia) ltac:(lia)).
assert (H176' : rdword (rdW W mem) (x_s1 cx + 176) = Some SHADOW_OFF).
{ apply (s21_rdword_keep _ _ _ _ H176). intros j Hj. apply HK; [lia|]. intros Hx.
  apply (A4 (x_s1 cx + 176 + j)); [lia | exact (s21_Xh_X _ _ _ _ Hx)]. }
destruct (s21_seedC W regs mem (x_s1 cx) tab ltac:(rewrite E9; exact R9) ltac:(lia) ltac:(lia) H176' R24 T2 T1
  ltac:(lia) ltac:(lia) ltac:(intros o Ho; exact (proj1 (T5 (tab + o) ltac:(lia)))) HRA1 ltac:(unfold SHADOW_OFF; lia))
  as [HS SHOK].
assert (EV : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew (EC regs) n = getr regs r)
  by (intros n r Hn Hr; unfold EC; apply s21_EE; assumption).
assert (HEI : img_env VAL A_LIM (EC regs)) by (unfold EC; apply Eimg_env).
assert (U24 : bv_unsigned (ew (EC regs) 24) = tab)
  by (rewrite (EV 24%nat 24%bv) by (lia || reflexivity); rewrite R24; apply s21_Uw; lia).
assert (E32 : ew (EC regs) 32 = w64 SHADOW_OFF)
  by (unfold EC; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); reflexivity).
set (E := EC regs) in *. clearbody E.
unfold cfg_at. change (w64 (BASE + S21_PC)) with (Z_to_bv 64 (BASE + S21_PC)).
(* 0x85834 .. 0x85864: tab + 16's shadow (check 27, covered), tab[0].vid := 33, s3 := the base, a1 := "enp1s0",
   a2 := 7, a0 := mt, jal memcpy *)
paj_run_tok RUN HS HJ SHOK S21_span.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U24 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; left. exists tab, (x_tabn cx).
  split; [exact HtIn | split; [exact (proj2 (s21_blk_new cx ly S W mem0 md0 _ tab (x_tabn cx) HAR0 HBL0 ltac:(cbn [In]; tauto))) | lia]]. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ (tab + 16 <= a < tab + 18) -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha Hna.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => tab + 16 <= a < tab + 18) HFr); [|exact Ha | exact Hna].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq0 | [Hq0 | []]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr; [|rewrite U24 in Hrr]; lia. }
assert (Wvid : sa_val (rdW W (ms_mem ms)) (tab + 16) 2 33).
{ lazymatch type of HS with st_ok _ _ (setpc ?ssx ?pcx) _ =>
    pose proof (s21_chunk_rdc E ssx pcx ms (w_H W) 1 _ 16 2 (SLit 33) 33 HS eq_refl ltac:(s21_in) eq_refl
      ltac:(cbn; lia) ltac:(lia)) as H end.
  cbn [YP09.r_base base_val] in H. rewrite U24 in H. exact H. }
clear HF HFr HG.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (18%bv : bv 5) P18. prreg HS (19%bv : bv 5) P19.
prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
rewrite (EV 2%nat 2%bv) in P2 by (lia || reflexivity). rewrite (EV 3%nat 3%bv) in P3 by (lia || reflexivity).
rewrite (EV 4%nat 4%bv) in P4 by (lia || reflexivity). rewrite (EV 8%nat 8%bv) in P8 by (lia || reflexivity).
rewrite (EV 9%nat 9%bv) in P9 by (lia || reflexivity). rewrite (EV 20%nat 20%bv) in P10 by (lia || reflexivity).
rewrite (EV 20%nat 20%bv) in P20 by (lia || reflexivity). rewrite (EV 21%nat 21%bv) in P21 by (lia || reflexivity).
rewrite (EV 22%nat 22%bv) in P22 by (lia || reflexivity). rewrite (EV 24%nat 24%bv) in P24 by (lia || reflexivity).
rewrite (EV 26%nat 26%bv) in P26 by (lia || reflexivity). rewrite E32 in P19.
rewrite <- (Z_to_bv_bv_unsigned _ (ew E 250)) in P11.
rewrite (HEI 250%nat ltac:(unfold A_TEXT, A_LIM; lia)) in P11. change 250%nat with (A_OBJ 9) in P11.
rewrite (VOBJS 9%nat ltac:(cbn; lia)) in P11. match type of P11 with context [nth 9 ?l 0] => change (nth 9 l 0) with 0x21060 in P11 end.
assert (P2' : getr (ms_regs ms) 2 = w64 (x_s1 cx)) by (rewrite P2, E2; exact R2).
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp).
assert (P10' : getr (ms_regs ms) 10 = w64 mt) by (rewrite P10; exact R20).
assert (Hsp' : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (unfold spZ; rewrite P2', s21_Uw by lia; lia).
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 2868))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
(* the literal "enp1s0" at the call *)
pose proof HI as (_ & HIMG & _). destruct HIMG as (_ & _ & Hfz & _).
destruct (Hfz _ s21_lit_enp_in) as [Hlit _]. rewrite s21_lit_enp in Hlit.
destruct Hlit as (Hl0 & ((Hlz & _) & _) & Hlp & _ & Hli).
pose proof (blk_off_imgP B ly S W mem md tab _ HAR HtIn) as To. unfold off_img in To.
assert (Hlz' : sa_zs (rdW W (ms_mem ms)) 0x21060 (LLVMFuzzerTestOneInput_c.LIT_ENP ++ [0])).
{ apply (s21_zs_keep _ _ _ _ Hlz). intros i Hi. cbn in Hi. apply KC; lia. }
pose proof (proj1 HJ) as HARc.
destruct (Hlp ly S W (ms_mem ms) md1 HARc) as (Hla0 & Hla1 & Hla2 & Hla3 & Hla4).
change (Z.of_nat (length LLVMFuzzerTestOneInput_c.LIT_ENP) + 1) with 7 in Hla1, Hla2, Hla3, Hla4.
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIG SS___asan_memcpy) (AMEMCPY fx) W (ms_regs ms) (ms_mem ms)
    STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S md1 k mt 0x21060 7 (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 2868))
    HJ P10' P11 P12 ltac:(lia) ltac:(lia) ltac:(lia) Hsp' (s21_o16 _ _ N3 N1) ltac:(lia)
    ltac:(unfold ESTACK, STK_LLVMFuzzerTestOneInput; lia) P3' P4' P1 Hraw).
  - intros a Ha. split.
    + right; right; left. exists mt, (x_mtn cx). split; [exact HmtIn | split; [exact Hmtnew | lia]].
    + unfold ESTACK. lia.
  - intros a Ha (r0 & Hr0 & Hlo & Hhi). exfalso. cbn [ltoi_PG In] in Hr0.
    destruct Hr0 as [<- | []]. cbn [fst snd] in Hlo, Hhi. unfold longlA, A_LONGL, LONGL_N in *. lia.
  - exact (amem_range_of_block SEGS B LAWS ly S W mem md mt _ mt 7 HAR HmtIn ltac:(lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) md1 mt _ mt 7 HARc HmtIn ltac:(lia) ltac:(lia)).
  - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) md1 mt _ mt 7 HARc HmtIn ltac:(lia) ltac:(lia) Hpos).
  - split; [lia|]. split; [lia|]. split.
    { intros a Ha. split.
      - specialize (Hlz' (Z.to_nat (a - 0x21060)) ltac:(cbn; lia)).
        replace (0x21060 + Z.of_nat (Z.to_nat (a - 0x21060))) with a in Hlz' by lia. rewrite Hlz'. discriminate.
      - rewrite Hsp'. unfold ESTACK. lia. }
    split; [lia|]. split; [exact Hla2|]. split; [exact Hla3 | exact Hla4]. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
assert (PR : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r z Hz Hr; exact (s21_pres (ms_regs ms) regs2 r z HP2 Hz Hr)).
assert (KCP : forall a, 0 <= a < 2 ^ 64 -> ~ (mt <= a < mt + 7) -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
  rdW W mem2 a = rdW W (ms_mem ms) a).
{ intros a Ha H1 H2. apply HKC; [exact Ha | exact H1 | unfold ESTACK; lia]. }
apply (HD cx ly S W regs0 mem0 md0 k acc c m tab mt regs2 mem2 md2 HK0 HJ2).
- rewrite (PR 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P2. exact E2.
- rewrite (PR 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P3. exact E3.
- rewrite (PR 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P4. exact E4.
- rewrite (PR 8%bv 8 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P8. exact E8.
- rewrite (PR 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P9. exact E9.
- rewrite (PR 18%bv 18 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P18. reflexivity.
- rewrite (PR 19%bv 19 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P19. reflexivity.
- rewrite (PR 20%bv 20 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P20. exact R20.
- rewrite (PR 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P21. exact R21.
- rewrite (PR 22%bv 22 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P22. exact R22.
- rewrite (PR 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P24. exact R24.
- rewrite (PR 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P26. exact R26.
- exact Hfl.
- exact Hcp.
- intros a Ha Hx. rewrite KCP; [| exact Ha | intros H; apply Hx; unfold s21_Xh; tauto | intros H; apply Hx; unfold s21_Xh; tauto].
  rewrite KC; [| exact Ha | intros H; apply Hx; unfold s21_Xh; tauto]. exact (HK a Ha Hx).
- intros i Hi. rewrite KCP by lia. rewrite KC by lia. exact (Hg i Hi).
- rewrite KCP by lia. rewrite KC by lia. exact H32.
- apply (s21_zs_keep _ _ _ _ Htl). intros i Hi. cbn in Hi. rewrite KCP by lia. apply KC; lia.
- apply (s21_val_keep _ _ _ _ _ Wvid). intros i Hi. cbn in Hi. apply KCP; lia.
- intros i Hi. cbn in Hi. rewrite (HCPY (Z.of_nat i) ltac:(lia)). exact (Hlz' i ltac:(cbn; lia)).
Qed.


(* ---------------------------------- stage B: 0x857f4 .. 0x85894 or memcpy(tab) ---------------------------------- *)
Definition S21_B_stmt : Prop :=
  forall cx ly S W regs0 mem0 md0 k acc (c m tab mt : Z) regs mem md,
  s21_K0 cx ly S W regs0 mem0 md0 k acc c m tab mt ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem md k ->
  getr regs 2 = getr regs0 2 -> getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 8 = getr regs0 8 -> getr regs 9 = getr regs0 9 ->
  getr regs 18 = w64 (x_cap cx) -> getr regs 20 = w64 mt -> getr regs 21 = w64 (x_sh cx) ->
  getr regs 24 = w64 tab -> getr regs 26 = w64 (shadow_addr (m + seg_spec.MC_N)) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ s21_Xh cx tab mt a -> rdW W mem a = rdW W mem0 a) ->
  (forall i, 0 <= i < 18 -> rdW W mem (tab + 18 * x_cap cx + i) = Some (90 mod 256)) ->
  SRr SEGS W (cfg_at SEGS (BASE + S21_PB) regs mem md) (lt_post B MT cx).

Lemma s21_stageB : S21_T_stmt -> S21_C_stmt -> S21_B_stmt.
Proof.
intros HT HCs. unfold S21_B_stmt.
intros cx ly S W regs0 mem0 md0 k acc c m tab mt regs mem md HK0 HJ E2 E3 E4 E8 E9 R18 R20 R21 R24 R26 HK Hg.
pose proof pa_segs_low as Hsegs.
pose proof HK0 as (HB & HFRM & HC0 & Hc0 & Hm0 & Ht0 & Hmt0 & Hz1 & Hz2 & R26_0 & HSL0 & HCM0).
pose proof HC0 as (HF0 & HI0 & HBL0 & _).
destruct (s21_nums cx ly S W regs0 mem0 md0 k LFO0 HB HF0) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HF0 as (HJ0 & R2 & R3 & R4 & R8 & R9 & _ & _ & _ & _ & _ & H176 & _).
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof (proj1 HJ) as HAR. pose proof (proj1 HJ0) as HAR0.
pose proof (s21_EF cx ly S W regs0 mem0 md0 k LFO0 HB HF0) as EF.
pose proof Ht0 as (HtIn & _). pose proof Hmt0 as (HmtIn & _). pose proof Hm0 as (HmIn & _).
destruct (s21_X_apart cx ly S W regs0 mem0 md0 k LFO0 tab mt HB HF0 HtIn HmtIn) as (A1 & A2 & A3 & A4 & A5).
pose proof (s21_xcap_rng cx) as Hcap.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt]. pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Rm].
destruct (al_blocks _ _ LAWS ly S W mem md tab _ HAR HtIn) as (T1 & T2 & T3 & T4 & T5 & _).
destruct (al_blocks _ _ LAWS ly S W mem md mt _ HAR HmtIn) as (M1 & M2 & M3 & M4 & _).
assert (Hin3 : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Nfr; left; reflexivity).
destruct (al_frames _ _ LAWS ly S W mem md _ _ HAR Hin3) as (_ & _ & F3 & F4).
rewrite EF in F3, F4. change (fs_frame_bytes LT_FCLS) with 512 in F3, F4. change (512 / 8) with 64 in F4.
pose proof (sep_block_frame SEGS B LAWS ly S W mem md tab _ _ _ HAR HtIn Hin3) as DtF.
rewrite EF in DtF. unfold zdisjoint in DtF. cbn [fst snd] in DtF. change (fs_frame_bytes LT_FCLS) with 512 in DtF.
pose proof (sep_blocks SEGS B LAWS ly S W mem md tab _ mt _ HAR HtIn HmtIn ltac:(intros Heq; injection Heq; lia)) as Dtm.
unfold zdisjoint in Dtm. cbn [fst snd] in Dtm.
pose proof (blk_off_imgP B ly S W mem md tab _ HAR HtIn) as To. unfold off_img in To.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in T4, M4, N8.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
assert (Hsh : SHADOW_OFF <= x_sh cx < 0x10007fff8000 - 64)
  by (rewrite N9; unfold SHADOW_OFF; pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_mono (x_fr cx) 0x7fffff800000 8 ltac:(lia) ltac:(lia)); lia).
unfold SHADOW_OFF in Hsh.
assert (Htnew : ~ In (tab, x_tabn cx) (x_bl0 B cx))
  by exact (proj2 (s21_blk_new cx ly S W mem0 md0 _ tab (x_tabn cx) HAR0 HBL0 ltac:(cbn [In]; tauto))).
assert (KS : forall o v, In (o, v) (LT_L cx c m) -> o <= 88 \/ 144 <= o ->
  rdword (rdW W mem) (x_s1 cx + o) = Some v).
{ intros o v Hin Ho.
  assert (Hb : 8 <= o <= 184) by (unfold LT_L in Hin; cbn [In] in Hin;
    repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]); destruct Hin).
  apply (s21_rdword_keep _ _ _ _ (HSL0 o v ltac:(apply in_or_app; left; exact Hin))).
  intros j Hj. apply HK; [lia|]. intros Hx. apply (A4 (x_s1 cx + o + j)); [lia | exact (s21_Xh_X _ _ _ _ Hx)]. }
assert (H16 : rdword (rdW W mem) (x_s1 cx + 16) = Some (x_flags cx)) by (apply KS; [unfold LT_L; cbn [In]; tauto | lia]).
assert (H48 : rdword (rdW W mem) (x_s1 cx + 48) = Some (x_fr cx + FO_N)) by (apply KS; [unfold LT_L; cbn [In]; tauto | lia]).
assert (H168 : rdword (rdW W mem) (x_s1 cx + 168) = Some m) by (apply KS; [unfold LT_L; cbn [In]; tauto | lia]).
pose proof (s21_rdword_rng _ _ _ _ H16) as Hflr.
pose proof (s21_seedB W regs mem (x_s1 cx) (x_flags cx) (x_fr cx + FO_N) m (x_sh cx) ltac:(rewrite E9; exact R9)
  ltac:(lia) ltac:(lia) ltac:(intros o Ho; apply Hpres; unfold STK_LLVMFuzzerTestOneInput; lia) H16 H48 H168 R21
  ltac:(lia) ltac:(lia) ltac:(rewrite N9; exact (proj1 (F4 32 ltac:(lia)))) ltac:(unfold FO_N; lia) ltac:(unfold FO_N; lia)
  ltac:(intros o Ho; exact (proj1 (F3 (x_fr cx + FO_N + o) ltac:(unfold FO_N; lia))))
  ltac:(unfold FO_N; lia)) as HS.
assert (EV : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (EB regs (x_flags cx) (x_fr cx + FO_N) m) n = getr regs r) by (intros n r Hn Hr; unfold EB; apply s21_EE; assumption).
assert (HEI : img_env VAL A_LIM (EB regs (x_flags cx) (x_fr cx + FO_N) m)) by (unfold EB; apply Eimg_env).
assert (U9 : bv_unsigned (ew (EB regs (x_flags cx) (x_fr cx + FO_N) m) 9) = x_s1 cx)
  by (rewrite (EV 9%nat 9%bv) by (lia || reflexivity); rewrite E9, R9; apply s21_Uw; lia).
assert (U9s : bv_unsigned (ew (EB regs (x_flags cx) (x_fr cx + FO_N) m) 9) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (rewrite U9; lia).
assert (U18 : bv_unsigned (ew (EB regs (x_flags cx) (x_fr cx + FO_N) m) 18) = x_cap cx)
  by (rewrite (EV 18%nat 18%bv) by (lia || reflexivity); rewrite R18; apply s21_Uw; lia).
assert (U21 : bv_unsigned (ew (EB regs (x_flags cx) (x_fr cx + FO_N) m) 21) = x_sh cx)
  by (rewrite (EV 21%nat 21%bv) by (lia || reflexivity); rewrite R21; apply s21_Uw; lia).
assert (U32 : bv_unsigned (ew (EB regs (x_flags cx) (x_fr cx + FO_N) m) 32) = x_flags cx)
  by (unfold EB; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth]; apply s21_Uw; lia).
assert (U33 : bv_unsigned (ew (EB regs (x_flags cx) (x_fr cx + FO_N) m) 33) = x_fr cx + FO_N)
  by (unfold EB; rewrite (s21_EX regs _ 1 33) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth]; apply s21_Uw;
      unfold FO_N; lia).
assert (E34 : ew (EB regs (x_flags cx) (x_fr cx + FO_N) m) 34 = w64 m)
  by (unfold EB; rewrite (s21_EX regs _ 2 34) by (reflexivity || (unfold A_TEXT; lia)); reflexivity).
set (E := EB regs (x_flags cx) (x_fr cx + FO_N) m) in *. clearbody E.
unfold cfg_at. change (w64 (BASE + S21_PB)) with (Z_to_bv 64 (BASE + S21_PB)).
(* the three windows of B *)
Ltac s21_KB cx U9 U21 U33 HFr :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hna := fresh "Hna" in
  intros a Ha Hna;
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (s21_WB cx) HFr); [|exact Ha | exact Hna];
  let b := fresh "b" in let wlo := fresh "wlo" in let whi := fresh "whi" in let a' := fresh "a'" in
  let Hin := fresh "Hin" in let Hrr := fresh "Hrr" in let Hq0 := fresh "Hq0" in
  intros b wlo whi a' Hin Hrr; vm_compute in Hin; unfold s21_WB, FO_N in *;
  destruct Hin as [Hq0 | [Hq0 | [Hq0 | []]]]; injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
    [rewrite U9 in Hrr | rewrite U21 in Hrr | rewrite U33 in Hrr]; lia.
(* 0x857f4 .. 0x85814: 120(s1) := 0, n's shadow byte := 4, n := 0, s6 := mt + 16; beqz (flags & 1) *)
paj_run_sh RUNP HS HJ.
{ s21_awrB cx U9s U21 U33 EF. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (KB1 : forall a, 0 <= a < 2 ^ 64 -> ~ s21_WB cx a -> rdW W (ms_mem ms) a = rdW W mem a)
  by (s21_KB cx U9 U21 U33 HFr).
clear HF HFr HG. rename ms into ms1.
(* the facts of the state 0x85894 the two arrivals with no entry share *)
assert (U20 : bv_unsigned (ew E 20) = mt) by (rewrite (EV 20%nat 20%bv) by (lia || reflexivity); rewrite R20; apply s21_Uw; lia).
psrr_branch_pi RUNP BR HS.
- (* flags & 1 = 0: 0x85890 a6 := m, to 0x85894 *)
  rewrite (s21_beq_and1 E (x_flags cx) U32 Hflr) in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_sh RUNTOP HS HJ S21_PT.
  { s21_awrB cx U9s U21 U33 EF. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  assert (KB2 : forall a, 0 <= a < 2 ^ 64 -> ~ s21_WB cx a -> rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a)
    by (s21_KB cx U9 U21 U33 HFr).
  clear HF HFr HG.
  assert (W120 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 120) = Some 0)
    by (eapply (s21_slot_rd E _ ms (w_H W) _ 120 (SLit 0) 0 (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | reflexivity | lia]).
  assert (W32 : rdW W (ms_mem ms) (x_sh cx + 32) = Some 4).
  { pose proof (s21_chunk_rdi E _ ms (w_H W) 1 _ 32 1 (SLit 4) 4 HS eq_refl ltac:(s21_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as H.
    cbn [YP09.r_base base_val] in H. rewrite U21 in H. specialize (H 0%nat ltac:(lia)). rewrite Z.add_0_r in H. exact H. }
  assert (Wn : sa_val (rdW W (ms_mem ms)) (x_fr cx + FO_N) 4 0).
  { pose proof (s21_chunk_rdi E _ ms (w_H W) 2 _ 0 4 (SLit 0) 0 HS eq_refl ltac:(s21_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as H.
    cbn [YP09.r_base base_val] in H. rewrite U33, Z.add_0_r in H. exact H. }
  pmkst HS.
  prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
  prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (16%bv : bv 5) P16.
  prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
  prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
  apply (s21_BtoT HT cx ly S W regs0 mem0 md0 k acc c m tab mt mem (ms_regs ms) (ms_mem ms) md2 HK0 HJ).
  + rewrite P2, (EV 2%nat 2%bv) by (lia || reflexivity). exact E2.
  + rewrite P3, (EV 3%nat 3%bv) by (lia || reflexivity). exact E3.
  + rewrite P4, (EV 4%nat 4%bv) by (lia || reflexivity). exact E4.
  + rewrite P8, (EV 8%nat 8%bv) by (lia || reflexivity). exact E8.
  + rewrite P9, (EV 9%nat 9%bv) by (lia || reflexivity). exact E9.
  + rewrite P16. exact E34.
  + rewrite P20, (EV 20%nat 20%bv) by (lia || reflexivity). exact R20.
  + rewrite P21, (EV 21%nat 21%bv) by (lia || reflexivity). exact R21.
  + rewrite P22, U20. reflexivity.
  + rewrite P24, (EV 24%nat 24%bv) by (lia || reflexivity). exact R24.
  + rewrite P26, (EV 26%nat 26%bv) by (lia || reflexivity). exact R26.
  + exact (s21_tab0_nil_f cx Hc).
  + exact HK.
  + exact Hg.
  + intros a Ha Hw. rewrite KB2 by assumption. exact (KB1 a Ha Hw).
  + exact W32.
  + exact W120.
  + exact Wn.
- (* flags & 1 <> 0: 0x85818 a6 := m; beqz cap *)
  rewrite (s21_beq_and1 E (x_flags cx) U32 Hflr) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hfl.
  paj_run_sh RUNP HS HJ.
  { s21_awrB cx U9s U21 U33 EF. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
  assert (KB2 : forall a, 0 <= a < 2 ^ 64 -> ~ s21_WB cx a -> rdW W (ms_mem ms) a = rdW W (ms_mem ms1) a)
    by (s21_KB cx U9 U21 U33 HFr).
  clear HF HFr HG. rename ms into ms2.
  psrr_branch_pi RUNP BR HS.
  + (* cap = 0: to 0x85894 *)
    rewrite (s21_beq_atom E 18 (x_cap cx) U18 ltac:(lia)) in Hc. apply Z.eqb_eq in Hc.
    paj_run_to_sh RUNTOP HS HJ S21_PT.
    { s21_awrB cx U9s U21 U33 EF. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
    assert (KB3 : forall a, 0 <= a < 2 ^ 64 -> ~ s21_WB cx a -> rdW W (ms_mem ms) a = rdW W (ms_mem ms2) a)
      by (s21_KB cx U9 U21 U33 HFr).
    clear HF HFr HG.
    assert (W120 : rdword (rdW W (ms_mem ms)) (x_s1 cx + 120) = Some 0)
      by (eapply (s21_slot_rd E _ ms (w_H W) _ 120 (SLit 0) 0 (x_s1 cx) HS); [s21_in | reflexivity | exact U9 | s21_in | reflexivity | lia]).
    assert (W32 : rdW W (ms_mem ms) (x_sh cx + 32) = Some 4).
    { pose proof (s21_chunk_rdi E _ ms (w_H W) 1 _ 32 1 (SLit 4) 4 HS eq_refl ltac:(s21_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as H.
      cbn [YP09.r_base base_val] in H. rewrite U21 in H. specialize (H 0%nat ltac:(lia)). rewrite Z.add_0_r in H. exact H. }
    assert (Wn : sa_val (rdW W (ms_mem ms)) (x_fr cx + FO_N) 4 0).
    { pose proof (s21_chunk_rdi E _ ms (w_H W) 2 _ 0 4 (SLit 0) 0 HS eq_refl ltac:(s21_in) eq_refl ltac:(cbn; lia) ltac:(lia)) as H.
      cbn [YP09.r_base base_val] in H. rewrite U33, Z.add_0_r in H. exact H. }
    pmkst HS.
    prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (16%bv : bv 5) P16.
    prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
    prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
    apply (s21_BtoT HT cx ly S W regs0 mem0 md0 k acc c m tab mt mem (ms_regs ms) (ms_mem ms) md3 HK0 HJ).
    * rewrite P2, (EV 2%nat 2%bv) by (lia || reflexivity). exact E2.
    * rewrite P3, (EV 3%nat 3%bv) by (lia || reflexivity). exact E3.
    * rewrite P4, (EV 4%nat 4%bv) by (lia || reflexivity). exact E4.
    * rewrite P8, (EV 8%nat 8%bv) by (lia || reflexivity). exact E8.
    * rewrite P9, (EV 9%nat 9%bv) by (lia || reflexivity). exact E9.
    * rewrite P16. exact E34.
    * rewrite P20, (EV 20%nat 20%bv) by (lia || reflexivity). exact R20.
    * rewrite P21, (EV 21%nat 21%bv) by (lia || reflexivity). exact R21.
    * rewrite P22, U20. reflexivity.
    * rewrite P24, (EV 24%nat 24%bv) by (lia || reflexivity). exact R24.
    * rewrite P26, (EV 26%nat 26%bv) by (lia || reflexivity). exact R26.
    * exact (s21_tab0_nil_c cx Hc).
    * exact HK.
    * exact Hg.
    * intros a Ha Hw. rewrite KB3 by assumption. rewrite KB2 by assumption. exact (KB1 a Ha Hw).
    * exact W32.
    * exact W120.
    * exact Wn.
  + (* cap <> 0: 0x85820 .. memcpy(tab, "enp1s0", 7) *)
    rewrite (s21_beq_atom E 18 (x_cap cx) U18 ltac:(lia)) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hcp.
    paj_run_shc RUNP RUNC HS HJ.
    { s21_awrB cx U9s U21 U33 EF. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
    assert (KB3 : forall a, 0 <= a < 2 ^ 64 -> ~ s21_WB cx a -> rdW W (ms_mem ms) a = rdW W (ms_mem ms2) a)
      by (s21_KB cx U9 U21 U33 HFr).
    assert (KB123 : forall a, 0 <= a < 2 ^ 64 -> ~ s21_WB cx a -> rdW W (ms_mem ms) a = rdW W mem a)
      by (intros a Ha Hw; rewrite KB3, KB2 by assumption; exact (KB1 a Ha Hw)).
    assert (W32 : rdW W (ms_mem ms) (x_sh cx + 32) = Some 4).
    { lazymatch type of HS with
      | st_ok _ _ ?ssx _ =>
        pose proof (s21_chunk_rdo E ssx ms (w_H W) 1 _ 32 1 (SLit 4) 4 HS eq_refl ltac:(s21_in) eq_refl
          ltac:(cbn; lia) ltac:(lia)) as H
      | st_ok_pi _ _ _ ?ssx _ =>
        pose proof (s21_chunk_rdi E ssx ms (w_H W) 1 _ 32 1 (SLit 4) 4 HS eq_refl ltac:(s21_in) eq_refl
          ltac:(cbn; lia) ltac:(lia)) as H
      end.
      cbn [YP09.r_base base_val] in H. rewrite U21 in H. specialize (H 0%nat ltac:(lia)). rewrite Z.add_0_r in H. exact H. }
    clear HF HFr HG.
    pmkst HS.
    prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
    prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
    prreg HS (12%bv : bv 5) P12.
    prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21. prreg HS (22%bv : bv 5) P22.
    prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
    rewrite (EV 2%nat 2%bv) in P2 by (lia || reflexivity). rewrite (EV 3%nat 3%bv) in P3 by (lia || reflexivity).
    rewrite (EV 4%nat 4%bv) in P4 by (lia || reflexivity). rewrite (EV 8%nat 8%bv) in P8 by (lia || reflexivity).
    rewrite (EV 9%nat 9%bv) in P9 by (lia || reflexivity). rewrite (EV 24%nat 24%bv) in P10 by (lia || reflexivity).
    rewrite (EV 20%nat 20%bv) in P20 by (lia || reflexivity). rewrite (EV 21%nat 21%bv) in P21 by (lia || reflexivity).
    rewrite (EV 24%nat 24%bv) in P24 by (lia || reflexivity).
    rewrite (EV 26%nat 26%bv) in P26 by (lia || reflexivity).
    rewrite <- (Z_to_bv_bv_unsigned _ (ew E 250)) in P11.
    rewrite (HEI 250%nat ltac:(unfold A_TEXT, A_LIM; lia)) in P11. change 250%nat with (A_OBJ 9) in P11.
    rewrite (VOBJS 9%nat ltac:(cbn; lia)) in P11. match type of P11 with context [nth 9 ?l 0] => change (nth 9 l 0) with 0x21060 in P11 end.
    assert (P22' : getr (ms_regs ms) 22 = w64 (mt + 16)) by (rewrite P22, U20; reflexivity).
    assert (P2' : getr (ms_regs ms) 2 = w64 (x_s1 cx)) by (rewrite P2, E2; exact R2).
    assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, E3, R3; exact Hgp).
    assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, E4, R4; exact Htp).
    assert (P10' : getr (ms_regs ms) 10 = w64 tab) by (rewrite P10; exact R24).
    assert (Hsp' : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (unfold spZ; rewrite P2', s21_Uw by lia; lia).
    assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 2816))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
    (* the literal "enp1s0" at the call *)
    assert (HIc : lt_img B cx (rdW W (ms_mem ms))).
    { apply (s21_img_keep cx (w_H W) mem0 (w_H W) (ms_mem ms) HI0). intros x Hx.
      assert (Hx0 : ~ s21_X cx tab mt x) by exact (A1 x Hx).
      assert (Hx1 : ~ s21_Xh cx tab mt x) by (intros Hq; exact (Hx0 (s21_Xh_X _ _ _ _ Hq))).
      unfold kImgEnd in Hx. rewrite KB123; [| lia | intros Hw; exact (Hx1 (s21_WB_Xh _ _ _ _ Hw))].
      apply HK; [lia | exact Hx1]. }
    pose proof HIc as (_ & HIMG & _). destruct HIMG as (_ & _ & Hfz & _).
    destruct (Hfz _ s21_lit_enp_in) as [Hlit _]. rewrite s21_lit_enp in Hlit.
    destruct Hlit as (Hl0 & ((Hlz & _) & _) & Hlp & _ & Hli).
    pose proof (proj1 HJ) as HARc.
    destruct (Hlp ly S W (ms_mem ms) md3 HARc) as (Hla0 & Hla1 & Hla2 & Hla3 & Hla4).
    change (Z.of_nat (length LLVMFuzzerTestOneInput_c.LIT_ENP) + 1) with 7 in Hla1, Hla2, Hla3, Hla4.
    eapply SRr_bind.
    { apply (aj_intrin_atS SEGS B LAWS Hsegs OCpy (SIG SS___asan_memcpy) (AMEMCPY fx) W (ms_regs ms) (ms_mem ms)
        STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
        [(LT_FCLS, x_fpos cx)] ly S md3 k tab 0x21060 7 (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 2816))
        HJ P10' P11 P12 ltac:(lia) ltac:(lia) ltac:(lia) Hsp' (s21_o16 _ _ N3 N1) ltac:(lia)
        ltac:(unfold ESTACK, STK_LLVMFuzzerTestOneInput; lia) P3' P4' P1 Hraw).
      - intros a Ha. split.
        + right; right; left. exists tab, (x_tabn cx). split; [exact HtIn | split; [exact Htnew | lia]].
        + unfold ESTACK. lia.
      - intros a Ha (r0 & Hr0 & Hlo & Hhi). exfalso. cbn [ltoi_PG In] in Hr0.
        destruct Hr0 as [<- | []]. cbn [fst snd] in Hlo, Hhi. unfold longlA, A_LONGL, LONGL_N in *. lia.
      - exact (amem_range_of_block SEGS B LAWS ly S W mem md tab _ tab 7 HAR HtIn ltac:(lia) ltac:(lia)).
      - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) md3 tab _ tab 7 HARc HtIn ltac:(lia) ltac:(lia)).
      - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) md3 tab _ tab 7 HARc HtIn ltac:(lia) ltac:(lia) Hpos).
      - split; [lia|]. split; [lia|]. split.
        { intros a Ha. split.
          - specialize (Hlz (Z.to_nat (a - 0x21060)) ltac:(cbn; lia)).
            replace (0x21060 + Z.of_nat (Z.to_nat (a - 0x21060))) with a in Hlz by lia. rewrite Hlz. discriminate.
          - rewrite Hsp'. unfold ESTACK. lia. }
        split; [lia|]. split; [exact Hla2|]. split; [exact Hla3 | exact Hla4]. }
    cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md4 & -> & HJ2 & HP2 & H10b & HCPY & HKC & HPRS & HSAME).
    assert (PR : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
      by (intros r z Hz Hr; exact (s21_pres (ms_regs ms) regs2 r z HP2 Hz Hr)).
    assert (KCP : forall a, 0 <= a < 2 ^ 64 -> ~ (tab <= a < tab + 7) -> ~ (x_s1 cx - 4096 <= a < x_s1 cx) ->
      rdW W mem2 a = rdW W (ms_mem ms) a).
    { intros a Ha H1 H2. apply HKC; [exact Ha | exact H1 | unfold ESTACK; lia]. }
    apply (HCs cx ly S W regs0 mem0 md0 k acc c m tab mt regs2 mem2 md4 HK0 HJ2).
    * rewrite (PR 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P2. exact E2.
    * rewrite (PR 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P3. exact E3.
    * rewrite (PR 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P4. exact E4.
    * rewrite (PR 8%bv 8 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P8. exact E8.
    * rewrite (PR 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P9. exact E9.
    * rewrite (PR 20%bv 20 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P20. exact R20.
    * rewrite (PR 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P21. exact R21.
    * rewrite (PR 22%bv 22 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P22'.
    * rewrite (PR 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P24. exact R24.
    * rewrite (PR 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P26. exact R26.
    * exact Hfl.
    * exact Hcp.
    * intros a Ha Hx.
      rewrite KCP; [| exact Ha | intros H; apply Hx; unfold s21_Xh; tauto | intros H; apply Hx; unfold s21_Xh; tauto].
      rewrite KB123; [| exact Ha | intros Hw; exact (Hx (s21_WB_Xh _ _ _ _ Hw))]. exact (HK a Ha Hx).
    * intros i Hi. rewrite KCP by lia. rewrite KB123; [exact (Hg i Hi) | lia |].
      apply (s21_WB_blk cx ly S W regs0 mem0 md0 k LFO0 tab (x_tabn cx)); [exact HB | exact HF0 | exact HtIn | lia].
    * rewrite KCP by lia. exact W32.
    * intros i Hi. cbn in Hi. rewrite (HCPY (Z.of_nat i) ltac:(lia)). exact (Hlz i ltac:(cbn; lia)).
Qed.


(* ---------------------------------- the seed of A, at 0x857cc ---------------------------------- *)
Lemma s21_seedA : forall (W : world SEGS) regs mem s1 tab mt sh,
  getr regs 9 = w64 s1 -> 70368744177664 <= s1 -> s1 + 192 <= 140737488355328 -> s1 mod 32 = 0 ->
  rdword (rdW W mem) (s1 + 144) = Some sh ->
  getr regs 24 = w64 tab -> 4096 <= tab -> tab mod 16 = 0 -> tab <= 140737479966720 ->
  getr regs 10 = w64 mt -> 4096 <= mt -> mt mod 16 = 0 -> mt <= 140737479966720 ->
  st_ok_pi SEGS VAL (EA regs sh) ssA0 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K857cc)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 tab mt sh R9 Hs1a Hs1b Hs132 H144 R24 Ht1 Ht16 Ht2 R10 Hm1 Hm16 Hm2.
set (E := EA regs sh).
assert (U9 : bv_unsigned (ew E 9) = s1)
  by (subst E; unfold EA; rewrite (s21_EE regs _ 9 9%bv) by (lia || reflexivity); rewrite R9; apply s21_Uw; lia).
assert (U24 : bv_unsigned (ew E 24) = tab)
  by (subst E; unfold EA; rewrite (s21_EE regs _ 24 24%bv) by (lia || reflexivity); rewrite R24; apply s21_Uw; lia).
assert (U10 : bv_unsigned (ew E 10) = mt)
  by (subst E; unfold EA; rewrite (s21_EE regs _ 10 10%bv) by (lia || reflexivity); rewrite R10; apply s21_Uw; lia).
assert (U32 : bv_unsigned (ew E 32) = sh)
  by (subst E; unfold EA; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); cbn [nth];
      apply s21_Uw; exact (s21_rdword_rng _ _ _ _ H144)).
unfold ssA0. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. unfold EA. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rA. repeat apply Forall_cons; try apply Forall_nil; unfold YP09.region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  apply (s21_chunk8 E (w_H W) mem s1 144 (SOff 32 0) sh); [|exact H144]. cbn [sv_denot]. rewrite U32, Z.add_0_r. reflexivity.
- apply pairwise_disjoint_of_extents. unfold rA, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [base_val]. rewrite U9.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; try exact I; zl.
- split; [|split; [exact I | exact I]].
  cbn [fA f_atoms atoms_ok]. unfold afact_ok, S21_S1F, HPTR. cbn [af_lo af_hi af_al2].
  rewrite U9, U24, U10.
  change (2 ^ 5) with 32. change (2 ^ 4) with 16.
  repeat match goal with |- _ /\ _ => split end; first [exact I | reflexivity | lia].
Qed.

(* ---------------------------------- stage A: 0x857cc .. memset(&tab[cap], 0x5a, 18) ---------------------------------- *)
Lemma s21_stageA : S21_B_stmt -> LT_K857cc_stmt B MT.
Proof.
intros HBs. unfold LT_K857cc_stmt.
intros cx ly S W regs mem md k acc c m tab mt HB HFRM HC Hc Hm Ht Hmt Hz1 Hz2 R10 R18 R24 R26 HSL HCM.
assert (HK0 : s21_K0 cx ly S W regs mem md k acc c m tab mt)
  by exact (conj HB (conj HFRM (conj HC (conj Hc (conj Hm (conj Ht (conj Hmt (conj Hz1 (conj Hz2 (conj R26 (conj HSL HCM))))))))))).
pose proof pa_segs_low as Hsegs.
pose proof HC as (HFm & HI & HBL & _).
destruct (s21_nums cx ly S W regs mem md k LFO0 HB HFm) as (N1 & N2 & N3 & N4 & Nfr & N5 & N6 & N7 & N8 & N9 & N10).
pose proof HFm as (HJ & R2 & R3 & R4 & R8 & R9 & _).
pose proof HB as (HPRE & _). pose proof HPRE as (_ & _ & _ & Hgp & Htp & _).
pose proof (proj1 HJ) as HAR.
pose proof Ht as (HtIn & _). pose proof Hmt as (HmtIn & _).
pose proof (s21_xcap_rng cx) as Hcap.
assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
pose proof (req_size_pos (x_tabn cx) ltac:(lia)) as [_ Rt]. pose proof (req_size_pos (x_mtn cx) ltac:(lia)) as [_ Rm].
destruct (al_blocks _ _ LAWS ly S W mem md tab _ HAR HtIn) as (T1 & T2 & T3 & T4 & T5 & _).
destruct (al_blocks _ _ LAWS ly S W mem md mt _ HAR HmtIn) as (M1 & M2 & M3 & M4 & _).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in T4, M4, N8.
assert (Htnew : ~ In (tab, x_tabn cx) (x_bl0 B cx))
  by exact (proj2 (s21_blk_new cx ly S W mem md _ tab (x_tabn cx) HAR HBL ltac:(cbn [In]; tauto))).
assert (H144 : rdword (rdW W mem) (x_s1 cx + 144) = Some (x_sh cx))
  by (apply HSL; apply in_or_app; left; unfold LT_L; cbn [In]; tauto).
pose proof (s21_seedA W regs mem (x_s1 cx) tab mt (x_sh cx) R9 ltac:(lia) ltac:(lia) N3 H144 R24 T2 T1 ltac:(lia)
  R10 M2 M1 ltac:(lia)) as HS.
assert (EV : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (EA regs (x_sh cx)) n = getr regs r) by (intros n r Hn Hr; unfold EA; apply s21_EE; assumption).
assert (HEI : img_env VAL A_LIM (EA regs (x_sh cx))) by (unfold EA; apply Eimg_env).
assert (U9 : bv_unsigned (ew (EA regs (x_sh cx)) 9) = x_s1 cx)
  by (rewrite (EV 9%nat 9%bv) by (lia || reflexivity); rewrite R9; apply s21_Uw; lia).
assert (U24 : bv_unsigned (ew (EA regs (x_sh cx)) 24) = tab)
  by (rewrite (EV 24%nat 24%bv) by (lia || reflexivity); rewrite R24; apply s21_Uw; lia).
assert (U10 : bv_unsigned (ew (EA regs (x_sh cx)) 10) = mt)
  by (rewrite (EV 10%nat 10%bv) by (lia || reflexivity); rewrite R10; apply s21_Uw; lia).
assert (U18 : bv_unsigned (ew (EA regs (x_sh cx)) 18) = x_cap cx)
  by (rewrite (EV 18%nat 18%bv) by (lia || reflexivity); rewrite R18; apply s21_Uw; lia).
assert (E32 : ew (EA regs (x_sh cx)) 32 = w64 (x_sh cx))
  by (unfold EA; rewrite (s21_EX regs _ 0 32) by (reflexivity || (unfold A_TEXT; lia)); reflexivity).
set (E := EA regs (x_sh cx)) in *. clearbody E.
unfold cfg_at. change (w64 (BASE + LO_K857cc)) with (Z_to_bv 64 (BASE + LO_K857cc)).
(* 0x857cc .. 0x857f0: s5 := SH(FR); the NULL tests of tab and mt; a0 := tab + 18 cap, a1 := 0x5a, a2 := 18 *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?E0 ?rs ?stk ?sp0 ?fp ?b0 ?bc ?fr ?ly0 ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb E0 rs' stk sp0 fp b0 bc fr ly0 own) end.
  apply awr_ok_cons_ro; [cbn; lia|]. apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
assert (KA : forall a, 0 <= a < 2 ^ 64 -> rdW W (ms_mem ms) a = rdW W mem a).
{ intros a Ha.
  apply (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr); [|exact Ha | intros []].
  intros b wlo whi a' Hin Hrr. vm_compute in Hin.
  destruct Hin as [Hq0 | []]; injection Hq0 as <- <- <-; lia. }
clear HF HFr HG.
s21_reg HS (10%bv : bv 5) P10.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3. prreg HS (4%bv : bv 5) P4.
prreg HS (8%bv : bv 5) P8. prreg HS (9%bv : bv 5) P9. prreg HS (11%bv : bv 5) P11.
prreg HS (12%bv : bv 5) P12. prreg HS (18%bv : bv 5) P18.
prreg HS (20%bv : bv 5) P20. prreg HS (21%bv : bv 5) P21.
prreg HS (24%bv : bv 5) P24. prreg HS (26%bv : bv 5) P26.
rewrite (EV 2%nat 2%bv) in P2 by (lia || reflexivity). rewrite (EV 3%nat 3%bv) in P3 by (lia || reflexivity).
rewrite (EV 4%nat 4%bv) in P4 by (lia || reflexivity). rewrite (EV 8%nat 8%bv) in P8 by (lia || reflexivity).
rewrite (EV 9%nat 9%bv) in P9 by (lia || reflexivity). rewrite (EV 18%nat 18%bv) in P18 by (lia || reflexivity).
rewrite (EV 10%nat 10%bv) in P20 by (lia || reflexivity). rewrite E32 in P21.
rewrite (EV 24%nat 24%bv) in P24 by (lia || reflexivity). rewrite (EV 26%nat 26%bv) in P26 by (lia || reflexivity).
assert (P10' : getr (ms_regs ms) 10 = w64 (tab + 18 * x_cap cx)).
{ rewrite P10. change (w64 (tab + 18 * x_cap cx)) with (sv_denot E (SLit (tab + 18 * x_cap cx))). apply U_inj.
  rewrite U_SAlu, U_SMd, !U_SOff, !U_SLit, U18, U24, !Z.add_0_r. cbn [zalu_raw zmd_raw].
  rewrite (zcanon_small (x_cap cx)) by lia. change (zcanon 18) with 18.
  rewrite (zcanon_small (x_cap cx * 18)) by lia. rewrite (zcanon_small tab) by lia.
  replace (x_cap cx * 18 + tab) with (tab + 18 * x_cap cx) by lia. reflexivity. }
assert (P2' : getr (ms_regs ms) 2 = w64 (x_s1 cx)) by (rewrite P2; exact R2).
assert (P3' : getr (ms_regs ms) 3 = w64 (as_gp B)) by (rewrite P3, R3; exact Hgp).
assert (P4' : getr (ms_regs ms) 4 = w64 (as_tp B)) by (rewrite P4, R4; exact Htp).
assert (Hsp' : spZ (ms_regs ms) = x_sp0 cx + (x_s1 cx - x_sp0 cx)) by (unfold spZ; rewrite P2', s21_Uw by lia; lia).
assert (Hraw : YK0s.ret_ok (Z_to_bv 64 (BASE + 2752))) by (apply ret_ok_codeptr_v; [lia | reflexivity]).
pose proof (blk_off_imgP B ly S W mem md tab _ HAR HtIn) as To. unfold off_img in To.
pose proof (proj1 HJ) as HARc.
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS Hsegs OSet (SIG SS___asan_memset) (AMEMSET fx) W (ms_regs ms) (ms_mem ms)
    STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx)
    [(LT_FCLS, x_fpos cx)] ly S md1 k (tab + 18 * x_cap cx) 90 18 (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 2752))
    HJ P10' P11 P12 ltac:(lia) ltac:(lia) ltac:(lia) Hsp' (s21_o16 _ _ N3 N1) ltac:(lia)
    ltac:(unfold ESTACK, STK_LLVMFuzzerTestOneInput; lia) P3' P4' P1 Hraw).
  - intros a Ha. split.
    + right; right; left. exists tab, (x_tabn cx). split; [exact HtIn | split; [exact Htnew | lia]].
    + unfold ESTACK. lia.
  - intros a Ha (r0 & Hr0 & Hlo & Hhi). exfalso. cbn [ltoi_PG In] in Hr0.
    destruct Hr0 as [<- | []]. cbn [fst snd] in Hlo, Hhi. unfold longlA, A_LONGL, LONGL_N in *. lia.
  - exact (amem_range_of_block SEGS B LAWS ly S W mem md tab _ (tab + 18 * x_cap cx) 18 HAR HtIn ltac:(lia) ltac:(lia)).
  - exact (range_addressable_of_block SEGS B LAWS ly S W (ms_mem ms) md1 tab _ (tab + 18 * x_cap cx) 18 HARc HtIn
      ltac:(lia) ltac:(lia)).
  - intros Hpos. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W (ms_mem ms) md1 tab _ (tab + 18 * x_cap cx) 18 HARc
      HtIn ltac:(lia) ltac:(lia) Hpos).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10b & HSET & HKS & HPRS & HSAME).
assert (PR : forall (r : bv 5) z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
  by (intros r z Hz Hr; exact (s21_pres (ms_regs ms) regs2 r z HP2 Hz Hr)).
apply (HBs cx ly S W regs mem md k acc c m tab mt regs2 mem2 md2 HK0 HJ2).
- rewrite (PR 2%bv 2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P2.
- rewrite (PR 3%bv 3 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P3.
- rewrite (PR 4%bv 4 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P4.
- rewrite (PR 8%bv 8 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P8.
- rewrite (PR 9%bv 9 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P9.
- rewrite (PR 18%bv 18 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P18. exact R18.
- rewrite (PR 20%bv 20 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P20. exact R10.
- rewrite (PR 21%bv 21 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)). exact P21.
- rewrite (PR 24%bv 24 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P24. exact R24.
- rewrite (PR 26%bv 26 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)), P26. exact R26.
- intros a Ha Hx.
  rewrite HKS; [exact (KA a Ha) | exact Ha | intros H; apply Hx; unfold s21_Xh; left; lia |
    intros H; apply Hx; unfold s21_Xh, ESTACK in *; right; left; lia].
- intros i Hi. exact (HSET i Hi).
Qed.

(* ============================================ the segment ============================================ *)
Theorem lt_seg_S13 : lt_seg_S13_stmt B MT.
Proof.
unfold lt_seg_S13_stmt. intros HK0 HBD.
pose proof (s21_tail HK0 HBD) as HT.
exact (s21_stageA (s21_stageB HT (s21_stageC (s21_stageD HT)))).
Qed.


End e.
End f.
End d.
