(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require IConj.
Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.IConj.
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require RefMemcpyLib FuzzMem U7MemcpyBase U7Memcpy U7AdlerBase U7AdlerIface U7Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require U7LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require TBase T_U2C T_U2A T_It1.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Inftrees InftreesCoverage ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require ZTac ZMem ZCall ZCallL ZArr ZArr4 IDefs ISpecs ITac.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7S Require S_It0 S_It3 S_It4 S_It5 S_It6.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require Base T_It2.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require T_TokI. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U.T_TokI.




From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require T_Fast2.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require InflateInvTab.

From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require T_TokF. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U.T_TokF.







From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Frame Hoare.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RefMemcpyLib FuzzMem U7MemcpyBase U7Memcpy U7AdlerBase U7AdlerIface U7Adler.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import U7LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require Import TBase. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require T_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U.T_U2C.T_LeaveA. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require Import T_U2A. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require T_U2C. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U.T_U2C.T_U2B. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require Import T_U2C T_It1. Import T_It7. From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U Require T_Fast2. Import OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.I7U.T_Fast2.T_Fast1. Import T_Fast7.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.


Lemma w64_lit : forall z (w : word), bv_unsigned w = z -> w64 z = w.
Proof. intros z w <-. apply w64_of_word. Qed.

Lemma msteps_memcpy_U7 {RCa1 : RunCtx}  : msteps_memcpy (run_segments R_segs rc_inp rc_sp rc_mb) A_MEMCPY.
Proof.
  intros mem0 dst src n bs rom Hn Hlen Hsrc Hdst Hdisj Hnws Hnwd regs ret Hret H1 H10 H11 H12.
  unfold A_MEMCPY. rewrite (w64_lit 136304 (0x21470%bv : word)) by reflexivity.
  apply (ref_memcpy mem0 dst src n bs rom); try assumption.
  constructor; assumption.
Qed.
Theorem memcpy_ok_t {RCa1 : RunCtx}  : memcpy_spec_t.
Proof. unfold memcpy_spec_t. apply memcpy_glue. apply msteps_memcpy_U7. Qed.

Lemma img_ok_of_rom_ok : forall m, rom_ok m -> img_ok m.
Proof.
  intros m H. apply (img_ok_of_range m ROM_LO ROM_HI).
  - apply rom_hyp_of_okG; [cbv [ROM_LO]; lia_std | rewrite two64_eq; cbv [ROM_HI]; lia_std | exact H].
  - cbv [ROM_LO RO_LO]. lia_std.
  - cbv [ROM_HI RO_HI]. lia_std.
Qed.
Lemma msteps_adler32_U7 {RCa1 : RunCtx}  : msteps_adler32 (run_segments R_segs rc_inp rc_sp rc_mb) A_ADLER32 FR_AD rom_ok.
Proof.
  intros regs m rom retw usp a adr v len. unfold A_ADLER32, FR_AD. rewrite (w64_lit 99024 (0x182d0%bv : word)) by reflexivity.
  intros. eapply (u7_adler32 regs m rom retw usp a adr v len); try eassumption. apply img_ok_of_rom_ok. assumption.
Qed.
Theorem adler32_ok_t {RCa1 : RunCtx}  : adler32_spec_t.
Proof. unfold adler32_spec_t. apply adler32_glue; [cbv [FR_AD]; lia_std | apply msteps_adler32_U7]. Qed.

Lemma msteps_adler32_null_U7 {RCa1 : RunCtx}  : msteps_adler32_nullF (run_segments R_segs rc_inp rc_sp rc_mb) A_ADLER32 FR_AD.
Proof.
  intros regs m rom retw usp. unfold A_ADLER32, FR_AD. rewrite (w64_lit 99024 (0x182d0%bv : word)) by reflexivity.
  intros. eapply (u7_adler32_null regs m rom retw usp); try eassumption.
Qed.
Theorem adler32_null_ok_t {RCa1 : RunCtx}  : adler32_null_spec_t.
Proof. unfold adler32_null_spec_t. apply adler32_nullF_glue; [cbv [FR_AD]; lia_std | apply msteps_adler32_null_U7]. Qed.

Theorem itable_ok_t {RCa1 : RunCtx}  : itable_spec_t.
Proof. exact itable_t. Qed.
Theorem ifast_ok_t {RCa1 : RunCtx}  : ifast_spec_t.
Proof. exact ifast_t. Qed.

Section Local.
Context {RCa1 : RunCtx}.
Variable P : word -> Prop.
Variables M M' : mem.
Hypothesis AG : forall x, P x -> M' x = M x.

Lemma mem_is_local : forall a bs,
  (forall x : word, a <= bv_unsigned x < a + Z.of_nat (length bs) -> P x) ->
  0 <= a -> a + Z.of_nat (length bs) <= two64 ->
  mem_is (run_segments R_segs rc_inp rc_sp rc_mb) M a bs -> mem_is (run_segments R_segs rc_inp rc_sp rc_mb) M' a bs.
Proof.
  intros a bs HP Ha Hn H. unfold mem_is in *.
  destruct bs as [|b bs']; [exact H|].
  assert (Ha' : bv_unsigned (w64 a) = a).
  { rewrite w64_unsigned, mod_small_u64; [reflexivity|]. cbn [length] in Hn. lia_std. }
  rewrite (rdn_ext (run_segments R_segs rc_inp rc_sp rc_mb) (length (b :: bs')) M' M (w64 a)); [exact H | |].
  - rewrite Ha'. rewrite <- two64_eq. exact Hn.
  - intros x Hx. apply AG. apply HP. rewrite Ha' in Hx. exact Hx.
Qed.

Lemma mem_u64_local : forall a v,
  (forall x : word, a <= bv_unsigned x < a + 8 -> P x) -> 0 <= a -> a + 8 <= two64 ->
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M' a v.
Proof.
  intros a v HP Ha Hn H. unfold mem_u64 in *.
  apply (mem_is_local a (Z_to_le_bytes 8 v)); rewrite ?length_Z_to_le_bytes; first [exact HP | exact Ha | exact Hn | exact H].
Qed.
Lemma mem_u32_local : forall a v,
  (forall x : word, a <= bv_unsigned x < a + 4 -> P x) -> 0 <= a -> a + 4 <= two64 ->
  mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M a v -> mem_u32 (run_segments R_segs rc_inp rc_sp rc_mb) M' a v.
Proof.
  intros a v HP Ha Hn H. unfold mem_u32 in *.
  apply (mem_is_local a (Z_to_le_bytes 4 v)); rewrite ?length_Z_to_le_bytes; first [exact HP | exact Ha | exact Hn | exact H].
Qed.
Lemma mem_arr_local : forall k base n f,
  (forall x : word, base <= bv_unsigned x < base + k * n -> P x) ->
  mem_arr k (run_segments R_segs rc_inp rc_sp rc_mb) M base n f -> mem_arr k (run_segments R_segs rc_inp rc_sp rc_mb) M' base n f.
Proof.
  intros k base n f HP (A & B & C & D & H). split; [exact A | split; [exact B | split; [exact C | split; [exact D |]]]].
  intros i Hi. eapply mem_is_local; [ | nia | rewrite length_Z_to_le_bytes; nia | apply H; exact Hi].
  intros x Hx. apply HP. rewrite length_Z_to_le_bytes in Hx. nia.
Qed.

Lemma i_frame_local : forall cx,
  (forall x : word, c_u cx + -248 <= bv_unsigned x < c_u cx -> P x) ->
  0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 ->
  i_frame cx M -> i_frame cx M'.
Proof.
  intros cx HP Hu1 Hu2 H. unfold i_frame in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27).
  repeat split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma i_hooks_local : forall cx,
  (forall x : word, c_u cx + 64 <= bv_unsigned x < c_u cx + 80 -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 ->
  i_hooks cx M -> i_hooks cx M'.
Proof.
  intros cx HP Hu1 Hu2 [A B].
  split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma i_cst_local : forall cx,
  (forall x : word, (c_u cx + 56 <= bv_unsigned x < c_u cx + 88) \/ (c_p cx <= bv_unsigned x < c_p cx + 7164) -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M -> i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M'.
Proof.
  intros cx HP Hu1 Hu2 Hp1 Hp2 H. unfold i_cst, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma st_at_local : forall cx st,
  (forall x : word, c_p cx + 8 <= bv_unsigned x < c_p cx + 168 -> P x) ->
  0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M'.
Proof.
  intros cx st HP Hp1 Hp2 H. unfold st_at, st_rest, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma strm_at_local : forall cx st,
  (forall x : word, (c_u cx <= bv_unsigned x < c_u cx + 36) \/ (c_p cx + 96 <= bv_unsigned x < c_p cx + 108) -> P x) ->
  0 <= c_u cx -> c_u cx + 208 <= two64 -> 0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M -> strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M'.
Proof.
  intros cx st HP Hu1 Hu2 Hp1 Hp2 H. unfold strm_at, STATE_SIZE in *.
  dand H as (A1 & A2 & A3 & A4 & A5 & A6).
  repeat split; ((eapply mem_u64_local || eapply mem_u32_local); [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma s_lo_local : forall cx st,
  (forall x : word, (c_u cx + -168 <= bv_unsigned x < c_u cx + -160) \/ (c_u cx + -144 <= bv_unsigned x < c_u cx + -136) -> P x) ->
  0 <= c_u cx + -1024 -> c_u cx + 208 <= two64 ->
  s_lo cx st M -> s_lo cx st M'.
Proof.
  intros cx st HP Hu1 Hu2 [A B].
  split; (eapply mem_u64_local; [ | | | eassumption]; [intros x Hx; apply HP; lia_std | lia_std | lia_std]).
Qed.
Lemma s_bk_local : forall cx st,
  (forall x : word, c_p cx + 7164 <= bv_unsigned x < c_p cx + 7168 -> P x) ->
  0 <= c_p cx -> c_p cx + STATE_SIZE <= two64 ->
  s_bk cx st M -> s_bk cx st M'.
Proof.
  intros cx st HP Hp1 Hp2 (c & A & B). unfold STATE_SIZE in *. exists c. split; [| exact B].
  eapply mem_u32_local; [ | | | exact A]; [intros x Hx; apply HP; lia_std | lia_std | lia_std].
Qed.
End Local.

(* the context gains s5 (the harness's, carried through uncompress2_z, which does not save it) *)
Definition cxw (u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra : Z) : ictx :=
  cxc u p q n 0 0 s5 s6 s7 s8 s9 s10 s11 zc 0 cin0 cout0 W0 ra.

(* updatewindow's frame at its zalloc call (T_U2C's KW): ra, then inflate's 1.4 s0 .. s5 = p, put,
   strm, bits, left, v4 (= s4u). s5u (v5) stays in s6 and is not stored; the parameter is kept for the arity. *)
Definition tok_mem {RCa1 : RunCtx}  (cx : ictx) (st : ist) (s4u s5u : Z) (lf cf : Z -> Z) (M : mem) : Prop :=
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -264) L_UW_RET /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -272) (c_p cx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -280) (c_ob cx + t_cout st) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -288) (c_u cx) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -296) (t_bits st) /\
  mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -304) (t_out st - (c_osz cx - t_cout st)) /\ mem_u64 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_u cx + -312) s4u /\
  i_frame cx M /\ i_cst (run_segments R_segs rc_inp rc_sp rc_mb) cx M /\ i_hooks cx M /\
  st_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ strm_at (run_segments R_segs rc_inp rc_sp rc_mb) cx st M /\ s_lo cx st M /\ s_bk cx st M /\
  mem_arr 2 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 168) N_LENS lf /\ mem_arr 4 (run_segments R_segs rc_inp rc_sp rc_mb) M (c_p cx + 1384) N_CODES cf.

(* the pure side conditions of the zw invariant *)
Definition tok_pure (u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra s4u s5u s7u rvu : Z) (st : ist) (lf cf : Z -> Z) : Prop :=
  (ra = RA_C1 \/ ra = RA_C2) /\ 0 <= cin0 <= n /\ 0 <= cout0 <= 262144 /\
  0 <= s5 < two64 /\ 0 <= s6 < two64 /\ 0 <= s7 < two64 /\ 0 <= s8 < two64 /\ 0 <= s9 < two64 /\ 0 <= s10 < two64 /\ 0 <= s11 < two64 /\
  0 <= s4u < two64 /\ 0 <= s5u < two64 /\ 0 <= s7u < two64 /\ 0 <= rvu < two64 /\
  sinv (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st lf cf /\ cout0 < t_cout st /\ t_mode st <= DONE /\
  zc + FRA <= u /\ u + 208 <= 140737488355328 /\ 0 < p /\ p + STATE_SIZE <= zc.

(* s0 .. s11 at the zalloc call (T_U2C's KW): updatewindow's s0 .. s3 (put, left, 1, p), then
   inflate's s4 = left, s5 = v4, s6 = v5, s7 = have, s8 = s7u (free), s9 = hold, s10 = next, s11 = rv *)
Definition tok_regs (p q n s4u s5u s7u rvu : Z) (st : ist) : list Z :=
  [BUF + t_cout st; t_out st - (262144 - t_cout st); 1; p; t_out st - (262144 - t_cout st); s4u;
   s5u; n - t_cin st; s7u; t_hold st; q + t_cin st; rvu].

Definition zwtok_U7 {RCa1 : RunCtx}  : ZWINV := fun u p q n zc sE sW M =>
  exists (s5 s6 s7 s8 s9 s10 s11 cin0 cout0 W0 ra s4u s5u s7u rvu : Z) (st : ist) (lf cf : Z -> Z),
    sE = [s5; s6; s7; s8; s9; s10; s11] /\ sW = tok_regs p q n s4u s5u s7u rvu st /\
    tok_pure u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra s4u s5u s7u rvu st lf cf /\
    tok_mem (cxw u p q n s5 s6 s7 s8 s9 s10 s11 zc cin0 cout0 W0 ra) st s4u s5u lf cf M.

Theorem zw_local {RCa1 : RunCtx}  : zw_local_stmt_U7 zwtok_U7.
Proof.
  intros u p q n zc sE sW M M' AG H.
  dand H as (s5 & s6 & s7 & s8 & s9 & s10 & s11 & cin0 & cout0 & W0 & ra & s4u & s5u & s7u & rvu & st & lf & cf & EsE & EsW & PURE & TM).
  exists s5, s6, s7, s8, s9, s10, s11, cin0, cout0, W0, ra, s4u, s5u, s7u, rvu, st, lf, cf.
  split; [exact EsE | split; [exact EsW | split; [exact PURE |]]].
  pose proof two64_eq as TW64.
  assert (HL : zc + FRA <= u /\ u + 208 <= 140737488355328 /\ 0 < p /\ p + STATE_SIZE <= zc).
  { unfold tok_pure in PURE. destr_conj PURE. split_conj; assumption. }
  clear PURE EsE EsW. cbv [FRA STATE_SIZE] in HL. dand HL as (Hu0 & Hu1 & Hp0 & Hp1).
  unfold tok_mem, cxw, cxc in *. icx_cbn.
  dand TM as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & FRM & CST & HK & SAT & STRM & SLO & SBK & Hlens & Hcodes).
  unfold in_fpw_U7, U7_ZWD, U7_INFL_N, U7_BUF, U7_BUF_N in AG.
  split_conj.
  all: first [ eapply (mem_u64_local _ M M' AG); [ | | | eassumption]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_frame_local _ M M' AG); [ | | | eassumption]; icx_cbn; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_hooks_local _ M M' AG); [ | | | eassumption]; icx_cbn; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (i_cst_local _ M M' AG); [ | | | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std | lia_std | lia_std]
             | eapply (st_at_local _ M M' AG); [ | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (strm_at_local _ M M' AG); [ | | | | | eassumption]; icx_cbn; cbv [STATE_SIZE BUF]; [intros x Hx; lia_std | lia_std | lia_std | lia_std | lia_std]
             | eapply (s_lo_local _ M M' AG); [ | | | eassumption]; icx_cbn; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (s_bk_local _ M M' AG); [ | | | eassumption]; icx_cbn; cbv [STATE_SIZE]; [intros x Hx; lia_std | lia_std | lia_std]
             | eapply (mem_arr_local _ M M' AG); [ | eassumption]; cbv [N_LENS N_CODES]; intros x Hx; lia_std
             | match goal with |- ?G => idtac "LOCSIDE" G end ].
Qed.
