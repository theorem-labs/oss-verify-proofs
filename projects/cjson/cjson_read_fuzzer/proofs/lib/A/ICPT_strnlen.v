(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
Module F_strnlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memchr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Definition strnlen_entry := 0x9badc%Z.

(* [comment removed for export] *)
Definition STRNLEN_DEPTH : Z := 2336.   (* [comment removed for export] *)

Definition strnlen_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1
                 (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
                 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2336, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' (bv_unsigned a0) buf.

(* [comment removed for export] *)
Lemma strnlen_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (buf : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) ->
  bytes_at asegs m (bv_unsigned a0) buf ->
  memchr_ok (bv_unsigned a0) 0 (bv_unsigned a1) buf ->
  mem_inv asegs m ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (0 < bv_unsigned a0)%Z ->
  (* [comment removed for export] *)
  MRT m -> (alloc_ceiling <= lo)%Z -> (lo + STRNLEN_DEPTH <= bv_unsigned sp)%Z ->
  (bv_unsigned a1 < 2^40)%Z -> app_range (bv_unsigned a0) (Z.of_nat (length buf)) ->
  (let len := memchr_chk_len (bv_unsigned a0) 0 (bv_unsigned a1) buf in
   (0 < len)%Z -> app_range (bv_unsigned a0) len /\ shadow_ok m (bv_unsigned a0) len) ->
  (bv_unsigned a0 + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  evt asegs (strnlen_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9badc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST BUF OK MI LO SEP A0 MR CEIL SPB N40 AR CHK SEPl.
  unfold STRNLEN_DEPTH in SPB. pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  pose proof AINTRIN_STACK_val as AIS. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 2336, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MUf.
  pose proof (bytes_at_bound _ _ _ _ BUF) as AB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  carve_frame 32%nat ST.
  do 9 zstep.
  assert (AIf : Forall app_iv [(bv_unsigned sp - 32, bv_unsigned sp)]%Z)
    by (apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MR1 : MRT mm)
      by (eapply (MRT_munch _ m mm); [exact MR| exact MUf|];
          apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]);
    assert (CHK1 : let len := memchr_chk_len (bv_unsigned a0) 0 (bv_unsigned a1) buf in
                  (0 < len)%Z -> app_range (bv_unsigned a0) len /\ shadow_ok mm (bv_unsigned a0) len)
      by (cbv zeta; intros Hl; destruct (CHK Hl) as [A1 S1]; split; [exact A1|];
          eapply shadow_ok_munch_app; [exact S1| exact MUf| exact Hl| exact A1| exact AIf])
  end.
  clear MUf.
  callsp memchr_icpt_callw.
  1:{ exact BUF. }
  1:{ rewrite unsigned_lit by lia. exact OK. }
  1:{ assumption. }
  1:{ exact (MRT_icpt _ MR1). } 1:{ exact ST. } 1:{ exact CEIL. } 1:{ lia. } 1:{ lia. } 1:{ exact AR. }
  1:{ rewrite unsigned_lit by lia. exact CHK1. } 1:{ lia. }
  match goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
  rewrite unsigned_lit by lia. change (0 mod 256)%Z with 0%Z.
  unfold memchr_res.
  destruct (find_byte 0 (firstn (Z.to_nat (bv_unsigned a1)) buf)) as [i|] eqn:FB.
  - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite firstn_length in Hl.
    zstep. if_cases K; zify_cond K. { exfalso. lia. }
    do 7 zstep.
    replace (bv_unsigned a0 + Z.of_nat i - bv_unsigned a0)%Z with (strnlen_res (bv_unsigned a1) buf)
      by (unfold strnlen_res; rewrite FB; lia).
    release_frame FR ST (bv_unsigned sp). finish.
  - zstep. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
    do 6 zstep.
    lazymatch goal with |- evt _ ?Q _ => set (P := Q) end.
    replace a1 with (Z_to_bv 64 (strnlen_res (bv_unsigned a1) buf))
      by (unfold strnlen_res; rewrite FB; apply Z_to_bv_bv_unsigned).
    release_frame FR ST (bv_unsigned sp). finish.
Qed.


End CeilWrap.
End F_strnlen.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow ICPT_iface RT_poison RT_poison2 ICPT_mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_str3.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_str3.ICPT_str.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl.
Import F_strnlen.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope. Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition ASTRNLEN_T : Z := 0x424d4.        (* [comment removed for export] *)
Definition ASTRNLEN_ICPT : Z := 0x42800.
Definition ASTRNLEN_STACK : Z := 4480.       (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma strnlen_chk_len : forall s n buf, 0 < s -> 0 <= n ->
  memchr_chk_len s 0 n buf = Z.min (strnlen_res n buf + 1) n.
Proof.
  intros s n buf Hs Hn. unfold memchr_chk_len, memchr_res, strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:E.
  - pose proof (proj1 (find_byte_Some _ _ _ E)) as Hi. rewrite length_firstn in Hi.
    destruct (Z.eqb_spec (s + Z.of_nat i) 0); lia.
  - rewrite Z.eqb_refl. lia.
Qed.
Lemma strnlen_res_range : forall n buf, 0 <= n -> 0 <= strnlen_res n buf <= n.
Proof.
  intros n buf Hn. unfold strnlen_res.
  destruct (find_byte 0 (firstn (Z.to_nat n) buf)) as [i|] eqn:E; [|lia].
  pose proof (proj1 (find_byte_Some _ _ _ E)) as Hi. rewrite length_firstn in Hi. lia.
Qed.

Definition strnlen_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - ASTRNLEN_STACK, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' s buf
    /\ stk asegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
Definition strnlen_icpt_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s n : Z) (buf : list byte) (lo : Z),
  MRT m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + ASTRNLEN_STACK <= bv_unsigned sp ->
  a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 n ->
  bytes_at asegs m s buf -> memchr_ok s 0 n buf -> 0 < s -> 0 <= n < 2^40 ->
  app_range s (Z.of_nat (length buf)) ->
  (let len := memchr_chk_len s 0 n buf in 0 < len -> app_range s len /\ shadow_ok m s len) ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) ->
  evt asegs (strnlen_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASTRNLEN_T) fc None m (seg_rom asegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition strnlen_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s n : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strnlen_res n buf)) a1' a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2336, bv_unsigned sp)] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ bytes_at asegs m' s buf.

Lemma strnlen_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (s n : Z) (buf : list byte) (lo : Z),
  stk asegs m lo (bv_unsigned sp) -> bytes_at asegs m s buf -> memchr_ok s 0 n buf -> mem_inv asegs m ->
  lo <= bv_unsigned sp - 32 -> 0 < s -> s + Z.of_nat (length buf) < 2^64 -> 0 <= n < 2^40 ->
  MRT m -> alloc_ceiling <= lo -> lo + 2336 <= bv_unsigned sp -> app_range s (Z.of_nat (length buf)) ->
  (let len := memchr_chk_len s 0 n buf in 0 < len -> app_range s len /\ shadow_ok m s len) ->
  (s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s) ->
  evt asegs (strnlen_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s n buf lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9badc) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST BUF OK MI LO HS HB HN MR CEIL SPB AR CHK SEP.
  assert (ES : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (strnlen_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 s) (Z_to_bv 64 n)); rewrite ?ES, ?EN;
      first [exact ST| exact BUF| exact OK| exact MI| exact MR| exact CEIL| exact AR| exact CHK| exact SEP| unfold STRNLEN_DEPTH; lia]. }
  intros ms' P. unfold strnlen_post, strnlen_postv in *. rewrite ES, EN in P. exact P.
Qed.

Section StrnlenIcpt.
  Variables (rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : word -> option byte) (s n lo : Z) (buf : list byte).
  Variables (Lr K : Z).
  Hypothesis HN : 0 <= n < 2^40.
  Hypothesis HS : 0 < s.
  Hypothesis AR : app_range s (Z.of_nat (length buf)).
  Hypothesis OK : memchr_ok s 0 n buf.
  Hypothesis HLr : Lr = strnlen_res n buf.
  Hypothesis HK : K = memchr_chk_len s 0 n buf.
  Hypothesis ARK : 0 < K -> app_range s K.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPB : lo + ASTRNLEN_STACK <= bv_unsigned sp.
  Hypothesis SEP : s + Z.of_nat (length buf) <= lo \/ bv_unsigned sp <= s.

  Lemma LK_facts : 0 <= Lr <= n /\ K = Z.min (Lr + 1) n.
  Proof.
    subst Lr K. split; [apply strnlen_res_range; lia| apply strnlen_chk_len; lia].
  Qed.
  Lemma RB : 0 <= s /\ s + Z.of_nat (length buf) < 2^47. Proof. exact (app_range_lt47 _ _ AR). Qed.
  Lemma RBK : 0 < K -> s + K < 2^47. Proof. intros H. exact (proj2 (app_range_lt47 _ _ (ARK H))). Qed.
  Lemma CEILv : alloc_ceiling = alloc_ceiling. Proof. reflexivity. Qed.
  Lemma STKv : ASTRNLEN_STACK = 4480. Proof. reflexivity. Qed.

  #[warnings="-notation-for-abbreviation"]
  Notation POST := (strnlen_icpt_post rae sp gp tp s0e s1e s2e s3e s4e s5e s6e s7 s8 s9 s10 s11 F fc s n buf lo m).
  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"]
  Notation ST_ pc mm x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
            x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 n) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition asn_frame (mm : word -> option byte) : Prop :=
    mem_inv asegs mm /\ MRT mm /\ stk asegs mm lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs mm (bv_unsigned sp + -64) [C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 rae]
    /\ bytes_at asegs mm s buf
    /\ munch [(bv_unsigned sp - ASTRNLEN_STACK, bv_unsigned sp)] m mm /\ wmono asegs m mm
    /\ stk asegs mm (bv_unsigned sp + -2144) (bv_unsigned sp + -64)
    /\ (0 < K -> shadow_ok mm s K).

  (* [comment removed for export] *)
  Ltac lit_cond Kc := revert Kc; rewrite ?unsigned_lit by lia; intros Kc; try rewrite !Z.mod_small in Kc by lia.
  Ltac asn_intro AF := (nelim AF 9%nat; intros MI' MR' ST' FR' BUF' MU' WM' ST2 SO).
  Ltac asn_pack := refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); assumption.

  (* [comment removed for export] *)
  Lemma asn_after_callee : forall mm mm' k,
    MRT mm -> (0 < K -> shadow_ok mm s K) -> 0 <= k <= 2336 ->
    munch [(bv_unsigned sp - 2144 - k, bv_unsigned sp - 2144)] mm mm' ->
    MRT mm' /\ (0 < K -> shadow_ok mm' s K).
  Proof.
    intros mm mm' k MR SO Hk MUr. pose proof RB. pose proof CEILv. pose proof STKv.
    split.
    - eapply MRT_munch; [exact MR| exact MUr|]. apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil].
    - intros HK0. eapply shadow_ok_munch_app; [exact (SO HK0)| exact MUr| exact HK0| exact (ARK HK0)|].
      apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil].
  Qed.

  (* [comment removed for export] *)
  Lemma asn_ret : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm ->
    evt asegs POST (ST_ 0x428c4 mm x1 x5 x6 x7 x9 (Z_to_bv 64 Lr) x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. asn_intro AF.
    pose proof RB as RB'. pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    do 11 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with ST1 : stk asegs mm2 lo _ |- _ =>
      lazymatch goal with ST3 : stk asegs mm2 (bv_unsigned sp + -2144) _ |- _ =>
      lazymatch goal with FR3 : rw_cells asegs mm2 (bv_unsigned sp + -64) _ |- _ =>
        pose proof (stk_merge asegs mm2 _ _ _ ST1 ST3 ltac:(lia)) as STm;
        release_frame FR3 STm (bv_unsigned sp)
      end end end end.
    subst Lr. finish.
  Qed.

  (* [comment removed for export] *)
  Lemma asn_region : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm -> 0 < K ->
    evt asegs POST (ST_ 0x429b0 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 Lr) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HK0. asn_intro AF.
    pose proof RB as RB'. pose proof (RBK HK0) as RBK'. pose proof LK_facts as [LF1 LF2].
    pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof MR' as MR2. pose proof SO as SO2.
    pose proof (munch_refl [(bv_unsigned sp - 2144 - 80, bv_unsigned sp - 2144)] mm) as MU1.
    do 4 zstep.
    callsp region_is_poisoned_ok;
      [ exact (MRT_icpt _ MR') | exact MI' | exact ST' | exact CEIL | lia | reflexivity | reflexivity | lia
      | exact (ARK HK0) | exact (SO HK0) | ].
    zstep. zstep. zstep. fold_lits. sh_if_true.
    apply asn_ret.
    lazymatch goal with |- asn_frame ?mm2 =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        destruct (asn_after_callee mm mm2 80 MR2 SO2 ltac:(lia) MUc) as [MR3 SO3]
      end end.
    asn_pack.
  Qed.

  (* [comment removed for export] *)
  Lemma asn_62384 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm -> 0 < K ->
    evt asegs POST (ST_ 0x429a8 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 Lr) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HK0. pose proof RB as RB'.
    zstep. zstep. if_cases Kc.
    - apply asn_ret. exact AF.
    - apply asn_region; [exact AF| exact HK0].
  Qed.

  (* [comment removed for export] *)
  Lemma asn_loop : forall mm (k : nat) (i : Z) x1 x5 x6 x7 (acc : word) x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm -> 0 < K ->
    Z.to_nat (SH (s + K - 1) - SH s - i) = k -> 0 <= i -> SH s + i < SH (s + K - 1) ->
    evt asegs POST (ST_ 0x42998 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 Lr) (Z_to_bv 64 (2147450880 + s / 8 + i)) (Z_to_bv 64 (2147450880 + (s + K - 1) / 8))
                        acc x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros mm k. induction k as [|k IH]; intros i x1 x5 x6 x7 acc x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 AF HK0 Hk Hi Hlt;
      pose proof RB as RB'; pose proof (RBK HK0) as RBK'; pose proof (SH_bounds s ltac:(lia)) as B1; pose proof (SH_bounds (s + K - 1) ltac:(lia)) as B2;
      unfold SH, SHADOW_OFFSET in *; [lia|].
    pose proof AF as AF'. asn_intro AF'.
    assert (V : exists b, mm (wa (2147450880 + s / 8 + i)) = Some b).
    { destruct (mm (wa (2147450880 + s / 8 + i))) as [b|] eqn:E; [exists b; reflexivity| exfalso].
      apply (proj2 (SO HK0) (2147450880 + s / 8 + i)); [| exact E]. unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    destruct V as [b RDb]. pose proof (vis_read1 mm _ b RDb) as RD. unfold wa in RD.
    zstep. zstep. zstep. zstep.
    if_cases Kc; zify_cond Kc.
    - replace (2147450880 + s / 8 + i + 1) with (2147450880 + s / 8 + (i + 1)) by lia.
      apply (IH (i + 1)); try assumption; lia.
    - replace (2147450880 + s / 8 + i + 1) with (2147450880 + (s + K - 1) / 8) by lia.
      apply asn_62384; [exact AF| exact HK0].
  Qed.

  (* [comment removed for export] *)
  Lemma asn_slow : forall mm x1 x5 x6 x7 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm -> 0 < K ->
    evt asegs POST (ST_ 0x4297c mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 Lr) (Z_to_bv 64 (2147450880 + s / 8)) (Z_to_bv 64 (2147450880 + (s + K - 1) / 8))
                        (Z_to_bv 64 (s + K - 1)) x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HK0. pose proof RB as RB'. pose proof (RBK HK0) as RBK'.
    pose proof (SH_bounds s ltac:(lia)) as B1. pose proof (SH_bounds (s + K - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. asn_intro AF'.
    (nelim (shadow_ok_shb mm s K (K - 1) (SO HK0) ltac:(lia)) 3%nat; intros ve SHE Ce).
    pose proof (shb_load_div' mm (s + (K - 1)) ve (s + K - 1) SHE ltac:(lia) ltac:(lia)) as RD.
    zstep. clear RD.
    rewrite (sxb_zb_small ve) by lia.
    do 5 zstep.
    zstep. if_cases Kc; zify_cond Kc.
    - apply asn_62384; [exact AF| exact HK0].
    - replace (2147450880 + s / 8) with (2147450880 + s / 8 + 0) by lia.
      eapply (asn_loop mm (Z.to_nat (SH (s + K - 1) - SH s - 0)) 0); try exact AF; try exact HK0; unfold SH, SHADOW_OFFSET; try lia.
  Qed.

  (* [comment removed for export] *)
  Lemma asn_quick : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm -> 0 < K <= 64 ->
    evt asegs POST (ST_ 0x42888 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 Lr) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HKr. assert (HK0 : 0 < K) by lia. pose proof RB as RB'. pose proof (RBK HK0) as RBK'.
    pose proof (SH_bounds s ltac:(lia)) as B1. pose proof (SH_bounds (s + K - 1) ltac:(lia)) as B2. unfold SH, SHADOW_OFFSET in B1, B2.
    pose proof AF as AF'. asn_intro AF'.
    pose proof (MRT_icpt _ MR') as IC'. icpt_split IC'.
    do 9 zstep.
    rewrite !(Z.shiftr_div_pow2 _ 3) by lia. change (2 ^ 3) with 8.
    replace (s + K + -1) with (s + K - 1) by lia.
    zstep. zstep. rewrite !land_m8 by lia.
    destruct (vis_read8 mm ((2147450880 + s / 8) / 8 * 8)) as (w1 & L1 & W1). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SO HK0)). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    destruct (vis_read8 mm ((2147450880 + (s + K - 1) / 8) / 8 * 8)) as (w2 & L2 & W2). (* [comment removed for export] *)
    { intros j Hj. apply (proj2 (SO HK0)). unfold SH, SHADOW_OFFSET. Z.div_mod_to_equations. lia. }
    { Z.div_mod_to_equations. lia. } { Z.div_mod_to_equations. lia. }
    unfold wa in W1, W2.
    step. step. clear W1 W2.
    zstep. step. if_cases Kc.
    - apply asn_slow; [exact AF| exact HK0].
    - apply asn_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma asn_62350 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm ->
    evt asegs POST (ST_ 0x42974 mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 Lr) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'. pose proof LK_facts as [LF1 LF2].
    zstep. if_cases Kc; zify_cond Kc; lit_cond Kc.
    - apply asn_region; [exact AF| lia].
    - zstep. apply asn_ret. exact AF.
  Qed.

  (* [comment removed for export] *)
  Lemma asn_62258 : forall mm x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm ->
    evt asegs POST (ST_ 0x4287c mm x1 x5 x6 x7 (Z_to_bv 64 K) (Z_to_bv 64 Lr) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'. pose proof LK_facts as [LF1 LF2].
    zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
    - apply asn_62350. exact AF.
    - apply asn_quick; [exact AF|].
      revert Kc. rewrite ?unsigned_lit by lia. intros Kc.
      assert (NE : K <> 0) by (intros E; rewrite E in Kc; change ((0 + -65) mod 18446744073709551616) with 18446744073709551551 in Kc; lia).
      destruct (Z.lt_ge_cases K 65) as [Hl|Hg]; [lia| exfalso].
      rewrite Z.mod_small in Kc by lia. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma asn_622cc : forall mm x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm -> K = n ->
    evt asegs POST (ST_ 0x428f0 mm x1 x5 x6 x7 x9 (Z_to_bv 64 Lr) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 s) x20 x21 x22 x28 x29 x30 x31).
  Proof.
    intros until x31. intros AF HKn. pose proof RB as RB'. pose proof LK_facts as [LF1 LF2]. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    zstep. zstep. fold_lits. rewrite (zb_lxor_ones s) by lia. zstep. zstep.
    zstep. if_cases Kc; zify_cond Kc; lit_cond Kc.
    - pose proof (asn_62258 mm) as NX. rewrite HKn in NX. apply NX. exact AF.
    - exfalso. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma asn_body : forall mm x5 x6 x7 x9 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    asn_frame mm ->
    evt asegs POST
      (MS (mkR rae (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
              (Z_to_bv 64 s) (Z_to_bv 64 n) x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x4282c) fc None mm (seg_rom asegs)).
  Proof.
    intros until x31. intros AF. pose proof RB as RB'. pose proof LK_facts as [LF1 LF2].
    pose proof CEILv as CE. pose proof STKv as SE. pose proof (bv_unsigned_in_range 64 sp) as RSP.
    pose proof AF as AF'. asn_intro AF'. pose proof MR' as MR2. pose proof SO as SO2.
    pose proof (munch_refl [(bv_unsigned sp - 2144 - 16, bv_unsigned sp - 2144)] mm) as MU1.
    zstep. zstep. zstep.
    callsp try_init_ok; [exact (MRT_icpt _ MR')| exact MI'| exact ST'| exact CEIL| lia|].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      lazymatch goal with MUc : munch _ mm mm2 |- _ =>
        destruct (asn_after_callee mm mm2 16 MR2 SO2 ltac:(lia) MUc) as [MR3 SO3]; clear MUc
      end end.
    pose proof (MRT_icpt2 _ MR3) as [_ REAL]. pose proof (MRT_icpt _ MR3) as IC3. pose proof IC3 as IC4. icpt_split IC4.
    do 6 zstep.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm2 _) =>
      pose proof (munch_refl [(bv_unsigned sp - 2144 - 2336, bv_unsigned sp - 2144)] mm2) as MU2;
      lazymatch goal with STc : stk asegs mm2 lo _ |- _ =>
        callsp strnlen_callv;
        [ exact STc | exact BUF' | exact OK | assumption | lia | exact HS | lia | exact HN | exact MR3 | exact CEIL | lia | exact AR
        | cbv zeta; rewrite <- HK; intros HK0; split; [exact (ARK HK0)| exact (SO3 HK0)] | lia | ]
      end end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm4 _) =>
      lazymatch goal with MUc : munch _ _ mm4 |- _ =>
        lazymatch type of MUc with munch _ ?mm3 _ =>
          destruct (asn_after_callee mm3 mm4 2336 MR3 SO3 ltac:(lia) MUc) as [MR5 SO5]; clear MUc
        end end end.
    rewrite <- HLr.
    zstep. fold_lits. sh_if_false.
    zstep. zstep. zstep. fold_lits. zstep. sh_if_false.
    zstep.
    zstep. if_cases Kc; zify_cond Kc; lit_cond Kc.
    - (* [comment removed for export] *)
      apply asn_622cc; [asn_pack| lia].
    - (* [comment removed for export] *)
      zstep. fold_lits. rewrite (zb_lxor_ones s) by lia. zstep. zstep.
      zstep. if_cases Kc2; zify_cond Kc2; lit_cond Kc2.
      + exfalso. lia.
      + replace (Lr + 1) with K by lia.
        apply asn_62258. asn_pack.
  Qed.
End StrnlenIcpt.

Lemma strnlen_icpt_ok : strnlen_icpt_spec.
Proof.
  unfold strnlen_icpt_spec.
  intros until lo. intros MR MI ST CEIL SPB -> -> BUF OK HS HN AR CHK SEP.
  pose proof (app_range_lt47 _ _ AR) as RB. pose proof (bv_unsigned_in_range 64 sp) as RSP.
  assert (SE : ASTRNLEN_STACK = 4480) by reflexivity.
  pose proof (munch_refl [(bv_unsigned sp - ASTRNLEN_STACK, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  pose proof (conj MR (conj CHK BUF)) as PK.
  unfold ASTRNLEN_T.
  zstep.                                   (* [comment removed for export] *)
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB _ _ _ [] _ _ _ [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  do 11 zstep.
  (nelim PK 3%nat; intros MR0 CHK0 BUF0). clear MR CHK BUF.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m0 _) =>
  assert (AIf : Forall app_iv [(bv_unsigned sp - ASTRNLEN_STACK, bv_unsigned sp)])
    by (apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]);
  assert (MR1 : MRT m0)
    by (eapply MRT_munch; [exact MR0| exact MU|]; apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]);
  assert (SO1 : 0 < memchr_chk_len s 0 n buf -> shadow_ok m0 s (memchr_chk_len s 0 n buf))
    by (intros HK0; destruct (CHK0 HK0) as [ARK SOK]; eapply shadow_ok_munch_app; [exact SOK| exact MU| exact HK0| exact ARK| exact AIf]);
  assert (BUF1 : bytes_at asegs m0 s buf)
    by (eapply bytes_at_transport; [exact BUF0| exact MU|]; cbn; lia);
  destruct (stk_split asegs m0 lo (bv_unsigned sp + -2144) (bv_unsigned sp + -64) ST ltac:(lia)) as [ST1 ST2]
  end.
  eapply asn_body; try eassumption; try reflexivity; try lia.
  { intros HK0. exact (proj1 (CHK0 HK0)). }
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); eassumption.
Qed.


End CeilWrap.
