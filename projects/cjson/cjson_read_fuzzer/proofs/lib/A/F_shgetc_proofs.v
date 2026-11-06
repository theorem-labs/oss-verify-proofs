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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SFModel.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require SoftFloat.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require StrFun.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScan.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memcpy.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_frexpl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_shgetc_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
Module F_shgetc_B.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls.
Export OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_shgetc_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
  txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
  ((T + zlength txt) mod 8 = 0)%Z /\ (zlength txt <= 256)%Z.

Lemma zbytes_app : forall a b, zbytes (a ++ b) = zbytes a ++ zbytes b.
Proof. intros. unfold zbytes. apply map_app. Qed.
Lemma zbytes_length : forall a, length (zbytes a) = length a.
Proof. intros. unfold zbytes. apply length_map. Qed.
Lemma zbytes_skipn : forall k a, zbytes (skipn k a) = skipn k (zbytes a).
Proof. intros. unfold zbytes. rewrite skipn_map. reflexivity. Qed.
Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof.
  intros l H IN. unfold zbytes in IN. apply in_map_iff in IN. destruct IN as [c [E INc]].
  pose proof (proj1 (Forall_forall _ _) H c INc) as X. cbv beta in X.
  pose proof (f_equal bv_unsigned E) as E2. rewrite !Shgetc_lemmas.unsigned_lit8 in E2 by lia. lia.
Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. intros A P k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. tauto. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof.
  induction l as [|x l IH]; intros k b H; [destruct k; discriminate H|].
  destruct k as [|k]; cbn in H |- *; [injection H as ->; reflexivity|]. exact (IH k b H).
Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. intros [|x l] b H; [discriminate H|]. cbn in H |- *. injection H as ->. reflexivity. Qed.
Lemma rw_cells_CB1 : forall m A bs, rw_cells asegs m A [CB 1 bs] -> exists b, rw_cells asegs m A [CB 1 [b]].
Proof.
  intros m A bs H. pose proof H as H'. destruct H as [[[W _] _] _]. cbn in W.
  destruct bs as [|b [|]]; try discriminate W. exists b. exact H'.
Qed.
Lemma rw_cells_CB0 : forall m A cs, rw_cells asegs m A cs -> rw_cells asegs m A (CB 0 [] :: cs).
Proof. intros m A cs [[W B] R]. split; [split|]; [split; [reflexivity | exact W] | exact B | exact R]. Qed.
Lemma rw_cells_unCB0 : forall m A cs, rw_cells asegs m A (CB 0 [] :: cs) -> rw_cells asegs m A cs.
Proof. intros m A cs [[[_ W] B] R]. split; [split|]; [exact W | exact B | exact R]. Qed.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.

(* [comment removed for export] *)
Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' A buf.
Lemma memchr_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A C N : Z) (buf : list byte),
  bytes_at asegs m A buf -> memchr_ok A C N buf -> (0 <= C < 256)%Z -> (0 <= N < 2^64)%Z -> (A < 2^64)%Z -> mem_inv asegs m ->
  evt asegs (memchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A C N buf m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9b0f4) fc None m (seg_rom asegs)).
Proof.
  intros until buf. intros BA OK HC HN HA MI. pose proof (bytes_at_bound _ _ _ _ BA) as B.
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; lia).
  assert (EC : (bv_unsigned (Z_to_bv 64 C) mod 256 = C)%Z) by (rewrite unsigned_lit by lia; apply Z.mod_small; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply F_memchr.memchr_spec with (buf := buf); rewrite ?EA, ?EC, ?EN; [exact BA | exact OK | exact MI]. }
  intros ms' P. unfold F_memchr.memchr_post in P. rewrite EA, EC, EN in P. exact P.
Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Dst, Dst + N)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at asegs m' Src src.
Lemma memcpy_callv : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte),
  bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N)%Z -> (Src + N < 2^64)%Z -> (Dst + N < 2^64)%Z -> mem_inv asegs m ->
  evt asegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9b1f0) fc None m (seg_rom asegs)).
Proof.
  intros until junk. intros BA LEN DC SEP HN HS HD MI.
  pose proof (bytes_at_bound _ _ _ _ BA) as B1. pose proof (rw_cells_bound _ _ _ _ DC) as B2. cbn [cells_size csize] in B2.
  assert (ED : bv_unsigned (Z_to_bv 64 Dst) = Dst) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 Src) = Src) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply F_memcpy.memcpy_spec with (src := src) (junk := junk); rewrite ?ED, ?ES, ?EN; [exact BA | exact LEN | exact DC | exact SEP | exact MI]. }
  intros ms' P. unfold F_memcpy.memcpy_post in P. rewrite ED, ES, EN in P. exact P.
Qed.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (q - 64) (q)
    /\ rw_cells asegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) mode (T + p) shend shl shc)
    /\ rw_cells asegs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
    /\ bytes_at asegs m' T (zbytes txt).

Definition sread_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
  rw_cells asegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at asegs m T (zbytes txt) -> rw_cells asegs m D [CB 1 [dj]] ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk asegs m (q - 64) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 64 \/ q <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRING_READ) fc None m (seg_rom asegs)).

(* [comment removed for export] *)




End CeilWrap.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
End F_shgetc_B.

(* [comment removed for export] *)
Module F_shgetc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SFModel OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.SoftFloat OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.StrFun OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScan OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.FloatScanProps.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.SFW1_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Shgetc_lemmas.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memcpy OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_memchr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls.
Export F_shgetc_B.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition uflow_res (txt : list Z) (off p : Z) : Z := if (off <? p)%Z then znth txt off else -1.

Definition uflow_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p off : Z) (txt : list Z) (shend : Z) (shl shc canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (uflow_res txt off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 128, q); (Fp, Fp + 232)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (q - 128) (q)
    /\ rw_cells asegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) (Z_to_bv 64 M64) (T + p) shend shl shc)
    /\ bytes_at asegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition uflow_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p off rpos rend shend : Z) (txt pre post : list Z) (mode shl shc canary : word),
  rw_cells asegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  (mode = Z_to_bv 64 0 \/ mode = Z_to_bv 64 M64) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at asegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk asegs m (q - 128) (q) -> (4096 <= q - 128)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 128 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 128)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (uflow_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p off txt shend shl shc canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 UFLOW) fc None m (seg_rom asegs)).

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition shgetc_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T p : Z) (f : shfile) (txt : list Z) (canary : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (fst (sh_getc f))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 160, q); (Fp, Fp + 232)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (q - 160) q
    /\ rw_cells asegs m' Fp (rf_cells T p true (snd (sh_getc f)) ssJ)
    /\ bytes_at asegs m' T (zbytes txt)
    /\ ssp_cells m' canary.

Definition shgetc_stmt : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p : Z) (w : bool) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells asegs m Fp (rf_cells T p w f ssJ) ->
  sh_stdio f = true -> sh_n f = p -> sh_buf f = txt ->
  sh_rpos f = (if w then p else 0%Z) -> (w = false -> sh_cnt0 f = 0%Z /\ sh_shlim_neg f = false) -> (0 <= sh_cnt0 f <= sh_rpos f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at asegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk asegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 160 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 160)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv asegs m ->
  evt asegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom asegs)).

(* [comment removed for export] *)




End CeilWrap.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
End F_shgetc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_defs CJ_iface AShadow ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import SFModel Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim SoftFloat StrFun FloatScan FloatScanProps.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import SFW1_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require F_scan_calls.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.F_scan_calls.F_fmt_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Import F_scan_calls Shgetc_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_memcpy F_memchr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_frexpl.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_frexpl.F_fmt_fp_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import F_fwritex F_shgetc_A.
Import F_shgetc_B.
Import F_shgetc.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg ICPT_mem4 ICPT_str3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.

Definition SREAD_XD : Z := 2368.    (* [comment removed for export] *)
Definition UFLOW_XD : Z := 2432.    (* [comment removed for export] *)
Definition SHGETC_XD : Z := 2464.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition memchr_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A C N : Z) (buf : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - AINTRIN_STACK, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ bytes_at asegs m' A buf
    /\ stk asegs m' lo q.
Lemma memchr_icpt_callq : forall ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A C N : Z) (buf : list byte) (lo : Z),
  bytes_at asegs m A buf -> memchr_ok A C N buf -> (0 <= C < 256)%Z -> (0 <= N < 2^40)%Z -> (A < 2^64)%Z -> mem_inv asegs m ->
  icpt_cells m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo + AINTRIN_STACK <= q -> (0 <= q < 2^64)%Z ->
  app_range A (Z.of_nat (length buf)) ->
  (0 < memchr_chk_len A C N buf -> app_range A (memchr_chk_len A C N buf) /\ shadow_ok m A (memchr_chk_len A C N buf)) ->
  (A + Z.of_nat (length buf) <= lo \/ q <= A) ->
  evt asegs (memchr_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A C N buf lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 C) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMCHR_T) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros BA OK HC HN HA MI IC ST CEIL SPB HQ AR CHK SEP. pose proof (bytes_at_bound _ _ _ _ BA) as B.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  assert (EC : (C mod 256 = C)%Z) by (apply Z.mod_small; lia).
  eapply evt_mono.
  { eapply memchr_icpt_ok with (buf := buf) (lo := lo); rewrite ?EQ, ?EC; try reflexivity; try eassumption; try lia. }
  intros ms' P. unfold memchr_icpt_post in P. rewrite EQ, EC in P. exact P.
Qed.

Definition memcpy_postq (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Dst Src N : Z) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(Dst, Dst + N); (q - AINTRIN_STACK, q)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' Dst [CB (Z.to_nat N) src]
    /\ bytes_at asegs m' Src src
    /\ stk asegs m' lo q.
Lemma memcpy_icpt_callq : forall ra (q : Z) gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (Dst Src N : Z) (src junk : list byte) (lo : Z),
  bytes_at asegs m Src src -> length src = Z.to_nat N -> rw_cells asegs m Dst [CB (Z.to_nat N) junk] ->
  (Src + N <= Dst \/ Dst + N <= Src)%Z -> (0 <= N)%Z -> (Src + N < 2^64)%Z -> (Dst + N < 2^64)%Z -> mem_inv asegs m ->
  icpt_cells m -> stk asegs m lo q -> alloc_ceiling <= lo -> lo + AINTRIN_STACK <= q -> (0 <= q < 2^64)%Z ->
  (N < 2^40)%Z -> app_range Src N -> app_range Dst N -> wr_range_ok Dst N ->
  (0 < N -> shadow_ok m Src N) -> (0 < N -> shadow_ok m Dst N) ->
  (Src + N <= lo \/ q <= Src) -> (Dst + N <= lo \/ q <= Dst) ->
  evt asegs (memcpy_postq ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Dst Src N src lo m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) (Z_to_bv 64 Src) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AMEMCPY_T) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros BA LEN DC SEP HN HS HD MI IC ST CEIL SPB HQ N40 ARs ARd WR SOs SOd SEPs SEPd.
  pose proof (bytes_at_bound _ _ _ _ BA) as B1. pose proof (rw_cells_bound _ _ _ _ DC) as B2. cbn [cells_size csize] in B2.
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply memcpy_icpt_ok with (src := src) (junk := junk) (lo := lo); rewrite ?EQ; try reflexivity; try eassumption; try lia. }
  intros ms' P. unfold memcpy_like_post in P. rewrite EQ in P. exact P.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sread_postA (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(q - 2368, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' (q - 2368) (q)
    /\ rw_cells asegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) mode (T + p) shend shl shc)
    /\ rw_cells asegs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
    /\ bytes_at asegs m' T (zbytes txt).

Definition sread_stmtA : Prop :=
  forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
  rw_cells asegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
  rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
  bytes_at asegs m T (zbytes txt) -> rw_cells asegs m D [CB 1 [dj]] ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
  (D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk asegs m (q - SREAD_XD) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - SREAD_XD \/ q <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv asegs m ->
  (* [comment removed for export] *)
  MRT m -> (alloc_ceiling + 64 <= q - SREAD_XD)%Z -> (q + 64 <= 2^47 - 1)%Z ->
  app_range T (zlength txt) -> shadow_ok m T (p + 1) ->
  app_range D 1 -> wr_range_ok D 1 -> shadow_ok m D 1 ->
  evt asegs (sread_postA ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRING_READ) fc None m (seg_rom asegs)).

Lemma sread_spec : sread_stmtA.
Proof.
  unfold sread_stmtA. intros until shc. intros FC TXT Hp Hoff BY DC T0 T1 Rrp Rre Rsh SEP1 SEP2 SEP3 ST SPLO SPF SPF2 SPD SPD2 SPT Q0 Q1 MI.
  intros MR CEIL Q47 ART SOT ARD WRD SOD.
  pose proof CEIL as CE. unfold alloc_ceiling, sp_window_lo, stack_max_size in CE. pose proof AINTRIN_STACK_val as AIS. unfold SREAD_XD in *.
  pose proof (munch_refl [(q - 2368, q); (Fp, Fp + 232); (D, D + 1)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (nelim TXT 5%nat; intros Htxt NZ BYT AL L256).
  pose proof (rw_cells_bound _ _ _ _ FC) as B. unfold ss_cells, w0 in FC. cbn [cells_size csize Nat.add] in B.
  assert (LTX : length (zbytes txt) = length txt) by apply zbytes_length.
  assert (LT3 : length txt = (length pre + S (length post))%nat) by (rewrite Htxt, length_app; reflexivity).
  unfold STRING_READ, M64 in *. unfold zlength in *. pose_word_ranges.
  pose proof (app_range_lt47 _ _ ART) as TB.
  assert (WAPP : Forall app_iv [(q - 2368, q); (Fp, Fp + 232); (D, D + 1)]%Z).
  { apply Forall_cons; [apply app_iv_stack; lia|]. apply Forall_cons; [apply app_iv_stack; lia|].
    apply Forall_cons; [apply app_iv_stack; lia| apply Forall_nil]. }
  assert (WMRT : Forall mrt_iv_ok [(q - 2368, q); (Fp, Fp + 232); (D, D + 1)]%Z).
  { apply Forall_cons; [apply mrt_iv_ok_stack; lia|]. apply Forall_cons; [apply mrt_iv_ok_stack; lia|].
    apply Forall_cons; [apply mrt_iv_ok_stack; lia| apply Forall_nil]. }
  sepM.
  zs. carve_frame 64%nat ST.
  do 10 zs.
  (* [comment removed for export] *)
  set (k := Z.to_nat off).
  assert (SPLIT : zbytes txt = firstn k (zbytes pre) ++ (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post)).
  { rewrite Htxt, zbytes_app. cbn [zbytes map]. rewrite app_assoc. f_equal. rewrite zbytes_skipn. symmetry. apply firstn_skipn. }
  assert (LK : length (firstn k (zbytes pre)) = k) by (rewrite length_firstn, zbytes_length; lia).
  pose proof BY as BY2. rewrite SPLIT in BY2. apply bytes_at_app in BY2. destruct BY2 as [_ BY2]. rewrite LK in BY2.
  replace (T + Z.of_nat k)%Z with (T + off)%Z in BY2 by lia.
  assert (LSK : length (zbytes (skipn k pre)) = (length pre - k)%nat) by (rewrite zbytes_length, length_skipn; lia).
  assert (LBUF : length (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post) = (length txt - k)%nat).
  { rewrite length_app. cbn [length]. rewrite LSK, zbytes_length. lia. }
  assert (RES : memchr_res (T + off) 0 257 (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post) = (T + p)%Z).
  { rewrite memchr_res_cstr by (apply nonul_pos; apply Forall_skipn'; exact NZ). rewrite LSK.
    destruct (Z.ltb_spec0 (Z.of_nat (length pre - k)) 257); lia. }
  assert (CHK : memchr_chk_len (T + off) 0 257 (zbytes (skipn k pre) ++ Z_to_bv 8 0 :: zbytes post) = (p - off + 1)%Z).
  { unfold memchr_chk_len. rewrite RES. replace (T + p =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  zs. zs. zs. zs. zs.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (MR1 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
    assert (SOT1 : shadow_ok mm T (p + 1)) by (eapply shadow_ok_munch_app; [exact SOT| exact MU| lia| eapply app_range_sub; [exact ART| lia| lia| lia]| exact WAPP]);
    assert (SOD1 : shadow_ok mm D 1) by (eapply shadow_ok_munch_app; [exact SOD| exact MU| lia| exact ARD| exact WAPP])
  end.
  zs. callw (eapply memchr_icpt_callq with (lo := (q - 2368)%Z);
    [ exact BY2 | apply memchr_ok_cstr; [apply nonul_pos; apply Forall_skipn'; exact NZ | rewrite LSK, zbytes_length; clear -AL LT3 Hoff Hp T0; Z.div_mod_to_equations; lia ]
    | lia | lia | lia | hyp
    | exact (MRT_icpt _ MR1) | hyp | lia | lia | lia
    | rewrite LBUF; eapply app_range_sub; [exact ART| lia| lia| lia]
    | rewrite CHK; intros _; split; [eapply app_range_sub; [exact ART| lia| lia| lia] | eapply shadow_ok_sub; [exact SOT1| lia| lia| lia]]
    | rewrite LBUF; lia ]).
  rewrite RES in *. clear MR1 SOT1 SOD1.
  lazymatch goal with H : bytes_at _ _ (T + off)%Z _ |- _ => rename H into BY2 end.
  lazymatch goal with H : stk _ _ (q - 2368)%Z _ |- _ => rename H into ST end.
  zs. br K0. zs. zs. zs. br K1.
  - (* [comment removed for export] *)
    assert (Eo : off = p) by lia. replace (T + p - (T + off))%Z with 0%Z by lia.
    zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MR1 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]) end.
    callw (eapply memcpy_icpt_callq with (src := []) (junk := []) (lo := (q - 2368)%Z);
      [ apply (proj1 (proj1 (bytes_at_app asegs _ (T + off) [] _) BY2)) | reflexivity | apply (proj1 (proj1 (F_fwritex.rw_cells_app asegs _ D [CB 0 []] _) (rw_cells_CB0 _ _ _ DC))) | lia | lia | lia | lia | hyp
      | exact (MRT_icpt _ MR1) | hyp | lia | lia | lia
      | lia | eapply app_range_sub; [exact ART| lia| lia| lia] | eapply app_range_sub; [exact ARD| lia| lia| lia]
      | unfold wr_range_ok in *; eapply Forall_impl; [| exact WRD]; intros [u v] Huv; cbn [fst snd] in *; lia
      | intros X; exfalso; lia | intros X; exfalso; lia | lia | lia ]).
    clear MR1. replace (T + off + 0)%Z with (T + p)%Z by lia.
    try lazymatch goal with H : bytes_at _ _ (T + off)%Z [] |- _ => clear H end.
    try lazymatch goal with H : rw_cells _ _ D [CB (Z.to_nat 0) []] |- _ => clear H end.
    lazymatch goal with H : stk _ _ (q - 2368)%Z _ |- _ => rename H into ST end.
    do 15 zs.
    release_frame FR ST q.
    apply evt_done. unfold sread_postA, sread_len, SREAD_XD. replace (off <? p) with false by (symmetry; apply Z.ltb_ge; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [exact ST|].
    split; [unfold ss_cells, w0; rewrite Z.add_0_r; subst off; hyp|]. split; [hyp | hyp].
  - (* [comment removed for export] *)
    assert (NTH : nth_error (zbytes (skipn k pre)) 0 = Some (Z_to_bv 8 (znth txt off))).
    { rewrite zbytes_skipn, nth_error_skipn, Nat.add_0_r. subst k. rewrite zbytes_nth by (unfold zlength; lia).
      rewrite Htxt, znth_app_l by (unfold zlength; lia). reflexivity. }
    pose proof (hd_eq _ _ NTH) as SK. rewrite SK in BY2. cbn [app] in BY2.
    replace (T + p - (T + off))%Z with (p - off)%Z by lia.
    zs. zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (MR1 : MRT mm) by (eapply MRT_munch; [exact MR| exact MU| exact WMRT]);
      assert (SOT1 : shadow_ok mm T (p + 1)) by (eapply shadow_ok_munch_app; [exact SOT| exact MU| lia| eapply app_range_sub; [exact ART| lia| lia| lia]| exact WAPP]);
      assert (SOD1 : shadow_ok mm D 1) by (eapply shadow_ok_munch_app; [exact SOD| exact MU| lia| exact ARD| exact WAPP]) end.
    callw (eapply memcpy_icpt_callq with (src := [Z_to_bv 8 (znth txt off)]) (junk := [dj]) (lo := (q - 2368)%Z);
      [ apply (proj1 (proj1 (bytes_at_app asegs _ (T + off) [_] _) BY2)) | reflexivity | exact DC | lia | lia | lia | lia | hyp
      | exact (MRT_icpt _ MR1) | hyp | lia | lia | lia
      | lia | eapply app_range_sub; [exact ART| lia| lia| lia] | exact ARD | exact WRD
      | intros _; eapply shadow_ok_sub; [exact SOT1| lia| lia| lia] | intros _; exact SOD1 | lia | lia ]).
    clear MR1 SOT1 SOD1.
    try lazymatch goal with H : bytes_at _ _ (T + off)%Z [_] |- _ => clear H end.
    lazymatch goal with H : stk _ _ (q - 2368)%Z _ |- _ => rename H into ST end.
    do 15 zs.
    replace (T + off + (p - off))%Z with (T + p)%Z in * by lia.
    release_frame FR ST q.
    apply evt_done. unfold sread_postA, sread_len, SREAD_XD. replace (off <? p) with true by (symmetry; apply Z.ltb_lt; lia).
    repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [hyp|]. split; [exact ST|].
    split; [unfold ss_cells, w0; hyp|]. split; [hyp | hyp].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac hyp :=
  lazymatch goal with
  | |- rw_cells _ ?m ?A ?cs =>
      match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
  | |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
  end.
Ltac hyp_cells :=
  lazymatch goal with |- rw_cells _ ?m ?A ?cs =>
    match goal with H : rw_cells _ m A ?cs' |- _ => replace cs with cs' by (repeat (reflexivity || f_equal); lia); exact H end
  end.
