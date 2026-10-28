(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzHs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzHs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuJ9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuJ9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxDK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Export UxDK.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Open Scope bv_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x5b640%Z.
Definition w_71 := 0x0000a517%Z.
Definition w_72 := 0x27453903%Z.
Definition w_98 := 0x85df50ef%Z.
Definition hi_71 := (Z_to_bv 20 10).
Definition lo_72 := (Z_to_bv 12 628).
Definition joff_98 := (Z_to_bv 21 2054236).
Definition got_ssp := got_ssp.
Definition STRING_READ := STRING_READ.
Definition ssp_guard := ssp_guard.
Definition e_197bc := 0x51024%Z.
Definition e_memcpy := 0x5f438%Z.
Definition e_memchr := 0x5f33c%Z.
Lemma CODE : CodeAt.code_at rsegs 0x5b640 (QQRC.Mq3.shgetc_code 0x0000a517%Z 0x27453903%Z 0x85df50ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x5b640 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x5b640 /\ 0x5b640 + 544 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition memcpy_spec := @memcpy_spec.
Definition memchr_spec := @memchr_spec.
End GwI.

Ltac hyp :=
lazymatch goal with
| |- rw_cells _ ?m ?A ?cs =>
match goal with H : rw_cells _ ?m' ?A' ?cs' |- _ => constr_eq m' m; constr_eq A' A; unify cs' cs; exact H end
| |- ?G => match goal with H : ?T |- _ => constr_eq T G; exact H end
end.

Definition rtext (T : Z) (txt pre post : list Z) : Prop :=
txt = pre ++ 0%Z :: post /\ Forall (fun c => 0 < c < 256)%Z pre /\ Forall (fun c => 0 <= c < 256)%Z txt /\
((T + zlength txt) mod 8 = 0)%Z /\ (zlength txt <= 256)%Z.
Lemma gw_eq_rtext : @rtext = ltac:(GwInst.gw_term (@Q8l1.Mq3.rtext) (@rtext)). Proof. unfold rtext, Q8l1.Mq3.rtext; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rtext : gw_eqs.

Lemma zbytes_app : forall a b, zbytes (a ++ b) = zbytes a ++ zbytes b.
Proof. first [GwInst.gw_exact (@Q8l1.Mq3.zbytes_app) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq3.zbytes_app)]. Qed.
Lemma zbytes_length : forall a, length (zbytes a) = length a.
Proof. first [GwInst.gw_exact (@Q8l1.Mq3.zbytes_length) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq3.zbytes_length)]. Qed.
Lemma zbytes_skipn : forall k a, zbytes (skipn k a) = skipn k (zbytes a).
Proof. first [GwInst.gw_exact (@Q8l1.Mq3.zbytes_skipn) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq3.zbytes_skipn)]. Qed.
Lemma nonul_pos : forall l, Forall (fun c => 0 < c < 256)%Z l -> ~ In (Z_to_bv 8 0) (zbytes l).
Proof. first [GwInst.gw_exact (@Q8l1.Mq3.nonul_pos) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq3.nonul_pos)]. Qed.
Lemma Forall_skipn' : forall {A} (P : A -> Prop) k l, Forall P l -> Forall P (skipn k l).
Proof. first [GwInst.gw_exact (@Q8l1.Mq3.Forall_skipn') | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq3.Forall_skipn')]. Qed.
Lemma skipn_hd : forall (l : list byte) k b, nth_error l k = Some b -> skipn k l = b :: skipn (S k) l.
Proof. first [GwInst.gw_exact (@Q8l1.Mq3.skipn_hd) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq3.skipn_hd)]. Qed.
Lemma hd_eq : forall (l : list byte) b, nth_error l 0 = Some b -> l = b :: skipn 1 l.
Proof. first [GwInst.gw_exact (@Q8l1.Mq3.hd_eq) | autorewrite with gw_eqs; GwInst.gw_exact (@Q8l1.Mq3.hd_eq)]. Qed.
Lemma rw_cells_CB1 : forall m A bs, rw_cells rsegs m A [CB 1 bs] -> exists b, rw_cells rsegs m A [CB 1 [b]].
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.rw_cells_CB1) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.rw_cells_CB1)]. Qed.
Lemma rw_cells_CB0 : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A (CB 0 [] :: cs).
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.rw_cells_CB0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.rw_cells_CB0)]. Qed.
Lemma rw_cells_unCB0 : forall m A cs, rw_cells rsegs m A (CB 0 [] :: cs) -> rw_cells rsegs m A cs.
Proof. first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.rw_cells_unCB0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.rw_cells_unCB0)]. Qed.

Definition sread_len (off p : Z) : Z := if (off <? p)%Z then 1 else 0.
Lemma gw_eq_sread_len : @sread_len = ltac:(GwInst.gw_term (@Q8l1.Mq3.sread_len) (@sread_len)). Proof. unfold sread_len, Q8l1.Mq3.sread_len; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sread_len : gw_eqs.

Definition memchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(A C N : Z) (buf : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (memchr_res A C N buf)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ bytes_at rsegs m' A buf.
Lemma gw_eq_memchr_postv : @memchr_postv = ltac:(GwInst.gw_term (@Q8l1.Mq3.memchr_postv rsegs) (@memchr_postv)). Proof. unfold memchr_postv, Q8l1.Mq3.memchr_postv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_memchr_postv : gw_eqs.

Local Definition gwt_X : unit := Q6nq.gwt_nil.
Lemma memchr_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq3.memchr_callv) [[@gw_eq_memchr_postv]; [@gw_eq_rtext__3; @gw_eq_rtext__2; @gw_eq_rtext]; [@gw_eq_sread_len__3; @gw_eq_sread_len__2; @gw_eq_sread_len]] '([256; 389948]%Z : list Z) '(Q6nq.gwt_unf (@memchr_entry) gwt_X)).
Proof. rewrite ?gw_eq_memchr_postv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.memchr_callv) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.memchr_callv)]. Qed.

Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Dst Src N : Z) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Dst) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(Dst, Dst + N)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' Dst [CB (Z.to_nat N) src]
/\ bytes_at rsegs m' Src src.
Lemma gw_eq_memcpy_postv : @memcpy_postv = ltac:(GwInst.gw_term (@Q8l1.Mq3.memcpy_postv rsegs) (@memcpy_postv)). Proof. unfold memcpy_postv, Q8l1.Mq3.memcpy_postv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_memcpy_postv : gw_eqs.
Lemma memcpy_callv : ltac2:(Q6nq.ty1 'GwI.segs '(@Q8l1.Mq3.memcpy_callv) [[@gw_eq_memcpy_postv]; [@gw_eq_rtext__3; @gw_eq_rtext__2; @gw_eq_rtext]; [@gw_eq_sread_len__3; @gw_eq_sread_len__2; @gw_eq_sread_len]; [@gw_eq_memchr_postv__3; @gw_eq_memchr_postv__2; @gw_eq_memchr_postv]] '([390200]%Z : list Z) '(Q6nq.gwt_unf (@memcpy_entry) gwt_X)).
Proof. rewrite ?gw_eq_memcpy_postv; first [GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.memcpy_callv) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q8l1.Mq3.memcpy_callv)]. Qed.

Definition sread_post (ra : word) (q : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(Fp T D p off : Z) (txt : list Z) (dj : byte) (mode : word) (shend : Z) (shl shc : word) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sread_len off p)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(q - 64, q); (Fp, Fp + 232); (D, D + 1)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' (q - 64) (q)
/\ rw_cells rsegs m' Fp (ss_cells T (T + off + sread_len off p) (T + p) mode (T + p) shend shl shc)
/\ rw_cells rsegs m' D [CB 1 [if (off <? p)%Z then Z_to_bv 8 (znth txt off) else dj]]
/\ bytes_at rsegs m' T (zbytes txt).
Lemma gw_eq_sread_post : @sread_post = ltac:(GwInst.gw_term (@Q8l1.Mq3.sread_post rsegs STRING_READ) (@sread_post)). Proof. unfold sread_post, Q8l1.Mq3.sread_post; rewrite ?gw_eq_sread_len; ltac2:(GwEq.gw_rw [[@gw_eq_ss_cells__3; @gw_eq_ss_cells__2; @gw_eq_ss_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sread_post : gw_eqs.

Definition sread_stmt : Prop :=
forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T D p off rpos rend shend : Z) (txt pre post : list Z) (dj : byte) (mode shl shc : word),
rw_cells rsegs m Fp (ss_cells T rpos rend mode (T + off) shend shl shc) ->
rtext T txt pre post -> p = zlength pre -> (0 <= off <= p)%Z ->
bytes_at rsegs m T (zbytes txt) -> rw_cells rsegs m D [CB 1 [dj]] ->
(4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (0 <= rpos < 2^64)%Z -> (0 <= rend < 2^64)%Z -> (0 <= shend < 2^64)%Z ->
(D + 1 <= Fp \/ Fp + 232 <= D)%Z -> (D + 1 <= T \/ T + zlength txt <= D)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
stk rsegs m (q - 64) (q) -> (4096 <= q)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
(q <= D)%Z -> (D + 1 <= 2^63)%Z -> (T + zlength txt <= q - 64 \/ q <= T)%Z ->
(0 <= q)%Z -> (q < 2^63)%Z ->
mem_inv rsegs m ->
evt rsegs (sread_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T D p off txt dj mode shend shl shc m)
(MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) (Z_to_bv 64 D) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 STRING_READ) fc None m (seg_rom rsegs)).
Lemma gw_eq_sread_stmt : @sread_stmt = ltac:(GwInst.gw_term (@Q8l1.Mq3.sread_stmt rsegs STRING_READ) (@sread_stmt)). Proof. unfold sread_stmt, Q8l1.Mq3.sread_stmt; rewrite ?gw_eq_rtext, ?gw_eq_sread_post; ltac2:(GwEq.gw_rw [[@gw_eq_ss_cells__3; @gw_eq_ss_cells__2; @gw_eq_ss_cells]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_sread_stmt : gw_eqs.

