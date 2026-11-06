(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition put_kids (kids : list (option jshape)) (idx : nat) (v : option jshape) : list (option jshape) :=
firstn idx kids ++ repeat None (idx - length kids) ++ [v] ++ skipn (S idx) kids.

Definition ins_kids (kids : list (option jshape)) (idx : nat) (v : option jshape) : list (option jshape) :=
if (idx <? length kids)%nat then firstn idx kids ++ [v] ++ skipn idx kids else put_kids kids idx v.

Definition del_kids (kids : list (option jshape)) (idx cnt : nat) : list (option jshape) :=
firstn idx kids ++ skipn (idx + cnt) kids.

#[using="Type"] Lemma put_kids_length : forall kids idx v, length (put_kids kids idx v) = Nat.max (length kids) (S idx).
Proof.
intros kids idx v. unfold put_kids. rewrite !length_app, firstn_length, repeat_length, length_skipn. cbn [length]. lia.
Qed.
#[using="Type"] Lemma ins_kids_length : forall kids idx v,
length (ins_kids kids idx v) = if (idx <? length kids)%nat then S (length kids) else S idx.
Proof.
intros kids idx v. unfold ins_kids. destruct (Nat.ltb_spec idx (length kids)).
- rewrite !length_app, firstn_length, length_skipn. cbn [length]. lia.
- rewrite put_kids_length. lia.
Qed.
#[using="Type"] Lemma del_kids_length : forall kids idx cnt, (idx + cnt <= length kids)%nat ->
length (del_kids kids idx cnt) = (length kids - cnt)%nat.
Proof. intros kids idx cnt H. unfold del_kids. rewrite length_app, firstn_length, length_skipn. lia. Qed.

Section JoArrIdxStmts.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Notation segs := (hl_segs L).

Definition ja_pre (A : AS L HIx) (LBall : list blk) (m : word -> option byte) (md : Model)
(sp tp ra : word) (lo stkb : Z) (errv : word) : Prop :=
HEAP L HIx A LBall m md /\
stk segs m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - stkb /\
bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= hi_top L HIx /\
rw_cells segs m (hl_tp L - 164) [C4 errv] /\
tp = Z_to_bv 64 (hl_tp L) /\ bv_unsigned ra mod 2 = 0.

Definition ja_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres L LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells segs m' (hl_tp L - 164) [C4 errv']).

Definition jo_array_put_idx_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS VBS : list blk) (lo p v idx : Z) (kids : list (option jshape)) (vs : option jshape) (errv : word),
ja_pre A (ABS ++ VBS ++ LB) m md sp tp ra lo stkb errv ->
jval segs fn (Sarr kids) m ABS p 1 -> jopt segs fn vs m VBS v ->
0 <= idx < 2^31 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 idx -> a2 = Z_to_bv 64 v ->
(forall ms' md' m' r, ja_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ exists A' ABS', jval segs fn (Sarr (put_kids kids (Z.to_nat idx) vs)) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') \/
(r = 2^64 - 1 /\ exists A', jval segs fn (Sarr kids) m' ABS p 1 /\ jopt segs fn vs m' VBS v /\ HEAP L HIx A' (ABS ++ VBS ++ LB) m' md')) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_array_insert_idx_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS VBS : list blk) (lo p v idx : Z) (kids : list (option jshape)) (vs : option jshape) (errv : word),
ja_pre A (ABS ++ VBS ++ LB) m md sp tp ra lo stkb errv ->
jval segs fn (Sarr kids) m ABS p 1 -> jopt segs fn vs m VBS v ->
0 <= idx < 2^31 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 idx -> a2 = Z_to_bv 64 v ->
(forall ms' md' m' r, ja_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ exists A' ABS', jval segs fn (Sarr (ins_kids kids (Z.to_nat idx) vs)) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') \/
(r = 2^64 - 1 /\ exists A', jval segs fn (Sarr kids) m' ABS p 1 /\ jopt segs fn vs m' VBS v /\ HEAP L HIx A' (ABS ++ VBS ++ LB) m' md')) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_array_del_idx_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS : list blk) (lo p idx cnt : Z) (kids : list (option jshape)) (errv : word),
ja_pre A (ABS ++ LB) m md sp tp ra lo stkb errv ->
jval segs fn (Sarr kids) m ABS p 1 ->
0 <= idx < 2^64 -> 0 <= cnt < 2^64 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 idx -> a2 = Z_to_bv 64 cnt ->
(forall ms' md' m' r, ja_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ idx < Z.of_nat (length kids) /\ idx + cnt <= Z.of_nat (length kids) /\
exists A' ABS', jval segs fn (Sarr (del_kids kids (Z.to_nat idx) (Z.to_nat cnt))) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') \/
(r = 2^64 - 1 /\ (Z.of_nat (length kids) <= idx \/ Z.of_nat (length kids) < idx + cnt) /\
exists A', jval segs fn (Sarr kids) m' ABS p 1 /\ HEAP L HIx A' (ABS ++ LB) m' md')) ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_array_shrink2_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS : list blk) (lo p e : Z) (kids : list (option jshape)) (errv : word),
ja_pre A (ABS ++ LB) m md sp tp ra lo stkb errv ->
jval segs fn (Sarr kids) m ABS p 1 -> 0 <= e < 2^31 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 e ->
(forall ms' md' m' r, ja_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
(r = 0 \/ r = 2^64 - 1) ->
(exists A' ABS', jval segs fn (Sarr kids) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_array_get_idx_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS : list blk) (p idx : Z) (kids : list (option jshape)),
HEAP L HIx A (ABS ++ LB) m md -> jval segs fn (Sarr kids) m ABS p 1 ->
0 <= idx < 2^64 -> bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 idx ->
(forall ms' (r : word), ret_state L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m ms' ->
realizes segs (mkCfg ms' md) T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.

Definition jo_array_length_stmt (entry : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS : list blk) (p : Z) (kids : list (option jshape)),
HEAP L HIx A (ABS ++ LB) m md -> jval segs fn (Sarr kids) m ABS p 1 ->
bv_unsigned ra mod 2 = 0 -> a0 = Z_to_bv 64 p ->
(forall ms', ret_state L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 (Z.of_nat (length kids))) m ms' ->
realizes segs (mkCfg ms' md) T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs)) md) T.
End JoArrIdxStmts.

End RC__1.
