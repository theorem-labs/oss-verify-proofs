(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7UD Qhd4 QsRG QRjH QBxa QMz4 QXup QWxq_c1 QHnV QCcH QfLs Qsw7 QJjn Qwm6 Q2y2 QdM4 QscU Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import Q7UD Qhd4.
Import QsRG.Mq0 QRjH QBxa.Mq5 QMz4.
Import QXup QWxq_c1.
Import QHnV QCcH QfLs Qsw7 QJjn.
Import Qwm6.Mq0.
Import Q2y2 QdM4.Mq1.
Import QscU.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QrJ1.Mq0.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac.
Open Scope Z_scope.
Import Q6q3.

Section Obl.
Context {RC__ : Q6q3.RunConsts}.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation RZAx A md T := (AJ5 A4L HIx A T md).
Variable reqA : ASA A4L HIx -> Z.

Definition obl_free_nn : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).

Lemma heap_pres_mono : forall (L1 L2 : list blk) SP m m',
heap_pres A4H L1 SP m m' -> (forall b, In b L2 -> In b L1) -> heap_pres A4H L2 SP m m'.
Proof.
intros L1 L2 SP m m' HP SUB a Ha HC. apply HP; [exact Ha|].
destruct HC as [X|[X|X]]; [left; exact X | right; left; exact X | right; right].
unfold in_block in *. destruct X as (b & Hb & Hr). exists b. split; [apply SUB; exact Hb | exact Hr].
Qed.

Lemma OBL_CS_WIDE_ok : forall a, cs_wide a -> hl_client_static A4H a.
Proof. intros a Ha. exact Ha. Qed.

Lemma OBL_CLIENT_FRAME_ok : forall A LB LM FR B m m' md, HEAPAx A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPAx A LB LM FR B m' md.
Proof. intros. eapply (heapA_client_frame A4L HIx); eassumption. Qed.
End Obl.

Section Obl0.
Context {RC__ : Q6q3.RunConsts}.
Variable HIx : heap_iface_A A4L.

Lemma OBL_FREE_NN_ok : obl_free_nn HIx (fun _ => 0).
Proof.
unfold obl_free_nn. intros until u. intros HP HPIN ST CEIL LO AL TOP ERR TP A0 UPK BB BD K.
eapply (hiA_free A4L HIx); try eassumption.
intros ms' m' md' A' r RS VM ST' PRES ERR' HP'.
eapply K; try eassumption; [| lia].
eapply (heap_pres_mono); [exact PRES|]. intros b Hb. rewrite app_assoc. apply in_or_app. left. exact Hb.
Qed.
End Obl0.

Section OblN6.
Context {RC__ : Q6q3.RunConsts}.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPA6 := (QZsi.HEAPA A4L H6).
Notation bud6 := QZsi.bud.
Notation RZAx A md T := (AJ5 A4L HIx A T md).
Variable reqA : ASA A4L HIx -> Z.
Definition obl_malloc_n6 : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (n lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) ra u ->
1 <= QZsi.bN B -> acostA n <= QZsi.bB B -> uw_cost u <= QZsi.bD B -> n + 8192 <= QZsi.bQ B -> reqA A + n <= 2^31 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]) ->
HEAPA6 A' ((r, n) :: LB) LM FR (QZsi.chargeQ (QZsi.charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' md' ->
reqA A' <= reqA A + n ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc A4H)) fc None m (seg_rom asegs)).
Definition obl_free_n6 : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (p lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
(if Z.eqb p 0 then 0 else uw_cost u) <= QZsi.bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPA6 A' (lb_remove p LB) LM FR (QZsi.charge B 0 (if Z.eqb p 0 then 0 else uw_cost u) 0) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Definition obl_client_frame6 : Prop := forall A LB LM FR (B : bud6) m m' md, HEAPA6 A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPA6 A LB LM FR B m' md.
End OblN6.

Section OblN6ok.
Context {RC__ : Q6q3.RunConsts}.
Variable H6 : QZsi.heap_iface_A A4L.
Lemma OBL_MALLOC_N6_ok : obl_malloc_n6 H6 (fun _ => 0).
Proof.
unfold obl_malloc_n6. intros until u. intros HP ST LO LOS SPA HT ERR TP A0 N UW UWK BN BB BD BQ RQ K HGP.
assert (GP : gp = Z_to_bv 64 (hl_gp A4L)) by exact HGP.
eapply (QZsi.hiA_malloc A4L H6) with (B := B) (n := n) (u := u) (errv := errv) (lo := lo);
[ exact HP | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0
| exact N | exact UW | exact UWK | exact BN | exact BB | exact BD | exact BQ | ].
intros ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BLK HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' _ ERR' Hr BLK HP').
- lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Unshelve. eapply (heap_pres_mono); [exact HPR|]. intros b Hb. rewrite app_assoc. apply in_or_app. left. exact Hb.
Qed.
Lemma OBL_FREE_N6_ok : obl_free_n6 H6 (fun _ => 0).
Proof.
unfold obl_free_n6. intros until u. intros HP HPIN ST LO LOS SPA HT ERR TP A0 UPK BD K HGP.
assert (GP : gp = Z_to_bv 64 (hl_gp A4L)) by exact HGP.
eapply (QZsi.hiA_free A4L H6) with (B := B) (p := p) (u := u) (errv := errv) (lo := lo);
[ exact HP | exact HPIN | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0 | exact UPK | exact BD | ].
intros ms' m' c' A' r RS VM ST' HPR ERR' HP'.
eapply (K ms' m' c' A' r RS VM ST' _ ERR' HP').
- lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Unshelve. eapply (heap_pres_mono); [exact HPR|]. intros b Hb. rewrite app_assoc. apply in_or_app. left. exact Hb.
Qed.
Lemma OBL_CLIENT_FRAME6_ok : obl_client_frame6 H6.
Proof. unfold obl_client_frame6. intros. eapply (QZsi.heapA_client_frame A4L H6); eassumption. Qed.
End OblN6ok.
End Mq0.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Fs Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBxa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBxa.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMz4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QMz4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QdM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdM4.Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QscU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QscU.
Import ListNotations. Unset Keyed Unification. Local Ltac QlEo_c1.exec_pre i ::= QlEo_c1.mkr__exec_pre_13 i. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac QlEo_c1.solve_load ::= QrJ1.mkr__solve_load_1. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0. Local Ltac Stdlib.micromega.Zify.zify_pre_hook ::= idtac.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Section Obl.
Context {RC__ : Q6q3.RunConsts}.
Variable HIx : heap_iface_A A4L.
Notation HEAPAx := (HEAPA A4L HIx).
Notation RZAx A md T := (AJ5 A4L HIx A T md).
Variable reqA : ASA A4L HIx -> Z.

Definition obl_free_nn : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (p lo : Z) (errv : word) (u : uwd),
HEAPAx A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
512 <= bB B -> (if Z.eqb p 0 then 0 else uw_cost u) <= bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPAx A' (lb_remove p LB) LM FR (charge B 512 (if Z.eqb p 0 then 0 else uw_cost u)) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).

Lemma heap_pres_mono : forall (L1 L2 : list blk) SP m m',
heap_pres A4H L1 SP m m' -> (forall b, In b L2 -> In b L1) -> heap_pres A4H L2 SP m m'.
Proof.
intros L1 L2 SP m m' HP SUB a Ha HC. apply HP; [exact Ha|].
destruct HC as [X|[X|X]]; [left; exact X | right; left; exact X | right; right].
unfold in_block in *. destruct X as (b & Hb & Hr). exists b. split; [apply SUB; exact Hb | exact Hr].
Qed.

Lemma OBL_CS_WIDE_ok : forall a, cs_wide a -> hl_client_static A4H a.
Proof. intros a Ha. exact Ha. Qed.

Lemma OBL_CLIENT_FRAME_ok : forall A LB LM FR B m m' md, HEAPAx A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPAx A LB LM FR B m' md.
Proof. intros. eapply (heapA_client_frame A4L HIx); eassumption. Qed.
End Obl.

Section Obl0.
Context {RC__ : Q6q3.RunConsts}.
Variable HIx : heap_iface_A A4L.

Lemma OBL_FREE_NN_ok : obl_free_nn HIx (fun _ => 0).
Proof.
unfold obl_free_nn. intros until u. intros HP HPIN ST CEIL LO AL TOP ERR TP A0 UPK BB BD K.
eapply (hiA_free A4L HIx); try eassumption.
intros ms' m' md' A' r RS VM ST' PRES ERR' HP'.
eapply K; try eassumption; [| lia].
eapply (heap_pres_mono); [exact PRES|]. intros b Hb. rewrite app_assoc. apply in_or_app. left. exact Hb.
Qed.
End Obl0.

Section OblN6.
Context {RC__ : Q6q3.RunConsts}.
Variable H6 : QZsi.heap_iface_A A4L.
Notation HIx := (hi5_of_v6 A4L H6).
Notation HEAPA6 := (QZsi.HEAPA A4L H6).
Notation bud6 := QZsi.bud.
Notation RZAx A md T := (AJ5 A4L HIx A T md).
Variable reqA : ASA A4L HIx -> Z.
Definition obl_malloc_n6 : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (n lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 n -> 1 <= n <= 2^26 ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok A4L (hl_malloc A4H) ra u ->
1 <= QZsi.bN B -> acostA n <= QZsi.bB B -> uw_cost u <= QZsi.bD B -> n + 8192 <= QZsi.bQ B -> reqA A + n <= 2^31 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells asegs m' r [CB (Z.to_nat n) junk]) ->
HEAPA6 A' ((r, n) :: LB) LM FR (QZsi.chargeQ (QZsi.charge B (acostA n) (uw_cost u) 1) (n + 8192)) m' md' ->
reqA A' <= reqA A + n ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc A4H)) fc None m (seg_rom asegs)).
Definition obl_free_n6 : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : config) (T : TSet)
(A : ASA A4L HIx) (LB LM : list blk) (FR : list frame) (B : bud6) (p lo : Z) (errv : word) (u : uwd),
HEAPA6 A LB LM FR B m md ->
(p = 0 \/ exists n, In (p, n) LB) ->
stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A A4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top A4L HIx + 64 ->
rw_cells asegs m (hl_tp A4H - 164) [C4 errv] ->
tp = Z_to_bv 64 (hl_tp A4H) ->
a0 = Z_to_bv 64 p ->
uw_pre A4L (hiA_top A4L HIx) m (bv_unsigned sp) (bv_unsigned s0) u /\ uw_ok A4L (hl_free A4H) ra u ->
(if Z.eqb p 0 then 0 else uw_cost u) <= QZsi.bD B ->
(forall ms' m' md' A' (r : word),
ret_state A4H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only (cfg_model md) (cfg_model md') ->
stk asegs m' lo (bv_unsigned sp) ->
heap_pres A4H (lb_remove p LB ++ LM) (bv_unsigned sp) m m' ->
rw_cells asegs m' (hl_tp A4H - 164) [C4 errv] ->
HEAPA6 A' (lb_remove p LB) LM FR (QZsi.charge B 0 (if Z.eqb p 0 then 0 else uw_cost u) 0) m' md' ->
reqA A' <= reqA A ->
RZAx A' md' T ms') ->
RZAx A md T (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_free A4H)) fc None m (seg_rom asegs)).
Definition obl_client_frame6 : Prop := forall A LB LM FR (B : bud6) m m' md, HEAPA6 A LB LM FR B m md ->
(forall a, 0 <= a < 2^64 ->
~ client_addr A4H (LB ++ LM) alloc_ceiling a ->
~ hl_scratch A4H a ->
~ (exists F k, In (F, k) FR /\ (F <= a < F + fr_size k - 8 \/ shad A4L F <= a < shad A4L F + fr_shadow_len k)) ->
m' (wa a) = m (wa a)) ->
(forall x, wview asegs m x <> None -> wview asegs m' x <> None) ->
mem_inv asegs m' ->
HEAPA6 A LB LM FR B m' md.
End OblN6.

Section OblN6ok.
Context {RC__ : Q6q3.RunConsts}.
Variable H6 : QZsi.heap_iface_A A4L.
Lemma OBL_MALLOC_N6_ok : obl_malloc_n6 H6 (fun _ => 0).
Proof.
unfold obl_malloc_n6. intros until u. intros HP ST LO LOS SPA HT ERR TP A0 N UW UWK BN BB BD BQ RQ K HGP.
assert (GP : gp = Z_to_bv 64 (hl_gp A4L)) by exact HGP.
eapply (QZsi.hiA_malloc A4L H6) with (B := B) (n := n) (u := u) (errv := errv) (lo := lo);
[ exact HP | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0
| exact N | exact UW | exact UWK | exact BN | exact BB | exact BD | exact BQ | ].
intros ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BLK HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' _ ERR' Hr BLK HP').
- lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Unshelve. eapply (heap_pres_mono); [exact HPR|]. intros b Hb. rewrite app_assoc. apply in_or_app. left. exact Hb.
Qed.
Lemma OBL_FREE_N6_ok : obl_free_n6 H6 (fun _ => 0).
Proof.
unfold obl_free_n6. intros until u. intros HP HPIN ST LO LOS SPA HT ERR TP A0 UPK BD K HGP.
assert (GP : gp = Z_to_bv 64 (hl_gp A4L)) by exact HGP.
eapply (QZsi.hiA_free A4L H6) with (B := B) (p := p) (u := u) (errv := errv) (lo := lo);
[ exact HP | exact HPIN | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0 | exact UPK | exact BD | ].
intros ms' m' c' A' r RS VM ST' HPR ERR' HP'.
eapply (K ms' m' c' A' r RS VM ST' _ ERR' HP').
- lia.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Unshelve. eapply (heap_pres_mono); [exact HPR|]. intros b Hb. rewrite app_assoc. apply in_or_app. left. exact Hb.
Qed.
Lemma OBL_CLIENT_FRAME6_ok : obl_client_frame6 H6.
Proof. unfold obl_client_frame6. intros. eapply (QZsi.heapA_client_frame A4L H6); eassumption. Qed.
End OblN6ok.
