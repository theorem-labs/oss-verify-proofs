(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QzWc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfOM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc8V.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgTW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgTW.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy2A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPC3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPC3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPZI.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qu4M.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QG8z. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLbz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qa8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qa8x.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2Sr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzoi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qzoi.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qb4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qb4w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qzoi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qzoi. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTd1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTd1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTd1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTd1.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qyk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qyk8.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5CI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5CI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWt1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWt1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuXw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuXw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qjal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qjal. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9PQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9PQ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QD6K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QD6K.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QtfO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QtfO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLAQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLAQ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXKA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QU48.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QU48.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Unset Keyed Unification.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section ParseExP.
Variable HIx : heap_iface S4L.

#[using="Type"] Lemma auxv_hi : forall A LB m md, HEAP S4L HIx A LB m md -> exists aw keys, auxv_at m aw keys /\ hi_top S4L HIx <= aw.
Proof. intros A LB m md HP. destruct (heap_auxv S4L HIx A LB m md HP) as (aw & keys & B & H). exists aw, keys. split; [exact B | exact H]. Qed.

Definition hash_ok : lh_char_hash_stmt HIx model_vm_only 8320 :=
lh_char_hash_cps HIx model_vm_only model_vm_only_refl 400 ltac:(lia) (seed_settle HIx auxv_hi 400 ltac:(lia)) 8320 ltac:(lia).

Definition oadd_ok : jo_object_add_P HIx := json_object_object_add_cps HIx (json_object_put_P HIx) hash_ok.

Definition HC_null : forall pf q LBc payload me lo sv T F0, CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_null :=
fun pf q LBc payload me lo sv T F0 => case_null HIx memmove_spec pf q LBc payload me lo sv T F0 utf8rep.
Definition HC_bool : forall pf q LBc payload me lo sv T F0, CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_boolean :=
fun pf q LBc payload me lo sv T F0 => case_bool HIx memmove_spec pf q LBc payload me lo sv T F0 utf8rep.
Definition HC_inf : forall pf q LBc payload me lo sv T F0, CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_inf :=
fun pf q LBc payload me lo sv T F0 => case_inf HIx pf q LBc payload me lo sv T F0 utf8rep.

Definition HC_number : forall pf q LBc payload me lo sv T F0, CASE HIx pf q LBc payload me lo sv T F0 utf8rep ST_number :=
fun pf q LBc payload me lo sv T F0 => case_number HIx pf q LBc payload me lo sv T F0 utf8rep
memmove_spec strtoll_spec strtoull_spec (QgTW.Mq1.rstrtod_proof : Qy2A.rstrtod_stmt) (strdup_cps HIx).

Definition json_tokener_parse_ex_P :=
json_tokener_parse_ex_cps HIx
(json_object_put_P HIx) uselocale_ok errno_location_ok (duplocale_ok HIx) (newlocale_ok HIx) (freelocale_ok HIx)
memmove_spec (strdup_cps HIx)
(json_object_array_add_cps HIx) (json_object_array_shrink_cps HIx) oadd_ok
(json_object_new_object_cps HIx) (json_object_new_array_cps HIx)
HC_null HC_bool HC_number HC_inf.

Definition json_tokener_parse_ex_c_P :=
json_tokener_parse_ex_c_cps HIx
(json_object_put_P HIx) uselocale_ok errno_location_ok (duplocale_ok HIx) (newlocale_ok HIx) (freelocale_ok HIx)
memmove_spec (strdup_cps HIx)
(json_object_array_add_cps HIx) (json_object_array_shrink_cps HIx) oadd_ok
(json_object_new_object_cps HIx) (json_object_new_array_cps HIx)
HC_null HC_bool HC_number HC_inf.
End ParseExP.

End RC__1.
