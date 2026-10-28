(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc8V.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UgTW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UgTW.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uy2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPC3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPC3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uu4M.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uu4M.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua8x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua8x.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uzoi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uzoi.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ub4w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ub4w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uzoi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uzoi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTd1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTd1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTd1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTd1.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uyk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uyk8.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U5CI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U5CI. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWt1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWt1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UuXw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UuXw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ujal.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ujal. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U9PQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U9PQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UD6K.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UD6K.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtfO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtfO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULAQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULAQ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXKA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXKA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UU48.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UU48.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
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
memmove_spec strtoll_spec strtoull_spec (UgTW.Mq1.rstrtod_proof : Uy2A.rstrtod_stmt) (strdup_cps HIx).

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
