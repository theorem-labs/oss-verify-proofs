(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Mem MState Cells Step CellsX Frame PropExec Asn1Aux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow AEvtA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import ARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_oidv.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT AImgGlobals A_oid.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxARt.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import StepA. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_LxAOid () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.Lib.Step.ro_cells"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.CB"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C4"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.le_bytes_to_word"].


Tactic Notation "lx_bcmpA" constr(SPB) constr(spf) constr(RODATA) constr(len) constr(HXS) :=
  let RO := fresh "RO" in let ORO := fresh "ORO" in
  let nn := eval vm_compute in (Z.to_nat len) in
  ro_str RODATA nn as RO; img_aobj RODATA len as ORO;
  lazymatch goal with |- evtA _ _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch type of HXS with bytes_at _ mx ?qq ?qqs =>
    lazymatch goal with HH : HM _ _ _ ?hh ?lb ?lf mx |- _ =>
    lazymatch goal with STK : stk _ mx ?lo0 _ |- _ =>
      callxA_sp spf
        (eapply SPB with (h := hh) (LB := lb) (LF := lf) (P := RODATA) (Q := qq) (n := len) (lo := lo0) (qs := qqs);
         rewrite ?(unsigned_lit spf) by plia;
         first [ exact RO | exact HXS | exact ORO | eassumption | reflexivity | plia
               | match goal with H : aobj _ _ _ _ _ _ |- aobj _ _ _ _ _ _ => eapply aobj_sub; [exact H | plia | plia] end
               | match goal with H : crange _ _ _ |- crange _ _ _ => eapply crange_sub; [exact H | plia | plia] end
               | pose proof (@alloc_ceiling_bounds _); pose proof (@alloc_ceiling_pos _); plia
               | match goal with |- ?g => idtac "BCMP-SIDE:" g end ])
    end end end
  end;
  try clear RO ORO.

(* [comment removed for export] *)
Lemma le4_le_bytes_to_word : forall bs, length bs = 4%nat -> le4 (le_bytes_to_word bs) = bs.
Proof.
  intros bs Hl. unfold le4, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  change (bv_wrap 64 ?x) with (x mod 2^64).
  rewrite (Mem.Z_to_le_bytes_mod 4 _ 64) by (cbn; lia). rewrite <- Hl. apply Asn1Aux.Z_to_le_bytes_to_Z.
Qed.

Lemma ro_cells_CB4_C4 : ltac2:(CDefT.buildp (gd_tbl_LxAOid ()) "Psegs,(0.$1.)Pm,P,(2.&40.)(3.(2.&8.))PA,$4.Pbs,(0.(2.&8.))P,(5.R4.R3.R2.(6.$7.(8.#4.R1.)(9.$7.)))(5.R5.R4.R3.(6.$7.(:.(;.R2.))(9.$7.)))")
(* [comment removed for export] *).
Proof.
  intros segs m A bs [Hwf Hb]. cbn in Hwf.
  split. { cbn. tauto. }
  cbn [cells_bytes cbytes] in *. rewrite le4_le_bytes_to_word by tauto. exact Hb.
Qed.

(* [comment removed for export] *)
Ltac lx_tbl_attr1 a :=
  let H := fresh "TBA" in
  tbl_cells a 4%nat as H;
  apply ro_cells_CB4_C4 in H;
  lazymatch type of H with ro_cells _ _ _ (C4 (le_bytes_to_word ?bs) :: nil) =>
    let k := eval vm_compute in (bv_unsigned (le_bytes_to_word bs)) in
    replace (le_bytes_to_word bs) with (Z_to_bv 64 k) in H by (apply bv_eq; vm_compute; reflexivity)
  end.
Ltac lx_tbl_attrs base offs koff :=
  let l := eval cbv in offs in
  let b := eval cbv delta [base] in base in
  let rec go l := lazymatch l with
    | nil => idtac
    | cons ?k ?rest => let a := eval cbv in (b + k + koff) in lx_tbl_attr1 a; go rest
    end in
  go l.

(* [comment removed for export] *)
Ltac lx_oid_vres :=
  lazymatch goal with
  | |- oid_vres _ _ _ _ =>
      first [ apply oid_vres_notfound
            | apply oid_vres_found; rewrite unsigned_lit by (clear; cbn; lia); lx_solve_in ]
  end.
#[export] Ltac lx_app_hook ::= first [ lx_rw_sub | lx_rw_join | lx_rw_blob | lx_opqa | lx_oid_vres ].
