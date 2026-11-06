From Stdlib Require Import String ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib reac_ctrl_kind_name_c.
Import ListNotations.
Open Scope Z_scope.

Lemma kind_name_rel_bytes_length : length kind_name_rel_bytes = 56%nat.
Proof. reflexivity. Qed.

Ltac rel_entry m HT k :=
  let A := eval vm_compute in (KIND_NAME_REL + 4 * k) in
  let bs := eval vm_compute in (firstn 4 (skipn (Z.to_nat (4 * k)) kind_name_rel_bytes)) in
  let HR := fresh "HR" in
  assert (HR : ov_read_bytes rsegs m (wa A) 4 = Some bs)
    by (change A with (KIND_NAME_REL + 4 * k);
        rewrite (bytes_at_read rsegs m KIND_NAME_REL kind_name_rel_bytes (4 * k) 4 HT)
          by (rewrite ?kind_name_rel_bytes_length;
              first [ lia | let n := eval vm_compute in (Z.to_nat (4 * k)) in change (Z.to_nat (4 * k)) with n; lia ]);
        vm_compute; reflexivity).

Lemma kind_name_addr_big : forall x, 13 < x -> kind_name_addr x = QMARK.
Proof. intros x Hx. unfold kind_name_addr. rewrite (proj2 (Z.leb_gt x 13) Hx). reflexivity. Qed.

Theorem reac_ctrl_kind_name_holds : reac_ctrl_kind_name_contract.
Proof.
  unfold reac_ctrl_kind_name_contract, REAC_CTRL_KIND_NAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HT HS.
  pose proof (HS (bv_unsigned a0) (proj1 (bv_unsigned_in_range 64 a0))) as HSa.
  rel_entry m HT 0. rel_entry m HT 1. rel_entry m HT 2. rel_entry m HT 3. rel_entry m HT 4.
  rel_entry m HT 5. rel_entry m HT 6. rel_entry m HT 7. rel_entry m HT 8. rel_entry m HT 9.
  rel_entry m HT 10. rel_entry m HT 11. rel_entry m HT 12. rel_entry m HT 13.
  step. step.
  if_cases E; zify_cond E.
  - destruct (rc_word_le13 a0 ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]].
    all: do 7 step; rc_wrap_lits.
    all: apply evt_done; eexists; split; [reflexivity | exact HSa].
  - step. step. step.
    apply evt_done. eexists. split; [|exact HSa].
    rewrite (kind_name_addr_big (bv_unsigned a0)) by lia. reflexivity.
Qed.

Lemma reac_ctrl_kind_name_in_image : forall m, mem_inv rsegs m ->
  bytes_at rsegs m KIND_NAME_REL kind_name_rel_bytes /\ kind_name_strings m.
Proof.
  intros m Hm. split.
  - apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity].
  - intros x Hx. destruct (Z.leb_spec x 13) as [Hle|Hgt].
    + destruct (rc_Z_le13 x ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]];
        (apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity]).
    + rewrite (kind_name_addr_big x Hgt), (kind_name_big x Hgt).
      apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity].
Qed.
