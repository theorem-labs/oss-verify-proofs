From Stdlib Require Import String ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes Image ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcLeafLib RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import RcAsanRT reac_ctrl_kind_name_c.
Import ListNotations.
Open Scope Z_scope.

Lemma kn_bytes_length : length kind_name_bytes = 112%nat.
Proof. reflexivity. Qed.

Lemma kn_table_in_image :
  match image_bytes rsegs KIND_NAME 112 with
  | Some bs => if list_eq_dec (@bv_eq_dec 8) bs kind_name_bytes then true else false
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

Lemma kn_addr_big : forall x, 13 < x -> kind_name_addr x = QMARK.
Proof. intros x Hx. unfold kind_name_addr. rewrite (proj2 (Z.leb_gt x 13) Hx). reflexivity. Qed.

Lemma kn_str_below : forall x, 0 <= x ->
  kind_name_addr x + Z.of_nat (length (cstr_bytes (kind_name x))) <= KIND_NAME.
Proof.
  intros x Hx. destruct (Z.leb_spec x 13) as [Hle|Hgt].
  - destruct (rc_Z_le13 x ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]];
      vm_compute; intro H; discriminate H.
  - rewrite (kn_addr_big x Hgt), (kind_name_big x Hgt). vm_compute. intro H. discriminate H.
Qed.

Lemma kn_shadow0 : forall m off W i,
  asan_shadow_rd rsegs m off KIND_NAME 112 W -> asan_addressable rsegs m off KIND_NAME 112 ->
  asan_rt3 rsegs m off KIND_NAME 112 -> 0 <= i <= 13 ->
  ov_read_bytes rsegs m (wa ((KIND_NAME + 8 * i) / 8 + off)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m off W i HSR HAD H3 Hi.
  destruct (asan_shadow_read_at rsegs m off KIND_NAME 112 W (8 * i) ((KIND_NAME + 8 * i) / 8 + off) HSR
              ltac:(lia) eq_refl) as (k & RK & BK).
  pose proof (asan_check_8 rsegs m off KIND_NAME 112 (8 * i) k HAD H3 ltac:(lia) ltac:(lia)
                ltac:(unfold KIND_NAME; Z.div_mod_to_equations; lia) BK) as K0.
  replace (Z_to_bv 8 0) with k; [exact RK|].
  apply bv_eq. rewrite (rc_signed0_unsigned0 k K0). reflexivity.
Qed.

Ltac tab_entry m HT k :=
  let A := eval vm_compute in (KIND_NAME + 8 * k) in
  let bs := eval vm_compute in (firstn 8 (skipn (Z.to_nat (8 * k)) kind_name_bytes)) in
  let HR := fresh "HR" in
  assert (HR : ov_read_bytes rsegs m (wa A) 8 = Some bs)
    by (change A with (KIND_NAME + 8 * k);
        rewrite (bytes_at_read rsegs m KIND_NAME kind_name_bytes (8 * k) 8 HT)
          by (rewrite ?kn_bytes_length;
              first [ lia | let n := eval vm_compute in (Z.to_nat (8 * k)) in change (Z.to_nat (8 * k)) with n; lia ]);
        vm_compute; reflexivity).

Ltac sh_entry m off HSR HAD H3 k :=
  let L := eval vm_compute in ((KIND_NAME + 8 * k) / 8) in
  let HS := fresh "SH" in
  assert (HS : ov_read_bytes rsegs m (wa (L + off)) 1 = Some [Z_to_bv 8 0])
    by (change (L + off) with ((KIND_NAME + 8 * k) / 8 + off); apply (kn_shadow0 m off _ k HSR HAD H3); lia).

(* route (C): the proof below, formerly reac_ctrl_kind_name_holds's, proves the region form
   reac_ctrl_kind_name_contract_on (reac_ctrl_kind_name_c.v); reac_ctrl_kind_name_holds follows from it. *)
Theorem reac_ctrl_kind_name_holds_on : reac_ctrl_kind_name_contract_on.
Proof.
  unfold reac_ctrl_kind_name_contract_on, REAC_CTRL_KIND_NAME, REAC_CTRL_KIND_NAME_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    HT HS ST HLO HKT HCE HADR HW.
  pose proof (rt_asan_rt m _ HCE HW) as HRT.
  pose proof (rt_shadow_rd m KIND_NAME 112 _ HADR (fun x Hx => HW x (or_intror (or_intror Hx)))) as HSR.
  pose proof (rt_addressable m KIND_NAME 112 HADR) as HAD.
  pose proof (rt_rt3 m KIND_NAME 112 HADR) as H3.
  set (off := ASAN_K) in HRT, HSR, HAD, H3. clearbody off.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. change (bv_modulus 64) with (2^64) in Rsp.
  pose proof ST as (ST0 & _ & _).
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  assert (WVS : forall x, bv_unsigned sp - 16 <= x < bv_unsigned sp -> wview rsegs m (wa x) <> None)
    by (intros x Hx; apply (rc_wv_stk rsegs m lo (bv_unsigned sp)); [exact ST | lia]).
  assert (HSa : bytes_at rsegs m (kind_name_addr (bv_unsigned a0)) (cstr_bytes (kind_name (bv_unsigned a0))))
    by exact (HS (bv_unsigned a0) (proj1 (bv_unsigned_in_range 64 a0))).
  pose proof (kn_str_below (bv_unsigned a0) (proj1 (bv_unsigned_in_range 64 a0))) as HBL.
  pose proof kn_bytes_length as HTL.
  carve_frame 16%nat ST.
  step. step.
  match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
  pose proof (asan_rt_munch rsegs m m1 _ _ off _ _ HRT MU (fun x Hx => Hx)) as HRT1.
  pose proof (asan_shadow_rd_munch rsegs m m1 off KIND_NAME 112 _ _ HSR MU (fun x Hx => Hx)) as HSR1.
  pose proof (asan_addressable_munch rsegs m m1 off KIND_NAME 112 _ _ HAD HSR MU (fun x Hx => Hx)) as HAD1.
  pose proof (asan_rt3_munch rsegs m m1 off KIND_NAME 112 _ _ H3 HSR MU (fun x Hx => Hx)) as H31.
  pose proof (asan_rt_got_read rsegs m1 _ _ off _ HRT1) as RG.
  pose proof (asan_rt_cell_read rsegs m1 _ _ off _ HRT1) as RC.
  unfold GOT_CELL_K, CELL_K in RG, RC.
  tab_entry m1 HT 0. tab_entry m1 HT 1. tab_entry m1 HT 2. tab_entry m1 HT 3. tab_entry m1 HT 4.
  tab_entry m1 HT 5. tab_entry m1 HT 6. tab_entry m1 HT 7. tab_entry m1 HT 8. tab_entry m1 HT 9.
  tab_entry m1 HT 10. tab_entry m1 HT 11. tab_entry m1 HT 12. tab_entry m1 HT 13.
  sh_entry m1 off HSR1 HAD1 H31 0. sh_entry m1 off HSR1 HAD1 H31 1. sh_entry m1 off HSR1 HAD1 H31 2.
  sh_entry m1 off HSR1 HAD1 H31 3. sh_entry m1 off HSR1 HAD1 H31 4. sh_entry m1 off HSR1 HAD1 H31 5.
  sh_entry m1 off HSR1 HAD1 H31 6. sh_entry m1 off HSR1 HAD1 H31 7. sh_entry m1 off HSR1 HAD1 H31 8.
  sh_entry m1 off HSR1 HAD1 H31 9. sh_entry m1 off HSR1 HAD1 H31 10. sh_entry m1 off HSR1 HAD1 H31 11.
  sh_entry m1 off HSR1 HAD1 H31 12. sh_entry m1 off HSR1 HAD1 H31 13.
  step. step.
  if_cases E; zify_cond E.
  - destruct (rc_word_le13 a0 ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]].
    all: do 11 step; if_false; do 4 step.
    all: release_frame FR ST (bv_unsigned sp).
    all: apply evt_done; cbv beta; do 3 eexists; split; [reflexivity|].
    all: split; [exact MU|]; split; [exact WM|].
    all: split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WVS)|].
    all: split; [exact ST | exact HSa].
  - do 6 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. cbv beta. do 3 eexists. split.
    { rewrite (kn_addr_big (bv_unsigned a0)) by lia. reflexivity. }
    split; [exact MU|]. split; [exact WM|].
    split; [intros HI; exact (rc_mem_inv_frame rsegs m m1 _ _ HI MU WVS)|].
    split; [exact ST | exact HSa].
Qed.

Theorem reac_ctrl_kind_name_holds : reac_ctrl_kind_name_contract.
Proof. exact (reac_ctrl_kind_name_contract_of_on reac_ctrl_kind_name_holds_on). Qed.

Lemma reac_ctrl_kind_name_strings_in_image : forall m, mem_inv rsegs m -> kind_name_strings m.
Proof.
  intros m Hm x Hx. destruct (Z.leb_spec x 13) as [Hle|Hgt].
  - destruct (rc_Z_le13 x ltac:(lia)) as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]]];
      (apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity]).
  - rewrite (kn_addr_big x Hgt), (kind_name_big x Hgt).
    apply rc_ro_in_image; [exact Hm | vm_compute; reflexivity].
Qed.
