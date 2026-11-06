(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs RefMemcpyLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_app2 A_rt_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4A_kfn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.M4A_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4A_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Section SSF.
Variable E : valu.
Variable ms : machine_state.
Hypothesis Hd : sden ASEGS E SSF5_P0 ms.
Local Abbreviation u x := (bv_unsigned (E x%positive)).
Local Abbreviation m0 := (ms_mem ms).

#[using="Type"] Lemma Bnd : forall x : positive, 0 <= bv_unsigned (E x) < two64.
Proof. LiaFast.lf_pins LiaFast.u0. intros x. pose proof (bv_unsigned_in_range _ (E x)) as X. unfold bv_modulus in X. exact X. Qed.

Ltac open_ssf :=
  destruct (sden_0 _ _ _ _ Hd) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm);
  cbn [s_pc s_regs s_rgs s_facts s_resv SSF5_P0] in Hpc, Hresv, HR, HG, HD, HF;
  unfold SSF5_RGS, relro_rgs in HG; cbn [app] in HG;
  apply Forall_cons_iff in HG as [R0 HG]; apply Forall_cons_iff in HG as [R1 HG]; apply Forall_cons_iff in HG as [R2 HG];
  apply Forall_cons_iff in HG as [R3 HG]; clear HG.
Ltac open_facts :=
  destruct (sden_0 _ _ _ _ Hd) as (_ & _ & _ & _ & _ & _ & HF & _); cbn [s_facts SSF5_P0] in HF;
  unfold SSF5_F, rt_facts, two_class, two_class4k, stack_facts in HF; cbn [app] in HF;
  repeat match goal with H : Forall _ (_ :: _) |- _ => apply Forall_cons_iff in H as [?F H] end;
  cbn [fact_ok] in *;
  repeat match goal with H : context [lden E ?l] |- _ => progress lnorm_s_in H end;
  rewrite ?u_Z_to_bv in *; unfold vz in *; unfold KHI, KTOP, IMG_END, SH_LO in *.

#[using="ms Hd"] Lemma ssf_facts : u 5 mod 2 = 0 /\ 0 <= u 12 <= 1023 /\ 6529024 <= 4096 * u 10 /\ 4096 * u 10 + 11571200 <= 2 ^ 47.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  open_facts. pose proof (Bnd 10) as B10. change (2 ^ 1) with 2 in F. refine (conj F (conj F0 _)).
  clear -F1; change (6529024 / 4096) with 1594 in F1; change ((2 ^ 47 - 11571200) / 4096) with 34359735543 in F1; lia.
Qed.

Definition A0 : Z := 2147450880 + 512 * u 10 + 528896 + 128 * u 12.

#[using="ms Hd"] Lemma ssf_a0 : bv_unsigned (lden E SHSLOT4) = A0.
Proof. LiaFast.lf_pins (fun (ms Hd : LiaFast.U) => LiaFast.u0).
  pose proof ssf_facts as (_ & P & F1 & F2). pose proof (Bnd 10). pose proof (Bnd 12).
  unfold SHSLOT4, fsh, AR4, P4, FSP, SHB. ubase_s. rewrite Z.mod_small; [unfold A0; ring | unfold two64 in *; lia].
Qed.

#[using="Hd"] Lemma ssf_regs : getr (ms_regs ms) 10 = lden E SHSLOT4 /\ getr (ms_regs ms) 11 = Z_to_bv 64 128 /\ getr (ms_regs ms) 1 = E 5%positive.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_ssf. refine (conj _ (conj _ _)).
  - pose proof (HR 10%bv) as X. rget_norm_in X. exact X.
  - pose proof (HR 11%bv) as X. rget_norm_in X. rewrite X. reflexivity.
  - pose proof (HR 1%bv) as X. rget_norm_in X. rewrite X. apply lden_lvar.
Qed.

#[using="Hd"] Lemma ssf_old : exists old, u8arr ASEGS m0 A0 old /\ length old = 128%nat.
Proof. LiaFast.lf_pins (fun (Hd : LiaFast.U) => LiaFast.u0).
  open_ssf. apply (u8arr_of_stk ASEGS). apply (stk_of_rg ASEGS E _ _ _ _ R1 ltac:(left; reflexivity)).
  - exact ssf_a0.
  - unfold rsz. cbn [rg_size]. change (bv_unsigned (lden E (lconst 128))) with 128. lia.
Qed.

#[using="E Hd"] Lemma ssf_pr : pristine m0 888832 909312 /\ pristine m0 911824 912216.
Proof. LiaFast.lf_pins (fun (E Hd : LiaFast.U) => LiaFast.u0).
  open_ssf. split.
  - exact (pristine_of_rg_ro ASEGS E _ _ 888832 20480 R2 eq_refl eq_refl eq_refl).
  - exact (pristine_of_rg_ro ASEGS E _ _ 911824 392 R3 eq_refl eq_refl eq_refl).
Qed.

#[using="Type"] Lemma rg_disj_sym : forall R1 R2, rg_disj E R1 R2 -> rg_disj E R2 R1.
Proof. LiaFast.lf_pins LiaFast.u0. unfold rg_disj. intros R1 R2 H. lia. Qed.

Section Run.
Hypothesis SSF : set_shadow_f5_stmt.

Definition Eq (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : valu :=
  upds E [(205%positive, t0); (206%positive, t1); (207%positive, t2); (210%positive, a0); (211%positive, a1); (212%positive, a2);
          (213%positive, a3); (214%positive, a4); (215%positive, a5); (216%positive, a6); (217%positive, a7); (228%positive, t3);
          (229%positive, t4); (230%positive, t5); (231%positive, t6)].
#[using="Type"] Lemma Eq_agree : forall t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6, agree 200 E (Eq t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
Proof. LiaFast.lf_pins LiaFast.u0. intros. apply upds_agree. repeat constructor; cbn [fst]; lia. Qed.

#[using="Hd SSF"] Lemma ssf_run : exists ms' E', isteps ASEGS ms ms' /\
  sden ASEGS E' (with_pc SSF5_Q (bv_unsigned (lden E (rget (s_regs SSF5_P0) ra_key)))) ms' /\
  agree (s_next SSF5_P0) E E' /\ (forall x, fr_pt E (s_rgs SSF5_P0) x -> ms_mem ms' x = ms_mem ms x).
Proof. LiaFast.lf_pins (fun (Hd SSF : LiaFast.U) => LiaFast.u0).
  pose proof ssf_regs as (Ra0 & Ra1 & Rra). pose proof ssf_facts as (Fra & FP4 & FS1 & FS2). pose proof ssf_a0 as VA.
  destruct ssf_old as (old & OLD & Lold). pose proof ssf_pr as (PR1 & PR2).
  open_ssf.
  pose proof (SSF (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4) (getr (ms_regs ms) 5)
                 (getr (ms_regs ms) 6) (getr (ms_regs ms) 7) (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10)
                 (getr (ms_regs ms) 11) (getr (ms_regs ms) 12) (getr (ms_regs ms) 13) (getr (ms_regs ms) 14) (getr (ms_regs ms) 15)
                 (getr (ms_regs ms) 16) (getr (ms_regs ms) 17) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19) (getr (ms_regs ms) 20)
                 (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24) (getr (ms_regs ms) 25)
                 (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (getr (ms_regs ms) 28) (getr (ms_regs ms) 29) (getr (ms_regs ms) 30)
                 (getr (ms_regs ms) 31) (ms_fregs ms) (ms_fcsr ms) m0 old) as K.
  assert (HK : evt ASEGS (set_shadow_post (getr (ms_regs ms) 1) (getr (ms_regs ms) 2) (getr (ms_regs ms) 3) (getr (ms_regs ms) 4)
                 (getr (ms_regs ms) 8) (getr (ms_regs ms) 9) (getr (ms_regs ms) 10) (getr (ms_regs ms) 18) (getr (ms_regs ms) 19)
                 (getr (ms_regs ms) 20) (getr (ms_regs ms) 21) (getr (ms_regs ms) 22) (getr (ms_regs ms) 23) (getr (ms_regs ms) 24)
                 (getr (ms_regs ms) 25) (getr (ms_regs ms) 26) (getr (ms_regs ms) 27) (ms_fregs ms) (ms_fcsr ms) 245
                 (bv_unsigned (getr (ms_regs ms) 11)) m0) (kms ASEGS ms)).
  { unfold kms. rewrite Hpc, Hresv. apply K; clear K.
    - rewrite Ra0, VA. exact OLD.
    - rewrite Ra1, Lold. reflexivity.
    - rewrite Ra0, VA. unfold A0. replace (2147450880 + 512 * u 10 + 528896 + 128 * u 12) with ((268431360 + 64 * u 10 + 66112 + 16 * u 12) * 8) by ring.
      apply Z_mod_mult.
    - exact PR1.
    - exact PR2.
    - rewrite Ra0, Ra1, VA. change (bv_unsigned (Z_to_bv 64 128)) with 128. right. unfold A0. lia.
    - rewrite Rra. exact Fra. }
  clear K.
  destruct (kit_run ASEGS _ ms Hsvc HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & Hms2 & MU & WM & ARR).
  subst ms2. rewrite Ra0, VA, Ra1 in MU. rewrite Ra0, VA, Ra1 in ARR. change (bv_unsigned (Z_to_bv 64 128)) with 128 in MU, ARR.
  assert (Hmem : ms_mem ms1 = m') by (destruct Heq as (_ & _ & _ & _ & _ & _ & X & _); exact X).
  set (E' := Eq t0 t1 t2 (getr (ms_regs ms) 10) a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6).
  assert (AG : agree 200 E E') by apply Eq_agree.
  exists ms1, E'. split; [exact Hst|]. split; [|split].
  - eapply (sden_of_kit ASEGS _ _ ms1); [ | | exact Heq | | exact Hfrm | | | | ].
    + rewrite state_wf_with_pc. exact (proj1 (proj2 SSF5_wf)).
    + reflexivity.
    + cbn [s_pc with_pc s_regs SSF5_P0]. rget_norm. change (lden E {| l_c := 0; l_t := [(5%positive, 1)] |}) with (lden E (lvar 5)).
      rewrite lden_lvar, Z_to_bv_bv_unsigned, <- Rra. apply ret_pc_even_w. rewrite Rra. exact Fra.
    + (* [comment removed for export] *)
      apply regs_ok_of_cases. intros n Hn. cbn [s_regs with_pc SSF5_Q].
      do 32 (destruct n as [|n];
               [ getr_mkR_norm; rget_norm;
                 first [ reflexivity
                       | (rewrite (HR _); rget_norm; symmetry; apply (lden_agree 200 E E'); [vm_compute; reflexivity | exact AG])
                       | (symmetry; exact (lden_lvar E' _)) ]
               |]).
      lia.
    + (* [comment removed for export] *)
      cbn [s_rgs with_pc SSF5_Q]. unfold SSF5_RGS, relro_rgs. cbn [app].
      assert (UW : forall R, rg_ok ASEGS E m0 R -> rg_disj E R (RG SHSLOT4 (lconst 128) RW TEmpty) -> rwf 200 R = true -> rg_ok ASEGS E' m' R).
      { intros R HR0 Hdj Hw. apply (rg_ok_agree ASEGS 200 E _ _ R Hw AG). apply (rg_ok_munch ASEGS E m0 m' R _ HR0 MU).
        intros k Hk. unfold rg_disj, rsz in Hdj. cbn [rg_base rg_size] in Hdj. rewrite ssf_a0 in Hdj.
        change (bv_unsigned (lden E (lconst 128))) with 128 in Hdj. unfold rsz in Hk. cbn [Frame.outside]. split; [|exact I].
        pose proof (u_lden_range E (rg_base R)) as U. pose proof (rg_flat ASEGS E m0 R HR0) as (F1 & F2). unfold rsz in F2. lia. }
      assert (D01 : rg_disj E (RG SWB SWS RW TEmpty) (RG SHSLOT4 (lconst 128) RW TEmpty)).
      { destruct HD as (HD0 & _). unfold SSF5_RGS, relro_rgs in HD0. cbn [app] in HD0. apply Forall_cons_iff in HD0 as [X _]. exact X. }
      assert (D12 : rg_disj E (RG SHSLOT4 (lconst 128) RW TEmpty) (RGz (lconst 0xd9000) 0x5000 RO TEmpty)).
      { destruct HD as (_ & HD1 & _). apply Forall_cons_iff in HD1 as [X _]. exact X. }
      assert (D13 : rg_disj E (RG SHSLOT4 (lconst 128) RW TEmpty) (RGz (lconst 0xde9d0) 0x188 RO TEmpty)).
      { destruct HD as (_ & HD1 & _). apply Forall_cons_iff in HD1 as [_ X]. apply Forall_cons_iff in X as [X _]. exact X. }
      constructor; [apply UW; [exact R0 | exact D01 | vm_compute; reflexivity]|].
      constructor.
      { apply (track_of_bytes_at ASEGS E' m' _ 0 _); [ | lia | unfold rsz; cbn [rg_size]; change (bv_unsigned (lden E' (lconst 128))) with 128; cbn; lia | ].
        - eapply (rg_ok_agree ASEGS 200 E _ _ _); [vm_compute; reflexivity | exact AG |].
          eapply (rg_ok_of_u8arr ASEGS E m' _ A0); [reflexivity | reflexivity | exact ssf_a0 | | exact ARR].
          rewrite repeat_length. reflexivity.
        - cbn [rg_base]. assert (LB : lden E' SHSLOT4 = lden E SHSLOT4) by (symmetry; apply (lden_agree 200 E E'); [vm_compute; reflexivity | exact AG]).
          rewrite LB, ssf_a0, Z.add_0_r. rewrite map_repeat. exact (proj1 ARR). }
      constructor; [apply UW; [exact R2 | apply rg_disj_sym; exact D12 | vm_compute; reflexivity]|].
      constructor; [apply UW; [exact R3 | apply rg_disj_sym; exact D13 | vm_compute; reflexivity]|].
      constructor.
    + (* [comment removed for export] *)
      apply (rgs_disj_agree 200 E); [vm_compute; reflexivity | exact AG |].
      apply (rgs_disj_shape E (s_rgs SSF5_P0)); [apply shape_eqb_eq; exact (proj2 (proj2 SSF5_wf)) | exact HD].
    + (* [comment removed for export] *)
      cbn [s_facts with_pc SSF5_Q].
      assert (Hw : forallb (fwf 200) SSF5_F = true) by (vm_compute; reflexivity).
      rewrite forallb_forall in Hw. rewrite Forall_forall in HF |- *. intros f Hf.
      exact (fact_ok_agree 200 E _ f (Hw f Hf) AG (HF f Hf)).
  - exact AG.
  - intros x Hx. rewrite Hmem. apply MU. destruct Hx as [Hout|Hrt].
    + unfold FxStep.outside in Hout. unfold SSF5_RGS, relro_rgs in Hout. cbn [app] in Hout.
      apply Forall_cons_iff in Hout as [_ Hout]. apply Forall_cons_iff in Hout as [O1 _].
      unfold rsz in O1. cbn [rg_base rg_size] in O1. rewrite ssf_a0 in O1. change (bv_unsigned (lden E (lconst 128))) with 128 in O1.
      cbn [Frame.outside]. split; [lia | exact I].
    + exfalso. apply Exists_exists in Hrt as (R & HRin & Hrt & _). unfold SSF5_RGS, relro_rgs in HRin. cbn [app] in HRin.
      repeat (destruct HRin as [<-|HRin]; [cbn in Hrt; discriminate|]). destruct HRin.
Qed.
End Run.
End SSF.

Theorem ssf5_kfn : set_shadow_f5_stmt -> kfn_ok ASEGS SSF5_P0 SSF5_Q.
Proof. intros SSF E ms Hd. exact (ssf_run E ms Hd SSF). Qed.
