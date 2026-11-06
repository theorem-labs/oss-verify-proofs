(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require RelSpec SimInv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.RelSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SimInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim.ExitSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.

Module Hoare.
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition at_ (base : word) (d : Z) : word := Z_to_bv 64 (bv_unsigned base + d).

Lemma at_0 : forall base, at_ base 0 = base.
Proof.
  intros base. unfold at_. rewrite Z.add_0_r. apply bv_eq.
  rewrite Z_to_bv_unsigned. apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma at_addi : forall base d e, v_addi (at_ base d) e = at_ base (d + e).
Proof.
  intros base d e. unfold at_, v_addi. apply bv_eq.
  rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma at_at : forall base d e, at_ (at_ base d) e = at_ base (d + e).
Proof. exact at_addi. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma at_self : forall a : word, Z_to_bv 64 (bv_unsigned a + 0) = a.
Proof. intros a. exact (at_0 a). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition assn := bvmap 5 word -> (word -> option byte) -> (word -> option byte) -> Prop.

(* [comment removed for export] *)
Definition regset := reg -> Prop.
Definition memset := word -> Prop.

Definition regs_agree (C : regset) (regs regs' : bvmap 5 word) : Prop :=
  forall r, ~ C r -> getr regs' r = getr regs r.

Definition mem_agree (W : memset) (m m' : word -> option byte) : Prop :=
  forall x, ~ W x -> m' x = m x.

Lemma regs_agree_refl : forall C regs, regs_agree C regs regs.
Proof. intros C regs r _. reflexivity. Qed.

(* [comment removed for export] *)

Lemma regs_agree_trans : forall C regs1 regs2 regs3,
  regs_agree C regs1 regs2 -> regs_agree C regs2 regs3 -> regs_agree C regs1 regs3.
Proof. intros C r1 r2 r3 H1 H2 r Hr. rewrite (H2 r Hr). apply H1, Hr. Qed.

(* [comment removed for export] *)

Lemma regs_agree_mono : forall (C C' : regset) regs regs',
  (forall r, C r -> C' r) -> regs_agree C regs regs' -> regs_agree C' regs regs'.
Proof. intros C C' regs regs' Hsub H r Hr. apply H. intro; apply Hr, Hsub; assumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma regs_agree_upd : forall (C : regset) regs regs' r v,
  C r -> regs_agree C regs regs' -> regs_agree C regs (regupd regs' r v).
Proof.
  intros C regs regs' r v Hin H s Hs.
  rewrite getr_other by (intro Heq; subst; contradiction).
  apply H, Hs.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition triple (segs : list Segment)
                  (C : regset) (W : memset)
                  (P : assn) (a b : word) (Q : assn) : Prop :=
  forall regs mem rom, P regs mem rom ->
    exists regs' mem',
      msteps segs (mkst regs a mem rom) (mkst regs' b mem' rom)
      /\ Q regs' mem' rom
      /\ regs_agree C regs regs'
      /\ mem_agree W mem mem'.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition frameable (C : regset) (W : memset) (R : assn) : Prop :=
  forall regs mem rom regs' mem',
    regs_agree C regs regs' -> mem_agree W mem mem' ->
    R regs mem rom -> R regs' mem' rom.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ret_ok (k : word) : Prop := v_jalr k 0 = k.

Lemma land_m2_even : forall z : Z, (z mod 2 = 0)%Z -> Z.land z (-2) = z.
Proof.
  intros z Hz.
  assert (Hl : Z.land z 1 = 0%Z).
  { replace 1%Z with (Z.ones 1) by reflexivity. rewrite Z.land_ones by lia. exact Hz. }
  replace (-2)%Z with (Z.lnot 1) by reflexivity.
  rewrite <- Z.ldiff_land.
  rewrite <- (Z.lor_ldiff_and z 1) at 2.
  rewrite Hl, Z.lor_0_r. reflexivity.
Qed.

Lemma ret_ok_even : forall k, (bv_unsigned k mod 2 = 0)%Z -> ret_ok k.
Proof.
  intros k Hk. unfold ret_ok, v_jalr, jalr_tgtZ.
  rewrite Z.add_0_r, land_m2_even by exact Hk.
  apply bv_eq. rewrite Z_to_bv_unsigned.
  apply bv_wrap_small, bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Definition proc (segs : list Segment) (C : regset) (W : memset)
                (P : assn) (entry : word) (Q : assn) : Prop :=
  forall k : word, ret_ok k ->
    triple segs C W (fun regs mem rom => P regs mem rom /\ getr regs 1 = k) entry k Q.

(* [comment removed for export] *)
Definition ra_indep (P : assn) : Prop :=
  forall regs v mem rom, P regs mem rom -> P (regupd regs 1 v) mem rom.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End Hoare.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zmem (mem : word -> option byte) (b l : word) : word -> option byte :=
  fun a => if Z.leb (bv_unsigned b) (bv_unsigned a)
              && Z.ltb (bv_unsigned a) (bv_unsigned b + bv_unsigned l)
           then Some (Z_to_bv 8 0) else mem a.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma with_vmmaps_halted : forall h m, m_halted (with_vmmaps h m) = m_halted m.
Proof. reflexivity. Qed.
Lemma with_vmmaps_vm : forall h m, m_vmmaps (with_vmmaps h m) = h.
Proof. reflexivity. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_sys_input214 : forall segs ms x8,
  in_sysno (sys_input segs ms x8) = x8.
Proof. reflexivity. Qed.

Lemma in_arg0_sys_input214 : forall segs ms x8,
  in_arg (sys_input segs ms x8) 0 = ms_gpr ms 0.
Proof. reflexivity. Qed.


(* [comment removed for export] *)
Definition vm_model (h : VmMaps) : Model :=
  mkModel [] h IEof [] None None None.

Definition brk_grow_ok (h : VmMaps) (req r : word) : bool :=
  Mmap.brk_grow_ok (vm_model h) req r.

(* [comment removed for export] *)
Definition brk_r_ok (h : VmMaps) (req r : word) : Prop :=
  Mmap.brk_r_ok (vm_model h) req r = true.

(* [comment removed for export] *)
Definition brk_resolution_ok (m : Model) (req r : word) : Prop :=
  Mmap.brk_r_ok m req r = true.

(* [comment removed for export] *)
Definition brk_model (req r : word) (m : Model) : Model :=
  with_brk_next m req r.

Lemma alloc_forget_vm_ranges_halted : forall ranges m,
  m_halted (forget_vm_ranges ranges m) = m_halted m.
Proof.
  induction ranges as [|[a n] r IH]; intros m; [reflexivity|].
  cbn [forget_vm_ranges]. rewrite IH. reflexivity.
Qed.

Lemma alloc_brk_model_halted : forall req r m, m_halted (brk_model req r m) = m_halted m.
Proof.
  intros req r m. unfold brk_model, with_brk_next. cbv zeta.
  rewrite alloc_forget_vm_ranges_halted. reflexivity.
Qed.

Definition brk_refusable (m : Model) (req : word) : bool :=
  let h := m_vmmaps m in
  negb (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (Mmap.min_brk h)))
  && negb (bv_eqb req (vm_brk h))
  && negb (Mmap.brk_r_ok m req req).

Lemma brk_r_ok_keep : forall m req, Mmap.brk_r_ok m req (vm_brk (m_vmmaps m)) = true.
Proof.
  intros m req. unfold Mmap.brk_r_ok. unfold Mmap.brk_grow_ok. cbv zeta.
  rewrite (bv_eqb_refl (vm_brk (m_vmmaps m))), (Z.ltb_irrefl (bv_unsigned (vm_brk (m_vmmaps m)))).
  rewrite andb_false_r, !orb_true_r.
  destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (Mmap.min_brk (m_vmmaps m)))),
    (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps m)))); reflexivity.
Qed.

Lemma brk_r_ok_move_eq : forall m req r,
  (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (Mmap.min_brk (m_vmmaps m)))) = false ->
  Mmap.brk_r_ok m req r = true -> bv_eqb r (vm_brk (m_vmmaps m)) = false -> r = req.
Proof.
  intros m req r Hq H Hb. unfold Mmap.brk_r_ok in H. cbv zeta in H. rewrite Hq, Hb, orb_false_r in H.
  destruct (Z.ltb (bv_unsigned req) (bv_unsigned (vm_brk (m_vmmaps m)))) eqn:L;
    try rewrite L in H; cbv beta iota in H.
  - apply bv_eqb_eq in H. exact H.
  - apply andb_true_iff in H as [H _]. apply bv_eqb_eq in H. exact H.
Qed.

Lemma brk_refusable_false_of_grant : forall m req r,
  brk_resolution_ok m req r -> brk_refusal_b m req r = false -> brk_refusable m req = false.
Proof.
  intros m req r Hr Hnr. unfold brk_refusable. cbv zeta.
  destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (Mmap.min_brk (m_vmmaps m)))) eqn:Q;
    [reflexivity|].
  destruct (bv_eqb req (vm_brk (m_vmmaps m))) eqn:B; [reflexivity|].
  cbn [negb andb].
  assert (Hrb : bv_eqb r (vm_brk (m_vmmaps m)) = false).
  { unfold brk_refusal_b in Hnr. cbv zeta in Hnr. apply orb_false_iff in Q as [Q1 Q2].
    rewrite Q1, Q2 in Hnr. try rewrite B in Hnr. exact Hnr. }
  pose proof (brk_r_ok_move_eq m req r Q Hr Hrb) as E. subst r.
  unfold brk_resolution_ok in Hr. rewrite Hr. reflexivity.
Qed.

Lemma brk_grant_of_refusable_false : forall m req,
  brk_refusable m req = false -> exists r, brk_resolution_ok m req r /\ brk_refusal_b m req r = false.
Proof.
  intros m req Hf. unfold brk_refusable in Hf. cbv zeta in Hf.
  destruct (w_is0 req || Z.ltb (bv_unsigned req) (bv_unsigned (Mmap.min_brk (m_vmmaps m)))) eqn:Q.
  - exists (vm_brk (m_vmmaps m)). split; [exact (brk_r_ok_keep m req)|].
    unfold brk_refusal_b. cbv zeta. apply orb_true_iff in Q as [Q|Q]; rewrite Q;
      destruct (w_is0 req); reflexivity.
  - destruct (bv_eqb req (vm_brk (m_vmmaps m))) eqn:B.
    + exists (vm_brk (m_vmmaps m)). split; [exact (brk_r_ok_keep m req)|].
      unfold brk_refusal_b. cbv zeta. apply orb_false_iff in Q as [Q1 Q2]. rewrite Q1, Q2, B. reflexivity.
    + try rewrite Q in Hf. try rewrite B in Hf. cbn [negb andb] in Hf. apply negb_false_iff in Hf.
      exists req. split; [exact Hf|].
      unfold brk_refusal_b. cbv zeta. apply orb_false_iff in Q as [Q1 Q2]. rewrite Q1, Q2, B. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Lemma brk_outcome_si : forall segs ms x8 model o,
  bv_unsigned x8 = 214%Z ->
  m_halted model = None ->
  syscall_spec_acfg (sys_input segs ms x8) model o <->
  exists r, brk_resolution_ok model (ms_gpr ms 0) r
            /\ (brk_refusal_b model (ms_gpr ms 0) r = true -> brk_refusable model (ms_gpr ms 0) = true)
            /\ o = Ok (mkEffectU r []
                         (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                         (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
                      (brk_model (ms_gpr ms 0) r model) [].
Proof.
  intros segs ms x8 model o Hno Hh.
  assert (Hno' : bv_unsigned (in_sysno (sys_input segs ms x8)) = 214%Z)
    by (rewrite in_sysno_sys_input214; exact Hno).
  pose (RefR := fun o' : outcome SyscallEffect =>
    exists r, brk_resolution_ok model (ms_gpr ms 0) r /\ brk_refusal_b model (ms_gpr ms 0) r = true
      /\ o' = Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                    (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
                 (brk_model (ms_gpr ms 0) r model) []).
  pose (GrantR := fun o' : outcome SyscallEffect =>
    exists r, brk_resolution_ok model (ms_gpr ms 0) r /\ brk_refusal_b model (ms_gpr ms 0) r = false
      /\ o' = Ok (mkEffectU r [] (brk_zeros (ms_gpr ms 0) r (vm_brk (m_vmmaps model)))
                    (brk_unmaps r (vm_brk (m_vmmaps model))) [] [])
                 (brk_model (ms_gpr ms 0) r model) []).
  assert (Hchar : forall o', syscall_spec (sys_input segs ms x8) model o' <-> RefR o' \/ GrantR o').
  { intros o'. unfold RefR, GrantR.
    rewrite (syscall_spec_214 _ model o' Hno'). rewrite in_arg0_sys_input214.
    unfold brk_resolution_ok, brk_model. rewrite brk_outcome. split.
    - intros (r & Hr & ->). destruct (brk_refusal_b model (ms_gpr ms 0) r) eqn:E; [left | right];
        exists r; (split; [exact Hr|]); (split; [exact E | reflexivity]).
    - intros [(r & Hr & _ & ->) | (r & Hr & _ & ->)]; exists r; (split; [exact Hr | reflexivity]). }
  assert (HH : forall eff m' evs, syscall_spec (sys_input segs ms x8) model (Ok eff m' evs) -> m_halted m' = None).
  { intros eff m' evs Hs. apply Hchar in Hs.
    destruct Hs as [(r & _ & _ & Heq) | (r & _ & _ & Heq)];
      apply Ok_inj in Heq as (_ & E & _); rewrite E, alloc_brk_model_halted; exact Hh. }
  assert (HR : forall o', RefR o' -> exists eff m' evs, o' = Ok eff m' evs
                 /\ refusal_b (sys_input segs ms x8) model (eff_ret eff) = true).
  { intros o' (r & _ & Hrb & ->). do 3 eexists. split; [reflexivity|].
    rewrite (refusal_b_214 _ _ _ Hno'), in_arg0_sys_input214. exact Hrb. }
  assert (HG : forall o', GrantR o' -> exists eff m' evs, o' = Ok eff m' evs
                 /\ refusal_b (sys_input segs ms x8) model (eff_ret eff) = false).
  { intros o' (r & _ & Hrb & ->). do 3 eexists. split; [reflexivity|].
    rewrite (refusal_b_214 _ _ _ Hno'), in_arg0_sys_input214. exact Hrb. }
  assert (Hgf : forall o', GrantR o' -> brk_refusable model (ms_gpr ms 0) = false).
  { intros o' (r & Hr & Hrb & _). exact (brk_refusable_false_of_grant _ _ _ Hr Hrb). }
  assert (Hfg : brk_refusable model (ms_gpr ms 0) = false -> exists o', GrantR o').
  { intros Hf. destruct (brk_grant_of_refusable_false _ _ Hf) as (r & Hr & Hrb).
    eexists. exists r. split; [exact Hr|]. split; [exact Hrb | reflexivity]. }
  rewrite (acfg_char_split (sys_input segs ms x8) model RefR GrantR (brk_refusable model (ms_gpr ms 0))
             (acfg_family_off_no _ 214%Z Hno' (proj1 (alloc_no_b_In 214%Z) eq_refl))
             Hchar HH HR HG Hgf Hfg o).
  unfold RefR, GrantR. split.
  - intros [[Hf (r & Hr & Hrb & ->)] | (r & Hr & Hrb & ->)]; exists r; (split; [exact Hr|]);
      (split; [|reflexivity]).
    + intros _. exact Hf.
    + intros Hc. rewrite Hrb in Hc. discriminate Hc.
  - intros (r & Hr & Himp & ->). revert Himp.
    destruct (brk_refusal_b model (ms_gpr ms 0) r) eqn:E; intros Himp.
    + left. split; [exact (Himp eq_refl)|]. exists r. split; [exact Hr|]. split; [exact E | reflexivity].
    + right. exists r. split; [exact Hr|]. split; [exact E | reflexivity].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_zeros_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  brk_zeros req r old =
    brk_page_range (page_round_up_Z (bv_unsigned old))
                   (page_round_up_Z (bv_unsigned r)).
Proof.
  intros req r old Hreq Hold Hlt. unfold brk_zeros, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_grants_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  brk_grants req r old = [(old, r - old)].
Proof.
  intros req r old Hreq Hold Hlt. unfold brk_grants, brk_is_grow.
  assert (E1 : w_is0 req = false)
    by (unfold w_is0; apply bv_eqb_neq; exact Hreq).
  assert (E2 : (0 <? bv_unsigned old)%Z = true) by (apply Z.ltb_lt; lia).
  assert (E3 : (bv_unsigned old <? bv_unsigned r)%Z = true) by (apply Z.ltb_lt; lia).
  rewrite E1, E2, E3. reflexivity.
Qed.

Lemma brk_zeros_query : forall r old, brk_zeros (Z_to_bv 64 0) r old = [].
Proof.
  intros r old. unfold brk_zeros, brk_is_grow, w_is0.
  rewrite bv_eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma brk_zeros_keep : forall req old, brk_zeros req old old = [].
Proof.
  intros req old. unfold brk_zeros, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

Lemma brk_grants_keep : forall req old, brk_grants req old old = [].
Proof.
  intros req old. unfold brk_grants, brk_is_grow.
  rewrite Z.ltb_irrefl, !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_unmaps_keep : forall old, brk_unmaps old old = [].
Proof.
  intros old. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E; [|reflexivity].
  unfold brk_page_range. rewrite Z.ltb_irrefl. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma brk_unmaps_grow : forall r old,
  (bv_unsigned old <= bv_unsigned r)%Z -> brk_unmaps r old = [].
Proof.
  intros r old H. unfold brk_unmaps. cbv zeta.
  destruct (0 <? bv_unsigned old)%Z eqn:E0; [|reflexivity].
  assert (E : (page_round_up_Z (bv_unsigned r)
               <? page_round_up_Z (bv_unsigned old))%Z = false)
    by (apply Z.ltb_ge, page_round_up_Z_mono, H).
  unfold brk_page_range. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma page_round_up_Z_aligned : forall z,
  (0 <= z)%Z -> (z mod page_size = 0)%Z -> page_round_up_Z z = z.
Proof.
  intros z Hz Hmod. unfold page_round_up_Z, page_size in *.
  pose proof (Z.div_mod z 4096 ltac:(lia)) as Hdiv.
  replace (z + 4096 - 1)%Z with
    (4095 + (z / 4096) * 4096)%Z by lia.
  rewrite Z.div_add by lia.
  rewrite Z.div_small by lia. lia.
Qed.

Lemma page_round_up_Z_bounds : forall z,
  (0 <= z)%Z ->
  (z <= page_round_up_Z z <= z + page_size - 1)%Z.
Proof.
  intros z Hz. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as Hdiv.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)) as Hmod.
  lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma brk_zeros_aligned_grow : forall req r old,
  req <> Z_to_bv 64 0 ->
  (0 < bv_unsigned old)%Z -> (bv_unsigned old < bv_unsigned r)%Z ->
  (bv_unsigned old mod page_size = 0)%Z ->
  brk_zeros req r old =
    [(old, Z_to_bv 64 (page_round_up_Z (bv_unsigned r) - bv_unsigned old))].
Proof.
  intros req r old Hreq Hpos Hlt Halign.
  rewrite brk_zeros_grow by assumption.
  rewrite (page_round_up_Z_aligned (bv_unsigned old)) by lia.
  unfold brk_page_range.
  assert (Hround : (bv_unsigned old < page_round_up_Z (bv_unsigned r))%Z).
  { pose proof (page_round_up_Z_bounds (bv_unsigned r) ltac:(lia)). lia. }
  rewrite (proj2 (Z.ltb_lt _ _) Hround).
  rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition growable (reserved : list (word * word)) (lim top : Z) (t r : word)
    : Prop :=
  r <> Z_to_bv 64 0 /\ (bv_unsigned r + bv_unsigned t < 2 ^ 64)%Z /\
  (t = Z_to_bv 64 0 \/
   (((if (page_round_up_Z (bv_unsigned r)
          <? page_round_up_Z (bv_unsigned r + bv_unsigned t))%Z
      then (page_round_up_Z (bv_unsigned r + bv_unsigned t)
            <=? top)%Z
           && region_free reserved
                (Z_to_bv 64 (page_round_up_Z (bv_unsigned r)))
                (Z_to_bv 64 (page_round_up_Z
                               (bv_unsigned r + bv_unsigned t)
                              + page_size - page_round_up_Z (bv_unsigned r)))
      else true)
     && (bv_unsigned t <=? lim)%Z)%bool = true)).

(* [comment removed for export] *)
Definition T1 (reserved : list (word * word)) (lim top : Z) (t : word)
    (bufs : list (list byte))
    (r : word) : (list (list byte) * word) -> Prop :=
  fun o => (o = ([], Z_to_bv 64 4)
            /\ (r = Z_to_bv 64 0
                \/ (2 ^ 64 <= bv_unsigned r + bv_unsigned t)%Z
                \/ t <> Z_to_bv 64 0))
        \/ (growable reserved lim top t r /\ o = (bufs, Z_to_bv 64 0)).

(* [comment removed for export] *)
Definition T2 (want : word) (bufs : list (list byte)) (r2 : word)
    : (list (list byte) * word) -> Prop :=
  fun o => (r2 = want /\ o = (bufs, Z_to_bv 64 0))
        \/ (r2 <> want /\ o = ([], Z_to_bv 64 4)).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

Inductive to_outcomes : machine_state -> Model -> ((list (list byte) * word) -> Prop) -> Prop :=
| tou_wexit : forall ms model bufs code (U : (list (list byte) * word) -> Prop),
    fd1chan model ->
    to_wallexit segs (Z_to_bv 64 1) bufs code ms ->
    bufs_modeled bufs ->
    (forall o, U o <-> o = (bufs, code)) ->
    to_outcomes ms model U
| tou_step : forall ms ms' model U,
    ms_svc_pending ms = None ->
    RiscvSemantics.step segs ms = MachineOk ms' ->
    to_outcomes ms' model U ->
    to_outcomes ms model U
| tou_brk : forall ms model x8
    (T : SyscallEffect -> Model -> (list (list byte) * word) -> Prop)
    (U : (list (list byte) * word) -> Prop),
    ms_svc_pending ms = Some x8 ->
    bv_unsigned x8 = 214%Z ->
    (forall eff model' evs,
       syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
       to_outcomes (advance_past_svc (apply_effect ms eff)) model' (T eff model')) ->
    (forall o, U o <->
       (exists eff model' evs,
          syscall_spec (sys_input segs ms x8) model (Ok eff model' evs)
          /\ T eff model' o)) ->
    to_outcomes ms model U.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition outcome_trace (fs : Fs.Fs) (o : list (list byte) * word) : list event :=
  wevents (fst o) ++ [ExitEv (snd o) fs].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


Definition aon_path (c : config) : Prop :=
  (m_halted (cfg_model c) = None
   /\ m_vm_lazy (cfg_model c) = []
   /\ exists U, to_outcomes (cfg_ms c) (cfg_model c) U)
  \/ wall_won_path segs (Z_to_bv 64 1) (Z_to_bv 64 1) c
  \/ m_halted (cfg_model c) <> None.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

