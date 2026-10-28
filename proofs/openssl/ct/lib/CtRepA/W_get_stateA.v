(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog ApBase ApState ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow SegRw.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA AsStruct.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import ImplA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_locks W_tlocalA Fr_init_base.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

Definition GET_STATE : Z := 0x1feb4c.
Definition GET_STATE_STACK : Z := 48 + IB_STACK.      (* [comment removed for export] *)
Definition GET_STATE_RA1 : Z := 0x1febb0.            (* [comment removed for export] *)

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma errno_static8 : forall x, 0xba9348 <= x < 0xba9350 -> client_static x.
Proof.
  intros x Hx. split.
  - exists 0xba4690, 0xbcacd0. split; [unfold CLIENT_STATIC; cbn; tauto | lia].
  - intros (l & h & Hin & Hr). unfold RT_STATIC in Hin. cbn in Hin. destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-; lia.
Qed.

(* [comment removed for export] *)
Lemma errno_seg_rw : seg_rw_ok ctasegs ERRNO_A 4 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma errno_cellA : forall m : mem, exists v, rw_cells ctasegs m ERRNO_A [C4 v].
Proof. intros m. exact (seg_rw_c4 ctasegs m ERRNO_A errno_seg_rw). Qed.

(* [comment removed for export] *)
Definition aclient_ex_errno (L : list block) (SP a : Z) : Prop := aclient_addr L SP a /\ ~ (ERRNO_A <= a < ERRNO_A + 4).

(* [comment removed for export] *)
Lemma ap_state_rt_ex : forall Σ (st : ap_st bptr) m m' OW LB E bo SP,
  AHEAP Σ OW LB m -> ap_state st m OW E bo -> agree_on (aclient_ex_errno (OW ++ LB) SP) m m' -> ap_state st m' OW E bo.
Proof.
  intros Σ st m m' OW LB E bo SP HEAP AS AG. eapply ap_state_agree; [exact AS|].
  eapply agree_on_mono; [exact AG|]. intros a Ha. split; [exact (lib_addr_aclient OW LB SP a Ha)|].
  unfold ERRNO_A, TP_A. destruct Ha as [Ha|(b & Hb & Hr)].
  - unfold LIBW_S in Ha. cbn [rin_ivs fst snd] in Ha. clear - Ha. lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & _ & BI). unfold SEGTOP_A in BI. clear - Hr BI. lia.
Qed.

(* [comment removed for export] *)
Lemma lib_agree_of_ex_errno : forall Σ OW LB m0 m m' SP,
  AHEAP Σ OW LB m0 -> agree_on (aclient_ex_errno (OW ++ LB) SP) m m' -> agree_on (lib_addr OW) m m'.
Proof.
  intros Σ OW LB m0 m m' SP HEAP AG. eapply agree_on_mono; [exact AG|]. intros a Ha. split; [exact (lib_addr_aclient OW LB SP a Ha)|].
  unfold ERRNO_A, TP_A. destruct Ha as [Ha|(b & Hb & Hr)].
  - unfold LIBW_S in Ha. cbn [rin_ivs fst snd] in Ha. clear - Ha. lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & _ & BI). unfold SEGTOP_A in BI. clear - Hr BI. lia.
Qed.

Lemma ax_pres_of_ex_errno : forall (L LB : list block) SP SP' m m',
  agree_on (aclient_ex_errno (L ++ LB) SP') m m' -> SP' <= SP -> ax_pres LB SP LIBW_A m m'.
Proof.
  intros L LB SP SP' m m' AG LE. unfold ax_pres. eapply agree_on_mono; [exact AG|]. intros a [NA Ha]. split.
  - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; lia | right; left; exact Ha | right; right].
    exists b. split; [apply in_or_app; right; exact Hb | exact Hr].
  - intros Hin. apply NA. unfold LIBW_A, ERRNO_A, TP_A in *. cbn [rin_ivs fst snd]. lia.
Qed.

(* [comment removed for export] *)
Lemma gs_munch_agree : forall Σ OW LB m0 m m1 SP,
  AHEAP Σ OW LB m0 -> munch [(SP - 112, SP); (ERRNO_A, ERRNO_A + 4)]%Z m m1 -> ACEIL <= SP - 112 ->
  agree_on (aclient_ex_errno (OW ++ LB) SP) m m1.
Proof.
  intros Σ OW LB m0 m m1 SP HEAP MU LE. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a [Ha Hn]. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1. cbn [outside]. split; [| split; [exact Hn | exact I]].
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha; lia | |].
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    clear - Hin Hr C1 LE. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). clear - BC Hr LE. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem get_state_cpsA : forall (Q : config -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (E : ap_env) (st : ap_st bptr) (bo : Z * Z) (lo v : Z) (errv : word),
  AHEAP Σ OW LB m -> ap_state st m OW E bo ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + GET_STATE_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (length FR < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  rw_cells ctasegs m ERRNO_A [C4 errv] ->
  (v = 0 \/ v = 1) -> a0 = wz v ->
  (forall (Σ' : rts RT) (m' : mem) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (errv' : word),
     AHEAP Σ' OW LB m' -> rt_credit RT Σ' = rt_credit RT Σ - 1 -> rt_live RT Σ' = rt_live RT Σ ->
     stk ctasegs m' lo (bv_unsigned sp) -> mem_inv ctasegs m' ->
     agree_on (aclient_ex_errno (OW ++ LB) (bv_unsigned sp)) m m' ->
     rw_cells ctasegs m' ERRNO_A [C4 errv'] ->
     cps ctasegs (ASTA RT Σ' PMc (eq
       (MS (mkR ra sp gp (wz TP_A) t0' t1' t2' s0 s1 (wz (e_es E)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
           F' (ret_pc ra) fc' None m' (seg_rom ctasegs)))) Q) ->
  cps ctasegs (ASTA RT Σ PMc (eq
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz GET_STATE) fc None m (seg_rom ctasegs)))) Q.
Proof.
  intros until errv. intros HEAP AS ST CEIL LO TOP AL16 MI -> FLEN CRED HERR Hv -> K.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3.
  change ERRNO_A with 12227404 in HERR, K. unfold GET_STATE, GET_STATE_STACK, IB_STACK, IB_FRAME, RT_STACK, USTACK_TOP, TP_A, MallocRep.wz in *.
  (* [comment removed for export] *)
  pose proof AS as (HE & HSF & HCNF & _).
  pose proof HSF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTOP & HBONCE & HBRET & _).
  assert (HOD : exists od, rw_cells ctasegs m OI_OPTSDONE [C8 (Z_to_bv 64 od)] /\ (od = V_OI_OPTSDONE \/ od = V_OPTSDONE_CNF)).
  { clear - HCNF. destruct (as_cnf st) as [[[lk lh] bk]|]; cbn [ap_statics_cnf] in HCNF.
    - exists V_OPTSDONE_CNF. split; [exact (proj1 (proj2 (proj2 HCNF))) | right; reflexivity].
    - exists V_OI_OPTSDONE. split; [exact (proj1 (proj2 (proj2 HCNF))) | left; reflexivity]. }
  destruct HOD as (od & HOD & ODV). clear HCNF.
  unfold OI_STOPPED, OI_OPTSDONE, OI_BASE_ONCE, OI_BASE_RET in HSTOP, HOD, HBONCE, HBRET.
  pose proof HE as (_ & ND & HP). unfold CtRepP.ApRepDefs.env_blocks in HP.
  apply Forall_cons_iff in HP as [PES _]. cbn [blk_addr blk_size fst snd] in PES. unfold ES_SIZE in PES.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (12227404, 12227404 + 4)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 112, bv_unsigned sp); (12227404, 12227404 + 4)]%Z) by (cbn [offshW]; alia).
  assert (ACC8 : acc ctasegs m 12227400 8).
  { apply (af_acc_static RT AF Σ m 12227400 8 (AH_art _ _ _ _ HEAP) ltac:(clear; lia)). intros i Hi.
    split; [apply errno_static8; clear - Hi; lia|]. clear - Hi. lia. }
  apply cps_from_evt'. carve_frame 48%nat ST. do 8 zstep.
  zstep. (* [comment removed for export] *)
  destruct Hv as [-> | ->].
  2: { (* [comment removed for export] *)
  zstep. if_false.
  zstep. (* [comment removed for export] *)
  zstep. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. (* [comment removed for export] *)
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear - SPR LO LO0; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1) by (eapply AH_frame; [exact HEAP| exact MU| exact WM| constructor; [left; cbn; alia| constructor; [right; left; cbn; intros xe Hxe; apply errno_static8; clear - Hxe; lia | constructor]]]).
  apply evt_done.
  eapply (OPENSSL_init_base_cpsA _) with (lo := lo) (OW := OW) (LB := LB) (od := od);
    [exact HEAP1 | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold IB_STACK, IB_FRAME, RT_STACK; clear - LO; lia
    | rewrite ESP; unfold USTACK_TOP; clear - TOP; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | assumption | reflexivity | exact FLEN | exact CRED
    | exact HSTOP | exact HOD | exact ODV | exact HBONCE | exact HBRET | reflexivity |].
  clear HSTOP HOD ODV HBONCE HBRET.
  intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 HEAP2 CR2 EL2 ST2 MI2 AG2.
  rewrite ESP in ST2, AG2. rewrite (ret_pc_even GET_STATE_RA1) by (clear; unfold GET_STATE_RA1; lia). unfold GET_STATE_RA1, TP_A.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOP; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HERR; [| intros a Ha; right; left; cbn [cells_size csize Nat.add] in Ha; apply errno_static8; clear - Ha; lia].
  assert (AG01 : agree_on (aclient_ex_errno (OW ++ LB) (bv_unsigned sp)) m m1) by (eapply (gs_munch_agree Σ OW LB m); [exact HEAP | exact MU | clear - CEIL LO; lia]).
  assert (AG02 : agree_on (aclient_ex_errno (OW ++ LB) (bv_unsigned sp)) m m2).
  { eapply agree_on_trans; [exact AG01|]. eapply agree_on_mono; [exact AG2|].
    intros a [[Ha|[Ha|Ha]] Hn]; [left; clear - Ha; lia | right; left; exact Ha | right; right; exact Ha]. }
  pose proof (ap_state_rt_ex Σ st m m2 OW LB E bo (bv_unsigned sp) HEAP AS AG02) as AS2.
  clear MU WM AG01 ACC8.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (12227404, 12227404 + 4)]%Z m2) as MU. pose proof (wmono_refl ctasegs m2) as WM.
  assert (ACC8 : acc ctasegs m2 12227400 8).
  { apply (af_acc_static RT AF Σ2 m2 12227400 8 (AH_art _ _ _ _ HEAP2) ltac:(clear; lia)). intros i Hi.
    split; [apply errno_static8; clear - Hi; lia|]. clear - Hi. lia. }
  apply cps_from_evt'.
  zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. zstep. (* [comment removed for export] *)
  eapply evt_cut.
  { eapply CRYPTO_THREAD_get_local_ex_spec with (lo := lo);
      [exact HEAP2 | exact AS2 | rewrite ESP; exact ST2 | exact MI2 | exact CEIL | rewrite ESP; unfold GET_LOCAL_EX_STACK; clear - LO; lia
      | reflexivity | reflexivity | reflexivity]. }
  post_call_esp ESP m2. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST3 end.
  zstep. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by (clear - PES; lia); clear - K1 PES; lia|]. clear K1. (* [comment removed for export] *)
  zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by (clear - PES; lia); clear - K1 PES; lia]. clear K1. (* [comment removed for export] *)
  zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep.
  zstep. (* [comment removed for export] *)
  do 6 zstep. release_frame FR ST3 (bv_unsigned sp). zstep. zstep.
  apply evt_done. eapply K; [| exact CR2 | exact EL2 | exact ST3 | assumption | | eassumption].
  - eapply AH_frame; [exact HEAP2| exact MU| exact WM| constructor; [left; cbn; alia| constructor; [right; left; cbn; intros xe Hxe; apply errno_static8; clear - Hxe; lia | constructor]]].
  - eapply agree_on_trans; [exact AG02|]. eapply (gs_munch_agree Σ2 OW LB m2); [exact HEAP2 | exact MU | clear - CEIL LO; lia]. }
  (* [comment removed for export] *)
  zstep. if_true. zstep. (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. zstep. zstep. (* [comment removed for export] *)
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; clear - SPR LO LO0; lia).
  assert (HEAP1 : AHEAP Σ OW LB m1) by (eapply AH_frame; [exact HEAP| exact MU| exact WM| constructor; [left; cbn; alia| constructor; [right; left; cbn; intros xe Hxe; apply errno_static8; clear - Hxe; lia | constructor]]]).
  apply evt_done.
  eapply (OPENSSL_init_base_cpsA _) with (lo := lo) (OW := OW) (LB := LB) (od := od);
    [exact HEAP1 | rewrite ESP; exact ST | exact CEIL | rewrite ESP; unfold IB_STACK, IB_FRAME, RT_STACK; clear - LO; lia
    | rewrite ESP; unfold USTACK_TOP; clear - TOP; lia | rewrite ESP; clear - AL16; uchk_open; Z.div_mod_to_equations; lia | assumption | reflexivity | exact FLEN | exact CRED
    | exact HSTOP | exact HOD | exact ODV | exact HBONCE | exact HBRET | reflexivity |].
  clear HSTOP HOD ODV HBONCE HBRET.
  intros Σ2 m2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 HEAP2 CR2 EL2 ST2 MI2 AG2.
  rewrite ESP in ST2, AG2. rewrite (ret_pc_even GET_STATE_RA1) by (clear; unfold GET_STATE_RA1; lia). unfold GET_STATE_RA1, TP_A.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn [cells_size csize Nat.add] in Ha; unfold USTACK_TOP; clear - Ha TOP; lia].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HERR; [| intros a Ha; right; left; cbn [cells_size csize Nat.add] in Ha; apply errno_static8; clear - Ha; lia].
  assert (AG01 : agree_on (aclient_ex_errno (OW ++ LB) (bv_unsigned sp)) m m1) by (eapply (gs_munch_agree Σ OW LB m); [exact HEAP | exact MU | clear - CEIL LO; lia]).
  assert (AG02 : agree_on (aclient_ex_errno (OW ++ LB) (bv_unsigned sp)) m m2).
  { eapply agree_on_trans; [exact AG01|]. eapply agree_on_mono; [exact AG2|].
    intros a [[Ha|[Ha|Ha]] Hn]; [left; clear - Ha; lia | right; left; exact Ha | right; right; exact Ha]. }
  pose proof (ap_state_rt_ex Σ st m m2 OW LB E bo (bv_unsigned sp) HEAP AS AG02) as AS2.
  clear MU WM AG01 ACC8.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (12227404, 12227404 + 4)]%Z m2) as MU. pose proof (wmono_refl ctasegs m2) as WM.
  assert (ACC8 : acc ctasegs m2 12227400 8).
  { apply (af_acc_static RT AF Σ2 m2 12227400 8 (AH_art _ _ _ _ HEAP2) ltac:(clear; lia)). intros i Hi.
    split; [apply errno_static8; clear - Hi; lia|]. clear - Hi. lia. }
  apply cps_from_evt'.
  zstep. if_false. (* [comment removed for export] *)
  zstep. zstep. zstep. (* [comment removed for export] *)
  eapply evt_cut.
  { eapply CRYPTO_THREAD_get_local_ex_spec with (lo := lo);
      [exact HEAP2 | exact AS2 | rewrite ESP; exact ST2 | exact MI2 | exact CEIL | rewrite ESP; unfold GET_LOCAL_EX_STACK; clear - LO; lia
      | reflexivity | reflexivity | reflexivity]. }
  post_call_esp ESP m2. rewrite ?ESP in *.
  match goal with H : stk ctasegs _ lo (bv_unsigned sp + -48) |- _ => rename H into ST3 end.
  zstep. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by (clear - PES; lia); clear - K1 PES; lia|]. clear K1. (* [comment removed for export] *)
  zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit in K1 by (clear - PES; lia); clear - K1 PES; lia]. clear K1. (* [comment removed for export] *)
  zstep. if_true. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  do 6 zstep. release_frame FR ST3 (bv_unsigned sp). zstep. zstep.
  apply evt_done. eapply K; [| exact CR2 | exact EL2 | exact ST3 | assumption | | eassumption].
  - eapply AH_frame; [exact HEAP2| exact MU| exact WM| constructor; [left; cbn; alia| constructor; [right; left; cbn; intros xe Hxe; apply errno_static8; clear - Hxe; lia | constructor]]].
  - eapply agree_on_trans; [exact AG02|]. eapply (gs_munch_agree Σ2 OW LB m2); [exact HEAP2 | exact MU | clear - CEIL LO; lia].
Qed.

End WithRT.
