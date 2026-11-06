(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import PropExec MState Mem Exec Tac Arr Bytes ZBridge Frame ITree Nodes Decode Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF Realize SafeReach Bridge.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.LZ Require Import ITreeLZ BridgeLZ NodesLZ NodesLZSound NodesLZMm.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0 ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim LJ PEnv APrimSpec APrimSpec2 ASec AQuar AQuarM AHeap F_quar_E F_quar_P F_free_icpt F_free_null
                        ALedger AHeap2 AHeapB AFreeL8 ALinkPg ALinkVm ALink ALinkPrim ALinkFree ALinkFreeIn AVaOf AHeapLaws AHeapInst.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.T7 Require Import RealizeS A0Prog SeamA0.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section AC.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv) (FI : fs_if) (Bs : vmbase).
Hypothesis AO : alayout_ok AL.
Hypothesis FSBE : FSB FI = al_fsb AL.
Hypothesis SP0S : alloc_ceiling + 2^23 + 184 <= 2^47.
Hypothesis BO : base_ok Bs.
Hypothesis SPACE_EQ : vb_space Bs = al_space AL.
Hypothesis SPACE_AL : al_space AL mod 65536 = 0.
Hypothesis SWIN_LO : 65536 <= SWIN (al_depot AL).

Hypothesis FSEI : forall m, thread_env (al_thread AL) m -> AFsEnv.fs_tls_env (at_thr (al_thread AL)) AFsEnv.A0_DTV AFsEnv.A0_TLSB (al_dtls AL) (al_fsb AL) m -> FSENV FI m.

Notation AIB := (AI_B AL E FI Bs AO FSBE SP0S FSEI).
Notation JB := (JA FI AIB).
Notation kept mo mo' := (m_fds mo' = m_fds mo /\ m_fs mo' = m_fs mo).

Definition free_room : Prop := forall s LB (m : mem) ch n l1 l2,
  RHEAP_B AL E s LB m -> bs_live s = l1 ++ (ch, n) :: l2 ->
  let P := bs_prim s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
  let X1 := (fst (enq_prim P loc), bs_sec s) in let todo := put_todo P glob loc ch in
  (enq_refills P loc = true -> vroom Bs (va_of s) (D_enq P loc + D_enq P loc / 8 + 4 * page_size))
  /\ vroom Bs (va_enq (va_of s) P loc) (R_dorecycle X1 todo + 2 * page_size).

#[using="SWIN_LO"] Lemma free_walk_at : forall (gp s6 s7 s8 s9 s10 s11 : word) (F_ : bvmap 5 word) (fc : bv 32) (q lo : Z)
    (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 : word) s LB (m : mem) ch n l1 l2 ras,
  RHEAP_B AL E s LB m -> mclean (bs_H s) m -> mem_inv asegs m -> bs_live s = l1 ++ (ch, n) :: l2 ->
  stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - 4096 -> q mod 16 = 0 -> q + 16 < at_top (al_thread AL) ->
  fpchain m (at_top (al_thread AL)) q (bv_unsigned s0) ras -> In (PC0_FREE :: bv_unsigned ra :: ras) A0_TRACES ->
    let X := bs_X s in let glob := q_glob (bs_quar s) in let loc := q_loc (bs_quar s) in
    let hrest := flat_map prim_of (map fst (l1 ++ l2)) in
    implA (bs_H s) (ebind (t_enq AL (fst X) loc) (fun _ => t_dorecycle AL (fst (enq_prim (fst X) loc), snd X) (put_todo (fst X) glob loc ch)))
      (ficpt_post AL E gp s6 s7 s8 s9 s10 s11 F_ fc q lo 262144 262728 ra s0 s1 s2 s3 s4 s5 X (bs_H s) m glob loc ch hrest (bs_depot s) (bs_dtotal s) (free_tr ra ras))
      (MS (mkR ra (wz q) gp (wz A0_TP) t0 t1 t2 s0 s1 (wz (qc_hdr AL ch + 16)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (wz free_icpt_entry) fc None m (seg_rom asegs)).
Proof.
  intros gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m ch n l1 l2 ras HR MC MI EL ST CLO LOQ Q16 QTOP CH TRIN.
  destruct (free_pre_at AL E s LB m ch n l1 l2 HR MI EL) as (INV & HK & WFC & LREP & NSC & _).
  cbv zeta.
  pose proof (rheap_stats AL E s LB m HR) as (CA0 & CM0 & CM1). pose proof (rheap_refill_budget AL E s LB m HR K_BCLASS ltac:(lia)) as RB24.
  destruct HR as (PLB & LOK & AO' & _ & QLG & GC & QCL & MTX & (CST & AFM) & (FWF & QBL & QBG) & RD & DOK & _ & _ & _ & _ & _ & TE2 & HKE & TRE & AENV & (inited & IA) & _).
  pose proof alloc_ceiling_range as ACR. unfold alloc_floor, alloc_ceiling_max in ACR.
  destruct (traces_ok _ _ _ TRIN) as (LRAS & NPC & RA4 & RANE & RNG).
  assert (FWF' : Forall qbatch_wf (q_glob (bs_quar s) ++ q_loc (bs_quar s))) by (eapply Permutation_Forall; [apply Permutation_app_comm| exact FWF]).
  assert (LTR : (length (free_tr ra ras) <= 30)%nat) by (unfold free_tr; cbn [length]; lia).
  destruct (depot_room AL _ _ _ (free_tr ra ras) DOK LTR SWIN_LO) as (RN & RF & RT).
  eapply (free_icpt_spec AL E AO' gp s6 s7 s8 s9 s10 s11 F_ fc q lo ltac:(lia) CLO ltac:(unfold FICPT_STACK; exact LOQ) QTOP Q16 262144 262728 eq_refl eq_refl
            ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 (bs_X s) (bs_H s) m (q_glob (bs_quar s)) (q_loc (bs_quar s)) ch _ (bs_dtotal s) (bs_depot s) ras inited);
    [ exact MC | exact ST | exact INV | exact HK | exact WFC | exact LREP | exact NSC | exact QLG | exact GC | exact QCL | exact MTX | exact CST | exact AFM | exact FWF'
    | rewrite qbytes_app; lia
    | exact RB24
    | exact CA0 | exact CM0 | exact CM1
    | apply Forall_app in FWF as [FWL _]; pose proof (qbytes_len _ FWL) as QL; lia
    | exact TE2 | exact HKE | exact TRE | exact IA | exact RD | exact CH | exact LRAS | exact NPC | exact RA4 | exact RANE | exact RNG | exact RN | exact RF | exact RT ].
Qed.
#[using="Type"] Lemma mclean_of_seam : forall (H : word -> bool) (m : mem),
  (forall x, H x = true -> m x = None) -> H_off_segments asegs H -> mclean H m.
Proof. intros H m C O. split; assumption. Qed.

#[using="BO SPACE_EQ SPACE_AL SWIN_LO"] Theorem ac_free_B : free_room -> free_stmt_A FI AIB JB.
Proof.
  intros ROOM. unfold free_stmt_A.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st k A n lo ras
         HR HIN AE RF ST CLO LOQ Q16 QTOP MI CH TRIN EA0. subst a0.
  change (RHEAP_A FI AIB s LB m) with (RHEAP_B AL E s LB m) in HR.
  change (am_stack_top FI AIB) with (at_top (al_thread AL)) in QTOP, CH.
  destruct (free_pre AL E s LB m k A n HR MI HIN) as (ch & l1 & l2 & EL & EA & EK & _). subst A k.
  pose proof (free_link_inputs AL E s LB m ch n l1 l2 (va_of s) HR EL (va_of_linked s)) as LIN. cbv zeta in LIN.
  destruct LIN as (OKE & SOK & _ & _).
  destruct (ROOM s LB m ch n l1 l2 HR EL) as (ROOM1 & ROOM2). cbv zeta in ROOM1, ROOM2.
  set (P := bs_prim s) in *. set (glob := q_glob (bs_quar s)) in *. set (loc := q_loc (bs_quar s)) in *.
  set (X1 := (fst (enq_prim P loc), bs_sec s)) in *. set (todo := put_todo P glob loc ch) in *.
  set (v1 := va_enq (va_of s) P loc) in *. set (v' := va_dorecycle v1 X1 todo) in *.
  cbn [AJ JA].
  eapply (AJA_of_implL FI AIB
            (ebind (t_enq AL P loc) (fun _ => t_dorecycle AL X1 todo))
            (epostL (ficpt_post AL E gp s6 s7 s8 s9 s10 s11 F_ fc q lo 262144 262728 ra s0 s1 s2 s3 s4 s5 (bs_X s) (bs_H s) m glob loc ch
                                (flat_map prim_of (map fst (l1 ++ l2))) (bs_depot s) (bs_dtotal s) (free_tr ra ras)))
            (fun mo r mo' => r = Ok tt /\ LINK Bs v' mo' /\ kept mo mo')).
  -
    intros CL HOFF. cbn [ms_mem] in CL.
    pose proof (free_walk_at gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m ch n l1 l2 ras
                  HR (mclean_of_seam _ _ CL HOFF) MI EL ST CLO ltac:(unfold A0_RT_STACK in LOQ; exact LOQ) Q16 QTOP CH TRIN) as W. cbv zeta in W.
    exact W.
  -
    intros mo LF VM. cbn [am_vm AI_B] in VM.
    pose proof (LINK_of_LINKvm Bs _ _ VM) as LK.
    apply stwf_ebind. apply (link_enq Bs AL BO SPACE_EQ SPACE_AL (va_of s) _ P loc); [exact LK | |].
    + unfold ok_enq. intros ER. destruct (OKE ER) as (W24 & RB24). split; [exact W24|]. split; [exact RB24| exact (ROOM1 ER)].
    + intros mo1 L1 K1. fold v1 in L1.
      pose proof (vinv_of_LINK Bs _ _ L1) as VI1.
      destruct (room_dorecycle Bs AL todo v1 X1 VI1 SOK) as (_ & _ & _ & OKD).
      apply (link_dorecycle Bs AL BO SPACE_EQ SPACE_AL todo v1 mo1 X1); [exact L1 | apply (OKD 0 ltac:(lia)); rewrite Z.add_0_r; exact ROOM2 |].
      intros mo2 L2 K2. split; [reflexivity|]. split; [exact L2|]. destruct K1 as [K1a K1b]. destruct K2 as [K2a K2b]. split; congruence.
  - intros moE r moE' (_ & _ & K1 & K2). split; congruence.
  -
    intros r H' P' msr' moE moE' VM0 QW (-> & LK' & KP). cbn [epostL] in QW.
    destruct QW as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & W & hs' & total' & POST). cbv zeta in POST.
    destruct POST as (EMS & EH & MU & FW & INV' & XLE & STK' & QLG' & GC' & QCL' & MTX' & VNG & NBX & RD' & IA' & DEP).
    pose proof (law_blocks_nodup AL E AO s LB m HR) as NDK. apply NoDup_ListNoDup in NDK.
    pose proof (free_post_core AL E FI AIB FSBE (fun lo' hi' X => X) q lo s LB m ch n l1 l2 (free_tr ra ras) st H' m' W hs' total' HR MI AE RF EL NDK CLO
                  ltac:(unfold A0_RT_STACK in LOQ; lia) TRIN) as CORE. cbv zeta in CORE.
    destruct (CORE MU FW INV' QLG' GC' QCL' MTX' VNG NBX RD' (ex_intro _ true IA') DEP) as (MI' & AE' & RF' & AP' & _ & HR').
    clear CORE.
    pose proof (free_va_of AL E s LB m ch n l1 l2 H' hs' total' HR EL) as VAO. cbv zeta in VAO.
    fold P glob loc in VAO, HR'. fold X1 in VAO, HR'. fold todo in VAO, HR'. fold v1 in VAO. fold v' in VAO.
    destruct VAO as (VP & VC & VN & VA).
    set (X' := dorecycle X1 todo) in *.
    exists (mkASB H' P' (fst X') (snd X') (mkAQ (put_loc P loc ch) (put_glob P glob loc ch)) hs' total' (bs_nsec s) (l1 ++ l2) (bs_depot0 s)).
    exists (lb_remove Z.eqb (qc_hdr AL ch + 16) LB).
    split; [reflexivity|]. split.
    + cbn [am_vm AI_B]. apply LINKvm_of_LINK.
      pose proof (LINK_perm Bs _ _ _ LK' VC) as LK2.
      rewrite VP, VN, VA in LK2. exact LK2.
    + unfold free_post_A. exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
      split; [exact EMS|]. split.
      { unfold alloc_frame_A. split; [exact MI'|]. split; [exact STK'|]. split; [exact AE'|]. split; [exact RF'|].
        apply AP'. destruct HR as (PLB & _). rewrite EL in PLB.
        exact (lbrest_desc AL LB l1 (ch, n) l2 PLB NDK). }
      split; [reflexivity|]. split; [exact HR'| reflexivity].
Qed.

#[using="Type"] Lemma lb_desc_all : forall s LB (m : mem), RHEAP_B AL E s LB m ->
  forall b, In b LB -> exists r, In r (bs_live s) /\ blk_addr b = lc_user AL (fst r) /\ blk_size b = snd r.
Proof.
  intros s LB m (PLB & _) b Hb. pose proof (Permutation_in _ PLB Hb) as Hb'.
  apply in_map_iff in Hb' as (r & <- & Hr). exists r. split; [exact Hr|]. split; reflexivity.
Qed.

#[using="Type"] Theorem ac_free_null_B : free_null_stmt_A FI AIB.
Proof.
  unfold free_null_stmt_A.
  intros ra q gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F_ fc m s LB st lo ras
         HR AE RF ST CLO LOQ Q16 QTOP MI CH TRIN EA0. subst a0.
  change (RHEAP_A FI AIB s LB m) with (RHEAP_B AL E s LB m) in HR.
  change (am_stack_top FI AIB) with (at_top (al_thread AL)) in QTOP, CH.
  eapply evt_mono; [exact (free_null_walk AL E gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 t3 t4 t5 t6 s LB m ras
                            HR MI ST CLO ltac:(unfold A0_RT_STACK in LOQ; exact LOQ) Q16 QTOP CH TRIN)|].
  intros ms' POST.
  destruct (free_null_conv AL E FI AIB FSBE (fun lo' hi' X => X) gp s6 s7 s8 s9 s10 s11 F_ fc q lo ra s0 s1 s2 s3 s4 s5 s LB m st ms' HR MI AE RF CLO
              ltac:(unfold A0_RT_STACK in LOQ; lia) POST)
    as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EMS & MI' & STK' & AE' & RF' & AP' & WM & HR').
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [exact EMS|]. split.
  { unfold alloc_frame_A. split; [exact MI'|]. split; [exact STK'|]. split; [exact AE'|]. split; [exact RF'|].
    apply AP'. exact (lb_desc_all s LB m HR). }
  split; [exact WM| exact HR'].
Qed.
End AC.
