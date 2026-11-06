(* Arm c2 (op_mark), segment B: from mark_quietly's return (c2_13db0, 0x13db0) through the four checks
   and the loop's tail to the loop head of operation i + 1 (lh_ms) or to the exit (ex_ms).

     0x13db0  mv s2, a0                 the library's code
     0x13db4  jal check_socket          (leaf, K = 0, memory unchanged)
     0x13db8  mv a0, s2; mv a1, s3      the library's code, the model's
     0x13dc0  jal check_mark            (leaf, K = 0, memory unchanged; same_rc of the two codes)
     0x13dc4  mv a0, s7; mv a1, s0      the marks block, the model block
     0x13dcc  jal check_marks           (leaf, K = 32, writes only its frame)
     0x13dd0  mv a0, s0
     0x13dd4  jal check_requests        (leaf, K = 48, writes only its frame)
     0x13dd8 .. 0x14078                 LC2BWalk.c2b_tail

   The two callee frames lie in [S - 528, S - 480), below the slot's frame, so the loop head's memory
   (built at 0x13db0 from the call cut and mark_quietly's Post) carries over (LC2BSpec section 4). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require Import link_mem
  check_socket_c check_write_c check_marks_c check_requests_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LDefs LC2Defs.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.Slot Require Import LC2BSpec LC2BWalk.
Local Open Scope Z_scope.

Section B.
Hypothesis CHECK_SOCKET_OK : check_socket_contract.
Hypothesis CHECK_MARK_OK : check_mark_contract.
Hypothesis CHECK_MARKS_OK : check_marks_contract.
Hypothesis CHECK_REQUESTS_OK : check_requests_contract.

Lemma c2_segB : forall (E : lenv) (i : Z) (gp : word) (s : Z) (ms : machine_state),
  lenv_ok E -> c2_13db0 E i gp s ms ->
  evt rsegs (c2_post E (ms_mem ms) (fun c => (i < 47 /\ lh_ms E (i + 1) gp c) \/ ex_ms E gp c)) ms.
Proof.
  intros E i gp s ms HE H.
  destruct H as (ra & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & s4 & t3 & t4 & t5 & t6 & F & fc & m
                 & P & N & j0 & j1 & j2 & kbs & mbs & gbs & -> & FC & Hi & Hs & FR & FX & CU & MA & MW & MR & MM
                 & KWF & KO & KMI & KOC & KOB & KNX & KNS & GWF
                 & (gbs' & GA & GWF' & GN & GNN)
                 & (kbs' & KA & KWF' & KCH & KEE & KNI & KIF & KNX' & KSENT & KNS' & KO' & KMI' & KOC' & KOB')).
  try change (ms_mem (MS _ _ _ _ _ m _)) with m.
  destruct (c2b_env E HE) as (HS1 & HS2 & HS3 & HS4 & HS5 & HS6 & HS7 & HS8 & HS9).
  assert (HSa : 0x960e0 + 65536 <= e_S E) by lia.
  assert (SF : SLOT_FRAME = 480) by reflexivity.
  destruct FX as (SV & GN0 & OD & PR & LA & TX & IP & ER & GD & MI & TM & ST).
  (* the library's answer and the model's *)
  assert (Hsent : nk_sent kbs = []) by (apply c2b_sent_nil; exact KNS).
  assert (AG : same_rc (m_rc (c2_ML s kbs gbs)) (m_rc (c2_MM s kbs gbs)) = true /\
               m_marks (c2_ML s kbs gbs) = m_marks (c2_MM s kbs gbs) /\
               m_reqs (c2_ML s kbs gbs) = m_reqs (c2_MM s kbs gbs)).
  { unfold c2_ML, c2_MM. rewrite Hsent. apply c2b_agree. }
  destruct AG as (AGrc & AGm & AGr).
  assert (RG : - 2 ^ 31 <= m_rc (c2_ML s kbs gbs) < 2 ^ 31).
  { unfold c2_ML, mark_lib. apply c2b_mark_range.
    destruct KWF as (_ & _ & _ & _ & _ & _ & _ & _ & W9 & W10 & W11 & _ & _).
    unfold c2b_kb, nk_kstate. cbn [k_sock k_send k_end]. lia. }
  assert (GR : marks_are gbs' mbs).
  { apply (c2b_marks_are gbs' mbs (m_marks (c2_ML s kbs gbs))); [exact GN | exact GNN | | exact MW].
    rewrite AGm. exact MM. }
  (* the loop head's memory for operation i + 1, at mark_quietly's return *)
  assert (REST : c2b_rest E (i + 1) P N kbs' mbs gbs' m).
  { unfold c2b_rest.
    refine (conj SV (conj KA (conj KWF' (conj KIF (conj KO' (conj _ (conj _ (conj _ (conj GN0 (conj OD
      (conj PR (conj LA (conj TX (conj IP (conj MA (conj MW (conj GA (conj GWF' (conj GR (conj CU
      (conj ER GD))))))))))))))))))))); lia. }
  unfold wz.
  (* 0x13db0 mv s2, a0; 0x13db4 jal check_socket *)
  step. step.
  eapply (c2b_call _ _ _ _ _ CHECK_SOCKET_OK); [exact HE | lia | | exact MI | exact ST |].
  { cbv beta. exists kbs'. split; [exact KA|]. split; [exact KO'|]. split; lia. }
  intros r1 m1 MU1 WM1 MI1 ST1 PO1. hnf in PO1. subst m1. clear MU1 WM1 MI1 ST1.
  c2b_retpc.
  (* 0x13db8 mv a0, s2; 0x13dbc mv a1, s3; 0x13dc0 jal check_mark *)
  step. step. step.
  eapply (c2b_call _ _ _ _ _ CHECK_MARK_OK); [exact HE | lia | | exact MI | exact ST |].
  { cbv beta. apply c2b_mark_pre; [exact AGrc | exact RG]. }
  intros r2 m1 MU1 WM1 MI1 ST1 PO1. hnf in PO1. subst m1. clear MU1 WM1 MI1 ST1.
  c2b_retpc.
  (* 0x13dc4 mv a0, s7; 0x13dc8 mv a1, s0; 0x13dcc jal check_marks *)
  step. step. step.
  eapply (c2b_call _ _ _ _ _ CHECK_MARKS_OK); [exact HE | lia | | exact MI | exact ST |].
  { cbv beta. exists gbs', mbs. unfold apart_frame. rewrite c2b_arg0, c2b_arg1, c2b_spZ.
    rewrite !unsigned_lit by lia.
    split; [exact GA|]. split; [exact MA|]. split; [exact GWF'|].
    split; [exact (proj2 (proj2 (proj2 (proj2 (proj2 MW)))))|].
    split; [exact GR|].
    split; left; unfold MK_SIZE, MD_SIZE; lia. }
  intros r3 m1 MU1 WM1 MI1 ST1 _.
  unfold writes_nothing in MU1.
  assert (MU1w : munch (c2b_W (e_S E)) m m1) by (c2b_weaken MU1).
  pose proof (c2b_frame_tr (e_S E) m m1 HSa MU1w WM1 E P N j0 j1 j2 eq_refl FR) as FR1.
  pose proof (c2b_rest_tr (e_S E) m m1 HSa MU1w WM1 E (i + 1) P N kbs' mbs gbs' eq_refl HE REST) as REST1.
  pose proof (c2b_nlk_tr (e_S E) m m1 HSa MU1w WM1 kbs' KA) as KA1.
  pose proof (c2b_model_tr (e_S E) m m1 HSa MU1w WM1 (e_md E) mbs ltac:(unfold MD_SIZE; lia) MA) as MA1.
  c2b_retpc.
  (* 0x13dd0 mv a0, s0; 0x13dd4 jal check_requests *)
  step. step.
  eapply (c2b_call _ _ _ _ _ CHECK_REQUESTS_OK); [exact HE | lia | | exact MI1 | exact ST1 |].
  { cbv beta. exists kbs', mbs. unfold frame_apart_gnl, apart_frame. rewrite c2b_arg0, c2b_spZ.
    rewrite !unsigned_lit by lia.
    split; [exact KA1|].
    split; [unfold apart_gnl, A_G_NL, NK_SIZE; right; lia|].
    split; [exact MA1|]. split; [exact KWF'|]. split; [exact MW|].
    split.
    { apply c2b_requests_are; [| exact KWF' | exact MW | exact (proj2 KA) | exact (proj2 MA)].
      rewrite KSENT, AGr. symmetry. exact MR. }
    split; [left; unfold MD_SIZE; lia | exact HS9]. }
  intros r4 m2 MU2 WM2 MI2 ST2 _.
  unfold writes_nothing in MU2.
  assert (MU2w : munch (c2b_W (e_S E)) m1 m2) by (c2b_weaken MU2).
  pose proof (c2b_frame_tr (e_S E) m1 m2 HSa MU2w WM2 E P N j0 j1 j2 eq_refl FR1) as FR2.
  pose proof (c2b_rest_tr (e_S E) m1 m2 HSa MU2w WM2 E (i + 1) P N kbs' mbs gbs' eq_refl HE REST1) as REST2.
  assert (MU : munch (c2b_W (e_S E)) m m2) by (eapply munch_trans; [exact MU1w | exact MU2w]).
  assert (WM : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1 | exact WM2]).
  pose proof (c2b_task_tr (e_S E) m m2 HSa MU WM TM ST) as TM2.
  pose proof (c2b_fp (e_S E) m m2 HSa MU WM (c2_hp E)) as FP.
  c2b_retpc.
  eapply c2b_tail; [exact HE | exact Hi | exact FC | exact FR2 | exact REST2 | exact MI2 | exact TM2
                   | exact ST2 | exact FP].
Qed.

End B.
