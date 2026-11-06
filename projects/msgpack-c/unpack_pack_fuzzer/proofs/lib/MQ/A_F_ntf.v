(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.msgpack_c.unpack_pack_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_F_syscalls A_MallocRep A_F_malloc_free A_F_malloc_fast A_F_malloc_enframe A_MallocTree A_MallocBlocks A_MallocFacts_B.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import Monad Prog.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocKit_B A_MallocKit_B2 A_MallocModel_B A_F_ntf_A A_F_ntf_B A_F_ntf_C.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocKit_B3 A_F_ntf_D A_F_ntf_E A_F_ntf_F A_F_ntf_G A_F_ntf_H.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.MQ Require Import A_MallocFacts_Bpres.

Set Keyed Unification.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import CeilLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section CEIL.
Context {CLG : OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Malloc.Ceiling.ceiling}.

Lemma gmeta_mw st g p : gmeta_ok st g p -> mw_ok (get_meta_rec st g).
Proof.
  intros GO. pose proof (go_li _ _ _ GO). pose proof (go_freeable _ _ _ GO). pose proof (go_sc _ _ _ GO). pose proof (go_maplen _ _ _ GO).
  unfold mw_ok. repeat split; lia.
Qed.

Lemma ntf_unfold {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> Malloc.M R) bail :
  nontrivial_free dec (S f) st g i k bail =
  let mr := get_meta_rec st g in
  let sc := m_sizeclass mr in
  if ntf_cond st g i then
    match m_next mr with
    | Some _ =>
      guard 50 (sc <? 48) (
        let activate_new := optr_eqb (active st sc) (Some g) in
        let st1 := dequeue (LActive sc) g st in
        match activate_new, active st1 sc with
        | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
        | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
        end) bail
    | None => free_group R dec (nontrivial_free dec f) st g k bail
    end
  else if Z.lor (m_freed mr) (m_avail mr) =? 0 then
    guard 51 (sc <? 48) (
      if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st (fun st0 => k (aor_st st0 g i) None) bail
      else k (aor_st st g i) None) bail
  else k (aor_st st g i) None.
Proof. reflexivity. Qed.

Lemma free_group_unfold {R} (dec : decoder R) rec st g (k : mstate -> mapinfo -> Malloc.M R) bail :
  free_group R dec rec st g k bail =
  let mr := get_meta_rec st g in
  let st1 := fg_usage_st st g in
  match m_mem mr with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>
    let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
    if negb (m_maplen mr =? 0) then
      free_meta g (record_seq (m_sizeclass mr) (step_seq st1)) (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
    else
      dec st1 p (fun m idx => rec st1 m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
  end.
Proof. reflexivity. Qed.

Definition ntf_result (st' : mstate) (mi : mapinfo) (a0v a1v : word) : Prop :=
  match mi with
  | None => a1v = wz 0
  | Some (b, len) =>
      a0v = wz (conc st' b) /\ a1v = wz len /\ 0 < len < 2^64 /\ snd b = 0
      /\ (exists r, (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup /\ len = round_up_pg (r_len r))
      /\ (forall b' gh, (s_groups st') !! b' = Some gh -> fst b' <> fst b)
  end.

Definition oracle_ok (o m : word -> option byte) (st : mstate) : Prop :=
  forall rid r q h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= q < round_up_pg (r_len r) ->
    8 <= (r_base r + q) mod 16 ->
    cell_read (get_shadow st rid) q = Unknown h ->
    o (wa (r_base r + q)) = m (wa (r_base r + q)).

Definition ntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
    (st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ mrep st' m'
    /\ pres_except (free_fp st lo (bv_unsigned sp)) m m'
    /\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

Lemma pres_except_entry st lo (sp : word) m m1 :
  munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m1 -> wmono asegs m m1 -> lo <= bv_unsigned sp - 80 ->
  pres_except (free_fp st lo (bv_unsigned sp)) m m1.
Proof.
  intros MU WM LOLE. apply (pres_except_of_munch_cov (free_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply free_fp_stack. lia.
Qed.

Lemma oracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
  oracle_ok o m st -> mrep st mw -> alloc_ceiling <= lo -> pres_except (free_fp st lo sp) m m' -> oracle_ok o m' st.
Proof.
  intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
  rewrite (OK rid r q h Hr Hk Hq M8 Hc).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RF). destruct (reserved_disjoint _ _ RF) as [D1 D2].
  pose_ceil.
  symmetry. apply (PE (r_base r + q)); [lia|].
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold CTX in A. lia.
  - destruct A as (rid' & r' & Hr' & Hk' & Hin).
    destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
    pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
  - destruct A as (b & gh & Hb & Hin).
    destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RbB0 & _).
    destruct (WR (fst b) rb Hrb) as (_ & RbAL & _).
    assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
    Z.div_mod_to_equations. lia.
  - destruct A as (rid' & r' & v & Hr' & Hk' & Hin & HC).
    destruct (N.eq_dec rid' rid) as [->|NE].
    + rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

Lemma oracle_ok_frame o m st st' : oracle_ok o m st -> s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> oracle_ok o m st'.
Proof.
  intros OK ER ES rid r q h Hr Hk Hq M8 Hc. rewrite ER in Hr. unfold get_shadow in Hc. rewrite ES in Hc.
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

Lemma free_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
  intros FR HS H. eapply (free_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

Lemma free_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  free_fp st' lo sp a -> free_fp st lo sp a.
Proof. intros ER ES EG H. eapply (free_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

Lemma free_fp_lt st mw lo (sp : Z) a : mrep st mw -> alloc_ceiling <= lo -> lo <= sp -> free_fp st lo sp a -> a < sp.
Proof.
  intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
  pose_ceil.
  destruct H as [[A|[A|A]]|[A|A]].
  - lia.
  - unfold CTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
  - destruct A as (b & gh & Hb & Hin). destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). pose_ceil. lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). pose_ceil. lia.
Qed.

Lemma known_byte st m (q : aptr) r v :
  mrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v ->
  bytes_at asegs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof.
  intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

Lemma rdv_known o st q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> rdv pans_mem o st q = v.
Proof. intros H. unfold rdv. rewrite H. reflexivity. Qed.

Section NTF.
Variables (ra0 : word) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.

Lemma ntf_q_intro (Zs : list aptr) (ra sp : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
  ntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
  pres_except (free_fp st lo (bv_unsigned sp)) m mX ->
  (forall a, free_fp stX lo (bv_unsigned sp) a -> free_fp st lo (bv_unsigned sp) a) ->
  (exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
  oracle_ok o mX stX -> mrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
  ntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof.
  intros RP PE FP KI ZI FR RES OOK MRX ER ES.
  destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
  unfold ntf_q. do 16 eexists. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
  split. { eapply pres_except_trans; [exact PE|]. eapply pres_except_mono; [exact PE'|]. exact FP. }
  split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
  eapply oracle_ok_frame; [| exact ER | exact ES]. eapply oracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

End NTF.

End CEIL.
