(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names and numbers changed; 578 of its 664 lines of code are new or changed and 1143 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/U/Prog/relay_finish_seg.v, with its module names changed; 3267 of its 3354 lines of code are new or changed and 577 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YI04 YO10 YK14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0 Contract ContractT MemNorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import KindB wake_c send_line_c gesture_end_c relay_event_c RelayFrame RelayRunT RelayRunF RelayModel RelayKeys send_line_b_c gesture_end_b_c gestures_end_b_c relay_add_b_c relay_finish_b_c RelayRep HarnessRep drain_b_c relay_remove_b_c relay_remove_b_aux relay_remove_b_lem pthread_mutex_lock_c pthread_mutex_unlock_c memcpy_c memcpy_same_c relay_remove_b_seg relay_remove_b_run relay_finish_b.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require ListTr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma rm_K : RELAY_REMOVE_K = 8560 /\ DRAIN_K = 8512 /\ GESTURES_END_K = 8416 /\ ALLOC_STACK = 8192 /\
  UNLOCK_STACK = 96.
Proof. vm_compute. repeat split. Qed.

(* A disjunction that lia does not split: lia case-splits every disjunctive hypothesis in its context. *)
Definition RmOr (P Q : Prop) : Prop := P \/ Q.
Ltac rm_hide := repeat match goal with H : ?P \/ ?Q |- _ => change (RmOr P Q) in H end.

Ltac rm_ne := match goal with Hc : ?x <> ?x |- _ => exact (False_ind _ (Hc eq_refl)) end.
Ltac rm_geq X := etransitivity; [apply (getr_of_eqv _ _ _ X); reflexivity|]; reflexivity.

Lemma rm_rw_conv : forall sg m A cs cs', rw_cells sg m A cs -> cells_wf cs' ->
  cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs -> rw_cells sg m A cs'.
Proof.
  intros sg m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es.
  split; [split; [exact Hwf' | rewrite Eb; exact Hb] | rewrite Es; exact Hw].
Qed.

Lemma rm_rw_bytes : forall sg m A cs, rw_cells sg m A cs -> bytes_at sg m A (cells_bytes cs).
Proof. intros sg m A cs [[_ Hb] _]. exact Hb. Qed.

Lemma rm_rw_bound : forall sg m A cs, rw_cells sg m A cs -> 0 <= A /\ A + Z.of_nat (cells_size cs) <= 2 ^ 64.
Proof. intros sg m A cs [_ (H0 & H1 & _)]. lia. Qed.

Lemma rm_mu_cells : forall W m m' A cs, rw_cells rsegs m A cs -> munch W m m' -> wmono rsegs m m' ->
  (forall j, 0 <= j < Z.of_nat (cells_size cs) -> outside W (A + j)) -> rw_cells rsegs m' A cs.
Proof.
  intros W m m' A cs H MU WM HO. pose proof H as [_ (H0 & H1 & _)].
  apply (rw_cells_transfer rsegs m m' A cs H). intros j Hj. split.
  - exact (munch_mbyte rsegs W m m' (A + j) MU ltac:(lia) (HO j Hj)).
  - intros Hw. exact (WM _ Hw).
Qed.

Lemma rm_mu_bytes : forall W m m' A bs, bytes_at rsegs m A bs -> munch W m m' ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> outside W (A + j)) -> bytes_at rsegs m' A bs.
Proof.
  intros W m m' A bs H MU HO. pose proof H as (H0 & H1 & _).
  apply (bytes_at_transfer rsegs m m' A bs H). intros j Hj.
  exact (munch_mbyte rsegs W m m' (A + j) MU ltac:(lia) (HO j Hj)).
Qed.

Lemma rm_back : forall m m0' m1 W, ro_agree rsegs m -> mem_rel rsegs m1 m0' -> ro_same rsegs m m1 ->
  munch W (normalize rsegs m) m0' -> wmono rsegs (normalize rsegs m) m0' ->
  munch W m m1 /\ wmono rsegs m m1 /\ ro_agree rsegs m1.
Proof.
  intros m m0' m1 W Hro HR Hs MU WM. pose proof (mem_rel_normalize rsegs m Hro) as HR0.
  split; [exact (munch_rel rsegs W m (normalize rsegs m) m1 m0' HR0 HR Hs MU)|].
  split; [exact (wmono_rel rsegs m (normalize rsegs m) m1 m0' HR0 HR Hs WM)|].
  exact (ro_agree_same rsegs m m1 Hro Hs).
Qed.

Lemma rm_wr_hi : forall m a, 2 ^ 20 <= a < 2 ^ 64 -> writable_at rsegs m a ->
  wview rsegs m (wa a) <> None /\ exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m a Ha W. split; [exact W|].
  destruct (writable_hi_present m a Ha W) as [b E]. exists b. unfold mrd, wa. rewrite E. reflexivity.
Qed.

Lemma rm_outside2 : forall lo1 hi1 lo2 hi2 x, (x < lo1 \/ hi1 <= x) -> (x < lo2 \/ hi2 <= x) ->
  outside [(lo1, hi1); (lo2, hi2)] x.
Proof. intros lo1 hi1 lo2 hi2 x H1 H2. cbn [outside]. lia. Qed.

Lemma rm_ko_len : forall ks, Z.of_nat (length (keys_out ks)) = keys_total ks.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold keys_out, keys_total in *. cbn [map concat fold_right]. rewrite !length_app.
  change (length END5) with 5%nat. lia.
Qed.

Lemma rm_mkR_of : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
      (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
      (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
      (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
      (getr regs 29) (getr regs 30) (getr regs 31).
Proof. reflexivity. Qed.

Section Bridge.
Context {fx : YK11.FPState}.

Lemma rm_bridge : forall R pc m md (Q : machine_state -> Prop) (P : config -> Prop),
  ro_agree rsegs m -> m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of R) fp_regs pc fp_csr None (normalize rsegs m) (seg_rom rsegs)) ->
  (forall R0 pc0 m0 R' m', Q (MS R0 fp_regs pc0 fp_csr None m0 (seg_rom rsegs)) -> Regs6ss.xregs_eqv R0 R' ->
     mem_rel rsegs m' m0 -> ro_same rsegs m m' ->
     SR rsegs (mkCfg (YK11.mkst R' pc0 m' (seg_rom rsegs)) md) P) ->
  (forall s0, Q s0 -> exists R0 pc0 m0, s0 = MS R0 fp_regs pc0 fp_csr None m0 (seg_rom rsegs)) ->
  SR rsegs (mkCfg (YK11.mkst R pc m (seg_rom rsegs)) md) P.
Proof using.
  intros R pc m md Q P HRA Hh Hl HE K HS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. eapply evt_normalize; [vm_compute; reflexivity | exact HRA | exact HE]. }
  intros ms' (can & (s0 & HQ & HR & HO) & HEQ).
  destruct (HS s0 HQ) as (R0 & pc0 & m0 & ->).
  destruct ms' as [r f pv sv rv c mm o], can as [cr cf cp csv crv cc cmm co].
  destruct HR as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8).
  destruct HEQ as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *. subst.
  exact (K _ _ _ r mm HQ E1 R8 HO).
Qed.

Lemma rm_bridge0 : forall R pc m md (Q : machine_state -> Prop) (P : config -> Prop),
  m_halted md = None -> m_vm_lazy md = [] ->
  evt rsegs Q (MS (Regs6ss.mkR_of R) fp_regs pc fp_csr None m (seg_rom rsegs)) ->
  (forall R0 pc0 R', Q (MS R0 fp_regs pc0 fp_csr None m (seg_rom rsegs)) -> Regs6ss.xregs_eqv R0 R' ->
     SR rsegs (mkCfg (YK11.mkst R' pc0 m (seg_rom rsegs)) md) P) ->
  (forall s0, Q s0 -> exists R0 pc0, s0 = MS R0 fp_regs pc0 fp_csr None m (seg_rom rsegs)) ->
  SR rsegs (mkCfg (YK11.mkst R pc m (seg_rom rsegs)) md) P.
Proof using.
  intros R pc m md Q P Hh Hl HE K HS.
  eapply evt_SR_canon; [ | exact Hh | exact Hl | ].
  { rewrite canon_mkst. exact HE. }
  intros ms' (can & HQ & HEQ).
  destruct (HS can HQ) as (R0 & pc0 & ->).
  destruct (eqv_mkst _ _ _ _ _ _ _ HEQ eq_refl eq_refl) as (R' & -> & X).
  exact (K _ _ _ HQ X).
Qed.
End Bridge.

Lemma rm_not_out : forall W x, ~ outside W x -> exists lo hi, In (lo, hi) W /\ lo <= x < hi.
Proof.
  induction W as [|[lo hi] W IH]; intros x H; [exfalso; apply H; exact I|].
  cbn [outside] in H. destruct (Z_lt_le_dec x lo) as [L1|L1]; [|destruct (Z_lt_le_dec x hi) as [L2|L2]].
  - destruct (IH x) as (a & b & Hin & Hab); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists a, b. split; [right; exact Hin | exact Hab].
  - exists lo, hi. split; [left; reflexivity | lia].
  - destruct (IH x) as (a & b & Hin & Hab); [intros Ho; apply H; split; [lia | exact Ho]|].
    exists a, b. split; [right; exact Hin | exact Hab].
Qed.

Lemma rm_find_nth : forall FD0 (l : list rentry) i, NoDup (map re_fd l) -> (i < length l)%nat ->
  re_fd (nth i l no_entry) = FD0 -> find (fun e => re_fd e =? FD0) l = Some (nth i l no_entry).
Proof.
  intros FD0 l. induction l as [|a l IH]; intros i ND Hi HF; cbn [length] in Hi; [lia|].
  apply rma_nodup_std in ND. cbn [map] in ND. apply List.NoDup_cons_iff in ND as [NI ND].
  destruct i as [|i]; cbn [nth find] in HF |- *.
  - rewrite HF, Z.eqb_refl. reflexivity.
  - destruct (Z.eqb_spec (re_fd a) FD0) as [E|E].
    + exfalso. apply NI. rewrite E, <- HF. apply in_map. apply nth_In. lia.
    + apply IH; [apply rma_nodup_of_std; exact ND | lia | exact HF].
Qed.

Lemma rm_find_none : forall FD0 (l : list rentry), (forall e, In e l -> re_fd e <> FD0) ->
  find (fun e => re_fd e =? FD0) l = None.
Proof.
  intros FD0 l. induction l as [|a l IH]; intros H; [reflexivity|]. cbn [find].
  rewrite (proj2 (Z.eqb_neq _ _) (H a (or_introl eq_refl))). apply IH. intros e0 He. apply H. right. exact He.
Qed.

Lemma rm_klens : forall ks, map (fun x => Z.of_nat (length x)) (keys_texts ks) = key_lens ks.
Proof.
  intros ks. unfold keys_texts, key_lens, bzs. rewrite map_map. apply map_ext. intros k. rewrite length_map.
  reflexivity.
Qed.

Lemma rm_ker_eq : forall l l' mx0 no cap xks j o, (xks <> [] -> l = l') ->
  keys_end_run l mx0 no cap xks j o = keys_end_run l' mx0 no cap xks j o.
Proof. intros l l' mx0 no cap [|x xks] j o H; [reflexivity|]. rewrite (H ltac:(discriminate)). reflexivity. Qed.

Lemma rm_held_eq : forall hp kh (ha : adrF), (hp <> 0 -> kh <> 0) ->
  (if (if hp =? 0 then 0 else kh) =? 0 then [] else [RFree (if hp =? 0 then 0 else kh) ha]) =
  (if hp =? 0 then [] else [RFree kh ha]).
Proof.
  intros hp kh ha H. destruct (Z.eqb_spec hp 0) as [E|E]; [reflexivity|].
  rewrite (proj2 (Z.eqb_neq kh 0) (H E)). reflexivity.
Qed.

Lemma rm_live_ge : forall cl br dd T KT, (cl = 3 \/ cl = -1) -> (br = 0 \/ br = 1) -> (dd = 0 \/ dd = 1) ->
  KT <> 0 -> send_live cl (if send_off cl br T then br else dd) dd KT = send_live cl br dd 1.
Proof.
  intros cl br dd T KT Hc Hb Hd HK. unfold send_live, send_off.
  rewrite (proj2 (Z.eqb_neq KT 0) HK).
  destruct Hc as [-> | ->]; destruct Hb as [-> | ->]; destruct Hd as [-> | ->];
    destruct (Z.eqb_spec T 0); reflexivity.
Qed.

Lemma rm_signed_nn : forall x : word, 0 <= bv_signed x -> x = Z_to_bv 64 (bv_signed x).
Proof.
  intros x H. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2 ^ 64) in R.
  destruct (Z_lt_le_dec (bv_unsigned x) (2 ^ 63)) as [L|L].
  - rewrite (YK11.bv_signed_small x L). symmetry. apply Z_to_bv_bv_unsigned.
  - rewrite (YK11.bv_signed_hi x L) in H. lia.
Qed.

(* The relay globals [G_RELAY_LO, G_S + SRC_SIZE * SOURCES_MAX) of build U are not read-only. *)
Lemma rm_ro_glob_chk : forallb (fun i => negb (ro_addr rsegs (Z_to_bv 64 (0x318a0 + Z.of_nat i)))) (seq 0 512) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma rm_ro_glob : forall a, 0x318a0 <= a < 0x31aa0 -> ro_addr rsegs (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof (proj1 (forallb_forall _ _) rm_ro_glob_chk (Z.to_nat (a - 0x318a0))) as H.
  rewrite in_seq in H. specialize (H ltac:(lia)). rewrite Z2Nat.id in H by lia.
  replace (0x318a0 + (a - 0x318a0)) with a in H by lia.
  destruct (ro_addr rsegs (Z_to_bv 64 a)); [discriminate H | reflexivity].
Qed.

(* ---- The run of a trace reads only the addresses its requests returned so far. ---- *)

(* Ret i names one of the first n returned addresses. *)
Definition rm_ab (n : nat) (a : adrF) : Prop := match a with Known _ => True | Ret i => (i < n)%nat end.

Definition rm_dab (n : nat) (a : dadr) : Prop :=
  rm_ab n (da_out a) /\ rm_ab n (da_buf a) /\ rm_ab n (da_hp a) /\ Forall (rm_ab n) (da_keys a) /\
  Forall (rm_ab n) (da_pend a) /\ rm_ab n (da_ev a) /\ Forall (rm_ab n) (da_erecs a).

Lemma rm_ab_res : forall n qs ext a, rm_ab n a -> length qs = n -> resolveF (qs ++ ext) a = resolveF qs a.
Proof.
  intros n qs ext [p|i] H E; cbn [resolve]; [reflexivity|]. cbn in H. apply app_nth1. lia.
Qed.

Lemma rm_ab_mono : forall n n' a, rm_ab n a -> (n <= n')%nat -> rm_ab n' a.
Proof. intros n n' [p|i] H L; cbn in *; [exact I | lia]. Qed.

Lemma rm_fab_mono : forall n n' l, Forall (rm_ab n) l -> (n <= n')%nat -> Forall (rm_ab n') l.
Proof. intros n n' l H L. rewrite Forall_forall in H |- *. intros x Hx. exact (rm_ab_mono n n' x (H x Hx) L). Qed.

Lemma rm_dab_mono : forall n n' a, rm_dab n a -> (n <= n')%nat -> rm_dab n' a.
Proof.
  intros n n' a (A1 & A2 & A3 & A4 & A5 & A6 & A7) L.
  split; [exact (rm_ab_mono _ _ _ A1 L)|]. split; [exact (rm_ab_mono _ _ _ A2 L)|].
  split; [exact (rm_ab_mono _ _ _ A3 L)|]. split; [exact (rm_fab_mono _ _ _ A4 L)|].
  split; [exact (rm_fab_mono _ _ _ A5 L)|]. split; [exact (rm_ab_mono _ _ _ A6 L) | exact (rm_fab_mono _ _ _ A7 L)].
Qed.

Lemma rm_fab_skipn : forall n k l, Forall (rm_ab n) l -> Forall (rm_ab n) (skipn k l).
Proof.
  intros n k l H. rewrite Forall_forall in H |- *. intros x Hx. apply H.
  rewrite <- (firstn_skipn k l). apply in_or_app. right. exact Hx.
Qed.

Lemma rm_nth_ab : forall n ks j, Forall (rm_ab j) ks -> rm_ab j (nth n ks adr0).
Proof.
  intros n ks j H. destruct (nth_in_or_default n ks adr0) as [Hin|Hd].
  - rewrite Forall_forall in H. exact (H _ Hin).
  - rewrite Hd. exact I.
Qed.

Lemma rm_swap_forall : forall {X : Type} (P : X -> Prop) d n l, Forall P l -> P d -> Forall P (swap_remove d n l).
Proof.
  intros X P d n l H Hd. unfold swap_remove.
  assert (HL : P (last l d)).
  { clear n. induction l as [|x l IH]; [exact Hd|]. apply Forall_cons_iff in H as [H1 H2].
    destruct l as [|y l]; [exact H1 | exact (IH H2)]. }
  assert (HS : forall y m, P y -> Forall P (set_nth m y l)).
  { clear HL. induction H as [|x l Hx Hl IH]; intros y [|m] Hy; cbn [set_nth]; constructor; auto. }
  pose proof (HS _ n HL) as HS'. rewrite Forall_forall in HS' |- *. intros x Hx. apply HS'.
  rewrite <- (firstn_skipn (length l - 1) (set_nth n (last l d) l)). apply in_or_app. left. exact Hx.
Qed.

Lemma rm_wf_app : forall (t1 t2 : trF) j, wf_from sptr j t1 -> wf_from sptr (j + nretF t1) t2 ->
  wf_from sptr j (t1 ++ t2).
Proof.
  induction t1 as [|ev t1 IH]; intros t2 j H1 H2; cbn [app].
  - replace j with (j + nretF ([] : trF))%nat by (cbn; lia). exact H2.
  - destruct H1 as [Ha H1]. split; [exact Ha|]. apply IH; [exact H1|].
    rewrite p3c_nret_cons, Nat.add_assoc in H2. exact H2.
Qed.

(* A run and its room read only the addresses below j + nret t, the trace being well formed from j. *)
Lemma rm_wf_ext : forall F Q Q' (t : trF) b j, wf_from sptr j t ->
  (forall i, (i < j + nretF t)%nat -> nth i Q (SP 0 0) = nth i Q' (SP 0 0)) ->
  p3c_run F Q b j t = p3c_run F Q' b j t /\ (p3c_room F Q b j t <-> p3c_room F Q' b j t).
Proof.
  intros F Q Q' t. induction t as [|ev t IH]; intros b j Hw HQ; [split; [reflexivity | tauto]|].
  destruct Hw as [Ha Hw]. rewrite p3c_nret_cons in HQ.
  destruct ev as [n|n a|k n a]; cbn [rets] in Hw, HQ; cbn [run_from room_from].
  - rewrite Nat.add_1_r in Hw.
    destruct (IH (rt_malloc F b n) (S j) Hw ltac:(intros i Hi; apply HQ; lia)) as [R1 R2].
    split; [exact R1 | rewrite R2; tauto].
  - rewrite Nat.add_0_r in Hw.
    assert (RA : resolveF Q a = resolveF Q' a).
    { destruct a as [p|i]; cbn [resolve]; [reflexivity|]. apply HQ. cbn in Ha. lia. }
    rewrite RA. apply IH; [exact Hw | intros i Hi; apply HQ; lia].
  - rewrite Nat.add_1_r in Hw.
    assert (RA : resolveF Q a = resolveF Q' a).
    { destruct a as [p|i]; cbn [resolve]; [reflexivity|]. apply HQ. cbn in Ha. lia. }
    assert (RJ : nth j Q (SP 0 0) = nth j Q' (SP 0 0)) by (apply HQ; lia).
    rewrite RA, RJ.
    destruct (IH (rt_realloc F b k n (resolveF Q' a) (nth j Q' (SP 0 0))) (S j) Hw
      ltac:(intros i Hi; apply HQ; lia)) as [R1 R2].
    split; [exact R1 | rewrite R2; tauto].
Qed.

Lemma rm_sl_wf : forall f mx no cap rem j o, rm_ab j o ->
  wf_from sptr j (fst (sl_run f mx no cap rem j o)) /\
  rm_ab (j + nretF (fst (sl_run f mx no cap rem j o))) (snd (snd (sl_run f mx no cap rem j o))).
Proof.
  induction f as [|f IH]; intros mx no cap rem j o Ho; cbn [sl_run].
  - split; [exact I|]. cbn [fst snd]. apply (rm_ab_mono j); [exact Ho | lia].
  - destruct (rem <=? 0); [split; [exact I|]; cbn [fst snd]; apply (rm_ab_mono j); [exact Ho | lia]|].
    destruct (cap <? no + (if negb (mx =? 0) && (mx <? rem) then mx else rem)).
    + match goal with |- context [sl_run f mx ?no' ?c' ?rem' (S j) (Ret j)] =>
        destruct (IH mx no' c' rem' (S j) (Ret j) ltac:(cbn; lia)) as [W B] end.
      cbn [fst snd]. split.
      * split; [destruct (cap =? 0); [exact I | exact Ho]|].
        destruct (cap =? 0); cbn [rets]; rewrite Nat.add_1_r; exact W.
      * rewrite p3c_nret_cons. destruct (cap =? 0); cbn [rets]; (eapply rm_ab_mono; [exact B | lia]).
    + apply IH. exact Ho.
Qed.

Lemma rm_send_wf : forall live mx no cap len j o, rm_ab j o ->
  wf_from sptr j (send_line_tr live mx no cap len j o) /\
  rm_ab (j + nretF (send_line_tr live mx no cap len j o)) (send_line_out live mx no cap len j o).
Proof.
  intros live mx no cap len j o Ho. unfold send_line_tr, send_line_out.
  destruct live; [apply rm_sl_wf; exact Ho | split; [exact I | apply (rm_ab_mono j); [exact Ho | lia]]].
Qed.

Lemma rm_grow_wf : forall cap used j b, rm_ab j b ->
  wf_from sptr j (fst (grow_tr cap used j b)) /\
  rm_ab (j + nretF (fst (grow_tr cap used j b))) (snd (snd (grow_tr cap used j b))).
Proof.
  intros cap used j b Hb. unfold grow_tr. destruct (cap - used <? 4096); cbn [fst snd].
  - split.
    + split; [destruct (cap =? 0); [exact I | exact Hb] | exact I].
    + destruct (cap =? 0); cbn; lia.
  - split; [exact I | apply (rm_ab_mono j); [exact Hb | lia]].
Qed.

Lemma rm_push_wf : forall v N CAP n j, rm_ab j v -> wf_from sptr j (ListTr.list_push_tra v N CAP n) /\
  (1 <= nretF (ListTr.list_push_tra v N CAP n))%nat /\
  (N = CAP -> nretF (ListTr.list_push_tra v N CAP n) = 2%nat).
Proof.
  intros v N CAP n j Hv. unfold ListTr.list_push_tra.
  destruct (Z.eqb_spec N CAP) as [E|E]; [destruct (CAP =? 0)|]; cbn;
    (split; [|split; [lia | intros X; first [reflexivity | contradiction]]]);
    repeat split; try exact I; exact Hv.
Qed.

Lemma rm_drop_wf : forall a n j, rm_ab j a ->
  wf_from sptr j (ListTr.list_drop_tra a n) /\ nretF (ListTr.list_drop_tra a n) = 0%nat.
Proof. intros a n j Ha. unfold ListTr.list_drop_tra. cbn. split; [split; [exact Ha | exact I] | reflexivity]. Qed.

Lemma rm_pushes_wf : forall ls n cap j v rs, rm_ab j v -> Forall (rm_ab j) rs ->
  wf_from sptr j (fst (fst (pushes_run n cap ls j v rs))) /\
  rm_ab (j + nretF (fst (fst (pushes_run n cap ls j v rs)))) (fst (snd (pushes_run n cap ls j v rs))) /\
  Forall (rm_ab (j + nretF (fst (fst (pushes_run n cap ls j v rs))))) (snd (snd (pushes_run n cap ls j v rs))).
Proof.
  induction ls as [|l ls IH]; intros n cap j v rs Hv Hr; cbn [pushes_run fst snd].
  - split; [exact I|]. split; [apply (rm_ab_mono j); [exact Hv | lia] | apply (rm_fab_mono j); [exact Hr | lia]].
  - destruct (rm_push_wf v n cap (Z.of_nat (length l)) j Hv) as (W1 & N1 & N2).
    match goal with |- context [pushes_run (n + 1) (push_cap n cap) ls ?j' ?v' ?rs'] =>
      destruct (IH (n + 1) (push_cap n cap) j' v' rs') as (W2 & B2 & F2) end.
    + destruct (Z.eqb_spec n cap) as [E|E].
      * cbn [rm_ab]. rewrite (N2 E). lia.
      * apply (rm_ab_mono j); [exact Hv | lia].
    + apply Forall_app. split; [apply (rm_fab_mono j); [exact Hr | lia] | constructor; [cbn [rm_ab]; lia | constructor]].
    + split; [apply rm_wf_app; [exact W1 | exact W2]|].
      rewrite nret_app, Nat.add_assoc. split; [exact B2 | exact F2].
Qed.

Lemma rm_seen_wf : forall H ka l j ha ks, rm_ab j ha -> Forall (rm_ab j) ks ->
  wf_from sptr j (fst (fst (seen_tr H ka l j ha ks))) /\
  rm_ab (j + nretF (fst (fst (seen_tr H ka l j ha ks)))) (fst (snd (seen_tr H ka l j ha ks))) /\
  Forall (rm_ab (j + nretF (fst (fst (seen_tr H ka l j ha ks))))) (snd (snd (seen_tr H ka l j ha ks))).
Proof.
  intros H ka l j ha ks Hh Hk. unfold seen_tr.
  destruct (gesture l) as [[[|] x]|]; [destruct (index_of x H) as [n|] | destruct (index_of x H) as [n|] |];
    cbn [fst snd].
  - split; [exact I|]. split; [apply (rm_ab_mono j); [exact Hh | lia] | apply (rm_fab_mono j); [exact Hk | lia]].
  - split; [|split].
    + split; [destruct (ka =? 0); [exact I | exact Hh]|]. split; exact I.
    + destruct (ka =? 0); cbn; lia.
    + apply Forall_app. split; [apply (rm_fab_mono j); [exact Hk | lia]|].
      constructor; [destruct (ka =? 0); cbn; lia | constructor].
  - split; [|split].
    + split; [exact (rm_nth_ab n ks j Hk) | exact I].
    + apply (rm_ab_mono j); [exact Hh | lia].
    + apply rm_swap_forall; [apply (rm_fab_mono j); [exact Hk | lia] | exact I].
  - split; [exact I|]. split; [apply (rm_ab_mono j); [exact Hh | lia] | apply (rm_fab_mono j); [exact Hk | lia]].
  - split; [exact I|]. split; [apply (rm_ab_mono j); [exact Hh | lia] | apply (rm_fab_mono j); [exact Hk | lia]].
Qed.

Lemma rm_lr_wf : forall live mx ls no cap H ka j o ha ks, rm_ab j o -> rm_ab j ha -> Forall (rm_ab j) ks ->
  wf_from sptr j (fst (fst (lines_run live mx no cap H ka ls j o ha ks))) /\
  rm_ab (j + nretF (fst (fst (lines_run live mx no cap H ka ls j o ha ks))))
    (fst (fst (snd (lines_run live mx no cap H ka ls j o ha ks)))) /\
  rm_ab (j + nretF (fst (fst (lines_run live mx no cap H ka ls j o ha ks))))
    (snd (fst (snd (lines_run live mx no cap H ka ls j o ha ks)))) /\
  Forall (rm_ab (j + nretF (fst (fst (lines_run live mx no cap H ka ls j o ha ks)))))
    (snd (snd (lines_run live mx no cap H ka ls j o ha ks))).
Proof.
  intros live mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks Ho Hh Hk; cbn [lines_run fst snd].
  - split; [exact I|]. split; [apply (rm_ab_mono j); [exact Ho | lia]|].
    split; [apply (rm_ab_mono j); [exact Hh | lia] | apply (rm_fab_mono j); [exact Hk | lia]].
  - destruct (rm_send_wf live mx no cap (Z.of_nat (length l) + 1) j o Ho) as (W1 & B1).
    pose proof (rm_ab_mono j (j + nretF (send_line_tr live mx no cap (Z.of_nat (length l) + 1) j o)) ha Hh
      ltac:(lia)) as Hh'.
    pose proof (rm_fab_mono j (j + nretF (send_line_tr live mx no cap (Z.of_nat (length l) + 1) j o)) ks Hk
      ltac:(lia)) as Hk'.
    destruct (rm_seen_wf H ka l _ ha ks Hh' Hk') as (W2 & B2 & F2).
    match goal with |- context [lines_run live mx ?no' ?cap' ?H' ?ka' ls ?j' ?o' ?ha' ?ks'] =>
      destruct (IH no' cap' H' ka' j' o' ha' ks') as (W3 & B3 & B4 & F4) end.
    + eapply rm_ab_mono; [exact B1 | lia].
    + exact B2.
    + exact F2.
    + split; [apply rm_wf_app; [exact W1 | apply rm_wf_app; [exact W2 | exact W3]]|].
      rewrite !nret_app, !Nat.add_assoc. split; [exact B3|]. split; [exact B4 | exact F4].
Qed.

Lemma rm_dr_wf : forall f live mx s j a, rm_dab j a ->
  wf_from sptr j (fst (drain_run f live mx s j a)) /\
  rm_dab (j + nretF (fst (drain_run f live mx s j a))) (snd (snd (drain_run f live mx s j a))).
Proof.
  induction f as [|f IH]; intros live mx s j a Ha; cbn [drain_run].
  - split; [exact I|]. apply (rm_dab_mono j); [exact Ha | lia].
  - pose proof Ha as (Ao & Ab & Ah & Ak & Ap & Ae & Ar).
    destruct (rm_grow_wf (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a) Ab) as (Wg & Bg).
    assert (Ha1 : forall n, (j <= n)%nat -> rm_ab n (snd (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a)))) ->
              rm_dab n (DA (da_out a) (snd (snd (grow_tr (ds_cap s) (Z.of_nat (length (ds_u s))) j (da_buf a))))
                          (da_hp a) (da_keys a) (da_pend a) (da_ev a) (da_erecs a))).
    { intros n Ln Hb. split; [exact (rm_ab_mono _ _ _ Ao Ln)|]. split; [exact Hb|].
      split; [exact (rm_ab_mono _ _ _ Ah Ln)|]. split; [exact (rm_fab_mono _ _ _ Ak Ln)|].
      split; [exact (rm_fab_mono _ _ _ Ap Ln)|]. split; [exact (rm_ab_mono _ _ _ Ae Ln) | exact (rm_fab_mono _ _ _ Ar Ln)]. }
    destruct (ds_eintr s).
    + match goal with |- context [drain_run f live mx ?s' ?j' ?a'] =>
        destruct (IH live mx s' j' a') as (W & B) end.
      * apply Ha1; [lia | exact Bg].
      * cbn [fst snd]. split; [apply rm_wf_app; [exact Wg | exact W]|]. rewrite nret_app, Nat.add_assoc. exact B.
    + destruct (ds_pend s) as [|r0 rs].
      * cbn [fst snd]. split; [exact Wg | apply Ha1; [lia | exact Bg]].
      * match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end.
        -- cbn [fst snd]. split; [exact Wg | apply Ha1; [lia | exact Bg]].
        -- match goal with |- context [pushes_run (ds_en s) (ds_ecap s) ?ls' ?j1 (da_ev a) (da_erecs a)] =>
             destruct (rm_pushes_wf ls' (ds_en s) (ds_ecap s) j1 (da_ev a) (da_erecs a)
               (rm_ab_mono j j1 _ Ae ltac:(lia)) (rm_fab_mono j j1 _ Ar ltac:(lia))) as (Wp & Bp & Fp) end.
           match goal with |- context [if ?w then ListTr.list_drop_tra ?x ?y else []] =>
             assert (Wd : forall n, (j <= n)%nat -> wf_from sptr n (if w then ListTr.list_drop_tra x y else []) /\
                       nretF (if w then ListTr.list_drop_tra x y else []) = 0%nat);
             [intros n Ln; destruct w; [apply rm_drop_wf; apply (rm_ab_mono j); [apply rm_nth_ab; exact Ap | lia] |
                                        split; [exact I | reflexivity]] |] end.
           match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
           match goal with |- context [lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 _ _ _] =>
             destruct (rm_lr_wf live mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 (da_out a) (da_hp a) (da_keys a)
               (rm_ab_mono j j3 _ Ao ltac:(lia)) (rm_ab_mono j j3 _ Ah ltac:(lia)) (rm_fab_mono j j3 _ Ak ltac:(lia)))
               as (Wl & Bo & Bh & Fk);
             destruct (snd (fst (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 (da_out a) (da_hp a)
               (da_keys a)))) as [[oc' H'] ka'];
             destruct (snd (lines_run live mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 (da_out a) (da_hp a)
               (da_keys a))) as [[o' ha'] ks'] eqn:ES end.
           cbn [fst snd] in Bo, Bh, Fk.
           match goal with |- context [drain_run f live mx ?s' ?j' ?a'] =>
             destruct (IH live mx s' j' a') as (W & B) end.
           ++ split; [exact Bo|]. split; [apply (rm_ab_mono _ _ _ Bg); lia|]. split; [exact Bh|]. split; [exact Fk|].
              split; [cbn [da_pend]; match goal with |- Forall _ (if ?w then _ else _) => destruct w end;
                      [apply rm_fab_skipn|]; apply (rm_fab_mono j); [exact Ap | lia | exact Ap | lia]|].
              split; [apply (rm_ab_mono _ _ _ Bp); lia | apply (rm_fab_mono _ _ _ Fp); lia].
           ++ cbn [fst snd]. split.
              ** apply rm_wf_app; [exact Wg|]. apply rm_wf_app; [exact Wp|]. apply rm_wf_app; [apply Wd; lia|].
                 apply rm_wf_app; [exact Wl | exact W].
              ** rewrite !nret_app, !Nat.add_assoc. exact B.
Qed.

(* drain's run from base 0 at start addresses reads only what its own requests returned. *)
Lemma rm_drain_wf : forall F live mx NO CAP e h L A x qs ext b,
  let a := drain_start (known_at L A) (known_at L A x) e h in
  length qs = nretF (drain_tr live mx NO CAP e h 0 a) ->
  runF F (qs ++ ext) b (drain_tr live mx NO CAP e h 0 a) = runF F qs b (drain_tr live mx NO CAP e h 0 a) /\
  (roomF F (qs ++ ext) b (drain_tr live mx NO CAP e h 0 a) <-> roomF F qs b (drain_tr live mx NO CAP e h 0 a)) /\
  rm_dab (length qs) (drain_adr live mx NO CAP e h 0 a).
Proof.
  intros F live mx NO CAP e h L A x qs ext b a QL.
  assert (A0 : rm_dab 0 a).
  { unfold a, drain_start, rm_dab. cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
    repeat split; try exact I; apply Forall_forall; intros y Hy; apply in_map_iff in Hy as (z & <- & _); exact I. }
  unfold drain_tr, drain_adr, drain_go in *.
  destruct (rm_dr_wf (S (S (length (pending_stream h)))) live mx (drain_init NO CAP e h) 0 a A0) as (W & B).
  destruct (rm_wf_ext F (qs ++ ext) qs _ b 0 W) as (R1 & R2).
  { intros i Hi. apply app_nth1. lia. }
  split; [exact R1|]. split; [exact R2|]. rewrite QL. exact B.
Qed.

(* A dead drain leaves g_out's address as it was. *)
Lemma rm_lr_out_dead : forall mx ls no cap H ka j o ha ks,
  fst (fst (snd (lines_run false mx no cap H ka ls j o ha ks))) = o.
Proof.
  intros mx ls. induction ls as [|l ls IH]; intros no cap H ka j o ha ks; cbn [lines_run fst snd]; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma rm_dr_out_dead : forall f mx s j a, da_out (snd (snd (drain_run f false mx s j a))) = da_out a.
Proof.
  induction f as [|f IH]; intros mx s j a; cbn [drain_run fst snd]; [reflexivity|].
  destruct (ds_eintr s); cbn [fst snd]; [rewrite IH; reflexivity|].
  destruct (ds_pend s) as [|r0 rs]; cbn [fst snd]; [reflexivity|].
  match goal with |- context [if ?c <=? 0 then _ else _] => destruct (c <=? 0) end; [reflexivity|].
  match goal with |- context [chunk ?u ?k ?d] => destruct (chunk u k d) as [[u' sk'] rl] end.
  match goal with |- context [lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl ?j3 _ _ _] =>
    pose proof (rm_lr_out_dead mx rl (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) j3 (da_out a) (da_hp a) (da_keys a)) as LO;
    destruct (snd (fst (lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 (da_out a) (da_hp a)
      (da_keys a)))) as [[oc' H'] ka'];
    destruct (snd (lines_run false mx (ds_no s) (ds_ocap s) (ds_H s) (ds_ka s) rl j3 (da_out a) (da_hp a)
      (da_keys a))) as [[o' ha'] ks'] eqn:ES end.
  cbn [fst snd] in LO. cbn [snd]. rewrite IH. cbn [da_out]. exact LO.
Qed.

(* drain's addresses, like its requests, do not depend on the send's liveness when no line is complete. *)
Lemma rm_dadr_live : forall live live' mx NO CAP e h j a,
  J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h) -> 0 <= hs_off h ->
  lines (hs_state h) (bzs (pending_stream h)) = [] ->
  drain_adr live mx NO CAP e h j a = drain_adr live' mx NO CAP e h j a.
Proof.
  intros live live' mx NO CAP e h j a HJ HO HL. unfold drain_adr, drain_go.
  assert (HL' : lines (ds_ref (drain_init NO CAP e h)) (rma_ds (drain_init NO CAP e h)) = [])
    by (rewrite rma_ds_init; exact HL).
  rewrite (rma_dr_live _ (drain_init NO CAP e h) live live' mx j a HJ HO HL'). reflexivity.
Qed.

Lemma rm_map_ka : forall (f : Z -> adrF) (ks ks' : list (Z * list byte * list byte)), map key_addr ks = map key_addr ks' ->
  map (fun k => f (key_addr k)) ks = map (fun k => f (key_addr k)) ks'.
Proof.
  intros f ks. induction ks as [|k ks IH]; intros [|k' ks'] H; cbn [map] in H |- *; try discriminate; [reflexivity|].
  injection H as H1 H2. rewrite H1, (IH ks' H2). reflexivity.
Qed.
Lemma rm_f2_in : forall {X Y : Type} (P Q : X -> Y -> Prop) l l', Forall2 P l l' ->
  (forall x y, In x l -> P x y -> Q x y) -> Forall2 Q l l'.
Proof.
  intros X Y P Q l l' H. induction H as [|x y l l' Hxy _ IH]; intros HQ; constructor.
  - apply HQ; [left; reflexivity | exact Hxy].
  - apply IH. intros x0 y0 Hx0 Hp. apply HQ; [right; exact Hx0 | exact Hp].
Qed.

(* src_links moves to a state where every live block at an address of h1's blocks stays live. *)
Lemma rm_sl_mono : forall L A L' A' qs nm fa h1,
  (forall p a n, live_at L A p a n -> 0 < n -> In a (hs_blocks h1) -> live_at L' A' p a n) ->
  src_links L A qs nm fa h1 -> src_links L' A' qs nm fa h1.
Proof.
  intros L A L' A' qs nm fa h1 HM (S1 & S2 & S3 & (S4 & S5) & S6 & S7).
  assert (HB : forall a, In a (list_blocks (hs_pending h1)) \/ a = hs_partial h1 \/
                 In a (list_blocks (hs_expected h1)) \/ In a (list_blocks (hs_held h1)) -> In a (hs_blocks h1)).
  { intros a Ha. unfold hs_blocks. rewrite !in_app_iff. cbn [In].
    destruct Ha as [H|[H|[H|H]]];
      [left; exact H | right; left; left; symmetry; exact H | right; right; left; exact H |
       right; right; right; exact H]. }
  assert (LV : forall l, 0 < hl_cap l -> In (hl_v l) (list_blocks l)).
  { intros l Hl. unfold list_blocks. apply in_or_app. left. destruct (Z.eqb_spec (hl_cap l) 0); [lia|].
    left. reflexivity. }
  assert (LR : forall l r, In r (hl_recs l) -> In (fst r) (list_blocks l)).
  { intros l r Hr. unfold list_blocks. apply in_or_app. right. apply in_map. exact Hr. }
  split; [intros HC; apply HM; [exact (S1 HC) | lia | apply HB; left; exact (LV _ HC)]|].
  split; [apply (rm_f2_in _ _ _ _ S2); intros r a Hr Hl; apply HM;
          [exact Hl | lia | apply HB; left; exact (LR _ _ Hr)]|].
  split; [apply HM; [exact S3 | lia | apply HB; right; left; reflexivity]|].
  split; [split|].
  - intros HC. apply HM; [exact (S4 HC) | lia | apply HB; right; right; left; exact (LV _ HC)].
  - apply (rm_f2_in _ _ _ _ S5). intros r a Hr Hl. apply HM; [exact Hl | lia |].
    apply HB; right; right; left; exact (LR _ _ Hr).
  - split.
    + intros HC. apply HM; [exact (S6 HC) | lia | apply HB; right; right; right; exact (LV _ HC)].
    + rewrite Forall_forall in S7 |- *. intros r Hr. apply HM; [exact (S7 r Hr) | lia |].
      apply HB; right; right; right; exact (LR _ _ Hr).
Qed.

(* src_links read with more returned addresses: its addresses name only the first ones. *)
Lemma rm_sl_ext : forall L A qd ext L0 A0 fa h1, rm_dab (length qd) fa ->
  src_links L A qd (known_at L0 A0) fa h1 -> src_links L A (qd ++ ext) (known_at L0 A0) fa h1.
Proof.
  intros L A qd ext L0 A0 fa h1 (_ & _ & _ & _ & DP & DE & DR) (S1 & S2 & S3 & (S4 & S5) & S6 & S7).
  assert (RX : forall a, rm_ab (length qd) a -> resolveF (qd ++ ext) a = resolveF qd a)
    by (intros a Ha; exact (rm_ab_res _ qd ext a Ha eq_refl)).
  assert (F2 : forall (rs : list (Z * list byte)) das, Forall (rm_ab (length qd)) das ->
            Forall2 (fun r a => live_at L A (resolveF qd a) (fst r) (Z.of_nat (length (snd r)) + 1)) rs das ->
            Forall2 (fun r a => live_at L A (resolveF (qd ++ ext) a) (fst r) (Z.of_nat (length (snd r)) + 1)) rs das).
  { intros rs das D H. induction H as [|r a rs das Hra _ IH]; constructor.
    - apply Forall_cons_iff in D as [D1 _]. rewrite (RX a D1). exact Hra.
    - apply IH. exact (proj2 (proj1 (Forall_cons_iff _ _ _) D)). }
  split; [intros HC; exact (S1 HC)|].
  split; [exact (F2 _ _ DP S2)|].
  split; [exact S3|].
  split; [split|].
  - intros HC. rewrite (RX _ DE). exact (S4 HC).
  - exact (F2 _ _ DR S5).
  - split; [intros HC; exact (S6 HC) | exact S7].
Qed.

Lemma rm_fst_combine : forall {X Y : Type} (l1 : list X) (l2 : list Y), length l1 = length l2 ->
  map fst (combine l1 l2) = l1.
Proof.
  intros X Y l1. induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in *; try discriminate; [reflexivity|].
  f_equal. apply IH. lia.
Qed.

(* The held keys at their addresses after drain, against gestures_end's start names. *)
Lemma rm_xks_f2 : forall L A qd Q Q' ks das, NoDup (map fst (blocks L A)) ->
  Forall2 (fun k a => live_at L A (resolveF qd a) (key_addr k) (Z.of_nat (length (key_text k)) + 1)) ks das ->
  (forall a, In a das -> resolveF Q a = resolveF qd a) ->
  Forall2 (fun x x' => fst x = fst x' /\ resolveF Q (snd x) = resolveF Q' (snd x'))
    (combine (key_lens ks) das) (key_runs (known_at L A) ks).
Proof.
  intros L A qd Q Q' ks das ND H. induction H as [|k a ks das Hka _ IH]; intros HQ;
    cbn [combine key_lens key_runs map]; constructor.
  - cbn [fst snd]. split; [reflexivity|]. rewrite (HQ a (or_introl eq_refl)). unfold known_at. cbn [resolve].
    symmetry. exact (p3c_live_sptr _ _ _ _ _ ND Hka).
  - apply IH. intros a0 Ha0. apply HQ. right. exact Ha0.
Qed.

(* Keys still at their start blocks: linked through the start names. *)
Lemma rm_keys_f2 : forall L A qs ks ks0, NoDup (map fst (blocks L A)) ->
  map key_addr ks = map key_addr ks0 -> map key_text ks = map key_text ks0 ->
  Forall (fun k => In (key_addr k, Z.of_nat (length (key_text k)) + 1) (blocks L A)) ks0 ->
  Forall2 (fun k a => live_at L A (resolveF qs a) (key_addr k) (Z.of_nat (length (key_text k)) + 1))
    ks (map (fun k => known_at L A (key_addr k)) ks0).
Proof.
  intros L A qs ks ks0 ND. revert ks. induction ks0 as [|k0 ks0 IH]; intros [|k ks] HA HT HF; cbn [map] in HA, HT |- *;
    try discriminate; [constructor|].
  injection HA as HA1 HA2. injection HT as HT1 HT2. apply Forall_cons_iff in HF as [HF1 HF2].
  constructor; [|exact (IH ks HA2 HT2 HF2)].
  unfold known_at. cbn [resolve]. rewrite HA1, HT1. exact (sptr_of_spec L A _ _ ND HF1).
Qed.

Section RMB.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Local Notation segs := (ms_segs Bm).
Local Notation MR := (aa_MR API).
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis BSP : block_slack_present Bm API.
Hypothesis FREEPC : ms_free Bm = 0x15f4c.
Hypothesis HND : forall L A mem md, aa_MR API L A mem md -> NoDup (map fst (blocks L A)).

Section Run.
Hypothesis SEGS : ms_segs Bm = rsegs.
Hypothesis DRC : drain_contract Bm API F.
Hypothesis GSC : gestures_end_contract Bm API F.
Hypothesis FRC : free_contract_rt Bm API F.
Hypothesis FNC : free_null_contract Bm.
Hypothesis MCP : memcpy_contract.
Hypothesis MCS : memcpy_same_contract.
Hypothesis SPL : pthread_mutex_lock_contract.
Hypothesis SPU : pthread_mutex_unlock_contract.
Hypothesis SWK : wake_contract.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (bnd : rt_R F) (es : list rentry) (G : Z) (tail : list byte) (h : hsrc) (j : nat) (fs os : list Z)
  (O junk : list byte) (cl br dd ei : Z) (mx nout cap out : word).

Local Notation FD := (bv_signed (getr regs0 10)).
Local Notation N := (Z.of_nat (length es)).
Local Notation ERR := (errno_addr Bm).
Local Notation NO := (bv_unsigned nout).
Local Notation CAP := (bv_unsigned cap).
Local Notation OUT := (bv_unsigned out).
Local Notation HA := (G_S + SRC_SIZE * Z.of_nat j).
Local Notation PL := (Z.of_nat (length (pending_stream h))).
Local Notation lv := (send_live cl br dd 1).
Local Notation nm0 := (known_at L0 A0).
Local Notation trR := (relay_remove_tr lv (bv_unsigned mx) NO CAP FD es h (known_at L0 A0) 0
  (known_at L0 A0 (bv_unsigned out))).
Local Notation SP := (bv_unsigned (getr regs0 2)).

Hypothesis PRE : call_pre_k Bm MR RELAY_REMOVE_K L0 A0 regs0 mem0 md0.
Hypothesis INIT : st_init_done A0 = true.
Hypothesis TPE : ms_tp Bm + ERRNO_OFF = ERR.
Hypothesis HERR4 : ERR mod 4 = 0.
Hypothesis EHI : G_LOCK_HI <= ERR.
Hypothesis RO0 : ro_agree segs mem0.
Hypothesis IMR : forall a, G_RELAY_LO <= a < G_S + SRC_SIZE * SOURCES_MAX -> img_plain Bm a.
Hypothesis IML : forall a, G_LISTEN <= a < G_WAKE1 + 4 -> img_plain Bm a.
Hypothesis IME : forall a, ERR <= a < ERR + 4 -> in_img Bm a.
Hypothesis IM5 : forall a, END5_ADDR <= a < END5_ADDR + 5 -> img_plain Bm a.
Hypothesis HFD : - 2 ^ 31 <= FD < 2 ^ 31.
Hypothesis CLK : rw_cells segs mem0 G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Hypothesis CWK : bytes_at segs mem0 G_WAKE1 (le4 (Z_to_bv 64 (-1))).
Hypothesis CNS : rw_cells segs mem0 G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)].
Hypothesis CSR : rw_cells segs mem0 G_SRC [C8 (Z_to_bv 64 G)].
Hypothesis HN4 : N <= 4.
Hypothesis GIN : In (G, SRC_TABLE) (blocks L0 A0).
Hypothesis GFR : fresh_block Bm G SRC_TABLE.
Hypothesis TAB : table_at Bm mem0 G es tail.
Hypothesis EOK : Forall (entry_ok Bm L0 A0 mem0) es.
Hypothesis NDF : NoDup (map re_fd es).
Hypothesis NDB : NoDup (G :: OUT :: concat (map entry_blocks es)).
Hypothesis Hcl : cl = 3 \/ cl = -1.
Hypothesis Hbr : br = 0 \/ br = 1.
Hypothesis Hdd : dd = 0 \/ dd = 1.
Hypothesis Hei : ei = 0 \/ ei = 1.
Hypothesis CCL : rw_cells segs mem0 G_CLIENT [C4 (Z_to_bv 64 cl)].
Hypothesis CBR : rw_cells segs mem0 G_BROKEN [C1 (Z_to_bv 8 br)].
Hypothesis CDD : rw_cells segs mem0 G_DEAD [C1 (Z_to_bv 8 dd)].
Hypothesis CEI : rw_cells segs mem0 G_EINTR [C1 (Z_to_bv 8 ei)].
Hypothesis COV : rw_cells segs mem0 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out].
Hypothesis CER : exists ev, rw_cells segs mem0 ERR [C4 ev].
Hypothesis OUTD : (CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
  (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L0 A0) /\ fresh_block Bm OUT CAP /\
   bytes_at segs mem0 OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO).
Hypothesis RES : rt_ok F A0 bnd.
Hypothesis SRCP : forall e, In e es -> re_fd e = FD -> re_eof e = 0 ->
  src_at Bm L0 A0 mem0 HA h /\ others_at Bm mem0 j FD fs os /\ (j < 4)%nat /\ hs_fd h = FD /\
  re_skip e = hs_overlong h /\ (re_skip e = 0 -> bzs (re_U e) = bzs (hs_W h)) /\
  NoDup (G :: OUT :: concat (map entry_blocks es) ++ hs_blocks h) /\
  PL < 2 ^ 26 /\ hl_cap (hs_expected h) < 2 ^ 26 /\ re_nheld e + PL < 2 ^ 26.
Hypothesis ROOM : forall qs, length qs = nretF trR -> roomF F qs bnd trR.

(* relay_remove's write set and its set of blocks given up, as its contract states them. *)
Definition Efin (a : Z) : Prop :=
  send_writes true OUT CAP a \/ G_LOCK + 4 <= a < G_LOCK + 8 \/ G_NSRC <= a < G_NSRC + 4 \/
  G <= a < G + SRC_TABLE \/
  ((exists e, In e es /\ re_fd e = FD /\ re_eof e = 0) /\ HA + 12 <= a < HA + SRC_SIZE) \/
  (exists e q m, In e es /\ re_fd e = FD /\ In (q, m) (blocks L0 A0) /\ q <= a < q + m /\
     (In q (entry_blocks e) \/ (re_eof e = 0 /\ In q (hs_blocks h)))).

(* The lines relayed from a source e0. *)
Definition Lsf (e0 : rentry) : list (list Z) :=
  if re_eof e0 =? 0 then lines (hs_state h) (bzs (pending_stream h)) else [].

(* The blocks given up when the held keys sent total KT bytes: g_out only when a send was live. *)
Definition Ffin (KT : Z) (q : Z) : Prop :=
  ((exists e, In e es /\ re_fd e = FD /\ send_live cl br dd (Z.of_nat (length (with_nul (Lsf e))) + KT) = true) /\
   q = OUT) \/
  (exists e, In e es /\ re_fd e = FD /\ (In q (entry_blocks e) \/ (re_eof e = 0 /\ In q (hs_blocks h)))).

Definition Final (c' : config) : Prop :=
  exists L' A' regs' mem' md' (OUT' CAP' : Z) (junk' LB : list byte) (e' : rentry) (h' : hsrc) (tail' : list byte),
    c' = mkCfg (YK11.mkst regs' (getr regs0 1) mem' (seg_rom segs)) md' /\
    relay_post Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e'))) L0 A0 regs0 mem0 md0
      L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF trR /\ rt_ok F A' (runF F qs bnd trR) /\
       (forall i, (i < length es)%nat -> re_fd (nth i es no_entry) = FD ->
          let e := nth i es no_entry in
          let a0 := drain_start nm0 (nm0 OUT) e h in
          (send_live cl br dd (Z.of_nat (length (with_nul (Lsf e))) + keys_total (re_keys e')) = true ->
             live_at L' A' (resolveF qs (remove_entry_out lv (bv_unsigned mx) NO CAP e h 0 a0)) OUT' CAP') /\
          (re_eof e = 0 -> src_links L' A' qs nm0 (after_drain_adr lv (bv_unsigned mx) NO CAP e h 0 a0) h'))) /\
    ro_agree segs mem' /\
    rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] /\
    bytes_at segs mem' G_WAKE1 (le4 (Z_to_bv 64 (-1))) /\
    rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G)] /\ In (G, SRC_TABLE) (blocks L' A') /\
    rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] /\
    (exists ev', rw_cells segs mem' ERR [C4 ev']) /\
    ((forall e, In e es -> re_fd e <> FD) ->
       rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] /\
       table_at Bm mem' G es tail /\ blocks L' A' = blocks L0 A0 /\
       rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 br)] /\
       rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 ei)] /\
       rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out]) /\
    (forall i, (i < length es)%nat -> re_fd (nth i es no_entry) = FD ->
       let e := nth i es no_entry in
       let Ls := Lsf e in
       let TOT := Z.of_nat (length (with_nul Ls)) + keys_total (re_keys e') in
       let live := send_live cl br dd TOT in
       let off := send_off cl br TOT in
       let fin := drain_fin lv (bv_unsigned mx) NO CAP e h in
       rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 (N - 1)); C4 (Z_to_bv 64 16)] /\
       table_at Bm mem' G (remove_at i es) tail' /\
       re_fd e' = re_fd e /\ re_eof e' = re_eof e /\
       (re_eof e = 0 ->
          src_at Bm L' A' mem' HA h' /\ others_at Bm mem' j FD fs os /\
          hs_eintr h' = 0 /\ hl_recs (hs_pending h') = [] /\ hs_off h' = 0 /\
          hl_v (hs_pending h') = hl_v (hs_pending h) /\ hl_cap (hs_pending h') = hl_cap (hs_pending h) /\
          hs_partial h' = hs_partial h /\
          hs_state h' = feed (hs_state h) (bzs (pending_stream h)) /\
          map snd (hl_recs (hs_expected h')) =
            map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Ls /\
          firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h')) = hl_recs (hs_expected h) /\
          hs_held h' = hs_held h /\
          NoDup (keys_texts (re_keys e')) /\
          same_set (keys_texts (re_keys e')) (upds (keys_texts (re_keys e)) Ls) /\
          keys_texts (re_keys e') = ds_H fin /\ hl_cap (hs_expected h') = ds_ecap fin) /\
       (re_eof e = 1 -> re_keys e' = re_keys e) /\
       bzs LB = with_nul Ls /\
       rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 (if off then br else dd))] /\
       rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 (if off then ei else 0))] /\
       (forall q m, In (q, m) (blocks L0 A0) -> q <> OUT -> ~ In q (entry_blocks e) ->
          (re_eof e = 0 -> ~ In q (hs_blocks h)) -> In (q, m) (blocks L' A')) /\
       (forall q m, In (q, m) (blocks L0 A0) -> 0 < m -> q <> OUT -> ~ In q (entry_blocks e) ->
          (re_eof e = 0 -> ~ In q (hs_blocks h)) ->
          q <> OUT' /\ (re_eof e = 0 -> ~ In q (hs_blocks h'))) /\
       (re_eof e = 0 -> NoDup (OUT' :: hs_blocks h')) /\
       (forall q m, In (q, m) (blocks L' A') ->
          (In (q, m) (blocks L0 A0) /\ q <> OUT /\ ~ In q (entry_blocks e) /\
           (re_eof e = 0 -> ~ In q (hs_blocks h))) \/
          (re_eof e = 0 /\ In q (hs_blocks h')) \/ q = OUT') /\
       (live = false -> rw_cells segs mem' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\
          (0 < CAP -> In (OUT, CAP) (blocks L' A') /\ bytes_at segs mem' OUT (O ++ junk)) /\ OUT' = OUT) /\
       (live = true ->
          NO + TOT <= CAP' /\ CAP' = remove_entry_cap lv (bv_unsigned mx) NO CAP e h /\
          In (OUT', CAP') (blocks L' A') /\ fresh_block Bm OUT' CAP' /\
          bytes_at segs mem' OUT' (O ++ LB ++ keys_out (re_keys e') ++ junk') /\
          Z.of_nat (length junk') = CAP' - NO - TOT /\
          rw_cells segs mem' G_OUTV
            [C8 mx; C8 (Z_to_bv 64 (NO + TOT)); C8 (Z_to_bv 64 CAP'); C8 (Z_to_bv 64 OUT')])).

Lemma rm_pre : MR L0 A0 mem0 md0 /\ WF A0 /\ bounded A0 /\ YK0s.ret_ok (getr regs0 1) /\ SP mod 16 = 0 /\
  alloc_ceiling + 8560 <= SP /\ SP < 2 ^ 63 /\ (forall a, SP - 8560 <= a < SP -> writable_at segs mem0 a) /\
  getr regs0 4 = Z_to_bv 64 (ms_tp Bm) /\ (forall a, ERR <= a < ERR + 4 -> writable_at segs mem0 a) /\
  m_halted md0 = None /\ m_vm_lazy md0 = [] /\ 2 ^ 46 <= alloc_ceiling < 2 ^ 47.
Proof using O PRE es junk.
  destruct rm_K as (K1 & _). destruct PRE as (HM & HW & HB & HRA & HAL & HCE & H63 & HWS & HTP & HER & _).
  rewrite K1 in HCE, HWS. unfold spZ in *. destruct (mr_model Bm MR (aa_laws API) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  split; [exact HM|]. split; [exact HW|]. split; [exact HB|]. split; [exact HRA|]. split; [exact HAL|].
  split; [lia|]. split; [exact H63|]. split; [exact HWS|]. split; [exact HTP|]. split; [exact HER|].
  split; [exact Hh|]. split; [exact Hl|]. lia.
Qed.

Lemma rm_fresh_sep : forall q n lo hi, fresh_block Bm q n -> 0 < n -> lo < hi ->
  (forall a, lo <= a < hi -> in_img Bm a) -> q + n <= lo \/ hi <= q.
Proof using O es junk.
  intros q n lo hi (_ & _ & Hf) Hn Hlh Himg.
  destruct (Z_le_gt_dec (q + n) lo) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec hi q) as [D'|D']; [right; exact D'|]. exfalso.
  apply (Hf (Z.max q lo - q)); [lia|]. replace (q + (Z.max q lo - q)) with (Z.max q lo) by lia. apply Himg. lia.
Qed.

Lemma rm_sf : 203040 <= ERR /\ ERR + 4 <= 2 ^ 21 /\ 4096 <= G /\ G + 896 <= alloc_ceiling /\ G mod 16 = 0 /\
  (G + 896 <= 202912 \/ 203424 <= G) /\ (G + 896 <= 136736 \/ 136752 <= G) /\ (G + 896 <= ERR \/ ERR + 4 <= G).
Proof using EHI GFR GIN IME IML IMR O PRE SEGS es junk.
  pose proof rm_pre as (HM & _).
  pose proof (in_img_low Bm SEGS (ERR + 3) (IME (ERR + 3) ltac:(lia))) as E1.
  unfold G_LOCK_HI in EHI.
  assert (GB := GIN). apply rk_blocks_in in GB as (p & Ep & Hp).
  pose proof (mr_blocks_range Bm MR (aa_laws API) _ _ _ _ p _ HM Hp) as GR.
  pose proof (mr_blocks_aligned Bm MR (aa_laws API) _ _ _ _ p _ HM Hp) as GA.
  rewrite Ep in GR, GA. unfold SRC_TABLE, SRC_ENTRY in GR.
  assert (S1 : G + SRC_TABLE <= 202912 \/ 203424 <= G).
  { apply (rm_fresh_sep G SRC_TABLE 202912 203424 GFR); [unfold SRC_TABLE, SRC_ENTRY; lia | lia |].
    intros a Ha. apply (IMR a). unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX. lia. }
  assert (S2 : G + SRC_TABLE <= 136736 \/ 136752 <= G).
  { apply (rm_fresh_sep G SRC_TABLE 136736 136752 GFR); [unfold SRC_TABLE, SRC_ENTRY; lia | lia |].
    intros a Ha. apply (IML a). unfold G_LISTEN, G_WAKE1. lia. }
  assert (S3 : G + SRC_TABLE <= ERR \/ ERR + 4 <= G).
  { apply (rm_fresh_sep G SRC_TABLE ERR (ERR + 4) GFR); [unfold SRC_TABLE, SRC_ENTRY; lia | lia | exact IME]. }
  unfold SRC_TABLE, SRC_ENTRY in S1, S2, S3. repeat split; lia.
Qed.

Lemma rm_g8 : G mod 8 = 0.
Proof using EHI GFR GIN IME IML IMR O PRE SEGS es junk. pose proof rm_sf as (_ & _ & _ & _ & GM & _). clear - GM. Z.div_mod_to_equations. lia. Qed.

Section Match.
Variable i : nat.
Hypothesis Hi : (i < length es)%nat.
Hypothesis HFi : re_fd (nth i es no_entry) = FD.
Local Notation e := (nth i es no_entry).
Local Notation SA := (G + 56 * Z.of_nat i).

Definition Lsi : list (list Z) := if re_eof e =? 0 then lines (hs_state h) (bzs (pending_stream h)) else [].
Definition TD : Z := Z.of_nat (length (with_nul Lsi)).
(* The addresses at drain's start, the requests of `if (!s->eof) drain (s)` and the addresses after it. *)
Definition a0M : dadr := drain_start nm0 (nm0 OUT) e h.
Definition trD : trF := if re_eof e =? 0 then drain_tr lv (bv_unsigned mx) NO CAP e h 0 a0M else [].
Definition a1M : dadr := after_drain_adr lv (bv_unsigned mx) NO CAP e h 0 a0M.
Definition sDM : dstate := after_drain lv (bv_unsigned mx) NO CAP e h.
(* The requests of gestures_end (s) and of free (s->buf) in relay_remove's trace, and g_out after. *)
Definition xksM : list (Z * adrF) := combine (map (fun x => Z.of_nat (length x)) (ds_H sDM)) (da_keys a1M).
Definition trGM : trF :=
  gestures_end_tr lv (bv_unsigned mx) (ds_no sDM) (ds_ocap sDM) xksM (ds_ka sDM) (ds_ka sDM) (nretF trD)
    (da_out a1M) (da_hp a1M).
Definition trBM : trF := if ds_cap sDM =? 0 then [] else [RFree (ds_cap sDM) (da_buf a1M)].
Definition outR : adrF := remove_entry_out lv (bv_unsigned mx) NO CAP e h 0 a0M.
Definition hbi : list Z := if re_eof e =? 0 then hs_blocks h else [].
Definition hbo (h1 : hsrc) : list Z := if re_eof e =? 0 then hs_blocks h1 else [].
Definition Tpre : list byte := concat (map entry_bytes (firstn i es)).
Definition Tpost : list byte := concat (map entry_bytes (skipn (S i) es)) ++ tail.
Definition finI : dstate := drain_fin lv (bv_unsigned mx) NO CAP e h.
Definition bufl (e1 : rentry) : list Z := if re_cap e1 =? 0 then [] else [re_buf e1].

Definition rval (r : Z) : word :=
  if r =? 2 then Z_to_bv 64 (SP - 48) else if r =? 8 then Z_to_bv 64 203000 else if r =? 9 then Z_to_bv 64 FD
  else if r =? 18 then Z_to_bv 64 202912 else if r =? 19 then Z_to_bv 64 (56 * Z.of_nat i)
  else getr regs0 (Z_to_bv 5 r).
Definition RFr (R : bvmap 5 word) : Prop := forall r, callee_saved r -> getr R (Z_to_bv 5 r) = rval r.

Definition FRM (m : word -> option byte) : Prop :=
  exists jf, rw_cells segs m (SP - 48)
    [CB 8 jf; C8 (getr regs0 19); C8 (getr regs0 18); C8 (getr regs0 9); C8 (getr regs0 8); C8 (getr regs0 1)].

(* What drain leaves for the final state when s->eof = 0: the harness's source and the held keys ks1. *)
Definition DF (L : layout) (A : astate) (m : word -> option byte) (h1 : hsrc)
    (ks1 : list (Z * list byte * list byte)) : Prop :=
  src_at Bm L A m HA h1 /\ others_at Bm m j FD fs os /\
  hs_eintr h1 = 0 /\ hl_recs (hs_pending h1) = [] /\ hs_off h1 = 0 /\
  hl_v (hs_pending h1) = hl_v (hs_pending h) /\ hl_cap (hs_pending h1) = hl_cap (hs_pending h) /\
  hs_partial h1 = hs_partial h /\
  hs_state h1 = feed (hs_state h) (bzs (pending_stream h)) /\
  map snd (hl_recs (hs_expected h1)) =
    map snd (hl_recs (hs_expected h)) ++ map (map (Z_to_bv 8)) Lsi /\
  firstn (length (hl_recs (hs_expected h))) (hl_recs (hs_expected h1)) = hl_recs (hs_expected h) /\
  hs_held h1 = hs_held h /\
  NoDup (keys_texts ks1) /\
  same_set (keys_texts ks1) (upds (keys_texts (re_keys e)) Lsi) /\
  keys_texts ks1 = ds_H finI /\ hl_cap (hs_expected h1) = ds_ecap finI.

(* The globals other than g_outv, with the lock held, g_nsrc = N, g_client_broken = b1, g_eintr = ev1. *)
Definition GLB (m : word -> option byte) (b1 ev1 : Z) : Prop :=
  rw_cells segs m G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)] /\
  bytes_at segs m G_WAKE1 (le4 (Z_to_bv 64 (-1))) /\
  rw_cells segs m G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] /\
  rw_cells segs m G_SRC [C8 (Z_to_bv 64 G)] /\
  rw_cells segs m G_CLIENT [C4 (Z_to_bv 64 cl)] /\
  rw_cells segs m G_BROKEN [C1 (Z_to_bv 8 b1)] /\
  rw_cells segs m G_DEAD [C1 (Z_to_bv 8 dd)] /\
  rw_cells segs m G_EINTR [C1 (Z_to_bv 8 ev1)] /\
  (exists ev, rw_cells segs m ERR [C4 ev]).

(* The blocks of a state (L1, A1) against the initial ones: XB the source's blocks still held, OUT1 the output
   buffer, e1 and h1 the relay's and the harness's sources after drain. *)
Definition BF (L1 : layout) (A1 : astate) (OUT1 : Z) (e1 : rentry) (h1 : hsrc) (XB : list Z) : Prop :=
  (forall q m, In (q, m) (blocks L0 A0) -> q <> OUT -> ~ In q (entry_blocks e) -> ~ In q hbi ->
     In (q, m) (blocks L1 A1)) /\
  (forall q m, In (q, m) (blocks L1 A1) ->
     (In (q, m) (blocks L0 A0) /\ q <> OUT /\ ~ In q (entry_blocks e) /\ ~ In q hbi) \/ In q (XB ++ hbo h1) \/
     q = OUT1) /\
  (forall q m, In (q, m) (blocks L0 A0) -> 0 < m -> q <> OUT -> ~ In q (entry_blocks e) -> ~ In q hbi ->
     q <> OUT1 /\ ~ In q (entry_blocks e1) /\ ~ In q (hbo h1)).

(* g_outv and the output buffer after gestures_end, against the initial ones. *)
Definition LF (L : layout) (A : astate) (m : word -> option byte) (OUT2 CAP2 : Z) (junk2 LB : list byte)
    (ks1 : list (Z * list byte * list byte)) : Prop :=
  (send_live cl br dd (TD + keys_total ks1) = false ->
     rw_cells segs m G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] /\
     (0 < CAP -> In (OUT, CAP) (blocks L A) /\ bytes_at segs m OUT (O ++ junk)) /\ OUT2 = OUT) /\
  (send_live cl br dd (TD + keys_total ks1) = true ->
     NO + (TD + keys_total ks1) <= CAP2 /\
     CAP2 = remove_entry_cap lv (bv_unsigned mx) NO CAP e h /\
     In (OUT2, CAP2) (blocks L A) /\ fresh_block Bm OUT2 CAP2 /\
     bytes_at segs m OUT2 (O ++ LB ++ keys_out ks1 ++ junk2) /\
     Z.of_nat (length junk2) = CAP2 - NO - (TD + keys_total ks1) /\
     rw_cells segs m G_OUTV
       [C8 mx; C8 (Z_to_bv 64 (NO + (TD + keys_total ks1))); C8 (Z_to_bv 64 CAP2); C8 (Z_to_bv 64 OUT2)]).

(* The resource state after the whole run, with the held keys sent totalling KT: g_out after the run is the
   output buffer when a send was live; drain's harness-source blocks are linked. *)
Definition RT (L1 : layout) (A1 : astate) (KT OUT1 CAP1 : Z) (h1 : hsrc) : Prop :=
  exists qs, length qs = nretF trR /\ rt_ok F A1 (runF F qs bnd trR) /\
    (send_live cl br dd (TD + KT) = true -> live_at L1 A1 (resolveF qs outR) OUT1 CAP1) /\
    (re_eof e = 0 -> src_links L1 A1 qs nm0 a1M h1).

Lemma rm_e_in : In e es.
Proof using Hi. apply nth_In. exact Hi. Qed.

Lemma rm_i_uniq : forall i', (i' < length es)%nat -> re_fd (nth i' es no_entry) = FD -> i' = i.
Proof using HFi Hi NDF.
  intros i' Hi' HF'. apply (rma_nodup_map_nth re_fd es no_entry i' i NDF Hi' Hi). rewrite HF', HFi. reflexivity.
Qed.

Lemma rm_FDnn : 0 <= FD.
Proof using EOK HFi Hi O junk.
  destruct (proj1 (Forall_forall _ _) EOK e rm_e_in) as (_ & _ & _ & _ & HF & _). rewrite <- HFi. lia.
Qed.

(* relay_remove's trace: drain's, then gestures_end's, then free (s->buf)'s. *)
Lemma rm_trR : trR = trD ++ trGM ++ trBM.
Proof using EOK HFi Hi NDF O junk.
  unfold relay_remove_tr. rewrite (proj2 (Z.ltb_ge FD 0) rm_FDnn). rewrite (rm_find_nth FD es i NDF Hi HFi).
  reflexivity.
Qed.

Lemma rm_final_intro : forall L' A' regs' mem' md' (OUT' CAP' : Z) (junk' LB : list byte) (e1 : rentry) (h1 : hsrc)
    (tail' : list byte),
  rk_chain Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0 L' A' mem' md' ->
  regs_preserved regs0 regs' ->
  st_init_done A' = true -> RT L' A' (keys_total (re_keys e1)) OUT' CAP' h1 -> ro_agree segs mem' ->
  rw_cells segs mem' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  bytes_at segs mem' G_WAKE1 (le4 (Z_to_bv 64 (-1))) ->
  rw_cells segs mem' G_SRC [C8 (Z_to_bv 64 G)] -> In (G, SRC_TABLE) (blocks L' A') ->
  rw_cells segs mem' G_CLIENT [C4 (Z_to_bv 64 cl)] ->
  (exists ev', rw_cells segs mem' ERR [C4 ev']) ->
  rw_cells segs mem' G_NSRC [C4 (Z_to_bv 64 (N - 1)); C4 (Z_to_bv 64 16)] ->
  table_at Bm mem' G (remove_at i es) tail' ->
  (re_eof e = 0 -> DF L' A' mem' h1 (re_keys e1)) -> (re_eof e = 1 -> map fst (re_keys e1) = map fst (re_keys e)) ->
  bzs LB = with_nul Lsi ->
  rw_cells segs mem' G_BROKEN [C1 (Z_to_bv 8 (if send_off cl br (TD + keys_total (re_keys e1)) then br else dd))] ->
  rw_cells segs mem' G_EINTR [C1 (Z_to_bv 8 (if send_off cl br (TD + keys_total (re_keys e1)) then ei else 0))] ->
  BF L' A' OUT' e1 h1 [] -> (re_eof e = 0 -> NoDup (OUT' :: hs_blocks h1)) ->
  LF L' A' mem' OUT' CAP' junk' LB (re_keys e1) ->
  Final (mkCfg (YK11.mkst regs' (getr regs0 1) mem' (seg_rom segs)) md').
Proof using EOK HFi Hi NDF.
  intros L' A' regs' mem' md' OUT' CAP' junk' LB e1 h1 tail' CH RP INI RS RA LK WK SR1 GI CL ER NS TB DFH K1 LBH
    BRK EIN (B1 & B2 & B3) NDO (LF0 & LF1).
  assert (E01 : re_eof e = 0 \/ re_eof e = 1)
    by (destruct (proj1 (Forall_forall _ _) EOK e rm_e_in) as (X & _); exact X).
  assert (KFE : map fst (if re_eof e =? 0 then re_keys e1 else re_keys e) = map fst (re_keys e1)).
  { destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0]; [reflexivity|]. symmetry. apply K1. lia. }
  destruct (rma_keys_fst _ _ KFE) as (KTE & KOE & _).
  exists L', A', regs', mem', md', OUT', CAP', junk', LB,
    (rk_with_keys e (if re_eof e =? 0 then re_keys e1 else re_keys e)), h1, tail'.
  split; [reflexivity|].
  split; [cbn [rk_with_keys re_keys]; rewrite KTE; exact (rk_chain_post Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ CH RP)|].
  split; [exact INI|].
  split.
  { destruct RS as (qs & QL & RO & LO & LS). exists qs. split; [exact QL|]. split; [exact RO|].
    intros i' Hi' HF'. pose proof (rm_i_uniq i' Hi' HF') as ->. cbv zeta. cbn [rk_with_keys re_keys].
    rewrite KTE. split; [exact LO | exact LS]. }
  do 7 (split; [assumption|]).
  split.
  { intros NF. exfalso. exact (NF e rm_e_in HFi). }
  intros i' Hi' HF'. pose proof (rm_i_uniq i' Hi' HF') as ->. cbv zeta.
  cbn [rk_with_keys re_keys re_fd re_eof].
  rewrite KTE, KOE.
  unfold TD, Lsi, Lsf in *. fold finI.
  split; [exact NS|]. split; [exact TB|]. split; [reflexivity|]. split; [reflexivity|].
  split.
  { intros E0.
    replace (if re_eof e =? 0 then re_keys e1 else re_keys e) with (re_keys e1)
      by (rewrite (proj2 (Z.eqb_eq _ _) E0); reflexivity).
    destruct (DFH E0)
      as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16).
    repeat (split; [assumption|]). exact D16. }
  split; [intros E1; rewrite E1; reflexivity|]. split; [exact LBH|]. split; [exact BRK|]. split; [exact EIN|].
  unfold hbi, hbo in *.
  split.
  { intros q m Hq HO HE HH. apply (B1 q m Hq HO HE).
    destruct (re_eof e =? 0) eqn:E0; [apply HH; apply Z.eqb_eq; exact E0 | intros []]. }
  split.
  { intros q m Hq Hm HO HE HH.
    assert (HH' : ~ In q (if re_eof e =? 0 then hs_blocks h else [])).
    { destruct (re_eof e =? 0) eqn:E0; [apply HH; apply Z.eqb_eq; exact E0 | intros []]. }
    destruct (B3 q m Hq Hm HO HE HH') as (X1 & _ & X3). split; [exact X1|].
    intros E0. rewrite (proj2 (Z.eqb_eq _ _) E0) in X3. exact X3. }
  split; [exact NDO|].
  split.
  { intros q m Hq. destruct (B2 q m Hq) as [(X1 & XO & X2 & X3)|[X|X]].
    - left. split; [exact X1|]. split; [exact XO|]. split; [exact X2|].
      intros E0 Y. apply X3. rewrite (proj2 (Z.eqb_eq _ _) E0). exact Y.
    - right. left. cbn [app] in X. destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0]; [split; assumption | destruct X].
    - right. right. exact X. }
  split; [exact LF0 | exact LF1].
Qed.

Lemma rm_in_firstn : forall {X : Type} n (l : list X) x, In x (firstn n l) -> In x l.
Proof using. intros X n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

Lemma rm_in_skipn : forall {X : Type} n (l : list X) x, In x (skipn n l) -> In x l.
Proof using. intros X n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H. Qed.

Lemma rm_nd_hd : forall (a : Z) l, NoDup (a :: l) -> ~ In a l.
Proof using. intros a l H. apply rma_nodup_std in H. apply List.NoDup_cons_iff in H. exact (proj1 H). Qed.

Lemma rm_elen : forall e0, In e0 es -> length (entry_bytes e0) = 56%nat.
Proof using EOK.
  intros e0 H. pose proof (proj1 (Forall_forall _ _) EOK e0 H) as (_ & _ & P1 & P2 & _).
  exact (rma_entry_len e0 P1 P2).
Qed.

Lemma rm_catlen : forall l, (forall x, In x l -> In x es) -> length (concat (map entry_bytes l)) = (56 * length l)%nat.
Proof using EOK. intros l H. apply rma_concat_len. apply Forall_forall. intros x Hx. exact (rm_elen x (H x Hx)). Qed.

Lemma rm_tlen : Z.of_nat (length Tpre) = 56 * Z.of_nat i /\ Z.of_nat (length Tpost) = 840 - 56 * Z.of_nat i.
Proof using EOK Hi O TAB junk.
  destruct TAB as [TL _]. unfold Tpre, Tpost. rewrite length_app.
  rewrite (rm_catlen (firstn i es)) by (intros x Hx; exact (rm_in_firstn _ _ _ Hx)).
  rewrite (rm_catlen (skipn (S i) es)) by (intros x Hx; exact (rm_in_skipn _ _ _ Hx)).
  rewrite length_firstn, length_skipn. lia.
Qed.

Lemma rm_tsplit : forall m X, length X = 56%nat -> rw_cells rsegs m G [CB 896 (Tpre ++ X ++ Tpost)] ->
  rw_cells rsegs m G [CB (length Tpre) Tpre] /\ rw_cells rsegs m SA [CB 56 X] /\
  rw_cells rsegs m (SA + 56) [CB (length Tpost) Tpost].
Proof using EOK Hi O TAB junk.
  intros m X LX H. pose proof rm_tlen as (T1 & T2).
  assert (H' : rw_cells rsegs m G ([CB (length Tpre) Tpre] ++ [CB 56 X] ++ [CB (length Tpost) Tpost])).
  { eapply rm_rw_conv; [exact H | cbn [cells_wf cell_wf app]; repeat split; auto |
      cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity |
      cbn [cells_size csize app]; lia]. }
  apply rm_cells_cut in H' as [H1 H2]. apply rm_cells_cut in H2 as [H2 H3].
  cbn [cells_size csize] in H2, H3.
  split; [exact H1|]. split.
  - replace (G + 56 * Z.of_nat i) with (G + Z.of_nat (length Tpre + 0)) by lia. exact H2.
  - replace (G + 56 * Z.of_nat i + 56) with (G + Z.of_nat (length Tpre + 0) + Z.of_nat (56 + 0)) by lia. exact H3.
Qed.

Lemma rm_tjoin3 : forall m (Y X Z0 : list byte), length X = 56%nat -> (length Y + 56 + length Z0 = 896)%nat ->
  rw_cells rsegs m G [CB (length Y) Y] -> rw_cells rsegs m (G + Z.of_nat (length Y)) [CB 56 X] ->
  rw_cells rsegs m (G + Z.of_nat (length Y) + 56) [CB (length Z0) Z0] ->
  rw_cells rsegs m G [CB 896 (Y ++ X ++ Z0)].
Proof using Bm Hi O junk.
  intros m Y X Z0 LX LT H1 H2 H3.
  assert (H23 : rw_cells rsegs m (G + Z.of_nat (length Y)) ([CB 56 X] ++ [CB (length Z0) Z0])).
  { apply (rm_cells_join m _ (G + Z.of_nat (length Y) + 56)); [exact H2 | exact H3 | cbn [cells_size csize]; lia]. }
  assert (H123 : rw_cells rsegs m G ([CB (length Y) Y] ++ [CB 56 X] ++ [CB (length Z0) Z0])).
  { apply (rm_cells_join m _ (G + Z.of_nat (length Y))); [exact H1 | exact H23 | cbn [cells_size csize]; lia]. }
  eapply rm_rw_conv; [exact H123 | cbn [cells_wf cell_wf app]; rewrite !length_app; repeat split; lia |
    cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity |
    cbn [cells_size csize app]; lia].
Qed.

(* Intervals a run writes outside the allocator's blocks, or inside the table's block. *)
Definition IvOk (W : list (Z * Z)) : Prop :=
  Forall (fun iv => alloc_ceiling <= fst iv \/ (forall x, fst iv <= x < snd iv -> in_img Bm x) \/
                    (G <= fst iv /\ snd iv <= G + SRC_TABLE)) W.

Lemma rm_iv_blk : forall L A m md W q k x, MR L A m md -> In (G, SRC_TABLE) (blocks L A) -> IvOk W ->
  In (q, k) (blocks L A) -> q <> G -> q <= x < q + k -> outside W x.
Proof using AX Hi O junk.
  intros L A m md W q k x HM HG HW Hq Hne Hx.
  destruct (block_facts Bm MR (aa_laws API) L A m md q k (x - q) HM Hq ltac:(lia)) as (_ & Q1 & Q2 & _).
  assert (NI : ~ in_img Bm x).
  { apply rk_blocks_in in Hq as (p & Ep & Hp). subst q. replace x with (ptr_addr L p + (x - ptr_addr L p)) by lia.
    exact (ax_blocks_img AX L A m md p k (x - ptr_addr L p) HM Hp ltac:(lia)). }
  pose proof (blocks_disjoint Bm API L A m md q k G SRC_TABLE HM Hq HG Hne) as D.
  unfold SRC_TABLE, SRC_ENTRY in *.
  induction HW as [|[lo hi] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
  cbn [fst snd] in Hiv. destruct Hiv as [H|[H|H]].
  - lia.
  - destruct (Z_lt_le_dec x lo) as [L1|L1]; [lia|]. destruct (Z_lt_le_dec x hi) as [L2|L2]; [|lia].
    exfalso. exact (NI (H x ltac:(lia))).
  - unfold SRC_TABLE, SRC_ENTRY in H. lia.
Qed.

Lemma rm_DF_kept : forall L A m L' A' m' h1 ks, (j < 4)%nat -> DF L A m h1 ks ->
  (forall a, G_S <= a < G_S + 384 -> rk_kb2 Bm m m' a) ->
  (forall q, In q (hs_blocks h1) -> rk_bkept Bm L A m L' A' m' q) -> DF L' A' m' h1 ks.
Proof using Hi O junk.
  intros L A m L' A' m' h1 ks Hj (D1 & D2 & D3) K B.
  split.
  { apply (rk_src_at_kept Bm L A m L' A' m' HA h1 D1); [|exact B].
    intros k Hk. apply K. unfold G_S, SRC_SIZE in *. lia. }
  split; [|exact D3].
  destruct D2 as (F1 & F2 & F3). split; [exact F1|]. split; [exact F2|].
  intros k Hk Hkj. destruct (F3 k Hk Hkj) as (C & X). split; [|exact X].
  apply (rk_rw_kb2 Bm m); [exact C|]. intros q Hq. cbn [cells_size csize] in Hq. apply K.
  unfold G_S, SRC_SIZE in *. lia.
Qed.

Lemma rm_rf : forall R, RFr R ->
  getr R 2 = Z_to_bv 64 (SP - 48) /\ getr R 8 = Z_to_bv 64 203000 /\ getr R 9 = Z_to_bv 64 FD /\
  getr R 18 = Z_to_bv 64 202912 /\ getr R 19 = Z_to_bv 64 (56 * Z.of_nat i) /\
  (forall r, callee_saved r -> r <> 2 -> r <> 8 -> r <> 9 -> r <> 18 -> r <> 19 ->
     getr R (Z_to_bv 5 r) = getr regs0 (Z_to_bv 5 r)).
Proof using Bm Hi O junk.
  intros R H.
  split; [exact (H 2 ltac:(unfold callee_saved; lia))|].
  split; [exact (H 8 ltac:(unfold callee_saved; lia))|].
  split; [exact (H 9 ltac:(unfold callee_saved; lia))|].
  split; [exact (H 18 ltac:(unfold callee_saved; lia))|].
  split; [exact (H 19 ltac:(unfold callee_saved; lia))|].
  intros r Hr N2 N8 N9 N18 N19. rewrite (H r Hr). unfold rval.
  rewrite (proj2 (Z.eqb_neq r 2) N2), (proj2 (Z.eqb_neq r 8) N8), (proj2 (Z.eqb_neq r 9) N9),
    (proj2 (Z.eqb_neq r 18) N18), (proj2 (Z.eqb_neq r 19) N19). reflexivity.
Qed.

Lemma rm_G_safe : G <> OUT /\ ~ In G (entry_blocks e) /\ ~ In G hbi.
Proof using HFi Hi NDB SRCP.
  pose proof (rm_nd_hd _ _ NDB) as N1. cbn [In] in N1.
  split; [intros E; apply N1; left; symmetry; exact E|].
  assert (N2 : ~ In G (concat (map entry_blocks es))) by (intros X; apply N1; right; exact X).
  split.
  { intros X. apply N2. apply in_concat. exists (entry_blocks e). split; [apply in_map; exact rm_e_in | exact X]. }
  unfold hbi. destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0]; [|intros []].
  destruct (SRCP e rm_e_in HFi E0) as (_ & _ & _ & _ & _ & _ & ND & _).
  pose proof (rm_nd_hd _ _ ND) as N3. intros X. apply N3. right. apply in_or_app. right. exact X.
Qed.

(* After free (s->buf), at 0x14014. *)
Definition AtT (c : config) : Prop :=
  exists L3 A3 R3 m3 md3 (e1 : rentry) (h1 : hsrc) (OUT2 CAP2 : Z) (junk2 LB X : list byte),
    c = mkCfg (YK11.mkst R3 (Z_to_bv 64 0x14014) m3 (seg_rom segs)) md3 /\
    RFr R3 /\
    rk_chain Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0 L3 A3 m3 md3 /\
    st_init_done A3 = true /\ ro_agree segs m3 /\ RT L3 A3 (keys_total (re_keys e1)) OUT2 CAP2 h1 /\
    FRM m3 /\
    GLB m3 (if send_off cl br (TD + keys_total (re_keys e1)) then br else dd)
      (if send_off cl br (TD + keys_total (re_keys e1)) then ei else 0) /\
    length X = 56%nat /\ rw_cells segs m3 G [CB 896 (Tpre ++ X ++ Tpost)] /\ In (G, SRC_TABLE) (blocks L3 A3) /\
    (re_eof e = 0 -> DF L3 A3 m3 h1 (re_keys e1) /\ ~ In G (hs_blocks h1)) /\
    (re_eof e = 1 -> map fst (re_keys e1) = map fst (re_keys e)) /\
    bzs LB = with_nul Lsi /\ BF L3 A3 OUT2 e1 h1 [] /\ (re_eof e = 0 -> NoDup (OUT2 :: hs_blocks h1)) /\
    LF L3 A3 m3 OUT2 CAP2 junk2 LB (re_keys e1).

Lemma rm_split_last : forall {X : Type} (l : list X) (d : X), (0 < length l)%nat ->
  l = firstn (length l - 1) l ++ [nth (length l - 1) l d].
Proof using Bm Hi O junk.
  intros X l d. induction l as [|a l IH]; intros H; cbn [length] in H; [lia|].
  destruct l as [|b l]; [reflexivity|].
  cbn [length] in IH |- *. specialize (IH ltac:(lia)).
  replace (S (S (length l)) - 1)%nat with (S (S (length l) - 1)) by lia.
  cbn [firstn nth app]. f_equal. exact IH.
Qed.

(* The table after the memcpy (s = last entry) of relay.c:466: entry N-1 moved into slot i. *)
Lemma rm_tbl_after : forall m X src,
  length X = 56%nat ->
  ((S i < length es)%nat /\ src = entry_bytes (nth (length (skipn (S i) es) - 1) (skipn (S i) es) no_entry)) \/
  (S i = length es /\ src = X) ->
  rw_cells rsegs m G [CB (length Tpre) Tpre] -> rw_cells rsegs m SA [CB 56 src] ->
  rw_cells rsegs m (SA + 56) [CB (length Tpost) Tpost] ->
  exists tail', table_at Bm m G (remove_at i es) tail'.
Proof using EOK Hi O SEGS TAB junk.
  intros m X src LX HS T1 T2 T3. pose proof rm_tlen as (L1 & L2).
  assert (LTP : length (firstn i es) = i) by (rewrite length_firstn; lia).
  pose proof (rma_split_nth es no_entry i Hi) as ES.
  destruct TAB as [TL _].
  destruct HS as [(HS & ->) | (HS & ->)].
  - set (l := skipn (S i) es) in *.
    assert (Ll : length l = (length es - S i)%nat) by (unfold l; rewrite length_skipn; reflexivity).
    set (z := nth (length l - 1) l no_entry).
    set (mid := firstn (length l - 1) l).
    assert (El : l = mid ++ [z]) by (apply rm_split_last; lia).
    assert (ZIN : In z es) by (apply (rm_in_skipn (S i)); fold l; rewrite El; apply in_or_app; right; left; reflexivity).
    assert (MIN : forall x, In x mid -> In x es)
      by (intros x Hx; apply (rm_in_skipn (S i)); fold l; rewrite El; apply in_or_app; left; exact Hx).
    assert (RA : remove_at i es = firstn i es ++ z :: mid).
    { rewrite ES at 1. fold l. rewrite El. rewrite <- LTP at 1. apply rma_remove_at_mid. }
    assert (LM : length mid = (length l - 1)%nat) by (unfold mid; rewrite length_firstn; lia).
    assert (LCM : length (concat (map entry_bytes mid)) = (56 * length mid)%nat) by exact (rm_catlen mid MIN).
    pose proof (rm_elen z ZIN) as LZ.
    exists (entry_bytes z ++ tail). unfold table_at. rewrite SEGS. rewrite RA.
    rewrite !length_app. cbn [length].
    split; [lia|].
    rewrite map_app, concat_app. cbn [map concat]. rewrite <- !app_assoc.
    fold Tpre.
    assert (TP : Tpost = concat (map entry_bytes mid) ++ entry_bytes z ++ tail).
    { unfold Tpost. fold l. rewrite El, map_app, concat_app. cbn [map concat]. rewrite app_nil_r, <- app_assoc.
      reflexivity. }
    rewrite TP in T3.
    apply rm_tjoin3; [exact LZ | rewrite !length_app; lia | exact T1 |
      replace (G + Z.of_nat (length Tpre)) with SA by lia; exact T2 |].
    replace (G + Z.of_nat (length Tpre) + 56) with (SA + 56) by lia. exact T3.
  - assert (LS : skipn (S i) es = []) by (apply skipn_all2; lia).
    assert (ES' : es = firstn i es ++ [e]) by (rewrite ES at 1; rewrite LS; reflexivity).
    assert (RA : remove_at i es = firstn i es) by (rewrite ES' at 1; rewrite <- LTP at 1; apply rma_remove_at_last).
    assert (TP : Tpost = tail) by (unfold Tpost; rewrite LS; reflexivity).
    exists (X ++ tail). unfold table_at. rewrite SEGS, RA. rewrite length_app, LTP.
    split; [lia|]. fold Tpre. rewrite <- TP.
    apply rm_tjoin3; [exact LX | lia | exact T1 | replace (G + Z.of_nat (length Tpre)) with SA by lia; exact T2 |].
    replace (G + Z.of_nat (length Tpre) + 56) with (SA + 56) by lia. exact T3.
Qed.

(* The last entry's bytes, read by the memcpy of relay.c:466 when i < N - 1. *)
Lemma rm_src_bytes : forall m, (S i < length es)%nat ->
  rw_cells rsegs m (SA + 56) [CB (length Tpost) Tpost] ->
  let l := skipn (S i) es in
  let z := nth (length l - 1) l no_entry in
  bytes_at rsegs m (G + 56 * (N - 1)) (entry_bytes z) /\ length (entry_bytes z) = 56%nat.
Proof.
  intros m HS T3 l z.
  assert (Ll : length l = (length es - S i)%nat) by (unfold l; rewrite length_skipn; reflexivity).
  set (mid := firstn (length l - 1) l).
  assert (El : l = mid ++ [z]) by (apply rm_split_last; lia).
  assert (ZIN : In z es) by (apply (rm_in_skipn (S i)); fold l; rewrite El; apply in_or_app; right; left; reflexivity).
  assert (MIN : forall x, In x mid -> In x es)
    by (intros x Hx; apply (rm_in_skipn (S i)); fold l; rewrite El; apply in_or_app; left; exact Hx).
  assert (LM : length mid = (length l - 1)%nat) by (unfold mid; rewrite length_firstn; lia).
  pose proof (rm_catlen mid MIN) as LCM.
  assert (TP : Tpost = concat (map entry_bytes mid) ++ entry_bytes z ++ tail).
  { unfold Tpost. fold l. rewrite El, map_app, concat_app. cbn [map concat]. rewrite app_nil_r, <- app_assoc.
    reflexivity. }
  pose proof (rm_rw_bytes _ _ _ _ T3) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r, TP in B.
  apply bytes_at_app in B as [_ B]. apply bytes_at_app in B as [B _].
  split; [|exact (rm_elen z ZIN)].
  replace (G + 56 * (N - 1)) with (SA + 56 + Z.of_nat (length (concat (map entry_bytes mid)))) by lia. exact B.
Qed.

Lemma rm_W4_img : forall x, 0 <= x < 2 ^ 21 -> 2 ^ 46 <= alloc_ceiling -> alloc_ceiling + 8560 <= SP ->
  (x < G \/ G + 896 <= x) -> (x < 202936 \/ 202940 <= x) -> (x < 203004 \/ 203008 <= x) -> (i < 16)%nat ->
  outside [(SA, SA + 56); (202936, 202940); (SP - 48 - 96, SP - 48 + 48); (203004, 203008)] x.
Proof using Bm HN4 Hi O junk. intros x Hx AC HC HG HN HL Hi16. cbn [outside]. repeat split; lia. Qed.

Lemma rm_W4_ok : 4096 <= G -> G + 896 <= alloc_ceiling -> alloc_ceiling + 8560 <= SP -> (i < 16)%nat ->
  IvOk [(SA, SA + 56); (202936, 202940); (SP - 48 - 96, SP - 48 + 48); (203004, 203008)].
Proof using HN4 Hi IMR O PRE junk.
  intros G1 G2 HC Hi16. pose proof rm_pre as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & AC).
  constructor; [right; right; cbn [fst snd]; unfold SRC_TABLE, SRC_ENTRY; lia|].
  constructor; [right; left; cbn [fst snd]; intros x Hx;
    apply (proj1 (IMR x ltac:(unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia)))|].
  constructor; [left; cbn [fst snd]; lia|].
  constructor; [right; left; cbn [fst snd]; intros x Hx;
    apply (proj1 (IMR x ltac:(unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia)))|].
  constructor.
Qed.

Lemma rm_tail : forall c, AtT c -> SR segs c Final.
Proof using AX EHI EOK GFR GIN HERR4 HFi HN4 Hi IME IML IMR MCP MCS NDB NDF OUTD PRE SEGS SPU SRCP SWK TAB.
  intros c (L3 & A3 & R3 & m3 & md3 & e1 & h1 & OUT2 & CAP2 & junk2 & LB & X & -> & RF3 & CH & INI & RA3 & RS3 &
    (jf & FR3) & GL3 & LX & TB3 & GI3 & DF3 & K13 & LB3 & BF3 & ND3 & LF3).
  pose proof rm_pre as (HM0 & HW0 & HB0 & HRA & HAL & HCE & H63 & HWS & HTP & HER & Hh & Hl & AC).
  pose proof rm_sf as (E1 & E2 & G1 & G2 & G3 & G4 & G5 & G6).
  destruct (rm_rf R3 RF3) as (R2 & R8 & R9 & R18 & R19 & RO).
  pose proof CH as (M3 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW3).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M3) as (Hh3 & Hl3 & _).
  destruct GL3 as (LK3 & WK3 & NS3 & SR3 & CL3 & BR3 & DD3 & EI3 & ER3).
  pose proof rm_G_safe as (GO & GE & GH).
  assert (GB3 : G <> OUT2 /\ ~ In G (entry_blocks e1) /\ ~ In G (hbo h1)).
  { destruct BF3 as (_ & _ & B3). apply (B3 G SRC_TABLE GIN); [unfold SRC_TABLE, SRC_ENTRY; lia | exact GO | exact GE | exact GH]. }
  assert (Hi16 : (i < 16)%nat) by lia.
  assert (US : bv_unsigned (Z_to_bv 64 (SP - 48)) = SP - 48) by (apply unsigned_lit; lia).
  rewrite SEGS in RA3, FR3, TB3, LK3, WK3, NS3, SR3, CL3, BR3, DD3, EI3, ER3, SW3.
  assert (STK : stk rsegs m3 (SP - 8560) (SP - 48)).
  { split; [lia|]. split; [lia|]. intros a Ha. apply rm_wr_hi; [lia|]. apply SW3. unfold scratch_k, spZ.
    rewrite (proj1 rm_K). left. lia. }
  destruct (rm_cells_cut m3 G_NSRC [C4 _] [C4 _] NS3) as [NS3a NS3b].
  destruct (rm_tsplit m3 X LX TB3) as (T1 & T2 & T3).
  assert (ROB : forall k, 0 <= k < 896 -> ro_addr rsegs (Z_to_bv 64 (G + k)) = false).
  { intros k Hk. apply (ro_addr_out Bm SEGS); [lia|]. destruct GFR as (_ & _ & GF). apply GF.
    unfold SRC_TABLE, SRC_ENTRY. lia. }
  set (W4 := [(SA, SA + 56); (202936, 202940); (SP - 48 - 96, SP - 48 + 48); (203004, 203008)]).
  assert (HSRC : exists src, length src = 56%nat /\
     ((Z.of_nat i < N - 1 /\ bytes_at rsegs (normalize rsegs m3) (G + 56 * (N - 1)) src /\
       rw_cells rsegs (normalize rsegs m3) (G + 56 * Z.of_nat i) [CB 56 X]) \/
      (Z.of_nat i = N - 1 /\ rw_cells rsegs (normalize rsegs m3) (G + 56 * Z.of_nat i) [CB 56 src])) /\
     (((S i < length es)%nat /\ src = entry_bytes (nth (length (skipn (S i) es) - 1) (skipn (S i) es) no_entry)) \/
      (S i = length es /\ src = X))).
  { assert (T2n : rw_cells rsegs (normalize rsegs m3) (G + 56 * Z.of_nat i) [CB 56 X]).
    { apply rw_cells_normalize; [exact RA3 | exact T2 |]. intros k Hk. cbn [cells_size csize] in Hk.
      replace (G + 56 * Z.of_nat i + k) with (G + (56 * Z.of_nat i + k)) by lia. apply ROB. lia. }
    destruct (Nat.lt_ge_cases (S i) (length es)) as [LT|GEL].
    - destruct (rm_src_bytes m3 LT T3) as [SB SL]. cbv zeta in SB, SL.
      eexists. split; [exact SL|].
      split; [left; split; [lia|]; split; [apply bytes_at_normalize; [exact RA3 | exact SB] | exact T2n]|].
      left. split; [exact LT | reflexivity].
    - exists X. split; [exact LX|]. split; [right; split; [lia | exact T2n]|]. right. split; [lia | reflexivity]. }
  destruct HSRC as (src & LS & HC & HSC).
  rewrite SEGS. eapply rm_bridge; [exact RA3 | exact Hh3 | exact Hl3 | | | ].
  { rewrite rm_mkR_of, R2, R8, R18, R19.
    eapply (rm_tail2 MCP MCS SPU SWK) with (lo := SP - 8560) (G := G) (N := N) (i := i) (src := src) (dj := X) (jf := jf).
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - lia.
    - apply rw_cells_normalize; [exact RA3 | exact NS3a |]. intros k Hk. cbn [cells_size csize] in Hk.
      apply rm_ro_glob. unfold G_NSRC. lia.
    - apply bytes_at_normalize; [exact RA3|]. pose proof (rm_rw_bytes _ _ _ _ SR3) as B. cbn [cells_bytes cbytes] in B.
      rewrite app_nil_r in B. exact B.
    - exact LS.
    - exact HC.
    - rewrite US. apply rw_cells_normalize; [exact RA3 | exact FR3 |]. intros k Hk. cbn [cells_size csize] in Hk.
      apply ro_addr_hi. lia.
    - apply rw_cells_normalize; [exact RA3 | exact LK3 |]. intros k Hk. cbn [cells_size csize] in Hk.
      apply rm_ro_glob. unfold G_LOCK. lia.
    - apply bytes_at_normalize; [exact RA3 | exact WK3].
    - rewrite US. apply stk_normalize; [exact STK | lia].
    - rewrite US. lia.
    - lia.
    - rewrite US. lia.
    - apply mem_inv_normalize. }
  2: { intros s0 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & _).
       do 3 eexists. reflexivity. }
  intros R0 pc0 m0 R' m4 HQ X4 MR4 RS4.
  destruct HQ as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & EQ & MU
    & WM & NS4 & SL4 & LK4).
  injection EQ as ER0 Epc Em. subst R0 pc0 m0.
  rewrite US in MU. fold W4 in MU.
  destruct (rm_back m3 m' m4 W4 RA3 MR4 RS4 MU WM) as (MU' & WM' & RA4).
  replace (ret_pc (getr regs0 1)) with (getr regs0 1) by (symmetry; apply ret_pc_of_ok; exact HRA).
  replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  assert (OK4 : IvOk W4) by (apply rm_W4_ok; lia).
  assert (IMG4 : forall x, 0 <= x < 2 ^ 21 -> (x < G \/ G + 896 <= x) -> (x < 202936 \/ 202940 <= x) ->
                  (x < 203004 \/ 203008 <= x) -> outside W4 x) by (intros; apply rm_W4_img; lia).
  assert (BLK4 : forall q k x, In (q, k) (blocks L3 A3) -> q <> G -> q <= x < q + k -> outside W4 x)
    by (intros q k x Hq Hne Hx; exact (rm_iv_blk L3 A3 m3 md3 W4 q k x M3 GI3 OK4 Hq Hne Hx)).
  assert (TC : forall A cs, rw_cells rsegs m3 A cs -> (forall k, 0 <= k < Z.of_nat (cells_size cs) -> outside W4 (A + k)) ->
                 rw_cells rsegs m4 A cs) by (intros A cs H HO; exact (rm_mu_cells W4 m3 m4 A cs H MU' WM' HO)).
  assert (TB : forall A bs, bytes_at rsegs m3 A bs -> (forall k, 0 <= k < Z.of_nat (length bs) -> outside W4 (A + k)) ->
                 bytes_at rsegs m4 A bs) by (intros A bs H HO; exact (rm_mu_bytes W4 m3 m4 A bs H MU' HO)).
  rm_hide. unfold RmOr in G4, G5, G6.
  destruct (rm_tbl_after m4 X src LX HSC) as (tail' & TB4).
  { apply TC; [exact T1|]. intros k Hk. cbn [cells_size csize] in Hk. pose proof rm_tlen as (TL1 & _).
    cbn [outside W4]. repeat split; lia. }
  { exact (rw_cells_of_rel rsegs m4 m' _ _ MR4 SL4). }
  { apply TC; [exact T3|]. intros k Hk. cbn [cells_size csize] in Hk. pose proof rm_tlen as (_ & TL2).
    cbn [outside W4]. repeat split; lia. }
  apply SR_ret. apply (rm_final_intro L3 A3 R' m4 md3 OUT2 CAP2 junk2 LB e1 h1 tail').
  - eapply (rk_chain_munch Bm API AX SEGS); [exact CH | exact MU' | rewrite SEGS; exact WM' |].
    intros x Hx NO. destruct (rm_not_out _ _ NO) as (lo & hi & Hin & Hr). unfold W4 in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as <- <-.
    + right. split; [unfold Efin; right; right; right; left; unfold SRC_TABLE, SRC_ENTRY; lia|].
      right. exists G, SRC_TABLE. split; [exact GI3 | unfold SRC_TABLE, SRC_ENTRY; lia].
    + right. split; [unfold Efin; right; right; left; unfold G_NSRC; lia|].
      left. apply IMR. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX. lia.
    + left. split; [unfold scratch_k, spZ; rewrite (proj1 rm_K); left; lia | lia].
    + right. split; [unfold Efin; right; left; unfold G_LOCK; lia|].
      left. apply IMR. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX. lia.
  - intros r Hr. unfold callee_saved in Hr.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]]]; subst r;
      match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X4 eq_refl) end; simp_regs.
    + rewrite US. replace (SP - 48 + 48) with SP by lia. apply Z_to_bv_bv_unsigned.
    + exact (RO 3 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (RO 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exact (RO 20 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (RO 21 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (RO 22 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (RO 23 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (RO 24 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (RO 25 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (RO 26 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact (RO 27 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
  - exact INI.
  - exact RS3.
  - rewrite SEGS. exact RA4.
  - rewrite SEGS. exact (rw_cells_of_rel rsegs m4 m' _ _ MR4 LK4).
  - rewrite SEGS. apply TB; [exact WK3|]. intros k Hk. rewrite length_le4 in Hk. apply IMG4; unfold G_WAKE1; lia.
  - rewrite SEGS. apply TC; [exact SR3|]. intros k Hk. cbn [cells_size csize] in Hk. apply IMG4; unfold G_SRC; lia.
  - exact GI3.
  - rewrite SEGS. apply TC; [exact CL3|]. intros k Hk. cbn [cells_size csize] in Hk. apply IMG4; unfold G_CLIENT; lia.
  - destruct ER3 as (ev & ER3). exists ev. rewrite SEGS. apply TC; [exact ER3|]. intros k Hk.
    cbn [cells_size csize] in Hk. apply IMG4; lia.
  - rewrite SEGS. apply (rm_cells_join m4 G_NSRC (G_NSRC + 4) [C4 _] [C4 _]); [| | cbn [cells_size csize]; lia].
    + exact (rw_cells_of_rel rsegs m4 m' _ _ MR4 NS4).
    + apply TC; [exact NS3b|]. intros k Hk. cbn [cells_size csize] in Hk. apply IMG4; unfold G_NSRC; lia.
  - exact TB4.
  - intros E0. destruct (DF3 E0) as [D3 GHB].
    destruct (SRCP e rm_e_in HFi E0) as (_ & _ & Hj & _).
    apply (rm_DF_kept L3 A3 m3 L3 A3 m4 h1 (re_keys e1) Hj D3).
    + intros a Ha. unfold G_S in Ha. apply (rk_mu_kb2 Bm W4 m3 m4 a MU'); [rewrite SEGS; exact WM' | lia |].
      apply IMG4; lia.
    + intros q Hq. apply (rk_mu_bkept Bm API L3 A3 W4 m3 m4 md3 q M3 MU'); [rewrite SEGS; exact WM'|].
      intros k x Hqk Hx. apply (BLK4 q k (q + x) Hqk); [intros ->; exact (GHB Hq) | lia].
  - exact K13.
  - exact LB3.
  - rewrite SEGS. apply TC; [exact BR3|]. intros k Hk. cbn [cells_size csize] in Hk. apply IMG4; unfold G_BROKEN; lia.
  - rewrite SEGS. apply TC; [exact EI3|]. intros k Hk. cbn [cells_size csize] in Hk. apply IMG4; unfold G_EINTR; lia.
  - exact BF3.
  - exact ND3.
  - destruct LF3 as (LF0 & LF1). split.
    + intros LV. destruct (LF0 LV) as (OV & OB & OE). rewrite SEGS in OV, OB |- *.
      split; [apply TC; [exact OV|]; intros k Hk; cbn [cells_size csize] in Hk; apply IMG4; unfold G_OUTV; lia|].
      split; [|exact OE]. intros CP. destruct (OB CP) as (OI & OBy). split; [exact OI|].
      apply TB; [exact OBy|]. intros k Hk. rewrite length_app in Hk.
      destruct OUTD as [(C0 & _)|(_ & _ & _ & _ & _ & LO & LJ)]; [lia|].
      apply (BLK4 OUT CAP); [exact OI | intros E; apply GO; symmetry; exact E | lia].
    + intros LV. destruct (LF1 LV) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). rewrite SEGS in Q5, Q7 |- *.
      split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|]. split; [exact Q4|].
      assert (LLB : Z.of_nat (length LB) = TD) by (unfold TD; rewrite <- LB3; unfold bzs; rewrite length_map; reflexivity).
      pose proof (rma_keys_total_nonneg (re_keys e1)) as KTN.
      pose proof (rm_ko_len (re_keys e1)) as LKO.
      assert (LO0 : Z.of_nat (length O) = NO) by (destruct OUTD as [(_ & _ & N0 & OE)|(_ & _ & _ & _ & _ & LO & _)];
        [rewrite OE; cbn [length]; lia | exact LO]).
      split; [apply TB; [exact Q5|]; intros k Hk; apply (BLK4 OUT2 CAP2);
              [exact Q3 | intros E; apply (proj1 GB3); symmetry; exact E |];
              rewrite !length_app in Hk; lia|].
      split; [exact Q6|]. apply TC; [exact Q7|]. intros k Hk. cbn [cells_size csize] in Hk. apply IMG4; unfold G_OUTV; lia.
Qed.

Lemma rm_mid_in : forall (l b1 b2 : list (Z * Z)) x y, NoDup (map fst l) -> l = b1 ++ x :: b2 ->
  (In y (b1 ++ b2) <-> In y l /\ fst y <> fst x).
Proof using.
  intros l b1 b2 x y ND E. subst l. apply rma_nodup_std in ND. rewrite map_app in ND. cbn [map] in ND.
  apply List.NoDup_remove in ND as [ND NI]. rewrite <- map_app in NI.
  split.
  - intros H. split; [apply in_app_iff in H as [H|H]; apply in_app_iff; [left | right; right]; exact H|].
    intros E. apply NI. rewrite <- E. apply in_map. exact H.
  - intros [H NE]. apply in_app_iff in H as [H|[H|H]]; apply in_app_iff; [left; exact H | subst; contradiction | right; exact H].
Qed.

Lemma rm_ret_14014 : YK0s.ret_ok (Z_to_bv 64 0x14014).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rm_cp_cells : forall L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n A cs,
  MR L1 A1 m1 md1 -> In (p, n) (user_blocks A1) ->
  call_post Bm MR L1 A1 R1 m1 md1 (fun a => ptr_addr L1 p <= a < ptr_addr L1 p + n) L2 A2 R2 m2 md2 ->
  rw_cells segs m1 A cs ->
  (forall k, 0 <= k < Z.of_nat (cells_size cs) ->
     (img_plain Bm (A + k) \/ alloc_ceiling <= A + k < 2 ^ 64) /\ ~ scratch Bm R1 (A + k)) ->
  rw_cells segs m2 A cs.
Proof using AX.
  intros L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n A cs M1 HP CP H K.
  apply (rk_rw_kb2 Bm m1); [exact H|]. intros k Hk. destruct (K k Hk) as [K1 K2].
  exact (rk_cp_gkept Bm API AX L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 p n (A + k) M1 HP CP K1 K2).
Qed.

(* The resource state at free (s->buf): all the run's requests but the free made, which returned qs; s->buf the
   block the free names. *)
Definition RFz (L1 : layout) (A1 : astate) (e1 : rentry) (h1 : hsrc) (OUT1 CAP1 : Z) : Prop :=
  exists qs, length qs = nretF trR /\ rt_ok F A1 (runF F qs bnd (trD ++ trGM)) /\ ds_cap sDM = re_cap e1 /\
    (0 < re_cap e1 -> live_at L1 A1 (resolveF qs (da_buf a1M)) (re_buf e1) (re_cap e1)) /\
    (send_live cl br dd (TD + keys_total (re_keys e1)) = true -> live_at L1 A1 (resolveF qs outR) OUT1 CAP1) /\
    (re_eof e = 0 -> src_links L1 A1 qs nm0 a1M h1).

(* At free (s->buf), 0x15f4c, after gestures_end. *)
Definition AtF (c : config) : Prop :=
  exists L2 A2 R2 m2 md2 (e1 : rentry) (h1 : hsrc) (OUT2 CAP2 : Z) (junk2 LB X : list byte),
    c = mkCfg (YK11.mkst R2 (Z_to_bv 64 0x15f4c) m2 (seg_rom segs)) md2 /\
    RFr R2 /\ getr R2 1 = Z_to_bv 64 0x14014 /\ getr R2 10 = Z_to_bv 64 (re_buf e1) /\
    rk_chain Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0 L2 A2 m2 md2 /\
    st_init_done A2 = true /\ ro_agree segs m2 /\ RFz L2 A2 e1 h1 OUT2 CAP2 /\
    FRM m2 /\
    GLB m2 (if send_off cl br (TD + keys_total (re_keys e1)) then br else dd)
      (if send_off cl br (TD + keys_total (re_keys e1)) then ei else 0) /\
    length X = 56%nat /\ rw_cells segs m2 G [CB 896 (Tpre ++ X ++ Tpost)] /\ In (G, SRC_TABLE) (blocks L2 A2) /\
    (re_eof e = 0 -> DF L2 A2 m2 h1 (re_keys e1) /\ ~ In G (hs_blocks h1)) /\
    (re_eof e = 1 -> map fst (re_keys e1) = map fst (re_keys e)) /\
    bzs LB = with_nul Lsi /\ BF L2 A2 OUT2 e1 h1 (bufl e1) /\ (re_eof e = 0 -> NoDup (OUT2 :: hs_blocks h1)) /\
    LF L2 A2 m2 OUT2 CAP2 junk2 LB (re_keys e1) /\
    ((re_cap e1 = 0 /\ re_buf e1 = 0) \/
     (0 < re_cap e1 /\ In (re_buf e1, re_cap e1) (blocks L2 A2) /\ re_buf e1 <> G /\ re_buf e1 <> OUT2 /\
      (send_live cl br dd (TD + keys_total (re_keys e1)) = false -> re_buf e1 <> OUT) /\ ~ In (re_buf e1) (hbo h1))).

Lemma rm_free : forall c, AtF c -> SR segs c AtT.
Proof using AX CTX EHI EOK FNC FRC FREEPC GFR GIN HFi HND Hi IME IML IMR NDF OUTD PRE SEGS SRCP.
  intros c (L2 & A2 & R2 & m2 & md2 & e1 & h1 & OUT2 & CAP2 & junk2 & LB & X & -> & RF2 & RA2 & R10 & CH & INI &
    RO2 & RS2 & FR2 & GL2 & LX & TB2 & GI2 & DF2 & K12 & LB2 & BF2 & ND2 & LF2 & BUF).
  destruct RS2 as (qs & QL & RQ & CE & LBUF & LOq & LS).
  pose proof rm_pre as (HM0 & HW0 & HB0 & HRA & HAL & HCE & H63 & HWS & HTP & HER & Hh & Hl & AC).
  pose proof rm_sf as (E1 & E2 & G1 & G2 & G3 & G4 & G5 & G6).
  destruct (rm_rf R2 RF2) as (R2' & R8 & R9 & R18 & R19 & RO).
  pose proof CH as (M2 & W2 & B2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW2).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
  rewrite <- FREEPC.
  destruct BUF as [(C0 & B0) | (CP & BIN & BG & BO2 & BO & BH)].
  - (* free (NULL) *)
    eapply SR_bind.
    { apply FNC; [rewrite RA2; exact rm_ret_14014 | rewrite R10, B0; reflexivity | exact Hh2 | exact Hl2]. }
    intros c' ->. apply SR_ret. rewrite RA2.
    exists L2, A2, R2, m2, md2, e1, h1, OUT2, CAP2, junk2, LB, X.
    split; [reflexivity|]. split; [exact RF2|]. split; [exact CH|]. split; [exact INI|]. split; [exact RO2|].
    split.
    { exists qs. split; [exact QL|].
      split; [rewrite rm_trR; unfold trBM; rewrite CE, C0; cbn [Z.eqb]; rewrite app_nil_r; exact RQ|].
      split; [exact LOq | exact LS]. }
    split; [exact FR2|]. split; [exact GL2|]. split; [exact LX|]. split; [exact TB2|]. split; [exact GI2|].
    split; [exact DF2|]. split; [exact K12|]. split; [exact LB2|].
    split; [unfold bufl in BF2; rewrite C0 in BF2; exact BF2|]. split; [exact ND2 | exact LF2].
  - (* free (s->buf) *)
    assert (BIN' := BIN). apply rk_blocks_in in BIN' as (p & Ep & Hp).
    assert (HSP : spZ R2 = SP - 48) by (unfold spZ; rewrite R2'; apply unsigned_lit; lia).
    assert (PRE2 : call_pre Bm MR L2 A2 R2 m2 md2).
    { split; [exact M2|]. split; [exact W2|]. split; [exact B2|]. split; [rewrite RA2; exact rm_ret_14014|].
      rewrite HSP. split; [clear - HAL; Z.div_mod_to_equations; lia|]. split; [unfold ALLOC_STACK; lia|].
      split; [lia|].
      split; [intros a Ha; apply SW2; unfold scratch_k, spZ; rewrite (proj1 rm_K); left; unfold ALLOC_STACK in Ha; lia|].
      split; [transitivity (getr regs0 4);
              [exact (RO 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) |
               exact HTP]|].
      split; [intros a Ha; apply SW2; unfold scratch_k; right; exact Ha|].
      intros X0. rewrite INI in X0. discriminate. }
    assert (EP : resolveF qs (da_buf a1M) = p).
    { pose proof (HND _ _ _ _ M2) as NDp.
      rewrite <- (p3c_live_sptr _ _ _ _ _ NDp (LBUF CP)). exact (p3c_live_sptr _ _ _ _ _ NDp (conj Hp Ep)). }
    eapply SR_bind.
    { apply (FRC L2 A2 R2 m2 md2 p (re_cap e1) (runF F qs bnd (trD ++ trGM)) PRE2 RO2 Hp);
        [rewrite R10, Ep; reflexivity | exact RQ]. }
    intros c' (L3 & A3 & R3 & m3 & md3 & -> & CPo & (b1 & b2 & EB2 & EB3) & BK & RO3 & GK & KEEP & INI3 & RG3 & RS3).
    apply SR_ret. rewrite RA2. rewrite Ep in EB2.
    pose proof CPo as (M3 & W3 & B3 & LE3 & AD3 & RP3 & VM3 & FR3 & BY3 & SW3).
    pose proof (HND _ _ _ _ M2) as ND2b.
    assert (LV3 : forall p0 a n, live_at L2 A2 p0 a n -> a <> re_buf e1 -> live_at L3 A3 p0 a n).
    { intros p0 a n [Hin Ha] Hne. assert (NE : p0 <> p) by (intros ->; apply Hne; rewrite <- Ha; exact Ep).
      pose proof (KEEP _ _ Hin NE) as Hin2. split; [exact Hin2|]. rewrite (AD3 _ _ Hin Hin2). exact Ha. }
    assert (NB : forall q m, In (q, m) (blocks L2 A2) -> q <> re_buf e1 -> In (q, m) (blocks L3 A3)).
    { intros q m Hq Hne. rewrite EB3. apply (proj2 (rm_mid_in (blocks L2 A2) b1 b2 (re_buf e1, re_cap e1) (q, m) ND2b EB2)).
      split; [exact Hq | exact Hne]. }
    assert (KB : forall q, q <> re_buf e1 -> rk_bkept Bm L2 A2 m2 L3 A3 m3 q).
    { intros q Hq. apply (rk_cp_bkept Bm API L2 A2 R2 m2 md2 L3 A3 R3 m3 md3 p (re_cap e1) q M2 CPo KEEP).
      rewrite Ep. exact Hq. }
    assert (KG : forall a, (img_plain Bm a \/ alloc_ceiling <= a < 2 ^ 64) -> ~ scratch Bm R2 a -> rk_kb2 Bm m2 m3 a).
    { intros a Ha Hs. exact (rk_cp_gkept Bm API AX L2 A2 R2 m2 md2 L3 A3 R3 m3 md3 p (re_cap e1) a M2 Hp CPo Ha Hs). }
    assert (KS : forall a, img_plain Bm a -> ~ scratch Bm R2 a).
    { intros a K1. pose proof (in_img_low Bm SEGS _ (proj1 K1)) as IL. destruct K1 as (_ & _ & _ & K4).
      unfold scratch, ALLOC_STACK. rewrite HSP. intros [S1|S1]; [lia | exact (K4 S1)]. }
    assert (KC : forall A cs, rw_cells segs m2 A cs ->
                   (forall k, 0 <= k < Z.of_nat (cells_size cs) -> img_plain Bm (A + k)) ->
                   rw_cells segs m3 A cs).
    { intros A cs H K. apply (rk_rw_kb2 Bm m2); [exact H|]. intros k Hk. pose proof (K k Hk) as K1.
      apply KG; [left; exact K1 | exact (KS _ K1)]. }
    rm_hide.
    assert (CHAIN : rk_chain Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0
                      L3 A3 m3 md3).
    { apply (rk_chain_free Bm API AX CTX RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0
               L2 A2 m2 md2 R2 L3 A3 R3 m3 md3
               p (re_cap e1) HW0 CH CPo KEEP RG3 Hp CP).
      - intros a Ha. unfold scratch in Ha. unfold scratch_k, spZ. rewrite (proj1 rm_K). rewrite HSP in Ha.
        unfold ALLOC_STACK in Ha. lia.
      - intros a Ha Hn. unfold scratch_k, spZ in Ha. rewrite (proj1 rm_K) in Ha. unfold scratch in Hn.
        rewrite HSP in Hn. unfold ALLOC_STACK in Hn. lia.
      - intros p0 n0 Hp0 Hp2 Hn0 HF E. subst p0.
        destruct (rk_chain_in Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0
                    L2 A2 m2 md2 p n0 HW0 CH Hp0 HF)
          as [_ EA].
        assert (HBQ : In (re_buf e1, n0) (blocks L0 A0))
          by (apply rk_blocks_in; exists p; split; [rewrite <- EA; exact Ep | exact Hp0]).
        destruct BF2 as (_ & _ & BF3).
        assert (NF : ~ Ffin (keys_total (re_keys e1)) (re_buf e1)) by (rewrite <- Ep, EA; exact HF).
        assert (N1 : re_buf e1 <> OUT).
        { destruct (send_live cl br dd (TD + keys_total (re_keys e1))) eqn:LV; [|exact (BO eq_refl)].
          intros X0. apply NF. left. split; [|exact X0]. exists e. split; [exact rm_e_in|]. split; [exact HFi|].
          exact LV. }
        assert (N2 : ~ In (re_buf e1) (entry_blocks e))
          by (intros X0; apply NF; right; exists e; split; [exact rm_e_in|]; split; [exact HFi|]; left; exact X0).
        assert (N3 : ~ In (re_buf e1) hbi).
        { unfold hbi. destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0]; [|intros []].
          intros X0. apply NF. right. exists e. split; [exact rm_e_in|]. split; [exact HFi|]. right. split; assumption. }
        destruct (BF3 (re_buf e1) n0 HBQ Hn0 N1 N2 N3) as (_ & NE & _).
        apply NE. unfold entry_blocks. apply in_or_app. left.
        rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) ltac:(lia)). left. reflexivity. }
    exists L3, A3, R3, m3, md3, e1, h1, OUT2, CAP2, junk2, LB, X.
    split; [reflexivity|].
    split; [intros r Hr; rewrite (RP3 r Hr); exact (RF2 r Hr)|].
    split; [exact CHAIN|]. split; [exact (INI3 INI)|]. split; [exact RO3|].
    split.
    { exists qs. split; [exact QL|].
      split.
      { rewrite rm_trR, app_assoc. unfold trBM. rewrite CE, (proj2 (Z.eqb_neq (re_cap e1) 0) ltac:(lia)).
        rewrite p3c_runF_free, EP. exact RS3. }
      split; [intros LV; apply LV3; [exact (LOq LV) | exact (not_eq_sym BO2)]|].
      intros E0. apply (rm_sl_mono L2 A2 L3 A3 qs nm0 a1M h1); [|exact (LS E0)].
      intros p0 a n Hlv _ Ha. apply (LV3 p0 a n Hlv). intros ->. apply BH. unfold hbo.
      rewrite (proj2 (Z.eqb_eq _ _) E0). exact Ha. }
    destruct GL2 as (LK2 & WK2 & NS2 & SR2 & CL2 & BR2 & DD2 & EI2 & ER2).
    split.
    { destruct FR2 as (jf & FR2). exists jf. apply (rk_rw_kb2 Bm m2); [exact FR2|]. intros k Hk.
      cbn [cells_size csize] in Hk. apply KG; [right; lia|]. unfold scratch, ALLOC_STACK. rewrite HSP.
      pose proof (in_img_low Bm SEGS (ERR + 3) (IME (ERR + 3) ltac:(lia))). lia. }
    split.
    { split; [apply KC; [exact LK2|]; intros k Hk; cbn [cells_size csize] in Hk; apply IMR;
              unfold G_LOCK, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
      split; [apply (rk_bytes_kb2 Bm m2); [exact WK2|]; intros k Hk; rewrite length_le4 in Hk;
              assert (IP : img_plain Bm (G_WAKE1 + k)) by (apply IML; unfold G_WAKE1, G_LISTEN; lia);
              apply KG; [left; exact IP | exact (KS _ IP)]|].
      split; [apply KC; [exact NS2|]; intros k Hk; cbn [cells_size csize] in Hk; apply IMR;
              unfold G_NSRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
      split; [apply KC; [exact SR2|]; intros k Hk; cbn [cells_size csize] in Hk; apply IMR;
              unfold G_SRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
      split; [apply KC; [exact CL2|]; intros k Hk; cbn [cells_size csize] in Hk; apply IML;
              unfold G_CLIENT, G_LISTEN, G_WAKE1; lia|].
      split; [apply KC; [exact BR2|]; intros k Hk; cbn [cells_size csize] in Hk; apply IMR;
              unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
      split; [apply KC; [exact DD2|]; intros k Hk; cbn [cells_size csize] in Hk; apply IMR;
              unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
      split; [apply KC; [exact EI2|]; intros k Hk; cbn [cells_size csize] in Hk; apply IMR;
              unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
      rewrite SEGS. apply rk_err_cells; [lia | lia |]. intros k Hk. rewrite <- SEGS. apply SW3. unfold scratch. right. lia. }
    split; [exact LX|].
    split; [apply (rk_rw_in_block Bm L2 A2 m2 L3 A3 m3 G SRC_TABLE G _ TB2 (KB G ltac:(congruence)) GI2);
            [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia]|].
    split; [exact (proj1 (KB G ltac:(congruence) SRC_TABLE GI2))|].
    split.
    { intros E0. destruct (DF2 E0) as [D2 GHB]. split; [|exact GHB].
      destruct (SRCP e rm_e_in HFi E0) as (_ & _ & Hj & _).
      apply (rm_DF_kept L2 A2 m2 L3 A3 m3 h1 (re_keys e1) Hj D2).
      - intros a Ha. unfold G_S in Ha.
        assert (IP : img_plain Bm a) by (apply IMR; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia).
        apply KG; [left; exact IP | exact (KS _ IP)].
      - intros q Hq. apply KB. intros E. apply BH. subst q. unfold hbo. rewrite (proj2 (Z.eqb_eq _ _) E0). exact Hq. }
    split; [exact K12|]. split; [exact LB2|].
    split.
    { destruct BF2 as (BF1 & BFb & BF3). split; [|split; [|exact BF3]].
      - intros q m Hq HO HE HH. pose proof (BF1 q m Hq HO HE HH) as Q2. apply NB; [exact Q2|].
        intros ->. destruct (Z_lt_le_dec 0 m) as [Mp|Mn].
        + destruct (BF3 _ m Hq Mp HO HE HH) as (_ & NE & _). apply NE. unfold entry_blocks. apply in_or_app. left.
          rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) ltac:(lia)). left. reflexivity.
        + pose proof (rk_nodup_fst (blocks L2 A2) (re_buf e1) m (re_cap e1) (rma_nodup_std _ ND2b) Q2 BIN). lia.
      - intros q m Hq. rewrite EB3 in Hq.
        pose proof (proj1 (rm_mid_in (blocks L2 A2) b1 b2 (re_buf e1, re_cap e1) (q, m) ND2b EB2) Hq) as [Q2 NE].
        cbn [fst] in NE. destruct (BFb q m Q2) as [H|[H|H]]; [left; exact H | | right; right; exact H].
        right. left. unfold bufl in H. rewrite (proj2 (Z.eqb_neq (re_cap e1) 0) ltac:(lia)) in H. cbn [app In] in H.
        destruct H as [H|H]; [exfalso; exact (NE (eq_sym H)) | exact H]. }
    split; [exact ND2|].
    destruct LF2 as (LF0 & LF1). split.
    + intros LV. destruct (LF0 LV) as (OV & OB & OE).
      split; [apply KC; [exact OV|]; intros k Hk; cbn [cells_size csize] in Hk; apply IMR;
              unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia|].
      split; [|exact OE]. intros CP0. destruct (OB CP0) as (OI & OBy). split.
      * apply NB; [exact OI | exact (not_eq_sym (BO LV))].
      * apply (rk_bytes_in_block Bm L2 A2 m2 L3 A3 m3 OUT CAP OUT _ OBy (KB OUT (not_eq_sym (BO LV))) OI); [lia|].
        rewrite length_app. destruct OUTD as [(C1 & _)|(_ & _ & _ & _ & _ & LO & LJ)]; lia.
    + intros LV. destruct (LF1 LV) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      split; [exact Q1|]. split; [exact Q2|]. split; [apply NB; [exact Q3 | exact (not_eq_sym BO2)]|]. split; [exact Q4|].
      split.
      * apply (rk_bytes_in_block Bm L2 A2 m2 L3 A3 m3 OUT2 CAP2 OUT2 _ Q5 (KB OUT2 (not_eq_sym BO2)) Q3); [lia|].
        rewrite !length_app. pose proof (rma_keys_total_nonneg (re_keys e1)) as KTN.
        pose proof (rm_ko_len (re_keys e1)) as LKO.
        assert (LLB : Z.of_nat (length LB) = TD) by (unfold TD; rewrite <- LB2; unfold bzs; rewrite length_map; reflexivity).
        assert (LO0 : Z.of_nat (length O) = NO) by (destruct OUTD as [(_ & _ & N0 & OE)|(_ & _ & _ & _ & _ & LO & _)];
          [rewrite OE; cbn [length]; lia | exact LO]).
        lia.
      * split; [exact Q6|]. apply KC; [exact Q7|]. intros k Hk. cbn [cells_size csize] in Hk. apply IMR.
        unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia.
Qed.

Definition P40 (e1 : rentry) : list byte :=
  le4 (Z_to_bv 64 (re_fd e1)) ++ le4 (Z_to_bv 64 (re_eof e1)) ++ le4 (Z_to_bv 64 (re_skip e1)) ++ re_pad1 e1 ++
  le8 (Z_to_bv 64 (re_buf e1)) ++ le8 (Z_to_bv 64 (re_used e1)) ++ le8 (Z_to_bv 64 (re_cap e1)).

Lemma rm_eb_split : forall e1, entry_bytes e1 =
  P40 e1 ++ le8 (Z_to_bv 64 (re_hp e1)) ++ le4 (Z_to_bv 64 (re_nheld e1)) ++ re_pad2 e1.
Proof using. intros e1. unfold entry_bytes, P40. rewrite <- !app_assoc. reflexivity. Qed.

Lemma rm_P40_len : forall e1, length (re_pad1 e1) = 4%nat -> length (P40 e1) = 40%nat.
Proof using. intros e1 H. unfold P40. rewrite !length_app, !length_le4, !length_le8, H. reflexivity. Qed.

Lemma rm_slot_cut : forall m A e1, length (re_pad1 e1) = 4%nat -> length (re_pad2 e1) = 4%nat ->
  rw_cells rsegs m A [CB 56 (entry_bytes e1)] ->
  rw_cells rsegs m A [CB 40 (P40 e1)] /\
  rw_cells rsegs m (A + 40) [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))] /\
  rw_cells rsegs m (A + 52) [CB 4 (re_pad2 e1)] /\
  bytes_at rsegs m (A + 16) (le8 (Z_to_bv 64 (re_buf e1))).
Proof using Bm Hi O junk.
  intros m A e1 P1 P2 H.
  assert (H' : rw_cells rsegs m A ([CB 40 (P40 e1)] ++
                 [C8 (Z_to_bv 64 (re_hp e1)); C4 (Z_to_bv 64 (re_nheld e1))] ++ [CB 4 (re_pad2 e1)])).
  { eapply rm_rw_conv; [exact H | cbn [cells_wf cell_wf app]; rewrite (rm_P40_len e1 P1); repeat split; auto |
      cbn [cells_bytes cbytes app]; rewrite rm_eb_split, !app_nil_r; reflexivity |
      cbn [cells_size csize app]; reflexivity]. }
  apply rm_cells_cut in H' as [H1 H2]. apply rm_cells_cut in H2 as [H2 H3]. cbn [cells_size csize] in H2, H3.
  split; [exact H1|]. split; [exact H2|].
  split; [replace (A + 52) with (A + Z.of_nat (40 + 0) + Z.of_nat (8 + (4 + 0))) by lia; exact H3|].
  pose proof (rm_rw_bytes _ _ _ _ H1) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  assert (EP : P40 e1 = (le4 (Z_to_bv 64 (re_fd e1)) ++ le4 (Z_to_bv 64 (re_eof e1)) ++ le4 (Z_to_bv 64 (re_skip e1)) ++
                         re_pad1 e1) ++ le8 (Z_to_bv 64 (re_buf e1)) ++
                        (le8 (Z_to_bv 64 (re_used e1)) ++ le8 (Z_to_bv 64 (re_cap e1))))
    by (unfold P40; rewrite <- !app_assoc; reflexivity).
  rewrite EP in B. apply bytes_at_app in B as [_ B]. apply bytes_at_app in B as [B _].
  rewrite !length_app, !length_le4, P1 in B. change (Z.of_nat (4 + (4 + (4 + 4)))) with 16 in B. exact B.
Qed.

Lemma rm_slot_join : forall m A e1, length (re_pad1 e1) = 4%nat -> length (re_pad2 e1) = 4%nat ->
  rw_cells rsegs m A [CB 40 (P40 e1)] -> rw_cells rsegs m (A + 40) [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells rsegs m (A + 52) [CB 4 (re_pad2 e1)] ->
  rw_cells rsegs m A [CB 56 (P40 e1 ++ le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ re_pad2 e1)].
Proof using Bm Hi O junk.
  intros m A e1 P1 P2 H1 H2 H3.
  assert (H23 : rw_cells rsegs m (A + 40) ([C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [CB 4 (re_pad2 e1)])).
  { apply (rm_cells_join m _ (A + 52)); [exact H2 | exact H3 | cbn [cells_size csize]; lia]. }
  assert (H123 : rw_cells rsegs m A ([CB 40 (P40 e1)] ++ [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ++ [CB 4 (re_pad2 e1)])).
  { apply (rm_cells_join m _ (A + 40)); [exact H1 | exact H23 | cbn [cells_size csize]; lia]. }
  eapply rm_rw_conv; [exact H123 | cbn [cells_wf cell_wf app]; rewrite !length_app, (rm_P40_len e1 P1), length_le8,
    length_le4, P2; repeat split; auto | cbn [cells_bytes cbytes app]; rewrite !app_nil_r; reflexivity |
    cbn [cells_size csize app]; reflexivity].
Qed.

Lemma rm_rp_img : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 A cs,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  alloc_ceiling <= spZ R1 - K' -> rw_cells segs m1 A cs ->
  (forall k, 0 <= k < Z.of_nat (cells_size cs) -> img_plain Bm (A + k) /\ ~ E' (A + k)) ->
  rw_cells segs m2 A cs.
Proof using AX Hi O SEGS junk.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 A cs M1 RP HK H K.
  apply (rk_rw_kb2 Bm m1); [exact H|]. intros k Hk. destruct (K k Hk) as [K1 K2].
  apply (rk_rp_gkept Bm API AX K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 (A + k) M1 RP (or_introl K1) K2).
  pose proof (in_img_low Bm SEGS _ (proj1 K1)) as IL. pose proof (@YM05.alloc_ceiling_value rc) as AC.
  destruct K1 as (_ & _ & _ & K4). unfold scratch_k. intros [S|S]; [lia | exact (K4 S)].
Qed.

Lemma rm_rp_imgb : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 A bs,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  alloc_ceiling <= spZ R1 - K' -> bytes_at segs m1 A bs ->
  (forall k, 0 <= k < Z.of_nat (length bs) -> img_plain Bm (A + k) /\ ~ E' (A + k)) ->
  bytes_at segs m2 A bs.
Proof using AX Hi O SEGS junk.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 A bs M1 RP HK H K.
  apply (rk_bytes_kb2 Bm m1); [exact H|]. intros k Hk. destruct (K k Hk) as [K1 K2].
  apply (rk_rp_gkept Bm API AX K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 (A + k) M1 RP (or_introl K1) K2).
  pose proof (in_img_low Bm SEGS _ (proj1 K1)) as IL. pose proof (@YM05.alloc_ceiling_value rc) as AC.
  destruct K1 as (_ & _ & _ & K4). unfold scratch_k. intros [S|S]; [lia | exact (K4 S)].
Qed.

Lemma rm_rp_hi : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 A cs,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  spZ R1 <= A -> A + Z.of_nat (cells_size cs) <= 2 ^ 64 -> alloc_ceiling <= A -> ERR + 4 <= A ->
  (forall k, 0 <= k < Z.of_nat (cells_size cs) -> ~ E' (A + k)) ->
  rw_cells segs m1 A cs -> rw_cells segs m2 A cs.
Proof using AX Hi O junk.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 A cs M1 RP H1 H2 H3 H4 HE H.
  apply (rk_rw_kb2 Bm m1); [exact H|]. intros k Hk.
  apply (rk_rp_gkept Bm API AX K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 (A + k) M1 RP); [right; lia | exact (HE k Hk) |].
  unfold scratch_k. lia.
Qed.

Lemma rm_rp_bc : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k A cs,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> ~ F' q ->
  In (q, k) (blocks L1 A1) -> q <= A -> A + Z.of_nat (cells_size cs) <= q + k ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ~ E' (A + i)) -> rw_cells segs m1 A cs -> rw_cells segs m2 A cs.
Proof using Hi O junk.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k A cs M1 RP HF Hin H1 H2 HE H.
  destruct (rk_rp_kept Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k M1 RP HF Hin) as [_ KB].
  apply (rk_rw_kb2 Bm m1); [exact H|]. intros t Ht. replace (A + t) with (q + (A - q + t)) by lia.
  apply KB; [lia|]. replace (q + (A - q + t)) with (A + t) by lia. exact (HE t Ht).
Qed.

Lemma rm_rp_bb : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k A bs,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 -> ~ F' q ->
  In (q, k) (blocks L1 A1) -> q <= A -> A + Z.of_nat (length bs) <= q + k ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> ~ E' (A + i)) -> bytes_at segs m1 A bs -> bytes_at segs m2 A bs.
Proof using Hi O junk.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k A bs M1 RP HF Hin H1 H2 HE H.
  destruct (rk_rp_kept Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q k M1 RP HF Hin) as [_ KB].
  apply (rk_bytes_kb2 Bm m1); [exact H|]. intros t Ht. replace (A + t) with (q + (A - q + t)) by lia.
  apply KB; [lia|]. replace (q + (A - q + t)) with (A + t) by lia. exact (HE t Ht).
Qed.

Lemma rm_blk0 : forall L A m md q k, MR L A m md -> In (q, 0) (blocks L A) -> In (q, k) (blocks L A) -> 0 < k -> False.
Proof using HND Hi O junk.
  intros L A m md q k HM H0 H1 Hk.
  pose proof (rk_nodup_fst (blocks L A) q 0 k (rma_nodup_std _ (HND _ _ _ _ HM)) H0 H1). lia.
Qed.

Lemma rm_list_pos : forall L A m LA l b, list_at Bm L A m LA l b ->
  forall q, In q (list_blocks l) -> exists k, 0 < k /\ In (q, k) (blocks L A).
Proof using Hi O junk.
  intros L A m LA l b (_ & _ & HV & _ & _ & HR) q Hq. unfold list_blocks in Hq. apply in_app_iff in Hq as [Hq|Hq].
  - destruct (Z.eqb_spec (hl_cap l) 0) as [E|E]; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct HV as [(C0 & _)|(Cp & HI & _)]; [lia|]. exists (16 * hl_cap l). split; [lia | exact HI].
  - apply in_map_iff in Hq as (r & <- & Hr). destruct (proj1 (Forall_forall _ _) HR r Hr) as (HI & _).
    exists (Z.of_nat (length (snd r)) + 1). split; [lia | exact HI].
Qed.

Lemma rm_hs_pos : forall L A m h1, src_at Bm L A m HA h1 ->
  forall q, In q (hs_blocks h1) -> exists k, 0 < k /\ In (q, k) (blocks L A).
Proof using Hi O junk.
  intros L A m h1 (_ & _ & _ & _ & _ & LP & _ & _ & _ & _ & HPi & _ & _ & _ & _ & LE & LH & _) q Hq.
  unfold hs_blocks in Hq. rewrite !in_app_iff in Hq. destruct Hq as [Hq|[Hq|[Hq|Hq]]].
  - exact (rm_list_pos _ _ _ _ _ _ LP q Hq).
  - destruct Hq as [<-|[]]. exists 6000. split; [lia | exact HPi].
  - exact (rm_list_pos _ _ _ _ _ _ LE q Hq).
  - exact (rm_list_pos _ _ _ _ _ _ LH q Hq).
Qed.

Definition brT (T : Z) : Z := if send_off cl br T then br else dd.
Definition eiT (T : Z) : Z := if send_off cl br T then ei else 0.

(* The resource state at gestures_end (s): drain's requests made (none when s->eof = 1), which returned qd; the
   output buffer, the source's blocks and drain's harness-source blocks at the addresses after drain. *)
Definition RGz (L1 : layout) (A1 : astate) (e1 : rentry) (h1 : hsrc) (cap1 out1 : Z) : Prop :=
  exists qd, length qd = nretF trD /\ rt_ok F A1 (runF F qd bnd trD) /\
    (forall ext, runF F (qd ++ ext) bnd trD = runF F qd bnd trD) /\ rm_dab (length qd) a1M /\
    (cap1 <> 0 -> live_at L1 A1 (resolveF qd (da_out a1M)) out1 cap1) /\
    entry_links L1 A1 qd a1M e1 /\
    (re_eof e = 0 -> src_links L1 A1 qd nm0 a1M h1).

(* At gestures_end (s), 0x13200: e1 and h1 the sources after drain (e and h when s->eof = 1). *)
Definition AtG (c : config) : Prop :=
  exists L1 A1 R1 m1 md1 (e1 : rentry) (h1 : hsrc) (O1 junk1 LB : list byte) (nout1 cap1 out1 : word),
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 GESTURES_END) m1 (seg_rom segs)) md1 /\
    RFr R1 /\ getr R1 1 = Z_to_bv 64 0x13fe0 /\ getr R1 10 = Z_to_bv 64 SA /\
    rk_chain Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0 L1 A1 m1 md1 /\
    st_init_done A1 = true /\ ro_agree segs m1 /\ RGz L1 A1 e1 h1 (bv_unsigned cap1) (bv_unsigned out1) /\
    FRM m1 /\ GLB m1 (brT TD) (eiT TD) /\
    rw_cells segs m1 G_OUTV [C8 mx; C8 nout1; C8 cap1; C8 out1] /\
    rw_cells segs m1 G [CB 896 (Tpre ++ entry_bytes e1 ++ Tpost)] /\ In (G, SRC_TABLE) (blocks L1 A1) /\
    entry_ok Bm L1 A1 m1 e1 /\ NoDup (G :: bv_unsigned out1 :: entry_blocks e1 ++ hbo h1) /\
    (re_eof e = 0 -> DF L1 A1 m1 h1 (re_keys e1)) /\ (re_eof e = 1 -> map fst (re_keys e1) = map fst (re_keys e)) /\
    bzs LB = with_nul Lsi /\ BF L1 A1 (bv_unsigned out1) e1 h1 (entry_blocks e1) /\
    ((bv_unsigned cap1 = 0 /\ bv_unsigned out1 = 0 /\ bv_unsigned nout1 = 0 /\ O1 = []) \/
     (0 < bv_unsigned cap1 /\ bv_unsigned nout1 <= bv_unsigned cap1 /\
      In (bv_unsigned out1, bv_unsigned cap1) (blocks L1 A1) /\ fresh_block Bm (bv_unsigned out1) (bv_unsigned cap1) /\
      bytes_at segs m1 (bv_unsigned out1) (O1 ++ junk1) /\ Z.of_nat (length O1) = bv_unsigned nout1 /\
      Z.of_nat (length junk1) = bv_unsigned cap1 - bv_unsigned nout1)) /\
    (send_live cl br dd TD = false -> nout1 = nout /\ cap1 = cap /\ out1 = out /\ O1 = O /\ junk1 = junk) /\
    (send_live cl br dd TD = true -> bv_unsigned nout1 = NO + TD /\ O1 = O ++ LB) /\
    keys_texts (re_keys e1) = ds_H sDM /\ re_cap e1 = ds_cap sDM /\
    (forall xks jj o ha, map fst xks = key_lens (re_keys e1) ->
       gestures_end_tr lv (bv_unsigned mx) (ds_no sDM) (ds_ocap sDM) xks (ds_ka sDM) (ds_ka sDM) jj o ha =
       gestures_end_tr (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx)
         (bv_unsigned nout1) (bv_unsigned cap1) xks (re_hp e1) (re_kh e1) jj o ha /\
       gestures_end_out lv (bv_unsigned mx) (ds_no sDM) (ds_ocap sDM) xks jj o =
       gestures_end_out (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx)
         (bv_unsigned nout1) (bv_unsigned cap1) xks jj o) /\
    (send_live cl br dd (TD + keys_total (re_keys e1)) = true ->
       gestures_end_cap (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx) (bv_unsigned nout1)
         (bv_unsigned cap1) (key_lens (re_keys e1)) =
       remove_entry_cap lv (bv_unsigned mx) NO CAP e h).

Lemma rm_nd_app : forall {X : Type} (l1 l2 : list X) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof using.
  intros X l1. induction l1 as [|y l1 IH]; intros l2 x H Hx; [destruct Hx|].
  cbn [app] in H. apply List.NoDup_cons_iff in H as [Hn Hd]. destruct Hx as [<-|Hx].
  - intros Y. apply Hn. apply in_or_app. right. exact Y.
  - exact (IH l2 x Hd Hx).
Qed.

Lemma rm_eb_parts : forall e1 X, List.NoDup (entry_blocks e1 ++ X) ->
  (re_hp e1 <> 0 -> In (re_hp e1) (entry_blocks e1) /\ ~ In (re_hp e1) (map key_addr (re_keys e1))) /\
  (re_cap e1 <> 0 -> In (re_buf e1) (entry_blocks e1) /\ (re_hp e1 <> 0 -> re_buf e1 <> re_hp e1) /\
                     ~ In (re_buf e1) (map key_addr (re_keys e1))) /\
  (forall k, In k (re_keys e1) -> In (key_addr k) (entry_blocks e1)).
Proof using.
  intros e1 X H. apply List.NoDup_app_remove_r in H. unfold entry_blocks in *.
  set (bl := if re_cap e1 =? 0 then [] else [re_buf e1]) in *.
  set (hl := if re_hp e1 =? 0 then [] else [re_hp e1]) in *.
  split; [|split].
  - intros Hp. assert (HI : In (re_hp e1) hl) by (unfold hl; rewrite (proj2 (Z.eqb_neq _ 0) Hp); left; reflexivity).
    split; [apply in_or_app; right; apply in_or_app; left; exact HI|].
    apply List.NoDup_app_remove_l in H. exact (rm_nd_app _ _ _ H HI).
  - intros Hc. assert (BI : In (re_buf e1) bl) by (unfold bl; rewrite (proj2 (Z.eqb_neq _ 0) Hc); left; reflexivity).
    split; [apply in_or_app; left; exact BI|].
    pose proof (rm_nd_app _ _ _ H BI) as NB. split.
    + intros Hp E. apply NB. apply in_or_app. left. unfold hl. rewrite (proj2 (Z.eqb_neq _ 0) Hp). left.
      symmetry. exact E.
    + intros Y. apply NB. apply in_or_app. right. exact Y.
  - intros k Hk. apply in_or_app. right. apply in_or_app. right. apply in_map. exact Hk.
Qed.

Lemma rm_ret_13fe0 : YK0s.ret_ok (Z_to_bv 64 0x13fe0).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rm_blk_lo : forall L A m md q k, MR L A m md -> In (q, k) (blocks L A) -> 4096 <= q /\ q + k <= alloc_ceiling.
Proof using.
  intros L A m md q k HM Hq. apply rk_blocks_in in Hq as (p & Ep & Hp).
  pose proof (mr_blocks_range Bm MR (aa_laws API) _ _ _ _ p _ HM Hp) as GR. rewrite Ep in GR. exact GR.
Qed.

Lemma rm_blk_noimg : forall L A m md q k a, MR L A m md -> In (q, k) (blocks L A) -> q <= a < q + k ->
  ~ in_img Bm a /\ 4096 <= q /\ q + k <= alloc_ceiling.
Proof using AX Hi O junk.
  intros L A m md q k a HM Hq Ha. pose proof (rm_blk_lo L A m md q k HM Hq) as (Q1 & Q2).
  split; [|lia].
  apply rk_blocks_in in Hq as (p & Ep & Hp). subst q. replace a with (ptr_addr L p + (a - ptr_addr L p)) by lia.
  exact (ax_blocks_img AX L A m md p k (a - ptr_addr L p) HM Hp ltac:(lia)).
Qed.

Lemma rm_eb_pos : forall L A m e1, entry_ok Bm L A m e1 -> forall q, In q (entry_blocks e1) ->
  exists k, 0 < k /\ In (q, k) (blocks L A).
Proof using Hi O junk.
  intros L A m e1 (_ & _ & _ & _ & _ & _ & _ & _ & _ & BUFD & _ & HPD & _ & _ & KF) q Hq.
  unfold entry_blocks in Hq. rewrite !in_app_iff in Hq. destruct Hq as [Hq|[Hq|Hq]].
  - revert Hq. destruct (Z.eqb_spec (re_cap e1) 0) as [E|E]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct BUFD as [(C0 & _)|(Cp & BI & _)]; [lia|]. exists (re_cap e1). split; [exact Cp | exact BI].
  - revert Hq. destruct (Z.eqb_spec (re_hp e1) 0) as [E|E]; intros Hq; [destruct Hq|]. destruct Hq as [<-|[]].
    destruct HPD as [(H0 & _)|(HI & _ & _ & H8 & _)]; [lia|]. exists (re_kh e1). split; [lia | exact HI].
  - apply in_map_iff in Hq as (k & <- & Hk). destruct (proj1 (Forall_forall _ _) KF k Hk) as (KB & _).
    exists (Z.of_nat (length (key_text k)) + 1). split; [lia | exact KB].
Qed.

Lemma rm_ker_dead : forall mx0 no c xks j o, snd (keys_end_run false mx0 no c xks j o) = (c, o).
Proof using. intros. rewrite fi_ker_false. reflexivity. Qed.

Lemma rm_rp_kb : forall K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 a,
  MR L1 A1 m1 md1 -> relay_post Bm API K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 ->
  alloc_ceiling <= spZ R1 - K' -> img_plain Bm a -> ~ E' a -> rk_kb2 Bm m1 m2 a.
Proof using AX Hi O SEGS junk.
  intros K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 a M1 RP HK K1 K2.
  apply (rk_rp_gkept Bm API AX K' E' F' L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 a M1 RP (or_introl K1) K2).
  pose proof (in_img_low Bm SEGS _ (proj1 K1)) as IL. pose proof (@YM05.alloc_ceiling_value rc) as AC.
  destruct K1 as (_ & _ & _ & K4). unfold scratch_k. intros [S|S]; [lia | exact (K4 S)].
Qed.

Ltac rm_tg :=
  let k := fresh "k" in let Hk := fresh "Hk" in
  intros k Hk; cbn [cells_size csize] in Hk; split; [apply IMR | split; [|split]];
  unfold G_LOCK, G_NSRC, G_SRC, G_BROKEN, G_EINTR, G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in Hk |- *; lia.

Ltac rm_rfr X RFH :=
  let r := fresh "r" in let Hr := fresh "Hr" in let C := fresh "C" in
  intros r Hr; unfold callee_saved in Hr;
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]]]; subst r;
  (match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X eq_refl) end); simp_regs;
  first [ reflexivity | exact (RFH _ ltac:(unfold callee_saved; lia)) ].

Lemma rm_ge : forall c, AtG c -> SR segs c AtF.
Proof using AX EHI EOK GFR GIN GSC HERR4 HFi HN4 HND Hbr Hcl Hdd Hei Hi IM5 IME IML IMR NDB NDF PRE ROOM SEGS SRCP TAB TPE.
  intros c (L1 & A1 & R1 & m1 & md1 & e1 & h1 & O1 & junk1 & LB & nout1 & cap1 & out1 & -> & RF1 & RA1 & R10 & CH &
    INI & RO1 & RS1 & FR1 & GL1 & OV1 & TB1 & GI1 & EK1 & ND1 & DF1 & K11 & LB1 & BF1 & OD1 & LD0 & LD1 & KTX &
    CPX & GEQ & CAPF).
  pose proof rm_pre as (HM0 & HW0 & HB0 & HRA & HAL & HCE & H63 & HWS & HTP & HER & Hh & Hl & AC).
  pose proof rm_sf as (E1 & E2 & G1 & G2 & G3 & G4 & G5 & G6).
  destruct rm_K as (K1 & K2 & K3 & K4 & K5).
  destruct (rm_rf R1 RF1) as (R1s & R8 & R9 & R18 & R19 & RO).
  pose proof CH as (M1 & W1 & B1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & SW1).
  destruct GL1 as (LK1 & WK1 & NS1 & SR1 & CL1 & BR1 & DD1 & EI1 & (ev & ER1)).
  pose proof EK1 as (EOF1 & SK1 & P1 & P2 & FDR & CAPV & UL & UB & UNZ & BUFD & NHB & HPD & NDK & NDT & KF).
  pose proof rm_G_safe as (GO & GE & GH).
  assert (Hi16 : (i < 16)%nat) by lia.
  assert (HSP : spZ R1 = SP - 48) by (unfold spZ; rewrite R1s; apply unsigned_lit; lia).
  pose proof (rma_nodup_std _ ND1) as NDs. apply List.NoDup_cons_iff in NDs as [NG NDs].
  apply List.NoDup_cons_iff in NDs as [NOU NDs].
  destruct (rm_eb_parts e1 (hbo h1) NDs) as (EPH & EPB & EPK).
  assert (OUTF : bv_unsigned cap1 = 0 \/ (In (bv_unsigned out1, bv_unsigned cap1) (blocks L1 A1) /\
                   fresh_block Bm (bv_unsigned out1) (bv_unsigned cap1) /\ bv_unsigned nout1 <= bv_unsigned cap1))
    by (destruct OD1 as [(C0 & _)|(_ & NL & OI & OF & _)]; [left; exact C0 | right; auto]).
  pose proof (bv_unsigned_in_range 64 nout1) as RN1. pose proof (bv_unsigned_in_range 64 cap1) as RC1.
  pose proof (bv_unsigned_in_range 64 out1) as RO1'. change (bv_modulus 64) with (2 ^ 64) in RN1, RC1, RO1'.
  assert (NO1B : bv_unsigned nout1 < 2 ^ 47).
  { destruct OD1 as [(_ & _ & N0 & _)|(Cp & NL & _ & (F1 & F2 & _) & _)]; lia. }
  assert (TKB : keys_total (re_keys e1) <= 6005 * 2 ^ 26).
  { assert (KL : Forall (fun k => Z.of_nat (length (key_text k)) <= 6000) (re_keys e1)).
    { apply Forall_forall. intros k Hk. destruct (proj1 (Forall_forall _ _) KF k Hk) as (_ & _ & _ & _ & KLn & _).
      lia. }
    pose proof (rma_keys_total_bound _ KL). unfold re_nheld in NHB. lia. }
  pose proof (rma_keys_total_nonneg (re_keys e1)) as TKN.
  assert (TDN : 0 <= TD) by (unfold TD; lia).
  rewrite SEGS in TB1. destruct (rm_tsplit m1 (entry_bytes e1) (rma_entry_len e1 P1 P2) TB1) as (T1 & T2 & T3).
  destruct (rm_slot_cut m1 SA e1 P1 P2 T2) as (S1 & S2 & S3 & S4).
  rm_hide.
  (* The resource state after drain, and gestures_end's requests inside relay_remove's trace. *)
  destruct RS1 as (qd & QL & RQ & RX & DAB & LOd & ELk & SLs).
  pose proof (HND _ _ _ _ M1) as ND1b.
  destruct ELk as (ELb & ELh & ELs).
  assert (XKS : xksM = combine (key_lens (re_keys e1)) (da_keys a1M)) by (unfold xksM; rewrite <- KTX, rm_klens; reflexivity).
  assert (XF : map fst xksM = key_lens (re_keys e1)).
  { rewrite XKS. apply rm_fst_combine. unfold key_lens. rewrite length_map. exact (Forall2_length ELs). }
  destruct (GEQ xksM (nretF trD) (da_out a1M) (da_hp a1M) XF) as (GTq & GOq). fold trGM in GTq.
  assert (OR : outR = gestures_end_out lv (bv_unsigned mx) (ds_no sDM) (ds_ocap sDM) xksM (nretF trD) (da_out a1M))
    by reflexivity.
  rewrite GOq in OR.
  assert (RESX : forall qc ext,
    length qc = nretF (gestures_end_tr (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx)
      (bv_unsigned nout1) (bv_unsigned cap1) (key_runs (known_at L1 A1) (re_keys e1)) (re_hp e1) (re_kh e1) 0
      (known_at L1 A1 (bv_unsigned out1)) (known_at L1 A1 (re_hp e1))) ->
    p3c_res (qd ++ qc ++ ext) (nretF trD) trGM =
      p3c_res qc 0 (gestures_end_tr (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx)
      (bv_unsigned nout1) (bv_unsigned cap1) (key_runs (known_at L1 A1) (re_keys e1)) (re_hp e1) (re_kh e1) 0
      (known_at L1 A1 (bv_unsigned out1)) (known_at L1 A1 (re_hp e1))) /\
    nretF trGM = length qc /\
    (gestures_end_cap (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx) (bv_unsigned nout1)
       (bv_unsigned cap1) (key_lens (re_keys e1)) <> 0 ->
     resolveF (qd ++ qc ++ ext) outR =
     resolveF qc (gestures_end_out (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx)
       (bv_unsigned nout1) (bv_unsigned cap1) (key_runs (known_at L1 A1) (re_keys e1)) 0
       (known_at L1 A1 (bv_unsigned out1))))).
  { intros qc ext QLc.
    assert (RQX : forall a, rm_ab (length qd) a -> resolveF (qd ++ qc ++ ext) a = resolveF qd a)
      by (intros a Ha; exact (rm_ab_res _ qd (qc ++ ext) a Ha eq_refl)).
    destruct DAB as (DAo & DAb & DAh & DAk & _).
    destruct (p3c_ges_res (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx) (bv_unsigned nout1)
      (bv_unsigned cap1) xksM (key_runs (known_at L1 A1) (re_keys e1)) (re_hp e1) (re_kh e1) (qd ++ qc ++ ext) qc
      (nretF trD) 0%nat (da_out a1M) (known_at L1 A1 (bv_unsigned out1)) (da_hp a1M) (known_at L1 A1 (re_hp e1)))
      as (Rs1 & Rs2 & Rs3).
    - rewrite XKS. apply (rm_xks_f2 L1 A1 qd (qd ++ qc ++ ext) qc (re_keys e1) (da_keys a1M) ND1b ELs).
      intros a Ha. apply RQX. rewrite Forall_forall in DAk. exact (DAk a Ha).
    - intros HC. rewrite (RQX _ DAo). unfold known_at. cbn [resolve].
      symmetry. exact (p3c_live_sptr _ _ _ _ _ ND1b (LOd HC)).
    - intros HZ. rewrite (RQX _ DAh). unfold known_at. cbn [resolve].
      symmetry. exact (p3c_live_sptr _ _ _ _ _ ND1b (ELh HZ)).
    - intros i0 Hi0. rewrite app_nth2 by lia. replace (nretF trD + i0 - length qd)%nat with i0 by lia.
      rewrite app_nth1 by lia. reflexivity.
    - rewrite <- GTq in Rs1, Rs2. split; [exact Rs1|]. split; [rewrite QLc; exact Rs2|].
      intros HC. rewrite OR. apply Rs3. rewrite XF. exact HC. }
  eapply SR_bind.
  { pose proof GSC as GC. unfold gestures_end_contract in GC.
    specialize (GC L1 A1 R1 m1 md1 (runF F qd bnd trD) (re_keys e1) (re_hp e1) (re_kh e1) O1 junk1 cl (brT TD) dd
                   (eiT TD) mx nout1 cap1 out1 ev).
    cbv zeta in GC.
    match type of GC with context [bv_unsigned (PropExec.getr R1 ?r)] =>
      assert (U10 : bv_unsigned (PropExec.getr R1 r) = G + 56 * Z.of_nat i)
        by (transitivity (bv_unsigned (Z_to_bv 64 (G + 56 * Z.of_nat i))); [f_equal; exact R10 | apply unsigned_lit; lia]);
      rewrite U10 in GC
    end.
    apply GC; clear GC.
    - exact SEGS.
    - split; [exact M1|]. split; [exact W1|]. split; [exact B1|]. split; [rewrite RA1; exact rm_ret_13fe0|].
      rewrite HSP, K3. split; [clear - HAL; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      split; [intros a Ha; apply SW1; unfold scratch_k, spZ; rewrite K1; left; lia|].
      split; [transitivity (getr regs0 4);
              [exact (RO 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) |
               exact HTP]|].
      split; [intros a Ha; apply SW1; unfold scratch_k; right; exact Ha|].
      intros X0. rewrite INI in X0. discriminate.
    - exact INI.
    - exact TPE.
    - exact HERR4.
    - unfold G_RELAY_HI. lia.
    - exact RO1.
    - intros a Ha. apply IMR. unfold G_RELAY_LO, G_RELAY_HI, G_S, SRC_SIZE, SOURCES_MAX in *. lia.
    - intros a Ha. apply IML. unfold G_CLIENT, G_LISTEN, G_WAKE1 in *. lia.
    - exact IME.
    - exact IM5.
    - exists G, SRC_TABLE. split; [exact GI1|]. split; [exact GFR|]. split; [lia|].
      split; [unfold SRC_TABLE, SRC_ENTRY; lia|]. split; [intros E; apply NG; left; symmetry; exact E|].
      split.
      + intros E. destruct (Z.eq_dec (re_hp e1) 0) as [E0|E0]; [lia|].
        apply NG. right. apply in_or_app. left. rewrite E. exact (proj1 (EPH E0)).
      + intros X0. apply in_map_iff in X0 as (k & Ek & Hk). apply NG. right. apply in_or_app. left.
        rewrite <- Ek. exact (EPK k Hk).
    - clear - G3. Z.div_mod_to_equations. lia.
    - rewrite SEGS. exact S2.
    - unfold re_nheld in NHB. lia.
    - destruct HPD as [(H0 & HK)|(HI & HF & HN & H8 & HBy)]; [left; split; assumption | right].
      assert (HPn : re_hp e1 <> 0).
      { destruct (block_facts Bm MR (aa_laws API) L1 A1 m1 md1 _ _ 0 M1 HI ltac:(lia)) as (_ & Q1 & _). lia. }
      split; [exact HI|]. split; [exact HF|]. split; [unfold re_nheld in HN; exact HN|]. split; [exact H8|].
      split; [intros E; apply NOU; apply in_or_app; left; rewrite <- E; exact (proj1 (EPH HPn))|].
      split; [exact (proj2 (EPH HPn)) | exact HBy].
    - exact NDK.
    - apply Forall_forall. intros k Hk. destruct (proj1 (Forall_forall _ _) KF k Hk) as (KB & KFr & KBy & KNZ & KLn & KS).
      split; [exact KB|]. split; [exact KFr|]. split; [exact KBy|]. split; [exact KNZ|]. split; [lia|].
      split; [exact KS|]. intros E. apply NOU. apply in_or_app. left. rewrite <- E. exact (EPK k Hk).
    - exact Hcl.
    - unfold brT. destruct (send_off cl br TD); [exact Hbr | exact Hdd].
    - exact Hdd.
    - unfold eiT. destruct (send_off cl br TD); [exact Hei | left; reflexivity].
    - exact CL1.
    - exact BR1.
    - exact DD1.
    - exact EI1.
    - exact OV1.
    - exact ER1.
    - exact OD1.
    - lia.
    - exact RQ.
    - intros qc QLc. destruct (RESX qc [] QLc) as (Rs1 & Rs2 & _).
      assert (NB : nretF trBM = 0%nat) by (unfold trBM; destruct (ds_cap sDM =? 0); reflexivity).
      assert (LQ : length (qd ++ qc ++ []) = nretF trR).
      { rewrite rm_trR, !nret_app, NB, !length_app. cbn [length]. lia. }
      pose proof (ROOM (qd ++ qc ++ []) LQ) as HR. rewrite rm_trR in HR.
      unfold roomF, room_run in HR. apply room_from_app in HR as [_ HR]. apply room_from_app in HR as [HR _].
      rewrite Nat.add_0_l in HR.
      rewrite (p3c_room_res F) in HR. rewrite Rs1 in HR. rewrite <- (p3c_room_res F) in HR.
      assert (RB : p3c_run F (qd ++ qc ++ []) bnd 0 trD = runF F qd bnd trD) by exact (RX (qc ++ [])).
      rewrite RB in HR. exact HR. }
  intros c' (L2 & A2 & R2 & m2 & md2 & OUT' & CAP' & junk' & -> & RP & INI2 & (qc & QLc & RSc & LKc) & RO2 & HS2 &
    CL2 & BR2 & DD2 &
    EI2 & ER2 & BLK & LVF & LVT).
  pose proof RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
  assert (RF2 : RFr R2) by (intros r Hr; rewrite (RPr r Hr); exact (RF1 r Hr)).
  destruct (rm_rf R2 RF2) as (R2s & R28 & R29 & R218 & R219 & RO2').
  assert (HK : alloc_ceiling <= spZ R1 - GESTURES_END_K) by (rewrite HSP, K3; lia).
  set (lg := send_live cl (brT TD) dd (keys_total (re_keys e1))) in *.
  set (EG := gestures_writes lg (bv_unsigned out1) (bv_unsigned cap1) (G + 56 * Z.of_nat i)) in *.
  set (FG := fun q : Z => (lg = true /\ q = bv_unsigned out1) \/ q = re_hp e1 \/ In q (map key_addr (re_keys e1))) in *.
  assert (EGI : forall a, img_plain Bm a -> (a < G_BROKEN \/ G_BROKEN + 1 <= a) -> (a < G_EINTR \/ G_EINTR + 1 <= a) ->
                  (a < G_OUTV + 8 \/ G_OUTV + 32 <= a) -> ~ EG a).
  { intros a IP Q1 Q2 Q3 [X0|X0]; [|unfold SRC_TABLE in *; destruct (rm_fresh_sep G SRC_TABLE a (a + 1) GFR
      ltac:(unfold SRC_TABLE, SRC_ENTRY; lia) ltac:(lia) ltac:(intros x Hx; replace x with a by lia; exact (proj1 IP)));
      unfold SRC_TABLE, SRC_ENTRY in *; lia].
    destruct X0 as [X0|[X0|[X0|(LV & X0)]]]; [lia | lia | lia |].
    destruct OUTF as [C0|(OI & (F1 & F2 & F3) & _)]; [lia|]. apply (F3 (a - bv_unsigned out1)); [lia|].
    replace (bv_unsigned out1 + (a - bv_unsigned out1)) with a by lia. exact (proj1 IP). }
  assert (LOR0 : send_live cl br dd (TD + keys_total (re_keys e1)) = send_live cl br dd TD || lg)
    by exact (rma_live_or cl br dd TD (keys_total (re_keys e1)) Hcl Hbr Hdd TDN TKN).
  assert (LGK : lg = true -> keys_total (re_keys e1) <> 0).
  { intros LG Z0. unfold lg in LG. rewrite Z0 in LG. unfold send_live, send_off in LG.
    rewrite Z.eqb_refl, !orb_true_r in LG. cbn in LG. discriminate. }
  (* The chain from the start. *)
  assert (CH2 : rk_chain Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0
                  L2 A2 m2 md2).
  { apply (rk_chain_callee Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0
             L1 A1 m1 md1 GESTURES_END_K EG FG
             R1 L2 A2 R2 m2 md2 HW0 CH RP).
    - intros a Ha. unfold scratch_k in *. rewrite HSP, K3 in Ha. unfold spZ in *. rewrite K1. lia.
    - intros a Ha Hn. unfold scratch_k in *. rewrite HSP, K3 in Hn. unfold spZ in Ha. rewrite K1 in Ha. lia.
    - intros a Ha. unfold EG, gestures_writes, send_writes in Ha.
      destruct Ha as [[X0|[X0|[X0|(LV & X0)]]]|X0].
      + split; [unfold G_BROKEN in X0; lia|]. intros _. unfold Efin. left. left. exact X0.
      + split; [unfold G_EINTR in X0; lia|]. intros _. unfold Efin. left. right. left. exact X0.
      + split; [unfold G_OUTV in X0; lia|]. intros _. unfold Efin. left. right. right. left. exact X0.
      + destruct OUTF as [C0|(OI & (F1 & F2 & F3) & _)]; [lia|]. split; [lia|]. intros IM. exfalso.
        apply (F3 (a - bv_unsigned out1)); [lia|]. replace (bv_unsigned out1 + (a - bv_unsigned out1)) with a by lia.
        exact IM.
      + split; [unfold SRC_TABLE, SRC_ENTRY in *; lia|]. intros _. unfold Efin. right. right. right. left.
        unfold SRC_TABLE, SRC_ENTRY. lia.
    - intros p n Hp0 Hp1 Hn HF.
      assert (QB : In (ptr_addr L0 p, n) (blocks L0 A0)) by (apply rk_blocks_in; exists p; auto).
      destruct (rk_chain_in Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0
                  L1 A1 m1 md1 p n HW0 CH Hp0 HF)
        as [_ EA].
      assert (Q1 : In (ptr_addr L0 p, n) (blocks L1 A1)) by (apply rk_blocks_in; exists p; split; [exact EA | exact Hp1]).
      destruct (Z.eq_dec (ptr_addr L0 p) OUT) as [EO|N1].
      { (* The start output buffer, kept: no send was live. *)
        assert (LT0 : send_live cl br dd (TD + keys_total (re_keys e1)) = false).
        { destruct (send_live cl br dd (TD + keys_total (re_keys e1))) eqn:LV; [|reflexivity]. exfalso. apply HF.
          left. split; [|exact EO]. exists e. split; [exact rm_e_in|]. split; [exact HFi|]. exact LV. }
        rewrite LOR0 in LT0. apply orb_false_iff in LT0 as [LTD LGF].
        destruct (LD0 LTD) as (_ & _ & EOu & _).
        assert (OO : ptr_addr L0 p = bv_unsigned out1) by (rewrite EO, EOu; reflexivity).
        split.
        - intros [(LG & _)|[X0|X0]]; [rewrite LGF in LG; discriminate | |].
          + destruct (Z.eq_dec (re_hp e1) 0) as [E0|E0].
            * destruct (rm_blk_lo L0 A0 mem0 md0 _ _ HM0 QB). lia.
            * apply NOU. apply in_or_app. left. rewrite <- OO, X0. exact (proj1 (EPH E0)).
          + apply in_map_iff in X0 as (k & Ek & Hk). apply NOU. apply in_or_app. left. rewrite <- OO, <- Ek.
            exact (EPK k Hk).
        - intros t Ht NEf X0. unfold EG, gestures_writes, send_writes in X0.
          destruct X0 as [[X0|[X0|[X0|(LV & X0)]]]|X0].
          + apply NEf. unfold Efin. left. left. exact X0.
          + apply NEf. unfold Efin. left. right. left. exact X0.
          + apply NEf. unfold Efin. left. right. right. left. exact X0.
          + rewrite LGF in LV. discriminate.
          + apply NEf. unfold Efin. right. right. right. left. unfold SRC_TABLE, SRC_ENTRY. lia. }
      assert (N2 : ~ In (ptr_addr L0 p) (entry_blocks e))
        by (intros X0; apply HF; right; exists e; split; [exact rm_e_in|]; split; [exact HFi|]; left; exact X0).
      assert (N3 : ~ In (ptr_addr L0 p) hbi).
      { unfold hbi. destruct (Z.eqb_spec (re_eof e) 0) as [E0|E0]; [|intros []].
        intros X0. apply HF. right. exists e. split; [exact rm_e_in|]. split; [exact HFi|]. right. split; assumption. }
      destruct BF1 as (_ & _ & BF3). destruct (BF3 _ n QB Hn N1 N2 N3) as (NO1 & NE1 & _).
      destruct (block_facts Bm MR (aa_laws API) L1 A1 m1 md1 _ _ 0 M1 Q1 ltac:(lia)) as (_ & Q4 & Q5 & _).
      split.
      + intros [(_ & X0)|[X0|X0]]; [exact (NO1 X0) | |].
        * destruct (Z.eq_dec (re_hp e1) 0) as [E0|E0]; [lia|]. apply NE1. rewrite X0. exact (proj1 (EPH E0)).
        * apply in_map_iff in X0 as (k & Ek & Hk). apply NE1. rewrite <- Ek. exact (EPK k Hk).
      + intros t Ht NEf X0. unfold EG, gestures_writes, send_writes in X0.
        destruct X0 as [[X0|[X0|[X0|(LV & X0)]]]|X0].
        * destruct (block_facts Bm MR (aa_laws API) L1 A1 m1 md1 _ _ t M1 Q1 Ht) as (_ & _ & _ & _).
          apply NEf. unfold Efin. left. left. exact X0.
        * apply NEf. unfold Efin. left. right. left. exact X0.
        * apply NEf. unfold Efin. left. right. right. left. exact X0.
        * destruct OUTF as [C0|(OI & _)]; [lia|].
          destruct (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 Q1 OI NO1); lia.
        * apply NEf. unfold Efin. right. right. right. left. unfold SRC_TABLE, SRC_ENTRY. lia. }
  (* Liveness: the whole run's, drain's and gestures_end's. *)
  assert (LOR : send_live cl br dd (TD + keys_total (re_keys e1)) = send_live cl br dd TD || lg)
    by exact (rma_live_or cl br dd TD (keys_total (re_keys e1)) Hcl Hbr Hdd TDN TKN).
  assert (LFI : send_live cl br dd TD = false -> lg = true -> TD = 0)
    by exact (rma_live_first cl br dd TD (keys_total (re_keys e1)) Hcl Hbr Hdd TDN TKN).
  assert (LSE : send_live cl br dd TD = true -> lg = false -> keys_total (re_keys e1) = 0)
    by exact (rma_live_second cl br dd TD (keys_total (re_keys e1)) Hcl Hbr Hdd TDN TKN).
  clearbody lg.
  assert (LGD : lg = true \/ lg = false) by (destruct lg; auto).
  unfold brT, eiT in BR2, EI2.
  rewrite (rma_off_br cl br dd TD (keys_total (re_keys e1)) Hcl Hbr Hdd TDN TKN) in BR2.
  rewrite (rma_off_ei cl br dd ei TD (keys_total (re_keys e1)) Hcl Hbr Hdd TDN TKN) in EI2.
  (* Block facts. *)
  assert (GO1 : G <> bv_unsigned out1) by (intros E; apply NG; left; symmetry; exact E).
  assert (OG1 : bv_unsigned out1 <> G) by (intros E; apply NG; left; exact E).
  assert (GE1 : ~ In G (entry_blocks e1)) by (intros X0; apply NG; right; apply in_or_app; left; exact X0).
  assert (GH1 : ~ In G (hbo h1)) by (intros X0; apply NG; right; apply in_or_app; right; exact X0).
  assert (OE1 : ~ In (bv_unsigned out1) (entry_blocks e1)) by (intros X0; apply NOU; apply in_or_app; left; exact X0).
  assert (EBP : forall q, In q (entry_blocks e1) -> exists k, 0 < k /\ In (q, k) (blocks L1 A1))
    by exact (rm_eb_pos L1 A1 m1 e1 EK1).
  assert (HPN : forall q m, In (q, m) (blocks L1 A1) -> ~ In q (entry_blocks e1) -> q <> re_hp e1).
  { intros q m Hq Hn E. destruct (Z.eq_dec (re_hp e1) 0) as [E0|E0].
    - destruct (rm_blk_lo L1 A1 m1 md1 q m M1 Hq). lia.
    - apply Hn. rewrite E. exact (proj1 (EPH E0)). }
  assert (KYN : forall q, ~ In q (entry_blocks e1) -> ~ In q (map key_addr (re_keys e1))).
  { intros q Hn X0. apply in_map_iff in X0 as (k & Ek & Hk). apply Hn. rewrite <- Ek. exact (EPK k Hk). }
  assert (NEB : forall q m, In (q, m) (blocks L1 A1) -> q <> bv_unsigned out1 -> ~ In q (entry_blocks e1) ->
                  In (q, m) (blocks L2 A2)).
  { intros q m Hq HO Hn. apply (proj2 (BLK q m)). left. split; [exact Hq|]. split; [exact HO|].
    split; [exact (HPN q m Hq Hn) | exact (KYN q Hn)]. }
  assert (FGN : forall q m, In (q, m) (blocks L1 A1) -> q <> bv_unsigned out1 -> ~ In q (entry_blocks e1) -> ~ FG q).
  { intros q m Hq HO Hn X0. unfold FG in X0. destruct X0 as [(_ & X0)|[X0|X0]];
      [exact (HO X0) | exact (HPN q m Hq Hn X0) | exact (KYN q Hn X0)]. }
  assert (FGG : ~ FG G) by exact (FGN G SRC_TABLE GI1 GO1 GE1).
  assert (EGB : forall q k a, In (q, k) (blocks L1 A1) -> q <> G -> (lg = true -> q <> bv_unsigned out1) ->
                  q <= a < q + k -> ~ EG a).
  { intros q k a Hq HG HO Ha. destruct (rm_blk_noimg L1 A1 m1 md1 q k a M1 Hq Ha) as (NI & Q1 & Q2).
    unfold EG, gestures_writes, send_writes. intros [[X0|[X0|[X0|(LV & X0)]]]|X0].
    - exact (NI (proj1 (IMR a ltac:(unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - exact (NI (proj1 (IMR a ltac:(unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - exact (NI (proj1 (IMR a ltac:(unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - destruct OD1 as [(C0 & _)|(_ & _ & OI & _)]; [lia|].
      destruct (blocks_disjoint Bm API L1 A1 m1 md1 q k _ _ M1 Hq OI (HO LV)); lia.
    - destruct (blocks_disjoint Bm API L1 A1 m1 md1 q k G SRC_TABLE M1 Hq GI1 HG); unfold SRC_TABLE, SRC_ENTRY in *;
        lia. }
  assert (EGG : forall a, G <= a < G + 896 -> (a < SA + 40 \/ SA + 52 <= a) -> ~ EG a).
  { intros a Ha Hs. pose proof GFR as (GF1 & GF2 & GF3).
    assert (NI : ~ in_img Bm a) by (replace a with (G + (a - G)) by lia; apply GF3; unfold SRC_TABLE, SRC_ENTRY; lia).
    unfold EG, gestures_writes, send_writes. intros [[X0|[X0|[X0|(LV & X0)]]]|X0].
    - exact (NI (proj1 (IMR a ltac:(unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - exact (NI (proj1 (IMR a ltac:(unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - exact (NI (proj1 (IMR a ltac:(unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - destruct OD1 as [(C0 & _)|(_ & _ & OI & _)]; [lia|].
      destruct (blocks_disjoint Bm API L1 A1 m1 md1 G SRC_TABLE _ _ M1 GI1 OI GO1); unfold SRC_TABLE, SRC_ENTRY in *;
        lia.
    - lia. }
  assert (EGH : forall a, alloc_ceiling <= a -> ~ EG a).
  { intros a Ha. unfold EG, gestures_writes, send_writes. intros [[X0|[X0|[X0|(LV & X0)]]]|X0];
      [unfold G_BROKEN in X0; lia | unfold G_EINTR in X0; lia | unfold G_OUTV in X0; lia | | lia].
    destruct OD1 as [(C0 & _)|(_ & _ & _ & (F1 & F2 & _) & _)]; lia. }
  assert (TG : forall A cs, rw_cells segs m1 A cs ->
            (forall k, 0 <= k < Z.of_nat (cells_size cs) -> img_plain Bm (A + k) /\
               (A + k < G_BROKEN \/ G_BROKEN + 1 <= A + k) /\ (A + k < G_EINTR \/ G_EINTR + 1 <= A + k) /\
               (A + k < G_OUTV + 8 \/ G_OUTV + 32 <= A + k)) -> rw_cells segs m2 A cs).
  { intros A cs H KK. apply (rm_rp_img _ _ _ _ _ _ _ _ _ _ _ _ _ A cs M1 RP HK H). intros k Hk.
    destruct (KK k Hk) as (J1 & J2 & J3 & J4). split; [exact J1 | exact (EGI _ J1 J2 J3 J4)]. }
  assert (SRm2 : rw_cells segs m2 G_SRC [C8 (Z_to_bv 64 G)]) by (apply TG; [exact SR1 | rm_tg]).
  assert (BUFm2 : bytes_at rsegs m2 (SA + 16) (le8 (Z_to_bv 64 (re_buf e1)))).
  { rewrite <- SEGS. rewrite <- SEGS in S4.
    apply (rm_rp_bb _ _ _ _ _ _ _ _ _ _ _ _ _ G SRC_TABLE (SA + 16) _ M1 RP FGG GI1);
      [lia | rewrite length_le8; unfold SRC_TABLE, SRC_ENTRY; lia | | exact S4].
    intros t Ht. rewrite length_le8 in Ht. apply EGG; lia. }
  pose proof (bv_unsigned_in_range 64 nout) as RN0. change (bv_modulus 64) with (2 ^ 64) in RN0.
  first [rewrite RA1 | assert (RA1' : PropExec.getr R1 1 = Z_to_bv 64 0x13fe0) by exact RA1; rewrite RA1'].
  rewrite SEGS.
  eapply rm_bridge0; [exact Hh2 | exact Hl2 | | | ].
  { rewrite rm_mkR_of, R218, R219.
    eapply rm_segg with (G := G) (B := re_buf e1) (i := i); [lia | exact rm_g8 | lia | lia | | ].
    - apply rm_rd8. rewrite SEGS in SRm2. pose proof (rm_rw_bytes _ _ _ _ SRm2) as B.
      cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
    - apply rm_rd8. exact BUFm2. }
  2: { intros s0 HQ0. cbv beta in HQ0. subst s0. do 2 eexists. reflexivity. }
  intros R0 pc0 R3 HQ X3. cbv beta in HQ. injection HQ as ER0 Epc. subst R0 pc0.
  apply SR_ret. replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  exists L2, A2, R3, m2, md2, e1, h1, (if lg then OUT' else bv_unsigned out1), (if lg then CAP' else bv_unsigned cap1),
    (if lg then junk' else junk1), LB, (P40 e1 ++ le8 (Z_to_bv 64 0) ++ le4 (Z_to_bv 64 0) ++ re_pad2 e1).
  split; [reflexivity|].
  split.
  { intros r Hr. pose proof Hr as Hr'. unfold callee_saved in Hr'.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]]]; subst r;
      match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X3 eq_refl) end; simp_regs;
      first [ exact (RF2 _ Hr) | unfold rval; reflexivity ]. }
  split; [match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X3 eq_refl) end; simp_regs; reflexivity|].
  split; [match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X3 eq_refl) end; simp_regs; reflexivity|].
  split; [exact CH2|].
  split; [exact INI2|].
  split; [exact RO2|].
  split.
  { exists (qd ++ qc).
    destruct (RESX qc [] QLc) as (Rs1 & Rs2 & Rs3). rewrite app_nil_r in Rs1, Rs3.
    assert (NB : nretF trBM = 0%nat) by (unfold trBM; destruct (ds_cap sDM =? 0); reflexivity).
    split; [rewrite rm_trR, !nret_app, NB, length_app; lia|].
    split.
    { unfold runF, run_tr. rewrite run_from_app. rewrite Nat.add_0_l.
      assert (RB : p3c_run F (qd ++ qc) bnd 0 trD = runF F qd bnd trD) by exact (RX qc).
      rewrite RB. rewrite p3c_run_res, Rs1, <- p3c_run_res. exact RSc. }
    split; [symmetry; exact CPX|].
    assert (RQX : forall a, rm_ab (length qd) a -> resolveF (qd ++ qc) a = resolveF qd a)
      by (intros a Ha; exact (rm_ab_res _ qd qc a Ha eq_refl)).
    pose proof DAB as (DAo & DAb & DAh & DAk & DAp & DAe & DAr).
    assert (MV : forall p a n, live_at L1 A1 p a n -> 0 < n -> ~ FG a -> live_at L2 A2 p a n)
      by (intros p a n Hl0 Hn0 HF0; exact (p3c_rp_live Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP Hl0 Hn0 HF0)).
    assert (OBL : 0 < bv_unsigned cap1 -> 4096 <= bv_unsigned out1).
    { intros CP0. destruct OD1 as [(C0 & _)|(_ & _ & OI & _)]; [lia|].
      destruct (rm_blk_lo L1 A1 m1 md1 _ _ M1 OI). lia. }
    split.
    { intros CP. rewrite (RQX _ DAb). apply MV; [exact (ELb CP) | exact CP |].
      destruct (EPB ltac:(lia)) as (EB1 & EB2 & EB3).
      intros [(_ & X0)|[X0|X0]].
      - apply NOU. apply in_or_app. left. rewrite <- X0. exact EB1.
      - destruct (Z.eq_dec (re_hp e1) 0) as [H0|H0]; [|exact (EB2 H0 X0)].
        destruct BUFD as [(C0 & _)|(_ & BI & _)]; [lia|].
        destruct (rm_blk_lo L1 A1 m1 md1 _ _ M1 BI). lia.
      - exact (EB3 X0). }
    split.
    { intros LTv. destruct LGD as [LGT|LGF].
      - rewrite LGT. destruct (LVT LGT) as (LV1 & LV2 & _). pose proof (LGK LGT) as KZ.
        rewrite Rs3 by (rewrite <- LV2; lia). exact (LKc LGT).
      - rewrite LGF. cbv iota. rewrite LOR, LGF, orb_false_r in LTv.
        pose proof (rma_keys_total_zero _ (LSE LTv LGF)) as KN.
        assert (OE : outR = da_out a1M) by (rewrite OR, XKS, KN; reflexivity).
        assert (TD0 : TD <> 0).
        { intros T0. rewrite T0 in LTv. unfold send_live, send_off in LTv. rewrite Z.eqb_refl, !orb_true_r in LTv.
          cbn in LTv. discriminate. }
        assert (CN : bv_unsigned cap1 <> 0).
        { intros C0. destruct (LD1 LTv) as (N1 & _).
          destruct OD1 as [(_ & _ & N0 & _)|(Cp & _)]; lia. }
        rewrite OE, (RQX _ DAo). apply MV; [exact (LOd CN) | lia |].
        intros [(LG & _)|[X0|X0]]; [rewrite LGF in LG; discriminate | |].
        + destruct (Z.eq_dec (re_hp e1) 0) as [E0|E0]; [pose proof (OBL ltac:(lia)); lia|].
          apply NOU. apply in_or_app. left. rewrite X0. exact (proj1 (EPH E0)).
        + apply in_map_iff in X0 as (k & Ek & Hk). apply NOU. apply in_or_app. left. rewrite <- Ek.
          exact (EPK k Hk). }
    intros E0. apply (rm_sl_ext L2 A2 qd qc L0 A0 a1M h1 DAB).
    apply (rm_sl_mono L1 A1 L2 A2 qd nm0 a1M h1); [|exact (SLs E0)].
    assert (HBO : hbo h1 = hs_blocks h1) by (unfold hbo; rewrite (proj2 (Z.eqb_eq _ _) E0); reflexivity).
    intros p a n Hl0 Hn0 Ha. apply MV; [exact Hl0 | exact Hn0 |].
    assert (AB : In (a, n) (blocks L1 A1)).
    { destruct Hl0 as [Hin Hpa]. apply rk_blocks_in. exists p. split; [exact Hpa | exact Hin]. }
    destruct (rm_blk_lo L1 A1 m1 md1 _ _ M1 AB) as (A4 & _).
    intros [(_ & X0)|[X0|X0]].
    + apply NOU. apply in_or_app. right. rewrite HBO, <- X0. exact Ha.
    + destruct (Z.eq_dec (re_hp e1) 0) as [H0|H0]; [lia|].
      exact (rm_nd_app _ _ _ NDs (proj1 (EPH H0)) ltac:(rewrite HBO, <- X0; exact Ha)).
    + apply in_map_iff in X0 as (k & Ek & Hk).
      exact (rm_nd_app _ _ _ NDs (EPK k Hk) ltac:(rewrite HBO, Ek; exact Ha)). }
  split.
  { destruct FR1 as (jf & FR1). exists jf.
    apply (rm_rp_hi _ _ _ _ _ _ _ _ _ _ _ _ _ (SP - 48) _ M1 RP); [rewrite HSP; lia | cbn [cells_size csize]; lia |
      lia | lia | | exact FR1].
    intros k Hk. apply EGH. lia. }
  split.
  { unfold GLB.
    split; [apply TG; [exact LK1 | rm_tg]|].
    split.
    { apply (rm_rp_imgb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RP HK WK1). intros k Hk. rewrite length_le4 in Hk.
      assert (IP : img_plain Bm (G_WAKE1 + k)) by (apply IML; unfold G_WAKE1, G_LISTEN; lia).
      split; [exact IP|]. apply EGI; [exact IP | unfold G_WAKE1, G_BROKEN; lia | unfold G_WAKE1, G_EINTR; lia |
        unfold G_WAKE1, G_OUTV; lia]. }
    split; [apply TG; [exact NS1 | rm_tg]|].
    split; [exact SRm2|].
    split; [exact CL2|].
    split; [exact BR2|].
    split; [exact DD2|].
    split; [exact EI2 | exact ER2]. }
  split; [rewrite !length_app, (rm_P40_len e1 P1), length_le8, length_le4, P2; reflexivity|].
  split.
  { pose proof rm_tlen as (TL1 & TL2).
    assert (ST1 : rw_cells segs m2 G [CB (length Tpre) Tpre]).
    { apply (rm_rp_bc _ _ _ _ _ _ _ _ _ _ _ _ _ G SRC_TABLE G _ M1 RP FGG GI1);
        [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia | | rewrite SEGS; exact T1].
      intros t Ht. cbn [cells_size csize] in Ht. apply EGG; lia. }
    assert (ST3 : rw_cells segs m2 (SA + 56) [CB (length Tpost) Tpost]).
    { apply (rm_rp_bc _ _ _ _ _ _ _ _ _ _ _ _ _ G SRC_TABLE (SA + 56) _ M1 RP FGG GI1);
        [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia | | rewrite SEGS; exact T3].
      intros t Ht. cbn [cells_size csize] in Ht. apply EGG; lia. }
    assert (SS1 : rw_cells segs m2 SA [CB 40 (P40 e1)]).
    { apply (rm_rp_bc _ _ _ _ _ _ _ _ _ _ _ _ _ G SRC_TABLE SA _ M1 RP FGG GI1);
        [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia | | rewrite SEGS; exact S1].
      intros t Ht. cbn [cells_size csize] in Ht. apply EGG; lia. }
    assert (SS3 : rw_cells segs m2 (SA + 52) [CB 4 (re_pad2 e1)]).
    { apply (rm_rp_bc _ _ _ _ _ _ _ _ _ _ _ _ _ G SRC_TABLE (SA + 52) _ M1 RP FGG GI1);
        [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia | | rewrite SEGS; exact S3].
      intros t Ht. cbn [cells_size csize] in Ht. apply EGG; lia. }
    rewrite SEGS in ST1, ST3, SS1, SS3, HS2. rewrite SEGS.
    apply rm_tjoin3.
    - rewrite !length_app, (rm_P40_len e1 P1), length_le8, length_le4, P2. reflexivity.
    - lia.
    - exact ST1.
    - replace (G + Z.of_nat (length Tpre)) with (G + 56 * Z.of_nat i) by lia.
      exact (rm_slot_join m2 _ e1 P1 P2 SS1 HS2 SS3).
    - replace (G + Z.of_nat (length Tpre) + 56) with (G + 56 * Z.of_nat i + 56) by lia. exact ST3. }
  split; [exact (NEB G SRC_TABLE GI1 GO1 GE1)|].
  split.
  { intros E0. pose proof (DF1 E0) as D1. destruct (SRCP e rm_e_in HFi E0) as (_ & _ & Hj & _).
    assert (HBE : hbo h1 = hs_blocks h1) by (unfold hbo; rewrite (proj2 (Z.eqb_eq _ _) E0); reflexivity).
    split; [|rewrite <- HBE; exact GH1].
    apply (rm_DF_kept L1 A1 m1 L2 A2 m2 h1 (re_keys e1) Hj D1).
    - intros a Ha. unfold G_S in Ha.
      assert (IP : img_plain Bm a) by (apply IMR; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia).
      apply (rm_rp_kb _ _ _ _ _ _ _ _ _ _ _ _ _ a M1 RP HK IP).
      apply EGI; [exact IP | unfold G_BROKEN; lia | unfold G_EINTR; lia | unfold G_OUTV; lia].
    - intros q Hq.
      assert (QO : q <> bv_unsigned out1) by (intros E; apply NOU; apply in_or_app; right; rewrite HBE, <- E; exact Hq).
      assert (QE : ~ In q (entry_blocks e1)) by (intros X0; apply (rm_nd_app _ _ _ NDs X0); rewrite HBE; exact Hq).
      assert (QG : q <> G) by (intros E; apply GH1; rewrite HBE, <- E; exact Hq).
      destruct (rm_hs_pos L1 A1 m1 h1 (proj1 D1) q Hq) as (k0 & Kp & Qk).
      apply (rk_rp_bkept Bm API _ _ _ L1 A1 R1 m1 md1 L2 A2 R2 m2 md2 q M1 RP); [exact (FGN q k0 Qk QO QE)|].
      intros k t Hqk Ht. apply (EGB q k (q + t) Hqk QG (fun _ => QO)). lia. }
  split; [exact K11|].
  split; [exact LB1|].
  split.
  { unfold BF. destruct BF1 as (BF1a & BF1b & BF1c). split; [|split].
    - intros q m Hq HO HE HH. pose proof (BF1a q m Hq HO HE HH) as Q1.
      destruct (Z_lt_le_dec 0 m) as [Mp|Mn].
      + destruct (BF1c q m Hq Mp HO HE HH) as (Q2 & Q3 & _). exact (NEB q m Q1 Q2 Q3).
      + pose proof (rma_nodup_std _ (HND _ _ _ _ M1)) as NDL.
        apply NEB; [exact Q1 | |].
        * intros E. destruct OD1 as [(C0 & O0 & _)|(Cp & _ & OI & _)].
          -- destruct (rm_blk_lo L1 A1 m1 md1 q m M1 Q1). lia.
          -- rewrite <- E in OI. pose proof (rk_nodup_fst (blocks L1 A1) q m (bv_unsigned cap1) NDL Q1 OI). lia.
        * intros X0. destruct (EBP q X0) as (k0 & Kp & Qk).
          pose proof (rk_nodup_fst (blocks L1 A1) q m k0 NDL Q1 Qk). lia.
    - intros q m Hq. destruct (proj1 (BLK q m) Hq) as [(Q1 & QO & QH & QK)|[(LG & -> & ->)|(LG & Cp & -> & ->)]].
      + destruct (BF1b q m Q1) as [X0|[X0|X0]]; [left; exact X0 | | exfalso; exact (QO X0)].
        right. left. apply in_app_iff in X0 as [X0|X0]; apply in_app_iff; [left | right; exact X0].
        unfold entry_blocks in X0. rewrite !in_app_iff in X0. destruct X0 as [X0|[X0|X0]].
        * unfold bufl. exact X0.
        * exfalso. apply QH. revert X0. destruct (Z.eqb_spec (re_hp e1) 0); intros X0; [destruct X0|].
          destruct X0 as [<-|[]]. reflexivity.
        * exfalso. exact (QK X0).
      + right. right. rewrite LG. reflexivity.
      + right. right. rewrite LG. reflexivity.
    - intros q m Hq Mp HO HE HH. destruct (BF1c q m Hq Mp HO HE HH) as (Q2 & Q3 & Q4).
      split; [|split; [exact Q3 | exact Q4]].
      pose proof (BF1a q m Hq HO HE HH) as Q1.
      destruct LGD as [LG|LG]; rewrite LG; cbv iota; [|exact Q2].
      destruct (LVT LG) as (_ & _ & _ & QN & _). exact (QN q m Q1 Q2 (HPN q m Q1 Q3) (KYN q Q3) Mp). }
  split.
  { intros E0. pose proof (DF1 E0) as D1.
    assert (HBE : hbo h1 = hs_blocks h1) by (unfold hbo; rewrite (proj2 (Z.eqb_eq _ _) E0); reflexivity).
    assert (NDH : List.NoDup (hs_blocks h1)) by (rewrite <- HBE; exact (List.NoDup_app_remove_l _ _ NDs)).
    apply rma_nodup_of_std. constructor; [|exact NDH].
    destruct LGD as [LG|LG]; rewrite LG; cbv iota.
    - intros Hq. destruct (rm_hs_pos L1 A1 m1 h1 (proj1 D1) OUT' Hq) as (k0 & Kp & Qk).
      assert (QO : OUT' <> bv_unsigned out1) by (intros E; apply NOU; apply in_or_app; right; rewrite HBE, <- E; exact Hq).
      assert (QE : ~ In OUT' (entry_blocks e1)) by (intros X0; apply (rm_nd_app _ _ _ NDs X0); rewrite HBE; exact Hq).
      destruct (LVT LG) as (_ & _ & _ & QN & _). exact (QN OUT' k0 Qk QO (HPN _ _ Qk QE) (KYN _ QE) Kp eq_refl).
    - intros Hq. apply NOU. apply in_or_app. right. rewrite HBE. exact Hq. }
  split.
  { unfold LF. split.
    - intros LA. rewrite LOR in LA. apply orb_false_iff in LA as [LDf LGf].
      destruct (LD0 LDf) as (EN & EC & EO & EOo & EJ).
      rewrite LGf. cbv iota.
      split; [rewrite <- EN, <- EC, <- EO; exact (LVF LGf)|].
      split; [|rewrite EO; reflexivity].
      intros Cp. rewrite <- EC in Cp. rewrite <- EO, <- EC.
      destruct OD1 as [(C0 & _)|(_ & NL & OI & _ & OB & LO & LJ)]; [lia|].
      split; [apply (proj2 (BLK _ _)); right; right; split; [exact LGf | split; [exact Cp | split; reflexivity]]|].
      rewrite <- EOo, <- EJ.
      apply (rm_rp_bb _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned out1) (bv_unsigned cap1) _ _ M1 RP);
        [ | exact OI | lia | rewrite length_app; lia | | exact OB].
      + intros X0. unfold FG in X0. destruct X0 as [(LL & _)|[X0|X0]]; [rewrite LGf in LL; discriminate | |].
        * exact (HPN _ _ OI OE1 X0).
        * exact (KYN _ OE1 X0).
      + intros t Ht. rewrite length_app in Ht. apply (EGB _ _ _ OI OG1); [intros LL; congruence | lia].
    - intros LA. destruct LGD as [LG|LG].
      + assert (NO1F : bv_unsigned nout1 = NO + TD /\ O1 = O ++ LB).
        { destruct (send_live cl br dd TD) eqn:LD.
          - exact (LD1 eq_refl).
          - pose proof (LFI eq_refl LG) as TD0. destruct (LD0 eq_refl) as (EN & _ & _ & EOo & _).
            assert (LL0 : length LB = 0%nat).
            { pose proof (f_equal (@length Z) LB1) as LL. unfold bzs in LL. rewrite length_map in LL.
              unfold TD in TD0. lia. }
            apply length_zero_iff_nil in LL0. rewrite LL0, app_nil_r.
            split; [rewrite EN; lia | exact EOo]. }
        destruct (LVT LG) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). destruct NO1F as (NO1E & O1E).
        rewrite LG. cbv iota.
        split; [lia|].
        split; [rewrite Q2; exact (CAPF LA)|].
        split; [apply (proj2 (BLK _ _)); right; left; split; [exact LG | split; reflexivity]|].
        split; [exact Q3|].
        split; [rewrite O1E, <- !app_assoc in Q5; exact Q5|].
        split; [lia|].
        rewrite NO1E in Q7.
        replace (NO + TD + keys_total (re_keys e1)) with (NO + (TD + keys_total (re_keys e1))) in Q7 by lia.
        exact Q7.
      + assert (LDt : send_live cl br dd TD = true) by (rewrite LOR, LG, orb_false_r in LA; exact LA).
        pose proof (LSE LDt LG) as KT0. pose proof (rma_keys_total_zero _ KT0) as KS0.
        destruct (LD1 LDt) as (NO1E & O1E).
        assert (TDp : 0 < TD).
        { destruct (Z.eq_dec TD 0) as [E|E]; [|lia]. exfalso. rewrite E in LDt.
          unfold send_live, send_off in LDt. rewrite Z.eqb_refl, !orb_true_r in LDt. cbn in LDt. discriminate. }
        rewrite LG. cbv iota. rewrite KT0.
        destruct OD1 as [(C0 & O0 & N0 & OE)|(Cp & NL & OI & OF & OB & LO & LJ)]; [lia|].
        split; [lia|].
        split; [rewrite <- (CAPF LA), LG; symmetry; apply fi_gec_false|].
        split; [apply (proj2 (BLK _ _)); right; right; split; [exact LG | split; [exact Cp | split; reflexivity]]|].
        split; [exact OF|].
        split.
        { rewrite KS0. change (keys_out []) with (@nil byte). cbn [app]. rewrite app_assoc, <- O1E.
          apply (rm_rp_bb _ _ _ _ _ _ _ _ _ _ _ _ _ (bv_unsigned out1) (bv_unsigned cap1) _ _ M1 RP);
            [ | exact OI | lia | rewrite length_app; lia | | exact OB].
          - intros X0. unfold FG in X0. destruct X0 as [(LL & _)|[X0|X0]]; [rewrite LG in LL; discriminate | |].
            + exact (HPN _ _ OI OE1 X0).
            + exact (KYN _ OE1 X0).
          - intros t Ht. rewrite length_app in Ht. apply (EGB _ _ _ OI OG1); [intros LL; congruence | lia]. }
        split; [lia|].
        rewrite !Z_to_bv_bv_unsigned. replace (NO + (TD + 0)) with (bv_unsigned nout1) by lia.
        rewrite Z_to_bv_bv_unsigned. exact (LVF LG). }
  destruct BUFD as [(C0 & B0 & _)|(Cp & BI & _)]; [left; split; assumption | right].
  destruct (EPB ltac:(lia)) as (BE & BH & BK).
  assert (BO1 : re_buf e1 <> bv_unsigned out1) by (intros E; apply NOU; apply in_or_app; left; rewrite <- E; exact BE).
  assert (BG : re_buf e1 <> G) by (intros E; apply NG; right; apply in_or_app; left; rewrite <- E; exact BE).
  assert (BNH : re_buf e1 <> re_hp e1).
  { destruct (Z.eq_dec (re_hp e1) 0) as [E0|E0]; [|exact (BH E0)].
    destruct (rm_blk_lo _ _ _ _ _ _ M1 BI). lia. }
  split; [exact Cp|].
  split; [apply (proj2 (BLK _ _)); left; split; [exact BI | split; [exact BO1 | split; [exact BNH | exact BK]]]|].
  split; [exact BG|].
  split.
  { destruct LGD as [LG|LG]; rewrite LG; cbv iota; [|exact BO1].
    destruct (LVT LG) as (_ & _ & _ & QN & _). exact (QN _ _ BI BO1 BNH BK Cp). }
  split.
  { intros LA. rewrite LOR in LA. apply orb_false_iff in LA as [LDf _].
    destruct (LD0 LDf) as (_ & _ & EO & _). rewrite <- EO. exact BO1. }
  intros X0. exact (rm_nd_app _ _ _ NDs BE X0).
Qed.

(* What the head writes: its frame and the lock's second word. *)
Definition W1 : list (Z * Z) := [(SP - 48, SP); (203004, 203008)].

(* After the search, at the call of drain (s->eof = 0) or of gestures_end (s->eof = 1), with the lock held. *)
Definition AtH (c : config) : Prop :=
  exists R1 m1,
    c = mkCfg (YK11.mkst R1 (Z_to_bv 64 (if re_eof e =? 0 then DRAIN else GESTURES_END)) m1 (seg_rom segs)) md0 /\
    RFr R1 /\ getr R1 1 = Z_to_bv 64 (if re_eof e =? 0 then 0x13fbc else 0x13fe0) /\ getr R1 10 = Z_to_bv 64 SA /\
    munch W1 mem0 m1 /\ wmono rsegs mem0 m1 /\ ro_agree segs m1 /\ FRM m1 /\
    rw_cells segs m1 G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0)].

Lemma rm_W1_img : forall a, img_plain Bm a -> (a < 203004 \/ 203008 <= a) -> outside W1 a.
Proof using Hi O PRE SEGS junk.
  intros a IP Ha. pose proof (in_img_low Bm SEGS _ (proj1 IP)) as IL.
  pose proof rm_pre as (_ & _ & _ & _ & _ & HCE & _ & _ & _ & _ & _ & _ & AC).
  unfold W1. cbn [outside]. lia.
Qed.

Lemma rm_W1_err : forall a, ERR <= a < ERR + 4 -> outside W1 a.
Proof using EHI GFR GIN Hi IME IML IMR O PRE SEGS junk.
  intros a Ha. pose proof rm_sf as (E1 & E2 & _).
  pose proof rm_pre as (_ & _ & _ & _ & _ & HCE & _ & _ & _ & _ & _ & _ & AC).
  unfold W1. cbn [outside]. lia.
Qed.

Lemma rm_W1_blk : forall q k a, In (q, k) (blocks L0 A0) -> q <= a < q + k -> outside W1 a.
Proof using AX Hi IMR O PRE junk.
  intros q k a Hq Ha. pose proof rm_pre as (HM0 & _ & _ & _ & _ & HCE & _ & _ & _ & _ & _ & _ & AC).
  destruct (rm_blk_noimg L0 A0 mem0 md0 q k a HM0 Hq Ha) as (NI & Q1 & Q2).
  assert (N2 : a < 203004 \/ 203008 <= a).
  { destruct (Z_lt_le_dec a 203004) as [X1|X1]; [left; exact X1|].
    destruct (Z_lt_le_dec a 203008) as [X2|X2]; [|right; exact X2].
    exfalso. apply NI. apply (proj1 (IMR a ltac:(unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia))). }
  unfold W1. cbn [outside]. lia.
Qed.

Lemma rm_h_cells : forall m1 A cs, munch W1 mem0 m1 -> wmono rsegs mem0 m1 -> rw_cells segs mem0 A cs ->
  (forall j, 0 <= j < Z.of_nat (cells_size cs) -> outside W1 (A + j)) -> rw_cells segs m1 A cs.
Proof using SEGS. intros m1 A cs MU WM H HO. rewrite SEGS in H |- *. exact (rm_mu_cells W1 mem0 m1 A cs H MU WM HO). Qed.

Lemma rm_h_bytes : forall m1 A bs, munch W1 mem0 m1 -> bytes_at segs mem0 A bs ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> outside W1 (A + j)) -> bytes_at segs m1 A bs.
Proof using SEGS. intros m1 A bs MU H HO. rewrite SEGS in H |- *. exact (rm_mu_bytes W1 mem0 m1 A bs H MU HO). Qed.

Lemma rm_h_kb : forall m1 a, munch W1 mem0 m1 -> wmono rsegs mem0 m1 -> 0 <= a < 2 ^ 64 -> outside W1 a ->
  rk_kb2 Bm mem0 m1 a.
Proof using SEGS. intros m1 a MU WM Ha HO. apply (rk_mu_kb2 Bm W1 mem0 m1 a MU); [rewrite SEGS; exact WM | exact Ha | exact HO]. Qed.

Lemma rm_h_bkept : forall m1 q, munch W1 mem0 m1 -> wmono rsegs mem0 m1 -> rk_bkept Bm L0 A0 mem0 L0 A0 m1 q.
Proof using AX Hi IMR O PRE SEGS junk.
  intros m1 q MU WM. pose proof rm_pre as (HM0 & _).
  apply (rk_mu_bkept Bm API L0 A0 W1 mem0 m1 md0 q HM0 MU); [rewrite SEGS; exact WM|].
  intros k t Hq Ht. apply (rm_W1_blk q k (q + t) Hq). lia.
Qed.

Lemma rm_h_chain : forall (Fq : Z -> Prop) m1, munch W1 mem0 m1 -> wmono rsegs mem0 m1 ->
  rk_chain Bm API RELAY_REMOVE_K Efin Fq L0 A0 regs0 mem0 md0 L0 A0 m1 md0.
Proof using AX Hi IMR O PRE SEGS junk.
  intros Fq m1 MU WM. pose proof rm_pre as (HM0 & HW0 & HB0 & HRA & HAL & HCE & H63 & HWS & HTP & HER & Hh & Hl & AC).
  eapply (rk_chain_munch Bm API AX SEGS); [ | exact MU | rewrite SEGS; exact WM | ].
  - apply (rk_chain_refl Bm API); [exact HM0 | exact HW0 | exact HB0 |].
    intros a [Ha|Ha]; [apply HWS; unfold spZ in Ha; rewrite (proj1 rm_K) in Ha; lia | apply HER; exact Ha].
  - intros x Hx NO. destruct (rm_not_out _ _ NO) as (lo & hi & Hin & Hr). unfold W1 in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-.
    + left. split; [unfold scratch_k, spZ; rewrite (proj1 rm_K); left; lia | lia].
    + right. split; [unfold Efin; right; left; unfold G_LOCK; lia|].
      left. apply IMR. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX. lia.
Qed.

Lemma rm_tab_split : concat (map entry_bytes es) ++ tail = Tpre ++ entry_bytes e ++ Tpost.
Proof using Hi.
  unfold Tpre, Tpost. rewrite (rma_split_nth es no_entry i Hi) at 1. rewrite map_app, concat_app.
  cbn [map concat]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma rm_reslack : forall m1, munch W1 mem0 m1 -> wmono rsegs mem0 m1 -> MR L0 A0 m1 md0 ->
  exists ks, map fst ks = map fst (re_keys e) /\ entry_ok Bm L0 A0 m1 (rk_with_keys e ks).
Proof using AX BSP EOK Hi IMR O PRE SEGS junk.
  intros m1 MU WM M1.
  refine (rk_entry_okk_kept Bm API BSP L0 A0 mem0 L0 A0 m1 md0 e _ M1 _).
  - apply rk_entry_okk_of. exact (proj1 (Forall_forall _ _) EOK e rm_e_in).
  - intros q _. exact (rm_h_bkept m1 q MU WM).
Qed.

Lemma rm_noeof : forall c, AtH c -> re_eof e <> 0 -> AtG c.
Proof using AX BSP CBR CCL CDD CEI CER CNS COV CSR CWK EHI EOK GFR GIN HFi HND Hi IME IML IMR INIT NDB OUTD PRE RES SEGS TAB.
  intros c (R1 & m1 & -> & RF1 & RA1 & R10 & MU & WM & RO1 & FR1 & LK1) HE.
  pose proof rm_pre as (HM0 & HW0 & HB0 & HRA & HAL & HCE & H63 & HWS & HTP & HER & Hh & Hl & AC).
  pose proof rm_sf as (E1 & E2 & G1 & G2 & G3 & G4 & G5 & G6).
  pose proof (rm_h_chain (Ffin 0) m1 MU WM) as CH0. pose proof CH0 as (M1 & _).
  pose proof (proj1 (Forall_forall _ _) EOK e rm_e_in) as EOKe.
  pose proof EOKe as (EOF0 & SK0 & P10 & P20 & FDR0 & CAPV0 & UL0 & UB0 & UNZ0 & BUFD0 & NHB0 & HPD0 & NDK0 & NDT0 & KF0).
  rm_hide.
  destruct (rm_reslack m1 MU WM M1) as (ks & Eks & OK1).
  destruct (rk_map_fst_keys (re_keys e) ks Eks) as (EA & ET & EL & EP & EX).
  assert (HEf : (re_eof e =? 0) = false) by (apply Z.eqb_neq; exact HE).
  assert (TD0 : TD = 0) by (unfold TD, Lsi; rewrite HEf; reflexivity).
  assert (TRD : trD = []) by (unfold trD; rewrite HEf; reflexivity).
  assert (BR0 : brT TD = br) by (rewrite TD0; unfold brT, send_off; rewrite Z.eqb_refl, orb_true_r; reflexivity).
  assert (EI0 : eiT TD = ei) by (rewrite TD0; unfold eiT, send_off; rewrite Z.eqb_refl, orb_true_r; reflexivity).
  assert (LD0f : send_live cl br dd TD = false).
  { rewrite TD0. unfold send_live, send_off. rewrite Z.eqb_refl, orb_true_r. reflexivity. }
  assert (FDnn : 0 <= FD) by lia.
  assert (HKH : re_hp e <> 0 -> re_kh e <> 0)
    by (intros Hp; destruct HPD0 as [(H0 & _)|(_ & _ & _ & H8 & _)]; lia).
  exists L0, A0, R1, m1, md0, (rk_with_keys e ks), h, O, junk, [], nout, cap, out.
  cbn [rk_with_keys re_keys re_hp re_kh].
  split; [rewrite HEf; reflexivity|].
  split; [exact RF1|].
  split; [rewrite RA1, HEf; reflexivity|].
  split; [exact R10|].
  split; [exact (rm_h_chain _ m1 MU WM)|].
  split; [exact INIT|].
  split; [exact RO1|].
  split.
  { exists []. split; [rewrite TRD; reflexivity|]. split; [rewrite TRD; exact RES|].
    split; [intros ext; rewrite TRD; reflexivity|].
    assert (A1E : a1M = a0M) by (unfold a1M, after_drain_adr; rewrite HEf; reflexivity).
    rewrite A1E. pose proof (HND _ _ _ _ HM0) as ND0.
    split.
    { unfold rm_dab, a0M, drain_start. cbn [da_out da_buf da_hp da_keys da_pend da_ev da_erecs].
      repeat split; try exact I; apply Forall_forall; intros x Hx; apply in_map_iff in Hx as (y & <- & _); exact I. }
    split.
    { intros CN. unfold a0M, drain_start, known_at. cbn [da_out resolve].
      destruct OUTD as [(C0 & _)|(_ & _ & OI & _)]; [lia|]. exact (sptr_of_spec L0 A0 OUT CAP ND0 OI). }
    split.
    { unfold entry_links, a0M, drain_start.
      cbn [rk_with_keys da_buf da_hp da_keys re_cap re_buf re_hp re_kh re_keys].
      split.
      { intros CP. unfold known_at. cbn [resolve]. destruct BUFD0 as [(C0 & _)|(_ & BI & _)]; [lia|].
        exact (sptr_of_spec L0 A0 _ _ ND0 BI). }
      split.
      { intros HP. unfold known_at. cbn [resolve]. destruct HPD0 as [(H0 & _)|(HI & _)]; [lia|].
        exact (sptr_of_spec L0 A0 _ _ ND0 HI). }
      apply (rm_keys_f2 L0 A0 [] ks (re_keys e) ND0 EA ET).
      rewrite Forall_forall in KF0 |- *. intros k Hk. exact (proj1 (KF0 k Hk)). }
    intros E0. contradiction. }
  split; [exact FR1|].
  split.
  { rewrite BR0, EI0. unfold GLB.
    split; [exact LK1|].
    split; [apply (rm_h_bytes m1 _ _ MU CWK); intros t Ht; rewrite length_le4 in Ht; apply rm_W1_img;
            [apply IML; unfold G_WAKE1, G_LISTEN; lia | unfold G_WAKE1; lia]|].
    split; [apply (rm_h_cells m1 _ _ MU WM CNS); intros t Ht; cbn [cells_size csize] in Ht; apply rm_W1_img;
            [apply IMR; unfold G_NSRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia | unfold G_NSRC; lia]|].
    split; [apply (rm_h_cells m1 _ _ MU WM CSR); intros t Ht; cbn [cells_size csize] in Ht; apply rm_W1_img;
            [apply IMR; unfold G_SRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia | unfold G_SRC; lia]|].
    split; [apply (rm_h_cells m1 _ _ MU WM CCL); intros t Ht; cbn [cells_size csize] in Ht; apply rm_W1_img;
            [apply IML; unfold G_CLIENT, G_LISTEN, G_WAKE1; lia | unfold G_CLIENT; lia]|].
    split; [apply (rm_h_cells m1 _ _ MU WM CBR); intros t Ht; cbn [cells_size csize] in Ht; apply rm_W1_img;
            [apply IMR; unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia | unfold G_BROKEN; lia]|].
    split; [apply (rm_h_cells m1 _ _ MU WM CDD); intros t Ht; cbn [cells_size csize] in Ht; apply rm_W1_img;
            [apply IMR; unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia | unfold G_DEAD; lia]|].
    split; [apply (rm_h_cells m1 _ _ MU WM CEI); intros t Ht; cbn [cells_size csize] in Ht; apply rm_W1_img;
            [apply IMR; unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia | unfold G_EINTR; lia]|].
    destruct CER as (ev & CE). exists ev. apply (rm_h_cells m1 _ _ MU WM CE). intros t Ht.
    cbn [cells_size csize] in Ht. apply rm_W1_err. lia. }
  split; [apply (rm_h_cells m1 _ _ MU WM COV); intros t Ht; cbn [cells_size csize] in Ht; apply rm_W1_img;
          [apply IMR; unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia | unfold G_OUTV; lia]|].
  split.
  { rewrite (rk_entry_bytes_wk e ks EL), <- rm_tab_split. destruct TAB as [_ TR].
    apply (rm_h_cells m1 _ _ MU WM TR). intros t Ht. cbn [cells_size csize] in Ht.
    apply (rm_W1_blk G SRC_TABLE); [exact GIN | unfold SRC_TABLE, SRC_ENTRY; lia]. }
  split; [exact GIN|].
  split; [exact OK1|].
  split.
  { rewrite (rk_entry_blocks_wk e ks EA).
    replace (hbo h) with (@nil Z) by (unfold hbo; rewrite HEf; reflexivity).
    apply (rma_nodup_pick G OUT es [] i Hi). rewrite app_nil_r. exact NDB. }
  split; [intros E0; contradiction|].
  split; [intros _; exact Eks|].
  split; [unfold Lsi; rewrite HEf; reflexivity|].
  split.
  { unfold BF. replace (hbo h) with (@nil Z) by (unfold hbo; rewrite HEf; reflexivity).
    replace hbi with (@nil Z) by (unfold hbi; rewrite HEf; reflexivity).
    rewrite (rk_entry_blocks_wk e ks EA). rewrite app_nil_r.
    split; [intros q m Hq _ _ _; exact Hq|].
    split.
    - intros q m Hq. destruct (in_dec Z.eq_dec q (entry_blocks e)) as [X|X].
      + right. left. exact X.
      + destruct (Z.eq_dec q OUT) as [EO|EO]; [right; right; exact EO|].
        left. split; [exact Hq|]. split; [exact EO|]. split; [exact X | intros []].
    - intros q m Hq Hm HO HEb HH. split; [exact HO|]. split; [exact HEb | intros []]. }
  split.
  { destruct OUTD as [H|(Cp & NL & OI & OF & OB & LO & LJ)]; [left; exact H | right].
    split; [exact Cp|]. split; [exact NL|]. split; [exact OI|]. split; [exact OF|].
    split; [|split; [exact LO | exact LJ]].
    apply (rm_h_bytes m1 _ _ MU OB). intros t Ht. rewrite length_app in Ht.
    apply (rm_W1_blk OUT CAP); [exact OI | lia]. }
  split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; reflexivity|].
  split; [intros LT; rewrite LD0f in LT; discriminate|].
  assert (SDE : sDM = drain_init NO CAP e h) by (unfold sDM, after_drain; rewrite HEf; reflexivity).
  split; [rewrite SDE; unfold drain_init; cbn [ds_H]; exact EX|].
  split; [rewrite SDE; reflexivity|].
  split.
  { intros xks jj o ha HX. rewrite SDE. unfold drain_init. cbn [ds_no ds_ocap ds_ka]. rewrite BR0.
    assert (SL : xks <> [] -> send_live cl br dd (keys_total ks) = lv).
    { intros NE. apply rma_live_nz. intros Z0. apply NE. apply (map_eq_nil fst).
      rewrite HX, (rma_keys_total_zero _ Z0). reflexivity. }
    split.
    - unfold gestures_end_tr, ent_ka. rewrite (rm_held_eq _ _ _ HKH). rewrite (rm_ker_eq _ lv _ _ _ _ _ _ SL).
      reflexivity.
    - unfold gestures_end_out. rewrite (rm_ker_eq _ lv _ _ _ _ _ _ SL). reflexivity. }
  intros _. unfold remove_entry_cap, after_drain. rewrite HEf. cbv beta iota zeta. unfold drain_init.
  cbn [ds_no ds_ocap ds_H]. rewrite BR0, <- EX, rm_klens. unfold gestures_end_cap.
  rewrite (rm_ker_eq (send_live cl br dd (keys_total ks)) lv); [reflexivity|].
  intros NE. apply rma_live_nz. intros Z0. apply NE. rewrite (rma_keys_total_zero _ Z0). reflexivity.
Qed.

Lemma rm_nozero : forall l, ~ In (Z_to_bv 8 0) l -> nozero (bzs l).
Proof using.
  intros l H. unfold nozero, bzs. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (b & <- & Hb).
  intros E. apply H. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. unfold bz in E. rewrite E.
  reflexivity.
Qed.

Lemma rm_J1 : re_eof e = 0 -> J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h).
Proof using EOK HFi Hi O SRCP junk.
  intros E0. destruct (SRCP e rm_e_in HFi E0) as (_ & _ & _ & _ & SKO & SKW & _).
  pose proof (proj1 (Forall_forall _ _) EOK e rm_e_in) as (_ & SK & _ & _ & _ & _ & UL & UB & UNZ & _).
  unfold J1, hs_state. cbn [ls_k ls_w]. rewrite SKO.
  split; [reflexivity|]. split.
  - intros F0. apply SKW. destruct SK as [S|S]; [exact S|]. rewrite <- SKO, S in F0. discriminate.
  - split; [|apply rm_nozero; exact UNZ].
    unfold bzs. rewrite length_map. apply Nat2Z.inj_le. change (Z.of_nat LINE_LIMIT) with 6000. lia.
Qed.

Lemma rm_pok : re_eof e = 0 -> rma_pok (drain_init NO CAP e h).
Proof using HFi Hi O SRCP junk.
  intros E0. destruct (SRCP e rm_e_in HFi E0) as (SRC0 & _).
  destruct SRC0 as (_ & _ & _ & _ & _ & LP & _ & OFFD & _).
  destruct LP as (_ & _ & _ & _ & _ & HR).
  unfold rma_pok, drain_init. cbn [ds_off ds_pend].
  destruct OFFD as [(R0 & O0)|(r & rs & ER & OR)].
  - rewrite R0. split; [lia | exact I].
  - rewrite ER in HR |- *. cbn [map]. split; [lia|]. split; [unfold bzs; rewrite length_map; lia|].
    apply Forall_map. apply Forall_forall. intros r' Hr'. apply Forall_inv_tail in HR.
    destruct (proj1 (Forall_forall _ _) HR r' Hr') as (_ & _ & _ & _ & L1). unfold bzs. rewrite length_map.
    exact (L1 eq_refl).
Qed.

Lemma rm_ker_fst : forall l mx0 n0 c0 n1 c1 xks jj o, (l = true -> n0 = n1 /\ c0 = c1) ->
  fst (keys_end_run l mx0 n0 c0 xks jj o) = fst (keys_end_run l mx0 n1 c1 xks jj o).
Proof using.
  intros l mx0 n0 c0 n1 c1 xks jj o H. destruct l; [destruct (H eq_refl) as [-> ->]; reflexivity | apply rma_ge_dead].
Qed.

Lemma rm_ker_snd : forall l mx0 n0 c0 n1 c1 xks jj o, (l = true -> n0 = n1) -> c0 = c1 ->
  snd (keys_end_run l mx0 n0 c0 xks jj o) = snd (keys_end_run l mx0 n1 c1 xks jj o).
Proof using.
  intros l mx0 n0 c0 n1 c1 xks jj o H ->. destruct l; [rewrite (H eq_refl); reflexivity | rewrite !rm_ker_dead; reflexivity].
Qed.

Lemma rm_ret_13fbc : YK0s.ret_ok (Z_to_bv 64 0x13fbc).
Proof using. unfold YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

Lemma rm_kt_nz : forall ks, key_lens ks <> [] -> keys_total ks <> 0.
Proof using. intros ks NE Z0. apply NE. rewrite (rma_keys_total_zero _ Z0). reflexivity. Qed.

Lemma rm_drain : forall c, AtH c -> re_eof e = 0 -> SR segs c AtG.
Proof using AX BSP CBR CCL CDD CEI CER CNS COV CSR CWK DRC EHI EOK GFR GIN HERR4 HFi HN4 HND Hbr Hcl Hdd Hei Hi IME IML IMR INIT NDF OUTD PRE RES ROOM SEGS SRCP TAB TPE.
  intros c (R1 & m1 & -> & RF1 & RA1 & R10 & MU & WM & RO1 & FR1 & LK1) E0.
  pose proof rm_pre as (HM0 & HW0 & HB0 & HRA & HAL & HCE & H63 & HWS & HTP & HER & Hh & Hl & AC).
  pose proof rm_sf as (E1 & E2 & G1 & G2 & G3 & G4 & G5 & G6).
  destruct rm_K as (K1 & K2 & K3 & K4 & K5).
  pose proof (rm_h_chain (Ffin 0) m1 MU WM) as CH0. pose proof CH0 as (M1 & _).
  pose proof (proj1 (Forall_forall _ _) EOK e rm_e_in) as EOKe.
  pose proof EOKe as (EOF0 & SK0 & P10 & P20 & FDR0 & CAPV0 & UL0 & UB0 & UNZ0 & BUFD0 & NHB0 & HPD0 & NDK0 & NDT0 & KF0).
  destruct (SRCP e rm_e_in HFi E0) as (SRC0 & OTH0 & Hj & HFh & SKO & SKW & NDH0 & PLB & ECB & NPB).
  destruct (rm_rf R1 RF1) as (Q2 & Q8 & Q9 & Q18 & Q19 & QO).
  pose proof (rma_keys_total_nonneg (re_keys e)) as KTN0.
  rm_hide.
  destruct (rm_reslack m1 MU WM M1) as (ks & Eks & OK1).
  destruct (rk_map_fst_keys (re_keys e) ks Eks) as (EA & ET & EL & EP & EX).
  assert (HEt : (re_eof e =? 0) = true) by (apply Z.eqb_eq; exact E0).
  assert (LSE : Lsi = lines (hs_state h) (bzs (pending_stream h))) by (unfold Lsi; rewrite HEt; reflexivity).
  assert (TRDE : trD = drain_tr lv (bv_unsigned mx) NO CAP e h 0 a0M) by (unfold trD; rewrite HEt; reflexivity).
  assert (SDE : sDM = finI) by (unfold sDM, after_drain; rewrite HEt; reflexivity).
  assert (A1D : a1M = drain_adr lv (bv_unsigned mx) NO CAP e h 0 a0M)
    by (unfold a1M, after_drain_adr; rewrite HEt; reflexivity).
  assert (HBI : hbi = hs_blocks h) by (unfold hbi; rewrite HEt; reflexivity).
  assert (HBO : forall h2, hbo h2 = hs_blocks h2) by (intros h2; unfold hbo; rewrite HEt; reflexivity).
  assert (FDnn : 0 <= FD) by lia.
  assert (HSP : spZ R1 = SP - 48) by (unfold spZ; rewrite Q2; apply unsigned_lit; lia).
  assert (RA1' : getr R1 1 = Z_to_bv 64 0x13fbc) by (rewrite RA1, HEt; reflexivity).
  assert (TDN : 0 <= TD) by (unfold TD; lia).
  assert (EB0 : entry_blocks (rk_with_keys e ks) = entry_blocks e) by exact (rk_entry_blocks_wk e ks EA).
  assert (EY0 : entry_bytes (rk_with_keys e ks) = entry_bytes e) by exact (rk_entry_bytes_wk e ks EL).
  assert (INI0 : drain_init NO CAP (rk_with_keys e ks) h = drain_init NO CAP e h).
  { unfold drain_init, ent_ka. cbn [rk_with_keys re_cap re_U re_skip re_keys re_hp re_kh]. rewrite EX. reflexivity. }
  assert (A0E : drain_start (known_at L0 A0) (known_at L0 A0 OUT) (rk_with_keys e ks) h = a0M).
  { unfold a0M, drain_start. cbn [rk_with_keys re_buf re_hp re_keys].
    rewrite (rm_map_ka (known_at L0 A0) ks (re_keys e) EA). reflexivity. }
  assert (HOF : 0 <= hs_off h).
  { destruct SRC0 as (_ & _ & _ & _ & _ & _ & _ & OFFD & _). destruct OFFD as [(_ & O0)|(r & rs & _ & OR)]; lia. }
  assert (J1e : J1 (bzs (re_U e)) (re_skip e =? 1) (hs_state h)) by exact (rm_J1 E0).
  assert (LN0 : TD = 0 -> lines (hs_state h) (bzs (pending_stream h)) = []).
  { intros T0. apply rma_wn_nil. rewrite <- LSE. unfold TD in T0. lia. }
  assert (DRL : drain_tr (send_live cl br dd TD) (bv_unsigned mx) NO CAP e h 0 a0M = trD /\
                drain_fin (send_live cl br dd TD) (bv_unsigned mx) NO CAP e h = finI /\
                drain_adr (send_live cl br dd TD) (bv_unsigned mx) NO CAP e h 0 a0M = a1M).
  { rewrite TRDE, A1D. unfold finI. destruct (Z.eq_dec TD 0) as [T0|T0].
    - destruct (rma_fin_live (send_live cl br dd TD) lv (bv_unsigned mx) NO CAP e h 0 a0M J1e HOF (LN0 T0))
        as [X1 X2].
      split; [exact X1|]. split; [exact X2|]. exact (rm_dadr_live _ _ _ _ _ e h 0 a0M J1e HOF (LN0 T0)).
    - rewrite (rma_live_nz cl br dd TD T0). split; [reflexivity|]. split; reflexivity. }
  assert (DTR : drain_tr (send_live cl br dd TD) (bv_unsigned mx) NO CAP (rk_with_keys e ks) h 0 a0M = trD)
    by (rewrite <- (proj1 DRL); unfold drain_tr, drain_go; rewrite INI0; reflexivity).
  assert (DFN : drain_fin (send_live cl br dd TD) (bv_unsigned mx) NO CAP (rk_with_keys e ks) h = finI)
    by (rewrite <- (proj1 (proj2 DRL)); unfold drain_fin, drain_go; rewrite INI0; reflexivity).
  assert (DAD : drain_adr (send_live cl br dd TD) (bv_unsigned mx) NO CAP (rk_with_keys e ks) h 0 a0M = a1M)
    by (rewrite <- (proj2 (proj2 DRL)); unfold drain_adr, drain_go; rewrite INI0; reflexivity).
  assert (FNO : ds_no finI = NO + TD).
  { unfold finI. rewrite (rma_fin_no lv (bv_unsigned mx) NO CAP e h J1e (rm_pok E0));
      [rewrite <- LSE; reflexivity|].
    unfold RmOr in CAPV0. lia. }
  assert (FCP : TD = 0 -> ds_ocap finI = CAP).
  { intros T0. unfold finI.
    rewrite (proj2 (rma_fin_live lv false (bv_unsigned mx) NO CAP e h 0%nat dadr0 J1e HOF (LN0 T0))).
    apply rma_fin_cap. }
  assert (LDT : send_live cl br dd TD = true -> TD <> 0).
  { intros LT T0. rewrite T0 in LT. unfold send_live, send_off in LT. rewrite Z.eqb_refl, !orb_true_r in LT.
    cbn in LT. discriminate. }
  (* The table and the globals at the call. *)
  assert (TB1 : rw_cells rsegs m1 G [CB 896 (Tpre ++ entry_bytes e ++ Tpost)]).
  { rewrite <- rm_tab_split. destruct TAB as [_ TR]. rewrite <- SEGS. apply (rm_h_cells m1 _ _ MU WM TR).
    intros t Ht. cbn [cells_size csize] in Ht. apply (rm_W1_blk G SRC_TABLE); [exact GIN | unfold SRC_TABLE, SRC_ENTRY; lia]. }
  destruct (rm_tsplit m1 (entry_bytes e) (rma_entry_len e P10 P20) TB1) as (T1 & T2 & T3).
  assert (TGI : forall A cs, rw_cells segs mem0 A cs ->
             (forall t, 0 <= t < Z.of_nat (cells_size cs) -> G_RELAY_LO <= A + t < G_S + SRC_SIZE * SOURCES_MAX /\
                (A + t < 203004 \/ 203008 <= A + t)) -> rw_cells segs m1 A cs).
  { intros A cs H K. apply (rm_h_cells m1 _ _ MU WM H). intros t Ht. destruct (K t Ht) as [K1' K2'].
    exact (rm_W1_img _ (IMR _ K1') K2'). }
  assert (CL1 : rw_cells segs m1 G_CLIENT [C4 (Z_to_bv 64 cl)]).
  { apply (rm_h_cells m1 _ _ MU WM CCL). intros t Ht. cbn [cells_size csize] in Ht. apply rm_W1_img;
      [apply IML; unfold G_CLIENT, G_LISTEN, G_WAKE1; lia | unfold G_CLIENT; lia]. }
  assert (WK1 : bytes_at segs m1 G_WAKE1 (le4 (Z_to_bv 64 (-1)))).
  { apply (rm_h_bytes m1 _ _ MU CWK). intros t Ht. rewrite length_le4 in Ht. apply rm_W1_img;
      [apply IML; unfold G_WAKE1, G_LISTEN; lia | unfold G_WAKE1; lia]. }
  assert (BR1 : rw_cells segs m1 G_BROKEN [C1 (Z_to_bv 8 br)])
    by (apply TGI; [exact CBR | intros t Ht; cbn [cells_size csize] in Ht;
        unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia]).
  assert (DD1 : rw_cells segs m1 G_DEAD [C1 (Z_to_bv 8 dd)])
    by (apply TGI; [exact CDD | intros t Ht; cbn [cells_size csize] in Ht;
        unfold G_DEAD, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia]).
  assert (EI1 : rw_cells segs m1 G_EINTR [C1 (Z_to_bv 8 ei)])
    by (apply TGI; [exact CEI | intros t Ht; cbn [cells_size csize] in Ht;
        unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia]).
  assert (OV1 : rw_cells segs m1 G_OUTV [C8 mx; C8 nout; C8 cap; C8 out])
    by (apply TGI; [exact COV | intros t Ht; cbn [cells_size csize] in Ht;
        unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia]).
  assert (NS1 : rw_cells segs m1 G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)])
    by (apply TGI; [exact CNS | intros t Ht; cbn [cells_size csize] in Ht;
        unfold G_NSRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia]).
  assert (SR1 : rw_cells segs m1 G_SRC [C8 (Z_to_bv 64 G)])
    by (apply TGI; [exact CSR | intros t Ht; cbn [cells_size csize] in Ht;
        unfold G_SRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia]).
  assert (ER1 : exists ev, rw_cells segs m1 ERR [C4 ev]).
  { destruct CER as (ev & CE). exists ev. apply (rm_h_cells m1 _ _ MU WM CE). intros t Ht.
    cbn [cells_size csize] in Ht. apply rm_W1_err. lia. }
  assert (OUTD1 : (CAP = 0 /\ OUT = 0 /\ NO = 0 /\ O = []) \/
     (0 < CAP /\ NO <= CAP /\ In (OUT, CAP) (blocks L0 A0) /\ fresh_block Bm OUT CAP /\
      bytes_at segs m1 OUT (O ++ junk) /\ Z.of_nat (length O) = NO /\ Z.of_nat (length junk) = CAP - NO)).
  { destruct OUTD as [H|(Cp & NL & OI & OF & OB & LO & LJ)]; [left; exact H | right].
    split; [exact Cp|]. split; [exact NL|]. split; [exact OI|]. split; [exact OF|].
    split; [|split; [exact LO | exact LJ]].
    apply (rm_h_bytes m1 _ _ MU OB). intros t Ht. rewrite length_app in Ht. apply (rm_W1_blk OUT CAP); [exact OI | lia]. }
  assert (NDE : NoDup (G :: OUT :: entry_blocks e ++ hs_blocks h)) by exact (rma_nodup_pick G OUT es (hs_blocks h) i Hi NDH0).
  pose proof (rma_nodup_std _ NDE) as NDEs. apply List.NoDup_cons_iff in NDEs as [NGE NDEs].
  apply List.NoDup_cons_iff in NDEs as [NOE NDEs].
  replace (Z_to_bv 64 (if re_eof e =? 0 then DRAIN else GESTURES_END)) with (Z_to_bv 64 DRAIN) by (rewrite HEt; reflexivity).
  eapply SR_bind.
  { pose proof DRC as DC. unfold drain_contract in DC.
    specialize (DC L0 A0 R1 m1 md0 bnd (rk_with_keys e ks) h j fs os G O junk cl br dd ei mx nout cap out).
    cbv zeta in DC.
    match type of DC with context [bv_unsigned (PropExec.getr R1 ?r)] =>
      assert (U10 : bv_unsigned (PropExec.getr R1 r) = G + 56 * Z.of_nat i)
        by (transitivity (bv_unsigned (Z_to_bv 64 (G + 56 * Z.of_nat i))); [f_equal; exact R10 | apply unsigned_lit; lia]);
      rewrite U10 in DC
    end.
    apply DC; clear DC.
    - exact SEGS.
    - split; [exact M1|]. split; [exact HW0|]. split; [exact HB0|]. split; [rewrite RA1'; exact rm_ret_13fbc|].
      rewrite HSP, K2. split; [clear - HAL; Z.div_mod_to_equations; lia|]. split; [lia|]. split; [lia|].
      split; [intros a Ha; pose proof (HWS a ltac:(lia)) as W; rewrite SEGS in W |- *; exact (WM _ W)|].
      split; [transitivity (getr regs0 4);
              [exact (QO 4 ltac:(unfold callee_saved; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) |
               exact HTP]|].
      split; [intros a Ha; pose proof (HER a Ha) as W; rewrite SEGS in W |- *; exact (WM _ W)|].
      intros X0. rewrite INIT in X0. discriminate.
    - exact INIT.
    - exact TPE.
    - exact HERR4.
    - exact EHI.
    - exact RO1.
    - exact IMR.
    - intros a Ha. apply IML. unfold G_CLIENT, G_LISTEN, G_WAKE1 in *. lia.
    - exact IME.
    - exact Hj.
    - split; [exact GIN|]. split; [exact GFR|]. split; [lia|].
      split; [unfold SRC_TABLE, SRC_ENTRY; lia|].
      unfold SRC_ENTRY. replace (G + 56 * Z.of_nat i - G) with (Z.of_nat i * 56) by lia. apply Z_mod_mult.
    - rewrite EY0, SEGS. exact T2.
    - exact OK1.
    - apply (rk_src_at_kept Bm L0 A0 mem0 L0 A0 m1 HA h SRC0).
      + intros k Hk. apply (rm_h_kb m1 _ MU WM); [unfold G_S, SRC_SIZE in *; lia|]. apply rm_W1_img;
          [apply IMR; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia | unfold G_S, SRC_SIZE in *; lia].
      + intros q _. exact (rm_h_bkept m1 q MU WM).
    - destruct OTH0 as (F1 & F2 & F3). split; [exact F1|]. split; [exact F2|]. intros k Hk Hkj.
      destruct (F3 k Hk Hkj) as (C & X0 & Y0). cbn [rk_with_keys re_fd]. rewrite HFi.
      split; [|split; [exact X0 | exact Y0]].
      apply (rm_h_cells m1 _ _ MU WM C). intros t Ht. cbn [cells_size csize] in Ht. apply rm_W1_img;
        [apply IMR; unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia | unfold G_S, SRC_SIZE; lia].
    - cbn [rk_with_keys re_fd]. rewrite HFh. symmetry. exact HFi.
    - exact SKO.
    - exact SKW.
    - rewrite EB0. exact NDE.
    - exact PLB.
    - exact ECB.
    - unfold re_nheld in *. cbn [rk_with_keys re_keys]. rewrite EL. exact NPB.
    - exact Hcl.
    - exact Hbr.
    - exact Hdd.
    - exact Hei.
    - exact CL1.
    - exact BR1.
    - exact DD1.
    - exact EI1.
    - exact OV1.
    - exact ER1.
    - exact OUTD1.
    - exact RES.
    - rewrite <- LSE. fold TD. rewrite A0E, DTR. intros qs QLs.
      assert (NB : nretF trBM = 0%nat) by (unfold trBM; destruct (ds_cap sDM =? 0); reflexivity).
      assert (LQ : length (qs ++ p3c_pad (nretF trGM)) = nretF trR)
        by (rewrite rm_trR, length_app, p3c_pad_len, !nret_app, NB; lia).
      pose proof (ROOM _ LQ) as RM. rewrite rm_trR in RM.
      unfold roomF, room_run in RM. apply room_from_app in RM as [RM _].
      pose proof QLs as QL'. rewrite TRDE in QL'.
      destruct (rm_drain_wf F lv (bv_unsigned mx) NO CAP e h L0 A0 OUT qs (p3c_pad (nretF trGM)) bnd QL')
        as (_ & RR & _).
      rewrite TRDE in RM |- *. apply RR. exact RM. }
  intros c' (L2 & A2 & R2 & m2 & md2 & e1 & h1 & OUT' & CAP' & junk' & LB & -> & RP & INI2 & RS2 & RO2 & SL2 & EOK2 &
    SRC2 & OTH2 & FD2 & EOF2 & CP2 & CAPE & UE & SKE & KTE & KAE & ECE & HKH2 & ECL & HFD2 & HCL2 & HEI2 & HPN2 & HOF2 &
    HPV2 & HPC2 & HPP2 & HST2 & HEX2 & HFX2 & HHL2 & SKO2 & SKW2 & NDK2 & SSE & ND2 & GI2 & BFw & BRv & BFr & CL2 &
    BR2 & DD2 & EI2 & ER2 & LB2 & LF0 & LF1).
  rewrite <- LSE in RS2, CAPE, KTE, KAE, ECE, HEX2, SSE, BR2, EI2, LB2, LF0, LF1, RP.
  fold TD in RS2, CAPE, KTE, KAE, ECE, BR2, EI2, LF0, LF1, RP.
  rewrite A0E in RS2. rewrite DTR, DAD in RS2. rewrite DFN in CAPE, KTE, KAE, ECE, LF1.
  destruct RS2 as (qs & QLs & RSs & LOs & ELs & SLs).
  rewrite EB0 in RP, BFw, BRv, BFr.
  cbn [rk_with_keys re_keys] in SSE. rewrite EX in SSE.
  cbn [rk_with_keys re_fd] in OTH2. rewrite HFi in OTH2.
  pose proof RP as (M2 & W2 & B2 & LE2 & RG2 & AD2 & SV2 & Z2 & IO2 & RPr & VM2 & FR2 & BY2 & SW2).
  destruct (mr_model Bm MR (aa_laws API) _ _ _ _ M2) as (Hh2 & Hl2 & _).
  assert (RF2 : RFr R2) by (intros r Hr; rewrite (RPr r Hr); exact (RF1 r Hr)).
  destruct (rm_rf R2 RF2) as (R2s & R28 & R29 & R218 & R219 & RO2').
  assert (HK : alloc_ceiling <= spZ R1 - DRAIN_K) by (rewrite HSP, K2; lia).
  assert (LDNZ : TD <> 0 -> send_live cl br dd TD = lv) by (intros T0; exact (rma_live_nz cl br dd TD T0)).
  assert (LDD : send_live cl br dd TD = true \/ send_live cl br dd TD = false)
    by (destruct (send_live cl br dd TD); auto).
  set (ld := send_live cl br dd TD) in *.
  set (ED := fun a : Z => send_writes ld OUT CAP a \/ SA <= a < SA + SRC_ENTRY \/ HA + 12 <= a < HA + SRC_SIZE \/
                (exists q m, In q (entry_blocks e ++ hs_blocks h) /\ In (q, m) (blocks L0 A0) /\ q <= a < q + m)) in *.
  set (FD' := fun q : Z => (ld = true /\ q = OUT) \/ In q (entry_blocks e ++ hs_blocks h)) in *.
  (* What drain may write, against the run's write set. *)
  assert (EDI : forall a, img_plain Bm a -> (a < G_BROKEN \/ G_BROKEN + 1 <= a) -> (a < G_EINTR \/ G_EINTR + 1 <= a) ->
                  (a < G_OUTV + 8 \/ G_OUTV + 32 <= a) -> (a < HA + 12 \/ HA + SRC_SIZE <= a) -> ~ ED a).
  { intros a IP Y1 Y2 Y3 Y4 X0. unfold ED in X0.
    destruct X0 as [[X0|[X0|[X0|(LV & X0)]]]|[X0|[X0|(q & m & Hq & Hqm & X0)]]]; [lia | lia | lia | | | lia |].
    - destruct OUTD1 as [(C0 & _)|(_ & _ & OI & (F1 & F2 & F3) & _)]; [lia|]. apply (F3 (a - OUT)); [lia|].
      replace (OUT + (a - OUT)) with a by lia. exact (proj1 IP).
    - pose proof GFR as (GF1 & GF2 & GF3). apply (GF3 (a - G)); [unfold SRC_TABLE, SRC_ENTRY in *; lia|].
      replace (G + (a - G)) with a by lia. exact (proj1 IP).
    - destruct (rm_blk_noimg L0 A0 m1 md0 q m a M1 Hqm X0) as (NI & _). exact (NI (proj1 IP)). }
  assert (EDG : forall a, G <= a < G + 896 -> (a < SA \/ SA + 56 <= a) -> ~ ED a).
  { intros a Ha Hs X0. pose proof GFR as (GF1 & GF2 & GF3).
    assert (NI : ~ in_img Bm a) by (replace a with (G + (a - G)) by lia; apply GF3; unfold SRC_TABLE, SRC_ENTRY; lia).
    unfold ED in X0. destruct X0 as [[X0|[X0|[X0|(LV & X0)]]]|[X0|[X0|(q & m & Hq & Hqm & X0)]]].
    - exact (NI (proj1 (IMR a ltac:(unfold G_BROKEN, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - exact (NI (proj1 (IMR a ltac:(unfold G_EINTR, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - exact (NI (proj1 (IMR a ltac:(unfold G_OUTV, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - destruct OUTD1 as [(C0 & _)|(_ & _ & OI & _)]; [lia|].
      destruct (blocks_disjoint Bm API L0 A0 m1 md0 G SRC_TABLE _ _ M1 GIN OI (fun E => NGE (or_introl (eq_sym E))));
        unfold SRC_TABLE, SRC_ENTRY in *; lia.
    - unfold SRC_ENTRY in X0. lia.
    - exact (NI (proj1 (IMR a ltac:(unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX in *; lia)))).
    - assert (QG : q <> G) by (intros E; apply NGE; right; rewrite <- E; exact Hq).
      destruct (blocks_disjoint Bm API L0 A0 m1 md0 q m G SRC_TABLE M1 Hqm GIN QG); unfold SRC_TABLE, SRC_ENTRY in *;
        lia. }
  assert (EDH : forall a, alloc_ceiling <= a -> ~ ED a).
  { intros a Ha X0. unfold ED in X0.
    destruct X0 as [[X0|[X0|[X0|(LV & X0)]]]|[X0|[X0|(q & m & Hq & Hqm & X0)]]];
      [unfold G_BROKEN in X0; lia | unfold G_EINTR in X0; lia | unfold G_OUTV in X0; lia | | unfold SRC_ENTRY in X0; lia |
       unfold G_S, SRC_SIZE in X0; lia | ].
    - destruct OUTD1 as [(C0 & _)|(_ & _ & _ & (F1 & F2 & _) & _)]; lia.
    - destruct (rm_blk_lo L0 A0 m1 md0 q m M1 Hqm). lia. }
  assert (FDG : ~ FD' G).
  { intros [(_ & X0)|X0]; [exact (NGE (or_introl (eq_sym X0))) | exact (NGE (or_intror X0))]. }
  assert (CH2 : rk_chain Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0
                  L2 A2 m2 md2).
  { apply (rk_chain_callee Bm API RELAY_REMOVE_K Efin (Ffin (keys_total (re_keys e1))) L0 A0 regs0 mem0 md0
             L0 A0 m1 md0 DRAIN_K ED FD' R1 L2 A2 R2 m2 md2 HW0 (rm_h_chain _ m1 MU WM) RP).
    - intros a Ha. unfold scratch_k in *. rewrite HSP, K2 in Ha. unfold spZ in *. rewrite K1. lia.
    - intros a Ha Hn. unfold scratch_k in *. rewrite HSP, K2 in Hn. unfold spZ in Ha. rewrite K1 in Ha. lia.
    - intros a Ha. unfold ED in Ha.
      destruct Ha as [[X0|[X0|[X0|(LV & X0)]]]|[X0|[X0|(q & m & Hq & Hqm & X0)]]].
      + split; [unfold G_BROKEN in X0; lia|]. intros _. left. left. exact X0.
      + split; [unfold G_EINTR in X0; lia|]. intros _. left. right. left. exact X0.
      + split; [unfold G_OUTV in X0; lia|]. intros _. left. right. right. left. exact X0.
      + destruct OUTD1 as [(C0 & _)|(_ & _ & OI & (F1 & F2 & F3) & _)]; [lia|]. split; [lia|]. intros IM. exfalso.
        apply (F3 (a - OUT)); [lia|]. replace (OUT + (a - OUT)) with a by lia. exact IM.
      + split; [unfold SRC_ENTRY in X0; lia|]. intros _. right. right. right. left.
        unfold SRC_TABLE, SRC_ENTRY in *. lia.
      + split; [unfold G_S, SRC_SIZE in X0; lia|]. intros _. right. right. right. right. left.
        split; [exists e; split; [exact rm_e_in|]; split; [exact HFi | exact E0] | exact X0].
      + destruct (rm_blk_noimg L0 A0 m1 md0 q m a M1 Hqm X0) as (NI & _ & Q3). split; [lia|].
        intros IM. exfalso. exact (NI IM).
    - intros p n Hp0 Hp1 Hn HF.
      assert (QB : In (ptr_addr L0 p, n) (blocks L0 A0)) by (apply rk_blocks_in; exists p; auto).
      destruct (Z.eq_dec (ptr_addr L0 p) OUT) as [EO|N1].
      { (* The start output buffer, kept: no send was live. *)
        assert (LDf : ld = false).
        { destruct LDD as [LD|LD]; [exfalso|exact LD].
          assert (LD' : send_live cl br dd TD = true) by exact LD.
          apply HF. left. split; [|exact EO]. exists e. split; [exact rm_e_in|]. split; [exact HFi|].
          change (Z.of_nat (length (with_nul (Lsf e)))) with TD.
          rewrite (rma_live_or cl br dd TD (keys_total (re_keys e1)) Hcl Hbr Hdd TDN (rma_keys_total_nonneg _)), LD'.
          reflexivity. }
        split.
        + intros [(LT & _)|X0]; [rewrite LDf in LT; discriminate|]. rewrite EO in X0. exact (NOE X0).
        + intros t Ht NEf X0. unfold ED in X0.
          destruct X0 as [[X0|[X0|[X0|(LV & X0)]]]|[X0|[X0|(q & m & Hq & Hqm & X0)]]].
          * apply NEf. left. left. exact X0.
          * apply NEf. left. right. left. exact X0.
          * apply NEf. left. right. right. left. exact X0.
          * rewrite LDf in LV. discriminate.
          * apply NEf. right. right. right. left. unfold SRC_TABLE, SRC_ENTRY in *. lia.
          * apply NEf. right. right. right. right. left.
            split; [exists e; split; [exact rm_e_in|]; split; [exact HFi | exact E0] | exact X0].
          * destruct (Z.eq_dec q (ptr_addr L0 p)) as [Eq|Nq].
            -- subst q. rewrite EO in Hq. exact (NOE Hq).
            -- destruct (blocks_disjoint Bm API L0 A0 m1 md0 _ _ _ _ M1 QB Hqm (fun E => Nq (eq_sym E))); lia. }
      assert (N2 : ~ In (ptr_addr L0 p) (entry_blocks e))
        by (intros X0; apply HF; right; exists e; split; [exact rm_e_in|]; split; [exact HFi|]; left; exact X0).
      assert (N3 : ~ In (ptr_addr L0 p) (hs_blocks h))
        by (intros X0; apply HF; right; exists e; split; [exact rm_e_in|]; split; [exact HFi|]; right;
            split; [exact E0 | exact X0]).
      split.
      + intros [(_ & X0)|X0]; [exact (N1 X0)|]. apply in_app_iff in X0 as [X0|X0]; [exact (N2 X0) | exact (N3 X0)].
      + intros t Ht NEf X0. unfold ED in X0.
        destruct X0 as [[X0|[X0|[X0|(LV & X0)]]]|[X0|[X0|(q & m & Hq & Hqm & X0)]]].
        * apply NEf. left. left. exact X0.
        * apply NEf. left. right. left. exact X0.
        * apply NEf. left. right. right. left. exact X0.
        * destruct OUTD1 as [(C0 & _)|(_ & _ & OI & _)]; [lia|].
          destruct (blocks_disjoint Bm API L0 A0 m1 md0 _ _ _ _ M1 QB OI N1); lia.
        * apply NEf. right. right. right. left. unfold SRC_TABLE, SRC_ENTRY in *. lia.
        * apply NEf. right. right. right. right. left.
          split; [exists e; split; [exact rm_e_in|]; split; [exact HFi | exact E0] | exact X0].
        * destruct (Z.eq_dec q (ptr_addr L0 p)) as [Eq|Nq].
          -- subst q. apply in_app_iff in Hq as [Hq|Hq]; [exact (N2 Hq) | exact (N3 Hq)].
          -- destruct (blocks_disjoint Bm API L0 A0 m1 md0 _ _ _ _ M1 QB Hqm (fun E => Nq (eq_sym E))); lia. }
  (* g_outv and the output buffer after drain. *)
  assert (OUTW : exists (nout1 cap1 out1 : word) (O1 junk1 : list byte),
     bv_unsigned out1 = OUT' /\
     rw_cells segs m2 G_OUTV [C8 mx; C8 nout1; C8 cap1; C8 out1] /\
     ((bv_unsigned cap1 = 0 /\ bv_unsigned out1 = 0 /\ bv_unsigned nout1 = 0 /\ O1 = []) \/
      (0 < bv_unsigned cap1 /\ bv_unsigned nout1 <= bv_unsigned cap1 /\
       In (bv_unsigned out1, bv_unsigned cap1) (blocks L2 A2) /\ fresh_block Bm (bv_unsigned out1) (bv_unsigned cap1) /\
       bytes_at segs m2 (bv_unsigned out1) (O1 ++ junk1) /\ Z.of_nat (length O1) = bv_unsigned nout1 /\
       Z.of_nat (length junk1) = bv_unsigned cap1 - bv_unsigned nout1)) /\
     (ld = false -> nout1 = nout /\ cap1 = cap /\ out1 = out /\ O1 = O /\ junk1 = junk) /\
     (ld = true -> bv_unsigned nout1 = NO + TD /\ O1 = O ++ LB) /\
     (lv = true \/ ld = true -> bv_unsigned nout1 = ds_no finI /\ bv_unsigned cap1 = ds_ocap finI)).
  { destruct LDD as [LD|LD].
    - destruct (LF1 LD) as (Q1 & Q2' & Q3 & Q4 & Q5 & Q6 & Q7).
      pose proof (rm_blk_lo L2 A2 m2 md2 _ _ M2 Q3) as (B1 & B2').
      pose proof (LDT LD) as TDz.
      assert (LLB : Z.of_nat (length LB) = TD).
      { pose proof (f_equal (@length Z) LB2) as LL. unfold bzs in LL. rewrite length_map in LL. unfold TD. lia. }
      assert (LO0 : Z.of_nat (length O) = NO).
      { destruct OUTD1 as [(_ & _ & N0 & OE)|(_ & _ & _ & _ & _ & LO & _)]; [rewrite OE; cbn [length]; lia | exact LO]. }
      pose proof (bv_unsigned_in_range 64 nout) as RN0. change (bv_modulus 64) with (2 ^ 64) in RN0.
      exists (Z_to_bv 64 (NO + TD)), (Z_to_bv 64 CAP'), (Z_to_bv 64 OUT'), (O ++ LB), junk'.
      rewrite !unsigned_lit by lia.
      split; [reflexivity|]. split; [exact Q7|].
      split; [right; split; [lia|]; split; [lia|]; split; [exact Q3|]; split; [exact Q4|];
              split; [rewrite <- app_assoc; exact Q5|]; split; [rewrite length_app; lia | lia]|].
      split; [intros X0; rewrite LD in X0; discriminate|].
      split; [intros _; split; reflexivity|].
      intros _. split; [exact (eq_sym FNO) | exact Q2'].
    - destruct (LF0 LD) as (Q1 & Q2' & Q3).
      exists nout, cap, out, O, junk.
      split; [exact (eq_sym Q3)|]. split; [exact Q1|].
      split.
      { destruct OUTD1 as [H|(Cp & NL & OI & OF & OB & LO & LJ)]; [left; exact H | right].
        destruct (Q2' Cp) as (OI2 & OB2).
        split; [exact Cp|]. split; [exact NL|]. split; [exact OI2|]. split; [exact OF|].
        split; [exact OB2|]. split; [exact LO | exact LJ]. }
      split; [intros _; split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity|]; split; reflexivity|].
      split; [intros X0; rewrite LD in X0; discriminate|].
      intros [LV|LV]; [|rewrite LD in LV; discriminate].
      assert (T0 : TD = 0).
      { destruct (Z.eq_dec TD 0) as [T0|T0]; [exact T0|]. exfalso. pose proof (LDNZ T0) as X1.
        rewrite LD, LV in X1. discriminate. }
      split; [rewrite FNO, T0; lia | rewrite (FCP T0); reflexivity]. }
  destruct OUTW as (nout1 & cap1 & out1 & O1 & junk1 & OUF & OVF & ODF & LDF0 & LDF1 & NCF).
  (* Back to relay_remove at 0x13fbc, then the call of gestures_end. *)
  assert (SRm2 : rw_cells segs m2 G_SRC [C8 (Z_to_bv 64 G)]).
  { apply (rm_rp_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RP HK SR1). intros t Ht. cbn [cells_size csize] in Ht.
    assert (IP : img_plain Bm (G_SRC + t)) by (apply IMR; unfold G_SRC, G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX; lia).
    split; [exact IP|]. apply EDI; [exact IP | unfold G_SRC, G_BROKEN; lia | unfold G_SRC, G_EINTR; lia |
      unfold G_SRC, G_OUTV; lia | unfold G_SRC, G_S, SRC_SIZE in *; lia]. }
  assert (TGD : forall A cs, rw_cells segs m1 A cs ->
             (forall t, 0 <= t < Z.of_nat (cells_size cs) -> G_RELAY_LO <= A + t < G_S /\
                (A + t < G_BROKEN \/ G_BROKEN + 1 <= A + t) /\ (A + t < G_EINTR \/ G_EINTR + 1 <= A + t) /\
                (A + t < G_OUTV + 8 \/ G_OUTV + 32 <= A + t)) -> rw_cells segs m2 A cs).
  { intros A cs H KK. apply (rm_rp_img _ _ _ _ _ _ _ _ _ _ _ _ _ A cs M1 RP HK H). intros t Ht.
    destruct (KK t Ht) as (J1' & J2 & J3 & J4).
    assert (IP : img_plain Bm (A + t)) by (apply IMR; unfold G_S, SRC_SIZE, SOURCES_MAX in *; lia).
    split; [exact IP|]. apply EDI; [exact IP | exact J2 | exact J3 | exact J4 | unfold G_S, SRC_SIZE in *; lia]. }
  first [rewrite RA1' | assert (RA1'' : PropExec.getr R1 1 = Z_to_bv 64 0x13fbc) by exact RA1'; rewrite RA1''].
  rewrite SEGS.
  eapply rm_bridge0; [exact Hh2 | exact Hl2 | | | ].
  { rewrite rm_mkR_of, R218, R219.
    eapply rm_segd with (G := G) (i := i); [lia | lia | lia | ].
    apply rm_rd8. rewrite SEGS in SRm2. pose proof (rm_rw_bytes _ _ _ _ SRm2) as B.
    cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B. }
  2: { intros s0 HQ0. cbv beta in HQ0. subst s0. do 2 eexists. reflexivity. }
  intros R0 pc0 R3 HQ X3. cbv beta in HQ. injection HQ as ER0 Epc. subst R0 pc0.
  apply SR_ret. replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
  (* The trace from here on. *)
  assert (HKH1 : re_hp e1 <> 0 -> re_kh e1 <> 0).
  { intros Hp. pose proof EOK2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPD2 & _).
    destruct HPD2 as [(H0 & _)|(_ & _ & _ & H8 & _)]; lia. }
  assert (LOR : send_live cl br dd (TD + keys_total (re_keys e1)) =
                ld || send_live cl (brT TD) dd (keys_total (re_keys e1)))
    by exact (rma_live_or cl br dd TD (keys_total (re_keys e1)) Hcl Hbr Hdd TDN (rma_keys_total_nonneg _)).
  assert (GEQ : forall xks jj o ha, map fst xks = key_lens (re_keys e1) ->
     gestures_end_tr lv (bv_unsigned mx) (ds_no sDM) (ds_ocap sDM) xks (ds_ka sDM) (ds_ka sDM) jj o ha =
     gestures_end_tr (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx)
       (bv_unsigned nout1) (bv_unsigned cap1) xks (re_hp e1) (re_kh e1) jj o ha /\
     gestures_end_out lv (bv_unsigned mx) (ds_no sDM) (ds_ocap sDM) xks jj o =
     gestures_end_out (send_live cl (brT TD) dd (keys_total (re_keys e1))) (bv_unsigned mx)
       (bv_unsigned nout1) (bv_unsigned cap1) xks jj o).
  { intros xks jj o ha HX. rewrite SDE, <- KAE.
    split.
    - unfold gestures_end_tr, ent_ka. rewrite (rm_held_eq _ _ _ HKH1). f_equal.
      destruct xks as [|xk xks']; [reflexivity|].
      assert (XL : key_lens (re_keys e1) <> []) by (rewrite <- HX; discriminate).
      unfold brT. rewrite (rm_live_ge cl br dd TD _ Hcl Hbr Hdd (rm_kt_nz _ XL)).
      apply rm_ker_fst. intros LV. destruct (NCF (or_introl LV)) as [Y1 Y2]. split; symmetry; assumption.
    - unfold gestures_end_out. destruct xks as [|xk xks']; [reflexivity|].
      assert (XL : key_lens (re_keys e1) <> []) by (rewrite <- HX; discriminate).
      unfold brT. rewrite (rm_live_ge cl br dd TD _ Hcl Hbr Hdd (rm_kt_nz _ XL)).
      destruct (send_live cl br dd 1) eqn:LVv.
      + destruct (NCF (or_introl eq_refl)) as [Y1 Y2]. rewrite Y1, Y2. reflexivity.
      + rewrite !fi_ker_false. reflexivity. }
  exists L2, A2, R3, m2, md2, e1, h1, O1, junk1, LB, nout1, cap1, out1.
  split; [reflexivity|].
  split.
  { intros r Hr. pose proof Hr as Hr'. unfold callee_saved in Hr'.
    assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]]]; subst r;
      match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X3 eq_refl) end; simp_regs;
      first [ exact (RF2 _ Hr) | unfold rval; reflexivity ]. }
  split; [match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X3 eq_refl) end; simp_regs; reflexivity|].
  split; [match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X3 eq_refl) end; simp_regs; reflexivity|].
  split; [exact CH2|].
  split; [exact INI2|].
  split; [exact RO2|].
  split.
  { pose proof QLs as QL'. rewrite TRDE in QL'.
    exists qs. split; [exact QLs|]. split; [exact RSs|].
    split.
    { intros ext. rewrite TRDE.
      destruct (rm_drain_wf F lv (bv_unsigned mx) NO CAP e h L0 A0 OUT qs ext bnd QL') as (R & _ & _). exact R. }
    split.
    { destruct (rm_drain_wf F lv (bv_unsigned mx) NO CAP e h L0 A0 OUT qs [] bnd QL') as (_ & _ & DB).
      rewrite A1D. exact DB. }
    split.
    { intros CN. destruct LDD as [LD|LD].
      - destruct (LF1 LD) as (_ & Q2' & _). destruct (NCF (or_intror LD)) as [_ Y2]. rewrite OUF, Y2, <- Q2'.
        exact (LOs LD).
      - destruct (LDF0 LD) as (_ & EC & EOu & _). subst cap1 out1.
        assert (AOD : da_out a1M = nm0 OUT).
        { rewrite A1D.
          assert (DF0 : drain_adr lv (bv_unsigned mx) NO CAP e h 0 a0M = drain_adr false (bv_unsigned mx) NO CAP e h 0 a0M).
          { destruct (Z.eq_dec TD 0) as [T0|T0]; [exact (rm_dadr_live _ _ _ _ _ e h 0 a0M J1e HOF (LN0 T0))|].
            rewrite <- (LDNZ T0), LD. reflexivity. }
          rewrite DF0. unfold drain_adr, drain_go. rewrite rm_dr_out_dead. reflexivity. }
        rewrite AOD. unfold known_at. cbn [resolve].
        destruct OUTD1 as [(C0 & _)|(Cp & _ & OI & _)]; [lia|].
        apply (p3c_rp_live Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RP).
        + exact (sptr_of_spec L0 A0 OUT CAP (HND _ _ _ _ HM0) OI).
        + exact Cp.
        + intros [(LT & _)|X0]; [rewrite LD in LT; discriminate | exact (NOE X0)]. }
    split; [exact ELs|].
    intros _. exact SLs. }
  split.
  { destruct FR1 as (jf & FR1). exists jf.
    apply (rm_rp_hi _ _ _ _ _ _ _ _ _ _ _ _ _ (SP - 48) _ M1 RP); [rewrite HSP; lia | cbn [cells_size csize]; lia |
      lia | lia | | exact FR1].
    intros k Hk. apply EDH. lia. }
  split.
  { unfold GLB.
    split; [apply TGD; [exact LK1 | intros t Ht; cbn [cells_size csize] in Ht;
            unfold G_LOCK, G_RELAY_LO, G_S, G_BROKEN, G_EINTR, G_OUTV; lia]|].
    split.
    { apply (rm_rp_imgb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ M1 RP HK WK1). intros k Hk. rewrite length_le4 in Hk.
      assert (IP : img_plain Bm (G_WAKE1 + k)) by (apply IML; unfold G_WAKE1, G_LISTEN; lia).
      split; [exact IP|]. apply EDI; [exact IP | unfold G_WAKE1, G_BROKEN; lia | unfold G_WAKE1, G_EINTR; lia |
        unfold G_WAKE1, G_OUTV; lia | unfold G_WAKE1, G_S, SRC_SIZE in *; lia]. }
    split; [apply TGD; [exact NS1 | intros t Ht; cbn [cells_size csize] in Ht;
            unfold G_NSRC, G_RELAY_LO, G_S, G_BROKEN, G_EINTR, G_OUTV; lia]|].
    split; [exact SRm2|].
    split; [exact CL2|].
    split; [exact BR2|].
    split; [exact DD2|].
    split; [exact EI2 | exact ER2]. }
  split; [exact OVF|].
  split.
  { pose proof rm_tlen as (TL1 & TL2).
    assert (ST1 : rw_cells segs m2 G [CB (length Tpre) Tpre]).
    { apply (rm_rp_bc _ _ _ _ _ _ _ _ _ _ _ _ _ G SRC_TABLE G _ M1 RP FDG GIN);
        [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia | | rewrite SEGS; exact T1].
      intros t Ht. cbn [cells_size csize] in Ht. apply EDG; lia. }
    assert (ST3 : rw_cells segs m2 (SA + 56) [CB (length Tpost) Tpost]).
    { apply (rm_rp_bc _ _ _ _ _ _ _ _ _ _ _ _ _ G SRC_TABLE (SA + 56) _ M1 RP FDG GIN);
        [lia | cbn [cells_size csize]; unfold SRC_TABLE, SRC_ENTRY; lia | | rewrite SEGS; exact T3].
      intros t Ht. cbn [cells_size csize] in Ht. apply EDG; lia. }
    pose proof EOK2 as (_ & _ & P12 & P22 & _).
    rewrite SEGS in ST1, ST3, SL2. rewrite SEGS.
    apply rm_tjoin3.
    - exact (rma_entry_len e1 P12 P22).
    - lia.
    - exact ST1.
    - replace (G + Z.of_nat (length Tpre)) with (G + 56 * Z.of_nat i) by lia. exact SL2.
    - replace (G + Z.of_nat (length Tpre) + 56) with (G + 56 * Z.of_nat i + 56) by lia. exact ST3. }
  split; [exact GI2|].
  split; [exact EOK2|].
  split; [rewrite OUF, HBO; exact ND2|].
  split.
  { intros _. unfold DF. split; [exact SRC2|]. split; [exact OTH2|]. split; [exact HEI2|]. split; [exact HPN2|].
    split; [exact HOF2|]. split; [exact HPV2|]. split; [exact HPC2|]. split; [exact HPP2|]. split; [exact HST2|].
    split; [exact HEX2|]. split; [exact HFX2|]. split; [exact HHL2|].
    split; [exact NDK2|]. split; [exact SSE|]. split; [exact KTE | exact ECE]. }
  split; [intros E1q; lia|].
  split; [exact LB2|].
  split.
  { unfold BF. rewrite OUF, HBI, HBO. split; [|split].
    - intros q m Hq HO HE HH. apply (BFw q m Hq HO). intros X0. apply in_app_iff in X0 as [X0|X0];
        [exact (HE X0) | exact (HH X0)].
    - intros q m Hq. destruct (BRv q m Hq) as [(Q1 & QOo & Q3 & Q4)|[X0|X0]];
        [left; split; [exact Q1 | split; [exact QOo | split; [exact Q3 | exact Q4]]] | right; left; exact X0 |
         right; right; exact X0].
    - intros q m Hq Mp HO HE HH. apply (BFr q m Hq Mp HO). intros X0. apply in_app_iff in X0 as [X0|X0];
        [exact (HE X0) | exact (HH X0)]. }
  split; [exact ODF|].
  split; [exact LDF0|].
  split; [exact LDF1|].
  split; [rewrite SDE; exact KTE|].
  split; [rewrite SDE; exact CAPE|].
  split; [exact GEQ|].
  intros LA. unfold remove_entry_cap, after_drain. rewrite HEt. cbv beta iota zeta. fold finI.
  rewrite <- KTE, rm_klens. unfold gestures_end_cap.
  assert (CPE : bv_unsigned cap1 = ds_ocap finI).
  { destruct LDD as [LD|LD]; [exact (proj2 (NCF (or_intror LD)))|].
    rewrite LOR, LD in LA. cbn [orb] in LA.
    destruct (list_eq_dec Z.eq_dec (key_lens (re_keys e1)) []) as [XN|XN].
    - exfalso. assert (KT0 : keys_total (re_keys e1) = 0).
      { destruct (re_keys e1) as [|k ks0]; [reflexivity | discriminate XN]. }
      rewrite KT0 in LA. unfold send_live, send_off in LA. rewrite Z.eqb_refl, !orb_true_r in LA. cbn in LA.
      discriminate.
    - unfold brT in LA. rewrite (rm_live_ge cl br dd TD _ Hcl Hbr Hdd (rm_kt_nz _ XN)) in LA.
      exact (proj2 (NCF (or_introl LA))). }
  destruct (list_eq_dec Z.eq_dec (key_lens (re_keys e1)) []) as [XN|XN];
    [rewrite XN; cbn [map keys_end_run fst snd]; exact CPE|].
  unfold brT. rewrite (rm_live_ge cl br dd TD _ Hcl Hbr Hdd (rm_kt_nz _ XN)).
  f_equal. apply rm_ker_snd; [|exact CPE]. intros LV. exact (proj1 (NCF (or_introl LV))).
Qed.

Lemma rm_from_H : forall c, AtH c -> SR segs c Final.
Proof using AX BSP CBR CCL CDD CEI CER CNS COV CSR CTX CWK DRC EHI EOK FNC FRC FREEPC GFR GIN GSC HERR4 HFi HN4 HND Hbr Hcl Hdd Hei Hi IM5 IME IML IMR INIT MCP MCS NDB NDF OUTD PRE RES ROOM SEGS SPU SRCP SWK TAB TPE.
  intros c HH.
  assert (HG : SR segs c AtG).
  { destruct (Z.eq_dec (re_eof e) 0) as [E0|E0]; [exact (rm_drain c HH E0) | apply SR_ret; exact (rm_noeof c HH E0)]. }
  eapply SR_bind; [exact HG|]. intros c1 H1.
  eapply SR_bind; [exact (rm_ge c1 H1)|]. intros c2 H2.
  eapply SR_bind; [exact (rm_free c2 H2)|]. intros c3 H3.
  exact (rm_tail c3 H3).
Qed.

End Match.

Lemma rm_entry_at : forall k, (k < length es)%nat ->
  bytes_at rsegs mem0 (G + 56 * Z.of_nat k)
    (le4 (Z_to_bv 64 (re_fd (nth k es no_entry))) ++ le4 (Z_to_bv 64 (re_eof (nth k es no_entry)))).
Proof using EOK O SEGS TAB junk.
  intros k Hk. destruct TAB as [TL TR]. rewrite SEGS in TR. pose proof (rm_rw_bytes _ _ _ _ TR) as B.
  cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  assert (SP0 : concat (map entry_bytes es) ++ tail = concat (map entry_bytes (firstn k es)) ++
                  entry_bytes (nth k es no_entry) ++ concat (map entry_bytes (skipn (S k) es)) ++ tail).
  { rewrite (rma_split_nth es no_entry k Hk) at 1. rewrite map_app, concat_app. cbn [map concat].
    rewrite <- !app_assoc. reflexivity. }
  rewrite SP0 in B. apply bytes_at_app in B as [_ B]. apply bytes_at_app in B as [B _].
  rewrite (rm_catlen (firstn k es)) in B by (intros x Hx; exact (rm_in_firstn _ _ _ Hx)).
  rewrite length_firstn in B. replace (Nat.min k (length es)) with k in B by lia.
  unfold entry_bytes in B. rewrite app_assoc in B. apply bytes_at_app in B as [B _].
  replace (G + 56 * Z.of_nat k) with (G + Z.of_nat (56 * k)) by lia. exact B.
Qed.

Lemma rm_final_none : forall R' m', (forall e0, In e0 es -> re_fd e0 <> FD) -> regs_preserved regs0 R' ->
  rk_chain Bm API RELAY_REMOVE_K Efin (Ffin 0) L0 A0 regs0 mem0 md0 L0 A0 m' md0 -> ro_agree segs m' ->
  rw_cells segs m' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  bytes_at segs m' G_WAKE1 (le4 (Z_to_bv 64 (-1))) ->
  rw_cells segs m' G_SRC [C8 (Z_to_bv 64 G)] ->
  rw_cells segs m' G_CLIENT [C4 (Z_to_bv 64 cl)] ->
  (exists ev', rw_cells segs m' ERR [C4 ev']) ->
  rw_cells segs m' G_NSRC [C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 16)] ->
  table_at Bm m' G es tail ->
  rw_cells segs m' G_BROKEN [C1 (Z_to_bv 8 br)] ->
  rw_cells segs m' G_EINTR [C1 (Z_to_bv 8 ei)] ->
  rw_cells segs m' G_OUTV [C8 mx; C8 nout; C8 cap; C8 out] ->
  Final (mkCfg (YK11.mkst R' (getr regs0 1) m' (seg_rom segs)) md0).
Proof using GIN INIT RES.
  intros R' m' NF RP CH RA LK WK SR1 CL ER NS TB BR EI OV.
  exists L0, A0, R', m', md0, OUT, CAP, junk, [], no_entry, h, tail.
  split; [reflexivity|].
  split; [exact (rk_chain_post Bm API _ _ _ _ _ _ _ _ _ _ _ _ _ CH RP)|].
  split; [exact INIT|].
  split.
  { assert (TR0 : trR = [])
      by (unfold relay_remove_tr; destruct (FD <? 0); [reflexivity | rewrite (rm_find_none FD es NF); reflexivity]).
    exists []. rewrite TR0. split; [reflexivity|]. split; [exact RES|].
    intros i' Hi' HF'. exfalso. exact (NF _ (nth_In _ _ Hi') HF'). }
  split; [exact RA|]. split; [exact LK|]. split; [exact WK|]. split; [exact SR1|]. split; [exact GIN|].
  split; [exact CL|]. split; [exact ER|].
  split; [intros _; split; [exact NS|]; split; [exact TB|]; split; [reflexivity|]; split; [exact BR|];
          split; [exact EI | exact OV]|].
  intros i' Hi' HF'. exfalso. exact (NF _ (nth_In _ _ Hi') HF').
Qed.

(* The no-match end (fd < 0, or no entry has fd): the run wrote only its stack scratch and the lock's count word. *)
Lemma rm_none_munch : forall R' m', (forall e0, In e0 es -> re_fd e0 <> FD) -> regs_preserved regs0 R' ->
  munch [(SP - 144, SP); (203004, 203008)] mem0 m' -> wmono rsegs mem0 m' -> ro_agree rsegs m' ->
  rw_cells rsegs m' G_LOCK [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  Final (mkCfg (YK11.mkst R' (getr regs0 1) m' (seg_rom segs)) md0).
Proof using AX CBR CCL CEI CER CNS COV CSR CWK EHI GFR GIN IME IML IMR INIT PRE RES SEGS TAB.
  intros R' m' NF RP MU' WM' RA' GL'.
  pose proof rm_pre as (HM0 & HW0 & HB0 & HRA & HAL & HCE & H63 & HWS & HTP & HER & Hh & Hl & AC).
  pose proof rm_sf as (E1 & E2 & G1 & G2 & G3 & G4 & G5 & G6).
  destruct rm_K as (K1 & K2 & K3 & K4 & K5).
  pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  rm_hide.
  assert (OW : forall x, 0 <= x < SP - 144 -> (x < 203004 \/ 203008 <= x) -> outside [(SP - 144, SP); (203004, 203008)] x)
    by (intros x X1 X2; cbn [outside]; lia).
  assert (TRC : forall A cs, rw_cells segs mem0 A cs -> (forall t, 0 <= t < Z.of_nat (cells_size cs) ->
            0 <= A + t < SP - 144 /\ (A + t < 203004 \/ 203008 <= A + t)) -> rw_cells segs m' A cs).
  { intros A cs H KK. rewrite SEGS in H |- *. apply (rm_mu_cells _ mem0 m' A cs H MU' WM'). intros t Ht.
    destruct (KK t Ht) as [J1 J2]. exact (OW _ J1 J2). }
  apply rm_final_none.
  - exact NF.
  - exact RP.
  - eapply (rk_chain_munch Bm API AX SEGS); [ | exact MU' | rewrite SEGS; exact WM' | ].
    + apply (rk_chain_refl Bm API); [exact HM0 | exact HW0 | exact HB0 |].
      intros a [Ha|Ha]; [apply HWS; unfold spZ in Ha; rewrite K1 in Ha; lia | apply HER; exact Ha].
    + intros x Hx NO. destruct (rm_not_out _ _ NO) as (lo & hi & Hin & Hr). cbn [In] in Hin.
      destruct Hin as [E|[E|[]]]; injection E as <- <-.
      * left. split; [unfold scratch_k, spZ; rewrite K1; left; lia | lia].
      * right. split; [unfold Efin; right; left; unfold G_LOCK; lia|].
        left. apply IMR. unfold G_RELAY_LO, G_S, SRC_SIZE, SOURCES_MAX. lia.
  - rewrite SEGS. exact RA'.
  - rewrite SEGS. exact GL'.
  - pose proof CWK as WK0. rewrite SEGS in WK0 |- *. apply (rm_mu_bytes _ mem0 m' _ _ WK0 MU').
    intros t Ht. rewrite length_le4 in Ht. apply OW; unfold G_WAKE1; lia.
  - apply TRC; [exact CSR | intros t Ht; cbn [cells_size csize] in Ht; unfold G_SRC; lia].
  - apply TRC; [exact CCL | intros t Ht; cbn [cells_size csize] in Ht; unfold G_CLIENT; lia].
  - destruct CER as (ev & CE). exists ev. apply TRC; [exact CE | intros t Ht; cbn [cells_size csize] in Ht; lia].
  - apply TRC; [exact CNS | intros t Ht; cbn [cells_size csize] in Ht; unfold G_NSRC; lia].
  - destruct TAB as [TL TR]. split; [exact TL|]. apply TRC; [exact TR|]. intros t Ht.
    cbn [cells_size csize] in Ht. unfold RmOr in G4. lia.
  - apply TRC; [exact CBR | intros t Ht; cbn [cells_size csize] in Ht; unfold G_BROKEN; lia].
  - apply TRC; [exact CEI | intros t Ht; cbn [cells_size csize] in Ht; unfold G_EINTR; lia].
  - apply TRC; [exact COV | intros t Ht; cbn [cells_size csize] in Ht; unfold G_OUTV; lia].
Qed.

Ltac rm_rp0 X :=
  let r := fresh "r" in let Hr := fresh "Hr" in let C := fresh "C" in
  intros r Hr; unfold callee_saved in Hr;
  assert (C : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
              r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia;
  destruct C as [C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]]]]]]]]; subst r;
  match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X eq_refl) end; simp_regs;
  first [reflexivity | unfold rval; reflexivity].

Lemma rm_head_all : SR segs (mkCfg (YK11.mkst regs0 (Z_to_bv 64 RELAY_REMOVE) mem0 (seg_rom segs)) md0)
  (fun c => Final c \/ exists i, (i < length es)%nat /\ re_fd (nth i es no_entry) = FD /\ AtH i c).
Proof using AX CBR CCL CEI CER CLK CNS COV CSR CWK EHI EOK GFR GIN HFD HN4 IME IML IMR INIT PRE RES RO0 SEGS SPL SPU SWK TAB.
  pose proof rm_pre as (HM0 & HW0 & HB0 & HRA & HAL & HCE & H63 & HWS & HTP & HER & Hh & Hl & AC).
  pose proof rm_sf as (E1 & E2 & G1 & G2 & G3 & G4 & G5 & G6).
  destruct rm_K as (K1 & K2 & K3 & K4 & K5).
  pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as RSP. change (bv_modulus 64) with (2 ^ 64) in RSP.
  assert (FDE : forall e0, In e0 es -> 0 <= re_fd e0 < 2 ^ 31 /\ (re_eof e0 = 0 \/ re_eof e0 = 1)).
  { intros e0 He0. destruct (proj1 (Forall_forall _ _) EOK e0 He0) as (EF & _ & _ & _ & FR & _).
    split; [exact FR | exact EF]. }
  assert (ROr : ro_agree rsegs mem0) by (rewrite <- SEGS; exact RO0).
  rm_hide. rewrite SEGS.
  destruct (Z_lt_le_dec FD 0) as [FN|FP].
  - assert (STK : stk rsegs mem0 (SP - 8560) SP).
    { split; [lia|]. split; [lia|]. intros a Ha. apply rm_wr_hi; [lia|].
      pose proof (HWS a ltac:(lia)) as W. rewrite SEGS in W. exact W. }
    eapply rm_bridge; [exact ROr | exact Hh | exact Hl | | | ].
    { rewrite rm_mkR_of. eapply rm_neg with (lo := SP - 8560); [apply stk_normalize; [exact STK | lia] | lia | exact FN]. }
    2: { intros s0 (m1n & HE & _). subst s0. do 3 eexists. reflexivity. }
    intros R0 pc0 m0 R' m' HQ X MRl RS. destruct HQ as (m1n & EQ & MUn & WMn).
    injection EQ as ER0 Epc Em. subst R0 pc0 m0.
    destruct (rm_back mem0 m1n m' _ ROr MRl RS MUn WMn) as (MU' & WM' & RA').
    apply SR_ret. left. rewrite (ret_pc_of_ok _ HRA).
    replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
    apply rm_none_munch.
    + intros e0 He0 E. destruct (FDE e0 He0) as [F1 _]. lia.
    + rm_rp0 X.
    + eapply munch_weaken; [|exact MU']. intros x Hx. cbn [outside] in Hx |- *. lia.
    + exact WM'.
    + exact RA'.
    + pose proof CLK as LK0. rewrite SEGS in LK0. apply (rm_mu_cells _ mem0 m' _ _ LK0 MU' WM').
      intros t Ht. cbn [cells_size csize] in Ht. cbn [outside]. unfold G_LOCK. lia.
  - assert (A0E : getr regs0 10 = Z_to_bv 64 FD) by exact (rm_signed_nn _ FP).
    assert (STK : stk rsegs mem0 (SP - 8560) SP).
    { split; [lia|]. split; [lia|]. intros a Ha. apply rm_wr_hi; [lia|].
      pose proof (HWS a ltac:(lia)) as W. rewrite SEGS in W. exact W. }
    eapply rm_bridge; [exact ROr | exact Hh | exact Hl | | | ].
    { rewrite rm_mkR_of.
      eapply (rm_head SPL SPU SWK) with (lo := SP - 8560) (FD := FD) (G := G) (N := N)
        (fdk := fun k => re_fd (nth k es no_entry)) (eofk := fun k => re_eof (nth k es no_entry)).
      - apply stk_normalize; [exact STK | lia].
      - lia.
      - lia.
      - exact A0E.
      - lia.
      - apply rw_cells_normalize; [exact ROr | rewrite <- SEGS; exact CLK |].
        intros k Hk. cbn [cells_size csize] in Hk. apply rm_ro_glob. unfold G_LOCK in *. lia.
      - apply mem_inv_normalize.
      - lia.
      - exact rm_g8.
      - lia.
      - unfold RmOr in G4. lia.
      - lia.
      - intros k Hk. cbv beta. assert (Hk' : (k < length es)%nat) by lia.
        destruct (FDE _ (nth_In es no_entry Hk')) as [F1 F2]. split; [exact F1|]. split; [lia|].
        apply bytes_at_normalize; [exact ROr | exact (rm_entry_at k Hk')].
      - apply bytes_at_normalize; [exact ROr|]. pose proof CNS as B. rewrite SEGS in B. apply rm_rw_bytes in B.
        cbn [cells_bytes cbytes] in B. apply bytes_at_app in B as [B _]. exact B.
      - apply bytes_at_normalize; [exact ROr|]. pose proof CSR as B. rewrite SEGS in B. apply rm_rw_bytes in B.
        cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
      - apply bytes_at_normalize; [exact ROr|]. rewrite <- SEGS. exact CWK. }
    2: { intros s0 HQ0. unfold rm_hq in HQ0.
         destruct HQ0 as (m1n & jf & _ & [(_ & _ & _ & _ & i & _ & _ & _ & t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' &
           a6' & a7' & t3' & t4' & t5' & t6' & [(_ & HE)|(_ & HE)]) | (_ & _ & _ & t0' & t1' & t2' & a0' & a1' & a2' &
           a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & HE)]); subst s0; do 3 eexists; reflexivity. }
    intros R0 pc0 m0 R' m' HQ X MRl RS. unfold rm_hq in HQ.
    destruct HQ as (m1n & jf & WMn & [(MUn & MIn & FRn & GLn & i & Hi & Hfi & Hb & t0' & t1' & t2' & a1' & a2' & a3' &
      a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & [(Heof & EQ)|(Heof & EQ)]) | (NF & MUn & GLn & t0' & t1' & t2' &
      a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & EQ)]);
      injection EQ as ER0 Epc Em; subst R0 pc0 m0;
      destruct (rm_back mem0 m1n m' _ ROr MRl RS MUn WMn) as (MU' & WM' & RA').
    + cbv beta in Hfi, Heof. apply SR_ret. right. exists i. split; [lia|]. split; [exact Hfi|].
      exists R', m'.
      split; [rewrite (proj2 (Z.eqb_eq _ _) Heof), SEGS; reflexivity|].
      split; [rm_rp0 X|].
      split; [rewrite (proj2 (Z.eqb_eq _ _) Heof);
              match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X eq_refl) end; simp_regs; reflexivity|].
      split; [match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X eq_refl) end; simp_regs; reflexivity|].
      split; [unfold W1; replace (SP - 48) with (bv_unsigned (getr regs0 2) + -48) by lia; exact MU'|].
      split; [exact WM'|].
      split; [rewrite SEGS; exact RA'|].
      split; [exists jf; rewrite SEGS; replace (SP - 48) with (bv_unsigned (getr regs0 2) + -48) by lia;
              exact (rw_cells_of_rel rsegs m' m1n _ _ MRl FRn)|].
      rewrite SEGS. exact (rw_cells_of_rel rsegs m' m1n _ _ MRl GLn).
    + cbv beta in Hfi, Heof. apply SR_ret. right. exists i. split; [lia|]. split; [exact Hfi|].
      exists R', m'.
      split; [rewrite (proj2 (Z.eqb_neq _ _) Heof), SEGS; reflexivity|].
      split; [rm_rp0 X|].
      split; [rewrite (proj2 (Z.eqb_neq _ _) Heof);
              match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X eq_refl) end; simp_regs; reflexivity|].
      split; [match goal with |- getr _ ?rr = _ => rewrite (getr_of_eqv _ _ rr X eq_refl) end; simp_regs; reflexivity|].
      split; [unfold W1; replace (SP - 48) with (bv_unsigned (getr regs0 2) + -48) by lia; exact MU'|].
      split; [exact WM'|].
      split; [rewrite SEGS; exact RA'|].
      split; [exists jf; rewrite SEGS; replace (SP - 48) with (bv_unsigned (getr regs0 2) + -48) by lia;
              exact (rw_cells_of_rel rsegs m' m1n _ _ MRl FRn)|].
      rewrite SEGS. exact (rw_cells_of_rel rsegs m' m1n _ _ MRl GLn).
    + apply SR_ret. left. rewrite (ret_pc_of_ok _ HRA).
      replace (seg_rom rsegs) with (seg_rom segs) by (rewrite SEGS; reflexivity).
      apply rm_none_munch.
      * intros e0 He0 E. destruct (In_nth es e0 no_entry He0) as (k & Hk & Ek). apply (NF k ltac:(lia)).
        cbv beta. rewrite Ek. exact E.
      * rm_rp0 X.
      * exact MU'.
      * exact WM'.
      * exact RA'.
      * exact (rw_cells_of_rel rsegs m' m1n _ _ MRl GLn).
Qed.

Lemma rm_main : SR segs (mkCfg (YK11.mkst regs0 (Z_to_bv 64 RELAY_REMOVE) mem0 (seg_rom segs)) md0) Final.
Proof using All.
  eapply SR_bind; [exact rm_head_all|]. intros c [HF|(i & Hi & HFi & HH)].
  - apply SR_ret. exact HF.
  - apply (rm_from_H i); first [exact Hi | exact HFi | exact HH].
Qed.

End Run.

Theorem relay_remove_holds : drain_contract Bm API F -> gestures_end_contract Bm API F -> free_contract_rt Bm API F ->
  free_null_contract Bm -> memcpy_contract -> memcpy_same_contract -> pthread_mutex_lock_contract ->
  pthread_mutex_unlock_contract -> wake_contract -> relay_remove_contract Bm API F.
Proof using AX BSP CTX FREEPC HND.
  intros DRC GSC FRC FNC MCP MCS SPL SPU SWK. unfold relay_remove_contract. cbv zeta.
  intros L A regs mem md bnd es G tail h j fs os O junk cl br dd ei mx nout cap out SEG PRE INI TPE HERR4 EHI RO IMR IML
    IME IM5 HFD CLK CWK CNS CSR HN4 GIN GFR TAB EOK NDF NDB Hcl Hbr Hdd Hei CCL CBR CDD CEI COV CER OUTD RES SRCP ROOM.
  exact (rm_main SEG DRC GSC FRC FNC MCP MCS SPL SPU SWK L A regs mem md bnd es G tail h j fs os O junk cl br dd ei mx
    nout cap out PRE INI TPE HERR4 EHI RO IMR IML IME IM5 HFD CLK CWK CNS CSR HN4 GIN GFR TAB EOK NDF NDB Hcl Hbr Hdd Hei
    CCL CBR CDD CEI COV CER OUTD RES SRCP ROOM).
Qed.

End RMB.
