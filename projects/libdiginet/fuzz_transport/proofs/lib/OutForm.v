(* Modified by Theorem Labs, 2026-10: ported from libreac/fuzz_decode proofs/libreac/fuzz_decode/lib/OutForm.v at bf7779f81ed764787b77895d2f5c0db2627f33f3 for libdiginet/fuzz_transport; no image value changed; module path OSSVerify.Proofs.libdiginet.fuzz_transport.lib. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib Require Import Contract TraceHalting AllocSlots AllocRoom.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
  YK11 YK0h YK0i YK14 YK1b YK1a YK1i YK15 YK0n YP0n YP0m YP02 YH00 YN3f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK0o YK0s YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YO0i YO0f YO0d YO05
  YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YL0i.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

Section d.
Context {fx : YK11.FPState}.

Lemma t_emit_app : forall e1 e2 T, t_eq (t_emit e1 (t_emit e2 T)) (t_emit (e1 ++ e2) T).
Proof.
  intros e1 e2 T tr. unfold t_emit. split.
  - intros [Hp | (tr1 & -> & [Hp | (tr2 & -> & HT)])].
    + left. apply is_prefix_app_r. exact Hp.
    + left. apply is_prefix_app_mono. exact Hp.
    + right. exists tr2. split; [rewrite app_assoc; reflexivity | exact HT].
  - intros [Hp | (tr2 & -> & HT)].
    + apply is_prefix_app_split in Hp as [Hp | (b & -> & Hp)].
      * left. exact Hp.
      * right. exists b. split; [reflexivity | left; exact Hp].
    + right. exists (e2 ++ tr2). split; [rewrite app_assoc; reflexivity |].
      right. exists tr2. split; [reflexivity | exact HT].
Qed.

Lemma t_emit_ext : forall e T T', t_eq T T' -> t_eq (t_emit e T) (t_emit e T').
Proof.
  intros e T T' H tr. unfold t_emit.
  split; intros [Hp | (tr' & -> & HT)];
    [ left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT]
    | left; exact Hp | right; exists tr'; split; [reflexivity | apply H; exact HT] ].
Qed.

Lemma t_alt_const : forall (I : Type) (i0 : I) (F : I -> TSet) (T : TSet),
  (forall i, t_eq (F i) T) -> t_eq (t_alt F) T.
Proof.
  intros I i0 F T H tr. split.
  - intros [i Hi]. exact (proj1 (H i tr) Hi).
  - intro HT. exists i0. exact (proj2 (H i0 tr) HT).
Qed.

Lemma wr_ext : forall ch bs T T', t_eq T T' -> t_eq (wr ch bs T) (wr ch bs T').
Proof. intros ch bs T T' H. unfold wr. apply t_emit_ext. exact H. Qed.

Lemma wr_app : forall ch o1 o2 T, t_eq (wr ch o1 (wr ch o2 T)) (wr ch (o1 ++ o2) T).
Proof. intros ch o1 o2 T. unfold wr. rewrite map_app. apply t_emit_app. Qed.

Lemma wr_split : forall ch bs n out T,
  t_eq (t_emit (map (WriteEv ch) (firstn n bs)) (wr ch (skipn n bs ++ out) T)) (wr ch (bs ++ out) T).
Proof.
  intros ch bs n out T.
  change (t_emit (map (WriteEv ch) (firstn n bs)) (wr ch (skipn n bs ++ out) T))
    with (wr ch (firstn n bs) (wr ch (skipn n bs ++ out) T)).
  eapply t_eq_trans; [apply wr_app |].
  rewrite app_assoc, firstn_skipn. apply t_eq_refl.
Qed.

Section e.
Variable segs : list Segment.

Definition SRO (c : config) (out : list byte) (Q : config -> Prop) : Prop :=
  forall T, (forall c', Q c' -> realizes segs c' T) -> realizes segs c (wr ch_stderr out T).

Definition SRP (c : config) (out : list byte) (Q : config -> list byte -> Prop) : Prop :=
  forall T, (forall c' r, Q c' r -> realizes segs c' (wr ch_stderr r T)) -> realizes segs c (wr ch_stderr out T).

Lemma realizes_wr_nil : forall c T, realizes segs c T -> realizes segs c (wr ch_stderr [] T).
Proof. intros c T H. exact (realizes_emit_nil segs c T H). Qed.

Lemma SR_to_SRO : forall c (Q : config -> Prop), SR segs c Q -> SRO c [] Q.
Proof. intros c Q H T HK. apply realizes_wr_nil. exact (H T HK). Qed.

Lemma SRO_ret : forall c (Q : config -> Prop), Q c -> SRO c [] Q.
Proof. intros c Q HQ. apply SR_to_SRO. apply SR_ret. exact HQ. Qed.

Lemma SRO_bind : forall c o1 o2 (R Q : config -> Prop),
  SRO c o1 R -> (forall c', R c' -> SRO c' o2 Q) -> SRO c (o1 ++ o2) Q.
Proof.
  intros c o1 o2 R Q H1 H2 T HK.
  apply (rz_conseq segs c (wr ch_stderr o1 (wr ch_stderr o2 T))); [| apply wr_app].
  apply H1. intros c' HR. exact (H2 c' HR T HK).
Qed.

Lemma SRO_mono : forall c out (Q Q' : config -> Prop),
  SRO c out Q -> (forall c', Q c' -> Q' c') -> SRO c out Q'.
Proof. intros c out Q Q' H HQ T HK. apply H. intros c' Hq. apply HK, HQ, Hq. Qed.

Lemma SRO_realizes : forall c out (Q : config -> Prop) T,
  SRO c out Q -> (forall c', Q c' -> realizes segs c' T) -> realizes segs c (wr ch_stderr out T).
Proof. intros c out Q T H HK. exact (H T HK). Qed.

Lemma SR_SRO_bind : forall c out (R Q : config -> Prop),
  SR segs c R -> (forall c', R c' -> SRO c' out Q) -> SRO c out Q.
Proof. intros c out R Q H1 H2 T HK. apply (H1 (wr ch_stderr out T)). intros c' HR. exact (H2 c' HR T HK). Qed.

Lemma SRO_SR_bind : forall c out (R Q : config -> Prop),
  SRO c out R -> (forall c', R c' -> SR segs c' Q) -> SRO c out Q.
Proof. intros c out R Q H1 H2 T HK. apply H1. intros c' HR. exact (H2 c' HR T HK). Qed.

Lemma SRO_step : forall ms model ms' out (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' ->
  SRO (mkCfg ms' model) out Q -> SRO (mkCfg ms model) out Q.
Proof.
  intros ms model ms' out Q Hh Hl Hs Hst H T HK.
  exact (rz_step segs ms model ms' _ Hh Hl Hs Hst (H T HK)).
Qed.

Lemma SRO_msteps : forall ms ms' model out (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] -> msteps segs ms ms' ->
  SRO (mkCfg ms' model) out Q -> SRO (mkCfg ms model) out Q.
Proof.
  intros ms ms' model out Q Hh Hl Hms H T HK.
  exact (rz_msteps segs ms ms' model _ Hh Hl Hms (H T HK)).
Qed.

Lemma SRO_node : forall c (I : Type) (nx : I -> config) (i0 : I) out (Q : config -> Prop),
  node_ok segs c I (fun _ => []) nx -> (forall i, SRO (nx i) out Q) -> SRO c out Q.
Proof.
  intros c I nx i0 out Q Hn H T HK.
  exact (rz_silent_allI segs c I nx i0 _ Hn (fun i => H i T HK)).
Qed.

Lemma SRO_cut : forall c out (Q : config -> Prop), budget_refused_at segs c -> SRO c out Q.
Proof. intros c out Q Hb T _. apply rz_cut. exact Hb. Qed.

Lemma SRO_case : forall (A : Prop) c out (Q : config -> Prop),
  (A \/ ~ A) -> (A -> SRO c out Q) -> (~ A -> SRO c out Q) -> SRO c out Q.
Proof. intros A c out Q [a | na] H1 H2; auto. Qed.

Lemma SRP_ret : forall c out (Q : config -> list byte -> Prop), Q c out -> SRP c out Q.
Proof. intros c out Q HQ T HK. exact (HK c out HQ). Qed.

Lemma SRP_bind : forall c out (R Q : config -> list byte -> Prop),
  SRP c out R -> (forall c' r, R c' r -> SRP c' r Q) -> SRP c out Q.
Proof. intros c out R Q H1 H2 T HK. apply H1. intros c' r HR. exact (H2 c' r HR T HK). Qed.

Lemma SRP_mono : forall c out (Q Q' : config -> list byte -> Prop),
  SRP c out Q -> (forall c' r, Q c' r -> Q' c' r) -> SRP c out Q'.
Proof. intros c out Q Q' H HQ T HK. apply H. intros c' r Hq. apply HK, HQ, Hq. Qed.

Lemma SR_SRP_bind : forall c r (R : config -> Prop) (Q : config -> list byte -> Prop),
  SR segs c R -> (forall c', R c' -> SRP c' r Q) -> SRP c r Q.
Proof. intros c r R Q H1 H2 T HK. apply (H1 (wr ch_stderr r T)). intros c' HR. exact (H2 c' HR T HK). Qed.

Lemma SRP_of_SRO : forall c o r (R : config -> Prop) (Q : config -> list byte -> Prop),
  SRO c o R -> (forall c', R c' -> SRP c' r Q) -> SRP c (o ++ r) Q.
Proof.
  intros c o r R Q H1 H2 T HK.
  apply (rz_conseq segs c (wr ch_stderr o (wr ch_stderr r T))); [| apply wr_app].
  apply H1. intros c' HR. exact (H2 c' HR T HK).
Qed.

Lemma SRO_of_SRP : forall c out (Q : config -> Prop),
  SRP c out (fun c' r => Q c' /\ r = []) -> SRO c out Q.
Proof.
  intros c out Q H T HK. apply H. intros c' r [HQ ->]. apply realizes_wr_nil. exact (HK c' HQ).
Qed.

Lemma SRP_wf : forall (W : Type) (RR : W -> W -> Prop), well_founded RR ->
  forall (P : W -> config -> list byte -> Prop) (Q : config -> list byte -> Prop),
  (forall w c r, P w c r -> SRP c r (fun c' r' => Q c' r' \/ exists w', RR w' w /\ P w' c' r')) ->
  forall w c r, P w c r -> SRP c r Q.
Proof.
  intros W RR Hwf P Q Hbody w.
  induction (Hwf w) as [w _ IH].
  intros c r HP. eapply SRP_bind; [apply Hbody, HP |].
  intros c' r' [HQ | (w' & HR & HP')].
  - apply SRP_ret. exact HQ.
  - exact (IH w' HR c' r' HP').
Qed.

Lemma rz_writev_out : forall regs pc mem rom model iovs bs out T,
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 66 ->
  fdchan (Z_to_bv 64 2) ch_stderr model -> getr regs 10 = Z_to_bv 64 2 ->
  w_is0 (iovcnt32 (getr regs 12)) = false ->
  bv_unsigned (getr regs 12) <= IOV_MAX ->
  copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
    (word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
  access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
  iovs_access_okb iovs = true ->
  gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
  iovs_total iovs <= MAX_RW_COUNT ->
  (1 <= length bs)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
     realizes segs (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
       (wr ch_stderr (skipn n bs ++ out) T)) ->
  realizes segs (mkCfg (pend_at regs pc mem rom) model) (wr ch_stderr (bs ++ out) T).
Proof.
  intros regs pc mem rom model iovs bs out T Hh Hlz Hno Hfdc Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hc.
  eapply rz_conseq.
  - exact (rz_writev_dep segs regs pc mem rom model (Z_to_bv 64 2) ch_stderr iovs bs
      (fun n => wr ch_stderr (skipn n bs ++ out) T) Hh Hlz Hno Hfdc fd32_2 Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hc).
  - apply (t_alt_const _ (wr_full bs Hnb)). intros i. cbv beta. apply wr_split.
Qed.

Lemma SRO_writev : forall regs pc mem rom model iovs bs out (Q : config -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 66 ->
  fdchan (Z_to_bv 64 2) ch_stderr model -> getr regs 10 = Z_to_bv 64 2 ->
  w_is0 (iovcnt32 (getr regs 12)) = false ->
  bv_unsigned (getr regs 12) <= IOV_MAX ->
  copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
    (word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
  access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
  iovs_access_okb iovs = true ->
  gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
  iovs_total iovs <= MAX_RW_COUNT ->
  (1 <= length bs)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
     SRO (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
       (skipn n bs ++ out) Q) ->
  SRO (mkCfg (pend_at regs pc mem rom) model) (bs ++ out) Q.
Proof.
  intros regs pc mem rom model iovs bs out Q Hh Hlz Hno Hfdc Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hc T HK.
  apply (rz_writev_out regs pc mem rom model iovs bs out T Hh Hlz Hno Hfdc Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb).
  intros n H1 H2. exact (Hc n H1 H2 T HK).
Qed.

Lemma SRP_writev : forall regs pc mem rom model iovs bs r (Q : config -> list byte -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 66 ->
  fdchan (Z_to_bv 64 2) ch_stderr model -> getr regs 10 = Z_to_bv 64 2 ->
  w_is0 (iovcnt32 (getr regs 12)) = false ->
  bv_unsigned (getr regs 12) <= IOV_MAX ->
  copy_iovecs_aux (ms_read_byte (pend_at regs pc mem rom)) (getr regs 11)
    (word_to_nat (iovcnt32 (getr regs 12))) = ImpOk iovs ->
  access_okb (getr regs 11) (16 * bv_unsigned (getr regs 12)) = true ->
  iovs_access_okb iovs = true ->
  gather_iovecs (ms_read_byte (pend_at regs pc mem rom)) iovs = Some bs ->
  iovs_total iovs <= MAX_RW_COUNT ->
  (1 <= length bs)%nat ->
  (forall n, (1 <= n)%nat -> (n <= length bs)%nat ->
     SRP (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
       (skipn n bs ++ r) Q) ->
  SRP (mkCfg (pend_at regs pc mem rom) model) (bs ++ r) Q.
Proof.
  intros regs pc mem rom model iovs bs r Q Hh Hlz Hno Hfdc Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb Hc T HK.
  apply (rz_writev_out regs pc mem rom model iovs bs r T Hh Hlz Hno Hfdc Hfd Hcnt Hmax Himp Hiok Hbok Hg Htot Hnb).
  intros n H1 H2. exact (Hc n H1 H2 T HK).
Qed.

Lemma SRP_writev2 : forall regs pc mem rom model (b0 l0 b1 l1 : word) bs0 bs1 r (Q : config -> list byte -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 66 ->
  fdchan (Z_to_bv 64 2) ch_stderr model -> getr regs 10 = Z_to_bv 64 2 ->
  getr regs 12 = Z_to_bv 64 2 ->
  ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
  ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
  ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 16)) = Some b1 ->
  ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 24)) = Some l1 ->
  ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
  ms_read_bytes (pend_at regs pc mem rom) b1 l1 = Some bs1 ->
  access_okb (getr regs 11) 32 = true ->
  access_okb b0 (bv_unsigned l0) = true -> access_okb b1 (bv_unsigned l1) = true ->
  1 <= bv_unsigned l0 + bv_unsigned l1 <= MAX_RW_COUNT ->
  (forall n, (1 <= n)%nat -> (n <= length (bs0 ++ bs1))%nat ->
     SRP (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
       (skipn n (bs0 ++ bs1) ++ r) Q) ->
  SRP (mkCfg (pend_at regs pc mem rom) model) ((bs0 ++ bs1) ++ r) Q.
Proof.
  intros regs pc mem rom model b0 l0 b1 l1 bs0 bs1 r Q
    Hh Hlz Hno Hfdc Hfd Hcnt Hb0 Hl0 Hb1 Hl1 Hbs0 Hbs1 Hiok Hok0 Hok1 Htot Hc.
  rewrite <- read_bytes_map_read_byte in Hbs0, Hbs1.
  pose proof (gather_iovecs_2 _ _ _ _ _ _ _ Hbs0 Hbs1) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
  pose proof (read_bytes_map_length _ _ _ _ Hbs0). pose proof (read_bytes_map_length _ _ _ _ Hbs1).
  unfold MAX_RW_COUNT in Htot.
  apply (SRP_writev regs pc mem rom model [(b0, l0); (b1, l1)] (bs0 ++ bs1) r Q Hh Hlz Hno Hfdc Hfd).
  - rewrite Hcnt. reflexivity.
  - rewrite Hcnt. cbv. discriminate.
  - rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 2))) with 2%nat.
    apply copy_iovecs_2; try assumption; lia.
  - rewrite Hcnt. exact Hiok.
  - cbn [iovs_access_okb forallb fst snd]. rewrite Hok0, Hok1. reflexivity.
  - exact Hg.
  - cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
  - lia.
  - exact Hc.
Qed.

Lemma SRP_writev1 : forall regs pc mem rom model (b0 l0 : word) bs0 r (Q : config -> list byte -> Prop),
  m_halted model = None -> m_vm_lazy model = [] ->
  bv_unsigned (getr regs 17) = 66 ->
  fdchan (Z_to_bv 64 2) ch_stderr model -> getr regs 10 = Z_to_bv 64 2 ->
  getr regs 12 = Z_to_bv 64 1 ->
  ms_read_u64 (pend_at regs pc mem rom) (getr regs 11) = Some b0 ->
  ms_read_u64 (pend_at regs pc mem rom) (Z_to_bv 64 (bv_unsigned (getr regs 11) + 8)) = Some l0 ->
  ms_read_bytes (pend_at regs pc mem rom) b0 l0 = Some bs0 ->
  access_okb (getr regs 11) 16 = true ->
  access_okb b0 (bv_unsigned l0) = true ->
  1 <= bv_unsigned l0 <= MAX_RW_COUNT ->
  (forall n, (1 <= n)%nat -> (n <= length bs0)%nat ->
     SRP (mkCfg (mkst (regupd regs 10 (Z_to_bv 64 (Z.of_nat n))) (v_addi pc 4) mem rom) model)
       (skipn n bs0 ++ r) Q) ->
  SRP (mkCfg (pend_at regs pc mem rom) model) (bs0 ++ r) Q.
Proof.
  intros regs pc mem rom model b0 l0 bs0 r Q Hh Hlz Hno Hfdc Hfd Hcnt Hb0 Hl0 Hbs0 Hiok Hok0 Htot Hc.
  rewrite <- read_bytes_map_read_byte in Hbs0.
  pose proof (gather_iovecs_1 _ _ _ _ Hbs0) as Hg.
  pose proof (gather_iovecs_length _ _ _ Hg) as Hlen. cbn [iovs_total] in Hlen.
  pose proof (read_bytes_map_length _ _ _ _ Hbs0).
  unfold MAX_RW_COUNT in Htot.
  apply (SRP_writev regs pc mem rom model [(b0, l0)] bs0 r Q Hh Hlz Hno Hfdc Hfd).
  - rewrite Hcnt. reflexivity.
  - rewrite Hcnt. cbv. discriminate.
  - rewrite Hcnt. change (word_to_nat (iovcnt32 (Z_to_bv 64 1))) with 1%nat.
    apply copy_iovecs_1; try assumption; lia.
  - rewrite Hcnt. exact Hiok.
  - cbn [iovs_access_okb forallb fst snd]. rewrite Hok0. reflexivity.
  - exact Hg.
  - cbn [iovs_total]. unfold MAX_RW_COUNT. lia.
  - lia.
  - exact Hc.
Qed.

End e.
End d.

Definition out_shape (f : list byte -> list byte) : lib_shape :=
  {| LIBK := fun pl fs K => wr ch_stderr (f pl) (K (LL 0 fs (f pl)));
     LIBK_ext := fun pl fs K K' H => wr_ext ch_stderr (f pl) _ _ (H (LL 0 fs (f pl)));
     lib_delta := fun _ b => b;
     lib_room := fun b n => sb_live b <= 64 /\ 0 <= sb_bytes b <= 2 ^ 28 /\ sb_cap b = CAPMAX |}.

Lemma out_LIBK : forall f pl fs K,
  @LIBK (out_shape f) pl fs K = wr ch_stderr (f pl) (K (LL 0 fs (f pl))).
Proof. reflexivity. Qed.

Lemma permitted_prefix_o : forall allowed (a b : list event),
  is_prefix a b -> Forall (permitted_event allowed) b -> Forall (permitted_event allowed) a.
Proof.
  intros allowed a. induction a as [|x a IH]; intros b H HF.
  - constructor.
  - destruct b as [|y b]; [contradiction |].
    cbn in H. destruct H as [-> H]. inversion HF; subst.
    constructor; [assumption |]. eapply IH; eassumption.
Qed.

Lemma permitted_emit_o : forall allowed es T,
  Forall (permitted_event allowed) es -> permitted_traces allowed T ->
  permitted_traces allowed (t_emit es T).
Proof.
  intros allowed es T HE HT tr [HP | (tail & -> & Htail)].
  - eapply permitted_prefix_o; eassumption.
  - apply Forall_app. split; [exact HE | apply HT; exact Htail].
Qed.

Lemma permitted_wr_o : forall allowed ch bs T,
  permitted_traces allowed T -> permitted_traces allowed (wr ch bs T).
Proof.
  intros allowed ch bs T HT. apply permitted_emit_o; [| exact HT].
  apply Forall_map. apply Forall_forall. intros x _. exact I.
Qed.

Lemma permitted_ex_o : forall allowed code fs,
  In (Z_to_bv 64 code) allowed -> permitted_traces allowed (ex code fs).
Proof.
  intros allowed code fs Hin. apply permitted_emit_o.
  - constructor; [exact Hin | constructor].
  - intros tr ->. constructor.
Qed.

Lemma permitted_out_LIBK : forall allowed f pl fs K,
  (forall l, permitted_traces allowed (K l)) ->
  permitted_traces allowed (@LIBK (out_shape f) pl fs K).
Proof. intros allowed f pl fs K HK. exact (permitted_wr_o allowed ch_stderr (f pl) _ (HK _)). Qed.

Lemma permitted_iter_out : forall allowed f pl j K fs,
  (forall fs', permitted_traces allowed (K fs')) ->
  permitted_traces allowed (lib_iter (LS:=out_shape f) pl j K fs).
Proof.
  intros allowed f pl j. induction j as [|j IH]; intros K fs HK; cbn [lib_iter].
  - apply HK.
  - apply permitted_out_LIBK. intros l. apply IH. exact HK.
Qed.

Lemma permitted_run_out : forall allowed f pl k fs,
  In (Z_to_bv 64 0) allowed ->
  permitted_traces allowed (run_shape (LS:=out_shape f) pl k fs).
Proof.
  intros allowed f pl [|k] fs H0; cbn [run_shape].
  - apply permitted_ex_o. exact H0.
  - apply permitted_out_LIBK. intros l. apply permitted_wr_o. apply permitted_iter_out. intros fs'.
    destruct k; cbn [run_tail].
    + apply permitted_ex_o. exact H0.
    + apply permitted_wr_o. apply permitted_ex_o. exact H0.
Qed.

Section Slot.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Let segs := ms_segs B.

Definition lib_post_o (out : list byte) (G : list (Z * Z)) (stk : Z) (L : layout) (A : astate)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (p n : Z) (b : sbound) (l : lleaf)
    (L' : layout) (A' : astate) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  lib_post_g B API G stk L A regs mem md p n b (LL (ll_ret l) (ll_fs l) []) L' A' regs' mem' md' /\
  ll_out l = out.

Definition lib_contract_o (f : list byte -> list byte) (G R : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop) (j : nat) (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b (K : lleaf -> TSet),
    lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
    fdchan (Z_to_bv 64 2) ch_stderr md ->
    GI j mem ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    frm_zero fp_csr ->
    (forall (l : lleaf) (c' : config),
       (exists (fx' : FPState) L' A' regs' mem' md',
          c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
          frm_zero (@fp_csr fx') /\
          lib_post_o (f pl) G stk L A regs mem md p n b l L' A' regs' mem' md' /\
          GI (S j) mem') ->
       realizes segs c' (K l)) ->
    realizes segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (LIBK pl (m_fs md) K).

Definition lib_slot_o (f : list byte -> list byte) (G R : list (Z * Z))
    (GI : nat -> (word -> option byte) -> Prop) (j : nat) (pc ra empty stk : Z) : Prop :=
  forall L A regs mem md p n pl b,
    lib_pre_x B API stk empty L A regs mem md ra p n pl b ->
    fdchan (Z_to_bv 64 2) ch_stderr md ->
    GI j mem ->
    G_img_c B R mem ->
    ro_agree segs mem ->
    frm_zero fp_csr ->
    SRO segs (mkCfg (mkst regs (Z_to_bv 64 pc) mem (seg_rom segs)) md) (f pl)
      (fun c' => exists (fx' : FPState) L' A' regs' mem' md',
         c' = mkCfg (@mkst fx' regs' (Z_to_bv 64 ra) mem' (seg_rom segs)) md' /\
         frm_zero (@fp_csr fx') /\
         lib_post_g B API G stk L A regs mem md p n b (LL 0 (m_fs md) []) L' A' regs' mem' md' /\
         GI (S j) mem').

Lemma lib_contract_o_of_g : forall G R GI j pc ra empty stk,
  lib_contract_g B API G R GI j pc ra empty stk ->
  lib_contract_o (fun _ => []) G R GI j pc ra empty stk.
Proof.
  intros G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre _ HGI HR Hro Hfrm HK.
  apply (H L A regs mem md p n pl b K Hpre HGI HR Hro (lib_pre_x_sp B API stk empty L A regs mem md ra p n pl b Hpre) Hfrm).
  intros [r fs o] c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & HGI').
  assert (Ho : o = []).
  { destruct Hpost as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ho & _). exact Ho. }
  subst o. apply HK. exists fx', L', A', regs', mem', md'.
  split; [exact Hc |]. split; [exact Hf |]. split; [| exact HGI'].
  unfold lib_post_o. split; [exact Hpost | reflexivity].
Qed.

End Slot.

Section Out.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.

Lemma lib_contract_o_of_slot : forall f G R GI j pc ra empty stk,
  lib_slot_o (LS:=out_shape f) B API f G R GI j pc ra empty stk ->
  lib_contract_o (LS:=out_shape f) B API f G R GI j pc ra empty stk.
Proof.
  intros f G R GI j pc ra empty stk H L A regs mem md p n pl b K Hpre Hfd HGI HR Hro Hfrm HK.
  refine (H L A regs mem md p n pl b Hpre Hfd HGI HR Hro Hfrm (K (LL 0 (m_fs md) (f pl))) _).
  intros c' (fx' & L' & A' & regs' & mem' & md' & Hc & Hf & Hpost & HGI').
  apply HK. exists fx', L', A', regs', mem', md'.
  split; [exact Hc |]. split; [exact Hf |]. split; [| exact HGI'].
  unfold lib_post_o. split; [exact Hpost | reflexivity].
Qed.

End Out.
