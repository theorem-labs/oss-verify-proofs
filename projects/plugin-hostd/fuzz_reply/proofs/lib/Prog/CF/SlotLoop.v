From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0 Contract FrameAPI SlotKept SlotPack AllocPack.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import StatementKept SlotInv SlotSteps.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog.CF Require Import SRCF SRCF3.
Import ListNotations.
Local Open Scope Z_scope.

Lemma frame_LIBK : forall B API LS SH SK ra empty, frame_facts B API LS SH SK ra empty ->
  forall pl fs K, @LIBK LS pl fs K = K (LL 0 fs []).
Proof.
  intros B API LS SH SK ra empty H. do 28 (destruct H as [_ H]). exact (proj1 H).
Qed.

Lemma LI_bounds : forall rc B API E RI t k c, LI (rc := rc) B API E RI t k c ->
  0 <= t <= OPS_MAX /\ 0 <= k <= ss_n E.
Proof.
  intros rc B API E RI t k c
    (fx' & L & A & regs & mem & md & cl & br & gn & dd & ei & G & nfd & mx & nout & cap & out & es & hj &
     _ & _ & HT & HK & _).
  split; assumption.
Qed.

Theorem slot_of_steps : forall CS RI,
  entry_ok CS RI -> (forall op, 0 <= op < 10 -> pass_ok RI op) -> exit_ok CS RI -> fuzz_reply_slot_p3 CS frame_MCAP.
Proof.
  intros CS RI HE HP HX HCS B API LS SH SK ra empty FF rc fx j Hj.
  intros L A regs mem md p n pl b T K Hpre Hres Hpe Hmis HGI Htb Hpn HR Hro Hsp Hfrm HK.
  set (E := SS L A regs mem md p n pl b T).
  assert (HF : slot_frame B API LS SH SK ra empty rc fx j E CS).
  { split; [exact FF|]. split; [exact Hj|]. split; [unfold slot_pre; cbn; tauto|exact HCS]. }
  rewrite (frame_LIBK B API LS SH SK ra empty FF).
  assert (LOOP : forall t k c, LI (rc := rc) B (API rc) E RI t k c ->
            SR (ms_segs B) c (slot_post (rc := rc) (SH := SH) (SK := SK) B (API rc) ra j E CS)).
  { intros t k c HL.
    apply (SR_loopZ (ms_segs B) (Z * Z) (fun w => OPS_MAX - fst w)
             (fun w c => LI (rc := rc) B (API rc) E RI (fst w) (snd w) c)) with (w := (t, k)); [|exact HL].
    intros [t0 k0] c0 HL0. cbn [fst snd] in *.
    destruct (LI_bounds _ _ _ _ _ _ _ _ HL0) as [Bt Bk].
    destruct (head_body E t0 k0) eqn:HB.
    - unfold head_body in HB. apply andb_prop in HB as [H1 H2]. apply Z.ltb_lt in H1, H2.
      pose proof (Z.mod_pos_bound (in_byte E k0) 10 ltac:(lia)) as Hop.
      eapply SR_mono; [exact (HP (op_at E k0) Hop B API LS SH SK ra empty rc fx j E CS HF t0 k0 c0 HL0 H1 H2 eq_refl)|].
      intros c' [k' HL']. right. exists (t0 + 1, k'). cbn [fst snd]. split; [lia|exact HL'].
    - eapply SR_mono; [apply (HX B API LS SH SK ra empty rc fx j E HF t0 k0 c0 HL0)|].
      + unfold head_body in HB. apply andb_false_iff in HB as [H1|H1]; apply Z.ltb_ge in H1; lia.
      + intros c' Hc'. left. exact Hc'. }
  apply (SR_realizes (ms_segs B) (slot_cfg (fx := fx) B E)
           (slot_post (rc := rc) (SH := SH) (SK := SK) B (API rc) ra j E CS)).
  - eapply SR_bind; [exact (HE B API LS SH SK ra empty rc fx j E HF)|].
    intros c [Hp|Hl]; [apply SR_ret; exact Hp|exact (LOOP 0 0 c Hl)].
  - intros c' Hc'. apply HK. exact Hc'.
Qed.
