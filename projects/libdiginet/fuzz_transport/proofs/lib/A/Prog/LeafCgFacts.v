(* LeafCgFacts: LeafCgKit.v's cgif facts proved at decode's own definitions (image A, on the relocated core).
   ret_ok_stmt at YK0s.ret_ok (lib/Reusable/YK0s.v:193, the relocated copy of cgif's YK0s.v:192) is the released
   lemma lib/Prog/KindB.v:188 ret_pc_of_ok.
   aview_ext_stmt / aview_some_stmt at YG0n.aview segs (lib/Reusable/YG0n.v:18, cgif's YG0n.v:17): one unfolding
   each, the same steps as YCbq.v:148 aview_eq_of / :135 aview_some_of_apresent.
   bridge_evtF_stmt at YA0n.SRr rsegs: YA0nR.SRr_fevt (lib/Reusable/YA0nR.v + YK04R.v), after reading decode's footprint run
   ExecF.mstepsF as YK04R.fsteps (the same step predicate: ExecF.mstepF's body is YK04R.fstep's) and with
   wx_segs_nowrap rsegs computed (as A/DecodeCallocSeed.v:40 decode_wx). *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YP09 YK04 YA0n YG0f YG00 YG0d YG0n YG0q YG0s YA0o YK04R YA0nR.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog Require KindB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LeafCgKit.

Lemma ret_ok_stmt_YK0s : @LeafCgKit.ret_ok_stmt YK0s.ret_ok.
Proof. exact KindB.ret_pc_of_ok. Qed.

Section Core. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma aview_ext_stmt_YG0n : forall segs, @LeafCgKit.aview_ext_stmt (aview segs).
Proof.
  intros segs H mem mem' a E. unfold aview, mbyte, mrestrict. rewrite E. reflexivity.
Qed.

Lemma aview_some_stmt_YG0n : forall segs, @LeafCgKit.aview_some_stmt (aview segs).
Proof.
  intros segs H mem a Hh Hm. unfold aview, mbyte, mrestrict. rewrite Hh.
  destruct (mem (Z_to_bv 64 a)) as [b|]; [cbn; discriminate | contradiction].
Qed.

(* decode's footprint run is YK04R's (ExecF.mstepF RNG = YK04R.fstep segs RNG, acc_in unfolded). *)
Lemma fsteps_of_mstepsF : forall segs RNG ms ms',
  ExecF.mstepsF segs RNG ms ms' -> YK04R.fsteps segs RNG ms ms'.
Proof.
  intros segs RNG ms ms' Hr. induction Hr as [ms | ms ms1 ms2 Hs _ IH].
  - apply fsteps_refl.
  - eapply fsteps_cons; [exact Hs | exact IH].
Qed.

Lemma rsegs_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

Lemma bridge_evtF_stmt_YA0n :
  @LeafCgKit.bridge_evtF_stmt (world rsegs) (@w_H rsegs) (SRr rsegs) same_but_materialized.
Proof.
  intros W ms model RNG P Q (ms' & Hr & HP) Hfp Hk.
  apply (SRr_fevt rsegs rsegs_wx W ms model RNG P Q).
  - exists ms'. split; [apply fsteps_of_mstepsF; exact Hr | exact HP].
  - exact Hfp.
  - exact Hk.
Qed.

(* The four kit facts cgif proves at its AR (YA0n.v:39, YG0q.v:757, YG0s.v:170), instantiated; AR_sbm by AR_frame_law
   at mem' = mem, the model read as YA0o.v:27 same_but_materialized_wvb (as cgif's AD1y.v:139 / decode's YD1y.v:146). *)
Lemma SRr_ret_stmt_YA0n : forall segs, @LeafCgKit.SRr_ret_stmt (world segs) (SRr segs).
Proof. intros segs W c Q HQ. exact (SRr_ret segs W c Q HQ). Qed.

Lemma AR_frame_stmt_YG0q : forall segs B,
  @LeafCgKit.AR_frame_stmt (world segs) (@w_H segs) alayout astate (AR segs B) (aview segs) (aowned B).
Proof.
  intros segs B ly S W mem md mem' HAR Hown Hvis Hhid.
  apply (AR_frame_law_ok segs B ly S W mem md mem' md HAR Hown Hvis); [reflexivity | reflexivity | reflexivity |].
  intros a _ Ha. exact (Hhid (w64 a) Ha).
Qed.

Lemma AR_stack_stmt_YG0s : forall segs B,
  @LeafCgKit.AR_stack_stmt (world segs) alayout astate (AR segs B) ly_stk_lo ly_stk_hi (aowned B).
Proof. intros segs B. exact (AR_stack_law_ok segs B). Qed.

Lemma AR_sbm_stmt_YG0q : forall segs B,
  @LeafCgKit.AR_sbm_stmt (world segs) alayout astate (AR segs B) same_but_materialized.
Proof.
  intros segs B ly S W mem md md' HAR Hs. rewrite (same_but_materialized_wvb md md' Hs).
  apply (AR_frame_law_ok segs B ly S W mem md mem _ HAR).
  - intros; reflexivity.
  - intros a Ha; exact Ha.
  - reflexivity.
  - apply m_vm_lazy_wvb.
  - unfold eager_used. rewrite m_vm_lazy_wvb. reflexivity.
  - intros; reflexivity.
Qed.

End Core.
