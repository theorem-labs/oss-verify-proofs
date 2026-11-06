From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.U.Reusable Require Import YK11 YM05 YM06 YM06_cf YO0i YO0f YO0d YO0d_cf.
Import ListNotations.
Open Scope Z_scope.

(* Cut-free twin of CallocKB.mreal_post. *)
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma mreal_cf_post {R} : forall segs (t : itree astate R) c (Q Q' : R -> config -> Prop),
  mreal_cf segs c t Q -> (forall r c', Q r c' -> SR_cfv segs c' (Q' r)) -> mreal_cf segs c t Q'.
Proof using.
  intros segs t. induction t as [r | q s k IH | f]; intros c Q Q' H HK; cbn in *.
  - eapply SR_cfv_bind; [exact H | exact (HK r)].
  - eapply SR_cfv_mono; [exact H |]. intros c1 Hk.
    eapply knode_cf_mono; [| exact Hk]. intros z c2 Hc2. exact (IH z c2 Q Q' Hc2 HK).
  - exact I.
Qed.
End a.
