From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable Require Import YK11 YK0s YK0i YM06 YP09 YM05 YK15 YM02.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable Require Import YO0i YO0f YO0g YO0q YO0x YO0d YO0e YO05 YO02 YO03 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO04.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U.Reusable Require Import YO16 YL01 YK1j YO10 YO0s YO0u YO15 YN03 YN2b YN33.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import AllocSI AllocGS AllocFree AllocMalloc AllocRealloc.
From OSSVerify.Proofs.libreac.fuzz_knock.lib.U Require Import AllocPackGSF AllocPackGSFm.
Import ListNotations.
Local Open Scope Z_scope.

(* realloc keeps GSF. By ra_cases: the in-place resizes (rs_am) change only the slots of the meta; the class-63
   remap (rm_state) installs rm_am, whose class is 63 (GSF is vacuous above class 48), and changes only the regions
   otherwise; the move is malloc then free (ra_move), which keep GSF (malloc_GSF, free_GSF). *)

Lemma gf_rs_am a i off n : gfc a -> gfc (rs_am a i off n).
Proof. intros H. apply (gf_shape a); [reflexivity | reflexivity | reflexivity | exact H]. Qed.

Lemma gf_rm s g a i off n : am_sc a = 63 -> GSF s -> GSF (rm_state s g a i off n).
Proof.
  intros H63 HG. apply (gf_metas (rm_mid s g a i off n)); [reflexivity|]. unfold rm_mid. apply gf_upd.
  - intros a' E. injection E as E. subst a'. unfold gfc. intros _ Hsc _. exfalso.
    change (am_sc a < 48) in Hsc. lia.
  - apply (gf_metas s); [reflexivity | exact HG].
Qed.

Theorem realloc_GSF : forall s p k n tr r s', WF s -> In (p, k) (user_blocks s) -> GSF s -> 0 <= n ->
  yields (realloc (Some p) n s) tr (r, s') -> GSF s'.
Proof.
  intros s p k n tr r s' HW Hin HG Hn Y.
  destruct (ra_cases answer_ok s p k n tr r s' HW Hin (rpath_yields _ _ _ Y))
    as [(_ & ->) | (g & am & i & fr & Hu & _ & _ & _ & _ & _ & C)]; [exact HG|].
  pose proof (gf_MT s g am HG (proj1 (usedX_MT _ _ _ _ Hu))) as Ha.
  destruct C as [(_ & _ & ->) | [(_ & _ & _ & _ & ->) | [(H63 & _ & _ & _ & ->) | (tr' & Hm)]]].
  - apply gf_upd; [|exact HG]. intros a E. injection E as E. subst a. exact (gf_rs_am am i (fr_off fr) n Ha).
  - apply gf_upd; [|exact HG]. intros a E. injection E as E. subst a. exact (gf_rs_am am i (fr_off fr) n Ha).
  - exact (gf_rm s g am i (fr_off fr) n H63 HG).
  - destruct (ra_move answer_ok p n s tr' r s' Hm) as (tr1 & q & s1 & H1 & Hq).
    pose proof (malloc_GSF s n tr1 q s1 HW HG Hn (yields_rpath _ _ _ H1)) as HG1.
    destruct q as [q|]; [destruct Hq as (_ & tr2 & H2) | destruct Hq as (_ & ->); exact HG1].
    exact (free_GSF s1 p tr2 s' HG1 (yields_rpath _ _ _ H2)).
Qed.

Theorem realloc_null_GSF : forall s n tr r s', WF s -> GSF s -> 0 <= n -> yields (realloc None n s) tr (r, s') -> GSF s'.
Proof. intros s n tr r s' HW HG Hn Y. exact (malloc_GSF s n tr r s' HW HG Hn Y). Qed.
