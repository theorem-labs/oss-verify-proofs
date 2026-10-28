From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import State.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundI SymSoundR SymCFG.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv RingBuf RingCfg.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import r2_cuts r2_ex_base r2_ex_vals r2_ex_defs.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U.L7 Require Import S_r2.
Import ListNotations.
Open Scope Z_scope.
Import R2C R2X R2E.

(* The obligation of one exit node E against the cut list: the exit lemma shape of rcfg_complete_auto. t-L10's and t-L4's
   exit lemmas (r2_ex_exits.v, r2_ex_clip.v) prove ex_ok cuts E for any cuts containing the node the exit re-enters. *)
Definition ex_ok (cuts : list rnode) (E : rnode) : Prop :=
  forall K rho0 rho, rn_ghost NF VN LN LP rho0 E rho ->
    etriple segsU (SP segsU K (rn_state E) rho)
      (fun w => SPfamE segsU K (map (to_enodeR NF VN LN LP rho0) cuts) (rmeas LN E rho) w
                \/ LQ segsU K NF rho0 Posts_r2U w).

(* r2_sum_ex from the ring-CFG check and the exit lemmas, over the forced-clip region's cut pcs and nodes (r2_ex_g.v). *)
Section Gen.
Variables (cpsG : list Z) (cutsG exitsG : list rnode).
Let cps := ecutpcs_base ++ cpsG.
Let cuts := rcuts_base ++ cutsG.
Let exits := rexits_base ++ exitsG.
Hypothesis rchk : check_rcfg segsU NF VN LN LP 1000 cps cuts exits = true.
Hypothesis exs : Forall (ex_ok cuts) exits.
Theorem r2_sum_ex_gen : r2_sum_ex_stmt_U.
Proof.
  intros K rho w Hw.
  assert (Hn : nval VN rho < 2 ^ 32).
  { destruct w as [tr [ms md]]. destruct Hw as [Hsm _].
    pose proof (smatch_facts segsU _ _ _ Hsm) as HF.
    pose proof (base_n rho [] HF) as X. unfold nval. change VN with 13%positive. lia. }
  refine (rcfg_complete_auto segsU NF VN LN LP rho 1000 cps cuts exits K
            (LQ segsU K NF rho Posts_r2U) rchk _ N_Pre rho ltac:(apply in_or_app; left; left; reflexivity) _ w Hw).
  - intros E rho' HinE HG. exact (proj1 (Forall_forall _ _) exs E HinE K rho rho' HG).
  - split; [|split; [|split]]; try exact Logic.I.
    + split; [|split; [|split]]; intros; try reflexivity. exact Hn.
    + intros HX. discriminate HX.
Qed.
End Gen.
