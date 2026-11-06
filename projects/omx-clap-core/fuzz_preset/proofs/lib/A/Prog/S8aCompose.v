(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumWalk.v, with its module names changed; 118 of its 137 lines of code are new or changed and 25 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102): the COMPOSITION of ex_value's eleven pieces into the text
   tex_value_specX (lib/A/PRH_FnEx.v). ex_value_compose takes the eleven pieces as the lanes' specs
   (S8aIface.v: ev_entry_spec, ev_disp_spec, ev_number_spec, ev_items_open_spec, ev_item_spec, ev_items_close_spec,
   ev_items_end_spec, ev_exit_spec) and proves `forall n, tex_value_specX n` by two inductions:
   ev_items_loop over the remaining text (pieces 7 + 8 + 9 + 10) and the outer one on the nesting n (the recursion,
   where ev_item_spec n' is discharged from the IH tex_value_specX n'). Engine-free: only SRr_bind / SRr_mono and the
   piece specs. No number is image-dependent here. #102: the kit's tex_value_specX quantifies the ledger's two new cells
   (`.. fail ran most own`, walkkit-next decff67d721f), so the activation takes them as ea_most / ea_own. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From Stdlib Require Import Lia.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* the eleven pieces, as the lanes prove them (S8aIface.v) *)
Hypothesis HENTRY : ev_entry_spec B ARx SK.
Hypothesis HDISP  : ev_disp_spec B ARx SK.
Hypothesis HNUM   : ev_number_spec B ARx SK.
Hypothesis HOPEN  : ev_items_open_spec B ARx SK.
Hypothesis HITEM  : forall n', tex_value_specX B ARx SK n' -> ev_item_spec B ARx SK n'.
Hypothesis HCLOSE : ev_items_close_spec B ARx SK.
Hypothesis HEND   : ev_items_end_spec B ARx SK.
Hypothesis HEXIT  : ev_exit_spec B ARx SK.


(* project the index bound out of ev_at_step (robust: no shadowed tactic) *)
Lemma step_ile : forall a W regs mem md ly S Hp k o n cap acc i dln,
  ev_at_step B ARx SK a W regs mem md ly S Hp k o n cap acc i dln -> (i <= length (ea_x a))%nat.
Proof. intros * H. unfold ev_at_step in H. cbv zeta in H. decompose [and] H. assumption. Qed.

(* ---- the item loop (pieces 7 + 8 + 9 + 10): from P_STEP to P_EXIT, by induction on the remaining text ---- *)
Lemma ev_items_loop : forall n',
  tex_value_specX B ARx SK n' ->
  forall (fuel : nat) a fxc W regs mem md ly S Hp k o nn cap acc i dln,
  ea_n a = Nat.succ n' ->
  (length (ea_x a) - i <= fuel)%nat ->
  ev_pre (fx:=fx) B ARx a -> ev_fx (fx:=fx) fxc ->
  ev_at_step B ARx SK a W regs mem md ly S Hp k o nn cap acc i dln ->
  SRr segs W (ev_cfg fxc regs EV_STEP mem md) (ev_to_exit (fx:=fx) B ARx SK a).
Proof.
  intros n' HTV. induction fuel as [|fuel IH]; intros a fxc W regs mem md ly S Hp k o nn cap acc i dln En Hfu Hpre Hfxc Hstep.
  - (* fuel = 0: the step itself runs; its only non-exit outcomes have i < i' <= length x, impossible when
       length x - i <= 0, so no loop-back survives *)
    eapply SRr_bind; [exact (HITEM n' HTV a fxc W regs mem md ly S Hp k o nn cap acc i dln En Hpre Hfxc Hstep)|].
    cbv beta. intros Wb cb Hwle Hpost.
    destruct Hpost as [Hex | Hr]; [apply SRr_ret; exact Hex|].
    destruct Hr as (fxb & regsb & memb & mdb & lyb & Sb & Hpb & kb & ib & dlnb & nmb & ub & Hrest). destruct Hrest as (Hfxb & Hltb & Hcase).
    destruct Hcase as [(capb & Hceq & Hstepb) | (Hceq & Hcloseb)]; subst cb.
    { exfalso. apply step_ile in Hstepb. lia. }
    { exact (HCLOSE a fxb Wb regsb memb mdb lyb Sb Hpb kb o ((nmb, ub) :: acc) ib dlnb Hpre Hfxb Hcloseb). }
  - (* fuel = S fuel: one item, then loop-back (IH, strictly fewer remaining bytes), close, or exit *)
    eapply SRr_bind; [exact (HITEM n' HTV a fxc W regs mem md ly S Hp k o nn cap acc i dln En Hpre Hfxc Hstep)|].
    cbv beta. intros Wb cb Hwle Hpost.
    destruct Hpost as [Hex | Hr]; [apply SRr_ret; exact Hex|].
    destruct Hr as (fxb & regsb & memb & mdb & lyb & Sb & Hpb & kb & ib & dlnb & nmb & ub & Hrest). destruct Hrest as (Hfxb & Hltb & Hcase).
    destruct Hcase as [(capb & Hceq & Hstepb) | (Hceq & Hcloseb)]; subst cb.
    { eapply (IH a fxb Wb regsb memb mdb lyb Sb Hpb kb o (Nat.succ nn) capb ((nmb, ub) :: acc) ib dlnb);
        [exact En | | exact Hpre | exact Hfxb | exact Hstepb].
      apply step_ile in Hstepb. lia. }
    { exact (HCLOSE a fxb Wb regsb memb mdb lyb Sb Hpb kb o ((nmb, ub) :: acc) ib dlnb Hpre Hfxb Hcloseb). }
Qed.


(* project the depth bound out of ev_at_step *)
Lemma step_dep_le : forall a W regs mem md ly S Hp k o n cap acc i dln,
  ev_at_step B ARx SK a W regs mem md ly S Hp k o n cap acc i dln -> (ea_dep a <= 31).
Proof. intros * H. unfold ev_at_step in H. cbv zeta in H. decompose [and] H. assumption. Qed.

(* the "from P_STEP, reach the exit" capability at nesting n *)
Definition ev_step_ok (n : nat) : Prop :=
  forall a fxc W regs mem md ly S Hp k o nn cap acc i dln,
  ea_n a = n -> ev_pre (fx:=fx) B ARx a -> ev_fx (fx:=fx) fxc ->
  ev_at_step B ARx SK a W regs mem md ly S Hp k o nn cap acc i dln ->
  SRr segs W (ev_cfg fxc regs EV_STEP mem md) (ev_to_exit (fx:=fx) B ARx SK a).

(* n = 0: ex_value at nesting 0 is at depth 32, where no item loop is entered (ev_at_step needs dep <= 31) *)
Lemma ev_step_ok_0 : ev_step_ok 0.
Proof.
  intros a fxc W regs mem md ly S Hp k o nn cap acc i dln Hn Hpre Hfxc Hstep.
  exfalso. apply step_dep_le in Hstep.
  (* ea_dep a <= 31, but ev_pre gives 0 <= ea_dep a /\ 32 <= ea_dep a + n, n = 0 *)
  unfold ev_pre in Hpre. cbv zeta in Hpre. decompose [and] Hpre.
  rewrite Hn in *. simpl in *. lia.
Qed.

(* n = S n': the item loop, discharging the recursive call from the IH tex_value_specX n' *)
Lemma ev_step_ok_S : forall n', tex_value_specX B ARx SK n' -> ev_step_ok (Nat.succ n').
Proof.
  intros n' HTV a fxc W regs mem md ly S Hp k o nn cap acc i dln Hn Hpre Hfxc Hstep.
  eapply (ev_items_loop n' HTV (length (ea_x a) - i) a fxc W regs mem md ly S Hp k o nn cap acc i dln);
    [exact Hn | apply Nat.le_refl | exact Hpre | exact Hfxc | exact Hstep].
Qed.

(* the exit leg: an ev_to_exit hypothesis Hto at config ce closes the goal via HEXIT *)
Ltac fin_exit a1 Hpre1 Hto :=
  destruct Hto as (fxe & regse & meme & mde & lye & Se & Hpe & ke & re & pe & depe & dle & Hce & Hfxe & Hate);
  subst; exact (HEXIT a1 fxe _ regse meme mde lye Se Hpe ke re pe depe dle Hpre1 Hfxe Hate).

(* the common chain: entry -> ws/dispatch -> {number | items -> loop} -> exit *)
Lemma ex_value_from_stepok : forall n, ev_step_ok n -> tex_value_specX B ARx SK n.
Proof.
  intros n Hstepok.
  unfold tex_value_specX. cbv zeta.
  intros ly S Hp W regs mem md ch q v x0 i0 dep dl scr d x t D Lam peak cnt fail ran most own.
  intros Hfpre Hmn Hfrm Hcount H10 H11 Hcur Hqmod Hchap Hsp1 Hsp2 Hfwin Hsrc Hinblk Hlenb Hi0 Hdep Hdn Hdl
         Hwdest Hinblk2 Hdisj1 Hdisj2 Htree Hledger.
  pose (a := mkEA n regs ly S Hp W mem md ch q v x0 x i0 dep dl scr d t D Lam peak cnt fail ran most own 0).
  (* ev_pre's last conjunct is tex_value_specX's memnorm premise (Hmn, the text's second premise) *)
  assert (Hpre : ev_pre (fx:=fx) B ARx a).
  { unfold ev_pre, a.
    cbn [ea_n ea_regs ea_ly ea_S ea_Hp ea_W ea_mem ea_md ea_ch ea_q ea_v ea_x0 ea_x ea_i0 ea_dep ea_dl
         ea_scr ea_d ea_t ea_D ea_Lam ea_peak ea_cnt ea_fail ea_ran ea_most ea_own ea_len ea_STK]. cbv zeta.
    exact (conj Hfpre (conj Hfrm (conj Hcount (conj H10 (conj H11 (conj Hcur (conj Hqmod (conj Hchap (conj Hsp1 (conj Hsp2 (conj Hfwin (conj Hsrc (conj Hinblk (conj Hlenb (conj Hi0 (conj Hdep (conj Hdn (conj Hdl (conj Hwdest (conj Hinblk2 (conj Hdisj1 (conj Hdisj2 (conj Htree (conj Hledger Hmn)))))))))))))))))))))))). }
  assert (Hfx0 : ev_fx (fx:=fx) fx) by (split; [exact Hfrm | intros r Hr; reflexivity]).
  (* ENTRY *)
  eapply SRr_bind; [exact (HENTRY a Hpre)|].
  cbv beta. intros W1 c1 Hwle1 Hent.
  destruct Hent as (pos & regs1 & mem1 & md1 & ly1 & S1' & Hp1 & k1 & Hc1 & Hws). subst c1.
  pose (a1 := ev_setpos a pos).
  assert (Hpre1 : ev_pre (fx:=fx) B ARx a1) by exact Hpre.
  change (ev_at_ws B ARx SK (ev_setpos a pos)) with (ev_at_ws B ARx SK a1) in Hws.
  (* WS / DISPATCH *)
  eapply SRr_bind; [exact (HDISP a1 fx W1 regs1 mem1 md1 ly1 S1' Hp1 k1 Hpre1 Hfx0 Hws)|].
  cbv beta. intros W2 c2 Hwle2 Hdp.
  destruct Hdp as [Hto | (fx2 & regs2 & mem2 & md2 & ly2 & S2 & Hp2 & k2 & i1 & c & Hfx2 & Hkind & Hcase)].
  { (* end of input / leaf exit *) fin_exit a1 Hpre1 Hto. }
  { destruct Hcase as [(Hc123 & Hc2eq) | (Hn34 & Hn91 & Hn123 & Hn102 & Hn110 & Hn116 & Hc2eq)]; subst c2.
    { (* ITEMS *)
      eapply SRr_bind; [exact (HOPEN a1 fx2 W2 regs2 mem2 md2 ly2 S2 Hp2 k2 i1 c Hpre1 Hfx2 Hkind Hc123)|].
      cbv beta. intros W3 c3 Hwle3 Hop.
      destruct Hop as [Hto | (fx3 & regs3 & mem3 & md3 & ly3 & S3 & Hp3 & k3 & i3 & dln3 & Hfx3 & Hcase3)].
      { fin_exit a1 Hpre1 Hto. }
      { destruct Hcase3 as [(Hc3eq & Hstep3) | (Hc3eq & Hend3)]; subst c3.
        { (* P_STEP: the item loop *)
          eapply SRr_bind;
            [exact (Hstepok a1 fx3 W3 regs3 mem3 md3 ly3 S3 Hp3 k3 _ _ _ _ i3 dln3 eq_refl Hpre1 Hfx3 Hstep3)|].
          cbv beta. intros W4 c4 Hwle4 Hto. fin_exit a1 Hpre1 Hto. }
        { (* P_END: empty container *)
          eapply SRr_bind;
            [exact (HEND a1 fx3 W3 regs3 mem3 md3 ly3 S3 Hp3 k3 _ _ i3 dln3 Hpre1 Hfx3 Hend3)|].
          cbv beta. intros W4 c4 Hwle4 Hto. fin_exit a1 Hpre1 Hto. } } }
    { (* NUMBER *)
      eapply SRr_bind;
        [exact (HNUM a1 fx2 W2 regs2 mem2 md2 ly2 S2 Hp2 k2 i1 c Hpre1 Hfx2 Hkind Hn34 Hn91 Hn123 Hn102 Hn110 Hn116)|].
      cbv beta. intros W3 c3 Hwle3 Hto. fin_exit a1 Hpre1 Hto. } }
Qed.

(* ex_value walks: tex_value_specX at every nesting, the recursion closed by induction on n *)
Theorem ex_value_compose : forall n, tex_value_specX B ARx SK n.
Proof.
  intro n. induction n as [|n' IHn'].
  - apply ex_value_from_stepok. exact ev_step_ok_0.
  - apply ex_value_from_stepok. apply ev_step_ok_S. exact IHn'.
Qed.

End c.
