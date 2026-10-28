(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare AgentLib.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore CxPlan CxPlanSound CxPlanSoundSums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxAcctShape CxNodesLibE AsanNodesMmLib.
Import ListNotations.
Import AX2 AX2S APC CAP CXS APSX.
Open Scope Z_scope.

Module BDN.
Section WithSegs.
Variable segs : list Segment.
Variable A : atable.
Variable nx0 : nat.
Definition lits (l : list expr) : list nat := flat_map (fun e => match e with ELit r => [Z.to_nat r] | _ => [] end) l.
Definition node_band_diamond (args : list expr) (cs : acs) : option acs :=
  match args with
  | ELit v :: ELit joinpc :: ELit depth :: ELit itlo :: ELit itn :: rsl =>
      let IT := APC.mk_itab_ranges segs [(itlo, Z.to_nat itn)] in
      let nx := nxt cs in
      match node_band A cs (Z.to_nat v) with
      | Some (csl, csh) =>
          match CAP.diamond_tree segs IT A 0 true 400000 nx0 nx (Z.to_nat depth) joinpc csl,
                CAP.diamond_tree segs IT A 0 true 400000 nx0 nx (Z.to_nat depth) joinpc csh with
          | Some (l0 :: ll), Some lh => diamond_join_all A nx0 nx joinpc (lits rsl) l0 (ll ++ lh)
          | _, _ => None
          end
      | None => None
      end
  | _ => None
  end.
End WithSegs.
End BDN.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Hypothesis SEGS_wx : AsanAcct.wx_segs_nowrap SEGS.
Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : hull_okP A.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable FS0 : Fs.Fs.

Lemma nxt_band : forall cs v csa csb, node_band A cs v = Some (csa, csb) -> nxt csa = nxt cs /\ nxt csb = nxt cs.
Proof.
  intros cs v csa csb H. unfold node_band, node_band_at in H.
  repeat match type of H with
  | match ?x with _ => _ end = _ => destruct x; try discriminate H
  | (if ?c then _ else _) = _ => destruct c; try discriminate H
  end.
  injection H as <- <-. split; repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Theorem node_band_diamond_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (BDN.node_band_diamond SEGS A nx0 args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk.
  unfold BDN.node_band_diamond in Hn.
  destruct args as [|[v| | | | | | |] [|[joinpc| | | | | | |] [|[depth| | | | | | |] [|[itlo| | | | | | |] [|[itn| | | | | | |] rsl]]]]]; try discriminate Hn.
  set (IT := APC.mk_itab_ranges SEGS [(itlo, Z.to_nat itn)]) in *.
  assert (IT_ok : itab_sound SEGS IT) by apply mk_itab_ranges_sound.
  destruct (node_band A cs (Z.to_nat v)) as [[csl csh]|] eqn:HB; [|discriminate Hn].
  destruct (CAP.diamond_tree SEGS IT A 0 true 400000 nx0 (nxt cs) (Z.to_nat depth) joinpc csl) as [[|l0 ll]|] eqn:HTl; try discriminate Hn.
  destruct (CAP.diamond_tree SEGS IT A 0 true 400000 nx0 (nxt cs) (Z.to_nat depth) joinpc csh) as [lh|] eqn:HTh; [|discriminate Hn].
  destruct (nxt_band cs (Z.to_nat v) csl csh HB) as [Nl Nh].
  destruct (diamond_join_all_sound SEGS A nx0 LIMIT SEGS_in_hull HULL_ok NX0_spw SINV argH ISP argH_agree SINV_agree FS0 (nxt cs) joinpc (BDN.lits rsl) (ll ++ lh) l0 cs' Hn) as [Jacc Jls].
  assert (LEAF : forall l E' R' FULL' model', In l ((l0 :: ll) ++ lh) ->
            env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok SEGS A LIMIT SINV argH ISP FS0 E' l R' FULL' model' -> m_fs model' = m_fs model ->
            crz SEGS (cfg_of SEGS R' (pc l) FULL' model') T).
  { intros l E' R' FULL' model' Hin [Ag0 Ag1] HC' Hfs.
    assert (HJ : exists E'', (env_agree nx0 E' E'' /\ env_agree (nxt cs) E' E'') /\ cs_ok SEGS A LIMIT SINV argH ISP FS0 E'' cs' R' FULL' model' /\ pc cs' = pc l).
    { cbn [app] in Hin. destruct Hin as [<-|Hin]; [exact (Jacc E' R' FULL' model' HC') | exact (Jls l Hin E' R' FULL' model' HC')]. }
    destruct HJ as (E'' & [Bg0 Bg1] & HC'' & Hpc). rewrite <- Hpc.
    apply (Hk E'' R' FULL' model'); [split; [exact (env_agree_trans' nx0 E E' E'' Ag0 Bg0) | exact (env_agree_trans' (nxt cs) E E' E'' Ag1 Bg1)] | exact HC'' | exact Hfs]. }
  destruct (band_sound SEGS A LIMIT SINV argH ISP FS0 cs (Z.to_nat v) csl csh E R FULL model HC HB) as [[HCl Hpl]|[HCh Hph]].
  - rewrite <- Hpl.
    apply (diamond_tree_sound SEGS IT IT_ok A nx0 LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) SEGS_wx SEGS_in_hull HULL_ok NX0_spw SINV argH ISP
             argH_high argH_agree SINV_frame SINV_agree FS0 0%nat true 400000%nat (Z.to_nat depth) nx0 (nxt cs) joinpc csl (l0 :: ll) E R FULL model T (le_n _) ltac:(rewrite Nl; apply le_n) HTl HCl).
    intros l E' R' FULL' model' Hin Hag HC' Hfs. apply (LEAF l E' R' FULL' model'); [apply in_or_app; left; exact Hin | exact Hag | exact HC' | exact Hfs].
  - rewrite <- Hph.
    apply (diamond_tree_sound SEGS IT IT_ok A nx0 LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) SEGS_wx SEGS_in_hull HULL_ok NX0_spw SINV argH ISP
             argH_high argH_agree SINV_frame SINV_agree FS0 0%nat true 400000%nat (Z.to_nat depth) nx0 (nxt cs) joinpc csh lh E R FULL model T (le_n _) ltac:(rewrite Nh; apply le_n) HTh HCh).
    intros l E' R' FULL' model' Hin Hag HC' Hfs. apply (LEAF l E' R' FULL' model'); [apply in_or_app; right; exact Hin | exact Hag | exact HC' | exact Hfs].
Qed.
End Sound.
