(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import PropExec ShapeAlg SpinAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanAcctShapeCfg AsanPlanSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesGen.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS.
Unset Lia Cache.
Open Scope Z_scope.
Section WithFP1. Context {FP : PropExec.FPState}.
Section GNodes.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis NX0_sp : nx0_sp_ok nx0.
  Variable FS0 : Fs.Fs.

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).
  #[local] Notation u := bv_unsigned.

  Lemma u_eaddz_g : forall E a z, 0 <= z -> u (edenot E a) + z < 2 ^ 64 -> u (edenot E (eaddz a z)) = u (edenot E a) + z.
  Proof.
    intros E a z Hz Hnw. unfold eaddz. rewrite mkAlu_denot. rewrite u_add64. cbn [edenot].
    pose proof (u64_range (edenot E a)). rewrite (u64_lit z) by lia. apply Z.mod_small. lia.
  Qed.

  Lemma adenot_estart : forall E a, adenot E a = Z_to_bv 64 (estart E a).
  Proof. intros. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rs_addr_sound : forall E M k0 x y, know_ok SEGS E M k0 -> GN.rs_addr k0 x y = true -> estart E x = estart E y.
  Proof.
    intros E M k0 x y HK H. unfold GN.rs_addr in H. apply orb_prop in H as [H|H].
    - apply saddr_eqb_eq in H. subst. reflexivity.
    - apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply expr_eqb_eq in H2.
      destruct (xhi k0 (a_base y)) as [h|] eqn:Hx; [|discriminate]. apply Z.ltb_lt in H3. unfold two64 in H3.
      pose proof (xhi_sound SEGS E M k0 _ h HK Hx) as Hh.
      unfold estart. rewrite H2. rewrite u_eaddz_g by lia. lia.
  Qed.

  Lemma rs_k_sound : forall E M k0 x y, know_ok SEGS E M k0 -> GN.rs_k k0 x y = true -> kentry_ok SEGS E M y -> kentry_ok SEGS E M x.
  Proof.
    intros E M k0 x y HK H Hy. unfold GN.rs_k in H. apply orb_prop in H as [H|H]; [apply kentry_eqb_eq in H; subst; exact Hy|].
    destruct x, y; try discriminate;
      repeat match type of H with (_ && _)%bool = true => let H' := fresh "Hc" in apply andb_prop in H as [H H'] end;
      repeat match goal with
             | X : GN.rs_addr _ _ _ = true |- _ => apply (rs_addr_sound E M k0 _ _ HK) in X
             | X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X; subst
             | X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X; subst
             | X : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in X; subst
             end;
      cbn [kentry_ok] in *; unfold flat in *; rewrite ?adenot_estart in *;
      repeat match goal with X : estart E _ = estart E _ |- _ => rewrite X in *; clear X end; exact Hy.
  Qed.

  Lemma rs_kn_sound : forall E M k0 xs ys, know_ok SEGS E M k0 -> GN.rs_kn k0 xs ys = true -> know_ok SEGS E M ys -> know_ok SEGS E M xs.
  Proof.
    intros E M k0. induction xs as [|x xs IH]; intros ys HK H Hys; destruct ys as [|y ys]; cbn [GN.rs_kn] in H; try discriminate.
    - constructor.
    - apply andb_prop in H as [H1 H2]. inversion Hys as [|? ? Hy Hys']; subst.
      constructor; [exact (rs_k_sound E M k0 x y HK H1 Hy) | exact (IH ys HK H2 Hys')].
  Qed.

  (* [comment removed for export] *)
  Lemma acs_rs_eqb_eq : forall x y, GN.acs_rs_eqb x y = true ->
    x = set_kn y (kn x) /\ GN.rs_kn (kn y) (kn x) (kn y) = true.
  Proof.
    intros x y H. unfold GN.acs_rs_eqb in H.
    repeat match type of H with (_ && _)%bool = true => let H' := fresh "Hc" in apply andb_prop in H as [H H'] end.
    destruct x as [[xpc xregs xlog xkn xnx xresv] xm xt xy xe xv xg xab xb xf xtid].
    destruct y as [[ypc yregs ylog ykn ynx yresv] ym yt yy ye yv yg yab yb yf ytid].
    unfold pc, nxt, kn in *. cbn [a_ss s_pc s_regs s_log s_know s_next s_resv a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset] in *.
    destruct xlog; [|discriminate]. destruct ylog; [|discriminate]. destruct xresv; [discriminate|]. destruct yresv; [discriminate|].
    repeat match goal with
           | X : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in X; subst
           | X : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in X; subst
           | X : Bool.eqb _ _ = true |- _ => apply Bool.eqb_prop in X; subst
           | X : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in X; subst
           | X : afd_eqb _ _ = true |- _ => apply afd_eqb_eq in X; subst
           | X : list_eqb expr_eqb _ _ = true |- _ => apply (list_eqb_eq expr_eqb expr_eqb_eq) in X; subst
           | X : list_eqb amap_eqb _ _ = true |- _ => apply (list_eqb_eq amap_eqb amap_eqb_eq) in X; subst
           | X : list_eqb pair_eqb _ _ = true |- _ => apply (list_eqb_eq pair_eqb pair_eqb_eq) in X; subst
           end.
    split; [reflexivity | assumption].
  Qed.

  Lemma rebase_log : forall J rs cs, s_log (a_ss (GN.rebase J rs cs)) = [].
  Proof. reflexivity. Qed.
  Lemma rebase_pc : forall J rs cs, pc (GN.rebase J rs cs) = pc cs.
  Proof. reflexivity. Qed.

  Lemma node_rebase_inv : forall cs args cs', GN.node_rebase nx0 cs args = Some cs' ->
    exists q lo hi rs, fresh_ok nx0 cs = true
      /\ GN.acs_rs_eqb (inst (GN.rebase (nxt cs) rs cs) (nxt cs) (ELit q)) (inst cs (nxt cs) (ELit q)) = true
      /\ lo <= q <= hi /\ 0 <= q < 2 ^ 64
      /\ cs' = bump (add_kn (GN.rebase (nxt cs) rs cs) [KRange (EVar (nxt cs)) lo hi]) 1.
  Proof.
    intros cs args cs' H. unfold GN.node_rebase in H.
    destruct args as [|a0 args]; [discriminate|]. destruct a0; try discriminate.
    destruct args as [|a1 args]; [discriminate|]. destruct a1; try discriminate.
    destruct args as [|a2 args]; [discriminate|]. destruct a2; try discriminate.
    destruct (GN.parse_rules args) as [rs|]; [|discriminate].
    cbv zeta in H.
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection H as <-.
    repeat match type of Hc with (_ && _)%bool = true => let H' := fresh "Hd" in apply andb_prop in Hc as [Hc H'] end.
    repeat match goal with
           | X : Z.leb _ _ = true |- _ => apply Z.leb_le in X
           | X : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in X
           end.
    unfold two64 in *.
    eexists _, _, _, rs. split; [eassumption|]. split; [eassumption|]. refine (conj _ (conj _ eq_refl)); lia.
  Qed.

  Theorem node_rebase_sound : forall args,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => GN.node_rebase nx0 cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn.
    destruct (node_rebase_inv cs args cs' Hn) as (q & lo & hi & rs & Hf & Heq & Hq & Hq64 & ->). clear Hn.
    pose proof (fresh_ok_parts nx0 cs Hf) as (_ & _ & _ & _ & _ & _ & Fle).
    set (J := nxt cs) in *. set (e := ELit q) in *. set (cs1 := GN.rebase J rs cs) in *.
    set (E' := upd E J (edenot E e)).
    assert (Hag : env_agree J E E') by apply upd_agree.
    assert (Hlog : s_log (a_ss cs) = []) by exact (co_log _ _ _ _ _ _ _ _ _ _ _ HC).
    assert (HC0 : CSOK E (inst cs J e) R FULL model).
    { apply (proj2 (cs_ok_inst SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0 E J e cs R FULL model Fle Hlog)).
      exact (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0 E E' cs R FULL model Hag Hf HC). }
    destruct (acs_rs_eqb_eq _ _ Heq) as (Hx & Hrs).
    assert (HCx : CSOK E (inst cs1 J e) R FULL model).
    { rewrite Hx. apply cs_ok_set_kn; [exact HC0|].
      pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC0) as HK0.
      exact (rs_kn_sound E _ _ _ _ HK0 Hrs HK0). }
    assert (HC1 : CSOK E' cs1 R FULL model).
    { exact (proj1 (cs_ok_inst SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_sp FS0 E J e cs1 R FULL model Fle (rebase_log J rs cs)) HCx). }
    assert (Hpc : pc cs = pc (bump (add_kn cs1 [KRange (EVar J) lo hi]) 1)) by reflexivity.
    rewrite Hpc.
    apply (Hk E' R FULL model (conj (env_agree_le _ _ E E' Hag Fle) Hag)); [|reflexivity].
    assert (HC2 : CSOK E' (add_kn cs1 [KRange (EVar J) lo hi]) R FULL model).
    { unfold add_kn. apply cs_ok_set_kn; [exact HC1|]. constructor; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC1)].
      cbn [kentry_ok edenot]. unfold E'. rewrite upd_at. unfold e. cbn [edenot]. rewrite u64_lit by lia. lia. }
    destruct HC2; constructor;
      cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset] in *;
      try assumption; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma zs_covers_sound : forall E M b a m K, GN.zs_covers b a m K = true -> 0 < m -> kentry_ok SEGS E M K ->
    kentry_ok SEGS E M (KZero (SA b a) (ELit m)).
  Proof.
    intros E M b a m K H Hm HK. destruct K as [| [b' o] n | | | | | | | | |]; try discriminate. destruct n as [L| | | | | | |]; try discriminate.
    cbn [GN.zs_covers] in H.
    repeat match type of H with (_ && _)%bool = true => let H' := fresh "Hc" in apply andb_prop in H as [H H'] end.
    apply expr_eqb_eq in H. subst b'. apply Z.leb_le in Hc2, Hc1, Hc0. apply Z.ltb_lt in Hc. unfold two64 in Hc.
    cbn [kentry_ok] in *. destruct HK as ((F1 & F2 & F3 & F4) & HZ).
    unfold elenZ in *. cbn [edenot] in *. rewrite (u64_lit L) in * by lia.
    assert (Hm64 : 0 <= m < 2 ^ 64) by lia. rewrite (u64_lit m) by lia.
    unfold estart in *. cbn [a_base a_off] in *.
    split; [unfold flat, estart; cbn [a_base a_off]; lia|].
    intros i Hi. specialize (HZ (i + (a - o)) ltac:(lia)).
    replace (u (edenot E b) + a + i) with (u (edenot E b) + o + (i + (a - o))) by lia. exact HZ.
  Qed.

  Theorem node_zerosub_sound : forall args,
    APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (fun cs => GN.node_zerosub cs args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold GN.node_zerosub in Hn.
    destruct args as [|b [|[a| | | | | | |] [|[m| | | | | | |] [|? ?]]]]; try discriminate.
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection Hn as <-. apply andb_prop in Hc as [Hm Hex]. apply Z.ltb_lt in Hm.
    apply existsb_exists in Hex as (K & Hin & HKc).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK0.
    assert (HKK : kentry_ok SEGS E (Mr A argH E cs model FULL) K) by (unfold know_ok in HK0; rewrite Forall_forall in HK0; exact (HK0 K Hin)).
    specialize (Hk E R FULL model (conj (env_agree_refl nx0 E) (env_agree_refl (nxt cs) E))).
    rewrite pc_set_kn in Hk. apply Hk; [|reflexivity].
    apply cs_ok_set_kn; [exact HC|]. constructor; [exact (zs_covers_sound E _ b a m K HKc Hm HKK) | exact HK0].
  Qed.

  Theorem gn_xn_sound : forall id args, APSC.node1_stmt_fp SEGS A nx0 LIMIT SINV argH FS0 FP always (GN.xn nx0 id args).
  Proof.
    intros id args. unfold GN.xn. destruct (Nat.eqb id GN.GEN_ID); [exact (node_rebase_sound args)|].
    destruct (Nat.eqb id GN.ZSUB_ID); [exact (node_zerosub_sound args)|].
    intros cs cs' E R FULL model T _ _ Hn. discriminate.
  Qed.
End GNodes.
End WithFP1.
