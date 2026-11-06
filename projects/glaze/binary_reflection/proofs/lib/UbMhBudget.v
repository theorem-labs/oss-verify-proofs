(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount.UbMhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Budget.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (st : mst) (L : list (Z * Z)) (Jl : list (Z * Z)).
  Hypothesis HWF : WF st L.
  Hypothesis HJ : junk_in st Jl.
  Hypothesis HJl : Z.of_nat (length Jl) <= 2.
  Hypothesis Hlimbo : Z.of_nat (length (s_limbo st)) <= 8.

  Lemma L_len : Z.of_nat (length L) <= LMAX.
  Proof. destruct HWF as (_ & _ & _ & _ & _ & WL & _). exact (wL_len st L WL). Qed.

  Lemma groups_bound : Z.of_nat (length (s_groups st)) <= 1746 /\ Z.of_nat (length (top_groups st)) <= 194.
  Proof.
    pose proof (count_groups st L Jl HWF HJ) as [A B]. pose proof L_len. unfold LMAX in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma areas_room : s_flist st = [] -> c_avail_cnt (s_ctx st) = 0 -> Z.of_nat (length (s_areas st)) + 1 <= AREAMAX.
  Proof.
    intros Hfl Hav. pose proof (count_areas st L HWF Hfl Hav) as A. pose proof groups_bound as [G _]. unfold AREAMAX. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma regions_room : Z.of_nat (length (s_regions st)) <= 240.
  Proof.
    pose proof (count_regions st L HWF) as R. pose proof groups_bound as [_ T]. unfold AREAMAX in R. lia.
  Qed.

  (* [comment removed for export] *)
  Definition is_grp (r : region) : bool := match rg_kind r with RGroup _ => true | _ => false end.
  Definition is_meta (r : region) : bool := match rg_kind r with RMeta _ => true | _ => false end.
  Definition is_brk (r : region) : bool := match rg_kind r with RBrk => true | _ => false end.
  Definition sumK (f : region -> bool) (rs : list region) : Z := fold_right (fun r acc => (if f r then rg_len r else 0) + acc) 0 rs.

  Lemma RSUM_split : forall rs, RSUM rs = sumK is_grp rs + sumK is_meta rs + sumK is_brk rs.
  Proof.
    induction rs as [|r rs IH]; [reflexivity|]. rewrite RSUM_cons. cbn [sumK fold_right]. fold (sumK is_grp rs) (sumK is_meta rs) (sumK is_brk rs).
    destruct r as [b l [|e|x]]; cbn [is_grp is_meta is_brk rg_kind rg_len]; lia.
  Qed.
  Lemma sumK_grp_eq : forall rs,
    sumK is_grp rs = fold_right (fun r acc => match rg_kind r with RGroup _ => rg_len r + acc | _ => acc end) 0 rs.
  Proof. induction rs as [|r rs IH]; [reflexivity|]. cbn [sumK fold_right]. fold (sumK is_grp rs). rewrite IH. destruct r as [b l [|e|x]]; cbn; lia. Qed.
  Lemma sumK_le : forall f rs bnd, (forall r, In r rs -> f r = true -> 0 <= rg_len r <= bnd) -> 0 <= bnd ->
    sumK f rs <= Z.of_nat (length (List.filter f rs)) * bnd.
  Proof.
    intros f rs bnd Hb Hbnd. induction rs as [|r rs IH]; [cbn; lia|].
    cbn [sumK fold_right List.filter]. fold (sumK f rs).
    assert (IH' : sumK f rs <= Z.of_nat (length (List.filter f rs)) * bnd) by (apply IH; intros; apply Hb; [right|]; assumption).
    destruct (f r) eqn:E.
    - cbn [length]. rewrite Nat2Z.inj_succ. pose proof (Hb r ltac:(left; reflexivity) E). nia.
    - lia.
  Qed.
  Lemma PHI_fold : forall l, fold_right (fun b acc => snd b + MBLK + acc) 0 l = PHI l.
  Proof. induction l as [|b l IH]; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

  Lemma meta_bytes : sumK is_meta (s_regions st) <= (AREAMAX + 1) * 2 ^ 24.
  Proof.
    destruct HWF as (WC & WA & _ & _ & _ & _ & WR & _).
    eapply Z.le_trans.
    - apply (sumK_le is_meta _ (2 ^ 24)); [|lia]. intros r Hr F. destruct r as [b l [|e|x]]; cbn in F; try discriminate F.
      pose proof (wr_meta st WR b l e Hr). pose proof (wr_rng st WR _ Hr). cbn in *. lia.
    - pose proof (wr_meta_cnt st WR) as MC. pose proof (wc_shift st WC) as SH. pose proof (wa_cnt st WA) as AC.
      unfold is_meta. apply Z.mul_le_mono_nonneg_r; [lia|]. eapply Z.le_trans; [exact MC | lia].
  Qed.
  Lemma brk_bytes : sumK is_brk (s_regions st) <= AREAMAX * 8192.
  Proof.
    destruct HWF as (WC & WA & _ & _ & _ & _ & WR & _).
    eapply Z.le_trans.
    - apply (sumK_le is_brk _ 8192); [|lia]. intros r Hr F. destruct r as [b l [|e|x]]; cbn in F; try discriminate F.
      pose proof (wr_brklen st WR b l Hr). pose proof (wr_rng st WR _ Hr). cbn in *. lia.
    - pose proof (wa_cnt st WA) as AC. apply Z.mul_le_mono_nonneg_r; [lia|].
      pose proof (wr_brk st WR) as BR. unfold is_brk. destruct (s_brk st) as [|b0 b|g].
      + assert (E : forall rs, (forall bb ll, ~ In (RG bb ll RBrk) rs) ->
                   List.filter (fun r => match rg_kind r with RBrk => true | _ => false end) rs = []).
        { induction rs as [|r rs IH]; intros NB; [reflexivity|]. cbn.
          destruct r as [rb rl [|e|x]]; cbn; [exfalso; exact (NB rb rl ltac:(left; reflexivity)) | |];
          (apply IH; intros bb ll Hin; apply (NB bb ll); right; exact Hin). }
        rewrite (E _ BR). cbn. unfold AREAMAX. lia.
      + destruct BR as (_ & C & _). eapply Z.le_trans; [exact C | exact AC].
      + destruct BR as [C _]. eapply Z.le_trans; [exact C | exact AC].
  Qed.

  (* [comment removed for export] *)
  Hypothesis H63 : no_junk63 st.
  Theorem rsum_bound : RSUM (s_regions st) <= PHI L + 51 * GRPMAX + (AREAMAX + 1) * 2 ^ 24 + AREAMAX * 8192.
  Proof.
    rewrite RSUM_split. pose proof meta_bytes. pose proof brk_bytes.
    pose proof (count_bytes_no_junk63 st L Jl HWF HJ H63) as G. rewrite <- sumK_grp_eq, PHI_fold in G.
    assert (0 <= GRPMAX) by (unfold GRPMAX; lia). nia.
  Qed.
  Corollary rsum_MBASE : RSUM (s_regions st) + 2 ^ 27 <= PHI L + MBASE.
  Proof. pose proof rsum_bound. unfold GRPMAX, AREAMAX, MBASE in *. cbn in *. lia. Qed.
End Budget.
