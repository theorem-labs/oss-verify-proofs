(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3B CxfCarry.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxfCarry2 CxfL1 CxfL2 CxfL5 CxfLeaf CxfNat.
Import ListNotations.
Open Scope Z_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module CXFC2L.
Import CXFC2.
Notation "x && y" := (if x then y else false) (at level 40, left associativity) : bool_scope.
Notation "x || y" := (if x then true else y) (at level 50, left associativity) : bool_scope.
Import AX2.
Import AX2L.
Import AX2B.
Import AX2BL.
Import CXFC.
Import CXFCL.
Definition img_in (g : gval) (K' : kentry) : bool :=
  match K', g with
  | KImg lo' hi', (_, _, _, (glo, ghi)) =>
      if Z.ltb (hi' - lo') (CXLF.p64) then if Z.leb glo lo' then Z.leb (lo' + zlit64 (hi' - lo')) ghi else false else false
  | _, _ => false
  end.
Lemma L_CXFC2L_img_in : @img_in = @CXFC2.img_in.
Proof. unfold img_in. rewrite ?AX2BL.L_AX2BL_gval, ?AX2L.L_AX2L_zlit64, ?CXLF.zshr_eq, ?CXLF.zm64_eq, ?CXLF.zhalf_eq, ?CXLF.zmodp_eq, ?CXLF.zpow2_eq, ?CXNAT.eqbF_eqf, ?CXNAT.lebF_eqf, ?CXNAT.ltbF_eqf, ?CXNAT.compareF_eqf, ?CXNAT.of_succ_natF_eqf, ?CXNAT.nthF_eqf. reflexivity. Qed.

Definition sfF : positive -> bool := fun _ => false.
Lemma L_CXFC2L_sfF : @sfF = @CXFC2.sfF.
Proof. unfold sfF. reflexivity. Qed.

Fixpoint chainKFM2 (bc : bctx) (g : gval) (fl : flF) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (m : memo2) : list kentry :=
  match fl with
  | [] => [K]
  | (sxr, rest) :: fl' =>
      let sx := fst sxr in
      match prune1pcKM bc (sx_sp sx) (fst (snd sxr)) (snd (snd sxr)) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m with
      | (PKeep, m') => chainKFM2 bc g fl' K okb same_of br2 m'
      | (PRepl l, m') =>
          match okb with
          | Some kb =>
              flat_map (fun K' => match kbase K' with
                                  | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 (if subj_tail_eqb K K' then m' else memo0)
                                                else chain_slow bc (map fst rest) [K']
                                  | None => chain_slow bc (map fst rest) [K']
                                  end) l
          | None => flat_map (fun K' => if img_in g K' then chainKFM2 bc g fl' K' None sfF None memo0
                                        else chain_slow bc (map fst rest) [K']) l
          end
      end
  end.
Lemma L_CXFC2L_chainKFM2 : @chainKFM2 = @CXFC2.chainKFM2.
Proof. unfold chainKFM2. rewrite ?L_CXFC2L_img_in, ?L_CXFC2L_sfF, ?CXFCL.L_CXFCL_chainK2M, ?AX2BL.L_AX2BL_chain_slow, ?AX2L.L_AX2L_expr_eqb, ?CXFCL.L_CXFCL_flF, ?AX2BL.L_AX2BL_gval, ?AX2L.L_AX2L_kbase, ?CXFCL.L_CXFCL_memo0, ?CXFCL.L_CXFCL_prune1pcKM, ?CXFCL.L_CXFCL_subj_tail_eqb. reflexivity. Qed.

Fixpoint img_okF (bc : bctx) (g : gval) (fl : flF) : Prop :=
  match fl with
  | [] => True
  | (sxr, rest) :: fl' =>
      (forall K', img_in g K' = true -> chainKF bc (fl_proj fl') K' None sfF None = chain_slow bc (map fst rest) [K'])
      /\ img_okF bc g fl'
  end.
Lemma L_CXFC2L_img_okF : @img_okF = @CXFC2.img_okF.
Proof. unfold img_okF. rewrite ?L_CXFC2L_img_in, ?L_CXFC2L_sfF, ?AX2BL.L_AX2BL_chainKF, ?AX2BL.L_AX2BL_chain_slow, ?CXFCL.L_CXFCL_flF, ?CXFCL.L_CXFCL_fl_proj, ?AX2BL.L_AX2BL_gval. reflexivity. Qed.

Fixpoint chainKFM2B (bc : bctx) (g : gval) (fl : flF) (K : kentry) (okb : option expr) (same_of : positive -> bool)
         (br2 : option (Z * Z)) (m : memo2) : list kentry * blkc :=
  match fl with
  | [] => ([K], mm_blk m)
  | (sxr, rest) :: fl' =>
      let sx := fst sxr in
      match prune1pcKM bc (sx_sp sx) (fst (snd sxr)) (snd (snd sxr)) (sx_a sx) (sx_w sx) (sx_v sx) K (same_of (sx_bid sx)) br2 m with
      | (PKeep, m') => chainKFM2B bc g fl' K okb same_of br2 m'
      | (PRepl l, m') =>
          (match okb with
           | Some kb =>
               flat_map (fun K' => match kbase K' with
                                   | Some kb' => if expr_eqb kb' kb then chainK2M bc rest K' okb same_of br2 (if subj_tail_eqb K K' then m' else memo0)
                                                 else chain_slow bc (map fst rest) [K']
                                   | None => chain_slow bc (map fst rest) [K']
                                   end) l
           | None => flat_map (fun K' => if img_in g K' then chainKFM2 bc g fl' K' None sfF None memo0
                                         else chain_slow bc (map fst rest) [K']) l
           end, mm_blk m')
      end
  end.
Lemma L_CXFC2L_chainKFM2B : @chainKFM2B = @CXFC2.chainKFM2B.
Proof. unfold chainKFM2B. rewrite ?L_CXFC2L_img_in, ?L_CXFC2L_sfF, ?L_CXFC2L_chainKFM2, ?CXFCL.L_CXFCL_blkc, ?CXFCL.L_CXFCL_chainK2M, ?AX2BL.L_AX2BL_chain_slow, ?AX2L.L_AX2L_expr_eqb, ?CXFCL.L_CXFCL_flF, ?AX2BL.L_AX2BL_gval, ?AX2L.L_AX2L_kbase, ?CXFCL.L_CXFCL_memo0, ?CXFCL.L_CXFCL_prune1pcKM, ?CXFCL.L_CXFCL_subj_tail_eqb. reflexivity. Qed.

Fixpoint entriesGM2 (bc : bctx) (sxs : list stxr) (gl : ptree gflF) (kn : list kentry) (infos : list (option einfo)) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      (match oi with
       | Some ei =>
           let okb := kbase K in
           let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
           let br2 := match okb with Some _ => ei_br ei | None => None end in
           match pt_get gl (ei_gid ei) with
           | Some (g, fl) => if inb g ei then chainKFM2 bc g fl K okb same_of br2 memo0 else chainK2M bc sxs K okb same_of br2 memo0
           | None => chainK2M bc sxs K okb same_of br2 memo0
           end
       | None => if is_pure K then [K] else chainK2M bc sxs K None (fun _ => false) None memo0
       end) ++ entriesGM2 bc sxs gl rest irest
  | _, _ => []
  end.
Lemma L_CXFC2L_entriesGM2 : @entriesGM2 = @CXFC2.entriesGM2.
Proof. unfold entriesGM2. rewrite ?L_CXFC2L_chainKFM2, ?CXFCL.L_CXFCL_chainK2M, ?CXFCL.L_CXFCL_gflF, ?AX2BL.L_AX2BL_inb, ?CXFCL.L_CXFCL_is_pure, ?AX2L.L_AX2L_kbase, ?CXFCL.L_CXFCL_memo0, ?AX2L.L_AX2L_pt_get, ?CXFCL.L_CXFCL_stxr. reflexivity. Qed.

Fixpoint entriesGM2B (bc : bctx) (sxs : list stxr) (gl : ptree gflF) (kn : list kentry) (infos : list (option einfo)) (B : blkc) : list kentry :=
  match kn, infos with
  | K :: rest, oi :: irest =>
      let rb := (match oi with
                 | Some ei =>
                     let okb := kbase K in
                     let same_of := match okb with Some _ => Pos.eqb (ei_bid ei) | None => fun _ => false end in
                     let br2 := match okb with Some _ => ei_br ei | None => None end in
                     match pt_get gl (ei_gid ei) with
                     | Some (g, fl) => if inb g ei then chainKFM2B bc g fl K okb same_of br2 (memo0b B) else chainK2MB bc sxs K okb same_of br2 (memo0b B)
                     | None => chainK2MB bc sxs K okb same_of br2 (memo0b B)
                     end
                 | None => if is_pure K then ([K], B) else chainK2MB bc sxs K None (fun _ => false) None (memo0b B)
                 end) in
      fst rb ++ entriesGM2B bc sxs gl rest irest (snd rb)
  | _, _ => []
  end.
Lemma L_CXFC2L_entriesGM2B : @entriesGM2B = @CXFC2.entriesGM2B.
Proof. unfold entriesGM2B. rewrite ?L_CXFC2L_chainKFM2B, ?CXFCL.L_CXFCL_blkc, ?CXFCL.L_CXFCL_chainK2MB, ?CXFCL.L_CXFCL_gflF, ?AX2BL.L_AX2BL_inb, ?CXFCL.L_CXFCL_is_pure, ?AX2L.L_AX2L_kbase, ?CXFCL.L_CXFCL_memo0b, ?AX2L.L_AX2L_pt_get, ?CXFCL.L_CXFCL_stxr. reflexivity. Qed.

Definition carryGFL2 (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) : list kentry :=
  let '(sxs, t0) := fst (mk_stxsFC bc log lrs nt_empty) in
  let '(r, gs) := scan_entries bc kn t0 gst_empty in
  let '(infos, _) := r in
  stores_partM bc sxs ++ entriesGM2B bc sxs (mk_glV bc (gs_bnds gs) sxs) kn infos [].
Lemma L_CXFC2L_carryGFL2 : @carryGFL2 = @CXFC2.carryGFL2.
Proof. unfold carryGFL2. rewrite ?L_CXFC2L_entriesGM2B, ?AX2BL.L_AX2BL_gst_empty, ?CXFCL.L_CXFCL_mk_glV, ?CXFCL.L_CXFCL_mk_stxsFC, ?AX2BL.L_AX2BL_nt_empty, ?AX2BL.L_AX2BL_scan_entries, ?CXFCL.L_CXFCL_stores_partM. reflexivity. Qed.

Definition carryKFL2 (bc : bctx) (log : list sentry) (lrs : list (list positive)) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log, hints with
  | [], _ => (kn, [], hints)
  | _, [] => (carryGFL2 bc log lrs kn, [], [])
  | _, _ => carryB bc log kn hints
  end.
Lemma L_CXFC2L_carryKFL2 : @carryKFL2 = @CXFC2.carryKFL2.
Proof. unfold carryKFL2. rewrite ?L_CXFC2L_carryGFL2, ?AX2BL.L_AX2BL_carryB. reflexivity. Qed.

End CXFC2L.
