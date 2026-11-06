(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv.

Module AcLvN.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcFacts AcAst AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALp AcMALlib AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv.     (* [comment removed for export] *)
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition rkz (r : Z) : positive := bv_key (Z_to_bv 5 r).
Definition lc1 : lin := lconst 1.
(* [comment removed for export] *)
Definition LVB_KEY : positive := 40%positive.
(* [comment removed for export] *)
Definition LVF_KEY : positive := 41%positive.
(* [comment removed for export] *)
Definition lv_okb (a : ast) : bool :=
  (Nat.eqb (lv_cnt a) 0 || (Nat.eqb (lv_cnt a) (6 * LV_N) && Nat.leb (6 * LV_N) (List.length (a_live a))))%bool.
Definition lv_free_b (a : ast) (k : nat) : bool := (lv_okb a && Nat.ltb k LV_N && lin_eqb (lv_B a k) lc0)%bool.

(* [comment removed for export] *)
Definition hdr_cont (f n c : lin) : tree bval := put_bytes TEmpty 0 (lv_hdr f n c).
Definition hdr_read (ct : tree bval) : option (lin * lin * lin) :=
  match tget (okey 1) ct, tget (okey 4) ct, tget (okey 8) ct with
  | Some (BV f 0), Some (BV n 0), Some (BV c 0) => if tree_eqb bval_eqb ct (hdr_cont f n c) then Some (f, n, c) else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition sort3 (a b c : nat) : list nat :=
  let lo := Nat.min a (Nat.min b c) in let hi := Nat.max a (Nat.max b c) in let mid := (a + b + c - lo - hi)%nat in [lo; mid; hi].
Definition apost_stash (k i h u z : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let fs := s_facts S in
  obind (nth_error (a_ext a) i) (fun e =>
  obind (nth_error (s_rgs S) h) (fun H =>
  obind (nth_error (s_rgs S) u) (fun U =>
  obind (nth_error (s_rgs S) z) (fun Zr =>
  obind (hdr_read (rg_cont H)) (fun '(F, N, C) =>
  let hb := rg_base H in let XP := laddc hb 16 in let N8 := rg_size Zr in
  let rix := sort3 h u z in
  let nr := irange fs N8 in
  let Bl := rget (s_regs S) LVB_KEY in
  obool (givex_hdr_ok M a &&& incr_b rix &&& lv_free_b a k &&& lin_eqb (rg_size H) (lconst 16) &&& lin_eqb (rg_base U) XP &&&
         lin_eqb (rg_size U) (lscale 8 N8) &&&      (* [comment removed for export] *)
         (match ldiv8 XP with Some x => lin_eqb (rg_base Zr) (laddc x SH_OFF) | None => false end) &&&
         ext_in1 fs H e &&& ext_in1 fs U e &&& ext_in1 fs Zr e &&&
         inside_lin fs hb (laddc (lscale 8 N8) 16) (fst e) (snd e) &&& fact_implied fs (FMod hb 3 0) &&&
         fact_implied fs (FRange (lsub (lscale 8 N8) N) 0 7) &&& Z.leb 1 (fst nr) &&& Z.leb (snd nr) 8192 &&&
         (let br := irange fs Bl in (Z.eqb (fst br) 1 && Z.eqb (snd br) 1)%bool) &&& lwf (s_next S) Bl)
    (Some (with_rgs S (remove_ixs rix (s_rgs S)), M, lv_put (ext_drop a i) k Bl XP F N C N8))))))).

(* [comment removed for export] *)
Fixpoint cell8 (rgs : list region) (a : lin) : option lin :=
  match rgs with
  | [] => None
  | R :: rs =>
      match is_const (lsub a (rg_base R)) with
      | Some o =>
          match tget (okey o) (rg_cont R) with
          | Some (BV l 0) =>
              if (Z.leb 0 o && forallb (fun j => match tget (okey (o + Z.of_nat j)) (rg_cont R) with
                                                 | Some (BV l' j') => (lin_eqb l l' && Z.eqb j' (Z.of_nat j))%bool | _ => false end) (seq 1 7))%bool
              then Some l else cell8 rs a
          | _ => cell8 rs a
          end
      | None => cell8 rs a
      end
  end.
Definition apost_stashnil (k : nat) (r : Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let XP := match cell8 (s_rgs S) (laddc (rget (s_regs S) (rkz r)) 16) with Some l => l | None => lc0 end in
  let Bl := rget (s_regs S) LVB_KEY in let Fl := rget (s_regs S) LVF_KEY in
  obool (a_on a &&& lv_free_b a k &&& (let br := irange (s_facts S) Bl in (Z.eqb (fst br) 0 && Z.eqb (snd br) 0)%bool) &&& lwf (s_next S) Bl &&& lwf (s_next S) Fl)
    (Some (S, M, lv_put a k Bl XP Fl lc0 lc0 lc0)).

(* [comment removed for export] *)
Definition apost_lvdrop (k : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (a_on a &&& lv_okb a &&& Nat.ltb k LV_N) (Some (S, M, lv_put a k lc0 lc0 lc0 lc0 lc0 lc0)).
Definition apost_lvclear (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (a_on a) (Some (S, M, lv_clear a)).

(* [comment removed for export] *)
Definition apost_take (k : nat) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let fs := s_facts S in
  let B := lv_B a k in let XP := lv_XP a k in let N := lv_n a k in let F := lv_f a k in let C := lv_c a k in let N8 := lv_n8 a k in
  let VQ := s_next S in let EV := (s_next S + 1)%positive in
  let P8 := lscale 8 (lvar VQ) in let U8 := lscale 8 N8 in
  (* [comment removed for export] *)
  let NS := lsub U8 (lvar EV) in
  let sbr := irange fs (p_sb a) in
  obind (find_grant (sm_maps M) (p_pg a) PG_SIZE) (fun jP =>
  obind (find_grant (sm_maps M) (p_tg a) TG_SIZE) (fun jT =>
  obool (givex_hdr_ok M a &&& lv_okb a &&& Nat.ltb k LV_N &&& Z.eqb (s_pc S) 0xb9d70 &&& lin_eqb (rget (s_regs S) (rkz 10)) XP &&&
         (let br := irange fs B in (Z.eqb (fst br) 1 && Z.eqb (snd br) 1)%bool) &&&
         forallb_l (pri_sep_t fs (sm_maps M) ASEGSR jP jT (sm_sp M) a) (s_rgs S))      (* [comment removed for export] *)
    (let a' := ext_add (lv_put a k lc0 lc0 lc0 lc0 lc0 lc0) (laddc P8 (-16)) (laddc U8 16) in
     let newrgs := [RG (laddc P8 (-16)) (lconst 16) RW (hdr_cont F NS C); RG P8 U8 RW TEmpty; RG (laddc (lvar VQ) SH_OFF) N8 RW TEmpty] in
     let newfacts := [FRange (lsub XP P8) 0 0; FRange (lvar EV) 0 7; FRange (lsub NS N) 0 0; FRange N8 1 8192;
                      FRange (lvar VQ) ((fst sbr + 4294967296) / 8) ((snd sbr + 4294967296 * 30 + 262144) / 8);
                      FRange (lsub P8 (p_sb a)) 4294967296 (4294967296 * 30 + 262144)] in
     let S1 := with_reg S (rkz 10) P8 in
     Some (SST (s_pc S1) (s_regs S1) (newrgs ++ s_rgs S1) (s_facts S1 ++ newfacts) (s_next S + 2) (s_resv S1), M, a')))).
(* [comment removed for export] *)
End AcLvN.

From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPsr.

Module AcQjPos.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcFacts AcAst AcHA AcPri AcPriStep AcMALp AcMALlib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition apost_qjpos (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  if (a_on a &&& Nat.eqb (List.length (a_pri a)) PRI_LEN &&&
      (Z.leb 1 (fst (irange (s_facts S) (p_qn a))) ||| Z.leb 1 (fst (irange (s_facts S) (p_gn a)))))
  then Some (with_facts S (s_facts S ++ [FRange (p_j a 24) 1 32]), M, a) else None.

Section QjPos.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

#[using="Type"] Theorem nqjpos_node : forall S M a S' M' a', apost_qjpos S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_qjpos in H.
  destruct (a_on a) eqn:Hon; [|discriminate]. destruct (Nat.eqb (List.length (a_pri a)) PRI_LEN) eqn:Hlen; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hq; [|discriminate] end. injection H as <- <- <-.
  apply Nat.eqb_eq in Hlen. assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ (HHA Hon) Hne) as HP0. pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  assert (Ej : uE E (p_j a 24) = z_j pz 24) by (symmetry; apply zn_pden).
  assert (Hj1 : 1 <= z_j pz 24 <= 32).
  { destruct (cls_jb pz mem0 HI 24 in_cls_24) as (_ & K1 & _). change (sz_tbl 24) with 8192 in K1. split; [|clear - K1; lia].
    destruct (Z.leb 1 (fst (irange (s_facts S) (p_qn a)))) eqn:Hqn.
    - apply Z.leb_le in Hqn. pose proof (irange_sound E (s_facts S) (p_qn a) HF0) as R. fold (uE E (p_qn a)) in R.
      assert (Eqn : uE E (p_qn a) = z_qn pz) by (symmetry; apply zn_pden). rewrite Eqn in R.
      destruct (iz_q _ _ HI) as [HQ0 HQj]. specialize (HQj ltac:(clear - R Hqn; lia)).
      destruct HQ0 as (_ & _ & [(Q0 & _)|(_ & Q2 & _)]); [clear - Q0 R Hqn; lia | clear - Q2 HQj; lia].
    - apply Z.leb_le in Hq. pose proof (irange_sound E (s_facts S) (p_gn a) HF0) as R. fold (uE E (p_gn a)) in R.
      assert (Egn : uE E (p_gn a) = z_gn pz) by (symmetry; apply zn_pden). rewrite Egn in R.
      destruct (iz_gq _ _ HI) as [HG0 HGl]. specialize (HGl ltac:(clear - R Hq; lia)).
      destruct HG0 as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G2 & _)]); [clear - G0 R Hq; lia | clear - G2 HGl; lia]. }
  apply (Hk E mem0 ms model); [apply agree_refl | intros p Hp w Hw; reflexivity | | exact HHA].
  apply (den_add_facts ASEGS LIMIT model0 mem0 E S M ms model _ Hd). intros E' Ha. constructor; [|constructor].
  cbn [fact_ok]. fold (uE E' (p_j a 24)).
  rewrite (uE_agree (s_next S) E E' (p_j a 24) ltac:(apply lwf_p_nth; exact (awf_pri _ a Haw)) Ha), Ej. exact Hj1.
Qed.
End QjPos.
(* [comment removed for export] *)
End AcQjPos.

From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCache.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam3.AcLvN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPsr OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam3.AcQjPos OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCache.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Inductive anode3 : Type :=
| A2 (nk : anode2)                          (* [comment removed for export] *)
| NStash (k i h u z : nat)                  (* [comment removed for export] *)
| NStashNil (k : nat) (r : Z)               (* [comment removed for export] *)
| NLvDrop (k : nat)                         (* [comment removed for export] *)
| NLvClear                                  (* [comment removed for export] *)
| NPsr (i : nat)                            (* [comment removed for export] *)
| NTake (k : nat)                           (* [comment removed for export] *)
| NQjPos                                    (* [comment removed for export] *)
| NCacheAdd                                 (* [comment removed for export] *)
| NCacheDrop (n : nat)                      (* [comment removed for export] *)
| NCacheKeep (k : nat).                     (* [comment removed for export] *)

Definition apost_alloc3 (LIMIT : Z) (nk : anode3) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  match nk with
  | A2 k => apost_alloc2 LIMIT k S M a
  | NStash k i h u z => apost_stash k i h u z S M a
  | NStashNil k r => apost_stashnil k r S M a
  | NLvDrop k => apost_lvdrop k S M a
  | NLvClear => apost_lvclear S M a
  | NPsr i => apost_psr i S M a
  | NTake k => apost_take k S M a
  | NQjPos => apost_qjpos S M a
  | NCacheAdd => apost_cacheadd S M a
  | NCacheDrop n => apost_cachedrop n S M a
  | NCacheKeep k => apost_cachekeep k S M a
  end.
(* [comment removed for export] *)
