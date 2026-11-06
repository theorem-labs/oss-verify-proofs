(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxStep FxSubst.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode FxRunPost FxSNodes AsanSNodes FxSFam.

Module AsanCpNode.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec SeqExec CatExec CatSim.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require StepTac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require MemSplit RefMemcpyLib ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.SeqExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.CatSim OSSVerify.Proofs.fast_float.from_chars.lib.Common.StepTac.Hoare OSSVerify.Proofs.fast_float.from_chars.lib.Common.MemSplit OSSVerify.Proofs.fast_float.from_chars.lib.Common.RefMemcpyLib OSSVerify.Proofs.fast_float.from_chars.lib.Common.ShapeSet OSSVerify.Proofs.fast_float.from_chars.lib.Common.RealizesCfg OSSVerify.Proofs.fast_float.from_chars.lib.Common.AsanAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.PlacementCount OSSVerify.Proofs.fast_float.from_chars.lib.Common.AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChStart FxChFix FxChWv.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChWv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxMchr FxMNode FxRunPost FxRunPostM FxCarve FxSNodes FxSFam AsanSNodes AsanMBase AsanMcpy.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPostM OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxCarve OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanMBase OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanMcpy OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.FxKeep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition CP_PC : Z := 0xd4500.
Definition CP_HAVS : list reg := List.map xr [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31].

(* [comment removed for export] *)
Fixpoint find_cut (rgs : list region) (dst : lin) (j : nat) : option (nat * Z) :=
  match rgs with
  | [] => None
  | R :: rs => match lin_off dst (rg_base R), is_const (rg_size R) with
               | Some o, Some sz => if (rk_wz (rg_kind R) && Z.ltb 0 o && Z.ltb o sz)%bool then Some (j, o) else find_cut rs dst (Datatypes.S j)
               | _, _ => find_cut rs dst (Datatypes.S j)
               end
  end.
Definition cp_sep (fs : list fact) (d : lin) (n : Z) (r : srec) : bool :=
  (Z.ltb (snd (irange fs (fst (fst r))) + snd (irange fs (snd (fst r)))) two64 &&
   (Z.leb (snd (irange fs (fst (fst r))) + snd (irange fs (snd (fst r)))) (fst (irange fs d)) ||
    Z.leb (snd (irange fs d) + n) (fst (irange fs (fst (fst r))))))%bool.

(* [comment removed for export] *)
Definition lin_same (fs : list fact) (x y : lin) : bool :=
  if lin_eqb x y then true else let '(lo, hi) := irange fs (lsub x y) in (Z.eqb lo 0 && Z.eqb hi 0)%bool.
Lemma lin_same_sound : forall E fs x y, Forall (fact_ok E) fs -> lin_same fs x y = true -> lden E x = lden E y.
Proof.
  intros E fs x y HF H. unfold lin_same in H. destruct (lin_eqb x y) eqn:He; [apply lin_eqb_eq in He; subst; reflexivity|].
  pose proof (irange_sound E fs (lsub x y) HF) as R. destruct (irange fs (lsub x y)) as [lo hi]. cbn [fst snd] in R.
  apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1, H2. subst lo hi.
  assert (Hz : bv_unsigned (lden E (lsub x y)) = 0) by lia. rewrite lden_lsub, bv_sub_unsigned in Hz.
  pose proof (bv_unsigned_in_range _ (lden E x)) as Rx. pose proof (bv_unsigned_in_range _ (lden E y)) as Ry.
  unfold bv_modulus in *. change (2 ^ Z.of_N 64) with two64 in *. unfold bv_wrap, bv_modulus in Hz. change (2 ^ Z.of_N 64) with two64 in Hz.
  apply bv_eq. destruct (Z_le_gt_dec (bv_unsigned (lden E y)) (bv_unsigned (lden E x))) as [X|X].
  - rewrite Z.mod_small in Hz by (unfold two64 in *; lia). lia.
  - replace (bv_unsigned (lden E x) - bv_unsigned (lden E y)) with ((bv_unsigned (lden E x) - bv_unsigned (lden E y) + two64) + (-1) * two64) in Hz by ring.
    rewrite Z_mod_plus_full, Z.mod_small in Hz by (unfold two64 in *; lia). unfold two64 in *. lia.
Qed.

Definition cp_post (j : nat) (o2d : Z) (S : sst) (M : smodel) (a : sfam) : option (sst * smodel * sfam) :=
  let fs := s_facts S in let rgs := s_rgs S in
  match nth_error (sf_strs a) j, rg_is S 1, find_cut rgs (rget (s_regs S) (rkey (xr 10))) O with
  | Some (b, l, jj), Some r, Some (j0, o1) =>
      match nth_error rgs j0 with
      | Some R =>
          match is_const (rg_size R) with
          | Some sz =>
              let o2 := o1 + o2d in
              let S1 := run_post_fw2 S r [] CP_HAVS j0 o1 o2 in
              let S2 := with_rgs S1 (carve_rgs (s_rgs S1) j0 o1 o2 l) in
              let d := laddc (rg_base R) o1 in
              if (Z.eqb (s_pc S) CP_PC && Z.eqb (r mod 2) 0 && rsv_none S &&
                  lin_same fs (rget (s_regs S) (rkey (xr 11))) b && lin_same fs (rget (s_regs S) (rkey (xr 12))) l &&
                  Z.ltb 0 o2d && Z.ltb o2 sz && Z.leb (snd (irange fs l)) (o2d - 1) && lwf (s_next S) l &&
                  let Rh := RG (rg_base R) (rg_size R) RW (havoc_range (rg_cont R) o1 o2) in
                  rg_sub_ok Rh (R1c Rh o1) 0 && rg_sub_ok Rh (R3c Rh o2) o2 &&
                  Z.leb (snd (irange fs (lsub (sm_sp M) d))) stack_max_size &&
                  state_wf S2 && forallb (cp_sep fs d o2d) (sf_copies a))%bool
              then Some (S2, own_add M (d, l), (sf_strs a, (d, l, jj) :: sf_copies a))
              else None
          | None => None
          end
      | None => None
      end
  | _, _, _ => None
  end.

Lemma find_cut_spec : forall rgs dst j j0 o, find_cut rgs dst j = Some (j0, o) ->
  exists R sz, nth_error rgs (j0 - j) = Some R /\ (j <= j0)%nat /\ lin_off dst (rg_base R) = Some o /\
    is_const (rg_size R) = Some sz /\ rk_wz (rg_kind R) = true /\ 0 < o < sz.
Proof.
  induction rgs as [|R rs IH]; intros dst j j0 o H; cbn [find_cut] in H; [discriminate|].
  destruct (lin_off dst (rg_base R)) as [o0|] eqn:Ho; destruct (is_const (rg_size R)) as [sz|] eqn:Hs;
    try (destruct (IH dst (Datatypes.S j) j0 o H) as (R' & sz' & Hn & Hj & X); exists R', sz';
         replace (j0 - j)%nat with (Datatypes.S (j0 - Datatypes.S j)) by lia; split; [exact Hn|]; split; [lia | exact X]).
  destruct (rk_wz (rg_kind R) && Z.ltb 0 o0 && Z.ltb o0 sz)%bool eqn:Hc.
  - injection H as <- <-. apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2]. apply Z.ltb_lt in C2, C3.
    exists R, sz. rewrite Nat.sub_diag. split; [reflexivity|]. split; [lia|]. split; [exact Ho|]. split; [exact Hs|]. split; [exact C1 | lia].
  - destruct (IH dst (Datatypes.S j) j0 o H) as (R' & sz' & Hn & Hj & X). exists R', sz'.
    replace (j0 - j)%nat with (Datatypes.S (j0 - Datatypes.S j)) by lia. split; [exact Hn|]. split; [lia | exact X].
Qed.

Lemma map_nth_seq_self : forall (l : list byte) d, List.map (fun k => nth k l d) (seq 0 (length l)) = l.
Proof.
  induction l as [|x l IH]; intros d; [reflexivity|]. cbn [length seq List.map]. cbn [nth]. f_equal.
  rewrite <- seq_shift, map_map. cbn [nth]. exact (IH d).
Qed.
Lemma wbytes_or' : forall bs m (a w : word), wbytes m a bs w = m w \/ exists bb, wbytes m a bs w = Some bb.
Proof.
  induction bs as [|b rest IH]; intros m a w; cbn [wbytes]; [left; reflexivity|].
  destruct (IH (fun x => if bv_eqb x a then Some b else m x) (a + 1)%bv w) as [H|H]; [|right; exact H].
  rewrite H. destruct (bv_eqb w a); [right; exists b; reflexivity | left; reflexivity].
Qed.

Lemma mm_or_rd1' : forall segs (m m' : word -> option byte) (w : word), (m' w = m w \/ exists bb, m' w = Some bb) ->
  rd1 segs m w <> None -> rd1 segs m' w <> None.
Proof. intros segs m m' w [X|(bb & X)] H; unfold rd1 in *; rewrite X; [exact H | discriminate]. Qed.
Lemma mm_or_wview' : forall segs (m m' : word -> option byte) (w : word), (m' w = m w \/ exists bb, m' w = Some bb) ->
  wview segs m w <> None -> wview segs m' w <> None.
Proof. intros segs m m' w [X|(bb & X)] H; unfold wview in *; rewrite X; [exact H | discriminate]. Qed.

Section Node.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable sarg : nat -> list byte.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.

#[using="Hwx"] Theorem den_cp : forall j o2d S M a S' M' a', cp_post j o2d S M a = Some (S', M', a') ->
  forall model0 mem0 E ms model T, DEN ASEGSN LIMIT model0 mem0 E S M ms model -> awf3 (s_next S) a = true -> HA3 sarg E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' ->
     (forall p, In p (sm_frz M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     DEN ASEGSN LIMIT model0 mem0' E' S' M' ms' model' -> HA3 sarg E' M' a' mem0' -> keep_ok model' M M' mem0 mem0' ->
     realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros j o2d S M a S' M' a' Hp model0 mem0 E ms model T Hd Haw Hha Hk.
  unfold cp_post in Hp.
  destruct (nth_error (sf_strs a) j) as [[[b l] jj]|] eqn:Hrj; [|discriminate].
  destruct (rg_is S 1) as [r|] eqn:R1; [|discriminate].
  destruct (find_cut (s_rgs S) (rget (s_regs S) (rkey (xr 10))) O) as [[j0 o1]|] eqn:Hfc; [|discriminate].
  destruct (nth_error (s_rgs S) j0) as [R|] eqn:Hj0; [|discriminate].
  destruct (is_const (rg_size R)) as [sz|] eqn:Hsz; [|discriminate].
  set (o2 := o1 + o2d) in *.
  set (S1 := run_post_fw2 S r [] CP_HAVS j0 o1 o2) in *.
  cbv zeta in Hp. fold o2 S1 in Hp.
  match type of Hp with ((if ?c then _ else _) = Some _) => destruct c eqn:Hck; [|discriminate Hp] end.
  injection Hp as <- <- <-.
  repeat match type of Hck with ((_ && _)%bool = true) => apply andb_prop in Hck as [Hck ?Hc] end.
  repeat match goal with Hx : ((_ && _)%bool = true) |- _ => apply andb_prop in Hx as [Hx ?Hc] end.
  rename Hck into Hpc0.
  match goal with Hx : forallb (cp_sep _ _ _) _ = true |- _ => rename Hx into Hsep end.
  match goal with Hx : state_wf _ = true |- _ => rename Hx into Hswf end.
  match goal with Hx : rg_sub_ok _ (R1c _ o1) 0 = true |- _ => rename Hx into Hwk1 end.
  match goal with Hx : rg_sub_ok _ (R3c _ o2) o2 = true |- _ => rename Hx into Hwk3 end.
  match goal with Hx : lwf (s_next S) l = true |- _ => rename Hx into Hwl end.
  match goal with Hx : rsv_none S = true |- _ => rename Hx into Hrvn end.
  repeat match goal with
         | Hx : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in Hx
         | Hx : Z.leb _ _ = true |- _ => apply Z.leb_le in Hx
         | Hx : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in Hx
         | Hx : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in Hx
         end.
  match goal with Hx : lin_same (s_facts S) (rget (s_regs S) (rkey (xr 11))) b = true |- _ => rename Hx into Hb11 end.
  match goal with Hx : lin_same (s_facts S) (rget (s_regs S) (rkey (xr 12))) l = true |- _ => rename Hx into Hl12 end.
  match goal with Hx : snd (irange (s_facts S) l) <= o2d - 1 |- _ => rename Hx into Hlhi end.
  match goal with Hx : snd (irange (s_facts S) (lsub (sm_sp M) _)) <= stack_max_size |- _ => rename Hx into Hstk end.
  assert (Hrv : s_resv S = RNone) by (unfold rsv_none in Hrvn; destruct (s_resv S); [reflexivity|discriminate|discriminate]).
  destruct (find_cut_spec _ _ _ _ _ Hfc) as (R' & sz' & HR' & _ & Hoff & Hsz' & Hkd & Ho1). rewrite Nat.sub_0_r in HR'.
  rewrite Hj0 in HR'. injection HR' as <-. rewrite Hsz in Hsz'. injection Hsz' as <-.
  (* [comment removed for export] *)
  destruct Hha as [Hstrs Hcps]. pose proof Hstrs as Hstrs0. rewrite Forall_forall in Hstrs0.
  destruct (Hstrs0 (b, l, jj) (nth_error_In _ _ Hrj)) as [Hcs Hsb]. cbn [fst snd] in Hcs.
  destruct Hcs as (C1 & C2 & C3 & C4). unfold sbytes_ok in Hsb. destruct Hsb as [Hlen Hby].
  (* [comment removed for export] *)
  pose proof Hd as Hd0.
  destruct Hd0 as [Hsd Hwf Hbw Hh Hawf Hanz Hminv Hhoff Hres Hlim Hsp Hspok Hbrk Hsbrk Htid Hmaps Hgsh Hgtop Hivwf Hpd Hmres Hkind Hlzm Hzrsh Hzrm Hzr Hrl Hvmo Hproc Hfrz Hrom Hown Hblob].
  set (H := Hof E M model) in *.
  destruct (sden_0 _ _ _ _ Hsd) as (Hpc & Hsvc & Hrsv & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hrsv. cbn [rsv_ok] in Hrsv.
  cbn [restrict ms_pc_val ms_svc_pending ms_resv ms_regs] in Hpc, Hsvc, Hrsv, HR.
  pose proof (proj1 (Forall_nth' _ _) HG j0 R Hj0) as HRok. pose proof (rsz_R E R sz Hsz) as HrR.
  pose proof HRok as HRok0. destruct HRok0 as (Hrs & Hrw & Hpts & Hcont). rewrite HrR in Hrs, Hrw, Hpts.
  set (A := uE E (rg_base R)) in *. set (L := uE E l) in *. set (B := uE E b) in *.
  pose proof (uE_range E (rg_base R)) as RA. pose proof (uE_range E l) as RL. pose proof (uE_range E b) as RB. fold A L B in RA, RL, RB.
  pose proof (irange_sound E (s_facts S) l HF) as Rl. fold (uE E l) L in Rl.
  set (D := A + o1).
  assert (HD10 : uE E (rget (s_regs S) (rkey (xr 10))) = D).
  { unfold D, A, uE. apply (lin_off_u E _ _ o1 Hoff). unfold uE in *. lia. }
  assert (Hwend : wend B L <= 0x800000000000) by exact C1.
  assert (HBL : B + L < wend B L) by (unfold wend; pose proof (Z.div_mod (B + L) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (B + L) 8 ltac:(lia)); lia).
  (* [comment removed for export] *)
  destruct (is_const_sound E _ r R1) as [Hr1 Hr64].
  assert (Hra : getr (ms_regs ms) 1%bv = Z_to_bv 64 r) by (replace (1%bv : reg) with (xr 1) by (apply bv_eq; reflexivity); rewrite (HR (xr 1)); exact Hr1).
  assert (H10 : getr (ms_regs ms) 10%bv = Z_to_bv 64 D).
  { replace (10%bv : reg) with (xr 10) by (apply bv_eq; reflexivity). rewrite (HR (xr 10)). rewrite <- HD10. unfold uE. symmetry. apply u64_of. }
  assert (H11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 B).
  { replace (11%bv : reg) with (xr 11) by (apply bv_eq; reflexivity). rewrite (HR (xr 11)), (lin_same_sound E _ _ _ HF Hb11). unfold B, uE. symmetry. apply u64_of. }
  assert (H12 : getr (ms_regs ms) 12%bv = Z_to_bv 64 L).
  { replace (12%bv : reg) with (xr 12) by (apply bv_eq; reflexivity). rewrite (HR (xr 12)), (lin_same_sound E _ _ _ HF Hl12). unfold L, uE. symmetry. apply u64_of. }
  assert (Hret : ret_ok (Z_to_bv 64 r)) by (apply ret_ok_even; rewrite u_small64 by exact Hr64; assumption).
  (* [comment removed for export] *)
  set (bs := sarg jj) in *.
  assert (Hlbs : length bs = Z.to_nat L) by (rewrite <- (Nat2Z.id (length bs)), <- Hlen; reflexivity).
  set (mm := mrestrict H (ms_mem ms)).
  assert (Hfrzpt : forall w, B <= w < wend B L -> frz_pt E M w) by (intros w Hw; exact (proj1 (C2 w Hw))).
  assert (Hsrc : rdn ASEGSN mm (Z_to_bv 64 B) (length bs) = Some bs).
  { rewrite <- (map_nth_seq_self bs (Z_to_bv 8 0)) at 2.
    apply rdn_of_pts; [lia | rewrite Hlbs, Z2Nat.id by lia; unfold two64; lia|]. intros k Hkk.
    pose proof (frz_restrict ASEGSN LIMIT model0 mem0 E S M ms model _ Hd (Hfrzpt (B + Z.of_nat k) ltac:(rewrite Hlbs in Hkk; lia))) as X.
    fold H in X. change mm with (ms_mem (restrict H ms)). rewrite X.
    rewrite (Hby (Z.of_nat k) ltac:(rewrite Hlbs in Hkk; lia)). rewrite Nat2Z.id. reflexivity. }
  assert (Hpt : forall i, 0 <= i < sz -> rd1 ASEGSN mm (Z_to_bv 64 (A + i)) <> None /\ wview ASEGSN mm (Z_to_bv 64 (A + i)) <> None).
  { intros i Hi. specialize (Hpts i Hi). unfold rk_wz in Hkd. destruct (rg_kind R); try discriminate; [exact Hpts | exact (proj1 Hpts)]. }
  assert (Hdst : store_ok ASEGSN mm (Z_to_bv 64 D) (length bs) = true).
  { apply store_ok_from; [unfold D; lia | rewrite Hlbs, Z2Nat.id by lia; unfold D, o2, A, uE, two64 in *; lia|].
    intros i Hi. rewrite Hlbs, Z2Nat.id in Hi by lia. unfold D. replace (A + o1 + i) with (A + (o1 + i)) by lia. apply Hpt. lia. }
  (* [comment removed for export] *)
  assert (Hfout : forall w, B <= w < B + L -> ~ (A <= w < A + sz)).
  { intros w Hw Hin. destruct (Hfrzpt w ltac:(lia)) as (p & Hp & Hpw).
    destruct (Hfrz p Hp w Hpw) as (_ & Hout & _). unfold outside in Hout. rewrite Forall_forall in Hout.
    specialize (Hout R (nth_error_In _ _ Hj0)). rewrite u_small64 in Hout by (unfold two64; lia). unfold uE in *. rewrite HrR in Hout. fold A in Hout. lia. }
  assert (Hdisj : D + L <= B \/ B + L <= D).
  { destruct (Z.eq_dec L 0) as [HL0|HL0]; [unfold D; lia|].
    destruct (Z_lt_le_dec B A) as [HBA|HBA].
    - right. destruct (Z_le_gt_dec (B + L) A) as [X|X]; [unfold D; lia|]. exfalso. apply (Hfout A); lia.
    - left. destruct (Z_lt_le_dec B (A + sz)) as [X|X]; [exfalso; apply (Hfout B); lia | unfold D; lia]. }
  assert (HuB : bv_unsigned (Z_to_bv 64 B) = B) by (apply u_small64; unfold two64 in *; lia).
  assert (HuD0 : bv_unsigned (Z_to_bv 64 D) = D) by (apply u_small64; unfold D, o2, A, L, uE, two64 in *; lia).
  assert (HOK : mcH mm (Z_to_bv 64 D) (Z_to_bv 64 B) L bs).
  { constructor.
    - unfold two64 in *. lia.
    - exact Hlbs.
    - exact Hsrc.
    - exact Hdst.
    - rewrite HuB, HuD0. exact Hdisj.
    - rewrite HuB. unfold two64 in *. lia.
    - rewrite HuD0. unfold D, o2, A, L, uE, two64 in *. lia. }
  destruct (@ref_memcpy (mkFP (ms_fregs ms) (ms_fcsr ms)) mm (Z_to_bv 64 D) (Z_to_bv 64 B) L bs (ms_rom ms) HOK (ms_regs ms) (Z_to_bv 64 r)
              Hret Hra H10 H11 H12) as (regs' & Hms & Hkeep).
  assert (Hmsr : restrict H ms = @mkst (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_regs ms) (0xd4500 : word) mm (ms_rom ms)).
  { destruct ms as [rg fr pcv sv rv fc mem rom]. cbn [ms_pc_val ms_svc_pending ms_resv] in Hsvc, Hrsv, Hpc. subst sv rv.
    cbn [ms_pc_val] in Hpc. rewrite Hpc0 in Hpc. unfold CP_PC in Hpc. subst pcv.
    unfold restrict, mkst, mm. cbn. f_equal. apply bv_eq. reflexivity. }
  set (mem' := wbytes mm (Z_to_bv 64 D) bs).
  assert (HuD : bv_unsigned (Z_to_bv 64 D) = D) by exact HuD0.
  apply (den_run_post_fw2_m ASEGSN cfg LIMIT model0 mem0 Hwx E S M ms model T regs' r [] CP_HAVS j0 R o1 o2 mem' Hd Hrv Hj0 Hkd).
  - lia.
  - unfold o2. lia.
  - rewrite HrR. unfold o2. lia.
  - fold H. rewrite Hmsr. apply fx_isteps_of_msteps. exact Hms.
  - intros w Hw. unfold mem'. apply wbytes_outside; rewrite HuD, Hlbs, Z2Nat.id by lia; [unfold D, o2, A, L, uE, two64 in *; lia|].
    fold A in Hw. unfold D, o2 in *. lia.
  - intros i Hi. specialize (Hpt i ltac:(unfold o2 in *; lia)). fold A. destruct Hpt as [P1 P2].
    assert (Hor : forall w, mem' w = mm w \/ exists bb, mem' w = Some bb) by (intros w; apply wbytes_or').
    split; [exact (mm_or_rd1' _ _ _ _ (Hor _) P1) | exact (mm_or_wview' _ _ _ _ (Hor _) P2)].
  - apply Forall_nil.
  - unfold CP_HAVS. repeat constructor; intros Hc; apply (f_equal bv_unsigned) in Hc; vm_compute in Hc; discriminate.
  - intros rr Es Eh.
    assert (Hex : exists k, 0 <= k < 32 /\ rr = Z_to_bv 5 k).
    { exists (bv_unsigned rr). split; [pose proof (bv_unsigned_in_range _ rr) as X; change (bv_modulus 5) with 32 in X; lia|].
      symmetry; apply Z_to_bv_bv_unsigned. }
    destruct Hex as (k & Hk32 & ->).
    assert (Hc : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
    destruct Hc as [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | [ -> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].
    all: first
      [ (vm_compute in Eh; discriminate Eh)
      | (replace (Z_to_bv 5 0) with (0%bv : reg) by (apply bv_eq; reflexivity); rewrite !getr_zero; reflexivity)
      | (apply Hkeep; cbn [callee_kept]; repeat (first [left; apply bv_eq; reflexivity | right])) ].
  - intros E' ms' model' Ha' Hd' Hm'.
    assert (HbR : lwf (s_next S) (rg_base R) = true).
    { unfold bases_wf in Hbw. rewrite forallb_forall in Hbw. exact (proj1 (andb_prop _ _ (Hbw R (nth_error_In _ _ Hj0)))). }
    set (R1' := RG (rg_base R) (rg_size R) RW (havoc_range (rg_cont R) o1 o2)).
    assert (HS1j0 : nth_error (s_rgs S1) j0 = Some R1').
    { unfold S1, run_post_fw2. rewrite Hj0. cbn [s_rgs]. exact (nth_upd_same (s_rgs S) j0 R1' R Hj0). }
    assert (HbE' : uE E' (rg_base R) = A) by (unfold A; exact (uE_agree _ E E' _ HbR Ha')).
    assert (HlE' : uE E' l = L) by (unfold L; exact (uE_agree _ E E' l Hwl Ha')).
    assert (Hn1 : (s_next S <= s_next S1)%positive) by (unfold S1, run_post_fw2; rewrite Hj0; cbn [s_next]; apply pos_add_le).
    assert (Hwl1 : lwf (s_next S1) l = true) by exact (lwf_mono _ _ _ Hn1 Hwl).
    assert (Ho12 : 0 < o1 < o2 /\ o2 < sz) by (unfold o2; lia).
    pose proof (den_carve ASEGSN LIMIT model0 mem0 E' S1 M ms' model' j0 R1' o1 o2 sz l Hd' HS1j0 eq_refl Hsz Ho12 Hwk1 Hwk3 Hswf Hwl1
                  ltac:(rewrite HlE'; lia)) as Hd2.
    change (rg_base R1') with (rg_base R) in Hd2. rewrite HbE', HlE' in Hd2.
    set (mem0' := carve_mem0 mem0 (ms_mem ms') (A + o1) L) in Hd2.
    (* [comment removed for export] *)
    assert (Hnotcp : forall w : Z, outside E (s_rgs S) (Z_to_bv 64 w) -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hout. unfold mem0', carve_mem0.
      destruct (Z.leb (A + o1) (bv_unsigned (Z_to_bv 64 w)) && Z.ltb (bv_unsigned (Z_to_bv 64 w)) (A + o1 + L))%bool eqn:X; [|reflexivity].
      exfalso. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
      unfold outside in Hout. rewrite Forall_forall in Hout. specialize (Hout R (nth_error_In _ _ Hj0)).
      rewrite HrR in Hout. unfold A, uE in *. unfold o2 in *. lia. }
    assert (Hfsame : forall w, frz_pt E M w -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w (p & Hp & Hpw). destruct (Hfrz p Hp w Hpw) as (_ & Hout & _). exact (Hnotcp w Hout). }
    assert (Hfpt' : forall w, frz_pt E' M w -> frz_pt E M w).
    { intros w (p & Hp & Hpw). exists p. split; [exact Hp|]. pose proof (sm_wf_frz _ M Hwf) as Hfw. rewrite Forall_forall in Hfw.
      destruct (Hfw p Hp) as [W1 W2]. rewrite <- (uE_agree _ E E' _ W1 Ha'), <- (uE_agree _ E E' _ W2 Ha'). exact Hpw. }
    destruct (HA3_agree sarg (s_next S) E E' M a mem0 Hwf Haw Ha' (conj Hstrs Hcps)) as [Hs' Hc'].
    apply (Hk E' mem0' ms' model' Ha').
    + intros p Hp w Hw. apply Hfsame. exists p. split; [exact Hp | exact Hw].
    + exact Hd2.
    + split.
      * rewrite Forall_forall in Hs' |- *. intros rr Hrr. destruct (Hs' rr Hrr) as [(D1 & D2 & D3 & D4) D5].
        assert (Hfz : forall w, uE E' (fst (fst rr)) <= w < wend (uE E' (fst (fst rr))) (uE E' (snd (fst rr))) -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w))
          by (intros w Hw; apply Hfsame, Hfpt'; exact (proj1 (D2 w Hw))).
        assert (HBw : uE E' (fst (fst rr)) + uE E' (snd (fst rr)) < wend (uE E' (fst (fst rr))) (uE E' (snd (fst rr)))).
        { unfold wend. pose proof (Z.div_mod (uE E' (fst (fst rr)) + uE E' (snd (fst rr))) 8 ltac:(lia)).
          pose proof (Z.mod_pos_bound (uE E' (fst (fst rr)) + uE E' (snd (fst rr))) 8 ltac:(lia)). lia. }
        pose proof (uE_range E' (snd (fst rr))) as RLr.
        split; [split; [exact D1|split; [|split]]|].
        -- intros w Hw. destruct (D2 w Hw) as [X1 X2]. split; [exact X1|]. rewrite (Hfz w Hw). exact X2.
        -- intros k Hk'. pose proof (uE_range E' (fst (fst rr))). rewrite (Hfz (uE E' (fst (fst rr)) + k) ltac:(lia)). exact (D3 k Hk').
        -- pose proof (uE_range E' (fst (fst rr))). rewrite (Hfz (uE E' (fst (fst rr)) + uE E' (snd (fst rr))) ltac:(lia)). exact D4.
        -- pose proof (uE_range E' (fst (fst rr))) as RBr.
           destruct rr as [[rb rl] rj]. unfold sbytes_ok in D5 |- *. cbn [fst snd] in *. destruct D5 as [E1 E2]. split; [exact E1|].
           intros i Hi. rewrite (Hfz (uE E' rb + i) ltac:(lia)). exact (E2 i Hi).
      * constructor.
        -- cbn [sbytes_ok]. split; [rewrite HlE'; exact Hlen|]. intros i Hi. rewrite HlE' in Hi.
           assert (HdE : uE E' (laddc (rg_base R) o1) = D) by (rewrite uE_laddc; [rewrite HbE'; reflexivity | lia | rewrite HbE'; unfold D, o2, A, uE, two64 in *; lia]).
           rewrite HdE. unfold mem0', carve_mem0. rewrite u_small64 by (unfold D, o2, A, L, uE, two64 in *; lia).
           replace (Z.leb (A + o1) (D + i) && Z.ltb (D + i) (A + o1 + L))%bool with true
             by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; unfold D; lia).
           (* [comment removed for export] *)
           assert (Hvis : Hof E' M model' (Z_to_bv 64 (D + i)) = false).
           { pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd') as Hho'.
             destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd')) as (_ & _ & _ & _ & HG' & _ & _ & _).
             pose proof (proj1 (Forall_nth' _ _) HG' j0 R1' HS1j0) as HR1'.
             pose proof (rg_ok_visible ASEGSN _ (ms_mem ms') E' R1' Hho' HR1' (o1 + i)) as X.
             change (rg_base R1') with (rg_base R) in X. rewrite HbE' in X.
             assert (Hrs1 : rsz E' R1' = sz) by (unfold rsz, R1'; cbn [rg_size]; rewrite <- (rsz_R E' R sz Hsz); reflexivity).
             rewrite Hrs1 in X. unfold D. replace (A + o1 + i) with (A + (o1 + i)) by lia. apply X. unfold o2 in *. lia. }
           rewrite (Hm' _ Hvis). unfold mem'. rewrite wbytes_inside; [|rewrite HuD, Hlbs, Z2Nat.id by lia; unfold D, o2, A, L, uE, two64 in *; lia
                                                                   |rewrite HuD, u_small64 by (unfold D, o2, A, L, uE, two64 in *; lia); rewrite Hlbs, Z2Nat.id by lia; lia].
           rewrite HuD, u_small64 by (unfold D, o2, A, L, uE, two64 in *; lia). replace (D + i - D) with i by lia. reflexivity.
        -- rewrite Forall_forall in Hc' |- *. intros rr Hrr. pose proof (Hc' rr Hrr) as Hsb'.
           rewrite forallb_forall in Hsep. pose proof (Hsep rr Hrr) as Hspr. unfold cp_sep in Hspr.
           pose proof (irange_sound E (s_facts S) (fst (fst rr)) HF) as Rb'. pose proof (irange_sound E (s_facts S) (snd (fst rr)) HF) as Rl'.
           pose proof (irange_sound E (s_facts S) (laddc (rg_base R) o1) HF) as Rd'.
           assert (HdE : uE E (laddc (rg_base R) o1) = D) by (rewrite uE_laddc; [reflexivity | lia | unfold D, o2, A, uE, two64 in *; lia]).
           fold (uE E (fst (fst rr))) (uE E (snd (fst rr))) (uE E (laddc (rg_base R) o1)) in Rb', Rl', Rd'. rewrite HdE in Rd'.
           unfold awf3 in Haw. apply andb_prop in Haw as [_ Haw2]. rewrite forallb_forall in Haw2. pose proof (Haw2 rr Hrr) as Hw2.
           unfold rwf3 in Hw2. apply andb_prop in Hw2 as [Wb Wl].
           destruct rr as [[rb rl] rj]. unfold sbytes_ok in Hsb' |- *. cbn [fst snd] in *. destruct Hsb' as [E1 E2]. split; [exact E1|].
           intros i Hi. rewrite <- E2 by exact Hi. unfold mem0', carve_mem0.
           rewrite (uE_agree _ E E' rb Wb Ha') in *. rewrite (uE_agree _ E E' rl Wl Ha') in *.
           destruct (Z.leb (A + o1) (bv_unsigned (Z_to_bv 64 (uE E rb + i))) && Z.ltb (bv_unsigned (Z_to_bv 64 (uE E rb + i))) (A + o1 + L))%bool eqn:X; [|reflexivity].
           exfalso. apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
           pose proof (uE_range E rb). pose proof (uE_range E rl).
           rewrite Z_to_bv_unsigned in X1, X2. unfold bv_wrap, bv_modulus in X1, X2. change (2 ^ Z.of_N 64) with two64 in X1, X2.
           apply andb_prop in Hspr as [Hnw Hspr]. apply Z.ltb_lt in Hnw.
           rewrite Z.mod_small in X1, X2 by lia.
           apply orb_prop in Hspr as [Hspr|Hspr]; apply Z.leb_le in Hspr; unfold D in *; lia.
    + (* [comment removed for export] *)
      split; [apply incl_refl|]. split; [intros q Hq; right; exact Hq|]. split; [|intros x Hx; exact Hx].
      intros x Hx.
      assert (Htop : alloc_top (m_vmmaps model') <= D).
      { unfold alloc_top. rewrite (dn_sp _ _ _ _ _ _ _ _ _ Hd2). cbn [own_add sm_sp].
        destruct (sm_wf_parts _ _ Hwf) as (_ & _ & _ & _ & _ & Hwsp).
        fold (uE E' (sm_sp M)). rewrite (uE_agree _ E E' _ Hwsp Ha').
        pose proof (irange_sound E (s_facts S) (lsub (sm_sp M) (laddc (rg_base R) o1)) HF) as Rsp.
        assert (HdE : uE E (laddc (rg_base R) o1) = D) by (rewrite uE_laddc; [reflexivity | lia | unfold D, o2, A, uE, two64 in *; lia]).
        destruct (small_diff E (sm_sp M) (laddc (rg_base R) o1) _ _ Rsp) as [[Y1 Y2]|[Y1 Y2]]; rewrite HdE in Y1, Y2;
          unfold stack_max_size in *; unfold uE in *; lia. }
      unfold mem0', carve_mem0. rewrite u_small64 by (unfold D, o2, A, uE, two64 in *; lia).
      replace (Z.leb (A + o1) x) with false by (symmetry; apply Z.leb_gt; unfold D in Htop; lia). reflexivity.
Qed.
End Node.
(* [comment removed for export] *)
End AsanCpNode.

From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChLib.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSNodes OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxSFam OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanSFam3.AsanCpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib.FxKeep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Inductive snode : Type :=
| HSL3 (j : nat)      (* [comment removed for export] *)
| HMCH3 (j : nat)     (* [comment removed for export] *)
| HNUL3 (k j : nat)   (* [comment removed for export] *)
| HCP3 (j : nat) (o2d : Z).   (* [comment removed for export] *)

Section H.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable sarg : nat -> list byte.
Variable islx : Z.
Variable nsites : list nsite.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Hypothesis His : isl_ok ASEGSN islx.
Hypothesis Hns : Forall (nsite_ok ASEGSN) nsites.

Definition hpost3 (nk : snode) (S : sst) (M : smodel) (a : sfam) : option (sst * smodel * sfam) :=
  match nk with
  | HSL3 j => if isl_chk islx j S (strs_bl a) then Some (isl_post j S (strs_bl a), M, a) else None
  | HMCH3 j => if mch_chk j S (strs_bl a) then Some (mch_post j S (strs_bl a), M, a) else None
  | HNUL3 k j => match nth_error nsites k with
                 | Some q => if nul_chk q j S (strs_bl a) then Some (nul_post q S, M, a) else None
                 | None => None
                 end
  | HCP3 j o2d => cp_post j o2d S M a
  end.

#[using="Hwx His Hns"] Theorem hnode3_ok : forall nk S M a S' M' a', hpost3 nk S M a = Some (S', M', a') ->
  forall model0 mem0 E ms model T, DEN ASEGSN LIMIT model0 mem0 E S M ms model -> awf3 (s_next S) a = true -> HA3 sarg E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' ->
     (forall p, In p (sm_frz M) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> mem0' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
     DEN ASEGSN LIMIT model0 mem0' E' S' M' ms' model' -> HA3 sarg E' M' a' mem0' -> keep_ok model' M M' mem0 mem0' ->
     realizes_cfg ASEGSN cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGSN cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx His Hns : LiaFast.U) => LiaFast.u0).
  intros nk S M a S' M' a' Hp model0 mem0 E ms model T Hd Haw HHA Hk.
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf.
  assert (Kont : forall S2, (S' = S2) -> M' = M -> a' = a ->
            (forall E' ms' model', agree (s_next S) E E' -> DEN ASEGSN LIMIT model0 mem0 E' S2 M ms' model' -> realizes_cfg ASEGSN cfg (mkCfg ms' model') T)).
  { intros S2 HS HM Ha E' ms' model' Ha' Hd'. subst S' M' a'. apply (Hk E' mem0 ms' model' Ha'); [intros p _ w _; reflexivity | exact Hd' | | apply keep_ok_refl].
    exact (HA3_agree sarg (s_next S) E E' M a mem0 Hwf Haw Ha' HHA). }
  pose proof (HA3_HAS sarg E M a mem0 HHA) as HHS.
  destruct nk as [j|j|k j|j o2d]; cbn [hpost3] in Hp.
  - destruct (isl_chk islx j S (strs_bl a)) eqn:Hc; [|discriminate]. injection Hp as <- <- <-.
    apply (den_isl ASEGSN cfg LIMIT model0 mem0 Hwx islx j S M (strs_bl a) E ms model T His Hc Hd HHS).
    exact (Kont _ eq_refl eq_refl eq_refl).
  - destruct (mch_chk j S (strs_bl a)) eqn:Hc; [|discriminate]. injection Hp as <- <- <-.
    apply (den_mch cfg LIMIT model0 mem0 Hwx j S M (strs_bl a) E ms model T Hc Hd HHS).
    exact (Kont _ eq_refl eq_refl eq_refl).
  - destruct (nth_error nsites k) as [q|] eqn:Hq; [|discriminate].
    destruct (nul_chk q j S (strs_bl a)) eqn:Hc; [|discriminate]. injection Hp as <- <- <-.
    rewrite Forall_forall in Hns.
    apply (den_nul ASEGSN cfg LIMIT model0 mem0 Hwx q j S M (strs_bl a) E ms model T (Hns q (nth_error_In _ _ Hq)) Hc Hd HHS).
    exact (Kont _ eq_refl eq_refl eq_refl).
  - exact (den_cp cfg LIMIT sarg Hwx j o2d S M a S' M' a' Hp model0 mem0 E ms model T Hd Haw HHA Hk).
Qed.
End H.
(* [comment removed for export] *)
