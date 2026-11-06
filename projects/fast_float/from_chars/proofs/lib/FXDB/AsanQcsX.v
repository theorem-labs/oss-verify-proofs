(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Znumtheory List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.FxAcct.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChSep.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChEnt FxChMain FxChFam.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChSeg OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFam.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_nf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxQNode FxQRNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxMchr.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require FxRunPost.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXDB Require AsanQcsNode AsanQSSites.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxQChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxQRNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxMchr.FxQcsChk OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.FxRunPost OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode.AsanRpNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQcsNode OSSVerify.Proofs.fast_float.from_chars.lib.FXDB.AsanQSSites.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation ASEGSN := AsanUbsan.M.loaded_segments.

Inductive xnode : Type := XQcs (j : nat).     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition ext_rng (fs : list fact) (a : ast) (b nl : lin) : bool := existsb_l (fun p => inside_lin fs b nl (fst p) (snd p)) (a_ext a).
Definition apost_x (img : tree Z) (nk : xnode) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  match nk with
  | XQcs j =>
      match nth_error QSSITES_P j with
      | Some s =>
          let b := rget (s_regs S) (rkey (qs_rB (qss_q s))) in let nl := lsub (rget (s_regs S) (rkey (qs_rA (qss_q s)))) b in
          if (a_on a && match a_pri a with [] => false | _ => true end)%bool then
            if ext_rng (s_facts S) a b nl then (if qcs_chk0 img s S M then Some (qcs_post s S, M, a) else None) else None
          else None
      | None => None
      end
  end.
(* [comment removed for export] *)
Definition apostS {N1 N2 A : Type} (ap1 : N1 -> sst -> smodel -> A -> option (sst * smodel * A)) (ap2 : N2 -> sst -> smodel -> A -> option (sst * smodel * A))
    (nk : N1 + N2) : sst -> smodel -> A -> option (sst * smodel * A) := match nk with inl n => ap1 n | inr n => ap2 n end.

(* [comment removed for export] *)
Lemma words_in_class_shadow : forall sb c szj B n x, sb mod 4096 = 0 -> 0 <= sb -> 0 <= c -> 0 <= szj <= 262144 -> 1 <= n ->
  sb + 4294967296 * c <= B -> B + n <= sb + 4294967296 * c + szj -> qcs_words B n x ->
  sb / 8 + 2147450880 + 536870912 * c <= x < sb / 8 + 2147450880 + 536870912 * c + 32768.
Proof.
  intros sb c szj B n x Hsb Hsb0 Hc Hszj Hn H1 H2 Hx. unfold qcs_words, SH_OFF in Hx.
  assert (Esb : sb = 4096 * (sb / 4096)) by (pose proof (Z.div_mod sb 4096 ltac:(lia)); lia).
  set (k := sb / 4096) in *. assert (Es8 : sb / 8 = 512 * k) by (rewrite Esb; replace (4096 * k) with (512 * k * 8) by ring; apply Z.div_mul; lia).
  rewrite Es8.
  set (SHc := 512 * k + 2147450880 + 536870912 * c).
  assert (HSH8 : SHc = 8 * (64 * k + 268431360 + 67108864 * c)) by (unfold SHc; ring).
  assert (HB8 : 512 * k + 536870912 * c <= B / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HE8 : (B + n - 1) / 8 < 512 * k + 536870912 * c + 32768) by (apply Z.div_lt_upper_bound; lia).
  assert (HBB : B / 8 <= (B + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (Hlo : forall y, SHc <= y -> SHc <= 8 * (y / 8)).
  { intros y Hy. rewrite HSH8 in *. assert (64 * k + 268431360 + 67108864 * c <= y / 8) by (apply Z.div_le_lower_bound; lia). lia. }
  assert (Hhi : forall y, y < SHc + 32768 -> 8 * (y / 8) + 8 <= SHc + 32768).
  { intros y Hy. rewrite HSH8 in *. assert (y / 8 < 64 * k + 268431360 + 67108864 * c + 4096) by (apply Z.div_lt_upper_bound; lia). lia. }
  fold SHc. destruct Hx as [Hx|Hx].
  - pose proof (Hlo (2147450880 + B / 8) ltac:(unfold SHc; lia)). pose proof (Hhi (2147450880 + B / 8) ltac:(unfold SHc; lia)). lia.
  - pose proof (Hlo (2147450880 + (B + n - 1) / 8) ltac:(unfold SHc; lia)). pose proof (Hhi (2147450880 + (B + n - 1) / 8) ltac:(unfold SHc; lia)). lia.
Qed.

Section X.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable img : tree Z.
Hypothesis Hwx : wx_segs_nowrap ASEGSN.
Hypothesis Himg : img_ok ASEGSN img.
(* [comment removed for export] *)
Hypothesis Hshm : forall model0 mem0 E S M ms model a, DEN ASEGSN LIMIT model0 mem0 E S M ms model -> HA_on E M a mem0 -> a_pri a <> [] ->
  forall c, In c CLS -> 1 <= z_j (pden E a) c ->
  forall x, z_sh (pden E a) + 536870912 * c <= x < z_sh (pden E a) + 536870912 * c + 32768 ->
  rd1 ASEGSN (mrestrict (Hof E M model) (ms_mem ms)) (Z_to_bv 64 x) <> None.

#[using="Hwx Himg Hshm"] Theorem xnode_ok : forall nk, anode_ok ASEGSN cfg LIMIT (apost_x img) awf HA nk.
Proof. LiaFast.lf_pins (fun (Hwx Himg Hshm : LiaFast.U) => LiaFast.u0).
  intros [j] S M a S' M' a' Hp model0 mem0 E ms model T Hd Hw HAa Hk. cbn [apost_x] in Hp.
  destruct (nth_error QSSITES_P j) as [s|] eqn:Hj; [|discriminate]. cbv zeta in Hp.
  destruct (a_on a && match a_pri a with [] => false | _ => true end)%bool eqn:Hon; [|discriminate].
  destruct (ext_rng (s_facts S) a (rget (s_regs S) (rkey (qs_rB (qss_q s))))
              (lsub (rget (s_regs S) (rkey (qs_rA (qss_q s)))) (rget (s_regs S) (rkey (qs_rB (qss_q s)))))) eqn:Hxr; [|discriminate].
  destruct (qcs_chk0 img s S M) eqn:Hck; [|discriminate]. injection Hp as <- <- <-.
  apply andb_prop in Hon as [Hon Hpri]. assert (Hne : a_pri a <> []) by (destruct (a_pri a); [discriminate Hpri | discriminate]).
  pose proof (HAa Hon) as HAon. destruct (ha_pri _ _ _ _ HAon Hne) as [Hi _ _ _ _ _ Hxt].
  pose proof QSSITES_P_ok as Hss. rewrite Forall_forall in Hss. pose proof (Hss s (nth_error_In _ _ Hj)) as Hs.
  set (b := rget (s_regs S) (rkey (qs_rB (qss_q s)))) in *. set (nl := lsub (rget (s_regs S) (rkey (qs_rA (qss_q s)))) b) in *.
  destruct (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF & _).
  (* [comment removed for export] *)
  unfold ext_rng in Hxr. rewrite existsb_l_eq in Hxr. apply existsb_exists in Hxr as (p & Hp & Hin).
  destruct (Hxt p Hp) as ((c & Hc & X1 & X2 & X3) & _). pose proof (in_cls_rng c Hc) as Hcr.   (* [comment removed for export] *)
  pose proof Hi as Hi0. unfold INV_A in Hi0.
  destruct (iz_sb _ _ Hi0) as [Hsb1 Hsb2]. pose proof (iz_sh _ _ Hi0) as Hsh. pose proof (iz_pg _ _ Hi0) as Hpg. pose proof (iz_cls _ _ Hi0) as Hcls.
  unfold PG_SIZE in Hpg.
  assert (Hjb : 0 <= sz_tbl c * z_j (pden E a) c <= 262144 /\ (1 <= sz_tbl c * z_j (pden E a) c -> 1 <= z_j (pden E a) c)).
  { destruct (cls_tbl c Hc) as (Hszp & _ & _ & Hnw & Hnm & Hmc).
    destruct (Hcls c Hc) as [(J0 & _)|(J1 & _ & Jb & _)]; [rewrite J0, Z.mul_0_r; split; [lia | intros X; lia]|]. split; [|intros _; exact J1].
    assert (Hq : sz_tbl c * (262144 / sz_tbl c) <= 262144) by lia.
    assert (Hjq : z_j (pden E a) c <= 262144 / sz_tbl c) by lia. split; nia. }
  assert (Hb48 : uE E (fst p) + uE E (snd p) < 2 ^ 48) by lia.
  destruct (inside_lin_sound E (s_facts S) HF b nl (fst p) (snd p) Hin Hb48) as [L1 L2].
  (* [comment removed for export] *)
  assert (Hn1 : 1 <= uE E nl).
  { unfold qcs_chk0 in Hck. cbv zeta in Hck. fold b nl in Hck. destruct (s_resv S); try discriminate.
    destruct (is_const (rget (s_regs S) (rkey (qs_rP (qss_q s))))); [|discriminate].
    destruct (irange (s_facts S) nl) as [nlo nhi] eqn:Hnr.
    match type of Hck with ((if ?cc then ?x else false) = true) => destruct cc eqn:Hcc; [|discriminate Hck] end.
    repeat match type of Hcc with ((_ && _)%bool = true) => apply andb_prop in Hcc as [Hcc ?Hy] end.
    repeat match goal with Hy : Z.leb _ _ = true |- _ => apply Z.leb_le in Hy end.
    pose proof (irange_sound E (s_facts S) nl HF) as Rn. rewrite Hnr in Rn. cbn [fst snd] in Rn. fold (uE E nl) in Rn. lia. }
  apply (den_qcs_core cfg LIMIT model0 mem0 img Hwx Himg s S M E ms model T Hs Hck Hd).
  - intros x Hx. fold b nl in Hx.
    apply (Hshm model0 mem0 E S M ms model a Hd HAon Hne c Hc ltac:(apply (proj2 Hjb); lia) x).
    rewrite Hsh. apply (words_in_class_shadow (z_sb (pden E a)) c (sz_tbl c * z_j (pden E a) c) (uE E b) (uE E nl) x Hsb2 ltac:(lia) ltac:(lia) (proj1 Hjb) Hn1);
      [lia | lia | exact Hx].
  - intros E' ms' model' Ha Hd'. apply (Hk E' mem0 ms' model' Ha); [intros q _ w _; reflexivity | exact Hd'|].
    exact (HA_agree (s_next S) E E' M a mem0 (dn_wf _ _ _ _ _ _ _ _ _ Hd) Hw Ha HAa).
Qed.

(* [comment removed for export] *)
#[using="Hwx Himg Hshm"] Theorem anodeS_ok : forall {N1 : Type} (ap1 : N1 -> sst -> smodel -> ast -> option (sst * smodel * ast)),
  (forall nk, anode_ok ASEGSN cfg LIMIT ap1 awf HA nk) -> forall nk, anode_ok ASEGSN cfg LIMIT (apostS ap1 (apost_x img)) awf HA nk.
Proof. LiaFast.lf_pins (fun (Hwx Himg Hshm : LiaFast.U) => LiaFast.u0). intros N1 ap1 H1 [n|x]; [exact (H1 n) | exact (xnode_ok x)]. Qed.
End X.
(* [comment removed for export] *)
