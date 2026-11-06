(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import AxSymExec3 AsanPlanCore.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost SegProg.
Import ListNotations. Import AX2. Import ST.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section SH.
  Variable segs : list Segment.
  Variable gfp : nat -> list expr -> list SG.gwin.
  Variable gvc : SG.vc -> bool.

  (* [comment removed for export] *)
  Definition pclosedH (P : SP.prog) : bool :=
    (forallb tm_closed (SP.p_tm P) && forallb tm_closed (SP.p_ex P) && forallb tm_closed (SP.p_xt P)
     && forallb (SP.win_closed (SP.p_G P)) (SP.p_W P)
     && forallb (fun T => Nat.leb (SP.p_G P) (t_ns T)) (SP.p_xt P)
     && forallb (fun S => tm_closed (SP.sm_pre S) && forallb tm_closed (SP.sm_post S) && Nat.leb (SP.sm_G S) (t_ns (SP.sm_pre S))
                          && SX.aw_closed (SP.sm_G S) (SP.sm_A S) && SP.ps_closed (SP.sm_G S) (SP.sm_PS S))%bool (SP.p_cs P)
     && SX.aw_closed (SP.p_G P) (SP.p_A P)
     && SP.ps_closed (SP.p_G P) (SP.p_PS P) && forallb (SP.win_closed (SP.p_G P)) (SP.p_CR P) && APC.kn_vars_lt (SP.p_G P) (SP.p_IK P))%bool.

  Lemma tms_check_pairsH : forall P IT fuel rr (l : list (tmpl * list xhint)),
    SP.tms_check segs gfp gvc P IT fuel rr (map fst l) (map snd l)
    = forallb (fun th => SP.tm_check segs gfp gvc P IT fuel rr (fst th) (snd th)) l.
  Proof. intros P IT fuel rr l. induction l as [|[T h] r IH]; cbn [SP.tms_check forallb hd tl map fst snd]; [reflexivity|]. rewrite IH. reflexivity. Qed.

  Lemma pcheckH_of_chunksH : forall P IT fuel rr (chunks : list (list (tmpl * list xhint))) hints,
    pclosedH P = true -> SP.p_tm P = map fst (concat chunks) -> hints = map snd (concat chunks) ->
    Forall (fun l => forallb (fun th => SP.tm_check segs gfp gvc P IT fuel rr (fst th) (snd th)) l = true) chunks ->
    SP.pcheckH segs gfp gvc P IT fuel rr hints = true.
  Proof.
    intros P IT fuel rr chunks hints HC HE HH HF.
    assert (HT : forallb (fun th => SP.tm_check segs gfp gvc P IT fuel rr (fst th) (snd th)) (concat chunks) = true).
    { clear HE HH HC. induction HF as [|l r Hl Hr IH]; [reflexivity|]. cbn [concat]. rewrite forallb_app, Hl. exact IH. }
    unfold SP.pcheckH. rewrite HE, HH, tms_check_pairsH, HT. unfold pclosedH in HC. rewrite <- HE.
    repeat match type of HC with (_ && _)%bool = true => apply andb_prop in HC; destruct HC as [HC ?] end.
    repeat (apply andb_true_intro; split); try assumption; reflexivity.
  Qed.
End SH.
