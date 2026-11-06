(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j AIcpghc AIcpya4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.

Module A_PKit.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma PARSE_STACK_val : PARSE_STACK = 9120.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stores.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Fixpoint wzone (E : penv) (A : AS) (excl : list Z) (W : list (Z * Z)) : Prop :=
    match W with
    | [] => True
    | (lo, hi) :: W' =>
        ((exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= lo /\ hi <= p + n)
         \/ (pe_lo E <= lo /\ hi <= pe_fp E + 16)
         \/ (lo = h_vsc (pe_H E) + 1304 /\ hi = h_vsc (pe_H E) + 1320))
        /\ wzone E A excl W'
    end.

  (* [comment removed for export] *)
  Lemma wzone_cases : forall E A excl W a,
    wzone E A excl W -> ~ outside W a ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n)
    \/ (pe_lo E <= a < pe_fp E + 16)
    \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320).
  Proof.
    intros E A excl W a. induction W as [|[lo hi] W IH]; cbn; intros WZ NO; [exfalso; exact (NO I)|].
    destruct WZ as [C WZ].
    destruct (Classical_Prop.classic (lo <= a < hi)) as [IN|NIN].
    - destruct C as [(p & n & L & NI & H1 & H2)|[[H1 H2]|[H1 H2]]].
      + left. exists p, n. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia.
      + right; left. lia.
      + right; right. lia.
    - apply IH; [exact WZ|]. intros O. apply NO. split; [exact NIN| exact O].
  Qed.

  (* [comment removed for export] *)
  Lemma wzone_client_fp : forall E A v excl W j0 j8,
    penv_ok E -> hframe LPA A (pe_H E) ->
    stk rsegs v (pe_lo E) (pe_fp E) -> rw_cells rsegs v (pe_fp E) (pframe E j0 j8) ->
    wzone E A excl W -> client_fp LPA A v W.
  Proof.
    intros E A v excl W j0 j8 PE [age HF] ST FR.
    destruct PE as (HG & _ & _ & CEIL & LOP & SPH & _). (first [ dand3 HG as G1 G2 G3 | destruct HG as (G1 & G2 & G3) ]). unfold HFSIZE in G3.
    pose proof alloc_ceiling_num as ACV. rewrite PARSE_STACK_val in LOP.
    assert (MAPW : mapped v (pe_lo E) (pe_fp E + 16 - pe_lo E)).
    { intros i Hi. unfold pe_fp, PARSE_FRAME in *.
      destruct (Z_lt_le_dec (pe_lo E + i) (pe_sp E - 320)) as [Hb|Hb].
      - apply (stk_mapped (Clg:=Clg) (L:=LPA) v (pe_lo E) (pe_sp E - 320) (pe_lo E) (pe_sp E - 320 - pe_lo E) ST CEIL ltac:(lia) ltac:(lia)). lia.
      - pose proof (rw_cells_mapped LPA v _ _ FR ltac:(apply (off_image_stack LPA); lia)) as M.
        rewrite pframe_size in M. replace (pe_lo E + i) with (pe_sp E - 320 + (pe_lo E + i - (pe_sp E - 320))) by lia.
        apply M. lia. }
    induction W as [|[lo hi] W IH]; cbn; intros WZ; [exact I|].
    destruct WZ as [C WZ]. split; [|apply IH; exact WZ].
    destruct C as [(p & n & L & NI & H1 & H2)|[[H1 H2]|[H1 H2]]].
    - right; left. exists p, n. auto.
    - left. split; [lia|]. split; [unfold pe_fp, PARSE_FRAME in *; lia|].
      intros i Hi. replace (lo + i) with (pe_lo E + (lo + i - pe_lo E)) by lia. apply MAPW. lia.
    - right; right; left. exists (h_ff (pe_H E)), HCLASS, age. split; [exact HF|].
      change (fsize HCLASS) with 8192. unfold h_vsc in *. lia.
  Qed.

  Variables (E : penv) (A : AS) (m : mem) (md : Model) (v' : mem) (excl : list Z) (W : list (Z * Z)).
  Hypothesis PE : penv_ok E.
  Hypothesis AINV : ainv A m md.
  Hypothesis HFR : hframe LPA A (pe_H E).
  Hypothesis MU : munch W (aview A m) v'.
  Hypothesis WM : wmono rsegs (aview A m) v'.
  Hypothesis WZ : wzone E A excl W.
  (* [comment removed for export] *)
  Local Ltac touch := pose proof (conj PE (conj AINV (conj HFR (conj MU (conj WM WZ))))) as TT__; clear TT__.

  (* [comment removed for export] *)
  Lemma outside_blk : forall o0 k a,
    In o0 excl -> a_live A o0 = Some k -> o0 <= a < o0 + k -> outside W a.
  Proof.
    touch.
    intros o0 k a IN L Ha. destruct HFR as [age HF].
    destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
    destruct PE as (HG & _ & _ & CEIL & LOP & SPH & _).
    (first [ pose proof ((live_geomP LPA A m md o0 k AINV L)) as dR_2; dand5 dR_2 as _ _ LO HI _ | destruct (live_geomP LPA A m md o0 k AINV L) as (_ & _ & LO & HI & _) ]).
    destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|R]].
    - assert (NE : p <> o0) by (intros ->; exact (NI IN)).
      pose proof (as_live_disjoint LPA A m md p n o0 k AINV Lp L NE). lia.
    - rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME in *. lia.
    - pose proof (as_frame_blk_disjoint LPA A m md (h_ff (pe_H E)) HCLASS age o0 k AINV HF L) as D.
      change (fsize HCLASS) with 8192 in D. unfold h_vsc in R. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma outside_hframe : forall a,
    (h_ff (pe_H E) <= a < h_ff (pe_H E) + 8192 \/ sh (h_ff (pe_H E)) <= a < sh (h_ff (pe_H E)) + 1024) ->
    ~ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320) -> outside W a.
  Proof.
    touch.
    intros a Ha NC. destruct HFR as [age HF].
    destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
    destruct PE as (HG & _ & _ & CEIL & LOP & SPH & _). (first [ dand3 HG as G1 G2 G3 | destruct HG as (G1 & G2 & G3) ]). unfold HFSIZE in G3.
    pose proof alloc_ceiling_num as ACV.
    pose proof (app_sh_facts LPA (h_ff (pe_H E)) 8192 G2) as SF.   (* [comment removed for export] *)
    change ((8192 + 7) / 8) with 1024 in SF. rewrite SHMAX_val in SF.
    destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|R]].
    - pose proof (as_frame_blk_disjoint LPA A m md (h_ff (pe_H E)) HCLASS age p n AINV HF Lp) as D.
      change (fsize HCLASS) with 8192 in D.
      (first [ pose proof ((live_geomP LPA A m md p n AINV Lp)) as dR_4; dand4 dR_4 as _ _ PLO _ | destruct (live_geomP LPA A m md p n AINV Lp) as (_ & _ & PLO & _) ]). unfold kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME, kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - exact (NC R).
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma bytes_at_stores_blk : forall o0 k o bs,
    In o0 excl -> a_live A o0 = Some k -> o0 <= o -> o + Z.of_nat (length bs) <= o0 + k ->
    bytes_at rsegs (aview A m) o bs -> bytes_at rsegs v' o bs.
  Proof.
    touch.
    (intros o0 k o bs IN L H1 H2; (first [ intro dR_35; dand3 dR_35 as B0 B1 B | intros (B0 & B1 & B) ])). split; [exact B0|]. split; [exact B1|]. intros i Hi.
    unfold mrd. rewrite MU; [apply B; exact Hi|]. rewrite wa_unsigned by lia.
    eapply outside_blk; [exact IN| exact L| lia].
  Qed.

  Lemma vsb_obj_stores : forall S vr fin,
    In S excl -> In (vb_buf vr) excl -> vsb_obj LPA A (aview A m) S vr fin -> vsb_obj LPA A v' S vr fin.
  Proof.
    touch.
    intros S vr fin I1 I2 VO. (first [ pose proof (VO) as dR_6; dand5 dR_6 as _ _ LS LB _ | pose proof VO as (_ & _ & LS & LB & _) ]).
    eapply (vsb_obj_munch A W); [exact VO| exact MU| exact WM|].
    intros a [Ha|Ha]; [eapply (outside_blk S 40)| eapply (outside_blk (vb_buf vr) (vb_size vr))]; try eassumption.
  Qed.

  (* [comment removed for export] *)

  Lemma data_obj_stores : forall DATA inp,
    In DATA excl -> data_obj LPA A (aview A m) DATA inp -> data_obj LPA A v' DATA inp.
  Proof.
    touch.
    (intros DATA inp IN; (first [ intro dR_36; dand3 dR_36 as L B LEN | intros (L & B & LEN) ])). split; [exact L|]. split; [|exact LEN].
    eapply (bytes_at_stores_blk DATA (Z.of_nat (length inp))); [exact IN| exact L| lia| lia| exact B].
  Qed.

  (* [comment removed for export] *)
  Lemma henv_stores :
    (forall a, h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320 -> outside W a) ->
    henv_ok LPA VIA (pe_H E) A (aview A m) -> henv_ok LPA VIA (pe_H E) A v'.
  Proof.
    touch.
    intros NV HE. destruct PE as (HG & PE'). (first [ pose proof (HG) as dR_8; dand3 dR_8 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE in G3.
    eapply (henv_ok_munch LPA); [exact HE| exact MU| exact WM| exact HG|].
    intros a Ha. unfold HOBJ_END, HFSIZE in Ha.
    destruct (Classical_Prop.classic (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320)) as [C|NC]; [apply NV; exact C|].
    destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
    - (* [comment removed for export] *)
      destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
      destruct HFR as [age HF]. pose proof alloc_ceiling_num as ACV.
      destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|R]].
      + (first [ pose proof ((live_geomP LPA A m md p n AINV Lp)) as dR_9; dand4 dR_9 as _ _ PLO _ | destruct (live_geomP LPA A m md p n AINV Lp) as (_ & _ & PLO & _) ]). cbn [vi_bss_vsc VIA] in Ha. unfold kHighMemBeg in PLO. all_app_facts. unhide_app. lia.
      + cbn [vi_bss_vsc VIA] in Ha. rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME in *. lia.
      + cbn [vi_bss_vsc VIA] in Ha. unfold h_vsc, kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
      destruct HFR as [age HF]. pose proof alloc_ceiling_num as ACV.
      destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|R]].
      + (first [ pose proof ((live_geomP LPA A m md p n AINV Lp)) as dR_10; dand4 dR_10 as _ _ PLO _ | destruct (live_geomP LPA A m md p n AINV Lp) as (_ & _ & PLO & _) ]). cbn [vi_bss_cp VIA] in Ha. unfold kHighMemBeg in PLO. all_app_facts. unhide_app. lia.
      + cbn [vi_bss_cp VIA] in Ha. rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME in *. lia.
      + cbn [vi_bss_cp VIA] in Ha. unfold h_vsc, kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - exfalso. exact (NC Ha).
    - apply outside_hframe; [| exact NC]. left. unfold h_cp in Ha. lia.
    - apply outside_hframe; [| exact NC]. right. change (8192 / 8) with 1024 in Ha. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_shadow_stores : forall SB NS lo hi,
    stack_shadow LPA (aview A m) SB NS lo hi -> stack_shadow LPA v' SB NS lo hi.
  Proof.
    touch.
    (intros SB NS lo hi; (first [ intro dR_37; dand6 dR_37 as B N0 Lq Hh SLO T | intros (B & N0 & Lq & Hh & SLO & T) ])). split; [| exact (conj N0 (conj Lq (conj Hh (conj SLO T))))].
    eapply (bytes_at_munch LPA); [exact B| exact MU|]. rewrite repeat_length, Z2Nat.id by lia.
    intros a Ha. destruct HFR as [age HF]. pose proof alloc_ceiling_num as ACV.
    destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
    destruct PE as (HG & _ & _ & CEIL & LOP & SPH & _). (first [ dand3 HG as G1 G2 G3 | destruct HG as (G1 & G2 & G3) ]).
    destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|R]].
    - (first [ pose proof ((live_geomP LPA A m md p n AINV Lp)) as dR_12; dand4 dR_12 as _ _ PLO _ | destruct (live_geomP LPA A m md p n AINV Lp) as (_ & _ & PLO & _) ]). unfold kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME, kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - unfold h_vsc, kHighMemBeg in *. all_app_facts. unhide_app. lia.
  Qed.
End Stores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CStep.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition w_in_zone (E : penv) (x : pst) (W : list (Z * Z)) : Prop :=
    forall a, 0 <= a < 2^64 -> ~ outside W a -> (pe_sp E - PARSE_STACK <= a < pe_sp E) \/ pzone E x a.

  Lemma w_in_zone_nil : forall E x, w_in_zone E x [].
  Proof. intros E x a _ NO. exfalso. exact (NO I). Qed.
  Lemma w_in_zone_win : forall E x lo hi W,
    pe_sp E - PARSE_STACK <= lo -> hi <= pe_sp E -> w_in_zone E x W -> w_in_zone E x ((lo, hi) :: W).
  Proof.
    intros E x lo hi W H1 H2 IH a Ha NO. cbn in NO.
    destruct (Classical_Prop.classic (lo <= a < hi)) as [IN|NIN]; [left; lia|]. apply IH; [exact Ha|]. intros O. apply NO. split; assumption.
  Qed.
  Lemma w_in_zone_zone : forall E x lo hi W,
    (forall a, lo <= a < hi -> pzone E x a) -> w_in_zone E x W -> w_in_zone E x ((lo, hi) :: W).
  Proof.
    intros E x lo hi W HZ IH a Ha NO. cbn in NO.
    destruct (Classical_Prop.classic (lo <= a < hi)) as [IN|NIN]; [right; apply HZ; exact IN|]. apply IH; [exact Ha|]. intros O. apply NO. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma parse_window_mapped : forall E v j0 j8,
    penv_ok E -> stk rsegs v (pe_lo E) (pe_fp E) -> rw_cells rsegs v (pe_fp E) (pframe E j0 j8) ->
    mapped v (pe_sp E - PARSE_STACK) PARSE_STACK.
  Proof.
    intros E v j0 j8 PE ST FR. destruct PE as (HG & _ & _ & CEIL & LOP & _).
    eapply (window_mapped LPA v (pe_lo E) (pe_fp E) (pe_sp E) PARSE_STACK);
      [exact ST| exact FR| rewrite pframe_size; unfold pe_fp, PARSE_FRAME; lia| exact CEIL| lia| rewrite PARSE_STACK_val; unfold pe_fp, PARSE_FRAME; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_step_stores : forall E x x' A v v' W,
    cframe LPA (owned (pe_A0 E)) (owned A) (pe_sp E) PARSE_STACK
           (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E)) (parse_new (x_v x) (x_vv x) (x_va x) (x_vio x)) (pe_v0 E) v ->
    munch W v v' -> w_in_zone E x W ->
    mapped v' (pe_sp E - PARSE_STACK) PARSE_STACK ->
    (forall a, parse_new (x_v x') (x_vv x') (x_va x') (x_vio x') a -> pzone E x a) ->
    cframe LPA (owned (pe_A0 E)) (owned A) (pe_sp E) PARSE_STACK
           (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E)) (parse_new (x_v x') (x_vv x') (x_va x') (x_vio x')) (pe_v0 E) v'.
  Proof.
    intros E x x' A v v' W CF MU WZ MAP PN.
    assert (C2 : cframe LPA (owned A) (owned A) (pe_sp E) PARSE_STACK (pzone E x) (pzone E x) v v').
    { eapply (cframe_noalloc LPA); [exact MU| exact WZ| exact MAP| intros a X; exact X]. }
    eapply (cframe_seq LPA); [exact CF| exact C2| lia| lia| exact MAP| intros a X; exact X| |].
    - intros a X. unfold pzone in X. destruct X as [X|X]; [right; exact X| left; exact X].
    - intros a X. destruct (PN a X) as [Y|Y]; [right; right; exact Y| left; exact Y].
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_step_call : forall E x x' A A' v v' sp' win Vc Nc,
    cframe LPA (owned (pe_A0 E)) (owned A) (pe_sp E) PARSE_STACK
           (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E)) (parse_new (x_v x) (x_vv x) (x_va x) (x_vio x)) (pe_v0 E) v ->
    cframe LPA (owned A) (owned A') sp' win Vc Nc v v' ->
    pe_sp E - PARSE_STACK <= sp' - win -> sp' <= pe_sp E ->
    mapped v' (pe_sp E - PARSE_STACK) PARSE_STACK ->
    (forall a, Vc a -> pzone E x a) ->
    (forall a, parse_new (x_v x') (x_vv x') (x_va x') (x_vio x') a -> Nc a \/ pzone E x a) ->
    cframe LPA (owned (pe_A0 E)) (owned A') (pe_sp E) PARSE_STACK
           (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E)) (parse_new (x_v x') (x_vv x') (x_va x') (x_vio x')) (pe_v0 E) v'.
  Proof.
    intros E x x' A A' v v' sp' win Vc Nc CF CC LO HI MAP HV HN.
    assert (C2 : cframe LPA (owned A) (owned A') (pe_sp E) PARSE_STACK (pzone E x) Nc v v').
    { eapply (cframe_weaken LPA); [eapply (cframe_reframe LPA); [exact CC| exact LO| exact HI| exact MAP]| lia| exact MAP| exact HV| intros a X; exact X]. }
    eapply (cframe_seq LPA); [exact CF| exact C2| lia| lia| exact MAP| intros a X; exact X| |].
    - intros a X. unfold pzone in X. destruct X as [X|X]; [right; exact X| left; exact X].
    - intros a X. destruct (HN a X) as [Y|[Y|Y]]; [right; left; exact Y| right; right; exact Y| left; exact Y].
  Qed.
End CStep.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section VM.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
End VM.

Lemma vsb_apart3 : forall S x a b c, vsb_apart S x [a; b; c] ->
  S <> a /\ vb_buf x <> a /\ S <> b /\ vb_buf x <> b /\ S <> c /\ vb_buf x <> c.
Proof.
  intros S x a b c H. destruct (H a ltac:(cbn; auto)) as [? ?]. destruct (H b ltac:(cbn; auto)) as [? ?].
  destruct (H c ltac:(cbn; auto 8)) as [? ?]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition oabuf (x : pst) : Z := match x_va x with Some y => vb_buf y | None => 0 end.
Definition oibuf (x : pst) : Z := match x_vi x with Some y => vb_buf y | None => 0 end.

(* [comment removed for export] *)
Ltac neq_close :=
  first [ assumption | apply not_eq_sym; assumption | congruence
        | (repeat match goal with H : _ <> _ |- _ => clear H end; intros; lia) ].

Section Seps.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma pinv_seps : forall {d} E x A m md,   (* [comment removed for export] *)
    penv_ok E -> pinvg d E x A (aview A m) -> ainv A m md ->
    let VEP := pe_VEP E in let S := pe_S E in let B := vb_buf (x_vv x) in let D := pe_DATA E in
    let AT := x_v x Fattr_vsb in let AB := oabuf x in let IC := x_v x Finclude_src in let IB := oibuf x in
       (VEP <> S /\ VEP <> B /\ VEP <> D /\ S <> B /\ S <> D /\ B <> D)
    /\ (let W := pe_wa E in W <> VEP /\ W <> S /\ W <> B /\ W <> D /\ AT <> W /\ AB <> W /\ IC <> W /\ IB <> W)
    /\ (AT <> VEP /\ AT <> S /\ AT <> B /\ AT <> D /\ AB <> VEP /\ AB <> S /\ AB <> B /\ AB <> D)
    /\ (IC <> VEP /\ IC <> S /\ IC <> B /\ IC <> D /\ IB <> VEP /\ IB <> S /\ IB <> B /\ IB <> D)
    /\ (x_va x <> None -> AT <> AB /\ 4096 <= AT /\ 4096 <= AB)
    /\ (x_vi x <> None -> IC <> IB /\ 4096 <= IC /\ 4096 <= IB)
    /\ (x_va x <> None -> x_vi x <> None -> IC <> AT /\ IC <> AB /\ IB <> AT /\ IB <> AB).
  Proof.
    intros d E x A m md PE PI AINV. open_pinv PI. unfold va_world in VA. unfold vi_world in VI.
    clear BASE FLG VSBF STUP STATE CNT VERP PLE B01 TAGI DELIM ESIC UNTL MTCH DOST ARMED ATTR ATTRST MATTR LOOKA LOOKM
          ROOM OUT AVSB HENV STK FRAME MI SS LB NL TC FRS KEEP NEW CF.
    destruct PE as (_ & _ & _ & _ & _ & _ & _ & NE1 & NE2 & NE3 & NE4 & NE5 & NE6 & _).
    destruct VEPO as (LVEP & _). destruct DATA as (LDATA & _).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LVEP)) as dR_13; dand4 dR_13 as _ _ VEPlo _ | destruct (live_geomP LPA _ _ _ _ _ AINV LVEP) as (_ & _ & VEPlo & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LDATA)) as dR_14; dand4 dR_14 as _ _ Dlo _ | destruct (live_geomP LPA _ _ _ _ _ AINV LDATA) as (_ & _ & Dlo & _) ]).
    (first [ pose proof ((vsb_apart3 _ _ _ _ _ APART)) as dR_15; dand6 dR_15 as AP1 AP2 AP3 AP4 AP5 AP6 | pose proof (vsb_apart3 _ _ _ _ _ APART) as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6) ]).
    (first [ pose proof (VSBO) as dR_16; dand6 dR_16 as _ _ LVS LVB SNB _ | pose proof VSBO as (_ & _ & LVS & LVB & SNB & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LVS)) as dR_17; dand4 dR_17 as _ _ Slo _ | destruct (live_geomP LPA _ _ _ _ _ AINV LVS) as (_ & _ & Slo & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LVB)) as dR_18; dand4 dR_18 as _ _ Blo _ | destruct (live_geomP LPA _ _ _ _ _ AINV LVB) as (_ & _ & Blo & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV WAL)) as dR_19; dand4 dR_19 as _ _ Wlo _ | destruct (live_geomP LPA _ _ _ _ _ AINV WAL) as (_ & _ & Wlo & _) ]).
    unfold oabuf, oibuf. cbn zeta.
    split; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | apply not_eq_sym; assumption | congruence]|].
    match goal with |- ?P /\ ?Q => cut (Q /\ P); [intros [X Y]; exact (conj Y X)|] end.
    destruct (x_va x) as [ya|]; destruct (x_vi x) as [yi|].
    - (first [ dand5 VA as ANZ AO _ _ AAP | destruct VA as (ANZ & AO & _ & _ & AAP) ]). (first [ dand7 VI as INZ IO _ _ _ IAP IAP2 | destruct VI as (INZ & IO & _ & _ & _ & IAP & IAP2) ]).
      (first [ pose proof (AO) as dR_22; dand6 dR_22 as _ _ LAS LAB ASB _ | pose proof AO as (_ & _ & LAS & LAB & ASB & _) ]). (first [ pose proof (IO) as dR_23; dand6 dR_23 as _ _ LIS LIB ISB _ | pose proof IO as (_ & _ & LIS & LIB & ISB & _) ]).
      destruct (live_geomP LPA _ _ _ _ _ AINV LAS) as (_ & _ & ? & _). destruct (live_geomP LPA _ _ _ _ _ AINV LAB) as (_ & _ & ? & _).
      destruct (live_geomP LPA _ _ _ _ _ AINV LIS) as (_ & _ & ? & _). destruct (live_geomP LPA _ _ _ _ _ AINV LIB) as (_ & _ & ? & _).
      destruct (AAP (pe_VEP E) ltac:(cbn; auto)) as [? ?]. destruct (AAP (pe_wa E) ltac:(cbn; auto)) as [? ?].
      destruct (AAP (pe_DATA E) ltac:(cbn; auto 6)) as [? ?]. destruct (AAP (pe_S E) ltac:(cbn; auto 8)) as [? ?].
      destruct (AAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [? ?].
      destruct (IAP (pe_VEP E) ltac:(cbn; auto)) as [? ?]. destruct (IAP (pe_wa E) ltac:(cbn; auto)) as [? ?].
      destruct (IAP (pe_DATA E) ltac:(cbn; auto 6)) as [? ?]. destruct (IAP (pe_S E) ltac:(cbn; auto 8)) as [? ?].
      destruct (IAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [? ?].
      destruct (IAP2 (x_v x Fattr_vsb) ltac:(cbn; auto)) as [? ?]. destruct (IAP2 (vb_buf ya) ltac:(cbn; auto)) as [? ?].
      unfold kHighMemBeg in *; all_app_facts; all_app_bounds; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; neq_close.
    - (first [ dand5 VA as ANZ AO _ _ AAP | destruct VA as (ANZ & AO & _ & _ & AAP) ]).
      (first [ pose proof (AO) as dR_25; dand6 dR_25 as _ _ LAS LAB ASB _ | pose proof AO as (_ & _ & LAS & LAB & ASB & _) ]).
      destruct (live_geomP LPA _ _ _ _ _ AINV LAS) as (_ & _ & ? & _). destruct (live_geomP LPA _ _ _ _ _ AINV LAB) as (_ & _ & ? & _).
      destruct (AAP (pe_VEP E) ltac:(cbn; auto)) as [? ?]. destruct (AAP (pe_wa E) ltac:(cbn; auto)) as [? ?].
      destruct (AAP (pe_DATA E) ltac:(cbn; auto 6)) as [? ?]. destruct (AAP (pe_S E) ltac:(cbn; auto 8)) as [? ?].
      destruct (AAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [? ?].
      rewrite VI. unfold kHighMemBeg in *; all_app_facts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; neq_close.
    - (first [ dand7 VI as INZ IO _ _ _ IAP _ | destruct VI as (INZ & IO & _ & _ & _ & IAP & _) ]).
      (first [ pose proof (IO) as dR_27; dand6 dR_27 as _ _ LIS LIB ISB _ | pose proof IO as (_ & _ & LIS & LIB & ISB & _) ]).
      destruct (live_geomP LPA _ _ _ _ _ AINV LIS) as (_ & _ & ? & _). destruct (live_geomP LPA _ _ _ _ _ AINV LIB) as (_ & _ & ? & _).
      destruct (IAP (pe_VEP E) ltac:(cbn; auto)) as [? ?]. destruct (IAP (pe_wa E) ltac:(cbn; auto)) as [? ?].
      destruct (IAP (pe_DATA E) ltac:(cbn; auto 6)) as [? ?]. destruct (IAP (pe_S E) ltac:(cbn; auto 8)) as [? ?].
      destruct (IAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [? ?].
      rewrite VA. unfold kHighMemBeg in *; all_app_facts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; neq_close.
    - rewrite VA, VI. unfold kHighMemBeg in *; all_app_facts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; neq_close.
  Qed.
End Seps.

(* [comment removed for export] *)
Section WoTwins.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Record wo_seps_rec (E : penv) (x : pst) : Prop := Build_wo_seps_rec {
    wo_D_VS : pe_VEP E <> pe_S E; wo_D_VB : pe_VEP E <> vb_buf (x_vv x); wo_D_VD : pe_VEP E <> pe_DATA E;
    wo_D_SB : pe_S E <> vb_buf (x_vv x); wo_D_SD : pe_S E <> pe_DATA E; wo_D_BD : vb_buf (x_vv x) <> pe_DATA E;
    wo_D_WV : pe_wa E <> pe_VEP E; wo_D_WS : pe_wa E <> pe_S E; wo_D_WB : pe_wa E <> vb_buf (x_vv x); wo_D_WD : pe_wa E <> pe_DATA E;
    wo_D_AW : x_v x Fattr_vsb <> pe_wa E; wo_D_ABW : oabuf x <> pe_wa E; wo_D_IW : x_v x Finclude_src <> pe_wa E; wo_D_IBW : oibuf x <> pe_wa E;
    wo_D_AV : x_v x Fattr_vsb <> pe_VEP E; wo_D_AS : x_v x Fattr_vsb <> pe_S E; wo_D_AB : x_v x Fattr_vsb <> vb_buf (x_vv x); wo_D_AD : x_v x Fattr_vsb <> pe_DATA E;
    wo_D_ABV : oabuf x <> pe_VEP E; wo_D_ABS : oabuf x <> pe_S E; wo_D_ABB : oabuf x <> vb_buf (x_vv x); wo_D_ABD : oabuf x <> pe_DATA E;
    wo_D_IV : x_v x Finclude_src <> pe_VEP E; wo_D_IS : x_v x Finclude_src <> pe_S E; wo_D_IB : x_v x Finclude_src <> vb_buf (x_vv x); wo_D_ID : x_v x Finclude_src <> pe_DATA E;
    wo_D_IBV : oibuf x <> pe_VEP E; wo_D_IBS : oibuf x <> pe_S E; wo_D_IBB : oibuf x <> vb_buf (x_vv x); wo_D_IBD : oibuf x <> pe_DATA E;
    wo_D_AA : x_va x <> None -> x_v x Fattr_vsb <> oabuf x /\ 4096 <= x_v x Fattr_vsb /\ 4096 <= oabuf x;
    wo_D_II : x_vi x <> None -> x_v x Finclude_src <> oibuf x /\ 4096 <= x_v x Finclude_src /\ 4096 <= oibuf x;
    wo_D_AI : x_va x <> None -> x_vi x <> None -> x_v x Finclude_src <> x_v x Fattr_vsb /\ x_v x Finclude_src <> oabuf x /\ oibuf x <> x_v x Fattr_vsb /\ oibuf x <> oabuf x }.
  Lemma wo_pinv_seps_r : forall {d} E x A m md, penv_ok E -> pinvg d E x A (aview A m) -> ainv A m md -> wo_seps_rec E x.
  Proof.
    intros d E x A m md PE PI AINV.
    (first [ pose proof ((pinv_seps _ _ _ _ _ PE PI AINV)) as dR_28; dex4 dR_28 as g1 g2 g3 g4; dand3 dR_28 as DAA DII DAI | pose proof ((pinv_seps _ _ _ _ _ PE PI AINV)) as dR_28; dand7 dR_28 as g1 g2 g3 g4 DAA DII DAI | pose proof (pinv_seps _ _ _ _ _ PE PI AINV) as (g1 & g2 & g3 & g4 & DAA & DII & DAI) ]). cbn zeta in *.
    destruct g1 as (? & ? & ? & ? & ? & ?). destruct g2 as (? & ? & ? & ? & ? & ? & ? & ?).
    destruct g3 as (? & ? & ? & ? & ? & ? & ? & ?). destruct g4 as (? & ? & ? & ? & ? & ? & ? & ?).
    constructor; assumption.
  Qed.
  Record wo_penv_rec (E : penv) : Prop := Build_wo_penv_rec {
    wo_HG : henv_geom LPA (pe_H E); wo_FL : 0 <= pe_flags E < 16; wo_NN : 1 <= pe_N E < NMAX;
    wo_CEIL : alloc_ceiling <= pe_lo E; wo_LOP : pe_lo E + PARSE_STACK <= pe_sp E; wo_SPH : pe_sp E + 64 <= 2^47; wo_SP16 : pe_sp E mod 16 = 0;
    wo_NE1 : pe_VEP E <> pe_S E; wo_NE2 : pe_wa E <> pe_S E; wo_NE3 : pe_DATA E <> pe_VEP E; wo_NE4 : pe_DATA E <> pe_S E; wo_NE5 : pe_DATA E <> pe_wa E;
    wo_NE6 : pe_VEP E <> pe_wa E;
    wo_BUDL : a_livebytes (pe_A0 E) + PARSE_LIVE (pe_N E) <= LIVE_MAX; wo_BUDN : a_nlive (pe_A0 E) + PARSE_NLIVE <= NLIVE_MAX;
    wo_LIBF : lib_frames (pe_A0 E); wo_LB0 : a_live (pe_A0 E) (pe_b E) = Some 16; wo_LS0 : a_live (pe_A0 E) (pe_S E) = Some 40 }.
  Lemma wo_penv_ok_r : forall E, penv_ok E -> wo_penv_rec E.
  Proof. intros E (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?). constructor; assumption. Qed.
  Lemma wo_penv_ne_vd : forall E, penv_ok E -> pe_VEP E <> pe_DATA E.
  Proof. intros E PE XX. destruct PE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & XE & _). exact (XE (eq_sym XX)). Qed.
  Record wo_geom_rec (A : AS) (m : mem) (p n : Z) : Prop := Build_wo_geom_rec {
    wo_g1 : 0 <= n < REQ_MAX; wo_g2 : p mod 16 = 0;
    wo_g3 : app_range LPA p n /\ (n <= 64512 -> kHighMemBeg <= p) /\ (cl_image_lo LPA <= 65536 -> cl_image_hi LPA <= p);
    wo_g4 : p + n <= alloc_ceiling; wo_g5 : off_image LPA p n; wo_g6 : mapped (aview A m) p n; wo_g7 : forall i, 0 <= i < n -> ~ owned A (p + i) }.
  Lemma wo_live_geom_r : forall A m md p n, ainv A m md -> a_live A p = Some n -> wo_geom_rec A m p n.
  Proof. intros A m md p n AI0 LV. destruct (live_geomP LPA A m md p n AI0 LV) as (? & ? & ? & ? & ? & ? & ?). constructor; assumption. Qed.
End WoTwins.

Section Costs.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma ocosts_nonneg : forall {d} E x A v, pinvg d E x A v -> 0 <= oacost x /\ 0 <= oicost x.
  Proof.
    intros d E x A v PI. pose proof (pi_va _ _ _ _ PI) as VA. pose proof (pi_vi _ _ _ _ PI) as VI.
    unfold va_world in VA. unfold vi_world in VI. unfold oacost, oicost. split.
    - destruct (x_va x) as [y|]; [|lia]. (first [ dand3 VA as _ (_ & VIy & _) _ | destruct VA as (_ & (_ & VIy & _) & _) ]). unfold vsb_inv in VIy. lia.
    - destruct (x_vi x) as [y|]; [|lia]. (first [ dand3 VI as _ (_ & VIy & _) _ | destruct VI as (_ & (_ & VIy & _) & _) ]). unfold vsb_inv in VIy. lia.
  Qed.
End Costs.

Section Misc.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma parse_new_same : forall E x v' a,
  v' Fattr_vsb = x_v x Fattr_vsb -> v' Finclude_src = x_v x Finclude_src ->
  parse_new v' (x_vv x) (x_va x) (x_vio x) a -> pzone E x a.
Proof.
  intros E x v' a E1 E2 X. unfold pzone. right. unfold parse_new in *. rewrite E1, E2 in X. exact X.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pslice (E : penv) (q p : Z) : list byte :=
  firstn (Z.to_nat (p - q)) (skipn (Z.to_nat (q - pe_DATA E)) (pe_inp E)).

Lemma pslice_length : forall E q p,
  pe_DATA E <= q -> q <= p -> p <= pe_e E -> Z.of_nat (length (pslice E q p)) = p - q.
Proof.
  intros E q p H1 H2 H3. unfold pslice, pe_e, pe_N in *.
  rewrite firstn_length, skipn_length. lia.
Qed.

Lemma bytes_at_sub : forall segs m a bs k n,
  bytes_at segs m a bs -> (k + n <= length bs)%nat ->
  bytes_at segs m (a + Z.of_nat k) (firstn n (skipn k bs)).
Proof.
  intros segs m a bs k n B Hkn.
  rewrite <- (firstn_skipn k bs) in B. apply bytes_at_app in B as [B1 B2].
  rewrite firstn_length_le in B2 by lia.
  rewrite <- (firstn_skipn n (skipn k bs)) in B2. apply bytes_at_app in B2 as [B2 _]. exact B2.
Qed.

Lemma pslice_bytes : forall segs E m q p,
  bytes_at segs m (pe_DATA E) (pe_inp E) -> pe_DATA E <= q -> q <= p -> p <= pe_e E ->
  bytes_at segs m q (pslice E q p).
Proof.
  intros segs E m q p B H1 H2 H3. unfold pslice, pe_e, pe_N in *.
  replace q with (pe_DATA E + Z.of_nat (Z.to_nat (q - pe_DATA E))) at 1 by lia.
  apply bytes_at_sub; [exact B| lia].
Qed.

(* [comment removed for export] *)
Lemma look_read : forall segs E x m,
  bytes_at segs m (pe_DATA E) (pe_inp E) -> pe_DATA E <= x_p x -> x_p x < pe_e E ->
  exists b, nth_error (pe_inp E) (Z.to_nat (x_p x - pe_DATA E)) = Some b /\ bv_unsigned b = look E x /\
            ov_read_bytes segs m (wa (x_p x)) 1 = Some [b].
Proof.
  intros segs E x m B H1 H2. unfold look, pe_e, pe_N in *.
  destruct (nth_error (pe_inp E) (Z.to_nat (x_p x - pe_DATA E))) as [b|] eqn:EN.
  2:{ exfalso. apply nth_error_None in EN. lia. }
  exists b. split; [reflexivity|]. split; [reflexivity|].
  eapply u8ro_read; [exact B| exact EN| lia| unfold wa; f_equal; lia].
Qed.

(* [comment removed for export] *)
Lemma payload_read : forall segs E m q,
  bytes_at segs m (pe_DATA E) (pe_inp E) -> pe_DATA E <= q -> q < pe_e E ->
  exists b, nth_error (pe_inp E) (Z.to_nat (q - pe_DATA E)) = Some b /\
            ov_read_bytes segs m (wa q) 1 = Some [b].
Proof.
  intros segs E m q B H1 H2. unfold pe_e, pe_N in *.
  destruct (nth_error (pe_inp E) (Z.to_nat (q - pe_DATA E))) as [b|] eqn:EN.
  2:{ exfalso. apply nth_error_None in EN. lia. }
  exists b. split; [reflexivity|].
  eapply u8ro_read; [exact B| exact EN| lia| unfold wa; f_equal; lia].
Qed.
End Misc.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac hide_neqs := repeat match goal with H : (?x <> ?y) |- _ => hide H end.
Ltac unhide_neqs := repeat match goal with H : kept (?x <> ?y) |- _ => unhide H end.
Ltac hide_mods := repeat match goal with H : (?x mod ?y = ?z)%Z |- _ => hide H end.
Ltac unhide_mods := repeat match goal with H : kept (?x mod ?y = ?z)%Z |- _ => unhide H end.

Ltac unhide_djf := try match goal with H : kept (_ \/ _) |- _ => unhide H; unhide_djf end.

Ltac pose_seps PE PI AINV :=
  destruct (wo_pinv_seps_r _ _ _ _ _ PE PI AINV) as [D_VS D_VB D_VD D_SB D_SD D_BD D_WV D_WS D_WB D_WD D_AW D_ABW D_IW D_IBW
              D_AV D_AS D_AB D_AD D_ABV D_ABS D_ABB D_ABD D_IV D_IS D_IB D_ID D_IBV D_IBS D_IBB D_IBD D_AA D_II D_AI];
  cbn zeta in D_VS, D_VB, D_VD, D_SB, D_SD, D_BD, D_WV, D_WS, D_WB, D_WD, D_AW, D_ABW, D_IW, D_IBW,
              D_AV, D_AS, D_AB, D_AD, D_ABV, D_ABS, D_ABB, D_ABD,
              D_IV, D_IS, D_IB, D_ID, D_IBV, D_IBS, D_IBB, D_IBD, D_AA, D_II, D_AI;
  cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi] in D_VS, D_VB, D_VD, D_SB, D_SD, D_BD, D_WV, D_WS, D_WB, D_WD, D_AW, D_ABW, D_IW, D_IBW,
              D_AV, D_AS, D_AB, D_AD, D_ABV, D_ABS, D_ABB, D_ABD,
              D_IV, D_IS, D_IB, D_ID, D_IBV, D_IBS, D_IBB, D_IBD, D_AA, D_II, D_AI.

(* [comment removed for export] *)
Ltac world_open PE PI AINV :=
  pose_seps PE PI AINV;
  pose proof (ocosts_nonneg _ _ _ _ PI) as [OA0 OI0];
  destruct PI as [VEPO__ BASE FLG VSBF STUP STATE CNT VERP PLE B01 TAGI DELIM ESIC UNTL MTCH DOST ARMED ATTR ATTRST
                  MATTR LOOKA LOOKM VSBO ROOM OUT APART WAL AVSB VA VI DATA HENV STK FRAME__ MI SS LB NL TC FRS KEEP NEW CF CR0 WL SC PR0 PPH PC];   (* [comment removed for export] *)
  destruct VEPO__ as (LVEP & VEPC & TAG & PADS); destruct FRAME__ as (j0 & j8 & FR);   (* [comment removed for export] *)
  unfold walen, wilen, wpot in WL, SC;
  lazymatch type of DATA with data_obj _ _ _ _ _ =>
    pose proof DATA as (LDATA & DBY & DLEN);
    lazymatch type of LVEP with a_live _ ?vep__ = _ =>
    destruct (wo_live_geom_r _ _ _ _ _ AINV LVEP) as [_ VEP16 VEPlo VEPhi VEPimg _ _];
    destruct (wo_live_geom_r _ _ _ _ _ AINV LDATA) as [_ _ Dlo Dhi Dimg _ _];
    lazymatch type of PE with penv_ok ?E =>
      pose proof (as_live_disjoint LPA _ _ _ _ _ _ _ AINV LVEP LDATA (wo_penv_ne_vd _ PE)) as DJ_VD end;
    try pose proof PE as PE0;
    destruct (wo_penv_ok_r _ PE) as [HG FL NN CEIL LOP SPH SP16 NE1 NE2 NE3 NE4 NE5 NE6 BUDL BUDN LIBF LB0 LS0];
    pose proof HG as (G1 & G2 & G3); unfold HFSIZE in G3;
    pose proof alloc_ceiling_num as ACV;
    rewrite PARSE_STACK_val in LOP;
    unfold NMAX, pe_N in NN; unfold pe_e, pe_N in PLE;
    lazymatch type of PE with penv_ok ?E =>
      assert (EE : pe_e E = pe_DATA E + Z.of_nat (length (pe_inp E))) by reflexivity;
      assert (EFP : pe_fp E = pe_sp E - 320) by reflexivity end;
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB; rewrite (vep_cells_size _ _ _ TAG PADS) in VEPB;
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB; rewrite pframe_size in FRB;
    (* [comment removed for export] *)
    change (Z.of_nat 312) with 312 in VEPB; change (Z.of_nat 320) with 320 in FRB;
    unfold vep_cells in VEPC; unfold pframe in FR; cbv zeta in FR; rewrite STATE in VEPC;
    cbn [vi_st VIA stA] in VEPC;
    (first [ pose proof (B01) as dR_31; dand8 dR_31 as B_lm B_ef B_et B_em B_ca B_rm B_ie B_ic | pose proof B01 as (B_lm & B_ef & B_et & B_em & B_ca & B_rm & B_ie & B_ic) ]);
    (first [ pose proof ((vsb_apart3 _ _ _ _ _ APART)) as dR_32; dand6 dR_32 as AP1 AP2 AP3 AP4 AP5 AP6 | pose proof (vsb_apart3 _ _ _ _ _ APART) as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6) ]);
    pose proof (proj1 (proj2 (proj2 VSBO))) as LVS; pose proof (proj1 (proj2 (proj2 (proj2 VSBO)))) as LVB;
    (* [comment removed for export] *)
    pose proof (proj1 HENV) as HFR;
    let ageh := fresh "ageh" in let HFh := fresh "HFh" in
    destruct (proj1 HENV) as [ageh HFh];
    pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINV HFh LVEP) as DJfV;
    pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINV HFh LDATA) as DJfD;
    pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINV HFh LVS) as DJfS;
    pose proof (as_frame_blk_disjoint LPA _ _ _ _ HCLASS ageh _ _ AINV HFh LVB) as DJfB;
    change (fsize HCLASS) with 8192 in DJfV, DJfD, DJfS, DJfB; hide DJfV; hide DJfD; hide DJfS; hide DJfB;
    unfold in_tag_cluster, attr_states, avsb_states in ARMED, ATTRST, AVSB, ATTR; unfold va_world in VA; unfold vi_world in VI;
    try match goal with ST : x_st _ = _ |- _ => rewrite ST in ARMED, ATTRST, AVSB, ATTR, DELIM, UNTL, MTCH, MATTR, LOOKA, LOOKM, OUT end;
    cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi] in ARMED, ATTRST, AVSB, ATTR, DELIM, UNTL, MTCH, MATTR, LOOKA, LOOKM, OUT;
    cbn beta iota in ARMED, ATTRST, AVSB, ATTR, OUT; destruct DELIM as [DELIM1 DELIM2];
    (* [comment removed for export] *)
    hide DOST; hide ESIC; hide ATTR;
    (* [comment removed for export] *)
    unfold kHighMemBeg in VEPlo, Dlo; all_app_facts;
    let SHVB := fresh "SHVB" in
    pose proof (sh_bound vep__ 312 ltac:(lia) ltac:(lia) ltac:(exact VEPhi)) as SHVB;   (* [comment removed for export] *)
    rewrite SHMAX_val in SHVB; change ((312 + 7) / 8) with 39 in SHVB;
    pose proof (as_live_shadow LPA _ _ _ _ 312 AINV LVEP) as SHV0; fold_cl_segs; fold_aview;
    change (shpat 312) with (repeat (Z_to_bv 8 0) 39) in SHV0;
    remember (repeat (Z_to_bv 8 0) 39) as zsV eqn:EzsV in SHV0;
    assert (LZV : Z.of_nat (length zsV) = 39) by (rewrite EzsV; reflexivity)
  end end.

(* [comment removed for export] *)
Ltac handler_prologue PE PI AINV ST :=
  world_open PE PI AINV;
  unfold disp_ms, loop_ms; rewrite ST;
  cbn [disp_pc disp_a1 disp_a2 disp_a6 disp_s1 disp_s6 disp_s10 disp_pos oreg S9 T0 vi_st VIA stA];
  match goal with EFP : pe_fp _ = _ |- _ => rewrite EFP in * end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac psimp :=
  lazymatch goal with |- ?G =>
    let G := eval unfold va_world in G in let G := eval unfold vi_world in G in let G := eval unfold in_tag_cluster in G in
    let G := eval unfold attr_states in G in let G := eval unfold avsb_states in G in let G := eval unfold x_vio in G in
    let G := eval unfold walen in G in let G := eval unfold wilen in G in let G := eval unfold wpot in G in
    let G := eval cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb in_tag_cluster attr_states avsb_states oabuf oibuf option_map] in G in
    change_no_check G
  end.
Ltac psimp_in H := try unfold va_world in H; try unfold vi_world in H; try unfold in_tag_cluster in H; try unfold attr_states in H; try unfold avsb_states in H; try unfold x_vio in H;
  try unfold walen in H; try unfold wilen in H; try unfold wpot in H;
  cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb in_tag_cluster attr_states avsb_states oabuf oibuf option_map] in H.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_parse_junk :=
  repeat match goal with
  | H : bool01 _ |- _ => clear H
  | H : bool01 _ /\ _ |- _ => clear H
  | H : vep_cnt _ _ |- _ => clear H
  | H : _ <= 3 * _ + 2 * _ |- _ => clear H
  | H : context [vct_namestart _] |- _ => clear H
  | H : context [Fdostuff] |- _ => clear H
  | H : context [Fattr_delim] |- _ => clear H
  | H : context [Fesicmt] |- _ => clear H
  | H : context [Funtil] |- _ => clear H
  | H : context [Fmatch] |- _ => clear H
  | H : context [Fmatch_hit] |- _ => clear H
  | H : context [Fstartup] |- _ => clear H
  | H : context [Fflags] |- _ => clear H
  | H : context [Ftag_i] |- _ => clear H
  | H : x_v _ Fattr = _ \/ _ |- _ => clear H
  end.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module CPJ2.
Import Ltac2.
Ltac2 is_junk (t : constr) : bool :=
  lazy_match! t with
  | bool01 _ => true
  | bool01 _ /\ _ => true
  | vep_cnt _ _ => true
  | _ <= 3 * _ + 2 * _ => true
  | context [vct_namestart _] => true
  | context [Fdostuff] => true
  | context [Fattr_delim] => true
  | context [Fesicmt] => true
  | context [Funtil] => true
  | context [Fmatch] => true
  | context [Fmatch_hit] => true
  | context [Fstartup] => true
  | context [Fflags] => true
  | context [Ftag_i] => true
  | x_v _ Fattr = _ \/ _ => true
  | _ => false
  end.
Ltac2 clear_parse_junk_fast () : unit :=
  let ids := List.map_filter (fun h => let (id, _, ty) := h in if is_junk ty then Some id else None) (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ =>
      (* [comment removed for export] *)
      Control.once (fun () =>
        Control.plus (fun () => Std.clear ids)
                     (fun _ => List.iter (fun id => Control.once (fun () => Control.plus (fun () => Std.clear [id]) (fun _ => ()))) (List.rev ids)))
  end.
End CPJ2.
Ltac clear_parse_junk ::= ltac2:(Ltac2.Control.enter CPJ2.clear_parse_junk_fast).
Ltac unhide_parse_junk :=
  repeat match goal with
  | H : kept (_ = 0 \/ _) |- _ => unhide H
  | H : kept (_ = 0 /\ _ \/ _) |- _ => unhide H
  end.
Ltac wz_not_in :=
  cbn; let X := fresh "X" in intro X;
  repeat (destruct X as [X|X]); first [exact X | congruence].
Ltac ivl_base lo := lazymatch lo with | ?b + _ => ivl_base b | ?b - _ => ivl_base b | ?b => b end.
Ltac wzone_tac :=
  cbn [wzone];
  repeat lazymatch goal with
  | |- (_ \/ _) /\ _ =>
      split;
      [ lazymatch goal with
        | |- _ \/ (_ <= ?lo /\ _) \/ _ =>
            lazymatch lo with
            | context [pe_sp] => right; left; unfold pe_fp, PARSE_FRAME; lia
            | context [pe_fp] => right; left; unfold pe_fp, PARSE_FRAME; lia
            | context [bv_unsigned] => right; left; unfold pe_fp, PARSE_FRAME; lia
            | context [h_vsc] => right; right; split; reflexivity
            | _ => let b := ivl_base lo in
                   match goal with
                   | H : a_live _ b = Some ?n |- _ =>
                       left; exists b, n; split; [exact H|]; split; [ wz_not_in | lia ]
                   end
            end
        end
      | ]
  | |- True => exact I
  end.

(* [comment removed for export] *)
Ltac w_in_zone_tac :=
  repeat lazymatch goal with
  | |- w_in_zone _ _ [] => apply w_in_zone_nil
  | |- w_in_zone _ _ ((?lo, _) :: _) =>
      lazymatch lo with
      | context [pe_sp] => apply w_in_zone_win; [clear_parse_junk; rewrite ?PARSE_STACK_val; unfold pe_fp, PARSE_FRAME in *; lia | clear_parse_junk; rewrite ?PARSE_STACK_val; unfold pe_fp, PARSE_FRAME in *; lia |]
      | context [pe_fp] => apply w_in_zone_win; [clear_parse_junk; rewrite ?PARSE_STACK_val; unfold pe_fp, PARSE_FRAME in *; lia | clear_parse_junk; rewrite ?PARSE_STACK_val; unfold pe_fp, PARSE_FRAME in *; lia |]
      | context [bv_unsigned] => apply w_in_zone_win; [clear_parse_junk; rewrite ?PARSE_STACK_val; unfold pe_fp, PARSE_FRAME in *; lia | clear_parse_junk; rewrite ?PARSE_STACK_val; unfold pe_fp, PARSE_FRAME in *; lia |]
      | _ => apply w_in_zone_zone; [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold pzone | ]
      end
  end.

(* [comment removed for export] *)
Tactic Notation "vchk_at" constr(SRC) constr(E) constr(k) integer(n) :=
  let T := fresh "SHT" in pose proof SRC as T; rewrite E in T; shadow_addr T k; clear T; zstep; lit0; do n zstep; chk_branch.

(* [comment removed for export] *)
Ltac cf_stores CF MU PE0 STK FR :=
  eapply cframe_step_stores;
  [ exact CF | exact MU | w_in_zone_tac
  | eapply parse_window_mapped; [exact PE0| exact STK| unfold pframe; cbv zeta; exact FR]
  | let a := fresh "a" in let X := fresh "X" in intros a X; eapply parse_new_same; [| | exact X]; reflexivity ].

(* [comment removed for export] *)
Ltac pc_unfold := unfold pcharge, pbank, ptag, pbva, pbvi, phead, in_incl_tag, wppot, walen, wilen in *.
Ltac pc_keep_var a b c G :=
  first [ is_var a; lazymatch G with context [a] => idtac end
        | is_var b; lazymatch G with context [b] => idtac end
        | is_var c; lazymatch G with context [c] => idtac end ].
Ltac pc_keep :=
  repeat match goal with
  | H : context [x_p _] |- _ => revert H
  | H : context [x_st _] |- _ => revert H
  | H : context [Fattr] |- _ => revert H
  | H : context [Fattr_vsb] |- _ => revert H
  | H : context [Fmatch] |- _ => revert H
  | H : context [Fmatch_hit] |- _ => revert H
  | H : context [x_va _] |- _ => revert H
  | H : context [x_vi _] |- _ => revert H
  | H : context [vsb_ppot _] |- _ => revert H
  | H : context [vsb_phi _] |- _ => revert H
  | H : context [a_primcred _] |- _ => revert H
  | H : context [pe_N _] |- _ => revert H
  | H : context [ptag _] |- _ => revert H
  (* [comment removed for export] *)
  | H : (?a <= ?b)%Z |- ?G => pc_keep_var a b b G; revert H
  | H : (?a < ?b)%Z |- ?G => pc_keep_var a b b G; revert H
  | H : (?a <= ?b <= ?c)%Z |- ?G => pc_keep_var a b c G; revert H
  | H : (?a <= ?b < ?c)%Z |- ?G => pc_keep_var a b c G; revert H
  | H : (?a < ?b <= ?c)%Z |- ?G => pc_keep_var a b c G; revert H
  | H : (?a < ?b < ?c)%Z |- ?G => pc_keep_var a b c G; revert H
  | H : @eq Z ?a ?b |- ?G => pc_keep_var a b b G; revert H
  end.
(* [comment removed for export] *)
Ltac pc_zeta := repeat match goal with z := _ |- _ => subst z end.
(* [comment removed for export] *)
Ltac pc_lia := repeat match goal with H : _ /\ _ |- _ => destruct H end; Zify.zify; xlia zchecker.
Ltac pc_lits := cbn [negb Z.eqb Pos.eqb x_p x_st x_v x_tag x_q x_vv x_va x_vi fupd vf_beq vf_index N.eqb vi_tbl_attr_include vi_tbl_esi vi_tbl_bom vi_tbl_starttag VIA stA vi_st] in *;
  rewrite ?vsb_ppot_fresh, ?vsb_ppot_set_flags, ?vsb_ppot_set_len in *;
  unfold vsb_ppot in *; cbn [vb_len vb_size vb_buf vsb_fresh vsb_set_flags vsb_set_len] in *; try change (PVB 16) with 32 in *;
  unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include in *.
Ltac pc_facts :=
  repeat match goal with H : x_st _ = _ |- _ => rewrite H in *; clear H end;
  repeat match goal with H : x_va _ = _ |- _ => rewrite H in *; clear H end;
  repeat match goal with H : x_vi _ = _ |- _ => rewrite H in *; clear H end;
  repeat match goal with H : _ = x_va _ |- _ => rewrite <- H in *; clear H end;
  repeat match goal with H : _ = x_vi _ |- _ => rewrite <- H in *; clear H end;
  repeat match goal with H : x_v _ Fmatch = _ |- _ => rewrite H in *; clear H end;
  repeat match goal with H : x_v _ Fattr = _ |- _ => rewrite H in *; clear H end;
  repeat match goal with H : x_v _ Fmatch_hit = _ |- _ => rewrite H in *; clear H end.
Ltac pc_cases :=
  repeat match goal with
  | |- context [match x_va ?x with _ => _ end] => destruct (x_va x)
  | |- context [match x_vi ?x with _ => _ end] => destruct (x_vi x)
  | |- context [match x_st ?x with _ => _ end] => destruct (x_st x)
  | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
  end.
(* [comment removed for export] *)
Ltac pc_attr :=
  try match goal with H : x_v ?x Fattr = 0 \/ (x_v ?x Fattr = _ /\ _ /\ _) |- _ =>
    let Hd := fresh in let Hs := fresh in
    destruct H as [H|(H & Hd & Hs)];
    [ rewrite ?H in *
    | rewrite ?H in *; first [ exfalso; clear - Hs; repeat (destruct Hs as [Hs|Hs]); first [exact Hs | discriminate Hs] | clear Hs ] ]
  end.
(* [comment removed for export] *)
Ltac pc_attrst :=
  try match goal with H : True -> _ \/ x_va ?x <> None -> x_v ?x Fattr = _ /\ _ |- _ =>
    first [ let A := fresh in destruct (H I ltac:(left; reflexivity)) as [A _]; rewrite ?A in *
          | match goal with E : x_va x = Some _ |- _ => let A := fresh in destruct (H I ltac:(right; rewrite E; discriminate)) as [A _]; rewrite ?A in * end
          | match goal with E : Some _ = x_va x |- _ => let A := fresh in destruct (H I ltac:(right; rewrite <- E; discriminate)) as [A _]; rewrite ?A in * end
          | (* [comment removed for export] *)
            let E := fresh in let yv := fresh "yv" in
            destruct (x_va x) as [yv|] eqn:E;
            [ let A := fresh in destruct (H I ltac:(right; congruence)) as [A _]; rewrite ?A in * | ] ]   (* [comment removed for export] *)
  end.
Ltac pc_arith :=
  unhide_parse_junk; unhide_neqs; pc_keep; clear; intros; pc_zeta; pc_unfold; psimp;
  repeat match goal with H : _ |- _ => progress (psimp_in H) end;
  unfold vsb_phi in *; pc_lits; pc_attrst; pc_facts; pc_attr; pc_lits;
  first [ pc_lia (* [comment removed for export] *) | pc_cases; pc_lits; pc_lia ].
(* [comment removed for export] *)
Ltac phi_close :=
  repeat match goal with E : x_va ?x = _, H : match x_va ?x with Some _ => vsb_phi _ | None => True end /\ _ |- _ => rewrite E in H end;
  repeat match goal with E : x_vi ?x = _, H : _ /\ match x_vi ?x with Some _ => vsb_phi _ | None => True end |- _ => rewrite E in H end;
  repeat match goal with E : _ = x_va ?x, H : match x_va ?x with Some _ => vsb_phi _ | None => True end /\ _ |- _ => rewrite <- E in H end;
  repeat match goal with E : _ = x_vi ?x, H : _ /\ match x_vi ?x with Some _ => vsb_phi _ | None => True end |- _ => rewrite <- E in H end;
  split;
  first [ exact I | apply vsb_phi_fresh | assumption
        | match goal with H : _ /\ _ |- _ => first [exact (proj1 H) | exact (proj2 H)] end
        | match goal with H : _ /\ _ |- vsb_phi _ => first [ refine (vsb_phi_eq _ _ _ _ (proj1 H)); reflexivity | refine (vsb_phi_eq _ _ _ _ (proj2 H)); reflexivity ] end
        | match goal with H : vsb_phi _ |- vsb_phi _ => first [ exact H | refine (vsb_phi_eq _ _ _ _ H); reflexivity ] end ].
Ltac pc_auto :=
  lazymatch goal with |- _ - pcharge ?E _ - _ <= a_primcred ?A1 <= _ =>
    match goal with
    | PC : _ - pcharge E _ - _ <= a_primcred A1 <= _ |- _ => eapply (pc_mono _ _ _ _ _ _ PC); pc_arith
    | EQ : a_primcred A1 = a_primcred ?A, PC : _ - pcharge E _ - _ <= a_primcred ?A <= _ |- _ => eapply (pc_eq _ _ _ _ _ _ _ PC EQ); pc_arith
    | D : _ - _ <= a_primcred A1 <= a_primcred ?A, PC : _ - pcharge E _ - _ <= a_primcred ?A <= _ |- _ => eapply (pc_xfer _ _ _ _ _ _ _ _ PC D); pc_arith
    | EQ : a_primcred A1 = a_primcred ?A - _, PC : _ - pcharge E _ - _ <= a_primcred ?A <= _ |- _ => eapply (pc_eqd _ _ _ _ _ _ _ _ PC EQ); [clear; lia| pc_arith]
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac pinv_concl_neg G := lazymatch G with (_ <> _) => idtac | False => idtac | (~ _) => idtac | (_ -> ?B) => pinv_concl_neg B end.
Ltac pinv_triv :=
  first
    [ assumption
    | reflexivity
    | lazymatch goal with |- ?G => pinv_concl_neg G end; discriminate
    | match goal with |- _ -> _ => let X := fresh "X" in intros X; discriminate X end
    | match goal with |- _ -> _ -> _ => let X := fresh "X" in let Y := fresh "Y" in intros X Y; exfalso; revert Y; cbv; congruence end
    | match goal with |- True => exact I end
    | match goal with |- ~ False => let X := fresh "X" in intros X; exact X end
    | match goal with |- False -> _ => let X := fresh "X" in intros X; destruct X end ].

(* [comment removed for export] *)
Ltac in_list :=
  cbn; unfold oabuf, oibuf;
  try match goal with E : x_va _ = Some _ |- _ => rewrite E end;
  try match goal with E : x_vi _ = Some _ |- _ => rewrite E end;
  try match goal with E : Some _ = x_va _ |- _ => rewrite <- E end;
  try match goal with E : Some _ = x_vi _ |- _ => rewrite <- E end;
  cbn; repeat (first [ left; reflexivity | right ]).

(* [comment removed for export] *)
Ltac pinv_close PE0 AINV HFR MU WM WZ :=
  unhide_parse_junk;
  try pinv_triv;
  try lazymatch goal with
  (* [comment removed for export] *)
  | |- PARSE_CRED _ <= a_seccred _ => assumption
  (* [comment removed for export] *)
  | |- PARSE_PRIM _ <= a_primcred _ => assumption
  | |- match ?a with Some _ => vsb_phi _ | None => True end /\ match ?b with Some _ => vsb_phi _ | None => True end => first [assumption | phi_close]
  | |- vsb_phi _ /\ match ?b with Some _ => vsb_phi _ | None => True end => first [assumption | phi_close]
  | |- match ?a with Some _ => vsb_phi _ | None => True end /\ vsb_phi _ => first [assumption | phi_close]
  | |- vsb_phi _ /\ vsb_phi _ => first [assumption | phi_close]
  | |- True /\ match ?b with Some _ => vsb_phi _ | None => True end => first [assumption | phi_close]
  | |- match ?a with Some _ => vsb_phi _ | None => True end /\ True => first [assumption | phi_close]
  | |- True /\ vsb_phi _ => first [assumption | phi_close]
  | |- vsb_phi _ /\ True => first [assumption | phi_close]
  | |- True /\ True => split; exact I
  | |- _ - pcharge _ _ - _ <= a_primcred _ <= _ => first [assumption | pc_auto]
  | |- 0 <= _ /\ 0 <= _ /\ _ <= _ - pe_DATA _ => first [assumption | lia]
  | |- _ - _ <= a_seccred ?A <= _ =>
      first [ assumption
            | match goal with H : _ - _ <= a_seccred A <= _ |- _ =>
                first [ eapply (sc_mono _ _ _ _ _ _ H); lia | eapply (sc_xfer _ _ _ _ _ _ _ _ H); lia ] end ]
  | |- _ Fstate = vi_st VIA _ => first [reflexivity | match goal with S : _ Fstate = vi_st VIA ?s, E : ?s = _ |- _ => rewrite S, E; reflexivity end]
  | |- vep_obj _ _ _ _ _ _ _ => split; [assumption|]; split; [unfold vep_cells; psimp;
                                  try match goal with S : _ Fstate = vi_st VIA _ |- _ => rewrite S end; cbn [vi_st VIA stA]; assumption|]; split; assumption
  | |- bool01 _ /\ _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | left; reflexivity | right; reflexivity]
  | |- (_ -> _ = 0) /\ (_ -> _) =>
      split; [ intros _; first [assumption | reflexivity | match goal with H : _ -> ?v = 0 |- ?v = 0 => apply H; discriminate end]
             | let X := fresh "X" in intros X; first [discriminate X | match goal with H : _ -> ?c |- ?c => apply H; reflexivity end] ]
  | |- _ = _ -> _ \/ _ => intros _; first [assumption | left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; reflexivity
                                 | match goal with H : _ -> ?c |- ?c => apply H; reflexivity end]
  | |- _ = 0 \/ (_ = vi_tbl_attr_include VIA /\ _ = vi_do_include VIA /\ _) =>
      match goal with
      | H : _ = 0 \/ (_ = vi_tbl_attr_include VIA /\ _ = vi_do_include VIA /\ ?R) |- _ =>
          let A0 := fresh in let A1 := fresh in let A2 := fresh in let A3 := fresh in
          destruct H as [A0|(A1 & A2 & A3)];
          [ left; exact A0
          | first [ right; split; [exact A1|]; split; [exact A2|];
                    first [ left; exact I | left; reflexivity | left; assumption
                          | right; left; reflexivity | right; right; left; reflexivity | right; right; right; reflexivity ]
                  | exfalso; revert A3; clear; intros A3;
                    repeat (destruct A3 as [A3|A3]); first [exact A3 | discriminate A3 | revert A3; cbv; congruence] ] ]
      end
  | |- vsb_obj _ _ _ _ _ _ => eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV HFR MU WM WZ); [in_list| in_list| assumption]
  | |- data_obj _ _ _ _ _ => first [ split; [assumption| split; assumption] | eapply (data_obj_stores _ _ _ _ _ _ _ PE0 AINV HFR MU WM WZ); [in_list| assumption] ]
  | |- henv_ok _ _ _ _ _ => first [assumption | lazymatch type of MU with munch ?W _ _ => lazymatch W with context [h_vsc] => fail | _ => idtac end end; eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV HFR MU WM WZ); [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; clear_parse_junk; cbn [outside]; unhide_djf; unhide_app_img; unfold h_vsc, pe_fp, PARSE_FRAME in *; lia| assumption] ]   (* [comment removed for export] *)
  | |- stack_shadow _ _ _ _ _ _ => first [assumption | eapply (stack_shadow_stores _ _ _ _ _ _ _ PE0 AINV HFR MU WM WZ); assumption ]
  | |- exists j0 j8, rw_cells _ _ _ (pframe _ j0 j8) => eexists _, _; unfold pframe; cbv zeta; eassumption
  | |- _ <= 3 * _ + 2 * _ => psimp;
        match goal with H : _ <= 3 * _ + 2 * _ |- _ => revert H; clear; intros; cbv [oacost oicost x_va x_vi] in *; lia end
  | |- match ?o with Some _ => _ | None => _ end =>
      match goal with
      | H : match o with Some _ => _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ | None => _ end |- _ =>
          (* [comment removed for export] *)
          destruct o eqn:?; [| exact H];
          let H1 := fresh in let H2 := fresh in let H3 := fresh in
          (first [ dand3 H as H1 H2 H3 | destruct H as (H1 & H2 & H3) ]);
          refine (conj H1 (conj _ H3));
          eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV HFR MU WM WZ); [in_list| in_list| exact H2]
      | H : match o with Some _ => _ /\ _ /\ _ /\ _ /\ _ | None => _ end |- _ =>
          (* [comment removed for export] *)
          destruct o eqn:?; [| exact H];
          let H1 := fresh in let H2 := fresh in let H3 := fresh in
          (first [ dand3 H as H1 H2 H3 | destruct H as (H1 & H2 & H3) ]);
          refine (conj H1 (conj _ H3));
          eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV HFR MU WM WZ); [in_list| in_list| exact H2]
      end
  | |- _ => idtac
  end.
End A_PKit.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.

Module A_PCall.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma frames_same_fs : forall A A',
    frames_same A A' -> forall ff k age, a_frame A ff = Some (k, age) -> exists age', a_frame A' ff = Some (k, age').
  Proof. intros A A' FS ff k age HF. exists age. rewrite (FS ff). exact HF. Qed.

  Lemma world_keep : forall E x A A' m md v' sp' win N,
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md ->
    cframe LPA (owned A) (owned A') sp' win nowhere N (aview A m) v' ->
    alloc_ceiling <= sp' - win -> 0 <= win -> sp' <= pe_fp E ->
    (forall p k, a_live A p = Some k -> a_live A' p = Some k) ->
    (forall ff k age, a_frame A ff = Some (k, age) -> exists age', a_frame A' ff = Some (k, age')) ->
       vep_obj LPA A' v' (pe_VEP E) (x_v x) (x_tag x) (x_q x)
    /\ vsb_obj LPA A' v' (pe_S E) (x_vv x) false
    /\ va_world E x A' v' /\ vi_world E x A' v'
    /\ data_obj LPA A' v' (pe_DATA E) (pe_inp E)
    /\ henv_ok LPA VIA (pe_H E) A' v'
    /\ (exists j0 j8, rw_cells rsegs v' (pe_fp E) (pframe E j0 j8))
    /\ stack_shadow LPA v' (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64)
    /\ a_live A' (pe_wa E) = Some 40.
  Proof.
    intros E x A A' m md v' sp' win N PE PI AINV CFc CEIL WPOS SP LK FS.
    (first [ pose proof (PE) as dR_1; dand6 dR_1 as HG _ _ CEIL0 LOP _ | pose proof PE as (HG & _ & _ & CEIL0 & LOP & _) ]). rewrite PARSE_STACK_val in LOP.
    open_pinv PI. pose proof (proj1 HENV) as HFR.
    assert (CV : forall excl, vcover (pe_H E) A excl nowhere) by (intros excl a Ha; destruct Ha).
    assert (HC : forall excl, hcover A excl nowhere) by (intros excl a Ha; destruct Ha).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - eapply (vep_obj_call (pe_H E) A A' m md v' sp' win nowhere N [pe_VEP E] AINV CFc HFR CEIL);
        [apply CV| left; reflexivity| apply LK; exact (proj1 VEPO)| exact VEPO].
    - eapply (vsb_obj_call (pe_H E) A A' m md v' sp' win nowhere N [pe_S E; vb_buf (x_vv x)] AINV CFc HFR CEIL);
        [apply CV| left; reflexivity| right; left; reflexivity
        | apply LK; exact (proj1 (proj2 (proj2 VSBO)))| apply LK; exact (proj1 (proj2 (proj2 (proj2 VSBO))))| exact VSBO].
    - unfold va_world in *. destruct (x_va x) as [y|]; [| exact VA].
      (first [ dand3 VA as Q1 Q2 Q3 | destruct VA as (Q1 & Q2 & Q3) ]). refine (conj Q1 (conj _ Q3)).
      eapply (vsb_obj_call (pe_H E) A A' m md v' sp' win nowhere N [x_v x Fattr_vsb; vb_buf y] AINV CFc HFR CEIL);
        [apply CV| left; reflexivity| right; left; reflexivity
        | apply LK; exact (proj1 (proj2 (proj2 Q2)))| apply LK; exact (proj1 (proj2 (proj2 (proj2 Q2))))| exact Q2].
    - unfold vi_world in *. destruct (x_vi x) as [y|]; [| exact VI].
      (first [ dand3 VI as Q1 Q2 Q3 | destruct VI as (Q1 & Q2 & Q3) ]). refine (conj Q1 (conj _ Q3)).
      eapply (vsb_obj_call (pe_H E) A A' m md v' sp' win nowhere N [x_v x Finclude_src; vb_buf y] AINV CFc HFR CEIL);
        [apply CV| left; reflexivity| right; left; reflexivity
        | apply LK; exact (proj1 (proj2 (proj2 Q2)))| apply LK; exact (proj1 (proj2 (proj2 (proj2 Q2))))| exact Q2].
    - eapply (data_obj_call (pe_H E) A A' m md v' sp' win nowhere N [pe_DATA E] AINV CFc HFR CEIL);
        [apply CV| left; reflexivity| apply LK; exact (proj1 DATA)| exact DATA].
    - eapply (henv_call (pe_H E) A A' m md v' sp' win nowhere N [] AINV CFc CEIL); [apply HC| exact FS| exact HENV].
    - (first [ dex2 FRAME as j0 j8; rename FRAME into FR | dand3 FRAME as j0 j8 FR | destruct FRAME as (j0 & j8 & FR) ]). exists j0, j8.
      eapply (pframe_call E A A' m md v' sp' win nowhere N []); [exact PE| exact AINV| exact CFc| exact HFR| exact CEIL| exact WPOS| exact SP| apply CV| exact FR].
    - eapply (stack_shadow_call (pe_H E) A A' m md v' sp' win nowhere N [] AINV CFc HFR CEIL); [apply CV| rewrite PARSE_STACK_val; pose proof alloc_ceiling_num as ACV; try (generalize alloc_ceiling_val); clear - ACV CEIL0 LOP; try pose proof alloc_ceiling_val; lia| exact SS].
    - apply LK. exact WAL.
  Qed.
End S.
End A_PCall.

Module A_PH7ea.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma PH_StartTag : handler_stmt S_StartTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV. fold_cl_segs.
    zstep. (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_Match (fupd (fupd (fupd (x_v x) Fendtag 0) Fmatch TBL_starttag) Fstate (vi_st VIA S_Match))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
    - exact AINV0.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *)
      psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST.
      cbn [vi_tbl_attr_include vi_tbl_esi VIA]. unfold TBL_bom, TBL_starttag, TBL_esi, TBL_attr_include. cbn [Z.eqb Pos.eqb]. lia.
  Qed.
End S.
End A_PH7ea.

Module A_PHf78.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma PH_CDATA : handler_stmt S_CDATA.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV. fold_cl_segs.
    zstep. (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    vchk_at SHV0 EzsV 8 1. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0.
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_Until (fupd (fupd (fupd (fupd (x_v x) Funtil LIT_cdata_end) Funtil_p LIT_cdata_end) Funtil_s (vi_st VIA S_NxtTag)) Fstate (vi_st VIA S_Until)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) intros _. split; [right; reflexivity|]. split; [unfold LIT_cdata_end; cbn; lia| reflexivity].
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
    - exact AINV0.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *)
      psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHf78.

Module A_PHuqr.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma PH_ESI_Remove : handler_stmt S_ESI_Remove.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV. fold_cl_segs.
    zstep. (* [comment removed for export] *)
    vchk SHV0 EzsV 8 0. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. (* [comment removed for export] *)
    zstep. zstep. zstep. (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_InTag (fupd (fupd (x_v x) Fdostuff (vi_do_remove VIA)) Fstate (vi_st VIA S_InTag))
                    (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) right; right; left. reflexivity.
      + (* [comment removed for export] *) eapply cframe_step_stores; [exact CF| exact MU| | eapply parse_window_mapped; [exact PE0| exact STK| unfold pframe; cbv zeta; exact FR] |].
        * w_in_zone_tac. left; left. unfold blk. lia.
        * intros a X. eapply parse_new_same; [| | exact X]; reflexivity.
    - exact AINV0.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *)
      psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHuqr.

Module A_PHyoj.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require ShdFast.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_dead ::=
  exfalso;
  match goal with SOK : OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.shadow_val_ok ?b ?a ?k |- _ =>
    (let BR := fresh "SBR" in pose proof (OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.byte_range b) as BR;
     let MB := fresh "SMB" in first [ pose proof (Z.mod_pos_bound a 8 (@eq_refl comparison Lt)) as MB | idtac ]);   (* [comment removed for export] *)
    let Z0 := fresh "SZ" in let R1 := fresh "SR" in let R2 := fresh "SR" in
    destruct SOK as [Z0 | [R1 R2]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.sb_norm b a; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ShdFast.shd_mlia0
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietvxh.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Lemma PH_end_ESITag : handler_stmt S_end_ESITag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    hide_neqs.
    ago AINV. fold_cl_segs.
    zstep. (* [comment removed for export] *)
    vchk SHV0 EzsV 4 0. (* [comment removed for export] *)
    zstep. zstep. (* [comment removed for export] *)
    vrechk SHV0 EzsV (pe_VEP E + 64) 8 0.
    zstep. zstep. zstep. zstep. (* [comment removed for export] *)
    astop AINV MU WM CFP. fold_cl_segs.
    eapply (KL (PST (x_p x) S_ESITag (fupd (fupd (x_v x) Fendtag 1) Fstate (vi_st VIA S_ESITag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _).
    - apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
      + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
    - exact AINV0.
    - eapply amd_frame_sbm_r; [exact MDF | exact SBM].
    - (* [comment removed for export] *)
      psimp. intros _. split; [| discriminate]. unfold phi, rank; psimp. rewrite ST. lia.
  Qed.
End S.
End A_PHyoj.

Module A_PMark.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7 V_Vct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require Import LayoutPA AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section LiveKeep.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma live_keep : forall (A A' : AS) (b b' p k : Z),
    (forall r, r <> b -> r <> b' -> a_live A' r = a_live A r) ->
    (b' = b \/ (a_live A b' = None /\ a_live A' b = None)) ->
    a_live A p = Some k -> p <> b -> a_live A' p = Some k.
  Proof.
    intros A A' b b' p k LIVE REL Hp NB. destruct REL as [EB|[F1 F2]].
    - rewrite LIVE; [exact Hp| exact NB| rewrite EB; exact NB].
    - assert (p <> b') by (intros ->; congruence). rewrite LIVE; assumption.
  Qed.
  Lemma fresh_ne : forall (A A' : AS) (b b' p k : Z),
    (b' = b \/ (a_live A b' = None /\ a_live A' b = None)) ->
    a_live A p = Some k -> p <> b -> p <> b'.
  Proof. intros A A' b b' p k [EB|[F1 F2]] Hp NB; [congruence| intros ->; congruence]. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End LiveKeep.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mark_nf : forall f, existsb (vf_beq f) MARK_FIELDS = false -> ~ In f MARK_FIELDS.
Proof.
  intros f H IN. apply Bool.not_true_iff_false in H. apply H. apply existsb_exists. exists f. split; [exact IN| apply vf_beq_refl].
Qed.
Ltac vk_norm VK :=
  rewrite ?(VK Fflags (mark_nf Fflags eq_refl)), ?(VK Fvsb (mark_nf Fvsb eq_refl)), ?(VK Furl (mark_nf Furl eq_refl)), ?(VK Fvc (mark_nf Fvc eq_refl)), ?(VK Fdogzip (mark_nf Fdogzip eq_refl)), ?(VK Fcb (mark_nf Fcb eq_refl)), ?(VK Fcb_priv (mark_nf Fcb_priv eq_refl)), ?(VK Fstate (mark_nf Fstate eq_refl)), ?(VK Fstartup (mark_nf Fstartup eq_refl)), ?(VK Fesi_found (mark_nf Fesi_found eq_refl)), ?(VK Fendtag (mark_nf Fendtag eq_refl)), ?(VK Femptytag (mark_nf Femptytag eq_refl)), ?(VK Fcanattr (mark_nf Fcanattr eq_refl)), ?(VK Fremove (mark_nf Fremove eq_refl)), ?(VK Fhack_p (mark_nf Fhack_p eq_refl)), ?(VK Funtil (mark_nf Funtil eq_refl)), ?(VK Funtil_p (mark_nf Funtil_p eq_refl)), ?(VK Funtil_s (mark_nf Funtil_s eq_refl)), ?(VK Fin_esi_tag (mark_nf Fin_esi_tag eq_refl)), ?(VK Fesicmt (mark_nf Fesicmt eq_refl)), ?(VK Fesicmt_p (mark_nf Fesicmt_p eq_refl)), ?(VK Fattr (mark_nf Fattr eq_refl)), ?(VK Fattr_vsb (mark_nf Fattr_vsb eq_refl)), ?(VK Fattr_delim (mark_nf Fattr_delim eq_refl)), ?(VK Fmatch (mark_nf Fmatch eq_refl)), ?(VK Fmatch_hit (mark_nf Fmatch_hit eq_refl)), ?(VK Ftag_i (mark_nf Ftag_i eq_refl)), ?(VK Fdostuff (mark_nf Fdostuff eq_refl)), ?(VK Finclude_src (mark_nf Finclude_src eq_refl)), ?(VK Finclude_continue (mark_nf Finclude_continue eq_refl)), ?(VK Fnm_skip (mark_nf Fnm_skip eq_refl)), ?(VK Fnm_verbatim (mark_nf Fnm_verbatim eq_refl)), ?(VK Fnm_pending (mark_nf Fnm_pending eq_refl)).
Ltac vk_norm_in VK H :=
  rewrite ?(VK Fflags (mark_nf Fflags eq_refl)), ?(VK Fvsb (mark_nf Fvsb eq_refl)), ?(VK Furl (mark_nf Furl eq_refl)), ?(VK Fvc (mark_nf Fvc eq_refl)), ?(VK Fdogzip (mark_nf Fdogzip eq_refl)), ?(VK Fcb (mark_nf Fcb eq_refl)), ?(VK Fcb_priv (mark_nf Fcb_priv eq_refl)), ?(VK Fstate (mark_nf Fstate eq_refl)), ?(VK Fstartup (mark_nf Fstartup eq_refl)), ?(VK Fesi_found (mark_nf Fesi_found eq_refl)), ?(VK Fendtag (mark_nf Fendtag eq_refl)), ?(VK Femptytag (mark_nf Femptytag eq_refl)), ?(VK Fcanattr (mark_nf Fcanattr eq_refl)), ?(VK Fremove (mark_nf Fremove eq_refl)), ?(VK Fhack_p (mark_nf Fhack_p eq_refl)), ?(VK Funtil (mark_nf Funtil eq_refl)), ?(VK Funtil_p (mark_nf Funtil_p eq_refl)), ?(VK Funtil_s (mark_nf Funtil_s eq_refl)), ?(VK Fin_esi_tag (mark_nf Fin_esi_tag eq_refl)), ?(VK Fesicmt (mark_nf Fesicmt eq_refl)), ?(VK Fesicmt_p (mark_nf Fesicmt_p eq_refl)), ?(VK Fattr (mark_nf Fattr eq_refl)), ?(VK Fattr_vsb (mark_nf Fattr_vsb eq_refl)), ?(VK Fattr_delim (mark_nf Fattr_delim eq_refl)), ?(VK Fmatch (mark_nf Fmatch eq_refl)), ?(VK Fmatch_hit (mark_nf Fmatch_hit eq_refl)), ?(VK Ftag_i (mark_nf Ftag_i eq_refl)), ?(VK Fdostuff (mark_nf Fdostuff eq_refl)), ?(VK Finclude_src (mark_nf Finclude_src eq_refl)), ?(VK Finclude_continue (mark_nf Finclude_continue eq_refl)), ?(VK Fnm_skip (mark_nf Fnm_skip eq_refl)), ?(VK Fnm_verbatim (mark_nf Fnm_verbatim eq_refl)), ?(VK Fnm_pending (mark_nf Fnm_pending eq_refl)) in H.

Lemma MARK_STACK_val : MARK_STACK = 8800.
Proof. vm_compute. reflexivity. Qed.

Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sizes.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma pinv_sizes : forall E x A v, pinv E x A v ->
    vb_len (x_vv x) + oacost x + oicost x <= 7 * (pe_e E - pe_DATA E)
    /\ world_bytes (x_vv x) (x_va x) (x_vio x) <= 120 + 3 * 4096 + 7 * (pe_e E - pe_DATA E)
    /\ 0 <= vb_len (x_vv x) /\ 0 <= vb_size (x_vv x).
  Proof.
    intros E x A v PI. pose proof (ocosts_nonneg _ _ _ _ PI) as [OA0 OI0].
    open_pinv PI. unfold va_world in VA. unfold vi_world in VI. unfold vep_cnt in CNT.
    (first [ pose proof (VSBO) as dR_1; dand3 dR_1 as _ VIv _ | pose proof VSBO as (_ & VIv & _) ]). unfold vsb_inv in VIv.
    assert (O1 : vb_len (x_vv x) + oacost x + oicost x <= 7 * (pe_e E - pe_DATA E)).
    { revert OUT CNT VERP PLE OA0 OI0. clear. destruct (x_st x); intros; lia. }
    split; [exact O1|]. unfold world_bytes, x_vio. unfold oacost, oicost in O1.
    destruct (x_va x) as [ya|]; destruct (x_vi x) as [yi|]; cbn [option_map];
      try ((first [ pose proof (VA) as dR_2; dand4 dR_2 as _ (_ & VIa & _) SZa _ | pose proof VA as (_ & (_ & VIa & _) & SZa & _) ]); unfold vsb_inv in VIa);
      try ((first [ pose proof (VI) as dR_3; dand5 dR_3 as _ (_ & VIi & _) _ SZi _ | pose proof VI as (_ & (_ & VIi & _) & _ & SZi & _) ]); unfold vsb_inv in VIi); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pinv_seccred : forall E x A v, pinv E x A v ->
    a_seccred (pe_A0 E) - (vb_len (x_vv x) + (x_p x - pe_DATA E) + 4096) / 4096 <= a_seccred A <= a_seccred (pe_A0 E)
    /\ a_seccred (pe_A0 E) - (pe_N E / 682 + 1) <= a_seccred A /\ 15 <= a_seccred A.   (* [comment removed for export] *)
  Proof.
    intros E x A v PI. pose proof (ocosts_nonneg _ _ _ _ PI) as [OA0 OI0].
    open_pinv PI. unfold va_world in VA. unfold vi_world in VI. unfold vep_cnt in CNT.
    (first [ pose proof (VSBO) as dR_4; dand3 dR_4 as _ VIv _ | pose proof VSBO as (_ & VIv & _) ]). unfold vsb_inv in VIv.
    unfold oacost, oicost in OUT. unfold pe_e, pe_N, PARSE_CRED in *.
    assert (PV : vsb_pot (x_vv x) <= (vb_len (x_vv x) + 4096) / 4096).
    { eapply Z.le_trans; [apply vsb_pot_le; lia| apply Z.div_le_mono; lia]. }
    assert (PA : match x_va x with Some y => vsb_pot y | None => 0 end <= match x_va x with Some y => vb_len y | None => 0 end / 4096
                 /\ 0 <= match x_va x with Some y => vb_len y | None => 0 end).
    { destruct (x_va x) as [ya|]; [| cbn; lia]. (first [ dand5 VA as _ AO ASZ ALEN _ | destruct VA as (_ & AO & ASZ & ALEN & _) ]). (first [ pose proof (AO) as dR_6; dand3 dR_6 as _ VIa _ | pose proof AO as (_ & VIa & _) ]). unfold vsb_inv in VIa.
      split; [apply vsb_pot_len; lia| lia]. }
    assert (PIi : match x_vi x with Some y => vsb_pot y | None => 0 end <= match x_vi x with Some y => vb_len y | None => 0 end / 4096
                 /\ 0 <= match x_vi x with Some y => vb_len y | None => 0 end).
    { destruct (x_vi x) as [yi|]; [| cbn; lia]. (first [ dand6 VI as _ IO _ ISZ ILEN _ | destruct VI as (_ & IO & _ & ISZ & ILEN & _) ]). (first [ pose proof (IO) as dR_8; dand3 dR_8 as _ VIi _ | pose proof IO as (_ & VIi & _) ]). unfold vsb_inv in VIi.
      split; [apply vsb_pot_len; lia| lia]. }
    destruct PA as [PA A0']. destruct PIi as [PIi I0'].
    set (la := match x_va x with Some y => vb_len y | None => 0 end) in *.
    set (li := match x_vi x with Some y => vb_len y | None => 0 end) in *.
    set (sl := x_p x - pe_DATA E - la - li) in *.
    assert (SUM : (vb_len (x_vv x) + 4096) / 4096 + la / 4096 + li / 4096 + sl / 4096 <= (vb_len (x_vv x) + (x_p x - pe_DATA E) + 4096) / 4096).
    { pose proof (div4096_add (vb_len (x_vv x) + 4096) la ltac:(lia) A0') as S1.
      pose proof (div4096_add (vb_len (x_vv x) + 4096 + la) li ltac:(lia) I0') as S2.
      pose proof (div4096_add (vb_len (x_vv x) + 4096 + la + li) sl ltac:(lia) ltac:(subst sl; lia)) as S3.
      replace (vb_len (x_vv x) + 4096 + la + li + sl) with (vb_len (x_vv x) + (x_p x - pe_DATA E) + 4096) in S3 by (subst sl; lia). lia. }
    assert (TOT : (vb_len (x_vv x) + (x_p x - pe_DATA E) + 4096) / 4096 <= Z.of_nat (length (pe_inp E)) / 682 + 1).
    { assert (B7 : vb_len (x_vv x) + (x_p x - pe_DATA E) <= 6 * Z.of_nat (length (pe_inp E))).
      { subst la li. destruct (x_st x), (x_va x), (x_vi x); lia. }
      clear - B7 VIv VERP; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia. }
    try (generalize alloc_ceiling_val); clear - SC PV PA PIi SUM TOT CR0; try pose proof alloc_ceiling_val. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma pinv_primcred : forall E x A v, pinv E x A v ->
    a_primcred (pe_A0 E) - (12 * pe_N E + (vsb_ppot (x_vv x) - 96)) <= a_primcred A <= a_primcred (pe_A0 E)
    /\ PRIM_ROOM + (PPOT_CAP - vsb_ppot (x_vv x)) <= a_primcred A /\ PRIM_ROOM <= a_primcred A.
  Proof.
    intros E x A v PI. open_pinv PI. unfold va_world in VA. unfold vi_world in VI. unfold pe_e, pe_N, PARSE_PRIM in *.
    pose proof (vsb_ppot_range (x_vv x)) as RV. destruct PPH as [PHa PHi].
    assert (KEY : pcharge E x <= vsb_ppot (x_vv x) - 96 + 12 * (x_p x - pe_DATA E)).
    { unfold pcharge, pbank, ptag, pbva, pbvi, phead, in_incl_tag, wppot, walen, wilen. unfold avsb_states, attr_states in AVSB, ATTRST.
      destruct (x_vi x) as [yi|]; [ (first [ dand5 VI as _ _ _ _ ILEN | destruct VI as (_ & _ & _ & _ & ILEN & _) ]); unfold vsb_phi in PHi |];
      (destruct (x_va x) as [ya|];
       [ (first [ dand4 VA as ANZ _ _ ALEN | destruct VA as (ANZ & _ & _ & ALEN & _) ]); unfold vsb_phi in PHa; specialize (AVSB ANZ);
         destruct (x_st x); try (exfalso; exact AVSB);
         [ (* [comment removed for export] *) idtac
         | destruct (ATTRST I ltac:(right; discriminate)) as [EAT _]; rewrite EAT
         | destruct (ATTRST I ltac:(right; discriminate)) as [EAT _]; rewrite EAT ];
         cbn [negb Z.eqb Pos.eqb vi_tbl_attr_include VIA TBL_attr_include];
         repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b) end; cbn; lia
       | destruct (x_st x); cbn [negb]; repeat match goal with |- context [if ?c then _ else _] => destruct c end; cbn; lia ]). }
    unfold PPOT_CAP in *. revert PC PR0 VERP PLE KEY RV. clear. intros. lia.
  Qed.
End Sizes.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  Definition after_mark (x : pst) (p' : Z) (v1 : vep) (vv1 : vsb_rec) : pst :=
    PST p' (x_st x) v1 (x_tag x) (x_q x) vv1 (x_va x) (x_vi x).

  Lemma mark_call : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) (ps p' mark ret : Z)
      (t0 t1 t2 s1 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> amd_frame (pe_md0 E) md ->
    x_p x <= p' -> p' <= pe_e E -> bool01 mark -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (x_st x = S_Attr \/ x_st x = S_Match -> p' = x_p x) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m2 : mem) (md1 : Model)
            (v1 : vep) (vv1 : vsb_rec) (x1 : pst),
        x1 = after_mark x p' v1 vv1 ->
        pinv E x1 A1 (aview A1 m2) -> ainv A1 m2 md1 -> amd_frame (pe_md0 E) md1 ->
        vkeep (x_v x) v1 MARK_FIELDS -> v1 Fver_p = p' -> v1 Flast_mark = mark -> v1 Fo_pending = 0 ->
        0 <= v1 Fcrc < 2^64 -> 0 <= v1 Fcrcp < 2^64 ->
        srealizes rsegs (mkCfg (call_ms E ret ps (Z_to_bv 64 ret) t0' t1' t2' s1 a0' a1' a2' a3' a4' a5' a6' a7' s6 s10 s11 t3' t4' t5' t6' m2) md1) T) ->
    srealizes rsegs (mkCfg (call_ms E vep_mark_common_entry ps (Z_to_bv 64 ret) t0 t1 t2 s1
                               (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 p') (Z_to_bv 64 mark) a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until t6. intros PE PI AINV MDF0 LEP PLE' BM RR RET SAME K.
    pose proof PI as PI0. (first [ pose proof ((pinv_sizes _ _ _ _ PI)) as dR_9; dand4 dR_9 as OUT' WBB LEN0 SZ0 | pose proof (pinv_sizes _ _ _ _ PI) as (OUT' & WBB & LEN0 & SZ0) ]). (first [ pose proof ((pinv_seccred _ _ _ _ PI)) as dR_10; dand3 dR_10 as SCB SCN SC15 | pose proof (pinv_seccred _ _ _ _ PI) as (SCB & SCN & SC15) ]). pose proof (pinv_primcred _ _ _ _ PI) as (PCB & PCD & PCR).   (* [comment removed for export] *)
    world_open PE PI AINV. unfold call_ms in K |- *. cbv zeta in K |- *. rewrite EFP in *.
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LDATA)) as dR_11; dand3 dR_11 as _ D16 _ | destruct (live_geomP LPA _ _ _ _ _ AINV LDATA) as (_ & D16 & _) ]).
    pose proof (vsb_extendsize_tight (vb_size (x_vv x) + 9)) as EXT.
    pose proof (world_nlive_nonneg (x_va x) (x_vio x)) as WNL.
    unfold PARSE_LIVE, pe_N in BUDL. unfold PARSE_NLIVE in BUDN.
    eapply (HMC (pe_VEP E) (x_v x) (x_tag x) (x_q x) (x_vv x) (pe_H E)
                p' mark (x_v x Fver_p - pe_DATA E) (pslice E (x_v x Fver_p) p') (pe_lo E));
      [ exact AINV | exact MI | reflexivity | reflexivity | reflexivity | exact BM
      | exact (pi_vep _ _ _ _ PI0)
      | exact BASE | exact HENV
      | exact B_lm | exact CNT | klia VERP | unfold NMAX; klia VERP PLE' EE NN
      | rewrite VSBF; exact VSBO | rewrite VSBF; exact NE1 | exact D_VB
      | unfold EXT_MAX; klia ROOM OUT' OA0 OI0 NN EE
      | klia LB BUDL WBB EXT NN EE SZ0 ROOM OUT' OA0 OI0
      | klia NL BUDN WNL
      | klia SC15
      | exact PCR (* [comment removed for export] *)
      | apply lib_frames_young; eapply frames_same_lib; [exact FRS| exact LIBF]
      | apply pslice_bytes; [exact DBY| klia VERP| klia VERP LEP| exact PLE']
      | apply pslice_length; [klia VERP| klia VERP LEP| exact PLE']
      | klia Dlo VERP
      | klia Dhi PLE' EE
      | exists (pe_DATA E), (Z.of_nat (length (pe_inp E))); split; [exact (as_live_shadow LPA _ _ _ _ _ AINV LDATA)|];
        split; [try (generalize alloc_ceiling_val); clear - D16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia|]; klia Dlo VERP PLE' EE Dhi LEP
      | right; exists (pe_DATA E), (Z.of_nat (length (pe_inp E))); split; [exact LDATA|];
        split; [klia NN|]; split; [klia VERP|]; split; [klia PLE' EE|]; split; [exact NE3|]; split; [rewrite VSBF; exact NE4| exact (not_eq_sym D_BD)]
      | reflexivity
      | rewrite unsigned_lit by (klia FRB); rewrite Zminus_mod, SP16; reflexivity
      | rewrite unsigned_lit by (klia FRB); exact STK
      | exact CEIL
      | rewrite unsigned_lit by (klia FRB); rewrite MARK_STACK_val; klia LOP
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1. cbv zeta.
    intros AINV1 MI1 MDF1 ST1 VO1 VK VERP1 LM1 OP1 CNT1 CRC1 CRCP1 VSO1 LEN1 SZ1 REL LIVE1 FA1 LB1 TC1 NL1 SCC1 PCC1 HENV1 DBY1 CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in ST1, CF1 by (klia FRB). rewrite VSBF in VSO1, CF1. rewrite MARK_STACK_val in CF1.
    rewrite (ret_pc_even ret RR RET).
    assert (CV1 : vcover (pe_H E) A [pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         (fun a => blk (pe_VEP E) 312 a \/ newblk (vb_buf (x_vv x)) (vb_size (x_vv x)) a \/ (pe_S E <= a < pe_S E + 40))).
    { intros a [Ha|[Ha|Ha]].
      - eapply cover_blk; [exact LVEP| wz_not_in| exact Ha].
      - eapply cover_newblk; [exact LVB| wz_not_in| exact Ha].
      - eapply cover_rng; [exact LVS| wz_not_in| exact Ha]. }
    assert (WIN : alloc_ceiling <= pe_sp E - 320 - 8800) by (klia LOP CEIL).
    assert (W0 : 0 <= 8800) by (clear; lia).
    assert (FR2 : rw_cells rsegs (aview A1 m2) (pe_sp E - 320) (pframe E j0 j8)).
    { eapply (pframe_call E A A1 m md _ _ _ _ _ _ j0 j8);
        [exact PE| exact AINV| exact CF1| exact HFR| exact WIN| exact W0| unfold pe_fp, PARSE_FRAME; klia WIN| exact CV1| unfold pframe; cbv zeta; exact FR]. }
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))).
    { eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LDATA| exact (not_eq_sym D_BD)]. }
    assert (DATA1 : data_obj LPA A1 (aview A1 m2) (pe_DATA E) (pe_inp E)).
    { eapply (data_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN); [exact CV1| in_list| exact LDATA1| exact DATA]. }
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40).
    { eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact WAL| exact D_WB]. }
    assert (LVEP1 : a_live A1 (pe_VEP E) = Some 312).
    { eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LVEP| exact D_VB]. }
    assert (NB_V : pe_VEP E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVEP| exact D_VB]).
    assert (NB_W : pe_wa E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact WAL| exact D_WB]).
    assert (NB_D : pe_DATA E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LDATA| exact (not_eq_sym D_BD)]).
    assert (SS1 : stack_shadow LPA (aview A1 m2) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64)).
    { eapply (stack_shadow_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN); [exact CV1| rewrite PARSE_STACK_val; klia LOP CEIL ACV| exact SS]. }
    (* [comment removed for export] *)
    assert (VA2 : match x_va x with None => True | Some ya =>
                    vsb_obj LPA A1 (aview A1 m2) (x_v x Fattr_vsb) ya false /\ x_v x Fattr_vsb <> vb_buf vv1 /\ vb_buf ya <> vb_buf vv1 end).
    { destruct (x_va x) as [ya|] eqn:EQa; [| exact I]. (first [ dand5 VA as ANZ AO ASZ ALEN AAP | destruct VA as (ANZ & AO & ASZ & ALEN & AAP) ]).
      (first [ pose proof (AO) as dR_13; dand5 dR_13 as _ _ LAS LAB _ | pose proof AO as (_ & _ & LAS & LAB & _) ]).
      destruct (AAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [N1 N2].
      split; [| split; [eapply (fresh_ne _ _ _ _ _ _ REL); [exact LAS| exact N1] | eapply (fresh_ne _ _ _ _ _ _ REL); [exact LAB| exact N2]]].
      eapply (vsb_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN);
        [ exact CV1 | in_list | in_list
        | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LAS| exact N1]
        | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LAB| exact N2]
        | exact AO ]. }
    assert (VI2 : match x_vi x with None => True | Some yi =>
                    vsb_obj LPA A1 (aview A1 m2) (x_v x Finclude_src) yi true /\ x_v x Finclude_src <> vb_buf vv1 /\ vb_buf yi <> vb_buf vv1 end).
    { destruct (x_vi x) as [yi|] eqn:EQi; [| exact I]. (first [ dand7 VI as INZ IO IE0 ISZ ILEN IAP IAP2 | destruct VI as (INZ & IO & IE0 & ISZ & ILEN & IAP & IAP2) ]).
      (first [ pose proof (IO) as dR_15; dand5 dR_15 as _ _ LIS LIB _ | pose proof IO as (_ & _ & LIS & LIB & _) ]).
      destruct (IAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [N1 N2].
      split; [| split; [eapply (fresh_ne _ _ _ _ _ _ REL); [exact LIS| exact N1] | eapply (fresh_ne _ _ _ _ _ _ REL); [exact LIB| exact N2]]].
      eapply (vsb_obj_call (pe_H E) A A1 m md _ _ _ _ _ _ AINV CF1 HFR WIN);
        [ exact CV1 | in_list | in_list
        | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LIS| exact N1]
        | eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LIB| exact N2]
        | exact IO ]. }
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV LVS)) as dR_16; dand4 dR_16 as _ _ Slo _ | destruct (live_geomP LPA _ _ _ _ _ AINV LVS) as (_ & _ & Slo & _) ]). unfold kHighMemBeg in Slo. all_app_facts.
    pose proof (lib_frames_same A A1 2%nat 0%nat (frames_same_lib _ _ FRS LIBF) FA1) as FS1.
    assert (PI1 : pinv E (after_mark x p' v1 vv1) A1 (aview A1 m2)).
    { unfold after_mark. apply Build_pinv; psimp; vk_norm VK; psimp.
      - exact VO1.
      - unfold vep_base; vk_norm VK; unfold vep_base in BASE; exact BASE.
      - exact FLG. - exact VSBF. - exact STUP. - exact STATE.
      - rewrite VERP1. replace (p' - pe_DATA E) with (x_v x Fver_p - pe_DATA E + (p' - x_v x Fver_p)) by (clear; lia). exact CNT1.
      - rewrite VERP1. klia VERP LEP.
      - exact PLE'.
      - rewrite LM1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | exact BM].
      - exact TAGI.
      - split; [exact DELIM1| exact DELIM2].
      - exact ESIC. - exact UNTL. - exact MTCH. - exact DOST. - exact ARMED. - exact ATTR. - exact ATTRST. - exact MATTR.
      - intros X Y Z. rewrite (SAME (or_introl X)) in Z |- *. unfold look in LOOKA |- *. cbn [x_p]. exact (LOOKA X Y Z).
      - intros X Y Z. rewrite (SAME (or_intror X)) in Z |- *. unfold look in LOOKM |- *. cbn [x_p]. exact (LOOKM X Y Z).
      - exact VSO1.
      - klia SZ1 ROOM LEN1.
      - revert OUT LEN1 LEP VERP. clear. cbv [oacost oicost x_va x_vi]. destruct (x_st x), (x_va x), (x_vi x); intros; lia.
      - intros y Hy. split; [apply (proj1 (APART y Hy))|].
        cbn in Hy. destruct Hy as [<-|[<-|[<-|[]]]]; apply not_eq_sym; [exact NB_V| exact NB_W| exact NB_D].
      - exact WAL1.
      - exact AVSB.
      - clear - VA VA2 LEP; try pose proof alloc_ceiling_val. destruct (x_va x) as [ya|]; [|exact VA].
        (first [ dand5 VA as Q1 _ Q3 Q4 Q5 | destruct VA as (Q1 & _ & Q3 & Q4 & Q5) ]). (first [ dand3 VA2 as R1 R2 R3 | destruct VA2 as (R1 & R2 & R3) ]).
        refine (conj Q1 (conj R1 (conj Q3 (conj _ _)))); [lia|].
        intros y Hy. cbn in Hy. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]].
        1-4: apply Q5; cbn; auto 10.
        split; [exact R2| exact R3].
      - clear - VI VI2 LEP; try pose proof alloc_ceiling_val. destruct (x_vi x) as [yi|]; [|exact VI].
        (first [ dand7 VI as I1 _ I3 I4 I5 I6 I7 | destruct VI as (I1 & _ & I3 & I4 & I5 & I6 & I7) ]). (first [ dand3 VI2 as R1 R2 R3 | destruct VI2 as (R1 & R2 & R3) ]).
        refine (conj I1 (conj R1 (conj I3 (conj I4 (conj _ (conj _ I7)))))); [lia|].
        intros y Hy. cbn in Hy. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]].
        1-4: apply I6; cbn; auto 10.
        split; [exact R2| exact R3].
      - exact DATA1.
      - exact HENV1.
      - rewrite EFP. exact ST1.
      - exists j0, j8. rewrite EFP. exact FR2.
      - exact MI1.
      - exact SS1.
      - revert LB LB1. clear. unfold world_bytes, x_vio. destruct (x_va x), (x_vi x); cbn [option_map]; intros; lia.
      - rewrite NL1. exact NL.
      - rewrite TC1. exact TC.
      - intros ff. rewrite (FS1 ff). apply FRS.
      - intros p k Lp NBp. pose proof (KEEP p k Lp NBp) as LA.
        eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LA|].
        intros ->. destruct (NEW (vb_buf (x_vv x)) ltac:(unfold parse_blocks; left; reflexivity)) as [EQ|EQ]; [exact (NBp EQ)| rewrite EQ in Lp; discriminate Lp].
      - intros p Hp. unfold parse_blocks in Hp. vk_norm_in VK Hp. destruct Hp as [Hp|Hp].
        + subst p. destruct REL as [EQ|[E1 E2]].
          * rewrite EQ. apply NEW. unfold parse_blocks. left. reflexivity.
          * destruct (Z.eq_dec (vb_buf vv1) (pe_b E)) as [EQ|NEQ]; [left; exact EQ| right].
            destruct (a_live (pe_A0 E) (vb_buf vv1)) as [k|] eqn:EK; [| reflexivity].
            pose proof (KEEP _ _ EK NEQ) as LA. rewrite LA in E1. discriminate E1.
        + apply NEW. unfold parse_blocks. right. exact Hp.
      - eapply (cframe_step_call E x (after_mark x p' v1 vv1) A A1 _ _ (pe_sp E - 320) 8800);
          [ exact CF | exact CF1 | rewrite PARSE_STACK_val; klia W0 | klia W0
          | eapply parse_window_mapped; [exact PE| rewrite EFP; exact ST1| rewrite EFP; exact FR2]
          | intros a [Ha|[Ha|Ha]]; unfold pzone, parse_changed, parse_new;
            [ left; left; exact Ha | right; left; exact Ha | left; right; left; split; [klia Slo| exact Ha] ]
          | intros a Ha; unfold after_mark in Ha; unfold parse_new in Ha; cbn [x_v x_vv x_va x_vi x_vio option_map] in Ha;
            vk_norm_in VK Ha; destruct Ha as [Ha|Ha]; [left; exact Ha| right; unfold pzone; right; unfold parse_new; right; exact Ha] ].
      - exact CR0.
      - klia WL LEP.
      - lazymatch goal with |- _ - (_ + _ + ?s' / 4096) <= _ <= _ =>
          lazymatch type of SC with _ - (_ + _ + ?s / 4096) <= _ <= _ =>
            assert (DV : s / 4096 <= s' / 4096) by (apply Z.div_le_mono; klia LEP) end end.
        revert SC SCC1 DV. clear. intros; lia.
      - exact PR0.
      - exact PPH.
      - (* [comment removed for export] *)
        eapply (pc_xfer _ _ _ _ _ _ _ _ PC PCC1). unfold after_mark. pc_unfold. cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi]. vk_norm VK. klia LEP. }
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m2 md1 v1 vv1 _ eq_refl PI1 AINV1 (amd_frame_trans _ _ _ MDF0 MDF1) VK VERP1 LM1 OP1 CRC1 CRCP1).
  Qed.
End S.
End A_PMark.

   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition vep_pre33 (v : vep) (q : vep_pads) : list cell :=
  [ C4 (Z_to_bv 64 VEP_MAGIC); C4 (Z_to_bv 64 (v Fflags)); C8 (Z_to_bv 64 (v Fvsb)); C8 (Z_to_bv 64 (v Furl)); C8 (Z_to_bv 64 (v Fvc));
    C4 (Z_to_bv 64 (v Fdogzip)); CB 4 (p36 q); C8 (Z_to_bv 64 (v Fcb)); C8 (Z_to_bv 64 (v Fcb_priv));
    C8 (Z_to_bv 64 (v Fcb_x)); C8 (Z_to_bv 64 (v Fstate)); C4 (Z_to_bv 64 (v Fstartup)); C4 (Z_to_bv 64 (v Fesi_found));
    C4 (Z_to_bv 64 (v Fendtag)); C4 (Z_to_bv 64 (v Femptytag)); C4 (Z_to_bv 64 (v Fcanattr)); C4 (Z_to_bv 64 (v Fremove));
    C8 (Z_to_bv 64 (v Fo_wait)); C8 (Z_to_bv 64 (v Fo_pending)); C8 (Z_to_bv 64 (v Fo_total)); C4 (Z_to_bv 64 (v Fcrc));
    CB 4 (p124 q); C8 (Z_to_bv 64 (v Fo_crc)); C4 (Z_to_bv 64 (v Fcrcp)); CB 4 (p140 q);
    C8 (Z_to_bv 64 (v Fo_last)); C8 (Z_to_bv 64 (v Fhack_p)); C8 (Z_to_bv 64 (v Fver_p)); C8 (Z_to_bv 64 (v Funtil));
    C8 (Z_to_bv 64 (v Funtil_p)); C8 (Z_to_bv 64 (v Funtil_s)); C4 (Z_to_bv 64 (v Fin_esi_tag)); CB 4 (p196 q) ].
Definition vep_post35 (v : vep) (tag : list byte) (q : vep_pads) : list cell :=
  [ C8 (Z_to_bv 64 (v Fattr)); C8 (Z_to_bv 64 (v Fattr_vsb));
    C4 (Z_to_bv 64 (v Fattr_delim)); CB 4 (p236 q); C8 (Z_to_bv 64 (v Fmatch)); C8 (Z_to_bv 64 (v Fmatch_hit));
    CB 8 tag; C4 (Z_to_bv 64 (v Ftag_i)); CB 4 (p268 q); C8 (Z_to_bv 64 (v Fdostuff));
    C8 (Z_to_bv 64 (v Finclude_src)); C4 (Z_to_bv 64 (v Finclude_continue)); C4 (Z_to_bv 64 (v Fnm_skip)); C4 (Z_to_bv 64 (v Fnm_verbatim));
    C4 (Z_to_bv 64 (v Fnm_pending)); C4 (Z_to_bv 64 (v Flast_mark)); CB 4 (p308 q) ].

Lemma vep_cells_split3 : forall v tag q,
  vep_cells v tag q = vep_pre33 v q ++ [C8 (Z_to_bv 64 (v Fesicmt)); C8 (Z_to_bv 64 (v Fesicmt_p))] ++ vep_post35 v tag q.
Proof. intros; reflexivity. Qed.

Lemma vep_cells_esicmt0 : forall v tag q,
  vep_cells (fupd (fupd v Fesicmt 0) Fesicmt_p 0) tag q = vep_pre33 v q ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ++ vep_post35 v tag q.
Proof. intros; reflexivity. Qed.

Lemma vep_pre33_size : forall v q, cells_size (vep_pre33 v q) = 200%nat.
Proof. intros; reflexivity. Qed.

Definition memset_esicmt_post (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (VEP + 200)) a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(VEP + 200, VEP + 216); (bv_unsigned sp - ASAN_MEMSET_STACK, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' VEP (vep_cells (fupd (fupd vv Fesicmt 0) Fesicmt_p 0) tag q).

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma memset_esicmt_spec : forall VEP vv tag q ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z),
  rw_cells rsegs m VEP (vep_cells vv tag q) -> length tag = 8%nat -> vep_pads_wf q ->
  mem_inv rsegs m ->
  asan_memset_cells m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo + ASAN_MEMSET_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (0 <= VEP)%Z -> (VEP + 312 <= lo)%Z ->
  range_ok m (VEP + 200) 16 ->
  evt rsegs (memset_esicmt_post VEP vv tag q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (VEP + 200)) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57998) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros VEPC T8 PW MI CELLS ST LOLE CEIL V0 SEP RNG.
  pose proof alloc_ceiling_num as ACV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  rewrite vep_cells_split3 in VEPC.
  pose proof (rw_cells_merge rsegs _ _ _ _ _ VEPC) as V2. clear VEPC. cbn [cells_size cells_bytes csize cbytes Nat.add app] in V2.
  lazymatch type of V2 with rw_cells _ _ _ (_ ++ ?mid :: ?post) =>
    destruct (proj1 (rw_cells_app rsegs m VEP (vep_pre33 vv q) (mid :: post)) V2) as [VPRE V3] end.
  clear V2. rewrite vep_pre33_size in V3. change (Z.of_nat 200) with 200%Z in V3.
  lazymatch type of V3 with rw_cells _ _ _ (?mid :: ?post) =>
    destruct (proj1 (rw_cells_app rsegs m (VEP + 200) [mid] post) V3) as [VMID VPOST] end.
  clear V3. cbn [cells_size csize Nat.add] in VPOST. replace (VEP + 200 + Z.of_nat 16)%Z with (VEP + 216)%Z in VPOST by lia.
  pose proof (rw_cells_bound _ _ _ _ VPRE) as B1. rewrite vep_pre33_size in B1.
  pose proof (rw_cells_bound _ _ _ _ VPOST) as B2.
  assert (SZP : cells_size (vep_post35 vv tag q) = 96%nat) by reflexivity.
  rewrite SZP in B2.
  eapply evt_cut.
  { eapply (asan_memset_spec ra sp gp tp t0 t1 t2 s0 s1 _ _ _ a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m _ lo);
      rewrite ?unsigned_lit by lia;
      [ exact VMID | exact MI | exact CELLS | exact ST | exact LOLE | exact CEIL | left; lia | lia | right; exact RNG ]. }
  intros ms' PO. unfold asan_memset_post in PO. unfold ASAN_MEMSET_STACK in *.
  rewrite ?unsigned_lit in PO by lia.
  (first [ dex15 PO as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m'; dand6 PO as -> MU WM MI' ST' Z16 | dand21 PO as t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' -> MU WM MI' ST' Z16 | destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & Z16) ]).
  replace (VEP + 200 + 16)%Z with (VEP + 216)%Z in MU by lia.
  apply evt_done. unfold memset_esicmt_post. unfold ASAN_MEMSET_STACK.
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|].
  rewrite vep_cells_esicmt0.
  lazymatch type of MU with munch ?W _ _ =>
    apply (rw_cells_transport rsegs W m m' _ _) in VPRE; [| exact MU | exact WM | cbn [disjoint_from]; rewrite vep_pre33_size; lia];
    apply (rw_cells_transport rsegs W m m' _ _) in VPOST; [| exact MU | exact WM | cbn [disjoint_from]; rewrite SZP; lia] end.
  change (Z.to_nat 16) with 16%nat in Z16. change (0 mod 256)%Z with 0%Z in Z16.
  apply (rw_cells_recast rsegs _ _ _ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in Z16; [| cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity | vm_compute; reflexivity].
  apply (proj2 (rw_cells_app rsegs m' VEP (vep_pre33 vv q) _)). rewrite vep_pre33_size. split; [exact VPRE|].
  change (Z.of_nat 200) with 200%Z.
  apply (proj2 (rw_cells_app rsegs m' (VEP + 200) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] _)). split; [exact Z16|].
  cbn [cells_size csize Nat.add]. replace (VEP + 200 + Z.of_nat 16)%Z with (VEP + 216)%Z by lia. exact VPOST.
Qed.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DS.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma data_shadow : forall A m md DATA inp,
    ainv A m md -> data_obj LPA A (aview A m) DATA inp ->
    bytes_at rsegs (aview A m) (sh DATA) (shpat (Z.of_nat (length inp))) /\ DATA mod 16 = 0.
  Proof.
    (intros A m md DATA inp AINV; (first [ intro dR_5; dand3 dR_5 as L _ _ | intros (L & _ & _) ])). split.
    - pose proof (as_live_shadow LPA _ _ _ _ _ AINV L) as X. exact X.
    - (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV L)) as dR_2; dand3 dR_2 as _ X _ | destruct (live_geomP LPA _ _ _ _ _ AINV L) as (_ & X & _) ]). exact X.
  Qed.
End DS.

(* [comment removed for export] *)
Ltac shadow_slowj U :=
  zstep; zstep;
  let K2 := fresh "KS2" in
  first [ zstep; if_cases K2; zify_cond K2
        | zstep; zstep; if_cases K2; zify_cond K2 ];
  [ first [ shadow_dead | zstep; shadow_join U ] | first [ shadow_dead | zstep; shadow_join U ] ].

(* [comment removed for export] *)
Ltac pchk SRC k U :=
  zstep; zstep; shadow_addr SRC k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slowj U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slowj U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

Ltac prechk SRC X k U :=
  shadow_addr_at SRC X k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slowj U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slowj U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac world_close PE0 AINV HFR MU WM WZ :=
  unhide_parse_junk;
  lazymatch goal with
  | |- match ?o with Some _ => _ | None => _ end =>
      first
        [ match goal with
          | H : match o with Some _ => _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ | None => _ end |- _ =>
              destruct o eqn:?; [| exact H];
              let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in
              let H5 := fresh in let H6 := fresh in let H7 := fresh in
              (first [ dand7 H as H1 H2 H3 H4 H5 H6 H7 | destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7) ]);
              refine (conj H1 (conj _ (conj H3 (conj H4 (conj _ (conj H6 H7))))));
              [ eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV HFR MU WM WZ); [in_list| in_list| exact H2]
              | revert H5; unhide_neqs; repeat match goal with K : _ <> _ |- _ => clear K end; intros H5; clear_parse_junk; lia ]
          end
        | match goal with
          | H : match o with Some _ => _ /\ _ /\ _ /\ _ /\ _ | None => _ end |- _ =>
              destruct o eqn:?; [| exact H];
              let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in let H5 := fresh in
              (first [ dand5 H as H1 H2 H3 H4 H5 | destruct H as (H1 & H2 & H3 & H4 & H5) ]);
              refine (conj H1 (conj _ (conj H3 (conj _ H5))));
              [ eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV HFR MU WM WZ); [in_list| in_list| exact H2]
              | revert H4; unhide_neqs; repeat match goal with K : _ <> _ |- _ => clear K end; intros H4; clear_parse_junk; lia ]
          end ]
  end.

(* [comment removed for export] *)
Lemma zx16_vct : forall c, zx16 (Z_to_bv 64 (vct c)) = Z_to_bv 64 (vct c).
Proof.
  intros c. pose proof (vct_range c) as R. unfold zx16. rewrite unsigned_lit by lia.
  rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Ltac cf_stores_x CF MU PE0 STK FR X :=
  eapply (cframe_step_stores _ _ X);
  [ exact CF | exact MU | w_in_zone_tac
  | eapply parse_window_mapped; [exact PE0| exact STK| unfold pframe; cbv zeta; exact FR]
  | let a := fresh "a" in let Y := fresh "Y" in intros a Y; eapply parse_new_same; [| | exact Y]; reflexivity ].

(* [comment removed for export] *)
Tactic Notation "prechkn" constr(SRC) constr(X) constr(k) constr(U) integer(n) :=
  shadow_addr_at SRC X k;
  lazymatch goal with |- evt ?segs ?Q _ =>
    eapply (evt_cut segs _ Q);
    [ zstep; do n zstep;
      let K := fresh "KS" in
      zstep; if_cases K; zify_cond K;
      [ first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slowj U ]
      | first [ shadow_fast K; shadow_join U | shadow_dead | shadow_slowj U ] ]
    | let ms := fresh "ms" in let x := fresh "junk" in
      intros ms [x ->]; simp_regs ]
  end;
  shadow_cleanup.
