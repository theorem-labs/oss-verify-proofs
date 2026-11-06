(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.

Module A_PKitX.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Vsb A_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App.A_Fpx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Img A_La0bg A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_vez59 A_PDefs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit.
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

Section StoresX.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)

  Fixpoint wzonex (E : penv) (A : AS) (excl : list Z) (W : list (Z * Z)) : Prop :=
    match W with
    | [] => True
    | (lo, hi) :: W' =>
        ((exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= lo /\ hi <= p + n)
         \/ (pe_lo E <= lo /\ hi <= pe_fp E + 16)
         \/ (lo = h_vsc (pe_H E) + 1304 /\ hi = h_vsc (pe_H E) + 1320)
         \/ (lo = ERRNOA /\ hi = ERRNOA + 4))
        /\ wzonex E A excl W'
    end.

  (* [comment removed for export] *)
  Lemma wzonex_cases : forall E A excl W a,
    wzonex E A excl W -> ~ outside W a ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n)
    \/ (pe_lo E <= a < pe_fp E + 16)
    \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320)
    \/ (ERRNOA <= a < ERRNOA + 4).
  Proof.
    intros E A excl W a. induction W as [|[lo hi] W IH]; cbn; intros WZ NO; [exfalso; exact (NO I)|].
    destruct WZ as [C WZ].
    destruct (Classical_Prop.classic (lo <= a < hi)) as [IN|NIN].
    - destruct C as [(p & n & L & NI & H1 & H2)|[[H1 H2]|[[H1 H2]|[H1 H2]]]].
      + left. exists p, n. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia.
      + right; left. lia.
      + right; right; left. lia.
      + right; right; right. lia.
    - apply IH; [exact WZ|]. intros O. apply NO. split; [exact NIN| exact O].
  Qed.

  (* [comment removed for export] *)
  Lemma wzonex_client_fpx : forall E A v excl W j0 j8,
    penv_ok E -> hframe LPA A (pe_H E) ->
    stk rsegs v (pe_lo E) (pe_fp E) -> rw_cells rsegs v (pe_fp E) (pframe E j0 j8) ->
    wzonex E A excl W -> client_fpx A v W.
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
    destruct C as [(p & n & L & NI & H1 & H2)|[[H1 H2]|[[H1 H2]|[H1 H2]]]].
    - right; left. exists p, n. auto.
    - left. split; [lia|]. split; [unfold pe_fp, PARSE_FRAME in *; lia|].
      intros i Hi. replace (lo + i) with (pe_lo E + (lo + i - pe_lo E)) by lia. apply MAPW. lia.
    - right; right; left. exists (h_ff (pe_H E)), HCLASS, age. split; [exact HF|].
      change (fsize HCLASS) with 8192. unfold h_vsc in *. lia.
    - right; right; right; right. subst lo hi. rewrite <- ERRNOA_eq. exact (img_ivl_errno (L:=LPA)).
  Qed.

  Variables (E : penv) (A : AS) (m : mem) (md : Model) (v' : mem) (excl : list Z) (W : list (Z * Z)).
  Hypothesis PE : penv_ok E.
  Hypothesis AINV : ainv A m md.
  Hypothesis HFR : hframe LPA A (pe_H E).
  Hypothesis MU : munch W (aview A m) v'.
  Hypothesis WM : wmono rsegs (aview A m) v'.
  Hypothesis WZ : wzonex E A excl W.
  (* [comment removed for export] *)
  Local Ltac touch := pose proof (conj PE (conj AINV (conj HFR (conj MU (conj WM WZ))))) as TT__; clear TT__.

  (* [comment removed for export] *)
  Lemma outside_blkx : forall o0 k a,
    In o0 excl -> a_live A o0 = Some k -> o0 <= a < o0 + k -> outside W a.
  Proof.
    touch.
    intros o0 k a IN L Ha. destruct HFR as [age HF].
    destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
    destruct PE as (HG & _ & _ & CEIL & LOP & SPH & _).
    (first [ pose proof ((live_geomP LPA A m md o0 k AINV L)) as dR_2; dand5 dR_2 as _ _ LO HI _ | destruct (live_geomP LPA A m md o0 k AINV L) as (_ & _ & LO & HI & _) ]).
    destruct (wzonex_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]].
    - assert (NE : p <> o0) by (intros ->; exact (NI IN)).
      pose proof (as_live_disjoint LPA A m md p n o0 k AINV Lp L NE). lia.
    - rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME in *. lia.
    - pose proof (as_frame_blk_disjoint LPA A m md (h_ff (pe_H E)) HCLASS age o0 k AINV HF L) as D.
      change (fsize HCLASS) with 8192 in D. unfold h_vsc in R. lia.
    - (first [ pose proof ((live_geomP LPA A m md o0 k AINV L)) as dR_3; dand6 dR_3 as _ _ _ _ Pimg _ | destruct (live_geomP LPA A m md o0 k AINV L) as (_ & _ & _ & _ & Pimg & _) ]).
      unfold off_image in Pimg. cbn [cl_image_lo cl_image_hi LPA] in Pimg. unfold ERRNOA in R. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma outside_hframex : forall a,
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
    destruct (wzonex_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]].
    - pose proof (as_frame_blk_disjoint LPA A m md (h_ff (pe_H E)) HCLASS age p n AINV HF Lp) as D.
      change (fsize HCLASS) with 8192 in D.
      (first [ pose proof ((live_geomP LPA A m md p n AINV Lp)) as dR_5; dand4 dR_5 as _ _ PLO _ | destruct (live_geomP LPA A m md p n AINV Lp) as (_ & _ & PLO & _) ]). unfold kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME, kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - exact (NC R).
    - unfold ERRNOA, kHighMemBeg in *. all_app_facts. unhide_app. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma bytes_at_stores_blkx : forall o0 k o bs,
    In o0 excl -> a_live A o0 = Some k -> o0 <= o -> o + Z.of_nat (length bs) <= o0 + k ->
    bytes_at rsegs (aview A m) o bs -> bytes_at rsegs v' o bs.
  Proof.
    touch.
    (intros o0 k o bs IN L H1 H2; (first [ intro dR_14; dand3 dR_14 as B0 B1 B | intros (B0 & B1 & B) ])). split; [exact B0|]. split; [exact B1|]. intros i Hi.
    unfold mrd. rewrite MU; [apply B; exact Hi|]. rewrite wa_unsigned by lia.
    eapply outside_blkx; [exact IN| exact L| lia].
  Qed.

  Lemma vsb_obj_storesx : forall S vr fin,
    In S excl -> In (vb_buf vr) excl -> vsb_obj LPA A (aview A m) S vr fin -> vsb_obj LPA A v' S vr fin.
  Proof.
    touch.
    intros S vr fin I1 I2 VO. (first [ pose proof (VO) as dR_7; dand5 dR_7 as _ _ LS LB _ | pose proof VO as (_ & _ & LS & LB & _) ]).
    eapply (vsb_obj_munch A W); [exact VO| exact MU| exact WM|].
    intros a [Ha|Ha]; [eapply (outside_blkx S 40)| eapply (outside_blkx (vb_buf vr) (vb_size vr))]; try eassumption.
  Qed.

  (* [comment removed for export] *)

  Lemma data_obj_storesx : forall DATA inp,
    In DATA excl -> data_obj LPA A (aview A m) DATA inp -> data_obj LPA A v' DATA inp.
  Proof.
    touch.
    (intros DATA inp IN; (first [ intro dR_15; dand3 dR_15 as L B LEN | intros (L & B & LEN) ])). split; [exact L|]. split; [|exact LEN].
    eapply (bytes_at_stores_blkx DATA (Z.of_nat (length inp))); [exact IN| exact L| lia| lia| exact B].
  Qed.

  (* [comment removed for export] *)
  Lemma henv_storesx :
    (forall a, h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320 -> outside W a) ->
    henv_ok LPA VIA (pe_H E) A (aview A m) -> henv_ok LPA VIA (pe_H E) A v'.
  Proof.
    touch.
    intros NV HE. destruct PE as (HG & PE'). (first [ pose proof (HG) as dR_9; dand3 dR_9 as G1 G2 G3 | pose proof HG as (G1 & G2 & G3) ]). unfold HFSIZE in G3.
    eapply (henv_ok_munch LPA); [exact HE| exact MU| exact WM| exact HG|].
    intros a Ha. unfold HOBJ_END, HFSIZE in Ha.
    destruct (Classical_Prop.classic (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320)) as [C|NC]; [apply NV; exact C|].
    destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
    - (* [comment removed for export] *)
      destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
      destruct HFR as [age HF]. pose proof alloc_ceiling_num as ACV.
      destruct (wzonex_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]].
      + (first [ pose proof ((live_geomP LPA A m md p n AINV Lp)) as dR_10; dand4 dR_10 as _ _ PLO _ | destruct (live_geomP LPA A m md p n AINV Lp) as (_ & _ & PLO & _) ]). cbn [vi_bss_vsc VIA] in Ha. unfold kHighMemBeg in PLO. all_app_facts. unhide_app. lia.
      + cbn [vi_bss_vsc VIA] in Ha. rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME in *. lia.
      + cbn [vi_bss_vsc VIA] in Ha. unfold h_vsc, kHighMemBeg in *. all_app_facts. unhide_app. lia.
      + cbn [vi_bss_vsc VIA] in Ha. unfold ERRNOA in R. lia.
    - destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
      destruct HFR as [age HF]. pose proof alloc_ceiling_num as ACV.
      destruct (wzonex_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]].
      + (first [ pose proof ((live_geomP LPA A m md p n AINV Lp)) as dR_11; dand4 dR_11 as _ _ PLO _ | destruct (live_geomP LPA A m md p n AINV Lp) as (_ & _ & PLO & _) ]). cbn [vi_bss_cp VIA] in Ha. unfold kHighMemBeg in PLO. all_app_facts. unhide_app. lia.
      + cbn [vi_bss_cp VIA] in Ha. rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME in *. lia.
      + cbn [vi_bss_cp VIA] in Ha. unfold h_vsc, kHighMemBeg in *. all_app_facts. unhide_app. lia.
      + cbn [vi_bss_cp VIA] in Ha. unfold ERRNOA in R. lia.
    - exfalso. exact (NC Ha).
    - apply outside_hframex; [| exact NC]. left. unfold h_cp in Ha. lia.
    - apply outside_hframex; [| exact NC]. right. change (8192 / 8) with 1024 in Ha. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma stack_shadow_storesx : forall SB NS lo hi,
    stack_shadow LPA (aview A m) SB NS lo hi -> stack_shadow LPA v' SB NS lo hi.
  Proof.
    touch.
    (intros SB NS lo hi; (first [ intro dR_16; dand6 dR_16 as B N0 Lq Hh SLO T | intros (B & N0 & Lq & Hh & SLO & T) ])). split; [| exact (conj N0 (conj Lq (conj Hh (conj SLO T))))].
    eapply (bytes_at_munch LPA); [exact B| exact MU|]. rewrite repeat_length, Z2Nat.id by lia.
    intros a Ha. destruct HFR as [age HF]. pose proof alloc_ceiling_num as ACV.
    destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
    destruct PE as (HG & _ & _ & CEIL & LOP & SPH & _). (first [ dand3 HG as G1 G2 G3 | destruct HG as (G1 & G2 & G3) ]).
    destruct (wzonex_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]].
    - (first [ pose proof ((live_geomP LPA A m md p n AINV Lp)) as dR_13; dand4 dR_13 as _ _ PLO _ | destruct (live_geomP LPA A m md p n AINV Lp) as (_ & _ & PLO & _) ]). unfold kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - rewrite ?PARSE_STACK_val in *. unfold pe_fp, PARSE_FRAME, kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - unfold h_vsc, kHighMemBeg in *. all_app_facts. unhide_app. lia.
    - unfold ERRNOA, kHighMemBeg in *. all_app_facts. unhide_app. lia.
  Qed.
End StoresX.

(* [comment removed for export] *)
Ltac wzonex_tac :=
  cbn [wzonex];
  repeat lazymatch goal with
  | |- (_ \/ _) /\ _ =>
      split;
      [ lazymatch goal with
        | |- _ \/ (_ <= ?lo /\ _) \/ _ =>
            lazymatch lo with
            | context [pe_sp] => right; left; unfold pe_fp, PARSE_FRAME; lia
            | context [pe_fp] => right; left; unfold pe_fp, PARSE_FRAME; lia
            | context [bv_unsigned] => right; left; unfold pe_fp, PARSE_FRAME; lia
            | context [h_vsc] => right; right; left; split; reflexivity
            | ERRNOA => right; right; right; split; reflexivity
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
End A_PKitX.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDswi.A_PKitX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PCall OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require Import A_AI16.

Module A_PH81r.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PDncj.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PCall OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDncj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.
  Hypothesis HDS : VSB_destroy_stmt.

  #[using="HDS HMC"] Lemma PH_TagError : handler_stmt S_TagError.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 0) by (unfold phi, rank; rewrite ST; reflexivity).
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ ?P _ =>
    assert (LOOP : forall (k : nat) (q : Z) (ra' t1' t2' s1' a1' a2' a3' a4' a5' a6' s10' s11' t3' t4' t5' t6' : word),
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E ->
      evt rsegs P (loop_ms E 0x8c83c q ra' t1' t2' s1' (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' (Z_to_bv 64 (vi_st VIA S_NxtTag))
                          s10' s11' t3' t4' t5' t6' (aview A m)))
    end.
    { induction k as [|k IH]; intros until t6'; intros Hk LQ QE.
      { exfalso. try (generalize alloc_ceiling_val); clear - Hk QE; try pose proof alloc_ceiling_val. lia. }
      unfold loop_ms, S9, T0. rewrite EFP. cbn [vi_st VIA stA].
      (* [comment removed for export] *)
      zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU VERP LQ Dlo; lia ].
      (* [comment removed for export] *)
      shadow_chk SHD 1 12.
      (* [comment removed for export] *)
      (first [ pose proof ((payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val; lia) QE)) as dR_1; dex1 dR_1 as b; destruct dR_1 as [Hnth RDP] | pose proof ((payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val; lia) QE)) as dR_1; dand3 dR_1 as b Hnth RDP | destruct (payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val; lia) QE) as (b & Hnth & RDP) ]).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        zstep. zstep; if_cases KU; zify_cond KU; [ exfalso; clear - KU VERP LQ Dlo; lia | clear KU ].
        (* [comment removed for export] *)
        zstep. zstep. zstep. zstep. zstep.
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
        assert (PIq : pinv E (PST (q + 1) S_TagError (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A (aview A m)).
        { apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUh WMh WZ.
          - (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val. lia.
          - (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val. lia.
          - (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
          - (* [comment removed for export] *) revert VA LQ. clear. cbn [x_va x_v x_p x_vv]. destruct (x_va x); [| intros X _; exact X]. ((first [ intro dR_6; dand5 dR_6 as H1 H2 H3 H4 H5 | intros (H1 & H2 & H3 & H4 & H5) ]); intros LQ). refine (conj H1 (conj H2 (conj H3 (conj _ H5)))). lia.
          - (* [comment removed for export] *) revert VI LQ. clear. cbn [x_vi x_va x_v x_p x_vv]. destruct (x_vi x); [| intros X _; exact X]. ((first [ intro dR_7; dand7 dR_7 as H1 H2 H3 H4 H5 H6 H7 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) ]); intros LQ). refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 H7)))))). lia. }
        clear IH MUh WMh.
        astop0 AINV.
        eapply (mark_call HMC E _ A _ _ T (q + 1) (q + 1) 1 0x8cb44);
          [ exact PE | exact PIq | assumption | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
          | clear; cbn [x_p]; lia | cbn [x_p]; try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val; lia | right; reflexivity | clear; lia | reflexivity
          | cbn [x_st]; intros [X|X]; discriminate X | ].
        intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
        assert (ST1 : x_st x1 = S_TagError) by (rewrite EX1; reflexivity).
        assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
        assert (EPQ : x_p x1 = q + 1) by (rewrite EX1; reflexivity).
        clear - HMC HDS PE ST KL PHI PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EPQ LQ QE; try pose proof alloc_ceiling_val.
        pose proof PI1 as PIk.
        world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EPQ.
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
        assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                             [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
          by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
        (* [comment removed for export] *)
        assert (ATR : 0 <= x_v x1 Fattr_vsb < 2^64).
        { clear - VA AINV1 ACV; try pose proof alloc_ceiling_val. destruct (x_va x1) as [ya|].
          - (first [ dand3 VA as _ AOBJ _ | destruct VA as (_ & AOBJ & _) ]). (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV1 (proj1 (proj2 (proj2 AOBJ))))) as dR_3; dand5 dR_3 as _ _ L1 L2 _ | pose proof (live_geomP LPA _ _ _ _ _ AINV1 (proj1 (proj2 (proj2 AOBJ)))) as (_ & _ & L1 & L2 & _) ]). unfold kHighMemBeg in L1. all_app_facts. lia.
          - rewrite VA. lia. }
        hide_neqs.
        ago AINV1. fold_cl_segs.
        (* [comment removed for export] *)
        zstep. vchk SHV0 EzsV 4 0. zstep. zstep. zstep.
        (* [comment removed for export] *)
        zstep. vchk SHV0 EzsV 4 1. zstep.
        (* [comment removed for export] *)
        vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep.
        (* [comment removed for export] *)
        vchk SHV0 EzsV 8 0. zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. zstep. zstep.
          astop AINV1 MU WM CFP. fold_cl_segs.
          eapply (KL (PST (x_p x1) S_NxtTag (fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
          + apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
          * (* [comment removed for export] *) intros X. exfalso. exact (X K2).
            * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
          + assumption.
          + eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
          + (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ EPQ; try pose proof alloc_ceiling_val. lia.
        - (* [comment removed for export] *)
          assert (VNN : x_va x1 <> None).
          { clear - VA K2; try pose proof alloc_ceiling_val. destruct (x_va x1); [intros X; discriminate X| exfalso; exact (K2 VA)]. }
          zstep. zstep.
          astop AINV1 MU WM CFP. fold_cl_segs.
          lazymatch goal with H : ainv A1 ?mm ?mdd |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mm _) ?mdd) _ => rename H into AINVs end.
          assert (CFs : cframe LPA (owned (pe_A0 E)) (owned A1) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
                          (parse_new (fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) (x_vv x1) (x_va x1) (x_vio x1)) (pe_v0 E) (aview A1 _))
            by (cf_stores_x CF MU PE0 STK FR (PST (x_p x1) S_NxtTag (fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)); left; left; unfold blk; lia).
          unhide_neqs.
          eapply (destroy_attr HDS E x1 A1 _ _ _ _ T 0x8cbb4 [(pe_VEP E, pe_VEP E + 312)] (fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) j0 j8);
            [ exact PE | exact PIk | exact AINV1 | exact AINVs | exact MU | exact WM | exact WZ
            | intros a Ha; unfold h_vsc in Ha; cbn [outside]; unhide_djf; try (generalize alloc_ceiling_val); clear - Ha VEPhi ACV G2 DJfV; try pose proof alloc_ceiling_val; unfold kHighMemBeg in G2; all_app_facts; lia
            | exact MI | exact STK | unfold pframe; cbv zeta; exact FR
            | unfold vep_cells; psimp; exact VEPC
            | psimp; reflexivity | psimp; reflexivity
            | exact VNN | clear; lia | reflexivity | exact CFs | ].
          clear VEPC FR STK MI SHV0 HENV VSBO DATA SS VI WAL CF LVEP LVS LVB HFR MU WM WZ CFP CFs.
          intros t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x A2 m4 md2 ya EVA AINV2 MI2 MDF2 STK2 FR2 VEPC2 HENV2 DATA2 VSBO2 WAL2 LVEP2 VI2 SS2 LB2 NL2 TC2 SCC2 PCC2 FS2 KEEP2 CF2.
          unfold call_ms. cbv zeta. rewrite EFP in *.
          pose proof (proj1 HENV2) as HFR2.
          (* [comment removed for export] *)
          unfold pframe in FR2. cbv zeta in FR2.
          ago AINV2. fold_cl_segs.
          zstep. zstep. zstep. zstep.
          pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A2 m4)) as MU4. pose proof (wmono_refl rsegs (aview A2 m4)) as WM4.
          assert (WZ4 : wzone E A2 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Finclude_src; oibuf x1] [(pe_VEP E, pe_VEP E + 312)]).
          { cbn [wzone]. split; [| exact I]. left. exists (pe_VEP E), 312. split; [exact LVEP2|]. split; [wz_not_in| clear; lia]. }
          assert (PIf : pinv E (PST (x_p x1) S_NxtTag (fupd (fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) Fattr_vsb 0) (x_tag x1) (x_q x1) (x_vv x1) None (x_vi x1)) A2 (aview A2 m4)).
          { unfold vep_cells in VEPC2. psimp_in VEPC2. unfold vi_world in VI2. psimp_in VI2.
            apply Build_pinv; psimp; pinv_close PE0 AINV2 HFR2 MU4 WM4 WZ4.
            all: try lazymatch goal with |- _ - _ <= a_seccred _ <= _ => rewrite SCC2; rewrite EVA in WL, SC, VA; (first [ dand4 VA as _ AO_ ASZ_ _ | destruct VA as (_ & AO_ & ASZ_ & _) ]); (first [ pose proof (AO_) as dR_5; dand3 dR_5 as _ VIa_ _ | pose proof AO_ as (_ & VIa_ & _) ]); unfold vsb_inv in VIa_;
              pose proof (vsb_pot_len ya ASZ_ ltac:(try (generalize alloc_ceiling_val); clear - VIa_; try pose proof alloc_ceiling_val; lia) ltac:(try (generalize alloc_ceiling_val); clear - VIa_; try pose proof alloc_ceiling_val; lia)) as PL_;
              eapply (sc_xfer _ _ _ _ _ _ _ _ SC);
              match goal with |- _ + _ + ?s / 4096 <= _ => pose proof (div4096_add s (vb_len ya) ltac:(klia WL) ltac:(klia VIa_)) as DA_ end;
              match type of DA_ with _ <= ?t / 4096 => match goal with |- _ <= _ + _ + ?t' / 4096 => replace t' with t by (clear; lia) end end;
              klia PL_ DA_ end.
            all: try lazymatch goal with |- 0 <= _ /\ 0 <= _ /\ _ <= _ - pe_DATA _ => rewrite EVA in WL; klia WL end.
            + (* [comment removed for export] *) revert OUT OA0. unfold oacost, oicost. rewrite EVA. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
            + (* [comment removed for export] *) intros X. exact (X eq_refl).
            + (* [comment removed for export] *) revert LB LB2. rewrite EVA. clear. unfold world_bytes, x_vio. cbn [option_map]. destruct (x_vi x1); cbn [option_map]; intros; lia.
            + (* [comment removed for export] *) revert NL NL2. rewrite EVA. clear. unfold world_nlive, x_vio. cbn [option_map]. destruct (x_vi x1); cbn [option_map]; intros; lia.
            + (* [comment removed for export] *) rewrite TC2. exact TC.
            + (* [comment removed for export] *) intros ff. rewrite (FS2 ff). apply FRS.
            + (* [comment removed for export] *) intros p Hp. apply NEW. revert Hp. rewrite EVA. unfold parse_blocks. psimp. clear. intros [Hp|[[]|Hp]]; [left; exact Hp| right; right; exact Hp].
            all: try exact CF2. }
          hide_neqs.
          astop0 AINV2.
          eapply (KL (PST (x_p x1) S_NxtTag (fupd (fupd (fupd (fupd (x_v x1) Fnm_skip (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_skip))) + 1)) Fin_esi_tag 0) Fstate (vi_st VIA S_NxtTag)) Fattr_vsb 0) (x_tag x1) (x_q x1) (x_vv x1) None (x_vi x1)) A2 _ _);
            [ exact PIf | assumption
            | eapply amd_frame_sbm_r; [eapply amd_frame_trans; [eapply amd_frame_sbm_r; [exact MDF1| eassumption]| exact MDF2]| eassumption]
            | psimp; intros _; split; [| discriminate]; rewrite PHI; unfold phi, rank; psimp; try (generalize alloc_ceiling_val); clear - LQ EPQ; try pose proof alloc_ceiling_val; lia ]. }
      (* [comment removed for export] *)
      zstep. zstep. if_cases K3; zify_cond K3.
      { try replace (q + 1 + 1) with (q + 1 + 1) by reflexivity. try replace (q + 2) with (q + 1 + 1) by (clear; lia).
        eapply (IH (q + 1)); [try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - K3 Hk QE; try pose proof alloc_ceiling_val; lia]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
      assert (PIe : pinv E (PST (pe_e E) S_TagError (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A (aview A m)).
      { apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUh WMh WZ.
        * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP PLT; try pose proof alloc_ceiling_val. lia.
        * (* [comment removed for export] *) revert OUT PLT. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
        * (* [comment removed for export] *) revert VA PLT. clear. cbn [x_va x_v x_p x_vv]. destruct (x_va x); [| intros X _; exact X]. ((first [ intro dR_8; dand5 dR_8 as H1 H2 H3 H4 H5 | intros (H1 & H2 & H3 & H4 & H5) ]); intros PLT). refine (conj H1 (conj H2 (conj H3 (conj _ H5)))). lia.
        * (* [comment removed for export] *) revert VI PLT. clear. cbn [x_vi x_va x_v x_p x_vv]. destruct (x_vi x); [| intros X _; exact X]. ((first [ intro dR_9; dand7 dR_9 as H1 H2 H3 H4 H5 H6 H7 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) ]); intros PLT). refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 H7)))))). lia. }
      astop0 AINV.
      eapply (KL (PST (pe_e E) S_TagError (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A _ _);
        [exact PIe| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| psimp; intros H; exfalso; try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val; lia]. }
    (* [comment removed for export] *)
    zstep; if_cases K0; zify_cond K0; try (exfalso; try (generalize alloc_ceiling_val); clear - K0 PLT; try pose proof alloc_ceiling_val; lia); [].
    zstep.
    eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT].
  Qed.
End S.
End A_PH81r.

Module A_PHdsh.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark.
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@VEPlo; @Dlo; @TAG; @WL; @Hk; @DLEN; @FRB; @G2; @LQ; @ACV; @EE; @VERP; @NN; @Ha; @KS; @PLT; @PLT0; @SZ; @SR; @VEPhi; @DJ_VD; @DJfV; @DJfD; @H; @OUT; @H2; @H3; @PLEc; @ACV__; @K1; @KU; @Kb; @K0])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)


Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_NotMyTag : handler_stmt S_NotMyTag.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PLT as PLT0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 1) by (unfold phi, rank; rewrite ST; reflexivity).
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    (* [comment removed for export] *)
    assert (TAIL : forall (xc : pst) (mc : mem) (mdc : Model) (ra' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' : word),
      pinv E xc A (aview A mc) -> ainv A mc mdc -> amd_frame (pe_md0 E) mdc ->
      (x_st xc = S_NotMyTag \/ x_st xc = S_NxtTag) -> (x_p xc < pe_e E -> phi E xc < phi E x) ->
      srealizes rsegs (mkCfg (loop_ms E 0x8bed8 (x_p xc) ra' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc STc PHIc.
      clear - HMC PE KL PIc AINVc MDFc STc PHIc; try pose proof alloc_ceiling_val as ACV__.
      assert (NMB : x_st xc <> S_MatchBuf) by (destruct STc as [X|X]; rewrite X; discriminate).
      pose proof PIc as PIc0. pose proof (pi_pe _ _ _ _ PIc) as PLEc.
      world_open PE PIc AINVc. unfold loop_ms, S9, T0. rewrite EFP in *.
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0.
      { (* [comment removed for export] *)
        astop0 AINVc.
        eapply (KL xc A _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
        intros H. split; [exact (PHIc H)| exact NMB]. }
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
      2:{ (* [comment removed for export] *)
          zstep. if_cases K1; zify_cond K1. 2:{ exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia. } clear K1.
          astop0 AINVc.
          eapply (KL xc A _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
          intros H. exfalso. try (generalize alloc_ceiling_val); clear - H K0; try pose proof alloc_ceiling_val as ACV__. lia. }
      zstep. if_cases K1; zify_cond K1. { exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia. } clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      astop0 AINVc.
      eapply (mark_call HMC E xc A _ _ T (x_p xc) (x_p xc) 0 0x8bf0c);
        [ exact PE | exact PIc0 | assumption | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
        | clear; lia | exact PLEc | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; destruct STc as [Y|Y]; rewrite Y in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (ST1 : x_st x1 = x_st xc) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      assert (EPc : x_p x1 = pe_e E) by (rewrite EP1; exact K0).
      assert (NMB1 : x_st x1 <> S_MatchBuf) by (rewrite ST1; exact NMB).
      clear - HMC PE KL PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPc NMB1; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. zstep. zstep. zstep. zstep. zstep.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) (x_st x1) (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        all: rewrite ?ST1; try assumption.
        + exact (conj DELIM1 DELIM2).
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      - psimp. rewrite EPc. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia. }
    (* [comment removed for export] *)
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    vchk SHV0 EzsV 1 0.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (rw_cells_read_sub rsegs mx _ _ 4 1 VEPC ltac:(clear; lia) ltac:(cbn; clear; lia)) as RDF end.
    match type of RDF with _ = Some ?r => change r with [Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))] in RDF end.
    remember (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (x_v x Fflags)))) as fb eqn:Efb in RDF.
    set (RWv := rw_cells rsegs _ (pe_VEP E)) in VEPC.
    zstep. subst RWv. clear RDF. cbv beta.
    zstep. zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      zstep. zstep. zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU VERP Dlo; lia ].
      vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
      astop AINV MU WM CFP. fold_cl_segs.
      set (xa := PST (x_p x + 1) S_NxtTag (fupd (x_v x) Fstate (vi_st VIA S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
      lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIa : pinv E xa A (aview A mr)) end.
      { subst xa. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
        + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__. lia.
        + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
      eapply (TAIL xa); [exact PIa| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| right; reflexivity|].
      subst xa. intros _. rewrite PHI. unfold phi, rank; psimp. clear. lia.
    - (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep. zstep.
      lazymatch goal with |- evt _ ?P (MS _ _ _ _ _ ?mc _) =>
      assert (LOOP : forall (k : nat) (q : Z) (ra' t1' t2' s1' a1' a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' : word),
                q + Z.of_nat k = pe_e E -> x_p x <= q -> q <= pe_e E ->
                evt rsegs P (loop_ms E 0x8bbcc q ra' t1' t2' s1' (Z_to_bv 64 q) a1' a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' mc))
      end.
      { induction k as [|k IH]; intros until t6'; intros Hk LQ QE; unfold loop_ms, S9, T0.
        - (* [comment removed for export] *)
          zstep. if_cases Kb; zify_cond Kb. 2:{ exfalso. try (generalize alloc_ceiling_val); clear - Kb Hk; try pose proof alloc_ceiling_val as ACV__. lia. }
          astop AINV MU WM CFP. fold_cl_segs.
          set (xq := PST q S_NotMyTag (fupd (x_v x) Ftag_i 0) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIq : pinv E xq A (aview A mr)) end.
          { subst xq. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
            + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val as ACV__. lia.
            + (* [comment removed for export] *) clear. lia.
            + (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
            + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
            + (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
            + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
          eapply (TAIL xq); [exact PIq| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| left; reflexivity|].
          subst xq. cbn [x_p]. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H Hk; try pose proof alloc_ceiling_val as ACV__. lia.
        - zstep. if_cases Kb; zify_cond Kb. { exfalso. try (generalize alloc_ceiling_val); clear - Kb Hk; try pose proof alloc_ceiling_val as ACV__. lia. } clear Kb.
          (* [comment removed for export] *)
          zstep. zstep. zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU VERP LQ Dlo; lia ].
          (* [comment removed for export] *)
          shadow_chk SHD 1 13.
          (* [comment removed for export] *)
          destruct (payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia)) as (b & Hnth & RDP).
          pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
          zstep. clear RDP. cbv beta.
          zstep. zstep. zstep. zstep. zstep. if_cases Kc; zify_cond Kc.
          + (* [comment removed for export] *)
            eapply (IH (q + 1)); [try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia].
          + (* [comment removed for export] *)
            zstep. vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep.
            astop AINV MU WM CFP. fold_cl_segs.
            set (xg := PST (q + 1) S_NxtTag (fupd (fupd (x_v x) Ftag_i 0) Fstate (vi_st VIA S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIg : pinv E xg A (aview A mr)) end.
            { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MU WM WZ.
              * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val as ACV__. lia.
              * (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__. lia.
              * (* [comment removed for export] *) clear. lia.
              * (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
              * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
              * (* [comment removed for export] *) world_close PE0 AINV HFR MU WM WZ.
              * (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia. }
            eapply (TAIL xg); [exact PIg| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| right; reflexivity|].
            subst xg. intros _. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia. }
      eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by lia; lia| clear; lia| try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; lia].
  Qed.
End S.
End A_PHdsh.

Module A_PHobr.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_TestXml : handler_stmt S_TestXml.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    pose proof (got_vct_cell _ (consts_hold_ainv LPA A m md AINV)) as GOTV. pose proof (vct_shadowA _ (consts_hold_ainv LPA A m md AINV)) as VSH. fold_cl_segs. fold_aview.
    unfold GOTA_vct, VCT_TYPTABA in GOTV. unfold VCT_TYPTABA in VSH.
    assert (VSHB : 0 <= sh 148416 /\ sh 148416 + Z.of_nat (length (repeat (Z_to_bv 8 0) 64)) <= 17594064011264).
    { unfold sh. rewrite kShadowOffset_val. change (148416 / 8) with 18552. change (Z.of_nat (length (repeat (Z_to_bv 8 0) 64))) with 64. clear; lia. }
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 9) by (unfold phi, rank; rewrite ST; reflexivity).
    hide_neqs.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ ?P _ =>
    assert (LOOP : forall (k : nat) (q : Z) (ra' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' s6' s10' t3' t4' t5' t6' : word),
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E ->
      evt rsegs P (loop_ms E 0x8bb00 q ra' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' s6' s10' (Z_to_bv 64 q) t3' t4' t5' t6' (aview A m)))
    end.
    { induction k as [|k IH]; intros until t6'; intros Hk LQ QE.
      { exfalso. try (generalize alloc_ceiling_val); clear - Hk QE; try pose proof alloc_ceiling_val as ACV__. lia. }
      unfold loop_ms, S9, T0. rewrite EFP.
      (* [comment removed for export] *)
      zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU VERP LQ Dlo; lia ].
      (* [comment removed for export] *)
      shadow_chk SHD 1 11.
      (* [comment removed for export] *)
      (first [ pose proof ((payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val as ACV__; lia) QE)) as dR_1; dex1 dR_1 as b; destruct dR_1 as [Hnth RDP] | pose proof ((payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val as ACV__; lia) QE)) as dR_1; dand3 dR_1 as b Hnth RDP | destruct (payload_read rsegs E _ q DBY ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val as ACV__; lia) QE) as (b & Hnth & RDP) ]).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta. zstep. zstep. zstep. zstep.
      replace (Z.shiftl (bv_unsigned b) 1) with (2 * bv_unsigned b) by (rewrite Z.shiftl_mul_pow2; clear; lia).
      (* [comment removed for export] *)
      zstep. zstep. shadow_addr VSH 2. zstep. lit0. chk_branch.
      pose proof (vct_readA _ (bv_unsigned b) _ MI BR eq_refl) as RDV. unfold wa, VCT_TYPTABA in RDV.
      zstep. clear RDV. cbv beta. rewrite zx16_vct.
      pose proof (vct_range (bv_unsigned b)) as VR.
      zstep. zstep. if_cases K1; zify_cond K1.
      { (* [comment removed for export] *)
        zstep. zstep. zstep. zstep.
        pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
        assert (PIq : pinv E (PST q S_TestXml (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A (aview A m)).
        { apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUh WMh WZ.
          - (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val as ACV__. lia.
          - (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val as ACV__. lia.
          - (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
          - (* [comment removed for export] *) revert VA LQ. clear. cbn [x_va x_v x_p x_vv]. destruct (x_va x); [| intros X _; exact X]. ((first [ intro dR_9; dand5 dR_9 as H1 H2 H3 H4 H5 | intros (H1 & H2 & H3 & H4 & H5) ]); intros LQ). refine (conj H1 (conj H2 (conj H3 (conj _ H5)))). lia.
          - (* [comment removed for export] *) revert VI LQ. clear. cbn [x_vi x_va x_v x_p x_vv]. destruct (x_vi x); [| intros X _; exact X]. ((first [ intro dR_10; dand7 dR_10 as H1 H2 H3 H4 H5 H6 H7 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) ]); intros LQ). refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 H7)))))). lia. }
        assert (PHIq : q = x_p x \/ x_p x < q) by (try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia).
        clear IH MUh WMh.
        astop0 AINV.
        eapply (mark_call HMC E _ A _ _ T q q 0 0x8bfc4);
          [ exact PE | exact PIq | assumption | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
          | clear; cbn [x_p]; lia | cbn [x_p]; try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val as ACV__; lia | left; reflexivity | clear; lia | reflexivity
          | cbn [x_st]; intros [X|X]; discriminate X | ].
        intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
        assert (ST1 : x_st x1 = S_TestXml) by (rewrite EX1; reflexivity).
        assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
        assert (EPq : x_p x1 = x_p x1) by reflexivity.
        clear - HMC PE ST KL PHI PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EX1 LQ QE; try pose proof alloc_ceiling_val as ACV__.
        world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *.
        assert (EP1 : x_p x1 = x_p x1) by reflexivity.
        pose proof (munch_refl [(pe_sp E - 320 - 48, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
        assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1] [(pe_sp E - 320 - 48, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
        assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_sp E - 320 - 48, pe_sp E - 320); (pe_VEP E, pe_VEP E + 312)])
          by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
        assert (EPQ : x_p x1 = q) by (rewrite EX1; reflexivity). assert (LQ1 : x_p x <= x_p x1) by (rewrite EPQ; exact LQ). clear EX1.
        (first [ pose proof (HENV) as dR_2; dand4 dR_2 as _ GLOB HOBJ HSH | pose proof HENV as (_ & GLOB & HOBJ & HSH) ]).
        (first [ pose proof (HSH) as dR_3; dand7 dR_3 as _ _ _ _ SHc SHw _ | pose proof HSH as (_ & _ & _ & _ & SHc & SHw & _) ]). fold_cl_segs. fold_aview. unfold h_vc, h_wrk in SHc, SHw.
        unfold kHighMemBeg in G2. all_app_facts.
        pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff (pe_H E) + 2608) 72 ltac:(try (generalize alloc_ceiling_val); clear - G2; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) ltac:(try (generalize alloc_ceiling_val); clear - G3; try pose proof alloc_ceiling_val as ACV__; lia)) as SHcR. rewrite SHMAX_val in SHcR.
        pose proof (shpat_sh_boundL (Clg:=Clg) (h_ff (pe_H E) + 2720) 184 ltac:(try (generalize alloc_ceiling_val); clear - G2; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) ltac:(try (generalize alloc_ceiling_val); clear - G3; try pose proof alloc_ceiling_val as ACV__; lia)) as SHwR. rewrite SHMAX_val in SHwR.
        pose proof (hff_al8 (pe_H E) 2608 HG eq_refl) as ALc. pose proof (hff_al8 (pe_H E) 2720 HG eq_refl) as ALw.
        (first [ pose proof (HOBJ) as dR_4; dand3 dR_4 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]). (first [ dex2 VC as vcpad vcrest; dand3 VC as LP1 LR1 VC | dand5 VC as vcpad vcrest LP1 LR1 VC | destruct VC as (vcpad & vcrest & LP1 & LR1 & VC) ]). (first [ dex2 WK as wkpad wkrest; dand3 WK as LP2 LR2 WK | dand5 WK as wkpad wkrest LP2 LR2 WK | destruct WK as (wkpad & wkrest & LP2 & LR2 & WK) ]).
        fold_cl_segs. fold_aview. unfold vc_cells in VC. unfold wrk_cells in WK. unfold h_vc, h_resp, h_wrk in VC, WK.
        pose proof (proj1 BASE) as EVC. unfold h_vc in EVC.
        destruct (data_shadow A1 m2 md1 _ _ AINV1 DATA) as [SHD1 D16]. fold_cl_segs. fold_aview.
        pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(try (generalize alloc_ceiling_val); clear - Dlo; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(clear; lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
        rewrite <- EPQ.
        hide_neqs. unhide DJfV.
        ago AINV1. fold_cl_segs.
        (* [comment removed for export] *)
        zstep. vchk SHV0 EzsV 4 0. zstep. zstep. zstep.
        (* [comment removed for export] *)
        prechkn SHD1 (x_p x1) 1 11 2.
        (* [comment removed for export] *)
        (first [ pose proof ((look_read rsegs E x1 _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(rewrite EPQ; exact QE))) as dR_7; dex1 dR_7 as c; dand3 dR_7 as Hnthc Hlookc RDP | pose proof ((look_read rsegs E x1 _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(rewrite EPQ; exact QE))) as dR_7; dand4 dR_7 as c Hnthc Hlookc RDP | destruct (look_read rsegs E x1 _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(rewrite EPQ; exact QE)) as (c & Hnthc & Hlookc & RDP) ]).
        pose proof (bv_unsigned_in_range _ c) as CR. change (bv_modulus 8) with 256 in CR.
        zstep. clear RDP. cbv beta. zstep. zstep. if_cases K2; zify_cond K2.
        + (* [comment removed for export] *)
           prechkn SHD1 (x_p x1) 1 11 0.
           (* [comment removed for export] *)
           zstep. vchk SHV0 EzsV 8 0. zstep. rewrite EVC.
           (* [comment removed for export] *)
           (first [ pose proof ((look_read rsegs E x1 _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(rewrite EPQ; exact QE))) as dR_8; dex1 dR_8 as c2; dand3 dR_8 as _ _ RDP2 | pose proof ((look_read rsegs E x1 _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(rewrite EPQ; exact QE))) as dR_8; dand4 dR_8 as c2 _ _ RDP2 | destruct (look_read rsegs E x1 _ DBY ltac:(try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__; lia) ltac:(rewrite EPQ; exact QE)) as (c2 & _ & _ & RDP2) ]).
           pose proof (bv_unsigned_in_range _ c2) as CR2. change (bv_modulus 8) with 256 in CR2.
           zstep. clear RDP2. cbv beta. zstep. zstep. zstep. zstep. zstep. zstep. if_cases K3; zify_cond K3.
           * (* [comment removed for export] *)
               (* [comment removed for export] *)
               zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; revert KU; rewrite (land7_of_mod8 (h_ff (pe_H E) + 2608) ltac:(clear - G2; lia) ALc); rewrite (proj2 (Z.ltb_lt 0 (h_ff (pe_H E) + 2608))) by (clear - G2; lia); clear; intros KU; vm_compute in KU; discriminate KU ].
               (* [comment removed for export] *)
               zstep. shadow_chk0 SHc 8. zstep.
               (* [comment removed for export] *)
               zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU G2; lia ].
               zstep. zstep; if_cases KU; zify_cond KU; [ clear KU | paok KU HG ].
               (* [comment removed for export] *)
               zstep. shadow_chk0 SHw 8. zstep.
               (* [comment removed for export] *)
               zstep. zstep. zstep. zstep.
               carve_frame 48%nat STK. replace (pe_sp E + -320 + -48) with (pe_sp E + -368) in * by (clear; lia). do 8 zstep.
               lazymatch goal with FRs : rw_cells _ ?mx (pe_sp E + -368) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => release_frame FRs STK (pe_sp E + -320) end.
               replace (pe_sp E + -320) with (pe_sp E - 320) in * by (clear; lia).
               (* [comment removed for export] *)
               vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
               astop AINV1 MU WM CFP. fold_cl_segs.
               eapply (KL (PST (x_p x1) S_NotXml (fupd (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) Fstate (vi_st VIA S_NotXml)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
               -- apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
                  ++ (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
               -- assumption.
               -- eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
               -- (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ1; try pose proof alloc_ceiling_val as ACV__. lia.

           * (* [comment removed for export] *)
               (* [comment removed for export] *)
               zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; revert KU; rewrite (land7_of_mod8 (h_ff (pe_H E) + 2608) ltac:(clear - G2; lia) ALc); rewrite (proj2 (Z.ltb_lt 0 (h_ff (pe_H E) + 2608))) by (clear - G2; lia); clear; intros KU; vm_compute in KU; discriminate KU ].
               (* [comment removed for export] *)
               zstep. shadow_chk0 SHc 8. zstep.
               (* [comment removed for export] *)
               zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU G2; lia ].
               zstep. zstep; if_cases KU; zify_cond KU; [ clear KU | paok KU HG ].
               (* [comment removed for export] *)
               zstep. shadow_chk0 SHw 8. zstep.
               (* [comment removed for export] *)
               zstep. zstep. zstep. zstep.
               carve_frame 48%nat STK. replace (pe_sp E + -320 + -48) with (pe_sp E + -368) in * by (clear; lia). do 8 zstep.
               lazymatch goal with FRs : rw_cells _ ?mx (pe_sp E + -368) _ |- evt _ _ (MS _ _ _ _ _ ?mx _) => release_frame FRs STK (pe_sp E + -320) end.
               replace (pe_sp E + -320) with (pe_sp E - 320) in * by (clear; lia).
               (* [comment removed for export] *)
               vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
               astop AINV1 MU WM CFP. fold_cl_segs.
               eapply (KL (PST (x_p x1) S_NotXml (fupd (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) Fstate (vi_st VIA S_NotXml)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
               -- apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
                  ++ (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
               -- assumption.
               -- eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
               -- (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ1; try pose proof alloc_ceiling_val as ACV__. lia.

        + (* [comment removed for export] *)
           zstep. zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU QE EPQ EE Dhi ACV; lia ].
           vrechk SHV0 EzsV (pe_VEP E + 64) 8 0. zstep. zstep. zstep. zstep. zstep.
           astop AINV1 MU WM CFP. fold_cl_segs.
           eapply (KL (PST (x_p x1 + 1) S_StartTag (fupd (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) Fstate (vi_st VIA S_StartTag)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
           * apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
              -- (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP; try pose proof alloc_ceiling_val as ACV__. lia.
              -- (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - QE EPQ; try pose proof alloc_ceiling_val as ACV__. lia.
              -- (* [comment removed for export] *) world_close PE0 AINV1 HFR MU WM WZ.
              -- (* [comment removed for export] *) world_close PE0 AINV1 HFR MU WM WZ.
              -- (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
           * assumption.
           * eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
           * (* [comment removed for export] *) psimp. intros _. split; [| discriminate]. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ1; try pose proof alloc_ceiling_val as ACV__. lia.
 }
      (* [comment removed for export] *)
      zstep. zstep. zstep. if_cases K4; zify_cond K4.
      { eapply (IH (q + 1)); [try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - K4 Hk QE; try pose proof alloc_ceiling_val as ACV__; lia]. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep. zstep. zstep.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MUh. pose proof (wmono_refl rsegs (aview A m)) as WMh.
      assert (PIe : pinv E (PST (pe_e E) S_TestXml (x_v x) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)) A (aview A m)).
      { apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUh WMh WZ.
        - (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP PLT; try pose proof alloc_ceiling_val as ACV__. lia.
        - (* [comment removed for export] *) revert OUT PLT. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
        - (* [comment removed for export] *) revert VA PLT. clear. cbn [x_va x_v x_p x_vv]. destruct (x_va x); [| intros X _; exact X]. ((first [ intro dR_11; dand5 dR_11 as H1 H2 H3 H4 H5 | intros (H1 & H2 & H3 & H4 & H5) ]); intros PLT). refine (conj H1 (conj H2 (conj H3 (conj _ H5)))). lia.
        - (* [comment removed for export] *) revert VI PLT. clear. cbn [x_vi x_va x_v x_p x_vv]. destruct (x_vi x); [| intros X _; exact X]. ((first [ intro dR_12; dand7 dR_12 as H1 H2 H3 H4 H5 H6 H7 | intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) ]); intros PLT). refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj H6 H7)))))). lia. }
      clear IH MUh WMh.
      astop0 AINV.
      eapply (mark_call HMC E _ A _ _ T (pe_e E) (pe_e E) 0 0x8c044);
        [ exact PE | exact PIe | assumption | eapply amd_frame_sbm_r; [exact MDF | exact SBM]
        | clear; cbn [x_p]; lia | cbn [x_p]; clear; lia | left; reflexivity | clear; lia | reflexivity
        | cbn [x_st]; intros [X|X]; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (ST1 : x_st x1 = S_TestXml) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EPq : x_p x1 = x_p x1) by reflexivity.
      clear - HMC PE ST KL PHI PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EX1; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *.
      assert (EP1 : x_p x1 = x_p x1) by reflexivity.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1] [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      assert (EPE : x_p x1 = pe_e E) by (rewrite EX1; reflexivity). clear EX1.
      hide_neqs.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0. zstep. zstep. zstep. zstep. zstep. zstep.
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (pe_e E) S_TestXml (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
         + (* [comment removed for export] *) rewrite <- EPE. exact VERP.
         + (* [comment removed for export] *) revert OUT. rewrite EPE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
         + (* [comment removed for export] *) rewrite <- EPE. pinv_close PE0 AINV1 HFR MU WM WZ.
         + (* [comment removed for export] *) rewrite <- EPE. pinv_close PE0 AINV1 HFR MU WM WZ.
         + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      - (* [comment removed for export] *) psimp. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia.
 }
    (* [comment removed for export] *)
    zstep; if_cases K0; zify_cond K0; try (exfalso; try (generalize alloc_ceiling_val); clear - K0 PLT; try pose proof alloc_ceiling_val as ACV__; lia); [].
    zstep.
    eapply (LOOP (Z.to_nat (pe_e E - x_p x)) (x_p x)); [try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT].
  Qed.
End S.
End A_PHobr.

Module A_PHucc.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl Require A_PKit2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_La0bg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PDefs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zl.A_PKit2.A_PMark.
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaMunch.
Local Ltac hot_lia_prev := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietvxh.dlia_vk.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@VEPlo; @UB; @Dlo; @TAG; @WL; @LQ; @DLEN; @FRB; @G2; @Hk; @ACV; @EE; @HUR; @SZ; @SR; @VERP; @NN; @KS; @Ha; @QE; @PLT; @VEPhi; @H; @DJfV; @K3; @OUT; @H2; @H3; @Hj; @PLEc; @ACV__; @K1; @K0; @KU; @UBR; @UBR2; @PLT0; @Hz; @NEQ3; @HUR'])).
Ltac hot_lia_full := first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaMunch.munch_tier ltac:(hot_lia_prev) | hot_lia_prev ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2 DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)



(* [comment removed for export] *)
Definition until_byte (U j : Z) : Z :=
  if U =? LIT_arrow then (if j =? 0 then 45 else if j =? 1 then 45 else if j =? 2 then 62 else 0)
  else (if j =? 0 then 93 else if j =? 1 then 93 else if j =? 2 then 62 else 0).

Lemma until_read : forall m U j, mem_inv rsegs m -> (U = LIT_arrow \/ U = LIT_cdata_end) -> 0 <= j <= 3 ->
  ov_read_bytes rsegs m (wa (U + j)) 1 = Some [Z_to_bv 8 (until_byte U j)].
Proof.
  intros m U j MI HU Hj.
  assert (B : bytes_at rsegs m U [Z_to_bv 8 (until_byte U 0); Z_to_bv 8 (until_byte U 1); Z_to_bv 8 (until_byte U 2); Z_to_bv 8 (until_byte U 3)]).
  { apply (ro_bytes_at rsegs m); [exact MI| | |].
    - destruct HU as [-> | ->]; unfold LIT_arrow, LIT_cdata_end; cbn; lia.
    - cbn [length]. destruct HU as [-> | ->]; unfold LIT_arrow, LIT_cdata_end; cbn; lia.
    - apply ro_bytes_b_sound. destruct HU as [-> | ->]; vm_compute; reflexivity. }
  eapply (u8ro_read rsegs m U _ j); [exact B| | lia| reflexivity].
  assert (X : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
  destruct X as [-> |[-> |[-> | ->]]]; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma until_byte_3 : forall U, until_byte U 3 = 0.
Proof. intros U. unfold until_byte. destruct (U =? LIT_arrow); reflexivity. Qed.
Lemma until_byte_range : forall U j, 0 <= until_byte U j < 256.
Proof.
  intros U j. unfold until_byte.
  destruct (U =? LIT_arrow); destruct (j =? 0); destruct (j =? 1); destruct (j =? 2); lia.
Qed.
Lemma unsigned_lit8 : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. cbn. lia. Qed.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma until_shadow : forall v U, consts_hold LPA v -> (U = LIT_arrow \/ U = LIT_cdata_end) ->
  bytes_at rsegs v (sh U) (shpat 4) /\ U mod 8 = 0 /\ 0x22ec0 <= U <= 0x22fa0 /\ (0 <= sh U /\ sh U + Z.of_nat (length (shpat 4)) <= 17594064011264).
Proof.
  intros v U CH HU. destruct HU as [-> | ->]; unfold LIT_arrow, LIT_cdata_end; cbn [vi_arrow vi_cdata_end VIA].
  - split; [apply (global_shadow_pat v 0x22ec0 4 32 CH); gdesc_in|]. split; [reflexivity|]. split; [lia| change (Z.of_nat (length (shpat 4))) with 1; unfold sh; rewrite kShadowOffset_val; change (0x22ec0 / 8) with 17880; lia].
  - split; [apply (global_shadow_pat v 0x22fa0 4 32 CH); gdesc_in|]. split; [reflexivity|]. split; [lia| change (Z.of_nat (length (shpat 4))) with 1; unfold sh; rewrite kShadowOffset_val; change (0x22fa0 / 8) with 17908; lia].
Qed.

End CEIL.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HMC : vep_mark_common_stmt.

  #[using="HMC"] Lemma PH_Until : handler_stmt S_Until.
  Proof.
    intros E x A m md T. intros until t6. intros PE PI AINV MDF ST PLT KL KX.
    pose proof PLT as PLT0.
    handler_prologue PE PI AINV ST.
    pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A m)) as MU. pose proof (wmono_refl rsegs (aview A m)) as WM.
    assert (WZ : wzone E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
    assert (CFP : client_fp LPA A (aview A m) [(pe_VEP E, pe_VEP E + 312)])
      by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
    assert (PHI : phi E x = 16 * (pe_e E - x_p x) + 1) by (unfold phi, rank; rewrite ST; reflexivity).
    destruct (UNTL eq_refl) as (HU & UP & US).
    destruct (data_shadow A m md _ _ AINV DATA) as [SHD D16]. fold_cl_segs. fold_aview.
    pose proof (shpat_sh_boundL (Clg:=Clg) (pe_DATA E) (Z.of_nat (length (pe_inp E))) ltac:(lia) ltac:(lia) Dhi) as SHDB. rewrite SHMAX_val in SHDB.
    destruct (until_shadow _ (x_v x Funtil) (consts_hold_ainv LPA A m md AINV) HU) as (SHU & U8 & UB & SHUB). fold_cl_segs. fold_aview.
    (* [comment removed for export] *)
    assert (TAIL : forall (xc : pst) (mc : mem) (mdc : Model) (ra' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' : word),
      pinv E xc A (aview A mc) -> ainv A mc mdc -> amd_frame (pe_md0 E) mdc ->
      (x_st xc = S_Until \/ x_st xc = S_NxtTag) -> (x_p xc < pe_e E -> phi E xc < phi E x) ->
      srealizes rsegs (mkCfg (loop_ms E 0x8d3d0 (x_p xc) ra' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' mc) mdc) T).
    { intros until t6'. intros PIc AINVc MDFc STc PHIc.
      clear - HMC PE KL PIc AINVc MDFc STc PHIc; try pose proof alloc_ceiling_val as ACV__.
      assert (NMB : x_st xc <> S_MatchBuf) by (destruct STc as [X|X]; rewrite X; discriminate).
      pose proof PIc as PIc0. pose proof (pi_pe _ _ _ _ PIc) as PLEc.
      world_open PE PIc AINVc. unfold loop_ms, S9, T0. rewrite EFP in *.
      hide_neqs.
      ago AINVc. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. if_cases K0; zify_cond K0.
      { astop0 AINVc.
        eapply (KL xc A _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
        intros H. split; [exact (PHIc H)| exact NMB]. }
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. destruct B_rm as [RM|RM]; rewrite RM, sx32_small by (clear; lia).
      all: zstep; if_cases K1; zify_cond K1; try (exfalso; try (generalize alloc_ceiling_val); clear - K1; try pose proof alloc_ceiling_val as ACV__; rewrite ?unsigned_lit in K1 by (clear; lia); lia); clear K1.
      2:{ (* [comment removed for export] *)
          zstep. zstep. zstep. zstep.
          astop0 AINVc.
          eapply (KL xc A _ _); [exact PIc0| assumption| eapply amd_frame_sbm_r; [exact MDFc | exact SBM]|].
          intros H. exfalso. try (generalize alloc_ceiling_val); clear - H K0; try pose proof alloc_ceiling_val as ACV__. lia. }
      (* [comment removed for export] *)
      zstep. zstep. zstep. zstep.
      astop0 AINVc.
      eapply (mark_call HMC E xc A _ _ T (x_p xc) (x_p xc) 0 0x8d404);
        [ exact PE | exact PIc0 | assumption | eapply amd_frame_sbm_r; [exact MDFc | exact SBM]
        | clear; lia | exact PLEc | left; reflexivity | clear; lia | reflexivity
        | intros [X|X]; destruct STc as [Y|Y]; rewrite Y in X; discriminate X | ].
      intros t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' A1 m2 md1 v1 vv1 x1 EX1 PI1 AINV1 MDF1 VK VERP1 LM1 OP1 CRC1 CRCP1.
      assert (ST1 : x_st x1 = x_st xc) by (rewrite EX1; reflexivity).
      assert (EV1 : x_v x1 = v1) by (rewrite EX1; reflexivity).
      assert (EP1 : x_p x1 = x_p xc) by (rewrite EX1; reflexivity).
      assert (EPc : x_p x1 = pe_e E) by (rewrite EP1; exact K0).
      assert (NMB1 : x_st x1 <> S_MatchBuf) by (rewrite ST1; exact NMB).
      clear - HMC PE KL PI1 AINV1 MDF1 VK VERP1 LM1 OP1 ST1 EV1 EP1 EPc NMB1; try pose proof alloc_ceiling_val as ACV__.
      world_open PE PI1 AINV1. unfold call_ms. cbv zeta. rewrite EFP in *. rewrite <- EP1.
      pose proof (munch_refl [(pe_VEP E, pe_VEP E + 312)] (aview A1 m2)) as MU. pose proof (wmono_refl rsegs (aview A1 m2)) as WM.
      assert (WZ : wzone E A1 [pe_S E; vb_buf (x_vv x1); pe_DATA E; x_v x1 Fattr_vsb; oabuf x1; x_v x1 Finclude_src; oibuf x1]
                           [(pe_VEP E, pe_VEP E + 312)]) by wzone_tac.
      assert (CFP : client_fp LPA A1 (aview A1 m2) [(pe_VEP E, pe_VEP E + 312)])
        by (eapply wzone_client_fp; [exact PE| exact HFR| exact STK| unfold pframe; cbv zeta; exact FR| exact WZ]).
      hide_neqs.
      ago AINV1. fold_cl_segs.
      (* [comment removed for export] *)
      zstep. vchk SHV0 EzsV 4 0.
      zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
      astop AINV1 MU WM CFP. fold_cl_segs.
      eapply (KL (PST (x_p x1) (x_st x1) (fupd (x_v x1) Fnm_verbatim (bv_unsigned (sx32 (Z_to_bv 64 (x_v x1 Fnm_verbatim))) + 1)) (x_tag x1) (x_q x1) (x_vv x1) (x_va x1) (x_vi x1)) A1 _ _).
      - apply Build_pinv; psimp; pinv_close PE0 AINV1 HFR MU WM WZ.
        all: rewrite ?ST1; try assumption.
        + exact (conj DELIM1 DELIM2).
        + (* [comment removed for export] *) cf_stores CF MU PE0 STK FR. left; left. unfold blk. lia.
      - assumption.
      - eapply amd_frame_sbm_r; [exact MDF1 | exact SBM].
      - psimp. rewrite EPc. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia. }
    (* [comment removed for export] *)
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ _ _) _) _ => idtac end.
    hide_neqs.
    ago AINV. fold_cl_segs.
    lazymatch goal with |- evt _ ?P _ =>
    assert (ULOOP : forall (k : nat) (q u : Z) (ra' t1' t2' s1' a0' a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' : word) (mc : mem),
      munch [(pe_VEP E, pe_VEP E + 312)] (aview A m) mc -> wmono rsegs (aview A m) mc -> mem_inv rsegs mc ->
      rw_cells rsegs mc (pe_VEP E) (vep_cells (fupd (fupd (x_v x) Funtil_p u) Fstate (stA (x_st x))) (x_tag x) (x_q x)) ->
      rw_cells rsegs mc (pe_sp E - 320) (pframe E j0 j8) ->
      bytes_at rsegs mc (pe_DATA E) (pe_inp E) -> stk rsegs mc (pe_lo E) (pe_sp E - 320) ->
      bytes_at rsegs mc (sh (pe_VEP E)) zsV -> bytes_at rsegs mc (sh (pe_DATA E)) (shpat (Z.of_nat (length (pe_inp E)))) ->
      bytes_at rsegs mc (sh (x_v x Funtil)) (shpat 4) ->
      q + Z.of_nat k = pe_e E -> x_p x <= q -> q < pe_e E -> x_v x Funtil <= u <= x_v x Funtil + 2 ->
      evt rsegs P (loop_ms E 0x8b8f0 (q + 1) ra' t1' t2' s1' a0' (Z_to_bv 64 q) a2' a3' a4' a5' a6' s6' s10' s11' t3' t4' t5' t6' mc))
    end.
    { induction k as [|k IH]; intros until mc; intros MUc WMc MIc VEPCc FRc DBYc STKc SHVc SHDc SHUc Hk LQ QE HUR.
      { exfalso. try (generalize alloc_ceiling_val); clear - Hk QE; try pose proof alloc_ceiling_val as ACV__. lia. }
      unfold loop_ms, S9, T0. rewrite EFP.
      clear VEPC FR DBY STK MI SHV0 SHD SHU MU WM.
      unfold vep_cells in VEPCc. psimp_in VEPCc. unfold pframe in FRc. cbv zeta in FRc.
      (* [comment removed for export] *)
      zstep. zstep. zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU VERP LQ Dlo; lia ].
      (* [comment removed for export] *)
      zstep. vchk SHVc EzsV 8 0. zstep.
      (* [comment removed for export] *)
      zstep. zstep. zstep; if_cases KU; zify_cond KU; [ clear KU | exfalso; clear - KU HUR UB; lia ].
      (* [comment removed for export] *)
      shadow_chk SHDc 1 16.
      (* [comment removed for export] *)
      vrechk SHVc EzsV (pe_VEP E + 176) 8 2.
      (* [comment removed for export] *)
      destruct (payload_read rsegs E _ q DBYc ltac:(try (generalize alloc_ceiling_val); clear - LQ VERP; try pose proof alloc_ceiling_val as ACV__; lia) QE) as (b & Hnth & RDP).
      pose proof (bv_unsigned_in_range _ b) as BR. change (bv_modulus 8) with 256 in BR.
      zstep. clear RDP. cbv beta.
      (* [comment removed for export] *)
      zstep.
      (* [comment removed for export] *)
      shadow_chk SHUc 1 16.
      (* [comment removed for export] *)
      lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
        pose proof (until_read mcur (x_v x Funtil) (u - x_v x Funtil) MIx HU ltac:(try (generalize alloc_ceiling_val); clear - HUR; try pose proof alloc_ceiling_val as ACV__; lia)) as RDU end.
      replace (wa (x_v x Funtil + (u - x_v x Funtil))) with (Z_to_bv 64 u) in RDU by (unfold wa; f_equal; clear; lia).
      pose proof (until_byte_range (x_v x Funtil) (u - x_v x Funtil)) as UBR.
      remember (until_byte (x_v x Funtil) (u - x_v x Funtil)) as ub eqn:Eub in RDU, UBR.
      zstep. clear RDU. cbv beta. rewrite (unsigned_lit8 ub UBR).
      (* [comment removed for export] *)
      zstep. if_cases K1; zify_cond K1.
      - (* [comment removed for export] *)
        vchk SHVc EzsV 8 0. vrechk SHVc EzsV (pe_VEP E + 176) 8 0. zstep. zstep.
        (* [comment removed for export] *)
        zstep. zstep. zstep. if_cases K3; zify_cond K3.
        + replace (q + 1 + 1) with (q + 1 + 1) by reflexivity. try replace (q + 2) with (q + 1 + 1) by (clear; lia).
          lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
            eapply (IH (q + 1) (x_v x Funtil)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; exact VEPCc| exact FRc| exact DBYc| exact STKc
                                  | exact SHVc| exact SHDc| exact SHUc| try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - K3 Hk QE; try pose proof alloc_ceiling_val as ACV__; lia| clear; lia] end.
        + (* [comment removed for export] *)
          zstep. zstep. zstep.
          astop AINV MUc WMc CFP. fold_cl_segs.
          set (xc := PST (pe_e E) S_Until (fupd (x_v x) Funtil_p (x_v x Funtil)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIc : pinv E xc A (aview A mr)) end.
          { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUc WMc WZ.
            + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ QE; try pose proof alloc_ceiling_val as ACV__. lia.
            + (* [comment removed for export] *) intros _. refine (conj HU (conj _ US)). first [try (generalize alloc_ceiling_val); clear - HUR'; try pose proof alloc_ceiling_val as ACV__; lia | try (generalize alloc_ceiling_val); clear - HUR; try pose proof alloc_ceiling_val as ACV__; lia].
            + (* [comment removed for export] *) revert OUT LQ QE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
            + (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
            + (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
            + (* [comment removed for export] *) cf_stores CF MUc PE0 STKc FRc. left; left. unfold blk. lia. }
          eapply (TAIL xc); [exact PIc| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| left; reflexivity|].
          subst xc. cbn [x_p]. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia.
      - (* [comment removed for export] *)
        shadow_chk SHUc 1 12.
        lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
          pose proof (until_read mcur (x_v x Funtil) (u + 1 - x_v x Funtil) MIx HU ltac:(try (generalize alloc_ceiling_val); clear - HUR; try pose proof alloc_ceiling_val as ACV__; lia)) as RDU2 end.
        replace (wa (x_v x Funtil + (u + 1 - x_v x Funtil))) with (Z_to_bv 64 (u + 1)) in RDU2 by (unfold wa; f_equal; clear; lia).
        pose proof (until_byte_range (x_v x Funtil) (u + 1 - x_v x Funtil)) as UBR2.
        remember (until_byte (x_v x Funtil) (u + 1 - x_v x Funtil)) as ub2 eqn:Eub2 in RDU2, UBR2.
        zstep. clear RDU2. cbv beta. rewrite (unsigned_lit8 ub2 UBR2).
        zstep. if_cases K2; zify_cond K2.
        + (* [comment removed for export] *)
          assert (HUR' : x_v x Funtil <= u + 1 <= x_v x Funtil + 2).
          { destruct (Z.eq_dec (u + 1 - x_v x Funtil) 3) as [EQ3|NEQ3]; [| try (generalize alloc_ceiling_val); clear - HUR NEQ3; try pose proof alloc_ceiling_val as ACV__; lia].
            exfalso. apply K2. rewrite Eub2, EQ3. apply until_byte_3. }
          zstep. zstep. zstep. if_cases K3; zify_cond K3.
          * try replace (q + 2) with (q + 1 + 1) by (clear; lia).
            lazymatch goal with MIx : mem_inv _ ?mcur |- evt _ _ (MS _ _ _ _ _ ?mcur _) =>
              eapply (IH (q + 1) (u + 1)); [exact MUc| exact WMc| exact MIx| unfold vep_cells; psimp; exact VEPCc| exact FRc| exact DBYc| exact STKc
                                          | exact SHVc| exact SHDc| exact SHUc| try (generalize alloc_ceiling_val); clear - Hk; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__; lia| try (generalize alloc_ceiling_val); clear - K3 Hk QE; try pose proof alloc_ceiling_val as ACV__; lia| exact HUR'] end.
          * (* [comment removed for export] *)
            zstep. zstep. zstep.
            astop AINV MUc WMc CFP. fold_cl_segs.
            set (xc := PST (pe_e E) S_Until (fupd (x_v x) Funtil_p (u + 1)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
            lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIc : pinv E xc A (aview A mr)) end.
            { subst xc. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUc WMc WZ.
              + (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ QE; try pose proof alloc_ceiling_val as ACV__. lia.
              + (* [comment removed for export] *) intros _. refine (conj HU (conj _ US)). first [try (generalize alloc_ceiling_val); clear - HUR'; try pose proof alloc_ceiling_val as ACV__; lia | try (generalize alloc_ceiling_val); clear - HUR; try pose proof alloc_ceiling_val as ACV__; lia].
              + (* [comment removed for export] *) revert OUT LQ QE. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
              + (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
              + (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
              + (* [comment removed for export] *) cf_stores CF MUc PE0 STKc FRc. left; left. unfold blk. lia. }
            eapply (TAIL xc); [exact PIc| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| left; reflexivity|].
            subst xc. cbn [x_p]. intros H. exfalso. try (generalize alloc_ceiling_val); clear - H; try pose proof alloc_ceiling_val as ACV__. lia.
        + (* [comment removed for export] *)
          zstep. zstep. vchk SHVc EzsV 8 0. vrechk SHVc EzsV (pe_VEP E + 64) 8 0.
          zstep. zstep. rewrite US. zstep. zstep. zstep.
          astop AINV MUc WMc CFP. fold_cl_segs.
          set (xg := PST (q + 1) S_NxtTag (fupd (fupd (x_v x) Funtil_p (u + 1)) Fstate (vi_st VIA S_NxtTag)) (x_tag x) (x_q x) (x_vv x) (x_va x) (x_vi x)).
          lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?mr _) _) _ => assert (PIg : pinv E xg A (aview A mr)) end.
          { subst xg. apply Build_pinv; psimp; pinv_close PE0 AINV HFR MUc WMc WZ.
            -- (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - VERP LQ; try pose proof alloc_ceiling_val as ACV__. lia.
            -- (* [comment removed for export] *) try (generalize alloc_ceiling_val); clear - QE; try pose proof alloc_ceiling_val as ACV__. lia.
            -- (* [comment removed for export] *) revert OUT LQ. unfold oacost, oicost. cbn [x_va x_vi x_st x_p x_vv]. clear. intros; lia.
            -- (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
            -- (* [comment removed for export] *) world_close PE0 AINV HFR MUc WMc WZ.
            -- (* [comment removed for export] *) cf_stores CF MUc PE0 STKc FRc. left; left. unfold blk. lia. }
          eapply (TAIL xg); [exact PIg| assumption| eapply amd_frame_sbm_r; [exact MDF | exact SBM]| right; reflexivity|].
          subst xg. intros _. rewrite PHI. unfold phi, rank; psimp. try (generalize alloc_ceiling_val); clear - LQ; try pose proof alloc_ceiling_val as ACV__. lia. }
    (* [comment removed for export] *)
    zstep; if_cases K0; zify_cond K0; try (exfalso; try (generalize alloc_ceiling_val); clear - K0 PLT; try pose proof alloc_ceiling_val as ACV__; lia); [].
    zstep. zstep.
    eapply (ULOOP (Z.to_nat (pe_e E - x_p x)) (x_p x) (x_v x Funtil_p));
      [exact MU| exact WM| exact MI| unfold vep_cells; psimp; exact VEPC| exact FR| exact DBY| exact STK
      | exact SHV0| exact SHD| exact SHU
      | try (generalize alloc_ceiling_val); clear - PLT; try pose proof alloc_ceiling_val as ACV__; rewrite Z2Nat.id by lia; lia| clear; lia| exact PLT| exact UP].
  Qed.
End S.
End A_PHucc.

   (* [comment removed for export] *)
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.

Local Tactic Notation "klia" ne_hyp_list(hs) := try (generalize alloc_ceiling_val); clear - hs; try pose proof alloc_ceiling_val; lia.

Section S.
  Context {Clg : Ceiling}.
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Hypothesis HDS : VSB_destroy_stmt.

  Lemma destroy_attr_fin : forall (E : penv) (x : pst) (A : AS) (m m2 : mem) (md md2 : Model) (T : TSet) (ret : Z)
      (W : list (Z * Z)) (v' : vep) (ya yf : vsb_rec) (fin : bool) (fj0 fj8 : word)
      (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 : word) (ps : Z),
    penv_ok E -> pinv E x A (aview A m) -> ainv A m md -> ainv A m2 md2 ->
    munch W (aview A m) (aview A m2) -> wmono rsegs (aview A m) (aview A m2) ->
    wzonex E A [pe_S E; vb_buf (x_vv x); pe_DATA E; x_v x Finclude_src; oibuf x] W ->
    henv_ok LPA VIA (pe_H E) A (aview A m2) ->
    mem_inv rsegs (aview A m2) -> stk rsegs (aview A m2) (pe_lo E) (pe_fp E) -> rw_cells rsegs (aview A m2) (pe_fp E) (pframe E fj0 fj8) ->
    rw_cells rsegs (aview A m2) (pe_VEP E) (vep_cells v' (x_tag x) (x_q x)) ->
    v' Fattr_vsb = x_v x Fattr_vsb -> v' Finclude_src = x_v x Finclude_src ->
    x_va x = Some ya -> vsb_obj LPA A (aview A m2) (x_v x Fattr_vsb) yf fin -> vb_buf yf = vb_buf ya -> vb_size yf = vb_size ya ->
    0 <= ret < 2^64 -> ret mod 2 = 0 ->
    cframe LPA (owned (pe_A0 E)) (owned A) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
           (parse_new v' (x_vv x) (x_va x) (x_vio x)) (pe_v0 E) (aview A m2) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m1 : mem) (md1 : Model),
        ainv A1 m1 md1 -> mem_inv rsegs (aview A1 m1) -> amd_frame md2 md1 ->
        stk rsegs (aview A1 m1) (pe_lo E) (pe_fp E) -> rw_cells rsegs (aview A1 m1) (pe_fp E) (pframe E fj0 fj8) ->
        rw_cells rsegs (aview A1 m1) (pe_VEP E) (vep_cells (fupd v' Fattr_vsb 0) (x_tag x) (x_q x)) ->
        henv_ok LPA VIA (pe_H E) A1 (aview A1 m1) -> data_obj LPA A1 (aview A1 m1) (pe_DATA E) (pe_inp E) ->
        vsb_obj LPA A1 (aview A1 m1) (pe_S E) (x_vv x) false ->
        a_live A1 (pe_wa E) = Some 40 -> a_live A1 (pe_VEP E) = Some 312 ->
        vi_world E (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A1 (aview A1 m1) ->
        stack_shadow LPA (aview A1 m1) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64) ->
        a_livebytes A1 = a_livebytes A - 40 - vb_size ya -> a_nlive A1 = a_nlive A - 2 -> a_tinycred A1 = a_tinycred A ->
        a_seccred A1 = a_seccred A -> a_primcred A1 = a_primcred A (* [comment removed for export] *) -> frames_same A A1 ->
        (forall p k, a_live (pe_A0 E) p = Some k -> p <> pe_b E -> a_live A1 p = Some k) ->
        cframe LPA (owned (pe_A0 E)) (owned A1) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
               (parse_new (fupd v' Fattr_vsb 0) (x_vv x) None (x_vio x)) (pe_v0 E) (aview A1 m1) ->
        srealizes rsegs (mkCfg (call_ms E ret ps (Z_to_bv 64 ret) t0' t1' t2' s1 a0' a1' a2' a3' a4' a5' a6' a7' s6 s10 s11 t3' t4' t5' t6' m1) md1) T) ->
    srealizes rsegs (mkCfg (call_ms E VSB_destroy_entry ps (Z_to_bv 64 ret) t0 t1 t2 s1
                               (Z_to_bv 64 (pe_VEP E + 224)) a1 a2 a3 a4 a5 a6 a7 s6 s10 s11 t3 t4 t5 t6 m2) md2) T.
  Proof.
    intros until ps. intros PE PI AINV0 AINV2 MU WM WZ HENV2 MI2 STK2 FR2 VEPC2 EAV EIS EVA AOBJ2 EYB EYS RR RET CF2 K.
    pose proof PI as PI0.
    world_open PE PI AINV0. unfold call_ms in K |- *. cbv zeta in K |- *. rewrite EFP in *.
    clear VEPC FR STK MI SHV0.
    (* [comment removed for export] *)
    assert (VSBO2 : vsb_obj LPA A (aview A m2) (pe_S E) (x_vv x) false)
      by (eapply (vsb_obj_storesx _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); [in_list| in_list| exact VSBO]).
    assert (DATA2 : data_obj LPA A (aview A m2) (pe_DATA E) (pe_inp E))
      by (eapply (data_obj_storesx _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); [in_list| exact DATA]).
    assert (SS2 : stack_shadow LPA (aview A m2) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64))
      by (eapply (stack_shadow_storesx _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); exact SS).
    rewrite EVA in VA. (first [ dand5 VA as ANZ AOBJ0 ASZ ALEN AAP | destruct VA as (ANZ & AOBJ0 & ASZ & ALEN & AAP) ]).
    (first [ pose proof (AOBJ0) as dR_2; dand5 dR_2 as _ _ LAS0 LAB0 _ | pose proof AOBJ0 as (_ & _ & LAS0 & LAB0 & _) ]).
    assert (VI2 : match x_vi x with None => x_v x Finclude_src = 0 | Some yi =>
                    x_v x Finclude_src <> 0 /\ vsb_obj LPA A (aview A m2) (x_v x Finclude_src) yi true /\ vb_error yi = 0 /\
                    vb_size yi <= vb_len yi + 4096 /\ vb_len yi <= x_p x - pe_DATA E /\
                    vsb_apart (x_v x Finclude_src) yi [pe_VEP E; pe_wa E; pe_DATA E; pe_S E; vb_buf (x_vv x)] end).
    { destruct (x_vi x) as [yi|] eqn:EVI; [| exact VI]. (first [ dand7 VI as I1 I2 I3 I4 I5 I6 _ | destruct VI as (I1 & I2 & I3 & I4 & I5 & I6 & _) ]).
      refine (conj I1 (conj _ (conj I3 (conj I4 (conj I5 I6))))).
      eapply (vsb_obj_storesx _ _ _ _ _ _ _ PE0 AINV0 HFR MU WM WZ); [in_list| in_list| exact I2]. }
    clear VSBO DATA HENV SS AOBJ0 VI.
    (first [ pose proof (AOBJ2) as dR_4; dand6 dR_4 as _ _ LAS LAB ASB _ | pose proof AOBJ2 as (_ & _ & LAS & LAB & ASB & _) ]). try rewrite EYB in LAB; try rewrite EYS in LAB; try rewrite EYB in ASB; try rewrite EYS in ASB.
    unfold oabuf in *. rewrite ?EVA in *. cbn [oabuf x_va] in D_ABV, D_ABS, D_ABB, D_ABD, D_ABW, D_AA, D_AI.
    pose proof (as_live_disjoint LPA A _ _ _ _ _ _ AINV0 LAS LVEP D_AV) as DXS.
    pose proof (as_live_disjoint LPA A _ _ _ _ _ _ AINV0 LAB LVEP D_ABV) as DXB.
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV0 LAS)) as dR_5; dand5 dR_5 as _ _ SAlo SAhi _ | destruct (live_geomP LPA _ _ _ _ _ AINV0 LAS) as (_ & _ & SAlo & SAhi & _) ]).
    (first [ pose proof ((live_geomP LPA _ _ _ _ _ AINV0 LAB)) as dR_6; dand5 dR_6 as B0 _ BAlo BAhi _ | destruct (live_geomP LPA _ _ _ _ _ AINV0 LAB) as (B0 & _ & BAlo & BAhi & _) ]).
    unfold kHighMemBeg in SAlo, BAlo. all_app_facts.
    (* [comment removed for export] *)
    rewrite vep_cells_split_attr in VEPC2. rewrite EAV in VEPC2.
    lazymatch type of VEPC2 with rw_cells _ _ _ (_ ++ ?mid ++ ?post) =>
      destruct (proj1 (rw_cells_app rsegs _ (pe_VEP E) (vep_pre36 v' (x_q x)) (mid ++ post)) VEPC2) as [VPRE V3] end.
    clear VEPC2. rewrite vep_pre36_size in V3. change (Z.of_nat 224) with 224 in V3.
    lazymatch type of V3 with rw_cells _ _ _ (?mid ++ ?post) =>
      destruct (proj1 (rw_cells_app rsegs _ (pe_VEP E + 224) mid post) V3) as [VMID VPOST] end.
    clear V3. cbn [cells_size csize Nat.add] in VPOST. replace (pe_VEP E + 224 + Z.of_nat 8) with (pe_VEP E + 232) in VPOST by (clear; lia).
    assert (W0 : 0 <= 8224) by (clear; lia).
    eapply (HDS _ _ _ _ t0 t1 t2 _ s1 _ a1 a2 a3 a4 a5 a6 a7 _ _ _ s6 _ _ _ _ s10 s11 t3 t4 t5 t6 _ _ _ _ A (pe_VEP E + 224) (x_v x Fattr_vsb) yf fin (pe_lo E) T);
      [ exact AINV2 | exact MI2 | reflexivity | exact VMID
      | rewrite EYB; eapply cobj_block; [exact LVEP| cbn; intros [X|[X|[]]]; [exact (D_AV X)| exact (D_ABV X)]| klia VEPlo| klia VEPlo]
      | try (generalize alloc_ceiling_val); clear - VEP16; try pose proof alloc_ceiling_val; Z.div_mod_to_equations; lia | klia VEPhi
      | exact AOBJ2 | reflexivity
      | rewrite unsigned_lit by (klia FRB); rewrite Zminus_mod, SP16; reflexivity
      | rewrite unsigned_lit by (klia FRB); exact STK2 | exact CEIL
      | rewrite unsigned_lit by (klia FRB); rewrite DESTROY_STACK_val; klia LOP | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m1 md1. cbv zeta.
    intros AINV1 MI1 MDF1 FSA LB1 TC1 NL1 SCC1 PCC1 STK1 PS0 DEADS DEADB LQ CF1.   (* [comment removed for export] *)
    rewrite unsigned_lit in STK1, CF1 by (klia FRB). rewrite DESTROY_STACK_val in CF1.
    try rewrite EYB in CF1; try rewrite EYS in CF1; try rewrite EYB in LQ; try rewrite EYB in DEADB; try rewrite EYS in LB1.
    rewrite (ret_pc_even ret RR RET).
    pose proof (frames_same_fs A A1 FSA) as FS.
    assert (WIN : alloc_ceiling <= pe_sp E - 320 - 8224) by (klia LOP CEIL).
    (* [comment removed for export] *)
    assert (LK : forall p k, a_live A p = Some k -> p <> x_v x Fattr_vsb -> p <> vb_buf ya -> a_live A1 p = Some k)
      by (intros p k Hp N1 N2; rewrite (LQ p N1 N2); exact Hp).
    assert (LVEP1 : a_live A1 (pe_VEP E) = Some 312) by (apply (LK _ _ LVEP); [exact (not_eq_sym D_AV)| exact (not_eq_sym D_ABV)]).
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40) by (apply (LK _ _ WAL); [exact (not_eq_sym D_AW)| exact (not_eq_sym D_ABW)]).
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))) by (apply (LK _ _ LDATA); [exact (not_eq_sym D_AD)| exact (not_eq_sym D_ABD)]).
    assert (LVS1 : a_live A1 (pe_S E) = Some 40) by (apply (LK _ _ LVS); [exact (not_eq_sym D_AS)| exact (not_eq_sym D_ABS)]).
    assert (LVB1 : a_live A1 (vb_buf (x_vv x)) = Some (vb_size (x_vv x))) by (apply (LK _ _ LVB); [exact (not_eq_sym D_AB)| exact (not_eq_sym D_ABB)]).
    (* [comment removed for export] *)
    assert (CVX : forall excl, ~ In (x_v x Fattr_vsb) excl -> ~ In (vb_buf ya) excl -> ~ In (pe_VEP E) excl ->
                  vcover (pe_H E) A excl (fun a => newblk (x_v x Fattr_vsb) 40 a \/ newblk (vb_buf ya) (vb_size ya) a \/ (pe_VEP E + 224 <= a < pe_VEP E + 224 + 8))).
    { intros excl N1 N2 N3 a [Ha|[Ha|Ha]].
      - eapply cover_newblk; [exact LAS| exact N1| exact Ha].
      - eapply cover_newblk; [exact LAB| exact N2| exact Ha].
      - eapply cover_rng; [exact LVEP| exact N3| klia Ha]. }
    assert (HC : hcover A [] (fun a => newblk (x_v x Fattr_vsb) 40 a \/ newblk (vb_buf ya) (vb_size ya) a \/ (pe_VEP E + 224 <= a < pe_VEP E + 224 + 8))).
    { intros a [Ha|[Ha|Ha]].
      - eapply hcover_newblk; [exact LAS| intros []| exact Ha].
      - eapply hcover_newblk; [exact LAB| intros []| exact Ha].
      - eapply hcover_rng; [exact LVEP| intros []| klia Ha]. }
    (* [comment removed for export] *)
    assert (FR1 : rw_cells rsegs (aview A1 m1) (pe_sp E - 320) (pframe E fj0 fj8)).
    { eapply (pframe_call E A A1 m2 md2 _ _ _ _ _ [] fj0 fj8);
        [exact PE| exact AINV2| exact CF1| exact HFR| exact WIN| exact W0| unfold pe_fp, PARSE_FRAME; klia WIN| apply CVX; intros []| unfold pframe; cbv zeta; exact FR2]. }
    assert (DATA1 : data_obj LPA A1 (aview A1 m1) (pe_DATA E) (pe_inp E)).
    { eapply (data_obj_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [pe_DATA E] AINV2 CF1 HFR WIN);
        [apply CVX; wz_not_in | left; reflexivity| exact LDATA1| exact DATA2]. }
    assert (VSBO1 : vsb_obj LPA A1 (aview A1 m1) (pe_S E) (x_vv x) false).
    { eapply (vsb_obj_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [pe_S E; vb_buf (x_vv x)] AINV2 CF1 HFR WIN);
        [apply CVX; wz_not_in
        | left; reflexivity| right; left; reflexivity| exact LVS1| exact LVB1| exact VSBO2]. }
    assert (HENV1 : henv_ok LPA VIA (pe_H E) A1 (aview A1 m1)).
    { eapply (henv_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [] AINV2 CF1 WIN); [exact HC| exact FS| exact HENV2]. }
    assert (SS1 : stack_shadow LPA (aview A1 m1) (pe_SB E) (pe_NS E) (pe_sp E - PARSE_STACK - 64) (pe_sp E + 64)).
    { eapply (stack_shadow_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [] AINV2 CF1 HFR WIN); [apply CVX; intros []| rewrite PARSE_STACK_val; klia LOP CEIL ACV| exact SS2]. }
    assert (VI1 : vi_world E (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A1 (aview A1 m1)).
    { unfold vi_world. cbn [x_vi x_v x_va x_p x_vv]. psimp. rewrite EIS.
      destruct (x_vi x) as [yi|] eqn:EVI; [| exact VI2]. (first [ dand6 VI2 as I1 I2 I3 I4 I5 I6 | destruct VI2 as (I1 & I2 & I3 & I4 & I5 & I6) ]).
      (first [ pose proof (I2) as dR_8; dand5 dR_8 as _ _ LIS LIB _ | pose proof I2 as (_ & _ & LIS & LIB & _) ]).
      unfold oibuf in D_IBV, D_IBS, D_IBB, D_IBD, D_IBW. rewrite EVI in D_IBV, D_IBS, D_IBB, D_IBD, D_IBW.
      unfold oibuf in D_AI. rewrite EVI in D_AI. cbn beta iota in D_AI. (first [ pose proof ((D_AI ltac:(discriminate) ltac:(discriminate))) as dR_9; dand4 dR_9 as NIA NIB NIbA NIbB | destruct (D_AI ltac:(discriminate) ltac:(discriminate)) as (NIA & NIB & NIbA & NIbB) ]).
      refine (conj I1 (conj _ (conj I3 (conj I4 (conj I5 (conj I6 I)))))).
      eapply (vsb_obj_call (pe_H E) A A1 m2 md2 _ _ _ _ _ [x_v x Finclude_src; vb_buf yi] AINV2 CF1 HFR WIN);
        [ apply CVX; wz_not_in
        | left; reflexivity| right; left; reflexivity
        | apply (LK _ _ LIS); [exact NIA| exact NIB]
        | apply (LK _ _ LIB); [exact NIbA| exact NIbB]
        | exact I2 ]. }
    (* [comment removed for export] *)
    assert (AVX : forall a n, pe_VEP E <= a -> a + n <= pe_VEP E + 312 -> (a + n <= pe_VEP E + 224 \/ pe_VEP E + 232 <= a) -> 0 <= n ->
                  avoids_call (pe_sp E - 320) 8224 (fun a0 => newblk (x_v x Fattr_vsb) 40 a0 \/ newblk (vb_buf ya) (vb_size ya) a0 \/ (pe_VEP E + 224 <= a0 < pe_VEP E + 224 + 8)) a n).
    { intros a n H1 H2 H3 H4. split; [left; klia H2 VEPhi CEIL LOP ACV|]. intros i Hi [X|[X|X]].
      - destruct X as [[_ X]|[_ X]]; [klia X DXS H1 H2 Hi| pose proof (live_sh_low A m md _ _ _ AINV0 LAS X) as SL; rewrite SHMAX_val in SL; klia SL VEPlo H1 Hi].
      - destruct X as [[_ X]|[_ X]]; [klia X DXB H1 H2 Hi| pose proof (live_sh_low A m md _ _ _ AINV0 LAB X) as SL; rewrite SHMAX_val in SL; klia SL VEPlo H1 Hi].
      - klia X H3 Hi H4. }
    assert (VEPC1 : rw_cells rsegs (aview A1 m1) (pe_VEP E) (vep_cells (fupd v' Fattr_vsb 0) (x_tag x) (x_q x))).
    { rewrite vep_cells_attr0.
      apply (proj2 (rw_cells_app rsegs _ (pe_VEP E) (vep_pre36 v' (x_q x)) _)). rewrite vep_pre36_size. split.
      - eapply (rw_cells_ccall LPA A A1 _ _ _ _ _ _ CF1); [| | exact VPRE]; rewrite vep_pre36_size.
        + eapply (crange_block (L:=LPA)); [exact AINV2| exact LVEP| klia VEPlo| change (Z.of_nat 224) with 224; klia VEPlo| clear; lia].
        + apply AVX; change (Z.of_nat 224) with 224; klia VEPlo.
      - change (Z.of_nat 224) with 224.
        apply (proj2 (rw_cells_app rsegs _ (pe_VEP E + 224) [C8 (Z_to_bv 64 0)] _)). split; [exact PS0|].
        cbn [cells_size csize Nat.add]. replace (pe_VEP E + 224 + Z.of_nat 8) with (pe_VEP E + 232) by (clear; lia).
        eapply (rw_cells_ccall LPA A A1 _ _ _ _ _ _ CF1); [| | exact VPOST]; rewrite vep_post37_size.
        + eapply (crange_block (L:=LPA)); [exact AINV2| exact LVEP| klia VEPlo| change (Z.of_nat 80) with 80; klia VEPlo| clear; lia].
        + apply AVX; change (Z.of_nat 80) with 80; klia VEPlo. }
    (* [comment removed for export] *)
    assert (CFX : cframe LPA (owned (pe_A0 E)) (owned A1) (pe_sp E) PARSE_STACK (parse_changed (pe_H E) (pe_VEP E) (pe_S E) (pe_b E))
                         (parse_new (fupd v' Fattr_vsb 0) (x_vv x) None (x_vio x)) (pe_v0 E) (aview A1 m1)).
    { pose proof (cframe_step_call E (PST (x_p x) (x_st x) v' (x_tag x) (x_q x) (x_vv x) (Some ya) (x_vi x))
                    (PST (x_p x) (x_st x) (fupd v' Fattr_vsb 0) (x_tag x) (x_q x) (x_vv x) None (x_vi x)) A A1 (aview A m2) (aview A1 m1) (pe_sp E - 320) 8224) as STEP.
      cbn [x_v x_vv x_va x_vi x_vio x_p x_st option_map] in STEP. unfold x_vio in CF2 |- *. rewrite ?EVA in CF2. cbn [option_map] in CF2 |- *.
      eapply STEP;
        [ exact CF2 | exact CF1 | rewrite PARSE_STACK_val; klia W0 | klia W0
        | eapply parse_window_mapped; [exact PE| exact STK1| exact FR1]
        | intros a [Ha|[Ha|Ha]]; unfold pzone, parse_changed, parse_new; cbn [x_v x_vv x_va x_vi x_vio option_map];
          [ right; right; left; unfold vsb_blocks; rewrite EAV; left; exact Ha
          | right; right; left; unfold vsb_blocks; right; exact Ha
          | left; left; split; [klia VEPlo| klia Ha] ]
        | intros a Ha; right; unfold pzone, parse_new; cbn [x_v x_vv x_va x_vi x_vio option_map]; right;
          unfold parse_new in Ha; destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha| destruct Ha| right; right; exact Ha] ]. }
    assert (KEEP1 : forall p k, a_live (pe_A0 E) p = Some k -> p <> pe_b E -> a_live A1 p = Some k).
    { intros p k Lp NBp. pose proof (KEEP p k Lp NBp) as LA. apply (LK _ _ LA).
      - intros ->. destruct (NEW (x_v x Fattr_vsb) ltac:(unfold parse_blocks; right; left; left; reflexivity)) as [X|X]; [exact (NBp X)| rewrite X in Lp; discriminate Lp].
      - intros ->. destruct (NEW (vb_buf ya) ltac:(unfold parse_blocks; right; left; right; reflexivity)) as [X|X]; [exact (NBp X)| rewrite X in Lp; discriminate Lp]. }
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m1 md1 AINV1 MI1 MDF1 STK1 FR1 VEPC1 HENV1 DATA1 VSBO1 WAL1 LVEP1 VI1 SS1 LB1 NL1 TC1 SCC1 PCC1 FSA KEEP1 CFX).
  Qed.
End S.
