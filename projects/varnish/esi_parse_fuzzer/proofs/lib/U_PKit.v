(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_La7nl U_Img V_Vct U_Cov8m U_Pahif ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutPU OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Stores.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Fixpoint wzone (E : penv) (A : AS) (excl : list Z) (W : list ivl) : Prop :=
    match W with
    | [] => True
    | (lo, hi) :: W' =>
        ((exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= lo /\ hi <= p + n)
         \/ (pe_lo E <= lo /\ hi <= pe_sp E + 32)
         \/ (lo = h_vsc (pe_H E) + 1304 /\ hi = h_vsc (pe_H E) + 1320)
         \/ (lo = al_errno LayoutPU /\ hi = al_errno LayoutPU + 4))
        /\ wzone E A excl W'
    end.

  (* [comment removed for export] *)
  Lemma wzone_cases : forall E A excl W a,
    wzone E A excl W -> ~ outside W a ->
    (exists p n, a_live A p = Some n /\ ~ In p excl /\ p <= a < p + n)
    \/ (pe_lo E <= a < pe_sp E + 32)
    \/ (h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320)
    \/ (al_errno LayoutPU <= a < al_errno LayoutPU + 4).
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
  Lemma wzone_client_fp : forall E A excl W,
    penv_ok E -> wzone E A excl W -> client_fp LayoutPU A W.
  Proof.
    intros E A excl W PE. destruct PE as ((G1 & G2 & G3) & _ & _ & CEIL & LOP & _).
    induction W as [|[lo hi] W IH]; cbn; intros WZ; [exact I|].
    destruct WZ as [C WZ]. split; [|apply IH; exact WZ].
    destruct C as [(p & n & L & NI & H1 & H2)|[[H1 H2]|[[H1 H2]|[H1 H2]]]].
    - right; left. exists p, n. auto.
    - left. unfold pe_sp in H2. unfold HFRAME in G3. lia.
    - left. unfold h_vsc in *. unfold HFRAME in G3. lia.
    - right; right; left. split; assumption.
  Qed.

  Variables (E : penv) (A : AS) (m m' : mem) (md : Model) (excl : list Z) (W : list ivl).
  Hypothesis PE : penv_ok E.
  Hypothesis AINV : ainv A m md.
  Hypothesis MU : munch W m m'.
  Hypothesis WM : wmono rsegs m m'.
  Hypothesis WZ : wzone E A excl W.

  Lemma ainv_stores : ainv A m' md.
  Proof. eapply (ainv_munch LayoutPU); [exact AINV| exact MU| exact WM| eapply wzone_client_fp; eassumption]. Qed.

  (* [comment removed for export] *)
  Lemma outside_blk : forall o0 k a,
    In o0 excl -> a_live A o0 = Some k -> o0 <= a < o0 + k -> outside W a.
  Proof.
    intros o0 k a IN L Ha.
    destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
    destruct PE as ((G1 & G2 & G3) & _ & _ & CEIL & LOP & _).
    (first [ pose proof ((live_geom LayoutPU A m md o0 k AINV L)) as dR_1; dand6 dR_1 as _ _ LO HI OFF _ | destruct (live_geom LayoutPU A m md o0 k AINV L) as (_ & _ & LO & HI & OFF & _) ]).
    destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]].
    - assert (NE : p <> o0) by (intros ->; exact (NI IN)).
      pose proof (as_live_disjoint A m md p n o0 k AINV Lp L NE). lia.
    - unfold pe_sp in R. lia.
    - unfold h_vsc in R. lia.
    - change (al_errno LayoutPU) with 0x42454%Z in R. unfold off_image in OFF. cbn in OFF. lia.
  Qed.

  Lemma rw_cells_stores_blk : forall o0 k o cs,
    In o0 excl -> a_live A o0 = Some k -> o0 <= o -> o + Z.of_nat (cells_size cs) <= o0 + k ->
    rw_cells rsegs m o cs -> rw_cells rsegs m' o cs.
  Proof.
    intros o0 k o cs IN L H1 H2 RC. eapply (rw_cells_munch LayoutPU); [exact RC| exact MU| exact WM|].
    intros a Ha. eapply outside_blk; [exact IN| exact L| lia].
  Qed.

  Lemma u8arr_stores_blk : forall o0 k o bs,
    In o0 excl -> a_live A o0 = Some k -> o0 <= o -> o + Z.of_nat (length bs) <= o0 + k ->
    u8arr rsegs m o bs -> u8arr rsegs m' o bs.
  Proof.
    intros o0 k o bs IN L H1 H2 [B WR]. split.
    - (first [ dand3 B as B0 B1 B | destruct B as (B0 & B1 & B) ]). split; [exact B0|]. split; [exact B1|]. intros i Hi.
      unfold mrd. rewrite MU; [apply B; exact Hi|]. rewrite wa_unsigned by lia.
      eapply outside_blk; [exact IN| exact L| lia].
    - eapply wr_at_transport; eauto.
  Qed.

  Lemma bytes_at_stores_blk : forall o0 k o bs,
    In o0 excl -> a_live A o0 = Some k -> o0 <= o -> o + Z.of_nat (length bs) <= o0 + k ->
    bytes_at rsegs m o bs -> bytes_at rsegs m' o bs.
  Proof.
    (intros o0 k o bs IN L H1 H2; (first [ intro dR_33; dand3 dR_33 as B0 B1 B | intros (B0 & B1 & B) ])). split; [exact B0|]. split; [exact B1|]. intros i Hi.
    unfold mrd. rewrite MU; [apply B; exact Hi|]. rewrite wa_unsigned by lia.
    eapply outside_blk; [exact IN| exact L| lia].
  Qed.

  Lemma vsb_obj_stores : forall S v fin,
    In S excl -> In (vb_buf v) excl -> vsb_obj LayoutPU A m S v fin -> vsb_obj LayoutPU A m' S v fin.
  Proof.
    (intros S v fin I1 I2; (first [ intro dR_34; dand6 dR_34 as VC VI LS LB NE (bs & U & LEN & NUL) | intros (VC & VI & LS & LB & NE & (bs & U & LEN & NUL)) ])).
    split; [|split; [exact VI|]; split; [exact LS|]; split; [exact LB|]; split; [exact NE|]].
    - eapply (rw_cells_stores_blk S 40); [exact I1| exact LS| lia| rewrite vsb_cells_size; lia| exact VC].
    - exists bs. split; [|split; [exact LEN| exact NUL]].
      eapply (u8arr_stores_blk (vb_buf v) (vb_size v)); [exact I2| exact LB| lia| lia| exact U].
  Qed.

  Lemma data_obj_stores : forall DATA inp,
    In DATA excl -> data_obj LayoutPU A m DATA inp -> data_obj LayoutPU A m' DATA inp.
  Proof.
    (intros DATA inp IN; (first [ intro dR_35; dand3 dR_35 as L B LEN | intros (L & B & LEN) ])). split; [exact L|]. split; [|exact LEN].
    eapply (bytes_at_stores_blk DATA (Z.of_nat (length inp))); [exact IN| exact L| lia| lia| exact B].
  Qed.

  Lemma img_stores : img_okU m -> img_okU m'.
  Proof.
    intros IMG. eapply img_okU_munch; [exact MU| | exact IMG].
    intros a Ha. unfold IMGU_LO, IMGU_HI in Ha.
    destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
    destruct PE as ((G1 & G2 & G3) & _ & _ & CEIL & LOP & _). pose proof alloc_ceiling_val as CV.
    destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]].
    - (first [ pose proof ((live_geom LayoutPU A m md p n AINV Lp)) as dR_3; dand6 dR_3 as _ _ _ _ OFF _ | destruct (live_geom LayoutPU A m md p n AINV Lp) as (_ & _ & _ & _ & OFF & _) ]). unfold off_image in OFF. cbn in OFF. lia.
    - unfold pe_sp in R. lia.
    - unfold h_vsc in R. lia.
    - change (al_errno LayoutPU) with 0x42454%Z in R. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma henv_stores :
    (forall a, h_vsc (pe_H E) + 1304 <= a < h_vsc (pe_H E) + 1320 -> outside W a) ->
    henv_ok LayoutPU VIU (pe_H E) m -> henv_ok LayoutPU VIU (pe_H E) m'.
  Proof.
    intros NV HE. pose proof HE as ((EB & _) & _). cbn [vi_bss VIU] in EB.
    eapply (henv_ok_munch LayoutPU); [exact HE| exact MU| exact WM|].
    intros a Ha. destruct Ha as [Ha|[Ha|[Ha|Ha]]]; [| | | apply NV; exact Ha].
    all: destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]; exfalso.
    all: destruct PE as ((G1 & G2 & G3) & _ & _ & CEIL & LOP & _); pose proof alloc_ceiling_val as CV.
    all: rewrite ?EB in Ha.
    all: destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]]; unfold h_hd, h_wrk, h_req, h_vsc, pe_sp in *;
         [| lia| lia| change (al_errno LayoutPU) with 0x42454%Z in R; lia].
    all: (first [ pose proof ((live_geom LayoutPU A m md p n AINV Lp)) as dR_4; dand6 dR_4 as _ _ _ PHI OFF _ | destruct (live_geom LayoutPU A m md p n AINV Lp) as (_ & _ & _ & PHI & OFF & _) ]); unfold off_image in OFF; cbn in OFF; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hobj_stores : hobj_ok LayoutPU VIU (pe_H E) m -> hobj_ok LayoutPU VIU (pe_H E) m'.
  Proof.
    intros HO. eapply (hobj_ok_munch LayoutPU); [exact HO| exact MU| exact WM|].
    intros a Ha.
    destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
    destruct PE as ((G1 & G2 & G3) & _ & _ & CEIL & LOP & _). pose proof alloc_ceiling_val as CV.
    destruct (wzone_cases E A excl W a WZ X) as [(p & n & Lp & NI & R)|[R|[R|R]]]; unfold h_vc, h_hd, h_wrk, h_req, h_resp, h_cp, h_vsc, pe_sp in *;
      [| lia| lia| change (al_errno LayoutPU) with 0x42454%Z in R; lia].
    (first [ pose proof ((live_geom LayoutPU A m md p n AINV Lp)) as dR_5; dand6 dR_5 as _ _ _ PHI OFF _ | destruct (live_geom LayoutPU A m md p n AINV Lp) as (_ & _ & _ & PHI & OFF & _) ]). lia.
  Qed.
End Stores.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HStep.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  (* [comment removed for export] *)
  Definition w_in_zone (E : penv) (x : pst) (W : list ivl) : Prop :=
    forall a, 0 <= a < 2^64 -> ~ outside W a ->
      (h_sp (pe_H E) - PARSE_STACK <= a < h_sp (pe_H E)) \/ pzone E x a \/ (al_errno LayoutPU <= a < al_errno LayoutPU + 4).

  Lemma w_in_zone_nil : forall E x, w_in_zone E x [].
  Proof. intros E x a _ NO. exfalso. exact (NO I). Qed.
  Lemma w_in_zone_errno : forall E x W,
    w_in_zone E x W -> w_in_zone E x ((al_errno LayoutPU, al_errno LayoutPU + 4) :: W).
  Proof.
    intros E x W IH a Ha NO. cbn in NO.
    destruct (Classical_Prop.classic (al_errno LayoutPU <= a < al_errno LayoutPU + 4)) as [IN|NIN]; [right; right; exact IN|].
    apply IH; [exact Ha|]. intros O. apply NO. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_noalloc_e : forall o sp win (V N : Z -> Prop) m m0 (W : list ivl),
    munch W m m0 ->
    (forall a, 0 <= a < 2^64 -> ~ outside W a -> (sp - win <= a < sp) \/ V a \/ (al_errno LayoutPU <= a < al_errno LayoutPU + 4)) ->
    mapped m0 (sp - win) win ->
    (forall a, N a -> V a) ->
    cframe LayoutPU o o sp win V N m m0.
  Proof.
    intros o sp win V N m m0 W MU IN MAP NV. split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NVa. split; [|exact NO].
      apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia.
      destruct (Classical_Prop.classic (outside W a)) as [X|X]; [exact X|]. exfalso.
      destruct (IN a Ha X) as [Y|[Y|Y]]; [exact (NW Y)| exact (NVa Y)| exact (NE Y)].
    - intros a _ _ _ X. right; left. apply NV, X.
  Qed.
  Lemma w_in_zone_win : forall E x lo hi W,
    h_sp (pe_H E) - PARSE_STACK <= lo -> hi <= h_sp (pe_H E) -> w_in_zone E x W -> w_in_zone E x ((lo, hi) :: W).
  Proof.
    intros E x lo hi W H1 H2 IH a Ha NO. cbn in NO.
    destruct (Classical_Prop.classic (lo <= a < hi)) as [IN|NIN]; [left; lia|]. apply IH; [exact Ha|]. intros O. apply NO. split; assumption.
  Qed.
  Lemma w_in_zone_zone : forall E x lo hi W,
    (forall a, lo <= a < hi -> pzone E x a) -> w_in_zone E x W -> w_in_zone E x ((lo, hi) :: W).
  Proof.
    intros E x lo hi W HZ IH a Ha NO. cbn in NO.
    destruct (Classical_Prop.classic (lo <= a < hi)) as [IN|NIN]; [right; left; apply HZ; exact IN|]. apply IH; [exact Ha|]. intros O. apply NO. split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma parse_window_mapped : forall E m j0 j8 j16 j24,
    penv_ok E -> stk rsegs m (pe_lo E) (pe_sp E) -> rw_cells rsegs m (pe_sp E) (pframe E j0 j8 j16 j24) ->
    mapped m (h_sp (pe_H E) - PARSE_STACK) PARSE_STACK.
  Proof.
    intros E m j0 j8 j16 j24 PE ST FR. destruct PE as ((G1 & G2 & G3) & _ & _ & CEIL & LOP & _).
    eapply (window_mapped LayoutPU m (pe_lo E) (pe_sp E) (h_sp (pe_H E)) PARSE_STACK); [exact ST| exact FR| rewrite pframe_size; unfold pe_sp; lia| exact CEIL| lia| unfold pe_sp, PARSE_STACK, DOINCL_STACK, REALLOC_STACK; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma hstep_stores : forall E x x' A m m' W,
    munch W m m' -> w_in_zone E x W ->
    mapped m' (h_sp (pe_H E) - PARSE_STACK) PARSE_STACK ->
    (forall p, pst_blocks x' p -> pst_blocks x p) ->
    (forall a, parse_new (x_v x') (x_vv x') (x_va x') (option_map (fun y => (y, true)) (x_vi x')) a -> pzone E x a) ->
    hstep E x x' A A m m'.
  Proof.
    intros E x x' A m m' W MU WZ MAP PB PN. split; [|split].
    - intros p k Hp _. exact Hp.
    - intros p Hp. left. apply PB, Hp.
    - eapply cframe_noalloc_e; [exact MU| exact WZ| exact MAP| exact PN].
  Qed.

  (* [comment removed for export] *)
  Lemma hstep_intro : forall E x x' A A' m m' win V N,
    cframe LayoutPU (owned A) (owned A') (h_sp (pe_H E)) win V N m m' -> win <= PARSE_STACK ->
    mapped m' (h_sp (pe_H E) - PARSE_STACK) PARSE_STACK ->
    (forall a, V a -> pzone E x a) ->
    (forall a, parse_new (x_v x') (x_vv x') (x_va x') (option_map (fun y => (y, true)) (x_vi x')) a -> N a \/ pzone E x a) ->
    (forall p k, a_live A p = Some k -> ~ pst_blocks x p -> a_live A' p = Some k) ->
    (forall p, pst_blocks x' p -> pst_blocks x p \/ a_live A p = None) ->
    hstep E x x' A A' m m'.
  Proof.
    intros E x x' A A' m m' win V N CF WIN MAP HV HN L1 L2. split; [exact L1|]. split; [exact L2|].
    (first [ dand3 CF as C1 C2 C3 | destruct CF as (C1 & C2 & C3) ]). split; [|split; [exact MAP|]].
    - intros a Ha NO VIS NW NE NV. apply C1; [exact Ha| exact NO| exact VIS| lia| exact NE| intros X; apply NV, HV, X].
    - intros a Ha NW NE HNa. destruct (HN a HNa) as [X|X]; [|right; left; exact X].
      destruct (C3 a Ha ltac:(lia) NE X) as [Y|[Y|Y]]; [left; exact Y| right; left; apply HV, Y| right; right; exact Y].
  Qed.

  (* [comment removed for export] *)
  Lemma cframe_rebase : forall E o o' win V N m m',
    cframe LayoutPU o o' (pe_sp E) win V N m m' -> win + 208 <= PARSE_STACK ->
    mapped m' (h_sp (pe_H E) - PARSE_STACK) PARSE_STACK ->
    cframe LayoutPU o o' (h_sp (pe_H E)) PARSE_STACK V N m m'.
  Proof.
    intros E o o' win V N m m' CF WIN MAP.
    eapply (cframe_reframe LayoutPU); [exact CF| | | exact MAP]; unfold pe_sp in *; lia.
  Qed.
End HStep.

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

Section Seps.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Lemma pinv_seps : forall E x A m md,
    penv_ok E -> pinv E x A m -> ainv A m md ->
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
    intros E x A m md PE PI AINV. open_pinv PI. unfold va_world in VA. unfold vi_world in VI.
    destruct PE as (_ & _ & _ & _ & _ & NE1 & NE2 & NE3 & NE4 & NE5 & NE6 & _).
    destruct VEPO as (LVEP & _). destruct DATA as (LDATA & _).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LVEP)) as dR_7; dand4 dR_7 as _ _ VEPlo _ | destruct (live_geom LayoutPU _ _ _ _ _ AINV LVEP) as (_ & _ & VEPlo & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LDATA)) as dR_8; dand4 dR_8 as _ _ Dlo _ | destruct (live_geom LayoutPU _ _ _ _ _ AINV LDATA) as (_ & _ & Dlo & _) ]).
    (first [ pose proof ((vsb_apart3 _ _ _ _ _ APART)) as dR_9; dand6 dR_9 as AP1 AP2 AP3 AP4 AP5 AP6 | pose proof (vsb_apart3 _ _ _ _ _ APART) as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6) ]).
    (first [ pose proof (VSBO) as dR_10; dand6 dR_10 as _ _ LVS LVB SNB _ | pose proof VSBO as (_ & _ & LVS & LVB & SNB & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LVS)) as dR_11; dand4 dR_11 as _ _ Slo _ | destruct (live_geom LayoutPU _ _ _ _ _ AINV LVS) as (_ & _ & Slo & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV LVB)) as dR_12; dand4 dR_12 as _ _ Blo _ | destruct (live_geom LayoutPU _ _ _ _ _ AINV LVB) as (_ & _ & Blo & _) ]).
    (first [ pose proof ((live_geom LayoutPU _ _ _ _ _ AINV WAL)) as dR_13; dand4 dR_13 as _ _ Wlo _ | destruct (live_geom LayoutPU _ _ _ _ _ AINV WAL) as (_ & _ & Wlo & _) ]).
    unfold oabuf, oibuf. cbn zeta.
    split; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; congruence|].
    match goal with |- ?P /\ ?Q => cut (Q /\ P); [intros [X Y]; exact (conj Y X)|] end.
    destruct (x_va x) as [ya|]; destruct (x_vi x) as [yi|].
    - (first [ dand4 VA as ANZ AO _ AAP | destruct VA as (ANZ & AO & _ & AAP) ]). (first [ dand6 VI as INZ IO _ _ IAP IAP2 | destruct VI as (INZ & IO & _ & _ & IAP & IAP2) ]).
      (first [ pose proof (AO) as dR_16; dand6 dR_16 as _ _ LAS LAB ASB _ | pose proof AO as (_ & _ & LAS & LAB & ASB & _) ]). (first [ pose proof (IO) as dR_17; dand6 dR_17 as _ _ LIS LIB ISB _ | pose proof IO as (_ & _ & LIS & LIB & ISB & _) ]).
      destruct (live_geom LayoutPU _ _ _ _ _ AINV LAS) as (_ & _ & ? & _). destruct (live_geom LayoutPU _ _ _ _ _ AINV LAB) as (_ & _ & ? & _).
      destruct (live_geom LayoutPU _ _ _ _ _ AINV LIS) as (_ & _ & ? & _). destruct (live_geom LayoutPU _ _ _ _ _ AINV LIB) as (_ & _ & ? & _).
      destruct (AAP (pe_VEP E) ltac:(cbn; auto)) as [? ?]. destruct (AAP (pe_wa E) ltac:(cbn; auto)) as [? ?].
      destruct (AAP (pe_DATA E) ltac:(cbn; auto 6)) as [? ?]. destruct (AAP (pe_S E) ltac:(cbn; auto 8)) as [? ?].
      destruct (AAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [? ?].
      destruct (IAP (pe_VEP E) ltac:(cbn; auto)) as [? ?]. destruct (IAP (pe_wa E) ltac:(cbn; auto)) as [? ?].
      destruct (IAP (pe_DATA E) ltac:(cbn; auto 6)) as [? ?]. destruct (IAP (pe_S E) ltac:(cbn; auto 8)) as [? ?].
      destruct (IAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [? ?].
      destruct (IAP2 (x_v x Fattr_vsb) ltac:(cbn; auto)) as [? ?]. destruct (IAP2 (vb_buf ya) ltac:(cbn; auto)) as [? ?].
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; try congruence; try lia.
    - (first [ dand4 VA as ANZ AO _ AAP | destruct VA as (ANZ & AO & _ & AAP) ]).
      (first [ pose proof (AO) as dR_19; dand6 dR_19 as _ _ LAS LAB ASB _ | pose proof AO as (_ & _ & LAS & LAB & ASB & _) ]).
      destruct (live_geom LayoutPU _ _ _ _ _ AINV LAS) as (_ & _ & ? & _). destruct (live_geom LayoutPU _ _ _ _ _ AINV LAB) as (_ & _ & ? & _).
      destruct (AAP (pe_VEP E) ltac:(cbn; auto)) as [? ?]. destruct (AAP (pe_wa E) ltac:(cbn; auto)) as [? ?].
      destruct (AAP (pe_DATA E) ltac:(cbn; auto 6)) as [? ?]. destruct (AAP (pe_S E) ltac:(cbn; auto 8)) as [? ?].
      destruct (AAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [? ?].
      rewrite VI. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; try congruence; try lia.
    - (first [ dand6 VI as INZ IO _ _ IAP _ | destruct VI as (INZ & IO & _ & _ & IAP & _) ]).
      (first [ pose proof (IO) as dR_21; dand6 dR_21 as _ _ LIS LIB ISB _ | pose proof IO as (_ & _ & LIS & LIB & ISB & _) ]).
      destruct (live_geom LayoutPU _ _ _ _ _ AINV LIS) as (_ & _ & ? & _). destruct (live_geom LayoutPU _ _ _ _ _ AINV LIB) as (_ & _ & ? & _).
      destruct (IAP (pe_VEP E) ltac:(cbn; auto)) as [? ?]. destruct (IAP (pe_wa E) ltac:(cbn; auto)) as [? ?].
      destruct (IAP (pe_DATA E) ltac:(cbn; auto 6)) as [? ?]. destruct (IAP (pe_S E) ltac:(cbn; auto 8)) as [? ?].
      destruct (IAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [? ?].
      rewrite VA. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; try congruence; try lia.
    - rewrite VA, VI. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; try congruence; try lia.
  Qed.
End Seps.

(* [comment removed for export] *)
Section WoTwins.
Context {Clg : Ceiling}.
  Context {AI : AllocSpec LayoutPU}.
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
  Lemma wo_pinv_seps_r : forall E x A m md, penv_ok E -> pinv E x A m -> ainv A m md -> wo_seps_rec E x.
  Proof.
    intros E x A m md PE PI AINV.
    (first [ pose proof ((pinv_seps _ _ _ _ _ PE PI AINV)) as dR_22; dex4 dR_22 as g1 g2 g3 g4; dand3 dR_22 as DAA DII DAI | pose proof ((pinv_seps _ _ _ _ _ PE PI AINV)) as dR_22; dand7 dR_22 as g1 g2 g3 g4 DAA DII DAI | pose proof (pinv_seps _ _ _ _ _ PE PI AINV) as (g1 & g2 & g3 & g4 & DAA & DII & DAI) ]). cbn zeta in *.
    destruct g1 as (? & ? & ? & ? & ? & ?). destruct g2 as (? & ? & ? & ? & ? & ? & ? & ?).
    destruct g3 as (? & ? & ? & ? & ? & ? & ? & ?). destruct g4 as (? & ? & ? & ? & ? & ? & ? & ?).
    constructor; assumption.
  Qed.
  Record wo_penv_rec (E : penv) : Prop := Build_wo_penv_rec {
    wo_G1 : h_sp (pe_H E) mod 16 = 0; wo_G2 : alloc_ceiling + 12720 <= h_sp (pe_H E); wo_G3 : h_sp (pe_H E) + HFRAME + 64 <= 2^47;
    wo_FL : 0 <= pe_flags E < 16; wo_NN : 1 <= pe_N E < NMAX;
    wo_CEIL : alloc_ceiling <= pe_lo E; wo_LOP : pe_lo E + PARSE_STACK <= h_sp (pe_H E);
    wo_NE1 : pe_VEP E <> pe_S E; wo_NE2 : pe_wa E <> pe_S E; wo_NE3 : pe_DATA E <> pe_VEP E; wo_NE4 : pe_DATA E <> pe_S E; wo_NE5 : pe_DATA E <> pe_wa E;
    wo_NE6 : pe_VEP E <> pe_wa E; wo_RA2 : bv_unsigned (pe_ra E) mod 2 = 0;
    (* [comment removed for export] *)
    wo_BUDL : pe_LB0 E + PARSE_LIVE (pe_N E) <= LIVE_MAX; wo_BUDN : pe_NL0 E + PARSE_NLIVE <= NLIVE_MAX }.
  Lemma wo_penv_ok_r : forall E, penv_ok E -> wo_penv_rec E.
  Proof. intros E ((? & ? & ?) & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?). constructor; assumption. Qed.
  Lemma wo_penv_ne_vd : forall E, penv_ok E -> pe_VEP E <> pe_DATA E.
  Proof. intros E PE XX. destruct PE as (_ & _ & _ & _ & _ & _ & _ & XE & _). exact (XE (eq_sym XX)). Qed.
  Record wo_geom_rec (m : mem) (A : AS) (p n : Z) : Prop := Build_wo_geom_rec {
    wo_g1 : 0 <= n; wo_g2 : p mod 16 = 0; wo_g3 : 4096 <= p; wo_g4 : p + n <= alloc_ceiling; wo_g5 : off_image LayoutPU p n; wo_g6 : mapped m p n;
    wo_g7 : forall i, 0 <= i < n -> ~ owned A (p + i) }.
  Lemma wo_live_geom_r : forall A m md p n, ainv A m md -> a_live A p = Some n -> wo_geom_rec m A p n.
  Proof. intros A m md p n AI0 LV. destruct (live_geom LayoutPU A m md p n AI0 LV) as (? & ? & ? & ? & ? & ? & ?). constructor; assumption. Qed.
End WoTwins.

Section Costs.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  Lemma ocosts_nonneg : forall E x A m, pinv E x A m -> 0 <= oacost x /\ 0 <= oicost x.
  Proof.
    intros E x A m PI. pose proof (pi_va _ _ _ _ PI) as VA. pose proof (pi_vi _ _ _ _ PI) as VI.
    unfold va_world in VA. unfold vi_world in VI. unfold oacost, oicost. split.
    - destruct (x_va x) as [y|]; [|lia]. (first [ dand3 VA as _ (_ & VIy & _) _ | destruct VA as (_ & (_ & VIy & _) & _) ]). unfold vsb_inv in VIy. lia.
    - destruct (x_vi x) as [y|]; [|lia]. (first [ dand3 VI as _ (_ & VIy & _) _ | destruct VI as (_ & (_ & VIy & _) & _) ]). unfold vsb_inv in VIy. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pinv_sizes : forall E x A m, pinv E x A m ->
    vb_len (x_vv x) + oacost x + oicost x <= 7 * pe_N E
    /\ pw_bytes (x_vv x) (x_va x) (x_vi x) <= 7 * pe_N E + 12408
    /\ 0 <= vb_len (x_vv x) /\ 16 <= vb_size (x_vv x).
  Proof.
    intros E x A m PI. pose proof (ocosts_nonneg _ _ _ _ PI) as [OA0 OI0].
    pose proof (pi_out _ _ _ _ PI) as OUT. pose proof (pi_cnt _ _ _ _ PI) as CNT. pose proof (pi_verp _ _ _ _ PI) as VERP.
    pose proof (pi_pe _ _ _ _ PI) as PLE. pose proof (pi_room _ _ _ _ PI) as ROOM.
    pose proof (pi_va _ _ _ _ PI) as VA. pose proof (pi_vi _ _ _ _ PI) as VI. pose proof (pi_vsb _ _ _ _ PI) as VSBO.
    unfold va_world in VA. unfold vi_world in VI. unfold vep_cnt in CNT. unfold pe_e in PLE.
    pose proof (proj1 (proj2 VSBO)) as VIv. unfold vsb_inv in VIv.
    assert (O1 : vb_len (x_vv x) + oacost x + oicost x <= 7 * pe_N E).
    { revert OUT CNT VERP PLE OA0 OI0. clear. destruct (x_st x); intros; lia. }
    split; [exact O1|]. unfold pw_bytes. unfold oacost, oicost in O1.
    destruct (x_va x) as [ya|]; destruct (x_vi x) as [yi|];
      try (destruct VA as (_ & (_ & VIa & _) & SZa & _); unfold vsb_inv in VIa);
      try (destruct VI as (_ & (_ & VIi & _) & _ & SZi & _); unfold vsb_inv in VIi); lia.
  Qed.
End Costs.

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
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac world_open PE PI AINV :=
  pose_seps PE PI AINV;
  pose proof (ocosts_nonneg _ _ _ _ PI) as [OA0 OI0];
  destruct PI as [VEPO__ BASE FLG VSBF STUP STATE CNT VERP PLE B01 TAGI DELIM ESIC UNTL MTCH DOST ARMED ATTR ATTRST
                  MATTR LOOKA LOOKM VSBO ROOM OUT APART WAL AVSB VA VI DATA HENV IMG STK FRAME__ MI LB NL];
  destruct VEPO__ as (LVEP & VEPC & TAG & PADS); destruct FRAME__ as (j0 & j8 & j16 & j24 & FR);   (* [comment removed for export] *)
  lazymatch type of DATA with data_obj _ _ _ _ _ =>
    pose proof DATA as (LDATA & DBY & DLEN);
    lazymatch type of LVEP with a_live _ _ = _ =>
    destruct (wo_live_geom_r _ _ _ _ _ AINV LVEP) as [_ VEP16 VEPlo VEPhi VEPimg _ _];
    destruct (wo_live_geom_r _ _ _ _ _ AINV LDATA) as [_ _ Dlo Dhi Dimg _ _];
    lazymatch type of PE with penv_ok ?E =>
      pose proof (as_live_disjoint _ _ _ _ _ _ _ AINV LVEP LDATA (wo_penv_ne_vd _ PE)) as DJ_VD end;
    try pose proof PE as PE0;
    destruct (wo_penv_ok_r _ PE) as [G1 G2 G3 FL NN CEIL LOP NE1 NE2 NE3 NE4 NE5 NE6 RA2 BUDL BUDN];
    pose proof (conj G1 (conj G2 G3) : henv_geom _) as HG;
    pose proof alloc_ceiling_val as CV;
    lazymatch type of PE with penv_ok ?E =>
      assert (PSP : pe_sp E = h_sp (pe_H E) - 208) by reflexivity;
      assert (HVSC : h_vsc (pe_H E) = h_sp (pe_H E) + 2240) by reflexivity end;
    unfold PARSE_STACK, DOINCL_STACK, REALLOC_STACK in LOP;
    unfold NMAX, pe_N in NN; unfold pe_e, pe_N in PLE;
    lazymatch type of PE with penv_ok ?E =>
      assert (EE : pe_e E = pe_DATA E + Z.of_nat (length (pe_inp E))) by reflexivity end;
    pose proof (rw_cells_bound _ _ _ _ VEPC) as VEPB; rewrite (vep_cells_size _ _ _ TAG PADS) in VEPB;
    pose proof (rw_cells_bound _ _ _ _ FR) as FRB; rewrite pframe_size in FRB;
    unfold vep_cells in VEPC; unfold pframe in FR; rewrite STATE in VEPC; fold_al_segs;
    (first [ pose proof (B01) as dR_25; dand8 dR_25 as B_lm B_ef B_et B_em B_ca B_rm B_ie B_ic | pose proof B01 as (B_lm & B_ef & B_et & B_em & B_ca & B_rm & B_ie & B_ic) ]);
    (first [ pose proof ((vsb_apart3 _ _ _ _ _ APART)) as dR_26; dand6 dR_26 as AP1 AP2 AP3 AP4 AP5 AP6 | pose proof (vsb_apart3 _ _ _ _ _ APART) as (AP1 & AP2 & AP3 & AP4 & AP5 & AP6) ]);
    pose proof (proj1 (proj2 (proj2 VSBO))) as LVS; pose proof (proj1 (proj2 (proj2 (proj2 VSBO)))) as LVB;
    unfold in_tag_cluster, attr_states, avsb_states in ARMED, ATTRST, AVSB, ATTR; unfold va_world in VA; unfold vi_world in VI;
    try match goal with ST : x_st _ = _ |- _ => rewrite ST in ARMED, ATTRST, AVSB, ATTR, DELIM, UNTL, MTCH, MATTR, LOOKA, LOOKM, OUT end;
    cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi] in ARMED, ATTRST, AVSB, ATTR, DELIM, UNTL, MTCH, MATTR, LOOKA, LOOKM, OUT;
    cbn beta iota in ARMED, ATTRST, AVSB, ATTR, OUT; destruct DELIM as [DELIM1 DELIM2];
    (* [comment removed for export] *)
    try assert (VCR : 0 <= VCT_ADDR < 2^64) by (unfold VCT_ADDR; clear; lia)
  end end.

(* [comment removed for export] *)
Ltac handler_prologue PE PI AINV ST :=
  pose proof (as_lazy_nil _ _ _ AINV) as [MDL MDH];
  world_open PE PI AINV;
  unfold disp_ms, loop_ms, lms; rewrite ST; cbn [disp_pc stU disp_a1 disp_a2 disp_s8 oreg].

(* [comment removed for export] *)
Ltac unfold_stacks_g :=
  unfold PARSE_STACK, DOINCL_STACK, VEPFIN_STACK, VEPINIT_STACK, WSROLLBACK_STACK, WSALLOC_STACK, MARK_STACK, EMITC_STACK,
         EMITLEN_STACK, VEPERR_STACK, WSINIT_STACK, REALLOC_STACK, CALLOC_STACK, MALLOC_STACK, FREE_STACK.
Ltac stk_lia := unfold_stacks_g; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac psimp :=
  lazymatch goal with |- ?G =>
    let G := eval unfold va_world in G in let G := eval unfold vi_world in G in let G := eval unfold in_tag_cluster in G in
    let G := eval unfold attr_states in G in let G := eval unfold avsb_states in G in
    let G := eval cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb in_tag_cluster attr_states avsb_states oabuf oibuf] in G in
    change_no_check G
  end.
Ltac psimp_in H := try unfold va_world in H; try unfold vi_world in H; try unfold in_tag_cluster in H; try unfold attr_states in H; try unfold avsb_states in H; cbn [x_p x_st x_v x_tag x_q x_vv x_va x_vi fupd vf_beq vf_index N.eqb Pos.eqb in_tag_cluster attr_states avsb_states oabuf oibuf] in H.

(* [comment removed for export] *)
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
            | context [pe_sp] => right; left; lia
            | context [h_sp] => right; left; lia
            | context [bv_unsigned] => right; left; lia
            | context [h_vsc] => right; right; left; split; reflexivity
            | context [al_errno] => right; right; right; split; reflexivity
            | 0x42454 => right; right; right; change (al_errno LayoutPU) with 0x42454%Z; split; reflexivity
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
      | context [pe_sp] => apply w_in_zone_win; [unfold pe_sp, PARSE_STACK, DOINCL_STACK, REALLOC_STACK in *; lia | unfold pe_sp, PARSE_STACK, DOINCL_STACK, REALLOC_STACK in *; lia |]
      | context [h_sp] => apply w_in_zone_win; [unfold pe_sp, PARSE_STACK, DOINCL_STACK, REALLOC_STACK in *; lia | unfold pe_sp, PARSE_STACK, DOINCL_STACK, REALLOC_STACK in *; lia |]
      | context [bv_unsigned] => apply w_in_zone_win; [unfold pe_sp, PARSE_STACK, DOINCL_STACK, REALLOC_STACK in *; lia | unfold pe_sp, PARSE_STACK, DOINCL_STACK, REALLOC_STACK in *; lia |]
      | context [al_errno] => apply w_in_zone_errno
      | 0x42454 => change 0x42454%Z with (al_errno LayoutPU) at 1; apply w_in_zone_errno
      | _ => apply w_in_zone_zone; [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; unfold pzone | ]
      end
  end.

(* [comment removed for export] *)
Lemma pst_blocks_same : forall x p st v' tag q p0,
  v' Fattr_vsb = x_v x Fattr_vsb -> v' Finclude_src = x_v x Finclude_src ->
  pst_blocks (PST p st v' tag q (x_vv x) (x_va x) (x_vi x)) p0 -> pst_blocks x p0.
Proof. intros x p st v' tag q p0 E1 E2 X. unfold pst_blocks in *. cbn in X. rewrite E1, E2 in X. exact X. Qed.

Lemma parse_new_same : forall E x v' a,
  v' Fattr_vsb = x_v x Fattr_vsb -> v' Finclude_src = x_v x Finclude_src ->
  parse_new v' (x_vv x) (x_va x) (option_map (fun y => (y, true)) (x_vi x)) a -> pzone E x a.
Proof.
  intros E x v' a E1 E2 X. unfold parse_new in X. unfold pzone. rewrite E1, E2 in X.
  destruct X as [X|[X|X]]; [right; right; left; exact X| |].
  - right; right; right; left. destruct (x_va x); [exact X| destruct X].
  - right; right; right; right; left. destruct (x_vi x); [exact X| destruct X].
Qed.


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
Ltac pinv_close PE0 AINV MU WM WZ :=
  try pinv_triv;
  try lazymatch goal with
  | |- _ Fstate = stU _ => match goal with S : _ Fstate = stU ?s, E : ?s = _ |- _ => rewrite S, E; reflexivity end
  | |- vep_obj _ _ _ _ _ _ _ => split; [assumption|]; split; [unfold vep_cells; psimp;
                                  try match goal with S : _ Fstate = stU _ |- _ => rewrite S end; assumption|]; split; assumption
  | |- bool01 _ /\ _ => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | left; reflexivity | right; reflexivity]
  | |- (_ -> _ = 0) /\ (_ -> _) =>
      split; [ intros _; first [assumption | reflexivity | match goal with H : _ -> ?v = 0 |- ?v = 0 => apply H; discriminate end]
             | let X := fresh "X" in intros X; first [discriminate X | match goal with H : _ -> ?c |- ?c => apply H; reflexivity end] ]
  | |- _ = _ -> _ \/ _ => intros _; first [assumption | left; reflexivity | right; left; reflexivity | right; right; left; reflexivity | right; right; right; reflexivity
                                 | match goal with H : _ -> ?c |- ?c => apply H; reflexivity end]
  | |- _ = 0 \/ (_ = TBL_attr_include /\ _ = vi_do_include VIU /\ _) =>
      match goal with
      | H : _ = 0 \/ (_ = TBL_attr_include /\ _ = vi_do_include VIU /\ ?R) |- _ =>
          let A0 := fresh in let A1 := fresh in let A2 := fresh in let A3 := fresh in
          destruct H as [A0|(A1 & A2 & A3)];
          [ left; exact A0
          | first [ right; split; [exact A1|]; split; [exact A2|];
                    first [ left; exact I | left; reflexivity | left; assumption
                          | right; left; reflexivity | right; right; left; reflexivity | right; right; right; reflexivity ]
                  | exfalso; revert A3; clear; intros A3;
                    repeat (destruct A3 as [A3|A3]); first [exact A3 | discriminate A3 | revert A3; cbv; congruence] ] ]
      end
  | |- vsb_obj _ _ _ _ _ _ => eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV MU WM WZ); [in_list| in_list| assumption]
  | |- data_obj _ _ _ _ _ => first [ split; [assumption| split; assumption] | eapply (data_obj_stores _ _ _ _ _ _ _ PE0 AINV MU WZ); [in_list| assumption] ]
  | |- henv_ok _ _ _ _ => first [assumption | eapply (henv_stores _ _ _ _ _ _ _ PE0 AINV MU WM WZ); [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn [outside]; unfold h_vsc, pe_sp in *; lia| assumption] ]
  | |- hobj_ok _ _ _ _ => first [assumption | eapply (hobj_stores _ _ _ _ _ _ _ PE0 AINV MU WM WZ); assumption ]
  | |- img_okU _ => first [assumption | eapply (img_stores _ _ _ _ _ _ _ PE0 AINV MU WZ); assumption ]
  | |- exists j0 j8 j16 j24, rw_cells _ _ _ (pframe _ j0 j8 j16 j24) => eexists _, _, _, _; unfold pframe; eassumption
  | |- _ <= 3 * _ + 4 * _ => psimp;
        match goal with H : _ <= 3 * _ + 4 * _ |- _ => revert H; clear; intros; cbv [oacost oicost x_va x_vi] in *; lia end
  | |- match ?o with Some _ => _ | None => _ end =>
      match goal with
      | H : match o with Some _ => _ /\ _ /\ _ | None => _ end |- _ =>
          (* [comment removed for export] *)
          destruct o eqn:?; [| exact H];
          let H1 := fresh in let H2 := fresh in let H3 := fresh in
          (first [ dand3 H as H1 H2 H3 | destruct H as (H1 & H2 & H3) ]);
          refine (conj H1 (conj _ H3));
          eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV MU WM WZ); [in_list| in_list| exact H2]
      end
  | |- _ => idtac
  end.

(* [comment removed for export] *)
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

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mod8_of_mod16 : forall a, a mod 16 = 0 -> a mod 8 = 0.
Proof. intros a H. apply Z.mod_divide in H; [|lia]. destruct H as [k EK]. rewrite EK. replace (k * 16) with ((k * 2) * 8) by lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HStepCall.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.

  Lemma hstep_call1 : forall E x1 x2 A A' m1 m2 win V b n' b',
    cframe LayoutPU (owned A) (owned A') (pe_sp E) win V (blk b' n') m1 m2 -> win + 208 <= PARSE_STACK ->
    mapped m2 (h_sp (pe_H E) - PARSE_STACK) PARSE_STACK ->
    (forall a, V a -> pzone E x1 a) ->
    (forall r, r <> b -> r <> b' -> a_live A' r = a_live A r) ->
    (b' = b \/ (a_live A b' = None /\ a_live A' b = None)) ->
    pst_blocks x1 b ->
    (forall p, pst_blocks x2 p -> pst_blocks x1 p \/ p = b') ->
    (forall a, parse_new (x_v x2) (x_vv x2) (x_va x2) (option_map (fun y => (y, true)) (x_vi x2)) a ->
               blk b' n' a \/ pzone E x1 a) ->
    hstep E x1 x2 A A' m1 m2.
  Proof.
    intros E x1 x2 A A' m1 m2 win V b n' b' CF WIN MAP HV LIVE REL PB PB2 PN.
    eapply (hstep_intro E x1 x2 A A' m1 m2 PARSE_STACK V (blk b' n')).
    - eapply cframe_rebase; [exact CF| exact WIN| exact MAP].
    - lia.
    - exact MAP.
    - exact HV.
    - exact PN.
    - intros p k Hp NB. assert (p <> b) by (intros ->; exact (NB PB)).
      destruct REL as [EB|[F1 F2]].
      + rewrite LIVE; [exact Hp| assumption| rewrite EB; assumption].
      + assert (p <> b') by (intros ->; congruence). rewrite LIVE; assumption.
    - intros p Hp. destruct (PB2 p Hp) as [X| ->]; [left; exact X|].
      destruct REL as [EB|[F1 F2]]; [left; rewrite EB; exact PB| right; exact F1].
  Qed.

  (* [comment removed for export] *)
  Lemma hstep_call0 : forall E x1 x2 A A' m1 m2 win V,
    cframe LayoutPU (owned A) (owned A') (pe_sp E) win V nowhere m1 m2 -> win + 208 <= PARSE_STACK ->
    mapped m2 (h_sp (pe_H E) - PARSE_STACK) PARSE_STACK ->
    (forall a, V a -> pzone E x1 a) ->
    (forall p k, a_live A p = Some k -> ~ pst_blocks x1 p -> a_live A' p = Some k) ->
    (forall p, pst_blocks x2 p -> pst_blocks x1 p \/ a_live A p = None) ->
    (forall a, parse_new (x_v x2) (x_vv x2) (x_va x2) (option_map (fun y => (y, true)) (x_vi x2)) a -> pzone E x1 a) ->
    hstep E x1 x2 A A' m1 m2.
  Proof.
    intros E x1 x2 A A' m1 m2 win V CF WIN MAP HV L1 L2 PN.
    eapply (hstep_intro E x1 x2 A A' m1 m2 PARSE_STACK V nowhere).
    - eapply cframe_rebase; [exact CF| exact WIN| exact MAP].
    - lia.
    - exact MAP.
    - exact HV.
    - intros a Ha. right. apply PN, Ha.
    - exact L1.
    - exact L2.
  Qed.
End HStepCall.

Section LiveKeep.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutPU}.
  (* [comment removed for export] *)
  Lemma live_keep : forall (A A' : AS) (b b' p k : Z),
    (forall r, r <> b -> r <> b' -> a_live A' r = a_live A r) ->
    (b' = b \/ (a_live A b' = None /\ a_live A' b = None)) ->
    a_live A p = Some k -> p <> b -> a_live A' p = Some k.
  Proof.
    intros A A' b b' p k LIVE REL Hp NB. destruct REL as [EB|[F1 F2]].
    - rewrite LIVE; [exact Hp| exact NB| rewrite EB; exact NB].
    - assert (p <> b') by (intros ->; congruence). rewrite LIVE; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma fresh_ne : forall (A A' : AS) (b b' p k : Z),
    (b' = b \/ (a_live A b' = None /\ a_live A' b = None)) ->
    a_live A p = Some k -> p <> b -> p <> b'.
  Proof. intros A A' b b' p k [EB|[F1 F2]] Hp NB; [congruence| intros ->; congruence]. Qed.
End LiveKeep.

(* [comment removed for export] *)
Ltac world_call H CV CF AINV LIVE REL NB1 NB2 :=
  lazymatch type of H with
  | match ?o with Some _ => _ | None => _ end =>
      let EQ := fresh "EQo" in
      destruct o eqn:EQ; [| exact H];
      let body H2 :=
          eapply (vsb_obj_call _ _ _ _ _ _ _ _ _ _ _ AINV CF);
          [ match goal with HG : henv_geom _ |- _ => exact HG end
          | stk_lia
          | exact CV | in_list | in_list
          | eapply (live_keep _ _ _ _ _ _ LIVE REL); [exact (proj1 (proj2 (proj2 H2)))
              | first [exact NB1 | unfold oabuf, oibuf in NB1; rewrite EQ in NB1; exact NB1] ]
          | eapply (live_keep _ _ _ _ _ _ LIVE REL); [exact (proj1 (proj2 (proj2 (proj2 H2))))
              | first [exact NB2 | unfold oabuf, oibuf in NB2; rewrite EQ in NB2; exact NB2] ]
          | exact H2 ] in
      first
        [ (* [comment removed for export] *)
          let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in let H5 := fresh in
          (first [ dand5 H as H1 H2 H3 H4 H5 | destruct H as (H1 & H2 & H3 & H4 & H5) ]);
          refine (conj H1 (conj _ (conj H3 (conj H4 H5)))); body H2
        | let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in
          (first [ dand4 H as H1 H2 H3 H4 | destruct H as (H1 & H2 & H3 & H4) ]);
          refine (conj H1 (conj _ (conj H3 H4))); body H2 ]
  end.

(* [comment removed for export] *)
Ltac world_stores H PE0 AINV MU WM WZ :=
  lazymatch type of H with
  | match ?o with Some _ => _ | None => _ end =>
      let EQ := fresh "EQo" in
      destruct o eqn:EQ; [| exact H];
      let body H2 := eapply (vsb_obj_stores _ _ _ _ _ _ _ PE0 AINV MU WM WZ); [in_list| in_list| exact H2] in
      first
        [ let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in let H5 := fresh in
          (first [ dand5 H as H1 H2 H3 H4 H5 | destruct H as (H1 & H2 & H3 & H4 & H5) ]);
          refine (conj H1 (conj _ (conj H3 (conj H4 H5)))); body H2
        | let H1 := fresh in let H2 := fresh in let H3 := fresh in let H4 := fresh in
          (first [ dand4 H as H1 H2 H3 H4 | destruct H as (H1 & H2 & H3 & H4) ]);
          refine (conj H1 (conj _ (conj H3 H4))); body H2 ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mark_nf : forall f, existsb (vf_beq f) MARK_FIELDS = false -> ~ In f MARK_FIELDS.
Proof.
  intros f H IN. apply Bool.not_true_iff_false in H. apply H. apply existsb_exists. exists f. split; [exact IN| apply vf_beq_refl].
Qed.

(* [comment removed for export] *)
Ltac vk_norm VK :=
  rewrite ?(VK Fflags (mark_nf Fflags eq_refl)), ?(VK Fvsb (mark_nf Fvsb eq_refl)), ?(VK Furl (mark_nf Furl eq_refl)), ?(VK Fvc (mark_nf Fvc eq_refl)), ?(VK Fdogzip (mark_nf Fdogzip eq_refl)), ?(VK Fcb (mark_nf Fcb eq_refl)), ?(VK Fcb_priv (mark_nf Fcb_priv eq_refl)), ?(VK Fstate (mark_nf Fstate eq_refl)), ?(VK Fstartup (mark_nf Fstartup eq_refl)), ?(VK Fesi_found (mark_nf Fesi_found eq_refl)), ?(VK Fendtag (mark_nf Fendtag eq_refl)), ?(VK Femptytag (mark_nf Femptytag eq_refl)), ?(VK Fcanattr (mark_nf Fcanattr eq_refl)), ?(VK Fremove (mark_nf Fremove eq_refl)), ?(VK Fhack_p (mark_nf Fhack_p eq_refl)), ?(VK Funtil (mark_nf Funtil eq_refl)), ?(VK Funtil_p (mark_nf Funtil_p eq_refl)), ?(VK Funtil_s (mark_nf Funtil_s eq_refl)), ?(VK Fin_esi_tag (mark_nf Fin_esi_tag eq_refl)), ?(VK Fesicmt (mark_nf Fesicmt eq_refl)), ?(VK Fesicmt_p (mark_nf Fesicmt_p eq_refl)), ?(VK Fattr (mark_nf Fattr eq_refl)), ?(VK Fattr_vsb (mark_nf Fattr_vsb eq_refl)), ?(VK Fattr_delim (mark_nf Fattr_delim eq_refl)), ?(VK Fmatch (mark_nf Fmatch eq_refl)), ?(VK Fmatch_hit (mark_nf Fmatch_hit eq_refl)), ?(VK Ftag_i (mark_nf Ftag_i eq_refl)), ?(VK Fdostuff (mark_nf Fdostuff eq_refl)), ?(VK Finclude_src (mark_nf Finclude_src eq_refl)), ?(VK Finclude_continue (mark_nf Finclude_continue eq_refl)), ?(VK Fnm_skip (mark_nf Fnm_skip eq_refl)), ?(VK Fnm_verbatim (mark_nf Fnm_verbatim eq_refl)), ?(VK Fnm_pending (mark_nf Fnm_pending eq_refl)).
Ltac vk_norm_in VK H :=
  rewrite ?(VK Fflags (mark_nf Fflags eq_refl)), ?(VK Fvsb (mark_nf Fvsb eq_refl)), ?(VK Furl (mark_nf Furl eq_refl)), ?(VK Fvc (mark_nf Fvc eq_refl)), ?(VK Fdogzip (mark_nf Fdogzip eq_refl)), ?(VK Fcb (mark_nf Fcb eq_refl)), ?(VK Fcb_priv (mark_nf Fcb_priv eq_refl)), ?(VK Fstate (mark_nf Fstate eq_refl)), ?(VK Fstartup (mark_nf Fstartup eq_refl)), ?(VK Fesi_found (mark_nf Fesi_found eq_refl)), ?(VK Fendtag (mark_nf Fendtag eq_refl)), ?(VK Femptytag (mark_nf Femptytag eq_refl)), ?(VK Fcanattr (mark_nf Fcanattr eq_refl)), ?(VK Fremove (mark_nf Fremove eq_refl)), ?(VK Fhack_p (mark_nf Fhack_p eq_refl)), ?(VK Funtil (mark_nf Funtil eq_refl)), ?(VK Funtil_p (mark_nf Funtil_p eq_refl)), ?(VK Funtil_s (mark_nf Funtil_s eq_refl)), ?(VK Fin_esi_tag (mark_nf Fin_esi_tag eq_refl)), ?(VK Fesicmt (mark_nf Fesicmt eq_refl)), ?(VK Fesicmt_p (mark_nf Fesicmt_p eq_refl)), ?(VK Fattr (mark_nf Fattr eq_refl)), ?(VK Fattr_vsb (mark_nf Fattr_vsb eq_refl)), ?(VK Fattr_delim (mark_nf Fattr_delim eq_refl)), ?(VK Fmatch (mark_nf Fmatch eq_refl)), ?(VK Fmatch_hit (mark_nf Fmatch_hit eq_refl)), ?(VK Ftag_i (mark_nf Ftag_i eq_refl)), ?(VK Fdostuff (mark_nf Fdostuff eq_refl)), ?(VK Finclude_src (mark_nf Finclude_src eq_refl)), ?(VK Finclude_continue (mark_nf Finclude_continue eq_refl)), ?(VK Fnm_skip (mark_nf Fnm_skip eq_refl)), ?(VK Fnm_verbatim (mark_nf Fnm_verbatim eq_refl)), ?(VK Fnm_pending (mark_nf Fnm_pending eq_refl)) in H.


(* [comment removed for export] *)
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. rewrite unsigned_lit by lia. f_equal. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 32) with 32. rewrite Z.mod_small; [change (2 ^ 32 / 2) with (2^31); lia|].
  change (2 ^ 32 / 2) with (2^31). lia.
Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac if_lit :=
  let K := fresh "K" in
  if_cases K; zify_cond K; first [ exfalso; revert K; vm_compute; congruence | clear K ].

Lemma swrap32_small : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (Z.of_N 32) with 32. rewrite Z.mod_small; [change (2 ^ 32 / 2) with (2^31); lia|].
  change (2 ^ 32 / 2) with (2^31). lia.
Qed.
