(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_App.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive vstate : Type :=
  S_Start | S_BOM | S_TestXml | S_NotXml | S_NotMyTag | S_NxtTag | S_StartTag | S_Comment | S_CommentESI
| S_CDATA | S_end_ESITag | S_ESITag | S_ESI_Include | S_ESI_Remove | S_ESI_Comment | S_ESI_Bogon
| S_InTag | S_TagError | S_Attr | S_SkipAttribute | S_AttrGetValue | S_AttrDelim | S_AttrValue
| S_Until | S_Match | S_MatchBuf.

Record vimg : Type := VIMG {
  vi_bss_vsc    : Z;   (* [comment removed for export] *)
  vi_bss_cp     : Z;   (* [comment removed for export] *)
  vi_cb         : Z;   (* [comment removed for export] *)
  vi_do_include : Z;
  vi_do_remove  : Z;
  vi_do_comment : Z;
  vi_st         : vstate -> Z;   (* [comment removed for export] *)
  vi_stvar      : vstate -> Z;   (* [comment removed for export] *)
  vi_wsid       : Z;   (* [comment removed for export] *)
  vi_url        : Z;   (* [comment removed for export] *)
  vi_empty      : Z;   (* [comment removed for export] *)
  vi_arrow      : Z;   (* [comment removed for export] *)
  vi_cdata_end  : Z;   (* [comment removed for export] *)
  vi_tbl_bom : Z; vi_tbl_starttag : Z; vi_tbl_esi : Z; vi_tbl_attr_include : Z
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record henv : Type := HENV {
  h_ff : Z      (* [comment removed for export] *)
}.
Definition HCLASS : Z := 7.
Definition HFSIZE : Z := 8192.            (* [comment removed for export] *)
Definition h_vsc    (H : henv) : Z := h_ff H + 32.     (* [comment removed for export] *)
Definition h_cp     (H : henv) : Z := h_ff H + 1536.   (* [comment removed for export] *)
Definition h_req    (H : henv) : Z := h_ff H + 2416.   (* [comment removed for export] *)
Definition h_resp   (H : henv) : Z := h_ff H + 2512.   (* [comment removed for export] *)
Definition h_vc     (H : henv) : Z := h_ff H + 2608.   (* [comment removed for export] *)
Definition h_wrk    (H : henv) : Z := h_ff H + 2720.   (* [comment removed for export] *)
Definition h_ws     (H : henv) : Z := h_ff H + 2976.   (* [comment removed for export] *)
Definition h_vsbloc (H : henv) : Z := h_ff H + 3056.   (* [comment removed for export] *)
Definition h_hd     (H : henv) : Z := h_ff H + 3088.   (* [comment removed for export] *)
Definition h_wsbuf  (H : henv) : Z := h_ff H + 3152.   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition HOBJ_END : Z := 4176.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fsize_div8 : forall k, (fsize k + 7) / 8 = fsize k / 8.
Proof. intros k. unfold fsize. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
Definition http_cells (hd : Z) (mid : list byte) (ws : Z) (tl : list byte) (pad : list byte) : list cell :=
  [ C4 (Z_to_bv 64 HTTP_MAGIC); CB 4 pad; C8 (Z_to_bv 64 hd); CB 24 mid; C8 (Z_to_bv 64 ws); CB 8 tl ].

Section World.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context (L : clayout) {AI : AsanAlloc L}.
  Let segs := cl_segs L.

  (* [comment removed for export] *)
  Definition henv_geom (H : henv) : Prop :=
    h_ff H mod 4096 = 0 /\ app_range L (h_ff H) HFSIZE (* [comment removed for export] *) /\ h_ff H + HFSIZE <= alloc_ceiling.

  (* [comment removed for export] *)
  Definition hframe (A : AS) (H : henv) : Prop := exists age, a_frame A (h_ff H) = Some (HCLASS, age).

  (* [comment removed for export] *)
  Definition shadowed (v : mem) (a n : Z) : Prop :=
    exists p sz, bytes_at segs v (sh p) (shpat sz) /\ p mod 8 = 0 /\ 0 <= p /\ p <= a /\ a + n <= p + sz
                 /\ p + sz <= alloc_ceiling.

  Lemma shadowed_sub : forall v a n a' n', shadowed v a n -> a <= a' -> a' + n' <= a + n -> shadowed v a' n'.
  Proof.
    (intros v a n a' n'; (first [ intro dR_47; dex2 dR_47 as p sz; dand6 dR_47 as B AL P0 LO HI CE | intro dR_47; dand8 dR_47 as p sz B AL P0 LO HI CE | intros (p & sz & B & AL & P0 & LO & HI & CE) ]); intros Ha Hn). exists p, sz.
    split; [exact B|]. split; [exact AL|]. split; [exact P0|]. split; [lia|]. split; [lia| exact CE].
  Qed.

  (* [comment removed for export] *)
  Definition consts_hold (v : mem) : Prop :=
    Forall (fun c => bytes_at segs v (fst c) (snd c)) (cl_consts L).

  Lemma consts_hold_ainv : forall A m md, ainv A m md -> consts_hold (aview A m).
  Proof. intros A m md AI0. exact (as_consts L A m md AI0). Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hshadow (H : henv) (v : mem) : Prop :=
       bytes_at segs v (sh (h_vsc H)) (shpat 1368) /\ bytes_at segs v (sh (h_cp H)) (shpat 752)
    /\ bytes_at segs v (sh (h_req H)) (shpat 56) /\ bytes_at segs v (sh (h_resp H)) (shpat 56)
    /\ bytes_at segs v (sh (h_vc H)) (shpat 72) /\ bytes_at segs v (sh (h_wrk H)) (shpat 184)
    /\ bytes_at segs v (sh (h_ws H)) (shpat 40) /\ bytes_at segs v (sh (h_vsbloc H)) (shpat 8)
    /\ bytes_at segs v (sh (h_hd H)) (shpat 32) /\ bytes_at segs v (sh (h_wsbuf H)) (shpat 1024).

  (* [comment removed for export] *)
  Definition glob_ok (V : vimg) (H : henv) (v : mem) : Prop :=
       rw_cells segs v (vi_bss_vsc V) [C8 (Z_to_bv 64 (h_vsc H))]
    /\ rw_cells segs v (vi_bss_cp V) [C8 (Z_to_bv 64 (h_cp H))]
    /\ rw_cells segs v (h_cp H) [CB 752 (repeat (Z_to_bv 8 0) 752)]
    /\ (exists bs, rw_cells segs v (h_vsc H + 1304) [CB 16 bs]).   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hobj_ok (V : vimg) (H : henv) (v : mem) : Prop :=
       (exists pad rest, length pad = 12%nat /\ length rest = 40%nat /\
          rw_cells segs v (h_vc H) (vc_cells pad (h_resp H) (h_wrk H) rest))
    /\ (exists pad rest, length pad = 28%nat /\ length rest = 144%nat /\ rw_cells segs v (h_wrk H) (wrk_cells pad rest))
    /\ (exists mid tl pad, length mid = 24%nat /\ length tl = 8%nat /\ length pad = 4%nat /\
          rw_cells segs v (h_req H) (http_cells (h_hd H) mid (h_ws H) tl pad))
    /\ (exists hd mid tl pad, length mid = 24%nat /\ length tl = 8%nat /\ length pad = 4%nat /\
          rw_cells segs v (h_resp H) (http_cells hd mid (h_ws H) tl pad))
    /\ rw_cells segs v (h_hd H + 16) [C8 (Z_to_bv 64 (vi_url V))].

  (* [comment removed for export] *)
  Definition henv_ok (V : vimg) (H : henv) (A : AS) (v : mem) : Prop :=
    hframe A H /\ glob_ok V H v /\ hobj_ok V H v /\ hshadow H v.

  (* [comment removed for export] *)
  Definition ws_id_req : list byte := [Z_to_bv 8 114; Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0].   (* [comment removed for export] *)
  Definition ws_id_Req : list byte := [Z_to_bv 8 82; Z_to_bv 8 101; Z_to_bv 8 113; Z_to_bv 8 0].    (* [comment removed for export] *)
  Definition ws_id_ok (id : list byte) : Prop := id = ws_id_req \/ id = ws_id_Req.

  Definition ws_rec_of (H : henv) (id : list byte) : ws_rec := WSR id (h_wsbuf H) 0 0 (h_wsbuf H + 1016).

  Definition ws0_obj (H : henv) (v : mem) : Prop :=
    exists id, ws_id_ok id /\
      rw_cells segs v (h_ws H) (ws_cells (ws_rec_of H id)) /\
      rw_cells segs v (h_wsbuf H) (wsemu_cells (wsemu_WS0 (h_wsbuf H))).

  Definition ws1_obj (H : henv) (A : AS) (v : mem) (wa vep : Z) : Prop :=
    exists id pad, ws_id_ok id /\ length pad = 4%nat /\
      rw_cells segs v (h_ws H) (ws_cells (ws_rec_of H id)) /\
      rw_cells segs v (h_wsbuf H) (wsemu_cells (wsemu_WS1 wa)) /\
      a_live A wa = Some 40 /\ rw_cells segs v wa (wsalloc_cells (wsalloc_WS1 (h_wsbuf H) vep) pad) /\
      a_live A vep = Some 312.

  (* [comment removed for export] *)
  Definition vep_obj (A : AS) (v : mem) (VEP : Z) (vv : vep) (tag : list byte) (q : vep_pads) : Prop :=
    a_live A VEP = Some 312 /\ rw_cells segs v VEP (vep_cells vv tag q) /\ length tag = 8%nat /\ vep_pads_wf q.

  (* [comment removed for export] *)
  Definition data_obj (A : AS) (v : mem) (DATA : Z) (inp : list byte) : Prop :=
    a_live A DATA = Some (Z.of_nat (length inp)) /\ bytes_at segs v DATA inp /\ 1 <= Z.of_nat (length inp) < 2^26.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma henv_geom_of_frame : forall A m md H, ainv A m md -> hframe A H -> henv_geom H.
  Proof.
    intros A m md H AI0 [age HF].
    (first [ pose proof ((as_frame_ok L A m md _ _ _ AI0 HF)) as dR_1; dand5 dR_1 as _ AL LO HI _ | destruct (as_frame_ok L A m md _ _ _ AI0 HF) as (_ & AL & LO & HI & _) ]).
    unfold henv_geom, HFSIZE. change (fsize HCLASS) with 8192 in AL, HI.
    change (Z.min 8192 4096) with 4096 in AL. split; [exact AL|]. split; [exact LO| exact HI].
  Qed.

  (* [comment removed for export] *)
  Lemma hframe_crange : forall A m md H a n,
    ainv A m md -> hframe A H -> h_ff H <= a -> a + n <= h_ff H + HOBJ_END -> 0 <= n ->
    crange A (aview A m) a n.
  Proof.
    intros A m md H a n AI0 [age HF] Ha Hn Hn0.
    eapply (crange_fframe A m md _ _ _ a n AI0 HF Ha); [| exact Hn0].
    change (fsize HCLASS) with 8192. unfold HOBJ_END in Hn. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition hvis (H : henv) (v : mem) : Prop :=
    forall a, h_ff H <= a < h_ff H + HOBJ_END -> mapped v (sh a - sh a mod 8) 8.

  Lemma hvis_intro : forall A m md H, ainv A m md -> hframe A H -> hvis H (aview A m).
  Proof.
    intros A m md H AI0 [age HF] a Ha.
    (first [ pose proof ((as_frame_ok L A m md _ _ _ AI0 HF)) as dR_3; dand11 dR_3 as _ _ LO HI _ _ MP _ _ NO _ | destruct (as_frame_ok L A m md _ _ _ AI0 HF) as (_ & _ & LO & HI & _ & _ & MP & _ & _ & NO & _) ]).
    change (fsize HCLASS) with 8192 in LO, HI, MP, NO. unfold HOBJ_END in Ha.
    pose proof layout_facts as LF. app_facts_of LO Bnd IMG NS SA. pose proof alloc_ceiling_num as ACN.   (* [comment removed for export] *)
    apply (as_shadow_visible L A m md a AI0).
    - unfold kLowMemEnd, kHighMemBeg. destruct NS as [NS|NS]; [left; lia| right; lia].
    - replace a with (h_ff H + (a - h_ff H)) by lia. apply NO. lia.
    - right. unfold aview_of. fold (aview A m). replace a with (h_ff H + (a - h_ff H)) by lia. apply MP. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition cobj (A : AS) (v : mem) (excl : list Z) (a n : Z) : Prop :=
    (exists p k, a_live A p = Some k /\ ~ In p excl /\ p <= a /\ a + n <= p + k)
    \/ (exists ff kk age p sz, a_frame A ff = Some (kk, age) /\ ff <= p /\ p + sz <= ff + fsize kk - 8 /\
          p mod 8 = 0 /\ p <= a /\ a + n <= p + sz /\ bytes_at segs v (sh p) (shpat sz)).

  Lemma cobj_hframe : forall A v excl H a n p sz,
    hframe A H -> h_ff H <= p -> p + sz <= h_ff H + HOBJ_END -> p mod 8 = 0 -> p <= a -> a + n <= p + sz ->
    bytes_at segs v (sh p) (shpat sz) -> cobj A v excl a n.
  Proof.
    intros A v excl H a n p sz [age HF] H1 H2 H3 H4 H5 B. right.
    exists (h_ff H), HCLASS, age, p, sz. change (fsize HCLASS) with 8192. unfold HOBJ_END in H2.
    split; [exact HF|]. split; [lia|]. split; [lia|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5| exact B].
  Qed.

  Lemma cobj_block : forall A v excl a n p k,
    a_live A p = Some k -> ~ In p excl -> p <= a -> a + n <= p + k -> cobj A v excl a n.
  Proof. intros A v excl a n p k LV NI H1 H2. left. exists p, k. split; [exact LV|]. split; [exact NI|]. split; [exact H1| exact H2]. Qed.

  (* [comment removed for export] *)
  Lemma sh_sep : forall x n y, x + n <= y -> y mod 8 = 0 -> 0 <= x -> sh x + (n + 7) / 8 <= sh y.
  Proof.
    intros x n y Hxy Hy Hx. unfold sh.
    pose proof (Z.div_mod y 8 ltac:(lia)) as Dy. rewrite Hy, Z.add_0_r in Dy.
    pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
    assert ((n + 7) / 8 < y / 8 - x / 8 + 1); [|lia].
    apply Z.div_lt_upper_bound; [lia|]. nia.
  Qed.

  (* [comment removed for export] *)
  Lemma fframe_al8 : forall A m md ff k age, ainv A m md -> a_frame A ff = Some (k, age) -> ff mod 8 = 0.
  Proof.
    intros A m md ff k age AI0 HF.
    (first [ pose proof ((as_frame_ok L A m md ff k age AI0 HF)) as dR_4; dand3 dR_4 as K0 AL _ | destruct (as_frame_ok L A m md ff k age AI0 HF) as (K0 & AL & _) ]).
    assert (D8 : exists q, Z.min (fsize k) 4096 = 8 * q /\ 0 < q).
    { unfold fsize. destruct (Z.min_spec (64 * 2 ^ k) 4096) as [[_ ->]|[_ ->]].
      - exists (8 * 2 ^ k). pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). lia.
      - exists 512. lia. }
    (first [ dex1 D8 as q; destruct D8 as [E Q] | dand3 D8 as q E Q | destruct D8 as (q & E & Q) ]). rewrite E in AL.
    apply Z.mod_divide in AL; [|lia]. destruct AL as [c Hc]. rewrite Hc.
    replace (c * (8 * q)) with ((c * q) * 8) by lia. apply Z.mod_mul. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma newblk_avoids_fshadow : forall A m md q k ff kk age x,
    ainv A m md -> a_live A q = Some k -> a_frame A ff = Some (kk, age) -> newblk q k x ->
    ~ (sh ff <= x < sh ff + fsize kk / 8).
  Proof.
    intros A m md q k ff kk age x AI0 LV HF X.
    (first [ pose proof ((live_geom L A m md q k AI0 LV)) as dR_6; dand5 dR_6 as K0 Q16 QLO QHI _ | destruct (live_geom L A m md q k AI0 LV) as (K0 & Q16 & QLO & QHI & _) ]).
    (first [ pose proof ((fframe_geom L A m md ff kk age AI0 HF)) as dR_7; dand5 dR_7 as _ FS FLO FHI _ | destruct (fframe_geom L A m md ff kk age AI0 HF) as (_ & FS & FLO & FHI & _) ]).
    pose proof (fframe_al8 A m md ff kk age AI0 HF) as F8.
    pose proof (as_frame_blk_disjoint L A m md ff kk age q k AI0 HF LV) as DJ.
    pose proof layout_facts as LF. unfold kHighMemBeg in *.
    (first [ pose proof ((app_facts L ff (fsize kk) FLO)) as dR_8; dand4 dR_8 as FB _ FNS _ | pose proof (app_facts L ff (fsize kk) FLO) as (FB & _ & FNS & _) ]). (first [ pose proof ((app_facts L q k QLO)) as dR_9; dand4 dR_9 as QB _ QNS _ | pose proof (app_facts L q k QLO) as (QB & _ & QNS & _) ]).   (* [comment removed for export] *)
    assert (Q8 : q mod 8 = 0).
    { pose proof (Z.div_mod q 16 ltac:(lia)) as D. rewrite Q16, Z.add_0_r in D. rewrite D at 1.
      replace (16 * (q / 16)) with ((2 * (q / 16)) * 8) by lia. apply Z.mod_mul. lia. }
    assert (FF8 : (ff + fsize kk) mod 8 = 0).
    { rewrite Z.add_mod, F8 by lia. unfold fsize. replace (64 * 2 ^ kk) with ((8 * 2 ^ kk) * 8) by lia.
      rewrite Z.mod_mul by lia. reflexivity. }
    assert (SF : sh ff + fsize kk / 8 = sh (ff + fsize kk)).
    { unfold sh. pose proof (Z.div_mod ff 8 ltac:(lia)) as D. rewrite F8, Z.add_0_r in D. rewrite D at 2.
      unfold fsize. replace (8 * (ff / 8) + 64 * 2 ^ kk) with ((ff / 8 + 8 * 2 ^ kk) * 8) by lia.
      rewrite Z.div_mul by lia. replace (64 * 2 ^ kk) with ((8 * 2 ^ kk) * 8) by lia. rewrite Z.div_mul by lia. lia. }
    unfold newblk, blk in X. destruct X as [[_ X]|[_ X]].
    - (* [comment removed for export] *)
      intros [H1 H2].
      (first [ pose proof ((app_sh_facts L ff (fsize kk) FLO)) as dR_10; dand4 dR_10 as SF1 SF2 SF3 _ | pose proof (app_sh_facts L ff (fsize kk) FLO) as (SF1 & SF2 & SF3 & _) ]).
      pose proof SHMAX_below_highmem as SBH. unfold kHighMemBeg in SBH.
      pose proof (fsize_div8 kk) as E8.
      rewrite E8 in SF2. unfold sh, kShadowOffset in *. lia.
    - intros [H1 H2]. destruct DJ as [DJ|DJ].
      + (* [comment removed for export] *)
        pose proof (sh_sep ff (fsize kk) q ltac:(lia) Q8 ltac:(lia)) as SS.
        replace (fsize kk + 7) with (fsize kk / 8 * 8 + 7) in SS by (unfold fsize; nia).
        rewrite Z.div_add_l in SS by lia. change (7 / 8) with 0 in SS. lia.
      + (* [comment removed for export] *)
        pose proof (sh_sep q k ff DJ F8 ltac:(lia)) as SS. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma high_avoids_fshadow : forall A m md ff kk age x,
    ainv A m md -> a_frame A ff = Some (kk, age) -> kHighMemBeg <= x -> ~ (sh ff <= x < sh ff + fsize kk / 8).
  Proof.
    intros A m md ff kk age x AI0 HF Hx [H1 H2].
    (first [ pose proof ((fframe_geom L A m md ff kk age AI0 HF)) as dR_11; dand5 dR_11 as _ FS FLO FHI _ | destruct (fframe_geom L A m md ff kk age AI0 HF) as (_ & FS & FLO & FHI & _) ]).
    (* [comment removed for export] *)
    (first [ pose proof ((app_sh_facts L ff (fsize kk) FLO)) as dR_12; dand4 dR_12 as SF1 SF2 SF3 _ | pose proof (app_sh_facts L ff (fsize kk) FLO) as (SF1 & SF2 & SF3 & _) ]).
    pose proof SHMAX_below_highmem as SBH.
    pose proof (fsize_div8 kk) as E8.
    rewrite E8 in SF2. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition chome (A : AS) (excl : list Z) (p0 sz0 : Z) : Prop :=
       (a_live A p0 = Some sz0 /\ ~ In p0 excl)
    \/ (exists ff kk age, a_frame A ff = Some (kk, age) /\ ff <= p0 /\ p0 + sz0 <= ff + fsize kk - 8).

  Lemma cobj_open : forall A m md excl a n,
    ainv A m md -> cobj A (aview A m) excl a n -> 0 < n ->
    exists p0 sz0,
      bytes_at segs (aview A m) (sh p0) (shpat sz0) /\ p0 mod 8 = 0 /\ app_range L p0 sz0 (* [comment removed for export] *) /\ p0 <= a /\ a + n <= p0 + sz0
      /\ p0 + sz0 <= alloc_ceiling /\ chome A excl p0 sz0 /\ crange A (aview A m) a n
      /\ (forall q k, a_live A q = Some k -> In q excl -> a + n <= q - 16 \/ q + k <= a \/ (a + n <= q /\ k = k)).
  Proof.
    intros A m md excl a n AI0 CO N0. pose proof layout_facts as LF.
    destruct CO as [(p & k & LV & NI & P1 & P2) | (ff & kk & age & p & sz & HF & F1 & F2 & P8 & P1 & P2 & B)].
    - (first [ pose proof ((live_geom L A m md p k AI0 LV)) as dR_20; dand5 dR_20 as K0 P16 PLO PHI _ | destruct (live_geom L A m md p k AI0 LV) as (K0 & P16 & PLO & PHI & _) ]).
      assert (P8 : p mod 8 = 0).
      { pose proof (Z.div_mod p 16 ltac:(lia)) as D. rewrite P16, Z.add_0_r in D. rewrite D at 1.
        replace (16 * (p / 16)) with ((2 * (p / 16)) * 8) by lia. apply Z.mod_mul. lia. }
      exists p, k. split; [exact (as_live_shadow L A m md p k AI0 LV)|]. split; [exact P8|]. split; [exact PLO|].
      split; [exact P1|]. split; [exact P2|]. split; [exact PHI|]. split; [left; split; [exact LV| exact NI]|].
      split; [eapply crange_block; [exact AI0| exact LV| exact P1| exact P2| lia]|].
      intros q k' LQ IQ. assert (NE : p <> q) by (intros ->; exact (NI IQ)).
      destruct (as_live_disjoint L A m md p k q k' AI0 LV LQ NE); [right; right; split; [lia| reflexivity] | right; left; lia].
    - (first [ pose proof ((fframe_geom L A m md ff kk age AI0 HF)) as dR_21; dand5 dR_21 as _ FS FLO FHI _ | destruct (fframe_geom L A m md ff kk age AI0 HF) as (_ & FS & FLO & FHI & _) ]).
      pose proof (app_facts L ff (fsize kk) FLO) as (FB & _).   (* [comment removed for export] *)
      exists p, sz. split; [exact B|]. split; [exact P8|]. split; [eapply app_range_sub; [exact FLO| lia| lia| lia]|]. split; [exact P1|]. split; [exact P2|]. split; [lia|].
      split; [right; exists ff, kk, age; split; [exact HF|]; split; [exact F1| exact F2]|].
      split; [eapply crange_fframe; [exact AI0| exact HF| lia| lia| lia]|].
      intros q k' LQ IQ. destruct (as_frame_blk_disjoint L A m md ff kk age q k' AI0 HF LQ); [left; lia| right; left; lia].
  Qed.

  Lemma chome_call : forall A A' m md m' md' (v' : mem) sp win V N excl excl' p0 sz0,
    ainv A m md -> chome A excl p0 sz0 -> bytes_at segs (aview A m) (sh p0) (shpat sz0) -> 0 <= sz0 ->
    cframe L (owned A) (owned A') sp win V N (aview A m) v' -> alloc_ceiling <= sp - win ->
    (forall p k, a_live A p = Some k -> ~ In p excl -> a_live A' p = Some k /\ ~ In p excl') ->
    (forall ff kk age, a_frame A ff = Some (kk, age) -> a_frame A' ff = Some (kk, age)) ->
    (forall x ff kk age, V x -> a_frame A ff = Some (kk, age) -> ~ (sh ff <= x < sh ff + fsize kk / 8)) ->
    ainv A' m' md' -> v' = aview A' m' ->
    bytes_at segs v' (sh p0) (shpat sz0) /\ chome A' excl' p0 sz0.
  Proof.
    intros A A' m md m' md' v' sp win V N excl excl' p0 sz0 AI0 HO B SZ CF Hw KB KF HV AI1 EV.
    destruct HO as [[LV NI] | (ff & kk & age & HF & F1 & F2)].
    - destruct (KB _ _ LV NI) as [LV' NI']. split; [| left; split; [exact LV'| exact NI']].
      rewrite EV. exact (as_live_shadow L A' m' md' p0 sz0 AI1 LV').
    - split; [| right; exists ff, kk, age; split; [exact (KF _ _ _ HF)|]; split; [exact F1| exact F2]].
      (first [ pose proof ((fframe_geom L A m md ff kk age AI0 HF)) as dR_22; dand5 dR_22 as _ FS FLO FHI _ | destruct (fframe_geom L A m md ff kk age AI0 HF) as (_ & FS & FLO & FHI & _) ]).
      pose proof (fframe_al8 A m md ff kk age AI0 HF) as F8. pose proof layout_facts as LF. pose proof (app_facts L ff (fsize kk) FLO) as (FB0 & _).   (* [comment removed for export] *)
      pose proof (shpat_length sz0 SZ) as LEN.
      assert (LOW : sh ff <= sh p0) by (unfold sh; assert (ff / 8 <= p0 / 8) by (apply Z.div_le_mono; lia); lia).
      assert (FF8 : (ff + fsize kk) mod 8 = 0).
      { rewrite Z.add_mod, F8 by lia. unfold fsize. replace (64 * 2 ^ kk) with ((8 * 2 ^ kk) * 8) by lia.
        rewrite Z.mod_mul by lia. reflexivity. }
      pose proof (sh_sep p0 sz0 (ff + fsize kk) ltac:(lia) FF8 ltac:(lia)) as HIGH.
      assert (SF : sh (ff + fsize kk) = sh ff + fsize kk / 8).
      { unfold sh. pose proof (Z.div_mod ff 8 ltac:(lia)) as D. rewrite F8, Z.add_0_r in D. rewrite D at 1.
        unfold fsize. replace (8 * (ff / 8) + 64 * 2 ^ kk) with ((ff / 8 + 8 * 2 ^ kk) * 8) by lia.
        rewrite Z.div_mul by lia. replace (64 * 2 ^ kk) with ((8 * 2 ^ kk) * 8) by lia. rewrite Z.div_mul by lia. lia. }
      rewrite SF in HIGH.
      eapply (bytes_at_ccall L A A' sp win V N (aview A m) v' CF); [| | exact B].
      + eapply (crange_fshadow A m md ff kk age); [exact AI0| exact HF| exact LOW| rewrite LEN; exact HIGH| rewrite LEN; lia].
      + split.
        * left. rewrite LEN. (first [ pose proof ((sh_bound ff (fsize kk) ltac:(lia) ltac:(lia) FHI)) as dR_23; dand3 dR_23 as SB1 SB2 SB3 | pose proof (sh_bound ff (fsize kk) ltac:(lia) ltac:(lia) FHI) as (SB1 & SB2 & SB3) ]).   (* [comment removed for export] *)
          pose proof (fsize_div8 kk) as E8.
          rewrite E8 in SB2. lia.
        * intros i Hi X. rewrite LEN in Hi. apply (HV _ _ _ _ X HF). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma chome_crange : forall A m md excl p0 sz0 a n,
    ainv A m md -> chome A excl p0 sz0 -> p0 <= a -> a + n <= p0 + sz0 -> 0 <= n -> crange A (aview A m) a n.
  Proof.
    intros A m md excl p0 sz0 a n AI0 [[LV _] | (ff & kk & age & HF & F1 & F2)] H1 H2 N0.
    - eapply crange_block; [exact AI0| exact LV| exact H1| exact H2| exact N0].
    - eapply crange_fframe; [exact AI0| exact HF| lia| lia| exact N0].
  Qed.

  (* [comment removed for export] *)
  Lemma chome_fp : forall A excl p0 sz0 a n,
    chome A excl p0 sz0 -> p0 <= a -> a + n <= p0 + sz0 ->
    (exists p k, a_live A p = Some k /\ p <= a /\ a + n <= p + k)
    \/ (exists ff k age, a_frame A ff = Some (k, age) /\ ff <= a /\ a + n <= ff + fsize k - 8).
  Proof.
    intros A excl p0 sz0 a n [[LV _] | (ff & kk & age & HF & F1 & F2)] H1 H2.
    - left. exists p0, sz0. split; [exact LV| lia].
    - right. exists ff, kk, age. split; [exact HF| lia].
  Qed.

  (* [comment removed for export] *)
  Definition stack_shadow (v : mem) (SB N lo hi : Z) : Prop :=
    bytes_at segs v SB (repeat (Z_to_bv 8 0) (Z.to_nat N)) /\ 0 <= N /\ SB <= sh lo /\ sh hi < SB + N
    /\ sh alloc_ceiling <= SB /\ SB + N <= kHighMemBeg.

  Lemma stack_shadow_sub : forall v SB N lo hi lo' hi',
    stack_shadow v SB N lo hi -> lo <= lo' -> hi' <= hi -> 0 <= lo -> stack_shadow v SB N lo' hi'.
  Proof.
    (intros v SB N lo hi lo' hi'; (first [ intro dR_48; dand6 dR_48 as B N0 Lq Hh SL T | intros (B & N0 & Lq & Hh & SL & T) ]); intros H1 H2 H0). split; [exact B|]. split; [exact N0|].
    unfold sh in *. assert (lo / 8 <= lo' / 8) by (apply Z.div_le_mono; lia). assert (hi' / 8 <= hi / 8) by (apply Z.div_le_mono; lia).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.

  Lemma crange_stack_shadow : forall A m md SB N lo hi,
    ainv A m md -> stack_shadow (aview A m) SB N lo hi -> alloc_ceiling <= lo ->
    crange A (aview A m) SB N.
  Proof.
    (intros A m md SB N lo hi AI0; (first [ intro dR_49; dand6 dR_49 as B N0 Lq Hh SLO T | intros (B & N0 & Lq & Hh & SLO & T) ]); intros CE).
    (first [ pose proof (layout_facts) as dR_24; dand7 dR_24 as L1 L2 L3 L4 ACV L6 L7 | pose proof layout_facts as (L1 & L2 & L3 & L4 & ACV & L6 & L7) ]).
    assert (SLO' : 17591916560384 + 2147450880 <= SB) by (unfold sh, kShadowOffset in SLO; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    pose proof (bytes_at_mapped L (aview A m) SB _ B) as MP. rewrite repeat_length, Z2Nat.id in MP by lia.
    split; [lia|]. split; [unfold kHighMemBeg in T; lia|].
    intros i Hi. split; [|split].
    - apply (as_owned_not_stack_shadow L A m md); [exact AI0|]. lia.
    - lia.
    - left. apply MP; [| exact Hi]. right. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma hframe_keep : forall A A' H,
    hframe A H -> (forall ff, a_frame A' ff = a_frame A ff) -> hframe A' H.
  Proof. intros A A' H [age HF] E. exists age. rewrite E. exact HF. Qed.

  Lemma hframe_keep_aged : forall A A' H,
    hframe A H ->
    (forall ff k age, a_frame A ff = Some (k, age) -> exists age', a_frame A' ff = Some (k, age')) ->
    hframe A' H.
  Proof. intros A A' H [age HF] E. destruct (E _ _ _ HF) as [age' HF']. exists age'. exact HF'. Qed.

  (* [comment removed for export] *)
  Lemma hshadow_shadowed : forall H v,
    hshadow H v -> henv_geom H ->
       shadowed v (h_vsc H) 1368 /\ shadowed v (h_cp H) 752
    /\ shadowed v (h_req H) 56 /\ shadowed v (h_resp H) 56 /\ shadowed v (h_vc H) 72 /\ shadowed v (h_wrk H) 184
    /\ shadowed v (h_ws H) 40 /\ shadowed v (h_vsbloc H) 8 /\ shadowed v (h_hd H) 32 /\ shadowed v (h_wsbuf H) 1024.
  Proof.
    (intros H v HS; (first [ intro dR_50; dand3 dR_50 as G1 G2 G3 | intros (G1 & G2 & G3) ])).
    unfold hshadow in HS. unfold h_vsc, h_cp, h_req, h_resp, h_vc, h_wrk, h_ws, h_vsbloc, h_hd, h_wsbuf, HFSIZE in *.
    pose proof (Z.div_mod (h_ff H) 4096 ltac:(lia)) as D. rewrite G1, Z.add_0_r in D.
    assert (T : forall off n, bytes_at segs v (sh (h_ff H + off)) (shpat n) -> off mod 8 = 0 -> 0 <= off ->
                             off + n <= 8192 -> shadowed v (h_ff H + off) n).
    { intros off n B M8 O0 On. exists (h_ff H + off), n. split; [exact B|].
      split; [rewrite D; rewrite <- Zplus_mod_idemp_l; replace (4096 * (h_ff H / 4096)) with ((512 * (h_ff H / 4096)) * 8) by lia;
              rewrite Z.mod_mul by lia; exact M8 |].
      pose proof (app_facts L _ _ G2) as (GB & _). lia. }   (* [comment removed for export] *)
    (first [ dand10 HS as S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 | destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10) ]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
      first [ replace (h_ff H + 1536) with (h_ff H + 1536) by lia ]; (apply T; [assumption| reflexivity| lia| lia]).
  Qed.
End World.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Transport.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context (L : clayout) {AI : AsanAlloc L}.
  Let segs := cl_segs L.

  Lemma rw_cells_munch : forall W m m' A cs,
    rw_cells segs m A cs -> munch W m m' -> wmono segs m m' ->
    (forall a, A <= a < A + Z.of_nat (cells_size cs) -> outside W a) ->
    rw_cells segs m' A cs.
  Proof.
    intros W m m' A cs RC MU WM OUT.
    destruct RC as [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
    - (first [ dand3 HB as B0 B1 B | destruct HB as (B0 & B1 & B) ]). split; [exact B0|]. split; [exact B1|]. intros i Hi.
      unfold mrd. rewrite MU; [apply B; exact Hi|]. rewrite wa_unsigned by lia. apply OUT.
      rewrite cells_bytes_length in Hi by exact Hwf. lia.
    - eapply wr_at_transport; eauto.
  Qed.

  Lemma bytes_at_munch : forall W m m' A bs,
    bytes_at segs m A bs -> munch W m m' ->
    (forall a, A <= a < A + Z.of_nat (length bs) -> outside W a) ->
    bytes_at segs m' A bs.
  Proof.
    (intros W m m' A bs; (first [ intro dR_51; dand3 dR_51 as B0 B1 B | intros (B0 & B1 & B) ]); intros MU OUT). split; [exact B0|]. split; [exact B1|]. intros i Hi.
    unfold mrd. rewrite MU; [apply B; exact Hi|]. rewrite wa_unsigned by lia. apply OUT. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma hshadow_munch : forall H W m m',
    hshadow L H m -> munch W m m' -> henv_geom L H ->
    (forall x, sh (h_ff H) <= x < sh (h_ff H) + HFSIZE / 8 -> outside W x) ->
    hshadow L H m'.
  Proof.
    (intros H W m m' HS MU; (first [ intro dR_52; dand3 dR_52 as G1 G2 G3 | intros (G1 & G2 & G3) ]); intros OUT).
    unfold hshadow in *. unfold h_vsc, h_cp, h_req, h_resp, h_vc, h_wrk, h_ws, h_vsbloc, h_hd, h_wsbuf, HFSIZE in *.
    pose proof (Z.div_mod (h_ff H) 4096 ltac:(lia)) as D. rewrite G1, Z.add_0_r in D.
    assert (T : forall off n, bytes_at segs m (sh (h_ff H + off)) (shpat n) -> off mod 8 = 0 -> 0 <= off -> 0 <= n ->
                             off + n <= 8192 -> bytes_at segs m' (sh (h_ff H + off)) (shpat n)).
    { intros off n B M8 O0 N0 On. eapply bytes_at_munch; [exact B| exact MU|]. rewrite shpat_length by lia.
      intros x Hx. apply OUT. unfold sh in *. rewrite D in Hx |- *.
      pose proof (Z.div_mod off 8 ltac:(lia)) as D8. rewrite M8, Z.add_0_r in D8.
      replace (4096 * (h_ff H / 4096) + off) with ((512 * (h_ff H / 4096) + off / 8) * 8) in Hx by lia.
      replace (4096 * (h_ff H / 4096)) with ((512 * (h_ff H / 4096)) * 8) by lia.
      rewrite Z.div_mul in Hx |- * by lia.
      pose proof (Z.div_mod (n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. }
    (first [ dand10 HS as S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 | destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10) ]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; (apply T; [assumption| reflexivity| lia| lia| lia]).
  Qed.

  Lemma glob_ok_munch : forall V H W m m',
    glob_ok L V H m -> munch W m m' -> wmono segs m m' ->
    (forall a, (vi_bss_vsc V <= a < vi_bss_vsc V + 8 \/ vi_bss_cp V <= a < vi_bss_cp V + 8 \/
                h_cp H <= a < h_cp H + 752 \/ h_vsc H + 1304 <= a < h_vsc H + 1320) -> outside W a) ->
    glob_ok L V H m'.
  Proof.
    (intros V H W m m'; (first [ intro dR_53; dand4 dR_53 as B1 B2 C [bs D] | intros (B1 & B2 & C & [bs D]) ]); intros MU WM OUT).
    split; [|split; [|split; [|exists bs]]];
      (eapply rw_cells_munch; [eassumption| exact MU| exact WM|]); intros a Ha; apply OUT; cbn in Ha; lia.
  Qed.

  Lemma hobj_ok_munch : forall V H W m m',
    hobj_ok L V H m -> munch W m m' -> wmono segs m m' ->
    (forall a, (h_vc H <= a < h_vc H + 72 \/ h_wrk H <= a < h_wrk H + 184 \/ h_req H <= a < h_req H + 56 \/
                h_resp H <= a < h_resp H + 56 \/ h_hd H + 16 <= a < h_hd H + 24) -> outside W a) ->
    hobj_ok L V H m'.
  Proof.
    (intros V H W m m'; (first [ intro dR_54; dand5 dR_54 as VC WK RQ RS HD | intros (VC & WK & RQ & RS & HD) ]); intros MU WM OUT).
    (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]). (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]).
    (first [ dex3 RQ as mi1 tl1 pd1; dand4 RQ as L5 L6 L7 RQ | dand7 RQ as mi1 tl1 pd1 L5 L6 L7 RQ | destruct RQ as (mi1 & tl1 & pd1 & L5 & L6 & L7 & RQ) ]). (first [ dex4 RS as hd2 mi2 tl2 pd2; dand4 RS as L8 L9 L10 RS | dand8 RS as hd2 mi2 tl2 pd2 L8 L9 L10 RS | destruct RS as (hd2 & mi2 & tl2 & pd2 & L8 & L9 & L10 & RS) ]).
    split; [exists p1, r1; split; [exact L1|]; split; [exact L2|]|].
    2: split; [exists p2, r2; split; [exact L3|]; split; [exact L4|]|].
    3: split; [exists mi1, tl1, pd1; split; [exact L5|]; split; [exact L6|]; split; [exact L7|]|].
    4: split; [exists hd2, mi2, tl2, pd2; split; [exact L8|]; split; [exact L9|]; split; [exact L10|]|].
    all: eapply rw_cells_munch; [eassumption| exact MU| exact WM|]; intros a Ha; apply OUT;
         cbn [cells_size csize vc_cells wrk_cells http_cells Nat.add length] in Ha; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma henv_ok_munch : forall V H A W m m',
    henv_ok L V H A m -> munch W m m' -> wmono segs m m' -> henv_geom L H ->
    (forall a, (vi_bss_vsc V <= a < vi_bss_vsc V + 8 \/ vi_bss_cp V <= a < vi_bss_cp V + 8 \/
                h_vsc H + 1304 <= a < h_vsc H + 1320 \/ h_cp H <= a < h_ff H + HOBJ_END \/
                sh (h_ff H) <= a < sh (h_ff H) + HFSIZE / 8) -> outside W a) ->
    henv_ok L V H A m'.
  Proof.
    (intros V H A W m m'; (first [ intro dR_55; dand4 dR_55 as HF G O S | intros (HF & G & O & S) ]); intros MU WM HG OUT). split; [exact HF|]. split; [|split].
    - eapply glob_ok_munch; [exact G| exact MU| exact WM|]. intros a Ha. apply OUT.
      unfold h_cp, h_vsc, HOBJ_END in *. lia.
    - eapply hobj_ok_munch; [exact O| exact MU| exact WM|]. intros a Ha. apply OUT.
      unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_cp, HOBJ_END in *. lia.
    - eapply hshadow_munch; [exact S| exact MU| exact HG|]. intros a Ha. apply OUT. lia.
  Qed.

  Lemma ws0_obj_munch : forall H W m m',
    ws0_obj L H m -> munch W m m' -> wmono segs m m' ->
    (forall a, (h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32) -> outside W a) ->
    ws0_obj L H m'.
  Proof.
    (intros H W m m'; (first [ intro dR_56; dex1 dR_56 as id; dand3 dR_56 as ID A1 A2 | intro dR_56; dand4 dR_56 as id ID A1 A2 | intros (id & ID & A1 & A2) ]); intros MU WM OUT). exists id. split; [exact ID|].
    pose proof ID as ID'. destruct ID' as [-> | ->];
    (split; (eapply rw_cells_munch; [eassumption| exact MU| exact WM|]); intros a Ha; apply OUT; cbn in Ha; lia).
  Qed.

  Lemma ws1_obj_munch : forall H A W m m' wa vep,
    ws1_obj L H A m wa vep -> munch W m m' -> wmono segs m m' ->
    (forall a, (h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32 \/ wa <= a < wa + 40) -> outside W a) ->
    ws1_obj L H A m' wa vep.
  Proof.
    (intros H A W m m' wa vep; (first [ intro dR_57; dex2 dR_57 as id pad; dand7 dR_57 as ID LP A1 A2 LV A3 LV2 | intro dR_57; dand9 dR_57 as id pad ID LP A1 A2 LV A3 LV2 | intros (id & pad & ID & LP & A1 & A2 & LV & A3 & LV2) ]); intros MU WM OUT). exists id, pad.
    split; [exact ID|]. split; [exact LP|].
    pose proof ID as ID'. destruct ID' as [-> | ->];
    (split; [|split; [|split; [exact LV| split; [|exact LV2]]]];
     (eapply rw_cells_munch; [eassumption| exact MU| exact WM|]); intros a Ha; apply OUT; cbn in Ha; lia).
  Qed.
End Transport.

(* [comment removed for export] *)
Section Intro.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context (L : clayout) {AI : AsanAlloc L}.
  Let segs := cl_segs L.

  Lemma hobj_ok_intro : forall V H m p1 r1 p2 r2 mi1 tl1 pd1 hd2 mi2 tl2 pd2,
    length p1 = 12%nat -> length r1 = 40%nat -> rw_cells segs m (h_vc H) (vc_cells p1 (h_resp H) (h_wrk H) r1) ->
    length p2 = 28%nat -> length r2 = 144%nat -> rw_cells segs m (h_wrk H) (wrk_cells p2 r2) ->
    length mi1 = 24%nat -> length tl1 = 8%nat -> length pd1 = 4%nat ->
    rw_cells segs m (h_req H) (http_cells (h_hd H) mi1 (h_ws H) tl1 pd1) ->
    length mi2 = 24%nat -> length tl2 = 8%nat -> length pd2 = 4%nat ->
    rw_cells segs m (h_resp H) (http_cells hd2 mi2 (h_ws H) tl2 pd2) ->
    rw_cells segs m (h_hd H + 16) [C8 (Z_to_bv 64 (vi_url V))] ->
    hobj_ok L V H m.
  Proof.
    intros. split; [eexists _, _; eauto|]. split; [eexists _, _; eauto|].
    split; [eexists _, _, _; eauto|]. split; [eexists _, _, _, _; eauto| assumption].
  Qed.

  Lemma glob_ok_intro : forall V H m bs,
    rw_cells segs m (vi_bss_vsc V) [C8 (Z_to_bv 64 (h_vsc H))] ->
    rw_cells segs m (vi_bss_cp V) [C8 (Z_to_bv 64 (h_cp H))] ->
    rw_cells segs m (h_cp H) [CB 752 (repeat (Z_to_bv 8 0) 752)] ->
    rw_cells segs m (h_vsc H + 1304) [CB 16 bs] ->
    glob_ok L V H m.
  Proof. intros. split; [assumption|]. split; [assumption|]. split; [assumption| eexists; eassumption]. Qed.

  Lemma ws0_obj_intro : forall H m id,
    ws_id_ok id ->
    rw_cells segs m (h_ws H) (ws_cells (ws_rec_of H id)) ->
    rw_cells segs m (h_wsbuf H) (wsemu_cells (wsemu_WS0 (h_wsbuf H))) ->
    ws0_obj L H m.
  Proof. intros. eexists; eauto. Qed.

  Lemma ws1_obj_intro : forall H A m wa vep id pad,
    ws_id_ok id -> length pad = 4%nat ->
    rw_cells segs m (h_ws H) (ws_cells (ws_rec_of H id)) ->
    rw_cells segs m (h_wsbuf H) (wsemu_cells (wsemu_WS1 wa)) ->
    a_live A wa = Some 40 -> rw_cells segs m wa (wsalloc_cells (wsalloc_WS1 (h_wsbuf H) vep) pad) ->
    a_live A vep = Some 312 ->
    ws1_obj L H A m wa vep.
  Proof.
    intros H A m wa vep id pad ID LP A1 A2 LV A3 LV2. exists id, pad.
    split; [exact ID|]. split; [exact LP|]. split; [exact A1|]. split; [exact A2|]. split; [exact LV|]. split; [exact A3| exact LV2].
  Qed.
End Intro.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TransportCall.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context (L : clayout) {AI : AsanAlloc L}.
  Let segs := cl_segs L.

  (* [comment removed for export] *)
  Lemma rw_cells_ccall_hframe : forall A A' m md v' sp win V N H a cs,
    ainv A m md -> hframe L A H -> cframe L (owned A) (owned A') sp win V N (aview A m) v' ->
    rw_cells segs (aview A m) a cs -> h_ff H <= a -> a + Z.of_nat (cells_size cs) <= h_ff H + HOBJ_END ->
    alloc_ceiling <= sp - win ->
    (forall x, a <= x < a + Z.of_nat (cells_size cs) -> ~ V x) ->
    rw_cells segs v' a cs.
  Proof.
    intros A A' m md v' sp win V N H a cs AI0 HF CF RC Ha Hn Hw NV.
    (first [ pose proof ((henv_geom_of_frame L A m md H AI0 HF)) as dR_32; dand3 dR_32 as G1 G2 G3 | pose proof (henv_geom_of_frame L A m md H AI0 HF) as (G1 & G2 & G3) ]). unfold HFSIZE, HOBJ_END in *.
    eapply (rw_cells_ccall L A A' sp win V N (aview A m) v' CF); [| | exact RC].
    - eapply hframe_crange; [exact AI0| exact HF| exact Ha| unfold HOBJ_END; exact Hn| lia].
    - split; [left; lia|]. intros i Hi. apply NV. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma hshadow_ccall : forall A A' m md v' sp win V N H,
    ainv A m md -> hframe L A H -> cframe L (owned A) (owned A') sp win V N (aview A m) v' ->
    hshadow L H (aview A m) -> alloc_ceiling <= sp - win ->
    (forall x, sh (h_ff H) <= x < sh (h_ff H) + HFSIZE / 8 -> ~ V x) ->
    hshadow L H v'.
  Proof.
    intros A A' m md v' sp win V N H AI0 HF CF HS Hw NV.
    (first [ pose proof ((henv_geom_of_frame L A m md H AI0 HF)) as dR_34; dand3 dR_34 as G1 G2 G3 | pose proof (henv_geom_of_frame L A m md H AI0 HF) as (G1 & G2 & G3) ]).
    destruct HF as [age HFR].
    unfold hshadow in *. unfold h_vsc, h_cp, h_req, h_resp, h_vc, h_wrk, h_ws, h_vsbloc, h_hd, h_wsbuf, HFSIZE in *.
    pose proof (Z.div_mod (h_ff H) 4096 ltac:(lia)) as D. rewrite G1, Z.add_0_r in D.
    pose proof layout_facts as LF.
    assert (T : forall off n, bytes_at segs (aview A m) (sh (h_ff H + off)) (shpat n) -> off mod 8 = 0 -> 0 <= off -> 0 <= n ->
                             off + n <= 8192 -> bytes_at segs v' (sh (h_ff H + off)) (shpat n)).
    { intros off n B M8 O0 N0 On.
      pose proof (Z.div_mod off 8 ltac:(lia)) as D8. rewrite M8, Z.add_0_r in D8.
      assert (SH : sh (h_ff H + off) = sh (h_ff H) + off / 8).
      { unfold sh. rewrite D. replace (4096 * (h_ff H / 4096) + off) with ((512 * (h_ff H / 4096) + off / 8) * 8) by lia.
        replace (4096 * (h_ff H / 4096)) with ((512 * (h_ff H / 4096)) * 8) by lia. rewrite !Z.div_mul by lia. lia. }
      pose proof (Z.div_mod (n + 7) 8 ltac:(lia)) as D7. pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)) as M7.
      eapply (bytes_at_ccall L A A' sp win V N (aview A m) v' CF); [| | exact B].
      - eapply (crange_fshadow A m md _ _ _ _ _ AI0 HFR); rewrite ?shpat_length by lia; [lia| | lia].
        change (fsize HCLASS) with 8192. rewrite SH. lia.
      - split.
        + left. rewrite shpat_length by lia. pose proof (app_facts L _ _ G2) as (GB & _).   (* [comment removed for export] *)
          (first [ pose proof ((sh_bound (Clg:=Clg) (h_ff H + off) n ltac:(lia) ltac:(lia) ltac:(lia))) as dR_35; dand3 dR_35 as SB1 SB2 SB3 | pose proof (sh_bound (Clg:=Clg) (h_ff H + off) n ltac:(lia) ltac:(lia) ltac:(lia)) as (SB1 & SB2 & SB3) ]). lia.
        + intros i Hi. apply NV. rewrite shpat_length in Hi by lia. rewrite SH. lia. }
    (first [ dand10 HS as S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 | destruct HS as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10) ]).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; (apply T; [assumption| reflexivity| lia| lia| lia]).
  Qed.

  Lemma hobj_ok_ccall : forall V H A A' m md v' sp win Vc N,
    ainv A m md -> hframe L A H -> cframe L (owned A) (owned A') sp win Vc N (aview A m) v' ->
    hobj_ok L V H (aview A m) -> alloc_ceiling <= sp - win ->
    (forall a, (h_vc H <= a < h_vc H + 72 \/ h_wrk H <= a < h_wrk H + 184 \/ h_req H <= a < h_req H + 56 \/
                h_resp H <= a < h_resp H + 56 \/ h_hd H + 16 <= a < h_hd H + 24) -> ~ Vc a) ->
    hobj_ok L V H v'.
  Proof.
    (intros V H A A' m md v' sp win Vc N AI0 HF CF; (first [ intro dR_58; dand5 dR_58 as VC WK RQ RS HD | intros (VC & WK & RQ & RS & HD) ]); intros Hw NV).
    unfold h_vc, h_wrk, h_req, h_resp, h_hd in *.
    (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]). (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]).
    (first [ dex3 RQ as mi1 tl1 pd1; dand4 RQ as L5 L6 L7 RQ | dand7 RQ as mi1 tl1 pd1 L5 L6 L7 RQ | destruct RQ as (mi1 & tl1 & pd1 & L5 & L6 & L7 & RQ) ]). (first [ dex4 RS as hd2 mi2 tl2 pd2; dand4 RS as L8 L9 L10 RS | dand8 RS as hd2 mi2 tl2 pd2 L8 L9 L10 RS | destruct RS as (hd2 & mi2 & tl2 & pd2 & L8 & L9 & L10 & RS) ]).
    split; [exists p1, r1; split; [exact L1|]; split; [exact L2|]|].
    2: split; [exists p2, r2; split; [exact L3|]; split; [exact L4|]|].
    3: split; [exists mi1, tl1, pd1; split; [exact L5|]; split; [exact L6|]; split; [exact L7|]|].
    4: split; [exists hd2, mi2, tl2, pd2; split; [exact L8|]; split; [exact L9|]; split; [exact L10|]|].
    all: eapply (rw_cells_ccall_hframe A A' m md v' sp win Vc N H); [exact AI0| exact HF| exact CF| eassumption| | | exact Hw|];
         unfold h_vc, h_wrk, h_req, h_resp, h_hd, HOBJ_END; cbn [cells_size csize vc_cells wrk_cells http_cells Nat.add length];
         [lia| lia|]; intros x Hx; apply NV; lia.
  Qed.

  Lemma glob_ok_ccall : forall V H A A' m md v' sp win Vc N,
    ainv A m md -> hframe L A H -> cframe L (owned A) (owned A') sp win Vc N (aview A m) v' ->
    glob_ok L V H (aview A m) -> alloc_ceiling <= sp - win ->
    (* [comment removed for export] *)
    cl_rw_lo L <= vi_bss_vsc V -> vi_bss_vsc V + 8 <= cl_image_hi L ->
    (forall i, 0 <= i < 8 -> ~ cl_static L (vi_bss_vsc V + i)) ->
    (vi_bss_vsc V + 8 <= cl_errno L \/ cl_errno L + 4 <= vi_bss_vsc V) ->
    cl_rw_lo L <= vi_bss_cp V -> vi_bss_cp V + 8 <= cl_image_hi L ->
    (forall i, 0 <= i < 8 -> ~ cl_static L (vi_bss_cp V + i)) ->
    (vi_bss_cp V + 8 <= cl_errno L \/ cl_errno L + 4 <= vi_bss_cp V) ->
    (forall a, (vi_bss_vsc V <= a < vi_bss_vsc V + 8 \/ vi_bss_cp V <= a < vi_bss_cp V + 8 \/
                h_cp H <= a < h_cp H + 752 \/ h_vsc H + 1304 <= a < h_vsc H + 1320) -> ~ Vc a) ->
    glob_ok L V H v'.
  Proof.
    intros V H A A' m md v' sp win Vc N AI0 HF CF GL Hw R1 R2 R3 R4 R5 R6 R7 R8 NV.
    unfold glob_ok in *. unfold h_cp, h_vsc in *. (first [ dand4 GL as B1 B2 C [bs D] | destruct GL as (B1 & B2 & C & [bs D]) ]).
    pose proof layout_facts as LF.
    split; [|split; [|split; [|exists bs]]].
    - eapply (rw_cells_ccall L A A' sp win Vc N (aview A m) v' CF); [| | exact B1].
      + eapply crange_data; [exact AI0| exact R1| cbn; exact R2| cbn; lia| cbn; exact R3| cbn; exact R4].
      + split; [cbn; lia|]. intros i Hi. apply NV. cbn in Hi. lia.
    - eapply (rw_cells_ccall L A A' sp win Vc N (aview A m) v' CF); [| | exact B2].
      + eapply crange_data; [exact AI0| exact R5| cbn; exact R6| cbn; lia| cbn; exact R7| cbn; exact R8].
      + split; [cbn; lia|]. intros i Hi. apply NV. cbn in Hi. lia.
    - eapply (rw_cells_ccall_hframe A A' m md v' sp win Vc N H); [exact AI0| exact HF| exact CF| exact C| lia| cbn; unfold HOBJ_END; lia| exact Hw|].
      intros x Hx. apply NV. cbn in Hx. lia.
    - eapply (rw_cells_ccall_hframe A A' m md v' sp win Vc N H); [exact AI0| exact HF| exact CF| exact D| lia| cbn; unfold HOBJ_END; lia| exact Hw|].
      intros x Hx. apply NV. cbn in Hx. lia.
  Qed.

  Lemma henv_ok_ccall : forall V H A A' m md v' sp win Vc N,
    ainv A m md -> cframe L (owned A) (owned A') sp win Vc N (aview A m) v' ->
    henv_ok L V H A (aview A m) -> alloc_ceiling <= sp - win ->
    (forall ff, a_frame A' ff = a_frame A ff) ->
    cl_rw_lo L <= vi_bss_vsc V -> vi_bss_vsc V + 8 <= cl_image_hi L ->
    (forall i, 0 <= i < 8 -> ~ cl_static L (vi_bss_vsc V + i)) ->
    (vi_bss_vsc V + 8 <= cl_errno L \/ cl_errno L + 4 <= vi_bss_vsc V) ->
    cl_rw_lo L <= vi_bss_cp V -> vi_bss_cp V + 8 <= cl_image_hi L ->
    (forall i, 0 <= i < 8 -> ~ cl_static L (vi_bss_cp V + i)) ->
    (vi_bss_cp V + 8 <= cl_errno L \/ cl_errno L + 4 <= vi_bss_cp V) ->
    (forall a, (vi_bss_vsc V <= a < vi_bss_vsc V + 8 \/ vi_bss_cp V <= a < vi_bss_cp V + 8 \/
                h_vsc H + 1304 <= a < h_vsc H + 1320 \/ h_cp H <= a < h_ff H + HOBJ_END \/
                sh (h_ff H) <= a < sh (h_ff H) + HFSIZE / 8) -> ~ Vc a) ->
    henv_ok L V H A' v'.
  Proof.
    (intros V H A A' m md v' sp win Vc N AI0 CF; (first [ intro dR_59; dand4 dR_59 as HF G O S | intros (HF & G & O & S) ]); intros Hw FS R1 R2 R3 R4 R5 R6 R7 R8 NV).
    split; [eapply hframe_keep; [exact HF| exact FS]|]. split; [|split].
    - eapply glob_ok_ccall; [exact AI0| exact HF| exact CF| exact G| exact Hw| exact R1| exact R2| exact R3| exact R4
                            | exact R5| exact R6| exact R7| exact R8|].
      intros a Ha. apply NV. unfold h_cp, h_vsc, HOBJ_END in *. lia.
    - eapply hobj_ok_ccall; [exact AI0| exact HF| exact CF| exact O| exact Hw|].
      intros a Ha. apply NV. unfold h_vc, h_wrk, h_req, h_resp, h_hd, h_cp, HOBJ_END in *. lia.
    - eapply hshadow_ccall; [exact AI0| exact HF| exact CF| exact S| exact Hw|]. intros a Ha. apply NV. lia.
  Qed.

  (* [comment removed for export] *)

  Lemma ws1_obj_ccall : forall H A A' m md v' sp win Vc N wa vep,
    ainv A m md -> hframe L A H -> cframe L (owned A) (owned A') sp win Vc N (aview A m) v' ->
    ws1_obj L H A (aview A m) wa vep -> alloc_ceiling <= sp - win ->
    a_live A' wa = Some 40 -> a_live A' vep = Some 312 ->
    (forall a, (h_ws H <= a < h_ws H + 40 \/ h_wsbuf H <= a < h_wsbuf H + 32 \/ wa <= a < wa + 40) -> ~ Vc a) ->
    ws1_obj L H A' v' wa vep.
  Proof.
    intros H A A' m md v' sp win Vc N wa vep AI0 HF CF WS Hw LV' LV2' NV.
    unfold ws1_obj in *. unfold h_ws, h_wsbuf in *. (first [ dex2 WS as id pad; dand7 WS as ID LP A1 A2 LV A3 LV2 | dand9 WS as id pad ID LP A1 A2 LV A3 LV2 | destruct WS as (id & pad & ID & LP & A1 & A2 & LV & A3 & LV2) ]).
    exists id, pad. split; [exact ID|]. split; [exact LP|].
    (first [ pose proof ((live_geom L A m md wa 40 AI0 LV)) as dR_44; dand7 dR_44 as _ _ W1 W2 _ _ _ | destruct (live_geom L A m md wa 40 AI0 LV) as (_ & _ & W1 & W2 & _ & _ & _) ]).
    pose proof ID as ID'. destruct ID' as [-> | ->].
    all: split; [|split; [|split; [exact LV'| split; [|exact LV2']]]].
    1,2,4,5: eapply (rw_cells_ccall_hframe A A' m md v' sp win Vc N H); [exact AI0| exact HF| exact CF| eassumption| lia| cbn; unfold HOBJ_END; lia| exact Hw|];
         intros x Hx; apply NV; cbn in Hx; lia.
    all: eapply (rw_cells_ccall L A A' sp win Vc N (aview A m) v' CF); [| | exact A3];
         [ eapply crange_block; [exact AI0| exact LV| lia| cbn; lia| cbn; lia]
         | split; [cbn; lia|]; intros i Hi; apply NV; cbn in Hi; lia ].
  Qed.

  Lemma vep_obj_ccall : forall A A' m md v' sp win Vc N VEP vv tag q,
    ainv A m md -> cframe L (owned A) (owned A') sp win Vc N (aview A m) v' ->
    vep_obj L A (aview A m) VEP vv tag q -> alloc_ceiling <= sp - win ->
    a_live A' VEP = Some 312 -> (forall a, VEP <= a < VEP + 312 -> ~ Vc a) ->
    vep_obj L A' v' VEP vv tag q.
  Proof.
    (intros A A' m md v' sp win Vc N VEP vv tag q AI0 CF; (first [ intro dR_60; dand4 dR_60 as LV RC LT WF | intros (LV & RC & LT & WF) ]); intros Hw LV' NV).
    (first [ pose proof ((live_geom L A m md VEP 312 AI0 LV)) as dR_45; dand7 dR_45 as _ _ W1 W2 _ _ _ | destruct (live_geom L A m md VEP 312 AI0 LV) as (_ & _ & W1 & W2 & _ & _ & _) ]).
    split; [exact LV'|]. split; [|split; [exact LT| exact WF]].
    eapply (rw_cells_ccall L A A' sp win Vc N (aview A m) v' CF); [| | exact RC];
      rewrite (vep_cells_size vv tag q LT WF);
      [ eapply crange_block; [exact AI0| exact LV| lia| cbn; lia| cbn; lia]
      | split; [cbn; lia|]; intros i Hi; apply NV; cbn in Hi; lia ].
  Qed.

  Lemma data_obj_ccall : forall A A' m md v' sp win Vc N DATA inp,
    ainv A m md -> cframe L (owned A) (owned A') sp win Vc N (aview A m) v' ->
    data_obj L A (aview A m) DATA inp -> alloc_ceiling <= sp - win ->
    a_live A' DATA = Some (Z.of_nat (length inp)) -> (forall a, DATA <= a < DATA + Z.of_nat (length inp) -> ~ Vc a) ->
    data_obj L A' v' DATA inp.
  Proof.
    (intros A A' m md v' sp win Vc N DATA inp AI0 CF; (first [ intro dR_61; dand3 dR_61 as LV B LEN | intros (LV & B & LEN) ]); intros Hw LV' NV).
    (first [ pose proof ((live_geom L A m md DATA _ AI0 LV)) as dR_46; dand7 dR_46 as _ _ W1 W2 _ _ _ | destruct (live_geom L A m md DATA _ AI0 LV) as (_ & _ & W1 & W2 & _ & _ & _) ]).
    split; [exact LV'|]. split; [|exact LEN].
    eapply (bytes_at_ccall L A A' sp win Vc N (aview A m) v' CF); [| | exact B];
      [ eapply crange_block; [exact AI0| exact LV| lia| lia| lia]
      | split; [lia|]; intros i Hi; apply NV; lia ].
  Qed.
End TransportCall.
