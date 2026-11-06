(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes RzBridge SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Section Kit.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {L : clayout} {AI : AsanAlloc L}.

  Lemma astop_svc_lemma : forall (A : AS) m md T W R F pc x8 fc (v' : mem) rom,
    ainv A m md ->
    munch W (aview A m) v' -> wmono (cl_segs L) (aview A m) v' -> client_fp L A (aview A m) W ->
    (forall (m1 : mem) (md1 : Model),
        ainv A m1 md1 -> aview A m1 = v' -> same_but_materialized md md1 ->
        (forall a, hidc (ahull A) a = true -> m1 a = m a) ->
        srealizes (cl_segs L) (mkCfg (MSsvc R F pc x8 fc None m1 rom) md1) T) ->
    evt (cl_segs L) (srz_at_r (cl_segs L) (ahull A) (alhull A) (aeager A) m md T) (MSsvc R F pc x8 fc None v' rom).
  Proof.
    intros A m md T W R F pc x8 fc v' rom AINV MU WM CF K.
    apply srz_stop_restrict. intros md1 MI1 SB HC. rewrite unrestrict_MSsvc.
    assert (HC' : forall a, hidc (ahull A) a = true -> v' a = None) by exact HC.
    apply K.
    - exact (ainv_munch L A m md md1 v' W AINV MU WM CF HC' MI1 SB).
    - apply aview_recombine. exact HC'.
    - exact SB.
    - intros a Ha. apply munrestrict_hidden. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma ainv_fds : forall A m md f, ainv A m md -> ainv A m (with_fds f md).
  Proof.
    intros A m md f AINV. destruct (as_minv L A m md AINV) as [MI Hh].
    apply (as_md_frame L A m md); [exact AINV | reflexivity | cbn; exact Hh | apply MInv_with_fds; exact MI].
  Qed.

  (* [comment removed for export] *)
  Lemma ainv_mat : forall A m md md', ainv A m md -> MInv (ahull A) (alhull A) (aeager A) md' -> same_but_materialized md md' -> ainv A m md'.
  Proof.
    intros A m md md' AINV MI SB.
    rewrite <- (munrestrict_mrestrict (hidc (ahull A)) m).
    change (mrestrict (hidc (ahull A)) m) with (aview A m).
    apply (ainv_munch L A m md md' (aview A m) [] AINV (munch_refl [] _) (wmono_refl _ _) I); [|exact MI|exact SB].
    intros a Ha. unfold aview, aview_of, mrestrict. rewrite Ha. reflexivity.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition img_client (lo hi : Z) : Prop :=
    cl_rw_lo L <= lo /\ hi <= cl_image_hi L /\ forall a, lo <= a < hi -> ~ cl_static L a /\ ~ cl_shared L a.

  Fixpoint client_fpx (A : AS) (v : mem) (W : list (Z * Z)) : Prop :=
    match W with
    | [] => True
    | (lo, hi) :: W' => (client_fp L A v [(lo, hi)] \/ img_client lo hi) /\ client_fpx A v W'
    end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma client_fpx_facts : forall A m md W a,
    ainv A m md -> client_fpx A (aview A m) W -> ~ outside W a ->
    ~ owned A a /\ ~ cl_shared L a /\ (~ in_image L a -> 0 <= a < 2^64 /\ aview A m (Z_to_bv 64 a) <> None).
  Proof.
    intros A m md W a AI0 CF NO. pose proof (layout_facts (L:=L)) as LO.
    induction W as [|[lo hi] W IH]; cbn in *; [tauto|].
    destruct CF as [HW CF].
    assert (CASE : (lo <= a < hi) \/ ~ outside W a) by tauto.
    destruct CASE as [Hin|Hrest]; [|apply IH; assumption].
    destruct HW as [HW|(Hlo & Hhi & HC)].
    - (first [ pose proof ((client_fp_facts L A m md [(lo, hi)] a AI0 HW ltac:(cbn; lia))) as dR_1; dand5 dR_1 as NO' NS NI Ra VIS | destruct (client_fp_facts L A m md [(lo, hi)] a AI0 HW ltac:(cbn; lia)) as (NO' & NS & NI & Ra & VIS) ]).
      split; [exact NO'|]. split; [exact NS|]. intros _. split; [exact Ra| exact VIS].
    - destruct (HC a Hin) as [NST NSH]. split; [|split; [exact NSH| intros NI; exfalso; apply NI; unfold in_image; lia]].
      intros O. destruct (as_owned_where L A m md a AI0 O) as [Hs|[_ Hni]]; [exact (NST Hs)|]. apply Hni. unfold in_image. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ainv_framex : forall A m m' md md' (W : list (Z * Z)),
    ainv A m md ->
    (forall a, hidc (ahull A) a = true -> m' a = m a) ->
    munch W (aview A m) (aview A m') -> wmono (cl_segs L) (aview A m) (aview A m') ->
    client_fpx A (aview A m) W ->
    MInv (ahull A) (alhull A) (aeager A) md' -> same_but_materialized md md' ->
    ainv A m' md'.
  Proof.
    intros A m m' md md' W AI0 HIDq MU WM CF MI SB.
    pose proof (layout_facts (L:=L)) as LO.
    assert (EQ : forall a, 0 <= a < 2^64 -> outside W a -> aview A m' (Z_to_bv 64 a) = aview A m (Z_to_bv 64 a)).
    { intros a Ha Ho. apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia. exact Ho. }
    assert (EQo : forall a, (owned A a \/ cl_shared L a) -> aview A m' (Z_to_bv 64 a) = aview A m (Z_to_bv 64 a)).
    { intros a Ho.
      assert (Ra : 0 <= a < 2^64).
      { destruct Ho as [O|Sh].
        - destruct (as_owned_where L A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [apply (as_static_where L) in Hs; lia| lia].
        - apply (as_shared_where L) in Sh. lia. }
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN]; [exact (EQ a Ra OUT)|].
      exfalso. (first [ pose proof ((client_fpx_facts A m md W a AI0 CF NIN)) as dR_2; dand3 dR_2 as NO NS _ | destruct (client_fpx_facts A m md W a AI0 CF NIN) as (NO & NS & _) ]). tauto. }
    apply (as_frame L A [] m m' md md' AI0).
    - intros ff [].
    - constructor.
    - exact HIDq.
    - intros a O. left. apply EQo. left; exact O.
    - intros ff k age fa [].
    - intros a Sh. apply EQo. right; exact Sh.
    - intros a Ha Hni VIS. change (aview_of (ahull A) m') with (aview A m').
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite (EQ a Ha OUT). exact VIS.
      + specialize (WM (Z_to_bv 64 a)). unfold wview in WM.
        rewrite (as_find_segment_outside L (Z_to_bv 64 a)) in WM by (rewrite unsigned_lit by lia; exact Hni).
        change (aview_of (ahull A) m) with (aview A m) in VIS.
        destruct (aview A m (Z_to_bv 64 a)); [|exfalso; apply VIS; reflexivity].
        destruct (aview A m' (Z_to_bv 64 a)); [discriminate|]. exfalso. apply WM; [discriminate| reflexivity].
    - intros a Ha Hni VIS'. change (aview_of (ahull A) m') with (aview A m') in VIS'. change (aview_of (ahull A) m) with (aview A m).
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite <- (EQ a Ha OUT). exact VIS'.
      + (first [ pose proof ((client_fpx_facts A m md W a AI0 CF NIN)) as dR_3; dand3 dR_3 as _ _ VIS | destruct (client_fpx_facts A m md W a AI0 CF NIN) as (_ & _ & VIS) ]). exact (proj2 (VIS Hni)).
    - exact MI.
    - exact SB.
  Qed.

  (* [comment removed for export] *)
  Theorem ainv_munchx : forall A m md md' (v' : mem) (W : list (Z * Z)),
    ainv A m md ->
    munch W (aview A m) v' -> wmono (cl_segs L) (aview A m) v' ->
    client_fpx A (aview A m) W ->
    (forall a, hidc (ahull A) a = true -> v' a = None) ->
    MInv (ahull A) (alhull A) (aeager A) md' -> same_but_materialized md md' ->
    ainv A (munrestrict (hidc (ahull A)) m v') md'.
  Proof.
    intros A m md md' v' W AI0 MU WM CF HC MI SB.
    assert (EV : aview A (munrestrict (hidc (ahull A)) m v') = v') by (apply aview_recombine; exact HC).
    apply (ainv_framex A m _ md md' W AI0); [| rewrite EV; exact MU | rewrite EV; exact WM | exact CF | exact MI | exact SB].
    intros a Ha. apply munrestrict_hidden. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma aview_write_visible : forall A m a bs,
    0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> hidc (ahull A) (Z_to_bv 64 (a + i)) = false) ->
    aview A (write_to_mem m (Z_to_bv 64 a) bs) = write_to_mem (aview A m) (Z_to_bv 64 a) bs.
  Proof.
    intros A m a bs Ha Hl VIS. apply functional_extensionality. intros x.
    unfold aview, aview_of, mrestrict. change (Z_to_bv 64 a) with (wa a). rewrite !write_to_mem_spec by lia.
    pose proof (bv_unsigned_in_range 64 x) as Hx.
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
    specialize (VIS (bv_unsigned x - a) ltac:(lia)). replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in VIS by lia.
    rewrite Z_to_bv_bv_unsigned in VIS. rewrite VIS. reflexivity.
  Qed.

  Lemma write_hidden_same : forall A m a bs x,
    0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
    (forall i, 0 <= i < Z.of_nat (length bs) -> hidc (ahull A) (Z_to_bv 64 (a + i)) = false) ->
    hidc (ahull A) x = true -> write_to_mem m (Z_to_bv 64 a) bs x = m x.
  Proof.
    intros A m a bs x Ha Hl VIS Hx. change (Z_to_bv 64 a) with (wa a). rewrite write_to_mem_spec by lia.
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
    specialize (VIS (bv_unsigned x - a) ltac:(lia)). replace (a + (bv_unsigned x - a)) with (bv_unsigned x) in VIS by lia.
    rewrite Z_to_bv_bv_unsigned in VIS. congruence.
  Qed.

  Lemma munch_write_inside : forall (v : mem) a bs lo hi,
    0 <= a -> a + Z.of_nat (length bs) <= 2^64 -> lo <= a -> a + Z.of_nat (length bs) <= hi ->
    munch [(lo, hi)] v (write_to_mem v (Z_to_bv 64 a) bs).
  Proof.
    intros v a bs lo hi Ha Hl Hlo Hhi x OUT. cbn [outside] in OUT. change (Z_to_bv 64 a) with (wa a).
    rewrite write_to_mem_spec by lia.
    destruct (Z.leb_spec0 a (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (a + Z.of_nat (length bs))); cbn [andb]; try reflexivity.
    exfalso. lia.
  Qed.

  Lemma wmono_write_self : forall (v : mem) a bs, wmono (cl_segs L) v (write_to_mem v a bs).
  Proof. intros v a bs. apply wmono_write. apply wmono_refl. Qed.

  (* [comment removed for export] *)
  Lemma view_rw_cells_real : forall A m md a n junk,
    ainv A m md -> rw_cells (cl_segs L) (aview A m) a [CB n junk] ->
    store_ok (cl_segs L) m (Z_to_bv 64 a) n = true /\ bytes_in_hull (ahull A) (Z_to_bv 64 a) n
    /\ (forall i, 0 <= i < Z.of_nat n -> hidc (ahull A) (Z_to_bv 64 (a + i)) = false).
  Proof.
    intros A m md a n junk AINV RW.
    pose proof (rw_cells_CB_store_ok (cl_segs L) (aview A m) a n junk n RW ltac:(lia)) as SO. change (wa a) with (Z_to_bv 64 a) in SO.
    unfold aview, aview_of in SO.
    destruct (store_ok_restrict (cl_segs L) (hidc (ahull A)) (as_hull_segs L A m md AINV) n m (Z_to_bv 64 a) SO) as [S1 S2].
    destruct RW as [[Hwf Hb] Hw]. pose proof (bytes_at_bound _ _ _ _ Hb) as B. cbn [cells_bytes cbytes cells_size csize] in B, Hw.
    cbn in Hwf. destruct Hwf as [Hj _]. rewrite app_nil_r, Hj in B.
    split; [exact S1|]. split.
    - intros k Hk. specialize (S2 k Hk). unfold hidc in S2. destruct (in_hullb (ahull A) (bv_unsigned (woff (Z_to_bv 64 a) k))); [reflexivity| discriminate].
    - intros i Hi. specialize (S2 (Z.to_nat i) ltac:(lia)). unfold woff in S2. rewrite unsigned_lit in S2 by lia.
      replace (a + Z.of_nat (Z.to_nat i)) with (a + i) in S2 by lia.
      destruct (hidc (ahull A) (Z_to_bv 64 (a + i))); [discriminate| reflexivity].
  Qed.

  Lemma astopx_lemma : forall (A : AS) m md T W R F pc fc (v' : mem) rom,
    ainv A m md ->
    munch W (aview A m) v' -> wmono (cl_segs L) (aview A m) v' -> client_fpx A (aview A m) W ->
    (forall (m1 : mem) (md1 : Model),
        ainv A m1 md1 -> aview A m1 = v' -> same_but_materialized md md1 ->
        (forall a, hidc (ahull A) a = true -> m1 a = m a) ->
        srealizes (cl_segs L) (mkCfg (MS R F pc fc None m1 rom) md1) T) ->
    evt (cl_segs L) (srz_at_r (cl_segs L) (ahull A) (alhull A) (aeager A) m md T) (MS R F pc fc None v' rom).
  Proof.
    intros A m md T W R F pc fc v' rom AINV MU WM CF K.
    apply srz_stop_restrict. intros md1 MI1 SB HC. rewrite unrestrict_MS.
    assert (HC' : forall a, hidc (ahull A) a = true -> v' a = None) by exact HC.
    apply K.
    - exact (ainv_munchx A m md md1 v' W AINV MU WM CF HC' MI1 SB).
    - apply aview_recombine. exact HC'.
    - exact SB.
    - intros a Ha. apply munrestrict_hidden. exact Ha.
  Qed.

  Lemma astop_svcx_lemma : forall (A : AS) m md T W R F pc x8 fc (v' : mem) rom,
    ainv A m md ->
    munch W (aview A m) v' -> wmono (cl_segs L) (aview A m) v' -> client_fpx A (aview A m) W ->
    (forall (m1 : mem) (md1 : Model),
        ainv A m1 md1 -> aview A m1 = v' -> same_but_materialized md md1 ->
        (forall a, hidc (ahull A) a = true -> m1 a = m a) ->
        srealizes (cl_segs L) (mkCfg (MSsvc R F pc x8 fc None m1 rom) md1) T) ->
    evt (cl_segs L) (srz_at_r (cl_segs L) (ahull A) (alhull A) (aeager A) m md T) (MSsvc R F pc x8 fc None v' rom).
  Proof.
    intros A m md T W R F pc x8 fc v' rom AINV MU WM CF K.
    apply srz_stop_restrict. intros md1 MI1 SB HC. rewrite unrestrict_MSsvc.
    assert (HC' : forall a, hidc (ahull A) a = true -> v' a = None) by exact HC.
    apply K.
    - exact (ainv_munchx A m md md1 v' W AINV MU WM CF HC' MI1 SB).
    - apply aview_recombine. exact HC'.
    - exact SB.
    - intros a Ha. apply munrestrict_hidden. exact Ha.
  Qed.

  (* [comment removed for export] *)
  Lemma sbm_io : forall md md1, same_but_materialized md md1 ->
    m_fs md1 = m_fs md /\ m_fds md1 = m_fds md /\ m_halted md1 = m_halted md.
  Proof. intros md md1 SB. pose proof (same_but_materialized_frame md md1 SB). tauto. Qed.

  (* [comment removed for export] *)
  Lemma view_rdn_real : forall A m md a n bs,
    ainv A m md -> rdn (cl_segs L) (aview A m) a n = Some bs ->
    rdn (cl_segs L) m a n = Some bs /\ bytes_in_hull (ahull A) a n.
  Proof.
    intros A m md a n bs AINV H. unfold aview, aview_of in H. rewrite <- ov_rdn in H.
    destruct (ov_read_bytes_restrict (cl_segs L) (hidc (ahull A)) (as_hull_segs L A m md AINV) n m a bs H) as [H1 H2].
    rewrite <- ov_rdn. split; [exact H1|].
    intros k Hk. specialize (H2 k Hk). unfold hidc in H2. destruct (in_hullb (ahull A) (bv_unsigned (woff a k))); [reflexivity| discriminate].
  Qed.
End Kit.

(* [comment removed for export] *)
Ltac astop_svc AINV MU WM CF :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    apply (astop_svc_lemma (L:=L) A m md _ _ _ _ _ _ _ _ _ AINV MU WM CF);
    let m1 := fresh "m" in let md1 := fresh "md" in
    let A1 := fresh "AINV" in let EV := fresh "EVIEW" in let SB := fresh "SBM" in let HID := fresh "HID" in
    intros m1 md1 A1 EV SB HID;
    first [ lazymatch type of EV with ?av = ?v' => is_var v'; subst v' end | rewrite <- EV in *; clear EV ]
  end.

(* [comment removed for export] *)
Ltac astopx AINV MU WM CF :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    apply (astopx_lemma (L:=L) A m md _ _ _ _ _ _ _ _ AINV MU WM CF);
    let m1 := fresh "m" in let md1 := fresh "md" in
    let A1 := fresh "AINV" in let EV := fresh "EVIEW" in let SB := fresh "SBM" in let HID := fresh "HID" in
    intros m1 md1 A1 EV SB HID;
    first [ lazymatch type of EV with ?av = ?v' => is_var v'; subst v' end | rewrite <- EV in *; clear EV ]
  end.
Ltac astop_svcx AINV MU WM CF :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    apply (astop_svcx_lemma (L:=L) A m md _ _ _ _ _ _ _ _ _ AINV MU WM CF);
    let m1 := fresh "m" in let md1 := fresh "md" in
    let A1 := fresh "AINV" in let EV := fresh "EVIEW" in let SB := fresh "SBM" in let HID := fresh "HID" in
    intros m1 md1 A1 EV SB HID;
    first [ lazymatch type of EV with ?av = ?v' => is_var v'; subst v' end | rewrite <- EV in *; clear EV ]
  end.
