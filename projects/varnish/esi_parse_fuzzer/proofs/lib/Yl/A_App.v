(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.

Module A_Fpx.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Frame Step Arr Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AClient ATac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {L : clayout} {AI : AsanAlloc L}.
  Let segs := cl_segs L.

  (* [comment removed for export] *)
  Definition img_ivl (lo hi : Z) : Prop :=
    cl_rw_lo L <= lo /\ hi <= cl_image_hi L /\ (forall a, lo <= a < hi -> ~ cl_static L a /\ ~ cl_shared L a).

  Lemma img_ivl_errno : img_ivl (cl_errno L) (cl_errno L + 4).
  Proof.
    pose proof (as_errno_where L) as [E1 E2]. split; [exact E1|]. split; [exact E2|].
    intros a Ha. replace a with (cl_errno L + (a - cl_errno L)) by lia. apply (as_errno_not_static L). lia.
  Qed.

  Fixpoint client_fpx (A : AS) (v : mem) (W : list (Z * Z)) : Prop :=
    match W with
    | [] => True
    | (lo, hi) :: W' => (alloc_ceiling <= lo /\ hi <= 2^64 /\ mapped v lo (hi - lo)
                         \/ (exists p n, a_live A p = Some n /\ p <= lo /\ hi <= p + n)
                         \/ (exists ff k age, a_frame A ff = Some (k, age) /\ ff <= lo /\ hi <= ff + fsize k - 8)
                         \/ (exists ff k age, a_frame A ff = Some (k, age) /\ sh ff <= lo /\ hi <= sh ff + fsize k / 8)
                         \/ img_ivl lo hi)
                        /\ client_fpx A v W'
    end.

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  Lemma client_fpx_cases : forall A v W a,
    client_fpx A v W -> ~ outside W a ->
    (alloc_ceiling <= a < 2^64 /\ v (Z_to_bv 64 a) <> None)
    \/ (exists p n, a_live A p = Some n /\ p <= a < p + n)
    \/ (exists ff k age, a_frame A ff = Some (k, age) /\ ff <= a < ff + fsize k - 8)
    \/ (exists ff k age, a_frame A ff = Some (k, age) /\ sh ff <= a < sh ff + fsize k / 8)
    \/ (cl_rw_lo L <= a < cl_image_hi L /\ ~ cl_static L a /\ ~ cl_shared L a).
  Proof.
    intros A v W a CF NO. induction W as [|[lo hi] W IH]; cbn in *; [tauto|].
    destruct CF as [HW CF].
    assert (CASE : (lo <= a < hi) \/ ~ outside W a) by tauto.
    destruct CASE as [Hin|Hrest]; [|apply IH; assumption].
    destruct HW as [(Hc & Hh & HM)|[(p & n & HL & Hp & Hn)|[(ff & k & age & HF & H1 & H2)|[(ff & k & age & HF & H1 & H2)|(I1 & I2 & I3)]]]].
    - left. split; [lia|]. replace a with (lo + (a - lo)) by lia. apply HM. lia.
    - right; left. exists p, n. split; [exact HL|lia].
    - right; right; left. exists ff, k, age. split; [exact HF| lia].
    - right; right; right; left. exists ff, k, age. split; [exact HF| lia].
    - right; right; right; right. destruct (I3 a Hin) as [X Y]. split; [lia|]. split; [exact X| exact Y].
  Qed.

  (* [comment removed for export] *)
  Lemma client_fpx_facts : forall A m md W a,
    ainv A m md -> client_fpx A (aview A m) W -> ~ outside W a ->
    ~ owned A a /\ ~ cl_shared L a /\ 0 <= a < 2^64 /\ (~ in_image L a -> aview A m (Z_to_bv 64 a) <> None).
  Proof.
    intros A m md W a AI0 CF NO. pose proof (layout_facts (L:=L)) as LO.
    destruct (client_fpx_cases A _ W a CF NO) as [[Hc HM]|[(p & n & HL & Hp)|[(ff & k & age & HF & H1)|[(ff & k & age & HF & H1)|(I1 & I2 & I3)]]]].
    - (first [ pose proof ((client_fp_facts L A m md [(a, a + 1)] a AI0
                 ltac:(cbn; split; [left; split; [lia|]; split; [lia|]; intros i Hi; replace (a + i) with a by lia; exact HM| exact I])
                 ltac:(cbn; lia))) as dR_1; dand5 dR_1 as NO' NS NI Ra VIS | destruct (client_fp_facts L A m md [(a, a + 1)] a AI0
                 ltac:(cbn; split; [left; split; [lia|]; split; [lia|]; intros i Hi; replace (a + i) with a by lia; exact HM| exact I])
                 ltac:(cbn; lia)) as (NO' & NS & NI & Ra & VIS) ]).
      split; [exact NO'|]. split; [exact NS|]. split; [exact Ra| intros _; exact VIS].
    - (first [ pose proof ((client_fp_facts L A m md [(a, a + 1)] a AI0
                 ltac:(cbn; split; [right; left; exists p, n; split; [exact HL| lia]| exact I])
                 ltac:(cbn; lia))) as dR_2; dand5 dR_2 as NO' NS NI Ra VIS | destruct (client_fp_facts L A m md [(a, a + 1)] a AI0
                 ltac:(cbn; split; [right; left; exists p, n; split; [exact HL| lia]| exact I])
                 ltac:(cbn; lia)) as (NO' & NS & NI & Ra & VIS) ]).
      split; [exact NO'|]. split; [exact NS|]. split; [exact Ra| intros _; exact VIS].
    - (first [ pose proof ((client_fp_facts L A m md [(a, a + 1)] a AI0
                 ltac:(cbn; split; [right; right; left; exists ff, k, age; split; [exact HF| lia]| exact I])
                 ltac:(cbn; lia))) as dR_3; dand5 dR_3 as NO' NS NI Ra VIS | destruct (client_fp_facts L A m md [(a, a + 1)] a AI0
                 ltac:(cbn; split; [right; right; left; exists ff, k, age; split; [exact HF| lia]| exact I])
                 ltac:(cbn; lia)) as (NO' & NS & NI & Ra & VIS) ]).
      split; [exact NO'|]. split; [exact NS|]. split; [exact Ra| intros _; exact VIS].
    - (first [ pose proof ((client_fp_facts L A m md [(a, a + 1)] a AI0
                 ltac:(cbn; split; [right; right; right; exists ff, k, age; split; [exact HF| lia]| exact I])
                 ltac:(cbn; lia))) as dR_4; dand5 dR_4 as NO' NS NI Ra VIS | destruct (client_fp_facts L A m md [(a, a + 1)] a AI0
                 ltac:(cbn; split; [right; right; right; exists ff, k, age; split; [exact HF| lia]| exact I])
                 ltac:(cbn; lia)) as (NO' & NS & NI & Ra & VIS) ]).
      split; [exact NO'|]. split; [exact NS|]. split; [exact Ra| intros _; exact VIS].
    - split; [|split; [exact I3| split; [unfold in_image in *; lia| intros NI; exfalso; apply NI; unfold in_image; lia]]].
      intros O. destruct (as_owned_where L A m md a AI0 O) as [Hs|[_ Hni]]; [exact (I2 Hs)|]. apply Hni. unfold in_image. lia.
  Qed.

  (* [comment removed for export] *)
  Theorem ainv_munchx : forall A m md md' (v' : mem) (W : list (Z * Z)),
    ainv A m md ->
    munch W (aview A m) v' -> wmono segs (aview A m) v' ->
    client_fpx A (aview A m) W ->
    (forall a, hidc (ahull A) a = true -> v' a = None) ->
    MInv (ahull A) (alhull A) (aeager A) md' -> same_but_materialized md md' ->
    ainv A (munrestrict (hidc (ahull A)) m v') md'.
  Proof.
    intros A m md md' v' W AI0 MU WM CF HC MI SB.
    set (m1 := munrestrict (hidc (ahull A)) m v').
    assert (EV : aview_of (ahull A) m1 = v') by (apply aview_recombine; exact HC).
    pose proof (layout_facts (L:=L)) as LO.
    assert (EQ : forall a, 0 <= a < 2^64 -> outside W a -> v' (Z_to_bv 64 a) = aview A m (Z_to_bv 64 a)).
    { intros a Ha Ho. apply (MU (Z_to_bv 64 a)). rewrite unsigned_lit by lia. exact Ho. }
    assert (EQo : forall a, (owned A a \/ cl_shared L a) -> v' (Z_to_bv 64 a) = aview A m (Z_to_bv 64 a)).
    { intros a Ho.
      assert (Ra : 0 <= a < 2^64).
      { destruct Ho as [O|Sh].
        - destruct (as_owned_where L A m md a AI0 O) as [Hs|[[Hge Hlt] Hni]]; [apply (as_static_where L) in Hs; lia| lia].
        - apply (as_shared_where L) in Sh. lia. }
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN]; [exact (EQ a Ra OUT)|].
      exfalso. (first [ pose proof ((client_fpx_facts A m md W a AI0 CF NIN)) as dR_5; dand3 dR_5 as NO NS _ | destruct (client_fpx_facts A m md W a AI0 CF NIN) as (NO & NS & _) ]). tauto. }
    apply (as_frame L A [] m m1 md md' AI0).
    - intros ff [].
    - constructor.
    - intros a Ha. unfold m1. apply munrestrict_hidden. exact Ha.
    - intros a O. left. rewrite EV. apply EQo. left; exact O.
    - intros ff k age fa [].
    - intros a Sh. rewrite EV. apply EQo. right; exact Sh.
    - intros a Ha Hni VIS. rewrite EV.
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite (EQ a Ha OUT). exact VIS.
      + specialize (WM (Z_to_bv 64 a)). unfold wview in WM. subst segs.
        rewrite (as_find_segment_outside L (Z_to_bv 64 a)) in WM by (rewrite unsigned_lit by lia; exact Hni).
        change (aview_of (ahull A) m) with (aview A m) in VIS.
        destruct (aview A m (Z_to_bv 64 a)); [|exfalso; apply VIS; reflexivity].
        destruct (v' (Z_to_bv 64 a)); [discriminate|]. exfalso. apply WM; [discriminate| reflexivity].
    - intros a Ha Hni VIS'. rewrite EV in VIS'. change (aview_of (ahull A) m) with (aview A m).
      destruct (Classical_Prop.classic (outside W a)) as [OUT|NIN].
      + rewrite <- (EQ a Ha OUT). exact VIS'.
      + (first [ pose proof ((client_fpx_facts A m md W a AI0 CF NIN)) as dR_6; dand4 dR_6 as _ _ _ VIS | destruct (client_fpx_facts A m md W a AI0 CF NIN) as (_ & _ & _ & VIS) ]). exact (VIS Hni).
    - exact MI.
    - exact SB.
  Qed.

  (* [comment removed for export] *)
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
End S.

(* [comment removed for export] *)
Ltac astopx AINV MU WM CF :=
  lazymatch type of AINV with @ainv _ ?L ?AI ?A ?m ?md =>
    apply (astopx_lemma (L:=L) A m md _ _ _ _ _ _ _ _ AINV MU WM CF);
    let m1 := fresh "m" in let md1 := fresh "md" in
    let A1 := fresh "AINV" in let EV := fresh "EVIEW" in let SB := fresh "SBM" in let HID := fresh "HID" in
    intros m1 md1 A1 EV SB HID;
    first [ lazymatch type of EV with ?av = ?v' => is_var v'; subst v' end | rewrite <- EV in *; clear EV ]
  end.
End A_Fpx.


Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Stdlib.omega.PreOmega.Z.euclidean_division_equations_cleanup; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Kit.vk_lia_prune; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Open Scope Z_scope.

(* [comment removed for export] *)
Section ShLo.
  Context {Clg : Ceiling}.
  Lemma sh_lo : forall p, 0 <= p -> 2147450880 <= sh p.
  Proof. intros p Hp. unfold sh, kShadowOffset. Z.div_mod_to_equations. lia. Qed.
  (* [comment removed for export] *)
  Lemma sh_top_le : forall p n, 0 <= p -> 0 <= n -> p + n <= alloc_ceiling -> sh p + (n + 7) / 8 <= sh alloc_ceiling.
  Proof.
    intros p n Hp Hn H. pose proof alloc_ceiling_mod16 as M. unfold sh. Z.div_mod_to_equations. lia.
  Qed.
  Lemma sh_boundL : forall p n, 0 <= p -> 0 <= n -> p + n <= alloc_ceiling ->
    2147450880 <= sh p /\ sh p + (n + 7) / 8 <= SHMAX /\ SHMAX + 8 <= alloc_ceiling.
  Proof. intros p n Hp Hn H. pose proof (sh_bound p n Hp Hn H). pose proof (sh_lo p Hp). lia. Qed.
  Lemma shpat_sh_boundL : forall p n, 0 <= p -> 0 <= n -> p + n <= alloc_ceiling ->
    2147450880 <= sh p /\ sh p + Z.of_nat (length (shpat n)) <= SHMAX /\ SHMAX + 8 <= alloc_ceiling.
  Proof. intros p n Hp Hn H. rewrite shpat_length by lia. apply sh_boundL; lia. Qed.
  (* [comment removed for export] *)
End ShLo.

Section App.
  Context {Clg : Ceiling} (L : clayout) {AI : AsanAlloc L}.

  (* [comment removed for export] *)
  Lemma app_facts : forall p n, app_range L p n ->
    (4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling) /\ off_image L p n /\
    (p + n <= 2147446784 (* [comment removed for export] *) \/ 17594333495296 (* [comment removed for export] *) <= p) /\ shadow_apart p n.
  Proof.
    intros p n H. split; [exact (app_range_pos L p n H)|]. split; [exact (off_image_app L p n H)|].
    split; [pose proof (app_noshadow_of L p n H) as NS; unfold app_noshadow, kLowShadowMapBeg, kHighMemBeg in NS; exact NS|].
    exact (app_shadow_apart L p n H).
  Qed.

  (* [comment removed for export] *)
  Lemma app_sh_facts : forall p n, app_range L p n ->
    2147451392 (* [comment removed for export] *) <= sh p /\ sh p + (n + 7) / 8 <= SHMAX /\ SHMAX + 8 <= alloc_ceiling /\
    (sh p + (n + 7) / 8 <= 2415881728 (* [comment removed for export] *) \/ 2201439137792 (* [comment removed for export] *) <= sh p).
  Proof.
    intros p n H. (first [ pose proof ((app_facts p n H)) as dR_1; dand4 dR_1 as (P1 & P2 & P3) _ NS _ | pose proof (app_facts p n H) as ((P1 & P2 & P3) & _ & NS & _) ]).
    (first [ pose proof ((sh_bound p n ltac:(lia) P2 P3)) as dR_2; dand3 dR_2 as S1 S2 S3 | pose proof (sh_bound p n ltac:(lia) P2 P3) as (S1 & S2 & S3) ]).
    unfold sh, kShadowOffset in *. split; [lia|]. split; [lia|]. split; [lia|].
    destruct NS as [NS|NS]; [left| right]; Z.div_mod_to_equations; lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma sh_le_ceiling : forall p n, p mod 8 = 0 -> 0 <= n -> p + n <= alloc_ceiling -> sh p + (n + 7) / 8 <= sh alloc_ceiling.
  Proof. intros p n P8 N0 H. pose proof alloc_ceiling_mod16 as M. unfold sh. Z.div_mod_to_equations. lia. Qed.
  Lemma sh_ceiling_le_SHMAX : sh alloc_ceiling <= SHMAX.
  Proof. pose proof alloc_ceiling_num as ACV. unfold sh, kShadowOffset, SHMAX. Z.div_mod_to_equations. lia. Qed.
  Lemma sh_ceiling_ge : 17594064011264 <= sh alloc_ceiling.
  Proof. pose proof alloc_ceiling_num as ACV. unfold sh, kShadowOffset. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  Lemma live_high : forall A m md p n, ainv A m md -> a_live A p = Some n -> n <= 64512 -> kHighMemBeg <= p.
  Proof. intros A m md p n AI0 LV Hn. eapply (as_live_primary_high L A m md p n AI0 LV). unfold kMaxPrimaryUser. exact Hn. Qed.
  (* [comment removed for export] *)
  Lemma live_above_image : forall A m md p n, ainv A m md -> a_live A p = Some n -> cl_image_lo L <= 65536 -> cl_image_hi L <= p.
  Proof.
    intros A m md p n AI0 LV HLO. (first [ pose proof ((live_geom L A m md p n AI0 LV)) as dR_4; dand4 dR_4 as _ _ AR _ | destruct (live_geom L A m md p n AI0 LV) as (_ & _ & AR & _) ]).
    (first [ pose proof ((app_facts p n AR)) as dR_5; dand4 dR_5 as (P1 & P2 & P3) IMG NS SA | pose proof (app_facts p n AR) as ((P1 & P2 & P3) & IMG & NS & SA) ]). pose proof layout_facts as LF.
    unfold off_image in IMG. destruct (Z_lt_le_dec 64512 n) as [BIG|SMALL].
    - destruct IMG as [IMG|IMG]; [| exact IMG]. exfalso. unfold kLowShadowMapBeg, kHighMemBeg in *. lia.
    - pose proof (live_high A m md p n AI0 LV SMALL) as HI. unfold kHighMemBeg in HI. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma live_geomP : forall A m md p n, ainv A m md -> a_live A p = Some n ->
    0 <= n < REQ_MAX /\ p mod 16 = 0 /\
    (app_range L p n /\ (n <= 64512 -> kHighMemBeg <= p) /\ (cl_image_lo L <= 65536 -> cl_image_hi L <= p)) /\ p + n <= alloc_ceiling /\ off_image L p n /\
    mapped (aview A m) p n /\ (forall i, 0 <= i < n -> ~ owned A (p + i)).
  Proof.
    intros A m md p n AI0 LV. (first [ pose proof ((live_geom L A m md p n AI0 LV)) as dR_7; dand7 dR_7 as A1 A2 A3 A4 A5 A6 A7 | destruct (live_geom L A m md p n AI0 LV) as (A1 & A2 & A3 & A4 & A5 & A6 & A7) ]).
    split; [exact A1|]. split; [exact A2|].
    split; [split; [exact A3| split; [exact (live_high A m md p n AI0 LV)| exact (live_above_image A m md p n AI0 LV)]]|].
    split; [exact A4|]. split; [exact A5|]. split; [exact A6| exact A7].
  Qed.

  (* [comment removed for export] *)
  Lemma app_lin : forall p n, app_range L p n -> exists ix sx : Z,
    0 <= ix <= 1 /\ 0 <= sx <= 1 /\ 4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling /\
    p + n <= cl_image_lo L + ix * 281474976710656 /\ ix * cl_image_hi L <= p /\
    p + n <= 2147446784 + sx * 281474976710656 /\ sx * 17594333495296 <= p /\
    2147451392 <= sh p /\ sh p + (n + 7) / 8 <= 17594332446720 /\ 17594332446728 <= alloc_ceiling /\
    8 * (sh p - 2147450880) <= p /\ p < 8 * (sh p - 2147450880) + 8 /\
    p + n <= sh p + sx * 281474976710656 /\ sh p + (n + 7) / 8 <= p + (1 - sx) * 281474976710656 /\
    sh p + (n + 7) / 8 <= sh alloc_ceiling.
  Proof.
    intros p n H. (first [ pose proof ((app_facts p n H)) as dR_8; dand4 dR_8 as (P1 & P2 & P3) IMG NS SA | pose proof (app_facts p n H) as ((P1 & P2 & P3) & IMG & NS & SA) ]).
    pose proof (sh_top_le p n ltac:(lia) P2 P3) as TT.
    (first [ pose proof ((sh_bound p n ltac:(lia) P2 P3)) as dR_9; dand3 dR_9 as S1 S2 S3 | pose proof (sh_bound p n ltac:(lia) P2 P3) as (S1 & S2 & S3) ]). rewrite SHMAX_val in S2, S3.
    unfold off_image in IMG. unfold shadow_apart in SA. pose proof layout_facts as LF.
    assert (D8 : 8 * (sh p - 2147450880) <= p < 8 * (sh p - 2147450880) + 8)
      by (unfold sh, kShadowOffset; Z.div_mod_to_equations; lia).
    assert (LO : 2147451392 <= sh p) by (unfold sh, kShadowOffset in *; Z.div_mod_to_equations; lia).
    destruct NS as [NS|NS].
    - assert (SA' : p + n <= sh p) by (unfold sh, kShadowOffset in *; Z.div_mod_to_equations; lia).
      destruct IMG as [IMG|IMG]; [exists 0, 0| exists 1, 0]; lia.
    - assert (SA' : sh p + (n + 7) / 8 <= p) by lia.
      exists 1, 1. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma app_lin_high : forall p n, 17594333495296 <= p -> app_range L p n ->
    4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling /\ cl_image_hi L <= p /\
    2201439137792 <= sh p /\ sh p + (n + 7) / 8 <= 17594332446720 /\ 17594332446728 <= alloc_ceiling /\
    8 * (sh p - 2147450880) <= p /\ p < 8 * (sh p - 2147450880) + 8 /\ sh p + (n + 7) / 8 <= p /\
    sh p + (n + 7) / 8 <= sh alloc_ceiling.
  Proof.
    intros p n HI H. (first [ pose proof ((app_facts p n H)) as dR_10; dand4 dR_10 as (P1 & P2 & P3) IMG NS SA | pose proof (app_facts p n H) as ((P1 & P2 & P3) & IMG & NS & SA) ]).
    (first [ pose proof ((sh_bound p n ltac:(lia) P2 P3)) as dR_11; dand3 dR_11 as S1 S2 S3 | pose proof (sh_bound p n ltac:(lia) P2 P3) as (S1 & S2 & S3) ]). rewrite SHMAX_val in S2, S3.
    pose proof layout_facts as LF. pose proof (sh_top_le p n ltac:(lia) P2 P3) as TT.
    revert TT. unfold sh, kShadowOffset in *. Z.div_mod_to_equations. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma app_lin_img : forall p n, cl_image_hi L <= p -> app_range L p n -> exists sx : Z,
    0 <= sx <= 1 /\ 4096 <= p /\ 0 <= n /\ p + n <= alloc_ceiling /\ cl_image_hi L <= p /\
    p + n <= 2147446784 + sx * 281474976710656 /\ sx * 17594333495296 <= p /\
    2147451392 <= sh p /\ sh p + (n + 7) / 8 <= 17594332446720 /\ 17594332446728 <= alloc_ceiling /\
    8 * (sh p - 2147450880) <= p /\ p < 8 * (sh p - 2147450880) + 8 /\
    p + n <= sh p + sx * 281474976710656 /\ sh p + (n + 7) / 8 <= p + (1 - sx) * 281474976710656 /\
    sh p + (n + 7) / 8 <= sh alloc_ceiling.
  Proof.
    intros p n HI H. (first [ pose proof ((app_lin p n H)) as dR_12; dex2 dR_12 as ix sx; rename dR_12 into B | pose proof ((app_lin p n H)) as dR_12; dand3 dR_12 as ix sx B | destruct (app_lin p n H) as (ix & sx & B) ]). exists sx. lia.
  Qed.
End App.

(* [comment removed for export] *)
Ltac app_facts_of H B IMG NS SA :=
  lazymatch type of H with
  | app_range ?L ?p ?n => (first [ pose proof ((app_facts L p n H)) as dR_13; dand4 dR_13 as B IMG NS SA | pose proof (app_facts L p n H) as (B & IMG & NS & SA) ])
  end.

(* [comment removed for export] *)
Definition app_rangeF {Clg : Ceiling} (L : clayout) (p n : Z) : Prop := app_range L p n.
(* [comment removed for export] *)
Definition akept (P : Prop) : Prop := P.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ahide H := (lazymatch type of H with ?T__ => change (akept T__) in H end).
Ltac unhide_app := repeat match goal with H : akept _ |- _ => (lazymatch type of H with akept ?T__ => change T__ in H | _ => idtac end) end.
Ltac unhide_app_img := repeat match goal with H : akept (_ \/ 6332416 <= _) |- _ => (lazymatch type of H with akept ?T__ => change T__ in H | _ => idtac end) end.
Ltac unhide_app_sh := repeat match goal with H : akept (_ \/ 17594333495296 <= _) |- _ => (lazymatch type of H with akept ?T__ => change T__ in H | _ => idtac end) end.
Ltac unhide_app_of p := repeat match goal with H : akept (p + _ <= _ \/ _ <= p) |- _ => (lazymatch type of H with akept ?T__ => change T__ in H | _ => idtac end) end.
(* [comment removed for export] *)
Definition v16K : Prop := SHMAX = 17594332446720 /\ kHighMemBeg = 17594333495296 /\ kLowShadowMapBeg = 2147446784
                          /\ kLowShadowBeg = 2147450880 /\ kShadowOffset = 2147450880 /\ kLowMemEnd = 2147450879.
Lemma v16K_holds : v16K. Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Ltac app_lin_norm H n :=
  (* [comment removed for export] *)
  try (lazymatch n with
       | Z0 => idtac | Zpos _ => idtac
       end;
       let k := eval vm_compute in ((n + 7) / 8) in change ((n + 7) / 8) with k in H).
Ltac all_app_facts :=
  lazymatch goal with
  | _ : v16K |- _ => idtac
  | |- _ => let M := fresh "V16M" in let K := fresh "V16K" in pose proof v16K_holds as M; pose proof M as K; unfold v16K in K;
            try (let C1 := fresh "V16C" in pose proof sh_ceiling_ge as C1; let C2 := fresh "V16C" in pose proof sh_ceiling_le_SHMAX as C2)
  end;
  repeat match goal with
  | H : app_range ?L ?p ?n /\ (?n <= 64512 -> ?hb <= ?p) /\ (_ -> ?ih <= ?p) |- _ =>
      (* [comment removed for export] *)
      let Hh := fresh H "_h" in let Ha := fresh H "_a" in let Hl := fresh H "_l" in let Hi := fresh H "_ih" in let sx := fresh "sx" in
      (first [ dand3 H as Ha Hh Hi | destruct H as (Ha & Hh & Hi) ]);
      first [ specialize (Hh ltac:(clear; lia)); unfold kHighMemBeg in Hh; rename Hh into H; clear Hi;
              pose proof (app_lin_high L p n H Ha) as Hl;
              (let hi := eval lazy in (cl_image_hi L) in try change (cl_image_hi L) with hi in Hl);
              app_lin_norm Hl n;
              change (app_rangeF L p n) in Ha
            | clear Hh; specialize (Hi ltac:(clear; lazy; lia));
              destruct (app_lin_img L p n Hi Ha) as (sx & H); clear Hi;
              (let hi := eval lazy in (cl_image_hi L) in try change (cl_image_hi L) with hi in H);
              app_lin_norm H n;
              change (app_rangeF L p n) in Ha
            | clear Hi; rename Ha into H ]
  | H : app_range ?L ?p ?n /\ (?n <= 64512 -> ?hb <= ?p) |- _ =>
      (* [comment removed for export] *)
      let Hh := fresh H "_h" in let Ha := fresh H "_a" in let Hl := fresh H "_l" in
      destruct H as [Ha Hh];
      first [ specialize (Hh ltac:(clear; lia)); unfold kHighMemBeg in Hh; rename Hh into H;
              pose proof (app_lin_high L p n H Ha) as Hl;
              (let hi := eval lazy in (cl_image_hi L) in try change (cl_image_hi L) with hi in Hl);
              app_lin_norm Hl n;
              change (app_rangeF L p n) in Ha
            | clear Hh; rename Ha into H ]
  | H : app_range ?L ?p ?n |- _ =>
      (* [comment removed for export] *)
      let Ha := fresh H "_a" in let ix := fresh "ix" in let sx := fresh "sx" in
      rename H into Ha;
      destruct (app_lin L p n Ha) as (ix & sx & H);
      (let lo := eval lazy in (cl_image_lo L) in let hi := eval lazy in (cl_image_hi L) in
       try change (cl_image_lo L) with lo in H; try change (cl_image_hi L) with hi in H);
      app_lin_norm H n;
      change (app_rangeF L p n) in Ha
  end.
(* [comment removed for export] *)
Ltac all_app_bounds :=
  lazymatch goal with
  | _ : v16K |- _ => idtac
  | |- _ => let M := fresh "V16M" in let K := fresh "V16K" in pose proof v16K_holds as M; pose proof M as K; unfold v16K in K
  end;
  repeat match goal with
  | H : app_range ?L ?p ?n /\ (?n <= 64512 -> ?hb <= ?p) /\ (_ -> ?ih <= ?p) |- _ =>
      let Hh := fresh H "_h" in let Ha := fresh H "_a" in let Hi := fresh H "_ih" in
      (first [ dand3 H as Ha Hh Hi | destruct H as (Ha & Hh & Hi) ]);
      first [ specialize (Hh ltac:(clear; lia)); unfold kHighMemBeg in Hh; rename Hh into H; clear Hi; change (app_rangeF L p n) in Ha
            | clear Hh Hi; rename Ha into H ]
  | H : app_range ?L ?p ?n /\ (?n <= 64512 -> ?hb <= ?p) |- _ =>
      let Hh := fresh H "_h" in let Ha := fresh H "_a" in
      destruct H as [Ha Hh];
      first [ specialize (Hh ltac:(clear; lia)); unfold kHighMemBeg in Hh; rename Hh into H; change (app_rangeF L p n) in Ha
            | clear Hh; rename Ha into H ]
  | H : app_range ?L ?p ?n |- _ =>
      let Ha := fresh H "_a" in rename H into Ha; pose proof (app_range_pos L p n Ha) as H; change (app_rangeF L p n) in Ha
  end.

(* [comment removed for export] *)
Ltac app_shadow_of H :=
  let S := fresh H "_s" in let S2 := fresh H "_s8" in
  lazymatch type of H with
  | app_rangeF ?L ?p ?n => pose proof (app_shadow_apart L p n H) as S
  | app_range ?L ?p ?n => pose proof (app_shadow_apart L p n H) as S
  end;
  pose proof S as S2; unfold shadow_apart in S; unfold shadow_apart, sh, kShadowOffset in S2.
Ltac unF := unfold app_rangeF in *.

(* [comment removed for export] *)
Ltac fold_aview :=
  repeat match goal with
  | H : context [aview_of (@ahull ?C ?L ?AI ?A) ?m] |- _ => change (aview_of (@ahull C L AI A) m) with (@aview C L AI A m) in H
  | |- context [aview_of (@ahull ?C ?L ?AI ?A) ?m] => change (aview_of (@ahull C L AI A) m) with (@aview C L AI A m)
  end.

