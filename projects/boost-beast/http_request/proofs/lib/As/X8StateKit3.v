(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr Frame TacX Bytes StoreDj.
From OSSVerify.Proofs.boost_beast.http_request.lib.Ref Require Import XE_kit.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import AXRep AXRep2 AXPRep AXPRep2 AXRep_leafP N8Kit N8Kit2 N8Kit3 X8Kit X8Call X8LeafKit X8StateKit X8StateKit2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.


Ltac assign_loc_coreW W3 MEMCPY ASSIGNA SIDE MU WM FW HC1 TMP EC ST MI APE D8 BND D E e loc lo shi sp g j24 ej m :=
  steps_to 0xb8dd8%Z;
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let AS := fresh "AS" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SIDE MU WM FW) as SDc;
    pose proof ASSIGNA as AS;
    unfold aassignA_stmt, aassign_stmt, aassign_post, aassign_W, P_A_EC_CTOR_HTTP, AG_HTTP_CAT, AASSIGN_STACK, AINTRIN_STACK in AS;
    callZc (AS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D e lo shi g j24) (clear TMP ST AS);
    [ exact TMP | exact HC1 | exact (pside2_statics _ _ _ _ _ SDc) | rewrite ?unsigned_lit by (bnd_lia BND); exact ST
    | rewrite ?unsigned_lit by (bnd_lia BND); bnd_lia BND | bnd_lia BND | rewrite ?unsigned_lit by (bnd_lia BND); bnd_lia BND | bnd_lia BND
    | exact D8 | clear; lia
    | exact MI | exact (pside2_aconst _ _ _ _ _ SDc) | exact (pside2_stack0 _ _ _ _ _ SDc)
    | rewrite ?unsigned_lit by (bnd_lia BND); bnd_lia BND | ];
    clear SDc HC1 D8
  end;
  lazymatch goal with
  | TMP2 : rw_cells _ ?m2 D (ErrCodeCells _), HC2 : AHttpCat ?m2 true,
    AC2 : ACONST ?m2, SK2 : stack0 ?m2 lo shi, ST2 : stk _ ?m2 lo ?spc, MU' : munch _ m ?m2, WM' : wmono _ m ?m2 |- _ =>
    let SD2 := fresh "SD2" in let KF := fresh "KF" in
    let TMPa := fresh "TMPa" in let TMPb := fresh "TMPb" in let ECa := fresh "ECa" in let ECb := fresh "ECb" in
    let SRC := fresh "SRC" in let MU3 := fresh "MU3" in let WM3 := fresh "WM3" in
    pose proof (pside2_transport _ _ m2 _ _ _ _ SIDE ltac:(unfold AG_HTTP_CAT; exact MU') WM' FW) as SD2;
    (* [comment removed for export] *)
    unfold ErrCodeCells, EC_http, ec_make in TMP2; cbn [ec_val ec_cat ec_flags Z.eqb] in TMP2; unfold AG_HTTP_CAT, wz in TMP2;
    repeat (lazymatch goal with |- evt _ _ (MS _ _ _ _ _ _ _) => step end);
    if_cases KF; zify_cond KF; [exfalso; clear - KF; lia|];
    (* [comment removed for export] *)
    zstep; change (Z.land 3 1) with 1; step; step; zstep;
    replace (Z.lor 1 loc) with (loc + 1) by (vm_compute; reflexivity);
    (* [comment removed for export] *)
    steps_to 0x7186c%Z;
    split_frameA TMP2 [C8 (Z_to_bv 64 e); C8 (Z_to_bv 64 6667600)] [C8 (Z_to_bv 64 3)] TMPa TMPb;
    pose proof (rw_cells_bytes_at _ _ _ _ TMPa) as SRC; cbn [cells_bytes cbytes app] in SRC; rewrite app_nil_r in SRC;
    destruct (rw_cells_CB_split asegs _ E 24 16 ej EC ltac:(clear; lia)) as [ECa ECb]; clear EC;
    cbn [Nat.sub] in ECb; change (Z.of_nat 16) with 16 in ECb;
    pose proof (munch_refl W3 m2) as MU3; pose proof (wmono_refl asegs m2) as WM3;
    callZc (asan_memcpy_specZ MEMCPY _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ spc E D 16
              (le8 (Z_to_bv 64 e) ++ le8 (Z_to_bv 64 6667600)) (firstn 16 ej) lo)
           (clear ECa ST2 SRC);
    [ exact SRC | rewrite length_app, !length_le8; reflexivity | exact ECa
    | right; bnd_lia BND | clear; lia | bnd_lia BND | bnd_lia BND
    | eapply stack0_accessible; [exact SK2| bnd_lia BND| clear; lia| bnd_lia BND]
    | eapply accessible_sub; [exact (pside2_acc _ _ _ _ _ E 24 SD2 ltac:(ps_in))| clear; lia| clear; lia| clear; lia]
    | eapply stack0_shvis; [exact SK2| bnd_lia BND| clear; lia| bnd_lia BND]
    | eapply shvis_sub; [exact (pside2_shvis _ _ _ _ _ E 24 SD2 ltac:(ps_in))| bnd_lia BND| clear; lia| clear; lia| clear; lia| bnd_lia BND]
    | eapply stack0_in_app_mem; [exact SK2| bnd_lia BND| bnd_lia BND]
    | eapply aapp_in_app_mem; [exact APE| clear; lia| clear; lia]
    | eapply aconst_ok_aapp; [exact APE| clear; lia| clear; lia]
    | exact ST2 | bnd_lia BND | bnd_lia BND | bnd_lia BND
    | left; bnd_lia BND | right; clear; lia
    | assumption | exact AC2 | ];
    clear SK2 AC2 SD2
  end.


(* [comment removed for export] *)
Ltac assign_loc_closeW CATTAC SIDE FW E e loc m :=
  lazymatch goal with
  | DST : rw_cells _ ?m4 E [CB _ _], ECb' : rw_cells _ ?m4 (E + 16) [C8 _], MU4 : munch _ m ?m4, WM4 : wmono _ m ?m4,
    HC2 : AHttpCat ?m2 true, MU3' : munch _ ?m2 ?m4, WM3' : wmono _ ?m2 ?m4 |- _ =>
    let SD4 := fresh "SD4" in let HC4 := fresh "HC4" in
    let AC4 := fresh "AC4" in let SK4 := fresh "SK4" in let XS4 := fresh "XS4" in
    pose proof (pside2_transport _ _ m4 _ _ _ _ SIDE ltac:(unfold AG_HTTP_CAT; exact MU4) WM4 FW) as SD4;
    assert (HC4 : AHttpCat m4 true) by (eapply AHttpCat_transport; [exact HC2| exact MU3'| exact WM3'| CATTAC | CATTAC]);
    pose proof (pside2_aconst _ _ _ _ _ SD4) as AC4; pose proof (pside2_stack0 _ _ _ _ _ SD4) as SK4;
    pose proof (pside2_statics2 _ _ _ _ _ SD4) as XS4;
    join_frameA DST ECb' E;
    apply (ecloc_cells _ _ e loc ltac:(clear; lia)) in DST
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section IMG.
  Context {HCEIL : HeapCeil}.
  Lemma img_unhex_ok : forall m, ACONST m -> accessible m AL_TAB_UNHEX 256.
  Proof. intros m AC. apply (ACONST_gbody_accessible m AL_TAB_UNHEX 256 AC). vm_compute. reflexivity. Qed.
End IMG.

Ltac ps_chkw SD MU WM FW O n a BT PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let v := fresh "v" in let V1 := fresh "V1" in let V2 := fresh "V2" in let RD := fresh "RD" in
    let B1 := fresh "B1" in let B2 := fresh "B2" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    assert (B1 : O <= a) by BT; assert (B2 : a + 1 <= O + n) by BT;
    destruct (accessible_readw_sr mc a 1
                (accessible_sub _ _ _ a 1 (pside2_acc _ _ _ _ _ O n SDc ltac:(ps_in)) B1 B2 ltac:(clear; lia))
                ltac:(clear; lia) ltac:(clear; Z.div_mod_to_equations; lia)) as (v & V1 & V2 & RD);
    clear SDc B1 B2;
    PRE; clear RD;
    first [ rewrite (sxb_b8_small v) by (clear - V1; lia) | rewrite (zxb_b8_small v) by (clear - V1; lia) ];
    shchk_join V1 V2; clear V1 V2
  end.

Ltac ps_chkw_ge SD MU WM FW O n a BT PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let v := fresh "v" in let V1 := fresh "V1" in let V2 := fresh "V2" in let RD := fresh "RD" in
    let B1 := fresh "B1" in let B2 := fresh "B2" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    assert (B1 : O <= a) by BT; assert (B2 : a + 1 <= O + n) by BT;
    destruct (accessible_readw_sr mc a 1
                (accessible_sub _ _ _ a 1 (pside2_acc _ _ _ _ _ O n SDc ltac:(ps_in)) B1 B2 ltac:(clear; lia))
                ltac:(clear; lia) ltac:(clear; Z.div_mod_to_equations; lia)) as (v & V1 & V2 & RD);
    clear SDc B1 B2;
    PRE; clear RD;
    first [ rewrite (sxb_b8_small v) by (clear - V1; lia) | rewrite (zxb_b8_small v) by (clear - V1; lia) ];
    shchk_join_ge V1 V2; clear V1 V2
  end.

(* [comment removed for export] *)
Ltac ps_chktab SD MU WM FW x PRE :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    let SDc := fresh "SDc" in let RD := fresh "RD" in
    pose proof (pside2_transport _ _ mc _ _ _ _ SD MU WM FW) as SDc;
    pose proof (accessible_read0_in mc AL_TAB_UNHEX 256 x (img_unhex_ok mc (pside2_aconst _ _ _ _ _ SDc))
                  ltac:(reflexivity) ltac:(reflexivity) ltac:(unfold AL_TAB_UNHEX; lia)) as RD;
    unfold AL_TAB_UNHEX in RD; clear SDc;
    PRE; clear RD; sh0_lit;
    shchk_br
  end.
