(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_akit Sj_num_amem Od_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition od_rebase (E : odenv) (m : mem) : odenv :=
  mkOdEnv (o_ra E) (o_sp E) (o_gp E) (o_tp E) (o_s0 E) (o_s1 E) (o_s2 E) (o_s3 E) (o_s4 E) (o_s5 E) (o_s6 E) (o_s7 E) (o_s8 E) (o_s9 E)
          (o_s10 E) (o_s11 E) (o_lo E) (o_BUF E) (o_SB E) (o_CAP E) (o_IMPL E) (o_IDX E) (o_icap E) (o_COPY E) (o_act E) (o_bs E) (o_idxs E)
          (o_vptr E) (o_p12 E) (o_nxt E) (o_mid E) (o_docj E) (o_j304 E) (o_w320 E) (o_w328 E) (o_w336 E) (o_w344 E) (o_hi E) m.
Definition oa_rebase (E : oaenv) (m : mem) : oaenv := mkOaEnv (od_rebase E m) (oa_USP E) (oa_S1 E) (oa_F E).

Record od_geo (E : oaenv) : Prop := mkOdGeo {
  og_bytes : bytes_ok (o_bs E);
  og_s1 : S1OUT (o_bs E) (o_idxs E);
  og_len : o_len E <= S1_LEN_MAX;
  og_act : 0 <= o_act E <= 12;
  og_vptr : o_vptr E = Z_to_bv 64 OD_DPI_VPTR;
  og_tp : o_tp E = Z_to_bv 64 0x6488f0;
  og_usp : oa_USP E mod 16 = 0 /\ oa_USP E + 16 <= 0x800000000000;
  og_S1 : oa_S1 E mod 32 = 0 /\ oa_USP E - 528 <= oa_S1 E <= oa_USP E - 512;
  og_lo : 0x66b000 <= o_lo E /\ o_lo E + OD_NEED <= oa_S1 E;
  og_F : oa_F E mod 64 = 0 /\ 0x66b000 <= oa_F E /\ oa_F E + 512 <= o_lo E;
  og_Fsh : oa_F E / 8 + 2147450880 + 64 <= o_lo E
           /\ (oa_F E + 512 <= oa_F E / 8 + 2147450880 \/ oa_F E / 8 + 2147450880 + 64 <= oa_F E);
  og_copy : 0 < o_COPY E /\ o_COPY E mod 8 = 0 /\ o_COPY E <= o_BUF E <= o_COPY E + 3 /\ o_BUF E + o_len E + 64 <= o_lo E
            /\ (o_BUF E + o_len E + 64 <= 0x10000 \/ 0x66b000 <= o_COPY E);
  og_sb : 0 < o_SB E /\ o_SB E mod 8 = 0 /\ o_SB E + o_CAP E <= o_lo E /\ (o_SB E + o_CAP E <= 0x10000 \/ 0x66b000 <= o_SB E);
  og_cap : o_len E + 62 <= o_CAP E;
  og_cap8 : o_CAP E mod 8 = 0;
  og_impl : 0 < o_IMPL E /\ o_IMPL E mod 8 = 0 /\ o_IMPL E + 96 <= o_lo E /\ (o_IMPL E + 96 <= 0x10000 \/ 0x66b000 <= o_IMPL E);
  og_idx : 0 < o_IDX E /\ o_IDX E mod 8 = 0 /\ o_IDX E + 4 * Z.of_nat (o_icap E) <= o_lo E
           /\ (o_IDX E + 4 * Z.of_nat (o_icap E) <= 0x10000 \/ 0x66b000 <= o_IDX E);
  og_icap : o_n E + 4 <= Z.of_nat (o_icap E);
  og_sb_buf : o_SB E + o_CAP E <= o_COPY E \/ o_BUF E + o_len E + 64 <= o_SB E;
  og_sb_idx : o_SB E + o_CAP E <= o_IDX E \/ o_IDX E + 4 * Z.of_nat (o_icap E) <= o_SB E;
  og_sb_impl : o_SB E + o_CAP E <= o_IMPL E \/ o_IMPL E + 96 <= o_SB E;
  og_F_buf : oa_F E + 512 <= o_COPY E \/ o_BUF E + o_len E + 64 <= oa_F E;
  og_F_sb : oa_F E + 512 <= o_SB E \/ o_SB E + o_CAP E <= oa_F E;
  og_F_idx : oa_F E + 512 <= o_IDX E \/ o_IDX E + 4 * Z.of_nat (o_icap E) <= oa_F E;
  og_F_impl : oa_F E + 512 <= o_IMPL E \/ o_IMPL E + 96 <= oa_F E;
  og_Fs_sb : oa_F E / 8 + 2147450880 + 64 <= o_SB E \/ o_SB E + o_CAP E <= oa_F E / 8 + 2147450880
}.

Lemma od_geo_rebase : forall E m, od_geo E -> od_geo (oa_rebase E m).
Proof. intros E m [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?]. constructor; assumption. Qed.

Lemma od_geo_of_oka : forall E, od_oka E -> o_CAP E mod 8 = 0 -> o_tp E = Z_to_bv 64 0x6488f0 -> od_geo E.
Proof.
  intros E [? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ? ?] C8 TP. constructor; assumption.
Qed.

Ltac og_env G :=
  let BOK := fresh "BOK" in let S1 := fresh "S1" in let LEN := fresh "LEN" in let ACT := fresh "ACT" in let VPT := fresh "VPT" in
  let ETP := fresh "ETP" in
  let USP16 := fresh "USP16" in let USPT := fresh "USPT" in let S32 := fresh "S32" in let S1R := fresh "S1R" in
  let LOB := fresh "LOB" in let LOR := fresh "LOR" in
  let F64 := fresh "F64" in let FB := fresh "FB" in let FR := fresh "FR" in let FSH := fresh "FSH" in let FSD := fresh "FSD" in
  let CP0 := fresh "CP0" in let CP8 := fresh "CP8" in let CPB := fresh "CPB" in let BUFR := fresh "BUFR" in let BUFD := fresh "BUFD" in
  let SB0 := fresh "SB0" in let SB8 := fresh "SB8" in let SBR := fresh "SBR" in let SBD := fresh "SBD" in let CAPR := fresh "CAPR" in
  let CAP8 := fresh "CAP8" in
  let IM0 := fresh "IM0" in let IM8 := fresh "IM8" in let IMR := fresh "IMR" in let IMD := fresh "IMD" in
  let IX0 := fresh "IX0" in let IX8 := fresh "IX8" in let IXR := fresh "IXR" in let IXD := fresh "IXD" in let ICAP := fresh "ICAP" in
  let S_SB := fresh "S_SB" in let S_SI := fresh "S_SI" in let S_SM := fresh "S_SM" in
  let F_B := fresh "F_B" in let F_S := fresh "F_S" in let F_I := fresh "F_I" in let F_M := fresh "F_M" in let FS_S := fresh "FS_S" in
  pose proof G as [BOK S1 LEN ACT VPT ETP [USP16 USPT] [S32 S1R] [LOB LOR] [F64 [FB FR]] [FSH FSD]
                   [CP0 [CP8 [CPB [BUFR BUFD]]]] [SB0 [SB8 [SBR SBD]]] CAPR CAP8 [IM0 [IM8 [IMR IMD]]] [IX0 [IX8 [IXR IXD]]] ICAP
                   S_SB S_SI S_SM F_B F_S F_I F_M FS_S];
  clear FSD BUFD SBD IMD IXD S_SB S_SI S_SM F_B F_S F_I F_M FS_S;
  unfold S1_LEN_MAX, OD_NEED, OD_DPI_VPTR in *;
  lazymatch goal with E : oaenv |- _ =>
    let NR := fresh "NR" in pose proof (od_n_range E S1) as NR
  end.

Definition od_Wk (E : oaenv) : list (Z * Z) := [(oa_F E + 192, oa_F E + 256); (o_SB E, o_SB E + o_CAP E)].

Section Cps.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Record od_rt (Σ : rts RT) (E : oaenv) (mL : mem) : Prop := mkOdRt {
  ort_art : ART RT Σ (o_m0 E);
  ort_frames : rt_frames RT Σ = [(oa_F E, 3%nat)];
  ort_copy : In (o_COPY E, o_BUF E - o_COPY E + o_len E + 64) (rt_live RT Σ);
  ort_sb : In (o_SB E, o_CAP E) (rt_live RT Σ);
  ort_impl : In (o_IMPL E, 96) (rt_live RT Σ);
  ort_idx : In (o_IDX E, 4 * Z.of_nat (o_icap E)) (rt_live RT Σ);
  ort_lo : rt_sp0 RT Σ - STACK_WIN <= o_lo E;
  ort_shp : bytes_at asegs (o_m0 E) (oa_F E / 8 + 2147450880 + 12) (repeat (Z_to_bv 8 0) 7);
  ort_shd : bytes_at asegs (o_m0 E) (oa_F E / 8 + 2147450880 + 24) (repeat (Z_to_bv 8 0) 8);
  ort_keep : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (oa_S1 E + 352) (od_Wk E) mL (o_m0 E);
  ort_wm : wmono asegs mL (o_m0 E)
}.

Lemma od_rt_self : forall Σ E mL, od_rt Σ E mL -> od_rt Σ (oa_rebase E (o_m0 E)) mL.
Proof using. intros Σ E mL [? ? ? ? ? ? ? ? ? ? ?]. constructor; assumption. Qed.
Lemma od_rt_rebase2 : forall Σ E mL m m', od_rt Σ (oa_rebase (oa_rebase E m) m') mL -> od_rt Σ (oa_rebase E m') mL.
Proof using. intros Σ E mL m m' [? ? ? ? ? ? ? ? ? ? ?]. constructor; assumption. Qed.

Lemma od_fp_ok : forall Σ E mL, od_geo E -> od_rt Σ E mL -> fp_ok RT Σ (o_lo E) (od_W E).
Proof using.
  intros Σ E mL G R. destruct G as [_ _ _ _ _ _ [_ USPT] [_ S1R] [LOB LOR] [F64 [FB FR]] _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  unfold fp_ok, od_W. repeat apply Forall_cons; [| | | apply Forall_nil]; cbn [fst snd].
  - left. unfold OD_NEED, USTACK_TOP in *. lia.
  - right; right; left. exists (oa_F E), 3%nat. split; [rewrite (ort_frames _ _ _ R); left; reflexivity|].
    unfold fs_size. change (Z.shiftl 64 (Z.of_nat 3)) with 512. lia.
  - right; left. exists (o_SB E), (o_CAP E). split; [exact (ort_sb _ _ _ R)| lia].
Qed.

Lemma od_art_cur : forall Σ E mL m1, od_geo E -> od_rt Σ E mL ->
  munch (od_W E) (o_m0 E) m1 -> wmono asegs (o_m0 E) m1 -> ART RT Σ m1.
Proof using AF.
  intros Σ E mL m1 G R MU WM.
  exact (art_of_munch RT AF Σ (o_m0 E) m1 (o_lo E) (od_W E) (ort_art _ _ _ R) (ort_lo _ _ _ R) (od_fp_ok Σ E mL G R) MU WM).
Qed.

Lemma od_shz_lit : forall Σ m a n, ART RT Σ m -> In (a, n) ACC_LITS -> a mod 8 = 0 -> 0 <= a -> n mod 8 = 0 -> shz m a n.
Proof using AF.
  intros Σ m a n HA Hin A8 A0 N8. pose proof (acc_lit RT AF Σ m a n HA Hin) as AC.
  pose proof (shz_of_acc m a n AC A8 A0) as S. replace (8 * (n / 8)) with n in S by (Z.div_mod_to_equations; lia). exact S.
Qed.

Local Ltac lit_in := unfold ACC_LITS; repeat (first [left; reflexivity | right]).

Lemma od_W_shadow_apart : forall E j k, od_geo E -> 0 <= j -> j + k <= 64 -> 0 <= k ->
  disjoint_from (od_W E) (oa_F E / 8 + 2147450880 + j) k.
Proof.
  intros E j k G J0 JK K0. destruct G as [_ _ _ _ _ _ _ _ [_ LOR] [_ [_ FR]] [FSH FSD] _ _ _ _ _ _ _ _ _ _ _ _ _ _ FS_S].
  unfold od_W, OD_NEED in *. cbn [disjoint_from]. clear - LOR FR FSH FSD FS_S J0 JK K0.
  set (s := oa_F E / 8) in *. clearbody s.
  split; [lia|]. split; [lia|]. split; [lia| exact I].
Qed.

Theorem od_oka_of_rt : forall Σ E mL, od_geo E -> od_rt Σ E mL -> od_oka E.
Proof using AF.
  intros Σ E mL G R. pose proof (od_fp_ok Σ E mL G R) as FP.
  pose proof (fun m' MU WM => od_art_cur Σ E mL m' G R MU WM) as ARTc.
  pose proof (od_W_shadow_apart E 12 7 G ltac:(lia) ltac:(lia) ltac:(lia)) as DJP.
  pose proof (od_W_shadow_apart E 24 8 G ltac:(lia) ltac:(lia) ltac:(lia)) as DJD.
  pose proof G as [BOK S1 LEN ACT VPT ETP USPR S1R LOR FR FSH COPYR SBR CAPR CAP8 IMPLR IDXR ICAP S_SB S_SI S_SM F_B F_S F_I F_M FS_S].
  assert (F8 : oa_F E mod 8 = 0) by (destruct FR as [F64 _]; clear - F64; Z.div_mod_to_equations; lia).
  assert (F0 : 0 <= oa_F E) by (destruct FR as [_ [FB _]]; clear - FB; lia).
  constructor; try assumption.
  - intros m' MU WM. apply (od_shz_lit Σ m' OD_TAB_FIN 256 (ARTc m' MU WM)); [lit_in| reflexivity| unfold OD_TAB_FIN; clear; lia| reflexivity].
  - intros m' MU WM. apply (od_shz_lit Σ m' OD_TAB_SOWN 256 (ARTc m' MU WM)); [lit_in| reflexivity| unfold OD_TAB_SOWN; clear; lia| reflexivity].
  - intros m' MU WM. apply (od_shz_lit Σ m' OD_TAB_SOW 256 (ARTc m' MU WM)); [lit_in| reflexivity| unfold OD_TAB_SOW; clear; lia| reflexivity].
  - intros m' MU WM. apply (od_shz_lit Σ m' OD_TAB_DIG 3544 (ARTc m' MU WM)); [lit_in| reflexivity| unfold OD_TAB_DIG; clear; lia| reflexivity].
  - intros m' MU WM. apply (od_shz_lit Σ m' OD_TAB_POW5 10416 (ARTc m' MU WM)); [lit_in| reflexivity| unfold OD_TAB_POW5; clear; lia| reflexivity].
  - intros m' MU WM. apply (od_shz_lit Σ m' OD_TAB_ESC 256 (ARTc m' MU WM)); [lit_in| reflexivity| unfold OD_TAB_ESC; clear; lia| reflexivity].
  - intros m' MU WM. apply (od_shz_lit Σ m' OD_DPI_VT 96 (ARTc m' MU WM)); [lit_in| reflexivity| unfold OD_DPI_VT; clear; lia| reflexivity].
  -
    intros m' MU WM. pose proof (shz_live RT AF Σ m' _ _ (ARTc m' MU WM) (ort_sb _ _ _ R) (proj1 (proj2 SBR))) as S.
    replace (8 * (o_CAP E / 8)) with (o_CAP E) in S by (clear - CAP8; Z.div_mod_to_equations; lia). exact S.
  -
    intros m' MU WM. exact (shz_live RT AF Σ m' _ _ (ARTc m' MU WM) (ort_impl _ _ _ R) (proj1 (proj2 IMPLR))).
  -
    intros m' MU WM. replace (oa_F E + 96) with (oa_F E + 8 * 12) by (clear; lia). change 56 with (8 * Z.of_nat 7).
    apply shz_run; [exact F8| exact F0| clear; lia|].
    apply (bytes_at_transport asegs (od_W E) (o_m0 E) m' _ _ (ort_shp _ _ _ R) MU).
    rewrite repeat_length. exact DJP.
  -
    intros m' MU WM. pose proof (shz_live RT AF Σ m' _ _ (ARTc m' MU WM) (ort_copy _ _ _ R) (proj1 (proj2 COPYR))) as S.
    eapply shz_sub; [exact S| clear; lia|]. clear. Z.div_mod_to_equations; lia.
  -
    intros m' MU WM. pose proof (shz_live RT AF Σ m' _ _ (ARTc m' MU WM) (ort_idx _ _ _ R) (proj1 (proj2 IDXR))) as S.
    eapply shz_sub; [exact S| clear; lia|]. clear - ICAP. Z.div_mod_to_equations; lia.
  -
    intros m' MU WM. replace (oa_F E + 192) with (oa_F E + 8 * 24) by (clear; lia). change 64 with (8 * Z.of_nat 8).
    apply shz_run; [exact F8| exact F0| clear; lia|].
    apply (bytes_at_transport asegs (od_W E) (o_m0 E) m' _ _ (ort_shd _ _ _ R) MU).
    rewrite repeat_length. exact DJD.
Qed.

End Cps.

Notation HLASTP E := (tokT (o_bs E) (o_idxs E) (o_n E - 1) = C_RBRACKET).

Notation ODXST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m :=
  (MS (mkR xra (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
           (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
      xF (Z_to_bv 64 OD_EXIT) xfc None m (seg_rom asegs)).

Definition od_plus_stmt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) st st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINV E st' m1 ->
    od_head_k E Q st' ->
    evt asegs Q (ODST E OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).

Definition od_head_stmt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) st0 st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_head_pre E st0 st -> frm0 xfc -> ODINVh E v344 st m1 ->
    od_exit_k E Q -> od_plus_k E Q st ->
    (od_head_ok (o_bs E) (o_idxs E) 1 st -> arm_k E Q 0x974f0 st) ->
    evt asegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).

Definition od_head_exit_stmt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) st v344 xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    o_depth st < 1 -> frm0 xfc -> ODINVh E v344 st m1 ->
    od_exit_k E Q ->
    evt asegs Q (ODST E OD_HEAD xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).

Definition od_slow_k (E : oaenv) (Q : machine_state -> Prop) (st : ost) : Prop :=
  forall xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1,
    frm0 xfc -> ODINV E st m1 ->
    evt asegs Q
      (MS (mkR (Z_to_bv 64 0x99498) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
               (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E))
               (Z_to_bv 64 (o_BUF E + tokI (o_bs E) (o_idxs E) (o_pos st))) xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 2) (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
               (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 200))
               (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 (Z_to_bv 64 1) (Z_to_bv 64 1))
          xF (Z_to_bv 64 OD_FROMCH) xfc None m1 (seg_rom asegs)).
Definition arm_dbl_evt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) st,
    HLASTP E -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st -> od_slow_k E Q st ->
    arm_k E Q 0x974f0 st.

Definition dbl_resume_stmt (E : oaenv) : Prop :=
  forall (Q : machine_state -> Prop) st xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    HLASTP E -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    od_plus_k E Q st ->
    frm0 xfc -> ODINV E st m1 ->
    evt asegs Q
      (MS (mkR (Z_to_bv 64 0x99498) (Z_to_bv 64 (oa_S1 E)) (o_gp E) (o_tp E) xt0 xt1 xt2
               (Z_to_bv 64 (oa_USP E)) (Z_to_bv 64 (oa_S1 E)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
               (Z_to_bv 64 2) (Z_to_bv 64 2147450880) (Z_to_bv 64 (oa_F E + 32)) (Z_to_bv 64 ((oa_F E + 200) / 8 + 2147450880))
               (Z_to_bv 64 (oa_F E + 192)) (Z_to_bv 64 ((oa_F E + 228) / 8 + 2147450880)) (Z_to_bv 64 (oa_F E + 200))
               (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xt5 xt6)
          xF (Z_to_bv 64 0x99498) xfc None m1 (seg_rom asegs)).

Definition OD_DBL_CREDIT : Z := 16.

Section CpsStmt.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.

Definition od_exit_kc (Σ0 : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) (c : Z) : Prop :=
  forall (Σ' : rts RT) m0' st vs6 v224 v248 v304 v312 v328 v344
         xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_rt RT Σ' (oa_rebase E m0') mL ->
    rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = rt_frames RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> c <= rt_credit RT Σ' ->
    frm0 xfc -> ODINVg (oa_rebase E m0') vs6 v224 v248 v304 v312 v328 v344 st m1 ->
    aevt RT PMc Σ' K (ODXST (oa_rebase E m0') xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Definition od_plus_kc (Σ0 : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) (c : Z) (st : ost) : Prop :=
  forall (Σ' : rts RT) m0' st' xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1,
    od_rt RT Σ' (oa_rebase E m0') mL ->
    rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = rt_frames RT Σ0 -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> c <= rt_credit RT Σ' ->
    od_arm_out (o_bs E) (o_idxs E) st st' -> frm0 xfc -> ODINV (oa_rebase E m0') st' m1 ->
    aevt RT PMc Σ' K (ODST (oa_rebase E m0') OD_PLUS xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs9 xs10 xs11 xt3 xt4 xF xfc m1).

Definition arm_dbl_cps : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (E : oaenv) (mL : mem) st xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs11 xt3 xt4 xF xfc m1,
    od_geo E -> od_rt RT Σ E mL -> HLASTP E -> od_head_ok (o_bs E) (o_idxs E) 1 st ->
    OD_DBL_CREDIT <= rt_credit RT Σ ->
    frm0 xfc -> ODINV E st m1 ->
    od_plus_kc Σ K E mL (rt_credit RT Σ - OD_DBL_CREDIT) st ->
    aevt RT PMc Σ K (ODST E 0x974f0 (Z_to_bv 64 122) xt1 xt2 (Z_to_bv 64 1) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 2) (Z_to_bv 64 (o_IDX E + 4 * o_pos st)) (Z_to_bv 64 (oa_F E + 192)) xs11 xt3 xt4 xF xfc m1).

End CpsStmt.
