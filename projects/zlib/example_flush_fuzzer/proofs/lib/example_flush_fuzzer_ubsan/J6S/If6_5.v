(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InffastModel InffastCtx InffastSafe IfSpec IfSpec6 If6_1 If6_5I.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac symex_auto ::=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia;
  try solve [ reflexivity | assumption | symex_ret_auto | symex_read_auto | symex_store_auto | symex_sok_auto | lia | split; lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition cfg5 : cfg :=
  CFG [] [] [EVar 1%nat]
      [0x1f9a8; 0x1f9d0; 0x1f9f0; 0x1fa04; 0x1fa38; 0x1fa48; 0x1fa54; 0x1fa90; 0x1fab8; 0x1fadc; 0x1fae4; 0x1fb1c; 0x1fb74; 0x1fb80;
       0x1fb94; 0x1fb9c; 0x1fbbc; 0x1fbd4; 0x1fbe0; 0x1fbf8; 0x1fc00; 0x1fc0c; 0x1fc34; 0x1fc64; 0x1fc7c; 0x1fc94; 0x1fca0; 0x1fcb8;
       0x1fcd0; 0x1fcd4; 0x1fcd8; 0x1fce0; 0x1fd10; 0x1fd14; 0x1fd38; 0x1fd44;
       0x1fd58; 0x1fd78; 0x1fd80; 0x1fd8c; 0x1fd90; 0x1fe10] [].

Lemma cpn_in : forall x n f, f_in (cpn x n f) = f_in f. Proof. intros. apply cpn_keep. Qed.
Lemma cpn_hold : forall x n f, f_hold (cpn x n f) = f_hold f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_bits : forall x n f, f_bits (cpn x n f) = f_bits f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_len : forall x n f, f_len (cpn x n f) = f_len f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_dist : forall x n f, f_dist (cpn x n f) = f_dist f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_ob : forall x n f, f_ob (cpn x n f) = cblit (x_window x) (f_from f) (f_ob f) (f_out f) n. Proof. intros. apply cpn_cblit. Qed.
Lemma cpn_from : forall x n f, f_from (cpn x n f) = fr_add (f_from f) n. Proof. intros. apply (cpn_cblit x n f). Qed.
Lemma fset_len_id : forall f, fset_len f (f_len f) = f. Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9]; reflexivity. Qed.

Section Walk.
Context {mem : word -> option byte} {sp : Z} {ra : word}
        {s : inflate_state} {c : icall} {r : iregs}
        {ZP S I0 P0 WB : Z}.
Variable C : iff_pre s6_segs is6_LENFIX is6_DISTFIX ROD6_LO ROD6_HI IMG6_TOP mem sp ra s c r ZP S I0 P0 WB.
Local Notation X := (ffx_of s c r).
Local Notation IN := (arr_len (ic_input c)).
Local Notation ON := (arr_len (ic_outbuf c)).
Local Notation WN := (arr_len (is_window s)).
Local Notation LC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_lencode s)).
Local Notation DC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_distcode s)).
Local Notation LCN := (ctab_len (is_lencode s)).
Local Notation DCN := (ctab_len (is_distcode s)).
Local Notation KR := (@KREGS6 sp ZP S I0 P0 WB X (is_lenbits s) (is_distbits s) LC DC).
Local Notation MEMI := (@MEMINV s6_segs mem sp (arr_len (ic_outbuf c)) ZP S P0).
Let Hret := ifp_ret C.
Let Hzin := ifp_zs_in C. Let Hzain := ifp_zs_ain C. Let Hzout := ifp_zs_out C. Let Hzaout := ifp_zs_aout C. Let Hzst := ifp_zs_state C.
Let Hsc := ifp_scalars C. Let Hcodes := ifp_codes C. Let Hcodes_b := ifp_codes_b C.
Let Hwin := ifp_win C. Let Hwin_b := ifp_win_b C. Let Hinp := ifp_in C. Let Hinp_b := ifp_in_b C.
Let Hout := ifp_out C. Let Hout_b := ifp_out_b C. Let Hrod := ifp_rod C.
Let Hsp0 : 0x5c000 <= sp := proj1 (ifp_sp C). Let Hsp1 : sp + 112 < 2 ^ 63 := proj2 (ifp_sp C).
Let HZP0 : 0 < ZP := proj1 (ifp_ZP C). Let HZP1 : ZP + 112 < 2 ^ 63 := proj2 (ifp_ZP C).
Let HS0 : 0 < S := proj1 (ifp_S C). Let HS1 : S + 7176 < 2 ^ 63 := proj2 (ifp_S C).
Let HI0 : 0 <= I0 := proj1 (ifp_I0 C). Let HI1 : I0 + IN < 2 ^ 63 := proj2 (ifp_I0 C).
Let HP0 : 0 < P0 := proj1 (ifp_P0 C). Let HP1 : P0 + ON < 2 ^ 63 := proj2 (ifp_P0 C).
Let HW0 : 0 <= WB := proj1 (ifp_WB C). Let HWN0 : 0 <= WN := proj1 (proj2 (ifp_WB C)). Let HW1 : WB + WN < 2 ^ 63 := proj2 (proj2 (ifp_WB C)).
Let Hd_spZ := ifp_d_spZ C. Let Hd_spS := ifp_d_spS C. Let Hd_spI := ifp_d_spI C. Let Hd_spP := ifp_d_spP C. Let Hd_spW := ifp_d_spW C.
Let Hd_PZ := ifp_d_PZ C. Let Hd_PS := ifp_d_PS C. Let Hd_PI := ifp_d_PI C. Let Hd_PW := ifp_d_PW C.
Let Hd_ZS := ifp_d_ZS C. Let Hd_ZI := ifp_d_ZI C. Let Hd_ZW := ifp_d_ZW C. Let Hd_SI := ifp_d_SI C. Let Hd_SW := ifp_d_SW C.
Let Hmap_sp := ifp_map_sp C. Let Hmap_P := ifp_map_P C. Let Hmap_Z := ifp_map_Z C. Let Hmap_S := ifp_map_S C.
Let Hnin0 : 0 <= ic_next_in c := proj1 (proj1 (ifp_r_in C)). Let Hnin1 : ic_next_in c <= IN := proj2 (proj1 (ifp_r_in C)).
Let Hain0 : 0 <= ic_avail_in c := proj1 (proj2 (ifp_r_in C)). Let Hain1 : ic_avail_in c < 2 ^ 32 := proj2 (proj2 (ifp_r_in C)).
Let Hnout0 : 0 <= ic_next_out c := proj1 (ifp_r_out C). Let Haout0 : 0 <= ic_avail_out c := proj1 (proj2 (ifp_r_out C)).
Let Hroom : ic_next_out c + ic_avail_out c <= ON := proj2 (proj2 (ifp_r_out C)).
Let Hbeg0 : 0 <= ir_out r - ic_avail_out c := proj1 (ifp_r_start C). Let Hbeg1 : ir_out r - ic_avail_out c <= ic_next_out c := proj2 (ifp_r_start C).
Let HON : ON < 2 ^ 32 := ifp_r_room C.
Let Hhold0 : 0 <= is_hold s := proj1 (ifp_r_hold C). Let Hhold1 : is_hold s < 2 ^ is_bits s := proj2 (ifp_r_hold C).
Let Hbits0 : 0 <= is_bits s := proj1 (ifp_r_bits C). Let Hbits1 : is_bits s < 64 := proj2 (ifp_r_bits C).
Let Hwsize0 : 0 <= is_wsize s := proj1 (proj1 (ifp_r_w C)). Let Hwsize1 : is_wsize s < 2 ^ 31 := proj2 (proj1 (ifp_r_w C)).
Let Hwhave0 : 0 <= is_whave s := proj1 (proj1 (proj2 (ifp_r_w C))). Let Hwhave1 : is_whave s < 2 ^ 31 := proj2 (proj1 (proj2 (ifp_r_w C))).
Let Hwnext0 : 0 <= is_wnext s := proj1 (proj2 (proj2 (ifp_r_w C))). Let Hwnext1 : is_wnext s < 2 ^ 31 := proj2 (proj2 (proj2 (ifp_r_w C))).
Let Hlenbits0 : 0 <= is_lenbits s := proj1 (proj1 (ifp_r_lb C)). Let Hlenbits1 : is_lenbits s <= 15 := proj2 (proj1 (ifp_r_lb C)).
Let Hdistbits0 : 0 <= is_distbits s := proj1 (proj2 (ifp_r_lb C)). Let Hdistbits1 : is_distbits s <= 15 := proj2 (proj2 (ifp_r_lb C)).
Let Hsane0 : 0 <= is_sane s := proj1 (ifp_r_sane C). Let Hsane1 : is_sane s < 2 ^ 31 := proj2 (ifp_r_sane C).
Let Hlmask0 : 0 <= x_lmask X := proj1 (ffx_lmask_range C). Let Hlmask1 : x_lmask X < 65536 := proj2 (ffx_lmask_range C).
Let Hdmask0 : 0 <= x_dmask X := proj1 (ffx_dmask_range C). Let Hdmask1 : x_dmask X < 65536 := proj2 (ffx_dmask_range C).
Let Hlast0 : 0 <= x_last X := proj1 (ffx_last_range C). Let Hlast1 : x_last X <= IN + 2 ^ 32 := proj2 (ffx_last_range C).
Let Hend0 : 0 <= x_end X := proj1 (ffx_end_range C). Let Hend1 : x_end X <= ON + 2 ^ 32 := proj2 (ffx_end_range C).
Let Hxbeg0 : 0 <= x_beg X := proj1 (ffx_beg_range C). Let Hxbeg1 : x_beg X <= ic_next_out c := proj2 (ffx_beg_range C).
Let HLC0 : 0 <= LC := proj1 (lc_bounds C). Let HLCN0 : 0 <= LCN := proj1 (proj2 (lc_bounds C)). Let HLC1 : LC + 4 * LCN < 2 ^ 63 := proj2 (proj2 (lc_bounds C)).
Let HDC0 : 0 <= DC := proj1 (dc_bounds C). Let HDCN0 : 0 <= DCN := proj1 (proj2 (dc_bounds C)). Let HDC1 : DC + 4 * DCN < 2 ^ 63 := proj2 (proj2 (dc_bounds C)).
Let Hhold64 : is_hold s < 2 ^ 64 := hold_lt64 C.
Let Hpow_lb0 : 1 <= 2 ^ is_lenbits s := proj1 (lenbits_pow C). Let Hpow_lb1 : 2 ^ is_lenbits s <= 32768 := proj2 (lenbits_pow C).
Let Hpow_db0 : 1 <= 2 ^ is_distbits s := proj1 (distbits_pow C). Let Hpow_db1 : 2 ^ is_distbits s <= 32768 := proj2 (distbits_pow C).
Let Hlmask_eq : x_lmask X = 2 ^ is_lenbits s - 1 := ffx_lmask_eq C. Let Hdmask_eq : x_dmask X = 2 ^ is_distbits s - 1 := ffx_dmask_eq C.
Let Hbeg_eq : x_beg X = ic_next_out c - (ir_out r - ic_avail_out c) := ffx_beg_eq C.

Local Ltac side :=
  lazymatch goal with
  | |- @ex _ _ => fail
  | |- _ =>
    rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
    first [ sep_solve
          | match goal with H : getr ?rs ?i = zw _ |- getr ?rs ?i = zw _ => rewrite H; f_equal; lia end ]
  end.
Local Ltac mlia := Z.to_euclidean_division_equations; lia.
Local Ltac brc :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia; rewrite ?szwrap32_small by lia;
  rewrite ?Z.mod_small by lia; lia.
Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.
Local Ltac via1 Ha H :=
  lazymatch type of H with getr _ ?r = _ => rewrite (Ha r eq_refl); exact H end.
Local Ltac clear_layout :=
  clear Hzin Hzain Hzout Hzaout Hzst Hsc Hcodes Hcodes_b Hwin Hwin_b Hinp Hinp_b Hout Hout_b Hrod
        Hd_spZ Hd_spS Hd_spI Hd_spP Hd_spW Hd_PZ Hd_PS Hd_PI Hd_PW Hd_ZS Hd_ZI Hd_ZW Hd_SI Hd_SW
        Hmap_sp Hmap_P Hmap_Z Hmap_S.



Local Ltac frs Hr := first [ reflexivity | eapply reg_in_sub; [| exact Hr]; reflexivity ].
Local Ltac fr_chain2 Hfr2 Hfr1 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite (Hfr2 r), (Hfr1 r); frs Hr.
Local Ltac fr_chain3 Hfr3 Hfr2 Hfr1 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite (Hfr3 r), (Hfr2 r), (Hfr1 r); frs Hr.
Local Ltac kr_destr HK := destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).

Definition wtrip_stmt (hd ex : word) : Prop :=
  forall SV m ob w i k regs,
    KR regs -> MEMI SV m ob ->
    getr regs 1 = zw (WB + w) -> getr regs 25 = zw k -> getr regs 14 = zw (P0 + i) ->
    1 <= k < 2 ^ 17 -> 0 <= w < WN -> 0 <= i < ON ->
    exists R, msteps s6_segs (mkst regs hd m s6_rom)
                (mkst R (if k =? 1 then ex else hd) (wbytes m (zw (P0 + i)) (Z_to_le_bytes 1 (arr_get (is_window s) w))) s6_rom)
     /\ KR R /\ getr R 1 = zw (WB + w + 1) /\ getr R 25 = zw (k - 1) /\ getr R 14 = zw (P0 + i + 1)
     /\ (forall q, reg_in q [1; 14; 21; 25]%bv = false -> getr R q = getr regs q).

Local Ltac wtrip_tac R HR Hfr Hms :=
  let HK' := fresh "HK'" in
  intros SV m ob w i k regs HK HM H1 H25 H14 Hk Hw Hi;
  pose proof (MEMI_win C SV m ob HM) as Hwin_m; pose proof (ifp_win_b C) as Hwb;
  pose proof (MEMI_map_P SV m ob HM) as WP; pose proof (ifp_d_PW C) as HdPW;
  destruct (Hwb w ltac:(lia)) as [Hv0 Hv1];
  pose proof HK as HK'; kr_destr HK; clear_layout;
  destruct (Z.eqb_spec k 1) as [K1|K1];
  [ lazymatch goal with |- exists R, msteps _ ?st _ /\ _ =>
      symex s6_segs cfg5 8%nat [false] [RVal (EVar 36%nat)]
        [(1, EAdd (EVar 32%nat) (EVar 33%nat)); (25, EVar 35%nat); (14, EAdd (EVar 34%nat) (EVar 37%nat))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^17); (36%nat, 256); (37%nat, 2^32)] NoRegions
        [WB; w; P0; k; arr_get (is_window s) w; i] NoVals F0 F0' st R HR Hfr Hms end
  | lazymatch goal with |- exists R, msteps _ ?st _ /\ _ =>
      symex s6_segs cfg5 8%nat [true] [RVal (EVar 36%nat)]
        [(1, EAdd (EVar 32%nat) (EVar 33%nat)); (25, EVar 35%nat); (14, EAdd (EVar 34%nat) (EVar 37%nat))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^17); (36%nat, 256); (37%nat, 2^32)] NoRegions
        [WB; w; P0; k; arr_get (is_window s) w; i] NoVals F0 F0' st R HR Hfr Hms end ];
  try side;
  lazymatch goal with
  | |- exists R, _ =>
      exists R; split; [exact Hms|];
      split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|];
      let A := fresh "A" in
      split; [symex_reg HR (1%bv : reg) as A; rewrite A; f_equal; lia|];
      split; [symex_reg HR (25%bv : reg) as A; rewrite A; f_equal; rewrite ?szwrap32_small by lia; lia|];
      split; [symex_reg HR (14%bv : reg) as A; rewrite A; f_equal; lia|];
      fr_weak Hfr
  | |- _ => try brc
  end.

Lemma wtrip_1fa84 : wtrip_stmt (0x1fbbc : word) (0x1fbd4 : word).
Proof. unfold wtrip_stmt. wtrip_tac R HR Hfr Hms. Qed.
Lemma wtrip_1fb44 : wtrip_stmt (0x1fc7c : word) (0x1fc94 : word).
Proof. unfold wtrip_stmt. wtrip_tac R HR Hfr Hms. Qed.
Lemma wtrip_1fb80 : wtrip_stmt (0x1fcb8 : word) (0x1fcd0 : word).
Proof. unfold wtrip_stmt. wtrip_tac R HR Hfr Hms. Qed.

Lemma wleg_loop : forall hd ex, wtrip_stmt hd ex -> forall k SV m ob w i regs,
  KR regs -> MEMI SV m ob ->
  getr regs 1 = zw (WB + w) -> getr regs 25 = zw (Z.of_nat k) -> getr regs 14 = zw (P0 + i) ->
  (1 <= k)%nat -> Z.of_nat k < 2 ^ 17 -> 0 <= w -> w + Z.of_nat k <= WN -> 0 <= i -> i + Z.of_nat k <= ON ->
  exists R m', msteps s6_segs (mkst regs hd m s6_rom) (mkst R ex m' s6_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FWin w) ob i k)
   /\ getr R 14 = zw (P0 + (i + Z.of_nat k)) /\ getr R 1 = zw (WB + w + Z.of_nat k)
   /\ (forall q, reg_in q [1; 14; 21; 25]%bv = false -> getr R q = getr regs q).
Proof.
  intros hd ex TRIP. induction k as [|k IH]; intros SV m ob w i regs HK HM H1 H25 H14 Hk Hk17 Hw Hwk Hi Hik; [lia|].
  pose proof (ifp_win_b C) as Hwb. destruct (Hwb w ltac:(lia)) as [Hv0 Hv1].
  destruct (TRIP SV m ob w i (Z.of_nat (Datatypes.S k)) regs HK HM H1 H25 H14 ltac:(lia) ltac:(lia) ltac:(lia)) as (R1 & Hms1 & HK1 & A1 & A25 & A14 & Hfr1).
  pose proof (MEMI_cp1 C SV m ob i (arr_get (is_window s) w) HM ltac:(lia) ltac:(lia)) as HM1.
  destruct k as [|k'].
  - replace (Z.of_nat 1 =? 1) with true in Hms1 by reflexivity.
    exists R1. eexists. split; [exact Hms1|]. split; [exact HK1|].
    split; [cbn [cblit fval from_succ]; exact HM1|].
    split; [rewrite A14; f_equal; lia|]. split; [rewrite A1; f_equal; lia|]. exact Hfr1.
  - replace (Z.of_nat (Datatypes.S (Datatypes.S k')) =? 1) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    destruct (IH SV _ _ (w + 1) (i + 1) R1 HK1 HM1 ltac:(rewrite A1; f_equal; lia) ltac:(rewrite A25; f_equal; lia) ltac:(rewrite A14; f_equal; lia)
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R2 & m2 & Hms2 & HK2 & HM2 & B14 & B1 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|]. split; [cbn [cblit fval from_succ]; exact HM2|].
    split; [rewrite B14; f_equal; lia|]. split; [rewrite B1; f_equal; lia|]. fr_chain2 Hfr2 Hfr1.
Qed.

Lemma wleg_of_loop : forall hd ex, wtrip_stmt hd ex ->
  wleg_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) hd ex.
Proof.
  intros hd ex TRIP SV m f n wi regs HK HM Hfr H1 H25 H14 Hn Hn17 Hwi HwiN Hbeg HoN. cbv zeta.
  pose proof (proj1 (ffx_beg_range C)) as Hxbeg0'.
  destruct (wleg_loop hd ex TRIP n SV m (f_ob f) wi (f_out f) regs HK HM H1 H25 H14 Hn Hn17 Hwi HwiN ltac:(lia) HoN)
    as (R & m' & Hms & HK' & HM' & A14 & A1 & Hfr').
  exists R, m'. split; [exact Hms|]. split; [exact HK'|].
  split; [rewrite cpn_ob, Hfr; exact HM'|]. split; [rewrite cpn_out; exact A14|]. split; [exact A1| exact Hfr'].
Qed.

Lemma wleg_1fa84 : wleg_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) (0x1fbbc : word) (0x1fbd4 : word).
Proof. exact (wleg_of_loop _ _ wtrip_1fa84). Qed.
Lemma wleg_1fb44 : wleg_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) (0x1fc7c : word) (0x1fc94 : word).
Proof. exact (wleg_of_loop _ _ wtrip_1fb44). Qed.
Lemma wleg_1fb80 : wleg_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) (0x1fcb8 : word) (0x1fcd0 : word).
Proof. exact (wleg_of_loop _ _ wtrip_1fb80). Qed.

Lemma x24_end : forall regs, KR regs -> 1 <= x_wnext X -> getr regs 24 = zw (WB + x_wnext X).
Proof.
  intros regs HK Hw. kr_destr HK. rewrite K24. f_equal. pose proof Hwnext1 as B. change (is_wnext s) with (x_wnext X) in B.
  rewrite wrap32_eqmod, Z.mod_small; lia.
Qed.

Lemma wtrip2 : forall SV m ob w i regs,
  KR regs -> MEMI SV m ob ->
  getr regs 7 = zw (WB + w) -> getr regs 14 = zw (P0 + i) ->
  0 <= w < x_wnext X -> x_wnext X <= WN -> 0 <= i < ON ->
  exists R, msteps s6_segs (mkst regs (0x1fbe0 : word) m s6_rom)
              (mkst R (if w + 1 =? x_wnext X then (0x1fbf8 : word) else (0x1fbe0 : word))
                    (wbytes m (zw (P0 + i)) (Z_to_le_bytes 1 (arr_get (is_window s) w))) s6_rom)
   /\ KR R /\ getr R 7 = zw (WB + w + 1) /\ getr R 14 = zw (P0 + i + 1)
   /\ (forall q, reg_in q [7; 14; 21; 25]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob w i regs HK HM H7 H14 Hw HwN Hi.
  pose proof (MEMI_win C SV m ob HM) as Hwin_m. pose proof (ifp_win_b C) as Hwb.
  pose proof (MEMI_map_P SV m ob HM) as WP. pose proof (ifp_d_PW C) as HdPW.
  destruct (Hwb w ltac:(lia)) as [Hv0 Hv1]. pose proof (x24_end regs HK ltac:(lia)) as H24.
  assert (HwnB : x_wnext X < 2 ^ 31) by (pose proof Hwnext1 as B; change (is_wnext s) with (x_wnext X) in B; exact B).
  pose proof HK as HK'. kr_destr HK. clear_layout. clear K24.
  destruct (Z.eqb_spec (w + 1) (x_wnext X)) as [E1|E1].
  - symex s6_segs cfg5 8%nat [false] [RVal (EVar 36%nat)]
      [(7, EAdd (EVar 32%nat) (EVar 33%nat)); (14, EAdd (EVar 34%nat) (EVar 37%nat)); (24, EAdd (EVar 32%nat) (EVar 35%nat))]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^31); (36%nat, 256); (37%nat, 2^32)] NoRegions
      [WB; w; P0; x_wnext X; arr_get (is_window s) w; i] NoVals F0 F0' (mkst regs (0x1fbe0 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (7%bv : reg) as A; rewrite A; f_equal; lia|].
    split; [symex_reg HR (14%bv : reg) as A'; rewrite A'; f_equal; lia| fr_weak Hfr].
  - symex s6_segs cfg5 8%nat [true] [RVal (EVar 36%nat)]
      [(7, EAdd (EVar 32%nat) (EVar 33%nat)); (14, EAdd (EVar 34%nat) (EVar 37%nat)); (24, EAdd (EVar 32%nat) (EVar 35%nat))]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^31); (36%nat, 256); (37%nat, 2^32)] NoRegions
      [WB; w; P0; x_wnext X; arr_get (is_window s) w; i] NoVals F0 F0' (mkst regs (0x1fbe0 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (7%bv : reg) as A; rewrite A; f_equal; lia|].
    split; [symex_reg HR (14%bv : reg) as A'; rewrite A'; f_equal; lia| fr_weak Hfr].
Qed.

Lemma wleg2_loop : forall k SV m ob w i regs,
  KR regs -> MEMI SV m ob ->
  getr regs 7 = zw (WB + w) -> getr regs 14 = zw (P0 + i) ->
  (1 <= k)%nat -> 0 <= w -> w + Z.of_nat k = x_wnext X -> x_wnext X <= WN -> 0 <= i -> i + Z.of_nat k <= ON ->
  exists R m', msteps s6_segs (mkst regs (0x1fbe0 : word) m s6_rom) (mkst R (0x1fbf8 : word) m' s6_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FWin w) ob i k)
   /\ getr R 14 = zw (P0 + (i + Z.of_nat k))
   /\ (forall q, reg_in q [7; 14; 21; 25]%bv = false -> getr R q = getr regs q).
Proof.
  induction k as [|k IH]; intros SV m ob w i regs HK HM H7 H14 Hk Hw Hwk HwN Hi Hik; [lia|].
  pose proof (ifp_win_b C) as Hwb. destruct (Hwb w ltac:(lia)) as [Hv0 Hv1].
  destruct (wtrip2 SV m ob w i regs HK HM H7 H14 ltac:(lia) HwN ltac:(lia)) as (R1 & Hms1 & HK1 & A7 & A14 & Hfr1).
  pose proof (MEMI_cp1 C SV m ob i (arr_get (is_window s) w) HM ltac:(lia) ltac:(lia)) as HM1.
  destruct k as [|k'].
  - replace (w + 1 =? x_wnext X) with true in Hms1 by (symmetry; apply Z.eqb_eq; lia).
    exists R1. eexists. split; [exact Hms1|]. split; [exact HK1|].
    split; [cbn [cblit fval from_succ]; exact HM1|].
    split; [rewrite A14; f_equal; lia| exact Hfr1].
  - replace (w + 1 =? x_wnext X) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    destruct (IH SV _ _ (w + 1) (i + 1) R1 HK1 HM1 ltac:(rewrite A7; f_equal; lia) ltac:(rewrite A14; f_equal; lia)
                 ltac:(lia) ltac:(lia) ltac:(lia) HwN ltac:(lia) ltac:(lia)) as (R2 & m2 & Hms2 & HK2 & HM2 & B14 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|]. split; [cbn [cblit fval from_succ]; exact HM2|].
    split; [rewrite B14; f_equal; lia|]. fr_chain2 Hfr2 Hfr1.
Qed.

Lemma wleg2 : wleg2_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof.
  intros SV m f regs HK HM Hfr H7 H14 Hw1 HwN Hbeg HoN. cbv zeta.
  pose proof (proj1 (ffx_beg_range C)) as Hxbeg0'.
  destruct (wleg2_loop (Z.to_nat (x_wnext X)) SV m (f_ob f) 0 (f_out f) regs HK HM ltac:(rewrite Z.add_0_r; exact H7) H14
              ltac:(lia) ltac:(lia) ltac:(lia) HwN ltac:(lia) ltac:(lia)) as (R & m' & Hms & HK' & HM' & A14 & Hfr').
  exists R, m'. split; [exact Hms|]. split; [exact HK'|].
  split; [rewrite cpn_ob, Hfr; exact HM'|]. split; [rewrite cpn_out, A14; f_equal; lia| exact Hfr'].
Qed.

Lemma srcn_src_ok : forall fout fr n k, srcn_ok WN fout fr n -> 0 <= Z.of_nat k < n ->
  src_ok WN (fout + Z.of_nat k) (fr_add fr k).
Proof. intros fout [i|i] n k H Hk; cbn in H; [rewrite fr_add_win | rewrite fr_add_out]; cbn; lia. Qed.
Lemma srcn_ok_adv : forall fout fr n k, srcn_ok WN fout fr n -> Z.of_nat k <= n ->
  srcn_ok WN (fout + Z.of_nat k) (fr_add fr k) (n - Z.of_nat k).
Proof. intros fout [i|i] n k H Hk; cbn in H; [rewrite fr_add_win | rewrite fr_add_out]; cbn; lia. Qed.
Lemma srcn_ok_le : forall fout fr n n', srcn_ok WN fout fr n -> n' <= n -> srcn_ok WN fout fr n'.
Proof. intros fout [i|i] n n' H Hn; cbn in *; lia. Qed.

Lemma w3_trip : forall SV m ob fr fout len regs,
  KR regs -> MEMI SV m ob ->
  getr regs 1 = zw (faddr WB P0 fr) -> getr regs 14 = zw (P0 + fout) -> getr regs 26 = zw len ->
  3 <= len < 2 ^ 17 -> 0 <= fout -> fout + 3 <= ON -> srcn_ok WN fout fr 3 ->
  let ob' := cblit (is_window s) fr ob fout 3 in
  exists R m', msteps s6_segs (mkst regs (0x1fce0 : word) m s6_rom)
                 (mkst R (if 2 <? len - 3 then (0x1fce0 : word) else (0x1fd10 : word)) m' s6_rom)
   /\ KR R /\ MEMI SV m' ob'
   /\ getr R 1 = zw (faddr WB P0 (fr_add fr 3)) /\ getr R 25 = zw (faddr WB P0 (fr_add fr 3))
   /\ getr R 14 = zw (P0 + (fout + 3)) /\ getr R 7 = zw (P0 + (fout + 3)) /\ getr R 26 = zw (len - 3)
   /\ (forall q, reg_in q [1; 7; 14; 21; 25; 26]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob fr fout len regs HK HM H1 H14 H26 Hlen Hfout Hfout3 Hsrc ob'.
  pose proof HK as HK'. kr_destr HK. clear_layout.
  pose proof (srcn_src_ok fout fr 3 0 Hsrc ltac:(lia)) as S0. cbn [fr_add Z.of_nat] in S0. rewrite Z.add_0_r in S0.
  pose proof (faddr_range C fout fr S0 ltac:(lia)) as [Fa0 Fa1].
  pose proof (faddr_disj C fout fr S0 ltac:(lia)) as Fd.
  pose proof (fval_byte C SV m ob fout fr HM S0 ltac:(lia)) as [Fv0 Fv1].
  pose proof (src_read C SV m ob fout fr _ HM S0 ltac:(lia) eq_refl) as RD0.
  pose proof (MEMI_map_P SV m ob HM) as WP.
  symex s6_segs cfg5 2%nat NoDirs [RVal (EVar 35%nat)]
    [(1, EVar 32%nat); (14, EAdd (EVar 33%nat) (EVar 34%nat))]
    [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
    [faddr WB P0 fr; P0; fout; fval (is_window s) ob fr] NoVals F0 F0'
    (mkst regs (0x1fce0 : word) m s6_rom) R1 HR1 Hfr1 Hms1.
  all: try side.
  pose proof (MEMI_cp1 C SV m ob fout _ HM ltac:(lia) (conj Fv0 Fv1)) as HM1.
  clear WP RD0 Fd.
  set (m1 := wbytes m _ _) in Hms1, HM1. set (ob1 := arr_set ob fout _) in HM1.
  assert (A1 : getr R1 1 = zw (faddr WB P0 fr)) by (rewrite (Hfr1 1%bv eq_refl); exact H1).
  assert (A14 : getr R1 14 = zw (P0 + fout)) by (rewrite (Hfr1 14%bv eq_refl); exact H14).
  pose proof (srcn_src_ok fout fr 3 1 Hsrc ltac:(lia)) as S1. cbn [fr_add Z.of_nat] in S1. change (Z.of_nat 1) with 1 in S1.
  pose proof (faddr_disj C (fout + 1) (from_succ fr) S1 ltac:(lia)) as Fd. rewrite faddr_succ in Fd.
  pose proof (fval_byte C SV m1 ob1 (fout + 1) (from_succ fr) HM1 S1 ltac:(lia)) as [Fv10 Fv11].
  pose proof (src_read C SV m1 ob1 (fout + 1) (from_succ fr) (faddr WB P0 fr + 1) HM1 S1 ltac:(lia) ltac:(rewrite faddr_succ; reflexivity)) as RD1.
  pose proof (MEMI_map_P SV m1 ob1 HM1) as WP.
  symex s6_segs cfg5 2%nat NoDirs [RVal (EVar 35%nat)]
    [(1, EVar 32%nat); (14, EAdd (EVar 33%nat) (EVar 34%nat))]
    [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
    [faddr WB P0 fr; P0; fout; fval (is_window s) ob1 (from_succ fr)] NoVals F0 F0'
    (mkst R1 (0x1fce8 : word) m1 s6_rom) R2 HR2 Hfr2 Hms2.
  all: try side.
  pose proof (MEMI_cp1 C SV m1 ob1 (fout + 1) _ HM1 ltac:(lia) (conj Fv10 Fv11)) as HM2.
  clear WP RD1 Fd.
  replace (P0 + fout + 1) with (P0 + (fout + 1)) in Hms2 by lia.
  set (m2 := wbytes m1 _ _) in Hms2, HM2. set (ob2 := arr_set ob1 (fout + 1) _) in HM2.
  assert (B1 : getr R2 1 = zw (faddr WB P0 fr)) by (rewrite (Hfr2 1%bv eq_refl); exact A1).
  assert (B14 : getr R2 14 = zw (P0 + fout)) by (rewrite (Hfr2 14%bv eq_refl); exact A14).
  assert (B26 : getr R2 26 = zw len) by (rewrite (Hfr2 26%bv eq_refl), (Hfr1 26%bv eq_refl); exact H26).
  assert (B28 : getr R2 28 = zw 2) by (rewrite (Hfr2 28%bv eq_refl), (Hfr1 28%bv eq_refl); exact K28).
  pose proof (srcn_src_ok fout fr 3 2 Hsrc ltac:(lia)) as S2. cbn [fr_add Z.of_nat] in S2. change (Z.of_nat 2) with 2 in S2.
  pose proof (faddr_disj C (fout + 2) (from_succ (from_succ fr)) S2 ltac:(lia)) as Fd. rewrite !faddr_succ in Fd.
  pose proof (fval_byte C SV m2 ob2 (fout + 2) (from_succ (from_succ fr)) HM2 S2 ltac:(lia)) as [Fv20 Fv21].
  pose proof (src_read C SV m2 ob2 (fout + 2) (from_succ (from_succ fr)) (faddr WB P0 fr + 2) HM2 S2 ltac:(lia) ltac:(rewrite !faddr_succ; lia)) as RD2.
  pose proof (MEMI_map_P SV m2 ob2 HM2) as WP.
  assert (Eob : ob' = arr_set ob2 (fout + 2) (fval (is_window s) ob2 (from_succ (from_succ fr)))).
  { subst ob' ob2 ob1. cbn [cblit]. f_equal. lia. }
  rewrite Eob. clear Eob.
  destruct (Z.ltb_spec 2 (len - 3)) as [Hc|Hc].
  - symex s6_segs cfg5 8%nat [true] [RVal (EVar 35%nat)]
      [(1, EVar 32%nat); (14, EAdd (EVar 33%nat) (EVar 34%nat)); (26, EVar 36%nat); (28, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256); (36%nat, 2^17)] NoRegions
      [faddr WB P0 fr; P0; fout; fval (is_window s) ob2 (from_succ (from_succ fr)); len] NoVals F0 F0'
      (mkst R2 (0x1fcf0 : word) m2 s6_rom) R3 HR3 Hfr3 Hms3.
    all: try side. all: try brc.
    pose proof (MEMI_cp1 C SV m2 ob2 (fout + 2) _ HM2 ltac:(lia) (conj Fv20 Fv21)) as HM3.
    replace (P0 + fout + 2) with (P0 + (fout + 2)) in Hms3 by lia.
    assert (HF : forall q, reg_in q [1; 7; 14; 21; 25; 26]%bv = false -> getr R3 q = getr regs q) by fr_chain3 Hfr3 Hfr2 Hfr1.
    exists R3. eexists. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [exact HM3|].
    symex_reg HR3 (1%bv : reg) as C1. symex_reg HR3 (25%bv : reg) as C25. symex_reg HR3 (14%bv : reg) as C14.
    symex_reg HR3 (7%bv : reg) as C7. symex_reg HR3 (26%bv : reg) as C26.
    split; [rewrite C1; f_equal; rewrite faddr_add; cbn; lia|]. split; [rewrite C25; f_equal; rewrite faddr_add; cbn; lia|].
    split; [rewrite C14; f_equal; lia|]. split; [rewrite C7; f_equal; lia|].
    split; [rewrite C26; f_equal; rewrite ?szwrap32_small by lia; lia|]. exact HF.
  - symex s6_segs cfg5 8%nat [false] [RVal (EVar 35%nat)]
      [(1, EVar 32%nat); (14, EAdd (EVar 33%nat) (EVar 34%nat)); (26, EVar 36%nat); (28, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256); (36%nat, 2^17)] NoRegions
      [faddr WB P0 fr; P0; fout; fval (is_window s) ob2 (from_succ (from_succ fr)); len] NoVals F0 F0'
      (mkst R2 (0x1fcf0 : word) m2 s6_rom) R3 HR3 Hfr3 Hms3.
    all: try side. all: try brc.
    pose proof (MEMI_cp1 C SV m2 ob2 (fout + 2) _ HM2 ltac:(lia) (conj Fv20 Fv21)) as HM3.
    replace (P0 + fout + 2) with (P0 + (fout + 2)) in Hms3 by lia.
    assert (HF : forall q, reg_in q [1; 7; 14; 21; 25; 26]%bv = false -> getr R3 q = getr regs q) by fr_chain3 Hfr3 Hfr2 Hfr1.
    exists R3. eexists. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [exact HM3|].
    symex_reg HR3 (1%bv : reg) as C1. symex_reg HR3 (25%bv : reg) as C25. symex_reg HR3 (14%bv : reg) as C14.
    symex_reg HR3 (7%bv : reg) as C7. symex_reg HR3 (26%bv : reg) as C26.
    split; [rewrite C1; f_equal; rewrite faddr_add; cbn; lia|]. split; [rewrite C25; f_equal; rewrite faddr_add; cbn; lia|].
    split; [rewrite C14; f_equal; lia|]. split; [rewrite C7; f_equal; lia|].
    split; [rewrite C26; f_equal; rewrite ?szwrap32_small by lia; lia|]. exact HF.
Qed.

Lemma w3_loop : forall k SV m ob fr fout rem regs,
  KR regs -> MEMI SV m ob ->
  getr regs 1 = zw (faddr WB P0 fr) -> getr regs 14 = zw (P0 + fout) -> getr regs 26 = zw (3 * Z.of_nat k + rem) ->
  (1 <= k)%nat -> 0 <= rem <= 2 -> 3 * Z.of_nat k + rem < 2 ^ 17 -> 0 <= fout -> fout + 3 * Z.of_nat k <= ON ->
  srcn_ok WN fout fr (3 * Z.of_nat k) ->
  exists R m', msteps s6_segs (mkst regs (0x1fce0 : word) m s6_rom) (mkst R (0x1fd10 : word) m' s6_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) fr ob fout (3 * k))
   /\ getr R 1 = zw (faddr WB P0 (fr_add fr (3 * k))) /\ getr R 25 = zw (faddr WB P0 (fr_add fr (3 * k)))
   /\ getr R 14 = zw (P0 + (fout + 3 * Z.of_nat k)) /\ getr R 7 = zw (P0 + (fout + 3 * Z.of_nat k)) /\ getr R 26 = zw rem
   /\ (forall q, reg_in q [1; 7; 14; 21; 25; 26]%bv = false -> getr R q = getr regs q).
Proof.
  induction k as [|k IH]; intros SV m ob fr fout rem regs HK HM H1 H14 H26 Hk Hrem Hlen Hfout HfoutN Hsrc; [lia|].
  assert (Hs3 : srcn_ok WN fout fr 3) by (destruct fr; cbn in Hsrc |- *; lia).
  destruct (w3_trip SV m ob fr fout (3 * Z.of_nat (Datatypes.S k) + rem) regs HK HM H1 H14 H26 ltac:(lia) Hfout ltac:(lia) Hs3)
    as (R1 & m1 & Hms1 & HK1 & HM1 & A1 & A25 & A14 & A7 & A26 & Hfr1).
  destruct k as [|k'].
  -
    replace (2 <? 3 * Z.of_nat 1 + rem - 3) with false in Hms1 by (symmetry; apply Z.ltb_ge; lia).
    exists R1, m1. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HM1|].
    split; [exact A1|]. split; [exact A25|]. split; [rewrite A14; f_equal; lia|]. split; [rewrite A7; f_equal; lia|].
    split; [rewrite A26; f_equal; lia| exact Hfr1].
  - replace (2 <? 3 * Z.of_nat (Datatypes.S (Datatypes.S k')) + rem - 3) with true in Hms1 by (symmetry; apply Z.ltb_lt; lia).
    destruct (IH SV m1 (cblit (is_window s) fr ob fout 3) (fr_add fr 3) (fout + 3) rem R1 HK1 HM1
                 A1 A14 ltac:(rewrite A26; f_equal; lia) ltac:(lia) Hrem ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & m2 & Hms2 & HK2 & HM2 & B1 & B25 & B14 & B7 & B26 & Hfr2).
    { pose proof (srcn_ok_adv fout fr (3 * Z.of_nat (Datatypes.S (Datatypes.S k'))) 3 Hsrc ltac:(lia)) as H.
      replace (3 * Z.of_nat (Datatypes.S (Datatypes.S k')) - Z.of_nat 3) with (3 * Z.of_nat (Datatypes.S k')) in H by lia.
      replace (fout + Z.of_nat 3) with (fout + 3) in H by lia. exact H. }
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|].
    split; [replace (3 * Datatypes.S (Datatypes.S k'))%nat with (3 + 3 * Datatypes.S k')%nat by lia; rewrite cblit_add;
            replace (fout + Z.of_nat 3) with (fout + 3) by lia; exact HM2|].
    assert (EFR : fr_add fr (3 * Datatypes.S (Datatypes.S k')) = fr_add (fr_add fr 3) (3 * Datatypes.S k')).
    { replace (3 * Datatypes.S (Datatypes.S k'))%nat with (3 + 3 * Datatypes.S k')%nat by lia. apply fr_add_add. }
    rewrite EFR. split; [exact B1|]. split; [exact B25|].
    split; [rewrite B14; f_equal; lia|]. split; [rewrite B7; f_equal; lia|]. split; [exact B26|].
    fr_chain2 Hfr2 Hfr1.
Qed.

Lemma w3_tdc : forall SV m ob fr fout rem regs,
  KR regs -> MEMI SV m ob ->
  getr regs 25 = zw (faddr WB P0 fr) -> getr regs 7 = zw (P0 + fout) -> getr regs 26 = zw rem ->
  1 <= rem <= 2 -> 0 <= fout -> fout + rem <= ON -> srcn_ok WN fout fr rem ->
  exists R m', msteps s6_segs (mkst regs (0x1fd14 : word) m s6_rom) (mkst R (0x1fa48 : word) m' s6_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) fr ob fout (Z.to_nat rem))
   /\ getr R 14 = zw (P0 + (fout + rem))
   /\ (forall q, reg_in q [14; 21]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob fr fout rem regs HK HM H25 H7 H26 Hrem Hfout HfoutN Hsrc.
  pose proof HK as HK'. kr_destr HK. clear_layout.
  pose proof (srcn_src_ok fout fr rem 0 Hsrc ltac:(lia)) as S0. cbn [fr_add Z.of_nat] in S0. rewrite Z.add_0_r in S0.
  pose proof (faddr_range C fout fr S0 ltac:(lia)) as [Fa0 Fa1].
  pose proof (faddr_disj C fout fr S0 ltac:(lia)) as Fd.
  pose proof (fval_byte C SV m ob fout fr HM S0 ltac:(lia)) as [Fv0 Fv1].
  pose proof (src_read C SV m ob fout fr _ HM S0 ltac:(lia) eq_refl) as RD0.
  pose proof (MEMI_map_P SV m ob HM) as WP.
  destruct (Z.eq_dec rem 1) as [R1E|R2E].
  -
    subst rem.
    symex s6_segs cfg5 6%nat [true] [RVal (EVar 35%nat)]
      [(25, EVar 32%nat); (7, EAdd (EVar 33%nat) (EVar 34%nat)); (26, ELit 1); (28, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
      [faddr WB P0 fr; P0; fout; fval (is_window s) ob fr] NoVals F0 F0'
      (mkst regs (0x1fd14 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. eexists. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [cbn [Z.to_nat Pos.to_nat cblit]; apply (MEMI_cp1 C); [exact HM | lia | lia]|].
    split; [symex_reg HR (14%bv : reg) as A; rewrite A; f_equal; lia| fr_weak Hfr].
  -
    assert (R2 : rem = 2) by lia. subst rem.
    symex s6_segs cfg5 3%nat [false] [RVal (EVar 35%nat)]
      [(25, EVar 32%nat); (7, EAdd (EVar 33%nat) (EVar 34%nat)); (26, ELit 2); (28, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
      [faddr WB P0 fr; P0; fout; fval (is_window s) ob fr] NoVals F0 F0'
      (mkst regs (0x1fd14 : word) m s6_rom) R1 HR1 Hfr1 Hms1.
    all: try side. all: try brc.
    pose proof (MEMI_cp1 C SV m ob fout _ HM ltac:(lia) (conj Fv0 Fv1)) as HM1.
    clear WP RD0 Fd.
    set (m1 := wbytes m _ _) in Hms1, HM1. set (ob1 := arr_set ob fout _) in HM1.
    assert (A25 : getr R1 25 = zw (faddr WB P0 fr)) by (rewrite (Hfr1 25%bv eq_refl); exact H25).
    assert (A7 : getr R1 7 = zw (P0 + fout)) by (rewrite (Hfr1 7%bv eq_refl); exact H7).
    pose proof (srcn_src_ok fout fr 2 1 Hsrc ltac:(lia)) as S1. cbn [fr_add Z.of_nat] in S1. change (Z.of_nat 1) with 1 in S1.
    pose proof (faddr_disj C (fout + 1) (from_succ fr) S1 ltac:(lia)) as Fd. rewrite faddr_succ in Fd.
    pose proof (fval_byte C SV m1 ob1 (fout + 1) (from_succ fr) HM1 S1 ltac:(lia)) as [Fv10 Fv11].
    pose proof (src_read C SV m1 ob1 (fout + 1) (from_succ fr) (faddr WB P0 fr + 1) HM1 S1 ltac:(lia) ltac:(rewrite faddr_succ; reflexivity)) as RD1.
    pose proof (MEMI_map_P SV m1 ob1 HM1) as WP.
    symex s6_segs cfg5 6%nat NoDirs [RVal (EVar 35%nat)]
      [(25, EVar 32%nat); (7, EAdd (EVar 33%nat) (EVar 34%nat))]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
      [faddr WB P0 fr; P0; fout; fval (is_window s) ob1 (from_succ fr)] NoVals F0 F0'
      (mkst R1 (0x1fd20 : word) m1 s6_rom) R2 HR2 Hfr2 Hms2.
    all: try side.
    pose proof (MEMI_cp1 C SV m1 ob1 (fout + 1) _ HM1 ltac:(lia) (conj Fv10 Fv11)) as HM2.
    replace (P0 + fout + 1) with (P0 + (fout + 1)) in Hms2 by lia.
    assert (HF : forall q, reg_in q [14; 21]%bv = false -> getr R2 q = getr regs q) by fr_chain2 Hfr2 Hfr1.
    exists R2. eexists. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [subst ob1; cbn [Z.to_nat Pos.to_nat cblit]; exact HM2|].
    split; [symex_reg HR2 (14%bv : reg) as A; rewrite A; f_equal; lia| exact HF].
Qed.

Lemma w3_td8_0 : forall m o regs,
  KR regs -> getr regs 26 = zw 0 -> getr regs 7 = zw o -> 0 <= o < 2 ^ 63 ->
  exists R, msteps s6_segs (mkst regs (0x1fd10 : word) m s6_rom) (mkst R (0x1fa48 : word) m s6_rom)
   /\ KR R /\ getr R 14 = zw o /\ (forall q, reg_in q [14]%bv = false -> getr R q = getr regs q).
Proof.
  intros m o regs HK H26 H7 Ho. pose proof HK as HK'. kr_destr HK. clear_layout.
  symex s6_segs cfg5 6%nat [true] NoReads [(26, ELit 0); (7, EVar 32%nat)] [(32%nat, 2^63)] NoRegions [o] NoVals F0 F0'
    (mkst regs (0x1fd10 : word) m s6_rom) R HR Hfr Hms.
  all: try side. all: try brc.
  exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
  split; [symex_reg HR (14%bv : reg) as A; rewrite A; reflexivity| fr_weak Hfr].
Qed.
Lemma w3_td8_nz : forall m rem regs,
  KR regs -> getr regs 26 = zw rem -> 1 <= rem <= 2 ->
  exists R, msteps s6_segs (mkst regs (0x1fd10 : word) m s6_rom) (mkst R (0x1fd14 : word) m s6_rom)
   /\ KR R /\ (forall q, reg_in q (@nil reg) = false -> getr R q = getr regs q).
Proof.
  intros m rem regs HK H26 Hrem. pose proof HK as HK'. kr_destr HK. clear_layout.
  symex s6_segs cfg5 3%nat [false] NoReads [(26, EVar 32%nat)] [(32%nat, 3)] NoRegions [rem] NoVals F0 F0'
    (mkst regs (0x1fd10 : word) m s6_rom) R HR Hfr Hms.
  all: try side. all: try brc.
  exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity| fr_weak Hfr].
Qed.

Lemma w3_tc0c : forall m a o len regs,
  KR regs -> getr regs 1 = zw a -> getr regs 14 = zw o -> getr regs 26 = zw len -> 0 <= len <= 2 -> 0 <= a < 2 ^ 63 -> 0 <= o < 2 ^ 63 ->
  exists R, msteps s6_segs (mkst regs (0x1fd44 : word) m s6_rom)
              (mkst R (if len =? 0 then (0x1fa48 : word) else (0x1fd14 : word)) m s6_rom)
   /\ KR R /\ getr R 7 = zw o /\ getr R 25 = zw a /\ getr R 14 = zw o
   /\ (forall q, reg_in q [7; 14; 25]%bv = false -> getr R q = getr regs q).
Proof.
  intros m a o len regs HK H1 H14 H26 Hlen Ha Ho. pose proof HK as HK'. kr_destr HK. clear_layout.
  destruct (Z.eqb_spec len 0) as [L0|L0].
  - subst len.
    symex s6_segs cfg5 6%nat [false] NoReads [(1, EVar 32%nat); (14, EVar 33%nat); (26, ELit 0)] [(32%nat, 2^63); (33%nat, 2^63)] NoRegions [a; o] NoVals F0 F0'
      (mkst regs (0x1fd44 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (7%bv : reg) as A; rewrite A; reflexivity|]. split; [symex_reg HR (25%bv : reg) as A'; rewrite A'; reflexivity|].
    split; [symex_reg HR (14%bv : reg) as A''; rewrite A''; reflexivity| fr_weak Hfr].
  - symex s6_segs cfg5 6%nat [true] NoReads [(1, EVar 32%nat); (14, EVar 33%nat); (26, EVar 34%nat)] [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 3)] NoRegions [a; o; len] NoVals F0 F0'
      (mkst regs (0x1fd44 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (7%bv : reg) as A; rewrite A; reflexivity|]. split; [symex_reg HR (25%bv : reg) as A'; rewrite A'; reflexivity|].
    split; [symex_reg HR (14%bv : reg) as A''; rewrite A''; reflexivity| fr_weak Hfr].
Qed.

Lemma w3_head : forall m len regs,
  KR regs -> getr regs 26 = zw len -> 0 <= len < 2 ^ 17 ->
  exists R, msteps s6_segs (mkst regs (0x1fcd8 : word) m s6_rom)
              (mkst R (if len <? 3 then (0x1fd44 : word) else (0x1fce0 : word)) m s6_rom)
   /\ KR R /\ (forall q, reg_in q [7]%bv = false -> getr R q = getr regs q).
Proof.
  intros m len regs HK H26 Hlen. pose proof HK as HK'. kr_destr HK. clear_layout.
  destruct (Z.ltb_spec len 3) as [L3|L3].
  - symex s6_segs cfg5 4%nat [true] NoReads [(26, EVar 32%nat)] [(32%nat, 2^17)] NoRegions [len] NoVals F0 F0'
      (mkst regs (0x1fcd8 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity| fr_weak Hfr].
  - symex s6_segs cfg5 4%nat [false] NoReads [(26, EVar 32%nat)] [(32%nat, 2^17)] NoRegions [len] NoVals F0 F0'
      (mkst regs (0x1fcd8 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity| fr_weak Hfr].
Qed.
Lemma w3c_head : forall m len regs,
  KR regs -> getr regs 26 = zw len -> 0 <= len < 2 ^ 17 ->
  exists R, msteps s6_segs (mkst regs (0x1fd38 : word) m s6_rom)
              (mkst R (if len <? 3 then (0x1fd44 : word) else (0x1fce0 : word)) m s6_rom)
   /\ KR R /\ getr R 1 = zw WB /\ (forall q, reg_in q [1; 7]%bv = false -> getr R q = getr regs q).
Proof.
  intros m len regs HK H26 Hlen. pose proof HK as HK'. kr_destr HK. clear_layout.
  destruct (Z.ltb_spec len 3) as [L3|L3].
  - symex s6_segs cfg5 5%nat [false] NoReads [(26, EVar 32%nat); (8, EVar 33%nat)] [(32%nat, 2^17); (33%nat, 2^63)] NoRegions [len; WB] NoVals F0 F0'
      (mkst regs (0x1fd38 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (1%bv : reg) as A; rewrite A; reflexivity| fr_weak Hfr].
  - symex s6_segs cfg5 5%nat [true] NoReads [(26, EVar 32%nat); (8, EVar 33%nat)] [(32%nat, 2^17); (33%nat, 2^63)] NoRegions [len; WB] NoVals F0 F0'
      (mkst regs (0x1fd38 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (1%bv : reg) as A; rewrite A; reflexivity| fr_weak Hfr].
Qed.

Lemma fset_len_fields : forall g v,
  f_ob (fset_len g v) = f_ob g /\ f_from (fset_len g v) = f_from g /\ f_out (fset_len g v) = f_out g /\ f_len (fset_len g v) = v
  /\ f_in (fset_len g v) = f_in g /\ f_hold (fset_len g v) = f_hold g /\ f_bits (fset_len g v) = f_bits g /\ f_dist (fset_len g v) = f_dist g.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9] v; repeat split; reflexivity. Qed.

Lemma tail_sim : forall SV m f regs,
  KR regs -> MEMI SV m (f_ob f) ->
  getr regs 25 = zw (faddr WB P0 (f_from f)) -> getr regs 7 = zw (P0 + f_out f) -> getr regs 26 = zw (f_len f) ->
  1 <= f_len f <= 2 -> 0 <= f_out f -> f_out f + f_len f <= ON -> srcn_ok WN (f_out f) (f_from f) (f_len f) ->
  let f' := copy_tail X f in
  exists R m', msteps s6_segs (mkst regs (0x1fd14 : word) m s6_rom) (mkst R (0x1fa48 : word) m' s6_rom)
   /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 14 = zw (P0 + f_out f')
   /\ (forall q, reg_in q [14; 21]%bv = false -> getr R q = getr regs q)
   /\ f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_out f' = f_out f + f_len f /\ f_dist f' = f_dist f.
Proof.
  intros SV m f regs HK HM H25 H7 H26 Hlen Hfo Hfon Hsrc f'. subst f'. rewrite copy_tail_cpn by lia.
  destruct (w3_tdc SV m (f_ob f) (f_from f) (f_out f) (f_len f) regs HK HM H25 H7 H26 Hlen Hfo Hfon Hsrc)
    as (R & m' & Hms & HK' & HM' & A14 & Hfr).
  exists R, m'. split; [exact Hms|]. split; [exact HK'|].
  rewrite cpn_ob, cpn_in, cpn_hold, cpn_bits, cpn_out, cpn_dist. cbn [x_window ffx_of].
  split; [exact HM'|]. split; [rewrite A14; f_equal; lia|]. split; [exact Hfr|]. repeat split; lia.
Qed.

Lemma w3_core : forall SV m f regs,
  KR regs -> MEMI SV m (f_ob f) ->
  getr regs 1 = zw (faddr WB P0 (f_from f)) -> getr regs 14 = zw (P0 + f_out f) -> getr regs 26 = zw (f_len f) ->
  0 <= f_len f < 2 ^ 17 -> 0 <= f_out f -> f_out f + f_len f <= ON -> srcn_ok WN (f_out f) (f_from f) (f_len f) ->
  let f' := copy_tail X (copy_while3 X f) in
  exists R m', msteps s6_segs (mkst regs (if f_len f <? 3 then (0x1fd44 : word) else (0x1fce0 : word)) m s6_rom)
                      (mkst R (0x1fa48 : word) m' s6_rom)
   /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 14 = zw (P0 + f_out f')
   /\ (forall q, reg_in q [1; 7; 14; 21; 25; 26]%bv = false -> getr R q = getr regs q)
   /\ f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_out f' = f_out f + f_len f /\ f_dist f' = f_dist f.
Proof.
  intros SV m f regs HK HM H1 H14 H26 Hlen Hfo Hfon Hsrc f'. subst f'. rewrite copy_while3_cpn by lia.
  pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as Hm3.
  pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)) as Hq0.
  assert (S0 : f_len f >= 1 -> src_ok WN (f_out f) (f_from f)).
  { intros H. pose proof (srcn_src_ok (f_out f) (f_from f) (f_len f) 0 Hsrc ltac:(lia)) as X0. cbn [fr_add Z.of_nat] in X0. rewrite Z.add_0_r in X0. exact X0. }
  destruct (Z.ltb_spec (f_len f) 3) as [Hlt|Hge].
  -
    rewrite (Z.div_small (f_len f) 3), (Z.mod_small (f_len f) 3) by lia. cbn [Z.mul Z.to_nat cpn]. rewrite fset_len_id.
    assert (Fa : 0 <= faddr WB P0 (f_from f) < 2 ^ 63).
    { destruct (Z.eq_dec (f_len f) 0) as [Z0|Z0].
      - destruct (f_from f) as [i|i]; cbn in Hsrc |- *; lia.
      - pose proof (faddr_range C (f_out f) (f_from f) (S0 ltac:(lia)) ltac:(lia)). lia. }
    destruct (w3_tc0c m (faddr WB P0 (f_from f)) (P0 + f_out f) (f_len f) regs HK H1 H14 H26 ltac:(lia) Fa ltac:(lia))
      as (R1 & Hms1 & HK1 & A7 & A25 & A14 & Hfr1).
    destruct (Z.eqb_spec (f_len f) 0) as [L0|L0].
    + rewrite copy_tail_cpn by lia. rewrite L0. change (Z.to_nat 0) with 0%nat. cbn [cpn]. rewrite Z.add_0_r.
      exists R1, m. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HM|]. split; [exact A14|].
      split; [fr_weak Hfr1|]. repeat split; lia.
    + destruct (tail_sim SV m f R1 HK1 HM A25 A7 ltac:(rewrite (Hfr1 26%bv eq_refl); exact H26) ltac:(lia) Hfo Hfon Hsrc)
        as (R2 & m2 & Hms2 & HK2 & HM2 & B14 & Hfr2 & E).
      exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HK2|]. split; [exact HM2|].
      split; [exact B14|]. split; [fr_chain2 Hfr2 Hfr1 | exact E].
  - set (k := Z.to_nat (f_len f / 3)).
    assert (Hk : (1 <= k)%nat) by (subst k; assert (1 <= f_len f / 3) by (apply Z.div_le_lower_bound; lia); lia).
    assert (Hk3 : 3 * Z.of_nat k = 3 * (f_len f / 3)) by (subst k; lia).
    destruct (w3_loop k SV m (f_ob f) (f_from f) (f_out f) (f_len f mod 3) regs HK HM H1 H14
                ltac:(rewrite H26; f_equal; lia) Hk ltac:(lia) ltac:(lia) Hfo ltac:(lia) ltac:(apply (srcn_ok_le _ _ _ _ Hsrc); lia))
      as (R3 & m3 & Hms3 & HK3 & HM3 & C1 & C25 & C14 & C7 & C26 & Hfr3).
    set (f1 := fset_len (cpn X (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3)).
    assert (Ef1 : f_ob f1 = cblit (is_window s) (f_from f) (f_ob f) (f_out f) (3 * k) /\ f_from f1 = fr_add (f_from f) (3 * k)
                  /\ f_out f1 = f_out f + 3 * Z.of_nat k /\ f_len f1 = f_len f mod 3
                  /\ f_in f1 = f_in f /\ f_hold f1 = f_hold f /\ f_bits f1 = f_bits f /\ f_dist f1 = f_dist f).
    { subst f1. destruct (fset_len_fields (cpn X (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3)) as (-> & -> & -> & -> & -> & -> & -> & ->).
      rewrite cpn_ob, cpn_from, cpn_out, cpn_in, cpn_hold, cpn_bits, cpn_dist.
      replace (Z.to_nat (3 * (f_len f / 3))) with (3 * k)%nat by lia. cbn [x_window ffx_of]. repeat split; lia. }
    destruct Ef1 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (Z.eq_dec (f_len f mod 3) 0) as [M0|M0].
    +
      destruct (w3_td8_0 m3 (P0 + (f_out f + 3 * Z.of_nat k)) R3 HK3 ltac:(rewrite C26, M0; reflexivity) C7 ltac:(lia))
        as (R4 & Hms4 & HK4 & D14 & Hfr4).
      rewrite copy_tail_cpn by (rewrite E4; lia). rewrite E4, M0. change (Z.to_nat 0) with 0%nat. cbn [cpn].
      exists R4, m3. split; [eapply msteps_trans; [exact Hms3 | exact Hms4]|]. split; [exact HK4|].
      split; [rewrite E1; exact HM3|]. split; [rewrite D14, E3; reflexivity|].
      split; [fr_chain2 Hfr4 Hfr3|]. rewrite E5, E6, E7, E3, E8. repeat split; lia.
    + destruct (w3_td8_nz m3 (f_len f mod 3) R3 HK3 C26 ltac:(lia)) as (R4 & Hms4 & HK4 & Hfr4).
      destruct (tail_sim SV m3 f1 R4 HK4 ltac:(rewrite E1; exact HM3) ltac:(rewrite E2, (Hfr4 25%bv eq_refl); exact C25)
                  ltac:(rewrite E3, (Hfr4 7%bv eq_refl); exact C7) ltac:(rewrite E4, (Hfr4 26%bv eq_refl); exact C26)
                  ltac:(rewrite E4; lia) ltac:(lia) ltac:(rewrite E3, E4; lia)
                  ltac:(rewrite E3, E2, E4; replace (f_out f + 3 * Z.of_nat k) with (f_out f + Z.of_nat (3 * k)) by lia;
                        replace (f_len f mod 3) with (f_len f - Z.of_nat (3 * k)) by lia;
                        apply srcn_ok_adv; [exact Hsrc | lia]))
        as (R5 & m5 & Hms5 & HK5 & HM5 & D14 & Hfr5 & E).
      exists R5, m5. split.
      { eapply msteps_trans; [exact Hms3|]. eapply msteps_trans; [exact Hms4 | exact Hms5]. }
      split; [exact HK5|]. split; [exact HM5|]. split; [exact D14|].
      split; [fr_chain3 Hfr5 Hfr4 Hfr3|].
      rewrite E5, E6, E7, E3, E8, E4 in E. destruct E as (? & ? & ? & ? & ?). repeat split; try assumption. lia.
Qed.

Lemma w3 : w3_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof.
  intros SV m f regs HK HM H1 H14 H26 Hlen Hbeg Hfon Hsrc. cbv zeta.
  pose proof (proj1 (ffx_beg_range C)) as Hxbeg0'.
  destruct (w3_head m (f_len f) regs HK H26 Hlen) as (R1 & Hms1 & HK1 & Hfr1).
  destruct (w3_core SV m f R1 HK1 HM ltac:(rewrite (Hfr1 1%bv eq_refl); exact H1) ltac:(rewrite (Hfr1 14%bv eq_refl); exact H14)
              ltac:(rewrite (Hfr1 26%bv eq_refl); exact H26) Hlen ltac:(lia) Hfon Hsrc)
    as (R2 & m2 & Hms2 & HK2 & HM2 & A14 & Hfr2 & E).
  exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HK2|]. split; [exact HM2|].
  split; [exact A14|]. split; [fr_chain2 Hfr2 Hfr1 | exact E].
Qed.

Lemma w3c00 : w3c00_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof.
  intros SV m f regs HK HM Hfr0 H14 H26 Hlen Hbeg Hfon Hsrc. cbv zeta.
  pose proof (proj1 (ffx_beg_range C)) as Hxbeg0'.
  destruct (w3c_head m (f_len f) regs HK H26 Hlen) as (R1 & Hms1 & HK1 & A1 & Hfr1).
  destruct (w3_core SV m f R1 HK1 HM ltac:(rewrite A1, Hfr0; cbn [faddr]; rewrite Z.add_0_r; reflexivity)
              ltac:(rewrite (Hfr1 14%bv eq_refl); exact H14) ltac:(rewrite (Hfr1 26%bv eq_refl); exact H26) Hlen ltac:(lia) Hfon Hsrc)
    as (R2 & m2 & Hms2 & HK2 & HM2 & A14 & Hfr2 & E).
  exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HK2|]. split; [exact HM2|].
  split; [exact A14|]. split; [fr_chain2 Hfr2 Hfr1 | exact E].
Qed.

Lemma do3_trip : forall SV m ob dist fout len regs,
  KR regs -> MEMI SV m ob ->
  getr regs 14 = zw (P0 + fout + 2) -> getr regs 7 = zw (1 - dist) -> getr regs 26 = zw len ->
  3 <= len < 2 ^ 17 -> 1 <= dist < 2 ^ 17 -> dist <= fout -> fout + 3 <= ON ->
  let ob' := cblit (is_window s) (FOut (fout - dist)) ob fout 3 in
  exists R m', msteps s6_segs (mkst regs (0x1fc0c : word) m s6_rom)
                 (mkst R (if 2 <? len - 3 then (0x1fc0c : word) else (0x1fc34 : word)) m' s6_rom)
   /\ KR R /\ MEMI SV m' ob'
   /\ getr R 14 = zw (P0 + (fout + 3) + 2) /\ getr R 7 = zw (1 - dist) /\ getr R 26 = zw (len - 3)
   /\ (forall q, reg_in q [14; 21; 25; 26]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob dist fout len regs HK HM H14 H7 H26 Hlen Hdist Hdf Hfout3 ob'.
  pose proof HK as HK'. kr_destr HK. clear_layout.
  set (fr := FOut (fout - dist)) in ob'.
  assert (Hsrc : srcn_ok WN fout fr 3) by (subst fr; cbn; lia).
  pose proof (srcn_src_ok fout fr 3 0 Hsrc ltac:(lia)) as S0. cbn [fr_add Z.of_nat] in S0. rewrite Z.add_0_r in S0.
  pose proof (faddr_range C fout fr S0 ltac:(lia)) as [Fa0 Fa1].
  pose proof (faddr_disj C fout fr S0 ltac:(lia)) as Fd.
  pose proof (fval_byte C SV m ob fout fr HM S0 ltac:(lia)) as [Fv0 Fv1].
  pose proof (src_read C SV m ob fout fr (P0 + fout + (1 - dist) + -1) HM S0 ltac:(lia) ltac:(subst fr; cbn [faddr]; lia)) as RD0.
  pose proof (MEMI_map_P SV m ob HM) as WP.
  symex s6_segs cfg5 3%nat NoDirs [RVal (EVar 34%nat)]
    [(14, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (ELit 2)); (7, ESub (ELit 1) (EVar 35%nat))]
    [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 256); (35%nat, 2^17)] NoRegions
    [P0; fout; fval (is_window s) ob fr; dist] NoVals F0 F0'
    (mkst regs (0x1fc0c : word) m s6_rom) R1 HR1 Hfr1 Hms1.
  all: try side.
  pose proof (MEMI_cp1 C SV m ob fout _ HM ltac:(lia) (conj Fv0 Fv1)) as HM1.
  clear WP RD0 Fd.
  set (m1 := wbytes m _ _) in Hms1, HM1. set (ob1 := arr_set ob fout _) in HM1.
  assert (A14 : getr R1 14 = zw (P0 + fout + 2)) by (rewrite (Hfr1 14%bv eq_refl); exact H14).
  symex_reg HR1 (21%bv : reg) as A21.
  pose proof (srcn_src_ok fout fr 3 1 Hsrc ltac:(lia)) as S1. cbn [fr_add Z.of_nat] in S1. change (Z.of_nat 1) with 1 in S1.
  pose proof (faddr_disj C (fout + 1) (from_succ fr) S1 ltac:(lia)) as Fd. rewrite faddr_succ in Fd.
  pose proof (fval_byte C SV m1 ob1 (fout + 1) (from_succ fr) HM1 S1 ltac:(lia)) as [Fv10 Fv11].
  pose proof (src_read C SV m1 ob1 (fout + 1) (from_succ fr) (P0 + (fout + 3 - dist) + -2) HM1 S1 ltac:(lia)
                ltac:(rewrite faddr_succ; subst fr; cbn [faddr]; lia)) as RD1.
  pose proof (MEMI_map_P SV m1 ob1 HM1) as WP.
  symex s6_segs cfg5 2%nat NoDirs [RVal (EVar 34%nat)]
    [(14, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (ELit 2)); (21, EAdd (EVar 32%nat) (EVar 36%nat))]
    [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 256); (35%nat, 2^17); (36%nat, 2^32)] NoRegions
    [P0; fout; fval (is_window s) ob1 (from_succ fr); dist; fout + 3 - dist] NoVals F0 F0'
    (mkst R1 (0x1fc18 : word) m1 s6_rom) R2 HR2 Hfr2 Hms2.
  all: try side.
  pose proof (MEMI_cp1 C SV m1 ob1 (fout + 1) _ HM1 ltac:(lia) (conj Fv10 Fv11)) as HM2.
  clear WP RD1 Fd.
  replace (P0 + fout + 1) with (P0 + (fout + 1)) in Hms2 by lia.
  set (m2 := wbytes m1 _ _) in Hms2, HM2. set (ob2 := arr_set ob1 (fout + 1) _) in HM2.
  assert (B14 : getr R2 14 = zw (P0 + fout + 2)) by (rewrite (Hfr2 14%bv eq_refl); exact A14).
  assert (B21 : getr R2 21 = zw (P0 + fout + (1 - dist) + 2)) by (rewrite (Hfr2 21%bv eq_refl); exact A21).
  assert (B26 : getr R2 26 = zw len) by (rewrite (Hfr2 26%bv eq_refl), (Hfr1 26%bv eq_refl); exact H26).
  assert (B28 : getr R2 28 = zw 2) by (rewrite (Hfr2 28%bv eq_refl), (Hfr1 28%bv eq_refl); exact K28).
  pose proof (srcn_src_ok fout fr 3 2 Hsrc ltac:(lia)) as S2. cbn [fr_add Z.of_nat] in S2. change (Z.of_nat 2) with 2 in S2.
  pose proof (faddr_disj C (fout + 2) (from_succ (from_succ fr)) S2 ltac:(lia)) as Fd. rewrite !faddr_succ in Fd.
  pose proof (fval_byte C SV m2 ob2 (fout + 2) (from_succ (from_succ fr)) HM2 S2 ltac:(lia)) as [Fv20 Fv21].
  pose proof (src_read C SV m2 ob2 (fout + 2) (from_succ (from_succ fr)) (P0 + (fout + 3 - dist) + -1) HM2 S2 ltac:(lia)
                ltac:(rewrite !faddr_succ; subst fr; cbn [faddr]; lia)) as RD2.
  pose proof (MEMI_map_P SV m2 ob2 HM2) as WP.
  assert (Eob : ob' = arr_set ob2 (fout + 2) (fval (is_window s) ob2 (from_succ (from_succ fr)))).
  { subst ob' ob2 ob1. cbn [cblit]. f_equal. lia. }
  rewrite Eob. clear Eob.
  destruct (Z.ltb_spec 2 (len - 3)) as [Hc|Hc].
  - symex s6_segs cfg5 5%nat [true] [RVal (EVar 34%nat)]
      [(14, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (ELit 2)); (21, EAdd (EVar 32%nat) (EVar 36%nat)); (26, EVar 37%nat); (28, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 256); (35%nat, 2^17); (36%nat, 2^32); (37%nat, 2^17)] NoRegions
      [P0; fout; fval (is_window s) ob2 (from_succ (from_succ fr)); dist; fout + 3 - dist; len] NoVals F0 F0'
      (mkst R2 (0x1fc20 : word) m2 s6_rom) R3 HR3 Hfr3 Hms3.
    all: try side. all: try brc.
    pose proof (MEMI_cp1 C SV m2 ob2 (fout + 2) _ HM2 ltac:(lia) (conj Fv20 Fv21)) as HM3.
    replace (P0 + fout + 2) with (P0 + (fout + 2)) in Hms3 by lia.
    assert (HF : forall q, reg_in q [14; 21; 25; 26]%bv = false -> getr R3 q = getr regs q) by fr_chain3 Hfr3 Hfr2 Hfr1.
    exists R3. eexists. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [exact HM3|].
    symex_reg HR3 (14%bv : reg) as C14. symex_reg HR3 (26%bv : reg) as C26.
    split; [rewrite C14; f_equal; lia|]. split; [rewrite (HF 7%bv eq_refl); exact H7|].
    split; [rewrite C26; f_equal; rewrite ?szwrap32_small by lia; lia|]. exact HF.
  - symex s6_segs cfg5 5%nat [false] [RVal (EVar 34%nat)]
      [(14, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (ELit 2)); (21, EAdd (EVar 32%nat) (EVar 36%nat)); (26, EVar 37%nat); (28, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 256); (35%nat, 2^17); (36%nat, 2^32); (37%nat, 2^17)] NoRegions
      [P0; fout; fval (is_window s) ob2 (from_succ (from_succ fr)); dist; fout + 3 - dist; len] NoVals F0 F0'
      (mkst R2 (0x1fc20 : word) m2 s6_rom) R3 HR3 Hfr3 Hms3.
    all: try side. all: try brc.
    pose proof (MEMI_cp1 C SV m2 ob2 (fout + 2) _ HM2 ltac:(lia) (conj Fv20 Fv21)) as HM3.
    replace (P0 + fout + 2) with (P0 + (fout + 2)) in Hms3 by lia.
    assert (HF : forall q, reg_in q [14; 21; 25; 26]%bv = false -> getr R3 q = getr regs q) by fr_chain3 Hfr3 Hfr2 Hfr1.
    exists R3. eexists. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [exact HM3|].
    symex_reg HR3 (14%bv : reg) as C14. symex_reg HR3 (26%bv : reg) as C26.
    split; [rewrite C14; f_equal; lia|]. split; [rewrite (HF 7%bv eq_refl); exact H7|].
    split; [rewrite C26; f_equal; rewrite ?szwrap32_small by lia; lia|]. exact HF.
Qed.

Lemma do3_loop : forall k SV m ob dist fout rem regs,
  KR regs -> MEMI SV m ob ->
  getr regs 14 = zw (P0 + fout + 2) -> getr regs 7 = zw (1 - dist) -> getr regs 26 = zw (3 * Z.of_nat k + rem) ->
  (1 <= k)%nat -> 0 <= rem <= 2 -> 3 * Z.of_nat k + rem < 2 ^ 17 -> 1 <= dist < 2 ^ 17 -> dist <= fout -> fout + 3 * Z.of_nat k <= ON ->
  exists R m', msteps s6_segs (mkst regs (0x1fc0c : word) m s6_rom) (mkst R (0x1fc34 : word) m' s6_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FOut (fout - dist)) ob fout (3 * k))
   /\ getr R 14 = zw (P0 + (fout + 3 * Z.of_nat k) + 2) /\ getr R 7 = zw (1 - dist) /\ getr R 26 = zw rem
   /\ (forall q, reg_in q [14; 21; 25; 26]%bv = false -> getr R q = getr regs q).
Proof.
  induction k as [|k IH]; intros SV m ob dist fout rem regs HK HM H14 H7 H26 Hk Hrem Hlen Hdist Hdf HfoutN; [lia|].
  destruct (do3_trip SV m ob dist fout (3 * Z.of_nat (Datatypes.S k) + rem) regs HK HM H14 H7 H26 ltac:(lia) Hdist Hdf ltac:(lia))
    as (R1 & m1 & Hms1 & HK1 & HM1 & A14 & A7 & A26 & Hfr1).
  destruct k as [|k'].
  - replace (2 <? 3 * Z.of_nat 1 + rem - 3) with false in Hms1 by (symmetry; apply Z.ltb_ge; lia).
    exists R1, m1. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HM1|].
    split; [rewrite A14; f_equal; lia|]. split; [exact A7|]. split; [rewrite A26; f_equal; lia| exact Hfr1].
  - replace (2 <? 3 * Z.of_nat (Datatypes.S (Datatypes.S k')) + rem - 3) with true in Hms1 by (symmetry; apply Z.ltb_lt; lia).
    destruct (IH SV m1 (cblit (is_window s) (FOut (fout - dist)) ob fout 3) dist (fout + 3) rem R1 HK1 HM1
                 ltac:(rewrite A14; f_equal; lia) A7 ltac:(rewrite A26; f_equal; lia) ltac:(lia) Hrem ltac:(lia) Hdist ltac:(lia) ltac:(lia))
      as (R2 & m2 & Hms2 & HK2 & HM2 & B14 & B7 & B26 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|].
    split; [replace (3 * Datatypes.S (Datatypes.S k'))%nat with (3 + 3 * Datatypes.S k')%nat by lia; rewrite cblit_add, fr_add_out;
            replace (fout - dist + Z.of_nat 3) with (fout + 3 - dist) by lia; replace (fout + Z.of_nat 3) with (fout + 3) by lia; exact HM2|].
    split; [rewrite B14; f_equal; lia|]. split; [exact B7|]. split; [exact B26|].
    fr_chain2 Hfr2 Hfr1.
Qed.

Lemma do3_tail : forall SV m ob dist fo rem regs,
  KR regs -> MEMI SV m ob ->
  getr regs 14 = zw (P0 + fo + 2) -> getr regs 26 = zw rem -> getr regs 27 = zw dist ->
  0 <= rem <= 2 -> 1 <= dist < 2 ^ 17 -> dist <= fo -> fo + rem <= ON ->
  exists R m', msteps s6_segs (mkst regs (0x1fc34 : word) m s6_rom) (mkst R (0x1fa48 : word) m' s6_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FOut (fo - dist)) ob fo (Z.to_nat rem))
   /\ getr R 14 = zw (P0 + (fo + rem))
   /\ (forall q, reg_in q [7; 14]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob dist fo rem regs HK HM H14 H26 H27 Hrem Hdist Hdf HfoN.
  pose proof HK as HK'. kr_destr HK. clear_layout.
  pose proof (MEMI_len SV m ob HM) as HL.
  destruct (Z.eq_dec rem 0) as [R0E|RNZ].
  - subst rem.
    symex s6_segs cfg5 4%nat [true] NoReads [(14, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (ELit 2)); (26, ELit 0)]
      [(32%nat, 2^63); (33%nat, 2^32)] NoRegions [P0; fo] NoVals F0 F0'
      (mkst regs (0x1fc34 : word) m s6_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R, m. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [cbn [Z.to_nat cblit]; exact HM|].
    split; [symex_reg HR (14%bv : reg) as A; rewrite A; f_equal; lia| fr_weak Hfr].
  - set (fr := FOut (fo - dist)).
    assert (Hsrc : srcn_ok WN fo fr rem) by (subst fr; cbn; lia).
    pose proof (srcn_src_ok fo fr rem 0 Hsrc ltac:(lia)) as S0. cbn [fr_add Z.of_nat] in S0. rewrite Z.add_0_r in S0.
    pose proof (faddr_disj C fo fr S0 ltac:(lia)) as Fd.
    pose proof (fval_byte C SV m ob fo fr HM S0 ltac:(lia)) as [Fv0 Fv1].
    pose proof (src_read C SV m ob fo fr (P0 + fo - dist) HM S0 ltac:(lia) ltac:(subst fr; cbn [faddr]; lia)) as RD0.
    pose proof (MEMI_map_P SV m ob HM) as WP.
    destruct (Z.eq_dec rem 1) as [R1E|R2E].
    + subst rem.
      symex s6_segs cfg5 7%nat [false; true] [RVal (EVar 34%nat)]
        [(14, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (ELit 2)); (26, ELit 1); (27, EVar 35%nat); (28, ELit 2)]
        [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 256); (35%nat, 2^17)] NoRegions
        [P0; fo; fval (is_window s) ob fr; dist] NoVals F0 F0'
        (mkst regs (0x1fc34 : word) m s6_rom) R HR Hfr Hms.
      all: try side. all: try brc.
      exists R. eexists. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      split; [cbn [Z.to_nat Pos.to_nat cblit]; replace (P0 + fo + 2 + -2) with (P0 + fo) by lia; apply (MEMI_cp1 C); [exact HM | lia | lia]|].
      split; [symex_reg HR (14%bv : reg) as A; rewrite A; f_equal; lia| fr_weak Hfr].
    + assert (R2 : rem = 2) by lia. subst rem.
      symex s6_segs cfg5 5%nat [false; false] [RVal (EVar 34%nat)]
        [(14, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (ELit 2)); (26, ELit 2); (27, EVar 35%nat); (28, ELit 2)]
        [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 256); (35%nat, 2^17)] NoRegions
        [P0; fo; fval (is_window s) ob fr; dist] NoVals F0 F0'
        (mkst regs (0x1fc34 : word) m s6_rom) R1 HR1 Hfr1 Hms1.
      all: try side. all: try brc.
      pose proof (MEMI_cp1 C SV m ob fo _ HM ltac:(lia) (conj Fv0 Fv1)) as HM1.
      clear WP RD0 Fd.
      replace (P0 + fo + 2 + -2) with (P0 + fo) in Hms1 by lia.
      set (m1 := wbytes m _ _) in Hms1, HM1. set (ob1 := arr_set ob fo _) in HM1.
      assert (A14 : getr R1 14 = zw (P0 + fo + 2)) by (rewrite (Hfr1 14%bv eq_refl); exact H14).
      assert (A27 : getr R1 27 = zw dist) by (rewrite (Hfr1 27%bv eq_refl); exact H27).
      pose proof (srcn_src_ok fo fr 2 1 Hsrc ltac:(lia)) as S1. cbn [fr_add Z.of_nat] in S1. change (Z.of_nat 1) with 1 in S1.
      pose proof (faddr_disj C (fo + 1) (from_succ fr) S1 ltac:(lia)) as Fd. rewrite faddr_succ in Fd.
      pose proof (fval_byte C SV m1 ob1 (fo + 1) (from_succ fr) HM1 S1 ltac:(lia)) as [Fv10 Fv11].
      pose proof (src_read C SV m1 ob1 (fo + 1) (from_succ fr) (Z.lxor dist (-1) + (P0 + fo) + 2) HM1 S1 ltac:(lia)
                    ltac:(rewrite faddr_succ, Z.lxor_m1_r; unfold Z.lnot; subst fr; cbn [faddr]; lia)) as RD1.
      pose proof (MEMI_map_P SV m1 ob1 HM1) as WP.
      symex s6_segs cfg5 5%nat NoDirs [RVal (EVar 34%nat)]
        [(14, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (ELit 2)); (27, EVar 35%nat)]
        [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 256); (35%nat, 2^17)] NoRegions
        [P0; fo; fval (is_window s) ob1 (from_succ fr); dist] NoVals F0 F0'
        (mkst R1 (0x1fc48 : word) m1 s6_rom) R2 HR2 Hfr2 Hms2.
      all: try side. all: try (rewrite Z.lxor_m1_r; unfold Z.lnot; lia).
      pose proof (MEMI_cp1 C SV m1 ob1 (fo + 1) _ HM1 ltac:(lia) (conj Fv10 Fv11)) as HM2.
      replace (P0 + fo + 1) with (P0 + (fo + 1)) in Hms2 by lia.
      assert (HF : forall q, reg_in q [7; 14]%bv = false -> getr R2 q = getr regs q) by fr_chain2 Hfr2 Hfr1.
      exists R2. eexists. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
      split; [subst ob1; cbn [Z.to_nat Pos.to_nat cblit]; exact HM2|].
      split; [rewrite (Hfr2 14%bv eq_refl), A14; f_equal; lia| exact HF].
Qed.

Lemma fset_from_fields : forall g v,
  f_ob (fset_from g v) = f_ob g /\ f_from (fset_from g v) = v /\ f_out (fset_from g v) = f_out g /\ f_len (fset_from g v) = f_len g
  /\ f_in (fset_from g v) = f_in g /\ f_hold (fset_from g v) = f_hold g /\ f_bits (fset_from g v) = f_bits g /\ f_dist (fset_from g v) = f_dist g.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9] v; repeat split; reflexivity. Qed.

Definition do3_stmt27 : Prop :=
  forall SV m f regs,
    KR regs -> MEMI SV m (f_ob f) ->
    getr regs 14 = zw (P0 + f_out f + 2) -> getr regs 7 = zw (1 - f_dist f) -> getr regs 27 = zw (f_dist f) -> getr regs 26 = zw (f_len f) ->
    3 <= f_len f < 2 ^ 17 -> 1 <= f_dist f < 2 ^ 17 -> f_dist f <= f_out f -> x_beg X <= f_out f -> f_out f + f_len f <= ON ->
    let f' := copy_tail X (copy_do3 X (fset_from f (FOut (f_out f - f_dist f)))) in
    exists R m', msteps s6_segs (mkst regs (0x1fc0c : word) m s6_rom) (mkst R (0x1fa48 : word) m' s6_rom)
     /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 14 = zw (P0 + f_out f')
     /\ (forall k, reg_in k [7; 14; 21; 25; 26]%bv = false -> getr R k = getr regs k)
     /\ f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_out f' = f_out f + f_len f /\ f_dist f' = f_dist f.

Lemma do3_27 : do3_stmt27.
Proof.
  intros SV m f regs HK HM H14 H7 H27 H26 Hlen Hdist Hdf Hbeg Hfon. cbv zeta.
  pose proof (proj1 (ffx_beg_range C)) as Hxbeg0'.
  set (f0 := fset_from f (FOut (f_out f - f_dist f))).
  destruct (fset_from_fields f (FOut (f_out f - f_dist f))) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). fold f0 in F1, F2, F3, F4, F5, F6, F7, F8.
  rewrite copy_do3_cpn by (rewrite F4; lia). rewrite F4.
  pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as Hm3.
  set (k := Z.to_nat (f_len f / 3)).
  assert (Hk : (1 <= k)%nat) by (subst k; assert (1 <= f_len f / 3) by (apply Z.div_le_lower_bound; lia); lia).
  assert (Hk3 : 3 * Z.of_nat k = 3 * (f_len f / 3)) by (subst k; pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)); lia).
  destruct (do3_loop k SV m (f_ob f) (f_dist f) (f_out f) (f_len f mod 3) regs HK HM H14 H7 ltac:(rewrite H26; f_equal; lia)
              Hk ltac:(lia) ltac:(lia) Hdist Hdf ltac:(lia))
    as (R3 & m3 & Hms3 & HK3 & HM3 & C14 & C7 & C26 & Hfr3).
  destruct (do3_tail SV m3 _ (f_dist f) (f_out f + 3 * Z.of_nat k) (f_len f mod 3) R3 HK3 HM3 C14 C26
              ltac:(rewrite (Hfr3 27%bv eq_refl); exact H27) ltac:(lia) Hdist ltac:(lia) ltac:(lia))
    as (R4 & m4 & Hms4 & HK4 & HM4 & D14 & Hfr4).
  set (f1 := fset_len (cpn X (Z.to_nat (3 * (f_len f / 3))) f0) (f_len f mod 3)).
  destruct (fset_len_fields (cpn X (Z.to_nat (3 * (f_len f / 3))) f0) (f_len f mod 3)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  fold f1 in E1, E2, E3, E4, E5, E6, E7, E8.
  rewrite cpn_ob, F2, F1, F3 in E1. rewrite cpn_from, F2, fr_add_out in E2. rewrite cpn_out, F3 in E3.
  rewrite cpn_in, F5 in E5. rewrite cpn_hold, F6 in E6. rewrite cpn_bits, F7 in E7. rewrite cpn_dist, F8 in E8.
  replace (Z.to_nat (3 * (f_len f / 3))) with (3 * k)%nat in E1, E2, E3 by lia.
  replace (Z.of_nat (3 * k)) with (3 * Z.of_nat k) in E2, E3 by lia.
  rewrite copy_tail_cpn by (rewrite E4; lia). rewrite E4.
  rewrite cpn_ob, cpn_out, cpn_in, cpn_hold, cpn_bits, cpn_dist, E1, E2, E3, E5, E6, E7, E8. cbn [x_window ffx_of].
  exists R4, m4. split; [eapply msteps_trans; [exact Hms3 | exact Hms4]|]. split; [exact HK4|].
  split; [replace (f_out f - f_dist f + 3 * Z.of_nat k) with (f_out f + 3 * Z.of_nat k - f_dist f) by lia; exact HM4|].
  split; [rewrite D14; f_equal; lia|].
  split; [fr_chain2 Hfr4 Hfr3|]. repeat split; lia.
Qed.

Lemma do3 : do3_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof. exact do3_27. Qed.

End Walk.
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
