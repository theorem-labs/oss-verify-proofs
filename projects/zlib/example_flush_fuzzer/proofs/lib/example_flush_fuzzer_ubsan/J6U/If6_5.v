(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem InffastModel InffastSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InffastCtx IfSpec IfSpec6 If6_1 If6_5I.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac symex_auto ::=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia;
  try solve [ reflexivity | assumption | symex_ret_auto | symex_read_auto | symex_store_auto | symex_sok_auto | lia | split; lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma cpn_in : forall x n f, f_in (cpn x n f) = f_in f. Proof. intros. apply cpn_keep. Qed.
Lemma cpn_hold : forall x n f, f_hold (cpn x n f) = f_hold f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_bits : forall x n f, f_bits (cpn x n f) = f_bits f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_len : forall x n f, f_len (cpn x n f) = f_len f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_dist : forall x n f, f_dist (cpn x n f) = f_dist f. Proof. intros. apply (cpn_keep x n f). Qed.
Lemma cpn_ob : forall x n f, f_ob (cpn x n f) = cblit (x_window x) (f_from f) (f_ob f) (f_out f) n. Proof. intros. apply cpn_cblit. Qed.
Lemma cpn_from : forall x n f, f_from (cpn x n f) = fr_add (f_from f) n. Proof. intros. apply (cpn_cblit x n f). Qed.
Lemma fset_len_id : forall f, fset_len f (f_len f) = f. Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9]; reflexivity. Qed.
Lemma fset_len_fields : forall g v,
  f_ob (fset_len g v) = f_ob g /\ f_from (fset_len g v) = f_from g /\ f_out (fset_len g v) = f_out g /\ f_len (fset_len g v) = v
  /\ f_in (fset_len g v) = f_in g /\ f_hold (fset_len g v) = f_hold g /\ f_bits (fset_len g v) = f_bits g /\ f_dist (fset_len g v) = f_dist g.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9] v; repeat split; reflexivity. Qed.
Lemma fset_from_fields : forall g v,
  f_ob (fset_from g v) = f_ob g /\ f_from (fset_from g v) = v /\ f_out (fset_from g v) = f_out g /\ f_len (fset_from g v) = f_len g
  /\ f_in (fset_from g v) = f_in g /\ f_hold (fset_from g v) = f_hold g /\ f_bits (fset_from g v) = f_bits g /\ f_dist (fset_from g v) = f_dist g.
Proof. intros [a1 a2 a3 a4 a5 a6 a7 a8 a9] v; repeat split; reflexivity. Qed.

Section Walk.
Context {mem : word -> option byte} {sp : Z} {ra : word}
        {s : inflate_state} {c : icall} {r : iregs}
        {ZP S I0 P0 WB : Z}.
Variable C : iff_pre s6u_segs is6_LENFIX is6_DISTFIX ROD6_LO ROD6_HI IMG6_TOP mem sp ra s c r ZP S I0 P0 WB.
Local Notation X := (ffx_of s c r).
Local Notation IN := (arr_len (ic_input c)).
Local Notation ON := (arr_len (ic_outbuf c)).
Local Notation WN := (arr_len (is_window s)).
Local Notation LC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_lencode s)).
Local Notation DC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_distcode s)).
Local Notation LCN := (ctab_len (is_lencode s)).
Local Notation DCN := (ctab_len (is_distcode s)).
Local Notation KR := (@KREGS6 sp ZP S I0 P0 WB X (is_lenbits s) (is_distbits s) LC DC).
Local Notation MEMI := (@MEMINV s6u_segs mem sp (arr_len (ic_outbuf c)) ZP S P0).
Let Hret := ifp_ret C.
Let Hzin := ifp_zs_in C. Let Hzain := ifp_zs_ain C. Let Hzout := ifp_zs_out C. Let Hzaout := ifp_zs_aout C. Let Hzst := ifp_zs_state C.
Let Hsc := ifp_scalars C. Let Hcodes := ifp_codes C. Let Hcodes_b := ifp_codes_b C.
Let Hwin := ifp_win C. Let Hwin_b := ifp_win_b C. Let Hinp := ifp_in C. Let Hinp_b := ifp_in_b C.
Let Hout := ifp_out C. Let Hout_b := ifp_out_b C. Let Hrod := ifp_rod C.
Let Hsp0 : 0x5f000 <= sp := proj1 (ifp_sp C). Let Hsp1 : sp + 160 < 2 ^ 63 := proj2 (ifp_sp C).
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
Let HalZ : ZP mod 8 = 0 := proj1 (ifp_align C). Let HalS : S mod 8 = 0 := proj2 (ifp_align C).
Let HI17 : 0 < I0 := proj1 (ifp_hi C).
Let HWpos : 0 < WN -> 0 < WB := proj2 (ifp_hi C).

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
Local Ltac guards :=
  lazymatch goal with
  | |- @ex _ _ => idtac
  | |- Z.lxor (if 0 <? ?a then 1 else 0) (if ?b <? 1 then 1 else 0) <> 0 =>
      destruct (Z.ltb_spec 0 a); [| exfalso; mlia]; destruct (Z.ltb_spec b 1); [exfalso| discriminate];
      first [ mlia
            | match goal with H0 : Z.lxor ?o ?k < 1 |- _ =>
                pose proof (Z.lxor_nonneg o k) as HN; assert (HE : o = k) by (apply Z.lxor_eq; mlia); clear H0 HN; mlia end ]
  | |- Z.lxor 1 (if ?b <? 1 then 1 else 0) <> 0 =>
      destruct (Z.ltb_spec b 1); [exfalso; first [mlia | rewrite ?Z.lxor_m1_r in *; unfold Z.lnot in *; mlia] | discriminate]
  | |- _ => first [brc | mlia | progress (rewrite ?Z.lxor_m1_r; unfold Z.lnot); mlia | rewrite land1_mod2 by lia; mlia | idtac]
  end.
Local Ltac kr_destr HK := destruct HK as (K2 & K10 & K11 & K12 & K21 & K28 & K30 & K31 & K8 & K18 & K19 & K17 & K20 & K24 & K25 & K26).

Local Ltac frs Hr := first [ reflexivity | eapply reg_in_sub; [| exact Hr]; reflexivity ].
Local Ltac fr_chain2 Hfr2 Hfr1 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite (Hfr2 r), (Hfr1 r); frs Hr.
Local Ltac fr_chain3 Hfr3 Hfr2 Hfr1 :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; rewrite (Hfr3 r), (Hfr2 r), (Hfr1 r); frs Hr.

Lemma srcn_src_ok : forall fout fr n k, srcn_ok WN fout fr n -> 0 <= Z.of_nat k < n ->
  src_ok WN (fout + Z.of_nat k) (fr_add fr k).
Proof. intros fout [i|i] n k H Hk; cbn in H; [rewrite fr_add_win | rewrite fr_add_out]; cbn; lia. Qed.
Lemma srcn_ok_adv : forall fout fr n k, srcn_ok WN fout fr n -> Z.of_nat k <= n ->
  srcn_ok WN (fout + Z.of_nat k) (fr_add fr k) (n - Z.of_nat k).
Proof. intros fout [i|i] n k H Hk; cbn in H; [rewrite fr_add_win | rewrite fr_add_out]; cbn; lia. Qed.
Lemma srcn_ok_le : forall fout fr n n', srcn_ok WN fout fr n -> n' <= n -> srcn_ok WN fout fr n'.
Proof. intros fout [i|i] n n' H Hn; cbn in *; lia. Qed.

Lemma wtripA : forall SV m ob w i k regs,
  KR regs -> MEMI SV m ob ->
  getr regs 6 = zw (WB + w) -> getr regs 29 = zw (WB + w) -> getr regs 22 = zw (P0 + i) -> getr regs 7 = zw (P0 + i) ->
  getr regs 5 = zw (P0 + i + 1) -> getr regs 1 = zw k ->
  1 <= k < 2 ^ 17 -> 0 <= w < WN -> 0 <= i < ON ->
  exists R, msteps s6u_segs (mkst regs (0x22a24 : word) m s6u_rom)
              (mkst R (if k =? 1 then (0x22a58 : word) else (0x22a24 : word)) (wbytes m (zw (P0 + i)) (Z_to_le_bytes 1 (arr_get (is_window s) w))) s6u_rom)
   /\ KR R /\ getr R 6 = zw (WB + w + 1) /\ getr R 29 = zw (WB + w + 1) /\ getr R 22 = zw (P0 + i + 1) /\ getr R 7 = zw (P0 + i + 1)
   /\ getr R 5 = zw (P0 + i + 1 + 1) /\ getr R 1 = zw (k - 1) /\ getr R 13 = zw (P0 + i + 1) /\ getr R 9 = zw (P0 + i + 1)
   /\ (forall q, reg_in q [1; 5; 6; 7; 9; 13; 22; 29]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob w i k regs HK HM H6 H29 H22 H7 H5 H1 Hk Hw Hi.
  pose proof (MEMI_win C SV m ob HM) as Hwin_m. pose proof (ifp_win_b C) as Hwb.
  pose proof (MEMI_map_P SV m ob HM) as WP. pose proof (ifp_d_PW C) as HdPW.
  destruct (Hwb w ltac:(lia)) as [Hv0 Hv1]. assert (HWB : 0 < WB) by (apply HWpos; lia).
  pose proof HK as HK'. kr_destr HK. clear_layout.
  destruct (Z.eqb_spec k 1) as [K1|K1].
  - symex s6u_segs fastC6 14%nat [false; false; false] [RVal (EVar 37%nat)]
      [(6, EAdd (EVar 32%nat) (EVar 33%nat)); (29, EAdd (EVar 32%nat) (EVar 33%nat)); (22, EAdd (EVar 34%nat) (EVar 35%nat));
       (7, EAdd (EVar 34%nat) (EVar 35%nat)); (5, EAdd (EAdd (EVar 34%nat) (EVar 35%nat)) (ELit 1)); (1, EVar 36%nat); (18, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^17); (37%nat, 256)] NoRegions
      [WB; w; P0; i; k; arr_get (is_window s) w] NoVals F0 F0' (mkst regs (0x22a24 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    repeat lazymatch goal with
      | |- getr R ?q = _ /\ _ => split; [let A := fresh "A" in symex_reg HR (q : reg) as A; rewrite A; f_equal; rewrite ?szwrap32_small by lia; lia|]
      | |- forall q, _ => fr_weak Hfr
      end.
  - symex s6u_segs fastC6 14%nat [false; false; true] [RVal (EVar 37%nat)]
      [(6, EAdd (EVar 32%nat) (EVar 33%nat)); (29, EAdd (EVar 32%nat) (EVar 33%nat)); (22, EAdd (EVar 34%nat) (EVar 35%nat));
       (7, EAdd (EVar 34%nat) (EVar 35%nat)); (5, EAdd (EAdd (EVar 34%nat) (EVar 35%nat)) (ELit 1)); (1, EVar 36%nat); (18, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^17); (37%nat, 256)] NoRegions
      [WB; w; P0; i; k; arr_get (is_window s) w] NoVals F0 F0' (mkst regs (0x22a24 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    repeat lazymatch goal with
      | |- getr R ?q = _ /\ _ => split; [let A := fresh "A" in symex_reg HR (q : reg) as A; rewrite A; f_equal; rewrite ?szwrap32_small by lia; lia|]
      | |- forall q, _ => fr_weak Hfr
      end.
Qed.

Lemma wlegA_loop : forall k SV m ob w i regs,
  KR regs -> MEMI SV m ob ->
  getr regs 6 = zw (WB + w) -> getr regs 29 = zw (WB + w) -> getr regs 22 = zw (P0 + i) -> getr regs 7 = zw (P0 + i) ->
  getr regs 5 = zw (P0 + i + 1) -> getr regs 1 = zw (Z.of_nat k) ->
  (1 <= k)%nat -> Z.of_nat k < 2 ^ 17 -> 0 <= w -> w + Z.of_nat k <= WN -> 0 <= i -> i + Z.of_nat k <= ON ->
  exists R m', msteps s6u_segs (mkst regs (0x22a24 : word) m s6u_rom) (mkst R (0x22a58 : word) m' s6u_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FWin w) ob i k)
   /\ getr R 22 = zw (P0 + (i + Z.of_nat k)) /\ getr R 13 = zw (P0 + (i + Z.of_nat k)) /\ getr R 9 = zw (P0 + (i + Z.of_nat k))
   /\ getr R 6 = zw (WB + w + Z.of_nat k)
   /\ (forall q, reg_in q [1; 5; 6; 7; 9; 13; 22; 29]%bv = false -> getr R q = getr regs q).
Proof.
  induction k as [|k IH]; intros SV m ob w i regs HK HM H6 H29 H22 H7 H5 H1 Hk Hk17 Hw Hwk Hi Hik; [lia|].
  pose proof (ifp_win_b C) as Hwb. destruct (Hwb w ltac:(lia)) as [Hv0 Hv1].
  destruct (wtripA SV m ob w i (Z.of_nat (Datatypes.S k)) regs HK HM H6 H29 H22 H7 H5 H1 ltac:(lia) ltac:(lia) ltac:(lia))
    as (R1 & Hms1 & HK1 & A6 & A29 & A22 & A7 & A5 & A1 & A13 & A9 & Hfr1).
  pose proof (MEMI_cp1 C SV m ob i (arr_get (is_window s) w) HM ltac:(lia) ltac:(lia)) as HM1.
  destruct k as [|k'].
  - replace (Z.of_nat 1 =? 1) with true in Hms1 by reflexivity.
    exists R1. eexists. split; [exact Hms1|]. split; [exact HK1|].
    split; [cbn [cblit fval from_succ]; exact HM1|].
    split; [rewrite A22; f_equal; lia|]. split; [rewrite A13; f_equal; lia|]. split; [rewrite A9; f_equal; lia|].
    split; [rewrite A6; f_equal; lia| exact Hfr1].
  - replace (Z.of_nat (Datatypes.S (Datatypes.S k')) =? 1) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    destruct (IH SV _ _ (w + 1) (i + 1) R1 HK1 HM1 ltac:(rewrite A6; f_equal; lia) ltac:(rewrite A29; f_equal; lia) ltac:(rewrite A22; f_equal; lia)
                 ltac:(rewrite A7; f_equal; lia) ltac:(rewrite A5; f_equal; lia) ltac:(rewrite A1; f_equal; lia)
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R2 & m2 & Hms2 & HK2 & HM2 & B22 & B13 & B9 & B6 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|]. split; [cbn [cblit fval from_succ]; exact HM2|].
    split; [rewrite B22; f_equal; lia|]. split; [rewrite B13; f_equal; lia|]. split; [rewrite B9; f_equal; lia|].
    split; [rewrite B6; f_equal; lia|]. fr_chain2 Hfr2 Hfr1.
Qed.

Lemma wlegA : wlegA_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof.
  intros SV m f n wi regs HK HM Hfr H6 H29 H22 H7 H5 H1 Hn Hn17 Hwi HwiN Hbeg HoN. cbv zeta.
  destruct (wlegA_loop n SV m (f_ob f) wi (f_out f) regs HK HM H6 H29 H22 H7 H5 H1 Hn Hn17 Hwi HwiN ltac:(lia) HoN)
    as (R & m' & Hms & HK' & HM' & A22 & A13 & A9 & A6 & Hfr').
  exists R, m'. split; [exact Hms|]. split; [exact HK'|].
  split; [rewrite cpn_ob, Hfr; exact HM'|]. rewrite cpn_out.
  split; [exact A22|]. split; [exact A13|]. split; [exact A9|]. split; [exact A6| exact Hfr'].
Qed.

Definition wtripB_stmt (hd : word) : Prop :=
  forall SV m ob w i k regs,
    KR regs -> MEMI SV m ob ->
    getr regs 6 = zw (WB + w) -> getr regs 29 = zw (WB + w) -> getr regs 22 = zw (P0 + i) -> getr regs 13 = zw (P0 + i) -> getr regs 5 = zw k ->
    1 <= k < 2 ^ 17 -> 0 <= w < WN -> 0 <= i < ON ->
    exists R, msteps s6u_segs (mkst regs hd m s6u_rom)
                (mkst R (if k =? 1 then (0x22c30 : word) else hd) (wbytes m (zw (P0 + i)) (Z_to_le_bytes 1 (arr_get (is_window s) w))) s6u_rom)
     /\ KR R /\ getr R 6 = zw (WB + w + 1) /\ getr R 29 = zw (WB + w + 1) /\ getr R 22 = zw (P0 + i + 1) /\ getr R 13 = zw (P0 + i + 1)
     /\ getr R 5 = zw (k - 1) /\ getr R 1 = zw (P0 + i + 1)
     /\ (forall q, reg_in q [1; 5; 6; 7; 13; 22; 29]%bv = false -> getr R q = getr regs q).

Local Ltac wtripB_tac R HR Hfr Hms :=
  let HK' := fresh "HK'" in
  intros SV m ob w i k regs HK HM H6 H29 H22 H13 H5 Hk Hw Hi;
  pose proof (MEMI_win C SV m ob HM) as Hwin_m; pose proof (ifp_win_b C) as Hwb;
  pose proof (MEMI_map_P SV m ob HM) as WP; pose proof (ifp_d_PW C) as HdPW;
  destruct (Hwb w ltac:(lia)) as [Hv0 Hv1]; assert (HWB : 0 < WB) by (apply HWpos; lia);
  pose proof HK as HK'; kr_destr HK; clear_layout;
  destruct (Z.eqb_spec k 1) as [K1|K1];
  [ lazymatch goal with |- exists R0, msteps _ ?st _ /\ _ =>
      symex s6u_segs fastC6 14%nat [false; false; false] [RVal (EVar 37%nat)]
        [(6, EAdd (EVar 32%nat) (EVar 33%nat)); (29, EAdd (EVar 32%nat) (EVar 33%nat)); (22, EAdd (EVar 34%nat) (EVar 35%nat));
         (13, EAdd (EVar 34%nat) (EVar 35%nat)); (5, EVar 36%nat); (18, ELit 2)]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^17); (37%nat, 256)] NoRegions
        [WB; w; P0; i; k; arr_get (is_window s) w] NoVals F0 F0' st R HR Hfr Hms end
  | lazymatch goal with |- exists R0, msteps _ ?st _ /\ _ =>
      symex s6u_segs fastC6 14%nat [false; false; true] [RVal (EVar 37%nat)]
        [(6, EAdd (EVar 32%nat) (EVar 33%nat)); (29, EAdd (EVar 32%nat) (EVar 33%nat)); (22, EAdd (EVar 34%nat) (EVar 35%nat));
         (13, EAdd (EVar 34%nat) (EVar 35%nat)); (5, EVar 36%nat); (18, ELit 2)]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^17); (37%nat, 256)] NoRegions
        [WB; w; P0; i; k; arr_get (is_window s) w] NoVals F0 F0' st R HR Hfr Hms end ];
  try side; guards;
  lazymatch goal with
  | |- exists R0, _ =>
      exists R; split; [exact Hms|];
      split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|];
      repeat lazymatch goal with
        | |- getr R ?q = _ /\ _ => split; [let A := fresh "A" in symex_reg HR (q : reg) as A; rewrite A; f_equal; rewrite ?szwrap32_small by lia; lia|]
        | |- forall q, _ => fr_weak Hfr
        end
  | |- _ => idtac
  end.

Lemma wtripB_22a2c : wtripB_stmt (0x22b98 : word).
Proof. unfold wtripB_stmt. wtripB_tac R HR Hfr Hms. Qed.
Lemma wtripB_22a98 : wtripB_stmt (0x22c04 : word).
Proof. unfold wtripB_stmt. wtripB_tac R HR Hfr Hms. Qed.

Lemma wlegB_loop : forall hd, wtripB_stmt hd -> forall k SV m ob w i regs,
  KR regs -> MEMI SV m ob ->
  getr regs 6 = zw (WB + w) -> getr regs 29 = zw (WB + w) -> getr regs 22 = zw (P0 + i) -> getr regs 13 = zw (P0 + i) -> getr regs 5 = zw (Z.of_nat k) ->
  (1 <= k)%nat -> Z.of_nat k < 2 ^ 17 -> 0 <= w -> w + Z.of_nat k <= WN -> 0 <= i -> i + Z.of_nat k <= ON ->
  exists R m', msteps s6u_segs (mkst regs hd m s6u_rom) (mkst R (0x22c30 : word) m' s6u_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FWin w) ob i k)
   /\ getr R 22 = zw (P0 + (i + Z.of_nat k)) /\ getr R 13 = zw (P0 + (i + Z.of_nat k)) /\ getr R 1 = zw (P0 + (i + Z.of_nat k))
   /\ getr R 6 = zw (WB + w + Z.of_nat k)
   /\ (forall q, reg_in q [1; 5; 6; 7; 13; 22; 29]%bv = false -> getr R q = getr regs q).
Proof.
  intros hd TRIP. induction k as [|k IH]; intros SV m ob w i regs HK HM H6 H29 H22 H13 H5 Hk Hk17 Hw Hwk Hi Hik; [lia|].
  pose proof (ifp_win_b C) as Hwb. destruct (Hwb w ltac:(lia)) as [Hv0 Hv1].
  destruct (TRIP SV m ob w i (Z.of_nat (Datatypes.S k)) regs HK HM H6 H29 H22 H13 H5 ltac:(lia) ltac:(lia) ltac:(lia))
    as (R1 & Hms1 & HK1 & A6 & A29 & A22 & A13 & A5 & A1 & Hfr1).
  pose proof (MEMI_cp1 C SV m ob i (arr_get (is_window s) w) HM ltac:(lia) ltac:(lia)) as HM1.
  destruct k as [|k'].
  - replace (Z.of_nat 1 =? 1) with true in Hms1 by reflexivity.
    exists R1. eexists. split; [exact Hms1|]. split; [exact HK1|].
    split; [cbn [cblit fval from_succ]; exact HM1|].
    split; [rewrite A22; f_equal; lia|]. split; [rewrite A13; f_equal; lia|]. split; [rewrite A1; f_equal; lia|].
    split; [rewrite A6; f_equal; lia| exact Hfr1].
  - replace (Z.of_nat (Datatypes.S (Datatypes.S k')) =? 1) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    destruct (IH SV _ _ (w + 1) (i + 1) R1 HK1 HM1 ltac:(rewrite A6; f_equal; lia) ltac:(rewrite A29; f_equal; lia) ltac:(rewrite A22; f_equal; lia)
                 ltac:(rewrite A13; f_equal; lia) ltac:(rewrite A5; f_equal; lia)
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R2 & m2 & Hms2 & HK2 & HM2 & B22 & B13 & B1 & B6 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|]. split; [cbn [cblit fval from_succ]; exact HM2|].
    split; [rewrite B22; f_equal; lia|]. split; [rewrite B13; f_equal; lia|]. split; [rewrite B1; f_equal; lia|].
    split; [rewrite B6; f_equal; lia|]. fr_chain2 Hfr2 Hfr1.
Qed.

Lemma wlegB_of_loop : forall hd, wtripB_stmt hd ->
  wlegB_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) hd.
Proof.
  intros hd TRIP SV m f n wi regs HK HM Hfr H6 H29 H22 H13 H5 Hn Hn17 Hwi HwiN Hbeg HoN. cbv zeta.
  destruct (wlegB_loop hd TRIP n SV m (f_ob f) wi (f_out f) regs HK HM H6 H29 H22 H13 H5 Hn Hn17 Hwi HwiN ltac:(lia) HoN)
    as (R & m' & Hms & HK' & HM' & A22 & A13 & A1 & A6 & Hfr').
  exists R, m'. split; [exact Hms|]. split; [exact HK'|].
  split; [rewrite cpn_ob, Hfr; exact HM'|]. rewrite cpn_out.
  split; [exact A22|]. split; [exact A13|]. split; [exact A1|]. split; [exact A6| exact Hfr'].
Qed.
Lemma wlegB_22a2c : wlegB_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) (0x22b98 : word).
Proof. exact (wlegB_of_loop _ wtripB_22a2c). Qed.
Lemma wlegB_22a98 : wlegB_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem) (0x22c04 : word).
Proof. exact (wlegB_of_loop _ wtripB_22a98). Qed.

Lemma wtrip2 : forall SV m ob w i k regs,
  KR regs -> MEMI SV m ob ->
  getr regs 5 = zw (WB + w) -> getr regs 7 = zw (WB + w) -> getr regs 13 = zw (P0 + i) -> getr regs 9 = zw (P0 + i) -> getr regs 29 = zw k ->
  1 <= k < 2 ^ 31 -> 0 <= w < WN -> 0 <= i < ON ->
  exists R, msteps s6u_segs (mkst regs (0x22a6c : word) m s6u_rom)
              (mkst R (if k =? 1 then (0x22a98 : word) else (0x22a6c : word)) (wbytes m (zw (P0 + i)) (Z_to_le_bytes 1 (arr_get (is_window s) w))) s6u_rom)
   /\ KR R /\ getr R 5 = zw (WB + w + 1) /\ getr R 7 = zw (WB + w + 1) /\ getr R 13 = zw (P0 + i + 1) /\ getr R 9 = zw (P0 + i + 1)
   /\ getr R 29 = zw (k - 1) /\ getr R 1 = zw (P0 + i + 1)
   /\ (forall q, reg_in q [1; 5; 6; 7; 9; 13; 29]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob w i k regs HK HM H5 H7 H13 H9 H29 Hk Hw Hi.
  pose proof (MEMI_win C SV m ob HM) as Hwin_m. pose proof (ifp_win_b C) as Hwb.
  pose proof (MEMI_map_P SV m ob HM) as WP. pose proof (ifp_d_PW C) as HdPW.
  destruct (Hwb w ltac:(lia)) as [Hv0 Hv1]. assert (HWB : 0 < WB) by (apply HWpos; lia).
  pose proof HK as HK'. kr_destr HK. clear_layout.
  destruct (Z.eqb_spec k 1) as [K1|K1].
  - symex s6u_segs fastC6 14%nat [false; false; false] [RVal (EVar 37%nat)]
      [(5, EAdd (EVar 32%nat) (EVar 33%nat)); (7, EAdd (EVar 32%nat) (EVar 33%nat)); (13, EAdd (EVar 34%nat) (EVar 35%nat));
       (9, EAdd (EVar 34%nat) (EVar 35%nat)); (29, EVar 36%nat); (18, ELit 2); (8, ELit (-1))]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^31); (37%nat, 256)] NoRegions
      [WB; w; P0; i; k; arr_get (is_window s) w] NoVals F0 F0' (mkst regs (0x22a6c : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    repeat lazymatch goal with
      | |- getr R ?q = _ /\ _ => split; [let A := fresh "A" in symex_reg HR (q : reg) as A; rewrite A; f_equal; rewrite ?szwrap32_small by lia; lia|]
      | |- forall q, _ => fr_weak Hfr
      end.
  - symex s6u_segs fastC6 14%nat [false; false; true] [RVal (EVar 37%nat)]
      [(5, EAdd (EVar 32%nat) (EVar 33%nat)); (7, EAdd (EVar 32%nat) (EVar 33%nat)); (13, EAdd (EVar 34%nat) (EVar 35%nat));
       (9, EAdd (EVar 34%nat) (EVar 35%nat)); (29, EVar 36%nat); (18, ELit 2); (8, ELit (-1))]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^31); (37%nat, 256)] NoRegions
      [WB; w; P0; i; k; arr_get (is_window s) w] NoVals F0 F0' (mkst regs (0x22a6c : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    repeat lazymatch goal with
      | |- getr R ?q = _ /\ _ => split; [let A := fresh "A" in symex_reg HR (q : reg) as A; rewrite A; f_equal; rewrite ?szwrap32_small by lia; lia|]
      | |- forall q, _ => fr_weak Hfr
      end.
Qed.

Lemma wleg2_loop : forall k SV m ob w i regs,
  KR regs -> MEMI SV m ob ->
  getr regs 5 = zw (WB + w) -> getr regs 7 = zw (WB + w) -> getr regs 13 = zw (P0 + i) -> getr regs 9 = zw (P0 + i) -> getr regs 29 = zw (Z.of_nat k) ->
  (1 <= k)%nat -> Z.of_nat k < 2 ^ 31 -> 0 <= w -> w + Z.of_nat k <= WN -> 0 <= i -> i + Z.of_nat k <= ON ->
  exists R m', msteps s6u_segs (mkst regs (0x22a6c : word) m s6u_rom) (mkst R (0x22a98 : word) m' s6u_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FWin w) ob i k)
   /\ getr R 13 = zw (P0 + (i + Z.of_nat k)) /\ getr R 1 = zw (P0 + (i + Z.of_nat k)) /\ getr R 9 = zw (P0 + (i + Z.of_nat k))
   /\ (forall q, reg_in q [1; 5; 6; 7; 9; 13; 29]%bv = false -> getr R q = getr regs q).
Proof.
  induction k as [|k IH]; intros SV m ob w i regs HK HM H5 H7 H13 H9 H29 Hk Hk17 Hw Hwk Hi Hik; [lia|].
  pose proof (ifp_win_b C) as Hwb. destruct (Hwb w ltac:(lia)) as [Hv0 Hv1].
  destruct (wtrip2 SV m ob w i (Z.of_nat (Datatypes.S k)) regs HK HM H5 H7 H13 H9 H29 ltac:(lia) ltac:(lia) ltac:(lia))
    as (R1 & Hms1 & HK1 & A5 & A7 & A13 & A9 & A29 & A1 & Hfr1).
  pose proof (MEMI_cp1 C SV m ob i (arr_get (is_window s) w) HM ltac:(lia) ltac:(lia)) as HM1.
  destruct k as [|k'].
  - replace (Z.of_nat 1 =? 1) with true in Hms1 by reflexivity.
    exists R1. eexists. split; [exact Hms1|]. split; [exact HK1|].
    split; [cbn [cblit fval from_succ]; exact HM1|].
    split; [rewrite A13; f_equal; lia|]. split; [rewrite A1; f_equal; lia|]. split; [rewrite A9; f_equal; lia| exact Hfr1].
  - replace (Z.of_nat (Datatypes.S (Datatypes.S k')) =? 1) with false in Hms1 by (symmetry; apply Z.eqb_neq; lia).
    destruct (IH SV _ _ (w + 1) (i + 1) R1 HK1 HM1 ltac:(rewrite A5; f_equal; lia) ltac:(rewrite A7; f_equal; lia) ltac:(rewrite A13; f_equal; lia)
                 ltac:(rewrite A9; f_equal; lia) ltac:(rewrite A29; f_equal; lia)
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (R2 & m2 & Hms2 & HK2 & HM2 & B13 & B1 & B9 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|]. split; [cbn [cblit fval from_succ]; exact HM2|].
    split; [rewrite B13; f_equal; lia|]. split; [rewrite B1; f_equal; lia|]. split; [rewrite B9; f_equal; lia|]. fr_chain2 Hfr2 Hfr1.
Qed.

Lemma wleg2 : wleg2_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof.
  intros SV m f regs HK HM Hfr H5 H7 H13 H9 H29 Hw1 HwN Hbeg HoN. cbv zeta.
  assert (HwnB : x_wnext X < 2 ^ 31) by (pose proof Hwnext1 as B; change (is_wnext s) with (x_wnext X) in B; exact B).
  destruct (wleg2_loop (Z.to_nat (x_wnext X)) SV m (f_ob f) 0 (f_out f) regs HK HM ltac:(rewrite Z.add_0_r; exact H5) ltac:(rewrite Z.add_0_r; exact H7)
              H13 H9 ltac:(rewrite H29; f_equal; lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))
    as (R & m' & Hms & HK' & HM' & A13 & A1 & A9 & Hfr').
  exists R, m'. split; [exact Hms|]. split; [exact HK'|].
  split; [rewrite cpn_ob, Hfr; exact HM'|]. rewrite cpn_out.
  split; [rewrite A13; f_equal; lia|]. split; [rewrite A1; f_equal; lia|]. split; [rewrite A9; f_equal; lia| exact Hfr'].
Qed.

Lemma w3_trip : forall SV m ob fr fout len regs,
  KR regs -> MEMI SV m ob ->
  getr regs 29 = zw (faddr WB P0 fr) -> getr regs 5 = zw (faddr WB P0 fr) -> getr regs 1 = zw (P0 + fout) -> getr regs 13 = zw (P0 + fout) ->
  getr regs 27 = zw len ->
  3 <= len < 2 ^ 17 -> 0 <= fout -> fout + 3 <= ON -> srcn_ok WN fout fr 3 ->
  let ob' := cblit (is_window s) fr ob fout 3 in
  exists R m', msteps s6u_segs (mkst regs (0x22c58 : word) m s6u_rom)
                 (mkst R (if 2 <? len - 3 then (0x22c58 : word) else (0x22cc8 : word)) m' s6u_rom)
   /\ KR R /\ MEMI SV m' ob'
   /\ getr R 29 = zw (faddr WB P0 (fr_add fr 3)) /\ getr R 5 = zw (faddr WB P0 (fr_add fr 3))
   /\ getr R 1 = zw (P0 + (fout + 3)) /\ getr R 13 = zw (P0 + (fout + 3)) /\ getr R 27 = zw (len - 3)
   /\ (forall q, reg_in q [1; 5; 6; 7; 9; 13; 23; 27; 29]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob fr fout len regs HK HM H29 H5 H1 H13 H27 Hlen Hfout Hfout3 Hsrc ob'.
  pose proof HK as HK'. kr_destr HK. clear_layout.
  assert (HWB : match fr with FWin _ => 0 < WB | FOut _ => True end) by (destruct fr; [apply HWpos; cbn in Hsrc; lia| exact I]).
  pose proof (srcn_src_ok fout fr 3 0 Hsrc ltac:(lia)) as S0. cbn [fr_add Z.of_nat] in S0. rewrite Z.add_0_r in S0.
  pose proof (faddr_range C fout fr S0 ltac:(lia)) as [Fa0 Fa1].
  assert (Fa2 : 1 <= faddr WB P0 fr) by (destruct fr; cbn in S0, HWB |- *; lia).
  pose proof (faddr_disj C fout fr S0 ltac:(lia)) as Fd.
  pose proof (fval_byte C SV m ob fout fr HM S0 ltac:(lia)) as [Fv0 Fv1].
  pose proof (src_read C SV m ob fout fr _ HM S0 ltac:(lia) eq_refl) as RD0.
  pose proof (MEMI_map_P SV m ob HM) as WP.
  symex s6u_segs fastC6 12%nat [false; false; false; false] [RVal (EVar 35%nat)]
    [(29, EVar 32%nat); (5, EVar 32%nat); (1, EAdd (EVar 33%nat) (EVar 34%nat)); (13, EAdd (EVar 33%nat) (EVar 34%nat)); (18, ELit 2); (8, ELit (-1))]
    [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
    [faddr WB P0 fr; P0; fout; fval (is_window s) ob fr] NoVals F0 F0'
    (mkst regs (0x22c58 : word) m s6u_rom) R1 HR1 Hfr1 Hms1.
  all: try side. all: guards.
  pose proof (MEMI_cp1 C SV m ob fout _ HM ltac:(lia) (conj Fv0 Fv1)) as HM1.
  clear WP RD0 Fd.
  set (m1 := wbytes m _ _) in Hms1, HM1. set (ob1 := arr_set ob fout _) in HM1.
  symex_reg HR1 (23%bv : reg) as A23. symex_reg HR1 (29%bv : reg) as A29. symex_reg HR1 (6%bv : reg) as A6. symex_reg HR1 (7%bv : reg) as A7.
  symex_reg HR1 (5%bv : reg) as A5. symex_reg HR1 (13%bv : reg) as A13.
  assert (A27 : getr R1 27 = zw len) by (rewrite (Hfr1 27%bv eq_refl); exact H27).
  assert (A18 : getr R1 18 = zw 2) by (rewrite (Hfr1 18%bv eq_refl); exact K18).
  assert (A8 : getr R1 8 = zw (-1)) by (rewrite (Hfr1 8%bv eq_refl); exact K8).
  pose proof (srcn_src_ok fout fr 3 1 Hsrc ltac:(lia)) as S1. cbn [fr_add Z.of_nat] in S1. change (Z.of_nat 1) with 1 in S1.
  pose proof (faddr_disj C (fout + 1) (from_succ fr) S1 ltac:(lia)) as Fd. rewrite faddr_succ in Fd.
  pose proof (fval_byte C SV m1 ob1 (fout + 1) (from_succ fr) HM1 S1 ltac:(lia)) as [Fv10 Fv11].
  pose proof (src_read C SV m1 ob1 (fout + 1) (from_succ fr) (faddr WB P0 fr + 1) HM1 S1 ltac:(lia) ltac:(rewrite faddr_succ; reflexivity)) as RD1.
  pose proof (MEMI_map_P SV m1 ob1 HM1) as WP.
  symex s6u_segs fastC6 6%nat [false; false] [RVal (EVar 35%nat)]
    [(23, EVar 32%nat); (29, EAdd (EVar 32%nat) (ELit 1)); (6, EAdd (EAdd (EVar 33%nat) (EVar 34%nat)) (ELit 1)); (7, EAdd (EVar 33%nat) (EVar 34%nat)); (8, ELit (-1))]
    [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
    [faddr WB P0 fr; P0; fout; fval (is_window s) ob1 (from_succ fr)] NoVals F0 F0'
    (mkst R1 (0x22c88 : word) m1 s6u_rom) R2 HR2 Hfr2 Hms2.
  all: try side. all: guards.
  pose proof (MEMI_cp1 C SV m1 ob1 (fout + 1) _ HM1 ltac:(lia) (conj Fv10 Fv11)) as HM2.
  clear WP RD1 Fd.
  replace (P0 + fout + 1) with (P0 + (fout + 1)) in Hms2 by lia.
  set (m2 := wbytes m1 _ _) in Hms2, HM2. set (ob2 := arr_set ob1 (fout + 1) _) in HM2.
  symex_reg HR2 (29%bv : reg) as B29. symex_reg HR2 (6%bv : reg) as B6.
  assert (B7 : getr R2 7 = zw (P0 + fout)) by (rewrite (Hfr2 7%bv eq_refl); exact A7).
  assert (B5 : getr R2 5 = zw (faddr WB P0 fr)) by (rewrite (Hfr2 5%bv eq_refl); exact A5).
  assert (B13 : getr R2 13 = zw (P0 + fout)) by (rewrite (Hfr2 13%bv eq_refl); exact A13).
  assert (B23 : getr R2 23 = zw (faddr WB P0 fr)) by (rewrite (Hfr2 23%bv eq_refl); exact A23).
  assert (B27 : getr R2 27 = zw len) by (rewrite (Hfr2 27%bv eq_refl); exact A27).
  assert (B18 : getr R2 18 = zw 2) by (rewrite (Hfr2 18%bv eq_refl); exact A18).
  pose proof (srcn_src_ok fout fr 3 2 Hsrc ltac:(lia)) as S2. cbn [fr_add Z.of_nat] in S2. change (Z.of_nat 2) with 2 in S2.
  pose proof (faddr_disj C (fout + 2) (from_succ (from_succ fr)) S2 ltac:(lia)) as Fd. rewrite !faddr_succ in Fd.
  pose proof (fval_byte C SV m2 ob2 (fout + 2) (from_succ (from_succ fr)) HM2 S2 ltac:(lia)) as [Fv20 Fv21].
  pose proof (src_read C SV m2 ob2 (fout + 2) (from_succ (from_succ fr)) (faddr WB P0 fr + 2) HM2 S2 ltac:(lia) ltac:(rewrite !faddr_succ; lia)) as RD2.
  pose proof (MEMI_map_P SV m2 ob2 HM2) as WP.
  assert (Eob : ob' = arr_set ob2 (fout + 2) (fval (is_window s) ob2 (from_succ (from_succ fr)))).
  { subst ob' ob2 ob1. cbn [cblit]. f_equal. lia. }
  rewrite Eob. clear Eob.
  destruct (Z.ltb_spec 2 (len - 3)) as [Hc|Hc].
  - symex s6u_segs fastC6 8%nat [true] [RVal (EVar 35%nat)]
      [(29, EAdd (EVar 32%nat) (ELit 2)); (6, EAdd (EAdd (EVar 33%nat) (EVar 34%nat)) (ELit 2)); (7, EAdd (EVar 33%nat) (EVar 34%nat));
       (5, EVar 32%nat); (13, EAdd (EVar 33%nat) (EVar 34%nat)); (23, EVar 32%nat); (27, EVar 36%nat); (18, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256); (36%nat, 2^17)] NoRegions
      [faddr WB P0 fr; P0; fout; fval (is_window s) ob2 (from_succ (from_succ fr)); len] NoVals F0 F0'
      (mkst R2 (0x22ca0 : word) m2 s6u_rom) R3 HR3 Hfr3 Hms3.
    all: try side. all: guards.
    pose proof (MEMI_cp1 C SV m2 ob2 (fout + 2) _ HM2 ltac:(lia) (conj Fv20 Fv21)) as HM3.
    replace (P0 + fout + 2) with (P0 + (fout + 2)) in Hms3 by lia.
    assert (HF : forall q, reg_in q [1; 5; 6; 7; 9; 13; 23; 27; 29]%bv = false -> getr R3 q = getr regs q) by fr_chain3 Hfr3 Hfr2 Hfr1.
    exists R3. eexists. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [exact HM3|].
    symex_reg HR3 (29%bv : reg) as C29. symex_reg HR3 (5%bv : reg) as C5. symex_reg HR3 (1%bv : reg) as C1.
    symex_reg HR3 (13%bv : reg) as C13. symex_reg HR3 (27%bv : reg) as C27.
    split; [rewrite C29; f_equal; rewrite faddr_add; cbn; lia|]. split; [rewrite C5; f_equal; rewrite faddr_add; cbn; lia|].
    split; [rewrite C1; f_equal; lia|]. split; [rewrite C13; f_equal; lia|].
    split; [rewrite C27; f_equal; rewrite ?szwrap32_small by lia; lia|]. exact HF.
  - symex s6u_segs fastC6 10%nat [false] [RVal (EVar 35%nat)]
      [(29, EAdd (EVar 32%nat) (ELit 2)); (6, EAdd (EAdd (EVar 33%nat) (EVar 34%nat)) (ELit 2)); (7, EAdd (EVar 33%nat) (EVar 34%nat));
       (5, EVar 32%nat); (13, EAdd (EVar 33%nat) (EVar 34%nat)); (23, EVar 32%nat); (27, EVar 36%nat); (18, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256); (36%nat, 2^17)] NoRegions
      [faddr WB P0 fr; P0; fout; fval (is_window s) ob2 (from_succ (from_succ fr)); len] NoVals F0 F0'
      (mkst R2 (0x22ca0 : word) m2 s6u_rom) R3 HR3 Hfr3 Hms3.
    all: try side. all: guards.
    pose proof (MEMI_cp1 C SV m2 ob2 (fout + 2) _ HM2 ltac:(lia) (conj Fv20 Fv21)) as HM3.
    replace (P0 + fout + 2) with (P0 + (fout + 2)) in Hms3 by lia.
    assert (HF : forall q, reg_in q [1; 5; 6; 7; 9; 13; 23; 27; 29]%bv = false -> getr R3 q = getr regs q) by fr_chain3 Hfr3 Hfr2 Hfr1.
    exists R3. eexists. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [exact HM3|].
    symex_reg HR3 (29%bv : reg) as C29. symex_reg HR3 (5%bv : reg) as C5. symex_reg HR3 (1%bv : reg) as C1.
    symex_reg HR3 (13%bv : reg) as C13. symex_reg HR3 (27%bv : reg) as C27.
    split; [rewrite C29; f_equal; rewrite faddr_add; cbn; lia|]. split; [rewrite C5; f_equal; rewrite faddr_add; cbn; lia|].
    split; [rewrite C1; f_equal; lia|]. split; [rewrite C13; f_equal; lia|].
    split; [rewrite C27; f_equal; rewrite ?szwrap32_small by lia; lia|]. exact HF.
Qed.

Lemma w3_loop : forall k SV m ob fr fout rem regs,
  KR regs -> MEMI SV m ob ->
  getr regs 29 = zw (faddr WB P0 fr) -> getr regs 5 = zw (faddr WB P0 fr) -> getr regs 1 = zw (P0 + fout) -> getr regs 13 = zw (P0 + fout) ->
  getr regs 27 = zw (3 * Z.of_nat k + rem) ->
  (1 <= k)%nat -> 0 <= rem <= 2 -> 3 * Z.of_nat k + rem < 2 ^ 17 -> 0 <= fout -> fout + 3 * Z.of_nat k <= ON ->
  srcn_ok WN fout fr (3 * Z.of_nat k) ->
  exists R m', msteps s6u_segs (mkst regs (0x22c58 : word) m s6u_rom) (mkst R (0x22cc8 : word) m' s6u_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) fr ob fout (3 * k))
   /\ getr R 29 = zw (faddr WB P0 (fr_add fr (3 * k))) /\ getr R 1 = zw (P0 + (fout + 3 * Z.of_nat k)) /\ getr R 27 = zw rem
   /\ (forall q, reg_in q [1; 5; 6; 7; 9; 13; 23; 27; 29]%bv = false -> getr R q = getr regs q).
Proof.
  induction k as [|k IH]; intros SV m ob fr fout rem regs HK HM H29 H5 H1 H13 H27 Hk Hrem Hlen Hfout HfoutN Hsrc; [lia|].
  assert (Hs3 : srcn_ok WN fout fr 3) by (destruct fr; cbn in Hsrc |- *; lia).
  destruct (w3_trip SV m ob fr fout (3 * Z.of_nat (Datatypes.S k) + rem) regs HK HM H29 H5 H1 H13 H27 ltac:(lia) Hfout ltac:(lia) Hs3)
    as (R1 & m1 & Hms1 & HK1 & HM1 & A29 & A5 & A1 & A13 & A27 & Hfr1).
  destruct k as [|k'].
  - replace (2 <? 3 * Z.of_nat 1 + rem - 3) with false in Hms1 by (symmetry; apply Z.ltb_ge; lia).
    exists R1, m1. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HM1|].
    split; [exact A29|]. split; [rewrite A1; f_equal; lia|]. split; [rewrite A27; f_equal; lia| exact Hfr1].
  - replace (2 <? 3 * Z.of_nat (Datatypes.S (Datatypes.S k')) + rem - 3) with true in Hms1 by (symmetry; apply Z.ltb_lt; lia).
    destruct (IH SV m1 (cblit (is_window s) fr ob fout 3) (fr_add fr 3) (fout + 3) rem R1 HK1 HM1
                 A29 A5 A1 A13 ltac:(rewrite A27; f_equal; lia) ltac:(lia) Hrem ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & m2 & Hms2 & HK2 & HM2 & B29 & B1 & B27 & Hfr2).
    { pose proof (srcn_ok_adv fout fr (3 * Z.of_nat (Datatypes.S (Datatypes.S k'))) 3 Hsrc ltac:(lia)) as H.
      replace (3 * Z.of_nat (Datatypes.S (Datatypes.S k')) - Z.of_nat 3) with (3 * Z.of_nat (Datatypes.S k')) in H by lia.
      replace (fout + Z.of_nat 3) with (fout + 3) in H by lia. exact H. }
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|].
    split; [replace (3 * Datatypes.S (Datatypes.S k'))%nat with (3 + 3 * Datatypes.S k')%nat by lia; rewrite cblit_add;
            replace (fout + Z.of_nat 3) with (fout + 3) by lia; exact HM2|].
    assert (EFR : fr_add fr (3 * Datatypes.S (Datatypes.S k')) = fr_add (fr_add fr 3) (3 * Datatypes.S k')).
    { replace (3 * Datatypes.S (Datatypes.S k'))%nat with (3 + 3 * Datatypes.S k')%nat by lia. apply fr_add_add. }
    rewrite EFR. split; [exact B29|]. split; [rewrite B1; f_equal; lia|]. split; [exact B27|].
    fr_chain2 Hfr2 Hfr1.
Qed.

Lemma w3_tail : forall SV m ob fr fout rem regs,
  KR regs -> MEMI SV m ob ->
  getr regs 29 = zw (faddr WB P0 fr) -> getr regs 1 = zw (P0 + fout) -> getr regs 27 = zw rem ->
  0 <= rem <= 2 -> 0 <= fout -> fout + rem <= ON -> srcn_ok WN fout fr rem ->
  exists R m', msteps s6u_segs (mkst regs (0x22cc8 : word) m s6u_rom) (mkst R (0x22820 : word) m' s6u_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) fr ob fout (Z.to_nat rem))
   /\ getr R 22 = zw (P0 + (fout + rem))
   /\ (forall q, reg_in q [5; 13; 22]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob fr fout rem regs HK HM H29 H1 H27 Hrem Hfout HfoutN Hsrc.
  pose proof HK as HK'. kr_destr HK. clear_layout. pose proof (MEMI_len SV m ob HM) as HL.
  assert (Fa : 0 <= faddr WB P0 fr < 2 ^ 63) by (destruct fr; cbn in Hsrc |- *; lia).
  destruct (Z.eq_dec rem 0) as [R0E|RNZ].
  - subst rem.
    symex s6u_segs fastC6 4%nat [true] NoReads [(29, EVar 32%nat); (1, EAdd (EVar 33%nat) (EVar 34%nat)); (27, ELit 0)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32)] NoRegions [faddr WB P0 fr; P0; fout] NoVals F0 F0'
      (mkst regs (0x22cc8 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R, m. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [cbn [Z.to_nat cblit]; exact HM|].
    split; [symex_reg HR (22%bv : reg) as A; rewrite A; f_equal; lia| fr_weak Hfr].
  - assert (HWB : match fr with FWin _ => 0 < WB | FOut _ => True end) by (destruct fr; [apply HWpos; cbn in Hsrc; lia| exact I]).
    pose proof (srcn_src_ok fout fr rem 0 Hsrc ltac:(lia)) as S0. cbn [fr_add Z.of_nat] in S0. rewrite Z.add_0_r in S0.
    pose proof (faddr_range C fout fr S0 ltac:(lia)) as [Fa0 Fa1].
    assert (Fa2 : 1 <= faddr WB P0 fr) by (destruct fr; cbn in S0, HWB |- *; lia).
    pose proof (faddr_disj C fout fr S0 ltac:(lia)) as Fd.
    pose proof (fval_byte C SV m ob fout fr HM S0 ltac:(lia)) as [Fv0 Fv1].
    pose proof (src_read C SV m ob fout fr _ HM S0 ltac:(lia) eq_refl) as RD0.
    pose proof (MEMI_map_P SV m ob HM) as WP.
    destruct (Z.eq_dec rem 1) as [R1E|R2E].
    + subst rem.
      symex s6u_segs fastC6 8%nat [false; false; false; true] [RVal (EVar 35%nat)]
        [(29, EVar 32%nat); (1, EAdd (EVar 33%nat) (EVar 34%nat)); (27, ELit 1); (18, ELit 2); (8, ELit (-1))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
        [faddr WB P0 fr; P0; fout; fval (is_window s) ob fr] NoVals F0 F0'
        (mkst regs (0x22cc8 : word) m s6u_rom) R HR Hfr Hms.
      all: try side. all: guards.
      exists R. eexists. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      split; [cbn [Z.to_nat Pos.to_nat cblit]; apply (MEMI_cp1 C); [exact HM | lia | lia]|].
      split; [symex_reg HR (22%bv : reg) as A; rewrite A; f_equal; lia| fr_weak Hfr].
    + assert (R2 : rem = 2) by lia. subst rem.
      symex s6u_segs fastC6 8%nat [false; false; false; false] [RVal (EVar 35%nat)]
        [(29, EVar 32%nat); (1, EAdd (EVar 33%nat) (EVar 34%nat)); (27, ELit 2); (18, ELit 2); (8, ELit (-1))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
        [faddr WB P0 fr; P0; fout; fval (is_window s) ob fr] NoVals F0 F0'
        (mkst regs (0x22cc8 : word) m s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try side. all: guards.
      pose proof (MEMI_cp1 C SV m ob fout _ HM ltac:(lia) (conj Fv0 Fv1)) as HM1.
      clear WP RD0 Fd.
      set (m1 := wbytes m _ _) in Hms1, HM1. set (ob1 := arr_set ob fout _) in HM1.
      symex_reg HR1 (13%bv : reg) as A13. symex_reg HR1 (22%bv : reg) as A22.
      assert (A1 : getr R1 1 = zw (P0 + fout)) by (rewrite (Hfr1 1%bv eq_refl); exact H1).
      assert (A8 : getr R1 8 = zw (-1)) by (rewrite (Hfr1 8%bv eq_refl); exact K8).
      pose proof (srcn_src_ok fout fr 2 1 Hsrc ltac:(lia)) as S1. cbn [fr_add Z.of_nat] in S1. change (Z.of_nat 1) with 1 in S1.
      pose proof (faddr_disj C (fout + 1) (from_succ fr) S1 ltac:(lia)) as Fd. rewrite faddr_succ in Fd.
      pose proof (fval_byte C SV m1 ob1 (fout + 1) (from_succ fr) HM1 S1 ltac:(lia)) as [Fv10 Fv11].
      pose proof (src_read C SV m1 ob1 (fout + 1) (from_succ fr) (faddr WB P0 fr + 1) HM1 S1 ltac:(lia) ltac:(rewrite faddr_succ; reflexivity)) as RD1.
      pose proof (MEMI_map_P SV m1 ob1 HM1) as WP.
      symex s6u_segs fastC6 8%nat [false; false] [RVal (EVar 35%nat)]
        [(13, EAdd (EVar 32%nat) (ELit 1)); (22, EAdd (EAdd (EVar 33%nat) (EVar 34%nat)) (ELit 1)); (1, EAdd (EVar 33%nat) (EVar 34%nat)); (8, ELit (-1))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 256)] NoRegions
        [faddr WB P0 fr; P0; fout; fval (is_window s) ob1 (from_succ fr)] NoVals F0 F0'
        (mkst R1 (0x22ce8 : word) m1 s6u_rom) R2 HR2 Hfr2 Hms2.
      all: try side. all: guards.
      pose proof (MEMI_cp1 C SV m1 ob1 (fout + 1) _ HM1 ltac:(lia) (conj Fv10 Fv11)) as HM2.
      replace (P0 + fout + 1) with (P0 + (fout + 1)) in Hms2 by lia.
      assert (HF : forall q, reg_in q [5; 13; 22]%bv = false -> getr R2 q = getr regs q) by fr_chain2 Hfr2 Hfr1.
      exists R2. eexists. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
      split; [subst ob1; cbn [Z.to_nat Pos.to_nat cblit]; exact HM2|].
      split; [symex_reg HR2 (22%bv : reg) as A; rewrite A; f_equal; lia| exact HF].
Qed.

Lemma w3_pre : forall m a o regs,
  KR regs -> getr regs 29 = zw a -> getr regs 1 = zw o -> 0 <= a < 2 ^ 63 -> 0 <= o < 2 ^ 63 ->
  exists R, msteps s6u_segs (mkst regs (0x22c50 : word) m s6u_rom) (mkst R (0x22c58 : word) m s6u_rom)
   /\ KR R /\ getr R 13 = zw o /\ getr R 5 = zw a /\ (forall q, reg_in q [5; 13]%bv = false -> getr R q = getr regs q).
Proof.
  intros m a o regs HK H29 H1 Ha Ho. pose proof HK as HK'. kr_destr HK. clear_layout.
  symex s6u_segs fastC6 2%nat NoDirs NoReads [(29, EVar 32%nat); (1, EVar 33%nat)] [(32%nat, 2^63); (33%nat, 2^63)] NoRegions [a; o] NoVals F0 F0'
    (mkst regs (0x22c50 : word) m s6u_rom) R HR Hfr Hms.
  all: try side.
  exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
  split; [symex_reg HR (13%bv : reg) as A; rewrite A; reflexivity|].
  split; [symex_reg HR (5%bv : reg) as A'; rewrite A'; reflexivity| fr_weak Hfr].
Qed.

Lemma tail_sim : forall SV m f regs,
  KR regs -> MEMI SV m (f_ob f) ->
  getr regs 29 = zw (faddr WB P0 (f_from f)) -> getr regs 1 = zw (P0 + f_out f) -> getr regs 27 = zw (f_len f) ->
  0 <= f_len f <= 2 -> 0 <= f_out f -> f_out f + f_len f <= ON -> srcn_ok WN (f_out f) (f_from f) (f_len f) ->
  let f' := copy_tail X f in
  exists R m', msteps s6u_segs (mkst regs (0x22cc8 : word) m s6u_rom) (mkst R (0x22820 : word) m' s6u_rom)
   /\ KR R /\ MEMI SV m' (f_ob f') /\ getr R 22 = zw (P0 + f_out f')
   /\ (forall q, reg_in q [5; 13; 22]%bv = false -> getr R q = getr regs q)
   /\ f_in f' = f_in f /\ f_hold f' = f_hold f /\ f_bits f' = f_bits f /\ f_out f' = f_out f + f_len f /\ f_dist f' = f_dist f.
Proof.
  intros SV m f regs HK HM H29 H1 H27 Hlen Hfo Hfon Hsrc f'. subst f'. rewrite copy_tail_cpn by lia.
  destruct (w3_tail SV m (f_ob f) (f_from f) (f_out f) (f_len f) regs HK HM H29 H1 H27 Hlen Hfo Hfon Hsrc)
    as (R & m' & Hms & HK' & HM' & A22 & Hfr).
  exists R, m'. split; [exact Hms|]. split; [exact HK'|].
  rewrite cpn_ob, cpn_in, cpn_hold, cpn_bits, cpn_out, cpn_dist. cbn [x_window ffx_of].
  split; [exact HM'|]. split; [rewrite A22; f_equal; lia|]. split; [exact Hfr|]. repeat split; lia.
Qed.

Lemma w3 : w3_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof.
  intros SV m f regs HK HM H29 H1 H27 Hlen Hbeg Hfon Hsrc. cbv zeta. rewrite copy_while3_cpn by lia.
  pose proof (proj1 (ffx_beg_range C)) as Hxbeg0'.
  pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as Hm3.
  pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)) as Hq0.
  destruct (Z.ltb_spec (f_len f) 3) as [Hlt|Hge].
  -
    rewrite (Z.div_small (f_len f) 3), (Z.mod_small (f_len f) 3) by lia. cbn [Z.mul Z.to_nat cpn]. rewrite fset_len_id.
    destruct (tail_sim SV m f regs HK HM H29 H1 H27 ltac:(lia) ltac:(lia) Hfon Hsrc) as (R2 & m2 & Hms2 & HK2 & HM2 & B22 & Hfr2 & E).
    exists R2, m2. split; [exact Hms2|]. split; [exact HK2|]. split; [exact HM2|]. split; [exact B22|]. split; [fr_weak Hfr2 | exact E].
  - assert (Fa : 0 <= faddr WB P0 (f_from f) < 2 ^ 63) by (destruct (f_from f); cbn in Hsrc |- *; lia).
    destruct (w3_pre m (faddr WB P0 (f_from f)) (P0 + f_out f) regs HK H29 H1 Fa ltac:(lia)) as (R1 & Hms1 & HK1 & A13 & A5 & Hfr1).
    set (k := Z.to_nat (f_len f / 3)).
    assert (Hk : (1 <= k)%nat) by (subst k; assert (1 <= f_len f / 3) by (apply Z.div_le_lower_bound; lia); lia).
    assert (Hk3 : 3 * Z.of_nat k = 3 * (f_len f / 3)) by (subst k; lia).
    destruct (w3_loop k SV m (f_ob f) (f_from f) (f_out f) (f_len f mod 3) R1 HK1 HM ltac:(via1 Hfr1 H29) A5 ltac:(via1 Hfr1 H1) A13
                ltac:(rewrite (Hfr1 27%bv eq_refl), H27; f_equal; lia) Hk ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(apply (srcn_ok_le _ _ _ _ Hsrc); lia))
      as (R3 & m3 & Hms3 & HK3 & HM3 & C29 & C1 & C27 & Hfr3).
    set (f1 := fset_len (cpn X (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3)).
    assert (Ef1 : f_ob f1 = cblit (is_window s) (f_from f) (f_ob f) (f_out f) (3 * k) /\ f_from f1 = fr_add (f_from f) (3 * k)
                  /\ f_out f1 = f_out f + 3 * Z.of_nat k /\ f_len f1 = f_len f mod 3
                  /\ f_in f1 = f_in f /\ f_hold f1 = f_hold f /\ f_bits f1 = f_bits f /\ f_dist f1 = f_dist f).
    { subst f1. destruct (fset_len_fields (cpn X (Z.to_nat (3 * (f_len f / 3))) f) (f_len f mod 3)) as (-> & -> & -> & -> & -> & -> & -> & ->).
      rewrite cpn_ob, cpn_from, cpn_out, cpn_in, cpn_hold, cpn_bits, cpn_dist.
      replace (Z.to_nat (3 * (f_len f / 3))) with (3 * k)%nat by lia. cbn [x_window ffx_of]. repeat split; lia. }
    destruct Ef1 as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (tail_sim SV m3 f1 R3 HK3 ltac:(rewrite E1; exact HM3) ltac:(rewrite E2; exact C29) ltac:(rewrite E3; exact C1) ltac:(rewrite E4; exact C27)
                ltac:(rewrite E4; lia) ltac:(lia) ltac:(rewrite E3, E4; lia)
                ltac:(rewrite E3, E2, E4; replace (f_out f + 3 * Z.of_nat k) with (f_out f + Z.of_nat (3 * k)) by lia;
                      replace (f_len f mod 3) with (f_len f - Z.of_nat (3 * k)) by lia; apply srcn_ok_adv; [exact Hsrc | lia]))
      as (R5 & m5 & Hms5 & HK5 & HM5 & D22 & Hfr5 & E).
    exists R5, m5. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms3 | exact Hms5]. }
    split; [exact HK5|]. split; [exact HM5|]. split; [exact D22|].
    split; [fr_chain3 Hfr5 Hfr3 Hfr1|].
    rewrite E5, E6, E7, E3, E8, E4 in E. destruct E as (? & ? & ? & ? & ?). repeat split; try assumption. lia.
Qed.

Lemma w3A : w3A_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB).
Proof.
  intros m a o len regs HK H29 H22 H27 Hlen Ho. pose proof HK as HK'. kr_destr HK. clear_layout.
  destruct (Z.ltb_spec len 3) as [L3|L3].
  - symex s6u_segs fastC6 3%nat [true] NoReads [(22, EVar 32%nat); (27, EVar 33%nat)] [(32%nat, 2^63); (33%nat, 2^17)] NoRegions [o; len] NoVals F0 F0'
      (mkst regs (0x22c44 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [rewrite (Hfr 29%bv eq_refl); exact H29|]. split; [symex_reg HR (1%bv : reg) as A; rewrite A; reflexivity| fr_weak Hfr].
  - symex s6u_segs fastC6 3%nat [false] NoReads [(22, EVar 32%nat); (27, EVar 33%nat)] [(32%nat, 2^63); (33%nat, 2^17)] NoRegions [o; len] NoVals F0 F0'
      (mkst regs (0x22c44 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [rewrite (Hfr 29%bv eq_refl); exact H29|]. split; [symex_reg HR (1%bv : reg) as A; rewrite A; reflexivity| fr_weak Hfr].
Qed.

Lemma w3B : w3B_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof.
  intros SV m ob o len regs HK HM Hslot H13 H27 Hlen Ho.
  pose proof (fcells_get s6u_segs sp m SV _ _ _ (MEMI_saved SV m ob HM) Hslot) as Hc40. unfold cell in Hc40.
  pose proof HK as HK'. kr_destr HK. pose proof Hmap_sp as Wsp. unfold mapped in Wsp. clear_layout. clear HM.
  destruct (Z.ltb_spec len 3) as [L3|L3].
  - symex s6u_segs fastC6 5%nat [true] [RVal (EVar 34%nat)] [(13, EVar 32%nat); (27, EVar 33%nat); (2, EVar 35%nat)]
      [(32%nat, 2^63); (33%nat, 2^17); (34%nat, 2^63); (35%nat, 2^63)] NoRegions [o; len; WB; sp] NoVals F0 F0'
      (mkst regs (0x22d08 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (29%bv : reg) as A; rewrite A; reflexivity|]. split; [symex_reg HR (1%bv : reg) as A'; rewrite A'; reflexivity| fr_weak Hfr].
  - symex s6u_segs fastC6 5%nat [false] [RVal (EVar 34%nat)] [(13, EVar 32%nat); (27, EVar 33%nat); (2, EVar 35%nat)]
      [(32%nat, 2^63); (33%nat, 2^17); (34%nat, 2^63); (35%nat, 2^63)] NoRegions [o; len; WB; sp] NoVals F0 F0'
      (mkst regs (0x22d08 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (29%bv : reg) as A; rewrite A; reflexivity|]. split; [symex_reg HR (1%bv : reg) as A'; rewrite A'; reflexivity| fr_weak Hfr].
Qed.

Lemma w3J : w3J_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB).
Proof.
  intros m dist fout len regs HK H13 H1 H23 H27 Hlen Hdist Hfout Hdf. pose proof HK as HK'. kr_destr HK. clear_layout.
  destruct (Z.ltb_spec len 3) as [L3|L3].
  - symex s6u_segs fastC6 5%nat [false; false] NoReads [(13, EAdd (EVar 32%nat) (EVar 33%nat)); (1, EAdd (EVar 32%nat) (EVar 33%nat)); (23, EVar 34%nat); (27, EVar 35%nat)]
      [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^17)] NoRegions [P0; fout; dist; len] NoVals F0 F0'
      (mkst regs (0x22c30 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (29%bv : reg) as A; rewrite A; f_equal; lia|]. split; [rewrite (Hfr 1%bv eq_refl); exact H1| fr_weak Hfr].
  - symex s6u_segs fastC6 5%nat [false; true] NoReads [(13, EAdd (EVar 32%nat) (EVar 33%nat)); (1, EAdd (EVar 32%nat) (EVar 33%nat)); (23, EVar 34%nat); (27, EVar 35%nat)]
      [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^17)] NoRegions [P0; fout; dist; len] NoVals F0 F0'
      (mkst regs (0x22c30 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [symex_reg HR (29%bv : reg) as A; rewrite A; f_equal; lia|]. split; [rewrite (Hfr 1%bv eq_refl); exact H1| fr_weak Hfr].
Qed.

Lemma do3_trip : forall SV m ob dist fo0 i len regs,
  KR regs -> MEMI SV m ob ->
  getr regs 22 = zw (P0 + fo0) -> getr regs 29 = zw (P0 + fo0 - dist) -> getr regs 5 = zw i -> getr regs 27 = zw len ->
  3 <= len < 2 ^ 17 -> 1 <= dist < 2 ^ 17 -> dist <= fo0 -> 0 <= i < 2 ^ 32 -> fo0 + i + 3 <= ON ->
  let fout := fo0 + i in
  let ob' := cblit (is_window s) (FOut (fout - dist)) ob fout 3 in
  exists R m', msteps s6u_segs (mkst regs (0x22ac0 : word) m s6u_rom)
                 (mkst R (if 2 <? len - 3 then (0x22ac0 : word) else (0x22b14 : word)) m' s6u_rom)
   /\ KR R /\ MEMI SV m' ob'
   /\ getr R 5 = zw (i + 3) /\ getr R 27 = zw (len - 3)
   /\ (forall q, reg_in q [5; 6; 7; 9; 13; 23; 27]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob dist fo0 i len regs HK HM H22 H29 H5 H27 Hlen Hdist Hdf Hi Hfo3 fout ob'. subst fout.
  pose proof HK as HK'. kr_destr HK. clear_layout.
  set (fr := FOut (fo0 + i - dist)) in ob'.
  assert (Hsrc : srcn_ok WN (fo0 + i) fr 3) by (subst fr; cbn; lia).
  pose proof (srcn_src_ok (fo0 + i) fr 3 0 Hsrc ltac:(lia)) as S0. cbn [fr_add Z.of_nat] in S0. rewrite Z.add_0_r in S0.
  pose proof (faddr_disj C (fo0 + i) fr S0 ltac:(lia)) as Fd.
  pose proof (fval_byte C SV m ob (fo0 + i) fr HM S0 ltac:(lia)) as [Fv0 Fv1].
  pose proof (src_read C SV m ob (fo0 + i) fr (P0 + fo0 - dist + i) HM S0 ltac:(lia) ltac:(subst fr; cbn [faddr]; lia)) as RD0.
  pose proof (MEMI_map_P SV m ob HM) as WP.
  symex s6u_segs fastC6 10%nat [false; false; false; false] [RVal (EVar 36%nat)]
    [(22, EAdd (EVar 32%nat) (EVar 33%nat)); (29, ESub (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 34%nat)); (5, EVar 35%nat); (18, ELit 2); (8, ELit (-1))]
    [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^32); (36%nat, 256)] NoRegions
    [P0; fo0; dist; i; fval (is_window s) ob fr] NoVals F0 F0'
    (mkst regs (0x22ac0 : word) m s6u_rom) R1 HR1 Hfr1 Hms1.
  all: try side. all: guards.
  pose proof (MEMI_cp1 C SV m ob (fo0 + i) _ HM ltac:(lia) (conj Fv0 Fv1)) as HM1.
  clear WP RD0 Fd.
  replace (P0 + fo0 + i) with (P0 + (fo0 + i)) in Hms1 by lia.
  set (m1 := wbytes m _ _) in Hms1, HM1. set (ob1 := arr_set ob (fo0 + i) _) in HM1.
  symex_reg HR1 (7%bv : reg) as A7. symex_reg HR1 (6%bv : reg) as A6. symex_reg HR1 (9%bv : reg) as A9. symex_reg HR1 (13%bv : reg) as A13.
  assert (A8 : getr R1 8 = zw (-1)) by (rewrite (Hfr1 8%bv eq_refl); exact K8).
  pose proof (srcn_src_ok (fo0 + i) fr 3 1 Hsrc ltac:(lia)) as S1. cbn [fr_add Z.of_nat] in S1. change (Z.of_nat 1) with 1 in S1.
  pose proof (faddr_disj C (fo0 + i + 1) (from_succ fr) S1 ltac:(lia)) as Fd. rewrite faddr_succ in Fd.
  pose proof (fval_byte C SV m1 ob1 (fo0 + i + 1) (from_succ fr) HM1 S1 ltac:(lia)) as [Fv10 Fv11].
  pose proof (src_read C SV m1 ob1 (fo0 + i + 1) (from_succ fr) (P0 + fo0 - dist + i + 1) HM1 S1 ltac:(lia)
                ltac:(rewrite faddr_succ; subst fr; cbn [faddr]; lia)) as RD1.
  pose proof (MEMI_map_P SV m1 ob1 HM1) as WP.
  symex s6u_segs fastC6 6%nat [false; false] [RVal (EVar 36%nat)]
    [(7, EAdd (EAdd (ESub (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 34%nat)) (EVar 35%nat)) (ELit 1));
     (6, EAdd (ESub (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 34%nat)) (EVar 35%nat));
     (9, EAdd (EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 35%nat)) (ELit 1)); (13, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 35%nat)); (8, ELit (-1))]
    [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^32); (36%nat, 256)] NoRegions
    [P0; fo0; dist; i; fval (is_window s) ob1 (from_succ fr)] NoVals F0 F0'
    (mkst R1 (0x22ae8 : word) m1 s6u_rom) R2 HR2 Hfr2 Hms2.
  all: try side. all: guards.
  pose proof (MEMI_cp1 C SV m1 ob1 (fo0 + i + 1) _ HM1 ltac:(lia) (conj Fv10 Fv11)) as HM2.
  clear WP RD1 Fd.
  replace (P0 + fo0 + i + 1) with (P0 + (fo0 + i + 1)) in Hms2 by lia.
  set (m2 := wbytes m1 _ _) in Hms2, HM2. set (ob2 := arr_set ob1 (fo0 + i + 1) _) in HM2.
  symex_reg HR2 (6%bv : reg) as B6. symex_reg HR2 (13%bv : reg) as B13.
  assert (B27 : getr R2 27 = zw len) by (rewrite (Hfr2 27%bv eq_refl), (Hfr1 27%bv eq_refl); exact H27).
  assert (B5 : getr R2 5 = zw i) by (rewrite (Hfr2 5%bv eq_refl), (Hfr1 5%bv eq_refl); exact H5).
  assert (B18 : getr R2 18 = zw 2) by (rewrite (Hfr2 18%bv eq_refl), (Hfr1 18%bv eq_refl); exact K18).
  pose proof (srcn_src_ok (fo0 + i) fr 3 2 Hsrc ltac:(lia)) as S2. cbn [fr_add Z.of_nat] in S2. change (Z.of_nat 2) with 2 in S2.
  pose proof (faddr_disj C (fo0 + i + 2) (from_succ (from_succ fr)) S2 ltac:(lia)) as Fd. rewrite !faddr_succ in Fd.
  pose proof (fval_byte C SV m2 ob2 (fo0 + i + 2) (from_succ (from_succ fr)) HM2 S2 ltac:(lia)) as [Fv20 Fv21].
  pose proof (src_read C SV m2 ob2 (fo0 + i + 2) (from_succ (from_succ fr)) (P0 + fo0 - dist + i + 2) HM2 S2 ltac:(lia)
                ltac:(rewrite !faddr_succ; subst fr; cbn [faddr]; lia)) as RD2.
  pose proof (MEMI_map_P SV m2 ob2 HM2) as WP.
  assert (Eob : ob' = arr_set ob2 (fo0 + i + 2) (fval (is_window s) ob2 (from_succ (from_succ fr)))).
  { subst ob' ob2 ob1. cbn [cblit]. f_equal. lia. }
  rewrite Eob. clear Eob.
  destruct (Z.ltb_spec 2 (len - 3)) as [Hc|Hc].
  - symex s6u_segs fastC6 5%nat [true] [RVal (EVar 36%nat)]
      [(6, EAdd (EAdd (ESub (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 34%nat)) (EVar 35%nat)) (ELit 2));
       (13, EAdd (EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 35%nat)) (ELit 2)); (27, EVar 37%nat); (5, EVar 35%nat); (18, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^32); (36%nat, 256); (37%nat, 2^17)] NoRegions
      [P0; fo0; dist; i; fval (is_window s) ob2 (from_succ (from_succ fr)); len] NoVals F0 F0'
      (mkst R2 (0x22b00 : word) m2 s6u_rom) R3 HR3 Hfr3 Hms3.
    all: try side. all: guards.
    pose proof (MEMI_cp1 C SV m2 ob2 (fo0 + i + 2) _ HM2 ltac:(lia) (conj Fv20 Fv21)) as HM3.
    replace (P0 + fo0 + i + 2) with (P0 + (fo0 + i + 2)) in Hms3 by lia.
    assert (HF : forall q, reg_in q [5; 6; 7; 9; 13; 23; 27]%bv = false -> getr R3 q = getr regs q) by fr_chain3 Hfr3 Hfr2 Hfr1.
    exists R3. eexists. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [exact HM3|].
    symex_reg HR3 (5%bv : reg) as C5. symex_reg HR3 (27%bv : reg) as C27.
    split; [rewrite C5; f_equal; lia|]. split; [rewrite C27; f_equal; rewrite ?szwrap32_small by lia; lia|]. exact HF.
  - symex s6u_segs fastC6 5%nat [false] [RVal (EVar 36%nat)]
      [(6, EAdd (EAdd (ESub (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 34%nat)) (EVar 35%nat)) (ELit 2));
       (13, EAdd (EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 35%nat)) (ELit 2)); (27, EVar 37%nat); (5, EVar 35%nat); (18, ELit 2)]
      [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^32); (36%nat, 256); (37%nat, 2^17)] NoRegions
      [P0; fo0; dist; i; fval (is_window s) ob2 (from_succ (from_succ fr)); len] NoVals F0 F0'
      (mkst R2 (0x22b00 : word) m2 s6u_rom) R3 HR3 Hfr3 Hms3.
    all: try side. all: guards.
    pose proof (MEMI_cp1 C SV m2 ob2 (fo0 + i + 2) _ HM2 ltac:(lia) (conj Fv20 Fv21)) as HM3.
    replace (P0 + fo0 + i + 2) with (P0 + (fo0 + i + 2)) in Hms3 by lia.
    assert (HF : forall q, reg_in q [5; 6; 7; 9; 13; 23; 27]%bv = false -> getr R3 q = getr regs q) by fr_chain3 Hfr3 Hfr2 Hfr1.
    exists R3. eexists. split.
    { eapply msteps_trans; [exact Hms1|]. eapply msteps_trans; [exact Hms2|]. exact Hms3. }
    split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
    split; [exact HM3|].
    symex_reg HR3 (5%bv : reg) as C5. symex_reg HR3 (27%bv : reg) as C27.
    split; [rewrite C5; f_equal; lia|]. split; [rewrite C27; f_equal; rewrite ?szwrap32_small by lia; lia|]. exact HF.
Qed.

Lemma do3_loop : forall k SV m ob dist fo0 i rem regs,
  KR regs -> MEMI SV m ob ->
  getr regs 22 = zw (P0 + fo0) -> getr regs 29 = zw (P0 + fo0 - dist) -> getr regs 5 = zw i -> getr regs 27 = zw (3 * Z.of_nat k + rem) ->
  (1 <= k)%nat -> 0 <= rem <= 2 -> 3 * Z.of_nat k + rem < 2 ^ 17 -> 1 <= dist < 2 ^ 17 -> dist <= fo0 -> 0 <= i -> i + 3 * Z.of_nat k < 2 ^ 17 -> fo0 + i + 3 * Z.of_nat k <= ON ->
  exists R m', msteps s6u_segs (mkst regs (0x22ac0 : word) m s6u_rom) (mkst R (0x22b14 : word) m' s6u_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FOut (fo0 + i - dist)) ob (fo0 + i) (3 * k))
   /\ getr R 5 = zw (i + 3 * Z.of_nat k) /\ getr R 27 = zw rem
   /\ (forall q, reg_in q [5; 6; 7; 9; 13; 23; 27]%bv = false -> getr R q = getr regs q).
Proof.
  induction k as [|k IH]; intros SV m ob dist fo0 i rem regs HK HM H22 H29 H5 H27 Hk Hrem Hlen Hdist Hdf Hi Hik HfoN; [lia|].
  destruct (do3_trip SV m ob dist fo0 i (3 * Z.of_nat (Datatypes.S k) + rem) regs HK HM H22 H29 H5 H27 ltac:(lia) Hdist Hdf ltac:(lia) ltac:(lia))
    as (R1 & m1 & Hms1 & HK1 & HM1 & A5 & A27 & Hfr1).
  destruct k as [|k'].
  - replace (2 <? 3 * Z.of_nat 1 + rem - 3) with false in Hms1 by (symmetry; apply Z.ltb_ge; lia).
    exists R1, m1. split; [exact Hms1|]. split; [exact HK1|]. split; [exact HM1|].
    split; [rewrite A5; f_equal; lia|]. split; [rewrite A27; f_equal; lia| exact Hfr1].
  - replace (2 <? 3 * Z.of_nat (Datatypes.S (Datatypes.S k')) + rem - 3) with true in Hms1 by (symmetry; apply Z.ltb_lt; lia).
    destruct (IH SV m1 (cblit (is_window s) (FOut (fo0 + i - dist)) ob (fo0 + i) 3) dist fo0 (i + 3) rem R1 HK1 HM1
                 ltac:(via1 Hfr1 H22) ltac:(via1 Hfr1 H29) A5 ltac:(rewrite A27; f_equal; lia) ltac:(lia) Hrem ltac:(lia) Hdist Hdf ltac:(lia) ltac:(lia) ltac:(lia))
      as (R2 & m2 & Hms2 & HK2 & HM2 & B5 & B27 & Hfr2).
    exists R2, m2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    split; [exact HK2|].
    split; [replace (3 * Datatypes.S (Datatypes.S k'))%nat with (3 + 3 * Datatypes.S k')%nat by lia; rewrite cblit_add, fr_add_out;
            replace (fo0 + i - dist + Z.of_nat 3) with (fo0 + (i + 3) - dist) by lia; replace (fo0 + i + Z.of_nat 3) with (fo0 + (i + 3)) by lia; exact HM2|].
    split; [rewrite B5; f_equal; lia|]. split; [exact B27|]. fr_chain2 Hfr2 Hfr1.
Qed.

Lemma do3_tail : forall SV m ob dist fo0 i rem regs,
  KR regs -> MEMI SV m ob ->
  getr regs 22 = zw (P0 + fo0) -> getr regs 29 = zw (P0 + fo0 - dist) -> getr regs 5 = zw i -> getr regs 27 = zw rem ->
  0 <= rem <= 2 -> 1 <= dist < 2 ^ 17 -> dist <= fo0 -> 0 <= i < 2 ^ 17 -> fo0 + i + rem <= ON ->
  exists R m', msteps s6u_segs (mkst regs (0x22b14 : word) m s6u_rom) (mkst R (0x22820 : word) m' s6u_rom)
   /\ KR R /\ MEMI SV m' (cblit (is_window s) (FOut (fo0 + i - dist)) ob (fo0 + i) (Z.to_nat rem))
   /\ getr R 22 = zw (P0 + (fo0 + i + rem))
   /\ (forall q, reg_in q [5; 6; 13; 22]%bv = false -> getr R q = getr regs q).
Proof.
  intros SV m ob dist fo0 i rem regs HK HM H22 H29 H5 H27 Hrem Hdist Hdf Hi HfoN.
  pose proof HK as HK'. kr_destr HK. clear_layout. pose proof (MEMI_len SV m ob HM) as HL.
  destruct (Z.eq_dec rem 0) as [R0E|RNZ].
  - subst rem.
    symex s6u_segs fastC6 2%nat [true] NoReads [(22, EAdd (EVar 32%nat) (EVar 33%nat)); (5, EVar 35%nat); (27, ELit 0)]
      [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^17)] NoRegions [P0; fo0; dist; i] NoVals F0 F0'
      (mkst regs (0x22b14 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    exists R, m. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [cbn [Z.to_nat cblit]; exact HM|].
    split; [symex_reg HR (22%bv : reg) as A; rewrite A; f_equal; lia| fr_weak Hfr].
  - set (fr := FOut (fo0 + i - dist)).
    assert (Hsrc : srcn_ok WN (fo0 + i) fr rem) by (subst fr; cbn; lia).
    pose proof (srcn_src_ok (fo0 + i) fr rem 0 Hsrc ltac:(lia)) as S0. cbn [fr_add Z.of_nat] in S0. rewrite Z.add_0_r in S0.
    pose proof (faddr_disj C (fo0 + i) fr S0 ltac:(lia)) as Fd.
    pose proof (fval_byte C SV m ob (fo0 + i) fr HM S0 ltac:(lia)) as [Fv0 Fv1].
    pose proof (src_read C SV m ob (fo0 + i) fr (P0 + fo0 - dist + i) HM S0 ltac:(lia) ltac:(subst fr; cbn [faddr]; lia)) as RD0.
    pose proof (MEMI_map_P SV m ob HM) as WP.
    destruct (Z.eq_dec rem 1) as [R1E|R2E].
    + subst rem.
      symex s6u_segs fastC6 10%nat [false; false; false; true] [RVal (EVar 36%nat)]
        [(22, EAdd (EVar 32%nat) (EVar 33%nat)); (29, ESub (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 34%nat)); (5, EVar 35%nat); (27, ELit 1); (18, ELit 2); (8, ELit (-1))]
        [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^17); (36%nat, 256)] NoRegions
        [P0; fo0; dist; i; fval (is_window s) ob fr] NoVals F0 F0'
        (mkst regs (0x22b14 : word) m s6u_rom) R HR Hfr Hms.
      all: try side. all: guards.
      exists R. eexists. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      split; [cbn [Z.to_nat Pos.to_nat cblit]; replace (P0 + fo0 + i) with (P0 + (fo0 + i)) by lia; apply (MEMI_cp1 C); [exact HM | lia | lia]|].
      split; [symex_reg HR (22%bv : reg) as A; rewrite A; f_equal; lia| fr_weak Hfr].
    + assert (R2 : rem = 2) by lia. subst rem.
      symex s6u_segs fastC6 9%nat [false; false; false; false] [RVal (EVar 36%nat)]
        [(22, EAdd (EVar 32%nat) (EVar 33%nat)); (29, ESub (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 34%nat)); (5, EVar 35%nat); (27, ELit 2); (18, ELit 2); (8, ELit (-1))]
        [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^17); (36%nat, 256)] NoRegions
        [P0; fo0; dist; i; fval (is_window s) ob fr] NoVals F0 F0'
        (mkst regs (0x22b14 : word) m s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try side. all: guards.
      pose proof (MEMI_cp1 C SV m ob (fo0 + i) _ HM ltac:(lia) (conj Fv0 Fv1)) as HM1.
      clear WP RD0 Fd.
      replace (P0 + fo0 + i) with (P0 + (fo0 + i)) in Hms1 by lia.
      set (m1 := wbytes m _ _) in Hms1, HM1. set (ob1 := arr_set ob (fo0 + i) _) in HM1.
      symex_reg HR1 (5%bv : reg) as A5. symex_reg HR1 (22%bv : reg) as A22. symex_reg HR1 (13%bv : reg) as A13.
      assert (A8 : getr R1 8 = zw (-1)) by (rewrite (Hfr1 8%bv eq_refl); exact K8).
      pose proof (srcn_src_ok (fo0 + i) fr 2 1 Hsrc ltac:(lia)) as S1. cbn [fr_add Z.of_nat] in S1. change (Z.of_nat 1) with 1 in S1.
      pose proof (faddr_disj C (fo0 + i + 1) (from_succ fr) S1 ltac:(lia)) as Fd. rewrite faddr_succ in Fd.
      pose proof (fval_byte C SV m1 ob1 (fo0 + i + 1) (from_succ fr) HM1 S1 ltac:(lia)) as [Fv10 Fv11].
      pose proof (src_read C SV m1 ob1 (fo0 + i + 1) (from_succ fr) (P0 + fo0 - dist + i + 1) HM1 S1 ltac:(lia)
                    ltac:(rewrite faddr_succ; subst fr; cbn [faddr]; lia)) as RD1.
      pose proof (MEMI_map_P SV m1 ob1 HM1) as WP.
      symex s6u_segs fastC6 8%nat [false; false] [RVal (EVar 36%nat)]
        [(22, EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 35%nat)); (5, EAdd (ESub (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 34%nat)) (EVar 35%nat));
         (13, EAdd (EAdd (EAdd (EVar 32%nat) (EVar 33%nat)) (EVar 35%nat)) (ELit 1)); (8, ELit (-1))]
        [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17); (35%nat, 2^17); (36%nat, 256)] NoRegions
        [P0; fo0; dist; i; fval (is_window s) ob1 (from_succ fr)] NoVals F0 F0'
        (mkst R1 (0x22b38 : word) m1 s6u_rom) R2 HR2 Hfr2 Hms2.
      all: try side. all: guards.
      pose proof (MEMI_cp1 C SV m1 ob1 (fo0 + i + 1) _ HM1 ltac:(lia) (conj Fv10 Fv11)) as HM2.
      replace (P0 + fo0 + i + 1) with (P0 + (fo0 + i + 1)) in Hms2 by lia.
      assert (HF : forall q, reg_in q [5; 6; 13; 22]%bv = false -> getr R2 q = getr regs q) by fr_chain2 Hfr2 Hfr1.
      exists R2. eexists. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      split; [eapply KREGS6_frame; [ | exact HK' | exact HF]; reflexivity|].
      split; [subst ob1; cbn [Z.to_nat Pos.to_nat cblit]; exact HM2|].
      split; [symex_reg HR2 (22%bv : reg) as A; rewrite A; f_equal; lia| exact HF].
Qed.

Lemma do3 : do3_stmt (sp:=sp) (s:=s) (c:=c) (r:=r) (ZP:=ZP) (S:=S) (I0:=I0) (P0:=P0) (WB:=WB) (mem:=mem).
Proof.
  intros SV m f regs HK HM H22 H29 H5 H27 Hlen Hdist Hdf Hbeg Hfon. cbv zeta.
  pose proof (proj1 (ffx_beg_range C)) as Hxbeg0'.
  set (f0 := fset_from f (FOut (f_out f - f_dist f))).
  destruct (fset_from_fields f (FOut (f_out f - f_dist f))) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8). fold f0 in F1, F2, F3, F4, F5, F6, F7, F8.
  rewrite copy_do3_cpn by (rewrite F4; lia). rewrite F4.
  pose proof (Z.div_mod (f_len f) 3 ltac:(lia)) as Hdm. pose proof (Z.mod_pos_bound (f_len f) 3 ltac:(lia)) as Hm3.
  set (k := Z.to_nat (f_len f / 3)).
  assert (Hk : (1 <= k)%nat) by (subst k; assert (1 <= f_len f / 3) by (apply Z.div_le_lower_bound; lia); lia).
  assert (Hk3 : 3 * Z.of_nat k = 3 * (f_len f / 3)) by (subst k; pose proof (Z.div_pos (f_len f) 3 ltac:(lia) ltac:(lia)); lia).
  destruct (do3_loop k SV m (f_ob f) (f_dist f) (f_out f) 0 (f_len f mod 3) regs HK HM H22 H29 H5 ltac:(rewrite H27; f_equal; lia)
              Hk ltac:(lia) ltac:(lia) Hdist Hdf ltac:(lia) ltac:(lia) ltac:(lia))
    as (R3 & m3 & Hms3 & HK3 & HM3 & C5 & C27 & Hfr3).
  rewrite !Z.add_0_r in HM3. rewrite Z.add_0_l in C5.
  destruct (do3_tail SV m3 _ (f_dist f) (f_out f) (3 * Z.of_nat k) (f_len f mod 3) R3 HK3 HM3 ltac:(via1 Hfr3 H22) ltac:(via1 Hfr3 H29) C5 C27
              ltac:(lia) Hdist Hdf ltac:(lia) ltac:(lia))
    as (R4 & m4 & Hms4 & HK4 & HM4 & D22 & Hfr4).
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
  split; [rewrite D22; f_equal; lia|].
  split; [fr_chain2 Hfr4 Hfr3|]. repeat split; lia.
Qed.
End Walk.
End FXG.
