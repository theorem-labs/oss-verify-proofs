(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InffastModel InffastCtx InffastSafe IfSpec IfSpec6 If6_1 If6_2 If6_3.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac symex_auto ::=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia;
  try solve [ reflexivity | assumption | symex_ret_auto | symex_read_auto | symex_store_auto | symex_sok_auto | lia | split; lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

Definition dpull (inp : arr) (fin hold bits e : Z) : Z * Z * Z :=
  if bits <? e then
    if bits + 8 <? e then (fin + 2, hold + arr_get inp fin * 2 ^ bits + arr_get inp (fin + 1) * 2 ^ (bits + 8), bits + 16)
    else (fin + 1, hold + arr_get inp fin * 2 ^ bits, bits + 8)
  else (fin, hold, bits).

Lemma geu_szwrap32 : forall opd dist, 0 <= opd < 2 ^ 32 -> 0 <= dist < 2 ^ 31 ->
  (dist <= szwrap 32 opd mod 2 ^ 64 <-> dist <= opd).
Proof.
  intros opd dist Ho Hd. unfold szwrap. change (2 ^ (32 - 1)) with 2147483648. change (2 ^ 32) with 4294967296 in *.
  change (2 ^ 31) with 2147483648 in *. change (2 ^ 64) with 18446744073709551616.
  Z.to_euclidean_division_equations; lia.
Qed.

Definition dwp_pc (wnext opw : Z) : word :=
  if wnext =? 0 then (0x1fc64 : word) else if wnext <? opw then (0x1fb9c : word) else (0x1fca0 : word).

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


Lemma blk_DX : forall SV m ob didx hold bits fin regs,
  KR regs -> MEMI SV m ob -> 0 <= didx < DCN ->
  let here := code_at s (is_distcode s) didx in
  let op := code_op here in let e := op mod 2 ^ 4 in
  getr regs 7 = zw (DC + 4 * didx) -> getr regs 27 = zw op -> getr regs 11 = zw hold -> getr regs 17 = zw bits ->
  getr regs 13 = zw (I0 + fin) ->
  0 <= bits < 64 -> 0 <= hold < 2 ^ bits -> 0 <= fin <= IN ->
  (bits < e -> fin + 1 <= IN) -> (bits + 8 < e -> fin + 2 <= IN) ->
  let '(fin', hold', bits') := dpull (ic_input c) fin hold bits e in
  exists R, msteps s6_segs (mkst regs (0x1fb1c : word) m s6_rom) (mkst R (0x1fb74 : word) m s6_rom)
   /\ KR R /\ getr R 1 = zw e /\ getr R 25 = zw bits' /\ getr R 11 = zw (hold' / 2 ^ e)
   /\ getr R 27 = zw (hold' mod 2 ^ e + code_val here) /\ getr R 13 = zw (I0 + fin')
   /\ (forall r, reg_in r [1; 11; 13; 17; 25; 27]%bv = false -> getr R r = getr regs r)
   /\ 0 <= hold' < 2 ^ bits' /\ e <= bits' < 64 /\ 0 <= fin' <= IN
   /\ 0 <= hold' / 2 ^ e < 2 ^ (bits' - e) /\ 0 <= hold' mod 2 ^ e + code_val here < 2 ^ 17.
Proof.
  intros SV m ob didx hold bits fin regs HK HM Hdidx here op e H7 H27 H11 H17 H13 Hbits Hhold Hfin Hin1 Hin2. subst e.
  pose proof (distcode_cells C m (MEMI_FINV SV m ob HM)) as Htab.
  pose proof (ctab_read_val s6_segs m DC DCN (code_at s (is_distcode s)) didx (DC + 4 * didx + 2) Htab Hdidx ltac:(lia)) as RDval.
  pose proof (code_op_range here) as Hop. pose proof (code_val_range here) as Hval. change (code_op here) with op in Hop.
  pose proof (MEMI_in C SV m ob HM) as Hin_m. pose proof Hinp_b as Hinb.
  pose proof (Z.pow_le_mono_r 2 bits 63 ltac:(lia) ltac:(lia)) as Hh63. change (2 ^ 63) with 9223372036854775808 in Hh63.
  set (e := op mod 2 ^ 4) in *.
  assert (He : 0 <= e < 16) by (subst e; apply Z.mod_pos_bound; lia).
  pose proof (Z.pow_le_mono_r 2 e 15 ltac:(lia) ltac:(lia)) as Hpe. change (2 ^ 15) with 32768 in Hpe.
  pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)) as Hpe0.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout. clear Htab HM. unfold dpull.
  destruct (Z.ltb_spec bits e) as [Hbe|Hbe].
  - specialize (Hin1 Hbe). destruct (Hinb fin ltac:(lia)) as [Hv0 Hv1].
    pose proof (Z.pow_le_mono_r 2 bits 15 ltac:(lia) ltac:(lia)) as Hpb. change (2 ^ 15) with 32768 in Hpb.
    assert (Z0 : zalu ALU_SLL (arr_get (ic_input c) fin) bits = arr_get (ic_input c) fin * 2 ^ bits).
    { apply zalu_sll_small; [lia|lia|]. apply byte_shl_lt64; lia. }
    pose proof (pull1_lt hold bits (arr_get (ic_input c) fin) Hhold ltac:(lia) ltac:(lia)) as Hh1.
    destruct (Z.ltb_spec (bits + 8) e) as [Hbe8|Hbe8].
    +
      specialize (Hin2 Hbe8). destruct (Hinb (fin + 1) ltac:(lia)) as [Hv10 Hv11].
      assert (Z1 : zalu ALU_SLL (arr_get (ic_input c) (fin + 1)) (bits + 8) = arr_get (ic_input c) (fin + 1) * 2 ^ (bits + 8)).
      { apply zalu_sll_small; [lia|lia|]. apply byte_shl_lt64; lia. }
      pose proof (pull2_lt hold bits (arr_get (ic_input c) fin) (arr_get (ic_input c) (fin + 1)) Hhold ltac:(lia) ltac:(lia) ltac:(lia)) as Hh2.
      pose proof (Z.pow_le_mono_r 2 (bits + 16) 63 ltac:(lia) ltac:(lia)) as Hh2'. change (2 ^ 63) with 9223372036854775808 in Hh2'.
      pose proof (Z.pow_pos_nonneg 2 bits ltac:(lia) ltac:(lia)) as Hpb0. pose proof (Z.pow_pos_nonneg 2 (bits + 8) ltac:(lia) ltac:(lia)) as Hpb8.
      set (hold' := hold + arr_get (ic_input c) fin * 2 ^ bits + arr_get (ic_input c) (fin + 1) * 2 ^ (bits + 8)) in *.
      assert (Hh'0 : 0 <= hold') by (subst hold'; nia).
      symex s6_segs fastC6 30%nat [false; false] [RVal (EVar 39%nat); RVal (EVar 40%nat); RVal (EVar 41%nat)]
        [(7, EAdd (EVar 32%nat) (EMul (ELit 4) (EVar 33%nat))); (27, EVar 34%nat); (11, EVar 35%nat); (17, EVar 36%nat);
         (13, EAdd (EVar 37%nat) (EVar 38%nat)); (5, ELit (-1))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 256); (35%nat, 2^64); (36%nat, 64); (37%nat, 2^63); (38%nat, 2^63);
         (39%nat, 256); (40%nat, 256); (41%nat, 65536)] NoRegions
        [DC; didx; op; hold; bits; I0; fin; arr_get (ic_input c) fin; arr_get (ic_input c) (fin + 1); code_val here] NoVals F0 F0'
        (mkst regs (0x1fb1c : word) m s6_rom) R HR Hfr Hms.
      all: try side.
      all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [subst e; brc | idtac "LEFT_DX2" G] end.
      exists R. split; [exact Hms|].
      split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      symex_reg HR (1%bv : reg) as A1. symex_reg HR (25%bv : reg) as A25. symex_reg HR (11%bv : reg) as A11.
      symex_reg HR (27%bv : reg) as A27. symex_reg HR (13%bv : reg) as A13.
      all: idtac "DX2_MAIN".
      split; [rewrite A1; subst e; reflexivity|].
      split; [rewrite A25; f_equal; brc|].
      split. { rewrite A11, ?Z1, ?Z0. subst e. rewrite zalu_srl_small by lia. f_equal. f_equal. subst hold'. lia. }
      split. { rewrite A27, ?Z1, ?Z0. subst e. rewrite (Z.land_comm _ (Z.lxor _ _)), negmask_land by lia. f_equal.
               match goal with |- ?a mod _ + _ = _ => replace a with hold' by (subst hold'; lia) end. reflexivity. }
      split; [rewrite A13; f_equal; lia|].
      split; [fr_weak Hfr|].
      pose proof (Z.mod_pos_bound hold' (2 ^ e) Hpe0) as Hme.
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [split; [apply Z.div_pos; lia | apply shiftr_lt_pow2; lia]|]. lia.
    +
      set (hold' := hold + arr_get (ic_input c) fin * 2 ^ bits) in *.
      pose proof (Z.pow_le_mono_r 2 (bits + 8) 63 ltac:(lia) ltac:(lia)) as Hh1'. change (2 ^ 63) with 9223372036854775808 in Hh1'.
      pose proof (Z.pow_pos_nonneg 2 bits ltac:(lia) ltac:(lia)) as Hpb0.
      assert (Hh'0 : 0 <= hold') by (subst hold'; nia).
      symex s6_segs fastC6 30%nat [false; true] [RVal (EVar 39%nat); RVal (EVar 40%nat)]
        [(7, EAdd (EVar 32%nat) (EMul (ELit 4) (EVar 33%nat))); (27, EVar 34%nat); (11, EVar 35%nat); (17, EVar 36%nat);
         (13, EAdd (EVar 37%nat) (EVar 38%nat)); (5, ELit (-1))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 256); (35%nat, 2^64); (36%nat, 64); (37%nat, 2^63); (38%nat, 2^63);
         (39%nat, 256); (40%nat, 65536)] NoRegions
        [DC; didx; op; hold; bits; I0; fin; arr_get (ic_input c) fin; code_val here] NoVals F0 F0'
        (mkst regs (0x1fb1c : word) m s6_rom) R HR Hfr Hms.
      all: try side.
      all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [subst e; brc | idtac "LEFT_DX1" G] end.
      exists R. split; [exact Hms|].
      split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      symex_reg HR (1%bv : reg) as A1. symex_reg HR (25%bv : reg) as A25. symex_reg HR (11%bv : reg) as A11.
      symex_reg HR (27%bv : reg) as A27. symex_reg HR (13%bv : reg) as A13.
      all: idtac "DX1_MAIN".
      split; [rewrite A1; subst e; reflexivity|].
      split; [rewrite A25; f_equal; brc|].
      split. { rewrite A11, ?Z0. subst e. rewrite zalu_srl_small by lia. f_equal. f_equal. subst hold'. lia. }
      split. { rewrite A27, ?Z0. subst e. rewrite (Z.land_comm _ (Z.lxor _ _)), negmask_land by lia. f_equal.
               match goal with |- ?a mod _ + _ = _ => replace a with hold' by (subst hold'; lia) end. reflexivity. }
      split; [rewrite A13; f_equal; lia|].
      split; [fr_weak Hfr|].
      pose proof (Z.mod_pos_bound hold' (2 ^ e) Hpe0) as Hme.
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [split; [apply Z.div_pos; lia | apply shiftr_lt_pow2; lia]|]. lia.
  -
    symex s6_segs fastC6 30%nat [true] [RVal (EVar 39%nat)]
      [(7, EAdd (EVar 32%nat) (EMul (ELit 4) (EVar 33%nat))); (27, EVar 34%nat); (11, EVar 35%nat); (17, EVar 36%nat);
       (13, EAdd (EVar 37%nat) (EVar 38%nat)); (5, ELit (-1))]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 256); (35%nat, 2^64); (36%nat, 64); (37%nat, 2^63); (38%nat, 2^63);
       (39%nat, 65536)] NoRegions
      [DC; didx; op; hold; bits; I0; fin; code_val here] NoVals F0 F0'
      (mkst regs (0x1fb1c : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [subst e; brc | idtac "LEFT_DX0" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (1%bv : reg) as A1. symex_reg HR (25%bv : reg) as A25. symex_reg HR (11%bv : reg) as A11.
    symex_reg HR (27%bv : reg) as A27.
    all: idtac "DX0_MAIN".
    split; [rewrite A1; subst e; reflexivity|].
    split; [rewrite A25; f_equal; brc|].
    split. { rewrite A11. subst e. rewrite zalu_srl_small by lia. reflexivity. }
    split. { rewrite A27. subst e. rewrite (Z.land_comm _ (Z.lxor _ _)), negmask_land by lia. reflexivity. }
    split; [rewrite (Hfr 13%bv eq_refl); exact H13|].
    split; [fr_weak Hfr|].
    pose proof (Z.mod_pos_bound hold (2 ^ e) Hpe0) as Hme.
    split; [lia|]. split; [lia|]. split; [lia|].
    split; [split; [apply Z.div_pos; lia | apply shiftr_lt_pow2; lia]|]. lia.
Qed.

Lemma blk_DOP : forall m e bits' dist fout regs,
  KR regs -> getr regs 1 = zw e -> getr regs 25 = zw bits' -> getr regs 27 = zw dist -> getr regs 14 = zw (P0 + fout) ->
  0 <= e <= bits' -> bits' < 64 -> 0 <= dist < 2 ^ 17 -> x_beg X <= fout <= ON ->
  let opd := fout - x_beg X in
  exists R, msteps s6_segs (mkst regs (0x1fb74 : word) m s6_rom)
              (mkst R (if dist <=? opd then (0x1fc00 : word) else (0x1fb80 : word)) m s6_rom)
   /\ KR R /\ getr R 17 = zw (bits' - e)
   /\ (forall r, reg_in r [7; 17]%bv = false -> getr R r = getr regs r)
   /\ 0 <= opd <= ON.
Proof.
  intros m e bits' dist fout regs HK H1 H25 H27 H14 He Hb Hdist Hfout opd.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout.
  destruct (Z.leb_spec dist opd) as [Hd|Hd].
  - symex s6_segs fastC6 10%nat [true] NoReads
      [(1, EVar 32%nat); (25, EVar 33%nat); (27, EVar 34%nat); (14, EAdd (EVar 35%nat) (EVar 36%nat)); (20, EAdd (EVar 35%nat) (EVar 37%nat))]
      [(32%nat, 64); (33%nat, 64); (34%nat, 2^17); (35%nat, 2^63); (36%nat, 2^32); (37%nat, 2^32)] NoRegions
      [e; bits'; dist; P0; fout; x_beg X] NoVals F0 F0'
      (mkst regs (0x1fb74 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G =>
           first [ replace (P0 + fout - (P0 + x_beg X)) with opd by lia; apply (proj2 (geu_szwrap32 opd dist ltac:(lia) ltac:(lia))); lia
                 | idtac "LEFT_DOPa" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (17%bv : reg) as A17.
    split; [rewrite A17; f_equal; brc|]. split; [fr_weak Hfr|]. subst opd; lia.
  - symex s6_segs fastC6 10%nat [false] NoReads
      [(1, EVar 32%nat); (25, EVar 33%nat); (27, EVar 34%nat); (14, EAdd (EVar 35%nat) (EVar 36%nat)); (20, EAdd (EVar 35%nat) (EVar 37%nat))]
      [(32%nat, 64); (33%nat, 64); (34%nat, 2^17); (35%nat, 2^63); (36%nat, 2^32); (37%nat, 2^32)] NoRegions
      [e; bits'; dist; P0; fout; x_beg X] NoVals F0 F0'
      (mkst regs (0x1fb74 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G =>
           first [ replace (P0 + fout - (P0 + x_beg X)) with opd by lia;
                   pose proof (proj1 (geu_szwrap32 opd dist ltac:(lia) ltac:(lia))); lia
                 | idtac "LEFT_DOPb" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (17%bv : reg) as A17.
    split; [rewrite A17; f_equal; brc|]. split; [fr_weak Hfr|]. subst opd; lia.
Qed.

Lemma blk_DW : forall SV m ob dist fout regs,
  KR regs -> MEMI SV m ob -> getr regs 27 = zw dist -> getr regs 14 = zw (P0 + fout) ->
  0 <= dist < 2 ^ 17 -> x_beg X <= fout <= ON -> fout - x_beg X < dist ->
  let opw := dist - (fout - x_beg X) in
  let err := (x_whave X <? opw) && negb (x_sane X =? 0) in
  exists R, msteps s6_segs (mkst regs (0x1fb80 : word) m s6_rom)
              (mkst R (if err then (0x1fe10 : word) else (0x1fb94 : word)) m s6_rom)
   /\ KR R /\ getr R 7 = zw opw
   /\ (forall r, reg_in r [7; 25]%bv = false -> getr R r = getr regs r)
   /\ 0 < opw <= dist /\ (err = false -> opw <= x_whave X \/ x_sane X = 0).
Proof.
  intros SV m ob dist fout regs HK HM H27 H14 Hdist Hf1 Hf2 opw err.
  pose proof (isl_sane _ _ _ _ _ _ _ (MEMI_scalars C SV m ob HM)) as Fsane.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout. clear HM. subst err. cbn [x_whave x_sane ffx_of] in *.
  destruct (Z.ltb_spec (is_whave s) opw) as [Hw|Hw]; cbn [andb].
  - destruct (Z.eqb_spec (is_sane s) 0) as [Hz|Hz]; cbn [negb].
    + symex s6_segs fastC6 10%nat [false; false] [RVal (EVar 37%nat)]
        [(27, EVar 32%nat); (14, EAdd (EVar 33%nat) (EVar 34%nat)); (20, EAdd (EVar 33%nat) (EVar 35%nat)); (30, EVar 36%nat); (19, EAdd (EVar 38%nat) (ELit 7160))]
        [(32%nat, 2^17); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 2^32); (36%nat, 2^31); (37%nat, 2^31); (38%nat, 2^63)] NoRegions
        [dist; P0; fout; x_beg X; is_whave s; is_sane s; S] NoVals F0 F0'
        (mkst regs (0x1fb80 : word) m s6_rom) R HR Hfr Hms.
      all: try side.
      all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [assumption | subst opw; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia | idtac "LEFT_DWa" G] end.
      exists R. split; [exact Hms|].
      split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      symex_reg HR (7%bv : reg) as A7.
      split; [rewrite A7; f_equal; subst opw; brc|]. split; [fr_weak Hfr|]. split; [subst opw; lia|]. intros _; right; exact Hz.
    + symex s6_segs fastC6 10%nat [false; true] [RVal (EVar 37%nat)]
        [(27, EVar 32%nat); (14, EAdd (EVar 33%nat) (EVar 34%nat)); (20, EAdd (EVar 33%nat) (EVar 35%nat)); (30, EVar 36%nat); (19, EAdd (EVar 38%nat) (ELit 7160))]
        [(32%nat, 2^17); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 2^32); (36%nat, 2^31); (37%nat, 2^31); (38%nat, 2^63)] NoRegions
        [dist; P0; fout; x_beg X; is_whave s; is_sane s; S] NoVals F0 F0'
        (mkst regs (0x1fb80 : word) m s6_rom) R HR Hfr Hms.
      all: try side.
      all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [assumption | subst opw; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia | idtac "LEFT_DWb" G] end.
      exists R. split; [exact Hms|].
      split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      symex_reg HR (7%bv : reg) as A7.
      split; [rewrite A7; f_equal; subst opw; brc|]. split; [fr_weak Hfr|]. split; [subst opw; lia|]. intros E; discriminate E.
  - symex s6_segs fastC6 10%nat [true] NoReads
      [(27, EVar 32%nat); (14, EAdd (EVar 33%nat) (EVar 34%nat)); (20, EAdd (EVar 33%nat) (EVar 35%nat)); (30, EVar 36%nat); (19, EAdd (EVar 38%nat) (ELit 7160))]
      [(32%nat, 2^17); (33%nat, 2^63); (34%nat, 2^32); (35%nat, 2^32); (36%nat, 2^31); (37%nat, 2^31); (38%nat, 2^63)] NoRegions
      [dist; P0; fout; x_beg X; is_whave s; is_sane s; S] NoVals F0 F0'
      (mkst regs (0x1fb80 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [assumption | subst opw; rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; lia | idtac "LEFT_DWc" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (7%bv : reg) as A7.
    split; [rewrite A7; f_equal; subst opw; brc|]. split; [fr_weak Hfr|]. split; [subst opw; lia|]. intros _; left; exact Hw.
Qed.

Lemma blk_DWP : forall m opw regs,
  KR regs -> getr regs 7 = zw opw -> 0 < opw < 2 ^ 17 ->
  exists R, msteps s6_segs (mkst regs (0x1fb94 : word) m s6_rom) (mkst R (dwp_pc (x_wnext X) opw) m s6_rom)
   /\ (forall r, getr R r = getr regs r).
Proof.
  intros m opw regs HK H7 Hopw.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout. unfold dwp_pc. cbn [x_wnext ffx_of] in *.
  destruct (Z.eqb_spec (is_wnext s) 0) as [Hw0|Hw0].
  - symex s6_segs fastC6 10%nat [true] NoReads [(7, EVar 32%nat); (31, EVar 33%nat)] [(32%nat, 2^17); (33%nat, 2^31)] NoRegions
      [opw; is_wnext s] NoVals F0 F0' (mkst regs (0x1fb94 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    exists R. split; [exact Hms|]. intros r0; apply Hfr; reflexivity.
  - destruct (Z.ltb_spec (is_wnext s) opw) as [Hwl|Hwl].
    + symex s6_segs fastC6 10%nat [false; false] NoReads [(7, EVar 32%nat); (31, EVar 33%nat)] [(32%nat, 2^17); (33%nat, 2^31)] NoRegions
        [opw; is_wnext s] NoVals F0 F0' (mkst regs (0x1fb94 : word) m s6_rom) R HR Hfr Hms.
      all: try side.
      exists R. split; [exact Hms|]. intros r0; apply Hfr; reflexivity.
    + symex s6_segs fastC6 10%nat [false; true] NoReads [(7, EVar 32%nat); (31, EVar 33%nat)] [(32%nat, 2^17); (33%nat, 2^31)] NoRegions
        [opw; is_wnext s] NoVals F0 F0' (mkst regs (0x1fb94 : word) m s6_rom) R HR Hfr Hms.
      all: try side.
      exists R. split; [exact Hms|]. intros r0; apply Hfr; reflexivity.
Qed.

Lemma blk_FAR : forall SV m ob regs,
  KR regs -> MEMI SV m ob ->
  exists R, msteps s6_segs (mkst regs (0x1fe10 : word) m s6_rom)
              (mkst R (0x1fd90 : word) (brk_mem m ZP S BAD (Some MSG_invalid_distance_too_far_back)) s6_rom)
   /\ (forall r, reg_in r [5]%bv = false -> getr R r = getr regs r).
Proof.
  intros SV m ob regs HK HM.
  pose proof HK as HK'. destruct HK as (K2 & K10 & K12 & _). clear_layout.
  symex s6_segs fastC6 10%nat NoDirs NoReads (@nil (Z * expr)) (@nil (nat * Z)) NoRegions (@nil Z) NoVals F0 F0'
    (mkst regs (0x1fe10 : word) m s6_rom) R HR Hfr Hms.
  all: try side.
  symex_reg HR (5%bv : reg) as A5.
  destruct (brk_msg C SV m ob MSG_invalid_distance_too_far_back R ltac:(rewrite (Hfr 10%bv eq_refl); exact K10)
              ltac:(rewrite (Hfr 12%bv eq_refl); exact K12) HM ltac:(rewrite A5; reflexivity)) as (R2 & Hms2 & Hfr2).
  exists R2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
  intros r0 Hr0. rewrite (Hfr2 r0 Hr0). exact (Hfr r0 Hr0).
Qed.

Lemma blk_W1h : forall m opw len regs,
  KR regs -> x_wnext X = 0 -> getr regs 7 = zw opw -> getr regs 26 = zw len -> 0 < opw <= x_wsize X -> opw < 2 ^ 17 -> 0 <= len < 2 ^ 17 ->
  exists R, msteps s6_segs (mkst regs (0x1fc64 : word) m s6_rom)
              (mkst R (if opw <? len then (0x1fc7c : word) else (0x1fcd8 : word)) m s6_rom)
   /\ KR R /\ getr R 1 = zw (WB + (x_wsize X - opw)) /\ (opw < len -> getr R 25 = zw opw)
   /\ (forall r, reg_in r [1; 25]%bv = false -> getr R r = getr regs r).
Proof.
  intros m opw len regs HK Hw0 H7 H26 Hopw Hopw17 Hlen.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout. cbn [x_wnext x_wsize ffx_of] in *.
  destruct (Z.ltb_spec opw len) as [Hol|Hol].
  - symex s6_segs fastC6 10%nat [false] NoReads [(7, EVar 32%nat); (26, EVar 33%nat); (29, EVar 34%nat); (8, EVar 35%nat)]
      [(32%nat, 2^17); (33%nat, 2^17); (34%nat, 2^31); (35%nat, 2^63)] NoRegions [opw; len; is_wsize s; WB] NoVals F0 F0'
      (mkst regs (0x1fc64 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [brc | mlia | idtac "LEFT_W1a" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (1%bv : reg) as A1. symex_reg HR (25%bv : reg) as A25.
    split; [rewrite A1; f_equal; rewrite ?szwrap32_small by lia; mlia|].
    split; [intros _; exact A25 | fr_weak Hfr].
  - symex s6_segs fastC6 10%nat [true] NoReads [(7, EVar 32%nat); (26, EVar 33%nat); (29, EVar 34%nat); (8, EVar 35%nat)]
      [(32%nat, 2^17); (33%nat, 2^17); (34%nat, 2^31); (35%nat, 2^63)] NoRegions [opw; len; is_wsize s; WB] NoVals F0 F0'
      (mkst regs (0x1fc64 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [brc | mlia | idtac "LEFT_W1b" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (1%bv : reg) as A1.
    split; [rewrite A1; f_equal; rewrite ?szwrap32_small by lia; mlia|].
    split; [intros Hc; lia | fr_weak Hfr].
Qed.

Lemma blk_W3h : forall m opw len regs,
  KR regs -> getr regs 7 = zw opw -> getr regs 26 = zw len -> 0 < opw <= x_wnext X -> opw < 2 ^ 17 -> 0 <= len < 2 ^ 17 ->
  exists R, msteps s6_segs (mkst regs (0x1fca0 : word) m s6_rom)
              (mkst R (if opw <? len then (0x1fcb8 : word) else (0x1fcd8 : word)) m s6_rom)
   /\ KR R /\ getr R 1 = zw (WB + (x_wnext X - opw)) /\ (opw < len -> getr R 25 = zw opw)
   /\ (forall r, reg_in r [1; 21; 25]%bv = false -> getr R r = getr regs r).
Proof.
  intros m opw len regs HK H7 H26 Hopw Hopw17 Hlen.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout. cbn [x_wnext ffx_of] in *.
  destruct (Z.ltb_spec opw len) as [Hol|Hol].
  - symex s6_segs fastC6 10%nat [false] NoReads [(7, EVar 32%nat); (26, EVar 33%nat); (31, EVar 34%nat); (8, EVar 35%nat)]
      [(32%nat, 2^17); (33%nat, 2^17); (34%nat, 2^31); (35%nat, 2^63)] NoRegions [opw; len; is_wnext s; WB] NoVals F0 F0'
      (mkst regs (0x1fca0 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [brc | mlia | idtac "LEFT_W3a" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (1%bv : reg) as A1. symex_reg HR (25%bv : reg) as A25.
    split; [rewrite A1; f_equal; rewrite ?szwrap32_small by lia; mlia|].
    split; [intros _; exact A25 | fr_weak Hfr].
  - symex s6_segs fastC6 10%nat [true] NoReads [(7, EVar 32%nat); (26, EVar 33%nat); (31, EVar 34%nat); (8, EVar 35%nat)]
      [(32%nat, 2^17); (33%nat, 2^17); (34%nat, 2^31); (35%nat, 2^63)] NoRegions [opw; len; is_wnext s; WB] NoVals F0 F0'
      (mkst regs (0x1fca0 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [brc | mlia | idtac "LEFT_W3b" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (1%bv : reg) as A1.
    split; [rewrite A1; f_equal; rewrite ?szwrap32_small by lia; mlia|].
    split; [intros Hc; lia | fr_weak Hfr].
Qed.

Lemma blk_W2h : forall SV m ob opw len regs,
  KR regs -> MEMI SV m ob -> In (0, 8%nat, x_wsize X + x_wnext X) SV ->
  getr regs 7 = zw opw -> getr regs 26 = zw len ->
  0 < x_wnext X < opw -> opw <= x_wsize X + x_wnext X -> opw < 2 ^ 17 -> 0 <= len < 2 ^ 17 ->
  let opw' := opw - x_wnext X in
  exists R, msteps s6_segs (mkst regs (0x1fb9c : word) m s6_rom)
              (mkst R (if opw' <? len then (0x1fbbc : word) else (0x1fcd8 : word)) m s6_rom)
   /\ KR R /\ getr R 1 = zw (WB + (x_wsize X + x_wnext X - opw)) /\ getr R 7 = zw opw' /\ (opw' < len -> getr R 25 = zw opw')
   /\ (forall r, reg_in r [1; 7; 21; 25]%bv = false -> getr R r = getr regs r).
Proof.
  intros SV m ob opw len regs HK HM Hslot H7 H26 Hw Hopw Hopw17 Hlen opw'. subst opw'.
  pose proof (fcells_get s6_segs sp m SV _ _ _ (MEMI_saved SV m ob HM) Hslot) as Hc0. rewrite Z.add_0_r in Hc0. unfold cell in Hc0.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  pose proof Hmap_sp as Wsp. unfold mapped in Wsp. clear_layout. clear HM. cbn [x_wnext x_wsize ffx_of] in *.
  destruct (Z.ltb_spec (opw - is_wnext s) len) as [Hol|Hol].
  - symex s6_segs fastC6 12%nat [false] [RVal (EAdd (EVar 34%nat) (EVar 35%nat))]
      [(7, EVar 32%nat); (26, EVar 33%nat); (29, EVar 34%nat); (31, EVar 35%nat); (8, EVar 36%nat); (2, EVar 37%nat)]
      [(32%nat, 2^17); (33%nat, 2^17); (34%nat, 2^31); (35%nat, 2^31); (36%nat, 2^63); (37%nat, 2^63)] NoRegions
      [opw; len; is_wsize s; is_wnext s; WB; sp] NoVals F0 F0'
      (mkst regs (0x1fb9c : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [brc | mlia | idtac "LEFT_W2a" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (1%bv : reg) as A1. symex_reg HR (7%bv : reg) as A7. symex_reg HR (25%bv : reg) as A25.
    split; [rewrite A1; f_equal; rewrite ?szwrap32_small by lia; mlia|].
    split; [rewrite A7; f_equal; brc|].
    split; [intros _; rewrite A25; f_equal; brc | fr_weak Hfr].
  - symex s6_segs fastC6 12%nat [true] [RVal (EAdd (EVar 34%nat) (EVar 35%nat))]
      [(7, EVar 32%nat); (26, EVar 33%nat); (29, EVar 34%nat); (31, EVar 35%nat); (8, EVar 36%nat); (2, EVar 37%nat)]
      [(32%nat, 2^17); (33%nat, 2^17); (34%nat, 2^31); (35%nat, 2^31); (36%nat, 2^63); (37%nat, 2^63)] NoRegions
      [opw; len; is_wsize s; is_wnext s; WB; sp] NoVals F0 F0'
      (mkst regs (0x1fb9c : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [brc | mlia | idtac "LEFT_W2b" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (1%bv : reg) as A1. symex_reg HR (7%bv : reg) as A7.
    split; [rewrite A1; f_equal; rewrite ?szwrap32_small by lia; mlia|].
    split; [rewrite A7; f_equal; brc|].
    split; [intros Hc; lia | fr_weak Hfr].
Qed.

Lemma blk_W2m : forall m opw' len regs,
  KR regs -> getr regs 7 = zw opw' -> getr regs 26 = zw len -> 0 <= opw' <= len -> len < 2 ^ 17 ->
  exists R, msteps s6_segs (mkst regs (0x1fbd4 : word) m s6_rom)
              (mkst R (if x_wnext X <? len - opw' then (0x1fbe0 : word) else (0x1fd38 : word)) m s6_rom)
   /\ KR R /\ getr R 26 = zw (len - opw') /\ (x_wnext X < len - opw' -> getr R 7 = zw WB)
   /\ (forall r, reg_in r [7; 26]%bv = false -> getr R r = getr regs r).
Proof.
  intros m opw' len regs HK H7 H26 Ho Hlen.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout. cbn [x_wnext ffx_of] in *.
  destruct (Z.ltb_spec (is_wnext s) (len - opw')) as [Hc|Hc].
  - symex s6_segs fastC6 10%nat [false] NoReads [(7, EVar 32%nat); (26, EVar 33%nat); (31, EVar 34%nat); (8, EVar 35%nat)]
      [(32%nat, 2^17); (33%nat, 2^17); (34%nat, 2^31); (35%nat, 2^63)] NoRegions [opw'; len; is_wnext s; WB] NoVals F0 F0'
      (mkst regs (0x1fbd4 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [brc | idtac "LEFT_W2ma" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (26%bv : reg) as A26. symex_reg HR (7%bv : reg) as A7.
    split; [rewrite A26; f_equal; brc|]. split; [intros _; exact A7 | fr_weak Hfr].
  - symex s6_segs fastC6 10%nat [true] NoReads [(7, EVar 32%nat); (26, EVar 33%nat); (31, EVar 34%nat); (8, EVar 35%nat)]
      [(32%nat, 2^17); (33%nat, 2^17); (34%nat, 2^31); (35%nat, 2^63)] NoRegions [opw'; len; is_wnext s; WB] NoVals F0 F0'
      (mkst regs (0x1fbd4 : word) m s6_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => first [brc | idtac "LEFT_W2mb" G] end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (26%bv : reg) as A26.
    split; [rewrite A26; f_equal; brc|]. split; [intros Hx; lia | fr_weak Hfr].
Qed.

Lemma blk_W2e : forall m len regs,
  KR regs -> getr regs 26 = zw len -> x_wnext X <= len < 2 ^ 17 ->
  exists R, msteps s6_segs (mkst regs (0x1fbf8 : word) m s6_rom) (mkst R (0x1fcd4 : word) m s6_rom)
   /\ KR R /\ getr R 26 = zw (len - x_wnext X) /\ (forall r, reg_in r [26]%bv = false -> getr R r = getr regs r).
Proof.
  intros m len regs HK H26 Hlen.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout. cbn [x_wnext ffx_of] in *.
  symex s6_segs fastC6 10%nat NoDirs NoReads [(26, EVar 32%nat); (31, EVar 33%nat)] [(32%nat, 2^17); (33%nat, 2^31)] NoRegions
    [len; is_wnext s] NoVals F0 F0' (mkst regs (0x1fbf8 : word) m s6_rom) R HR Hfr Hms.
  all: try side.
  exists R. split; [exact Hms|].
  split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
  symex_reg HR (26%bv : reg) as A26. split; [rewrite A26; f_equal; brc | fr_weak Hfr].
Qed.

Lemma blk_J98 : forall m opw len regs,
  KR regs -> getr regs 7 = zw opw -> getr regs 26 = zw len -> 0 <= opw <= len -> len < 2 ^ 17 ->
  exists R, msteps s6_segs (mkst regs (0x1fcd0 : word) m s6_rom) (mkst R (0x1fcd4 : word) m s6_rom)
   /\ KR R /\ getr R 26 = zw (len - opw) /\ (forall r, reg_in r [26]%bv = false -> getr R r = getr regs r).
Proof.
  intros m opw len regs HK H7 H26 Ho Hlen.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout.
  symex s6_segs fastC6 10%nat NoDirs NoReads [(7, EVar 32%nat); (26, EVar 33%nat)] [(32%nat, 2^17); (33%nat, 2^17)] NoRegions
    [opw; len] NoVals F0 F0' (mkst regs (0x1fcd0 : word) m s6_rom) R HR Hfr Hms.
  all: try side.
  exists R. split; [exact Hms|].
  split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
  symex_reg HR (26%bv : reg) as A26. split; [rewrite A26; f_equal; brc | fr_weak Hfr].
Qed.

Lemma blk_J9c : forall m dist fout regs,
  KR regs -> getr regs 14 = zw (P0 + fout) -> getr regs 27 = zw dist -> 0 <= dist <= fout -> fout <= ON ->
  exists R, msteps s6_segs (mkst regs (0x1fcd4 : word) m s6_rom) (mkst R (0x1fcd8 : word) m s6_rom)
   /\ KR R /\ getr R 1 = zw (P0 + (fout - dist)) /\ (forall r, reg_in r [1]%bv = false -> getr R r = getr regs r).
Proof.
  intros m dist fout regs HK H14 H27 Hd Hf.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout.
  symex s6_segs fastC6 10%nat NoDirs NoReads [(14, EAdd (EVar 32%nat) (EVar 33%nat)); (27, EVar 34%nat)] [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^32)] NoRegions
    [P0; fout; dist] NoVals F0 F0' (mkst regs (0x1fcd4 : word) m s6_rom) R HR Hfr Hms.
  all: try side.
  exists R. split; [exact Hms|].
  split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
  symex_reg HR (1%bv : reg) as A1. split; [rewrite A1; f_equal; lia | fr_weak Hfr].
Qed.

Lemma blk_DCh : forall m dist fout regs,
  KR regs -> getr regs 14 = zw (P0 + fout) -> getr regs 27 = zw dist -> 0 <= dist < 2 ^ 17 -> 0 <= fout <= ON ->
  exists R, msteps s6_segs (mkst regs (0x1fc00 : word) m s6_rom) (mkst R (0x1fc0c : word) m s6_rom)
   /\ KR R /\ getr R 14 = zw (P0 + fout + 2) /\ getr R 7 = zw (1 - dist)
   /\ (forall r, reg_in r [7; 14]%bv = false -> getr R r = getr regs r).
Proof.
  intros m dist fout regs HK H14 H27 Hd Hf.
  pose proof HK as HK'.
  destruct HK as (K2 & K10 & K12 & K15 & K16 & K20 & K29 & K30 & K31 & K8 & K9 & K18 & K22 & K23 & K19 & K24 & K5 & K6 & K28).
  clear_layout.
  symex s6_segs fastC6 10%nat NoDirs NoReads [(14, EAdd (EVar 32%nat) (EVar 33%nat)); (27, EVar 34%nat)] [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^17)] NoRegions
    [P0; fout; dist] NoVals F0 F0' (mkst regs (0x1fc00 : word) m s6_rom) R HR Hfr Hms.
  all: try side.
  exists R. split; [exact Hms|].
  split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
  symex_reg HR (14%bv : reg) as A14. symex_reg HR (7%bv : reg) as A7.
  split; [rewrite A14; f_equal; lia|]. split; [rewrite A7; f_equal; lia | fr_weak Hfr].
Qed.

End Walk.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
