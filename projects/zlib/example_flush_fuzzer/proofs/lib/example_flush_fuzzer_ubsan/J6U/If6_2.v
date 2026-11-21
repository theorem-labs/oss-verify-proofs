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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InffastCtx IfSpec IfSpec6 If6_1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac symex_auto ::=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia;
  try solve [ reflexivity | assumption | symex_ret_auto | symex_read_auto | symex_store_auto | symex_sok_auto | lia | split; lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Lemma byte_shl_lt64 : forall v k, 0 <= v < 256 -> 0 <= k <= 55 -> v * 2 ^ k < 2 ^ 64.
Proof.
  intros v k Hv Hk. pose proof (Z.pow_le_mono_r 2 k 55 ltac:(lia) ltac:(lia)).
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) ltac:(lia)). change (2 ^ 64) with (256 * 2 ^ 56). change (2 ^ 56) with (2 * 2 ^ 55). nia.
Qed.

Lemma lor_16 : forall b, 0 <= b < 16 -> Z.lor b 16 = b + 16.
Proof.
  intros b Hb.
  assert (Hl : Z.land b 16 = 0).
  { rewrite <- (Z.mod_small b (2 ^ 4)) by lia. rewrite <- Z.land_ones by lia.
    rewrite <- Z.land_assoc. change (Z.land (Z.ones 4) 16) with 0. apply Z.land_0_r. }
  rewrite <- Z.lxor_lor by exact Hl. symmetry. apply Z.add_nocarry_lxor. exact Hl.
Qed.

Lemma zw_negmask : forall e, 0 <= e < 32 -> zw (Z.lxor (zaluw ALU_SLL (-1) e) (-1)) = zw (2 ^ e - 1).
Proof.
  intros e He. apply zw_eqm. rewrite zaluw_sll_m1 by lia. rewrite Z.lxor_m1_r. unfold Z.lnot, Z.pred.
  pose proof (Z.pow_le_mono_r 2 e 31 ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)).
  change (2 ^ 31) with 2147483648 in *. change (2 ^ 64) with 18446744073709551616 in *.
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma code_read_val_lo : forall segs m (A : Z) v,
  cell segs m A 4 v ->
  exists bs, rdn segs m (zw (A + 2)) 1 = Some bs /\ bytes_le_to_Z bs = code_val v mod 256.
Proof.
  intros segs m A v Hc. unfold cell in Hc.
  exists (firstn 1 (skipn 2 (Z_to_le_bytes 4 v))). split.
  - change 2 with (Z.of_nat 2) at 1. rewrite zw_add_nat. exact (rdn_sub segs 2 4 (zw A) m _ 1 Hc ltac:(lia)).
  - rewrite skipn_Z_to_le_bytes, firstn_Z_to_le_bytes by lia. rewrite bytes_le_to_Z_of_Z, code_val_eq.
    change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536.
    symmetry. apply Z.mod_mod_divide. exists 256. reflexivity.
Qed.
Lemma ctab_read_val_lo : forall segs m A n f i a,
  cells segs m A 4 4 n f -> 0 <= i < n -> a = A + 4 * i + 2 ->
  exists bs, rdn segs m (zw a) 1 = Some bs /\ bytes_le_to_Z bs = code_val (f i) mod 256.
Proof. intros segs m A n f i a Hc Hi ->. apply code_read_val_lo. exact (Hc i Hi). Qed.
Lemma wrap8_mod256 : forall v, wrap8 (v mod 256) = wrap8 v.
Proof. intros v. unfold wrap8. change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. apply Z.mod_mod. lia. Qed.

Definition brk_mem (m0 : word -> option byte) (ZP S md : Z) (mg : option Z) : word -> option byte :=
  match mg with
  | None => wbytes m0 (zw (S + 8)) (Z_to_le_bytes 4 md)
  | Some a => wbytes (wbytes m0 (zw (ZP + 48)) (Z_to_le_bytes 8 (msg6_addr a))) (zw (S + 8)) (Z_to_le_bytes 4 md)
  end.

Definition refill2 (inp : arr) (fin hold bits : Z) : Z * Z * Z :=
  if bits <? 15 then (fin + 2, hold + (arr_get inp (fin + 1) * 2 ^ (bits + 8) + arr_get inp fin * 2 ^ bits), bits + 16)
  else (fin, hold, bits).

Definition dl_pc (op : Z) : word := if op =? 0 then (0x2280c : word) else (0x227c0 : word).

Definition d1_pc (op : Z) : word :=
  if negb (Z.land op 16 =? 0) then (0x22830 : word)
  else if negb (Z.land op 64 =? 0) then (0x22d1c : word) else (0x227d0 : word).

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

Lemma blk_L0 : forall SV m ob fin hold bits regs,
  KR regs -> MEMI SV m ob -> getr regs 9 = zw 14 ->
  getr regs 16 = zw (I0 + fin) -> getr regs 14 = zw hold -> getr regs 15 = zw bits ->
  0 <= fin <= IN -> 0 <= bits < 64 -> 0 <= hold < 2 ^ bits ->
  (bits < 15 -> fin + 2 <= IN) ->
  let '(fin', hold', bits') := refill2 (ic_input c) fin hold bits in
  exists R, msteps s6u_segs (mkst regs (0x2274c : word) m s6u_rom) (mkst R (0x22780 : word) m s6u_rom)
    /\ KR R /\ getr R 16 = zw (I0 + fin') /\ getr R 14 = zw hold' /\ getr R 15 = zw bits'
    /\ (forall r, reg_in r [5; 6; 13; 14; 15; 16]%bv = false -> getr R r = getr regs r)
    /\ 0 <= hold' < 2 ^ bits' /\ 0 <= bits' < 64 /\ 0 <= fin' <= IN.
Proof.
  intros SV m ob fin hold bits regs HK HM H9 H16 H14 H15 Hfin Hbits Hhold Hin2.
  pose proof (MEMI_in C SV m ob HM) as Hin_m.
  pose proof (Z.pow_le_mono_r 2 bits 63 ltac:(lia) ltac:(lia)) as Hh63. change (2 ^ 63) with 9223372036854775808 in Hh63.
  pose proof HK as HK'. kr_destr HK.
  pose proof Hinp_b as Hinb. unfold refill2. clear_layout. clear HM.
  destruct (Z.ltb_spec bits 15) as [Hb15|Hb15].
  - specialize (Hin2 Hb15).
    pose proof (Z.pow_le_mono_r 2 bits 14 ltac:(lia) ltac:(lia)) as Hpb. change (2 ^ 14) with 16384 in Hpb.
    destruct (Hinb fin ltac:(lia)) as [Hv00 Hv01]. destruct (Hinb (fin + 1) ltac:(lia)) as [Hv10 Hv11].
    symex s6u_segs fastC6 20%nat [false; false; false] [RVal (EVar 37%nat); RVal (EVar 38%nat)]
      [(16, EAdd (EVar 32%nat) (EVar 33%nat)); (14, EVar 34%nat); (15, EVar 35%nat); (9, ELit 14); (18, ELit 2); (8, ELit (-1))]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 16384); (35%nat, 15); (37%nat, 256); (38%nat, 256)] NoRegions
      [I0; fin; hold; bits; x_lmask X; arr_get (ic_input c) fin; arr_get (ic_input c) (fin + 1)] NoVals F0 F0'
      (mkst regs (0x2274c : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    assert (Z0 : zalu ALU_SLL (arr_get (ic_input c) fin) bits = arr_get (ic_input c) fin * 2 ^ bits).
    { apply zalu_sll_small; [lia|lia|]. apply byte_shl_lt64; lia. }
    assert (Z1 : zalu ALU_SLL (arr_get (ic_input c) (fin + 1)) (bits + 8) = arr_get (ic_input c) (fin + 1) * 2 ^ (bits + 8)).
    { apply zalu_sll_small; [lia|lia|]. apply byte_shl_lt64; lia. }
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (16%bv : reg) as A16. symex_reg HR (14%bv : reg) as A14. symex_reg HR (15%bv : reg) as A15.
    split; [rewrite A16; f_equal; lia|].
    split; [rewrite A14, Z0, Z1; f_equal; lia|].
    split; [rewrite A15; f_equal; apply lor_16; lia|].
    split; [fr_weak Hfr|].
    pose proof (pull2_lt hold bits (arr_get (ic_input c) fin) (arr_get (ic_input c) (fin + 1)) Hhold ltac:(lia) ltac:(lia) ltac:(lia)).
    pose proof (Z.pow_pos_nonneg 2 bits ltac:(lia) ltac:(lia)). nia.
  - symex s6u_segs fastC6 20%nat [true] NoReads
      [(16, EAdd (EVar 32%nat) (EVar 33%nat)); (14, EVar 34%nat); (15, EVar 35%nat); (9, ELit 14)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^64); (35%nat, 64)] NoRegions
      [I0; fin; hold; bits] NoVals F0 F0'
      (mkst regs (0x2274c : word) m s6u_rom) R HR Hfr Hms.
    all: try side.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [rewrite (Hfr 16%bv eq_refl); exact H16|]. split; [rewrite (Hfr 14%bv eq_refl); exact H14|].
    split; [rewrite (Hfr 15%bv eq_refl); exact H15|]. split; [fr_weak Hfr|]. lia.
Qed.

Lemma blk_D0 : forall SV m ob hold bits regs,
  KR regs -> MEMI SV m ob ->
  getr regs 14 = zw hold -> getr regs 15 = zw bits -> 0 <= bits < 64 -> 0 <= hold < 2 ^ bits ->
  let idx := Z.land hold (x_lmask X) in
  let here := code_at s (is_lencode s) idx in
  idx < LCN -> code_bits here <= bits ->
  exists R, msteps s6u_segs (mkst regs (0x22780 : word) m s6u_rom) (mkst R (dl_pc (code_op here)) m s6u_rom)
   /\ KR R /\ getr R 5 = zw (LC + 4 * idx) /\ getr R 13 = zw (code_op here)
   /\ getr R 14 = zw (hold / 2 ^ code_bits here) /\ getr R 15 = zw (bits - code_bits here)
   /\ (forall r, reg_in r [5; 6; 13; 14; 15]%bv = false -> getr R r = getr regs r)
   /\ 0 <= hold / 2 ^ code_bits here < 2 ^ (bits - code_bits here) /\ 0 <= bits - code_bits here < 64.
Proof.
  intros SV m ob hold bits regs HK HM H14 H15 Hbits Hhold idx here Hidx Hcb.
  pose proof (lencode_cells C m (MEMI_FINV SV m ob HM)) as Htab.
  assert (Hidx0 : 0 <= idx) by (subst idx; rewrite Hlmask_eq; apply land_ones_range; lia).
  pose proof (ctab_read_bits s6u_segs m LC LCN (code_at s (is_lencode s)) idx (idx * 2 ^ 2 + LC + 1) Htab ltac:(lia) ltac:(lia)) as RDbits.
  pose proof (ctab_read_op s6u_segs m LC LCN (code_at s (is_lencode s)) idx (idx * 2 ^ 2 + LC) Htab ltac:(lia) ltac:(lia)) as RDop.
  assert (K20' : getr regs 20 = zw (x_lmask X)).
  { destruct HK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & K20 & _). rewrite K20, Hlmask_eq. apply zw_negmask. lia. }
  pose proof (code_op_range here) as Hop. pose proof (code_bits_range here) as Hcbr.
  pose proof (Z.pow_le_mono_r 2 bits 63 ltac:(lia) ltac:(lia)) as Hh63. change (2 ^ 63) with 9223372036854775808 in Hh63.
  assert (ZS : zalu ALU_SRL hold (code_bits here) = hold / 2 ^ code_bits here) by (apply zalu_srl_small; lia).
  assert (HB : 0 <= hold / 2 ^ code_bits here < 2 ^ (bits - code_bits here)).
  { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | apply shiftr_lt_pow2; lia]. }
  pose proof (lc_pos_even C) as [HLCp HLCe].
  pose proof HK as HK'. kr_destr HK. clear_layout. clear Htab HM. unfold dl_pc.
  destruct (Z.eqb_spec (code_op here) 0) as [Hz|Hz].
  - symex s6u_segs fastC6 24%nat [false; false; false; false; false; true] [RVal (EVar 36%nat); RVal (EVar 37%nat)]
      [(30, EVar 32%nat); (14, EVar 33%nat); (15, EVar 34%nat); (20, EVar 35%nat); (24, EXor (EVar 32%nat) (ELit (-1))); (26, ELit 1); (19, ELit 63)]
      [(32%nat, 2^63); (33%nat, 2^64); (34%nat, 64); (35%nat, 65536); (36%nat, 256); (37%nat, 256)] NoRegions
      [LC; hold; bits; x_lmask X; code_bits here; code_op here] NoVals F0 F0'
      (mkst regs (0x22780 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    all: match goal with |- @ex _ _ => idtac | |- ?G => idtac "LEFT_D0a" G end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (5%bv : reg) as A5. symex_reg HR (13%bv : reg) as A13. symex_reg HR (14%bv : reg) as A14. symex_reg HR (15%bv : reg) as A15.
    split; [rewrite A5; f_equal; subst idx; lia|].
    split; [rewrite A13; f_equal; lia|].
    split; [rewrite A14, ZS; reflexivity|].
    split; [rewrite A15; f_equal; rewrite ?szwrap32_small by lia; lia|].
    split; [fr_weak Hfr|]. split; [exact HB|]. lia.
  - symex s6u_segs fastC6 24%nat [false; false; false; false; false; false] [RVal (EVar 36%nat); RVal (EVar 37%nat)]
      [(30, EVar 32%nat); (14, EVar 33%nat); (15, EVar 34%nat); (20, EVar 35%nat); (24, EXor (EVar 32%nat) (ELit (-1))); (26, ELit 1); (19, ELit 63)]
      [(32%nat, 2^63); (33%nat, 2^64); (34%nat, 64); (35%nat, 65536); (36%nat, 256); (37%nat, 256)] NoRegions
      [LC; hold; bits; x_lmask X; code_bits here; code_op here] NoVals F0 F0'
      (mkst regs (0x22780 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards.
    all: match goal with |- @ex _ _ => idtac | |- ?G => idtac "LEFT_D0b" G end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (5%bv : reg) as A5. symex_reg HR (13%bv : reg) as A13. symex_reg HR (14%bv : reg) as A14. symex_reg HR (15%bv : reg) as A15.
    split; [rewrite A5; f_equal; subst idx; lia|].
    split; [rewrite A13; f_equal; lia|].
    split; [rewrite A14, ZS; reflexivity|].
    split; [rewrite A15; f_equal; rewrite ?szwrap32_small by lia; lia|].
    split; [fr_weak Hfr|]. split; [exact HB|]. lia.
Qed.

Lemma blk_LIT : forall SV m ob idx fout regs,
  KR regs -> MEMI SV m ob -> 0 <= idx < LCN ->
  getr regs 5 = zw (LC + 4 * idx) -> getr regs 22 = zw (P0 + fout) -> 0 <= fout < ON ->
  let here := code_at s (is_lencode s) idx in
  exists R m', msteps s6u_segs (mkst regs (0x2280c : word) m s6u_rom) (mkst R (0x22820 : word) m' s6u_rom)
   /\ KR R /\ getr R 22 = zw (P0 + (fout + 1))
   /\ (forall r, reg_in r [5; 13; 22]%bv = false -> getr R r = getr regs r)
   /\ MEMI SV m' (arr_set ob fout (wrap8 (code_val here))).
Proof.
  intros SV m ob idx fout regs HK HM Hidx H5 H22 Hfout here.
  pose proof (lencode_cells C m (MEMI_FINV SV m ob HM)) as Htab.
  pose proof (ctab_read_val_lo s6u_segs m LC LCN (code_at s (is_lencode s)) idx (LC + 4 * idx + 2) Htab Hidx ltac:(lia)) as RDval.
  pose proof (Z.mod_pos_bound (code_val here) 256 ltac:(lia)) as Hvlo.
  pose proof (MEMI_map_P SV m ob HM) as WP.
  pose proof HK as HK'. kr_destr HK. clear_layout. clear Htab.
  symex s6u_segs fastC6 20%nat [false] [RVal (EVar 35%nat)]
    [(5, EAdd (EVar 32%nat) (EMul (ELit 4) (EVar 33%nat))); (22, EAdd (EVar 34%nat) (EVar 36%nat)); (18, ELit 2)]
    [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 256); (36%nat, 2^32)] NoRegions
    [LC; idx; P0; code_val here mod 256; fout] NoVals F0 F0'
    (mkst regs (0x2280c : word) m s6u_rom) R HR Hfr Hms.
  all: try side. all: guards.
  all: match goal with |- @ex _ _ => idtac | |- ?G => idtac "LEFT_LIT" G end.
  exists R. eexists. split; [exact Hms|].
  split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
  symex_reg HR (22%bv : reg) as A22.
  split; [rewrite A22; f_equal; lia|].
  split; [fr_weak Hfr|].
  rewrite <- wrap8_mod256. apply (MEMI_store_out1 C); [exact HM | lia | apply wrap8_range].
Qed.

Lemma blk_D1 : forall m op regs,
  KR regs -> getr regs 13 = zw op -> 0 <= op < 256 ->
  exists R, msteps s6u_segs (mkst regs (0x227c0 : word) m s6u_rom) (mkst R (d1_pc op) m s6u_rom)
   /\ KR R /\ getr R 13 = zw op
   /\ (forall r, reg_in r [6]%bv = false -> getr R r = getr regs r).
Proof.
  intros m op regs HK H13 Hop. pose proof HK as HK'. kr_destr HK. clear_layout. unfold d1_pc.
  destruct (Z.eqb_spec (Z.land op 16) 0) as [H16|H16]; cbn [negb].
  - destruct (Z.eqb_spec (Z.land op 64) 0) as [H64|H64]; cbn [negb].
    + symex s6u_segs fastC6 20%nat [false; false] NoReads [(13, EVar 32%nat)] [(32%nat, 256)] NoRegions [op] NoVals F0 F0'
        (mkst regs (0x227c0 : word) m s6u_rom) R HR Hfr Hms.
      all: try side.
      exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      split; [rewrite (Hfr 13%bv eq_refl); exact H13 | fr_weak Hfr].
    + symex s6u_segs fastC6 20%nat [false; true] NoReads [(13, EVar 32%nat)] [(32%nat, 256)] NoRegions [op] NoVals F0 F0'
        (mkst regs (0x227c0 : word) m s6u_rom) R HR Hfr Hms.
      all: try side.
      exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
      split; [rewrite (Hfr 13%bv eq_refl); exact H13 | fr_weak Hfr].
  - symex s6u_segs fastC6 20%nat [true] NoReads [(13, EVar 32%nat)] [(32%nat, 256)] NoRegions [op] NoVals F0 F0'
      (mkst regs (0x227c0 : word) m s6u_rom) R HR Hfr Hms.
    all: try side.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    split; [rewrite (Hfr 13%bv eq_refl); exact H13 | fr_weak Hfr].
Qed.

Lemma blk_L2 : forall SV m ob idx hold bits regs,
  KR regs -> MEMI SV m ob -> 0 <= idx < LCN ->
  let here := code_at s (is_lencode s) idx in
  let op := code_op here in
  getr regs 5 = zw (LC + 4 * idx) -> getr regs 13 = zw op -> getr regs 14 = zw hold -> getr regs 15 = zw bits ->
  0 <= bits < 64 -> 0 <= hold < 2 ^ bits -> op < 16 ->
  let idx' := code_val here + hold mod 2 ^ op in
  let here' := code_at s (is_lencode s) idx' in
  idx' < LCN -> code_bits here' <= bits ->
  exists R, msteps s6u_segs (mkst regs (0x227d0 : word) m s6u_rom) (mkst R (dl_pc (code_op here')) m s6u_rom)
   /\ KR R /\ getr R 5 = zw (LC + 4 * idx') /\ getr R 13 = zw (code_op here')
   /\ getr R 14 = zw (hold / 2 ^ code_bits here') /\ getr R 15 = zw (bits - code_bits here')
   /\ (forall r, reg_in r [5; 6; 13; 14; 15]%bv = false -> getr R r = getr regs r)
   /\ 0 <= hold / 2 ^ code_bits here' < 2 ^ (bits - code_bits here') /\ 0 <= bits - code_bits here' < 64.
Proof.
  intros SV m ob idx hold bits regs HK HM Hidx here op H5 H13 H14 H15 Hbits Hhold Hop16 idx' here' Hidx' Hcb.
  pose proof (lencode_cells C m (MEMI_FINV SV m ob HM)) as Htab.
  pose proof (code_op_range here) as Hop. change (code_op here) with op in Hop.
  pose proof (code_val_range here) as Hval.
  pose proof (Z.mod_pos_bound hold (2 ^ op) ltac:(apply Z.pow_pos_nonneg; lia)) as Hhm.
  assert (Hidx'0 : 0 <= idx') by (subst idx'; lia).
  pose proof (ctab_read_val s6u_segs m LC LCN (code_at s (is_lencode s)) idx (LC + 4 * idx + 2) Htab Hidx ltac:(lia)) as RDval.
  pose proof (code_op_range here') as Hop'. pose proof (code_bits_range here') as Hcbr'.
  pose proof (Z.pow_le_mono_r 2 bits 63 ltac:(lia) ltac:(lia)) as Hh63. change (2 ^ 63) with 9223372036854775808 in Hh63.
  assert (ZS : zalu ALU_SRL hold (code_bits here') = hold / 2 ^ code_bits here') by (apply zalu_srl_small; lia).
  assert (HB : 0 <= hold / 2 ^ code_bits here' < 2 ^ (bits - code_bits here')).
  { split; [apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia] | apply shiftr_lt_pow2; lia]. }
  assert (Hmask : Z.land hold (Z.lxor (zaluw ALU_SLL (-1) op) (-1)) = hold mod 2 ^ op).
  { rewrite Z.land_comm. apply negmask_land; lia. }
  pose proof (lc_pos_even C) as [HLCp HLCe].
  pose proof HK as HK'. kr_destr HK. clear_layout. clear HM. unfold dl_pc.
  destruct (Z.eqb_spec (code_op here') 0) as [Hz|Hz].
  - symex s6u_segs fastC6 30%nat [false; false; false; true; false; true] [RVal (EVar 37%nat); RVal (EVar 38%nat); RVal (EVar 39%nat)]
      [(30, EVar 32%nat); (5, EAdd (EVar 32%nat) (EMul (ELit 4) (EVar 33%nat))); (13, EVar 34%nat); (14, EVar 35%nat); (15, EVar 36%nat);
       (8, ELit (-1)); (24, EXor (EVar 32%nat) (ELit (-1))); (17, ELit 31); (19, ELit 63)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 16); (35%nat, 2^64); (36%nat, 64); (37%nat, 65536); (38%nat, 256); (39%nat, 256)] NoRegions
      [LC; idx; op; hold; bits; code_val here; code_bits here'; code_op here'] NoVals F0 F0'
      (mkst regs (0x227d0 : word) m s6u_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with
         | |- @ex (list byte) _ =>
           first [ eapply (ctab_read_bits s6u_segs m LC LCN _ idx'); [exact Htab | lia | rewrite Hmask; subst idx'; lia]
                 | eapply (ctab_read_op s6u_segs m LC LCN _ idx'); [exact Htab | lia | rewrite Hmask; subst idx'; lia] ]
         | |- _ => idtac end.
    all: try rewrite Hmask. all: guards.
    all: match goal with |- @ex _ (fun _ => msteps _ _ _ /\ _) => idtac | |- ?G => idtac "LEFT_L2a" G end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (5%bv : reg) as A5. symex_reg HR (13%bv : reg) as A13. symex_reg HR (14%bv : reg) as A14. symex_reg HR (15%bv : reg) as A15.
    split; [rewrite A5, Hmask; f_equal; subst idx'; lia|].
    split; [rewrite A13; f_equal; lia|].
    split; [rewrite A14, ZS; reflexivity|].
    split; [rewrite A15; f_equal; rewrite ?szwrap32_small by lia; lia|].
    split; [fr_weak Hfr|]. split; [exact HB|]. lia.
  - symex s6u_segs fastC6 30%nat [false; false; false; true; false; false] [RVal (EVar 37%nat); RVal (EVar 38%nat); RVal (EVar 39%nat)]
      [(30, EVar 32%nat); (5, EAdd (EVar 32%nat) (EMul (ELit 4) (EVar 33%nat))); (13, EVar 34%nat); (14, EVar 35%nat); (15, EVar 36%nat);
       (8, ELit (-1)); (24, EXor (EVar 32%nat) (ELit (-1))); (17, ELit 31); (19, ELit 63)]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 16); (35%nat, 2^64); (36%nat, 64); (37%nat, 65536); (38%nat, 256); (39%nat, 256)] NoRegions
      [LC; idx; op; hold; bits; code_val here; code_bits here'; code_op here'] NoVals F0 F0'
      (mkst regs (0x227d0 : word) m s6u_rom) R HR Hfr Hms.
    all: try side.
    all: lazymatch goal with
         | |- @ex (list byte) _ =>
           first [ eapply (ctab_read_bits s6u_segs m LC LCN _ idx'); [exact Htab | lia | rewrite Hmask; subst idx'; lia]
                 | eapply (ctab_read_op s6u_segs m LC LCN _ idx'); [exact Htab | lia | rewrite Hmask; subst idx'; lia] ]
         | |- _ => idtac end.
    all: try rewrite Hmask. all: guards.
    all: match goal with |- @ex _ (fun _ => msteps _ _ _ /\ _) => idtac | |- ?G => idtac "LEFT_L2b" G end.
    exists R. split; [exact Hms|].
    split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity|].
    symex_reg HR (5%bv : reg) as A5. symex_reg HR (13%bv : reg) as A13. symex_reg HR (14%bv : reg) as A14. symex_reg HR (15%bv : reg) as A15.
    split; [rewrite A5, Hmask; f_equal; subst idx'; lia|].
    split; [rewrite A13; f_equal; lia|].
    split; [rewrite A14, ZS; reflexivity|].
    split; [rewrite A15; f_equal; rewrite ?szwrap32_small by lia; lia|].
    split; [fr_weak Hfr|]. split; [exact HB|]. lia.
Qed.

Lemma blk_MSG : forall m A regs,
  getr regs 10 = zw ZP -> getr regs 13 = zw A -> 0 <= A < 2 ^ 63 ->
  (forall x : word, ZP <= bv_unsigned x < ZP + 112 -> m x <> None) ->
  exists R, msteps s6u_segs (mkst regs (0x22d38 : word) m s6u_rom)
              (mkst R (0x22d50 : word) (wbytes m (zw (ZP + 48)) (Z_to_le_bytes 8 A)) s6u_rom)
   /\ getr R 13 = zw BAD /\ (forall r, reg_in r [13]%bv = false -> getr R r = getr regs r).
Proof.
  intros m A regs H10 H13 HA WZ. clear_layout.
  symex s6u_segs fastC6 10%nat NoDirs NoReads [(10, EVar 32%nat); (13, EVar 33%nat)] [(32%nat, 2^63); (33%nat, 2^63)] NoRegions
    [ZP; A] NoVals F0 F0' (mkst regs (0x22d38 : word) m s6u_rom) R HR Hfr Hms.
  all: try side.
  exists R. split; [exact Hms|]. symex_reg HR (13%bv : reg) as A13. split; [exact A13 | fr_weak Hfr].
Qed.

Lemma blk_MODE : forall m md regs,
  getr regs 11 = zw S -> getr regs 13 = zw md -> 0 <= md < 2 ^ 31 ->
  (forall x : word, S <= bv_unsigned x < S + 7176 -> m x <> None) ->
  exists R, msteps s6u_segs (mkst regs (0x22d50 : word) m s6u_rom)
              (mkst R (0x22d54 : word) (wbytes m (zw (S + 8)) (Z_to_le_bytes 4 md)) s6u_rom)
   /\ (forall r, getr R r = getr regs r).
Proof.
  intros m md regs H11 H13 Hmd WS. clear_layout.
  symex s6u_segs fastC6 10%nat NoDirs NoReads [(11, EVar 32%nat); (13, EVar 33%nat)] [(32%nat, 2^63); (33%nat, 2^31)] NoRegions
    [S; md] NoVals F0 F0' (mkst regs (0x22d50 : word) m s6u_rom) R HR Hfr Hms.
  all: try side.
  exists R. split; [exact Hms|]. intros r0. apply Hfr. reflexivity.
Qed.

Lemma brk_msg : forall SV m ob a regs,
  getr regs 10 = zw ZP -> getr regs 11 = zw S -> MEMI SV m ob -> getr regs 13 = zw (msg6_addr a) ->
  exists R, msteps s6u_segs (mkst regs (0x22d38 : word) m s6u_rom) (mkst R (0x22d54 : word) (brk_mem m ZP S BAD (Some a)) s6u_rom)
   /\ (forall r, reg_in r [13]%bv = false -> getr R r = getr regs r).
Proof.
  intros SV m ob a regs K10 K11 HM H13.
  pose proof (FINV_map_Z _ m (MEMI_FINV SV m ob HM)) as WZ. pose proof (FINV_map_S _ m (MEMI_FINV SV m ob HM)) as WS.
  assert (HA : 0 <= msg6_addr a < 2 ^ 63).
  { unfold msg6_addr. repeat (destruct (_ =? _); [lia|]). lia. }
  destruct (blk_MSG m (msg6_addr a) regs K10 H13 HA WZ) as (R1 & Hms1 & A13 & Hfr1).
  destruct (blk_MODE (wbytes m (zw (ZP + 48)) (Z_to_le_bytes 8 (msg6_addr a))) BAD R1
              ltac:(rewrite (Hfr1 11%bv eq_refl); exact K11) A13 ltac:(unfold BAD; lia)
              ltac:(intros x Hx; apply wbytes_grows; exact (WS x Hx))) as (R2 & Hms2 & Hfr2).
  exists R2. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
  intros r0 Hr0. rewrite (Hfr2 r0). exact (Hfr1 r0 Hr0).
Qed.

Definition eob_mem (m : word -> option byte) (ZP S op : Z) : word -> option byte :=
  if Z.land op 32 =? 0 then brk_mem m ZP S BAD (Some MSG_invalid_literal_length_code) else brk_mem m ZP S TYPE None.

Lemma blk_EOB : forall SV m ob op regs,
  KR regs -> MEMI SV m ob -> getr regs 13 = zw op -> 0 <= op < 256 ->
  exists R, msteps s6u_segs (mkst regs (0x22d1c : word) m s6u_rom) (mkst R (0x22d54 : word) (eob_mem m ZP S op) s6u_rom)
   /\ (forall r, reg_in r [13]%bv = false -> getr R r = getr regs r).
Proof.
  intros SV m ob op regs HK HM H13 Hop.
  pose proof (FINV_map_S _ m (MEMI_FINV SV m ob HM)) as WS.
  pose proof HK as HK'. destruct HK as (K2 & K10 & K11 & _).
  pose proof Hd_ZS as HdZS. clear_layout. unfold eob_mem.
  destruct (Z.eqb_spec (Z.land op 32) 0) as [H32|H32].
  - symex s6u_segs fastC6 10%nat [false] NoReads [(13, EVar 32%nat)] [(32%nat, 256)] NoRegions [op] NoVals F0 F0'
      (mkst regs (0x22d1c : word) m s6u_rom) R HR Hfr Hms.
    all: try side.
    symex_reg HR (13%bv : reg) as A13.
    destruct (brk_msg SV m ob MSG_invalid_literal_length_code R ltac:(rewrite (Hfr 10%bv eq_refl); exact K10)
                ltac:(rewrite (Hfr 11%bv eq_refl); exact K11) HM ltac:(rewrite A13; reflexivity)) as (R2 & Hms2 & Hfr2).
    exists R2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    intros r0 Hr0. rewrite (Hfr2 r0 Hr0). exact (Hfr r0 Hr0).
  - symex s6u_segs fastC6 10%nat [true] NoReads [(13, EVar 32%nat)] [(32%nat, 256)] NoRegions [op] NoVals F0 F0'
      (mkst regs (0x22d1c : word) m s6u_rom) R HR Hfr Hms.
    all: try side.
    symex_reg HR (13%bv : reg) as A13.
    destruct (blk_MODE m TYPE R ltac:(rewrite (Hfr 11%bv eq_refl); exact K11) A13 ltac:(unfold TYPE; lia) WS) as (R2 & Hms2 & Hfr2).
    exists R2. split; [eapply msteps_trans; [exact Hms | exact Hms2]|].
    intros r0 Hr0. rewrite (Hfr2 r0). exact (Hfr r0 Hr0).
Qed.
End Walk.
End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
