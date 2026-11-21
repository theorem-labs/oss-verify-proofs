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
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InffastCtx IfSpec IfSpec6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

End FXG.
Ltac symex_auto ::=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia;
  try solve [ reflexivity | assumption | symex_ret_auto | symex_read_auto | symex_store_auto | symex_sok_auto | lia | split; lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Definition fastC6 : cfg :=
  CFG [] [] [EVar 1%nat]
      [0x2274c; 0x22780; 0x227c0; 0x227d0; 0x2280c; 0x22820; 0x22830; 0x22888; 0x228b8; 0x22904; 0x2290c;
       0x22948; 0x22994; 0x229b8; 0x229d4; 0x229dc; 0x22a24; 0x22a58; 0x22a6c; 0x22a98; 0x22aa0; 0x22ac0; 0x22b14; 0x22b58;
       0x22b98; 0x22bc8; 0x22c04; 0x22c30; 0x22c44; 0x22c50; 0x22c58; 0x22cc8; 0x22d08;
       0x22d1c; 0x22d30; 0x22d38; 0x22d50; 0x22d54; 0x22e34; 0x22dbc] [].


Definition KREGS6 (sp ZP S I0 P0 WB : Z) (x : ffx) (LB DB LC DC : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = zw sp /\ getr regs 10 = zw ZP /\ getr regs 11 = zw S
  /\ getr regs 12 = zw (I0 + x_last x) /\ getr regs 21 = zw (P0 + x_end x) /\ getr regs 28 = zw (x_wnext x)
  /\ getr regs 30 = zw LC /\ getr regs 31 = zw DC
  /\ getr regs 8 = zw (-1) /\ getr regs 18 = zw 2 /\ getr regs 19 = zw 63 /\ getr regs 17 = zw 31
  /\ getr regs 20 = zw (Z.lxor (zaluw ALU_SLL (-1) LB) (-1))
  /\ getr regs 24 = zw (Z.lxor LC (-1)) /\ getr regs 25 = zw (Z.lxor DC (-1)) /\ getr regs 26 = zw 1.

Lemma wrap32_eqmod : forall z, wrap32 z = z mod 2 ^ 32.
Proof. intros z. unfold wrap32. change 4294967295 with (Z.ones 32). apply Z.land_ones. lia. Qed.

Definition kregs6_list : list reg := [2; 10; 11; 12; 21; 28; 30; 31; 8; 18; 19; 17; 20; 24; 25; 26]%bv.
Definition kregs6_kept (L : list reg) : bool := forallb (fun k => negb (reg_in k L)) kregs6_list.

Lemma KREGS6_frame : forall sp ZP S I0 P0 WB x LB DB LC DC regs R L,
  kregs6_kept L = true ->
  KREGS6 sp ZP S I0 P0 WB x LB DB LC DC regs ->
  (forall r : reg, reg_in r L = false -> getr R r = getr regs r) ->
  KREGS6 sp ZP S I0 P0 WB x LB DB LC DC R.
Proof.
  intros sp ZP S I0 P0 WB x LB DB LC DC regs R L HL HK Hfr.
  unfold kregs6_kept, kregs6_list in HL. cbn [forallb] in HL.
  repeat match type of HL with
  | (negb ?b && _) = true => let H := fresh "Hk" in apply andb_prop in HL as [H HL]; apply Bool.negb_true_iff in H
  | negb ?b = true => apply Bool.negb_true_iff in HL
  end.
  unfold KREGS6 in *.
  repeat match goal with |- _ /\ _ => split end;
  match goal with |- getr R ?k = _ => rewrite (Hfr k) by assumption end; tauto.
Qed.

Definition VREGS6 (I0 P0 : Z) (f : ffs) (regs : bvmap 5 word) : Prop :=
  getr regs 16 = zw (I0 + f_in f) /\ getr regs 22 = zw (P0 + f_out f) /\ getr regs 14 = zw (f_hold f) /\ getr regs 15 = zw (f_bits f).

Definition SAVED6 (S P0 WB : Z) (regs0 : bvmap 5 word) (x : ffx) : list (Z * nat * Z) :=
  let u := fun k : reg => bv_unsigned (getr regs0 k) in
  [(152, 8%nat, u 1%bv); (144, 8%nat, u 8%bv); (136, 8%nat, u 9%bv); (128, 8%nat, u 18%bv); (120, 8%nat, u 19%bv); (112, 8%nat, u 20%bv);
   (104, 8%nat, u 21%bv); (96, 8%nat, u 22%bv); (88, 8%nat, u 23%bv); (80, 8%nat, u 24%bv); (72, 8%nat, u 25%bv); (64, 8%nat, u 26%bv);
   (56, 8%nat, u 27%bv);
   (48, 8%nat, x_dmask x); (40, 8%nat, WB); (32, 8%nat, P0 + x_beg x); (24, 8%nat, x_whave x); (16, 8%nat, S + 7160);
   (8, 8%nat, x_wsize x); (0, 8%nat, x_wsize x + x_wnext x)].

Lemma SAVED6_ok : forall S P0 WB regs0 x, SVok (SAVED6 S P0 WB regs0 x).
Proof.
  intros S P0 WB regs0 x e He. unfold SAVED6 in He. cbv beta zeta in He.
  repeat (destruct He as [<-|He]; [cbn; lia|]). destruct He.
Qed.

Section Tables.
Context {mem : word -> option byte} {sp : Z} {ra : word}
        {s : inflate_state} {c : icall} {r : iregs}
        {ZP S I0 P0 WB : Z}.
Variable C : iff_pre s6u_segs is6_LENFIX is6_DISTFIX ROD6_LO ROD6_HI IMG6_TOP mem sp ra s c r ZP S I0 P0 WB.
Local Notation LC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_lencode s)).
Local Notation DC := (codeptr_addr is6_LENFIX is6_DISTFIX S (is_distcode s)).
Local Notation LCN := (ctab_len (is_lencode s)).
Local Notation DCN := (ctab_len (is_distcode s)).
Local Notation ON := (arr_len (ic_outbuf c)).
Local Notation LF1 := (FF1 sp P0 (arr_len (ic_outbuf c))).
Local Notation FI := (FINV mem sp P0 (arr_len (ic_outbuf c)) ZP S).
Local Notation MI6 := (fun regs0 => MEMINV s6u_segs mem sp (arr_len (ic_outbuf c)) ZP S P0 (SAVED6 S P0 WB regs0 (ffx_of s c r))).


Lemma rod6_of_FINV1 : forall m, FI LF1 m -> rod6_clear m.
Proof. intros m HM x Hx. exact (FINV1_rod C m HM x Hx). Qed.

Lemma lencode_cells : forall m, FI LF1 m -> cells s6u_segs m LC 4 4 LCN (code_at s (is_lencode s)).
Proof.
  intros m HM. pose proof (ifp_r_lencode C) as Hr.
  destruct (is_lencode s) as [ofs| |] eqn:E.
  - apply (FINV1_ctab_dyn C m ofs HM). exact Hr.
  - cbn [codeptr_addr ctab_len code_at]. exact (lenfix6_cells m (rod6_of_FINV1 m HM)).
  - cbn [codeptr_addr ctab_len code_at]. exact (distfix6_cells m (rod6_of_FINV1 m HM)).
Qed.

Lemma distcode_cells : forall m, FI LF1 m -> cells s6u_segs m DC 4 4 DCN (code_at s (is_distcode s)).
Proof.
  intros m HM. pose proof (ifp_r_distcode C) as Hr.
  destruct (is_distcode s) as [ofs| |] eqn:E.
  - apply (FINV1_ctab_dyn C m ofs HM). exact Hr.
  - cbn [codeptr_addr ctab_len code_at]. exact (lenfix6_cells m (rod6_of_FINV1 m HM)).
  - cbn [codeptr_addr ctab_len code_at]. exact (distfix6_cells m (rod6_of_FINV1 m HM)).
Qed.

End Tables.


Section TablesU.
Context {mem : word -> option byte} {sp : Z} {ra : word}
        {s : inflate_state} {c : icall} {r : iregs}
        {ZP S I0 P0 WB : Z}.
Variable C : iff_pre s6u_segs is6_LENFIX is6_DISTFIX ROD6_LO ROD6_HI IMG6_TOP mem sp ra s c r ZP S I0 P0 WB.

Lemma lc_pos_even : 0 < codeptr_addr is6_LENFIX is6_DISTFIX S (is_lencode s) /\ codeptr_addr is6_LENFIX is6_DISTFIX S (is_lencode s) mod 2 = 0.
Proof.
  pose proof (ifp_S C) as HS. pose proof (proj2 (ifp_align C)) as HalS. pose proof (ifp_r_lencode C) as Hr.
  destruct (is_lencode s) as [ofs| |]; cbn [codeptr_addr]; unfold is6_LENFIX, is6_DISTFIX.
  - cbn in Hr. split; [lia|]. replace (S + 1384 + 4 * ofs) with (S + 8 * 173 + 4 * ofs) by lia. clear - HalS Hr. Z.to_euclidean_division_equations; lia.
  - split; reflexivity.
  - split; reflexivity.
Qed.
Lemma dc_pos_even : 0 < codeptr_addr is6_LENFIX is6_DISTFIX S (is_distcode s) /\ codeptr_addr is6_LENFIX is6_DISTFIX S (is_distcode s) mod 2 = 0.
Proof.
  pose proof (ifp_S C) as HS. pose proof (proj2 (ifp_align C)) as HalS. pose proof (ifp_r_distcode C) as Hr.
  destruct (is_distcode s) as [ofs| |]; cbn [codeptr_addr]; unfold is6_LENFIX, is6_DISTFIX.
  - cbn in Hr. split; [lia|]. replace (S + 1384 + 4 * ofs) with (S + 8 * 173 + 4 * ofs) by lia. clear - HalS Hr. Z.to_euclidean_division_equations; lia.
  - split; reflexivity.
  - split; reflexivity.
Qed.
End TablesU.

Lemma negmask_mod64 : forall e, 0 <= e < 32 -> Z.lxor (zaluw ALU_SLL (-1) e) (-1) mod 2 ^ 64 = 2 ^ e - 1.
Proof.
  intros e He. rewrite zaluw_sll_m1 by lia. rewrite Z.lxor_m1_r. unfold Z.lnot, Z.pred.
  pose proof (Z.pow_le_mono_r 2 e 31 ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)).
  change (2 ^ 31) with 2147483648 in *. change (2 ^ 64) with 18446744073709551616 in *.
  Z.to_euclidean_division_equations; lia.
Qed.

Lemma land7_mod8 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land1_mod2 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof. intros x Hx. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

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
Local Ltac fr_weak Hfr :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; apply Hfr; eapply reg_in_sub; [| exact Hr]; reflexivity.
Local Ltac slot_cell :=
  repeat (first [ apply cell_write_same; rewrite ?length_Z_to_le_bytes; cbn; lia
                | apply cell_write_other; rewrite ?length_Z_to_le_bytes; [|cbn; lia|cbn; lia|lia|cbn; lia|cbn; lia] ]).


Lemma prologue_step : forall regs,
  getr regs 10 = zw ZP -> getr regs 11 = zw (ir_out r) -> getr regs 2 = zw (sp + 160) -> 0 <= ir_out r < 2 ^ 32 ->
  exists R m', msteps s6u_segs (mkst regs (0x225ec : word) mem s6u_rom) (mkst R (0x2274c : word) m' s6u_rom)
    /\ KR R /\ VREGS6 I0 P0 (ff0_of s c) R /\ MEMI (SAVED6 S P0 WB regs X) m' (ic_outbuf c)
    /\ getr R 9 = zw 14 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4.
Proof.
  intros regs H10 H11 H2 Hir.
  pose proof Hmap_sp as Hm. unfold mapped in Hm.
  pose proof (isl_wsize _ _ _ _ _ _ _ Hsc) as Fwsize. pose proof (isl_whave _ _ _ _ _ _ _ Hsc) as Fwhave.
  pose proof (isl_wnext _ _ _ _ _ _ _ Hsc) as Fwnext.
  pose proof (isl_window _ _ _ _ _ _ _ Hsc) as Fwindow. cbn [q_window] in Fwindow.
  pose proof (isl_hold _ _ _ _ _ _ _ Hsc) as Fhold. pose proof (isl_bits _ _ _ _ _ _ _ Hsc) as Fbits.
  pose proof (isl_lencode _ _ _ _ _ _ _ Hsc) as Flencode. pose proof (isl_distcode _ _ _ _ _ _ _ Hsc) as Fdistcode.
  pose proof (isl_lenbits _ _ _ _ _ _ _ Hsc) as Flenbits. pose proof (isl_distbits _ _ _ _ _ _ _ Hsc) as Fdistbits.
  pose proof Hzin as Hzin0. rewrite Z.add_0_r in Hzin0.
  pose proof (lc_pos_even C) as [HLCp HLCe]. pose proof (dc_pos_even C) as [HDCp HDCe].
  pose proof (land7_mod8 ZP ltac:(lia)) as HZ7. pose proof (land7_mod8 S ltac:(lia)) as HS7.
  clear Hcodes Hcodes_b Hwin Hwin_b Hinp Hinp_b Hrod Hd_spI Hd_spP Hd_spW Hd_PZ Hd_PS Hd_PI Hd_PW Hd_ZS Hd_ZI Hd_ZW Hd_SI Hd_SW Hmap_P Hmap_Z Hmap_S.
  time symex s6u_segs fastC6 100%nat [false; false; false; false; false; false; false; false; false; false; false; false]
    [RVal (EVar 36%nat); RVal (EAdd (EVar 48%nat) (EVar 49%nat)); RVal (EVar 37%nat); RVal (EAdd (EVar 50%nat) (EVar 51%nat)); RVal (EVar 35%nat);
     RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 38%nat); RVal (EVar 39%nat); RVal (EVar 40%nat); RVal (EVar 41%nat);
     RVal (EVar 42%nat); RVal (EVar 43%nat); RVal (EVar 44%nat); RVal (EVar 45%nat)]
    [(10, EVar 32%nat); (11, EVar 33%nat); (2, EAdd (EVar 34%nat) (ELit 160))]
    [(32%nat, 2^63); (33%nat, 2^32); (34%nat, 2^63); (35%nat, 2^63); (36%nat, 2^32); (37%nat, 2^32); (38%nat, 2^31); (39%nat, 2^31);
     (40%nat, 2^31); (41%nat, 2^63); (42%nat, 2^64); (43%nat, 64); (44%nat, 2^63); (45%nat, 2^63); (46%nat, 16); (47%nat, 16);
     (48%nat, 2^63); (49%nat, 2^63); (50%nat, 2^63); (51%nat, 2^32)] NoRegions
    [ZP; ir_out r; sp; S; ic_avail_in c; ic_avail_out c; is_wsize s; is_whave s; is_wnext s; WB; is_hold s; is_bits s; LC; DC;
     is_lenbits s; is_distbits s; I0; ic_next_in c; P0; ic_next_out c] NoVals F0 F0'
    (mkst regs (0x225ec : word) mem s6u_rom) R HR Hfr Hms.
  all: try side.
  all: lazymatch goal with
       | |- @ex _ _ => idtac
       | |- Z.lxor (if 0 <? ?a then 1 else 0) (if ?b <? 1 then 1 else 0) <> 0 =>
           destruct (Z.ltb_spec 0 a); [| exfalso; mlia]; destruct (Z.ltb_spec b 1); [exfalso| discriminate];
           first [ mlia
                 | match goal with H0 : Z.lxor ?o ?k < 1 |- _ =>
                     pose proof (Z.lxor_nonneg o k) as HN; assert (HE : o = k) by (apply Z.lxor_eq; mlia); clear H0 HN; mlia end ]
       | |- _ => mlia
       end.
  exists R. eexists. split; [exact Hms|].
  split.
  {
    unfold KREGS6. cbn [x_last x_end x_beg x_wsize x_whave x_wnext ffx_of]. rewrite !wrap32_eqmod.
    symex_reg HR (2%bv : reg) as A2. symex_reg HR (10%bv : reg) as A10. symex_reg HR (11%bv : reg) as A11.
    symex_reg HR (12%bv : reg) as A12. symex_reg HR (21%bv : reg) as A21. symex_reg HR (28%bv : reg) as A28.
    symex_reg HR (30%bv : reg) as A30. symex_reg HR (31%bv : reg) as A31.
    symex_reg HR (8%bv : reg) as A8. symex_reg HR (18%bv : reg) as A18. symex_reg HR (19%bv : reg) as A19. symex_reg HR (17%bv : reg) as A17.
    symex_reg HR (20%bv : reg) as A20. symex_reg HR (24%bv : reg) as A24. symex_reg HR (25%bv : reg) as A25. symex_reg HR (26%bv : reg) as A26.
    split; [exact A2|]. split; [exact A10|]. split; [exact A11|].
    split; [rewrite A12; f_equal; mlia|]. split; [rewrite A21; f_equal; mlia|]. split; [exact A28|].
    split; [exact A30|]. split; [exact A31|].
    split; [exact A8|]. split; [exact A18|]. split; [exact A19|]. split; [exact A17|].
    split; [exact A20|]. split; [exact A24|]. split; [exact A25|].
    rewrite A26. replace (0 <? LC) with true by (symmetry; apply Z.ltb_lt; exact HLCp). reflexivity. }
  split.
  { unfold VREGS6. cbn [f_in f_out f_hold f_bits ff0_of].
    symex_reg HR (16%bv : reg) as A16. symex_reg HR (22%bv : reg) as A22. symex_reg HR (14%bv : reg) as A14. symex_reg HR (15%bv : reg) as A15.
    split; [exact A16|]. split; [exact A22|]. split; [exact A14 | exact A15]. }
  split.
  split.
  { apply (FINV_weaken (FF0 sp) (FF1 sp P0 (arr_len (ic_outbuf c)))); [| apply FF0_FF1]. unfold FF0.
    lazymatch goal with |- FINV _ _ _ _ _ _ _ (wbytes ?M (zw sp) (Z_to_le_bytes 8 ?v)) =>
      pose proof (FINV_store_sp C nil M 0 8 v) as HF0; rewrite Z.add_0_r in HF0; apply HF0; [| lia | cbn; lia]; clear HF0 end.
    do 19 (apply (FINV_store_sp C); [|lia|cbn; lia]). exact (FINV_init C). }
  2:{ split; [symex_reg HR (9%bv : reg) as A9; exact A9|]. split; apply Hfr; reflexivity. }
  split.
  { unfold SAVED6. cbv beta. cbn [x_wsize x_wnext x_whave x_dmask x_beg ffx_of]. rewrite (Z.add_comm (is_wsize s) (is_wnext s)).
    repeat (apply fcells_cons; [rewrite ?Z.add_0_r; eapply cell_mod;
      [ slot_cell
      | first [ reflexivity
              | change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64); rewrite negmask_mod64 by lia; rewrite zmask_pow2 by lia; apply Z.mod_small;
                pose proof (Z.pow_le_mono_r 2 (is_distbits s) 15 ltac:(lia) ltac:(lia)); change (2 ^ 15) with 32768 in *; lia
              | rewrite wrap32_eqmod; f_equal; lia ] ] |]).
    apply fcells_nil. }
  split; [apply SAVED6_ok|].
  split.
  { lazymatch goal with |- cells _ (wbytes ?M (zw sp) (Z_to_le_bytes 8 ?v)) _ _ _ _ _ =>
      pose proof (out_store_sp C M (arr_get (ic_outbuf c)) 0 8 v) as HO0; rewrite Z.add_0_r in HO0; apply HO0; [| lia | cbn; lia]; clear HO0 end.
    do 19 (apply (out_store_sp C); [|lia|cbn; lia]). exact Hout. }
  split; [reflexivity | exact Hout_b].
Qed.
End Walk.
End FXG.
