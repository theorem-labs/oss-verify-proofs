(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require SymExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast Inftrees.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem InffastModel InffastSafe.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InffastCtx IfSpec IfSpec6 If6_1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac symex_auto ::=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap64_small by lia;
  try solve [ reflexivity | assumption | symex_ret_auto | symex_read_auto | symex_store_auto | symex_sok_auto | lia | split; lia ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Lemma le4_eqm : forall a b, a mod 2 ^ 32 = b mod 2 ^ 32 -> Z_to_le_bytes 4 a = Z_to_le_bytes 4 b.
Proof.
  intros a b H. rewrite <- (SymExec.Z_to_le_bytes_mod 4 a), <- (SymExec.Z_to_le_bytes_mod 4 b). change (8 * Z.of_nat 4) with 32.
  rewrite H. reflexivity.
Qed.
Lemma le4_wrap32 : forall a, Z_to_le_bytes 4 (wrap32 a) = Z_to_le_bytes 4 a.
Proof. intros a. apply le4_eqm. rewrite wrap32_mod. apply Z.mod_mod. lia. Qed.
Lemma eqm32_szwrap_add : forall x k, (szwrap 32 x + k) mod 2 ^ 32 = (x + k) mod 2 ^ 32.
Proof. intros x k. rewrite <- Zplus_mod_idemp_l, szwrap_eqm, Zplus_mod_idemp_l by lia. reflexivity. Qed.
Lemma wb_congr : forall (m m' : word -> option byte) (a : word) bs bs', m = m' -> bs = bs' -> wbytes m a bs = wbytes m' a bs'.
Proof. intros m m' a bs bs' -> ->. reflexivity. Qed.
Lemma le_congr : forall n x y, x = y -> Z_to_le_bytes n x = Z_to_le_bytes n y.
Proof. intros n x y ->. reflexivity. Qed.

Definition exit_mem6 (m : word -> option byte) (ZP S I0 P0 xlast xend fin fout hold bits : Z) : word -> option byte :=
  let len := bits / 8 in
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (zw ZP) (Z_to_le_bytes 8 (I0 + (fin - len))))
    (zw (ZP + 24)) (Z_to_le_bytes 8 (P0 + fout)))
    (zw (ZP + 8)) (Z_to_le_bytes 4 (wrap32 (5 + (xlast - (fin - len))))))
    (zw (ZP + 32)) (Z_to_le_bytes 4 (wrap32 (257 + (xend - fout)))))
    (zw (S + 96)) (Z_to_le_bytes 8 (hold mod 2 ^ (bits mod 8))))
    (zw (S + 104)) (Z_to_le_bytes 4 (bits mod 8)).

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

Lemma blk_LATCH : forall m fin fout regs,
  KR regs -> getr regs 16 = zw (I0 + fin) -> getr regs 22 = zw (P0 + fout) -> 0 <= fin <= IN -> 0 <= fout <= ON ->
  exists R, msteps s6u_segs (mkst regs (0x22820 : word) m s6u_rom)
              (mkst R (if (fin <? x_last X) && (fout <? x_end X) then (0x2274c : word) else (0x22d54 : word)) m s6u_rom)
   /\ KR R /\ getr R 9 = zw 14 /\ (forall r, reg_in r [9]%bv = false -> getr R r = getr regs r).
Proof.
  intros m fin fout regs HK H16 H22 Hfin Hfout. pose proof HK as HK'. kr_destr HK. clear_layout.
  destruct (Z.ltb_spec fin (x_last X)) as [H1|H1]; cbn [andb].
  - destruct (Z.ltb_spec fout (x_end X)) as [H2'|H2'].
    + symex s6u_segs fastC6 5%nat [false; true] NoReads
        [(16, EAdd (EVar 32%nat) (EVar 33%nat)); (22, EAdd (EVar 34%nat) (EVar 35%nat)); (12, EAdd (EVar 32%nat) (EVar 36%nat)); (21, EAdd (EVar 34%nat) (EVar 37%nat))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^64); (37%nat, 2^64)] NoRegions
        [I0; fin; P0; fout; x_last X; x_end X] NoVals F0 F0' (mkst regs (0x22820 : word) m s6u_rom) R HR Hfr Hms.
      all: try side. all: try brc.
      exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity |].
      symex_reg HR (9%bv : reg) as A9. split; [exact A9 | fr_weak Hfr].
    + symex s6u_segs fastC6 5%nat [false; false] NoReads
        [(16, EAdd (EVar 32%nat) (EVar 33%nat)); (22, EAdd (EVar 34%nat) (EVar 35%nat)); (12, EAdd (EVar 32%nat) (EVar 36%nat)); (21, EAdd (EVar 34%nat) (EVar 37%nat))]
        [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^64); (37%nat, 2^64)] NoRegions
        [I0; fin; P0; fout; x_last X; x_end X] NoVals F0 F0' (mkst regs (0x22820 : word) m s6u_rom) R HR Hfr Hms.
      all: try side. all: try brc.
      exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity |].
      symex_reg HR (9%bv : reg) as A9. split; [exact A9 | fr_weak Hfr].
  - symex s6u_segs fastC6 5%nat [true] NoReads
      [(16, EAdd (EVar 32%nat) (EVar 33%nat)); (22, EAdd (EVar 34%nat) (EVar 35%nat)); (12, EAdd (EVar 32%nat) (EVar 36%nat)); (21, EAdd (EVar 34%nat) (EVar 37%nat))]
      [(32%nat, 2^63); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^32); (36%nat, 2^64); (37%nat, 2^64)] NoRegions
      [I0; fin; P0; fout; x_last X; x_end X] NoVals F0 F0' (mkst regs (0x22820 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: try brc.
    exists R. split; [exact Hms|]. split; [eapply KREGS6_frame; [ | exact HK' | exact Hfr]; reflexivity |].
    symex_reg HR (9%bv : reg) as A9. split; [exact A9 | fr_weak Hfr].
Qed.

Definition exit_rds : list (option expr) :=
  [RVal (EVar 43%nat); RVal (EVar 44%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (EVar 47%nat); RVal (EVar 48%nat); RVal (EVar 49%nat);
   RVal (EVar 50%nat); RVal (EVar 51%nat); RVal (EVar 52%nat); RVal (EVar 53%nat); RVal (EVar 54%nat); RVal (EVar 55%nat)].
Local Ltac exit_run dirs vals st R HR Hfr Hms :=
  symex s6u_segs (CFG [] [] [EVar 43%nat] [] []) 60%nat dirs exit_rds
    [(15, EVar 32%nat); (16, EAdd (EVar 33%nat) (EVar 34%nat)); (22, EAdd (EVar 35%nat) (EVar 36%nat)); (14, EVar 37%nat);
     (12, EAdd (EVar 33%nat) (EVar 38%nat)); (21, EAdd (EVar 35%nat) (EVar 39%nat)); (10, EVar 40%nat); (11, EVar 41%nat); (2, EVar 42%nat)]
    [(32%nat, 64); (33%nat, 2^63); (34%nat, 2^63); (35%nat, 2^63); (36%nat, 2^32); (37%nat, 2^64); (38%nat, 2^64); (39%nat, 2^64);
     (40%nat, 2^63); (41%nat, 2^63); (42%nat, 2^63);
     (43%nat, 2^64); (44%nat, 2^64); (45%nat, 2^64); (46%nat, 2^64); (47%nat, 2^64); (48%nat, 2^64); (49%nat, 2^64); (50%nat, 2^64);
     (51%nat, 2^64); (52%nat, 2^64); (53%nat, 2^64); (54%nat, 2^64); (55%nat, 2^64)] NoRegions
    vals NoVals F0 F0' st R HR Hfr Hms.
Local Ltac exit_post R HR Hfr Hms H1 NM Hhm :=
    rewrite H1 in Hms;
    exists R; split;
    [ match type of Hms with msteps _ _ (mkst _ _ ?mm _) =>
        match goal with |- msteps _ _ (mkst _ _ ?em _) => replace em with mm; [exact Hms|] end end;
      unfold exit_mem6; change (2 ^ 3) with 8;
      apply wb_congr; [| apply le_congr; reflexivity];
      apply wb_congr; [| apply le_congr; exact NM];
      apply wb_congr; [| rewrite le4_wrap32; apply le4_eqm; rewrite ?eqm32_szwrap_add; apply (f_equal (fun z => z mod 2 ^ 32)); lia];
      apply wb_congr; [| rewrite le4_wrap32; apply le4_eqm; rewrite ?eqm32_szwrap_add; apply (f_equal (fun z => z mod 2 ^ 32)); lia];
      apply wb_congr; [| apply le_congr; lia];
      apply wb_congr; [reflexivity | apply le_congr; lia]
    | let A2 := fresh "A2" in
      symex_reg HR (2%bv : reg) as A2;
      split; [rewrite A2; f_equal; lia|];
      split;
      [ let k := fresh "k" in let Hk := fresh "Hk" in
        intros k Hk; cbn in Hk;
        repeat (destruct Hk as [<-|Hk]; [lazymatch goal with |- getr _ ?n = _ => let Q := fresh in symex_reg HR n as Q; rewrite Q; first [reflexivity | apply zw_u] end|]);
        destruct Hk
      | split; [apply Hfr; reflexivity|]; split; [apply Hfr; reflexivity|]; exact Hhm ] ].
Local Ltac sgn :=
    lazymatch goal with
    | |- @ex _ _ => idtac
    | |- _ => change (2 ^ 3) with 8 in *; rewrite ?szwrap64_small by lia;
              repeat match goal with |- context [if ?a <? ?b then _ else _] => destruct (Z.ltb_spec a b) end; first [lia | mlia | exfalso; mlia]
    end.

Lemma blk_EXIT : forall regs0 regs m fin fout hold bits,
  getr regs 2 = zw sp -> getr regs 10 = zw ZP -> getr regs 11 = zw S -> getr regs 12 = zw (I0 + x_last X) -> getr regs 21 = zw (P0 + x_end X) ->
  fcells s6u_segs sp m (SAVED6 S P0 WB regs0 X) ->
  (forall x : word, sp <= bv_unsigned x < sp + 160 -> m x <> None) ->
  (forall x : word, ZP <= bv_unsigned x < ZP + 112 -> m x <> None) ->
  (forall x : word, S <= bv_unsigned x < S + 7176 -> m x <> None) ->
  getr regs0 1 = ra ->
  getr regs 16 = zw (I0 + fin) -> getr regs 22 = zw (P0 + fout) -> getr regs 14 = zw hold -> getr regs 15 = zw bits ->
  0 <= bits < 64 -> 0 <= hold < 2 ^ 64 -> 0 <= fin <= IN -> bits / 8 <= fin -> 0 <= fout <= ON ->
  ic_next_in c <= fin ->
  exists R, msteps s6u_segs (mkst regs (0x22d54 : word) m s6u_rom)
              (mkst R ra (exit_mem6 m ZP S I0 P0 (x_last X) (x_end X) fin fout hold bits) s6u_rom)
   /\ getr R 2 = zw (sp + 160)
   /\ (forall k : reg, In k [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr R k = getr regs0 k)
   /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4
   /\ 0 <= hold mod 2 ^ (bits mod 8) < 2 ^ (bits mod 8).
Proof.
  intros regs0 regs m fin fout hold bits K2 K10 K11 K12 K21 HS Wsp WZ WS H1 H16 H22 H14 H15 Hbits Hhold Hfin Hfinlen Hfout HfinN.
  assert (HxlN : x_last X <= ic_next_in c + 2 ^ 32).
  { clear HS. cbn [x_last ffx_of]. rewrite wrap32_mod. pose proof (Z.mod_pos_bound (ic_avail_in c - 5) (2 ^ 32) ltac:(lia)). lia. }
  assert (Hu : forall k, 0 <= bv_unsigned (getr regs0 k) < 2 ^ 64) by (intros k; apply (u64_range (getr regs0 k))).
  pose proof (Hu 1%bv) as U1. pose proof (Hu 8%bv) as U8. pose proof (Hu 9%bv) as U9. pose proof (Hu 18%bv) as U18. pose proof (Hu 19%bv) as U19.
  pose proof (Hu 20%bv) as U20. pose proof (Hu 21%bv) as U21. pose proof (Hu 22%bv) as U22. pose proof (Hu 23%bv) as U23.
  pose proof (Hu 24%bv) as U24. pose proof (Hu 25%bv) as U25. pose proof (Hu 26%bv) as U26. pose proof (Hu 27%bv) as U27. clear Hu.
  unfold SAVED6 in HS. cbv beta zeta in HS.
  apply fcells_cons_inv in HS as [S152 HS]. apply fcells_cons_inv in HS as [S144 HS]. apply fcells_cons_inv in HS as [S136 HS].
  apply fcells_cons_inv in HS as [S128 HS]. apply fcells_cons_inv in HS as [S120 HS]. apply fcells_cons_inv in HS as [S112 HS].
  apply fcells_cons_inv in HS as [S104 HS]. apply fcells_cons_inv in HS as [S96 HS]. apply fcells_cons_inv in HS as [S88 HS].
  apply fcells_cons_inv in HS as [S80 HS]. apply fcells_cons_inv in HS as [S72 HS]. apply fcells_cons_inv in HS as [S64 HS].
  apply fcells_cons_inv in HS as [S56 _].
  unfold cell in S152, S144, S136, S128, S120, S112, S104, S96, S88, S80, S72, S64, S56.
  pose proof (Z.mod_pos_bound bits 8 ltac:(lia)) as Hb8.
  pose proof (Z.pow_pos_nonneg 2 (bits mod 8) ltac:(lia) ltac:(lia)) as Hp0.
  pose proof (Z.pow_le_mono_r 2 (bits mod 8) 7 ltac:(lia) ltac:(lia)) as Hp7. change (2 ^ 7) with 128 in Hp7.
  pose proof (Z.mod_pos_bound hold (2 ^ (bits mod 8)) Hp0) as Hhm.
  assert (Hlen : 0 <= bits / 8 < 8) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (NM : Z.land hold (Z.lxor (zaluw ALU_SLL (-1) (bits mod 8)) (-1)) = hold mod 2 ^ (bits mod 8)).
  { rewrite Z.land_comm. apply negmask_land; lia. }
  pose proof Hd_spZ as HdspZ. pose proof Hd_spS as HdspS. pose proof Hd_ZS as HdZS. clear_layout.
  destruct (Z.ltb_spec (fin - bits / 8) (x_last X)) as [Hi|Hi]; [destruct (Z.ltb_spec fout (x_end X)) as [Ho|Ho]|destruct (Z.ltb_spec fout (x_end X)) as [Ho|Ho]].
  - exit_run [false; false; false; true; false; true]
      [bits; I0; fin; P0; fout; hold; x_last X; x_end X; ZP; S; sp;
       bv_unsigned (getr regs0 1%bv); bv_unsigned (getr regs0 8%bv); bv_unsigned (getr regs0 9%bv); bv_unsigned (getr regs0 18%bv);
       bv_unsigned (getr regs0 19%bv); bv_unsigned (getr regs0 20%bv); bv_unsigned (getr regs0 21%bv); bv_unsigned (getr regs0 22%bv);
       bv_unsigned (getr regs0 23%bv); bv_unsigned (getr regs0 24%bv); bv_unsigned (getr regs0 25%bv); bv_unsigned (getr regs0 26%bv);
       bv_unsigned (getr regs0 27%bv)]
      (mkst regs (0x22d54 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards. all: sgn.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => idtac "LEFT_EXIT_TT" G end.
    exit_post R HR Hfr Hms H1 NM Hhm.
  - exit_run [false; false; false; true; true; false]
      [bits; I0; fin; P0; fout; hold; x_last X; x_end X; ZP; S; sp;
       bv_unsigned (getr regs0 1%bv); bv_unsigned (getr regs0 8%bv); bv_unsigned (getr regs0 9%bv); bv_unsigned (getr regs0 18%bv);
       bv_unsigned (getr regs0 19%bv); bv_unsigned (getr regs0 20%bv); bv_unsigned (getr regs0 21%bv); bv_unsigned (getr regs0 22%bv);
       bv_unsigned (getr regs0 23%bv); bv_unsigned (getr regs0 24%bv); bv_unsigned (getr regs0 25%bv); bv_unsigned (getr regs0 26%bv);
       bv_unsigned (getr regs0 27%bv)]
      (mkst regs (0x22d54 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards. all: sgn.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => idtac "LEFT_EXIT_TF" G end.
    exit_post R HR Hfr Hms H1 NM Hhm.
  - exit_run [false; false; true; false; false; true]
      [bits; I0; fin; P0; fout; hold; x_last X; x_end X; ZP; S; sp;
       bv_unsigned (getr regs0 1%bv); bv_unsigned (getr regs0 8%bv); bv_unsigned (getr regs0 9%bv); bv_unsigned (getr regs0 18%bv);
       bv_unsigned (getr regs0 19%bv); bv_unsigned (getr regs0 20%bv); bv_unsigned (getr regs0 21%bv); bv_unsigned (getr regs0 22%bv);
       bv_unsigned (getr regs0 23%bv); bv_unsigned (getr regs0 24%bv); bv_unsigned (getr regs0 25%bv); bv_unsigned (getr regs0 26%bv);
       bv_unsigned (getr regs0 27%bv)]
      (mkst regs (0x22d54 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards. all: sgn.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => idtac "LEFT_EXIT_FT" G end.
    exit_post R HR Hfr Hms H1 NM Hhm.
  - exit_run [false; false; true; false; true; false]
      [bits; I0; fin; P0; fout; hold; x_last X; x_end X; ZP; S; sp;
       bv_unsigned (getr regs0 1%bv); bv_unsigned (getr regs0 8%bv); bv_unsigned (getr regs0 9%bv); bv_unsigned (getr regs0 18%bv);
       bv_unsigned (getr regs0 19%bv); bv_unsigned (getr regs0 20%bv); bv_unsigned (getr regs0 21%bv); bv_unsigned (getr regs0 22%bv);
       bv_unsigned (getr regs0 23%bv); bv_unsigned (getr regs0 24%bv); bv_unsigned (getr regs0 25%bv); bv_unsigned (getr regs0 26%bv);
       bv_unsigned (getr regs0 27%bv)]
      (mkst regs (0x22d54 : word) m s6u_rom) R HR Hfr Hms.
    all: try side. all: guards. all: sgn.
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => idtac "LEFT_EXIT_FF" G end.
    exit_post R HR Hfr Hms H1 NM Hhm.
Qed.

End Walk.

End FXG.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
