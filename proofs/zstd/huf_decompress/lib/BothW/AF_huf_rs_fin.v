(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_fdw_sm RF_huf_fdw_st RF_huf_rs_pure
  RF_huf_rs_dl RF_huf_rs_cl RF_huf_rs_fin.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit FseRdKit2.
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac wk_post ::= repeat first [
    match goal with H : bv_unsigned (Z_to_bv 8 ?x) = ?x |- context [bv_unsigned (Z_to_bv 8 ?x)] => rewrite H end
  | match goal with |- context [sx32 (Z_to_bv 64 ?x)] => rewrite (FseRdKit2.sx32_small x) by lia end
  | match goal with |- context [bv_unsigned (Z_to_bv 64 ?x)] => rewrite (inr64_unsigned_lit x) by (unfold inr64; lia) end
  | match goal with |- context [bv_wrap 32 ?x] =>
      replace (bv_wrap 32 x) with x
        by (unfold bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296; rewrite Z.mod_small by lia; reflexivity) end
  | match goal with |- context [bv_swrap 32 ?x] =>
      replace (bv_swrap 32 x) with x
        by (unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
            rewrite Z.mod_small by lia; lia) end
  | match goal with |- context [Z.shiftr ?x 1] => rewrite (Z.shiftr_div_pow2 x 1) by lia; change (2 ^ 1) with 2 end
  | match goal with |- context [(2 * ?x) / 2] => replace ((2 * x) / 2) with x by (rewrite Z.mul_comm, Z.div_mul; lia) end
  | match goal with |- context [Z.land ?x 4294967295] =>
      change (Z.land x 4294967295) with (Z.land x (Z.ones 32)); rewrite (Z.land_ones x 32) by lia;
      rewrite (Z.mod_small x (2 ^ 32)) by lia end
  | match goal with |- context [Z.land ?x 18446744073709551615] =>
      change (Z.land x 18446744073709551615) with (Z.land x (Z.ones 64)); rewrite (Z.land_ones x 64) by lia;
      rewrite (Z.mod_small x (2 ^ 64)) by lia end ].
Ltac wk_lands := repeat first [
    match goal with |- context [Z.land ?x 7] =>
      change (Z.land x 7) with (Z.land x (Z.ones 3)); rewrite (Z.land_ones x 3) by lia; change (2 ^ 3) with 8 end
  | match goal with |- context [Z.land ?x 3] =>
      change (Z.land x 3) with (Z.land x (Z.ones 2)); rewrite (Z.land_ones x 2) by lia; change (2 ^ 2) with 4 end
  | match goal with |- context [Z.land ?x 4294967295] =>
      change (Z.land x 4294967295) with (Z.land x (Z.ones 32)); rewrite (Z.land_ones x 32) by lia end
  | match goal with |- context [Z.land ?x 18446744073709551615] =>
      change (Z.land x 18446744073709551615) with (Z.land x (Z.ones 64)); rewrite (Z.land_ones x 64) by lia end ].
Local Ltac wk_cond ::=
  lazymatch goal with
  | |- negb ?c = true => apply (proj2 (Bool.negb_true_iff c)); wk_cond
  | |- negb ?c = false => apply (proj2 (Bool.negb_false_iff c)); wk_cond
  | |- bv_ltu _ _ = false => wk_norm; wk_lands; apply Z.ltb_ge; lia
  | |- bv_ltu _ _ = true => wk_norm; wk_lands; apply Z.ltb_lt; lia
  | |- bv_eqb _ _ = false => wk_norm; wk_lands; apply Z.eqb_neq; lia
  | |- bv_eqb _ _ = true => wk_norm; wk_lands; apply Z.eqb_eq; lia
  | |- bv_lts _ _ = false => unfold bv_lts; wk_lands; rewrite ?signed_lit by lia; apply Z.ltb_ge; lia
  | |- bv_lts _ _ = true => unfold bv_lts; wk_lands; rewrite ?signed_lit by lia; apply Z.ltb_lt; lia
  end.
Ltac fin_acc := first [ wk_acc_hint
  | lazymatch goal with |- acc_in ?R (Z_to_bv 64 (Z.shiftr ?A 3 + ?c), ?n) =>
      match goal with H : rng R (shad A) ?len |- _ =>
        let nz := eval compute in (Z.of_nat n) in
        apply (rng_acc_litZ R (shad A) len _ n nz H eq_refl ltac:(lia)); unfold shad, ASHOFF; lia end end ].
Local Ltac acc_hint ::= fin_acc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac pregs := let v5 := reg_val 5%Z in let v6 := reg_val 6%Z in let v7 := reg_val 7%Z in let v12 := reg_val 12%Z in
    let v13 := reg_val 13%Z in let v11 := reg_val 11%Z in let v17 := reg_val 17%Z in let v21 := reg_val 21%Z in
    let v22 := reg_val 22%Z in let v23 := reg_val 23%Z in let v26 := reg_val 26%Z in let v27 := reg_val 27%Z in
    let v28 := reg_val 28%Z in let v29 := reg_val 29%Z in let v30 := reg_val 30%Z in let v31 := reg_val 31%Z in
    let v1 := reg_val 1%Z in let v10 := reg_val 10%Z in let v14 := reg_val 14%Z in let v15 := reg_val 15%Z in
    let v16 := reg_val 16%Z in let v8 := reg_val 8%Z in let v9 := reg_val 9%Z in let v18 := reg_val 18%Z in
    let v19 := reg_val 19%Z in let v20 := reg_val 20%Z in let v24 := reg_val 24%Z in let v25 := reg_val 25%Z in
    idtac "ra=" v1 " t0=" v5 " t1=" v6 " t2=" v7 " s0=" v8 " s1=" v9;
    idtac " a0=" v10 " a1=" v11 " a2=" v12 " a3=" v13 " a4=" v14 " a5=" v15 " a6=" v16 " a7=" v17;
    idtac " s2=" v18 " s3=" v19 " s4=" v20 " s5=" v21 " s6=" v22 " s7=" v23 " s8=" v24 " s9=" v25 " s10=" v26 " s11=" v27;
    idtac " t3=" v28 " t4=" v29 " t5=" v30 " t6=" v31;
    lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mm _) => idtac " pc=" pc " mem=" mm end.

Definition smearA (x : Z) : Z :=
  let a := Z.lor x (x ≫ 1) in let b := Z.lor a (a ≫ 2) in let c := Z.lor b (b ≫ 4) in
  let d := Z.lor c (c ≫ 8) in Z.lor d (d ≫ 16).

Fixpoint smchkA (n : nat) (x : Z) : bool :=
  match n with
  | O => true
  | Datatypes.S n' => if smearA x =? 2^(Z.log2 x + 1) - 1 then smchkA n' (x + 1) else false
  end.

Lemma smchkA_ok : forall n x, smchkA n x = true -> forall y, x <= y < x + Z.of_nat n -> smearA y = 2^(Z.log2 y + 1) - 1.
Proof.
  induction n as [|n IH]; intros x H y Hy; [lia|].
  cbn [smchkA] in H. destruct (smearA x =? 2^(Z.log2 x + 1) - 1) eqn:E; [|discriminate].
  destruct (Z.eq_dec y x) as [->|NE]; [apply Z.eqb_eq; exact E|].
  apply (IH (x + 1) H); lia.
Qed.

Lemma smearA_ok : forall x, 1 <= x < 2^19 -> smearA x = 2^(Z.log2 x + 1) - 1.
Proof.
  intros x Hx. apply (smchkA_ok (Z.to_nat 524287) 1); [vm_compute; reflexivity|].
  rewrite Z2Nat.id by lia. change (2^19) with 524288 in Hx. lia.
Qed.

Lemma lor_shr_ltA : forall a j k, 0 <= a < 2^k -> 0 <= j -> 0 <= k -> 0 <= Z.lor a (a ≫ j) < 2^k.
Proof.
  intros a j k Ha Hj Hk.
  assert (S0 : 0 <= a ≫ j) by (apply Z.shiftr_nonneg; lia).
  assert (S1 : a ≫ j <= a) by (rewrite Z.shiftr_div_pow2 by lia; pose proof (Z.pow_pos_nonneg 2 j ltac:(lia) Hj); Z.div_mod_to_equations; nia).
  split; [apply Z.lor_nonneg; lia|].
  destruct (Z.eq_dec (Z.lor a (a ≫ j)) 0) as [E|NE]; [rewrite E; apply Z.pow_pos_nonneg; lia|].
  apply Z.log2_lt_pow2; [pose proof (proj2 (Z.lor_nonneg a (a ≫ j)) (conj (proj1 Ha) S0)); lia|].
  rewrite Z.log2_lor by lia.
  destruct (Z.eq_dec a 0) as [->|NA]; [exfalso; apply NE; rewrite Z.shiftr_0_l; reflexivity|].
  assert (L1 : Z.log2 a < k) by (apply Z.log2_lt_pow2; lia).
  assert (L2 : Z.log2 (a ≫ j) <= Z.log2 a) by (apply Z.log2_le_mono; lia).
  lia.
Qed.

Lemma upd_nat_ForallA : forall (P : Z -> Prop) n v l, Forall P l -> P v -> Forall P (upd_nat n v l).
Proof.
  intros P n; induction n as [|n IH]; intros v l FL PV; destruct l as [|h t]; cbn;
    [constructor | inversion FL; subst; constructor; assumption | constructor
    | inversion FL; subst; constructor; [assumption | apply IH; assumption]].
Qed.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition rresA (HW RK NSP TLP : Z) (R : res hstats) (m' : amem) (a0v : Z) : Prop :=
  match R with
  | Ok h => a0v = hs_ret h
            /\ (exists jrest, u8arr bsegs m' HW (map (Z_to_bv 8) (hs_weights h) ++ jrest) /\ zlen jrest = 256 - hs_nbSymbols h)
            /\ u32arr bsegs m' RK (map (Z_to_bv 64) (hs_rank h))
            /\ rw_cells bsegs m' NSP [C4 (Z_to_bv 64 (hs_nbSymbols h))]
            /\ rw_cells bsegs m' TLP [C4 (Z_to_bv 64 (hs_tableLog h))]
  | Err e => a0v = - e /\ 0 < e < 120
  | Ub | NoFuel => False
  end.

Section FINA.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x23 x24 x25 x26 x27 x29 x30 x31 : word).
  Variables (m0 : amem) (RNG : footprint) (HW RK NSP TLP iS : Z) (ws : list Z) (junk : list byte) (nsv tlv : word).
  Variable Q : machine_state -> Prop.
  Hypothesis HWS : 1 <= zlen ws <= 255.
  Hypothesis HWB : Forall (fun c => 0 <= c < 256) ws.
  Hypothesis HIS : 0 <= iS <= 128.
  Hypothesis HJK : zlen junk = 256 - zlen ws.
  Hypothesis HHW : ablk HW (HW + 256).
  Hypothesis HRK : ablk RK (RK + 52).
  Hypothesis RK4 : RK mod 4 = 0.
  Hypothesis HNS : ablk NSP (NSP + 4).
  Hypothesis HTL : ablk TLP (TLP + 4).
  Hypothesis NS4 : NSP mod 4 = 0.
  Hypothesis TL4 : TLP mod 4 = 0.
  Hypothesis DHR : HW + 256 <= RK \/ RK + 52 <= HW.
  Hypothesis DHN : HW + 256 <= NSP \/ NSP + 4 <= HW.
  Hypothesis DHT : HW + 256 <= TLP \/ TLP + 4 <= HW.
  Hypothesis DRN : RK + 52 <= NSP \/ NSP + 4 <= RK.
  Hypothesis DRT : RK + 52 <= TLP \/ TLP + 4 <= RK.
  Hypothesis DNT : NSP + 4 <= TLP \/ TLP + 4 <= NSP.
  Hypothesis ZHW : zshadow m0 HW 256.
  Hypothesis ZRK : zshadow m0 RK 52.
  Hypothesis UNS : unpoisoned m0 NSP (NSP + 4).
  Hypothesis UTL : unpoisoned m0 TLP (TLP + 4).
  Notation WF := [(HW, HW + 256); (RK, RK + 52); (NSP, NSP + 4); (TLP, TLP + 4)].
  Hypothesis AWD : appW WF.
  Hypothesis RHW : rng RNG HW 256.
  Hypothesis RHWs : rng RNG (shad HW) (nshad (256 + HW mod 8)).
  Hypothesis RRK : rng RNG RK 52.
  Hypothesis RRKs : rng RNG (shad RK) (nshad (52 + RK mod 8)).
  Hypothesis RNS : rng RNG NSP 4.
  Hypothesis RNSs : rng RNG (shad NSP) 1.
  Hypothesis RTL : rng RNG TLP 4.
  Hypothesis RTLs : rng RNG (shad TLP) 1.

  Ltac zbnd := unfold ABIT_MASK; rewrite ?land64_mod; rewrite ?Z.shiftl_mul_pow2 by lia; (try change (2^2) with 4);
    rewrite ?Z.mod_small by lia; lia.
  Ltac zck r ZS0 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch ?W m0 mm |- _ =>
    let v := reg_val r in
    lazymatch v with Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880) =>
      let RDB := fresh "RDB" in
      pose proof (chkZ mm _ _ a (zshadow_appW W m0 mm _ _ ZS0 MU AWD ltac:(lia) ltac:(lia)) ltac:(zbnd) ltac:(zbnd)) as RDB;
      zstep; rewrite ?sxb0; clear RDB
    end end end.
  (* [comment removed for export] *)
  Ltac sjoin_close4 rY :=
    let G := fresh "G" in let G' := fresh "G" in
    zstep; if_cases G; zify_cond G;
    [ zstep; zstep; zstep; if_cases G'; zify_lts G'; [ lazymatch goal with KJ : forall w : word, _ |- _ => let v := reg_val rY in apply (KJ v) end
                                                   | exfalso; Z.div_mod_to_equations; lia ]
    | lazymatch goal with KJ : forall w : word, _ |- _ => let v := reg_val rY in apply (KJ v) end ].
  Ltac schk4J UH C rY J :=
    let b := fresh "b" in let RDB := fresh "RDB" in let CK := fresh "CK" in let SR := fresh "SR" in
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      destruct (AF_fse_rd_base.chk1A mg C (C + 4) C 4 (unpoisoned_appW _ _ mg _ _ UH ltac:(eassumption) ltac:(eassumption) ltac:(lia) ltac:(lia))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK & SR) end;
    zstep; rewrite sxb_sval; clear RDB;
    sjoinF rY J; [| sjoin_close4 rY].

  Ltac srl_sm X k NM :=
    rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 X ≫ k))), (RF_huf_rs_fin.srliw_small X k) by lia;
    change (Z.lor X (X ≫ k)) with NM.

  Notation EXIT mm a0v y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 :=
    (MS (mkR y1 sp gp tp y5 y6 y7 y8 y9 (Z_to_bv 64 a0v) y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 x23 x24 x25 x26 x27
             y28 x29 x30 x31)
       F (Z_to_bv 64 0x9780c) fc None mm (seg_rom bsegs)).

  Ltac kenum k := assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11
    \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15 \/ k = 16 \/ k = 17 \/ k = 18) as KE by lia;
    repeat (destruct KE as [KE|KE]; [subst k; vm_compute; reflexivity|]); subst k; vm_compute; reflexivity.
  Ltac wk_st8 r := let v := reg_val r in
    lazymatch v with Z_to_bv 64 ?E =>
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : u8arr _ mm ?A ?l |- _ =>
        let HS := fresh "HS" in
        assert (HS : store_ok bsegs mm (Z_to_bv 64 E) 1 = true)
          by (apply (u8arr_store_ok _ _ _ _ (E - A) _ H);
              [rewrite ?upd_length, ?length_app, ?length_map, ?length_skipn; lia | unfold wa; f_equal; lia]);
        zstep end end end.
  Ltac fjoin2 rY rZ J :=
    lazymatch goal with |- evtF ?segs ?RNG ?Q (MS ?R ?F _ ?fc ?rv ?m ?rom) =>
      let KJ := fresh "KJ" in
      assert (KJ : forall w1 w2 : word, evtF segs RNG Q (MS (@bvmap_set 5 word (Z_to_bv 5 rY) w1
                                                              (@bvmap_set 5 word (Z_to_bv 5 rZ) w2 R)) F (Z_to_bv 64 J) fc rv m rom));
      [ let w1 := fresh "w" in let w2 := fresh "w" in intros w1 w2; simp_regs | ]
    end.
  Ltac fjoin_close2 rY rZ :=
    let G := fresh "G" in let G' := fresh "G" in
    zstep; if_cases G; zify_cond G;
    [ zstep; zstep; zstep; if_cases G'; zify_lts G';
      [ lazymatch goal with KJ : forall w1 w2 : word, _ |- _ => let v1 := reg_val rY in let v2 := reg_val rZ in apply (KJ v1 v2) end
      | exfalso; first [lia | Z.div_mod_to_equations; lia] ]
    | lazymatch goal with KJ : forall w1 w2 : word, _ |- _ => let v1 := reg_val rY in let v2 := reg_val rZ in apply (KJ v1 v2) end ].
  Ltac fchk4 UH C :=
    let b := fresh "b" in let RDB := fresh "RDB" in let CK := fresh "CK" in let SR := fresh "SR" in
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mg _) =>
      destruct (AF_fse_rd_base.chk1A mg C (C + 4) C 4 (unpoisoned_appW _ _ mg _ _ UH ltac:(eassumption) ltac:(eassumption) ltac:(lia) ltac:(lia))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (b & RDB & CK & SR) end;
    zstep; rewrite sxb_sval; clear RDB.
  Ltac fin_st8 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?E) (le1 (Z_to_bv 64 ?x))) _) =>
      rewrite (FseWalkKit.le1_lit x);
      lazymatch goal with HS : store_ok _ mm _ 1 = true, MU : munch ?W m0 mm, WM : wmono _ m0 mm, MI : mem_inv _ mm,
                          HA : u8arr _ mm HW ?l, RA : u32arr _ mm RK ?rl, NA : rw_cells _ mm NSP ?nc,
                          TA : rw_cells _ mm TLP ?tc |- _ =>
        let m2 := fresh "m" in
        set (m2 := write_to_mem mm (Z_to_bv 64 E) [Z_to_bv 8 x]) in *;
        let MU2 := fresh "MU" in let WM2 := fresh "WM" in let MI2 := fresh "MI" in let HA2 := fresh "HWA" in
        let RA2 := fresh "RKA" in let NA2 := fresh "NSA" in let TA2 := fresh "TLA" in
        assert (MU2 : munch W m0 m2)
          by (unfold m2; change (Z_to_bv 64 E) with (wa E);
              apply munch_write_n with (n := 1); [reflexivity|lia|lia|exact MU|cbn; lia]);
        assert (WM2 : wmono bsegs m0 m2) by (unfold m2; apply wmono_write; exact WM);
        assert (MI2 : mem_inv bsegs m2) by (unfold m2; apply mem_inv_store; [exact MI|exact HS]);
        assert (HA2 : u8arr bsegs m2 HW (upd l (Z.to_nat (E - HW)) (Z_to_bv 8 x)))
          by (unfold m2; replace (Z_to_bv 64 E) with (wa (HW + (E - HW))) by (unfold wa; f_equal; lia);
              apply u8arr_write; [exact HA | rewrite ?upd_length, ?length_app, ?length_map; lia]);
        assert (RA2 : u32arr bsegs m2 RK rl)
          by (unfold m2; change (Z_to_bv 64 E) with (wa E);
              apply u32arr_frame_n with (n := 1); [reflexivity|lia|lia|exact RA|rewrite ?length_map; lia]);
        assert (NA2 : rw_cells bsegs m2 NSP nc)
          by (unfold m2; change (Z_to_bv 64 E) with (wa E);
              apply rw_cells_frame_n with (n := 1); [reflexivity|lia|lia|exact NA|cbn; lia]);
        assert (TA2 : rw_cells bsegs m2 TLP tc)
          by (unfold m2; change (Z_to_bv 64 E) with (wa E);
              apply rw_cells_frame_n with (n := 1); [reflexivity|lia|lia|exact TA|cbn; lia]);
        clearbody m2; clear HS MU WM MI HA RA NA TA;
        rename MU2 into MU; rename WM2 into WM; rename MI2 into MI; rename HA2 into HWA; rename RA2 into RKA;
        rename NA2 into NSA; rename TA2 into TLA
      end
    end.
  Ltac fin_st32 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 (Z.shiftl ?i 2 + RK)) (le4 ?v)) _) =>
      lazymatch goal with HS : store_ok _ mm _ 4 = true, MU : munch ?W m0 mm, WM : wmono _ m0 mm, MI : mem_inv _ mm,
                          HA : u8arr _ mm HW ?l, RA : u32arr _ mm RK ?rl, NA : rw_cells _ mm NSP ?nc,
                          TA : rw_cells _ mm TLP ?tc |- _ =>
        replace (Z_to_bv 64 (Z.shiftl i 2 + RK)) with (wa (RK + 4 * i)) in *
          by (unfold wa; f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia);
        let m2 := fresh "m" in
        set (m2 := write_to_mem mm (wa (RK + 4 * i)) (le4 v)) in *;
        let MU2 := fresh "MU" in let WM2 := fresh "WM" in let MI2 := fresh "MI" in let HA2 := fresh "HWA" in
        let RA2 := fresh "RKA" in let NA2 := fresh "NSA" in let TA2 := fresh "TLA" in
        assert (MU2 : munch W m0 m2)
          by (unfold m2; apply munch_write_n with (n := 4); [reflexivity|lia|lia|exact MU|cbn; lia]);
        assert (WM2 : wmono bsegs m0 m2) by (unfold m2; apply wmono_write; exact WM);
        assert (MI2 : mem_inv bsegs m2) by (unfold m2; apply mem_inv_store; [exact MI|exact HS]);
        assert (RA2 : u32arr bsegs m2 RK (upd rl (Z.to_nat i) v))
          by (unfold m2; apply u32arr_write; [exact RA | rewrite ?length_map, ?upd_length; lia]);
        assert (HA2 : u8arr bsegs m2 HW l)
          by (unfold m2; apply u8arr_frame_n with (n := 4);
              [reflexivity|lia|lia|exact HA|repeat (rewrite length_app || rewrite length_map); cbn [length]; lia]);
        assert (NA2 : rw_cells bsegs m2 NSP nc)
          by (unfold m2; apply rw_cells_frame_n with (n := 4); [reflexivity|lia|lia|exact NA|cbn; lia]);
        assert (TA2 : rw_cells bsegs m2 TLP tc)
          by (unfold m2; apply rw_cells_frame_n with (n := 4); [reflexivity|lia|lia|exact TA|cbn; lia]);
        clearbody m2; clear HS MU WM MI HA RA NA TA;
        rename MU2 into MU; rename WM2 into WM; rename MI2 into MI; rename HA2 into HWA; rename RA2 into RKA;
        rename NA2 into NSA; rename TA2 into TLA
      end
    end.
  Ltac fin_pure CL WP HB1 HB2 UR HB3 HB4 k :=
    unfold RF_huf_rs_pure.rs_tail; cbv zeta; change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat;
    rewrite CL; cbn - [highbit32 shl32 assert load store];
    rewrite (proj2 (Z.eqb_neq _ 0) WP), HB1; cbn [bind];
    rewrite (proj2 (Z.ltb_ge HUF_TABLELOG_MAX (k + 1)) ltac:(unfold HUF_TABLELOG_MAX; lia)); cbv iota;
    rewrite HB2; cbn [bind]; rewrite UR, HB3; cbn [bind]; rewrite HB4; cbn [bind].
  Ltac fin_pure2 CL WP HB1 HB2 UR HB3 HB4 k RJ PA PL1 PS PL2 :=
    fin_pure CL WP HB1 HB2 UR HB3 HB4 k;
    rewrite (proj2 (Z.eqb_eq _ _) (eq_sym RJ)); cbn [negb]; cbv iota;
    rewrite PA; cbn [bind]; rewrite PL1; cbn [bind]; rewrite PS; cbn [bind]; rewrite PL2; cbn [bind].

  Lemma finA : forall m1 rank1 wt (x1 x13 x14 x28 : word),
    collect_loop ws (repeat 0 13) 0 = Ok (rank1, wt) -> RF_huf_rs_cl.cl_ok (zlen ws) rank1 wt ->
    u32arr bsegs m1 RK (map (Z_to_bv 64) rank1) ->
    u8arr bsegs m1 HW (map (Z_to_bv 8) ws ++ junk) ->
    rw_cells bsegs m1 NSP [C4 nsv] -> rw_cells bsegs m1 TLP [C4 tlv] ->
    munch WF m0 m1 -> wmono bsegs m0 m1 -> mem_inv bsegs m1 ->
    (forall m2 a0v (y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28 : word),
       munch WF m0 m2 -> wmono bsegs m0 m2 -> mem_inv bsegs m2 ->
       rresA HW RK NSP TLP (RF_huf_rs_pure.rs_tail ws (zlen ws) iS) m2 a0v ->
       evtF bsegs RNG Q (EXIT m2 a0v y1 y5 y6 y7 y8 y9 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y28)) ->
    evtF bsegs RNG Q
     (MS (mkR x1 sp gp tp (Z_to_bv 64 1) (Z_to_bv 64 12) (Z_to_bv 64 30) (Z_to_bv 64 RK) (Z_to_bv 64 (zlen ws)) (Z_to_bv 64 (-20))
              (Z_to_bv 64 NSP) (Z_to_bv 64 TLP) x13 x14 (Z_to_bv 64 HW) (Z_to_bv 64 (18446744073709551615 - HW)) (Z_to_bv 64 wt)
              (Z_to_bv 64 iS) (Z_to_bv 64 TLP) (Z_to_bv 64 2147450880) (Z_to_bv 64 HW) (Z_to_bv 64 NSP) x23 x24 x25 x26 x27 x28 x29 x30 x31)
         F (Z_to_bv 64 0x975f0) fc None m1 (seg_rom bsegs)).
Proof.
intros m1 rank1 wt x1 x13 x14 x28 CL CO RKA HWA NSA TLA MU WM MI KX.
pose proof CO as (CO1 & CO2 & CO3).
pose proof (ablk_lin _ _ HHW) as (HWa & HWb & HWc & HWd).
pose proof (ablk_lin _ _ HRK) as (RKa & RKb & RKc & RKd).
pose proof (ablk_lin _ _ HNS) as (NSa & NSb & NSc & NSd).
pose proof (ablk_lin _ _ HTL) as (TLa & TLb & TLc & TLd).
unfold AIMG_HI in HWa, RKa, NSa, TLa.
destruct (Z.eq_dec wt 0) as [W0|WP].
{ subst wt. wk_go [0x9733c + 1232].
  apply (KX m1 (-20)); [exact MU|exact WM|exact MI|].
  unfold RF_huf_rs_pure.rs_tail. cbv zeta. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. rewrite CL. cbn.
  repeat split; exact eq_refl. }
assert (WB : 1 <= wt < 2^19) by (change (2^19) with 524288; lia).
wk_step. wk_step. zstep. zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 wt ≫ 1))), (RF_huf_rs_fin.srliw_small wt 1) by lia.
pose proof (lor_shr_ltA wt 1 19 ltac:(lia) ltac:(lia) ltac:(lia)) as RA. set (sa := Z.lor wt (wt ≫ 1)) in *.
zstep. zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 sa ≫ 2))), (RF_huf_rs_fin.srliw_small sa 2) by lia.
pose proof (lor_shr_ltA sa 2 19 ltac:(lia) ltac:(lia) ltac:(lia)) as RB. set (sb := Z.lor sa (sa ≫ 2)) in *.
zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 sb ≫ 4))), (RF_huf_rs_fin.srliw_small sb 4) by lia.
pose proof (lor_shr_ltA sb 4 19 ltac:(lia) ltac:(lia) ltac:(lia)) as RC. set (sc := Z.lor sb (sb ≫ 4)) in *.
zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 sc ≫ 8))), (RF_huf_rs_fin.srliw_small sc 8) by lia.
pose proof (lor_shr_ltA sc 8 19 ltac:(lia) ltac:(lia) ltac:(lia)) as RD. set (sd := Z.lor sc (sc ≫ 8)) in *.
zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 sd ≫ 16))), (RF_huf_rs_fin.srliw_small sd 16) by lia.
change (Z.lor sd (sd ≫ 16)) with (smearA wt). rewrite (smearA_ok wt WB).
clear RA RB RC RD. clearbody sa sb sc sd.
pose proof (Z.log2_nonneg wt) as K0. assert (K1 : Z.log2 wt < 19) by (apply Z.log2_lt_pow2; lia).
pose proof (Z.log2_spec wt ltac:(lia)) as LS. rewrite <- Z.add_1_r in LS.
remember (Z.log2 wt) as k eqn:KD.
do 21 zstep.
lazymatch goal with |- _ => let v13 := reg_val 13 in let v14 := reg_val 14 in
  lazymatch v13 with Z_to_bv 64 ?e13 => lazymatch v14 with Z_to_bv 64 ?e14 =>
    let E13 := fresh "E13" in let E14 := fresh "E14" in
    assert (E13 : e13 = k) by (clear - K0 K1; kenum k);
    assert (E14 : e14 = 31 - k) by (clear - K0 K1; kenum k);
    rewrite E13, E14; clear E13 E14 end end end.
assert (HB1 : highbit32 wt = Ok k) by (unfold highbit32; replace ((0 <? wt) && (wt <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia); rewrite KD; reflexivity).
destruct (Z_lt_le_dec 11 k) as [KH|KL].
{ wk_step. wk_step.
  apply (KX m1 (-20)); [exact MU|exact WM|exact MI|].
  unfold RF_huf_rs_pure.rs_tail. cbv zeta. change (Z.to_nat (HUF_TABLELOG_MAX + 1)) with 13%nat. rewrite CL. cbn - [highbit32].
  rewrite (proj2 (Z.eqb_neq wt 0) WP), HB1. cbn [bind].
  rewrite (proj2 (Z.ltb_lt HUF_TABLELOG_MAX (k + 1)) ltac:(unfold HUF_TABLELOG_MAX; lia)).
  repeat split; exact eq_refl. }
wk_go [0x9733c + 852].
fjoin2 5 6 (0x9733c + 860); [| fchk4 UTL TLP; fjoin_close2 5 6].
wk_go [0x9733c + 876].
replace (32 - (31 - k)) with (k + 1) by lia.
assert (HS : store_ok bsegs m1 (Z_to_bv 64 TLP) 4 = true)
  by (apply (rw_cells_store_ok_at bsegs m1 TLP [C4 tlv] 0 (C4 tlv) 4); [exact TLA | reflexivity | reflexivity | unfold wa; f_equal; lia]).
zstep. clear HS.
assert (P0 : 0 < 2^(k+1)) by (apply Z.pow_pos_nonneg; lia).
assert (P12 : 2^(k+1) <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
assert (P1 : 2^(k+1) = 2 * 2^k) by (rewrite Z.pow_add_r by lia; lia).
assert (A3 : bv_swrap 32 (2 ≪ (k mod 32)) = 2^(k+1))
  by (rewrite Z.mod_small by lia; rewrite Z.shiftl_mul_pow2 by lia; rewrite <- P1;
      unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
      rewrite Z.mod_small by lia; lia).
rewrite A3. clear A3.
wk_go [0x9733c + 884].
zstep. zstep. zstep.
assert (R0 : bv_swrap 32 (2^(k+1) - wt) = 2^(k+1) - wt)
  by (unfold bv_swrap, bv_half_modulus, bv_wrap, bv_modulus; change (2 ^ Z.of_N 32) with 4294967296;
      change (4294967296 / 2) with 2147483648; rewrite Z.mod_small by lia; lia).
rewrite R0. clear R0.
remember (2^(k+1) - wt) as rest eqn:RSD.
assert (RS0 : 1 <= rest <= 2048) by lia.
rewrite (land64_mod rest), (Z.mod_small rest) by lia.
zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 rest ≫ 1))), (RF_huf_rs_fin.srliw_small rest 1) by lia.
pose proof (lor_shr_ltA rest 1 19 ltac:(lia) ltac:(lia) ltac:(lia)) as RA. set (qa := Z.lor rest (rest ≫ 1)) in *.
zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 qa ≫ 2))), (RF_huf_rs_fin.srliw_small qa 2) by lia.
pose proof (lor_shr_ltA qa 2 19 ltac:(lia) ltac:(lia) ltac:(lia)) as RB. set (qb := Z.lor qa (qa ≫ 2)) in *.
zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 qb ≫ 4))), (RF_huf_rs_fin.srliw_small qb 4) by lia.
pose proof (lor_shr_ltA qb 4 19 ltac:(lia) ltac:(lia) ltac:(lia)) as RC. set (qc := Z.lor qb (qb ≫ 4)) in *.
zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 qc ≫ 8))), (RF_huf_rs_fin.srliw_small qc 8) by lia.
pose proof (lor_shr_ltA qc 8 19 ltac:(lia) ltac:(lia) ltac:(lia)) as RD. set (qd := Z.lor qc (qc ≫ 8)) in *.
zstep. zstep.
rewrite (land64_mod (bv_swrap 32 (bv_wrap 32 qd ≫ 16))), (RF_huf_rs_fin.srliw_small qd 16) by lia.
change (Z.lor qd (qd ≫ 16)) with (smearA rest). rewrite (smearA_ok rest ltac:(lia)).
clear RA RB RC RD. clearbody qa qb qc qd.
pose proof (Z.log2_nonneg rest) as J0. assert (J1 : Z.log2 rest < 12) by (apply Z.log2_lt_pow2; lia).
pose proof (Z.log2_spec rest ltac:(lia)) as JS. rewrite <- Z.add_1_r in JS.
remember (Z.log2 rest) as j eqn:JD.
do 19 zstep.
lazymatch goal with |- _ => let v14 := reg_val 14 in
  lazymatch v14 with Z_to_bv 64 ?e14 =>
    let E14 := fresh "E14" in
    assert (E14 : e14 = 31 - j) by (clear - J0 J1; kenum j);
    rewrite E14; clear E14 end end.
wk_step. wk_step. zstep. zstep. zstep.
lazymatch goal with |- _ => let v13 := reg_val 13 in
  lazymatch v13 with Z_to_bv 64 ?e13 =>
    let E13 := fresh "E13" in
    assert (E13 : e13 = 2^j) by (clear - J0 J1; kenum j);
    rewrite E13; clear E13 end end.
assert (PJ0 : 0 < 2^j) by (apply Z.pow_pos_nonneg; lia).
assert (PJ1 : 2^j <= 2048) by (change 2048 with (2^11); apply Z.pow_le_mono_r; lia).
assert (HB2 : shl32 1 (k + 1) = Ok (2^(k+1)))
  by (unfold shl32; replace ((0 <=? k + 1) && (k + 1 <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia);
      unfold u32; rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity).
assert (UR : u32 (2^(k+1) - wt) = rest) by (unfold u32; rewrite Z.mod_small by lia; lia).
assert (HB3 : highbit32 rest = Ok j)
  by (unfold highbit32; replace ((0 <? rest) && (rest <? 2^32)) with true by (symmetry; apply andb_true_iff; split; apply Z.ltb_lt; lia); rewrite JD; reflexivity).
assert (HB4 : shl32 1 j = Ok (2^j))
  by (unfold shl32; replace ((0 <=? j) && (j <? 32)) with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia);
      unfold u32; rewrite Z.mul_1_l, Z.mod_small by lia; reflexivity).
destruct (Z.eq_dec rest (2^j)) as [RJ|RJ].
2: { wk_step. wk_step.
     apply (KX m (-20)); [exact MU|exact WM|exact MI|].
     fin_pure CL WP HB1 HB2 UR HB3 HB4 k.
     rewrite (proj2 (Z.eqb_neq (2^j) rest) ltac:(lia)). cbn [negb].
     repeat split; exact eq_refl. }
wk_step. wk_step.
pose proof (zshadow_appW _ m0 m _ _ ZHW MU AWD ltac:(lia) ltac:(lia)) as ZH.
wk_go [0x9733c + 1072].
replace (32 - (31 - j)) with (j + 1) by lia.
wk_st8 13. clear ZH. fin_st8.
destruct junk as [|jh jr]; [cbn in HJK; lia|].
assert (HJR : zlen jr = 255 - zlen ws) by (cbn [length] in HJK; lia).
replace (Z.to_nat (HW + zlen ws - HW)) with (length (map (Z_to_bv 8) ws)) in HWA by (rewrite length_map; lia).
rewrite RF_huf_rs_fin.upd_app_mid' in HWA.
replace (map (Z_to_bv 8) ws ++ Z_to_bv 8 (j + 1) :: jr) with (map (Z_to_bv 8) (ws ++ [j + 1]) ++ jr) in HWA
  by (rewrite map_app, <- app_assoc; reflexivity).
set (hw2 := map (Z_to_bv 8) (ws ++ [j + 1]) ++ jr) in HWA.
assert (HL2 : zlen hw2 = 256) by (unfold hw2; repeat (rewrite length_app || rewrite length_map); cbn [length]; lia).
pose proof (zshadow_appW _ m0 m2 _ _ ZRK MU AWD ltac:(lia) ltac:(lia)) as ZR.
assert (RL1 : 0 <= j + 1 < 13) by lia.
wk_go [0x9733c + 1116].
assert (RV : 0 <= Znth (j + 1) rank1 <= zlen ws)
  by (unfold Znth; rewrite Forall_forall in CO2; apply CO2; apply nth_In; lia).
rewrite (FseRdKit2.sx32_small (Znth (j + 1) rank1)) by lia.
rewrite (inr64_unsigned_lit (Znth (j + 1) rank1)) by (unfold inr64; lia).
wk_st32 12. clear ZR. fin_st32.
rewrite <- (map_upd_nat (Z_to_bv 64) (Z.to_nat (j + 1)) (Znth (j + 1) rank1 + 1) rank1) in RKA.
pose proof (zshadow_appW _ m0 m3 _ _ ZRK MU AWD ltac:(lia) ltac:(lia)) as ZR.
wk_go [0x9733c + 1148].
replace (Z_to_bv 64 (RK + 4)) with (Z_to_bv 64 (Z.shiftl 1 2 + RK)) by (f_equal; rewrite Z.shiftl_mul_pow2 by lia; lia).
assert (UL : zlen (upd_nat (Z.to_nat (j + 1)) (Znth (j + 1) rank1 + 1) rank1) = 13) by (rewrite upd_nat_length; lia).
wk_step. clear ZR.
set (rank2 := upd_nat (Z.to_nat (j + 1)) (Znth (j + 1) rank1 + 1) rank1) in *.
assert (FR2 : Forall (fun v => 0 <= v <= zlen ws + 1) rank2)
  by (apply upd_nat_ForallA; [eapply Forall_impl; [|exact CO2]; cbn; intros; lia | lia]).
assert (R1B : 0 <= Znth 1 rank2 <= zlen ws + 1)
  by (unfold Znth; rewrite Forall_forall in FR2; apply FR2; apply nth_In; lia).
rewrite (FseRdKit2.sx32_small (Znth 1 rank2)) by lia.
assert (PA : assert (zlen ws <? HUF_SYMBOLVALUE_MAX + 1) = Ok tt)
  by (unfold assert; rewrite (proj2 (Z.ltb_lt (zlen ws) (HUF_SYMBOLVALUE_MAX + 1)) ltac:(unfold HUF_SYMBOLVALUE_MAX; lia)); reflexivity).
assert (PL1 : load rank1 (j + 1) = Ok (Znth (j + 1) rank1))
  by (unfold load; replace ((0 <=? j + 1) && (j + 1 <? FseNCount.Zlength rank1)) with true; [reflexivity|];
      symmetry; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; unfold FseNCount.Zlength; lia]).
assert (PS : store rank1 (j + 1) (u32 (Znth (j + 1) rank1 + 1)) = Ok rank2)
  by (unfold store; replace ((0 <=? j + 1) && (j + 1 <? FseNCount.Zlength rank1)) with true;
      [unfold Zupd, u32; rewrite Z.mod_small by lia; reflexivity|];
      symmetry; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; unfold FseNCount.Zlength; lia]).
assert (PL2 : load rank2 1 = Ok (Znth 1 rank2))
  by (unfold load; replace ((0 <=? 1) && (1 <? FseNCount.Zlength rank2)) with true; [reflexivity|];
      symmetry; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; unfold FseNCount.Zlength; lia]).
destruct (Z_lt_le_dec (Znth 1 rank2) 2) as [R1L|R1H].
{ wk_go [0x9733c + 1232].
  apply (KX m3 (-20)); [exact MU|exact WM|exact MI|].
  fin_pure2 CL WP HB1 HB2 UR HB3 HB4 k RJ PA PL1 PS PL2.
  rewrite (proj2 (Z.ltb_lt (Znth 1 rank2) 2) R1L); cbn [orb].
  repeat split; exact eq_refl. }
wk_go [0x9733c + 1164].
rewrite (RF_huf_rs_fin.land1_mod2 (Znth 1 rank2)).
destruct (Z.eq_dec (Znth 1 rank2 mod 2) 0) as [R1E|R1O].
2: { wk_go [0x9733c + 1232].
     apply (KX m3 (-20)); [exact MU|exact WM|exact MI|].
     fin_pure2 CL WP HB1 HB2 UR HB3 HB4 k RJ PA PL1 PS PL2.
     rewrite (proj2 (Z.ltb_ge (Znth 1 rank2) 2) R1H), (RF_huf_rs_fin.land1_mod2 (Znth 1 rank2)),
       (proj2 (Z.eqb_eq (Znth 1 rank2 mod 2) 1) ltac:(lia)); cbn [orb].
     repeat split; exact eq_refl. }
wk_go [0x9733c + 1188].
fjoin2 10 12 (0x9733c + 1196); [| fchk4 UNS NSP; fjoin_close2 10 12].
assert (HS : store_ok bsegs m3 (Z_to_bv 64 NSP) 4 = true)
  by (apply (rw_cells_store_ok_at bsegs m3 NSP [C4 nsv] 0 (C4 nsv) 4); [exact NSA | reflexivity | reflexivity | unfold wa; f_equal; lia]).
wk_go [0x9733c + 1232].
apply (KX m4 (iS + 1)); [exact MU|exact WM|exact MI|].
fin_pure2 CL WP HB1 HB2 UR HB3 HB4 k RJ PA PL1 PS PL2.
rewrite (proj2 (Z.ltb_ge (Znth 1 rank2) 2) R1H), (RF_huf_rs_fin.land1_mod2 (Znth 1 rank2)),
  (proj2 (Z.eqb_neq (Znth 1 rank2 mod 2) 1) ltac:(lia)); cbn [orb]; cbv iota.
unfold rresA; cbn [hs_ret hs_weights hs_rank hs_nbSymbols hs_tableLog].
unfold u32; rewrite (Z.mod_small (zlen ws + 1)) by lia.
split; [reflexivity|].
split; [exists jr; split; [exact HWA | lia] | split; [exact RKA | split; [exact NSA | exact TLA]]].
Qed.
End FINA.
End CANSEC1.
