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
Local Ltac acc_hint ::= wk_acc_hint.
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
Local Ltac wk_src r ::= let v := reg_val r in
  lazymatch v with Z_to_bv 64 ?E =>
    match goal with H : bytes_at _ _ ?A (map (Z_to_bv 8) ?l) |- _ =>
      let RD := fresh "RD" in
      pose proof (HufWalkKit.src_rd _ _ _ _ (E - A) H ltac:(lia)) as RD;
      replace (A + (E - A)) with E in RD by lia; ring_simplify (E - A) in RD; zstep; clear RD end end.
Ltac wk_lands := repeat first [
    match goal with |- context [Z.land ?x 7] =>
      change (Z.land x 7) with (Z.land x (Z.ones 3)); rewrite (Z.land_ones x 3) by lia; change (2 ^ 3) with 8 end
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

Section CANSEC1. Context {rc : runConstT}.

Section DLA.
  Variables (ra sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (x8 x13 x14 x17 x18 x19 x21 x22 x23 x24 x25 x26 x27 : word).
  Variables (m0 : amem) (RNG : footprint) (HW S oSize K : Z) (src : list Z) (jh : list byte).
  Variable Q : machine_state -> Prop.
  Hypothesis HOS : 1 <= oSize <= 255.
  Hypothesis HK : K = (oSize - 1) / 2.
  Hypothesis HJH : zlen jh = 256.
  Hypothesis HSRC : K + 2 <= zlen src.
  Hypothesis HSB : Forall (fun c => 0 <= c < 256) src.
  Hypothesis HHW : ablk HW (HW + 256).
  Hypothesis HS0 : ablk S (S + zlen src).
  Hypothesis DHS : HW + 256 <= S \/ S + zlen src <= HW.
  Hypothesis ZHW : zshadow m0 HW 256.
  Hypothesis USRC : unpoisoned m0 S (S + zlen src).
  Hypothesis AWD : appW [(HW, HW + 256)].
  Hypothesis RHW : rng RNG HW 256.
  Hypothesis RHWs : rng RNG (shad HW) (nshad (256 + HW mod 8)).
  Hypothesis RS : rng RNG S (zlen src).
  Hypothesis RSs : rng RNG (shad S) (nshad (zlen src + S mod 8)).

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
  Definition dlA_inv (m1 : amem) (acc : list Z) : Prop :=
    u8arr bsegs m1 HW (map (Z_to_bv 8) acc ++ skipn (length acc) jh)
    /\ bytes_at bsegs m1 S (map (Z_to_bv 8) src)
    /\ munch [(HW, HW + 256)] m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1.

  (* [comment removed for export] *)
  Notation ST pc mm x6 x7 x10 x11 x16 x28 x29 x30 x31 :=
    (MS (mkR ra sp gp tp (Z_to_bv 64 (18446744073709551615 - HW)) x6 x7 x8 (Z_to_bv 64 oSize) x10 x11 (Z_to_bv 64 HW) x13 x14
             (Z_to_bv 64 (S + 1)) x16 x17 x18 x19 (Z_to_bv 64 2147450880) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom bsegs)).

  Lemma dlA_upd2 : forall (acc : list Z) (js : list byte) x y,
    (length acc + 2 <= length js)%nat ->
    upd (upd (map (Z_to_bv 8) acc ++ skipn (length acc) js) (length acc) (Z_to_bv 8 x)) (Datatypes.S (length acc)) (Z_to_bv 8 y)
    = map (Z_to_bv 8) (acc ++ [x; y]) ++ skipn (length (acc ++ [x; y])) js.
  Proof.
    induction acc as [|a acc IH]; intros js x y Hl.
    - destruct js as [|j0 [|j1 js]]; cbn in Hl |- *; [lia|lia|reflexivity].
    - destruct js as [|j0 js]; cbn in Hl; [lia|]. cbn [map app length skipn upd]. f_equal. apply IH. lia.
  Qed.

  Lemma dlA_step : forall fuel k acc, 0 <= k <= K ->
    direct_loop src (Datatypes.S fuel) (2 * k) oSize acc
    = direct_loop src fuel (2 * k + 2) oSize (acc ++ [Znth (k + 1) src / 16; Z.land (Znth (k + 1) src) 15]).
  Proof.
    intros fuel k acc Hk. cbn [direct_loop].
    rewrite (proj2 (Z.ltb_lt (2 * k) oSize)) by lia.
    unfold load. rewrite FseLemmas.Zlength_correct.
    replace (1 + 2 * k / 2) with (k + 1) by (rewrite (Z.mul_comm 2 k), Z.div_mul by lia; lia).
    rewrite (proj2 (Z.leb_le 0 (k + 1))) by lia.
    rewrite (proj2 (Z.ltb_lt (k + 1) (zlen src))) by lia.
    cbn [andb bind]. unfold assert, HUF_SYMBOLVALUE_MAX.
    rewrite (proj2 (Z.ltb_lt (2 * k + 1) (255 + 1))) by lia.
    cbn [bind]. reflexivity.
  Qed.

  Lemma dlA_stop : forall fuel n acc, oSize <= n -> direct_loop src (Datatypes.S fuel) n oSize acc = Ok acc.
  Proof. intros fuel n acc H. cbn [direct_loop]. rewrite (proj2 (Z.ltb_ge n oSize)) by lia. reflexivity. Qed.

  Lemma dlA_forall : forall acc b, Forall (fun c => 0 <= c < 256) acc -> 0 <= b < 256 ->
    Forall (fun c => 0 <= c < 256) (acc ++ [b / 16; Z.land b 15]).
  Proof.
    intros acc b HA Hb. apply List.Forall_app. split; [exact HA|].
    assert (L : Z.land b 15 = b mod 16) by (change 15 with (Z.ones 4); rewrite Z.land_ones by lia; reflexivity).
    rewrite L. repeat constructor; lia.
  Qed.

  Ltac wk_st8 r := let v := reg_val r in
    lazymatch v with Z_to_bv 64 ?E =>
      lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      match goal with H : u8arr _ mm ?A ?l |- _ =>
        let HS := fresh "HS" in
        assert (HS : store_ok bsegs mm (Z_to_bv 64 E) 1 = true)
          by (apply (u8arr_store_ok _ _ _ _ (E - A) _ H);
              [rewrite ?upd_length, ?length_app, ?length_map, ?length_skipn; lia | unfold wa; f_equal; lia]);
        zstep end end end.
  Ltac dl_st8 :=
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem ?mm (Z_to_bv 64 ?E) (le1 (Z_to_bv 64 ?x))) _) =>
      rewrite (FseWalkKit.le1_lit x);
      lazymatch goal with HS : store_ok _ mm _ 1 = true, MU : munch ?W m0 mm, WM : wmono _ m0 mm, MI : mem_inv _ mm,
                          HA : u8arr _ mm HW ?l, SR : bytes_at _ mm S ?bs |- _ =>
        let m2 := fresh "m" in
        set (m2 := write_to_mem mm (Z_to_bv 64 E) [Z_to_bv 8 x]) in *;
        let MU2 := fresh "MU" in let WM2 := fresh "WM" in let MI2 := fresh "MI" in let HA2 := fresh "HWA" in
        let SR2 := fresh "SRA" in let ZH2 := fresh "ZHW" in
        assert (MU2 : munch W m0 m2)
          by (unfold m2; change (Z_to_bv 64 E) with (wa E);
              apply munch_write_n with (n := 1); [reflexivity|lia|lia|exact MU|cbn; lia]);
        assert (WM2 : wmono bsegs m0 m2) by (unfold m2; apply wmono_write; exact WM);
        assert (MI2 : mem_inv bsegs m2) by (unfold m2; apply mem_inv_store; [exact MI|exact HS]);
        assert (SR2 : bytes_at bsegs m2 S bs)
          by (unfold m2; change (Z_to_bv 64 E) with (wa E);
              apply bytes_at_write_other_n with (n := 1); [reflexivity|lia|lia|exact SR|rewrite ?length_map; lia]);
        assert (HA2 : u8arr bsegs m2 HW (upd l (Z.to_nat (E - HW)) (Z_to_bv 8 x)))
          by (unfold m2; replace (Z_to_bv 64 E) with (wa (HW + (E - HW))) by (unfold wa; f_equal; lia);
              apply u8arr_write; [exact HA | rewrite ?upd_length, ?length_app, ?length_map, ?length_skipn; lia]);
        pose proof (zshadow_appW _ m0 m2 _ _ ZHW MU2 AWD ltac:(lia) ltac:(lia)) as ZH2;
        clearbody m2; clear HS MU WM MI HA SR
      end
    end.
  Ltac dl_srcz a := lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MUm : munch _ m0 mm, U : forall mm', munch _ m0 mm' -> unpoisoned mm' S _ |- _ =>
      let sb := fresh "sb" in let RDB := fresh "RDB" in let CK := fresh "CK" in let SR := fresh "SR" in
      let B0 := fresh "B0" in let BP := fresh "BP" in let BL := fresh "BL" in
      destruct (AF_fse_rd_base.chkB mm S (S + zlen src) a (U mm MUm) ltac:(lia) ltac:(lia)) as (sb & RDB & CK & SR);
      zstep; clear RDB; rewrite sxb_sval;
      destruct CK as [B0|(BP & BL)]; [rewrite B0|]
    end end.
  Ltac dl_inv2 k acc :=
    lazymatch goal with HA : u8arr _ ?mm HW (upd (upd _ ?i0 (Z_to_bv 8 ?x0)) ?i1 (Z_to_bv 8 ?y0)),
                        SR : bytes_at _ ?mm S _, MU : munch _ m0 ?mm, WM : wmono _ m0 ?mm, MI : mem_inv _ ?mm |- _ =>
      replace i0 with (length acc) in HA by lia;
      replace i1 with (Datatypes.S (length acc)) in HA by lia;
      rewrite dlA_upd2 in HA by lia;
      replace x0 with (Znth (k + 1) src / 16) in HA by (rewrite Z.shiftr_div_pow2 by lia; reflexivity);
      let INV2 := fresh "INV2" in
      assert (INV2 : dlA_inv mm (acc ++ [Znth (k + 1) src / 16; y0]))
        by (split; [exact HA|split; [exact SR|split; [exact MU|split; [exact WM|exact MI]]]])
    end.

  Lemma dlA_loop : forall f k acc m1 fuel (x6 x7 x10 x28 x29 x30 x31 : word),
    Z.of_nat f = K - k + 1 -> 0 <= k <= K -> K - k + 2 <= Z.of_nat fuel ->
    zlen acc = 2 * k -> Forall (fun c => 0 <= c < 256) acc -> dlA_inv m1 acc ->
    (forall m2 cells (y6 y7 y10 y11 y16 y28 y29 y30 y31 : word),
       direct_loop src fuel (2 * k) oSize acc = Ok cells -> zlen cells = 2 * K + 2 ->
       Forall (fun c => 0 <= c < 256) cells -> dlA_inv m2 cells ->
       evtF bsegs RNG Q (ST 0x974f4 m2 y6 y7 y10 y11 y16 y28 y29 y30 y31)) ->
    evtF bsegs RNG Q (ST 0x97430 m1 x6 x7 x10 (Z_to_bv 64 (2 * k)) (Z_to_bv 64 (2 * k)) x28 x29 x30 x31).
Proof.
induction f as [|f IH]; intros k acc m1 fuel x6 x7 x10 x28 x29 x30 x31 Hf Hk Hfuel Hacc HBa INV KC; [lia|].
pose proof INV as INV0.
destruct INV as (HWA & SRA & MU & WM & MI).
pose proof (ablk_lin _ _ HHW) as (HWa & HWb & HWc & HWd).
pose proof (ablk_lin _ _ HS0) as (Sa & Sb & Sc & Sd).
unfold AIMG_HI in HWa, Sa.
pose proof (zshadow_appW _ m0 m1 _ _ ZHW MU AWD ltac:(lia) ltac:(lia)) as ZHW1.
assert (USRCm : forall mm, munch [(HW, HW + 256)] m0 mm -> unpoisoned mm S (S + zlen src)).
{ intros mm MUm. eapply unpoisoned_munch; [exact USRC | exact MUm |]. cbn [disjoint_from].
  assert (SHB : 0x7fff8000 <= shad S /\ shad (S + zlen src - 1) + 1 <= 0x7fff8000 + 2^44)
    by (unfold shad, ASHOFF; rewrite !Z.shiftr_div_pow2 by lia; change (2^3) with 8; split; Z.div_mod_to_equations; lia).
  split; [|exact I].
  destruct (app_vs_shadowZ HW 256 (shad S) (shad (S + zlen src - 1) + 1 - shad S) HHW ltac:(lia) ltac:(lia)); [right|left]; lia. }
assert (Hk1 : 2 * k < oSize) by lia.
assert (Hb : 0 <= Znth (k + 1) src < 256) by (apply (Forall_Znth _ src (k + 1) HSB); lia).
assert (Hbu : bv_unsigned (Z_to_bv 8 (Znth (k + 1) src)) = Znth (k + 1) src)
  by (rewrite Z_to_bv_unsigned; unfold bv_wrap, bv_modulus; apply Z.mod_small; lia).
assert (HWk : HW + 2 * k + 1 < HW + 256) by lia.
zstep. wk_go [0x9733c + 244; 0x9733c + 440].
dl_srcz (S + 1 + k).
all: wk_go [0x9733c + 244; 0x9733c + 440].
all: wk_st8 11%Z.
all: dl_st8.
all: wk_go [0x9733c + 244; 0x9733c + 440].
all: dl_srcz (S + 1 + k).
all: wk_go [0x9733c + 244; 0x9733c + 440].
all: wk_st8 11%Z.
all: dl_st8.
all: destruct (Z_lt_le_dec (2 * k + 2) oSize) as [LT|GE].
all: wk_go [0x9733c + 244; 0x9733c + 440].
all: dl_inv2 k acc.
all: pose proof (dlA_forall acc (Znth (k + 1) src) HBa Hb) as HB2.
all: assert (HL2 : zlen (acc ++ [Znth (k + 1) src / 16; Z.land (Znth (k + 1) src) 15]) = 2 * k + 2)
       by (rewrite length_app; cbn [length]; lia).
all: destruct fuel as [|fuel']; [lia|].
all: lazymatch goal with |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
  let o := eval vm_compute in (pc - 0x9733c) in lazymatch o with
  | 244 =>
      replace (2 * k + 2) with (2 * (k + 1)) by lia;
      apply (IH (k + 1) (acc ++ [Znth (k + 1) src / 16; Z.land (Znth (k + 1) src) 15]) _ fuel');
        [lia|lia|lia|lia|exact HB2|exact INV2|];
      intros m4 cells y6 y7 y10 y11 y16 y28 y29 y30 y31 E1 E2 E3 E4;
      apply (KC m4 cells y6 y7 y10 y11 y16 y28 y29 y30 y31); [|exact E2|exact E3|exact E4];
      rewrite dlA_step by lia; replace (2 * k + 2) with (2 * (k + 1)) by lia; exact E1
  | 440 =>
      apply (KC _ (acc ++ [Znth (k + 1) src / 16; Z.land (Znth (k + 1) src) 15])); [|lia|exact HB2|exact INV2];
      rewrite dlA_step by lia; destruct fuel' as [|fuel'']; [lia|]; apply dlA_stop; lia
  end end.
Qed.
End DLA.
End CANSEC1.
