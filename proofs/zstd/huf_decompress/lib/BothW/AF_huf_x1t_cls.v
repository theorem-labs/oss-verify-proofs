(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX1
  HufPure_HufTableX1.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model RF_huf_x1t_model RF_huf_x1t_cls.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require AF_fse_rd_base.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit FseRdKit2.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_x1t_cls () := "C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindC47Corelib4Init5Logic6eq_indI5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01I47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C47Corelib4Init5Logic9False_indK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res03K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res04I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z6moduloK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z9mod_smallC56Stdlib6ZArith6BinInt1Z4onesC56Stdlib6ZArith6BinInt1Z4landK46Stdlib9micromega6VarMap1t01C56Stdlib6ZArith6BinInt1Z9land_onesC47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00c5ARocqVerifyHarness?AgentSubmission5BothW>AF_huf_x1t_cls8x1placeAC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3mulC5ARocqVerifyHarness?AgentSubmission5BothW5ABase4ablkK47Corelib7Numbers7BinNums8positive01C5ARocqVerifyHarness?AgentSubmission4LibA5ExecF3rngI47Corelib4Init9Datatypes4prod00C5ARocqVerifyHarness?AgentSubmission4Spec9AsanEmbed4shadI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common7RunDraw:atop_rangeC5ARocqVerifyHarness?AgentSubmission3Lib8RunConst4ATOPC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr05K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C47Corelib4Init9Datatypes6lengthC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5nshadC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow:unpoisonedC5ARocqVerifyHarness?AgentSubmission5BothW@AF_huf_tbl_iface7zshadowK47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5BothW9Stdio_kit4appWC47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes3fstK46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C5ARocqVerifyHarness?AgentSubmission4LibA6Shadow5KHIGHC5ARocqVerifyHarness?AgentSubmission4LibA6Shadow4KLOWC5ARocqVerifyHarness?AgentSubmission4LibA5ExecF9footprintI47Corelib4Init9Datatypes3nat00".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module XM := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain.RF_huf_x1t_model.
Module XC := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain.RF_huf_x1t_cls.
Module BM := OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Plain.RF_huf_bdt_model.

Section CANSEC1. Context {rc : runConstT}.

Lemma bind_Ok_invA : forall {A B} (x : res A) (k : A -> res B) y, bind x k = Ok y -> exists a, x = Ok a /\ k a = Ok y.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_x1t_cls ()) ["CANSEC1"] "p'0h01Hh11ai001ah22H0h31eh41Ah51Bh62e0h71kh81xh91yi011ri021zp;1p;4p;2p;3p;6p200R0g0000R1p4p710p8p201R2g000hR3p4p710p8P2P1p4p7210p8g001DR4j12TP1j43Tg002=j21Tg0036j30Tg003Pj24Tg003kj25Tg004Ej2=Tg004_j4<Tg005:j4;Tg005Tj27TP3j66Tg006Mj28Tg006lj19Tg007ej1:Tf1R3#2f2R1%21[f3R5#2f4R6P5P1P3C3f0R7,1530P4f5R8%28R9f6R:P8P7P5C31181R;30f7R<f8R=#2R>11=7R?701%2<R@P8P7O111<6RA30RB'4X1<'5]0P5%2:RCP<P:11<7P6C311:5RD30P=f9RE#2RF11E111E730P:P7O111=850>'4X1=P311=3RG=0>GP8P3O1=0@A1=>GP7C<C;W0X1:P7O1g008^P<P:17<7P6C3=0CDP@17<3P4P=p-0RDP7g009<RCg009YRGPCPCn101101000410000100000000X6@g00:5R@PAP7E6PCf:RA#217A511A730P<P7O111E:50F'4X1E,5E/87b2W0W3P7O1%26REP8P6%98RFP1C31163R330P9PFP4P:PDP7PCPCPGPCn101101000410000100000000X39P@P;P7E6PC%9==0>?/4BX1<,5</87b2W0P8P6%:8R8P1C3=0E3P9P8P4P:PDP7PCPCPCPGn101101000410000100000000X39P@P;P7E6PC%:==0>?/4BX1<,5</87b2W0n101101000410100101020000P7O1W0X91W7W8X52X40o"). Qed.

Definition X1REPA : Z := 281479271743489.     (* [comment removed for export] *)

Lemma land255_small : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_x1t_cls ()) ["CANSEC1"] "h07__arithh14__ffh28__varmaph35__with44__x1h51Hh61xh71zp;2p;1p;3p;4p;8p;6p;7g00:Qj24Tg00:mj10Tg00;Rj15Tg00<0j26Tg003Pj29Tg00<Lj2QTg00<ij2LTg0036j37Tg00=Ij1?Tg00=ij1>Tg00>Ij2=Tg00>gj1;Tg00?Ej1:Tg00@0j21Tg00@Sj2RTg00A6j43Tg00Aaj1PTg00BCj1KTg00Baj3CTg00CDj8BTg00Chj2ATg004Ej2@Tg00DJj2DTg00E6j3ETg00EUj4FTg00FGj3GTg00Fjj1HTg00GHj2ITg00Gfj1JTg00HDj3<Tg00Hgj6MTg00IEj7NTg00Iij7OTf1R0g00JMR1g00JlR2P2g00KLR3f0R4g00KlFNp=2f2R5P1P2P2P3P0P4FOp=8g008^R6g00LLR7/44g00LjR8#0R9#0#0R:#0#0#0#0#0#5R;,64'9R<P6%59R9%5:R='QR>,L0A7645X76g00MOR?#?R@%>?R?1=60%;6RA%:6RBP1P2P2P3P61167R1g00N;RC1R68R8C3,2BRDP6P8g00NbRE116;C3,2B58B%P2P6P8PE1169%K:5C6C3,2B98BDGB1AB3R3P4P5g00OIRDg00OiR:'@1D45=7D:dAE670CFR:b1b2b3X461470160>'9\<^46P4P5P0O2b09G0>%H=,I0P@P?%J6PAP6P1PC116=C3,2BP3P:b1b2b3147=P4b09<0=EMW5W6o"). Qed.

(* [comment removed for export] *)
Definition x1frA (w u sym cnt SY : Z) (j144 j160 j192 j208 : list byte) : list cell :=
  [C8 (Z_to_bv 64 w); CB 8 j144; C8 (Z_to_bv 64 u); CB 8 j160; C8 (Z_to_bv 64 SY); C8 (Z_to_bv 64 sym);
   C8 (Z_to_bv 64 cnt); CB 8 j192; C8 (Z_to_bv 64 X1REPA); CB 88 j208].

(* [comment removed for export] *)
Definition x1ptrA (DT : Z) : list cell :=
  [C8 (Z_to_bv 64 (DT + 27)); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (DT + 19)); C8 (Z_to_bv 64 (DT + 35));
   C8 (Z_to_bv 64 (DT + 28)); C8 (Z_to_bv 64 (DT + 11))].

(* [comment removed for export] *)
Definition x1fA_inv (m0 m1 : amem) (SPA DT SY : Z) (js jt : list byte) (syms : list (option Z)) (ncells : nat)
    (cells : list (option deltX1)) : Prop :=
  u8arr bsegs m1 (DT + 4) (XM.ox1 jt cells) /\ length cells = ncells
  /\ bytes_at bsegs m1 SY (BM.omerge js syms)
  /\ munch [(DT + 4, DT + 4 + 2 * Z.of_nat ncells); (SPA + 136, SPA + 296)] m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1.

(* [comment removed for export] *)
Definition x1placeA (RNG : footprint) (m0 : amem) (SPA DT SY : Z) (js : list byte) (ncells : nat) : Prop :=
  ablk (DT + 4) (DT + 4 + 2 * Z.of_nat ncells) /\ ablk SY (SY + zlen js) /\ Z.of_nat ncells <= 8192
  /\ (DT + 4 + 2 * Z.of_nat ncells <= SY \/ SY + zlen js <= DT + 4)
  /\ DT + 4 + 2 * Z.of_nat ncells <= SPA /\ SY + zlen js <= SPA /\ KHIGH <= SPA /\ SPA + 312 <= 2^47
  /\ unpoisoned m0 (DT + 4) (DT + 4 + 2 * Z.of_nat ncells) /\ zshadow m0 SY (zlen js)
  /\ rng RNG (DT + 4) (2 * Z.of_nat ncells) /\ rng RNG (shad DT) (nshad (4 + 2 * Z.of_nat ncells + DT mod 8))
  /\ rng RNG SY (zlen js) /\ rng RNG (shad SY) (nshad (zlen js + SY mod 8)) /\ rng RNG SPA 312.

(* [comment removed for export] *)
Definition x1nextA (SP SPA len : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m2 : amem)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word) : machine_state :=
  MS (mkR y1 (Z_to_bv 64 SPA) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
          (Z_to_bv 64 2147450880) y21 y22 y23 y24 y25 y26 (Z_to_bv 64 len) y28 y29 y30 y31)
     F (Z_to_bv 64 0x80a1c) fc None m2 (seg_rom bsegs).

Definition x1clsA_stmt (pc : Z) (P : Z -> Prop) : Prop :=
  forall (SP SPA : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint)
         (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
         (m0 m1 : amem) (DT SY w cnt len nb u sym : Z) (syms : list (option Z)) (js jt : list byte) (ncells : nat)
         (cells : list (option deltX1)) (r : list (option deltX1) * Z) (j144 j160 j192 j208 : list byte)
         (Q : machine_state -> Prop),
  P len -> 1 <= w <= 12 -> len = 2^(w - 1) -> 1 <= nb <= 12 ->
  fill_syms (S (Z.to_nat cnt)) 0 cnt sym len nb syms cells u = Ok r ->
  0 <= cnt <= 256 -> 0 <= u -> 0 <= sym <= 256 ->
  length jt = (2 * ncells)%nat -> length js = length syms ->
  (forall i v, nth i syms None = Some v -> 0 <= v < 256) ->
  x1placeA RNG m0 SPA DT SY js ncells ->
  rw_cells bsegs m1 (SPA + 8) (x1ptrA DT) ->
  rw_cells bsegs m1 (SPA + 64) [C8 (Z_to_bv 64 (DT + 12)); C8 (Z_to_bv 64 (DT + 4))] ->
  rw_cells bsegs m1 (SPA + 120) [C8 (Z_to_bv 64 DT)] ->
  rw_cells bsegs m1 (SPA + 136) (x1frA w u sym cnt SY j144 j160 j192 j208) ->
  x1fA_inv m0 m1 SPA DT SY js jt syms ncells cells ->
  (forall m2 cells' (j144' j160' j192' j208' : list byte)
          (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y24 y25 y26 y28 y29 y30 y31 : word),
     r = (cells', u + cnt * len) -> x1fA_inv m0 m2 SPA DT SY js jt syms ncells cells' ->
     rw_cells bsegs m2 (SPA + 136) (x1frA w u sym cnt SY j144' j160' j192' j208') ->
     evtF bsegs RNG Q (x1nextA SP SPA len gp tp F fc m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y21 y22 y23 y24
                         y25 y26 y28 y29 y30 y31)) ->
  evtF bsegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 nb) x11 x12 x13 x14 x15 x16 x17
             x18 x19 (Z_to_bv 64 2147450880) x21 x22 x23 x24 x25 x26 (Z_to_bv 64 len) x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom bsegs)).

End CANSEC1.

(* [comment removed for export] *)
Ltac xbA DT4 ARR q :=
  let SOK := fresh "SOK" in
  pose proof (u8arr_store_ok bsegs _ DT4 _ q (wa (DT4 + q)) ARR ltac:(rewrite ?upd_length, ?XM.ox1_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (wa ?E) _) _) => replace E with (DT4 + q) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ (Z_to_bv 64 ?E) _) _) => replace E with (DT4 + q) by lia
  end;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?x)) _) =>
    first [ match goal with H : le1 x = [_] |- _ => rewrite H end | rewrite le1_lit ]
  end;
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ [?bb]) _) =>
    let ARR2 := fresh "ARR" in
    pose proof (u8arr_write bsegs _ DT4 _ q bb ARR ltac:(rewrite ?upd_length, ?XM.ox1_length; lia)) as ARR2;
    clear ARR; store_done; rename ARR2 into ARR
  end.

(* [comment removed for export] *)
Ltac xcA DT4 ARR U k :=
  xbA DT4 ARR (2 * Z.of_nat U + 2 * k); xbA DT4 ARR (2 * Z.of_nat U + 2 * k + 1);
  replace (Z.to_nat (2 * Z.of_nat U + 2 * k)) with (2 * (U + Z.to_nat k))%nat in ARR by lia;
  replace (Z.to_nat (2 * Z.of_nat U + 2 * k + 1)) with (2 * (U + Z.to_nat k) + 1)%nat in ARR by lia;
  rewrite XM.ox1_store' in ARR by (rewrite ?upd_length; lia).

(* [comment removed for export] *)
Ltac zckA r ZS0 AW :=
  lazymatch type of ZS0 with zshadow ?m0 _ _ =>
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch goal with MU : munch ?W m0 mm |- _ =>
  let v := reg_val r in
  lazymatch v with Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880) =>
    let RDB := fresh "RDB" in
    pose proof (chkZ mm _ _ a (zshadow_appW W m0 mm _ _ ZS0 MU AW ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia)) as RDB;
    zstep; rewrite ?sxb0; clear RDB
  end end end end.

(* [comment removed for export] *)
Ltac dchkA r UH AW :=
  lazymatch type of UH with unpoisoned ?m0 _ _ =>
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
  lazymatch goal with MU : munch ?W m0 mm |- _ =>
  let v := reg_val r in
  lazymatch v with Z_to_bv 64 (Z.shiftr ?a 3 + 2147450880) =>
    let b := fresh "b" in let RDB := fresh "RDB" in let CK := fresh "CK" in let SR := fresh "SR" in
    destruct (AF_fse_rd_base.chkB mm _ _ a (unpoisoned_appW W m0 mm _ _ UH MU AW ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))
      as (b & RDB & CK & SR);
    zstep; rewrite sxb_sval; clear RDB
  end end end end.

(* [comment removed for export] *)
Ltac pregs := let v5 := reg_val 5%Z in let v6 := reg_val 6%Z in let v7 := reg_val 7%Z in let v12 := reg_val 12%Z in
    let v13 := reg_val 13%Z in let v11 := reg_val 11%Z in let v17 := reg_val 17%Z in let v21 := reg_val 21%Z in
    let v22 := reg_val 22%Z in let v23 := reg_val 23%Z in let v26 := reg_val 26%Z in let v27 := reg_val 27%Z in
    let v28 := reg_val 28%Z in let v29 := reg_val 29%Z in let v30 := reg_val 30%Z in let v31 := reg_val 31%Z in
    let v1 := reg_val 1%Z in let v2 := reg_val 2%Z in let v10 := reg_val 10%Z in let v14 := reg_val 14%Z in let v15 := reg_val 15%Z in
    let v16 := reg_val 16%Z in let v8 := reg_val 8%Z in let v9 := reg_val 9%Z in let v18 := reg_val 18%Z in
    let v19 := reg_val 19%Z in let v20 := reg_val 20%Z in let v24 := reg_val 24%Z in let v25 := reg_val 25%Z in
    idtac "ra=" v1 " sp=" v2 " t0=" v5 " t1=" v6 " t2=" v7 " s0=" v8 " s1=" v9;
    idtac " a0=" v10 " a1=" v11 " a2=" v12 " a3=" v13 " a4=" v14 " a5=" v15 " a6=" v16 " a7=" v17;
    idtac " s2=" v18 " s3=" v19 " s4=" v20 " s5=" v21 " s6=" v22 " s7=" v23 " s8=" v24 " s9=" v25 " s10=" v26 " s11=" v27;
    idtac " t3=" v28 " t4=" v29 " t5=" v30 " t6=" v31;
    lazymatch goal with |- evtF _ _ _ (MS _ _ ?pc _ _ ?mm _) => idtac " pc=" pc " mem=" mm end.
