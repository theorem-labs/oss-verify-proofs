(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjNumber.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd Sj_num_kit Sj_num_walk Sj_num_sp_pdefs.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.A Require Import Layout Shadow RT_iface D_defs D_kit D_clx Sj_akit Sj_acps Sj_hkit Sj_rtf
  Sj_num_akit Sj_num_amem Sj_num_iface Sj_num_adefs Sj_num_abig Sj_num_lm_kit Sj_num_pm_kit Sj_num_fc_kit Sj_num_fc_kit2 Sj_num_fc_defs Sj_num_fc_defs2 Sj_num_fc_defs3 Sj_num_fc_kit3 Sj_num_pm_top.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zr_hook | asan_zc_hook | asan_zcp_hook | asan_ptr_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Local Ltac akstep ::=
  zstep; nnorm; kb2z; anorm;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (Z_to_le_bytes ?n ?z)) _) =>
      lazymatch n with
      | 8%nat => change (Z_to_le_bytes 8 z) with (le8 (Z_to_bv 64 z))
      | 4%nat => change (Z_to_le_bytes 4 z) with (le4 (Z_to_bv 64 z))
      | 2%nat => change (Z_to_le_bytes 2 z) with (le2 (Z_to_bv 64 z))
      | 1%nat => change (Z_to_le_bytes 1 z) with (le1 (Z_to_bv 64 z))
      end;
      mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ (wa (_ + Z.of_nat _)) (le1 ?v)) _) =>
      change (le1 v) with [Z_to_bv 8 (bv_unsigned v)]; mem_after_store
  | |- _ => idtac
  end.

Ltac akwalk_abs PCS K :=
  akwalk ltac:(fun pc => first [ K pc | (lazymatch PCS with context [pc] => idtac end; num_abstract_loads; num_abstract_data; akstep; akwalk_abs PCS K) ]).

Section FCA.
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (lo d spq f A FIRST LAST OUT : Z) (txt : list byte) (m0 : mem).
  Notation SP := (bv_unsigned sp).
  Notation S := (f / 8 + 2147450880)%Z.
  Notation TL := (Z.of_nat (length txt)).
  Hypothesis SPQ : (0 <= d <= 16 /\ spq = SP - 192 - d)%Z.
  Hypothesis ROOM : (lo + SPA_STACK <= SP)%Z.
  Hypothesis TOP : (SP + 16 <= USTACK_TOP)%Z.
  Hypothesis F64 : (f mod 64 = 0)%Z.
  Hypothesis FLO : (0x6c9000 <= f /\ f + 1016 <= lo)%Z.
  Hypothesis FSH : (f + 1016 <= S \/ S + 127 <= f)%Z.
  Hypothesis FS0 : (0 <= S /\ S + 127 <= lo)%Z.
  Hypothesis TXR : (0 < A /\ A + TL <= lo /\ TL < 2147483648)%Z.
  Hypothesis FLR : (A <= FIRST /\ FIRST < LAST /\ LAST <= A + TL)%Z.
  Hypothesis TSEP : ((A + TL <= f \/ f + 1024 <= A) /\ (A + TL <= S \/ S + 128 <= A))%Z.
  Hypothesis OUTR : (OUT mod 8 = 0 /\ SP <= OUT /\ OUT + 8 <= USTACK_TOP)%Z.

  Notation W := [(lo, spq + 88); (f + 32, f + 536); (f + 608, f + 680); (f / 8 + 2147450884, f / 8 + 2147450947); (OUT, OUT + 8)]%Z.

  Hypothesis SHPT : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (8 * (FIRST / 8)) (LAST - 8 * (FIRST / 8)).
  Hypothesis SHPO : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' OUT 8.
  Variable Q : machine_state -> Prop.
  Collection FCH := SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO.

  Notation FCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Notation FCP pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 mm :=
    (FCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 (Z_to_bv 64 (f + 608)) xs6 (Z_to_bv 64 LAST) xs8 (Z_to_bv 64 2147450880) xs10 xs11 xt3 xt4 xt5 xt6 mm).

  Notation tb := (ftb A txt).
  Notation ge48 := (fge48 A txt).
  Notation FCPINV := (fc_pinv spq f A OUT lo txt m0).

  Notation ERRA_K ra1 := (forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs6 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 (mm : mem), FCPINV c0 c8 c16 c24 c32 c40 c48 c56 c64 c80 mm ->
     evt asegs Q (FCP 0x81cb8 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs6 (Z_to_bv 64 OUT)
                      xs10 xs11 xt3 xt4 xt5 xt6 mm)) (only parsing).
  Notation ERRB_K ra1 := (forall xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8 xs10 xs11 xt3 xt4 xt5 xt6 c0 c8 c16 c24 c32 c40 c64 c80 (mm : mem), FCPINV c0 c8 c16 c24 c32 c40 (Z_to_bv 64 f) (Z_to_bv 64 OUT) c64 c80 mm ->
     evt asegs Q (FCP 0x81cb8 (Z_to_bv 64 ra1) xt0 xt1 xt2 (Z_to_bv 64 (f + 640)) (Z_to_bv 64 0) (Z_to_bv 64 32) xa3 xa4 xa5 xa6 xa7 xs3 xs6 xs8
                      xs10 xs11 xt3 xt4 xt5 xt6 mm)) (only parsing).
  Hypothesis KERRA : forall ra1, In ra1 FC_ERRA -> ERRA_K ra1.
  Hypothesis KERRB : forall ra1, In ra1 FC_ERRB -> ERRB_K ra1.

  Ltac fc_in_list := unfold FC_ERRA, FC_ERRB; cbn [In]; repeat (first [left; reflexivity | right]).
  Ltac fc_erra_cut := eapply evt_eq; [| eapply KERRA]; [num_st_eq | fc_in_list | fc_pclose].
  Ltac fc_errb_cut := eapply evt_eq; [| eapply KERRB]; [num_st_eq | fc_in_list | fc_pclose].

  Notation FCD D := (D sp gp tp F fc lo spq f A FIRST LAST OUT txt m0 Q) (only parsing).
  Notation FCL L := (L sp gp tp F fc lo d spq f A FIRST LAST OUT txt m0 SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO Q) (only parsing).

  Ltac fc_env :=
    destruct SPQ as [Hd Hspq]; unfold SPA_STACK, NDCA_STACK, P5A_STACK, LMA_STACK, RT_STACK, USTACK_TOP in *;
    let SPR := fresh "SPR" in pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
    let RL := fresh "RL" in pose proof (repeat_length (Z_to_bv 8 0) 63) as RL;
    let F8 := fresh "F8" in pose proof (f64_8 f F64) as F8.

  Hypothesis FRM0 : frm0 fc.
  Hypothesis SHPL1 : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2bd40 10416.
  Hypothesis SHPL2 : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2e6c0 640.
  Collection FCH2 := SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO SHPL1 SHPL2.
  Notation FCS2 pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm :=
    (MS (mkR xra (Z_to_bv 64 spq) gp tp xt0 xt1 xt2 sp (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) xs3 (Z_to_bv 64 S) xs5 xs6 xs7 xs8 xs9
             xs10 xs11 xt3 xt4 xt5 xt6) xF (Z_to_bv 64 pc) xfc None mm (seg_rom asegs)).
  Notation FCINV2 := (fc_inv2 spq f A OUT lo txt m0).

  Notation FCL2 L := (L sp gp tp lo d spq f A FIRST LAST OUT txt m0 SPQ ROOM TOP F64 FLO FSH FS0 TXR FLR TSEP OUTR SHPT SHPO Q SHPL1 SHPL2) (only parsing).

  Notation PF := (fpfacts A txt FIRST LAST).
  Notation FCINV3 := (fc_inv3 spq f A OUT lo txt m0).

  Definition fc_pdc_k : Prop :=
    forall (e dg len : Z) (xbs : list byte) xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc
           c0 c8 c16 c24 c32 c40 c64 qw ww lmw negb vb tmb ipw ilw fptw flw errw (mm : mem),
      FCINV3 c0 c8 c16 c24 c32 c40 c64 (Z_to_bv 64 dg) qw ww lmw negb vb tmb ipw ilw fptw flw errw mm -> frm0 xfc ->
      u8arr asegs mm (f + 32) xbs -> length xbs = 496%nat -> rw_cells asegs mm (f + 528) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
      (0 <= e <= 1111)%Z ->
      evt asegs Q (FCS2 0xe8150 (Z_to_bv 64 0xe6078) xt0 xt1 xt2 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 e) xa2 xa3 xa4 xa5 xa6 xa7
                        (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 xs8 (Z_to_bv 64 2147450880) xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Definition fc_ndc_k : Prop :=
    forall (e dg len : Z) (xbs : list byte) xt0 xt1 xt2 xa1 xa2 xa4 xa5 xa6 xa7 xs6 xs7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc
           c0 c8 c16 c24 c32 c40 c64 qw ww lmw negb vb tmb ipw ilw fptw flw errw (mm : mem),
      FCINV3 c0 c8 c16 c24 c32 c40 c64 (Z_to_bv 64 dg) qw ww lmw negb vb tmb ipw ilw fptw flw errw mm -> frm0 xfc ->
      u8arr asegs mm (f + 32) xbs -> length xbs = 496%nat -> rw_cells asegs mm (f + 528) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
      (-1111 <= e <= -1)%Z ->
      evt asegs Q (FCS2 0xe86ec (Z_to_bv 64 0xe6094) xt0 xt1 xt2 (Z_to_bv 64 (f + 32)) xa1 xa2 (Z_to_bv 64 e) xa4 xa5 xa6 xa7
                        (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 xs8 (Z_to_bv 64 2147450880) xs10 xs11 xt3 xt4 xt5 xt6 xF xfc mm).

  Section PMCALL.
  Hypothesis KPDC : fc_pdc_k.
  Hypothesis KNDC : fc_ndc_k.

  Hypothesis SHPD : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' (spq + 80) 8.
  Hypothesis SHPL3 : forall m', munch W m0 m' -> wmono asegs m0 m' -> shz m' 0x2e600 160.
  Hypothesis CCP : forall m', munch W m0 m' -> wmono asegs m0 m' -> client_consts m'.
  Hypothesis SPQ8 : (spq mod 8 = 0)%Z.

  Lemma fc_65c : forall (qe dg len : Z) (xbs : list byte) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 qw ww lmw negb vb tmb ipw ilw fptw flw errw (mm : mem),
    FCINV3 c0 c8 c16 c24 c32 c40 c64 (Z_to_bv 64 dg) qw ww lmw negb vb tmb ipw ilw fptw flw errw mm -> frm0 xfc ->
    u8arr asegs mm (f + 32) xbs -> length xbs = 496%nat -> rw_cells asegs mm (f + 528) [C2 (Z_to_bv 64 len)] -> (0 <= len <= 62)%Z ->
    (-342 <= qe <= 330)%Z -> (0 <= dg <= 770)%Z ->
    evt asegs Q (FCS2 0xe605c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KPDC KNDC SPQ8.
    intros until mm. intros INV FRM XA XL XN HLEN Hq Hdg. pose proof INV as INV0. fc_open3 INV0. fc_env.
    pose proof (fc_exp32 qe dg Hq Hdg) as EX.

    pose proof (fhold_in _ SPILL) as SPH.
    lazymatch type of SPILL with rw_cells _ _ _ [?a0; ?a1; ?a2; ?a3; ?a4; ?a5; ?a6; ?a7; ?a8; ?a9; ?a10] =>
      change [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] with ([a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] ++ [a10]) in SPILL end.
    apply num_rw_cells_app in SPILL. destruct SPILL as [SP10 DGC]. cbn [cells_size csize Nat.add] in DGC.
    change (Z.of_nat 80) with 80%Z in DGC.
    apply (fc_c8_split_lo asegs) in DGC; [| lia].
    akwalk ltac:(fun pc => lazymatch pc with
      | 0xe8150%Z => first [ rewrite EX in *; clear SP10 DGC; apply fhold_out in SPH;
                             eapply evt_eq; [| eapply (KPDC (qe - dg + 1)%Z dg len xbs)]; [num_st_eq | fc_close3 | assumption | exact XA | exact XL | exact XN | lia | lia]
                           | fail 100 "cut" pc ]
      | 0xe86ec%Z => first [ rewrite EX in *; clear SP10 DGC; apply fhold_out in SPH;
                             eapply evt_eq; [| eapply (KNDC (qe - dg + 1)%Z dg len xbs)]; [num_st_eq | fc_close3 | assumption | exact XA | exact XL | exact XN | lia | lia]
                           | fail 100 "cut" pc ]
      end).
  Qed.

  Lemma fc_648 : forall (qe IP IL FPT FL : Z) xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs6 xs7 xs11 xt3 xt4 xt5 xt6 xF xfc
      c0 c8 c16 c24 c32 c40 c64 qw ww lmw negb vb tmb errw (mm : mem),
    FCINV3 c0 c8 c16 c24 c32 c40 c64 (Z_to_bv 64 0) qw ww lmw negb vb tmb (Z_to_bv 64 IP) (Z_to_bv 64 IL) (Z_to_bv 64 FPT) (Z_to_bv 64 FL) errw mm -> frm0 xfc ->
    PF IP IL FPT FL -> (-342 <= qe <= 330)%Z ->
    rw_cells asegs mm (f + 32) [CB 504 (repeat (Z_to_bv 8 0) 504)] ->
    evt asegs Q (FCS2 0xe6048 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 f) (Z_to_bv 64 (f + 608)) xs6 xs7 (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147450880)
                      (Z_to_bv 64 qe) xs11 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using FCH2 KPDC KNDC SHPD SHPL3 CCP SPQ8.
    intros until mm. intros INV FRM PFp Hq BIG. pose proof INV as INV0. fc_open3 INV0. fc_env.
    awalk ltac:(fun pc => lazymatch pc with 0xe65c8%Z => idtac end).

    apply (rw_cells_split_CB asegs _ _ [] 504 _ [] [496;2;6]%nat) in BIG; [|reflexivity]. cbn [mk_CB_cells app] in BIG.
    lazymatch type of BIG with rw_cells _ _ _ [CB 496 ?b0; CB 2 ?b1; CB 6 ?b2] =>
      change [CB 496 b0; CB 2 b1; CB 6 b2] with ([CB 496 b0] ++ [CB 2 (le2 (Z_to_bv 64 0))] ++ [CB 6 b2]) in BIG end.
    apply num_rw_cells_app in BIG. destruct BIG as [BG R]. apply num_rw_cells_app in R. destruct R as [BGN BGP].
    cbn [cells_size csize Nat.add] in BGN, BGP. clear BGP.
    apply num_cb2_c2 in BGN. pose proof (u8arr_of_rw_cells asegs _ _ _ _ BG) as XA. clear BG.
    replace (f + 32 + Z.of_nat 496)%Z with (f + 32 + 496)%Z in BGN by lia.

    lazymatch type of SPILL with rw_cells _ _ _ [?a0; ?a1; ?a2; ?a3; ?a4; ?a5; ?a6; ?a7; ?a8; ?a9; ?a10] =>
      change [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9; a10] with ([a0; a1; a2; a3; a4; a5; a6; a7; a8; a9] ++ [a10]) in SPILL end.
    apply num_rw_cells_app in SPILL. destruct SPILL as [SP10 DGC]. cbn [cells_size csize Nat.add] in DGC.
    destruct (rw_cells_forget asegs _ _ _ DGC) as [jd DGC']. cbn [cells_size csize Nat.add] in DGC'. clear DGC.
    change (Z.of_nat 80) with 80%Z in DGC'.

    lazymatch type of PNS with rw_cells _ _ _ [?a0; ?a1; ?a2; ?a3; ?a4; ?a5; ?a6; ?a7; ?a8; ?a9; ?a10; ?a11] =>
      change [a0; a1; a2; a3; a4; a5; a6; a7; a8; a9; a10; a11] with ([a0; a1; a2; a3; a4; a5; a6] ++ ([a7; a8; a9; a10] ++ [a11])) in PNS end.
    apply num_rw_cells_app in PNS. destruct PNS as [PNH R]. apply num_rw_cells_app in R. destruct R as [SPANS PNT].
    cbn [cells_size csize Nat.add] in SPANS, PNT.
    change (Z.of_nat 32) with 32%Z in SPANS, PNT.

    destruct FLR as (R1 & R2 & R3). destruct TXR as (T1 & T2 & T3).
    pose proof (fc_sub_length A FIRST LAST txt R1 ltac:(lia) R3) as SUBL.
    pose proof (fc_sub_bytes asegs mm A FIRST LAST txt R1 ltac:(lia) R3 TXT) as SUBB.
    pose proof (fpfacts_spans_sub A txt FIRST LAST IP IL FPT FL R1 ltac:(lia) R3 PFp) as SPN.
    assert (SUBFP : sub_fp [(spq - 160, spq); (f + 32, f + 32 + 504); (spq + 80, spq + 80 + 8)]%Z W).
    { intros x HO. cbn [outside] in *. lia. }
    pose proof (rw_cells_bytes_at _ _ _ _ BSH) as ZSH. cbn [cells_bytes cbytes app] in ZSH. rewrite app_nil_r in ZSH.
    pose proof (rw_cells_bytes_at _ _ _ _ PSH) as ZPS. cbn [cells_bytes cbytes app] in ZPS. rewrite app_nil_r in ZPS.
    destruct (image_readable_b asegs mm 160 0x2e600 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tbp & TBL & TBP).
    assert (EUS : bv_unsigned (Z_to_bv 64 spq) = spq) by (apply unsigned_lit; lia).
    eapply evt_eq; [| eapply (pma_ok (Z_to_bv 64 0xe605c) (Z_to_bv 64 spq) gp tp sp (Z_to_bv 64 spq) (Z_to_bv 64 f) (Z_to_bv 64 f) (Z_to_bv 64 S) (Z_to_bv 64 (f + 608)) xs6 xs7
                                   (Z_to_bv 64 (f + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 qe) xs11 xF xfc
                                   (f + 32)%Z (f + 608)%Z (spq + 80)%Z FIRST IP IL FPT FL lo (fc_sub A FIRST LAST txt) mm)];
      rewrite ?EUS, ?SUBL; unfold PMA_STACK, USTACK_TOP.
    1: num_st_eq.
    1-9: lia.
    1: exact SPN.
    1: lia.
    1: {
      intros m' MUx WMx.
      pose proof (SHPT m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUBFP MUx)) (wmono_trans _ _ _ _ WM WMx)) as H.
      replace (FIRST + (LAST - FIRST) - 8 * (FIRST / 8))%Z with (LAST - 8 * (FIRST / 8))%Z by lia. exact H. }
    1: {
      intros m' MUx WMx.
      assert (ZP' : bytes_at asegs m' (f / 8 + 2147450880 + 76) (repeat (Z_to_bv 8 0) 9)).
      { replace (f / 8 + 2147450880 + 76)%Z with (f / 8 + 2147450956)%Z by lia.
        apply (bytes_at_agree asegs mm m' _ _ ZPS). apply (agree_of_munch _ _ _ _ MUx).
        intros x Hx. rewrite repeat_length in Hx. cbn [outside]. lia. }
      pose proof (shz_run m' f 76 9 F8 ltac:(lia) ltac:(lia) ZP') as H.
      eapply shz_sub; [exact H | lia | lia]. }
    1: { intros m' MUx WMx; exact (SHPD m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUBFP MUx)) (wmono_trans _ _ _ _ WM WMx)). }
    1: { intros m' MUx WMx; exact (SHPL3 m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUBFP MUx)) (wmono_trans _ _ _ _ WM WMx)). }
    2: exact MI. 2: exact ST. 2: exact (CCP mm MU WM). 2: exact XA. 2: (vm_compute; reflexivity). 2: exact BGN. 2: lia.
    2: { replace ((f + 32) / 8 + 2147450880)%Z with (f / 8 + 2147450884)%Z by lia. exact ZSH. }
    2: exact DGC'. 2: exact SPANS. 2: exact SUBB.
    2: { exists tbp. split; [exact TBP | rewrite TBL; reflexivity]. }

    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' xbs' len' dg' MUx WMx MI' ST' XA' XL' XN' HLEN' ZSH' DG' HDG' SPANS' TXT'.
    pose proof (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ SUBFP MUx)) as MUc. pose proof (wmono_trans _ _ _ _ WM WMx) as WMc.
    clear XA BGN DGC' SPANS MI ST ZSH ZPS SUBB TBP.
    transport_after_call asegs mm m' MUx WMx. clear MUx WMx MU WM.

    lazymatch type of SP10 with rw_cells _ _ _ ?l10 =>
      assert (SPILL : rw_cells asegs m' spq (l10 ++ [C8 (Z_to_bv 64 dg')]))
        by (apply num_rw_cells_app; split; [exact SP10 | cbn [cells_size csize Nat.add]; exact DG']) end.
    cbn [app] in SPILL.
    lazymatch type of PNH with rw_cells _ _ _ ?lh => lazymatch type of SPANS' with rw_cells _ _ _ ?ls => lazymatch type of PNT with rw_cells _ _ _ ?lt =>
      assert (PNS : rw_cells asegs m' (f + 608) (lh ++ (ls ++ lt)))
        by (apply num_rw_cells_app; split; [exact PNH | apply num_rw_cells_app; split; [exact SPANS' | exact PNT]]) end end end.
    cbn [app] in PNS.
    clear SP10 DG' PNH PNT SPANS'.
    rename MI' into MI. rename ST' into ST. rename MUc into MU. rename WMc into WM.
    num_ret_pc.
    eapply evt_eq; [| eapply (fc_65c qe dg' len' xbs')]; [num_st_eq | fc_close3 | exact FRM | exact XA' | exact XL' | (replace (f + 528)%Z with (f + 32 + 496)%Z by lia; exact XN') | exact HLEN' | exact Hq | exact HDG'].
  Qed.
  End PMCALL.
End FCA.
