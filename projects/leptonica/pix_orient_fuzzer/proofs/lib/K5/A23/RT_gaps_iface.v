(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Spec Require Import Prelim.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces D_iface D_defs.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_RT_gaps_iface () := "C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C56Stdlib6ZArith6BinInt1Z2ltK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z6moduloC47Corelib4Init5Logic3notK47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00c69OSSVerify5KrLib2K53A23=RT_gaps_iface8chain_okC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2eq00K47Corelib4Init5Logic2eq01C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC69OSSVerify5KrLib2K53Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr07C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc69OSSVerify5KrLib2K53A23=RT_gaps_iface<link_invalidC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A239RT_traces=CLIENT_TRACESC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init5Logic4True01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition e_calloc : Z := 0xcaf9c.          (* [comment removed for export] *)
Definition e_stack_free_6 : Z := 0xacdc0.    (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition link_invalid (lo f : Z) : Prop := f <= lo \/ f mod 8 <> 0 \/ 2^63 <= f.

Fixpoint chain_ok (m : mem) (lo f : Z) (ras : list Z) : Prop :=
  match ras with
  | [] => link_invalid lo f
  | ra1 :: ras' =>
      lo + 16 <= f /\ f mod 8 = 0 /\ f + 16 <= USTACK_TOP /\ 4096 <= ra1 < 2^64
      /\ exists fp1 : Z, 0 <= fp1 < 2^64 /\ rw_cells asegs m (f + -16) [C8 (Z_to_bv 64 fp1); C8 (Z_to_bv 64 ra1)]
                         /\ chain_ok m f fp1 ras'
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition unwind_okC (m : mem) (ra s0 sp : word) : Prop :=
  exists ras : list Z, chain_ok m (bv_unsigned sp) (bv_unsigned s0) ras /\ In (bv_unsigned ra :: ras) CLIENT_TRACES.

Lemma unwind_okC_of_ok : forall m ra s0 sp, In [bv_unsigned ra] CLIENT_TRACES ->
  (bv_unsigned s0 < bv_unsigned sp \/ bv_unsigned s0 mod 8 <> 0 \/ 2^63 <= bv_unsigned s0) -> unwind_okC m ra s0 sp.
Proof.
ltac2:(KReplay.run1 (kr_t_RT_gaps_iface ()) [] "h02Hah14__p1h26__sat4h36__sat5h44__x1h54__x2h64__x3h71ah81Hh92H0h:2H1h;2H2h<2H3h=7__arithh>4__ffh?6__sat3h@8__varmaphA5__withB1mhC2rahD3rashE2s0hF2sphG2zhp;1p;2p;3p;4p;6p;7p;8p-1R0g0000R1p4p710p8P0p1000Gp4p710p8P0p1000cp4p710p8P0p1001DR2p4p710p8P0P2p4p7210p8g001aj15Tg002Fj1>Tg002dj1HTg003Gj1PTg003ij1LTg004Ij20Tg0053j1ITg005Sj3?TP1j3=Tg0063j22Tg006Oj1;Tg006mj29Tg007Mj1ETg007fj16Tg008Kj2fTg008hj23Tg009Dj21Tg009^j4KTg00:`j2ATg00;;j2ZTg00;cj3YTg00<Gj2XTg00=8j2WTg00=Yj2VTg00>6j2UTg00>Sj2TTg00?0j3<Tg00?Jj2DTg00?dj3STg00@Kj2OTg00AJj2NTg00Akj2GTg00BIj4MTg00Bgj1QTg00CEj1RTg00D0j2FTg00DSj2:Tg00E6j6jTg00EZj7iTg00F>j1hTg00F`j4CTg00GKj6gTg00Goj3eTg00HRj2_Tg00I4j2^Tg00I`j3`Tg00J?j4]Tg00K1j2aTg00L7j4bTg00LRj4\Tg00Llj7cTg00MPj7dTg00N4j8[Tg00NXR1f0R2g00O6R03<p=71302p=4P1f1R3g00OTP2CCp=@P3g00P;R4g00PZR5P5g00Q:R6P2g00QZFcp=8f2R7P4P5P5P6P3P2Fdp=Bf3R8P4P5P5P6P7P3P2G[p=Jg00R:R9#5R:#5#5R;#5#5#5#>R<#HR=%>;#H#P[%L1R>10<7R?%I1R@5?1g00R_RA3=10<3,2?%;;R;,9?#7#E%;:RB%69RC#6#6#6#6RD#;RE'fRF/3?'1'1P>f6RG10<8RHf4RI,0<RJP2CKf5RK,0<RL=?12==>A'AXD>P@PKP?PHP@CKRMA?1J@==>A1ZBE120BRA%4E120F[R>[%4BRJg00SbR@AYBE3UW0%4FRE\@^0J1XL;%4L%4;f7RL,0<RN/9;RO#4RP[[10<G/W;%7;#E1VN;,U;/TO9<1N[g00T>RQg00Td'D120;e9SN;12O;,APg00UJf8,0<RP/O;ROePOP2P@PGP2P3O2X7JPE^7JPL1N0B,DQPAeO1P>p-0R>g00UfRA#I%LAP11G17P31G18CM%Q1%R1RAPAP4P5P5P61F10RQ1:1CRC'@,8APAP4P5P5P6PKEjFi%h5RLPAP11:19R9g00VR1:1:R:CC,8APAP4P5P5P6P1PCg00W9PQCC,8AEg1F1B%>D5e1/@9,8A5BARD5BAPL1@9:,8A=BADCJCJ1_A6P2P7g00W`RAg00X@R6'D1^27=<A6dA`103C]b>b@bAX41X51X61W1%47/A81237%78g00X`R0[13F3'1'11378%7IP0[13F7'1'1[[^41^51^61^1>P2f=,0<R2/9;R>/2;P>f<,0<P2PKf:O6b=b3b2bGf9,0<R</3P19<;#7#E13F<'1'1eb<b9b8b?b2b31a?HePMeP3CbC\W;W:XF=XE=XC=WBo"). Qed.

Section Gaps.
Variable RT : rt_sig.

(* [comment removed for export] *)
Definition malloc_contractC : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  1 <= n <= 0x4000000 -> a0 = Z_to_bv 64 n -> tp = Z_to_bv 64 TP_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost n <= rt_credit RT Σ ->
  (64512 < n -> sec_bytes (rt_live RT Σ) + n <= SEC_BYTES) (* [comment removed for export] *) ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_malloc m)))
            (malloc_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 n lo m).

Definition free_contractC : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (p n lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  In (p, n) (rt_live RT Σ) -> a0 = Z_to_bv 64 p -> tp = Z_to_bv 64 TP_A ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_free m)))
            (free_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 p lo m).

(* [comment removed for export] *)
Definition CALLOC_MAX : Z := 64512.
Definition calloc_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (nmemb size lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 < nmemb -> 0 < size -> nmemb * size <= CALLOC_MAX -> a0 = Z_to_bv 64 nmemb -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 TP_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_calloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ rw_cells asegs m' p [CB (Z.to_nat (nmemb * size)) (repeat (Z_to_bv 8 0) (Z.to_nat (nmemb * size)))]
         /\ acc asegs m' p (nmemb * size)) c
       /\ rt_live RT Σ' = (p, nmemb * size) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ /\ 0 < p /\ p mod 16 = 0 /\ p + nmemb * size < USTACK_TOP).

(* [comment removed for export] *)
Definition CALLOCK_MAX : Z := 0x4000000.
Definition calloc_contractK : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (nmemb size lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 < nmemb -> 0 < size -> nmemb * size <= CALLOCK_MAX -> a0 = Z_to_bv 64 nmemb -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 TP_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX ->
  (64512 < nmemb * size -> sec_bytes (rt_live RT Σ) + nmemb * size <= SEC_BYTES) -> mcost (nmemb * size) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_calloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' p (nmemb * size) /\ acc asegs m' p (nmemb * size)) c
       /\ rt_live RT Σ' = (p, nmemb * size) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (nmemb * size) /\ 0 < p /\ p mod 16 = 0 /\ p + nmemb * size < USTACK_TOP).

(* [comment removed for export] *)
Definition stack_malloc_contract' (k : nat) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> (k = 0 \/ k = 1 \/ k = 6)%nat -> tp = Z_to_bv 64 TP_A ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc (e_stack_malloc k) m)))
    (fun c => exists (Σ' : rts RT) (f : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 f) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' f (fs_size k - 8) /\ wr_at asegs m' (shad f) (fs_size k / 8)) c
       /\ rt_frames RT Σ' = (f, k) :: rt_frames RT Σ /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - 1 /\ 0 < f /\ f mod 64 = 0 /\ f + fs_size k < USTACK_TOP).

(* [comment removed for export] *)
Definition stack_free_contract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (f : Z) (fr : list (Z * nat)) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> a0 = Z_to_bv 64 f -> rt_frames RT Σ = (f, 6%nat) :: fr ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_stack_free_6 m)))
    (fun c => exists (Σ' : rts RT) (v : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) fr (bv_unsigned sp) m m') c
       /\ rt_frames RT Σ' = fr /\ rt_live RT Σ' = rt_live RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ).

(* [comment removed for export] *)
Definition LEPT_FMTS : list (Z * list bool) :=
  [(* [comment removed for export] *)
   (0x30a80, [true; true]);
   (0x35be0, [true; false; false; false]);
   (0x35ca0, [true]);
   (0x35d00, [true]);
   (0x35d60, [true]);
   (0x35de0, [true]);
   (0x379a0, [true]);
   (0x36b60, [true]);
   (0x37b00, [true; false]);
   (0x37b60, [true; false; false]);
   (0x37bc0, [true; false; false]);
   (0x37c20, [true; false]);
   (0x37c60, [true; false; false]);
   (0x37cc0, [true]);
   (0x37d20, [true; false; false]);
   (0x37d80, [true; false; false]);
   (0x3f520, [true; false]);
   (0x3f680, [true; false; false; false]);
   (* [comment removed for export] *)
   (0x45d60, [true]);
   (0x45dc0, [true]);
   (0x45e20, [true]);
   (0x45e80, [true]);
   (0x45ee0, [true]);
   (0x46060, [true])].  (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint lept_args (Σ : rts RT) (m : mem) (sp : word) (lo D : Z) (kinds : list bool) (ws : list word) : Prop :=
  match kinds, ws with
  | [], _ => True
  | true :: ks, w :: ws' =>
      (exists str, vsn_str RT Σ m sp lo D 2000 (bv_unsigned w) str /\ Z.of_nat (length str) < 96) /\ lept_args Σ m sp lo D ks ws'
  | false :: ks, _ :: ws' => lept_args Σ m sp lo D ks ws'
  | _ :: _, [] => False
  end.

Definition vsnprintf_lept_icontract : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (D ap fmt : Z) (kinds : list bool) (w1 w2 w3 w4 w5 w6 w7 : word) (junk : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 2000 -> a2 = Z_to_bv 64 fmt -> a3 = Z_to_bv 64 ap -> tp = Z_to_bv 64 TP_A ->
  In (fmt, kinds) LEPT_FMTS ->
  rw_cells asegs m ap [C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7] (* [comment removed for export] *) ->
  bv_unsigned sp <= ap -> ap + 56 <= USTACK_TOP - 16 ->
  lept_args Σ m sp lo D kinds [w1; w2; w3; w4; w5; w6; w7] ->
  rw_cells asegs m D [CB 2000 junk] -> checked_dst RT Σ m sp D 2000 -> SEGTOP_A <= D -> D + 2000 <= lo ->
  (D + 2000 <= ap \/ ap + 56 <= D) ->
  io_ssp m -> ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_vsnprintf m)))
    (fun c => exists v : word,
       icpt_post RT Σ PMc ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v lo D 2000 m
                 (fun m' => exists junk', rw_cells asegs m' D [CB 2000 junk']) c).

(* [comment removed for export] *)
Definition LEPT_LITS : list (Z * Z) :=
  [(* [comment removed for export] *)
   (0x35980, 14);
   (0x359a0, 10);
   (0x359c0, 16);
   (0x359e0, 29);
   (0x35ae0, 39);
   (0x35b40, 16);
   (0x35b60, 18);
   (0x35ba0, 19);
   (0x35c40, 12);
   (0x35c60, 24);
   (0x35e40, 11);
   (0x360c0, 16);
   (0x360e0, 12);
   (0x36160, 13);
   (0x361c0, 12);
   (0x36220, 17);
   (0x36300, 10);
   (0x36560, 15);
   (0x36580, 22);
   (0x36600, 11);
   (0x36860, 16);
   (0x36b40, 14);
   (0x37a00, 15);
   (0x37a20, 19);
   (0x37a60, 15);
   (0x37a80, 17);
   (0x37ac0, 23);
   (0x37e20, 22);
   (0x37e60, 15);
   (0x381e0, 17);
   (0x38360, 15);
   (0x38380, 29);
   (0x383c0, 11);
   (0x383e0, 14);
   (0x384c0, 17);
   (0x385c0, 22);
   (0x38600, 20);
   (0x38640, 37);
   (0x3a060, 19);
   (0x3a0a0, 8);
   (0x3a0c0, 16);
   (0x3f2a0, 13);
   (0x3f2c0, 17);
   (0x3f4e0, 25);
   (0x3f580, 18);
   (0x3f5c0, 14);
   (0x3f5e0, 15);
   (0x3f600, 15);
   (0x3f620, 16);
   (0x3f640, 22);
   (0x3f700, 14);
   (0x3f720, 18);
   (0x3f760, 25);
   (0x34280, 21);
   (0x342c0, 11);
   (0x342e0, 37);
   (0x34340, 12);
   (0x34360, 17);
   (0x343a0, 17);
   (0x343e0, 11);
   (0x34400, 16);
   (0x34420, 14);
   (0x34440, 17);
   (0x345e0, 13);
   (0x34600, 11);
   (0x34620, 16);
   (0x34640, 33);
   (0x346a0, 15);
   (0x346c0, 19);
   (0x34700, 21);
   (0x348c0, 37);
   (0x34980, 19);
   (0x349c0, 11);
   (0x34b00, 12);
   (0x35a20, 17);
   (0x35a60, 18);
   (0x35f00, 17);
   (0x363a0, 18);
   (0x36900, 17);
   (0x36d20, 14);
   (0x36d60, 20);
   (0x36da0, 23);
   (0x36fc0, 16);
   (0x370a0, 17);
   (0x370e0, 18);
   (0x37120, 17);
   (0x37160, 17);
   (0x371a0, 24);
   (0x371e0, 20);
   (0x37220, 21);
   (0x37260, 19);
   (0x372a0, 16);
   (0x372c0, 13);
   (0x372e0, 17);
   (0x37320, 19);
   (0x37360, 15);
   (0x37380, 39);
   (0x3a3a0, 17);
   (0x3a3e0, 12);
   (0x3a400, 17);
   (0x3a440, 31);
   (0x35aa0, 24);
   (0x36280, 10);
   (0x362a0, 17);
   (0x35e60, 8);
   (0x35f40, 16);
   (0x35fa0, 15);
   (0x35fc0, 15);
   (0x37960, 12);
   (0x37980, 13);
   (0x37e00, 16);
   (* [comment removed for export] *)
   (0x3a140, 30);
   (0x3a120, 15);
   (0x41620, 17);
   (0x415a0, 22);
   (0x415e0, 14);
   (0x41780, 21);
   (0x36980, 26);
   (0x36960, 10);
   (0x46300, 13);
   (0x41120, 4);
   (0x410c0, 2);
   (0x41140, 6);
   (0x30a80, 17);
   (0x30d00, 32);
   (0x30d40, 10);
   (0x30d60, 14);
   (0x30d80, 17);
   (0x30dc0, 11);
   (0x30de0, 16);
   (0x30e00, 18);
   (0x30e40, 14);
   (0x30fc0, 17);
   (0x31000, 11);
   (0x31020, 21);
   (0x31060, 18);
   (0x311e0, 23);
   (0x31220, 11);
   (0x31240, 17);
   (0x32c40, 19);
   (0x32c80, 13);
   (0x32de0, 37);
   (0x32e40, 14);
   (0x32e60, 15);
   (0x32e80, 16);
   (0x32ea0, 19);
   (0x32ee0, 17);
   (0x32f20, 17);
   (0x32f60, 15);
   (0x32f80, 16);
   (0x32fa0, 16);
   (0x33140, 18);
   (0x33180, 16);
   (0x331a0, 23);
   (0x33360, 18);
   (0x333a0, 37);
   (0x33400, 27);
   (0x35be0, 47);
   (0x35ca0, 48);
   (0x35d00, 52);
   (0x35d60, 53);
   (0x35dc0, 9);
   (0x35de0, 37);
   (0x35e80, 28);
   (0x35ec0, 19);
   (0x35f60, 31);
   (0x36100, 12);
   (0x36120, 19);
   (0x36180, 13);
   (0x361a0, 15);
   (0x361e0, 12);
   (0x36200, 15);
   (0x36260, 10);
   (0x362e0, 11);
   (0x363e0, 19);
   (0x36420, 22);
   (0x364a0, 19);
   (0x36540, 15);
   (0x36940, 12);
   (0x36b60, 27);
   (0x36d40, 13);
   (0x36de0, 16);
   (0x36e00, 23);
   (0x36e40, 25);
   (0x36e80, 18);
   (0x36ec0, 19);
   (0x37920, 18);
   (0x379a0, 37);
   (0x37b00, 37);
   (0x37b60, 47);
   (0x37bc0, 46);
   (0x37c20, 31);
   (0x37c60, 51);
   (0x37cc0, 56);
   (0x37d20, 58);
   (0x37d80, 77);
   (0x37ec0, 16);
   (0x39ee0, 14);
   (0x39f00, 18);
   (0x39f40, 6);
   (0x39f60, 18);
   (0x39fa0, 26);
   (0x39fe0, 24);
   (0x3a0e0, 19);
   (0x3a6e0, 34);
   (0x3a740, 22);
   (0x3a780, 22);
   (0x3c720, 17);
   (0x3c760, 14);
   (0x3c780, 23);
   (0x3c7c0, 13);
   (0x3c7e0, 32);
   (0x3c820, 14);
   (0x3c840, 12);
   (0x3c860, 18);
   (0x3c8a0, 32);
   (0x3c8e0, 10);
   (0x3c900, 16);
   (0x3c920, 10);
   (0x3f520, 35);
   (0x3f680, 84);
   (0x3fe00, 25);
   (0x3fe40, 10);
   (0x3fe60, 9);
   (0x3fe80, 7);
   (0x3ff00, 14);
   (0x3ff40, 17);
   (0x3ff80, 16);
   (0x3ffa0, 15);
   (0x3ffe0, 25);
   (0x40160, 36);
   (0x401c0, 21);
   (0x40200, 25);
   (0x40240, 18);
   (0x40280, 18);
   (0x402c0, 22);
   (0x40300, 33);
   (0x403a0, 20);
   (0x403e0, 19);
   (0x404e0, 22);
   (0x40520, 18);
   (0x40560, 14);
   (0x40580, 14);
   (0x40620, 19);
   (0x40660, 10);
   (0x40680, 37);
   (0x406e0, 11);
   (0x40700, 16);
   (0x40720, 25);
   (0x40760, 15);
   (0x40780, 25);
   (0x407c0, 13);
   (0x407e0, 21);
   (0x40820, 14);
   (0x40840, 18);
   (0x40880, 19);
   (0x408c0, 18);
   (0x40900, 17);
   (0x40940, 17);
   (0x40980, 17);
   (0x409c0, 22);
   (0x40a00, 22);
   (0x40a40, 14);
   (0x40a60, 17);
   (0x40aa0, 13);
   (0x40ac0, 18);
   (0x40b00, 23);
   (0x40b40, 24);
   (0x40b80, 20);
   (0x40bc0, 19);
   (0x40c00, 18);
   (0x40c40, 19);
   (0x40c80, 13);
   (0x40ca0, 71);
   (0x41000, 17);
   (0x41080, 21);
   (0x410e0, 19);
   (0x41160, 3);
   (0x41180, 28);
   (0x411c0, 21);
   (0x41240, 15);
   (0x41260, 20);
   (0x412a0, 20);
   (0x412e0, 46);
   (0x41340, 52);
   (0x413a0, 40);
   (0x41400, 26);
   (0x41440, 32);
   (0x41480, 31);
   (0x414c0, 25);
   (0x41500, 42);
   (0x41600, 13);
   (0x41660, 27);
   (0x416a0, 20);
   (0x416e0, 25);
   (0x41720, 52);
   (0x417c0, 16);
   (0x417e0, 31);
   (0x45ce0, 28);
   (0x45d20, 17);
   (0x45d60, 58);
   (0x45dc0, 46);
   (0x45e20, 59);
   (0x45e80, 49);
   (0x45ee0, 61);
   (0x45f40, 35);
   (0x45fa0, 30);
   (0x45fe0, 20);
   (0x46020, 19);
   (0x46060, 54);
   (0x460c0, 34);
   (0x46120, 45);
   (0x46180, 22);
   (0x461c0, 28);
   (0x46200, 21);
   (0x46240, 27);
   (0x46280, 18);
   (0x462c0, 16);
   (0x462e0, 12);
   (0x46320, 6);
   (0x46340, 24);
   (0x46380, 26);
   (0x463c0, 27);
   (0x46400, 42);
   (0x46460, 31);
   (0x464a0, 31);
   (0x464e0, 31);
   (0x46520, 31);
   (0x46560, 5)].

(* [comment removed for export] *)
Definition LEPT_GLOBALS : list (Z * Z) := [(0x216080, 4); (0x2160a0, 8); (0x216100, 8); (0x216120, 8)].
(* [comment removed for export] *)
Definition LEPT_RMASK32 : Z := 0x36ba0.
(* [comment removed for export] *)
Definition g_GOT_LeptMsgSeverity : Z := 0x212470.

Record rt_gaps : Prop := mkGaps {
  gp_malloc : malloc_contractC;
  gp_free : free_contractC;
  gp_calloc : calloc_contract;
  gp_stack_malloc_0 : stack_malloc_contract' 0;
  gp_stack_malloc_1 : stack_malloc_contract' 1;
  gp_stack_malloc_6 : stack_malloc_contract' 6;
  gp_stack_free_6 : stack_free_contract;
  gp_vsnprintf : vsnprintf_lept_icontract;
  (* [comment removed for export] *)
  gp_acc_lits : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_LITS;
  gp_acc_globals : forall Σ m, ART RT Σ m -> Forall (fun r => acc asegs m (fst r) (snd r)) LEPT_GLOBALS;
  gp_globals_client : forall a, in_ranges (map (fun r => (fst r, fst r + snd r)) LEPT_GLOBALS) a -> client_static a;
  gp_got_lib : forall Σ m, ART RT Σ m -> ro_cells asegs m g_GOT_LeptMsgSeverity [C8 (Z_to_bv 64 0x216080)];
  (* [comment removed for export] *)
  gp_ssp_keep : forall Σ' (m m' : mem), io_ssp m -> ART RT Σ' m' -> (forall a : word, client_static (bv_unsigned a) -> m' a = m a) ->
    io_ssp m';
  (* [comment removed for export] *)
  gp_live_hi : forall Σ m p n, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> p + n <= 0x7fff7000 \/ 0x10007fff8000 <= p;
  (* [comment removed for export] *)
  gp_acc_rmask : forall Σ m, ART RT Σ m -> acc asegs m LEPT_RMASK32 132
}.

End Gaps.
