(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjOd SjAlloc.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Spec Require Import Prelim SjModel AtpModel OdModel.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Sj_stage1_kit Atp_h_defs.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_iface2 RT_anndefs D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps
  Sj_hkit Sj_hkit2 Sj_new Sj_num_akit Sj_num_amem Od_hbaseA Atp_h_defsA Od_defsA Od_cpsA Od_beginA Od_topA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition OD_CUTA : Z := 0x96bc0.
Definition OD_CUTB : Z := 0x96d18.
Definition OD_ERRX : Z := 0x96e48.

Definition od_chars (bs : list byte) : list Z := map bv_unsigned bs.

Definition OD_VEC_COST : Z := 2^31 + 2^26.

Definition OD_PAD_COST : Z := mcost (2^20).

Definition od_shadow (p q : Z) : list cell :=
  map (fun z => C1 (Z_to_bv 8 z))
    [0xf1; 0xf1; 0xf1; 0xf1; 0; 0; 0; 0xf2; 0xf2; 0xf2; 0xf2; 0xf2; p; p; p; p; p; p; p; 0xf2; 0xf2; 0xf2; 0xf2; 0xf2; q; q; q; q; q; q; q; q;
     0xf3; 0xf3; 0xf3; 0xf3].

Definition od_lowA (F act : Z) (j0 j192 j216 j224 j248 : list byte) : list cell :=
  [CB 184 j0; C8 (wz act); CB 8 j192; C8 (wz F); C8 (wz (F + 96)); CB 8 j216; CB 16 j224; C8 (wz (F / 8 + 2147450880)); CB 104 j248].
Definition od_lowB (F act : Z) (j0 j192 j224 j248 : list byte) : list cell :=
  [CB 184 j0; C8 (wz act); CB 8 j192; C8 (wz F); C8 (wz (F + 96)); C8 (wz (F + 104)); CB 16 j224; C8 (wz (F / 8 + 2147450880)); CB 104 j248].

Definition od_parserB (jp : list byte) : list cell :=
  [C1 (Z_to_bv 8 0); CB 7 jp; C8 (wz 0); C8 (wz 0); C8 (wz 0xffffffff); C8 (wz 1024); C8 (wz 0); C8 (wz 0)].

Section SetupDefs.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).

Record od_cut0 (Σ0 Σx : rts RT) (m0 mx : mem) (usp S1 F lo : Z) (A cap size : Z) (els : list (Z * Z))
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop := mkOdCut0 {
  c0_usp : usp mod 16 = 0 /\ usp + 16 <= USTACK_TOP;
  c0_S1 : S1 mod 32 = 0 /\ usp - 528 <= S1 <= usp - 512;
  c0_lo : rt_sp0 RT Σ0 - STACK_WIN <= lo /\ lo + FUZZ_STACK <= usp;
  c0_F : F mod 64 = 0 /\ 0 < F;
  c0_frames0 : rt_frames RT Σ0 = [];
  c0_lpos : forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n;
  c0_lvb : Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX;
  c0_cr0 : FUZZ_COST <= rt_credit RT Σ0;
  c0_art : ART RT Σx mx;
  c0_mi : mem_inv asegs mx;
  c0_stk : stk asegs mx lo S1;
  c0_frames : rt_frames RT Σx = [(F, 3%nat)];
  c0_sp0 : rt_sp0 RT Σx = rt_sp0 RT Σ0;
  c0_hi : exists j352 j400, rw_cells asegs mx (S1 + 352) [CB 48 j352; CB 8 j400];
  c0_pad : stk asegs mx (S1 + 408) (usp - 104);
  c0_saved : rw_cells asegs mx (usp - 104) (fa_saved cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11);
  c0_hdr : exists h0 h8, rw_cells asegs mx F [CB 8 h0; CB 24 h8];
  c0_vec : vrepA mx (F + 32) A cap size els;
  c0_size : 1 <= size;
  c0_wrs : wr_at asegs mx (F / 8 + 2147450880) 64;
  c0_doc : exists jd, rw_cells asegs mx (F + 192) [CB 64 jd];
  c0_lib : LIB mx;
  c0_pres : rt_pres_fp (rt_live RT Σ0) [] usp LIB_FP m0 mx
}.

Record od_cutA (Σ0 ΣA : rts RT) (m0 mA : mem) (usp S1 F lo : Z) (dz : list Z) (A cap size p0 : Z) (els : list (Z * Z))
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop := mkOdCutA {
  ca_0 : od_cut0 Σ0 ΣA m0 mA usp S1 F lo A cap size els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11;
  ca_dz : bytes_ok dz /\ zlength dz < 2^26;
  ca_live : rt_live RT ΣA = vblockA A cap size ++ rt_live RT Σ0;
  ca_credit : rt_credit RT Σ0 - OD_VEC_COST <= rt_credit RT ΣA;
  ca_low : exists j0 j192 j216 j224 j248, rw_cells asegs mA S1 (od_lowA F (od_action dz) j0 j192 j216 j224 j248);
  ca_par : exists jp, rw_cells asegs mA (F + 96) [CB 56 jp];
  ca_sh : rw_cells asegs mA (F / 8 + 2147450880) (od_shadow 0xf8 0xf8);
  ca_s0 : exists els', els = (p0, zlength (od_s0 dz)) :: els';
  ca_s0p : 0 <= p0;
  ca_s0b : bytes_at asegs mA p0 (zbytes (od_s0 dz));
  ca_s0l : od_s0 dz = [] \/ exists p k, In (p, k) (rt_live RT Σ0) /\ p <= p0 /\ p0 + zlength (od_s0 dz) <= p + k
}.

Definition od_cutA_k (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z) (dz : list Z)
    (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop :=
  forall (ΣA : rts RT) (S1 F A cap size p0 : Z) (els : list (Z * Z))
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs8 xs9 xs10 xt3 xt4 xt5 xt6 : word) xF xfc (mA : mem),
    frm0 xfc ->
    od_cutA Σ0 ΣA m0 mA usp S1 F lo dz A cap size p0 els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
    aevt ΣA K (MS (mkR xra (wz S1) gp (wz 0x6488f0) xt0 xt1 xt2 (wz usp) (wz S1)
                       xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (wz F) (wz 2147450880) (wz (F + 32)) xs5 (wz (F + 192)) (wz A) xs8 xs9 xs10 (wz (F / 8 + 2147450880))
                       xt3 xt4 xt5 xt6)
                  xF (wz OD_CUTA) xfc None mA (seg_rom asegs)).

Record od_cutB (Σ0 ΣB : rts RT) (m0 mB : mem) (usp S1 F lo : Z) (dz : list Z) (A cap size COPY BUF : Z) (els : list (Z * Z))
    (cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop := mkOdCutB {
  cb_0 : od_cut0 Σ0 ΣB m0 mB usp S1 F lo A cap size els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11;
  cb_dz : bytes_ok dz /\ zlength dz < 2^26;
  cb_live : rt_live RT ΣB = (if od_copied dz then [(COPY, zlength (od_s0 dz) + 64)] else []) ++ vblockA A cap size ++ rt_live RT Σ0;
  cb_copy : if od_copied dz
            then 0 < COPY /\ COPY mod 16 = 0 /\ COPY <= BUF <= COPY + 3 /\ BUF - COPY + zlength (od_doc dz) = zlength (od_s0 dz)
                 /\ bytes_at asegs mB BUF (padded_bytes (od_doc dz))
            else COPY = 0 /\ BUF = 0;
  cb_credit : rt_credit RT Σ0 - OD_VEC_COST - OD_PAD_COST <= rt_credit RT ΣB;
  cb_low : exists j0 j192 j224 j248, rw_cells asegs mB S1 (od_lowB F (od_action dz) j0 j192 j224 j248);
  cb_par : exists jp, rw_cells asegs mB (F + 96) (od_parserB jp);
  cb_sh : rw_cells asegs mB (F / 8 + 2147450880) (od_shadow 0 0)
}.

Definition od_cutB_k (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z) (dz : list Z)
    (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop :=
  forall (ΣB : rts RT) (S1 F A cap size COPY BUF : Z) (els : list (Z * Z))
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs10 xt3 xt4 xt5 xt6 : word) xF xfc (mB : mem),
    frm0 xfc ->
    od_cutB Σ0 ΣB m0 mB usp S1 F lo dz A cap size COPY BUF els cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
    aevt ΣB K (MS (mkR xra (wz S1) gp (wz 0x6488f0) xt0 xt1 xt2 (wz usp) (wz S1)
                       xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                       (wz F) (wz 2147450880) (wz (F + 32)) (wz (F + 96)) (wz (F + 192)) (wz COPY) (wz (zlength (od_doc dz))) (wz BUF)
                       xs10 (wz (F / 8 + 2147450880))
                       xt3 xt4 xt5 xt6)
                  xF (wz OD_CUTB) xfc None mB (seg_rom asegs)).

Definition od_iter_k (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z)
    (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word) : Prop :=
  forall (Σ1 : rts RT) (E : oaenv) (A cap size IA OC : Z) (els : list (Z * Z))
         xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1,
    od_geo E -> od_rt RT Σ1 E m1 -> OD_PRE E m1 -> o_m0 E = m1 ->
    od_outer RT LIB Σ1 E A cap size IA OC els (rt_live RT Σ0) cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 m1 ->
    oa_USP E = usp -> o_lo E = lo -> o_gp E = gp ->
    rt_sp0 RT Σ1 = rt_sp0 RT Σ0 ->
    rt_credit RT Σ0 - FUZZ_COST + OD_DBL_CREDIT * (o_n E + 2) <= rt_credit RT Σ1 ->
    frm0 xfc ->
    aevt Σ1 K (ODIST E xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1).

Definition od_phaseA_stmt : Prop :=
  forall (Σ : rts RT) (K : config -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (d : Z) (bs : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 (Z.of_nat (length bs)) -> tp = Z_to_bv 64 0x6488f0 ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  rt_frames RT Σ = [] -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ ->
  LIB m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + FUZZ_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  od_cutA_k K Σ m (bv_unsigned sp) lo (od_chars bs) gp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ->
  aevt Σ K (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_fuzz m).

Definition od_phaseB_stmt : Prop :=
  forall (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z) (dz : list Z)
         (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word),
  fdfs_only PMc -> mat_stable PMc ->
  od_cutB_k K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  od_cutA_k K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11.

Definition od_phaseC_stmt : Prop :=
  forall (K : config -> Prop) (Σ0 : rts RT) (m0 : mem) (usp lo : Z) (dz : list Z)
         (gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 : word),
  fdfs_only PMc -> mat_stable PMc ->
  od_iter_k K Σ0 m0 usp lo gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 ->
  od_fin_k RT LIB PMc K Σ0 usp lo cra gp cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11 m0 (rt_credit RT Σ0 - FUZZ_COST) ->
  od_cutB_k K Σ0 m0 usp lo dz gp cra cs0 cs1 cs2 cs3 cs4 cs5 cs6 cs7 cs8 cs9 cs10 cs11.

Theorem od_setup_of_phases : od_phaseA_stmt -> od_phaseB_stmt -> od_phaseC_stmt -> od_setup_stmt RT LIB PMc.
Proof using.
  intros PA PB PC.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
    FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM KI KF.
  apply (PA Σ K ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m d bs lo
           FDO MST EA0 EA1 ETP D0 BSL BS INLV FRS0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM).
  apply (PB K Σ m (bv_unsigned sp) lo (od_chars bs) gp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FDO MST).
  apply (PC K Σ m (bv_unsigned sp) lo (od_chars bs) gp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FDO MST); [| exact KF].
  unfold od_iter_k. intros Σ1 E A cap size IA OC els xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
    G R PRE EM0 OUT EUSP ELO EGP SP1 CR1 FRM1.
  exact (KI Σ1 E A cap size IA OC els xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs8 xs10 xs11 xt3 xt4 xt5 xt6 xF xfc m1
           G R PRE EM0 OUT EUSP ELO EGP SP1 CR1 FRM1).
Qed.

End SetupDefs.
