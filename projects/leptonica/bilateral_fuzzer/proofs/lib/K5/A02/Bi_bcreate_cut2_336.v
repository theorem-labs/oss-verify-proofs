(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Km_setelem Km_iface Km_kit KmF_kit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Cf_iface Cf_kit CfX_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_fpkit Bi_pixakit Bi_addkit Bi_relkit Bi_restore Bi_lskit Bi_kmkit Bi_bgkit Bi_fpkit2 Bi_iface2 Bi_bcreate_defs Bi_bckit Bi_bcreate_cut Bi_bcreate_cut2 Bi_bcreate_cut336 D_iface D_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section BICUT2_336.
Variable RT : rt_sig.

Definition bc_cutB336_stmt : Prop :=
∀ (Σ : rts RT) (PMc : Model → Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (m : mem) (lo pix : Z) (v : pixv) (ras : list Z),
fdfs_only PMc → mat_stable PMc → reg_get F r_fa0 = fs32 F_5_0 → reg_get F r_fa1 = fs32 F_10_0 → pix8 (rt_live RT Σ) m pix v → 22 <= p_w v → 22 <= p_h v → let
usp := bv_unsigned sp in chain_ok m usp (bv_unsigned s0) ras → Forall (λ f : Z, In (f :: bv_unsigned ra :: ras) CLIENT_TRACES) [797260; 797536; 797672; 797756;
797844; 798012] → In (PIXA_CALLOC1 :: bv_unsigned ra :: ras) CLIENT_TRACES → In (PGLP_CALLOC :: RA_BC_LINEPTRS :: bv_unsigned ra :: ras) CLIENT_TRACES → Forall
(λ f : Z, In (f :: RA_BC_DESTROY :: bv_unsigned ra :: ras) CLIENT_TRACES) DESTROY_FREE_RAS → ∀ (m1 x1 : mem) (x0 : Z) (fr := x0) (m2 : mem), ART RT Σ m → rt_sp0
RT Σ - 8388608 <= lo → lo + (65536 + 1024 * 10) <= usp → usp + 16 <= 140737488355328 → usp mod 16 = 0 → usp <= rt_sp0 RT Σ → Z.of_nat (length (rt_frames RT Σ))
+ 9 <= Z.of_nat FRAMES_MAX → Z.of_nat (length (rt_live RT Σ)) + 48 <= LIVE_MAX → 22 * RASTER_COST + 2 ^ 26 <= rt_credit RT Σ → (∀ p n : Z, In (p, n) (rt_live RT
Σ) → 0 < n) → sec_bytes (rt_live RT Σ) + BC_SECB <= SEC_BYTES → pix_obj (rt_live RT Σ) m pix v {| c_arr := 0; c_depth := 0; c_nalloc := 0; c_n := 0 |} → p_d v =
8 → p_cmap v = 0 → p_data v ≠ 0 → In (pix, 64) (rt_live RT Σ) → 0 < pix → pix mod 16 = 0 → 0 < 64 → 6692864 + 8388608 <= rt_sp0 RT Σ → rt_sp0 RT Σ <=
140737488355328 → 140735340871680 <= rt_sp0 RT Σ → sp = Z_to_bv 64 usp → 0 <= usp → usp < 2 ^ 64 → let QF := λ c : config, ∃ (Σ' : rts RT) (bil : Z) (b : bilv)
(vsc : pixv) (ps : list pixe) (lps : list Z), ASTA RT Σ' PMc (λ ms : machine_state, ∃ m' : mem, ret_stF ra (Z_to_bv 64 usp) gp (Z_to_bv 64 TP_A) s0 s1 s2 s3 s4
s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 bil) F m' ms ∧ ((ART RT Σ' m' ∧ mem_inv asegs m' ∧ stk asegs m' lo usp) ∧ LIBH m' ∧ io_ssp m') ∧ rt_pres_fp (rt_live RT Σ)
(rt_frames RT Σ) usp [(pix + 20, pix + 24)] m m' ∧ (bil = 0 → pix8 (rt_live RT Σ') m' pix v) ∧ (bil ≠ 0 → b_pixs b = pix ∧ bil_obj (rt_live RT Σ') m' bil b v
vsc ps lps)) c ∧ rt_live RT Σ' = (if bil =? 0 then rt_live RT Σ else bil_live bil b vsc ps lps (rt_live RT Σ)) ∧ rt_frames RT Σ' = rt_frames RT Σ ∧ rt_sp0 RT Σ'
= rt_sp0 RT Σ ∧ rt_credit RT Σ - BC_COST <= rt_credit RT Σ' in 0 <= lo → usp <= 2 ^ 64 → let PF0 := λ a : Z, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ∧
outside [] a in (∀ a : Z, PF0 a → usp <= a ∨ a < lo) → usp mod 32 = 16 → In (pix, 64) (rt_live RT Σ) → pix + 64 <= rt_sp0 RT Σ - 8388608 → parked (pix + 64 <=
65536 ∨ 6692864 <= pix) → parked (pix + 64 <= 2147446784 ∨ 17594333495296 <= pix) → ∀ (junk : list byte) (x19 m3 x39 x58 x77 x96 : mem) (x37 : Z) (pixsc := x37)
(m4 x115 : mem) (x114 : Z) (bil := x114) (x130 : bvmap 5 word) (x57 : Z) (minval := x57) (x76 : Z) (maxval := x76) (m5 x133 m6 x152 m' : mem) (x151 : Z) (nc :=
x151) (m0 x171 mk : mem) (x170 : Z) (kidx := x170) (m7 x190 mf : mem) (x189 : Z) (kfr := x189) (m8 x209 : mem), wmono asegs m x209 → ART RT Σ m1 → ∀ x : rts RT,
rt_frames RT x = (fr, 2%nat) :: rt_frames RT Σ → rt_live RT x = rt_live RT Σ → rt_sp0 RT x = rt_sp0 RT Σ → rt_credit RT x = rt_credit RT Σ - 1 → 0 < fr → fr mod
64 = 0 → fr + 256 < 140737488355328 → ART RT x x1 → wmono asegs m1 x209 → ∀ x16 : bvmap 5 word, fs_agree (bvmap_set 8 (nan_box (sgnj_val F_SGNJ (unbox_s
(reg_get F 11)) (unbox_s (reg_get F 11)))) (bvmap_set 9 (nan_box (sgnj_val F_SGNJ (unbox_s (reg_get F 10)) (unbox_s (reg_get F 10)))) F)) x16 → ∀ jf js : list
byte, 0 < fr → fr + 256 <= rt_sp0 RT Σ - 8388608 → fr mod 64 = 0 → 6692864 <= fr → parked (fr + 256 <= 2147446784 ∨ 17594333495296 <= fr) → In (pix, 64)
(rt_live RT x) → pix + 64 <= rt_sp0 RT Σ - 8388608 → parked (pix + 64 <= 65536 ∨ 6692864 <= pix) → parked (pix + 64 <= 2147446784 ∨ 17594333495296 <= pix) →
parked (fr + 256 <= pix ∨ pix + 64 <= fr) → parked (pix + 64 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= pix) → wmono asegs x1 x209 → ∀ (me : mem)
(x208 : Z) (spat := x208) (m10 x4 mr : mem) (x3 : Z) (rng := x3) (m11 x29 : mem) (x25 : Z) (pxa := x25) (x38 : pixv) (vsc := x38) (m9 : mem), rw_cells asegs m9
(fr / 8 + 2147450880) [C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 (-15)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1
(Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1
(Z_to_bv 8 4); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-14));
C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 (-14)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); C1 (Z_to_bv 8 (-13)); CB 4 (skipn 1 (skipn 1 (skipn 1
(skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 5 (skipn 1 (skipn 1 (skipn 1 (skipn 5 (skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 1 (skipn 1
js))))))))))))))))))))] → ART RT x m2 → let PF := λ a : Z, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a ∧ outside [(pix + 20, pix + 24)] a in (∀ a : Z, PF a →
PF0 a) → (∀ a : Z, PF a → usp <= a ∨ a < lo) → (∀ a : Z, PF a → (a < fr ∨ fr + 256 <= a) ∧ (a < fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= a)) → wmono
asegs m2 x209 → (∀ (Σ0 : rts RT) (PMc0 : Model → Prop) (ra0 sp0 gp0 tp t0 t1 t2 s12 s13 a0 a1 a2 a3 a4 a5 a6 a7 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 t3 t4 t5
t6 : word) (F0 : bvmap 5 word) (fc : bv 32) (m12 : mem) (lo0 pix0 : Z) (v0 : pixv) (cv : cmapv) (rc : Z), fdfs_only PMc0 → mat_stable PMc0 → tp = Z_to_bv 64
TP_A → a0 = Z_to_bv 64 pix0 → pix_obj_rc (rt_live RT Σ0) m12 pix0 v0 cv rc → 1 <= rc < 2 ^ 31 - 1 → lenv RT Σ0 m12 sp0 lo0 (LSTK 1) → cps asegs (ASTA RT Σ0 PMc0
(eq (entry_st ra0 sp0 gp0 tp t0 t1 t2 s12 s13 a0 a1 a2 a3 a4 a5 a6 a7 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 t3 t4 t5 t6 F0 fc e_pixClone m12))) (λ c : config,
∃ Σ' : rts RT, ASTA RT Σ' PMc0 (λ ms : machine_state, ∃ m'0 : mem, ret_stF ra0 sp0 gp0 tp s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 (Z_to_bv 64 pix0) F0
m'0 ms ∧ ((ART RT Σ' m'0 ∧ mem_inv asegs m'0 ∧ wmono asegs m12 m'0 ∧ stk asegs m'0 lo0 (bv_unsigned sp0)) ∧ LIBH m'0 ∧ io_ssp m'0) ∧ rt_pres_fp (rt_live RT Σ')
(rt_frames RT Σ0) (bv_unsigned sp0) [( pix0 + 20, pix0 + 24)] m12 m'0 ∧ rw_cells asegs m'0 pix0 (pix_cells_rc v0 (rc + 1))) c ∧ rt_live RT Σ' = rt_live RT Σ0 ∧
rt_frames RT Σ' = rt_frames RT Σ0 ∧ rt_sp0 RT Σ' = rt_sp0 RT Σ0 ∧ rt_credit RT Σ' = rt_credit RT Σ0)) → ∀ x18 : rts RT, rt_live RT x18 = rt_live RT x →
rt_frames RT x18 = rt_frames RT x → rt_sp0 RT x18 = rt_sp0 RT x → rt_credit RT x18 = rt_credit RT x → ART RT x18 x19 → wmono asegs m2 x209 → ∀ x34 : bvmap 5
word, fs_agree x16 x34 → wmono asegs x19 x209 → rw_cells asegs m9 (fr + 100) [CB 12 (firstn 12 (skipn 4 (skipn 72 (firstn 104 (skipn 8 (skipn 8 (skipn 8
jf)))))))] → rw_cells asegs m9 (fr + 116) [CB 12 (firstn 12 (skipn 4 (skipn 12 (skipn 4 (skipn 72 (firstn 104 (skipn 8 (skipn 8 (skipn 8 jf)))))))))] → rw_cells
asegs m9 (fr + 136) [CB 112 (skipn 112 (skipn 8 (skipn 8 (skipn 8 jf))))] → reg_get F 10 = fs32 F_5_0 → reg_get F 10 = fs32 F_5_0 → parked (4096 <= bv_unsigned
ra < 2 ^ 64) → (∀ (S0 : rts RT) (mm : mem) (q n a : Z), ART RT S0 mm → In (fr, 2%nat) (rt_frames RT S0) → In (q, n) (rt_live RT S0) → q <= a < q + n → (a < fr ∨
fr + 256 <= a) ∧ (a < fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= a) ∧ a < rt_sp0 RT S0 - 8388608) → ART RT x18 m3 → (∀ (Σ0 : rts RT) (PMc0 : Model →
Prop) (ra0 sp0 gp0 tp t0 t1 t2 s12 s13 a0 a1 a2 a3 a4 a5 a6 a7 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 t3 t4 t5 t6 : word) (F0 : bvmap 5 word) (fc : bv 32) (m12
: mem) (lo0 pix0 : Z) (v0 : pixv) (l r t b rc : Z) (ras0 : list Z), fdfs_only PMc0 → mat_stable PMc0 → tp = Z_to_bv 64 TP_A → a0 = Z_to_bv 64 pix0 → a1 =
Z_to_bv 64 l → a2 = Z_to_bv 64 r → a3 = Z_to_bv 64 t → a4 = Z_to_bv 64 b → pix_obj_rc (rt_live RT Σ0) m12 pix0 v0 {| c_arr := 0; c_depth := 0; c_nalloc := 0;
c_n := 0 |} rc → 1 <= rc <= 2 → p_d v0 = 8 → p_cmap v0 = 0 → p_data v0 ≠ 0 → 1 <= l <= 21 → 1 <= r <= 21 → 1 <= t <= 21 → 1 <= b <= 21 → l <= p_w v0 → r <= p_w
v0 → t <= p_h v0 → b <= p_h v0 → uctx m12 sp0 s12 ras0 → In (PMCOPY_CALLOC1 :: 651260 :: 652488 :: bv_unsigned ra0 :: ras0) CLIENT_TRACES → lenv RT Σ0 m12 sp0
lo0 (LSTK 9) → lres RT Σ0 7 4 (RASTER_COST + 1024) → sec_bytes (rt_live RT Σ0) + 67108864 <= SEC_BYTES → cps asegs (ASTA RT Σ0 PMc0 (eq (entry_st ra0 sp0 gp0 tp
t0 t1 t2 s12 s13 a0 a1 a2 a3 a4 a5 a6 a7 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 t3 t4 t5 t6 F0 fc e_pixAddMirroredBorder m12))) (λ c : config, ∃ (Σ' : rts RT)
(pixd : Z) (vd : pixv), ASTA RT Σ' PMc0 (λ ms : machine_state, ∃ m'0 : mem, ret_stF ra0 sp0 gp0 tp s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 (Z_to_bv 64
pixd) F0 m'0 ms ∧ ((ART RT Σ' m'0 ∧ mem_inv asegs m'0 ∧ wmono asegs m12 m'0 ∧ stk asegs m'0 lo0 (bv_unsigned sp0)) ∧ LIBH m'0 ∧ io_ssp m'0) ∧ rt_pres_fp
(rt_live RT Σ0) (rt_frames RT Σ0) (bv_unsigned sp0) [] m12 m'0 ∧ pix_obj_rc (rt_live RT Σ') m'0 pix0 v0 {| c_arr := 0; c_depth := 0; c_nalloc := 0; c_n := 0 |}
rc ∧ (pixd ≠ 0 → pix8 (rt_live RT Σ') m'0 pixd vd ∧ p_w vd = p_w v0 + l + r ∧ p_h vd = p_h v0 + t + b)) c ∧ rt_live RT Σ' = (if pixd =? 0 then rt_live RT Σ0
else pix_new_live pixd vd (rt_live RT Σ0)) ∧ rt_frames RT Σ' = rt_frames RT Σ0 ∧ rt_sp0 RT Σ' = rt_sp0 RT Σ0 ∧ rt_credit RT Σ0 - (RASTER_COST + 1024) <=
rt_credit RT Σ')) → ∀ x36 : rts RT, let LIVE1 := if pixsc =? 0 then rt_live RT x18 else pix_new_live pixsc vsc (rt_live RT x18) in rt_live RT x36 = (p_data vsc,
4 * (p_wpl vsc * p_h vsc)) :: (pixsc, 64) :: rt_live RT x18 → rt_frames RT x36 = rt_frames RT x18 → rt_sp0 RT x36 = rt_sp0 RT x18 → rt_credit RT x18 -
(RASTER_COST + 1024) <= rt_credit RT x36 → ART RT x36 x39 → wmono asegs m3 x209 → ∀ x54 : bvmap 5 word, fs_agree (bvmap_set 9 (Z_to_bv 64 18446744070498811904)
(bvmap_set 14 (Z_to_bv 64 18446744070479937536) (bvmap_set 15 (Z_to_bv 64 18446744070508249088) x34))) x54 → (∀ e : Z * Z, In e (rt_live RT Σ) → In e LIVE1) →
Z.of_nat (length LIVE1) <= Z.of_nat (length (rt_live RT Σ)) + 2 → (∀ p n : Z, In (p, n) LIVE1 → 0 < n) → let LP := if pixsc =? 0 then [] else [(pixsc, 64)] in
(∀ bq kq xq : Z, In (bq, kq) [(pixsc, 64)] → bq <= xq < bq + kq → xq < pix + 20 ∨ pix + 24 <= xq) → rw_cells asegs m9 (fr / 8 + 2147450892) [C1 (Z_to_bv 8 4)] →
rw_cells asegs m9 (fr / 8 + 2147450894) [C1 (Z_to_bv 8 4)] → wmono asegs x39 x209 → (∀ (Σ0 : rts RT) (PMc0 : Model → Prop) (ra0 sp0 gp0 tp t0 t1 t2 s12 s13 a0
a1 a2 a3 a4 a5 a6 a7 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 t3 t4 t5 t6 : word) (F0 : bvmap 5 word) (fc : bv 32) (m12 : mem) (lo0 pix0 rc ty pg : Z) (v0 :
pixv) (x2 : word), fdfs_only PMc0 → mat_stable PMc0 → tp = Z_to_bv 64 TP_A → a0 = Z_to_bv 64 pix0 → a1 = Z_to_bv 64 1 → a2 = Z_to_bv 64 ty → a3 = z64 → a4 = z64
→ a5 = z64 → a6 = Z_to_bv 64 pg → ty = L_SELECT_MIN ∨ ty = L_SELECT_MAX → pix_obj_rc (rt_live RT Σ0) m12 pix0 v0 {| c_arr := 0; c_depth := 0; c_nalloc := 0; c_n
:= 0 |} rc → 1 <= rc <= 2 → p_d v0 = 8 → p_cmap v0 = 0 → p_data v0 ≠ 0 → optrF RT Σ0 m12 pg 4 → rw_cells asegs m12 pg [C4 x2] → lenv RT Σ0 m12 sp0 lo0 (LSTK 3)
→ lres RT Σ0 2 0 2 → cps asegs (ASTA RT Σ0 PMc0 (eq (entry_st ra0 sp0 gp0 tp t0 t1 t2 s12 s13 a0 a1 a2 a3 a4 a5 a6 a7 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 t3
t4 t5 t6 F0 fc e_pixGetExtremeValue m12))) (λ c : config, ∃ (Σ' : rts RT) (val : Z), ASTA RT Σ' PMc0 (λ ms : machine_state, ∃ m'0 : mem, ret_stF ra0 sp0 gp0 tp
s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 z64 F0 m'0 ms ∧ ((ART RT Σ' m'0 ∧ mem_inv asegs m'0 ∧ wmono asegs m12 m'0 ∧ stk asegs m'0 lo0 (bv_unsigned sp0))
∧ LIBH m'0 ∧ io_ssp m'0) ∧ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ0) (bv_unsigned sp0) [(pg, pg + 4)] m12 m'0 ∧ rw_cells asegs m'0 pg [C4 (Z_to_bv 64 val)] ∧
0 <= val <= 255) c ∧ rt_live RT Σ' = rt_live RT Σ0 ∧ rt_frames RT Σ' = rt_frames RT Σ0 ∧ rt_sp0 RT Σ' = rt_sp0 RT Σ0 ∧ rt_credit RT Σ0 - 2 <= rt_credit RT Σ'))
→ ∀ x56 : rts RT, rt_live RT x56 = rt_live RT x36 → rt_frames RT x56 = rt_frames RT x36 → rt_sp0 RT x56 = rt_sp0 RT x36 → ART RT x56 x58 → wmono asegs x39 x209
→ rw_cells asegs m9 (fr + 96) [C4 (Z_to_bv 64 minval)] → 0 <= minval → minval <= 255 → ∀ x73 : bvmap 5 word, fs_agree x54 x73 → wmono asegs x58 x209 → ∀ x75 :
rts RT, rt_live RT x75 = rt_live RT x56 → rt_frames RT x75 = rt_frames RT x56 → rt_sp0 RT x75 = rt_sp0 RT x56 → ART RT x75 x77 → wmono asegs x58 x209 → rw_cells
asegs m9 (fr + 112) [C4 (Z_to_bv 64 maxval)] → 0 <= maxval → maxval <= 255 → ∀ x92 : bvmap 5 word, fs_agree x73 x92 → rw_cells asegs m9 (fr / 8 + 2147450896)
[C1 (Z_to_bv 8 0)] → parked (fr + 256 <= pix ∨ pix + 64 <= fr) → wmono asegs x77 x209 → (∀ (Σ0 : rts RT) (PMc0 : Model → Prop) (ra0 sp0 gp0 tp t0 t1 t2 s12 s13
a0 a1 a2 a3 a4 a5 a6 a7 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 t3 t4 t5 t6 : word) (F0 : bvmap 5 word) (fc : bv 32) (m12 : mem) (lo0 pp pix0 : Z) (v0 : pixv)
(cv : cmapv) (rc : Z), fdfs_only PMc0 → mat_stable PMc0 → tp = Z_to_bv 64 TP_A → a0 = Z_to_bv 64 pp → optr RT Σ0 m12 pp 8 → rw_cells asegs m12 pp [C8 (Z_to_bv
64 pix0)] → pix_obj_rc (rt_live RT Σ0) m12 pix0 v0 cv rc → 2 <= rc < 2 ^ 31 → pp + 8 <= pix0 ∨ pix0 + 64 <= pp → lenv RT Σ0 m12 sp0 lo0 (LSTK 4) → lres RT Σ0 1
0 1 → cps asegs (ASTA RT Σ0 PMc0 (eq (entry_st ra0 sp0 gp0 tp t0 t1 t2 s12 s13 a0 a1 a2 a3 a4 a5 a6 a7 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 t3 t4 t5 t6 F0 fc
e_pixDestroy m12))) (λ c : config, ∃ (Σ' : rts RT) (rv : word), ASTA RT Σ' PMc0 (λ ms : machine_state, ∃ m'0 : mem, ret_stF ra0 sp0 gp0 tp s12 s13 s14 s15 s16
s17 s18 s19 s20 s21 s22 s23 rv F0 m'0 ms ∧ ((ART RT Σ' m'0 ∧ mem_inv asegs m'0 ∧ wmono asegs m12 m'0 ∧ stk asegs m'0 lo0 (bv_unsigned sp0)) ∧ LIBH m'0 ∧ io_ssp
m'0) ∧ rt_pres_fp (rt_live RT Σ') (rt_frames RT Σ0) (bv_unsigned sp0) [( pp, pp + 8); (pix0 + 20, pix0 + 24)] m12 m'0 ∧ rw_cells asegs m'0 pp [C8 z64] ∧
rw_cells asegs m'0 pix0 (pix_cells_rc v0 (rc - 1))) c ∧ rt_live RT Σ' = rt_live RT Σ0 ∧ rt_frames RT Σ' = rt_frames RT Σ0 ∧ rt_sp0 RT Σ' = rt_sp0 RT Σ0 ∧
rt_credit RT Σ0 - 1 <= rt_credit RT Σ')) → ∀ x94 : rts RT, rt_live RT x94 = rt_live RT x75 → rt_frames RT x94 = rt_frames RT x75 → rt_sp0 RT x94 = rt_sp0 RT x75
→ ART RT x94 x96 → wmono asegs x77 x209 → rw_cells asegs m9 (fr + 128) [ C8 z64] → ∀ x111 : bvmap 5 word, fs_agree x92 x111 → rt_credit RT Σ - (RASTER_COST +
1030) <= rt_credit RT x94 → wmono asegs x96 x209 → pixsc ≠ 0 → (pixsc =? 0) = false → p_w vsc = p_w v + 11 + 11 → p_h vsc = p_h v + 11 + 11 → In ( pixsc, 64)
(rt_live RT x36) → 0 < pixsc → pixsc mod 16 = 0 → pix_hdr_ok vsc → In (p_data vsc, 4 * (p_wpl vsc * p_h vsc)) (rt_live RT x36) → 0 < p_data vsc → p_data vsc mod
16 = 0 → p_data vsc ≠ pixsc → p_d vsc = 8 → p_cmap vsc = 0 → p_data vsc ≠ 0 → 0 < 4 * (p_wpl vsc * p_h vsc) → 4 * (p_wpl vsc * p_h vsc) <= 67108864 → pixsc + 64
<= rt_sp0 RT Σ - 8388608 → pixsc < 2 ^ 47 → In (797260 :: bv_unsigned ra :: ras) CLIENT_TRACES → In (797536 :: bv_unsigned ra :: ras) CLIENT_TRACES → In (797672
:: bv_unsigned ra :: ras) CLIENT_TRACES → In (797756 :: bv_unsigned ra :: ras) CLIENT_TRACES → In (797844 :: bv_unsigned ra :: ras) CLIENT_TRACES → In (798012
:: bv_unsigned ra :: ras) CLIENT_TRACES → (∀ e : Z * Z, In e [(pixsc, 64)] → In e (( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ)) →
(∀ e : Z * Z, In e (rt_live RT Σ) → In e (( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ)) → ART RT x94 m4 → ∀ x113 : rts RT, rt_live
RT x113 = (bil, 104) :: rt_live RT x94 → rt_frames RT x113 = rt_frames RT x94 → rt_sp0 RT x113 = rt_sp0 RT x94 → rt_credit RT x113 = rt_credit RT x94 → 0 < bil
→ bil mod 16 = 0 → bil + 104 < 140737488355328 → ART RT x113 x115 → wmono asegs m4 x209 → fs_agree x111 x130 → 0 < bil → In ( bil, 104) (rt_live RT x113) → bil
+ 104 <= rt_sp0 RT Σ - 8388608 → parked (bil + 104 <= 65536 ∨ 6692864 <= bil) → parked (bil + 104 <= 2147446784 ∨ 17594333495296 <= bil) → (∀ a : Z, PF a → a <
bil ∨ bil + 104 <= a) → parked (fr + 256 <= bil ∨ bil + 104 <= fr) → parked (bil + 104 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= bil) → wmono asegs
x115 x209 → (∀ q k : Z, In ( q, k) (( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ) → bil + 104 <= q ∨ q + k <= bil) → ART RT x113 m5
→ parked (bil + 104 <= pix ∨ pix + 64 <= bil) → ∀ x132 : rts RT, rt_live RT x132 = rt_live RT x113 → rt_frames RT x132 = rt_frames RT x113 → rt_sp0 RT x132 =
rt_sp0 RT x113 → rt_credit RT x132 = rt_credit RT x113 → ART RT x132 x133 → wmono asegs m5 x209 → ∀ x148 : bvmap 5 word, fs_agree x130 x148 → wmono asegs x133
x209 → rw_cells asegs m9 (usp + -248) [C8 (Z_to_bv 64 (fr + 192)); C8 (Z_to_bv 64 pixsc); C8 (Z_to_bv 64 10); C8 (Z_to_bv 64 (fr + 48)); C8 (Z_to_bv 64 (fr +
32)); C8 (Z_to_bv 64 11); C8 (Z_to_bv 64 (fr + 64)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 pix); CB 24 (skipn 24 (skipn 24 (firstn 72 (skipn 88 (firstn 184 (firstn
192 (firstn 200 (firstn 208 (firstn 216 (firstn 224 (firstn 232 (firstn 240 (firstn 248 (firstn 256 (firstn 264 (firstn 272 (firstn 280 (firstn 288 (firstn 296
(firstn 304 (skipn 24 junk))))))))))))))))))))); C8 (Z_to_bv 64 fr); CB 16 (skipn 80 (skipn 88 (firstn 184 (firstn 192 (firstn 200 (firstn 208 (firstn 216
(firstn 224 (firstn 232 (firstn 240 (firstn 248 (firstn 256 (firstn 264 (firstn 272 (firstn 280 (firstn 288 (firstn 296 (firstn 304 (skipn 24
junk))))))))))))))))))); C8 (reg_get F 18); C8 (reg_get F 9); C8 (reg_get F 8); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1;
C8 s0; C8 ra] → ART RT x132 m6 → ∀ x150 : rts RT, rt_live RT x150 = (nc, 40) :: rt_live RT x132 → rt_frames RT x150 = rt_frames RT x132 → rt_sp0 RT x150 =
rt_sp0 RT x132 → rt_credit RT x150 = rt_credit RT x132 → 0 < nc → nc mod 16 = 0 → nc + 40 < 140737488355328 → wmono asegs m6 x209 → ∀ x167 : bvmap 5 word,
fs_agree x148 x167 → (∀ e : Z * Z, In e [(pixsc, 64)] → In e (( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ)) → (∀ e :
Z * Z, In e (rt_live RT Σ) → In e (( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ)) → 0 < nc → In (nc, 40) (rt_live RT
x150) → nc + 40 <= rt_sp0 RT Σ - 8388608 → parked (nc + 40 <= 65536 ∨ 6692864 <= nc) → parked (nc + 40 <= 2147446784 ∨ 17594333495296 <= nc) → (∀ a : Z, PF a →
a < nc ∨ nc + 40 <= a) → (∀ q k : Z, In ( q, k) (( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ) → nc + 40 <= q ∨ q + k
<= nc) → parked (fr + 256 <= nc ∨ nc + 40 <= fr) → parked (nc + 40 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= nc) → wmono asegs x152 x209 → ∀ ncs :
list word, wmono asegs x152 x209 → length ncs = 10%nat → Forall (λ w : word, 0 <= bv_unsigned w <= 255) ncs → ART RT x150 m' → nc + 40 <= rt_sp0 RT Σ - 8388608
→ parked (nc + 40 <= 65536 ∨ 6692864 <= nc) → parked (nc + 40 <= 2147446784 ∨ 17594333495296 <= nc) → parked (fr + 256 <= nc ∨ nc + 40 <= fr) → parked (nc + 40
<= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= nc) → parked (nc + 40 <= bil ∨ bil + 104 <= nc) → wmono asegs m' x209 → let L2 := ( p_data vsc, 4 * (p_wpl
vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ in (∀ q k : Z, In (q, k) L2 → nc + 40 <= q ∨ q + k <= nc) → ART RT x150 m0 → ∀ x169 : rts RT, rt_live RT x169 =
( kidx, 1024) :: rt_live RT x150 → rt_frames RT x169 = rt_frames RT x150 → rt_sp0 RT x169 = rt_sp0 RT x150 → rt_credit RT x169 = rt_credit RT x150 → 0 < kidx →
kidx mod 16 = 0 → kidx + 1024 < 140737488355328 → wmono asegs m0 x209 → ∀ x186 : bvmap 5 word, fs_agree x167 x186 → 0 < kidx → In ( kidx, 1024) (rt_live RT
x169) → kidx + 1024 <= rt_sp0 RT Σ - 8388608 → parked (kidx + 1024 <= 65536 ∨ 6692864 <= kidx) → parked (kidx + 1024 <= 2147446784 ∨ 17594333495296 <= kidx) →
(∀ a : Z, PF a → a < kidx ∨ kidx + 1024 <= a) → (∀ q k : Z, In ( q, k) (( nc, 40) :: ( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) ::
rt_live RT Σ) → kidx + 1024 <= q ∨ q + k <= kidx) → (∀ q k : Z, In (q, k) L2 → kidx + 1024 <= q ∨ q + k <= kidx) → parked (fr + 256 <= kidx ∨ kidx + 1024 <= fr)
→ parked (kidx + 1024 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= kidx) → kidx + 1024 <= rt_sp0 RT Σ - 8388608 → parked (kidx + 1024 <= 65536 ∨ 6692864
<= kidx) → parked (kidx + 1024 <= 2147446784 ∨ 17594333495296 <= kidx) → parked (fr + 256 <= kidx ∨ kidx + 1024 <= fr) → parked (kidx + 1024 <= fr / 8 +
2147450880 ∨ fr / 8 + 32 + 2147450880 <= kidx) → wmono asegs x171 x209 → parked (kidx + 1024 <= nc ∨ nc + 40 <= kidx) → ∀ (Fk : bvmap 5 word) (ks : list word),
fs_agree x186 Fk → wmono asegs x171 x209 → kidx_ok 10 ks → ART RT x169 mk → parked (kidx + 1024 <= bil ∨ bil + 104 <= kidx) → length ks = 256%nat → Forall (λ w
: word, 0 <= bv_unsigned w <= 10 - 2) ks → wmono asegs mk x209 → ART RT x169 m7 → ∀ x188 : rts RT, rt_live RT x188 = ( kfr, 1024) :: rt_live RT x169 → rt_frames
RT x188 = rt_frames RT x169 → rt_sp0 RT x188 = rt_sp0 RT x169 → rt_credit RT x188 = rt_credit RT x169 → 0 < kfr → kfr mod 16 = 0 → kfr + 1024 < 140737488355328
→ wmono asegs m7 x209 → ∀ x205 : bvmap 5 word, fs_agree Fk x205 → 0 < kfr → In ( kfr, 1024) (rt_live RT x188) → kfr + 1024 <= rt_sp0 RT Σ - 8388608 → parked
(kfr + 1024 <= 65536 ∨ 6692864 <= kfr) → parked (kfr + 1024 <= 2147446784 ∨ 17594333495296 <= kfr) → (∀ a : Z, PF a → a < kfr ∨ kfr + 1024 <= a) → (∀ q k : Z,
In ( q, k) (( kidx, 1024) :: ( nc, 40) :: ( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ) → kfr + 1024 <= q ∨ q + k <=
kfr) → (∀ q k : Z, In (q, k) L2 → kfr + 1024 <= q ∨ q + k <= kfr) → parked (fr + 256 <= kfr ∨ kfr + 1024 <= fr) → parked (kfr + 1024 <= fr / 8 + 2147450880 ∨ fr
/ 8 + 32 + 2147450880 <= kfr) → kfr + 1024 <= rt_sp0 RT Σ - 8388608 → parked (kfr + 1024 <= 65536 ∨ 6692864 <= kfr) → parked (kfr + 1024 <= 2147446784 ∨
17594333495296 <= kfr) → parked (fr + 256 <= kfr ∨ kfr + 1024 <= fr) → parked (kfr + 1024 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= kfr) → wmono
asegs x190 x209 → parked (kfr + 1024 <= nc ∨ nc + 40 <= kfr) → ∀ Ff : bvmap 5 word, fs_agree x205 Ff → wmono asegs x190 x209 → rw_cells asegs m9 (usp + -336 +
72) [C8 (Z_to_bv 64 nc)] → ART RT x188 mf → 17594333495296 <= usp + -336 → parked (kfr + 1024 <= bil ∨ bil + 104 <= kfr) → parked (kfr + 1024 <= kidx ∨ kidx +
1024 <= kfr) → bil + 104 <= rt_sp0 RT Σ - 8388608 → wmono asegs mf x209 → ART RT x188 m8 → ∀ x207 : rts RT, rt_live RT x207 = (spat, 44) :: rt_live RT x188 →
rt_frames RT x207 = rt_frames RT x188 → rt_sp0 RT x207 = rt_sp0 RT x188 → rt_credit RT x207 = rt_credit RT x188 → 0 < spat → spat mod 16 = 0 → spat + 44 <
140737488355328 → ART RT x207 x209 → wmono asegs m8 x209 → ∀ x224 : bvmap 5 word, fs_agree Ff x224 → 0 < spat → In ( spat, 44) (rt_live RT x207) → spat + 44 <=
rt_sp0 RT Σ - 8388608 → parked (spat + 44 <= 65536 ∨ 6692864 <= spat) → parked (spat + 44 <= 2147446784 ∨ 17594333495296 <= spat) → (∀ a : Z, PF a → a < spat ∨
spat + 44 <= a) → (∀ q k : Z, In ( q, k) (( kfr, 1024) :: ( kidx, 1024) :: ( nc, 40) :: ( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64)
:: rt_live RT Σ) → spat + 44 <= q ∨ q + k <= spat) → (∀ q k : Z, In (q, k) L2 → spat + 44 <= q ∨ q + k <= spat) → parked (fr + 256 <= spat ∨ spat + 44 <= fr) →
parked (spat + 44 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= spat) → spat + 44 <= rt_sp0 RT Σ - 8388608 → parked (spat + 44 <= 65536 ∨ 6692864 <=
spat) → parked (spat + 44 <= 2147446784 ∨ 17594333495296 <= spat) → parked (fr + 256 <= spat ∨ spat + 44 <= fr) → parked (spat + 44 <= fr / 8 + 2147450880 ∨ fr
/ 8 + 32 + 2147450880 <= spat) → ∀ (PL := λ a : Z, aclient (rt_live RT x207) (rt_frames RT x207) (usp - 336) a ∧ outside [( spat, spat + 44)] a) (Se : rts RT)
(Fe : bvmap 5 word), fs_agree_but [8; 9; 18] F Fe → reg_get Fe 9 = Z_to_bv 64 4621819117588971520 → ART RT Se me → wmono asegs x209 x4 → agree_on PL x209 me →
rt_live RT Se = rt_live RT x207 → rt_frames RT Se = rt_frames RT x207 → rt_sp0 RT Se = rt_sp0 RT x207 → rt_credit RT Se = rt_credit RT x207 → (∀ xq : Z, usp -
336 <= xq < usp ∨ fr <= xq < fr + 248 ∨ fr / 8 + 2147450880 <= xq < fr / 8 + 2147450880 + 32 ∨ (∃ q k : Z, In ( q, k) (( kfr, 1024) :: ( kidx, 1024) :: ( nc,
40) :: ( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ) ∧ q <= xq < q + k) → PL xq) → In (spat, 44) (rt_live RT Se) →
wmono asegs me x4 → ART RT Se m10 → ∀ x2 : rts RT, rt_live RT x2 = (rng, 1024) :: rt_live RT Se → rt_frames RT x2 = rt_frames RT Se → rt_sp0 RT x2 = rt_sp0 RT
Se → rt_credit RT x2 = rt_credit RT Se → 0 < rng → rng mod 16 = 0 → rng + 1024 < 140737488355328 → ART RT x2 x4 → wmono asegs m10 x4 → ∀ x22 : bvmap 5 word,
fs_agree Fe x22 → 0 < rng → In ( rng, 1024) (rt_live RT x2) → rng + 1024 <= rt_sp0 RT Σ - 8388608 → parked (rng + 1024 <= 65536 ∨ 6692864 <= rng) → parked (rng
+ 1024 <= 2147446784 ∨ 17594333495296 <= rng) → (∀ a : Z, PF a → a < rng ∨ rng + 1024 <= a) → (∀ q k : Z, In ( q, k) (( spat, 44) :: ( kfr, 1024) :: ( kidx,
1024) :: ( nc, 40) :: ( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ) → rng + 1024 <= q ∨ q + k <= rng) → (∀ q k : Z,
In (q, k) L2 → rng + 1024 <= q ∨ q + k <= rng) → parked (fr + 256 <= rng ∨ rng + 1024 <= fr) → parked (rng + 1024 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 +
2147450880 <= rng) → rng + 1024 <= rt_sp0 RT Σ - 8388608 → parked (rng + 1024 <= 65536 ∨ 6692864 <= rng) → parked (rng + 1024 <= 2147446784 ∨ 17594333495296 <=
rng) → parked (fr + 256 <= rng ∨ rng + 1024 <= fr) → parked (rng + 1024 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= rng) → ∀ (PLR := λ a : Z, aclient
(rt_live RT x2) (rt_frames RT x2) (usp - 336) a ∧ outside [( rng, rng + 1024)] a) (Sr : rts RT) (Fq : bvmap 5 word), fs_agree_but [8; 9; 18] F Fq → reg_get Fq 9
= Z_to_bv 64 4621819117588971520 → ART RT Sr mr → wmono asegs x4 m9 → agree_on PLR x4 mr → wr_at asegs m9 rng 1024 → rw_cells asegs m9 (usp + -208) [C8 (Z_to_bv
64 11)] → rt_live RT Sr = rt_live RT x2 → rt_frames RT Sr = rt_frames RT x2 → rt_sp0 RT Sr = rt_sp0 RT x2 → rt_credit RT Sr = rt_credit RT x2 → (∀ xq : Z, usp -
336 <= xq < usp ∨ fr <= xq < fr + 248 ∨ fr / 8 + 2147450880 <= xq < fr / 8 + 2147450880 + 32 ∨ (∃ q k : Z, In ( q, k) (( kfr, 1024) :: ( kidx, 1024) :: ( nc,
40) :: ( bil, 104) :: ( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ) ∧ q <= xq < q + k) → PLR xq) → In ( rng, 1024) (rt_live RT Sr) →
wmono asegs mr m9 → rw_cells asegs m9 bil [C8 (Z_to_bv 64 pix); C8 (Z_to_bv 64 pixsc); C4 (Z_to_bv 64 1); C4 (reg_get x130 9); C4 (reg_get x130 8); CB 4 (repeat
(Z_to_bv 8 0) 4); C8 (Z_to_bv 64 spat); C8 (Z_to_bv 64 rng); C4 (sx32 (Z_to_bv 64 minval)); C4 (sx32 (Z_to_bv 64 maxval)); C4 (Z_to_bv 64 10); CB 4 (repeat
(Z_to_bv 8 0) 4); C8 (Z_to_bv 64 nc); C8 (Z_to_bv 64 kidx); C8 (Z_to_bv 64 kfr); C8 z64; C8 z64] → In (PIXA_CALLOC1 :: bv_unsigned ra :: ras) CLIENT_TRACES →
ART RT Sr m11 → ∀ (x24 : rts RT) (x26 x27 x28 : Z), let pxarr := x26 in let bxa := x27 in let bxarr := x28 in rt_live RT x24 = pixa_live pxa pxarr bxa bxarr 10
(rt_live RT Sr) → rt_frames RT x24 = rt_frames RT Sr → rt_sp0 RT x24 = rt_sp0 RT Sr → rt_credit RT x24 = rt_credit RT Sr → ART RT x24 x29 → mem_inv asegs m9 →
wmono asegs m11 m9 → LIBH m9 → io_ssp m9 → pixa_objn (rt_live RT x24) x29 pxa 10 pxarr bxa bxarr [] → ∀ (x32 x45 x46 x47 x48 : word) (x49 : bvmap 5 word),
fs_agree Fq x49 → pix8 (( p_data vsc, 4 * (p_wpl vsc * p_h vsc)) :: ( pixsc, 64) :: rt_live RT Σ) x29 pixsc vsc → pix_obj_rc (rt_live RT Σ) x29 pix v {| c_arr
:= 0; c_depth := 0; c_nalloc := 0; c_n := 0 |} 2 → u32arr asegs m9 nc ncs → u32arr asegs m9 kidx ks → agree_on PF m x29 → rw_cells asegs m9 fr [C8 (Z_to_bv 64
1102416563); C8 (Z_to_bv 64 142644); C8 (Z_to_bv 64 796688); CB 8 (firstn 8 (firstn 72 (firstn 104 (skipn 8 (skipn 8 (skipn 8 jf))))))] → rw_cells asegs m9 (fr
+ 36) [CB 12 (firstn 12 (skipn 4 (skipn 8 (firstn 72 (firstn 104 (skipn 8 (skipn 8 (skipn 8 jf))))))))] → rw_cells asegs m9 (fr + 52) [CB 12 (firstn 12 (skipn 4
(skipn 12 (skipn 4 (skipn 8 (firstn 72 (firstn 104 (skipn 8 (skipn 8 (skipn 8 jf))))))))))] → rw_cells asegs m9 (fr + 68) [CB 12 (firstn 12 (skipn 4 (skipn 12
(skipn 4 (skipn 12 (skipn 4 (skipn 8 (firstn 72 (firstn 104 (skipn 8 (skipn 8 (skipn 8 jf))))))))))))] → rw_cells asegs m9 (fr + 84) [CB 12 (firstn 12 (skipn 4
(skipn 12 (skipn 4 (skipn 12 (skipn 4 (skipn 12 (skipn 4 (skipn 8 (firstn 72 (firstn 104 (skipn 8 (skipn 8 (skipn 8 jf))))))))))))))] → acc asegs m9 (fr + 32) 4
→ acc asegs m9 (fr + 48) 4 → acc asegs m9 (fr + 64) 4 → acc asegs m9 (fr + 80) 4 → rw_cells asegs m9 pixsc [C4 (Z_to_bv 64 (p_w vsc)); C4 (Z_to_bv 64 (p_h
vsc)); C4 (Z_to_bv 64 (p_d vsc)); C4 (Z_to_bv 64 (p_spp vsc)); C4 (Z_to_bv 64 (p_wpl vsc)); C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 (p_xres vsc)); C4 (Z_to_bv 64
(p_yres vsc)); C4 (Z_to_bv 64 (p_inf vsc)); C4 (Z_to_bv 64 (p_spec vsc)); C8 z64; C8 (Z_to_bv 64 (p_cmap vsc)); C8 (Z_to_bv 64 (p_data vsc))] → rw_cells asegs
m9 pix [C4 (Z_to_bv 64 (p_w v)); C4 (Z_to_bv 64 (p_h v)); C4 (Z_to_bv 64 (p_d v)); C4 (Z_to_bv 64 (p_spp v)); C4 (Z_to_bv 64 (p_wpl v)); C4 (Z_to_bv 64 2); C4
(Z_to_bv 64 (p_xres v)); C4 (Z_to_bv 64 (p_yres v)); C4 (Z_to_bv 64 (p_inf v)); C4 (Z_to_bv 64 (p_spec v)); C8 z64; C8 (Z_to_bv 64 (p_cmap v)); C8 (Z_to_bv 64
(p_data v))] → parked (fr + 256 <= pixsc ∨ pixsc + 64 <= fr) → parked (pixsc + 64 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= pixsc) → parked (fr + 256
<= pixsc ∨ pixsc + 64 <= fr) → parked (pixsc + 64 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= pixsc) → parked (fr + 256 <= pix ∨ pix + 64 <= fr) →
parked (pix + 64 <= fr / 8 + 2147450880 ∨ fr / 8 + 32 + 2147450880 <= pix) → parked (fr + 256 <= pix ∨ pix + 64 <= fr) → parked (pix + 64 <= fr / 8 + 2147450880
∨ fr / 8 + 32 + 2147450880 <= pix) → ro_cells asegs m9 1039120 [C8 (Z_to_bv 64 1100920)] → ro_cells asegs m9 1100920 [C8 (Z_to_bv 64 2147450880)] → ro_cells
asegs m9 1039208 [C8 (Z_to_bv 64 1100928)] → ro_cells asegs m9 1100928 [C4 (Z_to_bv 64 1)] → acc asegs m9 rng 1024 → acc asegs m9 spat 44 → acc asegs m9 kfr
1024 → acc asegs m9 kidx 1024 → acc asegs m9 nc 40 → acc asegs m9 bil 104 → acc asegs m9 pixsc 64 → acc asegs m9 pix 64 → ro_cells asegs m9 1042312 [C8 (Z_to_bv
64 1057056)] → acc asegs m9 1057056 4 → munch [( usp - 592, usp); (fr + 32, fr + 84)] x29 m9 → wmono asegs x29 m9 → rw_cells asegs m9 (usp + -256) [C8 (Z_to_bv
64 pxa)] → rw_cells asegs m9 (fr + 48) [C4 (Z_to_bv 64 (p_w vsc))] → rw_cells asegs m9 (fr + 80) [C4 (Z_to_bv 64 (p_h vsc))] → ∀ u9 : word, rw_cells asegs m9
(fr + 32) [C4 (Z_to_bv 64 (p_w v))] → ∀ (u10 : word) (shb14 : byte) (u11 : word), rw_cells asegs m9 (fr + 64) [C4 (Z_to_bv 64 (p_h v))] → stk asegs m9 lo (usp +
-336) → ∀ fc3 : bv 32, frm0 fc3 → rw_cells asegs m9 (usp + -336) [CB 8 (firstn 8 (firstn 16 junk)); C8 (Z_to_bv 64 fr); C8 (Z_to_bv 64 (fr / 8 + 2147450880));
C8 (Z_to_bv 64 fr); C8 (Z_to_bv 64 bil); C8 (Z_to_bv 64 18446744073709551576); C8 (Z_to_bv 64 (p_data vsc + -10 + (p_wpl vsc * 4 + 1) * 11)); C8 (Z_to_bv 64
(p_h v)); C8 (Z_to_bv 64 (p_wpl vsc * 4))] → 0 < p_w v <= 20000 → 0 < p_h v <= 20000 → p_wpl vsc = (p_w vsc * 8 + 31) / 32 → 0 < p_wpl vsc <= 5006 → evt asegs
(λ ms' : machine_state, cps asegs (ASTA RT x24 PMc (eq ms')) QF) (MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x48) TEmpty) (Some z64) TEmpty)
(Some x32) (TNode TEmpty (Some (Z_to_bv 64 2147450880)) TEmpty)) (Some gp) (TNode (TNode TEmpty (Some (Z_to_bv 64 (-10))) TEmpty) (Some (Z_to_bv 64 (p_h v)))
(TNode TEmpty (Some (Z_to_bv 64 spat)) TEmpty))) (Some (Z_to_bv 64 798252)) (TNode (TNode (TNode TEmpty (Some u11) TEmpty) (Some (Z_to_bv 64 (usp + -336)))
(TNode TEmpty (Some (Z_to_bv 64 (p_w v))) TEmpty)) (Some u10) (TNode (TNode TEmpty (Some (Z_to_bv 64 21)) TEmpty) (Some (Z_to_bv 64 1)) (TNode TEmpty (Some x46)
TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 (bv_unsigned shb14))) TEmpty) (Some (Z_to_bv 64 usp)) (TNode TEmpty (Some z64) TEmpty))
(Some (Z_to_bv 64 TP_A)) (TNode (TNode TEmpty (Some (Z_to_bv 64 (p_h v))) TEmpty) (Some z64) (TNode TEmpty (Some x45) TEmpty))) (Some (Z_to_bv 64 (usp + -336)))
(TNode (TNode (TNode TEmpty (Some (Z_to_bv 64 rng)) TEmpty) (Some (Z_to_bv 64 18446744073709551576)) (TNode TEmpty (Some (Z_to_bv 64 10)) TEmpty)) (Some u9)
(TNode (TNode TEmpty (Some (Z_to_bv 64 (fr + 192))) TEmpty) (Some (Z_to_bv 64 2147450880)) (TNode TEmpty (Some x47) TEmpty))))) (bvmap_set 8 (Z_to_bv 64
18446744069414584320) x49) (Z_to_bv 64 798404) fc3 None m9 (seg_rom asegs)).

End BICUT2_336.
