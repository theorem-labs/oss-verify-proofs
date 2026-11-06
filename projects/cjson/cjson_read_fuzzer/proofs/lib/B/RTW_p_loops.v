(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art RT_kit RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
(* [comment removed for export] *)
Ltac if_lit := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota end.
(* [comment removed for export] *)
Ltac step_until p1 p2 :=
  lstep; try if_lit; try fl;
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    first [ constr_eq pc p1 | constr_eq pc p2 | step_until p1 p2 ] end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition fill_vals (alloc SZ : Z) (i : nat) : list word :=
  rev (map (fun j => Z_to_bv 64 ((alloc + Z.of_nat j * SZ) / 16)) (seq 0 i)).

Lemma fill_vals_S : forall alloc SZ i, fill_vals alloc SZ (S i) = Z_to_bv 64 ((alloc + Z.of_nat i * SZ) / 16) :: fill_vals alloc SZ i.
Proof. intros. unfold fill_vals. rewrite seq_S, map_app, rev_app_distr. reflexivity. Qed.
Lemma fill_vals_length : forall alloc SZ i, length (fill_vals alloc SZ i) = i.
Proof. intros. unfold fill_vals. rewrite length_rev, length_map, length_seq. reflexivity. Qed.

Lemma fill_loop : forall (k : nat) (i N D SZ alloc : Z) (pre : list word)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Q : machine_state -> Prop),
  Z.to_nat (N - i) = k -> 0 <= i < N -> N < 2^31 -> 0 < SZ -> 0 <= alloc -> alloc + N * SZ <= 2^40 ->
  AIMG_HI <= D -> length pre = k ->
  u32arr bsegs m D (pre ++ fill_vals alloc SZ (Z.to_nat i)) -> mem_inv bsegs m ->
  (forall m', u32arr bsegs m' D (fill_vals alloc SZ (Z.to_nat N)) -> munch [(D, D + 4 * N)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
     forall x14 x15, evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 N) (Z_to_bv 64 (D + 4 * N)) (Z_to_bv 64 (alloc + N * SZ)) a3 x14 x15 a6 a7
                                    s2 (Z_to_bv 64 N) s4 (Z_to_bv 64 SZ) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x372f4) fc None m' (seg_rom bsegs))) ->
  evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 i) (Z_to_bv 64 (D + 4 * N)) (Z_to_bv 64 (alloc + i * SZ)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 N) s4 (Z_to_bv 64 SZ) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x372d4) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros until Q; intros Hk Hi HN HS HA HAN HD Hpre ARR MI K; [lia|].
  pose proof (u32arr_bound bsegs m D _ ARR) as DB. rewrite length_app, fill_vals_length, Hpre in DB. unfold AIMG_HI in HD.
  pose proof (munch_refl [(D, D + 4 * N)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HiS : 0 <= i * SZ /\ i * SZ + SZ <= N * SZ) by nia.
  zstep. zstep. zstep. zstep. zstep. (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (D + 4 * (N - 1 - i))) ltac:(rewrite zb_lxor_ones by lia; rewrite Z.shiftl_mul_pow2 by lia; apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap;
     change (bv_modulus 64) with 18446744073709551616; Z.div_mod_to_equations; lia).
  pose proof (u32arr_store_ok bsegs _ D _ (N - 1 - i) (wa (D + 4 * (N - 1 - i))) ARR ltac:(rewrite length_app, fill_vals_length; lia) eq_refl) as SOK.
  zstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u32arr_write bsegs mm D _ (N - 1 - i) (Z_to_bv 64 (Z.shiftr (alloc + i * SZ) 4)) ARR ltac:(rewrite length_app, fill_vals_length; lia)) as ARR' end.
  store_done.
  zstep. (* [comment removed for export] *)
  assert (EV : upd (pre ++ fill_vals alloc SZ (Z.to_nat i)) (Z.to_nat (N - 1 - i)) (Z_to_bv 64 ((alloc + i * SZ) ≫ 4))
               = firstn k pre ++ fill_vals alloc SZ (Z.to_nat (i + 1))).
  { rewrite upd_firstn_skipn by (rewrite length_app, fill_vals_length; lia).
    rewrite firstn_app. replace (Z.to_nat (N - 1 - i) - length pre)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
    replace (Z.to_nat (N - 1 - i)) with k by lia.
    rewrite skipn_app. replace (S k - length pre)%nat with 0%nat by lia. rewrite skipn_all2 by lia. cbn [skipn app].
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. rewrite fill_vals_S.
    rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16. replace (Z.of_nat (Z.to_nat i)) with i by lia. reflexivity. }
  rewrite EV in ARR'. clear EV.
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    replace (alloc + i * SZ + SZ) with (alloc + (i + 1) * SZ) by lia.
    eapply (IH (i + 1) N D SZ alloc (firstn k pre)); [lia| lia| exact HN| exact HS| exact HA| exact HAN| unfold AIMG_HI; lia| rewrite firstn_length; lia| exact ARR'| exact MI|].
    intros m' ARR2 MU2 WM2 MI2 x14 x15. eapply K; [exact ARR2| eapply munch_trans; [exact MU| exact MU2]| eapply wmono_trans; [exact WM| exact WM2]| exact MI2].
  - (* [comment removed for export] *)
    assert (k = 0%nat) by lia. subst k. cbn [firstn app] in ARR'. replace (i + 1) with N in ARR' by lia.
    replace (alloc + i * SZ + SZ) with (alloc + N * SZ) by lia. replace (i + 1) with N by lia.
    eapply K; [exact ARR'| exact MU| exact WM| exact MI].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma upd_at_app : forall {X} (a : list X) (d : X) (b : list X) (v : X), upd (a ++ d :: b) (length a) v = a ++ v :: b.
Proof. intros X a. induction a as [|x a IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma firstn_len_snoc : forall {X} (a : list X) (x : X) (b : list X), firstn (S (length a)) (a ++ x :: b) = a ++ [x].
Proof. intros X a. induction a as [|y a IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma firstn_len_app : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros X a. induction a as [|y a IH]; intros; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Definition wl (zs : list Z) : list word := map (Z_to_bv 64) zs.
Lemma wl_length : forall zs, length (wl zs) = length zs. Proof. intros. apply length_map. Qed.

Lemma copy_loop_gfa : forall (k : nat) (i n S0 D0 : Z) (zs : list Z) (dpre : list word)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Q : machine_state -> Prop),
  Z.to_nat (n - i) = k -> 0 <= i < n -> n < 2^31 -> (4096 <= S0 /\ (S0 + 4 * n <= AIMG_LO \/ AIMG_HI <= S0)) -> (4096 <= D0 /\ (D0 + 4 * n <= AIMG_LO \/ AIMG_HI <= D0)) -> (S0 + 4 * n <= D0 \/ D0 + 4 * n <= S0) ->   (* [comment removed for export] *)
  length zs = Z.to_nat n -> Forall (fun z => 0 <= z < 2^31) zs -> length dpre = k ->
  u32arr bsegs m S0 (wl zs) -> u32arr bsegs m D0 (firstn (Z.to_nat i) (wl zs) ++ dpre) -> mem_inv bsegs m ->
  (forall m' x12, u32arr bsegs m' S0 (wl zs) -> u32arr bsegs m' D0 (wl zs) -> munch [(D0, D0 + 4 * n)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
     evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (D0 + 4 * n)) x12 (Z_to_bv 64 (D0 + 4 * n)) a4 a5 a6 a7
                      s2 s3 (Z_to_bv 64 (S0 + 4 * n)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36f98) fc None m' (seg_rom bsegs))) ->
  evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (D0 + 4 * n)) a2 (Z_to_bv 64 (D0 + 4 * i)) a4 a5 a6 a7
                   s2 s3 (Z_to_bv 64 (S0 + 4 * i)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36f84) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros until Q; intros Hk Hi Hn HS HD DISJ LS SMALL LD SRC DST MI K; [lia|].
  pose proof (u32arr_bound bsegs m S0 _ SRC) as SB. pose proof (u32arr_bound bsegs m D0 _ DST) as DB.
  rewrite length_app, firstn_length, wl_length, LS, LD in DB. rewrite wl_length, LS in SB. unfold AIMG_LO, AIMG_HI in HS, HD.
  assert (LW : length (wl zs) = Z.to_nat n) by (rewrite wl_length; exact LS).
  pose proof (munch_refl [(D0, D0 + 4 * n)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (nth_error zs (Z.to_nat i)) as [z|] eqn:NZ; [| apply nth_error_None in NZ; lia].
  pose proof (proj1 (Forall_forall _ _) SMALL z (nth_error_In _ _ NZ)) as Hz. cbv beta in Hz.
  assert (NW : nth_error (wl zs) (Z.to_nat i) = Some (Z_to_bv 64 z)) by (unfold wl; rewrite nth_error_map, NZ; reflexivity).
  pose proof (u32arr_read bsegs m S0 (wl zs) i (Z_to_bv 64 z) (wa (S0 + 4 * i)) SRC NW ltac:(lia) eq_refl) as RD.
  zstep. (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 z) ltac:(symmetry; apply sx32_small; lia).
  pose proof (u32arr_store_ok bsegs _ D0 _ i (wa (D0 + 4 * i)) DST ltac:(rewrite length_app, firstn_length, wl_length; lia) eq_refl) as SOK.
  zstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u32arr_write bsegs mm D0 _ i (Z_to_bv 64 z) DST ltac:(rewrite length_app, firstn_length, wl_length; lia)) as DST' end.
  store_done.
  (nelim (nth_error_split (wl zs) (Z.to_nat i) _ NW) 4%nat; intros pre0 post0 E0 L0).
  destruct dpre as [|d dpre']; [cbn in LD; lia|]. cbn in LD.
  assert (EV : upd (firstn (Z.to_nat i) (wl zs) ++ d :: dpre') (Z.to_nat i) (Z_to_bv 64 z) = firstn (Z.to_nat (i + 1)) (wl zs) ++ dpre').
  { rewrite E0 at 1. rewrite <- L0 at 1. rewrite firstn_len_app. rewrite <- L0 at 1. rewrite upd_at_app.
    replace (Z.to_nat (i + 1)) with (S (length pre0)) by lia. rewrite E0, firstn_len_snoc, <- app_assoc. reflexivity. }
  rewrite EV in DST'. clear EV.
  zstep. zstep. (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    replace (D0 + 4 * i + 4) with (D0 + 4 * (i + 1)) by lia. replace (S0 + 4 * i + 4) with (S0 + 4 * (i + 1)) by lia.
    eapply (IH (i + 1) n S0 D0 zs dpre'); [lia| lia| exact Hn| unfold AIMG_LO, AIMG_HI; lia| unfold AIMG_LO, AIMG_HI; lia| exact DISJ| exact LS| exact SMALL| lia| exact SRC| exact DST'| exact MI|].
    intros m' x12 SRC2 DST2 MU2 WM2 MI2. eapply K; [exact SRC2| exact DST2| eapply munch_trans; [exact MU| exact MU2]| eapply wmono_trans; [exact WM| exact WM2]| exact MI2].
  - (* [comment removed for export] *)
    assert (i + 1 = n) by lia. assert (k = 0%nat) by lia. subst k. destruct dpre'; [| cbn in LD; lia].
    rewrite app_nil_r in DST'. replace (Z.to_nat (i + 1)) with (length (wl zs)) in DST' by (rewrite wl_length; lia). rewrite firstn_all in DST'.
    replace (D0 + 4 * i + 4) with (D0 + 4 * n) by lia. replace (S0 + 4 * i + 4) with (S0 + 4 * n) by lia.
    eapply K; [exact SRC| exact DST'| exact MU| exact WM| exact MI].
Qed.


Lemma copy_loop_rta : forall (k : nat) (i n S0 D0 : Z) (zs : list Z) (dpre : list word)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Q : machine_state -> Prop),
  Z.to_nat (n - i) = k -> 0 <= i < n -> n < 2^31 -> (4096 <= S0 /\ (S0 + 4 * n <= AIMG_LO \/ AIMG_HI <= S0)) -> (4096 <= D0 /\ (D0 + 4 * n <= AIMG_LO \/ AIMG_HI <= D0)) -> (S0 + 4 * n <= D0 \/ D0 + 4 * n <= S0) ->   (* [comment removed for export] *)
  length zs = Z.to_nat n -> Forall (fun z => 0 <= z < 2^31) zs -> length dpre = k ->
  u32arr bsegs m S0 (wl zs) -> u32arr bsegs m D0 (firstn (Z.to_nat i) (wl zs) ++ dpre) -> mem_inv bsegs m ->
  (forall m' x11, u32arr bsegs m' S0 (wl zs) -> u32arr bsegs m' D0 (wl zs) -> munch [(D0, D0 + 4 * n)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
     evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S0 + 4 * n)) x11 a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 (Z_to_bv 64 (S0 + 4 * n)) s7 s8 (Z_to_bv 64 (D0 + 4 * n)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34c44) fc None m' (seg_rom bsegs))) ->
  evt bsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (S0 + 4 * n)) a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 (Z_to_bv 64 (S0 + 4 * i)) s7 s8 (Z_to_bv 64 (D0 + 4 * i)) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x34c30) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros until Q; intros Hk Hi Hn HS HD DISJ LS SMALL LD SRC DST MI K; [lia|].
  pose proof (u32arr_bound bsegs m S0 _ SRC) as SB. pose proof (u32arr_bound bsegs m D0 _ DST) as DB.
  rewrite length_app, firstn_length, wl_length, LS, LD in DB. rewrite wl_length, LS in SB. unfold AIMG_LO, AIMG_HI in HS, HD.
  assert (LW : length (wl zs) = Z.to_nat n) by (rewrite wl_length; exact LS).
  pose proof (munch_refl [(D0, D0 + 4 * n)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  destruct (nth_error zs (Z.to_nat i)) as [z|] eqn:NZ; [| apply nth_error_None in NZ; lia].
  pose proof (proj1 (Forall_forall _ _) SMALL z (nth_error_In _ _ NZ)) as Hz. cbv beta in Hz.
  assert (NW : nth_error (wl zs) (Z.to_nat i) = Some (Z_to_bv 64 z)) by (unfold wl; rewrite nth_error_map, NZ; reflexivity).
  pose proof (u32arr_read bsegs m S0 (wl zs) i (Z_to_bv 64 z) (wa (S0 + 4 * i)) SRC NW ltac:(lia) eq_refl) as RD.
  zstep. (* [comment removed for export] *)
  setreg 11 (Z_to_bv 64 z) ltac:(symmetry; apply sx32_small; lia).
  zstep. (* [comment removed for export] *)
  pose proof (u32arr_store_ok bsegs _ D0 _ i (wa (D0 + 4 * i)) DST ltac:(rewrite length_app, firstn_length, wl_length; lia) eq_refl) as SOK.
  zstep. (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
    pose proof (u32arr_write bsegs mm D0 _ i (Z_to_bv 64 z) DST ltac:(rewrite length_app, firstn_length, wl_length; lia)) as DST' end.
  store_done.
  (nelim (nth_error_split (wl zs) (Z.to_nat i) _ NW) 4%nat; intros pre0 post0 E0 L0).
  destruct dpre as [|d dpre']; [cbn in LD; lia|]. cbn in LD.
  assert (EV : upd (firstn (Z.to_nat i) (wl zs) ++ d :: dpre') (Z.to_nat i) (Z_to_bv 64 z) = firstn (Z.to_nat (i + 1)) (wl zs) ++ dpre').
  { rewrite E0 at 1. rewrite <- L0 at 1. rewrite firstn_len_app. rewrite <- L0 at 1. rewrite upd_at_app.
    replace (Z.to_nat (i + 1)) with (S (length pre0)) by lia. rewrite E0, firstn_len_snoc, <- app_assoc. reflexivity. }
  rewrite EV in DST'. clear EV.
  zstep. (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    replace (D0 + 4 * i + 4) with (D0 + 4 * (i + 1)) by lia. replace (S0 + 4 * i + 4) with (S0 + 4 * (i + 1)) by lia.
    eapply (IH (i + 1) n S0 D0 zs dpre'); [lia| lia| exact Hn| unfold AIMG_LO, AIMG_HI; lia| unfold AIMG_LO, AIMG_HI; lia| exact DISJ| exact LS| exact SMALL| lia| exact SRC| exact DST'| exact MI|].
    intros m' x11 SRC2 DST2 MU2 WM2 MI2. eapply K; [exact SRC2| exact DST2| eapply munch_trans; [exact MU| exact MU2]| eapply wmono_trans; [exact WM| exact WM2]| exact MI2].
  - (* [comment removed for export] *)
    assert (i + 1 = n) by lia. assert (k = 0%nat) by lia. subst k. destruct dpre'; [| cbn in LD; lia].
    rewrite app_nil_r in DST'. replace (Z.to_nat (i + 1)) with (length (wl zs)) in DST' by (rewrite wl_length; lia). rewrite firstn_all in DST'.
    replace (D0 + 4 * i + 4) with (D0 + 4 * n) by lia. replace (S0 + 4 * i + 4) with (S0 + 4 * n) by lia.
    eapply K; [exact SRC| exact DST'| exact MU| exact WM| exact MI].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac cases_1_31 i :=
  let HH := fresh in
  assert (HH : i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31) by lia;
  destruct HH as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].

(* [comment removed for export] *)
Ltac eval_cls :=
  repeat match goal with
  | |- context [cmaxcount ?c] => let v := eval vm_compute in (cmaxcount c) in change (cmaxcount c) with v
  | |- context [csize ?c] => let v := eval vm_compute in (csize c) in change (csize c) with v
  end.

(* [comment removed for export] *)
Lemma initc1_iter : forall (i q : Z) (cnt : word) (j2 j3 : list byte)
    (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Q : machine_state -> Prop),
  1 <= i <= 31 -> (4096 <= q /\ (q + 96 <= AIMG_LO \/ AIMG_HI <= q)) -> q + 96 <= 2^47 -> mem_inv bsegs m ->   (* [comment removed for export] *)
  rw_cells bsegs m q [C4 cnt; CB 4 j2; CB 8 j3] ->
  (forall m' (a1' a3' a5' : Z) (x28 x29 x30 : word),
     rw_cells bsegs m' q [C4 cnt; C4 (Z_to_bv 64 (cmaxcount i)); C8 (Z_to_bv 64 (csize i))] ->
     munch [(q + 4, q + 16)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
     a1' = q + 88 -> a3' = 32 * (i + 1) -> a5' = i + 1 - 16 ->
     evt bsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 a1') a2 (Z_to_bv 64 a3') a4 (Z_to_bv 64 a5')
                      (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
                  F (Z_to_bv 64 (if i =? 31 then 0x36e08 else 0x36db4)) fc None m' (seg_rom bsegs))) ->
  evt bsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (q + 8)) a2 (Z_to_bv 64 (32 * i)) a4 (Z_to_bv 64 (i - 16))
                   (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36db4) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros Hi HQ HQ2 MI CELL K. unfold AIMG_LO, AIMG_HI in HQ.
  pose proof (munch_refl [(q + 4, q + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  cases_1_31 i.
  all: step_until 224692 224776.
  all: eapply K; [eval_cls; exact CELL| exact MU| exact WM| exact MI| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma initc1_loop : forall (k : nat) (i P : Z) (cnt : Z -> word) (j2 j3 : Z -> list byte)
    (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Q : machine_state -> Prop),
  Z.to_nat (32 - i) = k -> 1 <= i <= 31 -> (4096 <= P /\ (P + 2656 <= AIMG_LO \/ AIMG_HI <= P)) -> P + 2656 <= 2^47 -> mem_inv bsegs m ->
  (forall c, i <= c <= 31 -> rw_cells bsegs m (P + 80 * c) [C4 (cnt c); CB 4 (j2 c); CB 8 (j3 c)]) ->
  (forall c, 1 <= c < i -> rw_cells bsegs m (P + 80 * c) [C4 (cnt c); C4 (Z_to_bv 64 (cmaxcount c)); C8 (Z_to_bv 64 (csize c))]) ->
  (forall m' (x11 x13 x15 x28 x29 x30 : word),
     (forall c, 1 <= c <= 31 -> rw_cells bsegs m' (P + 80 * c) [C4 (cnt c); C4 (Z_to_bv 64 (cmaxcount c)); C8 (Z_to_bv 64 (csize c))]) ->
     munch [(P + 80, P + 2560)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
     evt bsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 x11 a2 x13 a4 x15
                      (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 t6)
                  F (Z_to_bv 64 0x36e08) fc None m' (seg_rom bsegs))) ->
  evt bsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 17) (Z_to_bv 64 512) s0 s1 a0 (Z_to_bv 64 (P + 80 * i + 8)) a2 (Z_to_bv 64 (32 * i)) a4 (Z_to_bv 64 (i - 16))
                   (Z_to_bv 64 15) (Z_to_bv 64 1024) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x36db4) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros until Q; intros Hk Hi HP HP2 MI TODO DONE K; [lia|].
  eapply (initc1_iter i (P + 80 * i) (cnt i) (j2 i) (j3 i)); [lia| unfold AIMG_LO, AIMG_HI in *; lia| lia| exact MI| apply TODO; lia|].
  intros m' a1' a3' a5' x28 x29 x30 CELL' MU' WM' MI' E1 E3 E5. subst a1' a3' a5'.
  assert (TODO' : forall c, i + 1 <= c <= 31 -> rw_cells bsegs m' (P + 80 * c) [C4 (cnt c); CB 4 (j2 c); CB 8 (j3 c)]).
  { intros c Hc. eapply rw_cells_transport; [| exact MU'| exact WM'| cbn; lia]. apply TODO. lia. }
  assert (DONE' : forall c, 1 <= c < i + 1 -> rw_cells bsegs m' (P + 80 * c) [C4 (cnt c); C4 (Z_to_bv 64 (cmaxcount c)); C8 (Z_to_bv 64 (csize c))]).
  { intros c Hc. destruct (Z.eq_dec c i) as [->|NE]; [exact CELL'|]. eapply rw_cells_transport; [| exact MU'| exact WM'| cbn; lia]. apply DONE. lia. }
  assert (MUw : munch [(P + 80, P + 2560)] m m') by (eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn; intros; lia).
  destruct (Z.eqb_spec i 31) as [->|NE].
  - eapply K; [| exact MUw| exact WM'| exact MI']. intros c Hc. apply DONE'. lia.
  - replace (P + 80 * i + 88) with (P + 80 * (i + 1) + 8) by lia. replace (i + 1 - 16) with (i + 1 - 16) by lia.
    eapply (IH (i + 1) P cnt j2 j3); [lia| lia| exact HP| exact HP2| exact MI'| exact TODO'| exact DONE'|].
    intros m'' x11 x13 x15 y28 y29 y30 ALL MU'' WM'' MI''. eapply K; [exact ALL| eapply munch_trans; [exact MUw| exact MU'']| eapply wmono_trans; [exact WM'| exact WM'']| exact MI''].
Qed.

(* [comment removed for export] *)
Lemma initc2_iter : forall (i q : Z) (cnt : word) (j2 j3 : list byte)
    (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Q : machine_state -> Prop),
  1 <= i <= 31 -> (4096 <= q /\ (q + 96 <= AIMG_LO \/ AIMG_HI <= q)) -> q + 96 <= 2^47 -> mem_inv bsegs m ->   (* [comment removed for export] *)
  rw_cells bsegs m q [C4 cnt; CB 4 j2; CB 8 j3] ->
  (forall m' (a4' a5' a6' : Z) (x29 x30 x31 : word),
     rw_cells bsegs m' q [C4 cnt; C4 (Z_to_bv 64 (cmaxcount i)); C8 (Z_to_bv 64 (csize i))] ->
     munch [(q + 4, q + 16)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
     a4' = q + 88 -> a5' = 32 * (i + 1) -> a6' = i + 1 - 16 ->
     evt bsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 a4') (Z_to_bv 64 a5') (Z_to_bv 64 a6')
                      (Z_to_bv 64 15) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) x29 x30 x31)
                  F (Z_to_bv 64 (if i =? 31 then 0x34700 else 0x346ac)) fc None m' (seg_rom bsegs))) ->
  evt bsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (q + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16))
                   (Z_to_bv 64 15) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4 t5 t6) F (Z_to_bv 64 0x346ac) fc None m (seg_rom bsegs)).
Proof.
  intros until Q. intros Hi HQ HQ2 MI CELL K. unfold AIMG_LO, AIMG_HI in HQ.
  pose proof (munch_refl [(q + 4, q + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  cases_1_31 i.
  all: step_until 214700 214784.
  all: eapply K; [eval_cls; exact CELL| exact MU| exact WM| exact MI| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma initc2_loop : forall (k : nat) (i P : Z) (cnt : Z -> word) (j2 j3 : Z -> list byte)
    (ra sp gp tp s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (Q : machine_state -> Prop),
  Z.to_nat (32 - i) = k -> 1 <= i <= 31 -> (4096 <= P /\ (P + 2656 <= AIMG_LO \/ AIMG_HI <= P)) -> P + 2656 <= 2^47 -> mem_inv bsegs m ->
  (forall c, i <= c <= 31 -> rw_cells bsegs m (P + 80 * c) [C4 (cnt c); CB 4 (j2 c); CB 8 (j3 c)]) ->
  (forall c, 1 <= c < i -> rw_cells bsegs m (P + 80 * c) [C4 (cnt c); C4 (Z_to_bv 64 (cmaxcount c)); C8 (Z_to_bv 64 (csize c))]) ->
  (forall m' (x14 x15 x16 x29 x30 x31 : word),
     (forall c, 1 <= c <= 31 -> rw_cells bsegs m' (P + 80 * c) [C4 (cnt c); C4 (Z_to_bv 64 (cmaxcount c)); C8 (Z_to_bv 64 (csize c))]) ->
     munch [(P + 80, P + 2560)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
     evt bsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 x14 x15 x16
                      (Z_to_bv 64 15) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) x29 x30 x31)
                  F (Z_to_bv 64 0x34700) fc None m' (seg_rom bsegs))) ->
  evt bsegs Q (MS (mkR ra sp gp tp (Z_to_bv 64 1024) (Z_to_bv 64 16) (Z_to_bv 64 17) s0 s1 a0 a1 a2 a3 (Z_to_bv 64 (P + 80 * i + 8)) (Z_to_bv 64 (32 * i)) (Z_to_bv 64 (i - 16))
                   (Z_to_bv 64 15) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 512) t4 t5 t6) F (Z_to_bv 64 0x346ac) fc None m (seg_rom bsegs)).
Proof.
  induction k as [|k IH]; intros until Q; intros Hk Hi HP HP2 MI TODO DONE K; [lia|].
  eapply (initc2_iter i (P + 80 * i) (cnt i) (j2 i) (j3 i)); [lia| unfold AIMG_LO, AIMG_HI in *; lia| lia| exact MI| apply TODO; lia|].
  intros m' a1' a3' a5' x28 x29 x30 CELL' MU' WM' MI' E1 E3 E5. subst a1' a3' a5'.
  assert (TODO' : forall c, i + 1 <= c <= 31 -> rw_cells bsegs m' (P + 80 * c) [C4 (cnt c); CB 4 (j2 c); CB 8 (j3 c)]).
  { intros c Hc. eapply rw_cells_transport; [| exact MU'| exact WM'| cbn; lia]. apply TODO. lia. }
  assert (DONE' : forall c, 1 <= c < i + 1 -> rw_cells bsegs m' (P + 80 * c) [C4 (cnt c); C4 (Z_to_bv 64 (cmaxcount c)); C8 (Z_to_bv 64 (csize c))]).
  { intros c Hc. destruct (Z.eq_dec c i) as [->|NE]; [exact CELL'|]. eapply rw_cells_transport; [| exact MU'| exact WM'| cbn; lia]. apply DONE. lia. }
  assert (MUw : munch [(P + 80, P + 2560)] m m') by (eapply munch_weaken; [| exact MU']; unfold sub_fp; cbn; intros; lia).
  destruct (Z.eqb_spec i 31) as [->|NE].
  - eapply K; [| exact MUw| exact WM'| exact MI']. intros c Hc. apply DONE'. lia.
  - replace (P + 80 * i + 88) with (P + 80 * (i + 1) + 8) by lia. replace (i + 1 - 16) with (i + 1 - 16) by lia.
    eapply (IH (i + 1) P cnt j2 j3); [lia| lia| exact HP| exact HP2| exact MI'| exact TODO'| exact DONE'|].
    intros m'' x11 x13 x15 y28 y29 y30 ALL MU'' WM'' MI''. eapply K; [exact ALL| eapply munch_trans; [exact MUw| exact MU'']| eapply wmono_trans; [exact WM'| exact WM'']| exact MI''].
Qed.


End CeilWrap.
(* [comment removed for export] *)
Ltac setreg r v' tac := let v := reg_val r in replace v with v' by tac.
Ltac if_lit := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
  let v := eval vm_compute in c in replace c with v by (vm_compute; reflexivity); cbv iota end.
Ltac step_until p1 p2 :=
  lstep; try if_lit; try fl;
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
    first [ constr_eq pc p1 | constr_eq pc p2 | step_until p1 p2 ] end.
Ltac cases_1_31 i :=
  let HH := fresh in
  assert (HH : i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/ i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/ i = 24 \/ i = 25 \/ i = 26 \/ i = 27 \/ i = 28 \/ i = 29 \/ i = 30 \/ i = 31) by lia;
  destruct HH as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]]]]]]]]]]]]]]]]]].
Ltac eval_cls :=
  repeat match goal with
  | |- context [cmaxcount ?c] => let v := eval vm_compute in (cmaxcount c) in change (cmaxcount c) with v
  | |- context [csize ?c] => let v := eval vm_compute in (csize c) in change (csize c) with v
  end.
