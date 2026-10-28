(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit Atp_h_defs Atp_h_find.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Sj_hkitB Atp_h_defsA Atp_h_vkitA Atp_h_vkit2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition ff_frame (j0 : list byte) (s5 s4 s3 s2 s1 s0 ra : word) : list cell := [CB 8 j0; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma sep_at_lit : forall m : mem, mem_inv asegs m -> bytes_at asegs m ATPA_SEP SEPB.
Proof. intros m MI. apply ro_bytes_at; [exact MI| unfold ATPA_SEP; lia| unfold ATPA_SEP; cbn; lia|]. apply ro_bytes_b_sound. vm_compute. reflexivity. Qed.

Lemma f_sh_ok_cases : forall (b : byte) x, sh_ok b x -> b = Z_to_bv 8 0 \/ (exists k, b = Z_to_bv 8 k /\ 1 <= k <= 7 /\ x mod 8 < k).
Proof.
  intros b x [H|(H1 & H2)].
  - left. apply bv_eq. rewrite H. reflexivity.
  - right. exists (bv_unsigned b). split; [| lia]. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [reflexivity|]. apply bv_unsigned_in_range.
Qed.
Lemma f_sxb_small7 : forall k, 0 <= k < 128 -> sxb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof. intros k Hk. rewrite sxb_small by lia. destruct (Z.ltb_spec k 128); [reflexivity| lia]. Qed.

Definition fl_st (usp P L j : Z) (gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (rax : word) (m : mem)
    : machine_state :=
  MS (mkR rax (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 (P + j)) (Z_to_bv 64 (L - j)) a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 10) s3 (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4bcc) fc None m (seg_rom asegs).

Lemma fw1_short : forall (usp X P L lo : Z)
    (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 64 -> 0x6ca000 <= lo -> usp <= X -> X + 16 < 2^63 -> 0 < P -> 0 <= L < 4 -> P + L < 2^63 ->
  shb_consts m -> x_shz [(usp - 64, usp)] m X 16 ->
  rw_cells asegs m X [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 L)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a1' a2' a3' a4' : word),
      ms = MS (mkR ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 18446744073709551615) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ munch [(usp - 64, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo usp)
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 4) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_FIND m).
Proof.
  intros until m. intros ST LO GLO UX XH P0 LL PLH (G1 & G2) SHZ XC MI.
  unfold entry_st, ATPA_FIND, ATPA_SEP in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 7 zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' X ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (X + 8) ltac:(lia)) as RD1 end.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep. if_false. zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [exfalso; rewrite find_signed_small in K by lia; lia| clear K].
  zstep. zstep. zstep. zstep. zstep. zstep. rewrite sel_notfound by lia.
  zstep. do 7 zstep. release_frame FR ST usp. zstep. zstep.
  apply evt_done. do 5 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption| exact ST].
Qed.

Lemma fw1_long : forall (usp X P L lo : Z) (bsep : byte)
    (ra gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk asegs m lo usp -> lo <= usp - 64 -> 0x6ca000 <= lo -> usp <= X -> X + 16 < 2^63 -> 0 < P -> 4 <= L -> P + L < 2^63 ->
  shb_consts m -> x_shz [(usp - 64, usp)] m X 16 ->
  (forall m', munch [(usp - 64, usp)] m m' -> wmono asegs m m' -> bytes_at asegs m' (shad ATPA_SEP) [bsep]) -> sh_ok bsep ATPA_SEP ->
  rw_cells asegs m X [C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 L)] -> mem_inv asegs m ->
  evt asegs (fun ms => exists (m1 : mem) (a2' a4' : word) (j0 : list byte),
      ms = fl_st usp P L 0 gp tp t0 t1 t2 a2' (Z_to_bv 64 0) a4' a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc ra m1
      /\ munch [(usp - 64, usp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (usp + -64)
      /\ rw_cells asegs m1 (usp + -64) (ff_frame j0 s5 s4 s3 s2 s1 s0 ra))
    (entry_st ra (Z_to_bv 64 usp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 4) (Z_to_bv 64 0) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc ATPA_FIND m).
Proof.
  intros until m. intros ST LO GLO UX XH P0 LL PLH (G1 & G2) SHZ SHS SOK XC MI.
  unfold fl_st, ff_frame in *. unfold entry_st, ATPA_FIND, ATPA_SEP in *.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(usp - 64, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 64%nat ST.
  apply (rw_cells_split_CB asegs _ _ [] 64 _ [] [8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 7 zstep. zstep.
  zstep. zstep. zstep. clear G1 G2.
  lazymatch goal with MU' : munch _ m ?mm, WM' : wmono _ m ?mm |- _ =>
    pose proof (SHZ mm MU' WM' X ltac:(lia)) as RD0; pose proof (SHZ mm MU' WM' (X + 8) ltac:(lia)) as RD1;
    pose proof (bytes_at_read asegs mm _ _ 0 1 (SHS mm MU' WM') ltac:(lia) ltac:(cbn; lia)) as RDS end.
  rewrite Z.add_0_r in RDS. cbn [firstn skipn] in RDS. unfold shad, ATPA_SEP, SHB in RDS. change (145280 / 8 + 2147450880) with 2147469040 in RDS.
  zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. zstep. rewrite shr3_div. zstep. zstep. shz_norm. zstep. if_false.
  zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?unsigned_lit in K by lia; lia].
  zstep. if_false. zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [clear K| exfalso; rewrite find_signed_small in K by lia; lia].

  replace (L + - 0) with L by lia.
  lazymatch goal with |- evt _ ?QQ (MS _ _ _ _ _ ?mx _) =>
    assert (REST : forall xa0 xa2 xa4 : word,
      evt asegs QQ (MS (mkR ra (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 145280) xa0 (Z_to_bv 64 L) xa2 (Z_to_bv 64 0) xa4 a5 a6 a7
                           s2 s3 (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0xb4bc4) fc None mx (seg_rom asegs))) end.
  2:{ destruct (f_sh_ok_cases bsep 145280 SOK) as [-> | (k & -> & K17 & KM)].
      - zstep. zstep. zstep. rewrite sxb_z8. zstep. if_false. apply REST.
      - zstep. zstep. zstep. rewrite (f_sxb_small7 k) by lia. zstep. if_cases K2; zify_cond K2; [| exfalso; rewrite ?unsigned_lit in K2 by lia; lia].
        zstep. zstep. if_cases K3; zify_cond K3; [apply REST| exfalso; rewrite ?find_signed_small, ?unsigned_lit in K3 by lia; lia]. }
  intros xa0 xa2 xa4.
  zstep. zstep.
  apply evt_done. cbv beta. do 4 eexists. split; [cbv delta [mkR]; replace (P + 0) with P by lia; replace (L - 0) with L by lia; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST| exact FR].
Qed.

Lemma fw_head : forall (usp P L j : Z) (gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax : word) F fc (m : mem),
  0 < P -> P + L < 2^63 -> 0 <= j -> j + 4 <= L ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb4be0) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP)
                 (Z_to_bv 64 (P + j)) (Z_to_bv 64 10) (Z_to_bv 64 (L - j - 3)) a3 a4 a5 a6 a7
                 (Z_to_bv 64 10) s3 (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memchr m))
    (fl_st usp P L j gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc rax m).
Proof.
  intros until m. intros P0 PLH J0 J4. unfold fl_st, entry_st, e_memchr, ATPA_SEP.
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K]. zstep. zstep.
  apply evt_done. cbv delta [mkR]. replace (L - j + -4 + 1) with (L - j - 3) by lia. reflexivity.
Qed.

Lemma fw_tailN : forall (usp P L lo : Z) (j0 : list byte)
    (gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s5c s4c s3c s2c s1c s0c rac rax : word) F fc (m : mem),
  stk asegs m lo (usp + -64) -> lo <= usp - 64 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < P -> 0 <= L -> P + L < 2^63 ->
  rw_cells asegs m (usp + -64) (ff_frame j0 s5c s4c s3c s2c s1c s0c rac) -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 18446744073709551615) (Z_to_bv 64 L) a2
                                    (Z_to_bv 64 18446744073709551615) a4 a5 a6 a7 s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (ret_pc rac) fc None m (seg_rom asegs) /\ stk asegs m lo usp)
    (MS (mkR rax (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb4b74) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH P0 L0 PLH FR MI. unfold ff_frame in FR. pose proof ST as (STa & STb & _).
  zstep. zstep. zstep. zstep. zstep. zstep. rewrite sel_notfound by lia.
  zstep. do 7 zstep. release_frame FR ST usp. zstep. zstep.
  apply evt_done. split; [cbv delta [mkR]; replace (P + L + - P) with L by lia; reflexivity| exact ST].
Qed.

Lemma fw_tailF : forall (usp P L r lo : Z) (j0 : list byte)
    (gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s5c s4c s3c s2c s1c s0c rac rax : word) F fc (m : mem),
  stk asegs m lo (usp + -64) -> lo <= usp - 64 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < P -> 0 <= r < L -> P + L < 2^63 ->
  rw_cells asegs m (usp + -64) (ff_frame j0 s5c s4c s3c s2c s1c s0c rac) -> mem_inv asegs m ->
  evt asegs (fun ms => ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 r) (Z_to_bv 64 r) a2
                                    (Z_to_bv 64 r) a4 a5 a6 a7 s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                               F (ret_pc rac) fc None m (seg_rom asegs) /\ stk asegs m lo usp)
    (MS (mkR rax (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x (Z_to_bv 64 (P + r)) (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb4b78) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH P0 RL PLH FR MI. unfold ff_frame in FR. pose proof ST as (STa & STb & _).
  zstep. zstep. zstep. zstep. zstep. rewrite sel_found by lia.
  zstep. do 7 zstep. release_frame FR ST usp. zstep. zstep.
  apply evt_done. split; [cbv delta [mkR]; replace (P + r + - P) with r by lia; reflexivity| exact ST].
Qed.

Lemma fw_nf : forall (usp P L lo : Z) (j0 : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s5c s4c s3c s2c s1c s0c rac : word) F fc (m : mem),
  stk asegs m lo (usp + -64) -> lo <= usp - 64 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < P -> 0 <= L -> P + L < 2^63 ->
  rw_cells asegs m (usp + -64) (ff_frame j0 s5c s4c s3c s2c s1c s0c rac) -> mem_inv asegs m ->
  evt asegs (fun ms => exists a1' a3', ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 18446744073709551615) a1' a2 a3' a4 a5 a6 a7
                                           s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rac) fc None m (seg_rom asegs) /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb4be0) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 10) s3x (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4be0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH P0 L0 PLH FR MI. unfold ATPA_SEP.
  zstep. if_true.
  eapply evt_cut; [apply (fw_tailN usp P L lo j0); eassumption || lia|].
  cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity| exact ST'].
Qed.

Lemma fw_cand : forall (usp P L cand : Z) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < P -> P <= cand -> cand < P + L -> P + L < 2^63 ->
  evt asegs (eq (entry_st (Z_to_bv 64 0xb4bf4) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP)
                 (Z_to_bv 64 cand) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 4) a3 a4 a5 a6 a7
                 (Z_to_bv 64 10) (Z_to_bv 64 cand) (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_memcmp m))
    (MS (mkR (Z_to_bv 64 0xb4be0) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 cand) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 10) s3x (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4be0) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros P0 PC CL PLH. unfold entry_st, e_memcmp, ATPA_SEP.
  zstep. if_cases K; zify_cond K; [exfalso; rewrite ?unsigned_lit in K by lia; lia| clear K]. zstep. zstep. zstep. zstep.
  apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma fw_found : forall (usp P L r lo : Z) (j0 : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s5c s4c s3c s2c s1c s0c rac : word) F fc (m : mem),
  stk asegs m lo (usp + -64) -> lo <= usp - 64 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < P -> 0 <= r < L -> P + L < 2^63 ->
  rw_cells asegs m (usp + -64) (ff_frame j0 s5c s4c s3c s2c s1c s0c rac) -> mem_inv asegs m ->
  evt asegs (fun ms => exists a1' a3', ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 r) a1' a2 a3' a4 a5 a6 a7
                                           s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rac) fc None m (seg_rom asegs) /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb4bf4) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 10) (Z_to_bv 64 (P + r)) (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4bf4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH P0 RL PLH FR MI. unfold ATPA_SEP.
  zstep. if_true.
  eapply evt_cut; [apply (fw_tailF usp P L r lo j0); eassumption || lia|].
  cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity| exact ST'].
Qed.

Lemma fw_next : forall (usp P L r : Z) (rw : word) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 < P -> 0 <= r -> r + 1 + 4 <= L -> P + L < 2^63 -> rw <> Z_to_bv 64 0 ->
  evt asegs (eq (fl_st usp P L (r + 1) gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (P + r)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc (Z_to_bv 64 0xb4bf4) m))
    (MS (mkR (Z_to_bv 64 0xb4bf4) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP) rw a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 10) (Z_to_bv 64 (P + r)) (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4bf4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros P0 R0 RL PLH RW. unfold fl_st, ATPA_SEP.
  zstep. if_cases K; zify_cond K; [exfalso; apply RW; apply bv_eq; rewrite K; reflexivity| clear K].
  zstep. zstep. zstep. if_cases K; zify_cond K; [clear K| exfalso; rewrite ?find_signed_small, ?unsigned_lit in K by lia; lia].
  apply evt_done. cbv delta [mkR]. replace (P + L + - (P + r + 1)) with (L - (r + 1)) by lia. replace (P + r + 1) with (P + (r + 1)) by lia. reflexivity.
Qed.

Lemma fw_last : forall (usp P L r lo : Z) (rw : word) (j0 : list byte)
    (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s5c s4c s3c s2c s1c s0c rac : word) F fc (m : mem),
  stk asegs m lo (usp + -64) -> lo <= usp - 64 -> 0x6ca000 <= lo -> usp < 2^63 -> 0 < P -> 0 <= r < L -> L < r + 1 + 4 -> P + L < 2^63 -> rw <> Z_to_bv 64 0 ->
  rw_cells asegs m (usp + -64) (ff_frame j0 s5c s4c s3c s2c s1c s0c rac) -> mem_inv asegs m ->
  evt asegs (fun ms => exists a1' a3', ms = MS (mkR rac (Z_to_bv 64 usp) gp tp t0 t1 t2 s0c s1c (Z_to_bv 64 18446744073709551615) a1' a2 a3' a4 a5 a6 a7
                                           s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc rac) fc None m (seg_rom asegs) /\ stk asegs m lo usp)
    (MS (mkR (Z_to_bv 64 0xb4bf4) (Z_to_bv 64 (usp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP) rw a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 10) (Z_to_bv 64 (P + r)) (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb4bf4) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros ST LO GLO SPH P0 RL LR PLH RW FR MI. unfold ATPA_SEP.
  zstep. if_cases K; zify_cond K; [exfalso; apply RW; apply bv_eq; rewrite K; reflexivity| clear K].
  zstep. zstep. zstep. if_cases K; zify_cond K; [exfalso; rewrite ?find_signed_small, ?unsigned_lit in K by lia; lia| clear K]. zstep.
  eapply evt_cut; [apply (fw_tailN usp P L lo j0); eassumption || lia|].
  cbv beta. intros ms' [-> ST']. apply evt_done. do 2 eexists. split; [reflexivity| exact ST'].
Qed.

Lemma bytes_at_skipn_a : forall (m : mem) A (bs : list byte) k,
  bytes_at asegs m A bs -> (k <= length bs)%nat -> bytes_at asegs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros m A bs k H Hk. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia. exact H.
Qed.
Lemma bytes_at_firstn_a : forall (m : mem) A (bs : list byte) k, bytes_at asegs m A bs -> bytes_at asegs m A (firstn k bs).
Proof. intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [H _]. exact H. Qed.
Lemma mchk_le : forall c n buf, 0 <= n -> memchr_chk c n buf <= n.
Proof.
  intros c n buf Hn. unfold memchr_chk. destruct (find_byte c (firstn (Z.to_nat n) buf)) as [ix|] eqn:FB; [| lia].
  pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn in Hl. lia.
Qed.
Lemma mchk_nonneg : forall c n buf, 0 <= n -> 0 <= memchr_chk c n buf.
Proof. intros c n buf Hn. unfold memchr_chk. destruct (find_byte c (firstn (Z.to_nat n) buf)); lia. Qed.
Lemma to_bytes_length_a : forall l, length (to_bytes l) = length l.
Proof. intros l. unfold to_bytes. apply length_map. Qed.

Section Find.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis MCHR : memchr_icontract RT.

Local Ltac ul := unfold ATPA_FIND_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma find_loop : forall (k : nat) (Σ : rts RT) PMc (T : TSet) (usp lo P pk nk : Z) (l : list Z) (m0 : mem) (j0 : list byte)
    (gp tp s6 s7 s8 s9 s10 s11 s5c s4c s3c s2c s1c s0c rac : word),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 0x6a7e68 ->
  Forall (fun c => 0 <= c < 256) l -> 4 <= zlength l < 2^26 -> 0 < P ->
  In (pk, nk) (rt_live RT Σ) -> pk <= P -> P + zlength l <= pk + nk ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> lo + ATPA_FIND_STACK <= usp -> usp + 16 <= USTACK_TOP -> usp mod 16 = 0 -> ART RT Σ m0 ->
  (forall c', ASTA RT Σ PMc (fun ms => exists m', ret_st rac (Z_to_bv 64 usp) gp tp s0c s1c s2c s3c s4c s5c s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (find_resA l)) m' ms
                  /\ rt_after_f RT Σ usp lo m0 m' /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) usp [] m0 m') c' /\ cfrm0 c' -> realizes asegs c' T) ->
  forall (j : Z) (t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 rax : word) F fc (m1 : mem) (c1 : config),
  zlength l - j <= Z.of_nat k -> 0 <= j -> j + 4 <= zlength l -> (forall i, (i < Z.to_nat j)%nat -> ~ sep_at l i) ->
  ART RT Σ m1 -> mem_inv asegs m1 -> stk asegs m1 lo (usp + -64) ->
  rw_cells asegs m1 (usp + -64) (ff_frame j0 s5c s4c s3c s2c s1c s0c rac) -> bytes_at asegs m1 P (to_bytes l) ->
  (forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m1 a = m0 a) -> frm0 fc ->
  ASTA RT Σ PMc (eq (fl_st usp P (zlength l) j gp tp t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc rax m1)) c1 ->
  realizes asegs c1 T.
Proof using AF RTF MCHR.
  induction k as [|k IH]; intros Σ PMc T usp lo P pk nk l m0 j0 gp tp s6 s7 s8 s9 s10 s11 s5c s4c s3c s2c s1c s0c rac
    FDO MST ETP LBYT LL P0 INK PK1 PK2 LOW LOR SPT SPA ARTm0 Hk j t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 t3 t4 t5 t6 rax F fc m1 c1
    HK J0 J4 INV ART1 MI1 ST1 FR1 PB1 PRES1 FRM Hc1.
  { exfalso. unfold zlength in *. lia. }
  subst tp.
  pose proof (af_sp0_range RT AF Σ m1 ART1) as SP0R. pose proof (af_sp0_win RT AF Σ m1 ART1) as SP0W.
  pose proof (af_live_range RT AF Σ m1 pk nk ART1 INK) as (K0 & K1 & _).
  set (L := zlength l) in *. unfold zlength in L.
  assert (LBL : length (to_bytes l) = length l) by apply to_bytes_length_a.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -64)) = usp + -64) by (apply unsigned_lit; ul).
  assert (COK : forall m, stk asegs m lo (usp + -64) -> call_ok RT Σ m (Z_to_bv 64 (usp + -64)) lo).
  { intros mm STm. unfold call_ok. rewrite EU2. split; [exact STm|]. split; [ul|]. split; [ul|]. split; [ul|].
    replace (usp + -64) with (usp + (-4) * 16) by lia. rewrite Z.mod_add by lia. exact SPA. }

  pose proof (fw_head usp P L j gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 a2 a3 a4 a5 a6 a7 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rax F fc m1 P0 ltac:(ul) J0 J4) as W1.
  lazymatch type of W1 with evt asegs _ ?X0 => assert (W1' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W1) end. clear W1.
  apply (cps_realizes asegs _ _ _ c1 (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc1). clear W1'. intros c2 Hc2.

  set (buf := skipn (Z.to_nat j) (to_bytes l)).
  assert (PBJ : bytes_at asegs m1 (P + j) buf).
  { subst buf. replace (P + j) with (P + Z.of_nat (Z.to_nat j)) by lia. apply bytes_at_skipn_a; [exact PB1| lia]. }
  assert (LBUF : Z.of_nat (length buf) = L - j) by (subst buf; rewrite length_skipn; lia).
  pose proof (mchk_le 10 (L - j - 3) buf ltac:(lia)) as CH1. pose proof (mchk_nonneg 10 (L - j - 3) buf ltac:(lia)) as CH0.
  pose proof (af_acc_live RT AF Σ m1 pk nk ART1 INK) as [_ ACK].
  apply (MCHR Σ PMc (Z_to_bv 64 0xb4be0) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP)
           (Z_to_bv 64 (P + j)) (Z_to_bv 64 10) (Z_to_bv 64 (L - j - 3)) a3 a4 a5 a6 a7 (Z_to_bv 64 10) s3 (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           F fc m1 (P + j) 10 (L - j - 3) buf lo FDO MST eq_refl eq_refl eq_refl ltac:(ul) ltac:(lia) ltac:(lia) PBJ (memchr_ok_all (P + j) 10 (L - j - 3) buf ltac:(lia)) ltac:(left; ul));
    [| exact ART1| exact MI1| exact (COK m1 ST1)| exact Hc2|].
  { unfold checked_src. rewrite EU2. split; [| left; ul]. intros POS. split; [exact (acc_sub asegs m1 pk nk (P + j) (memchr_chk 10 (L - j - 3) buf) ACK ltac:(lia) ltac:(lia))|].
    left. exists pk, nk. split; [exact INK| lia]. }
  intros c3 Hc3.
  destruct (ASTA_unpack RT Σ _ _ c3 Hc3) as (ms3 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & _) & Hc3'). clear Hc3.
  destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & ->).
  rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb4be0) in Hc3' by lia.
  assert (AG12 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -64) (bv_unsigned a) -> m2 a = m1 a) by (intros a Ha; apply PRES2; [exact Ha| lia]).
  assert (FR2 : rw_cells asegs m2 (usp + -64) (ff_frame j0 s5c s4c s3c s2c s1c s0c rac)).
  { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). intros a Ha. apply AG12. left. unfold ff_frame in Ha. cbn [cells_size csize Nat.add] in Ha. ul. }
  assert (PB2 : bytes_at asegs m2 P (to_bytes l)).
  { apply (bytes_at_agree asegs m1 m2 _ _ PB1). intros a Ha. apply AG12. right; right; left. exists pk, nk. split; [exact INK| rewrite LBL in Ha; lia]. }
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m2 a = m0 a).
  { intros a Ha. rewrite (AG12 a); [exact (PRES1 a Ha)|]. apply (aclient_mono _ _ _ _ _ _ _ Ha); auto. lia. }
  unfold memchr_res in Hc3'.
  destruct (find_byte 10 (firstn (Z.to_nat (L - j - 3)) buf)) as [ix|] eqn:FB.
  -
    pose proof (find_byte_Some _ _ _ FB) as (Hl & (b & Hb & Hb10) & Hmin). rewrite length_firstn in Hl.
    pose proof (no_sep_before l (Z.to_nat j) (Z.to_nat (L - j - 3)) ix) as NOS. fold buf in NOS.
    specialize (NOS ltac:(intros t b0 Ht Hn; exact (Hmin t b0 Ht Hn)) ltac:(lia)).
    assert (IXR : 0 <= Z.of_nat ix /\ j + Z.of_nat ix + 4 <= L) by lia.

    pose proof (fw_cand usp P L (P + j + Z.of_nat ix) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s3 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F2 fc m2
                  P0 ltac:(lia) ltac:(lia) ltac:(ul)) as W2.
    lazymatch type of W2 with evt asegs _ ?X0 => assert (W2' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W2) end. clear W2.
    apply (cps_realizes asegs _ _ _ c3 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc3'). clear W2'. intros c4 Hc4.
    set (bp := firstn 4 (skipn (Z.to_nat (j + Z.of_nat ix)) (to_bytes l))).
    assert (LEN4 : length bp = 4%nat) by (subst bp; rewrite length_firstn, length_skipn; lia).
    assert (BP : bytes_at asegs m2 (P + j + Z.of_nat ix) bp).
    { subst bp. apply bytes_at_firstn_a. replace (P + j + Z.of_nat ix) with (P + Z.of_nat (Z.to_nat (j + Z.of_nat ix))) by lia. apply bytes_at_skipn_a; [exact PB2| lia]. }
    change (Z_to_bv 64 4) with (Z_to_bv 64 (Z.of_nat 4)) in Hc4. rewrite <- LEN4 in Hc4 at 2.
    pose proof (acc_lit RT AF Σ m2 ATPA_SEP 5 ART2 ltac:(unfold ACC_LITS, ATPA_SEP; cbn; tauto)) as ACS.
    pose proof (af_acc_live RT AF Σ m2 pk nk ART2 INK) as [_ ACK2].
    apply ((rf_memcmp RT RTF) Σ PMc (Z_to_bv 64 0xb4bf4) (Z_to_bv 64 (usp + -64)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 4) (Z_to_bv 64 ATPA_SEP)
             (Z_to_bv 64 (P + j + Z.of_nat ix)) (Z_to_bv 64 ATPA_SEP) (Z_to_bv 64 (Z.of_nat (length bp))) b3 b4 b5 b6 b7
             (Z_to_bv 64 10) (Z_to_bv 64 (P + j + Z.of_nat ix)) (Z_to_bv 64 P) (Z_to_bv 64 (P + L)) s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
             F2 fc m2 (P + j + Z.of_nat ix) ATPA_SEP bp SEPB lo FDO MST eq_refl eq_refl eq_refl ltac:(rewrite LEN4; reflexivity) ltac:(ul) ltac:(unfold ATPA_SEP; lia)
             ltac:(rewrite LEN4; lia) ltac:(rewrite LEN4; cbn; lia) BP (sep_at_lit m2 MI2));
      [| | exact ART2| exact MI2| exact (COK m2 ST2)| split; [exact Hc4| apply (cfrm0_of_asta RT Σ PMc (eq _) c4 Hc4); intros ms0 <-; exact FRM] |].
    { unfold checked_src. rewrite EU2, LEN4. change (Z.of_nat 4) with 4. split; [| left; ul]. intros _.
      split; [exact (acc_sub asegs m2 pk nk (P + j + Z.of_nat ix) 4 ACK2 ltac:(lia) ltac:(lia))|]. left. exists pk, nk. split; [exact INK| lia]. }
    { unfold checked_src. rewrite EU2, LEN4. change (Z.of_nat 4) with 4. split; [| left; unfold ATPA_SEP; ul]. intros _.
      split; [exact (acc_sub asegs m2 ATPA_SEP 5 ATPA_SEP 4 ACS ltac:(lia) ltac:(lia))|]. right; right; right. unfold ATPA_SEP, SEGTOP_A. lia. }
    intros c5 ((r & RIFF & Hc5) & FC5).
    destruct (ASTA_unpack_f RT Σ _ _ c5 Hc5 FC5) as (ms5 & (m3 & RS3 & (ART3 & MI3 & WM3 & ST3) & PRES3 & _) & FRM3 & Hc5'). clear Hc5.
    destruct RS3 as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & ->).
    cbn [ms_fcsr] in FRM3. rewrite EU2 in ST3, PRES3. rewrite (ret_pc_even 0xb4bf4) in Hc5' by lia.
    assert (AG23 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -64) (bv_unsigned a) -> m3 a = m2 a) by (intros a Ha; apply PRES3; [exact Ha| lia]).
    assert (FR3 : rw_cells asegs m3 (usp + -64) (ff_frame j0 s5c s4c s3c s2c s1c s0c rac)).
    { apply (rw_cells_agree_nw asegs m2 m3 _ _ FR2). intros a Ha. apply AG23. left. unfold ff_frame in Ha. cbn [cells_size csize Nat.add] in Ha. ul. }
    assert (PB3 : bytes_at asegs m3 P (to_bytes l)).
    { apply (bytes_at_agree asegs m2 m3 _ _ PB2). intros a Ha. apply AG23. right; right; left. exists pk, nk. split; [exact INK| rewrite LBL in Ha; lia]. }
    assert (PRES3' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m3 a = m0 a).
    { intros a Ha. rewrite (AG23 a); [exact (PRES2' a Ha)|]. apply (aclient_mono _ _ _ _ _ _ _ Ha); auto. lia. }
    pose proof (sep_at_of_bytes l (Z.to_nat (j + Z.of_nat ix)) LBYT ltac:(lia)) as SIFF. fold bp in SIFF.
    destruct (bv_eq_dec _ r (Z_to_bv 64 0)) as [ER|NR].
    +
      subst r. pose proof (proj1 SIFF (proj1 RIFF eq_refl)) as SA.
      assert (HS : find_sep l = Some (Z.to_nat (j + Z.of_nat ix))).
      { apply find_sep_Some_of; [exact SA|]. intros i' Hi'. destruct (Nat.lt_ge_cases i' (Z.to_nat j)) as [X0|X0]; [exact (INV i' X0)|]. apply NOS. lia. }
      replace (P + j + Z.of_nat ix) with (P + (j + Z.of_nat ix)) in Hc5' by lia.
      pose proof (fw_found usp P L (j + Z.of_nat ix) lo j0 gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
                    s5c s4c s3c s2c s1c s0c rac F3 fc3 m3 ST3 ltac:(ul) ltac:(ul) ltac:(ul) P0 ltac:(lia) ltac:(ul) FR3 MI3) as W3.
      lazymatch type of W3 with evt asegs _ ?X0 => assert (W3' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W3) end. clear W3.
      apply (cps_realizes asegs _ _ _ c5 (asta_evt_c RT AF Σ PMc _ _ MST W3') Hc5'). clear W3'. intros c6 Hc6.
      apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c6 Hc6); intros ms0 (a1' & a3' & E & _); rewrite E; exact FRM3].
      eapply ASTA_conseq; [exact Hc6|]. intros ms (a1' & a3' & -> & ST6). exists m3.
      split; [unfold ret_st; replace (find_resA l) with (j + Z.of_nat ix) by (unfold find_resA; rewrite HS; lia); do 16 eexists; reflexivity|].
      split; [split; [exact ART3| split; [exact MI3| exact ST6]]|].
      intros a Ha _. exact (PRES3' a Ha).
    +
      assert (NE : ~ sep_at l (Z.to_nat (j + Z.of_nat ix))).
      { intros SA. apply NR. apply (proj2 RIFF). apply (proj2 SIFF). exact SA. }
      assert (INV' : forall i, (i < Z.to_nat (j + Z.of_nat ix + 1))%nat -> ~ sep_at l i).
      { intros i Hi. destruct (Nat.lt_ge_cases i (Z.to_nat j)) as [X0|X0]; [exact (INV i X0)|].
        destruct (Nat.eq_dec i (Z.to_nat (j + Z.of_nat ix))) as [->|NEQ]; [exact NE|]. apply NOS. lia. }
      destruct (Z_le_gt_dec (j + Z.of_nat ix + 1 + 4) L) as [MORE|LAST].
      *
        pose proof (fw_next usp P L (j + Z.of_nat ix) r gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6 F3 fc3 m3
                      P0 ltac:(lia) MORE ltac:(ul) NR) as W3.
        replace (P + j + Z.of_nat ix) with (P + (j + Z.of_nat ix)) in Hc5' by lia.
        lazymatch type of W3 with evt asegs _ ?X0 => assert (W3' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W3) end. clear W3.
        apply (cps_realizes asegs _ _ _ c5 (asta_evt_c RT AF Σ PMc _ _ MST W3') Hc5'). clear W3'. intros c6 Hc6.
        apply (IH Σ PMc T usp lo P pk nk l m0 j0 gp (Z_to_bv 64 0x6a7e68) s6 s7 s8 s9 s10 s11 s5c s4c s3c s2c s1c s0c rac FDO MST eq_refl LBYT LL P0 INK PK1 PK2 LOW LOR SPT SPA ARTm0 Hk
                 (j + Z.of_nat ix + 1) v0 v1 v2 d2 d3 d4 d5 d6 d7 (Z_to_bv 64 (P + (j + Z.of_nat ix))) v3 v4 v5 v6 (Z_to_bv 64 0xb4bf4) F3 fc3 m3 c6);
          [subst L; unfold zlength in *; lia| lia| subst L; unfold zlength in *; lia| exact INV'| exact ART3| exact MI3| exact ST3| exact FR3| exact PB3| exact PRES3'| exact FRM3| subst L; unfold zlength in *; exact Hc6].
      *
        assert (HN : find_sep l = None) by (apply (find_sep_None_of l (Z.to_nat (j + Z.of_nat ix + 1)) INV'); lia).
        pose proof (fw_last usp P L (j + Z.of_nat ix) lo r j0 gp (Z_to_bv 64 0x6a7e68) v0 v1 v2 d1 d2 d3 d4 d5 d6 d7 s6 s7 s8 s9 s10 s11 v3 v4 v5 v6
                      s5c s4c s3c s2c s1c s0c rac F3 fc3 m3 ST3 ltac:(ul) ltac:(ul) ltac:(ul) P0 ltac:(lia) ltac:(lia) ltac:(ul) NR FR3 MI3) as W3.
        replace (P + j + Z.of_nat ix) with (P + (j + Z.of_nat ix)) in Hc5' by lia.
        lazymatch type of W3 with evt asegs _ ?X0 => assert (W3' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W3) end. clear W3.
        apply (cps_realizes asegs _ _ _ c5 (asta_evt_c RT AF Σ PMc _ _ MST W3') Hc5'). clear W3'. intros c6 Hc6.
        apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c6 Hc6); intros ms0 (a1' & a3' & E & _); rewrite E; exact FRM3].
        eapply ASTA_conseq; [exact Hc6|]. intros ms (a1' & a3' & -> & ST6). exists m3.
        split; [unfold ret_st; replace (Z_to_bv 64 (find_resA l)) with (Z_to_bv 64 18446744073709551615) by (unfold find_resA; rewrite HN; apply bv_eq; reflexivity); do 16 eexists; reflexivity|].
        split; [split; [exact ART3| split; [exact MI3| exact ST6]]|].
        intros a Ha _. exact (PRES3' a Ha).
  -
    assert (HN : find_sep l = None).
    { apply (find_sep_None_of l (Z.to_nat (L - 3))); [| lia]. intros i Hi.
      destruct (Nat.lt_ge_cases i (Z.to_nat j)) as [X0|X0]; [exact (INV i X0)|].
      pose proof (find_byte_None _ _ FB) as Hmin.
      apply (no_sep_before l (Z.to_nat j) (Z.to_nat (L - j - 3)) (Z.to_nat (L - j - 3))); [intros t b0 Ht Hn; exact (Hmin t b0 Hn)| lia| lia]. }
    pose proof (fw_nf usp P L lo j0 gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s3 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6
                  s5c s4c s3c s2c s1c s0c rac F2 fc m2 ST2 ltac:(ul) ltac:(ul) ltac:(ul) P0 ltac:(lia) ltac:(ul) FR2 MI2) as W2.
    lazymatch type of W2 with evt asegs _ ?X0 => assert (W2' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W2) end. clear W2.
    apply (cps_realizes asegs _ _ _ c3 (asta_evt_c RT AF Σ PMc _ _ MST W2') Hc3'). clear W2'. intros c6 Hc6.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c6 Hc6); intros ms0 (a1' & a3' & E & _); rewrite E; exact FRM].
    eapply ASTA_conseq; [exact Hc6|]. intros ms (a1' & a3' & -> & ST6). exists m2.
    split; [unfold ret_st; replace (Z_to_bv 64 (find_resA l)) with (Z_to_bv 64 18446744073709551615) by (unfold find_resA; rewrite HN; apply bv_eq; reflexivity); do 16 eexists; reflexivity|].
    split; [split; [exact ART2| split; [exact MI2| exact ST6]]|].
    intros a Ha _. exact (PRES2' a Ha).
Qed.

Theorem find_ok : find_cpsA RT.
Proof using AF RTF MCHR.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m X P l lo
    FDO MST -> -> -> -> -> UX XT X8 XC PB LBYT LL INLV ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct INLV as (pk & nk & INK & PK1 & PK2).
  pose proof (af_live_range RT AF Σ m pk nk ART0 INK) as (K0 & K1 & _).
  set (L := zlength l) in *. unfold zlength in L.
  assert (FPC : fp_client RT Σ lo [(usp - 64, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  pose proof (x_shz_of_fp RT AF Σ m lo _ X 16 ART0 LOW FPC ltac:(ul) ltac:(lia) ltac:(ul)) as SHX.
  destruct (Z_lt_ge_dec L 4) as [SHORT|LONG].
  -
    assert (HN : find_sep l = None) by (apply (find_sep_None_of l 0); [intros i Hi; lia| lia]).
    pose proof (fw1_short usp X P L lo ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  ST0 ltac:(ul) ltac:(ul) UX ltac:(ul) ltac:(lia) ltac:(lia) ltac:(ul) (conj G1 G2) SHX XC MI0) as W1.
    rewrite <- ESP in W1.
    lazymatch type of W1 with evt asegs _ ?X0 => assert (W1' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W1) end. clear W1.
    apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1); intros ms0 (m1 & a1' & a2' & a3' & a4' & E & _); rewrite E; exact FRM].
    eapply ASTA_conseq; [exact Hc1|]. intros ms (m1 & a1' & a2' & a3' & a4' & -> & MU1 & WM1 & MI1 & ST1). exists m1.
    split; [unfold ret_st; rewrite ESP; replace (Z_to_bv 64 (find_resA l)) with (Z_to_bv 64 18446744073709551615) by (unfold find_resA; rewrite HN; apply bv_eq; reflexivity); do 16 eexists; reflexivity|].
    split; [split; [exact (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1)| split; [exact MI1| exact ST1]]|].
    intros a Ha _. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL. apply MU1. cbn [outside]. split; [ul| exact I].
  -
    destruct (acc_lit RT AF Σ m ATPA_SEP 5 ART0 ltac:(unfold ACC_LITS, ATPA_SEP; cbn; tauto) 0 ltac:(lia)) as (bsep & BSEP & SOK). rewrite Z.add_0_r in BSEP, SOK.
    assert (SHS : forall m', munch [(usp - 64, usp)] m m' -> wmono asegs m m' -> bytes_at asegs m' (shad ATPA_SEP) [bsep]).
    { intros m' MU WM. apply (bytes_at_agree asegs m m' _ _ BSEP). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn [length Z.of_nat] in Hx.
      unfold shad, ATPA_SEP, SHB in Hx. cbn [outside]. split; [ul| exact I]. }
    pose proof (fw1_long usp X P L lo bsep ra gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                  ST0 ltac:(ul) ltac:(ul) UX ltac:(ul) ltac:(lia) ltac:(lia) ltac:(ul) (conj G1 G2) SHX SHS SOK XC MI0) as W1.
    rewrite <- ESP in W1.
    lazymatch type of W1 with evt asegs _ ?X0 => assert (W1' : forall ms, eq X0 ms -> evt asegs _ ms) by (intros ms <-; exact W1) end. clear W1.
    apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
    destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & a2' & a4' & j0 & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
    pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FPC MU1 WM1) as ART1.
    assert (PB1 : bytes_at asegs m1 P (to_bytes l)).
    { apply (bytes_at_agree asegs m m1 _ _ PB). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. rewrite to_bytes_length_a in Hx. cbn [outside]. split; [ul| exact I]. }
    assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) usp (bv_unsigned a) -> m1 a = m a).
    { intros a Ha. pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL. apply MU1. cbn [outside]. split; [ul| exact I]. }
    apply (find_loop (S (length l)) Σ PMc T usp lo P pk nk l m j0 gp (Z_to_bv 64 0x6a7e68) s6 s7 s8 s9 s10 s11 s5 s4 s3 s2 s1 s0 ra
             FDO MST eq_refl LBYT ltac:(subst L; unfold zlength in *; lia) ltac:(lia) INK PK1 ltac:(subst L; unfold zlength in *; lia) LOW LOR SPT SPA ART0
             ltac:(intros c' Hc'; apply Hk; rewrite ESP; exact Hc')
             0 t0 t1 t2 a2' (Z_to_bv 64 0) a4' a5 a6 a7 s3 t3 t4 t5 t6 ra F fc m1 c1);
      [subst L; unfold zlength in *; lia| lia| subst L; unfold zlength in *; lia| intros i Hi; lia| exact ART1| exact MI1| exact ST1| exact FR1| exact PB1| exact PRES1| exact FRM| subst L; unfold zlength in *; exact Hc1'].
Qed.

End Find.
