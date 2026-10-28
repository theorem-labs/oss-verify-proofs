(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit D_rlkit Sj_akit Sj_acps Sj_hkit
     Sj_num_akit Sj_num_amem Sj_num_aframe Sj_num_lm_kit Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_sfA_a Pj_sfA Pj_tocharsA_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zc_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac dlia := Z.div_mod_to_equations; lia.

Lemma sx32_smallB : forall x, (0 <= x < 2147483648)%Z -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
  intros x H. unfold sx32. rewrite Z_to_bv_unsigned, (bv_wrap_small 64 x) by (unfold bv_modulus; cbn; lia).
  rewrite swrap32_small by lia. reflexivity.
Qed.

Lemma dland_m32d : forall x, 0 <= x < 2^64 -> x mod 16 = 0 ->
  exists dd, (dd = 0 \/ dd = 16) /\ Z.land x 18446744073709551584 = x - dd /\ (x - dd) mod 32 = 0.
Proof.
  intros x Hx X16. exists (x - 32 * (x / 32)). rewrite (land_m32 x Hx).
  split; [Z.div_mod_to_equations; lia|]. split; [lia| Z.div_mod_to_equations; lia].
Qed.

Lemma db_pro1 : forall (p lo buf : Z) (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) fc (m : mem),
  stk bsegs m lo p -> lo + 176 <= p -> 0x6e0000 <= lo -> p + 48 <= USTACK_TOP -> p mod 16 = 0 -> client_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (dd : Z) (a1' a2' : word) (F1 : bvmap 5 word),
      (dd = 0 \/ dd = 16) /\ (p - 160 - dd) mod 32 = 0 /\
      ms = MS (mkR (wz 0xc011c) (wz (p - 160 - dd)) gp (wz TPV_A) t0 t1 t2 (wz p) (wz (p - 160 - dd)) (wz 128) a1' a2' a3 a4 a5 a6 a7
                   s2 (wz (p + 8)) (wz (p + 12)) (wz buf) s6 s7 s8 s9 (wz 2147450880) s11 t3 t4 t5 t6) F1 (wz e_stack_malloc_1) fc None m1 (seg_rom bsegs)
      /\ munch [(p - 160, p)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 lo (p - 112)
      /\ rw_cells bsegs m1 (p - 112) [C8 (reg_get F 8); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra (wz p) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz buf) (wz (p + 12)) (wz (p + 8)) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz DBOX_ENTRY_B) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO QT Q16 (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold DBOX_ENTRY_B, e_stack_malloc_1, TPV_A, USTACK_TOP in *.
  pose proof (munch_refl [(p - 160, p)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).

  zstep.
  carve_frame 160%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 160 _ [] [8; 40; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.

  lstep. do 13 zstep. zstep. zstep. zstep.
  destruct (dland_m32d (p + -160) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (dd & DD & ELAND & B32). rewrite ELAND.

  do 8 zstep. step. rewrite (sx32_smallB 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) => change (c0 :: c1 :: rest) with ([c0; c1] ++ rest) in FR end.
  apply (proj1 (num_rw_cells_app _ _ _ _ _)) in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  pose proof (stk_of_rw_cells bsegs _ _ _ FRl) as STl. cbn [cells_size csize Nat.add] in STl.
  pose proof (stk_merge bsegs _ _ _ _ ST STl ltac:(lia)) as ST2.
  replace (p + -160 + Z.of_nat 48) with (p - 112) in FRs, ST2 by lia.
  replace (p + -160 - dd) with (p - 160 - dd) by lia. replace (p + -160 + 160) with p by lia.
  apply evt_done. eexists. exists dd. do 3 eexists. split; [exact DD|]. split; [lia|]. split; [cbv delta [mkR]; reflexivity|].
  split. { eapply munch_weaken; [| exact MU]. intros x Hx. cbn [outside] in Hx |- *. lia. }
  split; [exact WM|]. split; [eassumption|]. split; [exact ST2| exact FRs].
Qed.

Lemma le8_zeroB : le8 (Z_to_bv 64 0) = repeat z8 8.
Proof. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia. reflexivity. Qed.
Definition sh16 (b : list byte) : list cell := map C1 b.
Lemma sh16_of_zerosB : forall (m : mem) a, rw_cells bsegs m a [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] -> rw_cells bsegs m a (sh16 (repeat z8 16)).
Proof.
  intros m a [[W B] R]. split; [split|].
  - cbn. repeat split; exact Logic.I.
  - cbn [cells_bytes cbytes app] in B. rewrite le8_zeroB in B. cbn [repeat app] in B. unfold sh16, z8. cbn [repeat map cells_bytes cbytes app]. exact B.
  - exact R.
Qed.

Definition pz (z : Z) : cell := C1 (Z_to_bv 8 z).
Definition sh_pro : list cell := [pz (-15); pz (-15); pz (-15); pz (-15); pz (-8); pz (-8); pz (-8); pz (-8); pz (-8); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13)].
Definition sh_run : list cell := [pz (-15); pz (-15); pz (-15); pz (-15); pz 0; pz 0; pz 0; pz 0; pz 0; pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); pz (-13)].

Definition pzm (z : Z) : cell := C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))).
Definition sh_f5 : list cell := [pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11); pzm (-11)].
Definition db_hdr : list cell := [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x20b27); C8 (Z_to_bv 64 DBOX_ENTRY_B)].

Lemma db_pro2 : forall (p b f lo buf : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (h : list byte) F fc (m : mem),
  0 < f -> f + 128 <= lo -> f / 8 + 2147450880 + 16 <= lo -> 8 * (f / 8) = f ->
  (f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f) ->
  0x6e0000 <= lo -> lo <= b -> b + 160 <= p -> p + 48 <= USTACK_TOP ->
  stk bsegs m b (p - 112) ->
  rw_cells bsegs m f [CB 24 h] -> stk bsegs m (f + 24) (f + 120) -> rw_cells bsegs m (f / 8 + 2147450880) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (EX : Z) (a0' a2' : word) (j24 j32 : list byte),
      0 <= EX <= 2047 /\
      ms = MS (mkR (wz 0xc01ec) (wz b) gp (wz TPV_A) t0 t1 t2 (wz p) (wz b) a0' (wz EX) a2' (wz (-8)) (wz (-15)) a5 a6 a7
                   (wz f) (wz (p + 8)) (wz (p + 12)) (wz buf) (wz (f + 32)) s7 (wz (f / 8 + 2147450880)) (wz f) (wz 2147450880) s11 t3 t4 t5 t6)
              F (wz PJ_SF_A) fc None m1 (seg_rom bsegs)
      /\ munch [(b + 24, b + 48); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450896)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ stk bsegs m1 b (b + 24) /\ rw_cells bsegs m1 (b + 24) [CB 8 j24; CB 8 j32; C8 (wz f)] /\ stk bsegs m1 (b + 48) (p - 112)
      /\ rw_cells bsegs m1 f db_hdr /\ stk bsegs m1 (f + 24) (f + 120) /\ rw_cells bsegs m1 (f / 8 + 2147450880) sh_pro)
    (MS (mkR (wz 0xc011c) (wz b) gp (wz TPV_A) t0 t1 t2 (wz p) (wz b) (wz f) a1 a2 a3 a4 a5 a6 a7 s2 (wz (p + 8)) (wz (p + 12)) (wz buf) s6 s7 s8 s9 (wz 2147450880) s11 t3 t4 t5 t6)
        F (wz 0xc011c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO SFL Ef SHf GLO LOB BQ QT STF FH F1S SHC MI.
  unfold TPV_A, USTACK_TOP, PJ_SF_A in *.
  pose proof (munch_refl [(b + 24, b + 48); (f, f + 24); (f / 8 + 2147450880, f / 8 + 2147450896)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.

  destruct (stk_split bsegs m _ (b + 24) _ STF ltac:(lia)) as [FR0 ST1].
  destruct (stk_split bsegs m _ (b + 48) _ ST1 ltac:(lia)) as [STs GAP].
  destruct (stk_CB bsegs m _ _ STs ltac:(lia)) as (js & FR). replace (Z.to_nat (b + 48 - (b + 24))) with 24%nat in FR by lia.
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "j" in set (j := tt) in FR; clearbody j end.

  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH; [| reflexivity]. cbn [mk_CB_cells app] in FH.
  repeat match type of FH with context [CB ?k ?tt] => lazymatch tt with firstn _ _ => idtac end; let j := fresh "h" in set (j := tt) in FH; clearbody j end.

  apply sh16_of_zerosB in SHC. unfold sh16, z8 in SHC. cbn [repeat map] in SHC.
  clear STF ST1 STs js.
  assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).

  zstep. zstep. step. if_cases K0; zify_cond K0; [clear K0| exfalso; pjnorm_in K0; lia].

  step. zstep. zstep. step. step. zstep. pjnorm. zstep. zstep. zstep. zstep. zstep. lstep. lstep. lstep.

  zstep. zstep. ls. ls. ls. ls. zstep. ls. ls. ls. ls. ls. ls. ls. ls. ls. ls. ls. ls.

  zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eexists m1, (Z.shiftr (Z.shiftl (bv_unsigned (reg_get F 8)) 1 mod 18446744073709551616) 53), _, _, j, j0.
  split. { pose proof (Z.mod_pos_bound (Z.shiftl (bv_unsigned (reg_get F 8)) 1) 18446744073709551616 ltac:(lia)) as HB.
           rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 53) with 9007199254740992. Z.div_mod_to_equations. lia. }
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
  split; [exact FR0|]. split; [exact FR|]. split; [exact GAP|]. split; [exact FH|]. split; [exact F1S|].
  unfold sh_pro, pz. exact SHC.
Qed.

Record dbI : Type := mkDB {
  d_p : Z;
  d_dd : Z;
  d_lo : Z;
  d_NB : Z;
  d_sg : Z;
  d_f : Z;
  d_gp : word;
  d_sv : list cell }.
Definition d_b (I : dbI) : Z := d_p I - 160 - d_dd I.
Definition d_S (I : dbI) : Z := d_f I / 8 + 2147450880.

Record db_ok (I : dbI) : Prop := mkDOK {
  k_dd : d_dd I = 0 \/ d_dd I = 16;
  k_lo : 0x6e0000 <= d_lo I;
  k_room : d_lo I + 192 + 0x10000 <= d_p I;
  k_ptop : d_p I + 48 <= 0x800000000000;
  k_nb8 : d_NB I mod 8 = 0;
  k_nblo : 0x6e0000 <= d_NB I;
  k_nbhi : d_NB I + 40 <= d_lo I;
  k_sg : 0 <= d_sg I <= 1;
  k_f64 : d_f I mod 64 = 0;
  k_flo : 0x6e0000 <= d_f I;
  k_fhi : d_f I + 128 <= d_lo I;
  k_fS : d_f I + 128 <= d_S I \/ d_S I + 16 <= d_f I;
  k_Shi : d_S I + 16 <= d_lo I;
  k_nbf : d_NB I + 40 <= d_f I \/ d_f I + 128 <= d_NB I;
  k_nbS : d_NB I + 40 <= d_S I \/ d_S I + 16 <= d_NB I;
  k_Snf : shad (d_NB I) + 5 <= d_f I \/ d_f I + 128 <= shad (d_NB I);
  k_SnS : shad (d_NB I) + 5 <= d_S I \/ d_S I + 16 <= shad (d_NB I);
  k_Snhi : shad (d_NB I) + 5 <= d_lo I;
  k_nbSn : d_NB I + 40 <= shad (d_NB I) \/ shad (d_NB I) + 5 <= d_NB I;
  k_p16 : d_p I mod 16 = 0;
  k_svz : cells_size (d_sv I) = 112%nat }.

Definition db_W (I : dbI) : list (Z * Z) :=
  [(d_b I + 24, d_b I + 32); (d_f I, d_f I + 24); (d_f I + 32, d_f I + 72); (d_S I, d_S I + 16); (d_NB I, d_NB I + 40); (d_p I + 8, d_p I + 16)].

Definition DINV (I : dbI) (shc : list cell) (mb m : mem) : Prop :=
  (exists j32, rw_cells bsegs m (d_b I + 24) [C8 (Z_to_bv 64 (d_f I + 32)); CB 8 j32; C8 (Z_to_bv 64 (d_f I))]) /\
  rw_cells bsegs m (d_p I + -112) (d_sv I) /\
  (exists h0 h1 h2, rw_cells bsegs m (d_f I) [C8 h0; C8 h1; C8 h2]) /\
  (exists tmp, u8arr bsegs m (d_f I + 32) tmp /\ length tmp = 40%nat) /\
  rw_cells bsegs m (d_S I) shc /\
  (exists nb, u8arr bsegs m (d_NB I) nb /\ length nb = 40%nat) /\
  (exists c0 c1, rw_cells bsegs m (d_p I + 8) [C4 c0; C4 c1]) /\
  mem_inv bsegs m /\ munch (db_W I) mb m /\ wmono bsegs mb m /\ stk bsegs m (d_lo I) (d_b I) /\
  stk bsegs m (d_b I) (d_b I + 24) /\ stk bsegs m (d_b I + 48) (d_p I + -112).

Ltac di_open H :=
  let j32 := fresh "j32" in let h0 := fresh "h0" in let h1 := fresh "h1" in let h2 := fresh "h2" in
  let tmp := fresh "tmp" in let nb := fresh "nb" in let c0 := fresh "c0" in let c1 := fresh "c1" in
  destruct H as ((j32 & LOC) & SAVED & (h0 & h1 & h2 & HDR) & (tmp & TA & TL) & SH & (nb & NA & NL) & (c0 & c1 & CEL) & MI & MU & WM & ST & FR0 & GAP).
Ltac di_close :=
  lazymatch goal with
  | |- DINV _ _ _ _ =>
      split; [eexists; eassumption|]; split; [eassumption|]; split; [do 3 eexists; eassumption|];
      split; [eexists; split; [eassumption| first [assumption | congruence]]|];
      split; [first [eassumption | unfold sh_pro, sh_run, sh_f5, pz; eassumption]|];
      split; [eexists; split; [eassumption| first [assumption | congruence]]|];
      split; [do 2 eexists; eassumption|];
      split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; [eassumption|]; split; eassumption
  end.

Ltac di_envX OK :=
  pose proof OK as OK'; destruct OK' as [Kdd Klo Kroom Kptop Knb8 Knblo Knbhi Ksg Kf64 Kflo Kfhi KfS KShi Knbf KnbS KSnf KSnS KSnhi KnbSn Kp16 Ksvz];
  unfold d_b, d_S in *; unfold shad, SHB in *.
Ltac di_env OK :=
  pose proof OK as OK'; destruct OK' as [Kdd' Klo Kroom Kptop _ Knblo Knbhi Ksg _ Kflo Kfhi KfS KShi Knbf KnbS _ _ _ _ _ Ksvz];
  lazymatch type of Kdd' with ?d = 0 \/ _ => let Kdd := fresh "Kdd" in assert (Kdd : 0 <= d <= 16) by (clear - Kdd'; lia); clear Kdd' end;
  unfold d_b, d_S in *; unfold shad, SHB in *.

Definition nb_shz (I : dbI) (mb : mem) : Prop := forall m', munch (db_W I) mb m' -> wmono bsegs mb m' -> shz m' (d_NB I) 40.
Definition dig_shz (I : dbI) (mb : mem) : Prop := forall m', munch (db_W I) mb m' -> wmono bsegs mb m' -> shz m' 0x29bb0 200.
Definition res_shz (I : dbI) (mb : mem) : Prop := forall m', munch (db_W I) mb m' -> wmono bsegs mb m' -> shz m' (d_p I + 8) 8.

Lemma db_f8 : forall I, db_ok I -> d_f I mod 8 = 0.
Proof. intros I OK. pose proof (k_f64 I OK). Z.div_mod_to_equations. lia. Qed.

Lemma lor_2r_1B : forall r, (0 <= r)%Z -> Z.lor (2 * r) 1 = (2 * r + 1)%Z.
Proof.
  intros r Hr.
  assert (L : Z.land (2 * r) 1 = 0%Z).
  { change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. change (2 ^ 1)%Z with 2%Z. rewrite Z.mul_comm. apply Z.mod_mul. lia. }
  rewrite <- (Z.lxor_lor _ _ L). symmetry. apply Z.add_nocarry_lxor. exact L.
Qed.

Ltac arr_forget UA L :=
  lazymatch type of UA with
  | u8arr _ _ _ (upd_bytes ?bs ?k ?xs) =>
      let L' := fresh "L" in
      assert (L' : length (upd_bytes bs k xs) = length bs)
        by (apply upd_bytes_length; rewrite ?length_le1, ?length_le2, ?length_le4, ?length_le8; cbn [length]; lia);
      rewrite L in L'; clear L; rename L' into L;
      let nb := fresh "bs" in set (nb := upd_bytes bs k xs) in *; clearbody nb
  end.
Ltac arr_store UA L k n := u8_store UA k n; arr_forget UA L.

Section Dig.
  Variable I : dbI.
  Hypothesis OK : db_ok I.
  Variable mb : mem.
  Variable Q : machine_state -> Prop.
  Variable e : Z.
  Hypothesis HE : (SF_EMIN <= e <= SF_EMAX)%Z.
  Hypothesis SHPN : nb_shz I mb.
  Hypothesis SHPD : dig_shz I mb.
  Variables (F : bvmap 5 word) (fc : bv 32).

  Notation p := (d_p I). Notation b := (d_b I). Notation NB := (d_NB I). Notation sg := (d_sg I). Notation f := (d_f I). Notation Sh := (d_S I). Notation lo := (d_lo I).

  Notation DBS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs6 xs7 xs11 xt3 xt4 xt5 xt6 m :=
    (MS (mkR xra (Z_to_bv 64 b) (d_gp I) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 p) (Z_to_bv 64 b) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 f) xs3 xs4 (Z_to_bv 64 (NB + sg)) xs6 xs7 (Z_to_bv 64 Sh) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

  Notation DS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 m :=
    (DBS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (p + 12)) (Z_to_bv 64 (f + 32)) xs7 (Z_to_bv 64 (f + 56)) xt3 xt4 xt5 xt6 m).

  Definition db_copy_k : Prop :=
    forall (n : Z) xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 (mm : mem),
      DINV I sh_run mb mm -> (1 <= n <= 20)%Z ->
      evt bsegs Q (DBS e_asan_memcpy (Z_to_bv 64 0xc0414) xt0 xt1 xt2 (Z_to_bv 64 (NB + sg)) (Z_to_bv 64 (f + 56 - n)) (Z_to_bv 64 16) xa3 xa4 xa5 xa6 xa7
                       (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (p + 12)) (Z_to_bv 64 (f + 56 - n)) (Z_to_bv 64 (f + 56)) xt3 xt4 xt5 xt6 mm).
  Hypothesis KC : db_copy_k.

  Lemma sh_run_zc : forall (m : mem), rw_cells bsegs m Sh sh_run -> rw_cells bsegs m (f / 8 + 2147450884) [CB 5 (repeat (Z_to_bv 8 0) 5)].
  Proof.
    intros m SHx. unfold sh_run, pz in SHx.
    destruct (proj1 (num_rw_cells_app bsegs m Sh [_; _; _; _] _) SHx) as [_ SH1]. cbn [cells_size csize Nat.add] in SH1.
    destruct (proj1 (num_rw_cells_app bsegs m _ [_; _; _; _; _] _) SH1) as [SH2 _].
    unfold d_S in SH2. replace (f / 8 + 2147450880 + Z.of_nat 4)%Z with (f / 8 + 2147450884)%Z in SH2 by lia.
    pose proof (rw_cells_merge_all _ _ _ SH2) as M. cbn [cells_size csize Nat.add cells_bytes cbytes app] in M.
    exact M.
  Qed.

  Ltac dig_open TI :=
    pose proof (sh_run_zc _ ltac:(destruct TI as (_ & _ & _ & _ & SHx & _); exact SHx)) as ZC;
    di_open TI; di_env OK;
    match goal with M : munch _ mb _ |- _ => unfold db_W, d_b, d_S in M end;
    match goal with P : nb_shz _ _ |- _ => unfold nb_shz, db_W, d_b, d_S in P end;
    match goal with P : dig_shz _ _ |- _ => unfold dig_shz, db_W, d_b, d_S in P end;
    match goal with H : (SF_EMIN <= _ <= SF_EMAX)%Z |- _ => unfold SF_EMIN, SF_EMAX in H end;
    match goal with H : rw_cells _ _ _ sh_run |- _ => unfold sh_run, pz in H end;
    pose proof (db_f8 I OK) as F8.

  Ltac dig_table m :=
    let tb := fresh "tb" in let TL := fresh "TBL" in let TB := fresh "TB" in
    destruct (image_readable_b bsegs m 200 0x29bb0 ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as (tb & TL & TB).

  Lemma db_904 : forall n xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm,
    DINV I sh_run mb mm -> (1 <= n <= 20)%Z ->
    evt bsegs Q (DBS 0xc0404 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (p + 12))
                     (Z_to_bv 64 (f + 56 - n)) (Z_to_bv 64 (f + 56)) xt3 xt4 xt5 xt6 mm).
  Proof using OK KC.
    intros until mm. intros TI HN. di_env OK.
    do 4 astep. unfold e_asan_memcpy in KC. apply KC; [exact TI| exact HN].
  Qed.

  Lemma db_tail1 : forall (j w : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa5 xa6 xa7 xs7 xt3 xt5 xt6 mm,
    DINV I sh_run mb mm -> (0 <= w < 10)%Z -> (1 <= j <= 10)%Z ->
    evt bsegs Q (DS 0xc03d4 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (e mod 4294967296)) xa2 xa3 (Z_to_bv 64 w) xa5 xa6 xa7 xs7 xt3 (Z_to_bv 64 (f + 36 + 2 * j)) xt5 xt6 mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros TI HW HJ. dig_open TI.

    zastep. zastep. if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|].
    zastep. zastep. zastep. zastep.
    zastep. zastep. zastep. zastep. if_false.
    astep. astep.
    eapply evt_eq; [| eapply (db_904 (21 - 2 * j)%Z); [di_close | lia]].
    num_st_eq.
  Qed.

  Lemma db_tail2 : forall (j w : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa5 xa6 xa7 xs7 xt3 xt5 xt6 mm,
    DINV I sh_run mb mm -> (10 <= w < 100)%Z -> (1 <= j <= 10)%Z ->
    evt bsegs Q (DS 0xc032c xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (e mod 4294967296)) xa2 xa3 (Z_to_bv 64 w) xa5 xa6 xa7 xs7 xt3 (Z_to_bv 64 (f + 36 + 2 * j)) xt5 xt6 mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros TI HW HJ. dig_open TI. dig_table mm.

    zastep. zastep. if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].
    zastep. rewrite shl1. rewrite (swrap32_id (2 * w)) by lia.
    zastep. zastep. zastep.
    zastep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    zastep. zastep. zastep. zastep. zastep. if_false.

    zastep. zastep. zastep. zastep. astep. zastep. if_false.

    zastep. rewrite (lor_2r_1B w) by lia.
    astep.
    zastep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].
    zastep. zastep. if_cases G4; zify_cond G4; [exfalso; rewrite ?unsigned_lit in G4 by lia; lia|].

    zastep. zastep. zastep. zastep. zastep. zastep. zastep. if_false.

    zastep. zastep. zastep. zastep. zastep. astep. zastep. if_false.
    astep. zastep.
    eapply evt_eq; [| eapply (db_904 (22 - 2 * j)%Z); [di_close | lia]].
    num_st_eq.
  Qed.

  Lemma db_8cc : forall (j w : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa5 xa6 xa7 xs7 xt3 xt5 xt6 mm,
    DINV I sh_run mb mm -> (0 <= w < 100)%Z -> (1 <= j <= 10)%Z ->
    evt bsegs Q (DS 0xc03cc xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (e mod 4294967296)) xa2 xa3 (Z_to_bv 64 w) xa5 xa6 xa7 xs7 xt3 (Z_to_bv 64 (f + 36 + 2 * j)) xt5 xt6 mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros TI HW HJ. pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ Kflo Kfhi _ _ _ _ _ _ _ _ _ _].
    zastep.
    zastep. if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply (db_tail2 j w); [exact TI | lia | lia]]. num_st_eq.
    - eapply evt_eq; [| eapply (db_tail1 j w); [exact TI | lia | lia]]. num_st_eq.
  Qed.

  Lemma db_824 : forall (w : Z) xra xt0 xt1 xt2 xa0 xa2 xa3 xa5 xa6 xa7 xs7 xt3 xt5 xt6 mm,
    DINV I sh_run mb mm -> (0 <= w < 100)%Z ->
    evt bsegs Q (DS 0xc0324 xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (e mod 4294967296)) xa2 xa3 (Z_to_bv 64 w) xa5 xa6 xa7 xs7 xt3 (Z_to_bv 64 (f + 56)) xt5 xt6 mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros TI HW. pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ Kflo Kfhi _ _ _ _ _ _ _ _ _ _].
    zastep.
    zastep. if_cases K; zify_cond K.
    - eapply evt_eq; [| eapply (db_tail1 10%Z w); [exact TI | lia | lia]]. num_st_eq.
    - eapply evt_eq; [| eapply (db_tail2 10%Z w); [exact TI | lia | lia]]. num_st_eq.
  Qed.

  Lemma db_loop : forall (fu : nat) (j w : Z) xra xa2 xa3 xa4 xt5 xt6 mm,
    DINV I sh_run mb mm -> (100 <= w < 100 ^ j)%Z -> (w < 18446744073709551616)%Z -> (j <= 10)%Z -> (j <= Z.of_nat fu)%Z ->
    evt bsegs Q (DS 0xc0244 xra (Z_to_bv 64 0x29bb0) (Z_to_bv 64 18446744073709380687) (Z_to_bv 64 (-1))
                    (Z_to_bv 64 w) (Z_to_bv 64 (e mod 4294967296)) xa2 xa3 xa4 (Z_to_bv 64 100) (Z_to_bv 64 3) (Z_to_bv 64 DIV100_MAGIC)
                    (Z_to_bv 64 (f + 34 + 2 * j)) (Z_to_bv 64 624) (Z_to_bv 64 (f + 34 + 2 * j)) xt5 xt6 mm).
  Proof using OK KC SHPN SHPD.
    induction fu as [|fu IH]; intros until mm; intros TI HW W64 HJ HF.
    { exfalso. pose proof (pow100_ge2 w j HW). lia. }
    pose proof (pow100_ge2 w j HW) as J2.
    pose proof (pow100_step w j ltac:(lia) ltac:(lia)) as HQ.
    dig_open TI. dig_table mm. unfold DIV100_MAGIC in *.

    zastep. zastep. if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].

    zstep. zstep. zstep.
    change 2951479051793528259%Z with DIV100_MAGIC. rewrite (div100_machine w) by lia.

    zastep. zastep.
    replace (w - w / 100 * 100)%Z with (w mod 100)%Z by (Z.div_mod_to_equations; lia).
    assert (R100 : (0 <= w mod 100 < 100)%Z) by (apply Z.mod_pos_bound; lia).
    set (r := (w mod 100)%Z) in *.
    rewrite (swrap32_id r) by lia.

    zastep. try rewrite (Z.mod_small r) by lia. rewrite shl1. rewrite (swrap32_id (2 * r)) by lia.
    zastep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    zastep. zastep. zastep. zastep. zastep. if_false.

    zastep. zastep. zastep. astep. zastep. if_false.

    zastep. rewrite (lor_2r_1B r) by lia.
    astep.
    zastep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].
    zastep. if_cases G4; zify_cond G4; [exfalso; rewrite ?unsigned_lit in G4 by lia; lia|].

    zastep. zastep. zastep. zastep. zastep. if_false.
    zastep. zastep. zastep. zastep. astep. zastep. if_false.
    astep.

    zastep. zastep. zastep. zastep.
    zastep. if_cases K; zify_cond K.
    -
      assert (W4 : (10000 <= w)%Z).
      { rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 4)%Z with 16%Z in K. Z.div_mod_to_equations. lia. }
      eapply evt_eq; [| eapply (IH (j - 1)%Z (w / 100)%Z); [di_close | | | lia | lia]].
      + num_st_eq.
      + split; [Z.div_mod_to_equations; lia| lia].
      + Z.div_mod_to_equations; lia.
    - assert (W4 : (w < 10000)%Z).
      { rewrite Z.shiftr_div_pow2 in K by lia. change (2 ^ 4)%Z with 16%Z in K. Z.div_mod_to_equations. lia. }
      assert (Q100 : (0 <= w / 100 < 100)%Z) by (Z.div_mod_to_equations; lia).

      zastep. zastep.
      eapply evt_eq; [| eapply (db_8cc (j - 1)%Z (w / 100)%Z); [di_close | lia | lia]].
      num_st_eq.
  Qed.

  Lemma db_dig : forall (wd : word) xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xs11 xt3 xt4 xt5 xt6 (j24 j32 : list byte) (h0 h1 h2 : word)
      (tmp nb : list byte) (c0 c1 : word) mm,
    rw_cells bsegs mm (b + 24) [CB 8 j24; CB 8 j32; C8 (Z_to_bv 64 f)] -> rw_cells bsegs mm (p + -112) (d_sv I) ->
    rw_cells bsegs mm f [C8 h0; C8 h1; C8 h2] -> u8arr bsegs mm (f + 32) tmp -> length tmp = 40%nat -> rw_cells bsegs mm Sh sh_pro ->
    u8arr bsegs mm NB nb -> length nb = 40%nat -> rw_cells bsegs mm (p + 8) [C4 c0; C4 c1] ->
    mem_inv bsegs mm -> munch (db_W I) mb mm -> wmono bsegs mb mm -> stk bsegs mm lo b -> stk bsegs mm b (b + 24) -> stk bsegs mm (b + 48) (p + -112) ->
    evt bsegs Q (DBS 0xc01ec xra xt0 xt1 xt2 wd (Z_to_bv 64 (e mod 4294967296)) xa2 xa3 xa4 xa5 xa6 xa7
                     (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (p + 12)) (Z_to_bv 64 (f + 32)) xs7 xs11 xt3 xt4 xt5 xt6 mm).
  Proof using OK KC SHPN SHPD.
    intros until mm. intros LOC SAVED HDR TA TL SH NA NL CEL MI MU WM ST FR0 GAP.
    pose proof (bv_unsigned_in_range 64 wd) as WR. unfold bv_modulus in WR. cbn in WR.
    rewrite <- (Z_to_bv_bv_unsigned wd). set (w := bv_unsigned wd) in *. clearbody w.
    di_env OK. unfold db_W, d_b, d_S in MU. unfold sh_pro, pz in SH. pose proof (db_f8 I OK) as F8.

    do 4 astep. zastep. astep. astep.

    zastep. if_cases G; zify_cond G; [exfalso; rewrite ?unsigned_lit in G by lia; lia|].
    zastep. zastep.
    zastep. if_cases K; zify_cond K.
    -
      zastep. zastep.
      eapply evt_eq; [| eapply (db_824 w); [di_close | lia]]. num_st_eq.
    -
      do 11 zastep.
      eapply evt_eq; [| eapply (db_loop 10%nat 10%Z w); [di_close | | lia | lia | lia]].
      + num_st_eq.
      + change (100 ^ 10)%Z with 100000000000000000000%Z. lia.
  Qed.
End Dig.

Section Fin.
  Variable I : dbI.
  Hypothesis OK : db_ok I.
  Variable mb : mem.
  Variable Q : machine_state -> Prop.
  Variables (e n : Z).
  Hypothesis HE : (SF_EMIN <= e <= SF_EMAX)%Z.
  Hypothesis HN : (1 <= n <= 20)%Z.
  Hypothesis SHPN : nb_shz I mb.
  Hypothesis SHPR : res_shz I mb.
  Variables (F : bvmap 5 word) (fc : bv 32).

  Notation p := (d_p I). Notation b := (d_b I). Notation NB := (d_NB I). Notation sg := (d_sg I). Notation f := (d_f I). Notation Sh := (d_S I). Notation lo := (d_lo I).
  Notation DBS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs11 xt3 xt4 xt5 xt6 m :=
    (MS (mkR xra (Z_to_bv 64 b) (d_gp I) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 p) (Z_to_bv 64 b) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 f) xs3 xs4 xs5 xs6 xs7 (Z_to_bv 64 Sh) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs11 xt3 xt4 xt5 xt6)
        F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

  Definition db_rel_k : Prop :=
    forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs11 xt3 xt4 xt5 xt6 (h1 h2 : word) (j32 tmp nb : list byte) (mm : mem),
      rw_cells bsegs mm (b + 24) [C8 (Z_to_bv 64 (f + 32)); CB 8 j32; C8 (Z_to_bv 64 f)] -> rw_cells bsegs mm (p + -112) (d_sv I) ->
      rw_cells bsegs mm f [C8 (Z_to_bv 64 0x45e0360e); C8 h1; C8 h2] -> u8arr bsegs mm (f + 32) tmp -> length tmp = 40%nat -> rw_cells bsegs mm Sh sh_f5 ->
      u8arr bsegs mm NB nb -> length nb = 40%nat -> rw_cells bsegs mm (p + 8) [C4 (Z_to_bv 64 (e mod 4294967296)); C4 (Z_to_bv 64 n)] ->
      mem_inv bsegs mm -> munch (db_W I) mb mm -> wmono bsegs mb mm -> stk bsegs mm lo b -> stk bsegs mm b (b + 24) -> stk bsegs mm (b + 48) (p + -112) ->
      evt bsegs Q (DBS 0xc04f4 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs11 xt3 xt4 xt5 xt6 mm).
  Hypothesis KR : db_rel_k.

  Lemma db_fin : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 mm,
    DINV I sh_run mb mm ->
    evt bsegs Q (DBS 0xc0414 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (e mod 4294967296)) (Z_to_bv 64 (p + 8)) (Z_to_bv 64 (NB + sg))
                     (Z_to_bv 64 (p + 12)) (Z_to_bv 64 (f + 56 - n)) (Z_to_bv 64 (f + 56)) xt3 xt4 xt5 xt6 mm).
  Proof using OK HE HN SHPN SHPR KR.
    intros until mm. intros TI.
    pose proof (sh_run_zc I _ ltac:(destruct TI as (_ & _ & _ & _ & SHx & _); exact SHx)) as ZC.
    di_open TI. di_env OK. unfold db_W, d_b, d_S in MU.
    unfold nb_shz, db_W, d_b, d_S in SHPN. unfold res_shz, db_W, d_b, d_S in SHPR. unfold SF_EMIN, SF_EMAX in HE. unfold sh_run, pz in SH.
    pose proof (db_f8 I OK) as F8.

    zastep.
    zastep. if_cases G1; zify_cond G1; [exfalso; rewrite ?unsigned_lit in G1 by lia; lia|].
    zastep. if_cases G2; zify_cond G2; [exfalso; rewrite ?unsigned_lit in G2 by lia; lia|].

    zastep. zastep. zastep. zastep. zastep. if_false.

    zastep. zastep. zastep. zastep. astep. zastep. if_false.

    zastep. astep. zastep.
    zastep. if_cases G3; zify_cond G3; [exfalso; rewrite ?unsigned_lit in G3 by lia; lia|].

    zastep. zastep. zastep. zastep. if_false.
    zastep.
    replace (f + 56 - (f + 56 - n))%Z with n by lia.
    zastep. astep. zastep. zastep. zastep. if_false.
    astep.

    zastep. zastep. clear ZC. do 5 astep. zastep. astep.
    zastep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|].
    zastep. do 16 astep.
    eapply (KR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 j32); [exact LOC| exact SAVED| exact HDR| exact TA| congruence| unfold sh_f5, pzm; exact SH| exact NA| congruence
      | exact CEL| exact MI| exact MU| exact WM| exact ST| exact FR0| exact GAP].
  Qed.
End Fin.

Lemma db_epi : forall (p b f fl lo : Z) (gp xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 xra : word)
    (vfs0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FRC : list cell) F fc (m : mem),
  0 < f -> f + 128 <= lo -> 0 < fl -> fl + 1 <= lo -> 0x6e0000 <= lo -> lo <= b -> cells_size FRC = 24%nat -> b + 160 <= p -> p + 48 <= USTACK_TOP -> b + 48 <= p - 112 ->
  stk bsegs m lo b -> stk bsegs m b (b + 24) -> rw_cells bsegs m (b + 24) FRC -> stk bsegs m (b + 48) (p + -112) ->
  rw_cells bsegs m (p + -112) [C8 vfs0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  ro_cells bsegs m (f + 120) [C8 (wz fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (F' : bvmap 5 word) ya0,
      ms = MS (mkR ra (wz p) gp (wz TPV_A) xt0 xt1 xt2 s0 s1 ya0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
              F' (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo p /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR xra (wz b) gp (wz TPV_A) xt0 xt1 xt2 (wz p) (wz b) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             (wz f) xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (wz 0xc04f4) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FLO FL0 FLLO GLO LOB SZ BQ QT GB ST FR0 FR GAP FS FW FLC MI.
  unfold TPV_A, USTACK_TOP in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 p) = p) by (apply unsigned_lit; lia).

  zstep. ls. step. zstep.

  do 13 zstep. zstep. zstep.
  pose proof (stk_merge bsegs _ _ _ _ ST FR0 ltac:(lia)) as ST0.
  pose proof (stk_release bsegs _ _ _ _ ST0 FR ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 24%nat) with 24 in ST1.
  replace (b + 24 + 24) with (b + 48) in ST1 by lia.
  pose proof (stk_merge bsegs _ _ _ _ ST1 GAP ltac:(lia)) as ST2.
  pose proof (stk_release bsegs _ _ _ _ ST2 FS ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (p + -112 + Z.of_nat 112) with p in ST3 by lia. replace (p + -160 + 160) with p by lia.

  zstep.
  apply evt_done. do 3 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.

Lemma u8arr_after_dst : forall (m m' : mem) A (bs0 : list byte) d (bs : list byte),
  u8arr bsegs m A bs0 -> length bs0 = 40%nat -> A <= d -> d + Z.of_nat (length bs) <= A + 40 ->
  agree_on (fun x => A <= x < A + 40 /\ ~ (d <= x < d + Z.of_nat (length bs))) m m' -> wmono bsegs m m' ->
  bytes_at bsegs m' d bs ->
  exists bs', u8arr bsegs m' A bs' /\ length bs' = 40%nat.
Proof.
  intros m m' A bs0 d bs UA L0 HA HD AG WM BY.
  destruct (u8arr_range_split bsegs m A bs0 (Z.to_nat (d - A)) (Z.to_nat (d - A) + length bs) UA ltac:(lia) ltac:(lia))
    as (b1 & mid & b3 & L1 & L2 & L3 & U1 & MID & U3).
  assert (U1' : u8arr bsegs m' A b1).
  { apply (u8arr_agree m m' A b1 U1); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite L1 in Hx. lia. }
  assert (U3' : u8arr bsegs m' (A + Z.of_nat (Z.to_nat (d - A) + length bs)) b3).
  { apply (u8arr_agree m m' _ b3 U3); [| exact WM]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. rewrite L3, L0 in Hx. lia. }
  assert (MID' : rw_cells bsegs m' (A + Z.of_nat (length b1)) [CB (length bs) bs]).
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat (d - A))) with d by lia. apply rw_cells_CB_intro; [exact BY|].
    destruct MID as [_ W2]. cbn [cells_size csize Nat.add] in W2. rewrite Nat.add_0_r in W2.
    replace (A + Z.of_nat (Z.to_nat (d - A))) with d in W2 by lia.
    replace (Z.to_nat (d - A) + length bs - Z.to_nat (d - A))%nat with (length bs) in W2 by lia.
    exact (wr_at_transport bsegs m m' d _ W2 WM). }
  destruct (u8arr_range_join bsegs m' A b1 (length bs) bs b3 U1' MID') as (bs' & LB & UB).
  { rewrite L1. replace (A + Z.of_nat (Z.to_nat (d - A)) + Z.of_nat (length bs)) with (A + Z.of_nat (Z.to_nat (d - A) + length bs)) by lia. exact U3'. }
  exists bs'. split; [exact UB|]. rewrite LB, L1, L3, L0. lia.
Qed.

Section DBK.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis MST : mat_stable PMc.
Variables (Σ Σ1 : rts RT) (I : dbI) (fN : Z) (kN : nat).
Hypothesis OK : db_ok I.

Notation p := (d_p I). Notation b := (d_b I). Notation NB := (d_NB I). Notation f := (d_f I). Notation Sh := (d_S I). Notation lo := (d_lo I).

Hypothesis EF : rt_frames RT Σ1 = (d_f I, 1%nat) :: rt_frames RT Σ.
Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ.
Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ.
Hypothesis INF : In (fN, kN) (rt_frames RT Σ).
Hypothesis NBF : fN <= d_NB I /\ d_NB I + 40 <= fN + fs_size kN - 8.
Hypothesis LOR : rt_sp0 RT Σ - STACK_WIN <= d_lo I.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition BASE (m0 mb : mem) : Prop :=
  ART RT Σ1 mb /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) p [(NB, NB + 40); (p + 8, p + 16)] m0 mb /\ bytes_at bsegs mb (shad NB) (repeat z8 5).

Lemma inF1 : In (d_f I, 1%nat) (rt_frames RT Σ1).
Proof using EF. rewrite EF. left. reflexivity. Qed.
Lemma inFN1 : In (fN, kN) (rt_frames RT Σ1).
Proof using EF INF. rewrite EF. right. exact INF. Qed.

Lemma fpW : fp_ok RT Σ1 b (db_W I).
Proof using OK EF INF NBF.
  pose proof inF1 as IN1. pose proof inFN1 as IN2. di_envX OK. unfold fp_ok, db_W, d_b, d_S.
  apply Forall_cons; [cbn [fst snd]; left; ul|].
  apply Forall_cons; [cbn [fst snd]; right; right; left; exists (d_f I), 1%nat; split; [exact IN1| rewrite fs1; lia]|].
  apply Forall_cons; [cbn [fst snd]; right; right; left; exists (d_f I), 1%nat; split; [exact IN1| rewrite fs1; lia]|].
  apply Forall_cons; [cbn [fst snd]; right; right; right; exists (d_f I), 1%nat; split; [exact IN1|]; rewrite fs1s; unfold shad, SHB; lia|].
  apply Forall_cons; [cbn [fst snd]; right; right; left; exists fN, kN; split; [exact IN2| lia]|].
  apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. left. ul.
Qed.

Lemma W_out : forall (mb : mem) a, ART RT Σ1 mb -> aclient (rt_live RT Σ) (rt_frames RT Σ) p a -> ~ (NB <= a < NB + 40) -> ~ (p + 8 <= a < p + 16) -> outside (db_W I) a.
Proof using AF OK EF EL ES LOR.
  intros mb a ART1 Ha Hnb Hp8. di_envX OK.
  assert (ELi : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL; auto).
  destruct (newframe_apartI RT AF Σ Σ1 mb (d_f I) 1%nat p a ART1 EF ELi ES ltac:(lia) Ha) as [N1 N2].
  rewrite ?fs1s, ?fs1 in N2. rewrite ?fs1 in N1. unfold shad, SHB, fs_size in N1, N2. cbn [Z.shiftl Z.of_nat Pos.of_succ_nat Pos.succ Pos.iter Z.mul Pos.mul] in N1, N2.
  assert (SPL : p <= a \/ a < rt_sp0 RT Σ - STACK_WIN).
  { destruct (aclient_split_c RT AF Σ1 mb p a ART1) as [H|H]; [| left; exact H| right; rewrite <- ES; exact H].
    rewrite EF. eapply aclient_mono; [exact Ha| exact ELi| intros x Hx; right; exact Hx| lia]. }
  unfold db_W, d_b, d_S. cbn [outside]. repeat split; lia.
Qed.

Lemma base_art : forall m0 mb mm shc, BASE m0 mb -> DINV I shc mb mm -> ART RT Σ1 mm.
Proof using AF OK EF INF NBF LOR ES.
  intros m0 mb mm shc (ART1 & _ & _) TI. di_open TI. pose proof OK as OK'. destruct OK' as [Kdd _ Kroom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  apply (art_of_munch RT AF Σ1 mb mm b (db_W I) ART1); [rewrite ES; unfold d_b; lia| exact fpW| exact MU| exact WM].
Qed.

Lemma base_pres : forall m0 mb mm, BASE m0 mb -> munch (db_W I) mb mm -> rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) p [(NB, NB + 40); (p + 8, p + 16)] m0 mm.
Proof using AF OK EF EL ES LOR.
  intros m0 mb mm (ART1 & PRES & _) MU.
  eapply pres_fp_trans; [exact PRES|]. apply (pres_fp_of_munch _ _ _ _ _ _ _ MU).
  intros a Ha Ho. cbn [outside] in Ho. apply (W_out mb a ART1 Ha); lia.
Qed.

Lemma base_nbsh : forall m0 mb mm, BASE m0 mb -> munch (db_W I) mb mm -> bytes_at bsegs mm (shad NB) (repeat z8 5).
Proof using OK.
  intros m0 mb mm (_ & _ & SHN) MU. di_envX OK.
  apply (bytes_at_agree bsegs mb mm _ _ SHN). apply (agree_of_munch _ _ _ _ MU).
  intros x Hx. rewrite repeat_length in Hx. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. unfold db_W, d_b, d_S. cbn [outside].
  repeat split; lia.
Qed.

Lemma base_shpn : forall m0 mb, BASE m0 mb -> nb_shz I mb.
Proof using OK.
  intros m0 mb B m' MU WM. pose proof (base_nbsh m0 mb m' B MU) as SHN. di_envX OK.
  change 40 with (8 * Z.of_nat 5). apply shz_run0; [exact Knb8| lia| exact SHN].
Qed.

Lemma base_shpd : forall m0 mb, BASE m0 mb -> dig_shz I mb.
Proof using AF OK EF INF NBF LOR ES.
  intros m0 mb (ART1 & _) m' MU WM. pose proof OK as OK'. destruct OK' as [Kdd _ Kroom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
  assert (ART' : ART RT Σ1 m').
  { apply (art_of_munch RT AF Σ1 mb m' b (db_W I) ART1); [rewrite ES; unfold d_b; lia| exact fpW| exact MU| exact WM]. }
  change 200 with (8 * (200 / 8)). apply shz_of_acc; [| reflexivity| lia].
  apply (acc_lit RT AF Σ1 m' 0x29bb0 200 ART'). unfold ACC_LITS. cbn [In]. repeat (first [left; reflexivity | right]).
Qed.

Lemma base_shpr : forall m0 mb, BASE m0 mb -> res_shz I mb.
Proof using AF OK EF INF NBF LOR ES.
  intros m0 mb (ART1 & _) m' MU WM. pose proof OK as OK'. destruct OK' as [Kdd Klo Kroom Kptop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Kp16 _].
  assert (ART' : ART RT Σ1 m').
  { apply (art_of_munch RT AF Σ1 mb m' b (db_W I) ART1); [rewrite ES; unfold d_b; lia| exact fpW| exact MU| exact WM]. }
  assert (AS : acc bsegs m' (p + 8) 8). { apply (af_acc_stack RT AF Σ1 m' (p + 8) 8 ART'); [rewrite ES; clear - LOR Kroom; lia| clear - Kptop; ul]. }
  assert (P8 : (p + 8) mod 8 = 0) by (clear - Kp16; Z.div_mod_to_equations; lia).
  exact (shz_of_acc m' (p + 8) 8 AS P8 ltac:(clear - Kroom Klo; lia)).
Qed.

Lemma dinv_client : forall x,
  (b <= x < p + 16) \/ (NB <= x < NB + 40) \/ (f <= x < f + 72) \/ (Sh <= x < Sh + 16) ->
  aclient (rt_live RT Σ1) (rt_frames RT Σ1) b x.
Proof using OK EF INF NBF.
  intros x Hx. pose proof inF1 as IN1. pose proof inFN1 as IN2. di_envX OK.
  destruct Hx as [H|[H|[H|H]]].
  - left. ul.
  - right; right; right; left. exists fN, kN. split; [exact IN2| lia].
  - right; right; right; left. exists (d_f I), 1%nat. split; [exact IN1| rewrite fs1; lia].
  - right; right; right; right. exists (d_f I), 1%nat. split; [exact IN1|]. rewrite fs1s. unfold shad, SHB. lia.
Qed.

Lemma dinv_after_nb : forall mb mm m' shc d k (bs : list byte), DINV I shc mb mm -> cells_size shc = 16%nat ->
  rt_after RT Σ1 b lo mm m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) b d k mm m' ->
  bytes_at bsegs m' d bs -> Z.of_nat (length bs) = k -> NB <= d -> d + k <= NB + 40 ->
  DINV I shc m' m'.
Proof using OK EF INF NBF.
  intros mb mm m' shc d k bs TI SZ (ART' & MI' & WM' & ST') PR BY LK D1 D2. subst k. di_open TI. di_envX OK.
  assert (AG : forall P : Z -> Prop,
    (forall x, P x -> ((p - 160 - d_dd I <= x < p + 16) \/ (NB <= x < NB + 40) \/ (f <= x < f + 72) \/ (f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16))
                      /\ ~ (d <= x < d + Z.of_nat (length bs))) -> agree_on P mm m').
  { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. apply (PR a); [| exact H2]. apply dinv_client. unfold d_b, d_S. exact H1. }
  split. { exists j32. apply (rw_cells_agree bsegs mm m' _ _ LOC); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
  split. { apply (rw_cells_agree bsegs mm m' _ _ SAVED); [| exact WM']. apply AG. intros x Hx. rewrite Ksvz in Hx. cbn in Hx. split; lia. }
  split. { exists h0, h1, h2. apply (rw_cells_agree bsegs mm m' _ _ HDR); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
  split. { exists tmp. split; [| exact TL]. apply (u8arr_agree mm m' _ _ TA); [| exact WM']. apply AG. intros x Hx. rewrite TL in Hx. cbn in Hx. split; lia. }
  split. { apply (rw_cells_agree bsegs mm m' _ _ SH); [| exact WM']. apply AG. intros x Hx. rewrite SZ in Hx. cbn in Hx. split; lia. }
  split. { apply (u8arr_after_dst mm m' _ nb d bs NA NL D1 D2); [| exact WM'| exact BY]. apply AG. intros x [Hx1 Hx2]. split; [lia| exact Hx2]. }
  split. { exists c0, c1. apply (rw_cells_agree bsegs mm m' _ _ CEL); [| exact WM']. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; lia. }
  split; [exact MI'|]. split; [apply munch_refl|]. split; [apply wmono_refl|]. split; [exact ST'|].
  split. { apply (stk_agree_nw bsegs mm m' _ _ FR0). apply AG. intros x Hx. split; lia. }
  apply (stk_agree_nw bsegs mm m' _ _ GAP). apply AG. intros x Hx. split; lia.
Qed.

Lemma base_after_call : forall m0 mb mm m' shc d k, BASE m0 mb -> DINV I shc mb mm ->
  ART RT Σ1 m' -> rt_pres_ex (rt_live RT Σ1) (rt_frames RT Σ1) b d k mm m' ->
  NB <= d /\ d + k <= NB + 40 ->
  BASE m0 m'.
Proof using AF OK EF EL ES INF NBF LOR.
  intros m0 mb mm m' shc d k B TI ART' PR HD. pose proof B as (ART1 & _ & _).
  assert (MUx : munch (db_W I) mb mm) by (destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & MU & _); exact MU).
  pose proof (base_pres m0 mb mm B MUx) as PRES. pose proof (base_nbsh m0 mb mm B MUx) as SHN.
  pose proof inFN1 as IN2. di_envX OK.
  assert (ELi : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL; auto).
  split; [exact ART'|]. split.
  - eapply pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply (PR a).
    + rewrite EF. eapply aclient_mono; [exact Ha| exact ELi| intros x Hx; right; exact Hx| lia].
    + cbn [outside] in Ho. destruct HD as [D1 D2]. lia.
  - apply (bytes_at_agree bsegs mm m' _ _ SHN). intros a Ha. rewrite repeat_length in Ha. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Ha.
    apply (PR a).
    + right; right; right; right. exists fN, kN. split; [exact IN2|].
      pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
      unfold shad, SHB. Z.div_mod_to_equations. lia.
    + destruct HD as [D1 D2]. lia.
Qed.
End DBK.

Section DBC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis SM1Z : stack_malloc1z_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Lemma db_smalloc1z : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 TPV_A ->
  (length (rt_frames RT Σ) < FRAMES_MAX2)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo -> rt_frames RT Σ <> [] ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at bsegs m' f (fs_size 1 - 8) -> wr_at bsegs m' (shad f) (fs_size 1 / 8) -> rw_cells bsegs m' (shad f) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
     rt_frames RT Σ' = (f, 1%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size 1 < USTACK_TOP ->
     aevt RT PMc Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_stack_malloc_1) fc None m (seg_rom bsegs)).
Proof using SM1Z FDO MST.
  intros until lo. intros ETP FRL CR ART0 MI0 COK NE HK.
  eapply aevt_icall.
  - exact (SM1Z Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo FDO MST ETP FRL CR ART0 MI0 COK NE).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2 & W3).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt RT PMc Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR W1 W2 W3 E1 E2 E3 E4 F1 F2 F3).
Qed.

Section Calls.
Variables (Σ Σ1 : rts RT) (I : dbI) (fN : Z) (kN : nat) (K : config -> Prop) (m0 : mem).
Variables (vfs0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32).
Hypothesis OK : db_ok I.
Hypothesis ESV : d_sv I = [C8 vfs0; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Notation p := (d_p I). Notation b := (d_b I). Notation NB := (d_NB I). Notation f := (d_f I). Notation Sh := (d_S I). Notation lo := (d_lo I). Notation sg := (d_sg I).
Hypothesis EF : rt_frames RT Σ1 = (d_f I, 1%nat) :: rt_frames RT Σ.
Hypothesis EL : rt_live RT Σ1 = rt_live RT Σ.
Hypothesis ES : rt_sp0 RT Σ1 = rt_sp0 RT Σ.
Hypothesis EC : rt_credit RT Σ1 = rt_credit RT Σ - 1.
Hypothesis INF : In (fN, kN) (rt_frames RT Σ).
Hypothesis NBF : fN <= d_NB I /\ d_NB I + 40 <= fN + fs_size kN - 8.
Hypothesis LOR : rt_sp0 RT Σ - STACK_WIN <= d_lo I.
Hypothesis FRM : frm0 fc.

Hypothesis HK : forall (Σ' : rts RT) (n e : Z) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' (nb' : list byte),
  frm0 fc' -> ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' lo p ->
  rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> rt_credit RT Σ - 1 <= rt_credit RT Σ' ->
  rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) p [(NB, NB + 40); (p + 8, p + 16)] m0 m' ->
  1 <= n <= 20 -> SF_EMIN <= e <= SF_EMAX ->
  rw_cells bsegs m' (p + 8) [C4 (Z_to_bv 64 (e mod 4294967296)); C4 (Z_to_bv 64 n)] -> u8arr bsegs m' NB nb' -> length nb' = 40%nat ->
  bytes_at bsegs m' (shad NB) (repeat z8 5) ->
  aevt RT PMc Σ' K (MS (mkR ra (Z_to_bv 64 p) (d_gp I) (Z_to_bv 64 TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                    F' (ret_pc ra) fc' None m' (seg_rom bsegs)).

Notation Q := (fun ms : machine_state => aevt RT PMc Σ1 K ms).
Notation BASEI := (BASE RT Σ Σ1 I).
Local Ltac ul := unfold d_b, d_S, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma db_call_ok : forall mb mm shc, DINV I shc mb mm -> call_ok RT Σ1 mm (Z_to_bv 64 b) lo.
Proof using OK ES LOR.
  intros mb mm shc TI. di_open TI. di_envX OK. unfold call_ok. rewrite unsigned_lit by ul. rewrite ES.
  split; [exact ST|]. split; [ul|]. split; [ul|]. split; [ul|].
  destruct Kdd as [Ed|Ed]; rewrite Ed; clear - Kp16; Z.div_mod_to_equations; lia.
Qed.

Lemma db_relB : forall (F : bvmap 5 word) mb e n, BASEI m0 mb -> SF_EMIN <= e <= SF_EMAX -> 1 <= n <= 20 -> db_rel_k I mb Q e n F fc.
Proof using AF MST OK ESV EF EL ES INF NBF LOR HK EC FRM.
  intros F mb e n B HE HN. pose proof B as (ARTb & _ & _). unfold db_rel_k. intros until mm. intros LOC SAVED HDR TA TL SH NA NL CEL MI MU WM ST FR0 GAP.
  pose proof (inFN1 RT Σ Σ1 I fN kN EF INF) as IN2. di_envX OK.
  assert (ELi : forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σ1)) by (rewrite EL; auto).
  assert (TI1 : DINV I sh_f5 mb mm) by di_close.
  pose proof (base_art RT AF Σ Σ1 I fN kN OK EF ES INF NBF LOR m0 mb mm sh_f5 B TI1) as ART1.
  destruct (af_frame_release RT AF Σ1 mm (d_f I) 1%nat (rt_frames RT Σ) ART1 EF) as (Σ2 & fl & FLAG & NAC & FL0 & FL1 & LAST & REL).
  rewrite fs1 in LAST. replace (d_f I + 128 - 8) with (d_f I + 120) in LAST by lia. rewrite ES in FL1.
  assert (FLX : fl + 1 <= lo) by (clear - FL1 LOR; lia).
  rewrite ESV in SAVED.
  eapply evt_cut; [eapply (db_epi p b f fl lo (d_gp I) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ vfs0 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                             [C8 (Z_to_bv 64 (f + 32)); CB 8 j32; C8 (Z_to_bv 64 f)] F fc mm);
                   [clear - Kflo; lia| exact Kfhi| exact FL0| exact FLX| exact Klo| clear - Kroom Kdd; ul| reflexivity| clear - Kdd; ul| ul| clear - Kdd; ul
                   | exact ST| exact FR0| exact LOC| exact GAP| exact SAVED| exact LAST| exact FLAG| exact MI]|].
  cbv beta. intros ms3 (m3 & F3 & ya0 & -> & MU3 & WM3 & MI3 & ST3 & FLC3).
  destruct (REL m3 MU3 WM3 FLC3) as (ART3 & FRS3 & LV3 & SP3 & CR3 & AL3 & AM3).
  apply evt_done. apply (aevt_switch RT PMc Σ1 Σ2 K _ AL3 AM3).

  assert (NFL : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) p a -> ~ (fl <= a < fl + 1)).
  { intros a Ha Hin. replace a with fl in Ha by (clear - Hin; lia).
    destruct Ha as [H|[H|[H|[H|H]]]]; [clear - H FLX Kroom; lia| apply NAC..];
      [right; left; exact H| right; right; left; destruct H as (pp & nn & Hp & Hr); exists pp, nn; split; [apply ELi; exact Hp| exact Hr]
      | right; right; right; left; destruct H as (g & kg & Hg & Hr); exists g, kg; split; [rewrite EF; right; exact Hg| exact Hr]
      | right; right; right; right; destruct H as (g & kg & Hg & Hr); exists g, kg; split; [rewrite EF; right; exact Hg| exact Hr]]. }
  assert (AG3 : forall P : Z -> Prop, (forall y, P y -> aclient (rt_live RT Σ) (rt_frames RT Σ) p y) -> agree_on P mm m3)
    by (intros P HP a Ha; apply MU3; cbn [outside]; split; [exact (NFL _ (HP _ Ha))| exact Logic.I]).
  pose proof (u8arr_agree mm m3 _ _ NA ltac:(apply AG3; intros y Hy; rewrite NL in Hy; cbn in Hy; right; right; right; left; exists fN, kN; split; [exact INF| lia]) WM3) as NA3.
  apply (HK Σ2 n e _ _ _ ya0 _ _ _ _ _ _ _ _ _ _ _ F3 fc m3 nb FRM ART3 MI3 ST3).
  - rewrite LV3, EL; reflexivity.
  - exact FRS3.
  - rewrite SP3, ES; reflexivity.
  - rewrite CR3, EC; lia.
  - eapply pres_fp_trans; [exact (base_pres RT AF Σ Σ1 I OK EF EL ES LOR m0 mb mm B MU)|].
    intros a Ha _. apply MU3. cbn [outside]. split; [exact (NFL _ Ha)| exact Logic.I].
  - exact HN.
  - exact HE.
  - apply (rw_cells_agree bsegs mm m3 _ _ CEL); [| exact WM3]. apply AG3. intros y Hy. cbn [cells_size csize Nat.add] in Hy. left. ul.
  - exact NA3.
  - exact NL.
  - apply (bytes_at_agree bsegs mm m3 _ _ (base_nbsh RT Σ Σ1 I OK m0 mb mm B MU)). apply AG3. intros y Hy.
    rewrite repeat_length in Hy. unfold shad, SHB in Hy. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hy.
    right; right; right; right. exists fN, kN. split; [exact INF|].
    pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
    unfold shad, SHB. Z.div_mod_to_equations. lia.
Qed.

Lemma db_copyB : forall (F : bvmap 5 word) mb e, BASEI m0 mb -> SF_EMIN <= e <= SF_EMAX -> db_copy_k I mb Q e F fc.
Proof using AF RC FDO MST OK ESV EF EL ES EC INF NBF LOR HK FRM.
  intros F mb e B HE. unfold db_copy_k. intros until mm. intros TI HN.
  pose proof (base_art RT AF Σ Σ1 I fN kN OK EF ES INF NBF LOR m0 mb mm _ B TI) as ART1. pose proof (db_call_ok mb mm _ TI) as COK.
  pose proof (sh_run_zc I _ ltac:(destruct TI as (_ & _ & _ & _ & SHx & _); exact SHx)) as ZC.
  pose proof (inF1 RT Σ Σ1 I EF) as IN1. pose proof (inFN1 RT Σ Σ1 I fN kN EF INF) as IN2.
  assert (MUx : munch (db_W I) mb mm) by (destruct TI as (_ & _ & _ & _ & _ & _ & _ & _ & MU & _); exact MU).
  pose proof (base_nbsh RT Σ Σ1 I OK m0 mb mm B MUx) as SHN.
  pose proof TI as TI0. di_open TI. di_envX OK. pose proof (db_f8 I OK) as F8.
  pose proof (bytes_at_sub bsegs mm (f + 32) tmp (Z.to_nat (24 - n)) 16 (proj1 TA) ltac:(rewrite TL; lia)) as SRC.
  replace (f + 32 + Z.of_nat (Z.to_nat (24 - n))) with (f + 56 - n) in SRC by lia.
  assert (LS : length (firstn 16 (skipn (Z.to_nat (24 - n)) tmp)) = 16%nat) by (rewrite length_firstn, length_skipn, TL; lia).
  set (bs := firstn 16 (skipn (Z.to_nat (24 - n)) tmp)) in *. clearbody bs.
  assert (CS : checked_src RT Σ1 mm (Z_to_bv 64 b) lo (f + 56 - n) 16).
  { unfold checked_src. rewrite unsigned_lit by ul. split; [| left; lia]. intros _. split.
    - apply (acc_sub bsegs mm (f + 32) 40); [| lia| lia]. change 40 with (8 * Z.of_nat 5). apply acc_zero_run; [clear - F8; Z.div_mod_to_equations; lia| lia|].
      unfold shad, SHB. replace ((f + 32) / 8 + 2147450880) with (f / 8 + 2147450884) by (clear - F8; Z.div_mod_to_equations; lia).
      exact (zero_run_of_CB mm _ 5 ZC).
    - right; left. exists (d_f I), 1%nat. split; [exact IN1| rewrite fs1; lia]. }
  assert (CD : checked_dst RT Σ1 mm (Z_to_bv 64 b) (NB + sg) 16).
  { unfold checked_dst. rewrite unsigned_lit by ul. split; [| split].
    - intros _. split; [| right; left; exists fN, kN; split; [exact IN2| lia]].
      apply (acc_sub bsegs mm NB 40); [| lia| lia]. change 40 with (8 * Z.of_nat 5). apply acc_zero_run; [exact Knb8| lia| exact SHN].
    - intros i Hi. apply (dinv_client RT Σ Σ1 I fN kN OK EF INF NBF). lia.
    - destruct NA as [_ W40]. rewrite NL in W40. destruct W40 as (W0 & W1 & W). split; [lia|]. split; [lia|]. intros i Hi.
      replace (NB + sg + i) with (NB + (sg + i)) by lia. apply W. lia. }
  apply evt_done.
  eapply (aevt_memcpyP RT RC PMc FDO MST Σ1 K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm (NB + sg) (f + 56 - n) bs lo);
    [reflexivity| reflexivity| rewrite LS; reflexivity| ul| ul| rewrite LS; lia| exact SRC| rewrite LS; exact CS| rewrite LS; exact CD| rewrite LS; clear - Knbf Ksg HN; lia
    | exact ART1| exact MI| exact COK|].
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m3 RA3 PR3 BY3.
  rewrite unsigned_lit in RA3, PR3 by ul. rewrite LS in PR3. pose proof RA3 as (ART3 & _ & _ & _).
  assert (TI3 : DINV I sh_run m3 m3).
  { eapply (dinv_after_nb RT Σ Σ1 I fN kN OK EF INF NBF mb mm m3 sh_run (NB + sg) 16);
      [exact TI0| reflexivity| exact RA3| exact PR3| exact BY3| rewrite LS; reflexivity| lia| lia]. }
  assert (B3 : BASEI m0 m3).
  { eapply (base_after_call RT AF Σ Σ1 I fN kN OK EF EL ES INF NBF LOR m0 mb mm m3); [exact B| exact TI0| exact ART3| exact PR3| lia]. }
  rewrite (ret_pc_even 0xc0414) by lia.
  apply (aevt_evt RT AF PMc MST).
  eapply (db_fin I OK m3 Q e n HE HN (base_shpn RT Σ Σ1 I OK m0 m3 B3) (base_shpr RT AF Σ Σ1 I fN kN OK EF ES INF NBF LOR m0 m3 B3) F' fc (db_relB F' m3 e n B3 HE HN)).
  exact TI3.
Qed.
End Calls.

Local Ltac ul0 := unfold d_b, d_S, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, DBOX_STACK_B in *; lia.

Theorem dbox_okB : dbox_cpsB RT PMc.
Proof using AF RC SM1Z FDO MST.
  unfold dbox_cpsB.
  intros Σ K p lo NB sg fN kN ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nb c0 c1
         _ _ INF FLE FHI NB8 NA NL NBSH HSG CEL ART0 MI ST LOR ROOM PTOP P16 FRM FRT CR HK.
  pose proof (af_sp0_range RT AF Σ m ART0) as SPR. pose proof (af_sp0_win RT AF Σ m ART0) as SPW.
  pose proof (af_frames_range RT AF Σ m fN kN ART0 INF) as (FN0 & FN1 & _ & _).
  pose proof (af_frames_align RT AF Σ m fN kN ART0 INF) as (_ & FNLO).
  pose proof (proj2 (af_fshadow_apart RT AF Σ m fN kN ART0 INF) fN kN INF) as FNSH.
  assert (FSZ : 0 <= fs_size kN) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  unfold DBOX_STACK_B, RT_STACK in ROOM.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (db_pro1 p lo (NB + sg) ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ST);
                   [clear - ROOM; lia| clear - SPR LOR; ul0| exact PTOP| exact P16| exact (af_client_consts RT AF Σ m ART0)| exact MI]|].
  cbv beta. intros ms1 (m1 & dd & a1' & a2' & F1 & DD & B32 & -> & MU1 & WM1 & MI1 & ST1 & FS1). apply evt_done.
  set (b := p - 160 - dd) in *.
  assert (LB : lo + 65552 <= b) by (unfold b; clear - ROOM DD; lia).
  assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; clear - LB SPR LOR PTOP DD; ul0).
  assert (CSEP : forall sp a, aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> sp <= a \/ a < lo).
  { intros sp a Ha. destruct (aclient_split_c RT AF Σ m sp a ART0 Ha) as [H|H]; [left; exact H| right; clear - H LOR; lia]. }
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (p - 160) ART0); [clear - LOR ROOM; lia| | exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. intros Hin. apply Ha. left. clear - Hin PTOP. ul0. }
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) p (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. destruct (CSEP _ _ Ha); clear - H ROOM; lia. }
  destruct (stk_split bsegs m1 _ b _ ST1 ltac:(unfold b; clear - ROOM DD; lia)) as [ST1l ST1h].

  eapply (db_smalloc1z Σ K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F1 fc m1 lo);
    [reflexivity| clear - FRT; unfold FRAMES_MAX2, FRAMES_TOT in *; lia| exact CR| exact ART1| exact MI1| | intros HN; exfalso; rewrite HN in INF; exact INF |].
  { unfold call_ok. rewrite EU. split; [exact ST1l|]. split; [exact LOR|]. split; [clear - LB; unfold RT_STACK; lia|].
    split; [unfold b; clear - PTOP DD; ul0| clear - B32; unfold b; Z.div_mod_to_equations; lia]. }
  intros Σ1 f v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 v3 v4 v5 v6 F2 m2 (ART2 & MI2 & WM2 & ST2) PRES2 WRF WRS SHZ2 FRS1 LV1 SP1 CR1 F0 F64 FTOP.
  rewrite EU in ST2, PRES2. rewrite (ret_pc_even 0xc011c) by (clear; lia).
  rewrite fs1 in WRF, WRS, FTOP. change (128 - 8) with 120 in WRF. change (128 / 8) with 16 in WRS.

  assert (IN1 : In (f, 1%nat) (rt_frames RT Σ1)) by (rewrite FRS1; left; reflexivity).
  assert (INF1 : In (fN, kN) (rt_frames RT Σ1)) by (rewrite FRS1; right; exact INF).
  pose proof (af_frames_range RT AF Σ1 m2 f 1%nat ART2 IN1) as (_ & FR1 & _ & _). rewrite fs1, SP1 in FR1.
  assert (FLO : f + 128 <= lo) by (clear - FR1 LOR; lia).
  pose proof (af_frames_align RT AF Σ1 m2 f 1%nat ART2 IN1) as [_ FSEGf].
  pose proof (proj2 (af_fshadow_apart RT AF Σ1 m2 f 1%nat ART2 IN1) f 1%nat IN1) as FSH. rewrite fs1s, fs1 in FSH.
  pose proof (frames_sep RT AF Σ1 m2 f 1%nat (rt_frames RT Σ) NB 40 ART2 FRS1 NB8 ltac:(lia) eq_refl ltac:(exists fN, kN; split; [exact INF| lia])) as SEP.
  cbv zeta in SEP. rewrite fs1 in SEP. change (128 / 8) with 16 in SEP. change (40 / 8) with 5 in SEP. destruct SEP as (SQ1 & SQ2 & SQ3 & SQ4).
  assert (Ef : 8 * (f / 8) = f) by (clear - F64; Z.div_mod_to_equations; lia).
  assert (E128 : (f + 128) / 8 = f / 8 + 16) by (clear - Ef; Z.div_mod_to_equations; lia).
  assert (SFL : f / 8 + 2147450880 + 16 <= lo) by (clear - Ef FLO SPW LOR F0; ul0).
  set (I := mkDB p dd lo NB sg f gp [C8 (reg_get F 8); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  assert (OK : db_ok I).
  { subst I. constructor; cbn [d_p d_dd d_NB d_lo d_f d_sg d_sv d_b d_S]; unfold d_S, d_b; cbn [d_f d_p d_dd]; unfold shad, SHB in *.
    - exact DD.
    - clear - SPR LOR. ul0.
    - clear - ROOM. lia.
    - exact PTOP.
    - exact NB8.
    - clear - FNLO FLE. ul0.
    - clear - FN1 FHI LOR FSZ. lia.
    - exact HSG.
    - exact F64.
    - clear - FSEGf. ul0.
    - exact FLO.
    - clear - FSH. lia.
    - exact SFL.
    - clear - SQ1. lia.
    - clear - SQ2. lia.
    - clear - SQ3. lia.
    - clear - SQ4. lia.
    - assert ((NB + 40) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia| clear - FN1 FHI LOR SPR FSZ; ul0]).
      pose proof (Z.div_le_mono NB (NB + 40) 8 ltac:(lia) ltac:(lia)). clear - H H0 SPR LOR SPW. ul0.
    - pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
      destruct FNSH as [HS|HS]; [left| right]; Z.div_mod_to_equations; lia.
    - exact P16.
    - reflexivity. }

  assert (AG2 : forall P : Z -> Prop,
    (forall x, P x -> (b <= x < p + 16) \/ (NB <= x < NB + 40) \/ (NB / 8 + 2147450880 <= x < NB / 8 + 2147450880 + 5)) -> agree_on P m1 m2).
  { intros P HP a Ha. apply PRES2. destruct (HP _ Ha) as [H|[H|H]].
    - left. clear - H PTOP. ul0.
    - right; right; right; left. exists fN, kN. split; [exact INF| lia].
    - right; right; right; right. exists fN, kN. split; [exact INF|].
      pose proof (Z.div_le_mono fN NB 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_le_mono (NB + 48) (fN + fs_size kN) 8 ltac:(lia) ltac:(lia)).
      unfold shad, SHB. Z.div_mod_to_equations. lia. }
  assert (AG1 : forall P : Z -> Prop, (forall x, P x -> ~ (p - 160 <= x < p)) -> agree_on P m m1).
  { intros P HP a Ha. apply MU1. cbn [outside]. split; [| exact Logic.I]. apply HP. exact Ha. }
  assert (STb2 : stk bsegs m2 b (p - 112)) by (eapply stk_agree_nw; [exact ST1h|]; apply AG2; intros y Hy; left; clear - Hy; lia).
  pose proof (rw_cells_agree bsegs m1 m2 _ _ FS1 ltac:(apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; unfold b; clear - Hx DD; lia) WM2) as FS2.
  pose proof (u8arr_agree m m1 _ _ NA ltac:(apply AG1; intros x Hx; rewrite NL in Hx; cbn in Hx; clear - Hx FN1 FHI LOR ROOM; lia) WM1) as NA1.
  pose proof (u8arr_agree m1 m2 _ _ NA1 ltac:(apply AG2; intros x Hx; rewrite NL in Hx; cbn in Hx; right; left; lia) WM2) as NA2.
  pose proof (bytes_at_agree bsegs m m1 _ _ NBSH ltac:(apply AG1; intros x Hx; rewrite repeat_length in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
                assert ((NB + 40) / 8 <= 17592186044416) by (apply Z.div_le_upper_bound; [lia| clear - FN1 FHI LOR SPR FSZ; ul0]); unfold shad, SHB in Hx;
                clear - Hx H ROOM SPW LOR; ul0)) as NBSH1.
  pose proof (bytes_at_agree bsegs m1 m2 _ _ NBSH1 ltac:(apply AG2; intros x Hx; rewrite repeat_length in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx;
                unfold shad, SHB in Hx; right; right; lia)) as NBSH2.
  pose proof (rw_cells_agree bsegs m m1 _ _ CEL ltac:(apply AG1; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx; lia) WM1) as CEL1.
  pose proof (rw_cells_agree bsegs m1 m2 _ _ CEL1 ltac:(apply AG2; intros x Hx; cbn [cells_size csize Nat.add] in Hx; left; unfold b; clear - Hx DD; lia) WM2) as CEL2.
  assert (PRES2' : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) p (bv_unsigned a) -> m2 a = m a).
  { intros a Ha. rewrite <- (PRES1 a Ha). apply PRES2. eapply aclient_mono; [exact Ha| intros x Hx; exact Hx| intros x Hx; exact Hx| unfold b; clear - DD; lia]. }

  assert (FRESH : forall sp a, lo <= sp -> aclient (rt_live RT Σ) (rt_frames RT Σ) sp a -> ~ (f <= a < f + 128) /\ ~ (f / 8 + 2147450880 <= a < f / 8 + 2147450880 + 16)).
  { intros sp a Hsp Ha. pose proof (newframe_apartI RT AF Σ Σ1 m2 f 1%nat sp a ART2 FRS1 ltac:(rewrite LV1; intros x Hx; exact Hx) SP1 ltac:(clear - Hsp LOR; lia) Ha) as [N1 N2].
    rewrite fs1 in N1, N2. unfold shad, SHB in N2. rewrite E128 in N2. split; [exact N1| clear - N2; lia]. }

  destruct (wr_at_rw_CB m2 f 24 (wr_at_sub m2 f 120 f 24 WRF ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & FH2). change (Z.to_nat 24) with 24%nat in FH2.
  pose proof (wr_at_stk m2 (f + 24) 96 (wr_at_sub m2 f 120 (f + 24) 96 WRF ltac:(lia) ltac:(lia) ltac:(lia))) as F1S2.
  replace (f + 24 + 96) with (f + 120) in F1S2 by lia.
  unfold shad, SHB in SHZ2.
  clear PRES1 ST1 ST1l ST1h FS1 WM1 MI1 ART1 WRF WRS NA1 NBSH1 CEL1.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (db_pro2 p b f lo (NB + sg) gp v0 v1 v2 e1 e2 e3 e4 e5 e6 e7 s2 s6 s7 s8 s9 s11 v3 v4 v5 v6 jh F2 fc m2 F0 FLO SFL Ef);
                   [| clear - SPR LOR; ul0| clear - LB; lia| unfold b; clear - DD; lia| exact PTOP| exact STb2| exact FH2| exact F1S2| exact SHZ2| exact MI2]|].
  { destruct (FSH) as [H|H]; unfold shad, SHB in H; rewrite ?E128 in H; [left| right]; clear - H; lia. }
  cbv beta. intros ms3 (m3 & EX & a0' & a2'' & j24 & j32 & HEX & -> & MU3 & WM3 & MI3 & FR0w & FRw & GAPw & FHw & F1Sw & SHFw).

  assert (CL3 : forall y, (b + 24 <= y < b + 48) \/ (f <= y < f + 24) \/ (f / 8 + 2147450880 <= y < f / 8 + 2147450896) ->
                aclient (rt_live RT Σ1) (rt_frames RT Σ1) b y).
  { intros y [Hy|[Hy|Hy]].
    - left. clear - Hy PTOP LB DD. unfold b in *. ul0.
    - right; right; right; left. exists f, 1%nat. split; [exact IN1| rewrite fs1; clear - Hy; lia].
    - right; right; right; right. exists f, 1%nat. split; [exact IN1| unfold shad, SHB; rewrite fs1, E128; clear - Hy; lia]. }
  assert (ART3 : ART RT Σ1 m3).
  { apply (art_client_write RT AF Σ1 m2 m3 b ART2); [rewrite SP1; clear - LOR LB; lia| | exact WM3].
    intros a Ha. apply MU3. cbn [outside]. repeat split; try exact Logic.I; intros Hin; apply Ha; apply CL3; clear - Hin; lia. }
  assert (ST3 : stk bsegs m3 lo b).
  { eapply stk_agree_nw; [exact ST2|]. eapply agree_of_munch; [exact MU3|]. intros y Hy. cbv beta in Hy. cbn [outside]. clear - Hy FLO SFL. repeat split; try exact Logic.I; lia. }

  eapply evt_cut; [eapply (sf_okA RT AF Σ1); [exact ART3| exact MI3| exact HEX| exact ST3| clear - LB; lia| rewrite SP1; exact LOR| clear - PTOP DD; unfold b; ul0]|].
  cbv beta. intros ms4 (m4 & PO & MUk & WMk & MIk & STk & ARTk). unfold sf_postA1 in PO.
  destruct PO as (y0 & y1 & y2 & wd & q2 & q3 & q4 & q5 & q6 & q7 & y3 & y4 & y5 & y6 & e & -> & HE).
  rewrite (ret_pc_even 0xc01ec) by (clear; lia).

  assert (AG34 : forall P : Z -> Prop, (forall x, P x -> ~ (b - 16 <= x < b)) -> agree_on P m3 m4).
  { intros P HP a Ha. apply MUk. cbn [outside]. split; [| exact Logic.I]. apply HP. exact Ha. }
  assert (AG23 : forall P : Z -> Prop, (forall x, P x -> ~ (b + 24 <= x < b + 48) /\ ~ (f <= x < f + 24) /\ ~ (f / 8 + 2147450880 <= x < f / 8 + 2147450896)) -> agree_on P m2 m3).
  { intros P HP a Ha. apply MU3. destruct (HP _ Ha) as (H1 & H2 & H3). cbn [outside]. repeat split; try exact Logic.I; assumption. }
  pose proof (rw_cells_agree bsegs m3 m4 _ _ FRw ltac:(apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx; lia) WMk) as LOC4.
  pose proof (stk_agree_nw bsegs m3 m4 _ _ FR0w ltac:(apply AG34; intros x Hx; clear - Hx; lia)) as FR04.
  pose proof (stk_agree_nw bsegs m3 m4 _ _ GAPw ltac:(apply AG34; intros x Hx; clear - Hx; lia)) as GAP4.
  pose proof (rw_cells_agree bsegs m3 m4 _ _ FHw ltac:(apply AG34; intros x Hx; unfold db_hdr in Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO LB; lia) WMk) as HDR4.
  pose proof (stk_agree_nw bsegs m3 m4 _ _ F1Sw ltac:(apply AG34; intros x Hx; clear - Hx FLO LB; lia)) as F1S4.
  pose proof (rw_cells_agree bsegs m3 m4 _ _ SHFw ltac:(apply AG34; intros x Hx; unfold sh_pro in Hx; cbn [cells_size csize Nat.add pz] in Hx; clear - Hx SFL LB; lia) WMk) as SH4.
  pose proof (rw_cells_agree bsegs m2 m3 _ _ FS2 ltac:(apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold b; clear - Hx DD FLO SFL ROOM; repeat split; lia) WM3) as FS3.
  pose proof (rw_cells_agree bsegs m3 m4 _ _ FS3 ltac:(apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold b; clear - Hx DD; lia) WMk) as FS4.
  pose proof (u8arr_agree m2 m3 _ _ NA2 ltac:(apply AG23; intros x Hx; rewrite NL in Hx; cbn in Hx; clear - Hx SQ1 SQ2 FN1 FHI LOR LB FSZ; repeat split; lia) WM3) as NA3.
  pose proof (u8arr_agree m3 m4 _ _ NA3 ltac:(apply AG34; intros x Hx; rewrite NL in Hx; cbn in Hx; clear - Hx FN1 FHI LOR LB FSZ; lia) WMk) as NA4.
  pose proof (bytes_at_agree bsegs m2 m3 _ _ NBSH2 ltac:(apply AG23; intros x Hx; rewrite repeat_length in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; unfold shad, SHB in Hx;
                pose proof (k_Snhi I OK) as X1; pose proof (k_Snf I OK) as X2; pose proof (k_SnS I OK) as X3; unfold I in X1, X2, X3; cbn [d_NB d_lo d_f] in X1, X2, X3; unfold d_S, shad, SHB in X1, X2, X3; cbn [d_f] in X1, X2, X3;
                clear - Hx X1 X2 X3 LB; repeat split; lia)) as NBSH3.
  pose proof (bytes_at_agree bsegs m3 m4 _ _ NBSH3 ltac:(apply AG34; intros x Hx; rewrite repeat_length in Hx; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; unfold shad, SHB in Hx;
                pose proof (k_Snhi I OK) as X1; unfold I in X1; cbn [d_NB d_lo] in X1; unfold shad, SHB in X1; clear - Hx X1 LB; lia)) as NBSH4.
  pose proof (rw_cells_agree bsegs m2 m3 _ _ CEL2 ltac:(apply AG23; intros x Hx; cbn [cells_size csize Nat.add] in Hx; clear - Hx FLO SFL ROOM LB DD; unfold b; repeat split; lia) WM3) as CEL3.
  pose proof (rw_cells_agree bsegs m3 m4 _ _ CEL3 ltac:(apply AG34; intros x Hx; cbn [cells_size csize Nat.add] in Hx; unfold b; clear - Hx DD; lia) WMk) as CEL4.

  destruct (stk_split bsegs m4 _ (f + 32) _ F1S4 ltac:(lia)) as [_ F1Sa]. destruct (stk_split bsegs m4 _ (f + 72) _ F1Sa ltac:(lia)) as [TMPs _].
  destruct (stk_CB bsegs m4 _ _ TMPs ltac:(lia)) as (tmp & TMPc). replace (Z.to_nat (f + 72 - (f + 32))) with 40%nat in TMPc by lia.
  pose proof (u8arr_of_rw_cells bsegs m4 _ _ _ TMPc) as TA4.
  assert (TL4 : length tmp = 40%nat) by (destruct TMPc as [[W _] _]; cbn in W; destruct W as [W _]; exact W).

  assert (B4 : BASE RT Σ Σ1 I m m4).
  { split; [exact ARTk|]. split; [| exact NBSH4].
    subst I. cbn [d_p d_NB]. intros a Ha Ho.
    rewrite (MUk a), (MU3 a), (PRES2' a Ha); [reflexivity| | ].
    - destruct (FRESH p _ ltac:(clear - ROOM; lia) Ha) as [N1 N2]. destruct (CSEP _ _ Ha) as [H|H]; cbn [outside]; unfold b; clear - H N1 N2 ROOM DD; repeat split; try exact Logic.I; lia.
    - destruct (CSEP _ _ Ha) as [H|H]; cbn [outside]; unfold b; clear - H ROOM DD; (split; [lia| exact Logic.I]). }

  eapply evt_eq; [| eapply (db_dig I OK m4 (fun ms => aevt RT PMc Σ1 K ms) e (base_shpn RT Σ Σ1 I OK m m4 B4) (base_shpd RT AF Σ Σ1 I fN kN OK FRS1 SP1 INF (conj FLE FHI) LOR m m4 B4) F2 fc
              (db_copyB Σ Σ1 I fN kN K m (reg_get F 8) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc OK eq_refl FRS1 LV1 SP1 CR1 INF (conj FLE FHI) LOR FRM HK F2 m4 e B4 HE)
              wd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j24 j32 _ _ _ tmp nb c0 c1 m4)].
  { subst I. unfold d_b, d_S. cbn [d_p d_dd d_gp d_f d_NB d_sg]. reflexivity. }
  all: subst I; unfold d_b, d_S; cbn [d_p d_dd d_gp d_f d_NB d_sg d_lo d_sv].
  - exact LOC4.
  - exact FS4.
  - exact HDR4.
  - exact TA4.
  - exact TL4.
  - exact SH4.
  - exact NA4.
  - exact NL.
  - exact CEL4.
  - exact MIk.
  - apply munch_refl.
  - apply wmono_refl.
  - exact STk.
  - exact FR04.
  - exact GAP4.
Qed.
End DBC.
