(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_tables Atp_fzwA Atp_activewA Atp_defsA Atp_kitA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA El_esc_ifaceA El_dump_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Ltac ls := lstep; try sb_fix.

Record ectx : Type := mkEC {
  e_q : Z; e_lo : Z; e_F : Z; e_f0 : Z; e_L : list (Z * Z); e_rfr : list (Z * nat); e_sp0 : Z; e_cr : Z; e_m0 : mem;
  e_SV : Z; e_P : Z; e_bs : list byte; e_p : Z; e_n8 : Z;
  e_gp : word; e_ra : word; e_s0 : word; e_s1 : word; e_s2 : word; e_s3 : word; e_s4 : word; e_s5 : word; e_s6 : word;
  e_s7 : word; e_s8 : word; e_s9 : word; e_s10 : word; e_s11 : word; e_j : list (list byte) }.
Definition e_G (E : ectx) : gctx :=
  mkG (e_q E - 192) 192 (e_lo E) (e_F E) (e_f0 E) 0%nat (e_rfr E) (e_L E) (e_sp0 E) (e_cr E) (e_m0 E).
Notation esp E := (e_q E - 192).
Notation eOS E := (e_F E + 144).
Notation eL E := (Z.of_nat (length (e_bs E))).
Definition EJ (E : ectx) (k : nat) : cell := CB 8 (nth k (e_j E) []).
Definition esaves (E : ectx) : list cell :=
  fa_saved (e_ra E) (e_s0 E) (e_s1 E) (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E).

Definition efr0 (E : ectx) : list cell :=
  [C8 (wz 0); EJ E 0; EJ E 1; EJ E 2; EJ E 3; EJ E 4; EJ E 5; EJ E 6; EJ E 7; EJ E 8; EJ E 9] ++ esaves E.

Definition efr1 (E : ectx) : list cell :=
  [C8 (wz 0); EJ E 0; C8 (wz (e_f0 E)); EJ E 2; EJ E 3; EJ E 4; EJ E 5; EJ E 6; EJ E 7; C8 (wz (e_f0 E)); EJ E 9] ++ esaves E.

Definition efrL (E : ectx) (w : list byte) : list cell :=
  [C8 (wz 0); EJ E 0; C8 (wz (e_f0 E)); C8 (wz 0x23b00); C8 (wz (e_f0 E + 32)); C8 (wz 0x235c0); C8 (wz 0x235a0); C8 (wz (shad (eOS E + 128))); EJ E 7; C8 (wz (e_f0 E)); CB 8 w]
  ++ esaves E.
Lemma esaves_size : forall E, cells_size (esaves E) = 104%nat. Proof. intros; reflexivity. Qed.
Lemma efr0_size : forall E, cells_size (efr0 E) = 192%nat. Proof. intros; reflexivity. Qed.
Lemma efr1_size : forall E, cells_size (efr1 E) = 192%nat. Proof. intros; reflexivity. Qed.
Lemma efrL_size : forall E w, cells_size (efrL E w) = 192%nat. Proof. intros; reflexivity. Qed.

Definition ectx_ok (E : ectx) : Prop :=
  gctx_ok (e_G E)
  /\ (e_q E <= e_SV E /\ e_SV E + 16 <= USTACK_TOP - 16 /\ e_SV E mod 8 = 0)
  /\ (In (e_p E, e_n8 E) (e_L E) /\ e_p E mod 8 = 0 /\ e_n8 E mod 8 = 0 /\ e_p E <= e_P E /\ e_P E + eL E <= e_p E + e_n8 E /\ 0 < e_p E /\ e_p E + e_n8 E <= e_lo E
      /\ (e_p E + e_n8 E <= 0x10000 \/ SEGTOP_A <= e_p E))
  /\ io_ssp (e_m0 E) /\ length (e_j E) = 10%nat /\ e_lo E + EL_ESC_STACK_A <= e_q E.

Lemma e_walk0 : forall (q lo OSP SV : Z) (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo q -> lo <= q - 192 -> 0x6ce000 <= lo -> q < 2^63 -> q mod 32 = 0 -> 0 <= OSP < 2^64 -> 0 <= SV < 2^64 ->
  client_consts m -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) (a1' : word) (js : list (list byte)),
      ms = entry_st (wz 0xb0e14) (wz (q - 192)) gp (wz TPV_A) t0 t1 t2 (wz q) (wz (q - 192)) (wz 64) a1' (wz 1) a3 a4 a5 a6 a7
                    (wz OSP) (wz SV) s4 s5 s6 s7 s8 s9 (wz SHB) s11 t3 t4 t5 t6 F fc (e_stack_malloc 0) m1
      /\ munch [(q - 192, q)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (q - 192)
      /\ rw_cells bsegs m1 (q - 192) ([C8 (wz 0); CB 8 (nth 0 js []); CB 8 (nth 1 js []); CB 8 (nth 2 js []); CB 8 (nth 3 js []); CB 8 (nth 4 js []); CB 8 (nth 5 js []);
            CB 8 (nth 6 js []); CB 8 (nth 7 js []); CB 8 (nth 8 js []); CB 8 (nth 9 js [])] ++ fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\ length js = 10%nat)
    (MS (mkR ra (wz q) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz OSP) (wz SV) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0xb0da0) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros ST LO GLO SPH S32 OR SVR (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, e_stack_malloc, fa_saved.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 192, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 192%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 192 _ [] (repeat 8%nat 24)) in FR; [| reflexivity].
  cbn [repeat mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  do 14 lstep. zstep. zstep.
  rewrite (land_m32 (q + -192)) by lia.
  replace (32 * ((q + -192) / 32)) with (q + -192) by (Z.div_mod_to_equations; lia).
  do 6 zstep. step. rewrite (sx32_small 1) by lia. zstep. zstep. zstep. if_false. zstep. zstep.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?rest) =>
    change (c0 :: rest) with ((c0 :: firstn 10 rest) ++ skipn 10 rest) in FR end.
  cbn [firstn skipn] in FR. replace (q + -192) with (q - 192) in * by lia.
  apply evt_done.
  lazymatch type of FR with rw_cells _ _ _ ((_ :: CB 8 ?x0 :: CB 8 ?x1 :: CB 8 ?x2 :: CB 8 ?x3 :: CB 8 ?x4 :: CB 8 ?x5 :: CB 8 ?x6 :: CB 8 ?x7 :: CB 8 ?x8 :: CB 8 ?x9
                                 :: _) ++ _) =>
    exists m1; eexists _; exists [x0; x1; x2; x3; x4; x5; x6; x7; x8; x9] end.
  cbn [nth]. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FR| reflexivity].
Qed.

Lemma e_walk1 : forall (E : ectx) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < e_f0 E -> e_f0 E + 64 <= esp E -> e_f0 E mod 8 = 0 -> 0 <= e_SV E -> e_SV E + 16 < 2^63 ->
  shad (e_f0 E) + 8 <= esp E -> (e_f0 E + 64 <= shad (e_f0 E) \/ shad (e_f0 E) + 8 <= e_f0 E) ->
  rw_cells bsegs m (esp E) (efr0 E) -> wr_at bsegs m (e_f0 E) 56 -> wr_at bsegs m (shad (e_f0 E)) 8 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb0e14) (wz (esp E)) (e_gp E) (wz TPV_A) t0 t1 t2 (wz (e_q E)) (wz (esp E)) (wz 0x41b58ab3) (wz 0x21c61) (wz 0xb0da0) (wz (-13)) (wz (-8)) (wz (-15)) a6 a7
                   (wz (eOS E + 128)) (wz (e_SV E)) s4 (wz (e_SV E + 8)) s6 (wz (shad (e_SV E + 8))) s8 (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) t3 t4 t5 t6)
              F (wz 0xb0ea8) fc None m1 (seg_rom bsegs)
      /\ munch [(esp E + 16, esp E + 24); (e_f0 E, e_f0 E + 24); (shad (e_f0 E), shad (e_f0 E) + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (esp E) ([C8 (wz 0); EJ E 0; C8 (wz (e_f0 E)); EJ E 2; EJ E 3; EJ E 4; EJ E 5; EJ E 6; EJ E 7; EJ E 8; EJ E 9] ++ esaves E))
    (MS (mkR (wz 0xb0e14) (wz (esp E)) (e_gp E) (wz TPV_A) t0 t1 t2 (wz (e_q E)) (wz (esp E)) (wz (e_f0 E)) a1 a2 a3 a4 a5 a6 a7
             (wz (eOS E + 128)) (wz (e_SV E)) s4 s5 s6 s7 s8 s9 (wz SHB) s11 t3 t4 t5 t6)
        F (ret_pc (wz 0xb0e14)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Q0 QH F0 FH F8 SV0 SVH SH1 SH2 FR WF1 WS1 MI.
  destruct E as [q lo Fr f0 L rfr sp0 cr m0 SV P bs p n8 gp xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 js].
  cbn [e_q e_lo e_F e_f0 e_L e_rfr e_sp0 e_cr e_m0 e_SV e_P e_bs e_p e_n8 e_gp e_ra e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_j] in *.
  unfold efr0, esaves, EJ, fa_saved, shad, SHB in *. cbn [e_j e_ra e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 map app nth] in *.
  rewrite (ret_pc_even 0xb0e14) by lia.
  set (qq := q - 192) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f0) = f0) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f0 / 8 + 2147450880)) = f0 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  destruct (wr_at_rw_CB m f0 24 (wr_at_sub m f0 56 f0 24 WF1 ltac:(lia) ltac:(lia) ltac:(lia)) ltac:(lia)) as (jh & FH1).
  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [8; 8; 8]%nat) in FH1; [| reflexivity]. cbn [mk_CB_cells app] in FH1.
  destruct (wr_at_rw_CB m _ 8 WS1 ltac:(lia)) as (jsx & FS1).
  apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] (repeat 1%nat 8)) in FS1; [| reflexivity]. cbn [repeat mk_CB_cells app] in FS1.

  zstep. zstep. zstep. if_true. lstep.

  zstep. zstep. zstep. astep. zstep. zstep. zstep. zstep. zstep. zstep.

  lstep. lstep. lstep.

  zstep. zstep. do 4 ls. astep. do 4 ls. zstep.
  apply evt_done. exists m2. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|]. split; [exact WM|]. split; [assumption| exact FR].
Qed.

Ltac prepE E :=
  destruct E as [q lo Fr f0 L rfr sp0 cr m0 SV P bs p n8 gp xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 js];
  unfold e_G, efr0, efr1, efrL, esaves, EJ, fa_saved, shad, SHB in *;
  cbn [e_q e_lo e_F e_f0 e_L e_rfr e_sp0 e_cr e_m0 e_SV e_P e_bs e_p e_n8 e_gp e_ra e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 e_j map app nth
       g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in *.

Lemma e_walk2 : forall (E : ectx) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < e_f0 E -> e_f0 E + 64 < 2^63 -> e_q E <= e_SV E -> e_SV E + 16 < 2^63 -> 0 <= eL E < 2^63 ->
  rw_cells bsegs m (esp E) ([C8 (wz 0); EJ E 0; C8 (wz (e_f0 E)); EJ E 2; EJ E 3; EJ E 4; EJ E 5; EJ E 6; EJ E 7; EJ E 8; EJ E 9] ++ esaves E) ->
  rw_cells bsegs m (e_SV E) [C8 (wz (e_P E)); C8 (wz (eL E))] -> shz m (e_SV E) 16 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (wz 0xb0e14) (wz (esp E)) (e_gp E) (wz TPV_A) t0 t1 t2 (wz (e_q E)) (wz (esp E)) (wz (eL E)) a1 a2 a3 a4 a5 a6 a7
                   (wz (eOS E + 128)) (wz (e_SV E)) s4 (wz (e_SV E + 8)) s6 (wz (shad (e_SV E + 8))) s8 (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) t3 t4 t5 t6)
              F (wz (if eL E =? 0 then 0xb1204 else 0xb0ebc)) fc None m1 (seg_rom bsegs)
      /\ munch [(esp E + 72, esp E + 80)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 (esp E) (efr1 E))
    (MS (mkR (wz 0xb0e14) (wz (esp E)) (e_gp E) (wz TPV_A) t0 t1 t2 (wz (e_q E)) (wz (esp E)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (eOS E + 128)) (wz (e_SV E)) s4 (wz (e_SV E + 8)) s6 (wz (shad (e_SV E + 8))) s8 (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) t3 t4 t5 t6)
        F (wz 0xb0ea8) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Q0 QH F0 FH QSV SVH LR FR SVC SHZ MI. prepE E.
  set (qq := q - 192) in *. set (Ln := Z.of_nat (length bs)) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  assert (EV : bv_unsigned (wz SV) = SV) by (apply unsigned_lit; lia).

  shz_pose SHZ (SV + 8). zstep. shz_norm. lstep. zstep. if_false.

  zstep. zstep.
  if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia;
    [rewrite (proj2 (Z.eqb_eq _ _) KB)| rewrite (proj2 (Z.eqb_neq _ _) KB)];
    (apply evt_done; eexists; split; [atp_st_eq_goal|];
     split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|]; split; [exact WM|]; split; [assumption| exact FR]).
Qed.

Lemma e_walk3 : forall (E : ectx) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s8 t3 t4 t5 t6 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < e_f0 E -> e_f0 E + 64 < 2^63 -> e_q E <= e_SV E -> e_SV E + 16 < 2^63 -> 0 < e_F E -> e_F E + 512 < 2^63 ->
  rw_cells bsegs m (esp E) (efr1 E) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) a0' a1' a2' a3',
      ms = MS (mkR (wz 0xb0e14) (wz (esp E)) (e_gp E) (wz TPV_A) t0 t1 t2 (wz (e_q E)) (wz (esp E)) a0' a1' a2' a3' a4 a5 a6 a7
                   (wz (eOS E + 128)) (wz (e_SV E)) (wz (shad (e_SV E))) (wz (e_SV E + 8)) (wz 5) (wz (shad (e_SV E + 8))) (wz 0) (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) t3 t4 t5 t6)
              F (wz 0xb0f04) fc None m1 (seg_rom bsegs)
      /\ munch [(esp E + 24, esp E + 64)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 (esp E) (efrL E (nth 9 (e_j E) [])))
    (MS (mkR (wz 0xb0e14) (wz (esp E)) (e_gp E) (wz TPV_A) t0 t1 t2 (wz (e_q E)) (wz (esp E)) a0 a1 a2 a3 a4 a5 a6 a7
             (wz (eOS E + 128)) (wz (e_SV E)) s4 (wz (e_SV E + 8)) s6 (wz (shad (e_SV E + 8))) s8 (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) t3 t4 t5 t6)
        F (wz 0xb0ebc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Q0 QH F0 FH QSV SVH E0 EH FR MI. prepE E.
  set (qq := q - 192) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).

  zstep. zstep. lstep. astep. zstep. zstep. zstep. astep. zstep. zstep.

  zstep. lstep. zstep. lstep. zstep. lstep. zstep. lstep.
  rewrite ?shr3_div in FR |- * by lia.
  apply evt_done. eexists m1, _, _, _, _. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|]. split; [exact WM|]. split; [assumption|].
  replace (Fr + 144 + 128) with (Fr + 272) by lia. exact FR.
Qed.

Definition EJT : Z := 0x2355c.
Definition EJT_TAB : list Z := [580104; 580568; 580580; 580148; 580592; 580604].
Definition ejt (i : Z) : Z := nth (Z.to_nat i) EJT_TAB 0.
Definition EJT_WORDS : list word := map (Z_to_bv 64) EJT_TAB.
Lemma ejt_image : ro_bytes_b bsegs EJT (u32s EJT_WORDS) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ejt_at : forall m, mem_inv bsegs m -> bytes_at bsegs m EJT (u32s EJT_WORDS).
Proof.
  intros m MI. apply ro_bytes_at; [exact MI| unfold EJT; lia | rewrite u32s_length; unfold EJT, EJT_WORDS; rewrite length_map; cbn; lia |].
  apply ro_bytes_b_sound. exact ejt_image.
Qed.
Lemma ejt_read : forall (m : word -> option byte) i a, mem_inv bsegs m -> 0 <= i < 6 -> a = wa (EJT + 4 * i) ->
  ov_read_bytes bsegs m a 4 = Some (le4 (Z_to_bv 64 (ejt i))).
Proof.
  intros m i a MI Hi ->. eapply (u32ro_read m EJT EJT_WORDS i); [apply ejt_at; exact MI| | lia | reflexivity].
  unfold EJT_WORDS, ejt. rewrite nth_error_map. rewrite (nth_error_nth' EJT_TAB 0); [reflexivity|].
  change (length EJT_TAB) with 6%nat. lia.
Qed.

Definition elit (c : Z) : Z :=
  if c =? 8 then 0x23a60 else if c =? 9 then 0x23ae0 else if c =? 10 then 0x23aa0 else if c =? 12 then 0x23a80 else if c =? 13 then 0x23ac0
  else if c =? 34 then 0x235a0 else 0x235c0.
Definition is_elit (c : Z) : Prop := c = 8 \/ c = 9 \/ c = 10 \/ c = 12 \/ c = 13 \/ c = 34 \/ c = 92.

Lemma shz_munch : forall m m' W0 a n, shz m a n -> munch W0 m m' -> 0 <= a -> a + n <= 2^62 ->
  (forall x, a <= x < a + n -> outside W0 (x / 8 + 2147450880)) -> shz m' a n.
Proof.
  intros m m' W0 a n SH MU A0 AN HW x Hx. unfold shz in SH. specialize (SH x Hx). specialize (HW x Hx).
  cbn [ov_read_bytes] in SH |- *.
  assert (E1 : m' (wa (x / 8 + 2147450880)) = m (wa (x / 8 + 2147450880))).
  { apply MU. unfold wa. rewrite unsigned_lit; [exact HW|]. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
  rewrite E1. exact SH.
Qed.

Lemma shad_off : forall x, 0 <= x < 2^47 -> 2147450880 <= x / 8 + 2147450880 < 0x10007fff8000.
Proof. intros x Hx. Z.div_mod_to_equations. lia. Qed.

Section Esc.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis PUT : os_put_cpsA RT PMc.
Hypothesis SETF : setfill_cpsA RT PMc.
Hypothesis INSI : ins_i_cpsA RT PMc.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.
Variable E : ectx.
Hypothesis EOK : ectx_ok E.

Hypothesis SVC0 : rw_cells bsegs (e_m0 E) (e_SV E) [C8 (wz (e_P E)); C8 (wz (eL E))].
Hypothesis PB0 : bytes_at bsegs (e_m0 E) (e_P E) (e_bs E).

Local Ltac ul := unfold EL_ESC_STACK_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_SETFILL_STACK_A, FUZZ_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Notation GI := (GINVA RT (e_G E)).
Local Ltac facts EOK :=
  pose proof EOK as (GOK & (QSV & SVT & SV8) & (INP & P8 & N8 & PP & PL & P0 & PLO & PSEG) & IOS0 & LJ & NEED);
  pose proof GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL];
  cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in *; change (fs_size 0) with 64 in *; change (64 / 8) with 8 in *.

Lemma efacts : forall FL W FP fcs k Σ m, GI FL W FP fcs k Σ m ->
  rw_cells bsegs m (e_SV E) [C8 (wz (e_P E)); C8 (wz (eL E))] /\ bytes_at bsegs m (e_P E) (e_bs E)
  /\ shz m (e_SV E) 16 /\ shz m (e_p E) (e_n8 E) /\ shz m 0x168e08 24 /\ shz m (eOS E) 288 /\ el_dccA m /\ io_ssp m.
Proof using AF EOK SVC0 PB0 DCC.
  intros FL W FP fcs k Σ m GIm. facts EOK.
  pose proof GIm as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
  cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in HA, FRS, LV, SP0, CR, ST, SHO, FR, REL.
  pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.
  assert (AGS : forall P : Z -> Prop, (forall x, P x -> (e_q E <= x < USTACK_TOP) \/ (e_p E <= x < e_p E + e_n8 E)) -> agree_on P (e_m0 E) m).
  { intros Q HQ a Ha. apply REL.
    - destruct (HQ _ Ha) as [X|X]; [left; replace (e_q E - 192 + 192) with (e_q E) by lia; exact X| right; right; left; exists (e_p E), (e_n8 E); split; [exact INP| exact X]].
    - unfold WD, EL_TPLOC_A, TPV_A. cbn [outside]. pose proof (RFR _ _ EIN) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (B6 _ _ INP) as [C1 _]. change (fs_size 3) with 512 in C1, B3.
      destruct (HQ _ Ha) as [X|X]; (repeat split; try exact I); clear - X C1 B2 B3 ESEG ELO LQ PSEG PLO LO1; ul. }
  split. { apply (rw_cells_agree_nw bsegs (e_m0 E) m _ _ SVC0). apply AGS. intros x Hx. cbn [cells_size csize Nat.add] in Hx. left. clear - Hx QSV SVT. ul. }
  split. { apply (bytes_at_agree bsegs (e_m0 E) m _ _ PB0). apply AGS. intros x Hx. right. clear - Hx PP PL. lia. }
  split. { apply (shz_stack RT AF Σ m (e_SV E) 16 HA); [rewrite SP0; clear - LO2 LQ QSV; ul| clear - SVT; ul| exact SV8| reflexivity| lia]. }
  split. { pose proof (shz_live RT AF Σ m _ _ HA ltac:(rewrite LV; exact INP) P8) as X. replace (8 * (e_n8 E / 8)) with (e_n8 E) in X by (clear - N8; Z.div_mod_to_equations; lia). exact X. }
  split. { pose proof (shz_of_acc m 0x168e08 24 (acc_lit RT AF Σ m 0x168e08 24 HA ltac:(clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right]))) eq_refl ltac:(clear; lia)) as X. exact X. }
  split. { pose proof (shz_of_zero_run m (eOS E) 36 ltac:(clear - E64; Z.div_mod_to_equations; lia) ltac:(clear - E0; lia) SHO) as X. exact X. }
  split; [exact (DCC Σ m HA)| exact (GINVA_iossp RT AF (e_G E) GOK _ _ _ _ _ _ _ IOS0 GIm)].
Qed.

Lemma GINVA_restream : forall FL W FP FL' W' (FP' : Z -> Prop) fcs k Σ m m' fill,
  GI FL W FP fcs k Σ m -> munch [(eOS E + 136, eOS E + 168)] m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  OSXW m' (eOS E) FL' W' fill -> FP' fill -> GI FL' W' FP' fcs k Σ m'.
Proof using AF EOK.
  intros FL W FP FL' W' FP' fcs k Σ m m' fill GIm MU WM MI' OX' FOK'. facts EOK.
  destruct GIm as (HA & MI & FRS & LV & SP0 & CR & ST & _ & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
  cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in HA, FRS, LV, SP0, CR, ST, SHO, FR, FSZ, WF1, WF2, REL |- *.
  change (fs_size 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.
  assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ (eOS E + 136 <= x < eOS E + 168)) -> agree_on P m m').
  { intros P HP a Ha. apply MU. cbn [outside]. split; [exact (HP _ Ha)| exact I]. }
  split. { apply (art_client_write RT AF Σ m m' (e_q E - 192) HA); [rewrite SP0; clear - LO2 LQ; ul| | exact WM].
           intros a Ha. apply MU. cbn [outside]. split; [| exact I]. intros X. apply Ha. rewrite FRS. right; right; right; left.
           exists (e_F E), 3%nat. split; [right; exact EIN| change (fs_size 3) with 512; clear - X; lia]. }
  split; [exact MI'|]. split; [exact FRS|]. split; [exact LV|]. split; [exact SP0|]. split; [exact CR|].
  split. { apply (stk_agree bsegs m m' _ _ ST); [| exact WM]. apply AG. intros x Hx. clear - Hx ELO LQ. ul. }
  split. { exists fill. split; [exact OX'| exact FOK']. }
  split. { apply (bytes_at_agree bsegs m m' _ _ SHO). apply AG. intros x Hx. rewrite repeat_length in Hx. unfold shad in *. clear - Hx ESH E0. lia. }
  split. { apply (rw_cells_agree_nw bsegs m m' _ _ TPL). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx ESEG. ul. }
  split. { apply (LOCBA_agree m m' LB). apply AG. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. clear - Hx ESEG. ul. }
  split. { split; [| exact FSZ]. apply (rw_cells_agree_nw bsegs m m' _ _ FR). apply AG. intros x Hx. rewrite FSZ in Hx. clear - Hx ELO LQ. ul. }
  split. { apply (wr_at_agree_nw bsegs m m' _ _ WF1). apply AG. intros x Hx. clear - Hx A1. lia. }
  split. { apply (wr_at_agree_nw bsegs m m' _ _ WF2). apply AG. intros x Hx. clear - Hx A2. lia. }
  intros a CA OU. etransitivity; [| exact (REL a CA OU)]. apply MU. unfold WD in OU. cbn [outside e_G g_F] in OU |- *. split; [| exact I]. clear - OU. lia.
Qed.

Definition ELSTA (pc i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR x1 (wz (esp E)) (e_gp E) (wz TPV_A) x5 x6 x7 (wz (e_q E)) (wz (esp E)) x10 x11 x12 x13 x14 x15 x16 x17
          (wz (eOS E + 128)) (wz (e_SV E)) (wz (shad (e_SV E))) (wz (e_SV E + 8)) (wz 5) (wz (shad (e_SV E + 8))) (wz i) (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) x28 x29 x30 x31)
     F (wz pc) fc None m (seg_rom bsegs).

Definition EKLOOPA (K : config -> Prop) (j : Z) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (w : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    GI 0x1002 0 FILLOK (efrL E w) k Σ m -> frm0 fc -> 0 <= k -> k <= 1 + 4 * j ->
    aevt RT PMc Σ K (ELSTA 0xb0f04 j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).

Definition EEXITA (K : config -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (j1 : list byte) (mid : list cell) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    GI 0x1002 0 FILLOK (C8 (wz 0) :: CB 8 j1 :: C8 (wz (e_f0 E)) :: mid ++ esaves E) k Σ m -> cells_size mid = 64%nat -> frm0 fc -> 0 <= k -> k <= 1 + 4 * eL E ->
    aevt RT PMc Σ K (MS (mkR x1 (wz (esp E)) (e_gp E) (wz TPV_A) x5 x6 x7 (wz (e_q E)) (wz (esp E)) x10 x11 x12 x13 x14 x15 x16 x17
                             (wz (eOS E + 128)) (wz (e_SV E)) x20 (wz (e_SV E + 8)) x22 (wz (shad (e_SV E + 8))) x24 (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) x28 x29 x30 x31)
                        F (wz 0xb1204) fc None m (seg_rom bsegs)).

Lemma w_ch : forall (i c : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  e_q E <= e_SV E -> e_SV E + 16 < 2^63 -> 0 < e_P E -> e_P E + eL E < 2^63 -> e_p E <= e_P E -> e_P E + eL E <= e_p E + e_n8 E -> 0 <= i < eL E ->
  firstn 1 (skipn (Z.to_nat i) (e_bs E)) = [Z_to_bv 8 c] -> 0 <= c < 256 ->
  rw_cells bsegs m (e_SV E) [C8 (wz (e_P E)); C8 (wz (eL E))] -> bytes_at bsegs m (e_P E) (e_bs E) -> shz m (e_SV E) 16 -> shz m (e_p E) (e_n8 E) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists x11' x13', ms = ELSTA 0xb0f44 i x1 x5 x6 x7 (wz (e_P E + i)) x11' (wz (c - 8)) x13' (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m)
    (ELSTA 0xb0f04 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros QSV SVH P0 PH PP PL Hi BI Hc SVC PB SHV SHP MI. unfold ELSTA. prepE E.
  set (qq := q - 192) in *. set (Ln := Z.of_nat (length bs)) in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bytes_at_ov_read bsegs m P bs (Z.to_nat i) 1 PB ltac:(lia)) as RD. rewrite BI, Z2Nat.id in RD by lia.
  shz_pose SHV SV. zstep. shz_norm. zstep. if_false.
  zstep. zstep.

  step. if_dead1 by P0 PH Hi. astep. astep.
  replace (0 <? P) with true by (symmetry; apply Z.ltb_lt; lia). replace (P + i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  astep. step. if_false. step. if_dead1 by P0.
  chk0 SHP (P + i). zstep. if_false.
  zstep. zstep.
  rewrite (a_u8_small c) by lia. replace (c + -8) with (c - 8) by lia.
  apply evt_done. do 2 eexists. atp_st_eq_goal.
Qed.

Lemma w_lit : forall (i c : Z) (w : list byte) (x1 x5 x6 x7 x11 x13 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> is_elit c -> rw_cells bsegs m (esp E) (efrL E w) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists x13' x14', ms = ELSTA EL_OSPUT i (wz 0xb116c) x5 x6 x7 (wz (eOS E + 128)) (wz (elit c)) (wz 2) x13' x14' x15 x16 x17 x28 x29 x30 x31 F fc m)
    (ELSTA 0xb0f44 i x1 x5 x6 x7 (wz (e_P E + i)) x11 (wz (c - 8)) x13 (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH HC FR MI. unfold ELSTA. prepE E.
  set (qq := q - 192) in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  destruct HC as [-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]; unfold elit; cbn [Z.eqb Pos.eqb Z.sub Z.add Z.pos_sub].
  -
    zstep. if_false. astep. zstep. zstep. astep.
    pose proof (ejt_read m 0 _ MI ltac:(lia) eq_refl) as JR; cbn [ejt nth Z.to_nat EJT_TAB] in JR.
    lazymatch type of JR with ov_read_bytes _ _ (wa ?a) _ = Some ?r => let r' := eval vm_compute in r in change r with r' in JR; let a' := eval vm_compute in a in change a with a' in JR end.
    step. astep. step.
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
  - zstep. if_false. astep. zstep. zstep. astep.
    pose proof (ejt_read m 1 _ MI ltac:(lia) eq_refl) as JR; cbn [ejt nth Z.to_nat EJT_TAB Pos.to_nat Pos.iter_op Nat.add] in JR.
    lazymatch type of JR with ov_read_bytes _ _ (wa ?a) _ = Some ?r => let r' := eval vm_compute in r in change r with r' in JR; let a' := eval vm_compute in a in change a with a' in JR end.
    step. astep. step.
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
  - zstep. if_false. astep. zstep. zstep. astep.
    pose proof (ejt_read m 2 _ MI ltac:(lia) eq_refl) as JR; cbn [ejt nth Z.to_nat EJT_TAB Pos.to_nat Pos.iter_op Nat.add] in JR.
    lazymatch type of JR with ov_read_bytes _ _ (wa ?a) _ = Some ?r => let r' := eval vm_compute in r in change r with r' in JR; let a' := eval vm_compute in a in change a with a' in JR end.
    step. astep. step.
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
  - zstep. if_false. astep. zstep. zstep. astep.
    pose proof (ejt_read m 4 _ MI ltac:(lia) eq_refl) as JR; cbn [ejt nth Z.to_nat EJT_TAB Pos.to_nat Pos.iter_op Nat.add] in JR.
    lazymatch type of JR with ov_read_bytes _ _ (wa ?a) _ = Some ?r => let r' := eval vm_compute in r in change r with r' in JR; let a' := eval vm_compute in a in change a with a' in JR end.
    step. astep. step.
    zstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
  - zstep. if_false. astep. zstep. zstep. astep.
    pose proof (ejt_read m 5 _ MI ltac:(lia) eq_refl) as JR; cbn [ejt nth Z.to_nat EJT_TAB Pos.to_nat Pos.iter_op Nat.add] in JR.
    lazymatch type of JR with ov_read_bytes _ _ (wa ?a) _ = Some ?r => let r' := eval vm_compute in r in change r with r' in JR; let a' := eval vm_compute in a in change a with a' in JR end.
    step. astep. step.
    zstep. zstep. zstep. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
  -
    zstep. if_true. zstep. zstep. if_true. zstep. zstep. step. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
  -
    zstep. if_true. zstep. zstep. if_false. zstep. zstep. if_false. zstep. zstep. step. zstep. zstep.
    apply evt_done. do 2 eexists. atp_st_eq_goal.
Qed.

Lemma w_hexin : forall (i c : Z) (w : list byte) (x1 x5 x6 x7 x11 x13 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < e_P E -> e_P E + eL E < 2^63 -> 0 <= i < eL E ->
  (c = 11 \/ (0 <= c <= 31 /\ ~ (8 <= c <= 13))) -> rw_cells bsegs m (esp E) (efrL E w) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists x11' x12' x13', ms = ELSTA 0xb0f9c i x1 x5 x6 x7 (wz 31) x11' x12' x13' (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m)
    (ELSTA 0xb0f44 i x1 x5 x6 x7 (wz (e_P E + i)) x11 (wz (c - 8)) x13 (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH P0 PH Hi HC FR MI. unfold ELSTA. prepE E.
  set (qq := q - 192) in *. set (Ln := Z.of_nat (length bs)) in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  destruct HC as [-> | [Hc NT]].
  -
    cbn [Z.sub Z.add Z.pos_sub]. zstep. if_false. astep. zstep. zstep. astep.
    pose proof (ejt_read m 3 _ MI ltac:(lia) eq_refl) as JR; cbn [ejt nth Z.to_nat EJT_TAB Pos.to_nat Pos.iter_op Nat.add] in JR.
    lazymatch type of JR with ov_read_bytes _ _ (wa ?a) _ = Some ?r => let r' := eval vm_compute in r in change r with r' in JR; let a' := eval vm_compute in a in change a with a' in JR end.
    step. astep. step. step. if_dead1 by P0 PH Hi. zstep. zstep. if_false.
    apply evt_done. do 3 eexists. atp_st_eq_goal.
  -
    replace (Z_to_bv 64 (c - 8)) with (Z_to_bv 64 (if c <? 8 then c - 8 + 2^64 else c - 8)).
    2:{ destruct (c <? 8) eqn:E8; [| reflexivity]. apply Z_to_bv64_eqm. replace (c - 8 + 2^64) with ((c - 8) + 1 * 2^64) by lia. rewrite Z_mod_plus_full. reflexivity. }
    assert (D5 : 5 < (if c <? 8 then c - 8 + 2^64 else c - 8) < 2^64) by (destruct (c <? 8) eqn:E8; [apply Z.ltb_lt in E8| apply Z.ltb_ge in E8]; lia).
    set (d := if c <? 8 then c - 8 + 2^64 else c - 8) in *.
    zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
    zstep. zstep. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by lia; [exfalso; lia|].
    zstep. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [| exfalso; lia].
    step. if_dead1 by P0 PH Hi.
    zstep. zstep. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia; [exfalso; lia|].
    apply evt_done. do 3 eexists. atp_st_eq_goal.
Qed.

Lemma w_ownin : forall (i c : Z) (w : list byte) (x1 x5 x6 x7 x11 x13 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < e_P E -> e_P E + eL E < 2^63 -> 0 <= i < eL E ->
  32 <= c < 256 -> c <> 34 -> c <> 92 -> rw_cells bsegs m (esp E) (efrL E w) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists x11' x12' x13', ms = ELSTA 0xb1194 i x1 x5 x6 x7 (wz 31) x11' x12' x13' (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m)
    (ELSTA 0xb0f44 i x1 x5 x6 x7 (wz (e_P E + i)) x11 (wz (c - 8)) x13 (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH P0 PH Hi Hc N34 N92 FR MI. unfold ELSTA. prepE E.
  set (qq := q - 192) in *. set (Ln := Z.of_nat (length bs)) in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  zstep. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
  zstep. zstep. if_cases KQ; zify_cond KQ; rewrite ?unsigned_lit in KQ by lia; [exfalso; lia|].
  zstep. zstep. if_cases KS; zify_cond KS; rewrite ?unsigned_lit in KS by lia; [| exfalso; lia].
  step. if_dead1 by P0 PH Hi.
  zstep. zstep. if_cases KP; zify_cond KP; rewrite ?unsigned_lit in KP by lia; [| exfalso; lia].
  apply evt_done. do 3 eexists. atp_st_eq_goal.
Qed.

Lemma w_own1 : forall (i c : Z) (w : list byte) (jc jsb : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < e_f0 E -> e_f0 E + 64 < 2^63 -> shad (e_f0 E) + 8 < 2^63 -> (e_f0 E + 64 <= shad (e_f0 E) \/ shad (e_f0 E) + 8 <= e_f0 E) ->
  e_f0 E + 64 <= esp E -> shad (e_f0 E) + 8 <= esp E -> 0 <= c < 256 ->
  rw_cells bsegs m (esp E) (efrL E w) -> rw_cells bsegs m (e_f0 E + 32) [CB 1 jc] -> rw_cells bsegs m (shad (e_f0 E) + 4) [CB 1 jsb] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = ELSTA EL_OSPUT i (wz 0xb11b0) x5 x6 x7 (wz (eOS E + 128)) (wz (e_f0 E + 32)) (wz 1) x13 (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m1
      /\ munch [(e_f0 E + 32, e_f0 E + 33); (shad (e_f0 E) + 4, shad (e_f0 E) + 5)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (e_f0 E + 32) [C1 (Z_to_bv 8 c)] /\ rw_cells bsegs m1 (shad (e_f0 E) + 4) [C1 (Z_to_bv 8 1)])
    (ELSTA 0xb1194 i x1 x5 x6 x7 x10 x11 x12 x13 (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH F0 FH SHH SAP FQ SQ Hc FR FC FS MI. unfold ELSTA. prepE E.
  set (qq := q - 192) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f0) = f0) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f0 / 8 + 2147450880)) = f0 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f0 / 8 + 2147450880 + 4) with (f0 / 8 + 2147450884) in FS by lia.
  zstep. ls. zstep. ls. zstep. zstep. zstep.
  apply evt_done. exists m2. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|]. split; [exact WM|]. split; [assumption|].
  replace (f0 / 8 + 2147450880 + 4) with (f0 / 8 + 2147450884) by lia. split; [exact FC| exact FS].
Qed.

Lemma w_own2 : forall (i : Z) (jsb : list byte) (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 < e_f0 E -> shad (e_f0 E) + 8 < 2^63 -> rw_cells bsegs m (shad (e_f0 E) + 4) [CB 1 jsb] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = ELSTA 0xb116c i (wz 0xb11b0) x5 x6 x7 (wz (-8)) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1
      /\ munch [(shad (e_f0 E) + 4, shad (e_f0 E) + 5)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1)
    (ELSTA 0xb11b0 i (wz 0xb11b0) x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros F0 SHH FS MI. unfold ELSTA. prepE E.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (wz (f0 / 8 + 2147450880)) = f0 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  replace (f0 / 8 + 2147450880 + 4) with (f0 / 8 + 2147450884) in FS by lia.
  zstep. ls. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM| assumption].
Qed.

Lemma w_join : forall (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E <= e_SV E -> e_SV E + 16 < 2^63 -> 0 <= i < eL E -> eL E < 2^62 ->
  rw_cells bsegs m (e_SV E) [C8 (wz (e_P E)); C8 (wz (eL E))] -> shz m (e_SV E) 16 -> mem_inv bsegs m ->
  evt bsegs (fun ms => ms = ELSTA (if i + 1 <? eL E then 0xb0f04 else 0xb1204) (i + 1) x1 x5 x6 x7 (wz (eL E)) x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m)
    (ELSTA 0xb116c i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QSV SVH Hi LH SVC SHV MI. unfold ELSTA. prepE E.
  set (Ln := Z.of_nat (length bs)) in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EV : bv_unsigned (wz SV) = SV) by (apply unsigned_lit; lia).
  shz_pose SHV (SV + 8). zstep. shz_norm. zstep. if_false. zstep. astep. zstep.
  if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
  - replace (i + 1 <? Ln) with true by (symmetry; apply Z.ltb_lt; lia). apply evt_done; atp_st_eq_goal.
  - zstep. replace (i + 1 <? Ln) with false by (symmetry; apply Z.ltb_ge; lia). apply evt_done; atp_st_eq_goal.
Qed.

Definition osflat (pb pp ep : word) (FL W fill : Z) (dum j148 j284 : list byte) : list cell :=
  [C8 (wz 0x168da8); C8 (wz 0x6aac28); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 pb; C8 pp; C8 ep; CB 64 dum; C8 (wz 0x168e30);
   C8 (wz 0x168e58); C4 (wz FL); CB 4 j148; C8 (wz 6); C8 (wz W); C4 (wz 0); C4 (wz 0); C8 (wz (eOS E)); C8 (wz 0x6aac28);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz fill); CB 4 j284].
Lemma osflat_eq : forall pb pp ep FL W fill dum j148 j284,
  os_cellsX (eOS E) pb pp ep FL W fill dum j148 j284 = osflat pb pp ep FL W fill dum j148 j284.
Proof. intros. reflexivity. Qed.

Definition ELSTX (pc i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 : word) (x27 : word) (x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR x1 (wz (esp E)) (e_gp E) (wz TPV_A) x5 x6 x7 (wz (e_q E)) (wz (esp E)) x10 x11 x12 x13 x14 x15 x16 x17
          (wz (eOS E + 128)) (wz (e_SV E)) (wz (shad (e_SV E))) (wz (e_SV E + 8)) (wz (e_f0 E)) (wz (shad (e_SV E + 8))) (wz i) (wz (shad (e_f0 E))) (wz SHB) x27 x28 x29 x30 x31)
     F (wz pc) fc None m (seg_rom bsegs).

Lemma w_hex1 : forall (i : Z) (w : list byte) pb pp ep FL W fill dum j148 j284 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < e_F E -> e_F E + 512 <= esp E -> e_F E mod 64 = 0 -> 0 <= FL < 2^31 ->
  rw_cells bsegs m (esp E) (efrL E w) -> rw_cells bsegs m (eOS E) (osflat pb pp ep FL W fill dum j148 j284) ->
  ro_cells bsegs m 0x168e08 [C8 (wz 0x111a64); C8 (wz 0xb0168); C8 (wz 8)] -> shz m (eOS E) 288 -> shz m 0x168e08 24 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists x11', ms = ELSTX EL_OSPUT i (wz 0xb0ffc) x5 x6 x7 (wz (eOS E + 128)) (wz 0x23b00) (wz 2) x13 x14 x15 x16 x17 (wz FL) x28 x29 x30 x31 F fc m /\ x11' = x11)
    (ELSTA 0xb0f9c i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH E0 EQS E64 FLR FR OSC VT SHO SHV MI. unfold ELSTA, ELSTX, osflat in *. prepE E.
  set (qq := q - 192) in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (wz (Fr + 144)) = Fr + 144) by (apply unsigned_lit; lia).

  zstep. shz_pose SHO (Fr + 144 + 128). zstep. shz_norm. zstep. if_false.

  zstep. zstep. chk0 SHV 0x168e18. zstep. if_false.

  zstep. zstep. astep. replace ((Fr + 280) mod 8) with 0 by (clear - E64; Z.div_mod_to_equations; lia). step. if_false.
  zstep. zstep. chk0 SHO (Fr + 144 + 144). zstep. if_false. step.

  zstep. zstep. zstep. zstep.
  rewrite (sx32_small FL) by lia.
  apply evt_done. eexists. split; [atp_st_eq_goal| reflexivity].
Qed.

Lemma w_hex2 : forall (i FL : Z) (w : list byte) pb pp ep W fill dum j148 j284 (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> SEGTOP_A <= e_F E -> e_F E + 512 <= esp E -> e_F E mod 64 = 0 -> 0 <= W < 2^63 ->
  rw_cells bsegs m (esp E) (efrL E w) -> rw_cells bsegs m (eOS E) (osflat pb pp ep 0x1002 W fill dum j148 j284) ->
  ro_cells bsegs m 0x168e08 [C8 (wz 0x111a64); C8 (wz 0xb0168); C8 (wz 8)] ->
  (forall m', munch [(eOS E + 144, eOS E + 148); (eOS E + 160, eOS E + 168); (esp E + 87, esp E + 88)] m m' -> wmono bsegs m m' -> shz m' (eOS E) 288) ->
  (forall m', munch [(eOS E + 144, eOS E + 148); (eOS E + 160, eOS E + 168); (esp E + 87, esp E + 88)] m m' -> wmono bsegs m m' -> shz m' 0x168e08 24) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) x12' x13' x14',
      ms = ELSTX EL_SETFILL i (wz 0xb109c) x5 x6 x7 (wz (eOS E + 128)) (wz (esp E + 87)) x12' x13' x14' x15 x16 x17 (wz FL) x28 x29 x30 x31 F fc m1
      /\ munch [(eOS E + 144, eOS E + 148); (eOS E + 160, eOS E + 168); (esp E + 87, esp E + 88)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (eOS E) (osflat pb pp ep 0x1008 4 fill dum j148 j284)
      /\ rw_cells bsegs m1 (esp E) (efrL E (firstn 7 w ++ [Z_to_bv 8 0x30])) /\ bytes_at bsegs m1 (esp E + 87) [Z_to_bv 8 0x30])
    (ELSTX 0xb0ffc i (wz 0xb0ffc) x5 x6 x7 (wz (eOS E + 128)) x11 x12 x13 x14 x15 x16 x17 (wz FL) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH ESEG EQS E64 WR FR OSC VT SHO SHV MI. unfold ELSTX, osflat in *. unfold SEGTOP_A in ESEG. prepE E.
  set (qq := q - 192) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (wz (Fr + 144)) = Fr + 144) by (apply unsigned_lit; lia).

  chk0 SHO (Fr + 144 + 128). zstep. if_false.
  zstep. zstep. chk0 SHV 0x168e18. zstep. if_false.
  zstep. zstep. astep. replace ((Fr + 280) mod 8) with 0 by (clear - E64; Z.div_mod_to_equations; lia). step. if_false.
  zstep. chk0 SHO (Fr + 144 + 144). zstep. if_false.

  step. zstep. zstep.
  rewrite (a_zx32_small 4098) by lia. rewrite (unsigned_lit 4098) by lia.
  change (Z.land 4098 18446744073709551541 + 8) with 4104.
  ls.

  shz_pose SHV 0x168e18. zstep. shz_norm. zstep. if_false.
  zstep. zstep. astep. replace ((Fr + 280) mod 8) with 0 by (clear - E64; Z.div_mod_to_equations; lia). step. if_false.
  zstep. chk0 SHO (Fr + 144 + 160). zstep. if_false. zstep. ls.

  zstep. ls. zstep. zstep.
  replace (Fr + 144 + 128) with (Fr + 272) in * by lia.
  apply evt_done. exists m3. do 3 eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|]. split; [exact WM|]. split; [assumption|].
  split; [exact OSC|]. split.
  - lazymatch type of FR with rw_cells _ _ _ ?l =>
      pose proof (rw_cells_merge bsegs m3 qq (firstn 10 l) [CB 7 (firstn 7 w); C1 (Z_to_bv 8 48)] (skipn 12 l)) as M;
      cbn [firstn skipn app cells_size csize cells_bytes cbytes Nat.add] in M end.
    cbn [cbytes]. apply M. exact FR.
  - pose proof FR as X. lazymatch type of X with rw_cells _ _ _ ?l => rewrite <- (firstn_skipn 11 l) in X end. cbn [firstn skipn] in X.
    apply rw_cells_app in X. destruct X as [_ X]. cbn [cells_size csize Nat.add] in X.
    lazymatch type of X with rw_cells _ _ _ ?l => rewrite <- (firstn_skipn 1 l) in X end. cbn [firstn skipn] in X.
    apply rw_cells_app in X. destruct X as [X _]. pose proof (rw_cells_bytes_at bsegs m3 _ _ X) as B. cbn [cells_bytes cbytes app] in B.
    replace (qq + Z.of_nat 87) with (qq + 87) in B by lia. exact B.
Qed.

Lemma w_hex3 : forall (i c FL : Z) (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  e_q E <= e_SV E -> e_SV E + 16 < 2^63 -> 0 < e_P E -> e_P E + eL E < 2^63 -> e_p E <= e_P E -> e_P E + eL E <= e_p E + e_n8 E -> 0 <= i < eL E ->
  firstn 1 (skipn (Z.to_nat i) (e_bs E)) = [Z_to_bv 8 c] -> 0 <= c < 256 ->
  rw_cells bsegs m (e_SV E) [C8 (wz (e_P E)); C8 (wz (eL E))] -> bytes_at bsegs m (e_P E) (e_bs E) -> shz m (e_SV E) 16 -> shz m (e_p E) (e_n8 E) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists x12' x13' x14', ms = ELSTX EL_INS_I i (wz 0xb10dc) x5 x6 x7 (wz (eOS E + 128)) (wz c) x12' x13' x14' x15 x16 x17 (wz FL) x28 x29 x30 x31 F fc m)
    (ELSTX 0xb109c i (wz 0xb109c) x5 x6 x7 (wz (eOS E + 128)) x11 x12 x13 x14 x15 x16 x17 (wz FL) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros QSV SVH P0 PH PP PL Hi BI Hc SVC PB SHV SHP MI. unfold ELSTX. prepE E.
  set (qq := q - 192) in *. set (Ln := Z.of_nat (length bs)) in *.
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (bytes_at_ov_read bsegs m P bs (Z.to_nat i) 1 PB ltac:(lia)) as RD. rewrite BI, Z2Nat.id in RD by lia.
  shz_pose SHV SV. zstep. shz_norm. zstep. if_false.
  zstep. zstep.
  step. if_dead1 by P0 PH Hi. astep. astep.
  replace (0 <? P) with true by (symmetry; apply Z.ltb_lt; lia). replace (P + i <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  astep. step. if_false. step. if_dead1 by P0.
  chk0 SHP (P + i). zstep. if_false.
  zstep. zstep.
  rewrite (a_u8_small c) by lia.
  apply evt_done. do 3 eexists. atp_st_eq_goal.
Qed.

Lemma w_hex4 : forall (i FL : Z) (w : list byte) pb pp ep FL1 W fill dum j148 j284 (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> SEGTOP_A <= e_F E -> e_F E + 512 <= esp E -> e_F E mod 64 = 0 -> 0 <= FL < 2^31 -> 0 < e_f0 E -> e_f0 E + 64 < 2^63 ->
  rw_cells bsegs m (esp E) (efrL E w) -> rw_cells bsegs m (eOS E) (osflat pb pp ep FL1 W fill dum j148 j284) ->
  ro_cells bsegs m 0x168e08 [C8 (wz 0x111a64); C8 (wz 0xb0168); C8 (wz 8)] ->
  (forall m', munch [(eOS E + 144, eOS E + 148)] m m' -> wmono bsegs m m' -> shz m' (eOS E) 288) ->
  (forall m', munch [(eOS E + 144, eOS E + 148)] m m' -> wmono bsegs m m' -> shz m' 0x168e08 24) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) x10' x11',
      ms = ELSTA 0xb116c i (wz 0xb10dc) x5 x6 x7 x10' x11' x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m1
      /\ munch [(eOS E + 144, eOS E + 148)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 (eOS E) (osflat pb pp ep FL W fill dum j148 j284))
    (ELSTX 0xb10dc i (wz 0xb10dc) x5 x6 x7 (wz (eOS E + 128)) x11 x12 x13 x14 x15 x16 x17 (wz FL) x28 x29 x30 x31 F fc m).
Proof.
  intros until m. intros Q0 QH ESEG EQS E64 FLR F0 FH FR OSC VT SHO SHV MI. unfold ELSTX, ELSTA, osflat in *. unfold SEGTOP_A in ESEG. prepE E.
  set (qq := q - 192) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  assert (EO : bv_unsigned (wz (Fr + 144)) = Fr + 144) by (apply unsigned_lit; lia).

  zstep. shz_pose SHO (Fr + 144 + 128). zstep. shz_norm. zstep. if_false.
  zstep. zstep. chk0 SHV 0x168e18. zstep. if_false.
  zstep. zstep. astep. replace ((Fr + 280) mod 8) with 0 by (clear - E64; Z.div_mod_to_equations; lia). step. if_false.
  zstep. chk0 SHO (Fr + 144 + 144). zstep. if_false.

  ls. zstep. zstep. zstep.
  replace (Fr + 144 + 128) with (Fr + 272) in * by lia.
  apply evt_done. exists m1. do 2 eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|]. split; [exact WM|]. split; [assumption| exact OSC].
Qed.

Lemma ew_x1 : forall (j1 : list byte) (mid : list cell) (jm jsh : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < e_f0 E -> e_f0 E + 64 < 2^63 -> shad (e_f0 E) + 8 < 2^63 -> (e_f0 E + 64 <= shad (e_f0 E) \/ shad (e_f0 E) + 8 <= e_f0 E) ->
  e_f0 E + 64 <= esp E -> shad (e_f0 E) + 8 <= esp E -> cells_size mid = 64%nat ->
  rw_cells bsegs m (esp E) (C8 (wz 0) :: CB 8 j1 :: C8 (wz (e_f0 E)) :: mid ++ esaves E) -> rw_cells bsegs m (e_f0 E) [CB 8 jm] -> rw_cells bsegs m (shad (e_f0 E)) [CB 8 jsh] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR x1 (wz (esp E)) (e_gp E) (wz TPV_A) x5 x6 x7 (wz (e_q E)) (wz (esp E)) (wz (-11)) (wz (e_f0 E)) x12 x13 x14 x15 x16 x17
                   (wz (eOS E + 128)) (wz (e_SV E)) x20 (wz (e_SV E + 8)) x22 (wz (shad (e_SV E + 8))) x24 (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) x28 x29 x30 x31)
              F (wz 0xb123c) fc None m1 (seg_rom bsegs)
      /\ munch [(e_f0 E, e_f0 E + 8); (shad (e_f0 E), shad (e_f0 E) + 8)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1)
    (MS (mkR x1 (wz (esp E)) (e_gp E) (wz TPV_A) x5 x6 x7 (wz (e_q E)) (wz (esp E)) x10 x11 x12 x13 x14 x15 x16 x17
             (wz (eOS E + 128)) (wz (e_SV E)) x20 (wz (e_SV E + 8)) x22 (wz (shad (e_SV E + 8))) x24 (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) x28 x29 x30 x31)
        F (wz 0xb1204) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Q0 QH F0 FH SHH SAP FQ SQ MSZ FR FM FS MI. prepE E.
  set (qq := q - 192) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f0) = f0) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (wz (f0 / 8 + 2147450880)) = f0 / 8 + 2147450880) by (apply unsigned_lit; Z.div_mod_to_equations; lia).
  apply (rw_cells_split_CB bsegs _ _ [] 8 _ [] (repeat 1%nat 8)) in FS; [| reflexivity]. cbn [repeat mk_CB_cells app] in FS.

  zstep. zstep. lstep. zstep. zstep. if_false. zstep. do 8 ls.
  apply evt_done. eexists. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM| assumption].
Qed.

Lemma ew_x2 : forall (fl : Z) (j1 jmid : list byte) (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 x31 : word) F fc (m : mem),
  0 <= esp E -> e_q E < 2^63 -> 0 < fl -> fl + 1 < 2^63 -> fl + 1 <= e_lo E -> e_lo E <= esp E -> 0 < e_f0 E -> e_f0 E + 64 <= esp E ->
  stk bsegs m (e_lo E) (esp E) -> rw_cells bsegs m (esp E) ([C8 (wz 0); CB 8 j1; C8 (wz (e_f0 E)); CB 64 jmid] ++ esaves E) -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  ro_cells bsegs m (e_f0 E + 56) [C8 (wz fl)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem) a1',
      ms = MS (mkR (e_ra E) (wz (e_q E)) (e_gp E) (wz TPV_A) x5 x6 x7 (e_s0 E) (e_s1 E) (wz (eOS E + 128)) a1' x12 x13 x14 x15 x16 x17
                   (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) x28 x29 x30 x31)
              F (ret_pc (e_ra E)) fc None m1 (seg_rom bsegs)
      /\ munch [(fl, fl + 1)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ rw_cells bsegs m1 fl [C1 (Z_to_bv 8 0)] /\ stk bsegs m1 (e_lo E) (e_q E))
    (MS (mkR x1 (wz (esp E)) (e_gp E) (wz TPV_A) x5 x6 x7 (wz (e_q E)) (wz (esp E)) (wz (-11)) (wz (e_f0 E)) x12 x13 x14 x15 x16 x17
             (wz (eOS E + 128)) (wz (e_SV E)) x20 (wz (e_SV E + 8)) x22 (wz (shad (e_SV E + 8))) x24 (wz (shad (e_f0 E))) (wz SHB) (wz (e_f0 E)) x28 x29 x30 x31)
        F (wz 0xb123c) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros Q0 QH FL0 FLH FLO LOQ F0 FQ ST FR FC FW MI. prepE E.
  set (qq := q - 192) in *.
  lazymatch goal with |- context [munch ?W0 m _] => pose proof (munch_refl W0 m) as MU end. pose proof (wmono_refl bsegs m) as WM.
  assert (EQ : bv_unsigned (wz qq) = qq) by (apply unsigned_lit; lia).
  assert (EU : bv_unsigned (wz q) = q) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (wz fl) = fl) by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (wz f0) = f0) by (apply unsigned_lit; lia).
  step. ls. zstep. zstep. zstep. replace (q + -192) with qq by (clear - qq; lia).
  do 13 step. zstep. release_frame FR ST q. step.
  apply evt_done. eexists m1, _. split; [atp_st_eq_goal|]. split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; lia|].
  split; [exact WM|]. split; [assumption|]. split; [exact FC| exact ST].
Qed.

Lemma GINVA_cws : forall FL W FP FL' W' (FP' : Z -> Prop) fcs fcs' k Σ m m' W0 fill,
  GI FL W FP fcs k Σ m -> munch W0 m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
  (forall a, outside W0 a \/ own (e_G E) a \/ eOS E + 136 <= a < eOS E + 168) ->
  rw_cells bsegs m' (esp E) fcs' -> cells_size fcs' = cells_size fcs ->
  OSXW m' (eOS E) FL' W' fill -> FP' fill -> GI FL' W' FP' fcs' k Σ m'.
Proof using AF EOK.
  intros FL W FP FL' W' FP' fcs fcs' k Σ m m' W0 fill GIm MU WM MI' HW FR' FSZ' OX' FOK'. facts EOK.
  destruct GIm as (HA & MI & FRS & LV & SP0 & CR & ST & _ & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
  cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in HA, FRS, LV, SP0, CR, ST, SHO, FR, FSZ, WF1, WF2, REL |- *.
  change (fs_size 0) with 64 in *. change (64 / 8) with 8 in *.
  pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.
  assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ own (e_G E) x /\ ~ (eOS E + 136 <= x < eOS E + 168)) -> agree_on P m m').
  { intros P HP a Ha. apply MU. destruct (HP _ Ha) as [N1 N2]. destruct (HW (bv_unsigned a)) as [X|[X|X]]; [exact X| exfalso; exact (N1 X)| exfalso; exact (N2 X)]. }
  assert (OWNC := own_aclient RT AF (e_G E) GOK). assert (NOS := os_not_own RT AF (e_G E) GOK).
  cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in OWNC, NOS. change (fs_size 0) with 64 in OWNC, NOS. change (64 / 8) with 8 in OWNC, NOS.
  split. { apply (art_client_write RT AF Σ m m' (e_q E - 192) HA); [rewrite SP0; clear - LO2 LQ; ul| | exact WM].
           intros a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|[X|X]]; [exact X| |].
           - exfalso. apply Ha. rewrite FRS, LV. exact (OWNC _ X).
           - exfalso. apply Ha. rewrite FRS. right; right; right; left. exists (e_F E), 3%nat. split; [right; exact EIN| change (fs_size 3) with 512; clear - X; lia]. }
  split; [exact MI'|]. split; [exact FRS|]. split; [exact LV|]. split; [exact SP0|]. split; [exact CR|].
  split. { apply (stk_agree bsegs m m' _ _ ST); [| exact WM]. apply AG. intros x Hx. split; [| clear - Hx ELO LQ; ul].
           intros OW. unfold own in OW. cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in OW. change (fs_size 0) with 64 in OW. change (64 / 8) with 8 in OW.
           unfold shad in *. clear - Hx OW FLO SHLO LQ. ul. }
  split. { exists fill. split; [exact OX'| exact FOK']. }
  split. { apply (bytes_at_agree bsegs m m' _ _ SHO). apply AG. intros x Hx. rewrite repeat_length in Hx. split; [apply NOS; right; left; exact Hx|].
           unfold shad in *. clear - Hx ESH E0. lia. }
  split. { apply (rw_cells_agree_nw bsegs m m' _ _ TPL). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply NOS; do 2 right; clear - Hx; ul| clear - Hx ESEG; ul]. }
  split. { apply (LOCBA_agree m m' LB). apply AG. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. split; [apply NOS; do 2 right; clear - Hx; ul| clear - Hx ESEG; ul]. }
  split; [split; [exact FR'| rewrite FSZ'; exact FSZ]|]. split; [exact (wr_at_transport bsegs m m' _ _ WF1 WM)|]. split; [exact (wr_at_transport bsegs m m' _ _ WF2 WM)|].
  intros a CA OU. etransitivity; [| exact (REL a CA OU)]. apply MU. destruct (HW (bv_unsigned a)) as [X|[X|X]]; [exact X| |].
  - exfalso. exact (own_not_caller RT AF (e_G E) GOK _ X CA).
  - exfalso. unfold WD in OU. cbn [outside e_G g_F] in OU. clear - OU X. lia.
Qed.

Lemma GINVA_fills : forall FL W (FP FP' : Z -> Prop) fcs k Σ m, (forall f, FP f -> FP' f) -> GI FL W FP fcs k Σ m -> GI FL W FP' fcs k Σ m.
Proof.
  intros FL W FP FP' fcs k Σ m H (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & REST).
  split; [exact HA|]. split; [exact MI|]. split; [exact FRS|]. split; [exact LV|]. split; [exact SP0|]. split; [exact CR|]. split; [exact ST|].
  split; [exists fill; split; [exact OX| apply H; exact FOK]| exact REST].
Qed.

Lemma esc_joinA : forall (K : config -> Prop) (i : Z) (Σ : rts RT) (m : mem) (k : Z) (w : list byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI 0x1002 0 FILLOK (efrL E w) k Σ m -> frm0 fc -> 0 <= i < eL E -> eL E < 2^62 -> 0 <= k -> k <= 1 + 4 * (i + 1) ->
  (i + 1 < eL E -> EKLOOPA K (i + 1)) -> EEXITA K ->
  aevt RT PMc Σ K (ELSTA 0xb116c i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof using AF MST EOK SVC0 PB0 DCC.
  intros until fc. intros GI0 FRM Hi LH K0 KB HK HX. facts EOK.
  pose proof (efacts _ _ _ _ _ _ _ GI0) as (SVC & PB & SHV & SHP & SHL & SHO & VT & IOS).
  pose proof GI0 as (_ & MI0 & _).
  assert (Q0 : 0 <= esp E) by (clear - LO1 LQ; ul).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (w_join i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m Q0 QSV ltac:(clear - SVT; ul) Hi LH SVC SHV MI0)|].
  cbv beta. intros ms1 ->. apply evt_done.
  destruct (Z.ltb_spec (i + 1) (eL E)) as [LT|GE].
  - apply (HK LT Σ m k w); [exact GI0| exact FRM| exact K0| exact KB].
  - unfold ELSTA. change (efrL E w) with (C8 (wz 0) :: CB 8 (nth 0 (e_j E) []) :: C8 (wz (e_f0 E)) :: (firstn 8 (skipn 3 (efrL E w))) ++ esaves E) in GI0.
    eapply (HX Σ m k _ _ x1 x5 x6 x7 (wz (eL E)) x11 x12 x13 x14 x15 x16 x17 _ _ _ x28 x29 x30 x31 F fc GI0); [reflexivity| exact FRM| exact K0| clear - KB GE Hi; lia].
Qed.

Definition EPOST (K : config -> Prop) : Prop :=
  forall (Σ' : rts RT) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem),
     ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (e_lo E) (e_q E) -> (exists fill', OSX m' (eOS E) fill' /\ FILLOK fill') ->
     bytes_at bsegs m' (shad (eOS E)) (repeat z8 36) -> LOCBA m' -> el_tploc m' -> frm0 fc' ->
     rt_live RT Σ' = e_L E -> rt_frames RT Σ' = e_rfr E -> rt_sp0 RT Σ' = e_sp0 E -> e_cr E - esc_costA (eL E) <= rt_credit RT Σ' ->
     rt_pres_fp (e_L E) (e_rfr E) (e_q E) (ESC_W (e_F E)) (e_m0 E) m' ->
     aevt RT PMc Σ' K (MS (mkR (e_ra E) (wz (e_q E)) (e_gp E) (wz TPV_A) t0' t1' t2' (e_s0 E) (e_s1 E) (wz (e_F E + 272)) a1' a2' a3' a4' a5' a6' a7'
                            (e_s2 E) (e_s3 E) (e_s4 E) (e_s5 E) (e_s6 E) (e_s7 E) (e_s8 E) (e_s9 E) (e_s10 E) (e_s11 E) t3' t4' t5' t6')
                       F' (ret_pc (e_ra E)) fc' None m' (seg_rom bsegs)).

Lemma esc_exitA : forall (K : config -> Prop), EPOST K -> EEXITA K.
Proof using AF MST EOK SVC0 PB0 DCC.
  intros K HK. unfold EEXITA. intros Σ m k j1 mid x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 x31 F fc GI0 MSZ FRM K0 KB. facts EOK.
  assert (Q0 : 0 <= esp E) by (clear - LO1 LQ; ul). assert (QH : e_q E < 2^63) by (clear - QT; ul).
  pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.
  pose proof GI0 as (HA0 & MI0 & FRS0 & LV0 & SP0 & CR0 & ST0 & (fill0 & OX0 & FOK0) & SHO0 & TPL0 & LB0 & (FR0 & FSZ0) & WF0 & WS0 & REL0).
  cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in HA0, FRS0, LV0, SP0, CR0, ST0, OX0, SHO0, FR0, FSZ0, WF0, WS0, REL0.
  change (fs_size 0) with 64 in WF0, WS0. replace (64 - 8) with 56 in WF0 by reflexivity. change (64 / 8) with 8 in WS0.

  pose proof (rw_cells_merge bsegs m (esp E) [C8 (wz 0); CB 8 j1; C8 (wz (e_f0 E))] mid (esaves E) FR0) as FRJ. rewrite MSZ in FRJ. cbn [app] in FRJ.

  destruct (wr_at_cell m _ 56 0 8 WF0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jm FM]. replace (e_f0 E + 0) with (e_f0 E) in FM by (clear; lia).
  destruct (wr_at_cell m _ 8 0 8 WS0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jsh FS]. replace (shad (e_f0 E) + 0) with (shad (e_f0 E)) in FS by (clear; lia).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ew_x1 j1 [CB 64 (cells_bytes mid)] jm jsh x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 x31 F fc m Q0 QH F0);
    [clear - FLO LQ QT; ul| clear - SHLO LQ QT; ul| exact SHAP| clear - FLO LQ; ul| clear - SHLO LQ; ul| reflexivity| exact FRJ| exact FM| exact FS| exact MI0]|].
  cbv beta. intros ms2 (m4 & -> & MU4 & WM4 & MI4). apply evt_done.
  assert (GI4 : GI 0x1002 0 FILLOK ([C8 (wz 0); CB 8 j1; C8 (wz (e_f0 E)); CB 64 (cells_bytes mid)] ++ esaves E) k Σ m4).
  { eapply (GINVA_cw RT AF (e_G E) GOK _ _ _ _ _ _ Σ m m4 _ GI0 MU4 WM4 MI4);
      [(intros ?; unfold own; cbn [outside e_G g_q g_fsz g_ff g_ffk]; change (fs_size 0) with 64; change (64 / 8) with 8; clear; lia)| | cbn [cells_size csize Nat.add app]; rewrite cells_size_app, MSZ; reflexivity].
    cbn [e_G g_q]. apply (rw_cells_agree_nw bsegs m m4 _ _ FRJ). apply (agree_of_munch _ _ _ _ MU4). intros x Hx. cbn [cells_size csize Nat.add app] in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  pose proof GI4 as (HA4 & _ & FRS4 & LV4 & SP4 & CR4 & ST4 & (fill4 & OX4 & FOK4) & SHO4 & TPL4 & LB4 & (FR4 & _) & _ & _ & REL4).
  cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in HA4, FRS4, LV4, SP4, CR4, ST4, OX4, SHO4, FR4, REL4.
  clear HA0 MI0 ST0 FR0 WF0 WS0 FM FS MU4 WM4 CR0 FRS0 LV0 SP0 OX0 SHO0 TPL0 LB0 REL0 FRJ GI0 m.

  destruct (af_frame_release RT AF Σ m4 (e_f0 E) 0%nat (e_rfr E) HA4 FRS4) as (Σ5 & fl & FLC & NAC & FL0 & FLW & FW & RELF).
  change (fs_size 0) with 64 in FW. replace (e_f0 E + 64 - 8) with (e_f0 E + 56) in FW by (clear; lia). rewrite SP4 in FLW.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (ew_x2 fl j1 (cells_bytes mid) x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x20 x22 x24 x28 x29 x30 x31 F fc m4 Q0 QH FL0);
    [clear - FLW LO2 LQ QT; ul| clear - FLW LO2; lia| clear - LQ; ul| exact F0| clear - FLO LQ; ul| exact ST4| exact FR4| exact FLC| exact FW| exact MI4]|].
  cbv beta. intros ms3 (m5 & a1' & -> & MU5 & WM5 & MI5 & FL5 & ST5). apply evt_done.
  destruct (RELF m5 MU5 WM5 FL5) as (HA5 & FRS5 & LV5 & SP5 & CR5 & AL5 & AM5).
  apply (aevt_switch RT PMc Σ Σ5 K _ AL5 AM5).

  assert (NFL : forall x, aclient (e_L E) (e_rfr E) (e_q E) x -> fl <= x < fl + 1 -> False).
  { intros x CA X. destruct CA as [SX|CA']; [clear - SX X FLW LO2 LQ; ul|].
    apply NAC. rewrite LV4, FRS4. replace fl with x by (clear - X; lia).
    apply (aclient_mono (e_L E) (e_rfr E) USTACK_TOP); [right; exact CA'| auto| intros e He; right; exact He| clear; lia]. }
  assert (REL5 : forall a : word, aclient (e_L E) (e_rfr E) (e_q E) (bv_unsigned a) -> outside (WD (eOS E)) (bv_unsigned a) -> m5 a = e_m0 E a).
  { intros a CA OU. rewrite (MU5 a); [apply (REL4 a); [| exact OU]; replace (e_q E - 192 + 192) with (e_q E) by (clear; lia); exact CA|].
    cbn [outside]. split; [| exact I]. intros X. exact (NFL _ CA X). }
  assert (AGc : forall P : Z -> Prop, (forall x, P x -> aclient (e_L E) (e_rfr E) (e_q E) x /\ ~ (fl <= x < fl + 1)) -> agree_on P m4 m5).
  { intros P HP a Ha. apply MU5. cbn [outside]. split; [exact (proj2 (HP _ Ha))| exact I]. }
  assert (CLF : forall x, e_F E <= x < e_F E + 504 -> aclient (e_L E) (e_rfr E) (e_q E) x /\ ~ (fl <= x < fl + 1)).
  { intros x Hx. assert (CA : aclient (e_L E) (e_rfr E) (e_q E) x) by (right; right; right; left; exists (e_F E), 3%nat; split; [exact EIN| change (fs_size 3) with 512; clear - Hx; lia]).
    split; [exact CA| intros X; exact (NFL _ CA X)]. }
  assert (CLS : forall x, shad (e_F E) <= x < shad (e_F E) + 64 -> aclient (e_L E) (e_rfr E) (e_q E) x /\ ~ (fl <= x < fl + 1)).
  { intros x Hx. assert (CA : aclient (e_L E) (e_rfr E) (e_q E) x) by (do 4 right; exists (e_F E), 3%nat; split; [exact EIN| change (fs_size 3) with 512; unfold shad in *; clear - Hx E64; Z.div_mod_to_equations; lia]).
    split; [exact CA| intros X; exact (NFL _ CA X)]. }
  assert (CLT : forall x, client_static x -> aclient (e_L E) (e_rfr E) (e_q E) x /\ ~ (fl <= x < fl + 1)).
  { intros x Hx. assert (CA : aclient (e_L E) (e_rfr E) (e_q E) x) by (right; left; exact Hx). split; [exact CA| intros X; exact (NFL _ CA X)]. }
  replace (eOS E + 128) with (e_F E + 272) by (clear; lia).
  eapply (HK Σ5 x5 x6 x7 a1' x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m5 HA5 MI5 ST5); [ | | | | exact FRM| rewrite LV5; exact LV4| exact FRS5| rewrite SP5; exact SP4
    | rewrite CR5; unfold esc_costA; clear - CR4 KB K0; lia| ].
  - exists fill4. split; [| exact FOK4]. apply (OSX_agree m4 m5); [apply (proj2 (OSX_W m4 (eOS E) fill4)); exact OX4| | exact WM5]. apply AGc. intros x Hx. apply CLF. clear - Hx. lia.
  - apply (bytes_at_agree bsegs m4 m5 _ _ SHO4). apply AGc. intros x Hx. rewrite repeat_length in Hx. apply CLS. unfold shad in *. clear - Hx E64. Z.div_mod_to_equations. lia.
  - apply (LOCBA_agree m4 m5 LB4). apply AGc. intros x Hx. apply CLT. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. apply client_static_intro. clear - Hx. lia.
  - unfold el_tploc. apply (rw_cells_agree_nw bsegs m4 m5 _ _ TPL4). apply AGc. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply CLT. apply client_static_intro. clear - Hx. lia.
  - intros a CA OU. apply (REL5 a CA). unfold ESC_W in OU. unfold WD, EL_TPLOC_A, TPV_A. exact OU.
Qed.

Hypothesis CRB : esc_costA (eL E) <= e_cr E.
Hypothesis FRB : (length (e_rfr E) + 4 <= FRAMES_MAX)%nat.

Lemma esc_litA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (w : list byte)
    (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI 0x1002 0 FILLOK (efrL E w) k Σ m -> frm0 fc -> 0 <= i < eL E -> eL E < 2^62 -> is_elit c -> 0 <= k -> k <= 1 + 4 * i ->
  (i + 1 < eL E -> EKLOOPA K (i + 1)) -> EEXITA K ->
  aevt RT PMc Σ K (ELSTA EL_OSPUT i (wz 0xb116c) x5 x6 x7 (wz (eOS E + 128)) (wz (elit c)) (wz 2) x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof using AF FDO MST PUT EOK SVC0 PB0 DCC CRB FRB.
  intros until fc. intros GI0 FRM Hi LH HC K0 KB HK HX. facts EOK.
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  unfold ELSTA. replace (eOS E + 128) with (e_F E + 272) by (clear; lia).
  assert (LIT : In (elit c, 3) ACC_LITS /\ ro_bytes_b bsegs (elit c) (lit (elit c) 3) = true /\ length (lit (elit c) 3) = 3%nat /\ 0x10000 <= elit c /\ elit c + 3 <= SEGTOP_A).
  { destruct HC as [-> |[-> |[-> |[-> |[-> |[-> | ->]]]]]]; unfold elit; cbn [Z.eqb Pos.eqb];
      (split; [clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])|]; split; [vm_compute; reflexivity|]; split; [vm_compute; reflexivity|]; clear; unfold SEGTOP_A; lia). }
  destruct LIT as (INL & RB & LLn & BLO & BHI).
  pose proof (g_put_lit RT AF PMc FDO MST (e_G E) GOK) as GPL. cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in GPL.
  eapply (GPL FILLOK FILLOK _ k Σ K (elit c) 2 3 3%nat);
    [exact PUT| exact GI0| intros f Hf; exact Hf| exact FA| exact INL| exact RB| exact LLn| clear; lia| clear; lia| exact BLO| exact BHI
    | clear - LQ; ul| unfold FRAMES_TOT; unfold FRAMES_MAX in FRB; clear - FRB; lia
    | unfold esc_costA in CRB; clear - CRB KB K0 Hi; lia|].
  clear GPL GI0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m2 GI2.
  rewrite (ret_pc_even 0xb116c) by (clear; lia). replace (e_F E + 272) with (eOS E + 128) by (clear; lia).
  eapply (esc_joinA K i Σ2 m2 (k + 2) w _ u0 u1 u2 _ b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc); [exact GI2| exact FRM| exact Hi| exact LH| clear - K0; lia| clear - KB; lia| exact HK| exact HX].
Qed.

Lemma esc_ownA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (w : list byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI 0x1002 0 FILLOK (efrL E w) k Σ m -> frm0 fc -> 0 <= i < eL E -> eL E < 2^62 -> 0 <= c < 256 -> 0 <= k -> k <= 1 + 4 * i ->
  (i + 1 < eL E -> EKLOOPA K (i + 1)) -> EEXITA K ->
  aevt RT PMc Σ K (ELSTA 0xb1194 i x1 x5 x6 x7 x10 x11 x12 x13 (wz c) x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof using AF FDO MST PUT EOK SVC0 PB0 DCC CRB FRB.
  intros until fc. intros GI0 FRM Hi LH Hc K0 KB HK HX. facts EOK.
  assert (Q0 : 0 <= esp E) by (clear - LO1 LQ; ul). assert (QH : e_q E < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> FILLOK (fill_after f)) by (intros f Hf; destruct (FILLOK_after f Hf) as [e|e]; rewrite e; [right; left| right; right]; reflexivity).
  pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.
  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & WF0 & WS0 & _). cbn [e_G g_ff g_FS g_ffk g_q] in WF0, WS0, FR0.
  change (fs_size 0) with 64 in WF0, WS0. replace (64 - 8) with 56 in WF0 by reflexivity. change (64 / 8) with 8 in WS0.
  destruct (wr_at_cell m _ 56 32 1 WF0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jc FCj].
  destruct (wr_at_cell m _ 8 4 1 WS0 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [jsb FSj].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (w_own1 i c w jc jsb x1 x5 x6 x7 x10 x11 x12 x13 x15 x16 x17 x28 x29 x30 x31 F fc m Q0 QH F0);
    [clear - FLO LQ QT; ul| clear - SHLO LQ QT; ul| exact SHAP| clear - FLO LQ; ul| clear - SHLO LQ; ul| exact Hc| exact FR0| exact FCj| exact FSj| exact MI0]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FC1 & FS1). apply evt_done. unfold ELSTA.
  assert (GI1 : GI 0x1002 0 FILLOK (efrL E w) k Σ m1).
  { eapply (GINVA_cw RT AF (e_G E) GOK _ _ _ _ _ _ Σ m m1 _ GI0 MU1 WM1 MI1); [(intros ?; unfold own; cbn [outside e_G g_q g_fsz g_ff g_ffk]; change (fs_size 0) with 64; change (64 / 8) with 8; clear; lia)| | reflexivity].
    cbn [e_G g_q]. apply (rw_cells_agree_nw bsegs m m1 _ _ FR0). apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [e_G g_q] in Hx. rewrite efrL_size in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx FLO LQ SHLO; ul. }
  clear GI0 MI0 FR0 WF0 WS0 FCj FSj MU1 WM1.
  pose proof (g_put_ownc RT AF PMc FDO MST (e_G E) GOK) as GPO. cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in GPO.
  change (fs_size 0) with 64 in GPO. replace (eOS E + 128) with (e_F E + 272) by (clear; lia).
  eapply (GPO FILLOK FILLOK _ k Σ K 32 (Z_to_bv 8 c));
    [exact PUT| exact GI1| intros f Hf; exact Hf| exact FA| exact FC1| change (32 / 8) with 4; exact FS1| reflexivity| clear; lia| clear; lia
    | clear - LQ; ul| unfold FRAMES_TOT; unfold FRAMES_MAX in FRB; clear - FRB; lia| unfold esc_costA in CRB; clear - CRB KB K0 Hi; lia|].
  clear GPO GI1 FC1 FS1 MI1 m1. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m2 GI2.
  rewrite (ret_pc_even 0xb11b0) by (clear; lia). replace (e_F E + 272) with (eOS E + 128) by (clear; lia).

  pose proof GI2 as (_ & MI2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR2 & _) & _ & WS2 & _). cbn [e_G g_ff g_FS g_ffk g_q] in WS2, FR2.
  change (fs_size 0) with 64 in WS2. change (64 / 8) with 8 in WS2.
  destruct (wr_at_cell m2 _ 8 4 1 WS2 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia)) as [js2 FS2].
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (w_own2 i js2 u0 u1 u2 _ b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc m2 F0); [clear - SHLO LQ QT; ul| exact FS2| exact MI2]|].
  cbv beta. intros ms3 (m3 & -> & MU3 & WM3 & MI3). apply evt_done.
  assert (GI3 : GI 0x1002 0 FILLOK (efrL E w) (k + 2) Σ2 m3).
  { eapply (GINVA_cw RT AF (e_G E) GOK _ _ _ _ _ _ Σ2 m2 m3 _ GI2 MU3 WM3 MI3); [(intros ?; unfold own; cbn [outside e_G g_q g_fsz g_ff g_ffk]; change (fs_size 0) with 64; change (64 / 8) with 8; clear; lia)| | reflexivity].
    cbn [e_G g_q]. apply (rw_cells_agree_nw bsegs m2 m3 _ _ FR2). apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [e_G g_q] in Hx. rewrite efrL_size in Hx.
    cbn [outside]. repeat split; try exact I; clear - Hx SHLO LQ; ul. }
  eapply (esc_joinA K i Σ2 m3 (k + 2) w _ u0 u1 u2 _ b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc); [exact GI3| exact FRM| exact Hi| exact LH| clear - K0; lia| clear - KB; lia| exact HK| exact HX].
Qed.

Lemma esc_hexA : forall (K : config -> Prop) (i c : Z) (Σ : rts RT) (m : mem) (k : Z) (w : list byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI 0x1002 0 FILLOK (efrL E w) k Σ m -> frm0 fc -> 0 <= i < eL E -> eL E < 2^62 -> 0 <= c < 32 ->
  firstn 1 (skipn (Z.to_nat i) (e_bs E)) = [Z_to_bv 8 c] -> 0 <= k -> k <= 1 + 4 * i ->
  (i + 1 < eL E -> EKLOOPA K (i + 1)) -> EEXITA K ->
  aevt RT PMc Σ K (ELSTA 0xb0f9c i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof using AF FDO MST PUT SETF INSI EOK SVC0 PB0 DCC CRB FRB.
  intros until fc. intros GI0 FRM Hi LH Hc BI K0 KB HK HX. facts EOK.
  assert (Q0 : 0 <= esp E) by (clear - LO1 LQ; ul). assert (QH : e_q E < 2^63) by (clear - QT; ul).
  assert (FA : forall f, FILLOK f -> f = 0x20 \/ f = 0x30 -> False \/ True) by (intros; right; exact I). clear FA.
  assert (FA2 : forall f, FILLOK f -> (fun g => g = 0x20 \/ g = 0x30) (fill_after f)) by (intros f Hf; exact (FILLOK_after f Hf)).
  pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 3) with 512 in A1, A2, A3.

  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & (fill0 & OX0 & FOK0) & _ & _ & _ & (FR0 & _) & _). cbn [e_G g_q g_F] in OX0, FR0.
  destruct OX0 as (pb0 & pp0 & ep0 & dum0 & ja0 & jb0 & OSC0 & PI0). rewrite osflat_eq in OSC0.
  pose proof (efacts _ _ _ _ _ _ _ GI0) as (_ & _ & _ & _ & SHL0 & SHO0 & (VT0 & _) & _).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (w_hex1 i w pb0 (wz pp0) (wz ep0) 0x1002 0 fill0 dum0 ja0 jb0 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m Q0 QH E0);
    [clear - ELO LQ; ul| exact E64| clear; lia| exact FR0| exact OSC0| exact VT0| exact SHO0| exact SHL0| exact MI0]|].
  cbv beta. intros ms1 (x11' & -> & _). apply evt_done. unfold ELSTX.
  pose proof (g_put_lit RT AF PMc FDO MST (e_G E) GOK) as GPL. cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in GPL.
  replace (eOS E + 128) with (e_F E + 272) by (clear; lia).
  eapply (GPL FILLOK (fun g => g = 0x20 \/ g = 0x30) _ k Σ K 0x23b00 2 3 3%nat);
    [exact PUT| exact GI0| intros f Hf; exact Hf| exact FA2| clear; cbn [In ACC_LITS]; repeat (first [left; reflexivity | right])| vm_compute; reflexivity| vm_compute; reflexivity
    | clear; lia| clear; lia| clear; lia| clear; unfold SEGTOP_A; lia
    | clear - LQ; ul| unfold FRAMES_TOT; unfold FRAMES_MAX in FRB; clear - FRB; lia| unfold esc_costA in CRB; clear - CRB KB K0 Hi; lia|].
  clear GPL GI0 MI0 FR0 OSC0 PI0 SHL0 SHO0 VT0 pb0 pp0 ep0 dum0 ja0 jb0 FOK0 fill0. intros Σ2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 m2 GI2.
  rewrite (ret_pc_even 0xb0ffc) by (clear; lia). replace (e_F E + 272) with (eOS E + 128) by (clear; lia).

  pose proof GI2 as (_ & MI2 & _ & _ & _ & _ & _ & (fill2 & OX2 & FOK2) & _ & _ & _ & (FR2 & _) & _). cbn [e_G g_q g_F] in OX2, FR2.
  destruct OX2 as (pb2 & pp2 & ep2 & dum2 & ja2 & jb2 & OSC2 & PI2). rewrite osflat_eq in OSC2.
  pose proof (efacts _ _ _ _ _ _ _ GI2) as (_ & _ & _ & _ & SHL2 & SHO2 & (VT2 & _) & _).
  assert (SHOF : forall W0, (forall y, 2147450880 <= y < 0x10007fff8000 -> outside W0 y) -> forall m', munch W0 m2 m' -> wmono bsegs m2 m' -> shz m' (eOS E) 288).
  { intros W0 HW m' MU _. eapply (shz_munch m2 m' W0 _ _ SHO2 MU); [clear - E0; lia| clear - ELO LQ QT; ul| intros x Hx; apply HW; apply shad_off; clear - Hx E0 ELO LQ QT; ul]. }
  assert (SHLF : forall W0, (forall y, 2147450880 <= y < 0x10007fff8000 -> outside W0 y) -> forall m', munch W0 m2 m' -> wmono bsegs m2 m' -> shz m' 0x168e08 24).
  { intros W0 HW m' MU _. eapply (shz_munch m2 m' W0 _ _ SHL2 MU); [clear; lia| clear; lia| intros x Hx; apply HW; apply shad_off; clear - Hx; lia]. }
  assert (OW2 : forall y, 2147450880 <= y < 0x10007fff8000 -> outside [(eOS E + 144, eOS E + 148); (eOS E + 160, eOS E + 168); (esp E + 87, esp E + 88)] y).
  { intros y Hy. cbn [outside]. repeat split; try exact I; clear - Hy EHI LO1 LQ; ul. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (w_hex2 i 0x1002 w pb2 (wz pp2) (wz ep2) 0 fill2 dum2 ja2 jb2 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc m2 Q0 QH ESEG);
    [clear - ELO LQ; ul| exact E64| clear; lia| exact FR2| exact OSC2| exact VT2| exact (SHOF _ OW2)| exact (SHLF _ OW2)| exact MI2]|].
  cbv beta. intros ms3 (m3 & x12' & x13' & x14' & -> & MU3 & WM3 & MI3 & OSC3 & FR3 & B3). apply evt_done. unfold ELSTX.
  assert (GI3 : GI 0x1008 4 (fun g => g = 0x20 \/ g = 0x30) (efrL E (firstn 7 w ++ [Z_to_bv 8 48])) (k + 2) Σ2 m3).
  { eapply (GINVA_cws _ _ _ 0x1008 4 _ _ _ _ Σ2 m2 m3 _ fill2 GI2 MU3 WM3 MI3); [| exact FR3| rewrite !efrL_size; reflexivity| | exact FOK2].
    - intros a. cbn [outside]. unfold own. cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk]. clear. lia.
    - exists pb2, pp2, ep2, dum2, ja2, jb2. split; [rewrite osflat_eq; exact OSC3| exact PI2]. }
  clear GI2 MI2 FR2 OSC2 SHL2 SHO2 VT2 SHOF SHLF OW2 MU3 WM3 OSC3.
  pose proof (g_setfill RT AF PMc FDO MST (e_G E) GOK) as GSF. cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in GSF.
  replace (eOS E + 128) with (e_F E + 272) by (clear; lia).
  eapply (GSF 0x1008 4 _ _ (k + 2) Σ2 K (esp E + 87) 48);
    [exact SETF| exact GI3| intros f Hf; exact Hf| exact B3| clear; lia| clear; lia| clear; lia
    | first [unfold FRAMES_TOT; unfold FRAMES_MAX in FRB; clear - FRB; lia | unfold FRAMES_MAX in *; clear - FRB; lia]
    | unfold esc_costA in CRB; clear - CRB KB K0 Hi; lia|].
  clear GSF GI3 B3 FR3 MI3 m3 m2. intros Σ4 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 m4 GI4.
  rewrite (ret_pc_even 0xb109c) by (clear; lia). replace (e_F E + 272) with (eOS E + 128) by (clear; lia).

  pose proof GI4 as (_ & MI4 & _). pose proof (efacts _ _ _ _ _ _ _ GI4) as (SVC4 & PB4 & SHV4 & SHP4 & _).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (w_hex3 i c 0x1002 v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 F4 fc m4 QSV);
    [clear - SVT; ul| clear - P0 PP; lia| clear - PL PLO LQ QT; ul| exact PP| exact PL| exact Hi| exact BI| clear - Hc; lia| exact SVC4| exact PB4| exact SHV4| exact SHP4| exact MI4]|].
  cbv beta. intros ms5 (x12'' & x13'' & x14'' & ->). apply evt_done. unfold ELSTX.
  pose proof (g_ins RT AF PMc FDO MST (e_G E) GOK) as GIN. cbn [e_G g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0] in GIN.
  replace (eOS E + 128) with (e_F E + 272) by (clear; lia).
  eapply (GIN EL_INS_I _ 0x1008 4 (fun f => f = 0x30) (fun f => f = 48) (fun f => f = 48) EL_INS_STACK_A _ (k + 2 + 1) Σ4 K c);
    [exact INSI| exact GI4| exact IOS0| intros f Hf; exact Hf| intros f ->; reflexivity| cbv beta; clear - Hc; lia| exact FRM
    | clear - LQ; ul| first [unfold FRAMES_TOT; unfold FRAMES_MAX in FRB; clear - FRB; lia | unfold FRAMES_MAX in *; clear - FRB; lia]
    | unfold esc_costA in CRB; clear - CRB KB K0 Hi; lia|].
  clear GIN GI4 MI4 SVC4 PB4 SHV4 SHP4 m4. intros Σ5 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F5 fc5 m5 GI5 FRM5.
  rewrite (ret_pc_even 0xb10dc) by (clear; lia). replace (e_F E + 272) with (eOS E + 128) by (clear; lia).

  pose proof GI5 as (_ & MI5 & _ & _ & _ & _ & _ & (fill5 & OX5 & FOK5) & _ & _ & _ & (FR5 & _) & _). cbn [e_G g_q g_F] in OX5, FR5.
  destruct OX5 as (pb5 & pp5 & ep5 & dum5 & ja5 & jb5 & OSC5 & PI5). rewrite osflat_eq in OSC5.
  pose proof (efacts _ _ _ _ _ _ _ GI5) as (_ & _ & _ & _ & SHL5 & SHO5 & (VT5 & _) & _).
  assert (OW5 : forall y, 2147450880 <= y < 0x10007fff8000 -> outside [(eOS E + 144, eOS E + 148)] y).
  { intros y Hy. cbn [outside]. repeat split; try exact I; clear - Hy EHI LO1 LQ; ul. }
  assert (SHOF : forall m', munch [(eOS E + 144, eOS E + 148)] m5 m' -> wmono bsegs m5 m' -> shz m' (eOS E) 288).
  { intros m' MU _. eapply (shz_munch m5 m' _ _ _ SHO5 MU); [clear - E0; lia| clear - ELO LQ QT; ul| intros x Hx; apply OW5; apply shad_off; clear - Hx E0 ELO LQ QT; ul]. }
  assert (SHLF : forall m', munch [(eOS E + 144, eOS E + 148)] m5 m' -> wmono bsegs m5 m' -> shz m' 0x168e08 24).
  { intros m' MU _. eapply (shz_munch m5 m' _ _ _ SHL5 MU); [clear; lia| clear; lia| intros x Hx; apply OW5; apply shad_off; clear - Hx; lia]. }
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (w_hex4 i 0x1002 (firstn 7 w ++ [Z_to_bv 8 48]) pb5 (wz pp5) (wz ep5) 0x1008 0 fill5 dum5 ja5 jb5 w0 w1 w2 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F5 fc5 m5 Q0 QH ESEG);
    [clear - ELO LQ; ul| exact E64| clear; lia| exact F0| clear - FLO LQ QT; ul| exact FR5| exact OSC5| exact VT5| exact SHOF| exact SHLF| exact MI5]|].
  cbv beta. intros ms6 (m6 & y10 & y11 & -> & MU6 & WM6 & MI6 & OSC6). apply evt_done. unfold ELSTA.
  assert (GI6 : GI 0x1002 0 FILLOK (efrL E (firstn 7 w ++ [Z_to_bv 8 48])) (k + 2 + 1 + 1) Σ5 m6).
  { eapply (GINVA_restream _ _ _ 0x1002 0 FILLOK _ _ Σ5 m5 m6 fill5 GI5);
      [eapply munch_weaken; [| exact MU6]; intros x Hx; cbn [outside] in Hx |- *; clear - Hx; lia| exact WM6| exact MI6| | rewrite FOK5; right; right; reflexivity].
    exists pb5, pp5, ep5, dum5, ja5, jb5. split; [rewrite osflat_eq; exact OSC6| exact PI5]. }
  eapply (esc_joinA K i Σ5 m6 (k + 4) (firstn 7 w ++ [Z_to_bv 8 48]) _ w0 w1 w2 y10 y11 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 F5 fc5);
    [replace (k + 4) with (k + 2 + 1 + 1) by (clear; lia); exact GI6| exact FRM5| exact Hi| exact LH| clear - K0; lia| clear - KB; lia| exact HK| exact HX].
Qed.

Lemma esc_charA : forall (K : config -> Prop) (i : Z) (Σ : rts RT) (m : mem) (k : Z) (w : list byte)
    (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
  GI 0x1002 0 FILLOK (efrL E w) k Σ m -> frm0 fc -> 0 <= i < eL E -> eL E < 2^62 -> 0 <= k -> k <= 1 + 4 * i ->
  (i + 1 < eL E -> EKLOOPA K (i + 1)) -> EEXITA K ->
  aevt RT PMc Σ K (ELSTA 0xb0f04 i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m).
Proof using AF FDO MST PUT SETF INSI EOK SVC0 PB0 DCC CRB FRB.
  intros until fc. intros GI0 FRM Hi LH K0 KB HK HX. facts EOK.
  assert (Q0 : 0 <= esp E) by (clear - LO1 LQ; ul). assert (QH : e_q E < 2^63) by (clear - QT; ul).

  assert (CH : exists c, 0 <= c < 256 /\ firstn 1 (skipn (Z.to_nat i) (e_bs E)) = [Z_to_bv 8 c]).
  { destruct (skipn (Z.to_nat i) (e_bs E)) as [|b rest] eqn:SK.
    - exfalso. pose proof (length_skipn (Z.to_nat i) (e_bs E)) as LS. rewrite SK in LS. cbn in LS. clear - LS Hi. lia.
    - exists (bv_unsigned b). split; [pose proof (bv_unsigned_in_range _ b) as R; unfold bv_modulus in R; cbn in R; clear - R; lia|].
      cbn. f_equal. symmetry. apply bitvector.definitions.Z_to_bv_bv_unsigned. }
  destruct CH as (c & Hc & BI).
  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & _). cbn [e_G g_q g_F] in FR0.
  pose proof (efacts _ _ _ _ _ _ _ GI0) as (SVC & PB & SHV & SHP & _).
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (w_ch i c x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 F fc m);
    [exact QSV| clear - SVT; ul| clear - P0 PP; lia| clear - PL PLO LQ QT; ul| exact PP| exact PL| exact Hi| exact BI| exact Hc| exact SVC| exact PB| exact SHV| exact SHP| exact MI0]|].
  cbv beta. intros ms1 (z11 & z13 & ->).
  assert (CASES : is_elit c \/ (c = 11 \/ (0 <= c <= 31 /\ ~ (8 <= c <= 13))) \/ (32 <= c < 256 /\ c <> 34 /\ c <> 92)) by (unfold is_elit; clear - Hc; lia).
  destruct CASES as [CL|[CHX|(C32 & N34 & N92)]].
  - eapply evt_cut; [eapply (w_lit i c w x1 x5 x6 x7 z11 z13 x15 x16 x17 x28 x29 x30 x31 F fc m Q0 QH CL FR0 MI0)|].
    cbv beta. intros ms2 (y13 & y14 & ->). apply evt_done.
    eapply (esc_litA K i c Σ m k w); [exact GI0| exact FRM| exact Hi| exact LH| exact CL| exact K0| exact KB| exact HK| exact HX].
  - eapply evt_cut; [eapply (w_hexin i c w x1 x5 x6 x7 z11 z13 x15 x16 x17 x28 x29 x30 x31 F fc m Q0 QH ltac:(clear - P0 PP; lia) ltac:(clear - PL PLO LQ QT; ul) Hi CHX FR0 MI0)|].
    cbv beta. intros ms2 (y11 & y12 & y13 & ->). apply evt_done.
    eapply (esc_hexA K i c Σ m k w); [exact GI0| exact FRM| exact Hi| exact LH| clear - CHX Hc; lia| exact BI| exact K0| exact KB| exact HK| exact HX].
  - eapply evt_cut; [eapply (w_ownin i c w x1 x5 x6 x7 z11 z13 x15 x16 x17 x28 x29 x30 x31 F fc m Q0 QH ltac:(clear - P0 PP; lia) ltac:(clear - PL PLO LQ QT; ul) Hi C32 N34 N92 FR0 MI0)|].
    cbv beta. intros ms2 (y11 & y12 & y13 & ->). apply evt_done.
    eapply (esc_ownA K i c Σ m k w); [exact GI0| exact FRM| exact Hi| exact LH| exact Hc| exact K0| exact KB| exact HK| exact HX].
Qed.

Lemma esc_loopA : forall (n : nat) (i : Z) (K : config -> Prop),
  0 <= i -> i + Z.of_nat n + 1 = eL E -> eL E < 2^62 -> EEXITA K -> EKLOOPA K i.
Proof using AF FDO MST PUT SETF INSI EOK SVC0 PB0 DCC CRB FRB.
  induction n as [|n IH]; intros i K I0 IK LH HX; unfold EKLOOPA; intros until fc; intros GI0 FRM K0 KB.
  - eapply esc_charA; [exact GI0| exact FRM| clear - I0 IK; lia| exact LH| exact K0| exact KB| intros C; exfalso; clear - C IK; lia| exact HX].
  - eapply esc_charA; [exact GI0| exact FRM| clear - I0 IK; lia| exact LH| exact K0| exact KB| intros _; apply IH; [clear - I0; lia| clear - IK; lia| exact LH| exact HX]| exact HX].
Qed.

Lemma esc_bodyA : forall (K : config -> Prop) (Σ : rts RT) (m : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
  GI 0x1002 0 FILLOK (efr0 E) 1 Σ m -> frm0 fc -> EPOST K ->
  aevt RT PMc Σ K (MS (mkR (wz 0xb0e14) (wz (esp E)) (e_gp E) (wz TPV_A) t0 t1 t2 (wz (e_q E)) (wz (esp E)) (wz (e_f0 E)) a1 a2 a3 a4 a5 a6 a7
                          (wz (eOS E + 128)) (wz (e_SV E)) s4 s5 s6 s7 s8 s9 (wz SHB) s11 t3 t4 t5 t6)
                     F (ret_pc (wz 0xb0e14)) fc None m (seg_rom bsegs)).
Proof using AF FDO MST PUT SETF INSI EOK SVC0 PB0 DCC CRB FRB.
  intros until fc. intros GI0 FRM HK. facts EOK.
  assert (Q0 : 0 <= esp E) by (clear - LO1 LQ; ul). assert (QH : e_q E < 2^63) by (clear - QT; ul).
  assert (LH : eL E < 2^62) by (clear - PL PLO LQ QT P0 PP; ul).

  pose proof GI0 as (_ & MI0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR0 & _) & WF0 & WS0 & _). cbn [e_G g_q g_ff g_FS g_ffk] in FR0, WF0, WS0.
  change (fs_size 0) with 64 in WF0, WS0. replace (64 - 8) with 56 in WF0 by reflexivity. change (64 / 8) with 8 in WS0.
  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (e_walk1 E t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 F fc m Q0 QH F0);
    [clear - FLO LQ; ul| clear - F64; Z.div_mod_to_equations; lia| clear - QSV LQ LO1; ul| clear - SVT; ul| clear - SHLO LQ; ul| exact SHAP| exact FR0| exact WF0| exact WS0| exact MI0]|].
  cbv beta. intros ms1 (m1 & -> & MU1 & WM1 & MI1 & FR1).
  assert (GI1 : GI 0x1002 0 FILLOK ([C8 (wz 0); EJ E 0; C8 (wz (e_f0 E)); EJ E 2; EJ E 3; EJ E 4; EJ E 5; EJ E 6; EJ E 7; EJ E 8; EJ E 9] ++ esaves E) 1 Σ m1).
  { eapply (GINVA_cw RT AF (e_G E) GOK _ _ _ _ _ _ Σ m m1 _ GI0 MU1 WM1 MI1);
      [(intros ?; unfold own; cbn [outside e_G g_q g_fsz g_ff g_ffk]; change (fs_size 0) with 64; change (64 / 8) with 8; clear; lia)| exact FR1| reflexivity]. }
  clear GI0 MI0 FR0 WF0 WS0 MU1 WM1 FR1 m.

  pose proof GI1 as (_ & MI1' & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR1 & _) & _). cbn [e_G g_q] in FR1.
  pose proof (efacts _ _ _ _ _ _ _ GI1) as (SVC1 & _ & SHV1 & _).
  eapply evt_cut; [eapply (e_walk2 E); [exact Q0| exact QH| exact F0| clear - FLO LQ QT; ul| exact QSV| clear - SVT; ul| clear - LH; lia| exact FR1| exact SVC1| exact SHV1| exact MI1']|].
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & FR2).
  assert (GI2 : GI 0x1002 0 FILLOK (efr1 E) 1 Σ m2).
  { eapply (GINVA_cw RT AF (e_G E) GOK _ _ _ _ _ _ Σ m1 m2 _ GI1 MU2 WM2 MI2);
      [(intros ?; unfold own; cbn [outside e_G g_q g_fsz g_ff g_ffk]; change (fs_size 0) with 64; change (64 / 8) with 8; clear; lia)| exact FR2| reflexivity]. }
  clear GI1 MI1' MI1 FR1 SVC1 SHV1 MU2 WM2 m1.
  destruct (eL E =? 0) eqn:EL0.
  -
    apply Z.eqb_eq in EL0. apply evt_done.
    pose proof (esc_exitA K HK) as HX. unfold EEXITA in HX.
    eapply (HX Σ m2 1 (nth 0 (e_j E) []) [EJ E 2; EJ E 3; EJ E 4; EJ E 5; EJ E 6; EJ E 7; C8 (wz (e_f0 E)); EJ E 9]);
      [exact GI2| reflexivity| exact FRM| clear; lia| rewrite EL0; clear; lia].
  -
    apply Z.eqb_neq in EL0.
    pose proof GI2 as (_ & MI2' & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR2' & _) & _). cbn [e_G g_q] in FR2'.
    eapply evt_cut; [eapply (e_walk3 E); [exact Q0| exact QH| exact F0| clear - FLO LQ QT; ul| exact QSV| clear - SVT; ul| exact E0| clear - ELO LQ QT; ul| exact FR2'| exact MI2']|].
    cbv beta. intros ms3 (m3 & b0 & b1 & b2 & b3 & -> & MU3 & WM3 & MI3 & FR3). apply evt_done.
    assert (GI3 : GI 0x1002 0 FILLOK (efrL E (nth 9 (e_j E) [])) 1 Σ m3).
    { eapply (GINVA_cw RT AF (e_G E) GOK _ _ _ _ _ _ Σ m2 m3 _ GI2 MU3 WM3 MI3);
        [(intros ?; unfold own; cbn [outside e_G g_q g_fsz g_ff g_ffk]; change (fs_size 0) with 64; change (64 / 8) with 8; clear; lia)| exact FR3| reflexivity]. }
    assert (LP : EKLOOPA K 0).
    { apply (esc_loopA (Z.to_nat (eL E - 1)) 0 K); [clear; lia| rewrite Z2Nat.id; [clear; lia| clear - EL0; lia]| exact LH| exact (esc_exitA K HK)]. }
    unfold EKLOOPA in LP. eapply (LP Σ m3 1 (nth 9 (e_j E) [])); [exact GI3| exact FRM| clear; lia| clear; lia].
Qed.
End Esc.

Section TopF.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis PUT : os_put_cpsA RT PMc.
Hypothesis SETF : setfill_cpsA RT PMc.
Hypothesis INSI : ins_i_cpsA RT PMc.
Hypothesis DCC : forall Σ m, ART RT Σ m -> el_dccA m.

Local Ltac ul := unfold EL_ESC_STACK_A, EL_PUT_STACK_A, EL_INS_STACK_A, EL_SETFILL_STACK_A, FUZZ_STACK, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.

Theorem esc_okA : esc_cpsA RT PMc.
Proof.
  unfold esc_cpsA. intros Σ K F q lo SV P L fill p n8 bs ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m
    FDO MST INF OSX0 FOK0 SHO0 LB0 TPL0 IOS0 FRM SVC QSV SVT SV8 PB LEN L0 INP P8 N8 PP PL HA MI ST LO2 LO1 NEED QT Q32 FRB CRB HK.
  pose proof (af_sp0_range RT AF Σ m HA) as SPR. pose proof (af_frames_range RT AF Σ m F 3%nat HA INF) as (F0 & FHI & FSG & FLV).
  pose proof (af_frames_align RT AF Σ m F 3%nat HA INF) as [F64 _]. change (fs_size 3) with 512 in FHI, FSG, FLV.
  rewrite <- LEN in SVC, PL, CRB.

  apply (aevt_evt RT AF PMc MST).
  eapply evt_cut; [eapply (e_walk0 q lo (F + 272) SV ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m);
    [exact ST| clear - NEED; ul| clear - LO1; ul| clear - QT; ul| exact Q32| clear - F0 FHI SPR; ul| clear - QSV SVT NEED LO1; ul| exact (af_client_consts RT AF Σ m HA)| exact MI]|].
  cbv beta. intros ms1 (m1 & a1' & js & -> & MU1 & WM1 & MI1 & ST1 & FR1 & LJ). apply evt_done. unfold entry_st.
  assert (EQ : bv_unsigned (wz (q - 192)) = q - 192) by (apply unsigned_lit; clear - NEED LO1 QT; ul).
  assert (PRES1 : forall a : word, aclient (rt_live RT Σ) (rt_frames RT Σ) q (bv_unsigned a) -> m1 a = m a).
  { intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. destruct (aclient_split_c RT AF Σ m q _ HA Ha); clear - H NEED LO2; ul. }

  eapply (aevt_smalloc0 RT RC PMc FDO MST Σ K); [reflexivity| clear - FRB; lia| unfold esc_costA in CRB; clear - CRB L0 LEN; lia| | exact MI1| | intros EF; rewrite EF in INF; exact (False_ind _ INF)|].
  { apply (art_client_write RT AF Σ m m1 (q - 192) HA ltac:(clear - NEED LO2; ul)); [| exact WM1].
    intros a Ha. apply MU1. cbn [outside]. split; [| exact I]. intros Hin. apply Ha. left. clear - Hin QT; ul. }
  { unfold call_ok. rewrite EQ. split; [exact ST1|]. split; [exact LO2|]. split; [clear - NEED; ul|]. split; [clear - QT; ul| clear - Q32; Z.div_mod_to_equations; lia]. }
  intros Σ1 f0 w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 w3 w4 w5 w6 F1 m2 (HA2 & MI2 & WM2 & ST2) PRES2 WRF WRS FRS1 LV1 SP1 CRE F0P F064 F0T.
  rewrite EQ in ST2, PRES2.
  set (E := mkEC q lo F f0 (rt_live RT Σ) (rt_frames RT Σ) (rt_sp0 RT Σ) (rt_credit RT Σ) m SV P bs p n8 gp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 js).
  assert (GOK : gctx_ok (e_G E)).
  { subst E. apply (gctx_ok_intro RT AF _ Σ1 m2 HA2); cbn [e_G e_q e_lo e_F e_f0 e_L e_rfr e_sp0 e_cr e_m0 g_q g_fsz g_lo g_F g_ff g_ffk g_rfr g_L g_sp0 g_cr g_m0].
    - exact FRS1. - exact LV1. - exact SP1. - clear - Q32; Z.div_mod_to_equations; lia. - clear; lia. - clear - QT; lia. - clear - NEED; ul. - exact LO1. - exact LO2.
    - exact INF. - left; reflexivity. }
  assert (EOK : ectx_ok E).
  { pose proof (af_live_range RT AF Σ m p n8 HA INP) as (P0 & P1 & P2).
    split; [exact GOK|]. subst E. cbn [e_q e_lo e_F e_f0 e_L e_rfr e_sp0 e_cr e_m0 e_SV e_P e_bs e_p e_n8 e_j].
    split; [split; [exact QSV| split; [exact SVT| exact SV8]]|].
    split; [split; [exact INP|]; split; [exact P8|]; split; [exact N8|]; split; [exact PP|]; split; [exact PL|]; split; [exact P0|]; split; [clear - P1 LO2; lia| exact P2]|].
    split; [exact IOS0|]. split; [exact LJ| exact NEED]. }

  assert (AGc : forall Pp : Z -> Prop, (forall x, Pp x -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x) -> agree_on Pp m m2).
  { intros Pp HP a Ha. pose proof (HP _ Ha) as CA. rewrite (PRES2 a); [exact (PRES1 a CA)|]. apply (aclient_mono _ _ _ _ _ _ _ CA); [auto| auto| clear; lia]. }
  assert (CLF : forall x, F <= x < F + 504 -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x).
  { intros x Hx. right; right; right; left. exists F, 3%nat. split; [exact INF| change (fs_size 3) with 512; clear - Hx; lia]. }
  assert (CLS : forall x, shad F <= x < shad F + 64 -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x).
  { intros x Hx. do 4 right. exists F, 3%nat. split; [exact INF| change (fs_size 3) with 512; unfold shad in *; clear - Hx F64; Z.div_mod_to_equations; lia]. }
  assert (CLT : forall x, client_static x -> aclient (rt_live RT Σ) (rt_frames RT Σ) q x) by (intros x Hx; right; left; exact Hx).
  assert (GI0 : GINVA RT (e_G E) 0x1002 0 FILLOK (efr0 E) 1 Σ1 m2).
  { unfold GINVA. split; [exact HA2|]. split; [exact MI2|].
    split; [subst E; exact FRS1|]. split; [subst E; exact LV1|]. split; [subst E; exact SP1|]. split; [subst E; cbn [e_G e_cr g_cr]; clear - CRE; lia|].
    split; [subst E; exact ST2|].
    split. { exists fill. split; [| exact FOK0]. subst E. cbn [e_G g_F e_F]. apply (proj1 (OSX_W m2 (F + 144) fill)).
             apply (OSX_agree m m2 _ _ OSX0); [| exact (wmono_trans _ _ _ _ WM1 WM2)]. apply AGc. intros x Hx. apply CLF. clear - Hx. lia. }
    split. { subst E. cbn [e_G g_F e_F]. apply (bytes_at_agree bsegs m m2 _ _ SHO0). apply AGc. intros x Hx. rewrite repeat_length in Hx. apply CLS.
             unfold shad in *. clear - Hx F64. Z.div_mod_to_equations. lia. }
    split. { unfold el_tploc in *. apply (rw_cells_agree_nw bsegs m m2 _ _ TPL0). apply AGc. intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply CLT.
             unfold EL_TPLOC_A in Hx. apply client_static_intro; clear - Hx; lia. }
    split. { apply (LOCBA_agree m m2 LB0). apply AGc. intros x Hx. apply CLT. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. apply client_static_intro; clear - Hx; lia. }
    split. { split; [| rewrite efr0_size; reflexivity]. subst E. unfold efr0, esaves, EJ. cbn [e_G g_q e_q e_j e_f0 e_ra e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11 app].
             apply (rw_cells_agree_nw bsegs m1 m2 _ _ FR1). intros a Ha. apply PRES2. left. unfold fa_saved in Ha. cbn [cells_size csize Nat.add length app] in Ha.
             clear - Ha QT. ul. }
    split; [subst E; exact WRF|]. split; [subst E; exact WRS|].
    subst E. cbn [e_G g_L g_rfr g_q g_fsz g_m0 g_F e_L e_rfr e_q e_m0 e_F]. intros a CA OU. replace (q - 192 + 192) with q in CA by (clear; lia).
    rewrite (PRES2 a); [exact (PRES1 a CA)|]. apply (aclient_mono _ _ _ _ _ _ _ CA); [auto| auto| clear; lia]. }

  replace (F + 272) with (F + 144 + 128) by (clear; lia).
  apply (esc_bodyA RT AF PMc FDO MST PUT SETF INSI DCC E EOK SVC PB CRB FRB K Σ1 m2 w0 w1 w2 c1 c2 c3 c4 c5 c6 c7 s4 s5 s6 s7 s8 s9 s11 w3 w4 w5 w6 F1 fc GI0 FRM).

  unfold EPOST. clear GI0 EOK GOK. subst E.
  cbn [e_q e_lo e_F e_f0 e_L e_rfr e_sp0 e_cr e_m0 e_SV e_P e_bs e_p e_n8 e_j e_gp e_ra e_s0 e_s1 e_s2 e_s3 e_s4 e_s5 e_s6 e_s7 e_s8 e_s9 e_s10 e_s11].
  intros Σ' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' m' HA' MI' ST' OX' SHO' LB' TPL' FRM' LV' FRS' SP' CR' PRES'.
  rewrite LEN in CR'.
  exact (HK Σ' u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F' fc' m' HA' MI' ST' OX' SHO' LB' TPL' FRM' LV' FRS' SP' CR' PRES').
Qed.
End TopF.
