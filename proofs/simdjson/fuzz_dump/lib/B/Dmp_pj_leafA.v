(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Pj_defsA El_defsA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition DMP_PJ_PUT_A : Z := 0xb13cc.
Definition DMP_LIT_NULL_A : Z := 0x234c0.
Definition pjR (q f : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) : bvmap 5 word :=
  mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7
      s9 (Z_to_bv 64 f) s5 s4 s6 (Z_to_bv 64 f) s8 (Z_to_bv 64 SHB) s11 (Z_to_bv 64 (shad f)) t3 t4 t5 t6.

Definition pj_slot (f k : Z) : Z := f + (32 + 16 * k).
Definition pj_gofs (k : Z) : Z := 4 + 2 * k.

Definition pj_endl_pc (k : Z) : Z :=
  match k with 1 => 0xaf0bc | 2 => 0xaf1dc | 3 => 0xaf100 | 4 => 0xaf070 | 5 => 0xaf324 | 6 => 0xaf280 | _ => 0xaf028 end.

Ltac pj_endl_consts f :=
  lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc0) _ _ _ _) =>
    lazymatch pc0 with context [pj_endl_pc ?k] =>
      let v := eval cbv in (32 + 16 * k) in change (pj_slot f k) with (f + v) in *;
      let g := eval cbv in (pj_gofs k) in change (pj_gofs k) with g in *;
      let p := eval cbv in (pj_endl_pc k) in
      let p' := eval cbv in (p + 28) in
      change (pj_endl_pc k + 28) with p' in *; change (pj_endl_pc k) with p in *
    end end.

Lemma pj_endl1 : forall (k q f : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (g b : list byte) F fc (m : mem),
  1 <= k <= 6 -> 0 < f -> f + 256 < 2^63 -> 0 <= shad f -> shad f + 32 < 2^63 -> (f + 256 <= shad f \/ shad f + 32 <= f) ->
  rw_cells bsegs m (shad f + pj_gofs k) [CB 1 g] -> rw_cells bsegs m (pj_slot f k) [CB 1 b] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc k + 28)) a0 (Z_to_bv 64 (pj_slot f k)) (Z_to_bv 64 1) a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m' (seg_rom bsegs)
      /\ munch [(shad f + pj_gofs k, shad f + pj_gofs k + 1); (pj_slot f k, pj_slot f k + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (shad f + pj_gofs k) [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m' (pj_slot f k) [C1 (Z_to_bv 8 10)])
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 (pj_endl_pc k)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros K F0 FH SH0 SHH SEP FG FB MI.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (shad f)) = shad f) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_PUT_A.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia. clear K.
  destruct KC as [-> |[-> |[-> |[-> |[-> | ->]]]]]; pj_endl_consts f;
  (pose proof (wmono_refl bsegs m) as WM;
   lazymatch goal with |- evt _ (fun _ => exists _, _ /\ (munch ?W _ _ /\ _)) _ => pose proof (munch_refl W m) as MU end;

   zstep; zstep; ls; zstep; ls; zstep; zstep;
   apply evt_done; eexists; split; [cbv delta [mkR]; reflexivity|];
   split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]; split; [exact WM|]; split; [eassumption|]; split; eassumption).
Qed.

Lemma pj_endl2 : forall (k q f : Z) (gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (g : list byte) F fc (m : mem),
  1 <= k <= 6 -> 0 <= shad f -> shad f + 32 < 2^63 ->
  rw_cells bsegs m (shad f + pj_gofs k) [CB 1 g] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a0' : word),
      ms = MS (pjR q f gp ra a0' a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_EXIT_A) fc None m' (seg_rom bsegs)
      /\ munch [(shad f + pj_gofs k, shad f + pj_gofs k + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (shad f + pj_gofs k) [C1 (Z_to_bv 8 (-8))])
    (MS (pjR q f gp ra a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 (pj_endl_pc k + 28)) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros K SH0 SHH FG MI.
  assert (ES : bv_unsigned (Z_to_bv 64 (shad f)) = shad f) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_EXIT_A.
  assert (KC : k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6) by lia. clear K.
  destruct KC as [-> |[-> |[-> |[-> |[-> | ->]]]]]; pj_endl_consts f;
  (pose proof (wmono_refl bsegs m) as WM;
   lazymatch goal with |- evt _ (fun _ => exists _ _, _ /\ (munch ?W _ _ /\ _)) _ => pose proof (munch_refl W m) as MU end;

   zstep; ls; zstep;
   apply evt_done; do 2 eexists; split; [cbv delta [mkR]; reflexivity|];
   split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]; split; [exact WM|]; split; [eassumption|]; eassumption).
Qed.

Lemma pj_null1 : forall (E : aenvA) (q f osp i : Z) (j80 : list byte) (gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i < ae_n E -> 0 <= ae_T E i < 2^64 -> ttype (ae_T E i) = 110 ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells bsegs m (q - 256 + 80) [CB 8 j80; C8 (Z_to_bv 64 osp)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc 1)) (Z_to_bv 64 osp) (Z_to_bv 64 DMP_LIT_NULL_A) (Z_to_bv 64 4) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m' (seg_rom bsegs)
      /\ munch [(q - 176, q - 168)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (q - 176) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)])
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK IR TR TY QLO QH OR AI SHZT FO MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, DMP_PJ_PUT_A, DMP_LIT_NULL_A. cbn [pj_endl_pc].
  pose proof (munch_refl [(q - 176, q - 168)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.

  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.

  step. astep. first [change (ae_T E i / 2 ^ 56) with (ttype (ae_T E i)) | idtac]. rewrite TY.

  pj_run 0xb13cc.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|].
  split; [eassumption|]. split; [eassumption|]. replace (q - 176) with (q - 256 + 80) by lia. eassumption.
Qed.

Definition DMP_INS_B_A : Z := 0x111a40.  Definition DMP_INS_L_A : Z := 0x111c0c.  Definition DMP_INS_UL_A : Z := 0x111dd8.  Definition DMP_INS_D_A : Z := 0x111fa4.
Definition pj_boolv (w : Z) : Z := if w =? 116 * 2^56 then 1 else 0.

Lemma pj_boolv_xor : forall w, 0 <= w -> Z.b2z (Z.lxor w 8358680908399640576 <? 1) = pj_boolv w.
Proof.
  intros w W. unfold pj_boolv. change (116 * 2^56) with 8358680908399640576.
  destruct (Z.eqb_spec w 8358680908399640576) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (0 <= Z.lxor w 8358680908399640576) by (apply (proj2 (Z.lxor_nonneg _ _)); lia).
    assert (Z.lxor w 8358680908399640576 <> 0) by (intros H0; apply NE; apply Z.lxor_eq; exact H0).
    destruct (Z.ltb_spec (Z.lxor w 8358680908399640576) 1); [lia| reflexivity].
Qed.

Lemma shz_munch_hi : forall W (m m' : mem) a n, shz m a n -> munch W m m' -> 0 <= a -> a + n <= 2^47 ->
  (forall y, 0 <= y < 2^45 -> outside W y) -> shz m' a n.
Proof.
  intros W m m' a n SH MU A0 AH HW x Hx. unfold shz in SH. rewrite <- (SH x Hx). cbn [ov_read_bytes].
  rewrite (MU (wa _)); [reflexivity|]. unfold wa. rewrite unsigned_lit by (Z.div_mod_to_equations; lia).
  apply HW. Z.div_mod_to_equations. lia.
Qed.

Ltac pj_tix E sp idx :=
  eapply evt_cut; [eapply (pj_tixE E sp idx); try eassumption; try lia;
    try (eapply AINV_A_munch; [eassumption| eassumption| eassumption| repeat constructor; cbn [fst]; lia]);
    try (eapply OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B.El_os_defsA.client_consts_munch; [eassumption| eassumption| intros ? ?; cbn [outside]; repeat (split; try exact I); lia])|];
  cbv beta;
  let ms := fresh "ms" in let m1 := fresh "m" in let a4 := fresh "a4x" in let MU1 := fresh "MUt" in let WM1 := fresh "WMt" in
  let MI1 := fresh "MIt" in let ST1 := fresh "STt" in let AI1 := fresh "AIt" in let CC1 := fresh "CCt" in
  intros ms (m1 & a4 & -> & MU1 & WM1 & MI1 & ST1 & AI1 & CC1);
  rewrite ret_pc_even by first [lia | reflexivity];
  lazymatch type of MU1 with munch _ ?mm _ =>
  match goal with MU0 : munch ?W ?m0 mm, WM0 : wmono bsegs ?m0 mm |- _ =>
    repeat match goal with
    | H : rw_cells bsegs mm ?A ?cs |- _ =>
        eapply rw_cells_transport in H; [| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add map]; repeat split; lia]
    | H : shz mm ?a ?n |- _ =>
        eapply shz_munch_hi in H; [| exact MU1| lia| lia| intros ? ?; cbn [outside]; split; [lia| exact I]]
    end;
    let H := fresh "MU" in let H2 := fresh "WM" in
    assert (H : munch W m0 m1) by (eapply munch_trans; [exact MU0| eapply munch_weaken; [| exact MU1]; intros ? ?; cbn [outside] in *; lia]);
    assert (H2 : wmono bsegs m0 m1) by (eapply wmono_trans; [exact WM0| exact WM1]);
    clear MU0 MU1 WM0 WM1
  end end.

Ltac pj_retape E SHZT RDT idx :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of SHZT with
    | shz mm _ _ => idtac
    | shz ?m00 _ _ =>
      lazymatch goal with MUx : munch _ m00 mm |- _ =>
        eapply shz_munch_hi in SHZT; [| exact MUx | lia | lia | intros ? ?; cbn [outside]; repeat (split; try exact I); lia] end
    end;
    lazymatch goal with AIx : AINV_A _ mm |- _ =>
      let TB := fresh "TAPEB" in pose proof AIx as (TB & _); try clear RDT;
      pose proof (tape_read _ (ae_TAPE E) (ae_tws E) idx TB ltac:(lia)) as RDT end end.

Ltac pr_at ps := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
  let b := eval vm_compute in (existsb (Z.eqb p) ps) in lazymatch b with true => idtac | false => fail end end.
Ltac pj_runs ps := repeat (tryif pr_at ps then fail else first [ls | (rewrite shr3_div; ls) | if_false | if_true | pj_gt]).

Lemma pj_bool1 : forall (E : aenvA) (q f osp i : Z) (j80 : list byte) (gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i < ae_n E -> 0 <= ae_T E i < 2^64 -> (ttype (ae_T E i) = 116 \/ ttype (ae_T E i) = 102) ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> client_consts m -> stk bsegs m (ae_lo E) (q - 256) -> ae_lo E <= q - 272 ->
  rw_cells bsegs m (q - 256 + 80) [CB 8 j80; C8 (Z_to_bv 64 osp)] ->
  rw_cells bsegs m (q - 256 + 136) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a2x a3x a4x s5x s9x : word),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc 2)) (Z_to_bv 64 osp) (Z_to_bv 64 (pj_boolv (ae_T E i))) a2x a3x a4x a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) s5x s6 s8 s9x s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_INS_B_A) fc None m' (seg_rom bsegs)
      /\ munch [(q - 272, q - 256); (q - 176, q - 168)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' (ae_lo E) (q - 256)
      /\ rw_cells bsegs m' (q - 176) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)])
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK IR TR TY QLO QH OR AI SHZT CC ST SLO FO FD MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, DMP_INS_B_A. cbn [pj_endl_pc].
  pose proof (munch_refl [(q - 272, q - 256); (q - 176, q - 168)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.

  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. astep. first [change (ae_T E i / 2 ^ 56) with (ttype (ae_T E i)) | idtac].
  destruct TY as [TY|TY]; rewrite TY; pj_run 0xaf190.
  all: zstep.
  all: pj_tix E (q - 256) i.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         lazymatch type of SHZT with shz ?m00 _ _ =>
         lazymatch goal with MUx : munch _ m00 mm, AIx : AINV_A _ mm |- _ =>
           eapply shz_munch_hi in SHZT; [| exact MUx | lia | lia | intros ? ?; cbn [outside]; repeat (split; try exact I); lia];
           let TB := fresh "TAPEB" in pose proof AIx as (TB & _); clear RDT;
           pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TB ltac:(lia)) as RDT end end end.
  all: chk0 SHZT (ae_TAPE E + 8 * i). all: step. all: if_false.
  all: pj_run 0x111a40.
  all: let GB := fresh "GB" in if_cases GB.
  all: first [ pj_at 0xaf1cc | (pj_run 0xaf1c8; zstep; pj_tix E (q - 256) i) ].
  all: pj_run 0x111a40.
  all: rewrite ?(pj_boolv_xor (ae_T E i)) by lia.
  all: apply evt_done; do 6 eexists; split; [atp_st_eq_goal|].
  all: split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: replace (q - 176) with (q - 256 + 80) by lia; eassumption.
Qed.

Definition pj_num_ins (t : Z) : Z := if t =? 108 then DMP_INS_L_A else DMP_INS_UL_A.
Definition pj_num_slot (t : Z) : Z := if t =? 108 then 6 else 5.

Lemma pj_num1 : forall (E : aenvA) (t q f osp i : Z) (j80 : list byte) (gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i + 1 < ae_n E -> (t = 108 \/ t = 117) -> ae_T E i = t * 2^56 ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) -> client_consts m -> stk bsegs m (ae_lo E) (q - 256) -> ae_lo E <= q - 272 ->
  rw_cells bsegs m (q - 256 + 80) [CB 8 j80; C8 (Z_to_bv 64 osp)] ->
  rw_cells bsegs m (q - 256 + 136) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 i)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a2x a3x a4x s5x s9x : word),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc (pj_num_slot t))) (Z_to_bv 64 osp) (Z_to_bv 64 (ae_T E (i + 1))) a2x a3x a4x (Z_to_bv 64 (t * 2^56)) a6 a7
                   (Z_to_bv 64 (ae_DOC E)) s5x s6 s8 s9x s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 (pj_num_ins t)) fc None m' (seg_rom bsegs)
      /\ munch [(q - 272, q - 256); (q - 176, q - 168)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' (ae_lo E) (q - 256)
      /\ rw_cells bsegs m' (q - 176) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)])
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IR TY WX QLO QH OR AI SHZT CC ST SLO FO FD MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A, pj_num_ins, pj_num_slot, DMP_INS_L_A, DMP_INS_UL_A.
  pose proof (munch_refl [(q - 272, q - 256); (q - 176, q - 168)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.

  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. astep. rewrite WX. destruct TY as [-> | ->]; cbn [Z.eqb Pos.eqb pj_endl_pc].
  all: pj_run 0xafc0c.
  all: pj_tix E (q - 256) i.
  all: pj_retape E SHZT RDT i.
  all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
         lazymatch goal with AIx : AINV_A _ mm |- _ =>
           let TB := fresh "TAPEB" in pose proof AIx as (TB & _);
           pose proof (tape_read _ (ae_TAPE E) (ae_tws E) (i + 1) TB ltac:(lia)) as RDT1;
           replace (ae_TAPE E + 8 * (i + 1)) with (ae_TAPE E + 8 * i + 8) in RDT1 by lia end end.
  all: pj_run 0xafc0c.
  all: shz_pose SHZT (ae_TAPE E + 8 * i). all: rewrite ?shr3_div. all: zstep. all: shz_norm.
  all: pj_run 0xafc0c.
  all: assert (DOC0 : 0 < ae_DOC E) by lia.
  all: assert (DOC7 : Z.land (ae_DOC E) 7 = 0) by (rewrite land7_mod by lia; exact D8).
  all: rewrite ?DOC7; cbn [Z.ltb Z.compare Z.b2z Z.land].
  all: rewrite ?(proj2 (Z.ltb_lt 0 (ae_DOC E)) DOC0); cbn [Z.b2z Z.land].
  all: if_false.
  all: pj_run 0xafc0c.
  all: pj_tix E (q - 256) (i + 1).
  all: pj_retape E SHZT RDT1 (i + 1).
  all: shz_pose SHZT (ae_TAPE E + 8 * (i + 1)). all: rewrite ?shr3_div. all: zstep. all: shz_norm.
  all: pj_runs [0x111c0c; 0x111dd8].
  all: apply evt_done; do 6 eexists; split; [atp_st_eq_goal|].
  all: split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|].
  all: split; [eassumption|]. all: split; [eassumption|]. all: split; [eassumption|].
  all: replace (q - 176) with (q - 256 + 80) by lia; eassumption.
Qed.

Lemma pj_dbl1 : forall (E : aenvA) (q f osp i : Z) (j80 : list byte) (gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> 0 <= i -> i + 1 < ae_n E -> ae_T E i = 100 * 2^56 ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells bsegs m (q - 256 + 80) [CB 8 j80; C8 (Z_to_bv 64 osp)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a1x a2x a3x : word),
      ms = MS (pjR q f gp (Z_to_bv 64 0xaf068) (Z_to_bv 64 (q - 256 + 136)) a1x a2x a3x a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 0xb01f0) fc None m' (seg_rom bsegs)
      /\ munch [(q - 176, q - 168)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (q - 176) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)])
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK I0 IR WX QLO QH OR AI SHZT FO MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & DOCC & _).
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (ae_DOC E)) = ae_DOC E) by (apply unsigned_lit; lia).
  assert (EI : bv_unsigned (Z_to_bv 64 i) = i) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_PJ_DISP_A.
  pose proof (munch_refl [(q - 176, q - 168)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.

  chk0 SHZT (ae_TAPE E + 8 * i). step. if_false.
  step. astep. rewrite WX.
  pj_run 0xb01f0.
  apply evt_done. do 4 eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|].
  split; [eassumption|]. split; [eassumption|]. replace (q - 176) with (q - 256 + 80) by lia. eassumption.
Qed.

Lemma pj_dbl2 : forall (q f osp : Z) (gp a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  rw_cells bsegs m (q - 176) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => ms = MS (pjR q f gp (Z_to_bv 64 (pj_endl_pc 4)) (Z_to_bv 64 osp) a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
                                F (Z_to_bv 64 DMP_INS_D_A) fc None m (seg_rom bsegs))
    (MS (pjR q f gp (Z_to_bv 64 0xaf068) a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6) F (Z_to_bv 64 0xaf068) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros QLO QH OR FO MI.
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  unfold pjR, DMP_INS_D_A. cbn [pj_endl_pc].
  pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  replace (q - 176) with (q - 256 + 80) in FO by lia.
  pj_run 0x111fa4.
  apply evt_done. atp_st_eq_goal.
Qed.

Definition DMP_LIT_LBRK_A : Z := 0x23520.  Definition DMP_LIT_LBRC_A : Z := 0x23580.
Definition pj_open_lit (t : Z) : Z := if t =? 91 then DMP_LIT_LBRK_A else DMP_LIT_LBRC_A.
Definition pj_open_ret (t : Z) : Z := if t =? 91 then 0xaf13c else 0xaefb4.

Lemma pj_open1 : forall (E : aenvA) (t q f osp i : Z) (gp ra a1 a2 a3 a4 a5 a6 a7 s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6 : word) (j80 : list byte) F fc (m : mem),
  aenvA_ok E -> 0 <= i < ae_n E -> 0 <= ae_T E i < 2^64 -> ttype (ae_T E i) = t -> (t = 91 \/ t = 123) ->
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  AINV_A E m -> shz m (ae_TAPE E) (8 * ae_n E) ->
  rw_cells bsegs m (q - 256 + 80) [CB 8 j80; C8 (Z_to_bv 64 osp)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem),
      ms = MS (pjR q f gp (Z_to_bv 64 (pj_open_ret t)) (Z_to_bv 64 osp) (Z_to_bv 64 (pj_open_lit t)) (Z_to_bv 64 1) a3 a4 a5 a6 a7
                   (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m' (seg_rom bsegs)
      /\ munch [(q - 256 + 80, q - 256 + 88)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (q - 256 + 80) [C8 (Z_to_bv 64 SHB); C8 (Z_to_bv 64 osp)])
    (MS (pjR q f gp ra (Z_to_bv 64 (ae_TAPE E + 8 * i)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 i) s6 s8 s9 s11 t0 t1 t2 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK IR TR TY TT QLO QH OR AI SHZT F80 MI.
  pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP in HT. unfold SEGTOP_A in *.
  pose proof AI as (TAPEB & _ & _ & _ & _).
  pose proof (tape_read _ (ae_TAPE E) (ae_tws E) i TAPEB ltac:(lia)) as RDT.
  assert (TS56 : Z.shiftr (ae_T E i) 56 = t).
  { rewrite Z.shiftr_div_pow2 by lia. change (ae_T E i / 2^56) with (ttype (ae_T E i)). exact TY. }
  unfold pjR, DMP_PJ_DISP_A, DMP_PJ_PUT_A, pj_open_lit, pj_open_ret, DMP_LIT_LBRK_A, DMP_LIT_LBRC_A, SHB, shad.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 (ae_TAPE E + 8 * i)) = ae_TAPE E + 8 * i) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(q - 256 + 80, q - 256 + 88)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  shz_pose SHZT (ae_TAPE E + 8 * i).
  destruct TT as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - repeat (tryif pr_at [0xb13cc] then fail else first [ls | (rewrite shr3_div; ls) | if_false | if_true | pj_gt | rewrite TS56]).
    apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; eassumption.
  - repeat (tryif pr_at [0xb13cc] then fail else first [ls | (rewrite shr3_div; ls) | if_false | if_true | pj_gt | rewrite TS56]).
    apply evt_done. eexists. split; [cbv delta [mkR]; reflexivity|].
    split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; eassumption.
Qed.

Lemma pj_close0 : forall (q osp : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 ->
  rw_cells bsegs m (q - 256 + 88) [C8 (Z_to_bv 64 osp)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 DMP_PJ_EXIT_A) (Z_to_bv 64 (q - 256)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (q - 256)) (Z_to_bv 64 osp) a1 (Z_to_bv 64 1) a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_CLOSE_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros QLO QH OR FO MI. unfold DMP_PJ_CLOSE_A, DMP_PJ_PUT_A, DMP_PJ_EXIT_A.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  pj_run 0xb13cc. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.

Lemma pj_close1 : forall (q f osp lit : Z) (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  0x6d5000 <= q - 256 -> q < 2^63 -> 0 <= osp < 2^64 -> 0 <= lit < 2^64 -> 0 < f -> f + 256 < 2^63 ->
  rw_cells bsegs m (q - 256) [C8 (Z_to_bv 64 lit); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)] ->
  rw_cells bsegs m (q - 256 + 88) [C8 (Z_to_bv 64 osp)] -> mem_inv bsegs m ->
  evt bsegs (fun ms => ms = MS (mkR (Z_to_bv 64 DMP_PJ_EXIT_A) (Z_to_bv 64 (q - 256)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (q - 256)) (Z_to_bv 64 osp) (Z_to_bv 64 lit) (Z_to_bv 64 1)
                                   a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 DMP_PJ_PUT_A) fc None m (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_LOOPX_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros QLO QH OR LR F0 FH F0C FO MI. unfold DMP_PJ_LOOPX_A, DMP_PJ_PUT_A, DMP_PJ_EXIT_A.
  assert (EQ : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  pj_run 0xb13cc. apply evt_done. cbv delta [mkR]. reflexivity.
Qed.
