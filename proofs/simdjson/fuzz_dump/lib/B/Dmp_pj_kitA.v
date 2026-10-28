(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Pj_defsA El_defsA Pj_ser_trefA El_os_defsA Dmp_hdefsA Dmp_pj_ifaceA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Ltac pj_at pc := lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?p) _ _ _ _) =>
  let b := eval vm_compute in (Z.eqb p pc) in lazymatch b with true => idtac | false => fail end end.
Ltac pj_gt := let G := fresh "G" in if_cases G; zify_cond G;
  [exfalso; rewrite ?unsigned_lit in G by lia; rewrite ?land7_mod in G by lia; lia|]; try clear G.
Ltac pj_run stop := repeat (tryif pj_at stop then fail else first [ls | (rewrite shr3_div; ls) | if_false | if_true | pj_gt]).

Definition DMP_PJ_SMRET_A : Z := 0xaee70.
Definition DMP_PJ_DISP_A : Z := 0xaef50.
Definition DMP_PJ_EXIT_A : Z := 0xaf5a8.
Definition DMP_PJ_LOOPX_A : Z := 0xaf53c.
Definition DMP_PJ_CLOSE_A : Z := 0xaf59c.
Definition DMP_PJ_ALOOP_A : Z := 0xaf4a0.
Definition DMP_PJ_OLOOP_A : Z := 0xaf738.
Definition DMP_PJ_DESC_A : Z := 0x1d174.

Definition pj_saved (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma pj_saved_size : forall ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11, cells_size (pj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) = 104%nat.
Proof. intros. reflexivity. Qed.

Definition pj_locals0 (j0 j1 : list byte) (osp : Z) (j2 j3 : list byte) : list cell := [CB 8 j0; CB 80 j1; C8 (Z_to_bv 64 osp); CB 48 j2; CB 8 j3].

Definition pj_mid0 (q lo osp doc i : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (a1' a2' : word) (j0 j1 j2 j3 : list byte),
    ms = entry_st (Z_to_bv 64 DMP_PJ_SMRET_A) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) (Z_to_bv 64 160)
                  a1' a2' a3 a4 a5 a6 a7
                  s2 s3 (Z_to_bv 64 i) (Z_to_bv 64 doc) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6 F fc e_stack_malloc_2 m1
    /\ munch [(q - 256, q)] m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (q - 256)
    /\ rw_cells bsegs m1 (q - 256) (pj_locals0 j0 j1 osp j2 j3)
    /\ rw_cells bsegs m1 (q - 104) (pj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

Lemma pj_walk0 : forall (q lo osp doc i : Z) (ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc (m : mem),
  stk bsegs m lo q -> lo <= q - 256 -> 0x6d5000 <= lo -> q < 2^63 -> q mod 32 = 0 -> 0 <= osp < 2^64 -> 0 <= doc < 2^64 -> 0 <= i < 2^64 ->
  client_consts m -> mem_inv bsegs m ->
  evt bsegs (pj_mid0 q lo osp doc i ra gp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m)
    (entry_st ra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 (Z_to_bv 64 osp) (Z_to_bv 64 doc) (Z_to_bv 64 i) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
       t3 t4 t5 t6 F fc DMP_PJ_A m).
Proof.
  intros until m. intros ST LO GLO SPH S32 RO RD RI (G1 & G2 & G3 & G4) MI.
  unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in *.
  unfold entry_st, DMP_PJ_A, pj_mid0, pj_saved, pj_locals0, DMP_PJ_SMRET_A, e_stack_malloc_2, TPV_A.
  pose proof ST as (STa & STb & _).
  pose proof (munch_refl [(q - 256, q)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).
  zstep.
  carve_frame 256%nat ST.
  apply (rw_cells_split_CB bsegs _ _ [] 256 _ [] [8; 80; 8; 48; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity].
  cbn [mk_CB_cells app] in FR.
  repeat match type of FR with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "j" in set (j := t) in FR; clearbody j end.
  lstep. do 13 zstep. zstep. zstep.
  rewrite (land_m32 (q + -256)) by lia.
  replace (32 * ((q + -256) / 32)) with (q + -256) by (Z.div_mod_to_equations; lia).
  do 7 zstep. step. rewrite (sx32_small 1) by lia. zstep. ls. zstep. if_false. zstep. zstep.

  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?rest) =>
    change (c0 :: c1 :: c2 :: c3 :: c4 :: rest) with ([c0; c1; c2; c3; c4] ++ rest) in FR end.
  apply rw_cells_app in FR. destruct FR as [FRl FRs]. cbn [cells_size csize Nat.add] in FRs.
  apply (rw_cells_forget_C8 bsegs _ _ [] _ _) in FRl. cbn [app] in FRl.
  replace (q + -256 + Z.of_nat 152) with (q - 104) in FRs by lia.
  replace (q + -256) with (q - 256) in * by lia.
  apply evt_done. do 7 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST|]. split; [exact FRl| exact FRs].
Qed.

Definition pj_locals1 (j0 j1 : list byte) (osp : Z) (j2 : list byte) (f doc i : Z) : list cell :=
  [CB 8 j0; CB 80 j1; C8 (Z_to_bv 64 osp); CB 8 (firstn 8 j2); C8 (Z_to_bv 64 f); CB 24 (firstn 24 (skipn 16 j2)); C8 (Z_to_bv 64 doc); C8 (Z_to_bv 64 i)].

Definition pj_sh_pro : list byte :=
  repeat (Z_to_bv 8 (-15)) 4 ++ [Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8); Z_to_bv 8 (-14);
                                  Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8); Z_to_bv 8 (-14); Z_to_bv 8 (-8)]
  ++ repeat (Z_to_bv 8 (-13)) 3.
Lemma pj_sh_pro_length : length pj_sh_pro = 20%nat.
Proof. reflexivity. Qed.
Definition pj_shadow0 (ls : list (list byte)) : list cell := map (fun l => CB 1 l) ls.
Definition pj_W1 (q f : Z) : list ivl :=
  [(q - 256 + 104, q - 256 + 112); (q - 256 + 136, q - 256 + 152); (f, f + 24); (shad f, shad f + 20); (q - 272, q - 256)].

Lemma pj_walk1 : forall (q f lo osp doc i TAPE : Z) (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3x s6 s7x s8 s2x s10x s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 j3 h0 h1 h2 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 20%nat ->
  0 < f -> f + 256 <= lo -> shad f + 32 <= lo -> 0 <= shad f -> (f + 256 <= shad f \/ shad f + 32 <= f) ->
  0x7fff7f800000 <= lo -> lo <= q - 256 -> q < 2^63 -> (0 < doc < 2^63 /\ doc mod 8 = 0) -> 0 <= i < 2^64 -> 0 <= osp < 2^64 ->
  (forall m', munch (pj_W1 q f) m m' -> wmono bsegs m m' ->
     rw_cells bsegs m' doc [C8 (Z_to_bv 64 TAPE)] /\ bytes_at bsegs m' (shad doc) [z8; z8] /\ client_consts m') ->
  rw_cells bsegs m (q - 256) (pj_locals0 j0 j1 osp j2 j3) ->
  rw_cells bsegs m f [CB 8 h0; CB 8 h1; CB 8 h2] ->
  rw_cells bsegs m (shad f) (pj_shadow0 ls) ->
  mem_inv bsegs m -> stk bsegs m lo (q - 256) -> lo <= q - 272 ->
  0 < TAPE -> TAPE mod 8 = 0 -> TAPE + 8 * i < 2^63 -> doc + 16 < 2^47 -> (doc + 8 <= q - 272 \/ q - 256 <= doc) ->
  evt bsegs (fun ms => exists (m1 : mem) (a4' : word),
      ms = MS (mkR (Z_to_bv 64 DMP_PJ_DISP_A) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256))
                   (Z_to_bv 64 (TAPE + 8 * i)) (Z_to_bv 64 0) (Z_to_bv 64 TAPE) (Z_to_bv 64 (2^60)) a4' a5 a6 a7
                   s2x (Z_to_bv 64 f) (Z_to_bv 64 i) (Z_to_bv 64 doc) s6 (Z_to_bv 64 f) s8 (Z_to_bv 64 SHB) s10x (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
             F (Z_to_bv 64 DMP_PJ_DISP_A) fc None m1 (seg_rom bsegs)
      /\ munch (pj_W1 q f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1 /\ stk bsegs m1 lo (q - 256)
      /\ rw_cells bsegs m1 (q - 256) (pj_locals1 j0 j1 osp j2 f doc i)
      /\ rw_cells bsegs m1 f [C8 (Z_to_bv 64 DMP_MAGIC0); C8 (Z_to_bv 64 DMP_PJ_DESC_A); C8 (Z_to_bv 64 DMP_PJ_A)]
      /\ rw_cells bsegs m1 (shad f) (map C1 pj_sh_pro))
    (MS (mkR (Z_to_bv 64 DMP_PJ_SMRET_A) (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) (Z_to_bv 64 f) a1 a2 a3 a4 a5 a6 a7
             s2x s3x (Z_to_bv 64 i) (Z_to_bv 64 doc) s6 s7x s8 (Z_to_bv 64 SHB) s10x s11 t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_SMRET_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros LS F0 FLO SLO SH0 SEP GLO LSP SPH DR IR OR SHZD FRl FH FS MI ST L16 T0 T8 TI D47 DSEP.
  do 20 (destruct ls as [|? ls]; [discriminate LS|]). destruct ls; [| discriminate LS]. clear LS.
  unfold pj_W1, pj_locals0, pj_locals1, pj_shadow0, pj_sh_pro, DMP_PJ_SMRET_A, DMP_PJ_DISP_A, DMP_MAGIC0, DMP_PJ_DESC_A, DMP_PJ_A, TPV_A, shad, SHB in *.
  cbn [map app repeat] in *.
  pose proof (munch_refl [(q - 256 + 104, q - 256 + 112); (q - 256 + 136, q - 256 + 152); (f, f + 24);
                          (f / 8 + 2147450880, f / 8 + 2147450880 + 20); (q - 272, q - 256)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESP : bv_unsigned (Z_to_bv 64 (q - 256)) = q - 256) by (apply unsigned_lit; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 doc) = doc) by (apply unsigned_lit; lia).

  zstep. zstep. zstep. zstep.
  if_cases K; zify_cond K; [| exfalso; lia].
  pj_run PJ_TREF_A.

  destruct (SHZD _ MU WM) as (DC & DSH & CC).
  eapply evt_cut.
  { eapply (tref_walk doc TAPE i (q - 256) lo); [exact ST| lia| lia| lia| exact CC| lia| exact D47| lia
      | unfold shad, SHB; exact DSH| exact DC| exact T0| exact T8| lia| exact TI| clear - DSEP; lia| eassumption]. }
  cbv beta. intros ms' (m2 & a4' & -> & MU2 & WM2 & MI2 & ST2).
  rewrite (ret_pc_even 716624) by lia.
  apply evt_done. exists m2, a4'. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; intros x Hx; cbn [outside] in *; lia|].
  split; [eapply wmono_trans; [exact WM| exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
  split; [| split]; (eapply rw_cells_transport; [eassumption| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add map]; repeat split; lia]).
Qed.

Lemma pj_tixE : forall (E : aenvA) (sp idx : Z) (ra gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem),
  aenvA_ok E -> AINV_A E m -> client_consts m -> stk bsegs m (ae_lo E) sp -> ae_lo E <= sp - 16 -> sp < 2^63 ->
  0 <= idx -> ae_TAPE E + 8 * idx < 2^63 -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a4' : word),
      ms = MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ae_TAPE E + 8 * idx)) (Z_to_bv 64 0) (Z_to_bv 64 (ae_TAPE E)) (Z_to_bv 64 (2^60)) a4' a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs)
      /\ munch [(sp - 16, sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' (ae_lo E) sp
      /\ AINV_A E m' /\ client_consts m')
    (MS (mkR ra (Z_to_bv 64 sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ae_DOC E)) (Z_to_bv 64 idx) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PJ_TREF_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros OK AI CC ST LO SPH I0 IH MI.
  pose proof OK as OK'. destruct OK' as [_ _ _ _ (T16 & _ & _ & T0 & TL) _ _ _ (D8 & DF & DL & DS & DT) LOW [HL HT]].
  unfold USTACK_TOP, SEGTOP_A in *.
  assert (FS0 : 0 <= fs_size (ae_kD E)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
  pose proof AI as (TB & SB & PB & DC & DSH).
  change [C8 (Z_to_bv 64 (ae_TAPE E)); C8 (Z_to_bv 64 (ae_SBUF E))] with ([C8 (Z_to_bv 64 (ae_TAPE E))] ++ [C8 (Z_to_bv 64 (ae_SBUF E))]) in DC.
  apply rw_cells_app in DC. destruct DC as [DC _].
  eapply evt_cut.
  { eapply (tref_walk (ae_DOC E) (ae_TAPE E) idx sp (ae_lo E)); [exact ST| lia| lia| lia| exact CC| lia| lia| lia
      | unfold shad, SHB in *; exact DSH| exact DC| lia| clear - T16; Z.div_mod_to_equations; lia| lia| exact IH| lia| exact MI]. }
  cbv beta. intros ms' (m' & a4' & -> & MU & WM & MI' & ST').
  apply evt_done. exists m', a4'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact ST'|]. split.
  - assert (PTRB : Prelim.zlength (ae_p1 E) = 0 \/ ae_PTR E + Prelim.zlength (ae_p1 E) <= ae_lo E).
    { destruct OK as [_ _ _ _ _ _ PT _ _ _ _]. destruct (ae_p1 E) as [|c cs] eqn:EP; [left; reflexivity|]. right.
      destruct (PT ltac:(first [discriminate| rewrite EP; discriminate])) as (_ & _ & X & Y). rewrite ?EP in *. lia. }
    pose proof (Atp_defsA.ok_sbuf E OK) as (_ & _ & SN & _ & SL). pose proof (Atp_defsA.ok_tape E OK) as (_ & _ & TN & _ & _).
    apply (AINV_A_agree E m m' AI). intros a Ha. apply MU. unfold ainv_rng, shad, SHB in Ha. cbn [outside]. split; [| exact I].
    clear - Ha PTRB SN SL TN TL DL DT DF DS LOW LO HL HT FS0. Z.div_mod_to_equations. lia.
  - apply (client_consts_munch _ m m' CC MU). intros x Hx. cbn [outside]. split; [lia| exact I].
Qed.

Definition DMP_PJ_X2_A : Z := 0xaf63c.

Lemma pj_walkX1 : forall (f : Z) (ra sp gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 t3 t4 t5 t6 : word)
    (h0 : list byte) (ls : list (list byte)) F fc (m : mem),
  length ls = 32%nat -> 0 < f -> f + 256 < 2^63 -> 0 <= shad f -> shad f + 32 < 2^63 -> (f + 256 <= shad f \/ shad f + 32 <= f) ->
  rw_cells bsegs m f [CB 8 h0] -> rw_cells bsegs m (shad f) (pj_shadow0 ls) -> mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem) (a0' : word),
      ms = MS (mkR ra sp gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
              F (Z_to_bv 64 DMP_PJ_X2_A) fc None m' (seg_rom bsegs)
      /\ munch [(f, f + 8); (shad f, shad f + 32)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m')
    (MS (mkR ra sp gp (Z_to_bv 64 TPV_A) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_EXIT_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros L32 F0 FH SH0 SHH SEP FHD FS MI.
  do 32 (destruct ls as [|? ls]; [discriminate L32|]). destruct ls; [| discriminate L32]. clear L32.
  unfold pj_shadow0, DMP_PJ_EXIT_A, DMP_PJ_X2_A, DMP_MAGIC1, TPV_A, shad, SHB in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(f, f + 8); (f / 8 + 2147450880, f / 8 + 2147450880 + 32)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).
  pj_run 718396.
  apply evt_done. do 2 eexists. split; [cbv delta [mkR]; reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM| eassumption].
Qed.

Lemma pj_walkX2 : forall (q f fl lo : Z) (ra gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 t3 t4 t5 t6 : word)
    (xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 : word) (LC : list cell) F fc (m : mem),
  0 < f -> f + 256 < 2^63 -> 0 < fl -> fl + 1 <= lo ->
  0x6d5000 <= lo -> lo <= q - 256 -> q < 2^63 -> cells_size LC = 152%nat ->
  stk bsegs m lo (q - 256) -> rw_cells bsegs m (q - 256) LC ->
  rw_cells bsegs m (q - 104) (pj_saved xra xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11) ->
  ro_cells bsegs m (f + 248) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m' : mem), ret_st xra (Z_to_bv 64 q) gp (Z_to_bv 64 TPV_A) xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 (Z_to_bv 64 fl) m' ms
      /\ ms_fcsr ms = fc /\ munch [(fl, fl + 1)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo q
      /\ rw_cells bsegs m' fl [C1 (Z_to_bv 8 0)])
    (MS (mkR ra (Z_to_bv 64 (q - 256)) gp (Z_to_bv 64 TPV_A) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 (q - 256)) a0 a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 f) s4 s5 s6 (Z_to_bv 64 f) s8 s9 s10 (Z_to_bv 64 (shad f)) t3 t4 t5 t6)
        F (Z_to_bv 64 DMP_PJ_X2_A) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH FL0 FLLO GLO LSP SPH SZ ST FRl FRs FW FLC MI.
  unfold pj_saved, DMP_PJ_X2_A, TPV_A in *.
  pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (EFL : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply unsigned_lit; lia).
  assert (EQ : bv_unsigned (Z_to_bv 64 q) = q) by (apply unsigned_lit; lia).

  zstep. ls. zstep.

  replace (q - 104) with (q + -104) in FRs by lia.
  zstep. do 13 zstep. zstep.
  replace (q + -104) with (q - 104) in FRs by lia.
  pose proof (stk_release bsegs _ _ _ _ ST FRl ltac:(lia)) as ST1. rewrite SZ in ST1. change (Z.of_nat 152%nat) with 152 in ST1.
  replace (q - 256 + 152) with (q - 104) in ST1 by lia.
  pose proof (stk_release bsegs _ _ _ _ ST1 FRs ltac:(lia)) as ST3. cbn [cells_size csize Nat.add] in ST3.
  replace (q - 104 + Z.of_nat 104) with q in ST3 by lia.
  zstep.
  apply evt_done. eexists. split; [unfold ret_st; do 16 eexists; cbv delta [mkR]; reflexivity|]. split; [reflexivity|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|]. split; [exact ST3| eassumption].
Qed.
