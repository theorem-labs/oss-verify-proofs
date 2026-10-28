(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface D_kit Sj_akit Sj_acps Sj_hkit Sj_rtf Sj_num_iface Sj_num_akit
  Sj_stage2_defs Sj_stage2_main.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section World.
  Variable RT : rt_sig.
  Variable PMc : Model -> Prop.
  Variable E0 : s2env.
  Variable K : config -> Prop.

  Definition WD : Type := (mem * rts RT)%type.
  Definition wm (w : WD) : mem := fst w.
  Definition wS (w : WD) : rts RT := snd w.
  Definition wQ (w : WD) : machine_state -> Prop := aevt RT PMc (snd w) K.
  Notation wE := (Sj_stage2_main.wE E0 WD wm).

  Definition s2_region (x : Z) : Prop :=
    e_spa E0 <= x < bv_unsigned (e_sp E0)
    \/ e_THIS E0 <= x < e_THIS E0 + 96 \/ e_DOC E0 <= x < e_DOC E0 + 24
    \/ e_IDX E0 <= x < e_IDX E0 + 4 * Z.of_nat (length (e_iws E0)) \/ e_BUF E0 <= x < e_BUF E0 + e_len E0 + 64
    \/ e_TAPE E0 <= x < e_TAPE E0 + 8 * e_tcap E0 \/ e_SBUF E0 <= x < e_SBUF E0 + e_scap E0
    \/ e_OC E0 <= x < e_OC E0 + 8192 \/ e_IA E0 <= x < e_IA E0 + 1024 \/ e_FF E0 <= x < e_FF E0 + 8.

  Record numw_facts (w : WD) : Prop := {
    nw_art    : ART RT (snd w) (wm w);
    nw_frames : (length (rt_frames RT (snd w)) + NUMA_FRAMES <= FRAMES_MAX)%nat;
    nw_credit : NUMA_CREDIT <= rt_credit RT (snd w);
    nw_win    : rt_sp0 RT (snd w) - STACK_WIN <= e_lo E0;
    nw_room   : e_lo E0 + NUMA_STACK <= e_spa E0;
    nw_top    : bv_unsigned (e_sp E0) + 16 <= USTACK_TOP;
    nw_tp     : e_tp E0 = Z_to_bv 64 0x6abde8;
    nw_buf    : exists p n, In (p, n) (rt_live RT (snd w)) /\ p mod 8 = 0 /\ p <= e_BUF E0 /\ e_BUF E0 + e_len E0 + 64 <= p + n;
    nw_client : forall x, s2_region x -> aclient (rt_live RT (snd w)) (rt_frames RT (snd w)) (e_spa E0) x;
    nw_fnz    : rt_frames RT (snd w) <> [] }.

  Definition s2_X0 : list (Z * Z) :=
    [(e_THIS E0, e_THIS E0 + 96); (e_TAPE E0, e_TAPE E0 + 8 * e_tcap E0); (e_SBUF E0, e_SBUF E0 + e_scap E0);
     (e_OC E0, e_OC E0 + 8192); (e_IA E0, e_IA E0 + 1024); (e_FF E0, e_FF E0 + 8)].
  Record rootw_facts (w : WD) : Prop := {
    rw_num    : numw_facts w;
    rw_live   : Z.of_nat (length (rt_live RT (snd w))) < LIVE_MAX;
    rw_credit : mcost (e_len E0 + 64) + NUMA_CREDIT <= rt_credit RT (snd w);

    rw_shz    : forall Σ' (m' : mem), ART RT Σ' m' -> (forall e, In e (rt_live RT (snd w)) -> In e (rt_live RT Σ')) ->
                  rt_frames RT Σ' = rt_frames RT (snd w) ->
                  agree_on (fun x => shad (e_DOC E0) <= x < shad (e_DOC E0) + 3) (wm w) m' -> shz_all E0 m';

    rw_docsh  : forall x, shad (e_DOC E0) <= x < shad (e_DOC E0) + 3 ->
                  (forall usp, aclient (rt_live RT (snd w)) (rt_frames RT (snd w)) usp x) /\ x < e_lo E0 /\ outside s2_X0 x }.

  Definition wstep (w w' : WD) : Prop := exists m1,
    munch (s2_W (wE w)) (wm w) m1 /\ wmono bsegs (wm w) m1 /\ ART RT (snd w) m1 /\
    rt_after RT (snd w') (e_spa E0) (e_lo E0) m1 (wm w') /\
    rt_pres_ex (rt_live RT (snd w)) (rt_frames RT (snd w)) (e_spa E0) (e_spa E0 + 304) 8 m1 (wm w') /\
    rt_frames RT (snd w') = rt_frames RT (snd w) /\ rt_live RT (snd w') = rt_live RT (snd w) /\ rt_sp0 RT (snd w') = rt_sp0 RT (snd w) /\
    rt_credit RT (snd w) - NUMA_CREDIT <= rt_credit RT (snd w').

  Definition wroot (w w' : WD) : Prop :=
    ART RT (snd w') (wm w') /\
    rt_pres_fp (rt_live RT (snd w)) (rt_frames RT (snd w)) (bv_unsigned (e_sp E0)) s2_X0 (wm w) (wm w') /\
    rt_frames RT (snd w') = rt_frames RT (snd w) /\ rt_live RT (snd w') = rt_live RT (snd w) /\ rt_sp0 RT (snd w') = rt_sp0 RT (snd w) /\
    rt_credit RT (snd w) - (mcost (e_len E0 + 64) + NUMA_CREDIT) <= rt_credit RT (snd w').

  Section Good.
    Variable good : WD -> Z -> Prop.

    Definition g_shz : Prop := forall w kk, good w kk -> a_shz (wE w).
    Definition g_mono : Prop := forall w kk kk', good w kk -> (kk <= kk') -> good w kk'.
    Definition g_kx : Prop := forall w kk tws sbs, good w kk -> exit_k (s2_ghost (wE w) tws sbs) (wQ w).

    Definition g_num : Prop := forall w kk, good w kk -> 0 <= kk <= e_n E0 -> numw_facts w.
    Definition g_step : Prop := forall w w' kk, good w kk -> 0 <= kk <= e_n E0 -> wstep w w' -> good w' (kk + 1).
    Definition g_rootf : Prop := forall w, good w 0 -> rootw_facts w.
    Definition g_root : Prop := forall w w', good w 0 -> wroot w w' -> good w' 1.

    Definition numa_shape : Prop := forall w s (tws sbs : list Z), good w (k s) -> vexp E0 s -> Z.of_nat (length tws) = W s ->
      (is_numstart (e_tok E0 (k s)) = true -> forall w' v r, good w' (k s + 1) -> num_word v ->
         arrcont_k (s2_ghost (wE w') (tws ++ [v; r]) (sbs ++ [])) (wQ w') (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
      arrnum_k (s2_ghost (wE w) tws sbs) (wQ w) s.
    Definition numo_shape : Prop := forall w s (tws sbs : list Z), good w (k s) -> vexp E0 s -> Z.of_nat (length tws) = W s ->
      (is_numstart (e_tok E0 (k s)) = true -> forall w' v r, good w' (k s + 1) -> num_word v ->
         objcont_k (s2_ghost (wE w') (tws ++ [v; r]) (sbs ++ [])) (wQ w') (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
      objnum_k (s2_ghost (wE w) tws sbs) (wQ w) s.
    Definition rootnum_shape : Prop := forall w (h0 : Z), good w 0 -> is_numstart (e_tok E0 0) = true ->
      (forall w' v r, good w' 1 -> num_word v -> docend_k (s2_ghost (wE w') [h0; v; r] []) (wQ w') (mkst 1 0 3 0 [])) ->
      rootprim_k (s2_ghost (wE w) [h0] []) (wQ w) 0xb757c.
  End Good.
End World.

Definition numa_stmt (RT : rt_sig) : Prop :=
  forall PMc, fdfs_only PMc -> mat_stable PMc -> forall E0, env_ok E0 -> forall K good,
    g_shz RT E0 good -> g_mono RT good -> g_kx RT PMc E0 K good -> g_num RT E0 good -> g_step RT E0 good ->
    numa_shape RT PMc E0 K good.
Definition numo_stmt (RT : rt_sig) : Prop :=
  forall PMc, fdfs_only PMc -> mat_stable PMc -> forall E0, env_ok E0 -> forall K good,
    g_shz RT E0 good -> g_mono RT good -> g_kx RT PMc E0 K good -> g_num RT E0 good -> g_step RT E0 good ->
    numo_shape RT PMc E0 K good.
Definition rootnum_stmt (RT : rt_sig) : Prop :=
  forall PMc, fdfs_only PMc -> mat_stable PMc -> forall E0, env_ok E0 -> forall K good,
    g_shz RT E0 good -> g_mono RT good -> g_kx RT PMc E0 K good -> g_num RT E0 good -> g_step RT E0 good ->
    g_rootf RT E0 good -> g_root RT E0 good ->
    rootnum_shape RT PMc E0 K good.
