(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX StoreFast.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec Require Import Prelim STree Malloc Monad Stdio SjModel Target Prog.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Layout Exit Printf_wfile Sj_iface Sj_kit.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition SJ_OPNEW_NT : Z := 0x7bb14.
Definition SJ_OPNEW_ARR_NT : Z := 0x7bb48.
Definition SJ_OPDEL : Z := 0x7bb7c.
Definition SJ_OPDEL_ARR : Z := 0x7bb84.
Definition SJ_OPNEW_STACK : Z := 32 + RMALLOC_STACK.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition opnew_postZ (ra : word) (q : Z) (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (s : PState) (LB : list block) (n lo B : Z) (m : mem)
    (p : bptr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) A junk,
    ms' = MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo q
    /\ rw_cells usegs m' LX_ERRNO [C4 errv']
    /\ rauxv_ok m' B
    /\ rheap_pres LB q m m'
    /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ rblock_range A n
    /\ RHEAP s' ((p, A, n) :: LB) m'
    /\ rw_cells usegs m' A [CB (Z.to_nat n) junk].

Definition opnew_stmt (entry : Z) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q n lo B : Z) (errv : word),
  RHEAP s LB m ->
  rauxv_ok m B -> q <= B ->
  stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - SJ_OPNEW_STACK ->
  rw_cells usegs m LX_ERRNO [C4 errv] ->
  mem_inv usegs m -> 0 <= q < 2^64 -> 1 <= n < 2^32 ->
  implM usegs (newnt lops n) s
        (opnew_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom usegs)).

Definition opnew_nt_stmt : Prop := opnew_stmt SJ_OPNEW_NT.
Definition opnew_arr_nt_stmt : Prop := opnew_stmt SJ_OPNEW_ARR_NT.

Definition opdel_stmt (entry : Z) : Prop :=
  forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (p : bptr) (q A n lo B : Z) (errv : word),
  RHEAP s LB m -> In (p, A, n) LB ->
  rauxv_ok m B -> q <= B ->
  stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - RFREE_STACK ->
  rw_cells usegs m LX_ERRNO [C4 errv] ->
  mem_inv usegs m -> 0 <= q < 2^64 ->
  implM usegs (del lops p) s
        (free_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB p lo B errv m)
        (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 entry) fc None m (seg_rom usegs)).

Definition opdel_nt_stmt : Prop := opdel_stmt SJ_OPDEL.
Definition opdel_arr_stmt : Prop := opdel_stmt SJ_OPDEL_ARR.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Lemma opdel_proof : opdel_nt_stmt.
  Proof.
    unfold opdel_nt_stmt, opdel_stmt, SJ_OPDEL. intros until errv. intros HEAP IN AUX QB ST CEIL LO ERR MI Hq.
    unfold del. cbn [lib_free lops Target.ops lib_free_opt].
    unfold implM. iprefix. step. ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (free_callZ HF) with (B := B) (lo := lo) (A := A) (n := n); eassumption.
  Qed.

  Lemma opdel_arr_proof : opdel_arr_stmt.
  Proof.
    unfold opdel_arr_stmt, opdel_stmt, SJ_OPDEL_ARR. intros until errv. intros HEAP IN AUX QB ST CEIL LO ERR MI Hq.
    unfold del. cbn [lib_free lops Target.ops lib_free_opt].
    unfold implM. iprefix. step. step. ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply (free_callZ HF) with (B := B) (lo := lo) (A := A) (n := n); eassumption.
  Qed.

  Lemma opnew_body : forall (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (q n lo B : Z) (errv : word),
    RHEAP s LB m ->
    rauxv_ok m B -> q <= B ->
    stk usegs m lo q -> alloc_ceiling <= lo -> lo <= q - (16 + RMALLOC_STACK) ->
    rw_cells usegs m LX_ERRNO [C4 errv] ->
    mem_inv usegs m -> 0 <= q < 2^64 -> 1 <= n < 2^32 ->
    implM usegs (newnt lops n) s
          (opnew_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m)
          (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xd4db0) fc None m (seg_rom usegs)).
  Proof.
    intros until errv. intros HEAP AUX QB ST CEIL LO ERR MI Hq Hn.
    unfold RMALLOC_STACK in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr LB q a -> outside [(q - 16, q)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in B3'. lia. }
    unfold newnt. cbn [bind ret unreachable lib_malloc lops Target.ops].
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    unfold implM. iprefix.
    step. carve_frame 16%nat ST.
    apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    step. step. zstep. zstep. step. step.
    replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HEAP1 : RHEAP s LB m1).
    { eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor]. }
    assert (AUX1 : rauxv_ok m1 B).
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia. }
    assert (ERR1 : rw_cells usegs m1 LX_ERRNO [C4 errv]) by (rewrite ELX; assumption).
    ihere.
    lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
      lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
    eapply implM_bind.
    { eapply (malloc_callZ HM) with (B := B) (lo := lo);
        [exact HEAP1| exact AUX1| lia| exact ST| exact CEIL'| unfold RMALLOC_STACK; lia| exact ERR1| exact MI| lia| lia]. }
    cbv beta. intros r s1' ms1 PO. unfold malloc_postZ in PO.
    destruct PO as (r5 & r6 & r7 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv2
                    & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & RES).
    destruct r as [p|]; [| apply implM_unr].
    destruct RES as (A & junkA & -> & BR & HEAP3 & BLK).
    pose proof BR as (BA0 & BA16 & _ & BAC & BAI). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BAC.
    replace (ret_pc (Z_to_bv 64 871884)) with (Z_to_bv 64 871884) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
    rename MU into MU0. rename WM into WM0.
    pose proof (munch_refl [(q - 16, q)]%Z m3) as MU. pose proof (wmono_refl usegs m3) as WM.
    apply implM_ret.
    step. if_cases KA; zify_cond KA; [| exfalso; rewrite ?unsigned_lit in KA by lia; lia]. clear KA.
    step. step. step. release_frame FR ST3 q. step.
    apply evt_done. unfold opnew_postZ.
    do 14 eexists. exists m3, errv2, A, junkA.
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
    split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU0| exact WM0| apply CLI]|].
             eapply rheap_pres_weaken; [exact HP| lia| auto]. }
    split; [exact FA|]. split; [exact SO|]. split; [exact BR|]. split; [exact HEAP3| exact BLK].
  Qed.

  Lemma opnew_wrap : forall entry, (entry = SJ_OPNEW_NT \/ entry = SJ_OPNEW_ARR_NT) -> opnew_stmt entry.
  Proof.
    intros entry HE. unfold opnew_stmt. intros until errv. intros HEAP AUX QB ST CEIL LO ERR MI Hq Hn.
    unfold SJ_OPNEW_STACK, RMALLOC_STACK in *.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof CEIL as CEIL'. unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in CEIL; try (pose proof alloc_ceiling_range as CEIL_RANGE__).
    pose proof (munch_refl [(q - 16, q)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
    assert (CLI : forall a, 0 <= a < 2^64 -> rclient_addr LB q a -> outside [(q - 16, q)] a).
    { intros a Ha Hc. cbn. split; [|exact I]. apply rclient_addr_cases in Hc. destruct Hc as [Hc|[Hc|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ _ HEAP Hb') as (_ & _ & _ & B3' & _).
      unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in B3'. lia. }
    assert (ELX : LX_ERRNO = 977220) by reflexivity. rewrite ELX in ERR.
    unfold implM. iprefix.
    assert (GO : forall ra1 (junk8 : list byte) m1 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6,
               (ra1 = Z_to_bv 64 0x7bb20 \/ ra1 = Z_to_bv 64 0x7bb54) ->
               rw_cells usegs m1 (q + -16) [CB 8 junk8; C8 ra] -> stk usegs m1 lo (q + -16) ->
               RHEAP s LB m1 -> rauxv_ok m1 B -> rw_cells usegs m1 977220 [C4 errv] -> mem_inv usegs m1 ->
               munch [(q - 16, q)]%Z m m1 -> wmono usegs m m1 ->
               impl usegs (at_node usegs) ((r <- raw_malloc n;; match r with Some p => mret p | None => munr end) s)
                 (epost (fun p : bptr * PState => opnew_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m p.1 p.2))
                 (MS (mkR ra1 (Z_to_bv 64 (q + -16)) gp (Z_to_bv 64 RATP) xt0 xt1 xt2 s0 s1 (Z_to_bv 64 n) xa1 xa2 xa3 xa4 xa5 xa6 xa7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0xd4db0) fc None m1 (seg_rom usegs))).
    { intros ra1 junk8 m1 xt0 xt1 xt2 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 HRA FR ST1 HEAP1 AUX1 ERR1 MI1 MU1 WM1.
      lazymatch goal with |- impl ?segs _ (?c ?st) (epost ?E) ?ms =>
        lazymatch E with (fun p => ?Q (fst p) (snd p)) => change (implM segs c st Q ms) end end.
      eapply implM_post_evt.
      { eapply (opnew_body ra1 gp xt0 xt1 xt2 s0 s1 xa1 xa2 xa3 xa4 xa5 xa6 xa7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6 F fc m1 s LB (q + -16) n lo B errv);
          [exact HEAP1| exact AUX1| lia| exact ST1| exact CEIL'| unfold RMALLOC_STACK; lia| rewrite ELX; exact ERR1| exact MI1| lia| lia]. }
      cbv beta. intros p s' ms' PO. unfold opnew_postZ in PO.
      destruct PO as (r5 & r6 & r7 & r11 & r12 & r13 & r14 & r15 & r16 & r17 & r28 & r29 & r30 & r31 & m3 & errv2 & A & junkA
                      & -> & MI3 & ST3 & ERR3 & AUX3 & HP & FA & SO & BR & HEAP3 & BLK).
      apply (rw_cells_agree _ _ _ _ _ (agree_of_heap_pres _ _ _ _ HP)) in FR; [| intros a Ha; left; cbn in Ha; lia].
      pose proof BR as (BA0 & BA16 & _ & BAC & BAI). unfold OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Spec.Malloc.MCEIL in BAC.
      pose proof (munch_refl [(q - 16, q)]%Z m3) as MU3. pose proof (wmono_refl usegs m3) as WM3.
      assert (EP : ret_pc ra1 = ra1).
      { destruct HRA as [-> | ->]; apply ret_pc_even; [lia| reflexivity| lia| reflexivity]. }
      rewrite EP.
      assert (FIN : forall pc, (pc = 0x7bb20 \/ pc = 0x7bb54) ->
                evt usegs (opnew_postZ ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB n lo B m p s')
                  (MS (mkR ra1 (Z_to_bv 64 (q + -16)) gp (Z_to_bv 64 RATP) r5 r6 r7 s0 s1 (Z_to_bv 64 A) r11 r12 r13 r14 r15 r16 r17
                           s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 r28 r29 r30 r31) F (Z_to_bv 64 pc) fc None m3 (seg_rom usegs))).
      { intros pc [-> | ->].
        - step. release_frame FR ST3 q. step. step.
          apply evt_done. unfold opnew_postZ. do 14 eexists. exists m3, errv2, A, junkA.
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
          split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU1| exact WM1| apply CLI]|].
                   eapply rheap_pres_weaken; [exact HP| lia| auto]. }
          split; [exact FA|]. split; [exact SO|]. split; [exact BR|]. split; [exact HEAP3| exact BLK].
        - step. release_frame FR ST3 q. step. step.
          apply evt_done. unfold opnew_postZ. do 14 eexists. exists m3, errv2, A, junkA.
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MI3|]. split; [exact ST3|]. split; [exact ERR3|]. split; [exact AUX3|].
          split. { eapply rheap_pres_trans; [eapply heap_pres_of_munch; [exact MU1| exact WM1| apply CLI]|].
                   eapply rheap_pres_weaken; [exact HP| lia| auto]. }
          split; [exact FA|]. split; [exact SO|]. split; [exact BR|]. split; [exact HEAP3| exact BLK]. }
      destruct HRA as [-> | ->]; apply FIN; auto. }
    destruct HE as [-> | ->]; unfold SJ_OPNEW_NT, SJ_OPNEW_ARR_NT.
    - step. carve_frame 16%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. eapply GO; try eassumption; [left; reflexivity| |].
      + eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia.
    - step. carve_frame 16%nat ST.
      apply (rw_cells_split_CB usegs _ _ [] 16 junk [] [8;8]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      step. step. step.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
      ihere. eapply GO; try eassumption; [right; reflexivity| |].
      + eapply LH_frame; [exact HEAP| exact MU| exact WM|]. constructor; [apply W_ok_stack; cbn; lia| constructor].
      + eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. constructor; [| constructor]. cbn. unfold RAUXV_CELL. lia.
  Qed.

  Theorem opnew_nt_proof : opnew_nt_stmt.
  Proof. apply opnew_wrap. left. reflexivity. Qed.
  Theorem opnew_arr_nt_proof : opnew_arr_nt_stmt.
  Proof. apply opnew_wrap. right. reflexivity. Qed.
End Proofs.
End WithCeiling0.
