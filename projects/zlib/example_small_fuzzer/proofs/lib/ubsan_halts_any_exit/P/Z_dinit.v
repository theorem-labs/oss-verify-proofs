(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Exit Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit Printf_pieces Z_zrd Z_trees_iface.

Module Z_dend.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Exit Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit Printf_pieces Z_zrd.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_zrd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Deflate HarnessSmall ZApiInst DeflateTaintRel ZTaint.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.

Lemma agree_on_hpres : forall LB SP m m' lo hi, rheap_pres LB SP m m' -> 0 <= lo -> hi <= 2^64 ->
  (forall a, lo <= a < hi -> rclient_addr LB SP a) -> agree_on lo hi m m'.
Proof. intros LB SP m m' lo hi H H0 H1 HC a Ha. apply H; [lia| apply HC; exact Ha]. Qed.

Lemma state_check_cases : forall d, deflateStateCheck d = false ->
  let st := ds_status d in st = 42 \/ st = 57 \/ st = 69 \/ st = 73 \/ st = 91 \/ st = 103 \/ st = 113 \/ st = 666.
Proof.
  intros d H. unfold deflateStateCheck in H. apply negb_false_iff in H. cbv zeta.
  unfold INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, BUSY_STATE, FINISH_STATE in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]); apply Z.eqb_eq in H; lia.
Qed.

Section DEND.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.

  Definition Z_DEFLATEEND_A : Z := 0x164c8.

  Lemma dend_zfree : forall {A : Type} (K : unit -> M PState A) (POST : A -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LBc : list block) (p : bptr) (Ab n lo B : Z) (errv : word),
    RHEAP s LBc m -> In (p, Ab, n) LBc ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m -> tp = Z_to_bv 64 RATP ->
    a1 = wz Ab ->
    (forall (s' : PState) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' (errno_addr tp) [C4 errv] -> rauxv_ok m' B ->
       rheap_pres (lb_remove p LBc) (bv_unsigned sp) m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
       RHEAP s' (lb_remove p LBc) m' ->
       implM psegs (K tt) s' POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    implM psegs (bind lops (lib_free lops (Some p)) K) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros HP HIN AUX SPB STK CEIL LOSP ERRC MI TP -> KONT.
    cbn [bind lops Target.ops lib_free].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold Z_ZCFREE. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
    eapply implM_bind.
    { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LBc p Ab n lo B errv);
        [ exact HP | exact HIN | exact AUX | exact SPB | exact STK | exact CEIL | exact LOSP | exact ERRC | exact MI | exact TP | reflexivity ]. }
    cbv beta. intros [] s' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR' & EFA' & ESO' & HP').
    exact (KONT s' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' MI' ST' ERR' AUX' HPR' EFA' ESO' HP').
  Qed.

  Lemma dend_zfree_last : forall (POST : unit -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LBc : list block) (p : bptr) (Ab n lo B : Z) (errv : word),
    RHEAP s LBc m -> In (p, Ab, n) LBc ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RFREE_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m -> tp = Z_to_bv 64 RATP ->
    a1 = wz Ab ->
    (forall (s' : PState) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' (errno_addr tp) [C4 errv] -> rauxv_ok m' B ->
       rheap_pres (lb_remove p LBc) (bv_unsigned sp) m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
       RHEAP s' (lb_remove p LBc) m' ->
       evt psegs (POST tt s')
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    implM psegs (lib_free lops (Some p)) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCFREE) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros HP HIN AUX SPB STK CEIL LOSP ERRC MI TP -> KONT.
    cbn [lops Target.ops lib_free].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold Z_ZCFREE. zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
    eapply implM_post_evt.
    { eapply (FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LBc p Ab n lo B errv);
        [ exact HP | exact HIN | exact AUX | exact SPB | exact STK | exact CEIL | exact LOSP | exact ERRC | exact MI | exact TP | reflexivity ]. }
    intros [] s' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & -> & MI' & ST' & ERR' & AUX' & HPR' & EFA' & ESO' & HP').
    exact (KONT s' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' MI' ST' ERR' AUX' HPR' EFA' ESO' HP').
  Qed.

  Ltac tr_up HPR H Hn :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia| intros ?a ?Ha; cbn in Ha; left; lia])) as Hn.
  Ltac tr_st HPR H Hn blk :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia
      | intros ?a ?Ha; cbn in Ha; right; right; exists blk; split; [cbn; tauto| cbn; lia]])) as Hn.

  Theorem deflateEnd_drep : forall (L : dlay) (d : deflate_state) (z : zstrm)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (b : bptr * bptr * bptr * bptr * bptr)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
    lx_env m s (zd_blocks b L) LB sp tp B lo errv canary ->
    rw_cells psegs m (dl_S L) (zs_pub ni ai ti no ao to p1 p2) ->
    DREPq m L d z ->
    deflateStateCheck d = false -> ds_status d <> BUSY_STATE ->
    strm_in_frame sp (dl_S L) B ->
    lo <= bv_unsigned sp - Z_DEFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
    frm0 fc ->
    a0 = wz (dl_S L) ->
    implM psegs (deflate_end lops b) s
          (deflateEnd_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz Z_DEFLATEEND_A) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. intros ENV PUB (ZQ & ST) CHK NBUSY SIF LOSP SP16 FRM ->.
    destruct b as [[[[bs bw] bpv] bh] bb]. unfold zd_blocks in ENV. cbn [deflate_end].
    pose proof (st_lay _ _ _ _ ST) as LAY.
    pose proof ENV as (HP & _ & _ & _ & _ & AUX & SPB & B63 & STK & CEIL & GLO & ERRC & TP & MI).
    destruct ZQ as (p3 & resv & ZQ). unfold zs_priv_cells in ZQ.
    destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. destruct GA as (h1 & h2 & h3 & h4 & h5 & GA). unfold dsA_cells in GA.
    lay_open LAY.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (BEL : dl_As L + 5968 <= lo /\ dl_Aw L + 65536 <= lo /\ dl_Ap L + 65536 <= lo /\ dl_Ah L + 65536 <= lo /\ dl_Ab L + 65536 <= lo).
    { pose proof (fun b Hb => HBR _ _ _ b HP (in_or_app _ _ b (or_introl Hb))) as BR.
      pose proof (BR (bs, dl_As L, 5968) ltac:(cbn; tauto)) as (_ & _ & _ & X1 & _).
      pose proof (BR (bw, dl_Aw L, 65536) ltac:(cbn; tauto)) as (_ & _ & _ & X2 & _).
      pose proof (BR (bpv, dl_Ap L, 65536) ltac:(cbn; tauto)) as (_ & _ & _ & X3 & _).
      pose proof (BR (bh, dl_Ah L, 65536) ltac:(cbn; tauto)) as (_ & _ & _ & X4 & _).
      pose proof (BR (bb, dl_Ab L, 65536) ltac:(cbn; tauto)) as (_ & _ & _ & X5 & _).
      cbn [blk_addr blk_size fst snd] in *. lia. }
    destruct BEL as (Bs & Bw & Bp & Bh & Bb).
    subst tp. unfold errno_addr in ERRC.
    unfold Z_DEFLATEEND_STACK, RFREE_STACK in LOSP. unfold strm_in_frame, ZS_SIZEOF in SIF.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    assert (EUS : bv_unsigned (wz (dl_S L)) = dl_S L) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz (dl_As L)) = dl_As L) by (apply unsigned_lit; lia).
    assert (EUb : bv_unsigned (wz (dl_Ab L)) = dl_Ab L) by (apply unsigned_lit; lia).
    assert (EUh : bv_unsigned (wz (dl_Ah L)) = dl_Ah L) by (apply unsigned_lit; lia).
    assert (EUp : bv_unsigned (wz (dl_Ap L)) = dl_Ap L) by (apply unsigned_lit; lia).
    assert (EUw : bv_unsigned (wz (dl_Aw L)) = dl_Aw L) by (apply unsigned_lit; lia).
    unfold implM. iprefix. unfold Z_DEFLATEEND_A.
    zstep. zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_false.
    carve_frame 32%nat STK.
    zstep. zstep. zstep. zstep. zstep. zstep. if_false.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (evt_cut psegs (fun ms' => exists a4' a5' : word,
        ms' = MS (mkR ra (wz (bv_unsigned sp + -32)) gp (MallocRep.wz RATP) t0 t1 t2 (sx32 (wz (ds_status d))) s1 (wz (dl_S L)) (wz (dl_As L))
                      (wz (-2)) (wz Z_ZCFREE) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x16524) fc None mm (seg_rom psegs))) end.
    { pose proof (state_check_cases d CHK) as CS. cbv zeta in CS.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let bs := eval vm_compute in (option.default [] (image_bytes psegs 0x106a0 8)) in
        assert (MASK : ro_cells psegs mm 0x106a0 [CB (length bs) bs])
          by (apply ro_cells_image; [assumption| vm_compute; reflexivity| lia| cbn; lia]) end.
      cbn [length] in MASK.
      destruct CS as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E.
      - zstep. zstep. if_true. zstep. zstep. if_false. zstep. zstep. if_true. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_false. do 4 zstep. zstep. if_false. apply evt_done. do 2 eexists. reflexivity.
      - zstep. zstep. if_true. zstep. zstep. if_true. apply evt_done. do 2 eexists. reflexivity. }
    intros ms' (a4' & a5' & ->).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    unfold Z_ZCALLOC, Z_ZCFREE in ZQ.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ENV1 : lx_env mm s [(bb, dl_Ab L, 65536); (bh, dl_Ah L, 65536); (bpv, dl_Ap L, 65536); (bw, dl_Aw L, 65536); (bs, dl_As L, 5968)] LB
                       (wz (bv_unsigned sp + -32)) (MallocRep.wz RATP) B lo errv canary) end.
    { eapply (lx_env_munch [(lo, bv_unsigned sp)] m _); [exact HFRAME| exact ENV| exact MU| exact WM| assumption| rewrite E32; exact STK| rewrite E32; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. unfold GLOBALS_TOP in GLO. split; [lia| exact I]. }
    assert (LBR : forall bx, In bx LB -> blk_addr bx + blk_size bx <= lo).
    { intros bx Hb. pose proof (HBR _ _ _ bx HP (in_or_app _ _ bx (or_intror Hb))) as (_ & _ & _ & X1 & _). lia. }
    assert (PR0 : lx_pres LB (bv_unsigned sp) [(dl_S L, dl_S L + 112)] m m0).
    { eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [outside fst snd]; (split; [|exact I]).
      - lia.
      - specialize (LBR bx Hb). lia.
      - unfold GLOBALS_TOP in GLO. lia. }
    zstep. zstep. zstep. if_false. zstep. zstep. zstep.
    apply evt_done.
    replace (ret_pc (wz Z_ZCFREE)) with (wz Z_ZCFREE) by (symmetry; unfold Z_ZCFREE; rpc).
    pose proof ENV1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & STK1 & _ & _ & ERR1 & _ & MI1). rewrite E32 in STK1.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s (deflateEnd_post ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
    eapply (dend_zfree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s _ bb (dl_Ab L) 65536 lo B errv);
      [ exact HP1 | left; reflexivity | exact AUX1 | rewrite E32; lia | rewrite E32; exact STK1 | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERR1 | exact MI1
      | reflexivity | reflexivity | ].
    intros s1' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 MIa STa ERRa AUXa HPRa EFAa ESOa HPa.
    rewrite (lb_remove_head bb _ _ _ (HND _ _ _ HP1)) in HPRa, HPa. rewrite E32 in HPRa, STa.
    assert (ENVa : lx_env m1 s1' [(bh, dl_Ah L, 65536); (bpv, dl_Ap L, 65536); (bw, dl_Aw L, 65536); (bs, dl_As L, 5968)] LB (wz (bv_unsigned sp + -32)) (MallocRep.wz RATP) B lo errv canary).
    { eapply (lx_env_heap m0 m1 s s1'); [exact ENV1| rewrite E32; eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; do 4 right; exact Hb]| exact HPa| exact MIa
        | rewrite E32; exact STa| exact ERRa| exact AUXa]. }
    assert (PRa : lx_pres LB (bv_unsigned sp) [(dl_S L, dl_S L + 112)] m m1).
    { eapply lx_pres_trans; [exact PR0|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; do 4 right; exact Hb]. }
    tr_st HPRa GA GAa (bs, dl_As L, 5968). tr_up HPRa ZQ ZQa. tr_up HPRa PUB PUBa. tr_up HPRa FR FRa.
    clear GA ZQ PUB FR.
    replace (ret_pc (wz 91452)) with (wz 91452) by (symmetry; rpc).
    pose proof (munch_refl [] m1) as MUa. pose proof (wmono_refl psegs m1) as WMa.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    zstep. zstep. if_false. zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s1' (deflateEnd_post ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
    eapply (dend_zfree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s1' _ bh (dl_Ah L) 65536 lo B errv);
      [ exact HPa | left; reflexivity | exact AUXa | rewrite E32; lia | rewrite E32; exact STa | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERRa | exact MIa
      | reflexivity | reflexivity | ].
    intros s2' v0 v1 v2 c0 c1 c2 c3 c4 c5 c6 c7 v3 v4 v5 v6 m2 MIb STb ERRb AUXb HPRb EFAb ESOb HPb.
    rewrite (lb_remove_head bh _ _ _ (HND _ _ _ HPa)) in HPRb, HPb. rewrite E32 in HPRb, STb.
    assert (ENVb : lx_env m2 s2' [(bpv, dl_Ap L, 65536); (bw, dl_Aw L, 65536); (bs, dl_As L, 5968)] LB (wz (bv_unsigned sp + -32)) (MallocRep.wz RATP) B lo errv canary).
    { eapply (lx_env_heap m1 m2 s1' s2'); [exact ENVa| rewrite E32; eapply rheap_pres_weaken; [exact HPRb| lia| intros bx Hb; do 3 right; exact Hb]| exact HPb| exact MIb
        | rewrite E32; exact STb| exact ERRb| exact AUXb]. }
    assert (PRb : lx_pres LB (bv_unsigned sp) [(dl_S L, dl_S L + 112)] m m2).
    { eapply lx_pres_trans; [exact PRa|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRb| lia| intros bx Hb; do 3 right; exact Hb]. }
    tr_st HPRb GAa GAb (bs, dl_As L, 5968). tr_up HPRb ZQa ZQb. tr_up HPRb PUBa PUBb. tr_up HPRb FRa FRb.
    clear GAa ZQa PUBa FRa.
    replace (ret_pc (wz 91484)) with (wz 91484) by (symmetry; rpc).
    pose proof (munch_refl [] m2) as MUb. pose proof (wmono_refl psegs m2) as WMb.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    zstep. zstep. if_false. zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s2' (deflateEnd_post ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
    eapply (dend_zfree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s2' _ bpv (dl_Ap L) 65536 lo B errv);
      [ exact HPb | left; reflexivity | exact AUXb | rewrite E32; lia | rewrite E32; exact STb | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERRb | exact MIb
      | reflexivity | reflexivity | ].
    intros s3' w0 w1 w2 d0 d1 d2 d3 d4 d5 d6 d7 w3 w4 w5 w6 m3 MIc STc ERRc AUXc HPRc EFAc ESOc HPc.
    rewrite (lb_remove_head bpv _ _ _ (HND _ _ _ HPb)) in HPRc, HPc. rewrite E32 in HPRc, STc.
    assert (ENVc : lx_env m3 s3' [(bw, dl_Aw L, 65536); (bs, dl_As L, 5968)] LB (wz (bv_unsigned sp + -32)) (MallocRep.wz RATP) B lo errv canary).
    { eapply (lx_env_heap m2 m3 s2' s3'); [exact ENVb| rewrite E32; eapply rheap_pres_weaken; [exact HPRc| lia| intros bx Hb; do 2 right; exact Hb]| exact HPc| exact MIc
        | rewrite E32; exact STc| exact ERRc| exact AUXc]. }
    assert (PRc : lx_pres LB (bv_unsigned sp) [(dl_S L, dl_S L + 112)] m m3).
    { eapply lx_pres_trans; [exact PRb|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRc| lia| intros bx Hb; do 2 right; exact Hb]. }
    tr_st HPRc GAb GAc (bs, dl_As L, 5968). tr_up HPRc ZQb ZQc. tr_up HPRc PUBb PUBc. tr_up HPRc FRb FRc.
    clear GAb ZQb PUBb FRb.
    replace (ret_pc (wz 91516)) with (wz 91516) by (symmetry; rpc).
    pose proof (munch_refl [] m3) as MUc. pose proof (wmono_refl psegs m3) as WMc.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    zstep. zstep. if_false. zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s3' (deflateEnd_post ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
    eapply (dend_zfree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s3' _ bw (dl_Aw L) 65536 lo B errv);
      [ exact HPc | left; reflexivity | exact AUXc | rewrite E32; lia | rewrite E32; exact STc | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERRc | exact MIc
      | reflexivity | reflexivity | ].
    intros s4' x0 x1 x2 e0 e1 e2 e3 e4 e5 e6 e7 x3 x4 x5 x6 m4 MId STd ERRd AUXd HPRd EFAd ESOd HPd.
    rewrite (lb_remove_head bw _ _ _ (HND _ _ _ HPc)) in HPRd, HPd. rewrite E32 in HPRd, STd.
    assert (ENVd : lx_env m4 s4' [(bs, dl_As L, 5968)] LB (wz (bv_unsigned sp + -32)) (MallocRep.wz RATP) B lo errv canary).
    { eapply (lx_env_heap m3 m4 s3' s4'); [exact ENVc| rewrite E32; eapply rheap_pres_weaken; [exact HPRd| lia| intros bx Hb; do 1 right; exact Hb]| exact HPd| exact MId
        | rewrite E32; exact STd| exact ERRd| exact AUXd]. }
    assert (PRd : lx_pres LB (bv_unsigned sp) [(dl_S L, dl_S L + 112)] m m4).
    { eapply lx_pres_trans; [exact PRc|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRd| lia| intros bx Hb; do 1 right; exact Hb]. }
    tr_st HPRd GAc GAd (bs, dl_As L, 5968). tr_up HPRd ZQc ZQd. tr_up HPRd PUBc PUBd. tr_up HPRd FRc FRd.
    clear GAc ZQc PUBc FRc.
    replace (ret_pc (wz 91548)) with (wz 91548) by (symmetry; rpc).
    pose proof (munch_refl [] m4) as MUd. pose proof (wmono_refl psegs m4) as WMd.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    zstep. zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s4' (deflateEnd_post ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
    eapply (dend_zfree_last _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s4' _ bs (dl_As L) 5968 lo B errv);
      [ exact HPd | left; reflexivity | exact AUXd | rewrite E32; lia | rewrite E32; exact STd | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERRd | exact MId
      | reflexivity | reflexivity | ].
    intros s5' y0 y1 y2 f0 f1 f2 f3 f4 f5 f6 f7 y3 y4 y5 y6 m5 MIe STe ERRe AUXe HPRe EFAe ESOe HPe.
    rewrite (lb_remove_head bs _ _ _ (HND _ _ _ HPd)) in HPRe, HPe. rewrite E32 in HPRe, STe.
    assert (ENVe : lx_env m5 s5' [] LB (wz (bv_unsigned sp + -32)) (MallocRep.wz RATP) B lo errv canary).
    { eapply (lx_env_heap m4 m5 s4' s5'); [exact ENVd| rewrite E32; eapply rheap_pres_weaken; [exact HPRe| lia| intros bx Hb; exact Hb]| exact HPe| exact MIe
        | rewrite E32; exact STe| exact ERRe| exact AUXe]. }
    assert (PRe : lx_pres LB (bv_unsigned sp) [(dl_S L, dl_S L + 112)] m m5).
    { eapply lx_pres_trans; [exact PRd|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRe| lia| intros bx Hb; exact Hb]. }
    tr_up HPRe ZQd ZQe. tr_up HPRe PUBd PUBe. tr_up HPRe FRd FRe.
    clear GAd ZQd PUBd FRd.
    replace (ret_pc (wz 91576)) with (wz 91576) by (symmetry; rpc).
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112)] m5) as MUe. pose proof (wmono_refl psegs m5) as WMe.
    unfold zs_pub in PUBe.
    zstep. change (Z_to_le_bytes 8 0) with (le8 (wz 0)); mem_after_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (evt_cut psegs (fun ms' => exists a0' : word,
        ms' = MS (mkR (wz 91576) (wz (bv_unsigned sp + -32)) gp (MallocRep.wz RATP) y0 y1 y2 (sx32 (wz (ds_status d))) (wz (dl_S L)) a0' f1
                      (wz 0) f3 f4 f5 f6 f7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6) F (wz 0x165cc) fc None mm (seg_rom psegs))) end.
    { pose proof (state_check_cases d CHK) as CS. cbv zeta in CS. unfold BUSY_STATE in NBUSY.
      destruct CS as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; try (exfalso; apply NBUSY; exact E); rewrite E;
        zstep; zstep; zstep; zstep; apply evt_done; eexists; reflexivity. }
    intros ms' (a0' & ->).
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FRe STe (bv_unsigned sp).
    assert (ENVf : lx_env m6 s5' [] LB sp (MallocRep.wz RATP) B lo errv canary).
    { eapply (lx_env_munch [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112)] m5 m6); [exact HFRAME| exact ENVe| exact MUe| exact WMe| exact MIe| exact STe| exact SPB| |].
      - constructor; [left; cbn [fst]; lia| constructor; [left; cbn [fst]; lia| constructor]].
      - intros a Ha. cbn [outside fst snd]. unfold GLOBALS_TOP in GLO. split; [lia| split; [lia| exact I]]. }
    assert (PRf : lx_pres LB (bv_unsigned sp) [(dl_S L, dl_S L + 112)] m m6).
    { eapply lx_pres_trans; [exact PRe|]. eapply lx_pres_of_munch; [exact MUe| exact WMe|].
      intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; cbn [outside fst snd]; (split; [|split; [|exact I]]); try lia.
      all: try (specialize (LBR bx Hb); lia).
      all: unfold GLOBALS_TOP in GLO; lia. }
    apply evt_done. unfold deflateEnd_post.
    do 15 eexists. exists F, fc, m6.
    split; [reflexivity|].
    split; [|split; [reflexivity|]].
    - unfold lx_post_env. split; [exists errv; exact ENVf|]. split; [exact FRM|]. split; [exact PRf|].
      split; [rewrite ESOe, ESOd, ESOc, ESOb, ESOa; reflexivity| rewrite EFAe, EFAd, EFAc, EFAb, EFAa; reflexivity].
    - assert (ALL : rw_cells psegs m6 (dl_S L) (zs_pub ni ai ti no ao to p1 p2 ++
                      [C8 (wz (msg_ptr (zs_msg z))); C8 (wz 0); C8 (wz 106364); C8 (wz 106380); C8 (wz 0); C4 (wz (zs_data_type z)); CB 4 p3; C8 (wz (zs_adler z)); C8 resv])).
      { apply rw_cells_app. split; [exact PUBe| exact ZQe]. }
      destruct (rw_cells_forget psegs m6 _ _ ALL) as (j & Hj). exists j. exact Hj.
  Qed.

  Lemma dend_rc_ok : forall sa x, DREL sa x -> dend_rc (dz_s x) = ZIface.Z_OK ->
    deflateStateCheck sa = false /\ ds_status sa <> BUSY_STATE.
  Proof.
    intros sa x DR RC. destruct (DREL_facts _ _ DR) as (_ & _ & _ & CL).
    assert (E : ds_status sa = ds_status (dz_s x)) by (change (ds_status (clean sa) = ds_status (clean (dz_s x))); rewrite CL; reflexivity).
    unfold dend_rc in RC.
    destruct (deflateStateCheck (dz_s x)) eqn:C; [unfold Z_STREAM_ERROR, ZIface.Z_OK in RC; lia|].
    destruct (ds_status (dz_s x) =? BUSY_STATE) eqn:BS; [unfold Z_DATA_ERROR, ZIface.Z_OK in RC; lia|].
    split; [unfold deflateStateCheck in *; rewrite E; exact C| rewrite E; apply Z.eqb_neq; exact BS].
  Qed.

  Local Transparent the_zapi.
  Theorem deflateEnd_proof : forall R : zreps, Zlib_iface.zr_d R = Z_zrd.zr_d -> deflateEnd_stmt R.
  Proof.
    intros R RD. unfold deflateEnd_stmt. intros until canary. intros ENV PUB ZR DE SIF LOSP SP16 FRM EA0.
    rewrite RD in ZR. destruct ZR as (L & sa & b' & EQ & ES & DQ & DR & PT).
    destruct b as [[[[bs bw] bpv] bh] bb]. destruct b' as [[[[bs' bw'] bpv'] bh'] bb'].
    cbv [blk5_blocks zd_blocks z_dpend z_dhead z_dprev z_dwin z_dstate the_zapi zinst] in EQ, ENV.
    injection EQ as -> -> -> -> -> -> -> -> -> ->. subst S.
    destruct (dend_rc_ok sa ds DR DE) as (CHK & NB).
    eapply (deflateEnd_drep L sa (dz_z ds)) with (b := (bs', bw', bpv', bh', bb')) (errv := errv);
      [ exact ENV | exact PUB | exact DQ | exact CHK | exact NB | exact SIF | exact LOSP | exact SP16 | exact FRM | exact EA0 ].
  Qed.
End DEND.
End WithCeiling0.
End Z_dend.

From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_dinit_kit Z_dinit_model Z_dreset.

Module Z_dendk.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Exit Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit Printf_pieces.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_dinit_kit Z_dreset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dreset.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZIface DeflateState Deflate HarnessSmall ZApiInst DeflateTaintRel ZTaint.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition oblk (o : option bptr) (A n : Z) : list block := match o with Some p => [(p, A, n)] | None => [] end.
Definition oadr (o : option bptr) (A : Z) : Z := match o with Some _ => A | None => 0 end.

Section DENDK.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.

  Ltac tr_up HPR H Hn :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia| intros ?a ?Ha; cbn in Ha; left; lia])) as Hn.
  Ltac tr_st HPR H Hn blk :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia
      | intros ?a ?Ha; cbn in Ha; right; right; exists blk; split; [first [left; reflexivity | apply in_or_app; left; apply in_or_app; right; left; reflexivity]| cbn; lia]])) as Hn.

  Section Walk.
  Context {A : Type}.
  Variable K : M PState A.
  Variable POST : A -> PState -> machine_state -> Prop.
  Variables (S As Ab Ah Ap Aw : Z) (bs : bptr) (sx : deflate_state).
  Variables (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word).
  Variables (pPO pGZ : word) (h1 h2 h3 h4 h5 : list byte).
  Variables (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (LB : list block) (lo B : Z) (errv canary : word).
  Variable junk : list byte.
  Notation tp := (MallocRep.wz RATP).
  Notation X := [(S, S + 112)].
  Notation SP32 := (wz (bv_unsigned sp + -32)).

  Hypothesis ST666 : ds_status sx = 666.
  Hypothesis SIF : strm_in_frame sp S B.
  Hypothesis LOSP : lo <= bv_unsigned sp - Z_DEFLATEEND_STACK.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis RAS : 0 < As /\ As + 5968 <= lo.

  Hypothesis KONT : forall (s' : PState) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    lx_env m' s' [] LB sp tp B lo errv canary ->
    lx_pres LB (bv_unsigned sp) X m m' -> ps_so s' = ps_so s -> ps_fa s' = ps_fa s ->
    rw_cells psegs m' S (zs_raw 0 ni ai ti no ao to p1 p2 msg opq dt p3 adl resv) ->
    implM psegs K s' POST
      (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (ret_pc ra) fc None m' (seg_rom psegs)).

  Local Notation "x ;;- k" := (bind lops x (fun _ => k)) (at level 62, right associativity).

  Definition DK (ob oh op ow : option bptr) (OW : list block) (sk : PState) (mk : mem) : Prop :=
    lx_env mk sk (OW ++ [(bs, As, 5968)]) LB SP32 tp B lo errv canary
    /\ lx_pres LB (bv_unsigned sp) X m mk /\ ps_so sk = ps_so s /\ ps_fa sk = ps_fa s
    /\ rw_cells psegs mk S (zs_raw As ni ai ti no ao to p1 p2 msg opq dt p3 adl resv)
    /\ rw_cells psegs mk As (dsA_raw (wz S) (wz (oadr ob Ab)) pPO pGZ (wz (oadr ow Aw)) (wz (oadr op Ap)) (wz (oadr oh Ah)) sx h1 h2 h3 h4 h5)
    /\ rw_cells psegs mk (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 s1; C8 s0; C8 ra].


  Lemma dk_site5 : forall (ob oh op ow : option bptr) (sk : PState) (mk : mem) (ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    DK ob oh op ow [] sk mk -> B < 2^63 ->
    implM psegs (lib_free lops (Some bs) ;;- K) sk POST
      (MS (mkR ra' SP32 gp tp t0' t1' t2' (wz 666) (wz S) (wz S) (wz As) a2' (wz Z_ZCFREE) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (wz 0x165a8) fc None mk (seg_rom psegs)).
  Proof.
    intros ob oh op ow sk mk ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' (ENV & PR & ESO & EFA & ZS & _ & FR) B63.
    cbn [app] in ENV.
    pose proof ENV as (HP & _ & _ & _ & _ & AUX & SPB & _ & STK & _ & _ & ERRC & _ & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold Z_DEFLATEEND_STACK, RFREE_STACK in LOSP. unfold strm_in_frame, ZS_SIZEOF in SIF.
    assert (E32 : bv_unsigned SP32 = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
    rewrite E32 in STK, SPB. unfold errno_addr in ERRC.
    unfold zs_raw, zs_pub in ZS. cbn [app] in ZS.
    pose proof (munch_refl [] mk) as MU. pose proof (wmono_refl psegs mk) as WM.
    unfold implM. iprefix.
    zstep. zstep. zstep. zstep.
    apply evt_done.
    replace (ret_pc (wz Z_ZCFREE)) with (wz Z_ZCFREE) by (symmetry; unfold Z_ZCFREE; rpc).
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm sk POST msx) end.
    eapply (dend_zfree FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ sk _ bs As 5968 lo B errv);
      [ exact HP | left; reflexivity | exact AUX | rewrite E32; exact SPB | rewrite E32; exact STK | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERRC | exact MI
      | reflexivity | reflexivity | ].
    intros s5' y0 y1 y2 f0 f1 f2 f3 f4 f5 f6 f7 y3 y4 y5 y6 m5 MIe STe ERRe AUXe HPRe EFAe ESOe HPe.
    rewrite (lb_remove_head bs _ _ _ (HND _ _ _ HP)) in HPRe, HPe. rewrite E32 in HPRe, STe.
    assert (ENVe : lx_env m5 s5' [] LB SP32 tp B lo errv canary).
    { eapply (lx_env_heap mk m5 sk s5'); [exact ENV| rewrite E32; exact HPRe| exact HPe| exact MIe| rewrite E32; exact STe| exact ERRe| exact AUXe]. }
    assert (PRe : lx_pres LB (bv_unsigned sp) X m m5).
    { eapply lx_pres_trans; [exact PR|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRe| lia| intros bx Hb; exact Hb]. }
    tr_up HPRe ZS ZSe. tr_up HPRe FR FRe. clear ZS FR.
    replace (ret_pc (wz 91576)) with (wz 91576) by (symmetry; rpc).
    pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112)] m5) as MUe. pose proof (wmono_refl psegs m5) as WMe.
    unfold implM. iprefix.
    zstep. change (Z_to_le_bytes 8 0) with (le8 (wz 0)); mem_after_store.
    zstep. zstep. zstep. zstep.
    zstep. zstep. zstep. zstep. zstep. zstep.
    release_frame FRe STe (bv_unsigned sp).
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s5' POST msx) end.
    lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ENVf : lx_env mm s5' [] LB sp tp B lo errv canary) end.
    { eapply (lx_env_munch [(lo, bv_unsigned sp); (S, S + 112)] m5 _); [exact HFRAME| exact ENVe| exact MUe| exact WMe| eassumption| exact STe| lia| |].
      - constructor; [left; cbn [fst]; lia| constructor; [left; cbn [fst]; lia| constructor]].
      - intros a Ha. cbn [outside fst snd]. unfold GLOBALS_TOP in GLO. split; [lia| split; [lia| exact I]]. }
    change (Z.land (Z.land (Z.b2z (0 <? 553) + -1) 18446744073709551615) 18446744073709551613) with 0.
    eapply KONT; [exact ENVf| | rewrite ESOe; exact ESO| rewrite EFAe; exact EFA| unfold zs_raw, zs_pub; cbn [app]; exact ZSe].
    eapply lx_pres_trans; [exact PRe|]. eapply lx_pres_of_munch; [exact MUe| exact WMe|].
    assert (LBR : forall bx, In bx LB -> blk_addr bx + blk_size bx <= lo).
    { intros bx Hb. pose proof (HBR _ _ _ bx HPe Hb) as (_ & _ & _ & X1 & _). lia. }
    intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; cbn [outside fst snd]; (split; [|split; [|exact I]]); try lia.
    all: try (specialize (LBR bx Hb); lia).
    all: unfold GLOBALS_TOP in GLO; lia.
  Qed.

  Lemma dk_site4 : forall (ob oh op ow : option bptr) (sk : PState) (mk : mem) (ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    DK ob oh op ow (oblk ow Aw 65536) sk mk -> B < 2^63 ->
    implM psegs (lib_free lops ow ;;- lib_free lops (Some bs) ;;- K) sk POST
      (MS (mkR ra' SP32 gp tp t0' t1' t2' (wz 666) (wz S) (wz S) (wz As) a2' (wz Z_ZCFREE) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (wz 0x16588) fc None mk (seg_rom psegs)).
  Proof.
    intros ob oh op ow sk mk ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' (ENV & PR & ESO & EFA & ZS & GA & FR) B63.
    pose proof ENV as (HP & _ & _ & _ & _ & AUX & SPB & _ & STK & _ & _ & ERRC & _ & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold Z_DEFLATEEND_STACK, RFREE_STACK in LOSP. unfold strm_in_frame, ZS_SIZEOF in SIF.
    assert (E32 : bv_unsigned SP32 = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
    rewrite E32 in STK, SPB. unfold errno_addr in ERRC.
    pose proof (munch_refl [] mk) as MU. pose proof (wmono_refl psegs mk) as WM.
    destruct ow as [pb|].
    -
      cbn [oadr oblk app] in HP, ENV, GA.
      pose proof (HBR _ _ _ (pb, Aw, 65536) HP (or_introl eq_refl)) as (BR1 & _ & _ & BR2 & _). cbn [blk_addr blk_size fst snd] in BR1, BR2.
      assert (EUa : bv_unsigned (wz Aw) = Aw) by (apply unsigned_lit; lia).
      pose proof ZS as ZS0. pose proof GA as GA0. unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. unfold dsA_raw in GA.
      unfold implM. iprefix.
      zstep. zstep. if_false. zstep. zstep. zstep.
      apply evt_done.
      replace (ret_pc (wz Z_ZCFREE)) with (wz Z_ZCFREE) by (symmetry; unfold Z_ZCFREE; rpc).
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm sk POST msx) end.
      eapply (dend_zfree FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ sk _ pb Aw 65536 lo B errv);
        [ exact HP | left; reflexivity | exact AUX | rewrite E32; exact SPB | rewrite E32; exact STK | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERRC | exact MI
        | reflexivity | reflexivity | ].
      intros s1' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 MIa STa ERRa AUXa HPRa EFAa ESOa HPa.
      rewrite (lb_remove_head pb _ _ _ (HND _ _ _ HP)) in HPRa, HPa. rewrite E32 in HPRa, STa.
      assert (ENVa : lx_env m1 s1' (([]) ++ [(bs, As, 5968)]) LB SP32 tp B lo errv canary).
      { eapply (lx_env_heap mk m1 sk s1'); [exact ENV| rewrite E32; eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; first [apply in_or_app; right; exact Hb | right; exact Hb]]| exact HPa| exact MIa
          | rewrite E32; exact STa| exact ERRa| exact AUXa]. }
      assert (PRa : lx_pres LB (bv_unsigned sp) X m m1).
      { eapply lx_pres_trans; [exact PR|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; first [apply in_or_app; right; exact Hb | right; exact Hb]]. }
      tr_st HPRa GA GAa (bs, As, 5968). tr_up HPRa ZS ZSa. tr_up HPRa FR FRa.
      clear GA ZS.
      replace (ret_pc (wz 91548)) with (wz 91548) by (symmetry; rpc).
      pose proof (munch_refl [] m1) as MUa. pose proof (wmono_refl psegs m1) as WMa.
      unfold implM. iprefix.
      zstep. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1' POST msx) end.
      eapply (dk_site5 ob oh op (Some pb)); [| exact B63].
      split; [exact ENVa|]. split; [exact PRa|]. split; [rewrite ESOa; exact ESO|]. split; [rewrite EFAa; exact EFA|].
      split; [unfold zs_raw, zs_pub; cbn [app]; exact ZSa|]. split; [unfold dsA_raw; exact GAa| exact FRa].
    -
      cbn [oadr oblk app] in ENV, GA.
      pose proof GA as GA0. unfold dsA_raw in GA.
      unfold implM. iprefix.
      zstep. zstep. if_true.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm sk POST msx) end.
      cbn [bind lops Target.ops lib_free lib_free_opt]. apply implM_ret_bind.
      eapply (dk_site5 ob oh op None); [| exact B63].
      split; [exact ENV|]. split; [exact PR|]. split; [exact ESO|]. split; [exact EFA|]. split; [exact ZS|]. split; [exact GA0| exact FR].
  Qed.

  Lemma dk_site3 : forall (ob oh op ow : option bptr) (sk : PState) (mk : mem) (ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    DK ob oh op ow (oblk op Ap 65536 ++ oblk ow Aw 65536) sk mk -> B < 2^63 ->
    implM psegs (lib_free lops op ;;- lib_free lops ow ;;- lib_free lops (Some bs) ;;- K) sk POST
      (MS (mkR ra' SP32 gp tp t0' t1' t2' (wz 666) (wz S) (wz S) (wz As) a2' (wz Z_ZCFREE) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (wz 0x16568) fc None mk (seg_rom psegs)).
  Proof.
    intros ob oh op ow sk mk ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' (ENV & PR & ESO & EFA & ZS & GA & FR) B63.
    pose proof ENV as (HP & _ & _ & _ & _ & AUX & SPB & _ & STK & _ & _ & ERRC & _ & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold Z_DEFLATEEND_STACK, RFREE_STACK in LOSP. unfold strm_in_frame, ZS_SIZEOF in SIF.
    assert (E32 : bv_unsigned SP32 = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
    rewrite E32 in STK, SPB. unfold errno_addr in ERRC.
    pose proof (munch_refl [] mk) as MU. pose proof (wmono_refl psegs mk) as WM.
    destruct op as [pb|].
    -
      cbn [oadr oblk app] in HP, ENV, GA.
      pose proof (HBR _ _ _ (pb, Ap, 65536) HP (or_introl eq_refl)) as (BR1 & _ & _ & BR2 & _). cbn [blk_addr blk_size fst snd] in BR1, BR2.
      assert (EUa : bv_unsigned (wz Ap) = Ap) by (apply unsigned_lit; lia).
      pose proof ZS as ZS0. pose proof GA as GA0. unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. unfold dsA_raw in GA.
      unfold implM. iprefix.
      zstep. zstep. if_false. zstep. zstep. zstep.
      apply evt_done.
      replace (ret_pc (wz Z_ZCFREE)) with (wz Z_ZCFREE) by (symmetry; unfold Z_ZCFREE; rpc).
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm sk POST msx) end.
      eapply (dend_zfree FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ sk _ pb Ap 65536 lo B errv);
        [ exact HP | left; reflexivity | exact AUX | rewrite E32; exact SPB | rewrite E32; exact STK | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERRC | exact MI
        | reflexivity | reflexivity | ].
      intros s1' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 MIa STa ERRa AUXa HPRa EFAa ESOa HPa.
      rewrite (lb_remove_head pb _ _ _ (HND _ _ _ HP)) in HPRa, HPa. rewrite E32 in HPRa, STa.
      assert (ENVa : lx_env m1 s1' ((oblk ow Aw 65536) ++ [(bs, As, 5968)]) LB SP32 tp B lo errv canary).
      { eapply (lx_env_heap mk m1 sk s1'); [exact ENV| rewrite E32; eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; first [apply in_or_app; right; exact Hb | right; exact Hb]]| exact HPa| exact MIa
          | rewrite E32; exact STa| exact ERRa| exact AUXa]. }
      assert (PRa : lx_pres LB (bv_unsigned sp) X m m1).
      { eapply lx_pres_trans; [exact PR|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; first [apply in_or_app; right; exact Hb | right; exact Hb]]. }
      tr_st HPRa GA GAa (bs, As, 5968). tr_up HPRa ZS ZSa. tr_up HPRa FR FRa.
      clear GA ZS.
      replace (ret_pc (wz 91516)) with (wz 91516) by (symmetry; rpc).
      pose proof (munch_refl [] m1) as MUa. pose proof (wmono_refl psegs m1) as WMa.
      unfold implM. iprefix.
      zstep. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1' POST msx) end.
      eapply (dk_site4 ob oh (Some pb) ow); [| exact B63].
      split; [exact ENVa|]. split; [exact PRa|]. split; [rewrite ESOa; exact ESO|]. split; [rewrite EFAa; exact EFA|].
      split; [unfold zs_raw, zs_pub; cbn [app]; exact ZSa|]. split; [unfold dsA_raw; exact GAa| exact FRa].
    -
      cbn [oadr oblk app] in ENV, GA.
      pose proof GA as GA0. unfold dsA_raw in GA.
      unfold implM. iprefix.
      zstep. zstep. if_true.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm sk POST msx) end.
      cbn [bind lops Target.ops lib_free lib_free_opt]. apply implM_ret_bind.
      eapply (dk_site4 ob oh None ow); [| exact B63].
      split; [exact ENV|]. split; [exact PR|]. split; [exact ESO|]. split; [exact EFA|]. split; [exact ZS|]. split; [exact GA0| exact FR].
  Qed.

  Lemma dk_site2 : forall (ob oh op ow : option bptr) (sk : PState) (mk : mem) (ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' : word),
    DK ob oh op ow (oblk oh Ah 65536 ++ oblk op Ap 65536 ++ oblk ow Aw 65536) sk mk -> B < 2^63 ->
    implM psegs (lib_free lops oh ;;- lib_free lops op ;;- lib_free lops ow ;;- lib_free lops (Some bs) ;;- K) sk POST
      (MS (mkR ra' SP32 gp tp t0' t1' t2' (wz 666) (wz S) (wz S) (wz As) a2' (wz Z_ZCFREE) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
          F (wz 0x16548) fc None mk (seg_rom psegs)).
  Proof.
    intros ob oh op ow sk mk ra' t0' t1' t2' a2' a4' a5' a6' a7' t3' t4' t5' t6' (ENV & PR & ESO & EFA & ZS & GA & FR) B63.
    pose proof ENV as (HP & _ & _ & _ & _ & AUX & SPB & _ & STK & _ & _ & ERRC & _ & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold Z_DEFLATEEND_STACK, RFREE_STACK in LOSP. unfold strm_in_frame, ZS_SIZEOF in SIF.
    assert (E32 : bv_unsigned SP32 = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
    rewrite E32 in STK, SPB. unfold errno_addr in ERRC.
    pose proof (munch_refl [] mk) as MU. pose proof (wmono_refl psegs mk) as WM.
    destruct oh as [pb|].
    -
      cbn [oadr oblk app] in HP, ENV, GA.
      pose proof (HBR _ _ _ (pb, Ah, 65536) HP (or_introl eq_refl)) as (BR1 & _ & _ & BR2 & _). cbn [blk_addr blk_size fst snd] in BR1, BR2.
      assert (EUa : bv_unsigned (wz Ah) = Ah) by (apply unsigned_lit; lia).
      pose proof ZS as ZS0. pose proof GA as GA0. unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. unfold dsA_raw in GA.
      unfold implM. iprefix.
      zstep. zstep. if_false. zstep. zstep. zstep.
      apply evt_done.
      replace (ret_pc (wz Z_ZCFREE)) with (wz Z_ZCFREE) by (symmetry; unfold Z_ZCFREE; rpc).
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm sk POST msx) end.
      eapply (dend_zfree FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ sk _ pb Ah 65536 lo B errv);
        [ exact HP | left; reflexivity | exact AUX | rewrite E32; exact SPB | rewrite E32; exact STK | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERRC | exact MI
        | reflexivity | reflexivity | ].
      intros s1' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 MIa STa ERRa AUXa HPRa EFAa ESOa HPa.
      rewrite (lb_remove_head pb _ _ _ (HND _ _ _ HP)) in HPRa, HPa. rewrite E32 in HPRa, STa.
      assert (ENVa : lx_env m1 s1' ((oblk op Ap 65536 ++ oblk ow Aw 65536) ++ [(bs, As, 5968)]) LB SP32 tp B lo errv canary).
      { eapply (lx_env_heap mk m1 sk s1'); [exact ENV| rewrite E32; eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; first [apply in_or_app; right; exact Hb | right; exact Hb]]| exact HPa| exact MIa
          | rewrite E32; exact STa| exact ERRa| exact AUXa]. }
      assert (PRa : lx_pres LB (bv_unsigned sp) X m m1).
      { eapply lx_pres_trans; [exact PR|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; first [apply in_or_app; right; exact Hb | right; exact Hb]]. }
      tr_st HPRa GA GAa (bs, As, 5968). tr_up HPRa ZS ZSa. tr_up HPRa FR FRa.
      clear GA ZS.
      replace (ret_pc (wz 91484)) with (wz 91484) by (symmetry; rpc).
      pose proof (munch_refl [] m1) as MUa. pose proof (wmono_refl psegs m1) as WMa.
      unfold implM. iprefix.
      zstep. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1' POST msx) end.
      eapply (dk_site3 ob (Some pb) op ow); [| exact B63].
      split; [exact ENVa|]. split; [exact PRa|]. split; [rewrite ESOa; exact ESO|]. split; [rewrite EFAa; exact EFA|].
      split; [unfold zs_raw, zs_pub; cbn [app]; exact ZSa|]. split; [unfold dsA_raw; exact GAa| exact FRa].
    -
      cbn [oadr oblk app] in ENV, GA.
      pose proof GA as GA0. unfold dsA_raw in GA.
      unfold implM. iprefix.
      zstep. zstep. if_true.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm sk POST msx) end.
      cbn [bind lops Target.ops lib_free lib_free_opt]. apply implM_ret_bind.
      eapply (dk_site3 ob None op ow); [| exact B63].
      split; [exact ENV|]. split; [exact PR|]. split; [exact ESO|]. split; [exact EFA|]. split; [exact ZS|]. split; [exact GA0| exact FR].
  Qed.
  End Walk.

  Local Notation "x ;;- k" := (bind lops x (fun _ => k)) (at level 62, right associativity).

  Theorem deflateEnd_rawK : forall {A : Type} (K : M PState A) (POST : A -> PState -> machine_state -> Prop)
         (S As Ab Ah Ap Aw : Z) (bs : bptr) (sx : deflate_state)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (msg opq dt : word) (p3 : list byte) (adl resv : word)
         (pPO pGZ : word) (h1 h2 h3 h4 h5 : list byte) (ob oh op ow : option bptr)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (lo B : Z) (errv canary : word),
    lx_env m s ((oblk ob Ab 65536 ++ oblk oh Ah 65536 ++ oblk op Ap 65536 ++ oblk ow Aw 65536) ++ [(bs, As, 5968)]) LB sp tp B lo errv canary ->
    rw_cells psegs m S (zs_raw As ni ai ti no ao to p1 p2 msg opq dt p3 adl resv) ->
    rw_cells psegs m As (dsA_raw (wz S) (wz (oadr ob Ab)) pPO pGZ (wz (oadr ow Aw)) (wz (oadr op Ap)) (wz (oadr oh Ah)) sx h1 h2 h3 h4 h5) ->
    ds_status sx = 666 ->
    strm_in_frame sp S B -> lo <= bv_unsigned sp - Z_DEFLATEEND_STACK ->
    a0 = wz S ->
    (forall (s' : PState) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
       lx_env m' s' [] LB sp tp B lo errv canary ->
       lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m' -> ps_so s' = ps_so s -> ps_fa s' = ps_fa s ->
       rw_cells psegs m' S (zs_raw 0 ni ai ti no ao to p1 p2 msg opq dt p3 adl resv) ->
       implM psegs K s' POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    implM psegs (lib_free lops ob ;;- lib_free lops oh ;;- lib_free lops op ;;- lib_free lops ow ;;- lib_free lops (Some bs) ;;- K) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_DEFLATEEND_A) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. intros ENV ZS GA ST666 SIF LOSP -> KONT.
    pose proof ENV as (HP & _ & _ & _ & _ & AUX & SPB & B63 & STK & CEIL & GLO & ERRC & TP & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (RAS : 0 < As /\ As + 5968 <= lo).
    { pose proof (HBR _ _ _ (bs, As, 5968) HP ltac:(apply in_or_app; left; apply in_or_app; right; left; reflexivity)) as (X1 & _ & _ & X2 & _).
      cbn [blk_addr blk_size fst snd] in X1, X2. lia. }
    subst tp. unfold errno_addr in ERRC.
    pose proof LOSP as LOSP'. unfold Z_DEFLATEEND_STACK, RFREE_STACK in LOSP'. pose proof SIF as SIF'. unfold strm_in_frame, ZS_SIZEOF in SIF'.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
    assert (E32 : bv_unsigned (wz (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
    unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. unfold dsA_raw in GA.
    unfold implM. iprefix. unfold Z_DEFLATEEND_A.
    zstep. zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_false. zstep. zstep. if_false.
    carve_frame 32%nat STK.
    zstep. zstep. zstep. zstep. zstep. zstep. if_false.
    zstep. rewrite ST666, (sx32_wz 666) by lia. zstep. zstep. zstep. if_true. zstep. zstep. if_true.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ENV1 : lx_env mm s ((oblk ob Ab 65536 ++ oblk oh Ah 65536 ++ oblk op Ap 65536 ++ oblk ow Aw 65536) ++ [(bs, As, 5968)]) LB
                       (wz (bv_unsigned sp + -32)) (MallocRep.wz RATP) B lo errv canary) end.
    { eapply (lx_env_munch [(lo, bv_unsigned sp)] m _); [exact HFRAME| exact ENV| exact MU| exact WM| assumption| rewrite E32; exact STK| rewrite E32; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. unfold GLOBALS_TOP in GLO. split; [lia| exact I]. }
    assert (LBR : forall bx, In bx LB -> blk_addr bx + blk_size bx <= lo).
    { intros bx Hb. pose proof (HBR _ _ _ bx HP (in_or_app _ _ bx (or_intror Hb))) as (_ & _ & _ & X1 & _). lia. }
    assert (PR0 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m0).
    { eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [outside fst snd]; (split; [|exact I]).
      - lia.
      - specialize (LBR bx Hb). lia.
      - unfold GLOBALS_TOP in GLO. lia. }
    pose proof ENV1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & STK1 & _ & _ & ERR1 & _ & MI1). rewrite E32 in STK1, SPB1. unfold errno_addr in ERR1.
    destruct ob as [pb|].
    - cbn [oadr oblk app] in HP1, ENV1, GA.
      pose proof (HBR _ _ _ (pb, Ab, 65536) HP1 (or_introl eq_refl)) as (BR1 & _ & _ & BR2 & _). cbn [blk_addr blk_size fst snd] in BR1, BR2.
      assert (EUa : bv_unsigned (wz Ab) = Ab) by (apply unsigned_lit; lia).
      zstep. zstep. zstep. if_false. zstep. zstep. zstep.
      apply evt_done.
      replace (ret_pc (wz Z_ZCFREE)) with (wz Z_ZCFREE) by (symmetry; unfold Z_ZCFREE; rpc).
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
      eapply (dend_zfree FREE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ s _ pb Ab 65536 lo B errv);
        [ exact HP1 | left; reflexivity | exact AUX1 | rewrite E32; exact SPB1 | rewrite E32; exact STK1 | exact CEIL | rewrite E32; unfold RFREE_STACK; lia | exact ERR1 | exact MI1
        | reflexivity | reflexivity | ].
      intros s1' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1 MIa STa ERRa AUXa HPRa EFAa ESOa HPa.
      rewrite (lb_remove_head pb _ _ _ (HND _ _ _ HP1)) in HPRa, HPa. rewrite E32 in HPRa, STa.
      assert (ENVa : lx_env m1 s1' ((oblk oh Ah 65536 ++ oblk op Ap 65536 ++ oblk ow Aw 65536) ++ [(bs, As, 5968)]) LB (wz (bv_unsigned sp + -32)) (MallocRep.wz RATP) B lo errv canary).
      { eapply (lx_env_heap m0 m1 s s1'); [exact ENV1| rewrite E32; eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; apply in_or_app; right; exact Hb]| exact HPa| exact MIa
          | rewrite E32; exact STa| exact ERRa| exact AUXa]. }
      assert (PRa : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m1).
      { eapply lx_pres_trans; [exact PR0|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPRa| lia| intros bx Hb; apply in_or_app; right; exact Hb]. }
      tr_st HPRa GA GAa (bs, As, 5968). tr_up HPRa ZS ZSa. tr_up HPRa FR FRa.
      clear GA ZS.
      replace (ret_pc (wz 91452)) with (wz 91452) by (symmetry; rpc).
      pose proof (munch_refl [] m1) as MUa. pose proof (wmono_refl psegs m1) as WMa.
      unfold implM. iprefix.
      zstep. zstep. zstep.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s1' POST msx) end.
      eapply (dk_site2 K POST S As Ab Ah Ap Aw bs sx ni ai ti no ao to p1 p2 msg opq dt p3 adl resv pPO pGZ h1 h2 h3 h4 h5)
        with (B := B) (lo := lo) (LB := LB) (m := m) (s := s) (errv := errv) (canary := canary) (junk := junk) (ra := ra) (s0 := s0) (s1 := s1) (ob := Some pb);
        [ exact SIF | exact LOSP | exact CEIL | exact GLO | exact RAS | exact KONT | | exact B63 ].
      split; [exact ENVa|]. split; [exact PRa|]. split; [exact ESOa|]. split; [exact EFAa|].
      split; [unfold zs_raw, zs_pub; cbn [app]; exact ZSa|]. split; [unfold dsA_raw; exact GAa| exact FRa].
    - cbn [oadr oblk app] in ENV1, GA.
      zstep. zstep. zstep. if_true.
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
      cbn [bind lops Target.ops lib_free lib_free_opt]. apply implM_ret_bind.
      eapply (dk_site2 K POST S As Ab Ah Ap Aw bs sx ni ai ti no ao to p1 p2 msg opq dt p3 adl resv pPO pGZ h1 h2 h3 h4 h5)
        with (B := B) (lo := lo) (LB := LB) (m := m) (s := s) (errv := errv) (canary := canary) (junk := junk) (ra := ra) (s0 := s0) (s1 := s1) (ob := None);
        [ exact SIF | exact LOSP | exact CEIL | exact GLO | exact RAS | exact KONT | | exact B63 ].
      split; [exact ENV1|]. split; [exact PR0|]. split; [reflexivity|]. split; [reflexivity|].
      split; [unfold zs_raw, zs_pub; cbn [app]; exact ZS|]. split; [unfold dsA_raw; exact GA| exact FR].
  Qed.
End DENDK.
End WithCeiling0.
End Z_dendk.


Module Z_dinit_pieces.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Exit Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit Printf_pieces Z_zrd Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_dinit_kit Z_dinit_model Z_dreset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_zrd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dreset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dendk.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface DeflateState Deflate RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require HarnessSmall ZApiInst DeflateTaintRel ZTaint BoundPat ZPat FillWinModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflateInitLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.HarnessSmall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateTaintRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZTaint OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BoundPat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZPat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation MP := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Monad.M PState).
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section DINIT_PIECES.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.

  Lemma dinit_zalloc : forall {A : Type} (K : option bptr -> MP A) (POST : A -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LBc : list block) (items size n lo B : Z) (errv : word),
    RHEAP s LBc m ->
    rauxv_ok m B -> bv_unsigned sp <= B ->
    stk psegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RMALLOC_STACK ->
    rw_cells psegs m (errno_addr tp) [C4 errv] -> mem_inv psegs m -> tp = Z_to_bv 64 RATP ->
    a1 = wz items -> a2 = wz size -> n = items * size -> 0 <= items < 2^31 -> 0 <= size < 2^31 -> items * size < 2^32 ->
    (forall (r : option bptr) (s' : PState) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (errv' : word),
       mem_inv psegs m' -> stk psegs m' lo (bv_unsigned sp) -> rw_cells psegs m' (errno_addr tp) [C4 errv'] -> rauxv_ok m' B ->
       rheap_pres LBc (bv_unsigned sp) m m' -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
       match r with
       | None => a0' = wz 0 /\ RHEAP s' LBc m'
       | Some p => exists Ab junk, a0' = wz Ab /\ rblock_range Ab n /\ RHEAP s' ((p, Ab, n) :: LBc) m' /\ rw_cells psegs m' Ab [CB (Z.to_nat n) junk]
       end ->
       implM psegs (K r) s' POST
         (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom psegs))) ->
    implM psegs (bind lops (lib_malloc lops n) K) s POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz Z_ZCALLOC) fc None m (seg_rom psegs)).
  Proof.
    intros until errv. intros HP AUX SPB STK CEIL LOSP ERRC MI TP -> -> -> RI RS RN KONT.
    cbn [bind lops Target.ops lib_malloc].
    pose proof (munch_refl [] m) as MU. pose proof (wmono_refl psegs m) as WM.
    unfold implM. iprefix. unfold Z_ZCALLOC. zstep. zstep. zstep. zstep.
    replace (Z.land (size * items) 4294967295) with (items * size).
    2:{ change 4294967295 with (Z.ones 32). rewrite Z.land_ones by lia. rewrite Z.mod_small by nia. lia. }
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
    eapply implM_bind.
    { eapply (MALLOC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s LBc (items * size) lo B errv);
        [ exact HP | exact AUX | exact SPB | exact STK | exact CEIL | exact LOSP | exact ERRC | exact MI | exact TP | reflexivity | nia ]. }
    cbv beta. intros r s' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & errv' & -> & MI' & ST' & ERR' & AUX' & HPR' & EFA' & ESO' & PR).
    eapply (KONT r s' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m' errv' MI' ST' ERR' AUX' HPR' EFA' ESO').
    destruct r as [p|].
    - destruct PR as (Ab & junk & E0 & BR & HP' & CB & _). exists Ab, junk. auto.
    - exact PR.
  Qed.


  Local Notation "x ;;- k" := (bind lops x (fun _ => k)) (at level 62, right associativity).

  Lemma dinit_fail : forall (R : zreps)
         (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LB : list block) (S As : Z) (ps : bptr) (lo B : Z) (canary : word)
         (ni ai ti no ao to : Z) (p1 p2 : list byte)
         (ob oh op ow : option bptr) (Ab Ah Ap Aw : Z) (sk : PState) (mk : mem) (errv : word)
         (msg dt : word) (p3 : list byte) (adl resv pPO pGZ : word) (sx : deflate_state) (h1 h2 h3 h4 h5 : list byte)
         (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' v18 v19 v20 v21 v22 v23 t3' t4' t5' t6' : word),
    strm_in_frame sp S B -> lo <= bv_unsigned sp - Z_DEFLATEINIT_STACK -> frm0 fc ->
    lx_env mk sk ((oblk ob Ab 65536 ++ oblk oh Ah 65536 ++ oblk op Ap 65536 ++ oblk ow Aw 65536) ++ [(ps, As, 5968)]) LB
           (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv canary ->
    lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mk -> ps_so sk = ps_so s -> ps_fa sk = ps_fa s ->
    rw_cells psegs mk S (zs_raw As ni ai ti no ao to p1 p2 msg (wz 0) dt p3 adl resv) ->
    rw_cells psegs mk As (dsA_raw (wz S) (wz (oadr ob Ab)) pPO pGZ (wz (oadr ow Aw)) (wz (oadr op Ap)) (wz (oadr oh Ah)) sx h1 h2 h3 h4 h5) ->
    rw_cells psegs mk (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    implM psegs (lib_free lops ob ;;- lib_free lops oh ;;- lib_free lops op ;;- lib_free lops ow ;;- lib_free lops (Some ps) ;;- ret lops None) sk
      (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
      (MS (mkR ra' (wz (bv_unsigned sp + -80)) gp (wz RATP) t0' t1' t2' (wz S) (wz As) a0' a1' a2' a3' a4' a5' a6' a7' v18 v19 v20 v21 v22 v23 s8 s9 s10 s11 t3' t4' t5' t6')
          F (wz 0x16474) fc None mk (seg_rom psegs)).
  Proof.
    intros until t6'. intros SIF LOSP FRM ENV PR ESO EFA ZS GA FR.
    pose proof ENV as (HP & _ & ZLS & _ & _ & AUX & SPB & B63 & STK & CEIL & GLO & ERRC & _ & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof SIF as SIF'. unfold strm_in_frame, ZS_SIZEOF in SIF'. pose proof LOSP as LOSP'. unfold Z_DEFLATEINIT_STACK, RMALLOC_STACK in LOSP'.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    assert (E80 : bv_unsigned (wz (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    rewrite E80 in STK, SPB.
    assert (INs : In (ps, As, 5968) (((oblk ob Ab 65536 ++ oblk oh Ah 65536 ++ oblk op Ap 65536 ++ oblk ow Aw 65536) ++ [(ps, As, 5968)]) ++ LB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    assert (RAS : 0 < As /\ As + 5968 <= lo).
    { pose proof (HBR _ _ _ (ps, As, 5968) HP INs) as (X1 & _ & _ & X2 & _). cbn [blk_addr blk_size fst snd] in X1, X2. lia. }
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
    pose proof (got_zalloc_relro _ (relro_clean_of_zl _ ZLS)) as GOT.
    pose proof (errmsg6_relro _ (relro_clean_of_zl _ ZLS)) as EMSG.
    unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. unfold dsA_raw in GA.
    pose proof (munch_refl [(S, S + 112); (As, As + 212)] mk) as MU. pose proof (wmono_refl psegs mk) as WM.
    unfold implM. iprefix.
    zs. zs. zs. zs. zs. zs. zs. zs.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ (MS _ _ _ _ _ ?mm _) => assert (ENV1 : lx_env mm sk
        ((oblk ob Ab 65536 ++ oblk oh Ah 65536 ++ oblk op Ap 65536 ++ oblk ow Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv canary) end.
    { pose proof (HBR _ _ _ (ps, As, 5968) HP INs) as (_ & _ & _ & _ & IMG). cbn [blk_addr blk_size fst snd] in IMG.
      eapply (lx_env_munch [(S, S + 112); (As, As + 212)] mk _); [exact HFRAME| exact ENV| exact MU| exact WM| eassumption| rewrite E80; exact STK| rewrite E80; lia| |].
      - constructor; [left; cbn [fst]; lia|]. constructor; [|constructor].
        right; right. exists (ps, As, 5968). split; [exact INs| cbn [blk_addr blk_size fst snd]; lia].
      - intros a Ha. cbn [outside fst snd]. split; [lia| split; [lia| exact I]]. }
    assert (PR1 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m1).
    { eapply lx_pres_trans; [exact PR|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
      assert (LBR : forall bx, In bx LB -> blk_addr bx + blk_size bx <= As \/ As + 5968 <= blk_addr bx).
      { intros bx Hb. pose proof (heap_sep sk _ LB mk (ps, As, 5968) bx HND HBD HP ltac:(apply in_or_app; right; left; reflexivity) Hb) as SEP.
        cbn [blk_addr blk_size fst snd] in SEP. lia. }
      intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; cbn [outside fst snd]; (split; [|split; [|exact I]]); try lia.
      all: try (specialize (LBR bx Hb); lia).
      pose proof (HBR _ _ _ (ps, As, 5968) HP INs) as (_ & _ & _ & _ & IMG).
      cbn [blk_addr blk_size fst snd] in IMG. lia. }
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm sk (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
    eapply (deflateEnd_rawK FREE HND HBR HFRAME (ret lops None) _ S As Ab Ah Ap Aw ps (set_status sx 666) ni ai ti no ao to p1 p2 _ (wz 0) dt p3 adl resv pPO pGZ h1 h2 h3 h4 h5 ob oh op ow)
      with (lo := lo) (B := B) (errv := errv) (canary := canary) (LB := LB);
      [ exact ENV1 | unfold zs_raw, zs_pub; cbn [app]; exact ZS | exact GA | reflexivity
      | unfold strm_in_frame, ZS_SIZEOF; rewrite E80; lia | rewrite E80; unfold Z_DEFLATEEND_STACK, RFREE_STACK; lia | reflexivity | ].
    intros s' u0 u1 u2 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6 m' ENV' PR' ESO' EFA' ZS'.
    rewrite E80 in PR'.
    replace (ret_pc (wz 91284)) with (wz 91284) by (symmetry; rpc).
    assert (FR' : rw_cells psegs m' (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply Drv_kit.rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PR')| exact FR|].
      intros a Ha. cbn in Ha. apply stack_client; [lia| cbn [rin_ivs fst snd]; lia]. }
    pose proof ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & STK' & _ & _ & _ & _ & MI'). rewrite E80 in STK'.
    cbn [ret lops Target.ops]. apply implM_ret.
    pose proof (munch_refl [] m') as MU'. pose proof (wmono_refl psegs m') as WM'.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. (* 1.4: + ld s8 *)
    release_frame FR' STK' (bv_unsigned sp).
    apply evt_done. unfold deflateInit_post. do 15 eexists. exists F, fc, m'.
    split; [reflexivity|]. cbv beta iota.
    split; [|split; [unfold wint, ZApi.Z_MEM_ERROR, MallocRep.wz; apply bv_eq; reflexivity|]].
    - unfold lx_post_env. split; [exists errv; eapply lx_env_sp; [exact ENV'| exact STK'| lia]|]. split; [exact FRM|].
      split; [| split; [rewrite ESO'; exact ESO| rewrite EFA'; exact EFA]].
      eapply lx_pres_trans; [exact PR1|]. eapply lx_pres_weaken; [exact PR'| lia| intros bx Hb; exact Hb| intros a Ha; exact Ha].
    - destruct (rw_cells_forget psegs m' _ _ ZS') as (j & Hj). exists j. exact Hj.
  Qed.


  Lemma zalloc_res : forall (r : option bptr) (a0' : word) (s' : PState) (LBc : list block) (m' : mem) (n : Z),
    match r with
    | None => a0' = wz 0 /\ RHEAP s' LBc m'
    | Some p => exists Ab junk, a0' = wz Ab /\ rblock_range Ab n /\ RHEAP s' ((p, Ab, n) :: LBc) m' /\ rw_cells psegs m' Ab [CB (Z.to_nat n) junk]
    end ->
    exists (A : Z) (junk : list byte), a0' = wz (oadr r A) /\ RHEAP s' (oblk r A n ++ LBc) m'
      /\ (forall p, r = Some p -> rblock_range A n /\ rw_cells psegs m' A [CB (Z.to_nat n) junk]).
  Proof.
    intros [p|] a0' s' LBc m' n H.
    - destruct H as (Ab & junk & E & BR & HP & CB). exists Ab, junk. cbn [oadr oblk app]. split; [exact E|]. split; [exact HP|]. intros q _. split; assumption.
    - destruct H as (E & HP). exists 0, []. cbn [oadr oblk app]. split; [exact E|]. split; [exact HP|]. intros q Hq. discriminate Hq.
  Qed.

  Definition BK (o : option bptr) (A : Z) (mk mc : mem) : Prop := forall p, o = Some p -> agree_on A (A + 65536) mk mc.

  Lemma BK_refl : forall o A mk, BK o A mk mk.
  Proof. intros o A mk p _. apply agree_on_refl. Qed.

  Lemma BK_hpres : forall o A mk mc mc' LBc SP, BK o A mk mc -> rheap_pres LBc SP mc mc' ->
    (forall p, o = Some p -> In (p, A, 65536) LBc /\ 0 <= A /\ A + 65536 <= 2^64) -> BK o A mk mc'.
  Proof.
    intros o A mk mc mc' LBc SP H HPR HIN p E. destruct (HIN p E) as (IN & R0 & R1).
    eapply agree_on_trans; [exact (H p E)|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR); [exact R0| exact R1|].
    intros a Ha. right; right. exists (p, A, 65536). split; [exact IN| cbn [blk_addr blk_size fst snd]; lia].
  Qed.

  Lemma BK_munch : forall o A mk mc mc' W, BK o A mk mc -> munch W mc mc' -> wmono psegs mc mc' ->
    (forall p, o = Some p -> disjoint_from W A 65536 /\ 0 <= A /\ A + 65536 <= 2^64) -> BK o A mk mc'.
  Proof.
    intros o A mk mc mc' W H MU WM HD p E. destruct (HD p E) as (D & R0 & R1).
    eapply agree_on_trans; [exact (H p E)|]. apply (agree_on_of_munch W); [exact MU| exact WM| exact R0| exact R1| exact D].
  Qed.

  Definition WI (S As : Z) : list ivl := [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)].

  Lemma dinit_env_munch : forall m m' st OW LB (sp' : word) B lo errv canary S As ps,
    lx_env m st OW LB sp' (wz RATP) B lo errv canary -> munch (WI S As) m m' -> wmono psegs m m' -> mem_inv psegs m' ->
    In (ps, As, 5968) (OW ++ LB) -> bv_unsigned sp' <= S -> lo <= S -> S + 112 <= B -> As + 5968 <= lo ->
    lx_env m' st OW LB sp' (wz RATP) B lo errv canary.
  Proof.
    intros m m' st OW LB sp' B lo errv canary S As ps ENV MU WM MI' IN LS LLS SB LA.
    pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & _ & STK & CEIL & GLO & _).
    pose proof (HBR _ _ _ _ HP IN) as (R1 & _ & _ & R2 & IMG). cbn [blk_addr blk_size fst snd] in R1, R2, IMG.
    unfold GLOBALS_TOP in GLO.
    assert (STK' : stk psegs m' lo (bv_unsigned sp')).
    { eapply (stk_transport_disjoint psegs (WI S As) m m' lo (bv_unsigned sp')); [exact STK| exact MU| exact WM|].
      unfold WI. cbn [disjoint_from]. lia. }
    eapply (lx_env_munch (WI S As) m m'); [exact HFRAME| exact ENV| exact MU| exact WM| exact MI'| exact STK'| exact SPB| |].
    - unfold WI. constructor; [left; cbn [fst]; lia|].
      constructor; [right; right; exists (ps, As, 5968); split; [exact IN| cbn [blk_addr blk_size fst snd]; lia]|].
      constructor; [right; right; exists (ps, As, 5968); split; [exact IN| cbn [blk_addr blk_size fst snd]; lia]| constructor].
    - intros a Ha. unfold WI. cbn [outside fst snd]. split; [lia| split; [lia| split; [lia| exact I]]].
  Qed.

  Lemma dinit_pres_munch : forall LB SP m0 m m' st OW S As ps,
    lx_pres LB SP [(S, S + 112)] m0 m -> munch (WI S As) m m' -> wmono psegs m m' ->
    RHEAP st (OW ++ LB) m -> In (ps, As, 5968) OW -> As + 5968 <= SP ->
    lx_pres LB SP [(S, S + 112)] m0 m'.
  Proof.
    intros LB SP m0 m m' st OW S As ps PR MU WM HP IN LS.
    eapply lx_pres_trans; [exact PR|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_introl IN))) as (R1 & _ & _ & R2 & IMG). cbn [blk_addr blk_size fst snd] in R1, R2, IMG.
    intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; unfold WI; cbn [outside fst snd]; (split; [|split; [|split; [|exact I]]]); try lia.
    all: pose proof (heap_sep st OW LB m (ps, As, 5968) bx HND HBD HP IN Hb) as SEP; cbn [blk_addr blk_size fst snd] in SEP; lia.
  Qed.

  (* 1.4: deflateInit2_'s memset(s + 8, 0, 5960) writes inside the state block only. *)
  Definition WZ (As : Z) : list ivl := [(As + 8, As + 5968)].

  Lemma dinit_env_munchZ : forall m m' st OW LB (sp' : word) B lo errv canary As ps,
    lx_env m st OW LB sp' (wz RATP) B lo errv canary -> munch (WZ As) m m' -> wmono psegs m m' -> mem_inv psegs m' ->
    In (ps, As, 5968) (OW ++ LB) -> As + 5968 <= lo -> lo <= B ->
    lx_env m' st OW LB sp' (wz RATP) B lo errv canary.
  Proof.
    intros m m' st OW LB sp' B lo errv canary As ps ENV MU WM MI' IN LA LB'.
    pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & _ & STK & CEIL & GLO & _).
    pose proof (HBR _ _ _ _ HP IN) as (R1 & _ & _ & R2 & IMG). cbn [blk_addr blk_size fst snd] in R1, R2, IMG.
    unfold GLOBALS_TOP in GLO.
    assert (STK' : stk psegs m' lo (bv_unsigned sp')).
    { eapply (stk_transport_disjoint psegs (WZ As) m m' lo (bv_unsigned sp')); [exact STK| exact MU| exact WM|].
      unfold WZ. cbn [disjoint_from]. lia. }
    eapply (lx_env_munch (WZ As) m m'); [exact HFRAME| exact ENV| exact MU| exact WM| exact MI'| exact STK'| exact SPB| |].
    - unfold WZ. constructor; [right; right; exists (ps, As, 5968); split; [exact IN| cbn [blk_addr blk_size fst snd]; lia]| constructor].
    - intros a Ha. unfold WZ. cbn [outside fst snd]. split; [lia| exact I].
  Qed.

  Lemma dinit_pres_munchZ : forall LB SP m0 m m' st OW S As ps,
    lx_pres LB SP [(S, S + 112)] m0 m -> munch (WZ As) m m' -> wmono psegs m m' ->
    RHEAP st (OW ++ LB) m -> In (ps, As, 5968) OW -> As + 5968 <= SP ->
    lx_pres LB SP [(S, S + 112)] m0 m'.
  Proof.
    intros LB SP m0 m m' st OW S As ps PR MU WM HP IN LS.
    eapply lx_pres_trans; [exact PR|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_introl IN))) as (R1 & _ & _ & R2 & IMG). cbn [blk_addr blk_size fst snd] in R1, R2, IMG.
    intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; unfold WZ; cbn [outside fst snd]; (split; [|exact I]); try lia.
    all: pose proof (heap_sep st OW LB m (ps, As, 5968) bx HND HBD HP IN Hb) as SEP; cbn [blk_addr blk_size fst snd] in SEP; lia.
  Qed.

  Lemma dinit_ags_munch : forall m1 m m' S As, agree_on (As + 212) (As + 5881) m1 m -> munch (WI S As) m m' -> wmono psegs m m' ->
    0 <= As -> As + 5968 <= 2^64 -> (S + 112 <= As \/ As + 5968 <= S) -> agree_on (As + 212) (As + 5881) m1 m'.
  Proof.
    intros m1 m m' S As AG MU WM R0 R1 SEP. eapply agree_on_trans; [exact AG|].
    apply (agree_on_sub (As + 212) (As + 212 + 5669)); [| lia| lia].
    apply (agree_on_of_munch (WI S As)); [exact MU| exact WM| lia| lia|]. unfold WI. cbn [disjoint_from]. lia.
  Qed.

  Lemma buf_in : forall st OWb LB m p A As ps, RHEAP st (OWb ++ (ps, As, 5968) :: LB) m -> In (p, A, 65536) OWb ->
    In (p, A, 65536) (OWb ++ (ps, As, 5968) :: LB) /\ 0 <= A /\ A + 65536 <= 2^64.
  Proof.
    intros st OWb LB m p A As ps HP IN. assert (IN' : In (p, A, 65536) (OWb ++ (ps, As, 5968) :: LB)) by (apply in_or_app; left; exact IN).
    pose proof (HBR _ _ _ _ HP IN') as (R1 & _ & _ & R2 & _). cbn [blk_addr blk_size fst snd] in R1, R2. split; [exact IN'| lia].
  Qed.

  Lemma buf_disj : forall st OWb LB m p A S As ps lo, RHEAP st (OWb ++ (ps, As, 5968) :: LB) m -> In (p, A, 65536) OWb ->
    lo <= S -> alloc_ceiling <= lo ->
    disjoint_from (WI S As) A 65536 /\ 0 <= A /\ A + 65536 <= 2^64.
  Proof.
    intros st OWb LB m p A S As ps lo HP IN LS CEIL. destruct (buf_in _ _ _ _ _ _ _ _ HP IN) as (IN' & R0 & R1).
    pose proof (HBR _ _ _ _ HP IN') as (_ & _ & _ & R2 & _). cbn [blk_addr blk_size fst snd] in R2.
    pose proof (heap_sep st OWb ((ps, As, 5968) :: LB) m (p, A, 65536) (ps, As, 5968) HND HBD HP IN (or_introl eq_refl)) as SEP.
    cbn [blk_addr blk_size fst snd] in SEP. split; [| lia]. unfold WI. cbn [disjoint_from]. lia.
  Qed.

End DINIT_PIECES.
End WithCeiling0.

  Ltac in_ow E := rewrite E; repeat first [solve [left; reflexivity] | apply in_or_app; right].

  Ltac tr_up HPR H Hn :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia| intros ?a ?Ha; cbn in Ha; left; lia])) as Hn.
  Ltac tr_blk HPR H Hn blk IN :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia
      | intros ?a ?Ha; cbn in Ha; right; right; exists blk; split; [exact IN| cbn; lia]])) as Hn.
End Z_dinit_pieces.


Module Z_dinit_tail.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Str_tac.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Exit Startup_glue.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_fwritex.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit Printf_pieces Z_zrd Z_trees_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Z_dinit_kit Z_dinit_model Z_dreset.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_zrd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dreset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dendk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dinit_pieces.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface DeflateState Deflate RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require HarnessSmall ZApiInst ZApiOk DeflateTaintRel ZTaint BoundPat ZPat FillWinModel DeflateSafe.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflateInitLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.HarnessSmall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZApiOk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateTaintRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZTaint OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BoundPat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZPat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation MP := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Monad.M PState).
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section DINIT_TAIL.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HTRI : tr_init_stmt.
  Local Notation dinit_failH := (dinit_fail FREE HND HBR HBD HFRAME).
  Local Notation dinit_env_munchH := (dinit_env_munch HBR HFRAME).
  Local Notation dinit_pres_munchH := (dinit_pres_munch HND HBR HBD).
  Local Notation buf_inH := (buf_in HBR).
  Local Notation buf_disjH := (buf_disj HND HBR HBD).
  Local Notation "x ;;- k" := (bind lops x (fun _ => k)) (at level 62, right associativity).
  Local Transparent the_zapi.

  Definition sx5 (jks : list byte) : deflate_state := s_lbs (s_setup (orc jks) 0%N dinit_cs 1 15 8) 8.

  Definition G5 (jks jkw jkp jkh jkb : list byte) (k : N) : Z -> Z :=
    match k with 0%N => orc jks | 1%N => orc jkw | 2%N => orc jkp | 3%N => orc jkh | _ => orc jkb end.

  Lemma dinit_tail : forall (R : zreps), Zlib_iface.zr_d R = Z_zrd.zr_d ->
    forall (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : mem) (s : PState) (LB : list block) (S ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (canary : word)
         (ps : bptr) (As : Z) (jks : list byte) (m1 : mem)
         (rw rp rh rb : option bptr) (Aw Ap Ah Ab : Z) (jkw jkp jkh jkb : list byte) (mP2 mP3 mP4 mP5 : mem) (st5 : PState) (errv5 : word)
         (dt0 : word) (p30 : list byte) (adl0 resv0 : word)
         (ra0 v50 v51 v52 d51 d52 d53 d54 d55 d56 d57 v53 v54 v55 v56 : word),
    strm_in_frame sp S B -> lo <= bv_unsigned sp - Z_DEFLATEINIT_STACK -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
    lx_env mP5 st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB
           (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv5 canary ->
    lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP5 -> ps_so st5 = ps_so s -> ps_fa st5 = ps_fa s ->
    rw_cells psegs m1 As [CB (Z.to_nat 5968) jks] -> rblock_range As 5968 ->
    agree_on (As + 212) (As + 5881) m1 mP5 ->
    BK rw Aw mP2 mP5 -> BK rp Ap mP3 mP5 -> BK rh Ah mP4 mP5 ->
    (forall p, rw = Some p -> rblock_range Aw 65536 /\ rw_cells psegs mP2 Aw [CB (Z.to_nat 65536) jkw]) ->
    (forall p, rp = Some p -> rblock_range Ap 65536 /\ rw_cells psegs mP3 Ap [CB (Z.to_nat 65536) jkp]) ->
    (forall p, rh = Some p -> rblock_range Ah 65536 /\ rw_cells psegs mP4 Ah [CB (Z.to_nat 65536) jkh]) ->
    (forall p, rb = Some p -> rblock_range Ab 65536 /\ rw_cells psegs mP5 Ab [CB (Z.to_nat 65536) jkb]) ->
    rw_cells psegs mP5 As (dsA_raw (wz S) (jw jks 16) (jw jks 32) (wz 0) (wz (oadr rw Aw)) (wz (oadr rp Ap)) (wz (oadr rh Ah)) (sx5 jks)
                                   (jp jks 12 4) (jp jks 52 4) (jp jks 73 3) (jp jks 92 4) (jp jks 148 4)) ->
    rw_cells psegs mP5 (As + 5881) (dsD_raw (jw jks 5888) (sx5 jks) (jp jks 5881 7) (jp jks 5908 4) (jp jks 5938 2) (jp jks 5944 4) (jp jks 5960 4)) ->
    rw_cells psegs mP5 S (zs_raw As ni ai ti no ao to p1 p2 (wz 0) (wz 0) dt0 p30 adl0 resv0) ->
    rw_cells psegs mP5 (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    implM psegs
      (match rw, rp, rh, rb with
       | Some wp, Some pp, Some hp, Some bp => ret lops (Some (ps, wp, pp, hp, bp))
       | _, _, _, _ => lib_free lops rb ;;- lib_free lops rh ;;- lib_free lops rp ;;- lib_free lops rw ;;- lib_free lops (Some ps) ;;- ret lops None
       end) st5
      (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
      (MS (mkR ra0 (wz (bv_unsigned sp + -80)) gp (wz RATP) v50 v51 v52 (wz S) (wz As) (wz (oadr rb Ab)) d51 d52 d53 d54 d55 d56 d57
               (wz 0) (wz 6) (wz (As + 5888)) (wz 1) (wz 15) (wz 8) s8 s9 s10 s11 v53 v54 v55 v56)
          F (wz 0x163ec) fc None mP5 (seg_rom psegs)).
  Proof.
    intros R RD. intros until v56. intros SIF LOSP SP16 FRM ENV5 PR5 ESO5 EFA5 CBs BRs AGs5 BKw BKp BKh BUFw BUFp BUFh BUFb GA GD ZS FR.
    pose proof ENV5 as (HP5 & _ & ZLS & _ & _ & AUX & SPB & B63 & STK & CEIL & GLO & ERRC & _ & MI).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof SIF as SIF'. unfold strm_in_frame, ZS_SIZEOF in SIF'. pose proof LOSP as LOSP'. unfold Z_DEFLATEINIT_STACK, RMALLOC_STACK in LOSP'.
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    assert (E80 : bv_unsigned (wz (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    rewrite E80 in STK, SPB.
    destruct BRs as (BRs1 & BRs2 & _ & BRs3 & BRs4).
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
    assert (INs : In (ps, As, 5968) (((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) ++ LB))
      by (apply in_or_app; left; apply in_or_app; right; left; reflexivity).
    unfold zs_raw, zs_pub in ZS. cbn [app] in ZS. unfold dsA_raw, sx5 in GA. unfold dsD_raw, sx5 in GD.
    cbn [s_lbs s_setup set_status set_wrap set_gzhead set_w_bits set_w_size set_w_mask set_hash_bits set_hash_size set_hash_mask set_hash_shift set_high_water set_lit_bufsize
         ds_of_oracle ds_status ds_pending_buf_size ds_pending ds_wrap ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask
         ds_window_size ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available
         ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match
         ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water] in GA, GD.
    change (Z.shiftl 1 15) with 32768 in GA. change (Z.shiftl 1 (8 + 7)) with 32768 in GA. change (8 + 7) with 15 in GA.
    change ((15 + MIN_MATCH - 1) / MIN_MATCH) with 5 in GA. change (32768 - 1) with 32767 in GA. change (Z.shiftl 1 (8 + 6)) with 16384 in GD.
    unfold MallocRep.wz, Z_ZCALLOC, Z_ZCFREE in ZS.
    pose proof (munch_refl (WI S As) mP5) as MU5. pose proof (wmono_refl psegs mP5) as WM5. unfold WI in MU5.
    unfold implM. iprefix.
    zs. zs. zs. zs. zs.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mF end.
    assert (MIF : mem_inv psegs mF) by eassumption.
    assert (ENVF : lx_env mF st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB
                          (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv5 canary)
      by (eapply (dinit_env_munchH mP5 mF); [exact ENV5| exact MU5| exact WM5| exact MIF| exact INs| rewrite E80; lia| lia| lia| lia]).
    assert (PRF : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mF)
      by (eapply (dinit_pres_munchH LB _ m mP5 mF st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]));
          [exact PR5| exact MU5| exact WM5| exact HP5| apply in_or_app; right; left; reflexivity| lia]).
    assert (FAILK : forall (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' v18 v19 v20 v21 v22 v23 t3' t4' t5' t6' : word),
      implM psegs (lib_free lops rb ;;- lib_free lops rh ;;- lib_free lops rp ;;- lib_free lops rw ;;- lib_free lops (Some ps) ;;- ret lops None) st5
        (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
        (MS (mkR ra' (wz (bv_unsigned sp + -80)) gp (wz RATP) t0' t1' t2' (wz S) (wz As) a0' a1' a2' a3' a4' a5' a6' a7' v18 v19 v20 v21 v22 v23 s8 s9 s10 s11 t3' t4' t5' t6')
            F (wz 0x16474) fc None mF (seg_rom psegs))).
    { intros. eapply (dinit_failH R ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB S As ps lo B canary ni ai ti no ao to p1 p2
                        rb rh rp rw Ab Ah Ap Aw st5 mF errv5 (wz 0) dt0 p30 adl0 resv0 (jw jks 32) (wz 0) (set_pending_buf_size (sx5 jks) 65536));
        [ exact SIF | exact LOSP | exact FRM | exact ENVF | exact PRF | exact ESO5 | exact EFA5 | exact ZS | exact GA | exact FR ]. }
    zs. destruct rw as [pw|]; cbn [oadr].
    2:{ if_true. apply evt_done. apply FAILK. }
    destruct (BUFw pw eq_refl) as ((BRw1 & BRw2 & _ & BRw3 & BRw4) & CBw). clear BUFw.
    assert (EUw : bv_unsigned (wz Aw) = Aw) by (apply unsigned_lit; lia).
    if_false.
    zs. zs. destruct rp as [pp|]; cbn [oadr].
    2:{ if_true. apply evt_done. apply FAILK. }
    destruct (BUFp pp eq_refl) as ((BRp1 & BRp2 & _ & BRp3 & BRp4) & CBp). clear BUFp.
    assert (EUp : bv_unsigned (wz Ap) = Ap) by (apply unsigned_lit; lia).
    if_false.
    zs. zs. destruct rh as [ph|]; cbn [oadr].
    2:{ if_true. apply evt_done. apply FAILK. }
    destruct (BUFh ph eq_refl) as ((BRh1 & BRh2 & _ & BRh3 & BRh4) & CBh). clear BUFh.
    assert (EUh : bv_unsigned (wz Ah) = Ah) by (apply unsigned_lit; lia).
    if_false.
    zs. destruct rb as [pb|]; cbn [oadr].
    2:{ if_true. apply evt_done. apply FAILK. }
    destruct (BUFb pb eq_refl) as ((BRb1 & BRb2 & _ & BRb3 & BRb4) & CBb). clear BUFb.
    assert (EUb : bv_unsigned (wz Ab) = Ab) by (apply unsigned_lit; lia).
    if_false.
    clear FAILK.
    do 9 zs.
    zstep. replace (le1 (wz 8)) with [Z_to_bv 8 8] by (vm_compute; reflexivity). mem_after_store.
    zs.
    do 10 zs. zs. zs. (* 1.4: + ld s8 *)
    release_frame FR STK (bv_unsigned sp).
    cbn [oadr] in GA.
    cbn [oblk app] in HP5.
    assert (SEP : apart As 5968 Aw 65536 /\ apart As 5968 Ap 65536 /\ apart As 5968 Ah 65536 /\ apart As 5968 Ab 65536
                  /\ apart Aw 65536 Ap 65536 /\ apart Aw 65536 Ah 65536 /\ apart Aw 65536 Ab 65536
                  /\ apart Ap 65536 Ah 65536 /\ apart Ap 65536 Ab 65536 /\ apart Ah 65536 Ab 65536).
    { unfold apart.
      pose proof (fun b1 b2 (I1 : In b1 [(pb, Ab, 65536)]) I2 => heap_sep st5 [(pb, Ab, 65536)] _ mP5 b1 b2 HND HBD HP5 I1 I2) as X1.
      pose proof (fun b1 b2 (I1 : In b1 [(pb, Ab, 65536); (ph, Ah, 65536)]) I2 => heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536)] _ mP5 b1 b2 HND HBD HP5 I1 I2) as X2.
      pose proof (fun b1 b2 (I1 : In b1 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536)]) I2 =>
                    heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536)] _ mP5 b1 b2 HND HBD HP5 I1 I2) as X3.
      pose proof (fun b1 b2 (I1 : In b1 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536)]) I2 =>
                    heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536)] _ mP5 b1 b2 HND HBD HP5 I1 I2) as X4.
      pose proof (X1 _ (ph, Ah, 65536) (or_introl eq_refl) (or_introl eq_refl)) as Y1.
      pose proof (X1 _ (pp, Ap, 65536) (or_introl eq_refl) (or_intror (or_introl eq_refl))) as Y2.
      pose proof (X1 _ (pw, Aw, 65536) (or_introl eq_refl) (or_intror (or_intror (or_introl eq_refl)))) as Y3.
      pose proof (X1 _ (ps, As, 5968) (or_introl eq_refl) (or_intror (or_intror (or_intror (or_introl eq_refl))))) as Y4.
      pose proof (X2 (ph, Ah, 65536) (pp, Ap, 65536) (or_intror (or_introl eq_refl)) (or_introl eq_refl)) as Y5.
      pose proof (X2 (ph, Ah, 65536) (pw, Aw, 65536) (or_intror (or_introl eq_refl)) (or_intror (or_introl eq_refl))) as Y6.
      pose proof (X2 (ph, Ah, 65536) (ps, As, 5968) (or_intror (or_introl eq_refl)) (or_intror (or_intror (or_introl eq_refl)))) as Y7.
      pose proof (X3 (pp, Ap, 65536) (pw, Aw, 65536) (or_intror (or_intror (or_introl eq_refl))) (or_introl eq_refl)) as Y8.
      pose proof (X3 (pp, Ap, 65536) (ps, As, 5968) (or_intror (or_intror (or_introl eq_refl))) (or_intror (or_introl eq_refl))) as Y9.
      pose proof (X4 (pw, Aw, 65536) (ps, As, 5968) (or_intror (or_intror (or_intror (or_introl eq_refl)))) (or_introl eq_refl)) as Y10.
      cbn [blk_addr blk_size fst snd] in Y1, Y2, Y3, Y4, Y5, Y6, Y7, Y8, Y9, Y10. clear - Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10. lia. }
    destruct SEP as (Qsw & Qsp & Qsh & Qsb & Qwp & Qwh & Qwb & Qph & Qpb & Qhb).
    assert (LAY : dlay_ok (Z_drep.mkDL S As Aw Ap Ah Ab 0 0)).
    { constructor; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab].
      - unfold blk_ok. clear - BRs1 BRs2 BRs3 BRs4. lia.
      - unfold blk_ok. clear - BRw1 BRw2 BRw3 BRw4. lia.
      - unfold blk_ok. clear - BRp1 BRp2 BRp3 BRp4. lia.
      - unfold blk_ok. clear - BRh1 BRh2 BRh3 BRh4. lia.
      - unfold blk_ok. clear - BRb1 BRb2 BRb3 BRb4. lia.
      - clear - SIF' B63 RSP LOSP' CEIL. lia.
      - exact Qsw. - exact Qsp. - exact Qsh. - exact Qsb. - exact Qwp. - exact Qwh. - exact Qwb. - exact Qph. - exact Qpb. - exact Qhb.
      - unfold apart. clear - SIF' LOSP' CEIL BRs3. lia.
      - unfold apart. clear - SIF' LOSP' CEIL BRw3. lia.
      - unfold apart. clear - SIF' LOSP' CEIL BRp3. lia.
      - unfold apart. clear - SIF' LOSP' CEIL BRh3. lia.
      - unfold apart. clear - SIF' LOSP' CEIL BRb3. lia. }
    remember (Z_drep.mkDL S As Aw Ap Ah Ab 0 0) as L eqn:EL.
    assert (ENVJ : lx_env m0 st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)] LB
                          (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv5 canary).
    { eapply (dinit_env_munchH mP5 m0); [exact ENV5| unfold WI; exact MU5| exact WM5| exact MIF| exact INs| rewrite E80; lia| lia| lia| lia]. }
    assert (PRJ : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m0).
    { eapply (dinit_pres_munchH LB _ m mP5 m0 st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)]);
        [exact PR5| unfold WI; exact MU5| exact WM5| exact HP5| right; right; right; right; left; reflexivity| lia]. }
    pose proof ENVJ as (_ & _ & ZLSJ & _). pose proof (relro_clean_of_zl _ ZLSJ) as RCJ.
    assert (AGJ : agree_on (As + 212) (As + 5881) m1 m0)
      by (eapply (dinit_ags_munch m1 mP5 m0 S As); [exact AGs5| unfold WI; exact MU5| exact WM5| lia| lia| lia]).
    assert (AGw : agree_on Aw (Aw + 65536) mP2 m0).
    { eapply agree_on_trans; [exact (BKw pw eq_refl)|]. apply (agree_on_of_munch _ _ _ _ _ MU5 WM5); [lia| lia|]. cbn [disjoint_from]. clear - Qsw SIF' LOSP' CEIL BRw3 RSP. unfold apart in Qsw. lia. }
    assert (AGp : agree_on Ap (Ap + 65536) mP3 m0).
    { eapply agree_on_trans; [exact (BKp pp eq_refl)|]. apply (agree_on_of_munch _ _ _ _ _ MU5 WM5); [lia| lia|]. cbn [disjoint_from]. clear - Qsp SIF' LOSP' CEIL BRp3 RSP. unfold apart in Qsp. lia. }
    assert (AGh : agree_on Ah (Ah + 65536) mP4 m0).
    { eapply agree_on_trans; [exact (BKh ph eq_refl)|]. apply (agree_on_of_munch _ _ _ _ _ MU5 WM5); [lia| lia|]. cbn [disjoint_from]. clear - Qsh SIF' LOSP' CEIL BRh3 RSP. unfold apart in Qsh. lia. }
    assert (AGb : agree_on Ab (Ab + 65536) mP5 m0).
    { apply (agree_on_of_munch _ _ _ _ _ MU5 WM5); [lia| lia|]. cbn [disjoint_from]. clear - Qsb SIF' LOSP' CEIL BRb3 RSP. unfold apart in Qsb. lia. }
    remember (init_u64 (orc jks) 32 0 - Ab) as po eqn:Epo.
    assert (ST : DSTi m0 L (spre (G5 jks jkw jkp jkh jkb) po)).
    { pose proof (recast_Bi m1 As jks 0%N dinit_cs CBs) as GB. pose proof (recast_C m1 As jks 0%N dinit_cs CBs) as GC.
      pose proof (recast_lt m1 As jks 0%N dinit_cs CBs) as Glt. pose proof (recast_dt m1 As jks 0%N dinit_cs CBs) as Gdt.
      pose proof (recast_bt m1 As jks 0%N dinit_cs CBs) as Gbt. pose proof (recast_blc m1 As jks 0%N dinit_cs CBs) as Gblc.
      pose proof (recast_heap m1 As jks 0%N dinit_cs CBs) as Gheap. pose proof (recast_dep m1 As jks 0%N dinit_cs CBs) as Gdep.
      change (Z.to_nat 65536) with (Z.to_nat (2 * 32768)) in CBp, CBh.
      pose proof (recast_bytes mP2 Aw jkw 65536 CBw ltac:(lia)) as Gwin. pose proof (recast_ush mP3 Ap jkp 32768 CBp ltac:(lia)) as Gprev.
      pose proof (recast_ush mP4 Ah jkh 32768 CBh ltac:(lia)) as Ghead. pose proof (recast_bytes mP5 Ab jkb 65536 CBb ltac:(lia)) as Gpend.
      unfold jw in GA. subst L. constructor.
      - abstract (do 5 eexists; rewrite spre_A_cells; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab G5]; close_cells GA).
      - abstract (do 9 eexists; rewrite spre_Bi_cells; unfold s_raw; cbn [dl_As G5]; eapply (Z_dview.rw_cells_agree m1 m0); [exact GB| lazymatch goal with |- agree_on _ (_ + Z.of_nat ?n) _ _ => replace (Z.of_nat n) with 72 by reflexivity end; eapply agree_on_sub; [exact AGJ| lia| lia]]).
      - abstract (unfold dsC; rewrite spre_C_cells; unfold s_raw; cbn [dl_As G5]; eapply (Z_dview.rw_cells_agree m1 m0); [exact GC| lazymatch goal with |- agree_on _ (_ + Z.of_nat ?n) _ _ => replace (Z.of_nat n) with 8 by reflexivity end; eapply agree_on_sub; [exact AGJ| lia| lia]]).
      - abstract (do 5 eexists; rewrite spre_D_cells; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab G5]; close_cells GD).
      - abstract (apply spre_lt; unfold s_raw; cbn [G5]; apply (dlt_agree m1 m0 _ _ Glt); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre_dt; unfold s_raw; cbn [G5]; apply (ddt_agree m1 m0 _ _ Gdt); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre_bt; unfold s_raw; cbn [G5]; apply (dbt_agree m1 m0 _ _ Gbt); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre_blc; unfold s_raw; cbn [G5]; apply (dblc_agree m1 m0 _ _ Gblc); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre_heap; unfold s_raw; cbn [G5]; apply (dheap_agree m1 m0 _ _ Gheap); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre_dep; unfold s_raw; cbn [G5]; apply (ddep_agree m1 m0 _ _ Gdep); cbn [dl_As]; eapply agree_on_sub; [exact AGJ| lia| lia]).
      - abstract (apply spre_win; cbn [dl_Aw G5]; eapply (Z_dview.u8arr_agree mP2 m0); [exact Gwin| rewrite av8_length; change (Z.of_nat (Z.to_nat 65536)) with 65536; exact AGw]).
      - abstract (apply spre_prev; cbn [dl_Ap G5]; eapply (Z_dview.u16arr_agree mP3 m0); [exact Gprev| rewrite av16_length; change (2 * Z.of_nat (Z.to_nat 32768)) with 65536; exact AGp]).
      - abstract (apply spre_head; cbn [dl_Ah G5]; eapply (Z_dview.u16arr_agree mP4 m0); [exact Ghead| rewrite av16_length; change (2 * Z.of_nat (Z.to_nat 32768)) with 65536; exact AGh]).
      - abstract (apply spre_pend; cbn [dl_Ab G5]; eapply (Z_dview.u8arr_agree mP5 m0); [exact Gpend| rewrite av8_length; change (Z.of_nat (Z.to_nat 65536)) with 65536; exact AGb]).
      - exact (spre_lens _ _).
      - exact LAY. }
    destruct (spre_facts (G5 jks jkw jkp jkh jkb) po) as (Fchk & Fwrap & Flev & Fws & Fhs).
    eapply evt_mono.
    { eapply (deflateReset_spec HTRI L (spre (G5 jks jkw jkp jkh jkb) po) ni ai ti no ao to p1 p2 (wz 0) (wz 0) dt0 p30 adl0 resv0 lo).
      - exact ST.
      - subst L. unfold zs_raw, zs_pub. cbn [app dl_S dl_As]. exact ZS.
      - exact RCJ.
      - exact Fchk.
      - rewrite Fwrap. lia.
      - exact Flev. - exact Fws. - exact Fhs. - reflexivity. (* 1.4: ds_gzhead = 0 for deflateResetKeep *)
      - exact STK.
      - subst L. unfold dlay_below. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab]. clear - SIF' LOSP' CEIL GLO' BRs3 BRw3 BRp3 BRh3 BRb3. lia.
      - unfold Z_DRESET_STACK. clear - LOSP'. lia.
      - exact MIF.
      - subst L. reflexivity. }
    intros ms' POST. cbv beta.
    destruct POST as (u0 & u1 & u2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM' & MI' & STK' & EA0 & ZS' & ST').
    rewrite dinit_state_eq in ST'.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm st5 (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
    cbn [ret lops Target.ops]. apply implM_ret. apply evt_done.
    unfold deflateInit_post. do 15 eexists. exists F, fc, m'.
    split; [reflexivity|]. cbv beta iota.
    exists As, Aw, Ap, Ah, Ab.
    subst L. cbn [dl_S dl_As dl_Ah] in MU'. cbn [dl_S dl_As] in ZS'.
    assert (LBR : forall bx, In bx LB -> blk_addr bx + blk_size bx <= lo
                                    /\ (blk_addr bx + blk_size bx <= As \/ As + 5968 <= blk_addr bx) /\ (blk_addr bx + blk_size bx <= Ah \/ Ah + 65536 <= blk_addr bx)).
    { intros bx Hb. pose proof (HBR _ _ _ bx HP5 ltac:(do 5 right; exact Hb)) as (_ & _ & _ & X1 & _).
      pose proof (heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)] LB mP5 (ps, As, 5968) bx HND HBD HP5
                    ltac:(do 4 right; left; reflexivity) Hb) as X2.
      pose proof (heap_sep st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)] LB mP5 (ph, Ah, 65536) bx HND HBD HP5
                    ltac:(right; left; reflexivity) Hb) as X3.
      cbn [blk_addr blk_size fst snd] in X2, X3. clear - X1 X2 X3 CEIL. lia. }
    assert (ENVE : lx_env m' st5 [(pb, Ab, 65536); (ph, Ah, 65536); (pp, Ap, 65536); (pw, Aw, 65536); (ps, As, 5968)] LB sp (wz RATP) B lo errv5 canary).
    { eapply (lx_env_munch _ m0 m'); [exact HFRAME| exact ENVJ| exact MU'| exact WM'| exact MI'| exact STK'| clear - SIF'; lia| |].
      - constructor; [left; cbn [fst]; clear - CEIL; lia|].
        constructor; [left; cbn [fst]; clear - CEIL SIF' LOSP'; lia|].
        constructor; [right; right; exists (ps, As, 5968); split; [do 4 right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]|].
        constructor; [right; right; exists (ph, Ah, 65536); split; [right; left; reflexivity| cbn [blk_addr blk_size fst snd]; lia]| constructor].
      - intros a Ha. cbn [outside fst snd]. clear - Ha SIF' LOSP' CEIL GLO' BRs3 BRh3 BRs4 BRh4 B63 RSP.
        split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]. }
    split.
    { unfold lx_post_env. split; [exists errv5; exact ENVE|]. split; [exact FRM|]. split; [| split; [exact ESO5| exact EFA5]].
      eapply lx_pres_trans; [exact PRJ|]. eapply lx_pres_of_munch; [exact MU'| exact WM'|].
      intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; unfold ZS_SIZEOF in NX; cbn [outside fst snd].
      - clear - NX Ha SIF' LOSP' CEIL BRs3 BRh3. split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]].
      - destruct (LBR bx Hb) as (Y1 & Y2 & Y3). clear - NX Hr Y1 Y2 Y3 SIF' LOSP' CEIL. split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]].
      - clear - NX Ha GLO' SIF' LOSP' CEIL BRs4 BRh4. split; [lia| split; [lia| split; [lia| split; [lia| exact I]]]]. }
    split; [rewrite EA0; unfold wint, ZApi.Z_OK, MallocRep.wz; apply bv_eq; reflexivity|].
    unfold zs_raw in ZS'. apply Startup_glue.rw_cells_app in ZS'. destruct ZS' as [ZP ZQ].
    split; [exact ZP|].
    rewrite RD.
    change (zr_d m' (dl_S (Z_drep.mkDL S As Aw Ap Ah Ab 0 0)) (zd_blocks (ps, pw, pp, ph, pb) (Z_drep.mkDL S As Aw Ap Ah Ab 0 0)) zd_init).
    apply (zr_d_intro m' _ (dinit_of (G5 jks jkw jkp jkh jkb)) _ zd_init).
    - split; [| exact ST']. destruct dz_init_scalars as (Em & Edt & Ead & _). unfold dzq. rewrite Em, Edt, Ead. exists p30, resv0.
      unfold zs_priv_cells. cbn [dl_S dl_As].
      lazymatch type of ZQ with rw_cells _ _ (_ + Z.of_nat ?n) _ => replace (Z.of_nat n) with 48 in ZQ by reflexivity end.
      close_cells ZQ.
    - apply DREL_init.
    - apply PAT_init.
    - unfold dlay_ceil. cbn [dl_As dl_Aw dl_Ap dl_Ah dl_Ab]. clear - BRs3 BRw3 BRp3 BRh3 BRb3. lia.
    - exact (proj2 (proj2 (proj2 HI_init))).
  Qed.
End DINIT_TAIL.
End WithCeiling0.
End Z_dinit_tail.

Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_tac.Layout OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Exit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Startup_glue OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_fwritex.Printf_lib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_stdio_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zlib_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Driver_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Drv_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Zh_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dview OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_drep OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dkit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Printf_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_zrd OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_trees_iface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dend OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit_kit OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit_model OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dreset OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dendk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dinit_pieces OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Z_dinit.Z_dinit_tail.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZProg ZIface DeflateState Deflate RefDeflateInitLib.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeI6.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require HarnessSmall ZApiInst DeflateTaintRel ZTaint BoundPat ZPat FillWinModel.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZProg OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflateInitLib OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeI6.RefDeflSafeI5b OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.HarnessSmall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateTaintRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZTaint OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BoundPat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZPat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.FillWinModel.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require F_memset Str_memset.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Notation psegs := Image.psegs.
Notation mem := (word -> option byte).
Local Notation wz := (Z_to_bv 64).
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Local Notation MP := (OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec.Monad.M PState).
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Section DINIT.
  Hypothesis MALLOC : rmalloc_stmt.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HTRI : tr_init_stmt.
  Local Notation dinit_zallocH := (dinit_zalloc MALLOC).
  Local Notation dinit_env_munchH := (dinit_env_munch HBR HFRAME).
  Local Notation dinit_pres_munchH := (dinit_pres_munch HND HBR HBD).
  Local Notation dinit_env_munchZH := (dinit_env_munchZ HBR HFRAME).
  Local Notation dinit_pres_munchZH := (dinit_pres_munchZ HND HBR HBD).
  Local Notation buf_inH := (buf_in HBR).
  Local Notation buf_disjH := (buf_disj HND HBR HBD).

  Local Transparent the_zapi.

  Theorem deflateInit_proof : forall R : zreps, Zlib_iface.zr_d R = Z_zrd.zr_d -> deflateInit_stmt R.
  Proof.
    intros R RD. unfold deflateInit_stmt. intros until canary. intros ENV ZS SIF LOSP SP16 FRM -> -> -> ->.
    pose proof ENV as (HP & _ & ZLS & _ & _ & AUX & SPB & B63 & STK & CEIL & GLO & ERRC & TP & MI). cbn [app] in HP.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    subst tp. unfold errno_addr in ERRC.
    unfold Z_DEFLATEINIT_STACK, RMALLOC_STACK in LOSP. unfold strm_in_frame, ZS_SIZEOF in SIF.
    assert (LBR : forall bx, In bx LB -> blk_addr bx + blk_size bx <= lo).
    { intros bx Hb. pose proof (HBR _ _ _ bx HP Hb) as (_ & _ & _ & X1 & _). lia. }
    pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
    pose proof (got_zalloc_relro _ (relro_clean_of_zl _ ZLS)) as GOT.
    assert (EUS : bv_unsigned (wz S) = S) by (apply unsigned_lit; lia).
    assert (E80 : bv_unsigned (wz (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; lia).
    unfold zs_pub in ZS. cbn [app] in ZS.
    destruct (zs_tail_recast m S [C8 (Zlib_iface.wz ni); C4 (Zlib_iface.wz ai); CB 4 p1; C8 (Zlib_iface.wz ti); C8 (Zlib_iface.wz no); C4 (Zlib_iface.wz ao); CB 4 p2;
                                  C8 (Zlib_iface.wz to); C8 jmsg; C8 jstate; C8 (Zlib_iface.wz 0); C8 (Zlib_iface.wz 0); C8 (Zlib_iface.wz 0)] jrest ZS) as (dt0 & p30 & adl0 & resv0 & ZS').
    clear ZS. rename ZS' into ZS. cbn [app] in ZS.
    pose proof (munch_refl [(lo, bv_unsigned sp); (S, S + 112)] m) as MU. pose proof (wmono_refl psegs m) as WM.
    cbv [deflate_init z_dstate z_dwin z_dprev z_dhead z_dpend the_zapi zinst].
    unfold implM. iprefix. unfold Z_DEFLATEINIT_, A_ZVERSION, ZS_SIZEOF, wint, MallocRep.wz in *.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    carve_frame 80%nat STK.
    do 11 zstep. (* 1.4: + sd s8,0(sp) *)
    zstep. zstep. zstep. if_false.
    zstep. zstep. if_false.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let bs := eval vm_compute in (option.default [] (image_bytes psegs 0x10402 1)) in
      assert (VER : ro_cells psegs mm 0x10402 [CB (length bs) bs])
        by (apply ro_cells_image; [assumption| vm_compute; reflexivity| lia| cbn; lia]) end.
    cbn [length] in VER.
    zstep. zstep. zstep. if_false.
    zstep. zstep. if_false.
    zs. zs. zs. if_true.
    zs. zs. zs. zs. zs. zs. if_false.
    zs. zs. zs. zs. zs. if_false.
    zs. zs. if_true. zs. zs. if_true. zs. zs. zs. zs. if_false. zs. zs. if_false. zs. zs. if_false.
    zs. zs. zs. if_false. zs. zs. zs. if_false. zs. zs. zs. zs. if_false.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    clear GOT VER.
    (* 1.4: one more frame store (s8) shifts the stepper's memory names; name the current memory m0 as in 1.3.1 *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m0 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ENV0 : lx_env mm s [] LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv canary) end.
    { eapply (lx_env_munch [(lo, bv_unsigned sp); (S, S + 112)] m _); [exact HFRAME| exact ENV| exact MU| exact WM| eassumption| rewrite E80; exact STK| rewrite E80; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor; [left; cbn [fst]; lia| constructor]].
      - intros a Ha. cbn [outside fst snd]. split; [lia| split; [lia| exact I]]. }
    assert (PR0 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m0).
    { eapply lx_pres_of_munch; [exact MU| exact WM|].
      intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; cbn [outside fst snd]; (split; [|split; [|exact I]]); try lia.
      specialize (LBR bx Hb). lia. }
    pose proof ENV0 as (HP0 & _ & _ & _ & _ & AUX0 & SPB0 & _ & STK0 & _ & _ & ERR0 & _ & MI0). cbn [app] in HP0. rewrite E80 in STK0, SPB0. unfold errno_addr in ERR0.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
    eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m0 s LB 1 5968 5968 lo B errv);
      [ exact HP0 | exact AUX0 | rewrite E80; exact SPB0 | rewrite E80; exact STK0 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR0 | exact MI0
      | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
    intros r1 st1 u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6 m1 errv1 MI1 ST1 ERR1 AUX1 HPR1 EFA1 ESO1 RES1.
    rewrite E80 in ST1, HPR1.
    replace (ret_pc (wz 90856)) with (wz 90856) by (symmetry; rpc).
    assert (PR1 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m m1).
    { eapply lx_pres_trans; [exact PR0|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR1| lia| intros bx Hb; exact Hb]. }
    pose proof (Drv_kit.rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ (lx_pres_of_heap_pres _ _ [] _ _ HPR1)) ZS
                  ltac:(intros a Ha; cbn in Ha; apply stack_client; [lia| cbn [rin_ivs]; tauto])) as ZS1.
    pose proof (Drv_kit.rw_cells_agree _ _ _ _ _ (agree_of_lx_pres _ _ _ _ _ (lx_pres_of_heap_pres _ _ [] _ _ HPR1)) FR
                  ltac:(intros a Ha; cbn in Ha; apply stack_client; [lia| cbn [rin_ivs]; tauto])) as FR1.
    clear ZS FR.
    destruct r1 as [ps|].
    -
      destruct RES1 as (As & jks & -> & BRs & HP1 & CBs).
      pose proof (box _ CBs) as CBX. pose proof (box _ BRs) as BRX.
      destruct BRs as (BRs1 & BRs2 & _ & BRs3 & BRs4).
      assert (EUs : bv_unsigned (wz As) = As) by (apply unsigned_lit; lia).
      assert (ENV1 : lx_env m1 st1 [(ps, As, 5968)] LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv1 canary).
      { eapply (lx_env_heap m0 m1 s st1); [exact ENV0| rewrite E80; exact HPR1| exact HP1| exact MI1| rewrite E80; exact ST1| exact ERR1| exact AUX1]. }
      (* 1.4: deflateInit2_ calls memset(s + 8, 0, 5960) right after the zalloc, before any store into the state; the
         recast then starts from the block's first 8 junk bytes followed by zeros (jkz). *)
      pose proof (recast_lenZ m1 As jks CBs) as LJ.
      assert (CBs' : rw_cells psegs m1 As [CB (length jks) jks]) by (rewrite (recast_len m1 As jks CBs); exact CBs).
      pose proof (cb_subZ m1 As jks 8 5960 CBs' ltac:(lia) ltac:(lia) ltac:(lia)) as C8r.
      pose proof (cb_subZ m1 As jks 0 8 CBs' ltac:(lia) ltac:(lia) ltac:(lia)) as C8l. rewrite Z.add_0_r in C8l.
      remember (sub jks (Z.to_nat 0) (Z.to_nat 8) ++ repeat (Z_to_bv 8 0) (Z.to_nat 5960)) as jkz eqn:Ejkz.
      assert (HZz : forall k, 8 <= Z.of_nat k < 5968 -> nth k jkz (Z_to_bv 8 0) = Z_to_bv 8 0).
      { intros k Hk. subst jkz. rewrite app_nth2.
        - apply nth_repeat.
        - rewrite sub_length; [lia| rewrite (recast_len m1 As jks CBs); lia]. }
      clear CBs' CBX CBs.
      unfold implM. iprefix.
      zs. zs. zs. if_false.
      zs. zs. zs. zs. zs. if_true.
      zs. zs. zs. zs. zs.
      lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
        eapply evt_cut; [eapply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset.memset_callZ with (D := As + 8) (C := 0) (N := 5960); [exact C8r| eassumption| lia| lia| lia| lia] |] end.
      intros msz POSTZ. unfold OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.F_memset.memset_postZ in POSTZ. destruct_exs POSTZ.
      destruct POSTZ as (Ez & MUz & WMz & MIz & CBzr). subst msz.
      lazymatch type of MUz with munch _ _ ?mm => rename mm into mz end.
      clear C8r.
      transport_after_call psegs m1 mz MUz WMz.
      try (replace (ret_pc (wz 90912)) with (wz 90912) by (symmetry; rpc)).
      change (0 mod 256) with 0 in CBzr.
      assert (CBz : rw_cells psegs mz As [CB (Z.to_nat 5968) jkz]).
      { assert (J : rw_cells psegs mz As ([CB (Z.to_nat 8) (sub jks (Z.to_nat 0) (Z.to_nat 8))] ++ [CB (Z.to_nat 5960) (repeat (Z_to_bv 8 0) (Z.to_nat 5960))])).
        { apply OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P.Str_memset.Str_cpy.rw_cells_app. split; [exact C8l|]. cbn [cells_size csize].
          replace (As + Z.of_nat (Z.to_nat 8 + 0)) with (As + 8) by lia. exact CBzr. }
        subst jkz. eapply Zh_kit.rw_cells_recast; [exact J| |].
        - cbn [cells_wf cell_wf app]. split; [|exact I].
          rewrite length_app, repeat_length, sub_length; lia.
        - cbn [cells_bytes cbytes app]. rewrite !app_nil_r. reflexivity. }
      pose proof (box _ CBz) as CBXz. clear C8l CBzr.
      assert (MUz' : munch (WZ As) m1 mz) by (unfold WZ; replace (As + 5968) with (As + 8 + 5960) by lia; exact MUz).
      assert (ENV1z : lx_env mz st1 [(ps, As, 5968)] LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv1 canary)
        by (eapply (dinit_env_munchZH m1 mz); [exact ENV1| exact MUz'| exact WMz| exact MIz| left; reflexivity| lia| lia]).
      assert (PR1z : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mz).
      { destruct ENV1 as (HPx & _).
        eapply (dinit_pres_munchZH LB _ m m1 mz st1 [(ps, As, 5968)]); [exact PR1| exact MUz'| exact WMz| exact HPx| left; reflexivity| lia]. }
      clear MUz MUz' WMz.
      pose proof (recast_A mz As jkz 0%N dinit_cs CBz) as GA.
      pose proof (recast_D mz As jkz 0%N dinit_cs CBz HZz) as GD.
      pose proof (box _ (recast_Bi mz As jkz 0%N dinit_cs CBz)) as RBi. pose proof (box _ (recast_C mz As jkz 0%N dinit_cs CBz)) as RC.
      pose proof (recast_lt mz As jkz 0%N dinit_cs CBz) as Rlt. pose proof (recast_dt mz As jkz 0%N dinit_cs CBz) as Rdt.
      pose proof (recast_bt mz As jkz 0%N dinit_cs CBz) as Rbt. pose proof (recast_blc mz As jkz 0%N dinit_cs CBz) as Rblc.
      pose proof (recast_heap mz As jkz 0%N dinit_cs CBz) as Rheap. pose proof (recast_dep mz As jkz 0%N dinit_cs CBz) as Rdep.
      clear CBz.
      unfold dsA_raw in GA. unfold dsD_raw in GD.
      cbn [ds_of_oracle ds_status ds_pending_buf_size ds_pending ds_wrap ds_gzindex ds_method ds_last_flush ds_w_size ds_w_bits ds_w_mask
           ds_window_size ds_ins_h ds_hash_size ds_hash_bits ds_hash_mask ds_hash_shift ds_block_start ds_match_length ds_prev_match ds_match_available
           ds_strstart ds_match_start ds_lookahead ds_prev_length ds_max_chain_length ds_max_lazy_match ds_level ds_strategy ds_good_match ds_nice_match
           ds_lit_bufsize ds_sym_next ds_sym_end ds_opt_len ds_static_len ds_matches ds_insert ds_bi_buf ds_bi_valid ds_high_water] in GA, GD.
      pose proof (agree_on_refl (As + 212) (As + 5881) mz) as AGs.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mz) as MU1. pose proof (wmono_refl psegs mz) as WM1.
      do 28 zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE2 end.
      assert (ENV2 : lx_env mE2 st1 ([(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv1 canary)
        by (eapply (dinit_env_munchH mz mE2); [exact ENV1z| exact MU1| exact WM1| eassumption| left; reflexivity| rewrite E80; lia| lia| lia| lia]).
      assert (HPe2 : RHEAP st1 (([(ps, As, 5968)]) ++ LB) mz) by (destruct ENV1z as (HPx & _); exact HPx).
      assert (PR2 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mE2)
        by (eapply (dinit_pres_munchH LB _ m mz mE2 st1 ([(ps, As, 5968)])); [exact PR1z| exact MU1| exact WM1| exact HPe2| left; reflexivity| lia]).
      assert (AGs2 : agree_on (As + 212) (As + 5881) mz mE2)
        by (eapply (dinit_ags_munch mz mz mE2 S As); [exact AGs| exact MU1| exact WM1| lia| lia| lia]).
      pose proof ENV2 as (HPx2 & _ & _ & _ & _ & AUX2 & SPB2 & _ & STK2 & _ & _ & ERR2 & _ & MI2). rewrite E80 in STK2, SPB2. unfold errno_addr in ERR2.
      assert (HPc2 : RHEAP st1 ((ps, As, 5968) :: LB) mE2) by (exact HPx2).
      assert (INs2 : In (ps, As, 5968) ((ps, As, 5968) :: LB)) by (left; reflexivity).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
        change (implM psegs tm st1 (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
      eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mE2 st1 ((ps, As, 5968) :: LB) 32768 2 65536 lo B errv1);
        [ exact HPc2 | exact AUX2 | rewrite E80; exact SPB2 | rewrite E80; exact STK2 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR2 | exact MI2
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      intros rw st2 v20 v21 v22 d20 d21 d22 d23 d24 d25 d26 d27 v23 v24 v25 v26 mP2 errv2 MIp2 STp2 ERRp2 AUXp2 HPR2 EFA2 ESO2 RES2.
      rewrite E80 in STp2, HPR2.
      destruct (zalloc_res _ _ _ _ _ _ RES2) as (Aw & jkw & -> & HPp2 & BUFrw). clear RES2.
      assert (HPc2p : RHEAP st2 ((oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mP2) by exact HPp2.
      replace (ret_pc (wz 91024)) with (wz 91024) by (symmetry; rpc).
      assert (ENV2p : lx_env mP2 st2 ((oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv2 canary).
      { eapply (lx_env_heap mE2 mP2 st1 st2); [exact ENV2| rewrite E80; eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]
          | rewrite <- app_assoc; cbn [app]; exact HPc2p| exact MIp2| rewrite E80; exact STp2| exact ERRp2| exact AUXp2]. }
      assert (PR2p : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP2).
      { eapply lx_pres_trans; [exact PR2|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR2| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]. }
      assert (AGs2p : agree_on (As + 212) (As + 5881) mz mP2).
      { eapply agree_on_trans; [exact AGs2|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR2); [lia| lia|].
        intros a Ha. right; right. exists (ps, As, 5968). split; [exact INs2| cbn [blk_addr blk_size fst snd]; lia]. }
      pose proof (BK_refl rw Aw mP2) as BKrw2p.
      assert (ESOs2 : ps_so st2 = ps_so s) by (rewrite ESO2; exact ESO1).
      assert (EFAs2 : ps_fa st2 = ps_fa s) by (rewrite EFA2; exact EFA1).
      tr_blk HPR2 GA GA2 (ps, As, 5968) INs2. tr_blk HPR2 GD GD2 (ps, As, 5968) INs2. tr_up HPR2 ZS1 ZS2. tr_up HPR2 FR1 FR2.
      clear GA GD ZS1 FR1.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mP2) as MU2. pose proof (wmono_refl psegs mP2) as WM2.
      unfold implM. iprefix.
      do 7 zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE3 end.
      assert (ENV3 : lx_env mE3 st2 ((oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv2 canary)
        by (eapply (dinit_env_munchH mP2 mE3); [exact ENV2p| exact MU2| exact WM2| eassumption| apply in_or_app; left; apply in_or_app; right; left; reflexivity| rewrite E80; lia| lia| lia| lia]).
      assert (HPe3 : RHEAP st2 (((oblk rw Aw 65536) ++ [(ps, As, 5968)]) ++ LB) mP2) by (destruct ENV2p as (HPx & _); exact HPx).
      assert (PR3 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mE3)
        by (eapply (dinit_pres_munchH LB _ m mP2 mE3 st2 ((oblk rw Aw 65536) ++ [(ps, As, 5968)])); [exact PR2p| exact MU2| exact WM2| exact HPe3| apply in_or_app; right; left; reflexivity| lia]).
      assert (AGs3 : agree_on (As + 212) (As + 5881) mz mE3)
        by (eapply (dinit_ags_munch mz mP2 mE3 S As); [exact AGs2p| exact MU2| exact WM2| lia| lia| lia]).
      assert (BKrw3 : BK rw Aw _ mE3)
        by (eapply BK_munch; [exact BKrw2p| exact MU2| exact WM2| intros q E; eapply (buf_disjH st2 (oblk rw Aw 65536) LB mP2 q Aw S As ps lo); [exact HPc2p| in_ow E| lia| exact CEIL]]).
      pose proof ENV3 as (HPx3 & _ & _ & _ & _ & AUX3 & SPB3 & _ & STK3 & _ & _ & ERR3 & _ & MI3). rewrite E80 in STK3, SPB3. unfold errno_addr in ERR3.
      assert (HPc3 : RHEAP st2 ((oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mE3) by (rewrite <- app_assoc in HPx3; cbn [app] in HPx3; exact HPx3).
      assert (INs3 : In (ps, As, 5968) ((oblk rw Aw 65536) ++ (ps, As, 5968) :: LB)) by (apply in_or_app; right; left; reflexivity).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
        change (implM psegs tm st2 (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
      eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mE3 st2 ((oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) 32768 2 65536 lo B errv2);
        [ exact HPc3 | exact AUX3 | rewrite E80; exact SPB3 | rewrite E80; exact STK3 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR3 | exact MI3
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      intros rp st3 v30 v31 v32 d30 d31 d32 d33 d34 d35 d36 d37 v33 v34 v35 v36 mP3 errv3 MIp3 STp3 ERRp3 AUXp3 HPR3 EFA3 ESO3 RES3.
      rewrite E80 in STp3, HPR3.
      destruct (zalloc_res _ _ _ _ _ _ RES3) as (Ap & jkp & -> & HPp3 & BUFrp). clear RES3.
      rewrite app_assoc in HPp3.
      assert (HPc3p : RHEAP st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mP3) by exact HPp3.
      replace (ret_pc (wz 91052)) with (wz 91052) by (symmetry; rpc).
      assert (ENV3p : lx_env mP3 st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv3 canary).
      { eapply (lx_env_heap mE3 mP3 st2 st3); [exact ENV3| rewrite E80; eapply rheap_pres_weaken; [exact HPR3| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]
          | rewrite <- app_assoc; cbn [app]; exact HPc3p| exact MIp3| rewrite E80; exact STp3| exact ERRp3| exact AUXp3]. }
      assert (PR3p : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP3).
      { eapply lx_pres_trans; [exact PR3|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR3| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]. }
      assert (AGs3p : agree_on (As + 212) (As + 5881) mz mP3).
      { eapply agree_on_trans; [exact AGs3|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR3); [lia| lia|].
        intros a Ha. right; right. exists (ps, As, 5968). split; [exact INs3| cbn [blk_addr blk_size fst snd]; lia]. }
      assert (BKrw3p : BK rw Aw _ mP3) by (eapply BK_hpres; [exact BKrw3| exact HPR3| intros q E; eapply buf_inH; [exact HPc3| in_ow E]]).
      pose proof (BK_refl rp Ap mP3) as BKrp3p.
      assert (ESOs3 : ps_so st3 = ps_so s) by (rewrite ESO3; exact ESOs2).
      assert (EFAs3 : ps_fa st3 = ps_fa s) by (rewrite EFA3; exact EFAs2).
      tr_blk HPR3 GA2 GA3 (ps, As, 5968) INs3. tr_blk HPR3 GD2 GD3 (ps, As, 5968) INs3. tr_up HPR3 ZS2 ZS3. tr_up HPR3 FR2 FR3.
      clear GA2 GD2 ZS2 FR2.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mP3) as MU3. pose proof (wmono_refl psegs mP3) as WM3.
      unfold implM. iprefix.
      do 7 zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE4 end.
      assert (ENV4 : lx_env mE4 st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv3 canary)
        by (eapply (dinit_env_munchH mP3 mE4); [exact ENV3p| exact MU3| exact WM3| eassumption| apply in_or_app; left; apply in_or_app; right; left; reflexivity| rewrite E80; lia| lia| lia| lia]).
      assert (HPe4 : RHEAP st3 (((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) ++ LB) mP3) by (destruct ENV3p as (HPx & _); exact HPx).
      assert (PR4 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mE4)
        by (eapply (dinit_pres_munchH LB _ m mP3 mE4 st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)])); [exact PR3p| exact MU3| exact WM3| exact HPe4| apply in_or_app; right; left; reflexivity| lia]).
      assert (AGs4 : agree_on (As + 212) (As + 5881) mz mE4)
        by (eapply (dinit_ags_munch mz mP3 mE4 S As); [exact AGs3p| exact MU3| exact WM3| lia| lia| lia]).
      assert (BKrw4 : BK rw Aw _ mE4)
        by (eapply BK_munch; [exact BKrw3p| exact MU3| exact WM3| intros q E; eapply (buf_disjH st3 (oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP3 q Aw S As ps lo); [exact HPc3p| in_ow E| lia| exact CEIL]]).
      assert (BKrp4 : BK rp Ap _ mE4)
        by (eapply BK_munch; [exact BKrp3p| exact MU3| exact WM3| intros q E; eapply (buf_disjH st3 (oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP3 q Ap S As ps lo); [exact HPc3p| in_ow E| lia| exact CEIL]]).
      pose proof ENV4 as (HPx4 & _ & _ & _ & _ & AUX4 & SPB4 & _ & STK4 & _ & _ & ERR4 & _ & MI4). rewrite E80 in STK4, SPB4. unfold errno_addr in ERR4.
      assert (HPc4 : RHEAP st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mE4) by (rewrite <- app_assoc in HPx4; cbn [app] in HPx4; exact HPx4).
      assert (INs4 : In (ps, As, 5968) ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB)) by (apply in_or_app; right; left; reflexivity).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
        change (implM psegs tm st3 (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
      eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mE4 st3 ((oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) 32768 2 65536 lo B errv3);
        [ exact HPc4 | exact AUX4 | rewrite E80; exact SPB4 | rewrite E80; exact STK4 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR4 | exact MI4
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      intros rh st4 v40 v41 v42 d40 d41 d42 d43 d44 d45 d46 d47 v43 v44 v45 v46 mP4 errv4 MIp4 STp4 ERRp4 AUXp4 HPR4 EFA4 ESO4 RES4.
      rewrite E80 in STp4, HPR4.
      destruct (zalloc_res _ _ _ _ _ _ RES4) as (Ah & jkh & -> & HPp4 & BUFrh). clear RES4.
      rewrite app_assoc in HPp4.
      assert (HPc4p : RHEAP st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mP4) by exact HPp4.
      replace (ret_pc (wz 91080)) with (wz 91080) by (symmetry; rpc).
      assert (ENV4p : lx_env mP4 st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv4 canary).
      { eapply (lx_env_heap mE4 mP4 st3 st4); [exact ENV4| rewrite E80; eapply rheap_pres_weaken; [exact HPR4| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]
          | rewrite <- app_assoc; cbn [app]; exact HPc4p| exact MIp4| rewrite E80; exact STp4| exact ERRp4| exact AUXp4]. }
      assert (PR4p : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP4).
      { eapply lx_pres_trans; [exact PR4|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR4| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]. }
      assert (AGs4p : agree_on (As + 212) (As + 5881) mz mP4).
      { eapply agree_on_trans; [exact AGs4|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR4); [lia| lia|].
        intros a Ha. right; right. exists (ps, As, 5968). split; [exact INs4| cbn [blk_addr blk_size fst snd]; lia]. }
      assert (BKrw4p : BK rw Aw _ mP4) by (eapply BK_hpres; [exact BKrw4| exact HPR4| intros q E; eapply buf_inH; [exact HPc4| in_ow E]]).
      assert (BKrp4p : BK rp Ap _ mP4) by (eapply BK_hpres; [exact BKrp4| exact HPR4| intros q E; eapply buf_inH; [exact HPc4| in_ow E]]).
      pose proof (BK_refl rh Ah mP4) as BKrh4p.
      assert (ESOs4 : ps_so st4 = ps_so s) by (rewrite ESO4; exact ESOs3).
      assert (EFAs4 : ps_fa st4 = ps_fa s) by (rewrite EFA4; exact EFAs3).
      tr_blk HPR4 GA3 GA4 (ps, As, 5968) INs4. tr_blk HPR4 GD3 GD4 (ps, As, 5968) INs4. tr_up HPR4 ZS3 ZS4. tr_up HPR4 FR3 FR4.
      clear GA3 GD3 ZS3 FR3.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mP4) as MU4. pose proof (wmono_refl psegs mP4) as WM4.
      unfold implM. iprefix.
      do 9 zs.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mE5 end.
      assert (ENV5 : lx_env mE5 st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv4 canary)
        by (eapply (dinit_env_munchH mP4 mE5); [exact ENV4p| exact MU4| exact WM4| eassumption| apply in_or_app; left; apply in_or_app; right; left; reflexivity| rewrite E80; lia| lia| lia| lia]).
      assert (HPe5 : RHEAP st4 (((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) ++ LB) mP4) by (destruct ENV4p as (HPx & _); exact HPx).
      assert (PR5 : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mE5)
        by (eapply (dinit_pres_munchH LB _ m mP4 mE5 st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)])); [exact PR4p| exact MU4| exact WM4| exact HPe5| apply in_or_app; right; left; reflexivity| lia]).
      assert (AGs5 : agree_on (As + 212) (As + 5881) mz mE5)
        by (eapply (dinit_ags_munch mz mP4 mE5 S As); [exact AGs4p| exact MU4| exact WM4| lia| lia| lia]).
      assert (BKrw5 : BK rw Aw _ mE5)
        by (eapply BK_munch; [exact BKrw4p| exact MU4| exact WM4| intros q E; eapply (buf_disjH st4 (oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP4 q Aw S As ps lo); [exact HPc4p| in_ow E| lia| exact CEIL]]).
      assert (BKrp5 : BK rp Ap _ mE5)
        by (eapply BK_munch; [exact BKrp4p| exact MU4| exact WM4| intros q E; eapply (buf_disjH st4 (oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP4 q Ap S As ps lo); [exact HPc4p| in_ow E| lia| exact CEIL]]).
      assert (BKrh5 : BK rh Ah _ mE5)
        by (eapply BK_munch; [exact BKrh4p| exact MU4| exact WM4| intros q E; eapply (buf_disjH st4 (oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) LB mP4 q Ah S As ps lo); [exact HPc4p| in_ow E| lia| exact CEIL]]).
      pose proof ENV5 as (HPx5 & _ & _ & _ & _ & AUX5 & SPB5 & _ & STK5 & _ & _ & ERR5 & _ & MI5). rewrite E80 in STK5, SPB5. unfold errno_addr in ERR5.
      assert (HPc5 : RHEAP st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mE5) by (rewrite <- app_assoc in HPx5; cbn [app] in HPx5; exact HPx5).
      assert (INs5 : In (ps, As, 5968) ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB)) by (apply in_or_app; right; left; reflexivity).
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
        change (implM psegs tm st4 (deflateInit_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
      eapply (dinit_zallocH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mE5 st4 ((oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) 16384 4 65536 lo B errv4);
        [ exact HPc5 | exact AUX5 | rewrite E80; exact SPB5 | rewrite E80; exact STK5 | exact CEIL | rewrite E80; unfold RMALLOC_STACK; lia | exact ERR5 | exact MI5
        | reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
      intros rb st5 v50 v51 v52 d50 d51 d52 d53 d54 d55 d56 d57 v53 v54 v55 v56 mP5 errv5 MIp5 STp5 ERRp5 AUXp5 HPR5 EFA5 ESO5 RES5.
      rewrite E80 in STp5, HPR5.
      destruct (zalloc_res _ _ _ _ _ _ RES5) as (Ab & jkb & -> & HPp5 & BUFrb). clear RES5.
      rewrite app_assoc in HPp5.
      assert (HPc5p : RHEAP st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ (ps, As, 5968) :: LB) mP5) by exact HPp5.
      replace (ret_pc (wz 91116)) with (wz 91116) by (symmetry; rpc).
      assert (ENV5p : lx_env mP5 st5 ((oblk rb Ab 65536 ++ oblk rh Ah 65536 ++ oblk rp Ap 65536 ++ oblk rw Aw 65536) ++ [(ps, As, 5968)]) LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv5 canary).
      { eapply (lx_env_heap mE5 mP5 st4 st5); [exact ENV5| rewrite E80; eapply rheap_pres_weaken; [exact HPR5| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]
          | rewrite <- app_assoc; cbn [app]; exact HPc5p| exact MIp5| rewrite E80; exact STp5| exact ERRp5| exact AUXp5]. }
      assert (PR5p : lx_pres LB (bv_unsigned sp) [(S, S + 112)] m mP5).
      { eapply lx_pres_trans; [exact PR5|]. apply lx_pres_of_heap_pres. eapply rheap_pres_weaken; [exact HPR5| lia| intros bx Hb; first [right; exact Hb | apply in_or_app; right; right; exact Hb]]. }
      assert (AGs5p : agree_on (As + 212) (As + 5881) mz mP5).
      { eapply agree_on_trans; [exact AGs5|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR5); [lia| lia|].
        intros a Ha. right; right. exists (ps, As, 5968). split; [exact INs5| cbn [blk_addr blk_size fst snd]; lia]. }
      assert (BKrw5p : BK rw Aw _ mP5) by (eapply BK_hpres; [exact BKrw5| exact HPR5| intros q E; eapply buf_inH; [exact HPc5| in_ow E]]).
      assert (BKrp5p : BK rp Ap _ mP5) by (eapply BK_hpres; [exact BKrp5| exact HPR5| intros q E; eapply buf_inH; [exact HPc5| in_ow E]]).
      assert (BKrh5p : BK rh Ah _ mP5) by (eapply BK_hpres; [exact BKrh5| exact HPR5| intros q E; eapply buf_inH; [exact HPc5| in_ow E]]).
      pose proof (BK_refl rb Ab mP5) as BKrb5p.
      assert (ESOs5 : ps_so st5 = ps_so s) by (rewrite ESO5; exact ESOs4).
      assert (EFAs5 : ps_fa st5 = ps_fa s) by (rewrite EFA5; exact EFAs4).
      tr_blk HPR5 GA4 GA5 (ps, As, 5968) INs5. tr_blk HPR5 GD4 GD5 (ps, As, 5968) INs5. tr_up HPR5 ZS4 ZS5. tr_up HPR5 FR4 FR5.
      clear GA4 GD4 ZS4 FR4.
      pose proof (munch_refl [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)] mP5) as MU5. pose proof (wmono_refl psegs mP5) as WM5.
      (* 1.4: gzhead is no longer stored (sd zero,56(s1) is gone); the memset left it 0 *)
      assert (EGZ : jw jkz 56 = wz 0) by (apply jw_zero; [lia| intros k Hk; apply HZz; lia]).
      rewrite EGZ in GA5.
      eapply (dinit_tail FREE HND HBR HBD HFRAME HTRI R RD ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB S ni ai ti no ao to p1 p2 lo B canary
                ps As jkz mz rw rp rh rb Aw Ap Ah Ab jkw jkp jkh jkb mP2 mP3 mP4 mP5 st5 errv5 dt0 p30 adl0 resv0 _);
        [ exact SIF | exact LOSP | exact SP16 | exact FRM | exact ENV5p | exact PR5p | exact ESOs5 | exact EFAs5 | exact (unbox _ CBXz) | exact (unbox _ BRX) | exact AGs5p
        | exact BKrw5p | exact BKrp5p | exact BKrh5p | exact BUFrw | exact BUFrp | exact BUFrh | exact BUFrb | exact GA5 | exact GD5 | exact ZS5 | exact FR5 ].
    -
      destruct RES1 as (-> & HP1).
      assert (ENV1 : lx_env m1 st1 [] LB (wz (bv_unsigned sp + -80)) (wz RATP) B lo errv1 canary).
      { eapply (lx_env_heap m0 m1 s st1); [exact ENV0| rewrite E80; exact HPR1| exact HP1| exact MI1| rewrite E80; exact ST1| exact ERR1| exact AUX1]. }
      cbn [ret lops Target.ops]. apply implM_ret.
      pose proof (munch_refl [] m1) as MU1. pose proof (wmono_refl psegs m1) as WM1.
      zs. zs. zs. if_true.
      zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. (* 1.4: + ld s8 *)
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evt_done. unfold deflateInit_post. do 15 eexists. exists F, fc, m1.
      split; [reflexivity|]. cbv beta iota.
      split; [|split; [unfold wint, ZApi.Z_MEM_ERROR, MallocRep.wz; apply bv_eq; reflexivity|]].
      + unfold lx_post_env. split; [exists errv1; eapply lx_env_sp; [exact ENV1| exact ST1| lia]|]. split; [exact FRM|].
        split; [exact PR1| split; [exact ESO1| exact EFA1]].
      + destruct (rw_cells_forget psegs m1 _ _ ZS1) as (j & Hj). exists j. exact Hj.
  Qed.
End DINIT.
End WithCeiling0.
