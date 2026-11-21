(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import SysStep. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInst. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTarget. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Driver. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Layout Exit Startup_glue Printf_lib Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Printf_pieces. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_zrd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Deflate HarnessSmall ZApiInst DeflateTaintRel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import ZTaint.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import StoreFast.
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

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapi.

(* [comment removed for export] *)
Lemma agree_on_hpres : forall LB SP m m' lo hi, rheap_pres LB SP m m' -> 0 <= lo -> hi <= 2^64 ->
  (forall a, lo <= a < hi -> rclient_addr LB SP a) -> agree_on lo hi m m'.
Proof. intros LB SP m m' lo hi H H0 H1 HC a Ha. apply H; [lia| apply HC; exact Ha]. Qed.

(* [comment removed for export] *)

Section DEND.
  Hypothesis FREE : rfree_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HFRAME : RHEAP_frame_stmt.

  Definition Z_DEFLATEEND_A : Z := 0x165ac.

  (* [comment removed for export] *)
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

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac tr_up HPR H Hn :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia| intros ?a ?Ha; cbn in Ha; left; lia])) as Hn.
  Ltac tr_st HPR H Hn blk :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia
      | intros ?a ?Ha; cbn in Ha; right; right; exists blk; split; [cbn; tauto| cbn; lia]])) as Hn.

  (* [comment removed for export] *)

  Local Transparent the_zapi.

End DEND.
End WithCeiling0.
