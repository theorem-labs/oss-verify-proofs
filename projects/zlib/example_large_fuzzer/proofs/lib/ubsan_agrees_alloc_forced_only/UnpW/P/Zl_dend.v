(* reloc-zl14c *)
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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInst. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTarget ZApiL ZHarnessL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import ZInstL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import ZTargetL. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Target. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Driver. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Layout Exit Startup_glue Printf_lib Printf_stdio_iface Zlib_iface Zl_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Printf_pieces. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_zrd Zg_defl_pathi Zl_zrd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Deflate DeflateSafe. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import RefDeflateRel RefDeflSafeI1. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import HarnessSmall ZApiInst ZApiInstL DeflateTaintRel. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Z Require Import ZTaint ZTaintL.
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

(* [comment removed for export] *)
Lemma agree_on_hpres : forall LB SP m m' lo hi, rheap_pres LB SP m m' -> 0 <= lo -> hi <= 2^64 ->
  (forall a, lo <= a < hi -> rclient_addr LB SP a) -> agree_on lo hi m m'.
Proof. intros LB SP m m' lo hi H H0 H1 HC a Ha. apply H; [lia| apply HC; exact Ha]. Qed.

(* [comment removed for export] *)
Lemma state_check_cases : forall d, deflateStateCheck d = false ->
  let st := ds_status d in st = 42 \/ st = 57 \/ st = 69 \/ st = 73 \/ st = 91 \/ st = 103 \/ st = 113 \/ st = 666.
Proof.
  intros d H. unfold deflateStateCheck in H. apply negb_false_iff in H. cbv zeta.
  unfold INIT_STATE, GZIP_STATE, EXTRA_STATE, NAME_STATE, COMMENT_STATE, HCRC_STATE, BUSY_STATE, FINISH_STATE in H.
  repeat (apply orb_true_iff in H; destruct H as [H|H]); apply Z.eqb_eq in H; lia.
Qed.

Section DENDL.
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

  (* [comment removed for export] *)
  Ltac tr_up HPR H Hn :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia| intros ?a ?Ha; cbn in Ha; left; lia])) as Hn.
  Ltac tr_st HPR H Hn blk :=
    pose proof (Z_dview.rw_cells_agree _ _ _ _ H ltac:(eapply (agree_on_hpres _ _ _ _ _ _ HPR); [lia| cbn; lia
      | intros ?a ?Ha; cbn in Ha; right; right; exists blk; split; [cbn; tauto| cbn; lia]])) as Hn.

  (* [comment removed for export] *)
  Definition deflateEnd_postR (rc : Z) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (s : PState) (LB : list block) (S : Z) (lo B : Z) (canary : word) (m : mem)
      (r : unit) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F' (ret_pc ra) fc' None m' (seg_rom psegs)
      /\ lx_post_env m m' s s' [] LB sp tp B lo canary [(S, S + ZS_SIZEOF)] fc'
      /\ a0 = wint rc
      /\ (exists j : list byte, rw_cells psegs m' S [CB 112 j]).

  Theorem deflateEnd_drepL : forall (L : dlay) (d : deflate_state) (z : zstrm)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem)
         (s : PState) (LB : list block) (b : bptr * bptr * bptr * bptr * bptr)
         (ni ai ti no ao to : Z) (p1 p2 : list byte) (lo B : Z) (errv canary : word),
    lx_env m s (zd_blocks b L) LB sp tp B lo errv canary ->
    rw_cells psegs m (dl_S L) (zs_pub ni ai ti no ao to p1 p2) ->
    DREPq m L d z ->
    deflateStateCheck d = false ->
    strm_in_frame sp (dl_S L) B ->
    lo <= bv_unsigned sp - Z_DEFLATEEND_STACK -> bv_unsigned sp mod 16 = 0 ->
    frm0 fc ->
    a0 = wz (dl_S L) ->
    implM psegs (deflate_end lops b) s
          (deflateEnd_postR (dend_rc d) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m)
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (wz Z_DEFLATEEND_A) fc None m (seg_rom psegs)).
  Proof.
    intros until canary. intros ENV PUB (ZQ & ST) CHK SIF LOSP SP16 FRM ->.
    destruct b as [[[[bs bw] bpv] bh] bb]. unfold zd_blocks in ENV. cbn [deflate_end].
    pose proof (st_lay _ _ _ _ ST) as LAY.
    pose proof ENV as (HP & _ & _ & _ & _ & AUX & SPB & B63 & STK & CEIL & GLO & ERRC & TP & MI).
    destruct ZQ as (p3 & resv & ZQ). unfold zs_priv_cells in ZQ.
    destruct ST as [GA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. destruct GA as (h1 & h2 & h3 & h4 & h5 & GA). unfold dsA_cells in GA.
    lay_open LAY.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    (* [comment removed for export] *)
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
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (evt_cut psegs (fun ms' => exists a4' a5' : word,
        ms' = MS (mkR ra (wz (bv_unsigned sp + -32)) gp (MallocRep.wz RATP) t0 t1 t2 (sx32 (wz (ds_status d))) s1 (wz (dl_S L)) (wz (dl_As L))
                      (wz (-2)) (wz Z_ZCFREE) a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x16608) fc None mm (seg_rom psegs))) end.
    { pose proof (state_check_cases d CHK) as CS. cbv zeta in CS.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        let bs := eval vm_compute in (option.default [] (image_bytes psegs 0x10700 8)) in
        assert (MASK : ro_cells psegs mm 0x10700 [CB (length bs) bs])
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
    (* [comment removed for export] *)
    zstep. zstep. zstep. if_false. zstep. zstep. zstep.
    apply evt_done.
    replace (ret_pc (wz Z_ZCFREE)) with (wz Z_ZCFREE) by (symmetry; unfold Z_ZCFREE; rpc).
    pose proof ENV1 as (HP1 & _ & _ & _ & _ & AUX1 & SPB1 & _ & STK1 & _ & _ & ERR1 & _ & MI1). rewrite E32 in STK1.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s (deflateEnd_postR (dend_rc d) ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
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
    replace (ret_pc (wz 91680)) with (wz 91680) by (symmetry; rpc).
    pose proof (munch_refl [] m1) as MUa. pose proof (wmono_refl psegs m1) as WMa.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. if_false. zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s1' (deflateEnd_postR (dend_rc d) ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
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
    replace (ret_pc (wz 91712)) with (wz 91712) by (symmetry; rpc).
    pose proof (munch_refl [] m2) as MUb. pose proof (wmono_refl psegs m2) as WMb.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. if_false. zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s2' (deflateEnd_postR (dend_rc d) ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
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
    replace (ret_pc (wz 91744)) with (wz 91744) by (symmetry; rpc).
    pose proof (munch_refl [] m3) as MUc. pose proof (wmono_refl psegs m3) as WMc.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. if_false. zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s3' (deflateEnd_postR (dend_rc d) ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
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
    replace (ret_pc (wz 91776)) with (wz 91776) by (symmetry; rpc).
    pose proof (munch_refl [] m4) as MUd. pose proof (wmono_refl psegs m4) as WMd.
    unfold implM. iprefix.
    zstep. zstep. zstep.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx =>
      change (implM psegs tm s4' (deflateEnd_postR (dend_rc d) ra sp gp (MallocRep.wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB (dl_S L) lo B canary m) msx) end.
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
    replace (ret_pc (wz 91804)) with (wz 91804) by (symmetry; rpc).
    pose proof (munch_refl [(lo, bv_unsigned sp); (dl_S L, dl_S L + 112)] m5) as MUe. pose proof (wmono_refl psegs m5) as WMe.
    unfold zs_pub in PUBe.
    zstep. change (Z_to_le_bytes 8 0) with (le8 (wz 0)); mem_after_store.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (evt_cut psegs (fun ms' => exists a0' a2' : word,
        ms' = MS (mkR (wz 91804) (wz (bv_unsigned sp + -32)) gp (MallocRep.wz RATP) y0 y1 y2 (sx32 (wz (ds_status d))) (wz (dl_S L)) a0' f1
                      a2' f3 f4 f5 f6 f7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y3 y4 y5 y6) F (wz 0x166b0) fc None mm (seg_rom psegs)
        /\ a2' = wint (dend_rc d))) end.
    { pose proof (state_check_cases d CHK) as CS. cbv zeta in CS. unfold dend_rc. rewrite CHK.
      destruct CS as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E;
        zstep; zstep; zstep; zstep; apply evt_done; do 2 eexists; (split; [reflexivity| apply bv_eq; vm_compute; reflexivity]). }
    intros ms' (a0' & a2' & -> & EA2).
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
    apply evt_done. unfold deflateEnd_postR.
    do 15 eexists. exists F, fc, m6.
    split; [reflexivity|].
    split; [|split; [first [exact EA2 | rewrite <- EA2; apply bv_eq; reflexivity] |]].
    - unfold lx_post_env. split; [exists errv; exact ENVf|]. split; [exact FRM|]. split; [exact PRf|].
      split; [rewrite ESOe, ESOd, ESOc, ESOb, ESOa; reflexivity| rewrite EFAe, EFAd, EFAc, EFAb, EFAa; reflexivity].
    - assert (ALL : rw_cells psegs m6 (dl_S L) (zs_pub ni ai ti no ao to p1 p2 ++
                      [C8 (wz (msg_ptr (zs_msg z))); C8 (wz 0); C8 (wz 107260); C8 (wz 107276); C8 (wz 0); C4 (wz (zs_data_type z)); CB 4 p3; C8 (wz (zs_adler z)); C8 resv])).
      { apply rw_cells_app. split; [exact PUBe| exact ZQe]. }
      destruct (rw_cells_forget psegs m6 _ _ ALL) as (j & Hj). exists j. exact Hj.
  Qed.

  (* [comment removed for export] *)
  Local Transparent the_zapiL.
  Theorem deflateEnd_proofL : forall R : zrepsL, zrd R = zr_dL -> deflateEnd_stmtL R.
  Proof.
    intros R RD. unfold deflateEnd_stmtL. intros until canary. intros ENV PUB ZR SIF LOSP SP16 FRM EA0.
    rewrite RD in ZR. destruct ZR as (L & sa & b' & EQ & ES & DQ & DR & PT & DCL & ZOK).
    destruct b as [[[[bs bw] bpv] bh] bb]. destruct b' as [[[[bs' bw'] bpv'] bh'] bb'].
    cbv [blk5L zd_blocks zl_dpend zl_dhead zl_dprev zl_dwin zl_dstate the_zapiL ZApiInstL.zinstL] in EQ, ENV.
    injection EQ as -> -> -> -> -> -> -> -> -> ->. subst S.
    pose proof (df_status _ (proj1 (proj1 (zr_dL_facts sa ds DR)))) as CHK.
    unfold deflateEnd_postL. cbn [dl_end the_zapiL ZApiInstL.zinstL]. rewrite <- (DRELL_dend_rc sa ds DR).
    change (deflate_endL lops (bs', bw', bpv', bh', bb')) with (deflate_end lops (bs', bw', bpv', bh', bb')).
    eapply (deflateEnd_drepL L sa (dz_z ds)) with (b := (bs', bw', bpv', bh', bb')) (errv := errv);
      [ exact ENV | exact PUB | exact DQ | exact CHK | exact SIF | exact LOSP | exact SP16 | exact FRM | exact EA0 ].
  Qed.
End DENDL.
End WithCeiling0.
