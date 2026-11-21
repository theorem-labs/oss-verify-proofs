(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget ZApiL ZHarnessL ZInstL ZTargetL Target Driver Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Layout Exit Startup_glue Printf_lib Printf_stdio_iface Zlib_iface Zl_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit Printf_pieces Z_zrd Z_trees_iface Z_dend Z_dinit_kit Zl_dinit9_model Zl_dreset9 Z_dendk.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Z Require Import ZProg ZIface DeflateState Deflate RefDeflateInitLib RefDeflSafeI5b HarnessSmall ZApiInst DeflateTaintRel ZTaint BoundPat ZPat FillWinModel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import StoreFast.
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

Local Notation MP := (OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec.Monad.M PState).
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
  Proof using MALLOC.
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

  Lemma dinit_fail : forall (R : zrepsL)
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
      (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m)
      (MS (mkR ra' (wz (bv_unsigned sp + -80)) gp (wz RATP) t0' t1' t2' (wz S) (wz As) a0' a1' a2' a3' a4' a5' a6' a7' v18 v19 v20 v21 v22 v23 s8 s9 s10 s11 t3' t4' t5' t6')
          F (wz 0x16558) fc None mk (seg_rom psegs)).
  Proof using HFRAME HBD HBR HND FREE.
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
      change (implM psegs tm sk (deflateInit9_post R ra sp gp (wz RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB S ni ai no ao p1 p2 lo B canary m) msx) end.
    eapply (deflateEnd_rawK FREE HND HBR HFRAME (ret lops None) _ S As Ab Ah Ap Aw ps (set_status sx 666) ni ai ti no ao to p1 p2 _ (wz 0) dt p3 adl resv pPO pGZ h1 h2 h3 h4 h5 ob oh op ow)
      with (lo := lo) (B := B) (errv := errv) (canary := canary) (LB := LB);
      [ exact ENV1 | unfold zs_raw, zs_pub; cbn [app]; exact ZS | exact GA | reflexivity
      | unfold strm_in_frame, ZS_SIZEOF; rewrite E80; lia | rewrite E80; unfold Z_DEFLATEEND_STACK, RFREE_STACK; lia | reflexivity | ].
    intros s' u0 u1 u2 c1 c2 c3 c4 c5 c6 c7 u3 u4 u5 u6 m' ENV' PR' ESO' EFA' ZS'.
    rewrite E80 in PR'.
    replace (ret_pc (wz 91512)) with (wz 91512) by (symmetry; rpc).
    assert (FR' : rw_cells psegs m' (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply Drv_kit.rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ PR')| exact FR|].
      intros a Ha. cbn in Ha. apply stack_client; [lia| cbn [rin_ivs fst snd]; lia]. }
    pose proof ENV' as (_ & _ & _ & _ & _ & _ & _ & _ & STK' & _ & _ & _ & _ & MI'). rewrite E80 in STK'.
    cbn [ret lops Target.ops]. apply implM_ret.
    pose proof (munch_refl [] m') as MU'. pose proof (wmono_refl psegs m') as WM'.
    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. zs. (* 1.4: + ld s8 *)
    release_frame FR' STK' (bv_unsigned sp).
    apply evt_done. unfold deflateInit9_post. do 15 eexists. exists F, fc, m'.
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
  Proof using.
    intros [p|] a0' s' LBc m' n H.
    - destruct H as (Ab & junk & E & BR & HP & CB). exists Ab, junk. cbn [oadr oblk app]. split; [exact E|]. split; [exact HP|]. intros q _. split; assumption.
    - destruct H as (E & HP). exists 0, []. cbn [oadr oblk app]. split; [exact E|]. split; [exact HP|]. intros q Hq. discriminate Hq.
  Qed.

  Definition BK (o : option bptr) (A : Z) (mk mc : mem) : Prop := forall p, o = Some p -> agree_on A (A + 65536) mk mc.

  Lemma BK_refl : forall o A mk, BK o A mk mk.
  Proof using. intros o A mk p _. apply agree_on_refl. Qed.

  Lemma BK_hpres : forall o A mk mc mc' LBc SP, BK o A mk mc -> rheap_pres LBc SP mc mc' ->
    (forall p, o = Some p -> In (p, A, 65536) LBc /\ 0 <= A /\ A + 65536 <= 2^64) -> BK o A mk mc'.
  Proof using.
    intros o A mk mc mc' LBc SP H HPR HIN p E. destruct (HIN p E) as (IN & R0 & R1).
    eapply agree_on_trans; [exact (H p E)|]. eapply (agree_on_hpres _ _ _ _ _ _ HPR); [exact R0| exact R1|].
    intros a Ha. right; right. exists (p, A, 65536). split; [exact IN| cbn [blk_addr blk_size fst snd]; lia].
  Qed.

  Lemma BK_munch : forall o A mk mc mc' W, BK o A mk mc -> munch W mc mc' -> wmono psegs mc mc' ->
    (forall p, o = Some p -> disjoint_from W A 65536 /\ 0 <= A /\ A + 65536 <= 2^64) -> BK o A mk mc'.
  Proof using.
    intros o A mk mc mc' W H MU WM HD p E. destruct (HD p E) as (D & R0 & R1).
    eapply agree_on_trans; [exact (H p E)|]. apply (agree_on_of_munch W); [exact MU| exact WM| exact R0| exact R1| exact D].
  Qed.

  Definition WI (S As : Z) : list ivl := [(S, S + 112); (As, As + 212); (As + 5881, As + 5968)].

  Lemma dinit_env_munch : forall m m' st OW LB (sp' : word) B lo errv canary S As ps,
    lx_env m st OW LB sp' (wz RATP) B lo errv canary -> munch (WI S As) m m' -> wmono psegs m m' -> mem_inv psegs m' ->
    In (ps, As, 5968) (OW ++ LB) -> bv_unsigned sp' <= S -> lo <= S -> S + 112 <= B -> As + 5968 <= lo ->
    lx_env m' st OW LB sp' (wz RATP) B lo errv canary.
  Proof using HFRAME HBR.
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
  Proof using HBD HBR HND.
    intros LB SP m0 m m' st OW S As ps PR MU WM HP IN LS.
    eapply lx_pres_trans; [exact PR|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_introl IN))) as (R1 & _ & _ & R2 & IMG). cbn [blk_addr blk_size fst snd] in R1, R2, IMG.
    intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; unfold WI; cbn [outside fst snd]; (split; [|split; [|split; [|exact I]]]); try lia.
    all: pose proof (heap_sep st OW LB m (ps, As, 5968) bx HND HBD HP IN Hb) as SEP; cbn [blk_addr blk_size fst snd] in SEP; lia.
  Qed.

  (* deflateInit2_'s memset(s + 8, 0, 5960) writes inside the state block only. *)
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

  (* 1.4: the munch after the memset and the state stores: the memset window plus the stack and state fields *)
  Lemma munch_shrinkZ : forall W W' (m m' : mem), munch W m m' -> (forall x : word, outside W' (bv_unsigned x) -> outside W (bv_unsigned x) \/ m' x = m x) -> munch W' m m'.
  Proof. intros W W' m m' MU H x Hx. destruct (H x Hx) as [O|E]; [exact (MU x O)| exact E]. Qed.

  Definition WZS (S As : Z) : list ivl := [(S, S + 112); (As, As + 5968)].

  Lemma outside_app_split : forall W1 W2 x, outside (W1 ++ W2) x -> outside W1 x /\ outside W2 x.
  Proof.
    induction W1 as [|[l h] W IH]; cbn [outside app]; [intros; split; [exact I| assumption]|].
    intros W2 x (N & R). destruct (IH W2 x R) as (R1 & R2). split; [split; assumption| exact R2].
  Qed.

  Lemma munch_comp2 : forall W1 W2 (m0 m1 m2 : mem), munch W1 m0 m1 -> munch W2 m1 m2 -> munch (W1 ++ W2) m0 m2.
  Proof.
    intros W1 W2 m0 m1 m2 H1 H2 x Hx. pose proof (outside_app_split _ _ _ Hx) as O1.
    rewrite (H2 x (proj2 O1)). apply H1, O1.
  Qed.

  Lemma munch_comp3 : forall S As (m0 m1 m2 m3 : mem), munch [(As + 8, As + 5968)] m0 m1 -> munch [(S, S + 112)] m1 m2 -> munch [(As, As + 212)] m2 m3 -> munch (WZS S As) m0 m3.
  Proof.
    intros S As m0 m1 m2 m3 H1 H2 H3 x Hx. unfold WZS in Hx. cbn [outside] in Hx. destruct Hx as (A & B & _).
    rewrite (H3 x), (H2 x), (H1 x); try reflexivity; cbn [outside]; repeat split; try exact I; lia.
  Qed.

  Lemma dinit_env_munchZS : forall m m' st OW LB (sp' : word) B lo errv canary S As ps,
    lx_env m st OW LB sp' (wz RATP) B lo errv canary -> munch (WZS S As) m m' -> wmono psegs m m' -> mem_inv psegs m' ->
    In (ps, As, 5968) (OW ++ LB) -> bv_unsigned sp' <= S -> lo <= S -> S + 112 <= B -> As + 5968 <= lo ->
    lx_env m' st OW LB sp' (wz RATP) B lo errv canary.
  Proof.
    intros m m' st OW LB sp' B lo errv canary S As ps ENV MU WM MI' IN LS LLS SB LA.
    pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & _ & STK & CEIL & GLO & _).
    pose proof (HBR _ _ _ _ HP IN) as (R1 & _ & _ & R2 & IMG). cbn [blk_addr blk_size fst snd] in R1, R2, IMG.
    unfold GLOBALS_TOP in GLO.
    assert (STK' : stk psegs m' lo (bv_unsigned sp')).
    { eapply (stk_transport_disjoint psegs (WZS S As) m m' lo (bv_unsigned sp')); [exact STK| exact MU| exact WM|].
      unfold WZS. cbn [disjoint_from]. lia. }
    eapply (lx_env_munch (WZS S As) m m'); [exact HFRAME| exact ENV| exact MU| exact WM| exact MI'| exact STK'| exact SPB| |].
    - unfold WZS. constructor; [left; cbn [fst]; lia|].
      constructor; [right; right; exists (ps, As, 5968); split; [exact IN| cbn [blk_addr blk_size fst snd]; lia]| constructor].
    - intros a Ha. unfold WZS. cbn [outside fst snd]. split; [lia| split; [lia| exact I]].
  Qed.

  Lemma dinit_pres_munchZS : forall LB SP m0 m m' st OW S As ps,
    lx_pres LB SP [(S, S + 112)] m0 m -> munch (WZS S As) m m' -> wmono psegs m m' ->
    RHEAP st (OW ++ LB) m -> In (ps, As, 5968) OW -> As + 5968 <= SP ->
    lx_pres LB SP [(S, S + 112)] m0 m'.
  Proof.
    intros LB SP m0 m m' st OW S As ps PR MU WM HP IN LS.
    eapply lx_pres_trans; [exact PR|]. eapply lx_pres_of_munch; [exact MU| exact WM|].
    pose proof (HBR _ _ _ _ HP (in_or_app _ _ _ (or_introl IN))) as (R1 & _ & _ & R2 & IMG). cbn [blk_addr blk_size fst snd] in R1, R2, IMG.
    intros a (NX & [Ha|[(bx & Hb & Hr)|[Ha _]]]); cbn [rin_ivs fst snd] in NX; unfold WZS; cbn [outside fst snd]; (split; [|split; [|exact I]]); try lia.
    all: pose proof (heap_sep st OW LB m (ps, As, 5968) bx HND HBD HP IN Hb) as SEP; cbn [blk_addr blk_size fst snd] in SEP; lia.
  Qed.

  Lemma dinit_ags_munch : forall m1 m m' S As, agree_on (As + 212) (As + 5881) m1 m -> munch (WI S As) m m' -> wmono psegs m m' ->
    0 <= As -> As + 5968 <= 2^64 -> (S + 112 <= As \/ As + 5968 <= S) -> agree_on (As + 212) (As + 5881) m1 m'.
  Proof using.
    intros m1 m m' S As AG MU WM R0 R1 SEP. eapply agree_on_trans; [exact AG|].
    apply (agree_on_sub (As + 212) (As + 212 + 5669)); [| lia| lia].
    apply (agree_on_of_munch (WI S As)); [exact MU| exact WM| lia| lia|]. unfold WI. cbn [disjoint_from]. lia.
  Qed.

  Lemma buf_in : forall st OWb LB m p A As ps, RHEAP st (OWb ++ (ps, As, 5968) :: LB) m -> In (p, A, 65536) OWb ->
    In (p, A, 65536) (OWb ++ (ps, As, 5968) :: LB) /\ 0 <= A /\ A + 65536 <= 2^64.
  Proof using HBR.
    intros st OWb LB m p A As ps HP IN. assert (IN' : In (p, A, 65536) (OWb ++ (ps, As, 5968) :: LB)) by (apply in_or_app; left; exact IN).
    pose proof (HBR _ _ _ _ HP IN') as (R1 & _ & _ & R2 & _). cbn [blk_addr blk_size fst snd] in R1, R2. split; [exact IN'| lia].
  Qed.

  Lemma buf_disj : forall st OWb LB m p A S As ps lo, RHEAP st (OWb ++ (ps, As, 5968) :: LB) m -> In (p, A, 65536) OWb ->
    lo <= S -> alloc_ceiling <= lo ->
    disjoint_from (WI S As) A 65536 /\ 0 <= A /\ A + 65536 <= 2^64.
  Proof using HBD HBR HND.
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
