(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZInst ZTarget Target Driver Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Layout Exit Startup_glue Printf_lib Printf_stdio_iface Zlib_iface Driver_iface Drv_kit Zh_kit Z_kit Z_dview Z_drep Z_dkit Printf_pieces Z_dend Z_dinit_kit Z_dreset.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface DeflateState Deflate HarnessSmall ZApiInst DeflateTaintRel ZTaint.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.P Require Import Rnd.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import StoreFast.
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
          F (wz 0x166e0) fc None mk (seg_rom psegs)).
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
    replace (ret_pc (wz 91888)) with (wz 91888) by (symmetry; rpc).
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
          F (wz 0x166c0) fc None mk (seg_rom psegs)).
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
      replace (ret_pc (wz 91860)) with (wz 91860) by (symmetry; rpc).
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
          F (wz 0x166a0) fc None mk (seg_rom psegs)).
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
      replace (ret_pc (wz 91828)) with (wz 91828) by (symmetry; rpc).
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
          F (wz 0x16680) fc None mk (seg_rom psegs)).
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
      replace (ret_pc (wz 91796)) with (wz 91796) by (symmetry; rpc).
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
      replace (ret_pc (wz 91764)) with (wz 91764) by (symmetry; rpc).
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
