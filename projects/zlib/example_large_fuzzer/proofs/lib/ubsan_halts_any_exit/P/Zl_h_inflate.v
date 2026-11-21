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
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL ZInstL ZTargetL Target Driver Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_halts_any_exit.P Require Import Layout Exit Startup_glue Printf_lib Printf_stdio_iface Stdio_iface F_fprintf Zlib_iface Driver_iface Drv_kit Zh_kit Zl_stderr Zl_iface.
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
Notation wz := MallocRep.wz.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].
Ltac nm n t := first [t | fail 100 "premise" n].
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapiL.

Section TI.
  Variable R : zrepsL.
  Hypothesis ZOK : zlib_okL R.
  Hypothesis CHK : @check_err_stmt PState.
  Hypothesis BAD : @bad_msg_stmt PState.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  Variables (ra sp gp tp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Variables (LB : list block) (C U size N diff : Z) (comprc : list Z) (cp up : bptr) (lo B : Z) (canary : word).
  Notation usp := (bv_unsigned sp).
  Notation SS := (usp + -136).
  Notation ZHS := 0x3a6d0.
  Hypothesis INC : In (cp, C, N) LB.
  Hypothesis INU : In (up, U, N) LB.
  Hypothesis NEQ : cp <> up.
  Hypothesis SZ : 1 <= size <= ZL_MAX.
  Hypothesis EN : N = NofL size.
  Hypothesis CCL : zlength comprc = N.
  Hypothesis DIFR : 0 <= diff < 2^32.
  Hypothesis SPB : usp <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOG : GLOBALS_TOP <= lo.
  Hypothesis LOSP : lo <= usp - ZHL_TEST_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis SP16 : usp mod 16 = 0.
  Hypothesis CR : rblock_range C N.
  Hypothesis UR : rblock_range U N.
  Hypothesis CU : U + N <= C \/ C + N <= U.
  Hypothesis LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b).

  Definition cc : list Z := norm8 comprc.
  Lemma cc_facts : zlength cc = N /\ Forall (fun c => 0 <= c < 256) cc /\ to_bytes cc = to_bytes comprc.
  Proof. unfold cc. split; [rewrite norm8_length; exact CCL|]. split; [apply norm8_bytes| apply to_bytes_norm8]. Qed.
  Lemma N_facts : 103 <= N <= 1572964.
  Proof. rewrite EN. unfold NofL, ZL_MAX in *. lia. Qed.

  Notation XX := [(U, U + N); LXW_STDERR].

  Definition FRLO (mm : mem) : Prop := exists j0 : list byte, rw_cells psegs mm (usp + -144) [CB 8 j0].
  Definition FRHI (mm : mem) : Prop := rw_cells psegs mm (usp + -24) [C8 S1; C8 S0; C8 ra].

  Lemma client_inner : forall a, lx_client LB usp XX a -> lx_client LB (usp + -144) [(SS, SS + ZS_SIZEOF); (U, U + N)] a.
  Proof.
    intros a [HX Hc]. split.
    - cbn [rin_ivs fst snd]. intros [Hi|[Hi|[]]].
      + unfold ZS_SIZEOF in Hi. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| |].
        * destruct (LBR b Hb) as (_ & _ & _ & BC & _). unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
        * unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *. lia.
      + apply HX. cbn [rin_ivs fst snd]. left. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.
  Lemma client_inner0 : forall a, lx_client LB usp XX a -> lx_client LB (usp + -144) [(SS, SS + ZS_SIZEOF)] a.
  Proof.
    intros a [HX Hc]. split.
    - cbn [rin_ivs fst snd]. intros [Hi|[]]. unfold ZS_SIZEOF in Hi. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| |].
      + destruct (LBR b Hb) as (_ & _ & _ & BC & _). unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
      + unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Lemma pres_munch : forall W m m', munch W m m' -> wmono psegs m m' ->
    (forall a, usp <= a \/ (0x29000 <= a < 0x5c000 /\ ~ stderr_addr a)
               \/ (a < lo /\ (a < 0x10000 \/ 0x5c000 <= a) /\ ~ (U <= a < U + N)) -> outside W a) ->
    lx_pres LB usp XX m m'.
  Proof.
    intros W m m' MU WM HW. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; apply HW.
    - left. exact Ha.
    - right; right. destruct (LBR b Hb) as (_ & _ & _ & BC & BI). split; [lia|]. split; [lia|].
      intros Hc. apply HX. cbn [rin_ivs fst snd]. left. exact Hc.
    - right; left. split; [exact Ha|]. intros Hs. apply HX. cbn [rin_ivs]. right; left. unfold LXW_STDERR, LX_STDERR_FILE, stderr_addr in *. cbn [fst snd]. lia.
  Qed.

  Section Inv.
    Variables (m0 : mem) (s0 : PState) (pst : bptr) (As : Z).

    Definition EINV (m : mem) (s : PState) (fc : bv 32) (OW : list block) : Prop :=
      (exists errv, lx_env m s OW LB (Z_to_bv 64 (usp + -144)) tp B lo errv canary)
      /\ FRLO m /\ FRHI m /\ rw_cells psegs m ZHS [C4 (wz diff)] /\ u8arr psegs m C (to_bytes cc)
      /\ lx_pres LB usp XX m0 m /\ ps_so s = ps_so s0 /\ ps_fa s = ps_fa s0 /\ frm0 fc.

    Definition IINV (m : mem) (s : PState) (fc : bv 32) (is : ISL za) (uc : list Z) (w : option bptr) (Aw : Z) : Prop :=
      EINV m s fc (iblocksL w Aw pst As)
      /\ (exists no ao p1 p2, rw_cells psegs m SS (zs_pub (C + il_total_in za is) (N - il_total_in za is) (il_total_in za is) no ao (il_total_out za is) p1 p2))
      /\ 0 <= il_total_in za is <= N /\ 0 <= il_total_out za is
      /\ zri R m SS (iblocksL w Aw pst As) is
      /\ u8arr psegs m U (to_bytes uc) /\ zlength uc = N.

    Definition IINVw (m : mem) (s : PState) (fc : bv 32) (is : ISL za) (uc : list Z) (w : option bptr) (Aw : Z) : Prop :=
      EINV m s fc (iblocksL w Aw pst As)
      /\ (exists ni ai no ao p1 p2, rw_cells psegs m SS (zs_pub ni ai (il_total_in za is) no ao (il_total_out za is) p1 p2))
      /\ zri R m SS (iblocksL w Aw pst As) is
      /\ u8arr psegs m U (to_bytes uc) /\ zlength uc = N.

    Lemma wint_cases : forall rc, - 2^31 <= rc < 2^31 -> (0 <= rc /\ bv_unsigned (wint rc) = rc) \/ (rc < 0 /\ bv_unsigned (wint rc) = rc + 2^64).
    Proof.
      intros rc Hrc. unfold wint, wz. rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
      destruct (Z.lt_ge_cases rc 0) as [Ng|Ng]; [right| left]; (split; [lia|]).
      - symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia.
      - apply Z.mod_small. lia.
    Qed.

    Lemma cells_lx : forall X m m' (A : Z) cs, lx_pres LB (usp + -144) X m m' -> rw_cells psegs m A cs ->
      (forall a, A <= a < A + Z.of_nat (cells_size cs) -> lx_client LB (usp + -144) X a) -> rw_cells psegs m' A cs.
    Proof. intros X m m' A cs LXP H HC. eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact H| exact HC]. Qed.

    Notation TIST pc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m :=
      (MS (mkR x1 (wz (usp + -144)) gp tp t0 t1 t2 (wz N) (wz U) a0 a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz pc) fc None m (seg_rom psegs)).

    Ltac stackc := apply stack_client; [lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia].

    Lemma einv_step : forall m m' s s' fc fc' OW OW' X,
      EINV m s fc OW -> (X = [(SS, SS + ZS_SIZEOF); (U, U + N)] \/ X = [(SS, SS + ZS_SIZEOF)]) ->
      lx_post_env m m' s s' OW' LB (Z_to_bv 64 (usp + -144)) tp B lo canary X fc' ->
      EINV m' s' fc' OW'.
    Proof.
      intros m m' s s' fc fc' OW OW' X ((errv & ENV) & (j0 & FRL) & FRH & ZH & CARR & PRES & ESO & EFA & FRM) HX (ENV' & FRM' & LXP & ESO' & EFA').
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG. pose proof N_facts as NF.
      rewrite unsigned_lit in LXP by lia.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      destruct cc_facts as (CCL' & _ & _).
      assert (NX : forall a, ~ rin_ivs [(SS, SS + ZS_SIZEOF); (U, U + N)] a -> ~ rin_ivs X a).
      { intros a Ha. destruct HX as [-> | ->]; [exact Ha|]. cbn [rin_ivs fst snd] in *. tauto. }
      unfold EINV. split; [exact ENV'|].
      split. { exists j0. eapply cells_lx; [exact LXP| exact FRL|]. intros a Ha. cbn in Ha. apply stack_client; [lia| apply NX; cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      split. { unfold FRHI in *. eapply cells_lx; [exact LXP| exact FRH|]. intros a Ha. cbn in Ha. apply stack_client; [lia| apply NX; cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      split. { eapply cells_lx; [exact LXP| exact ZH|]. intros a Ha. cbn in Ha. apply zls_addr_client.
               - unfold zls_addr, ZH_STATICS in *. lia.
               - apply NX. cbn [rin_ivs fst snd]. unfold ZS_SIZEOF in *. lia. }
      split. { eapply u8arr_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact CARR|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zlength in CCL'.
               eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| apply NX; cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      split. { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_sub; [exact LXP|]. intros a Ha. destruct HX as [-> | ->]; [apply client_inner| apply client_inner0]; exact Ha. }
      split; [rewrite ESO'; exact ESO|]. split; [rewrite EFA'; exact EFA| exact FRM'].
    Qed.

    Lemma zri_pub : forall m m' LBz is, (forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b)) ->
      zri R m SS LBz is -> munch [(SS, SS + 48)] m m' -> wmono psegs m m' -> zri R m' SS LBz is.
    Proof.
      intros m m' LBz is LBZR ZR MU WM. eapply (zri_frame R); [exact ZR|]. intros a Ha Hin.
      apply (agree_on_of_munch _ _ _ MU WM a Ha). cbn [outside]. split; [| exact I].
      destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|].
      destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, ZS_PUB in *. lia.
    Qed.

    Lemma ti_loop : forall (A : Type) (K : @iloopL_res bptr za -> M PState A) (POSTQ : A -> PState -> machine_state -> Prop),
      (forall is uc w Aw s (x1 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m, IINVw m s fc is uc w Aw -> 0 <= il_total_out za is <= 2^62 ->
         implM psegs (K (ILLdone is w)) s POSTQ (TIST 0x160e0 x1 t0 t1 t2 (wz 1) a1 a2 (wint Z_STREAM_END) a4 a5 a6 a7 t3 t4 t5 t6 F fc m)) ->
      (forall rc is uc w Aw s (x1 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m, IINVw m s fc is uc w Aw ->
         - 2^31 <= rc < 2^31 ->
         implM psegs (K (ILLerr rc w)) s POSTQ (TIST 0x16140 x1 t0 t1 t2 (wz 1) a1 a2 (wint rc) a4 a5 a6 a7 t3 t4 t5 t6 F fc m)) ->
      forall (fuel : nat) is uc w Aw s (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m,
      IINV m s fc is uc w Aw -> il_total_out za is + (Z.of_nat fuel) * N <= 2^62 ->
      implM psegs (mbind (iloopL lops za fuel N cc is w) K) s POSTQ
            (TIST 0x160bc x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m).
    Proof.
      destruct ZOK as (_ & _ & _ & _ & _ & INFL & _).
      intros A K POSTQ KDONE KERR. induction fuel as [|f IH]; intros until m; intros INV BO.
      { cbn [iloopL unreachable lops Target.ops]. unfold implM. rewrite mbind_munr. apply impl_ret_unr. }
      cbn [iloopL]. cbn [bind ret unreachable lib_malloc lops Target.ops].
      pose proof INV as (EI & (no & ao & p1 & p2 & PUB) & TI & TO & ZR & UARR & ULEN).
      pose proof EI as ((errv & ENV) & (j0 & FRL) & FRH & ZH & CARR & PRES & ESO & EFA & FRM).
      pose proof ENV as (HP & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof N_facts as NF. destruct cc_facts as (CCL' & CCR & _).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E144 : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; lia). rewrite E144 in ST.
      assert (FN : il_total_out za is + N <= 2^62) by (rewrite Nat2Z.inj_succ in BO; nia).
      unfold zs_pub in PUB. cbv beta delta [MallocRep.wz] in PUB |- *.
      assert (LCC : Z.of_nat (length (to_bytes cc)) = N) by (rewrite to_bytes_len; exact CCL').
      assert (LUC : Z.of_nat (length (to_bytes uc)) = N) by (rewrite to_bytes_len; exact ULEN).
      pose proof (munch_refl [(SS, SS + 48)] m) as MUz. pose proof (wmono_refl psegs m) as WMz.
      unfold FRHI in *.
      unfold implM. iprefix.
      zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
      assert (LBZR : forall b, In b (iblocksL w Aw pst As) -> rblock_range (blk_addr b) (blk_size b)).
      { intros b Hb. apply (HBR _ _ _ _ HP). apply in_or_app. left. exact Hb. }
      assert (ZR2 : zri R m2 SS (iblocksL w Aw pst As) is) by (eapply zri_pub; [exact LBZR| exact ZR| exact MUz| exact WMz]).
      assert (ENV2 : lx_env m2 s (iblocksL w Aw pst As) LB (Z_to_bv 64 (usp + -144)) tp B lo errv canary).
      { eapply (lx_env_munch [(SS, SS + 48)] m m2); [exact HFRAME| exact ENV| exact MUz| exact WMz| exact MI| rewrite E144; exact ST| rewrite E144; lia| |].
        - constructor; [left; cbn [fst]; lia| constructor].
        - intros a Ha. cbn [outside]. lia. }
      assert (EI2 : EINV m2 s fc (iblocksL w Aw pst As)).
      { unfold EINV, FRLO, FRHI. cbv beta delta [MallocRep.wz].
        split; [exists errv; exact ENV2|]. split; [exists j0; exact FRL|]. split; [exact FRH|]. split; [exact ZH|]. split; [exact CARR|].
        split. { eapply lx_pres_trans; [exact PRES|]. eapply pres_munch; [exact MUz| exact WMz|]. intros a Ha. cbn [outside]. lia. }
        split; [exact ESO|]. split; [exact EFA| exact FRM]. }
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POSTQ msx) end.
      apply implM_bind_assoc. eapply implM_bind.
      { assert (SPM : (usp + -144) mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
        eapply INFL with (S := SS) (C := C) (U := U) (cl := N) (size := N) (comprc := cc) (uc := uc) (is := is) (w := w) (Aw := Aw) (sp_ := pst) (As := As)
                         (p1 := p1) (p2 := p2) (lo := lo) (B := B) (errv := errv) (canary := canary);
          unfold strm_in_frame, Z_INFLATE_STACK, RMALLOC_STACK, ZS_SIZEOF; rewrite ?E144;
          [ nm 1 ltac:(exact ENV2)
          | nm 2 ltac:(unfold zs_pub; cbv beta delta [MallocRep.wz]; exact PUB)
          | nm 3 ltac:(exact ZR2)
          | nm 4 ltac:(exists (cp, C, N); split; [exact INC| split; reflexivity])
          | nm 5 ltac:(exact CARR) | nm 6 ltac:(exact CCL') | nm 7 ltac:(exact CCR)
          | nm 8 ltac:(exists (up, U, N); split; [exact INU| split; reflexivity])
          | nm 9 ltac:(exact UARR) | nm 10 ltac:(exact ULEN) | nm 11 ltac:(lia) | nm 12 ltac:(lia) | nm 13 ltac:(lia) | nm 14 ltac:(lia) | nm 15 ltac:(lia) | nm 16 ltac:(exact CU)
          | nm 17 ltac:(repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia)
          | nm 18 ltac:(lia) | nm 19 ltac:(exact SPM) | nm 20 ltac:(exact FRM) | nm 21 ltac:(reflexivity) | nm 22 ltac:(reflexivity) ]. }
      cbv beta. intros r s' ms' PO. unfold inflate_postL in PO. cbv zeta.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F' & fc' & m' & p1' & p2' & Aw' & ni' & ai' & PO).
      unfold i_okL, i_windowL, i_wantsbL in PO. unfold i_callL, i_wantsL.
      pose proof (zo_ircL za the_zapiL_ok (zdrop (il_total_in za is) cc) is N
                    (if il_wants_window za (zdrop (il_total_in za is) cc) is N && match w with None => true | Some _ => false end
                     then match r with Some _ => true | None => false end else true)) as RCR.
      revert PO RCR.
      destruct (il_inflate za (zdrop (il_total_in za is) cc) is N
                 (if il_wants_window za (zdrop (il_total_in za is) cc) is N && match w with None => true | Some _ => false end
                  then match r with Some _ => true | None => false end else true)) as [[[is' c] bs] rc] eqn:EINF.
      cbn [snd]. intros (-> & LPE & AWE & -> & BSN & PUB' & NIE & TOE & ZR' & UARR') RCR. unfold cint in RCR.
      replace (ret_pc (Z_to_bv 64 0x160d0)) with (Z_to_bv 64 0x160d0) by (symmetry; rpc).
      set (w' := if il_wants_window za (zdrop (il_total_in za is) cc) is N && match w with None => true | Some _ => false end then r else w) in *.
      assert (BS0 : 0 <= zlength bs) by (unfold zlength; lia).
      pose proof (einv_step _ _ _ _ _ _ _ _ _ EI2 (or_introl eq_refl) LPE) as EI'.
      assert (INVw : IINVw m' s' fc' is' (zstore uc 0 bs) w' Aw').
      { unfold IINVw. split; [exact EI'|]. split; [exists ni', ai', (U + zlength bs), (N - zlength bs), p1', p2'; exact PUB'|].
        split; [exact ZR'|]. split; [exact UARR'|]. rewrite zstore_length. exact ULEN. }
      destruct (wint_cases rc RCR) as [[RC0 ERC]|[RC0 ERC]].
      - destruct (rc =? Z_STREAM_END) eqn:RC1.
        +
          apply Z.eqb_eq in RC1. apply implM_ret_bind. pose proof (TOE (or_intror RC1)) as TOQ.
          unfold implM. iprefix. cbv beta delta [MallocRep.wz].
          zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ERC in KB; unfold Z_STREAM_END in *; lia|].
          zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; unfold Z_STREAM_END in *; rewrite ?unsigned_lit in KC by lia; lia|].
          apply evt_done. subst rc. apply (KDONE is' (zstore uc 0 bs) w' Aw' s' _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m'); [exact INVw| lia].
        + apply Z.eqb_neq in RC1. destruct (rc =? Z_OK) eqn:RC2.
          *
            apply Z.eqb_eq in RC2. pose proof (NIE RC2) as (ENI & EAI & TIR). pose proof (TOE (or_introl RC2)) as TOQ.
            unfold implM. iprefix. cbv beta delta [MallocRep.wz].
            zstep. if_cases KB; zify_cond KB; [| exfalso; rewrite ERC in KB; unfold Z_OK in *; lia].
            assert (INVx : IINV m' s' fc' is' (zstore uc 0 bs) w' Aw').
            { unfold IINV. split; [exact EI'|]. split; [exists (U + zlength bs), (N - zlength bs), p1', p2'; rewrite <- ENI, <- EAI; exact PUB'|].
              split; [exact TIR|]. split; [lia|]. split; [exact ZR'|]. split; [exact UARR'|]. rewrite zstore_length. exact ULEN. }
            apply evt_done. apply (IH is' (zstore uc 0 bs) w' Aw' s' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' INVx). rewrite TOQ. nia.
          *
            apply Z.eqb_neq in RC2. apply implM_ret_bind.
            unfold implM. iprefix. cbv beta delta [MallocRep.wz].
            zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ERC in KB; unfold Z_OK in *; lia|].
            zstep. zstep. zstep. if_cases KC; zify_cond KC; [| exfalso; unfold Z_STREAM_END in *; rewrite ?unsigned_lit in KC by lia; lia].
            apply evt_done. apply (KERR rc is' (zstore uc 0 bs) w' Aw' s' _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m'); [exact INVw| lia].
      -
        assert (RC1 : rc <> Z_STREAM_END) by (unfold Z_STREAM_END; lia). assert (RC2 : rc <> Z_OK) by (unfold Z_OK; lia).
        replace (rc =? Z_STREAM_END) with false by (symmetry; apply Z.eqb_neq; exact RC1). replace (rc =? Z_OK) with false by (symmetry; apply Z.eqb_neq; exact RC2).
        apply implM_ret_bind.
        unfold implM. iprefix. cbv beta delta [MallocRep.wz].
        zstep. if_cases KB; zify_cond KB; [exfalso; rewrite ERC in KB; lia|].
        zstep. zstep. zstep. if_cases KC; zify_cond KC; [| exfalso; rewrite ERC in KC; lia].
        apply evt_done. apply (KERR rc is' (zstore uc 0 bs) w' Aw' s' _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m'); [exact INVw| lia].
    Qed.

    Lemma einv_print : forall m m' s fc fc' OW,
      EINV m s fc OW -> munch [(lo, usp + -144); (RSTDERR, RSTDERR + 232)] m m' -> wmono psegs m m' -> mem_inv psegs m' ->
      stk psegs m' lo (usp + -144) -> stderr_wfile0 m' -> frm0 fc' -> EINV m' s fc' OW.
    Proof.
      intros m m' s fc fc' OW ((errv & ENV) & (j0 & FRL) & FRH & ZH & CARR & PRES & ESO & EFA & FRM) MU WM MI' ST' SEW' FRM'.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG. pose proof N_facts as NF.
      assert (E144 : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; lia).
      pose proof CR as (C0 & _ & _ & CC & CI). destruct cc_facts as (CCL' & _ & _).
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
      unfold EINV. split.
      { exists errv. eapply (lx_env_munch_se _ m m'); [exact HFRAME| exact ENV| exact MU| exact WM| exact MI'| rewrite E144; exact ST'| rewrite E144; lia| | | exact SEW'].
        - constructor; [left; cbn [fst]; lia|]. constructor; [| constructor]. right; left. cbn [fst snd].
          unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        - intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia. }
      split. { exists j0. eapply rw_cells_agree; [exact AG| exact FRL|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split. { unfold FRHI in *. eapply rw_cells_agree; [exact AG| exact FRH|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split. { eapply rw_cells_agree; [exact AG| exact ZH|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split. { eapply u8arr_agree; [exact AG| exact CARR|]. intros a Ha. rewrite to_bytes_len in Ha. cbn [outside]. unfold zlength in *. lia. }
      split. { eapply lx_pres_trans; [exact PRES|]. eapply pres_munch; [exact MU| exact WM|]. intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia. }
      split; [exact ESO|]. split; [exact EFA| exact FRM'].
    Qed.

    Notation POST := (rtest_large_inflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB U N lo B canary m0).

    Lemma ti_tail : forall s LK (x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m (scs : list cell),
      EINV m s fc LK -> rw_cells psegs m SS scs -> cells_size scs = 112%nat -> (length LK <= 2)%nat ->
      evt psegs (POST tt s)
        (MS (mkR x1 (wz (usp + -144)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (wz 0x16104) fc None m (seg_rom psegs)).
    Proof.
      intros until scs. intros ((errv & ENV) & (j0 & FRL) & FRH & _ & _ & PRES & ESO & EFA & FRM) STR SZc LKL.
      pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E144 : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; lia). rewrite E144 in ST.
      unfold FRHI in FRH. cbv beta delta [MallocRep.wz].
      do 5 zstep.
      assert (FALL : rw_cells psegs m (usp + -144) ([CB 8 j0] ++ scs ++ [C8 S1; C8 S0; C8 ra])).
      { apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [exact FRL|]. apply (proj2 (rw_cells_app psegs _ _ _ _)).
        cbn [cells_size csize Nat.add]. rewrite SZc. split; [eapply rw_cells_addr_eq; [exact STR| lia]| eapply rw_cells_addr_eq; [exact FRH| lia]]. }
      eapply stk_release in FALL; [| exact ST| lia]. rewrite !cells_size_app, SZc in FALL. cbn [cells_size csize Nat.add] in FALL.
      replace (usp + -144 + Z.of_nat (8 + (112 + 24))) with usp in FALL by lia.
      zstep.
      apply evt_done. unfold rtest_large_inflate_post.
      do 15 eexists. exists F, fc, m, LK. split; [reflexivity|]. split; [| exact LKL].
      unfold lx_post_env. split; [exists errv; eapply lx_env_sp; [exact ENV| exact FALL| exact SPB]|].
      split; [exact FRM|]. split; [exact PRES|]. split; [exact ESO| exact EFA].
    Qed.

    Lemma wint_mod32 : forall rc, - 2^31 <= rc < 2^31 -> bv_unsigned (wint rc) mod 2^32 = rc mod 2^32.
    Proof.
      intros rc Hrc. unfold wint, wz. rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
      change (2^64) with (2^32 * 2^32). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
    Qed.

    Lemma stream_cells : forall m LBz is, zri R m SS LBz is ->
      (exists ni ai ti no ao to p1 p2, rw_cells psegs m SS (zs_pub ni ai ti no ao to p1 p2)) ->
      exists scs, rw_cells psegs m SS scs /\ cells_size scs = 112%nat.
    Proof.
      intros m LBz is ZR (ni & ai & ti & no & ao & to & p1 & p2 & PUB). destruct (zri_stream R _ _ _ _ ZR) as [j PRIV].
      exists (zs_pub ni ai ti no ao to p1 p2 ++ [CB 64 j]). split; [| reflexivity].
      apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [exact PUB|]. eapply rw_cells_addr_eq; [exact PRIV|]. unfold ZS_PUB. cbn. lia.
    Qed.

    Lemma ti_check : forall (An : Z) (name : list Z) (rc : Z) (pc : Z) s LK (x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m (scs : list cell),
      harness_name An name -> - 2^31 <= rc < 2^31 ->
      EINV m s fc LK -> rw_cells psegs m SS scs -> cells_size scs = 112%nat -> (length LK <= 2)%nat ->
      (forall (Q : machine_state -> Prop) (mm : mem), lx_statics mm -> mem_inv psegs mm ->
         evt psegs Q (MS (mkR (wz 0x16184) (wz (usp + -144)) gp tp t0 t1 t2 s0v s1v (wz RSTDERR) (wz A_FMT_err) (wz An) (wint rc) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                         F (wz 0x2279c) fc None mm (seg_rom psegs)) ->
         evt psegs Q (MS (mkR x1 (wz (usp + -144)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                         F (wz pc) fc None mm (seg_rom psegs))) ->
      implM psegs (stderr_fprintf [msg_err name rc]) s POST
        (MS (mkR x1 (wz (usp + -144)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (wz pc) fc None m (seg_rom psegs)).
    Proof.
      intros until scs. intros HN RCR EI STR SZc LKL LOAD.
      pose proof EI as ((errv & ENV) & _ & _ & _ & _ & _ & _ & _ & FRM).
      pose proof ENV as (_ & LXS & _ & SEW & SSP & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E144 : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; lia).
      unfold implM. iprefix. eapply LOAD; [exact LXS| exact MI|]. cbv beta delta [MallocRep.wz].
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
      eapply (Printf_pieces.implM_post_evt psegs).
      { eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s lo canary An name rc);
          rewrite ?E144;
          [ exact SEW | reflexivity | reflexivity | reflexivity | exact HN | exact RCR | apply wint_mod32; exact RCR
          | first [exact ST| rewrite E144 in ST; exact ST] | unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | lia
          | exact SSP | exact MI | exact FRM ]. }
      cbv beta. intros [] s3 ms3 PO3.
      destruct PO3 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FREG3 & ST3 & SEW3 & SSP3 & ->).
      rewrite E144 in MU3, ST3.
      replace (ret_pc (Z_to_bv 64 0x16184)) with (Z_to_bv 64 0x16184) by (symmetry; rpc).
      pose proof (einv_print _ _ _ _ fc3 _ EI MU3 WM3 MI3 ST3 SEW3 FRM3) as EI3.
      assert (STR3 : rw_cells psegs m3 SS scs).
      { eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU3 WM3)| exact STR|]. intros a Ha. rewrite SZc in Ha. cbn [outside]. lia. }
      zstep.
      eapply ti_tail; eassumption.
    Qed.

    Definition KONT (r : @iloopL_res bptr za) : M PState unit :=
      match r with
      | ILLerr rc w => stderr_fprintf [msg_err NL_inflate rc]
      | ILLdone is w =>
          mbind (Target.lib_free_opt raw_free w) (fun _ => mbind (Target.lib_free_opt raw_free (Some pst)) (fun _ =>
            if il_end za is =? Z_OK
            then (if il_total_out za is =? 2 * N + diff then mret tt else stderr_fprintf [msgl_bad (il_total_out za is)])
            else stderr_fprintf [msg_err NL_inflateEnd (il_end za is)]))
      end.

    Lemma iblocksL_len : forall w Aw, (length (iblocksL w Aw pst As) <= 2)%nat.
    Proof. intros [q|] Aw; cbn; lia. Qed.

    Lemma ti_err : forall rc is uc w Aw s (x1 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m, IINVw m s fc is uc w Aw ->
      - 2^31 <= rc < 2^31 ->
      implM psegs (KONT (ILLerr rc w)) s POST (TIST 0x16140 x1 t0 t1 t2 (wz 1) a1 a2 (wint rc) a4 a5 a6 a7 t3 t4 t5 t6 F fc m).
    Proof.
      intros until m. intros (EI & (ni & ai & no & ao & p1 & p2 & PUB) & ZR & _) RCR. cbn [KONT].
      destruct (stream_cells _ _ _ ZR ltac:(do 8 eexists; exact PUB)) as (scs & STR & SZc).
      eapply (ti_check AL_N_INFLATE NL_inflate rc 0x16140); try eassumption.
      - exists [102; 105; 108]. unfold harness_names. cbn [In]. do 6 right. left. reflexivity.
      - apply iblocksL_len.
      - intros Q mm (GS1 & GS2) MIm KK. unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2 |- *.
        do 9 zstep. exact KK.
    Qed.

    Lemma ti_done : forall is uc w Aw s (x1 t0 t1 t2 a1 a2 a4 a5 a6 a7 t3 t4 t5 t6 : word) F fc m, IINVw m s fc is uc w Aw ->
      0 <= il_total_out za is <= 2^62 ->
      implM psegs (KONT (ILLdone is w)) s POST (TIST 0x160e0 x1 t0 t1 t2 (wz 1) a1 a2 (wint Z_STREAM_END) a4 a5 a6 a7 t3 t4 t5 t6 F fc m).
    Proof.
      destruct ZOK as (_ & _ & _ & _ & _ & _ & IEND).
      intros until m. intros (EI & (ni & ai & no & ao & p1 & p2 & PUB) & ZR & UARR & ULEN) TOR. cbn [KONT].
      pose proof EI as ((errv & ENV) & _ & _ & _ & _ & _ & _ & _ & FRM).
      pose proof ENV as (HP & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof N_facts as NF.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E144 : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; lia).
      assert (SPM : (usp + -144) mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
      unfold implM. iprefix. cbv beta delta [MallocRep.wz].
      zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
      eapply implM_bind2.
      { eapply IEND with (S := SS) (is := is) (w := w) (Aw := Aw) (sp_ := pst) (As := As) (lo := lo) (B := B) (errv := errv) (canary := canary);
          unfold strm_in_frame, Z_INFLATEEND_STACK, RFREE_STACK, ZS_SIZEOF; rewrite ?E144;
          [ exact ENV | exact PUB | exact ZR
          | repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia
          | lia | exact SPM | exact FRM | reflexivity ]. }
      cbv beta. intros [] s6 ms6 PO6. unfold inflateEnd_postL in PO6.
      destruct PO6 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F6 & fc6 & m6 & -> & LPE6 & -> & (js & STR6)).
      replace (ret_pc (Z_to_bv 64 0x160e8)) with (Z_to_bv 64 0x160e8) by (symmetry; rpc).
      pose proof (einv_step _ _ _ _ _ _ _ _ _ EI (or_intror eq_refl) LPE6) as EI6.
      pose proof EI6 as ((errv7 & ENV7) & (j0 & FRL6) & FRH6 & ZH6 & CARR6 & _ & _ & _ & FRM6).
      pose proof ENV7 as (_ & (GS1 & GS2) & _ & SEW6 & SSP6 & _ & _ & _ & ST6 & _ & _ & _ & _ & MI6). rewrite E144 in ST6.
      pose proof (zo_iendL za the_zapiL_ok is) as RCRE. unfold cint in RCRE.
      destruct (Z.eq_dec (il_end za is) Z_OK) as [EOK|ENZ].
      2:{ replace (il_end za is =? Z_OK) with false by (symmetry; apply Z.eqb_neq; exact ENZ).
          unfold implM. iprefix.
          zstep; if_cases KB; zify_cond KB; [| exfalso; destruct (wint_cases _ RCRE) as [[RC0 ERC]|[RC0 ERC]]; rewrite ERC in KB; unfold Z_OK in *; lia].
          apply evt_done.
          lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s6 POST msx) end.
          eapply (ti_check A_N_INFLATEEND NL_inflateEnd (il_end za is) 0x16160 s6 []); [exists [105; 110; 118; 97; 108; 105; 100]; unfold harness_names; cbn [In]; do 7 right; left; reflexivity| exact RCRE| exact EI6| exact STR6| reflexivity| cbn; lia|].
          intros Q mm (GT1 & GT2) MIm KK. unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GT1, GT2. cbv beta delta [MallocRep.wz] in GT1, GT2 |- *.
          do 9 zstep. exact KK. }
      rewrite EOK. replace (Z_OK =? Z_OK) with true by reflexivity. change (wint Z_OK) with (Z_to_bv 64 0).
      unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2.
      pose proof STR6 as PUB6. unfold zs_pub in PUB6. cbn [app] in PUB6. cbv beta delta [MallocRep.wz] in PUB6.
      destruct (Z.eq_dec (il_total_out za is) (2 * N + diff)) as [ETO|NTO].
      + replace (il_total_out za is =? 2 * N + diff) with true by (symmetry; apply Z.eqb_eq; exact ETO).
        unfold implM. iprefix.
        zstep. if_false.
        zstep. zstep. zstep. zstep. zstep. zstep. if_cases KD; zify_cond KD.
        { exfalso. apply KD. rewrite ETO. unfold MallocRep.wz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
          change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite !Z.mod_small by lia. lia. }
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s6 POST msx) end.
        apply implM_ret. eapply (ti_tail s6 []); [exact EI6| exact STR6| reflexivity| cbn; lia].
      + replace (il_total_out za is =? 2 * N + diff) with false by (symmetry; apply Z.eqb_neq; exact NTO).
        unfold implM. iprefix.
        zstep. if_false.
        zstep. zstep. zstep. zstep. zstep. zstep. if_cases KD; zify_cond KD.
        2:{ exfalso. apply NTO. rewrite KD. unfold MallocRep.wz. rewrite unsigned_lit by lia. rewrite Z.shiftl_mul_pow2 by lia.
            change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. rewrite !Z.mod_small by lia. lia. }
        zstep. zstep. zstep. zstep. zstep. zstep.
        apply evt_done.
        lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s6 POST msx) end.
        eapply (Printf_pieces.implM_post_evt psegs).
        { eapply (BAD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F6 fc6 m6 s6 lo canary (il_total_out za is));
            rewrite ?E144;
            [ exact SEW6 | reflexivity | reflexivity | lia | unfold MallocRep.wz; rewrite unsigned_lit by lia; reflexivity
            | exact ST6 | unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | lia
            | exact SSP6 | exact MI6 | exact FRM6 ]. }
        cbv beta. intros [] s7 ms7 PO7.
        destruct PO7 as (y0 & y1 & y2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & y3 & y4 & y5 & y6 & F7 & fc7 & m7 & -> & MU7 & WM7 & MI7 & FRM7 & FREG7 & ST7 & SEW7 & SSP7 & ->).
        rewrite E144 in MU7, ST7.
        replace (ret_pc (Z_to_bv 64 0x161a0)) with (Z_to_bv 64 0x161a0) by (symmetry; rpc).
        pose proof (einv_print _ _ _ _ fc7 _ EI6 MU7 WM7 MI7 ST7 SEW7 FRM7) as EI7.
        assert (STR7 : rw_cells psegs m7 SS ([C8 (wz ni); C4 (wz ai); CB 4 p1; C8 (wz (il_total_in za is)); C8 (wz no); C4 (wz ao); CB 4 p2; C8 (wz (il_total_out za is))] ++ [CB 64 js])).
        { eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU7 WM7)| exact STR6|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
        zstep.
        eapply (ti_tail s6 []); [exact EI7| exact STR7| reflexivity| cbn; lia].
    Qed.
  End Inv.

  Lemma frame_split_iL : forall m (j0 p1 jti jno jao p2 jto jm js jr : list byte),
    rw_cells psegs m (usp + -144) [CB 8 j0; C8 (Z_to_bv 64 C); C4 (Z_to_bv 64 N); CB 4 p1; CB 8 jti; CB 8 jno; CB 4 jao; CB 4 p2; CB 8 jto;
                                   CB 8 jm; CB 8 js; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 24 jr;
                                   C8 S1; C8 S0; C8 ra] ->
    FRLO m /\ FRHI m
    /\ exists ti no ao to (jmsg jstate : word),
         rw_cells psegs m SS (zs_pub C N ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jr]).
  Proof.
    intros m j0 p1 jti jno jao p2 jto jm js jr FR.
    apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FR. destruct FR as [FRL FR].
    apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_;_;_;_;_;_;_;_;_;_;_] _)) in FR. destruct FR as [FRS FRH].
    cbn [cells_size csize Nat.add] in FRS, FRH.
    replace (usp + -144 + Z.of_nat 8) with SS in FRS, FRH by lia. replace (SS + Z.of_nat 112) with (usp + -24) in FRH by lia.
    split; [exists j0; exact FRL|]. split; [exact FRH|].
    pose proof FRS as [[WFS _] _]. cbn [cells_wf cell_wf] in WFS.
    destruct WFS as (_ & _ & L1 & L2 & L2b & L3 & L4 & L5 & L6 & L7 & _ & _ & _ & L8 & _).
    destruct (le8_of_bytes _ L2) as (ti & _ & Eti). destruct (le8_of_bytes _ L2b) as (no & _ & Eno). destruct (le4_of_bytes _ L3) as (ao & _ & Eao).
    destruct (le8_of_bytes _ L5) as (to & _ & Eto).
    destruct (le8_of_bytes _ L6) as (zmsg & _ & Emsg). destruct (le8_of_bytes _ L7) as (zst & _ & Est).
    exists ti, no, ao, to, (Z_to_bv 64 zmsg), (Z_to_bv 64 zst).
    eapply rw_cells_recast; [exact FRS| |].
    - unfold zs_pub. cbn [app cells_wf cell_wf]. repeat split; assumption.
    - unfold zs_pub, wz. cbn [app cells_bytes cbytes]. rewrite Eti, Eno, Eao, Eto, Emsg, Est. reflexivity.
  Qed.

  Notation POSTM s0 m0 := (rtest_large_inflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB U N lo B canary m0).

  Theorem ti_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (s : PState) (errv : word) (uc0 : list Z),
    lx_env m0 s [] LB sp tp B lo errv canary -> rw_cells psegs m0 ZHS [C4 (wz diff)] ->
    u8arr psegs m0 C (to_bytes cc) -> u8arr psegs m0 U (to_bytes uc0) -> zlength uc0 = N -> frm0 fc ->
    implM psegs (test_large_inflateM lops za N comprc diff) s (POSTM s m0)
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz C) (wz N) (wz U) (wz N) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz ZHL_TEST_INFLATE) fc None m0 (seg_rom psegs)).
  Proof.
    intros until uc0. intros ENV0 DIF0 CARR0 UARR0 ULEN0 FRM.
    pose proof ENV0 as (HP0 & _ & _ & _ & _ & _ & _ & _ & ST0 & _ & _ & _ & _ & MI0).
    pose proof N_facts as NF. destruct cc_facts as (CCL' & CCR & ECC).
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
    unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    destruct ZOK as (_ & _ & _ & _ & IINIT & _).
    unfold test_large_inflateM. cbn [bind ret lops Target.ops out_stderr lib_malloc lib_free].
    unfold ZHL_TEST_INFLATE. cbv beta delta [MallocRep.wz] in DIF0 |- *.
    assert (LCC : Z.of_nat (length (to_bytes cc)) = N) by (rewrite to_bytes_len; exact CCL').
    assert (LU0 : Z.of_nat (length (to_bytes uc0)) = N) by (rewrite to_bytes_len; exact ULEN0).
    pose proof (munch_refl [(usp + -144, usp)] m0) as MU. pose proof (wmono_refl psegs m0) as WM.
    unfold implM. iprefix.
    zstep. carve_frame 144%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 144 junk [] [8; 8; 4; 4; 8; 8; 4; 4; 8; 8; 8; 8; 8; 8; 24; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 3 zstep. do 2 zstep. zs. zstep. zstep. zs. zs. do 4 zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (frame_split_iL m1 _ _ _ _ _ _ _ _ _ _ FR) as (FRL1 & FRH1 & (ti & no & ao & to & jmsg & jstate & FRS1)). clear FR.
    assert (SPM : (usp + -144) mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
    assert (E144 : bv_unsigned (Z_to_bv 64 (usp + -144)) = usp + -144) by (apply unsigned_lit; lia).
    assert (ENV1 : lx_env m1 s [] LB (Z_to_bv 64 (usp + -144)) tp B lo errv canary).
    { eapply (lx_env_munch [(usp + -144, usp)] m0 m1); [exact HFRAME| exact ENV0| exact MU| exact WM| assumption| rewrite E144; assumption| rewrite E144; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (DIF1 : rw_cells psegs m1 ZHS [C4 (Z_to_bv 64 diff)]) by (first [exact DIF0| eapply rw_cells_agree; [exact AG1| exact DIF0| intros a Ha; cbn in Ha; cbn [outside]; lia]]).
    assert (CARR1 : u8arr psegs m1 C (to_bytes cc)) by (first [exact CARR0| eapply u8arr_agree; [exact AG1| exact CARR0| intros a Ha; rewrite LCC in Ha; cbn [outside]; lia]]).
    assert (UARR1 : u8arr psegs m1 U (to_bytes uc0)) by (first [exact UARR0| eapply u8arr_agree; [exact AG1| exact UARR0| intros a Ha; rewrite LU0 in Ha; cbn [outside]; lia]]).
    assert (PRES1 : lx_pres LB usp XX m0 m1) by (eapply pres_munch; [exact MU| exact WM|]; intros a Ha; cbn [outside]; lia).
    assert (EI1 : EINV m0 s m1 s fc []).
    { unfold EINV. cbv beta delta [MallocRep.wz]. split; [exists errv; exact ENV1|]. split; [exact FRL1|]. split; [exact FRH1|]. split; [exact DIF1|]. split; [exact CARR1|].
      split; [exact PRES1|]. split; [reflexivity|]. split; [reflexivity| exact FRM]. }
    clear DIF0 CARR0 UARR0 AG1 MU WM.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s (POSTM s m0) msx) end.
    eapply implM_bind.
    { eapply IINIT with (S := SS) (lo := lo) (B := B) (errv := errv) (canary := canary);
        [ exact ENV1 | exact FRS1
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E144; repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia
        | rewrite E144; unfold Z_INFLATEINIT_STACK, RMALLOC_STACK; lia | rewrite E144; exact SPM | exact FRM
        | f_equal; lia | reflexivity | reflexivity ]. }
    cbv beta. intros r s2 ms2 PO. unfold inflateInit_postL in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & PO).
    replace (ret_pc (Z_to_bv 64 0x160b8)) with (Z_to_bv 64 0x160b8) by (symmetry; rpc).
    destruct r as [pst|].
    2:{
      destruct PO as (LPE2 & -> & (js & STR2)).
      pose proof (einv_step _ _ _ _ _ _ _ _ _ _ _ EI1 (or_intror eq_refl) LPE2) as EI2.
      change (wint Z_MEM_ERROR) with (Z_to_bv 64 18446744073709551612).
      unfold implM. iprefix. zstep. if_true. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s2 (POSTM s m0) msx) end.
      change (Z_to_bv 64 18446744073709551612) with (wint Z_MEM_ERROR).
      eapply (ti_check m0 s A_N_INFLATEINIT NL_inflateInit Z_MEM_ERROR 0x1611c s2 []);
        [exists [100; 101]; unfold harness_names; cbn [In]; do 5 right; left; reflexivity| unfold Z_MEM_ERROR; lia| exact EI2| exact STR2| reflexivity| cbn; lia|].
      intros Q mm (GS1 & GS2) MIm KK. unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2 |- *.
      do 10 zstep. exact KK. }
    destruct PO as (As & LPE2 & -> & PUB2 & ZR2).
    pose proof (einv_step _ _ _ _ _ _ _ _ _ _ _ EI1 (or_intror eq_refl) LPE2) as EI2.
    pose proof LPE2 as (_ & _ & LXP2 & _ & _). rewrite E144 in LXP2.
    assert (UARR2 : u8arr psegs m2 U (to_bytes uc0)).
    { eapply u8arr_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP2)| exact UARR1|]. intros a Ha. rewrite LU0 in Ha.
      eapply block_client; [exact INU| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    destruct (zo_iinitL za the_zapiL_ok) as [TI0 TO0].
    assert (INV2 : IINV m0 s pst As m2 s2 fc2 (il_init za) uc0 None 0).
    { unfold IINV. split; [exact EI2|]. split.
      { exists no, ao. eexists. eexists. rewrite TI0, TO0 in PUB2 |- *. replace (C + 0) with C by lia. replace (N - 0) with N by lia. exact PUB2. }
      split; [rewrite TI0; lia|]. split; [rewrite TO0; lia|]. split; [exact ZR2|]. split; [exact UARR2| exact ULEN0]. }
    change (wint Z_OK) with (Z_to_bv 64 0).
    unfold implM. iprefix. zstep. if_false. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s2 (POSTM s m0) msx) end.
    eapply (ti_loop m0 s pst As unit (KONT pst) _ (ti_done m0 s pst As) (ti_err m0 s pst As)); [exact INV2|].
    rewrite TO0, Z2Nat.id by (unfold ZIL_FUEL; lia). unfold ZIL_FUEL. clear - NF. nia.
  Qed.
End TI.

Theorem rtest_large_inflate_proof : forall R : zrepsL, zlib_okL R -> @check_err_stmt PState -> @bad_msg_stmt PState ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rtest_large_inflate_stmt.
Proof.
  intros R ZOK CHK BAD HFRAME HBR HND HBD. unfold rtest_large_inflate_stmt. intros until canary.
  intros ENV DIF DIFR SZ EN INC CARR CCL INU UARR ULEN NEQ LOSP SP16 FRM -> -> -> ->.
  pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & B63 & _ & LOC & LOG & _ & TP & _). cbn [app] in HP.
  pose proof (HBR _ _ _ _ HP INC) as CR. cbn [blk_addr blk_size fst snd] in CR.
  pose proof (HBR _ _ _ _ HP INU) as UR. cbn [blk_addr blk_size fst snd] in UR.
  assert (CU : U + N <= C \/ C + N <= U).
  { pose proof (HBD _ _ _ _ _ HP INU INC) as D. cbn [blk_id blk_addr blk_size fst snd] in D. apply D. intros E. apply NEQ. symmetry. exact E. }
  assert (LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (HBR _ _ _ _ HP Hb)).
  unfold zhl_diff, ZHL_DIFF, ZH_STATICS in DIF.
  assert (CARR' : u8arr psegs m C (to_bytes (cc comprc))) by (unfold cc; rewrite to_bytes_norm8; exact CARR).
  eapply (ti_main R) with (cp := cp) (up := up) (errv := errv) (uc0 := uc); eassumption.
Qed.
End WithCeiling0.
