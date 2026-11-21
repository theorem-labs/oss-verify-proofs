(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP MonadX.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.MallocP Require Import RMallocRep RMallocTree RMalloc_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Spec Require Import Prelim STree Malloc Monad Stdio ZApi ZHarness ZTarget ZApiL ZHarnessL ZInstL ZTargetL Target Driver Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Layout Exit Startup_glue Printf_lib Printf_stdio_iface Stdio_iface F_fprintf Zlib_iface Driver_iface Drv_kit Zh_kit Zl_stderr Zl_iface.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Rnd.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import StoreFast.
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

(* [comment removed for export] *)
Lemma rev_append_rev' : forall (l l' : list Z), rev_append l l' = rev l ++ l'.
Proof. induction l as [|a l IH]; intros l'; cbn; [reflexivity|]. rewrite IH, <- app_assoc. reflexivity. Qed.

Lemma zlength_app' : forall (l1 l2 : list Z), zlength (l1 ++ l2) = zlength l1 + zlength l2.
Proof. intros. unfold zlength. rewrite length_app. lia. Qed.

Lemma zlength_zrepeat' : forall v n, 0 <= n -> zlength (zrepeat v n) = n.
Proof. intros. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.

Lemma upd_nat_app'' : forall (pre post : list Z) x b, upd_nat (pre ++ x :: post) (length pre) b = pre ++ b :: post.
Proof. induction pre as [|a pre IH]; intros post x b; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.
Lemma zstore_split'' : forall (bs pre post : list Z), (length bs <= length post)%nat ->
  zstore (pre ++ post) (Z.of_nat (length pre)) bs = pre ++ bs ++ skipn (length bs) post.
Proof.
  induction bs as [|b bs IH]; intros pre post HL; cbn; [reflexivity|].
  destruct post as [|x post]; [cbn in HL; lia|]. cbn in HL.
  unfold zupd. replace (Z.of_nat (length pre) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Nat2Z.id, upd_nat_app''.
  replace (pre ++ b :: post) with ((pre ++ [b]) ++ post) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length (pre ++ [b]))) by (rewrite length_app; cbn; lia).
  rewrite IH by lia. rewrite <- app_assoc. reflexivity.
Qed.
Lemma zstore_zrepeat0 : forall (bs : list Z) k, zlength bs <= k -> zstore (zrepeat 0 k) 0 bs = bs ++ zrepeat 0 (k - zlength bs).
Proof.
  intros bs k Hk. assert (B0 : 0 <= zlength bs) by (unfold zlength; lia).
  pose proof (zstore_split'' bs [] (zrepeat 0 k) ltac:(unfold zrepeat; rewrite repeat_length; unfold zlength in *; lia)) as E.
  cbn [app length Z.of_nat] in E. rewrite E. f_equal. unfold zrepeat.
  replace (Z.to_nat k) with (length bs + Z.to_nat (k - zlength bs))%nat by (unfold zlength in *; lia).
  rewrite repeat_app, skipn_app, skipn_all2 by (rewrite repeat_length; lia). rewrite repeat_length, Nat.sub_diag. reflexivity.
Qed.

Lemma firstn_all_app : forall (l : list Z) n, length l = n -> firstn n l = l.
Proof. intros l n <-. apply firstn_all. Qed.

Lemma Forall_skipn_ : forall (P : Z -> Prop) n (l : list Z), Forall P l -> Forall P (skipn n l).
Proof. induction n as [|n IH]; intros [|x l] H; cbn; auto. inversion H; subst. apply IH. assumption. Qed.

(* [comment removed for export] *)
Lemma wr_at_app_ : forall m a n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at psegs m a (n1 + n2) <-> wr_at psegs m a n1 /\ wr_at psegs m (a + n1) n2.
Proof.
  intros m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i) with (a + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i) with (a + n1 + (i - n1)) by lia. apply HB. lia.
Qed.
Lemma u8arr_app_ : forall m A (b1 b2 : list byte),
  u8arr psegs m A (b1 ++ b2) <-> u8arr psegs m A b1 /\ u8arr psegs m (A + Z.of_nat (length b1)) b2.
Proof.
  intros m A b1 b2. unfold u8arr. rewrite bytes_at_app, length_app, Nat2Z.inj_add, wr_at_app_ by lia. tauto.
Qed.
Lemma to_bytes_app : forall l1 l2, to_bytes (l1 ++ l2) = to_bytes l1 ++ to_bytes l2.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. symmetry. apply skipn_map. Qed.

(* [comment removed for export] *)
Lemma lit_bytes_at : forall m A f, mem_inv psegs m -> ro_bytes_b psegs A (zb f) = true -> 0 <= A -> A + zlength f <= 2^64 ->
  bytes_at psegs m A (zb f).
Proof.
  intros m A f MI RB H0 H1.
  pose proof (ro_cells_bytes_at psegs m A _ (ro_cells_image psegs m A (zb f) MI RB H0 ltac:(unfold zb; rewrite length_map; unfold zlength in H1; lia))) as Bq.
  cbn [cells_bytes cbytes] in Bq. rewrite app_nil_r in Bq. exact Bq.
Qed.

Lemma swrap32_id' : forall z, 0 <= z < 2^31 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. unfold bv_swrap. rewrite bv_wrap_small; [lia|].
  unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N (32 - 1)%N) with (2^31). change (2 ^ Z.of_N 32) with (2^32). lia.
Qed.
Lemma sx32_small : forall z, 0 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit by lia. apply swrap32_id'. exact Hz. Qed.

(* [comment removed for export] *)
Definition zidle (P : Prop) : Prop := P.
Ltac zidle1 H := let T := type of H in change (zidle T) in H.
(* [comment removed for export] *)
Ltac hba :=
  lazymatch goal with
  | |- rw_cells _ _ ?A _ => match goal with H : rw_cells _ _ A _ |- _ => exact H end
  | |- stk _ _ _ _ => match goal with H : stk _ _ _ _ |- _ => exact H end
  | |- mem_inv _ _ => match goal with H : mem_inv _ _ |- _ => exact H end
  end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Notation za := the_zapiL.

(* [comment removed for export] *)
Lemma comprL_eq : forall (x : dphL za) N, dp_n za x = zlength (rev (dp_orev za x)) -> 0 <= dp_n za x <= N ->
  comprL za x N = rev (dp_orev za x) ++ zrepeat 0 (N - dp_n za x).
Proof.
  intros x N E R. unfold comprL. rewrite rev_append_rev', app_nil_r, <- E.
  apply firstn_all_app. pose proof (zlength_app' (rev (dp_orev za x)) (zrepeat 0 (N - dp_n za x))) as L.
  rewrite zlength_zrepeat' in L by lia. unfold zlength in L, E. lia.
Qed.

(* [comment removed for export] *)
Lemma greedy_bytes : ro_bytes_b psegs AL_GREEDY (zb MSGL_GREEDY) = true. Proof. vm_compute. reflexivity. Qed.
Lemma finish_bytes : ro_bytes_b psegs AL_FINISH (zb MSGL_FINISH) = true. Proof. vm_compute. reflexivity. Qed.
Lemma greedy_range : Forall (fun c => 0 <= c < 256) MSGL_GREEDY. Proof. unfold MSGL_GREEDY. apply forall_range_b. vm_compute. reflexivity. Qed.
Lemma finish_range : Forall (fun c => 0 <= c < 256) MSGL_FINISH. Proof. unfold MSGL_FINISH. apply forall_range_b. vm_compute. reflexivity. Qed.

Section TD.
  Variable R : zrepsL.
  Hypothesis ZOK : zlib_okL R.
  Hypothesis CHK : @check_err_stmt PState.
  Hypothesis FWR : @fwrite_diag_stmt PState.
  Hypothesis HFRAME : RHEAP_frame_stmt.
  Hypothesis HBR : RHEAP_block_range_stmt.
  Hypothesis HND : RHEAP_blocks_nodup_stmt.
  Hypothesis HBD : RHEAP_blocks_disjoint_stmt.

  (* [comment removed for export] *)
  Variables (ra sp gp tp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Variables (LB : list block) (C U size N diff0 : Z) (cp up : bptr) (lo B : Z) (canary : word).
  Notation usp := (bv_unsigned sp).
  Notation SS := (usp + -152).              (* [comment removed for export] *)
  Notation ZHS := 0x3a6d0.                  (* [comment removed for export] *)
  Hypothesis INC : In (cp, C, N) LB.
  Hypothesis INU : In (up, U, N) LB.
  Hypothesis NEQ : cp <> up.
  Hypothesis SZ : 1 <= size <= ZL_MAX.
  Hypothesis EN : N = NofL size.
  Hypothesis DIFR0 : 0 <= diff0 < 2^32.
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

  Lemma N_facts : 103 <= N <= 1572964.
  Proof. rewrite EN. unfold NofL, ZL_MAX in *. lia. Qed.

  Notation XX := [(C, C + N); LXW_ZH; LXW_STDERR].

  (* [comment removed for export] *)
  Definition FRLO (mm : mem) : Prop := exists j0 : list byte, rw_cells psegs mm (usp + -160) [CB 8 j0].
  Definition FRHI (mm : mem) : Prop := rw_cells psegs mm (usp + -40) [C8 S3; C8 S2; C8 S1; C8 S0; C8 ra].

  Lemma frame_split : forall m (j0 jp jm js jr : list byte),
    rw_cells psegs m (usp + -160) [CB 8 j0; CB 48 jp; CB 8 jm; CB 8 js; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 24 jr;
                                   C8 S3; C8 S2; C8 S1; C8 S0; C8 ra] ->
    FRLO m /\ FRHI m
    /\ exists ni ai ti no ao to p1 p2 (jmsg jstate : word),
         rw_cells psegs m SS (zs_pub ni ai ti no ao to p1 p2 ++ [C8 jmsg; C8 jstate; C8 (wz 0); C8 (wz 0); C8 (wz 0); CB 24 jr]).
  Proof.
    intros m j0 jp jm js jr FR.
    apply (proj1 (rw_cells_app psegs _ _ [_] _)) in FR. destruct FR as [FRL FR].
    apply (proj1 (rw_cells_app psegs _ _ [_;_;_;_;_;_;_] _)) in FR. destruct FR as [FRS FRH].
    cbn [cells_size csize Nat.add] in FRS, FRH.
    replace (usp + -160 + Z.of_nat 8) with SS in FRS, FRH by lia. replace (SS + Z.of_nat 112) with (usp + -40) in FRH by lia.
    split; [exists j0; exact FRL|]. split; [exact FRH|].
    pose proof FRS as [[WFS _] _]. cbn [cells_wf cell_wf] in WFS. destruct WFS as (L1 & L2 & L3 & _ & _ & _ & L4 & _).
    destruct (zs_pub_of_bytes _ L1) as (ni & ai & ti & no & ao & to & p1 & p2 & EB & WFP & _).
    destruct (le8_of_bytes _ L2) as (zmsg & _ & Emsg). destruct (le8_of_bytes _ L3) as (zst & _ & Est).
    exists ni, ai, ti, no, ao, to, p1, p2, (Z_to_bv 64 zmsg), (Z_to_bv 64 zst).
    eapply rw_cells_recast; [exact FRS| |].
    - apply cells_wf_app. split; [exact WFP|]. cbn [cells_wf cell_wf]. repeat split. exact L4.
    - rewrite cells_bytes_app, EB. cbn [cells_bytes cbytes]. rewrite Emsg, Est. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma client_inner : forall a, lx_client LB usp XX a -> lx_client LB (usp + -160) [(SS, SS + ZS_SIZEOF)] a.
  Proof.
    intros a [_ Hc]. split.
    - cbn [rin_ivs fst snd]. intros [Hi|[]]. unfold ZS_SIZEOF in Hi. destruct Hc as [Hc|[(b & Hb & Hr)|[Hc _]]]; [lia| |].
      + destruct (LBR b Hb) as (_ & _ & _ & BC & _). unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
      + unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *. lia.
    - destruct Hc as [Hc|[Hc|Hc]]; [left; lia| right; left; exact Hc| right; right; exact Hc].
  Qed.

  Lemma fr_lx : forall m m' (A : Z) cs, lx_pres LB (usp + -160) [(SS, SS + ZS_SIZEOF)] m m' -> rw_cells psegs m A cs ->
    usp + -160 <= A -> (A + Z.of_nat (cells_size cs) <= SS \/ SS + ZS_SIZEOF <= A) -> rw_cells psegs m' A cs.
  Proof.
    intros m m' A cs LXP H HA HD. eapply rw_cells_agree; [exact (agree_of_lx_pres _ _ _ _ _ LXP)| exact H|].
    intros a Ha. apply stack_client; [lia|]. cbn [rin_ivs fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma pres_munch : forall W m m', munch W m m' -> wmono psegs m m' ->
    (forall a, usp <= a \/ (0x29000 <= a < 0x5c000 /\ ~ stderr_addr a /\ ~ (ZHS <= a < ZHS + 16))
               \/ (a < lo /\ (a < 0x10000 \/ 0x5c000 <= a) /\ ~ (C <= a < C + N) /\ exists b, In b LB /\ blk_addr b <= a < blk_addr b + blk_size b) -> outside W a) ->
    lx_pres LB usp XX m m'.
  Proof.
    intros W m m' MU WM HW. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a [HX [Ha|[(b & Hb & Hr)|[Ha _]]]]; apply HW.
    - left. exact Ha.
    - right; right. destruct (LBR b Hb) as (_ & _ & _ & BC & BI). split; [lia|]. split; [lia|]. split; [| exists b; auto].
      intros Hc. apply HX. cbn [rin_ivs fst snd]. left. exact Hc.
    - right; left. split; [exact Ha|]. split.
      + intros Hs. apply HX. cbn [rin_ivs]. right; right; left. unfold LXW_STDERR, LX_STDERR_FILE, stderr_addr in *. cbn [fst snd]. lia.
      + intros Hz. apply HX. cbn [rin_ivs]. right; left. unfold LXW_ZH, ZH_STATICS in *. cbn [fst snd]. lia.
  Qed.

  (* [comment removed for export] *)
  Section Exits.
    Variables (m0 : mem) (s0 : PState).

    (* [comment removed for export] *)
    Definition EINV (m : mem) (s : PState) (fc : bv 32) (OW : list block) (cc : list Z) (dcur : Z) : Prop :=
      (exists errv, lx_env m s OW LB (Z_to_bv 64 (usp + -160)) tp B lo errv canary)
      /\ FRLO m /\ FRHI m /\ u8arr psegs m C (to_bytes cc) /\ zlength cc = N
      /\ rw_cells psegs m ZHS [C4 (wz dcur)] /\ 0 <= dcur < 2^32
      /\ lx_pres LB usp XX m0 m /\ ps_so s = ps_so s0 /\ ps_fa s = ps_fa s0 /\ frm0 fc.

    (* [comment removed for export] *)
    Lemma einv_print : forall m m' s fc fc' OW cc dcur,
      EINV m s fc OW cc dcur -> munch [(lo, usp + -160); (RSTDERR, RSTDERR + 232)] m m' -> wmono psegs m m' -> mem_inv psegs m' ->
      stk psegs m' lo (usp + -160) -> stderr_wfile0 m' -> frm0 fc' -> EINV m' s fc' OW cc dcur.
    Proof.
      intros m m' s fc fc' OW cc dcur ((errv & ENV) & (j0 & FRL) & FRH & CARR & CCL & ZH & DCR & PRES & ESO & EFA & FRM) MU WM MI' ST' SEW' FRM'.
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      pose proof CR as (C0 & _ & _ & CC & CI).
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
      unfold EINV. split.
      { exists errv. eapply (lx_env_munch_se _ m m'); [exact HFRAME| exact ENV| exact MU| exact WM| exact MI'| rewrite E160; exact ST'| rewrite E160; lia| | | exact SEW'].
        - constructor; [left; cbn [fst]; lia|]. constructor; [| constructor]. right; left. cbn [fst snd].
          unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        - intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia. }
      split. { exists j0. eapply rw_cells_agree; [exact AG| exact FRL|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split. { unfold FRHI in *. eapply rw_cells_agree; [exact AG| exact FRH|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split. { eapply u8arr_agree; [exact AG| exact CARR|]. intros a Ha. rewrite to_bytes_len in Ha. cbn [outside]. unfold zlength in *. lia. }
      split; [exact CCL|].
      split. { eapply rw_cells_agree; [exact AG| exact ZH|]. intros a Ha. cbn in Ha. cbn [outside]. lia. }
      split; [exact DCR|].
      split. { eapply lx_pres_trans; [exact PRES|]. eapply pres_munch; [exact MU| exact WM|]. intros a Ha. cbn [outside]. unfold stderr_addr in Ha. lia. }
      split; [exact ESO|]. split; [exact EFA| exact FRM'].
    Qed.

    Notation POST := (rtest_large_deflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB C N lo B canary m0).

    (* [comment removed for export] *)
    Lemma td_tail : forall s LK cc dcur (x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v t3 t4 t5 t6 : word) F fc m (scs : list cell),
      EINV m s fc LK cc dcur -> rw_cells psegs m SS scs -> cells_size scs = 112%nat -> (length LK <= 5)%nat ->
      evt psegs (POST (cc, dcur) s)
        (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (wz 0x16058) fc None m (seg_rom psegs)).
    Proof.
      intros until scs. intros ((errv & ENV) & (j0 & FRL) & FRH & CARR & CCL & ZH & DCR & PRES & ESO & EFA & FRM) STR SZc LKL.
      pose proof ENV as (_ & _ & _ & _ & _ & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia). rewrite E160 in ST.
      unfold FRHI in FRH. cbv beta delta [MallocRep.wz].
      do 7 zstep.
      assert (FALL : rw_cells psegs m (usp + -160) ([CB 8 j0] ++ scs ++ [C8 S3; C8 S2; C8 S1; C8 S0; C8 ra])).
      { apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [exact FRL|]. apply (proj2 (rw_cells_app psegs _ _ _ _)).
        cbn [cells_size csize Nat.add]. rewrite SZc. split; [eapply rw_cells_addr_eq; [exact STR| lia]| eapply rw_cells_addr_eq; [exact FRH| lia]]. }
      eapply stk_release in FALL; [| exact ST| lia]. rewrite !cells_size_app, SZc in FALL. cbn [cells_size csize Nat.add] in FALL.
      replace (usp + -160 + Z.of_nat (8 + (112 + 40))) with usp in FALL by lia.
      zstep.
      apply evt_done. unfold rtest_large_deflate_post. cbn [fst snd].
      do 15 eexists. exists F, fc, m, LK. split; [reflexivity|]. split; [| split; [exact LKL| split; [exact CARR| split; [exact CCL| split; [exact ZH| exact DCR]]]]].
      unfold lx_post_env. split; [exists errv; eapply lx_env_sp; [exact ENV| exact FALL| exact SPB]|].
      split; [exact FRM|]. split; [exact PRES|]. split; [exact ESO| exact EFA].
    Qed.

    Lemma wint_cases : forall rc, - 2^31 <= rc < 2^31 -> (0 <= rc /\ bv_unsigned (wint rc) = rc) \/ (rc < 0 /\ bv_unsigned (wint rc) = rc + 2^64).
    Proof.
      intros rc Hrc. unfold wint, wz. rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
      destruct (Z.lt_ge_cases rc 0) as [Ng|Ng]; [right| left]; (split; [lia|]).
      - symmetry. apply (Z.mod_unique_pos _ _ (-1)); lia.
      - apply Z.mod_small. lia.
    Qed.

    Lemma wint_mod32 : forall rc, - 2^31 <= rc < 2^31 -> bv_unsigned (wint rc) mod 2^32 = rc mod 2^32.
    Proof.
      intros rc Hrc. unfold wint, wz. rewrite unsigned_lit by (apply Z.mod_pos_bound; lia).
      change (2^64) with (2^32 * 2^32). rewrite Z.rem_mul_r by lia. rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma td_check : forall (An : Z) (name : list Z) (rc : Z) (pc : Z) s LK cc dcur
        (x1 t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v t3 t4 t5 t6 : word) F fc m (scs : list cell),
      harness_name An name -> - 2^31 <= rc < 2^31 ->
      EINV m s fc LK cc dcur -> rw_cells psegs m SS scs -> cells_size scs = 112%nat -> (length LK <= 5)%nat ->
      (forall (Q : machine_state -> Prop) (mm : mem), lx_statics mm -> mem_inv psegs mm ->
         evt psegs Q (MS (mkR (wz 0x16034) (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v (wz RSTDERR) (wz A_FMT_err) (wz An) (wint rc) a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                         F (wz 0x2279c) fc None mm (seg_rom psegs)) ->
         evt psegs Q (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
                         F (wz pc) fc None mm (seg_rom psegs))) ->
      implM psegs (mbind (stderr_fprintf [msg_err name rc]) (fun _ => mret (cc, dcur))) s POST
        (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (wz pc) fc None m (seg_rom psegs)).
    Proof.
      intros until scs. intros HN RCR EI STR SZc LKL LOAD.
      pose proof EI as ((errv & ENV) & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRM).
      pose proof ENV as (_ & LXS & _ & SEW & SSP & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      unfold implM. iprefix. eapply LOAD; [exact LXS| exact MI|]. cbv beta delta [MallocRep.wz].
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
      eapply implM_bind.
      { eapply (CHK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s lo canary An name rc);
          rewrite ?E160;
          [ exact SEW | reflexivity | reflexivity | reflexivity | exact HN | exact RCR | apply wint_mod32; exact RCR
          | first [exact ST | rewrite E160 in ST; exact ST] | unfold FPRINTF_DEPTH; lia | unfold GLOBALS_TOP; lia | lia
          | exact SSP | exact MI | exact FRM ]. }
      cbv beta. intros [] s3 ms3 PO3.
      destruct PO3 as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & F3 & fc3 & m3 & -> & MU3 & WM3 & MI3 & FRM3 & FREG3 & ST3 & SEW3 & SSP3 & ->).
      rewrite E160 in MU3, ST3.
      replace (ret_pc (Z_to_bv 64 0x16034)) with (Z_to_bv 64 0x16034) by (symmetry; rpc).
      pose proof (einv_print _ _ _ _ fc3 _ _ _ EI MU3 WM3 MI3 ST3 SEW3 FRM3) as EI3.
      assert (STR3 : rw_cells psegs m3 SS scs).
      { eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU3 WM3)| exact STR|]. intros a Ha. rewrite SZc in Ha. cbn [outside]. lia. }
      apply implM_ret. zstep.
      eapply td_tail; eassumption.
    Qed.

    (* [comment removed for export] *)
    Lemma td_fwtail : forall (An : Z) (msg : list Z) s LK cc dcur
        (x1 t0 t1 t2 s0v s1v a2 a4 a5 a6 a7 s2v s3v t3 t4 t5 t6 : word) F fc m (scs : list cell),
      ro_bytes_b psegs An (zb msg) = true -> Forall (fun c => 0 <= c < 256) msg -> 0 < zlength msg < 64 -> 0x10000 <= An -> An + zlength msg <= 0x29000 ->
      EINV m s fc LK cc dcur -> rw_cells psegs m SS scs -> cells_size scs = 112%nat -> (length LK <= 5)%nat ->
      implM psegs (mbind (stderr_fwrite msg) (fun _ => mret (cc, dcur))) s POST
        (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 s0v s1v (wz An) (wz (zlength msg)) a2 (wz RSTDERR) a4 a5 a6 a7 s2v s3v S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
            F (wz 0x16050) fc None m (seg_rom psegs)).
    Proof.
      intros until scs. intros RB MF ML ALO AHI EI STR SZc LKL.
      pose proof EI as ((errv & ENV) & _ & _ & _ & _ & _ & _ & _ & _ & _ & FRM).
      pose proof ENV as (_ & LXS & _ & SEW & SSP & _ & _ & _ & ST & _ & _ & _ & _ & MI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      unfold implM. iprefix. cbv beta delta [MallocRep.wz]. zstep. zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s POST msx) end.
      eapply implM_bind.
      { eapply (FWR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m s lo canary msg);
          rewrite ?unsigned_lit by lia; rewrite ?E160;
          [ exact SEW
          | apply (lit_bytes_at m An msg MI RB); [lia| lia]
          | exact MF | lia
          | reflexivity | reflexivity | reflexivity
          | first [exact ST | rewrite E160 in ST; exact ST] | unfold FWRITE_DEPTH; lia | unfold GLOBALS_TOP; lia
          | left; lia | left; lia
          | exact SSP | exact MI ]. }
      cbv beta. intros [] s8 ms8 PO8.
      destruct PO8 as (g0 & g1 & g2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & g3 & g4 & g5 & g6 & m8 & -> & MU8 & WM8 & MI8 & ST8 & SEW8 & SSP8 & ->).
      rewrite ?E160 in MU8, ST8.
      replace (ret_pc (Z_to_bv 64 0x16058)) with (Z_to_bv 64 0x16058) by (symmetry; rpc).
      pose proof (einv_print _ _ _ _ fc _ _ _ EI MU8 WM8 MI8 ST8 SEW8 FRM) as EI8.
      assert (STR8 : rw_cells psegs m8 SS scs).
      { eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU8 WM8)| exact STR|]. intros a Ha. rewrite SZc in Ha. cbn [outside]. lia. }
      apply implM_ret.
      eapply td_tail; eassumption.
    Qed.
  End Exits.

  (* [comment removed for export] *)
  Section Live.
    Variables (LBz : list block) (m2 : mem) (F : bvmap 5 word) (fc : bv 32).
    Hypothesis LBZR : forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b).
    Hypothesis LBZC : forall b, In b LBz -> blk_addr b + blk_size b <= C \/ C + N <= blk_addr b.
    Hypothesis LBZU : forall b, In b LBz -> blk_addr b + blk_size b <= U \/ U + N <= blk_addr b.
    Hypothesis ZLS2 : zl_statics m2.

    (* [comment removed for export] *)
    Definition W0 : list (Z * Z) :=
      [(lo, usp + -160); (SS, SS + ZS_SIZEOF); (C, C + N); (ZHS, ZHS + 16)] ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz.

    Lemma outside_app : forall (W1 W2 : list (Z * Z)) x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
    Proof. induction W1 as [|[l h] W1 IH]; intros W2 x; cbn [app outside]; [tauto|]. rewrite IH. tauto. Qed.

    Lemma outside_blocks : forall a, (forall b, In b LBz -> ~ (blk_addr b <= a < blk_addr b + blk_size b)) ->
      outside (map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) a.
    Proof.
      intros a Hb. clear LBZC LBZU LBZR. induction LBz as [|b L IH]; cbn [map outside]; [exact I|]. split.
      - pose proof (Hb b (or_introl eq_refl)). lia.
      - apply IH. intros b' Hb'. apply Hb. right. exact Hb'.
    Qed.

    (* [comment removed for export] *)
    Lemma fp_sub : forall n k, 0 <= n -> 0 <= k -> n + k <= N ->
      sub_fp ([(lo, usp + -160); (SS, SS + ZS_SIZEOF); (C + n, C + n + k)] ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) W0.
    Proof.
      intros n k H0 Hk H x Hx. unfold W0 in Hx. apply outside_app in Hx. destruct Hx as [Hx1 Hx2]. apply outside_app. split; [| exact Hx2].
      cbn [outside] in Hx1 |- *. lia.
    Qed.

    Lemma fp_pubzh : sub_fp [(SS, SS + 48); (ZHS, ZHS + 4)] W0.
    Proof. intros x Hx. unfold W0 in Hx. cbn [app outside] in Hx |- *. unfold ZS_SIZEOF in Hx. lia. Qed.

    (* [comment removed for export] *)
    Lemma W0_image : forall a, 0x29000 <= a < 0x5c000 -> ~ (ZHS <= a < ZHS + 16) -> outside W0 a.
    Proof.
      intros a Ha Hz. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold GLOBALS_TOP, ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, ZS_SIZEOF in *. destruct CR as (_ & _ & _ & _ & CI). lia.
      - apply outside_blocks. intros b Hb. destruct (LBZR b Hb) as (_ & _ & _ & _ & BI). lia.
    Qed.
    Lemma W0_high : forall a, B <= a -> outside W0 a.
    Proof.
      intros a Ha. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, ZS_SIZEOF in *. destruct CR as (_ & _ & _ & CC & _). lia.
      - apply outside_blocks. intros b Hb. destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
    Qed.
    Lemma W0_stack : forall a, usp + -160 <= a -> ~ (SS <= a < SS + ZS_SIZEOF) -> outside W0 a.
    Proof.
      intros a Ha Hs. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in *. destruct CR as (_ & _ & _ & CC & _). lia.
      - apply outside_blocks. intros b Hb. destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK in *. lia.
    Qed.
    Lemma W0_heap : forall a, a < lo -> ~ (C <= a < C + N) -> (a < 0x10000 \/ 0x5c000 <= a) ->
      (forall b, In b LBz -> ~ (blk_addr b <= a < blk_addr b + blk_size b)) -> outside W0 a.
    Proof.
      intros a Ha Hc Hi Hb. unfold W0. apply outside_app. split.
      - cbn [outside]. unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, ZS_SIZEOF in *. lia.
      - apply outside_blocks. exact Hb.
    Qed.

    (* [comment removed for export] *)
    Lemma zls_inv : forall m dcur pad dv, munch W0 m2 m -> wmono psegs m2 m -> rw_cells psegs m ZHS [C4 (wz dcur); CB 4 pad; C8 dv] -> zl_statics m.
    Proof.
      intros m dcur pad dv MU WM ZH. pose proof (agree_on_of_munch _ _ _ MU WM) as AG. destruct ZLS2 as (N1 & N2 & _ & MRP).
      assert (TR : forall a : word, outside W0 (bv_unsigned a) -> m2 a = None -> m a = None).
      { intros a Po E. pose proof (bv_unsigned_in_range 64 a) as Ra. change (bv_modulus 64) with (2^64) in Ra.
        destruct (AG (bv_unsigned a) Ra Po) as [E' _]. unfold wa in E'. rewrite Z_to_bv_bv_unsigned in E'. congruence. }
      unfold zl_statics. split; [intros a Ha; apply TR; [apply W0_image; unfold ZL_RELRO_LO, ZL_RELRO_HI in *; lia| apply N1; exact Ha]|].
      split; [intros a Ha; apply TR; [apply W0_image; unfold ZL_GOT_LO, ZL_GOT_HI in *; lia| apply N2; exact Ha]|].
      split.
      - pose proof ZH as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LP & _).
        destruct (le8_of_bytes (le4 (wz dcur) ++ pad) ltac:(rewrite length_app, Mem.length_le4, LP; reflexivity)) as (v & _ & Ev).
        exists (Z_to_bv 64 v), dv. eapply rw_cells_recast; [exact ZH| cbn [cells_wf cell_wf]; repeat split| ].
        cbn [cells_bytes cbytes]. rewrite Ev, <- app_assoc. reflexivity.
      - eapply rw_cells_agree; [exact AG| exact MRP|]. intros a Ha. cbn in Ha. apply W0_image; unfold ZL_MREPL in *; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma zrd_own : forall m m' ds W, zrd R m SS LBz ds -> munch W m m' -> wmono psegs m m' -> sub_fp W [(SS, SS + 48); (ZHS, ZHS + 4)] ->
      zrd R m' SS LBz ds.
    Proof.
      intros m m' ds W ZR MU WM SUB. eapply (zrd_frame R); [exact ZR|]. intros a Ha Hin.
      apply (agree_on_of_munch _ _ _ (munch_weaken _ _ _ _ SUB MU) WM a Ha). cbn [outside]. split; [| split; [| exact I]].
      - destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF in *; lia|].
        destruct (LBZR b Hb) as (_ & _ & _ & BC & _). unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, ZS_PUB in *. lia.
      - destruct Hin as [Hin|(b & Hb & Hr)]; [unfold ZS_PUB, ZS_SIZEOF, ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in *; lia|].
        destruct (LBZR b Hb) as (_ & _ & _ & _ & BI). lia.
    Qed.

    (* [comment removed for export] *)
    (* [comment removed for export] *)
    Definition TDCORE (m : mem) (x : dphL za) (dcur : Z) (pad : list byte) (dv : word) (k : Z) : Prop :=
      zrd R m SS LBz (dp_ds za x)
      /\ u8arr psegs m C (to_bytes (rev (dp_orev za x) ++ zrepeat 0 (N - dp_n za x)))
      /\ dp_n za x = zlength (rev (dp_orev za x)) /\ 0 <= dp_n za x <= N
      /\ Forall (fun c => 0 <= c < 256) (rev (dp_orev za x))
      /\ rw_cells psegs m ZHS [C4 (wz dcur); CB 4 pad; C8 dv] /\ 0 <= dcur < 2^32
      /\ u8arr psegs m U (to_bytes (zrepeat 0 N))
      /\ munch W0 m2 m /\ wmono psegs m2 m /\ mem_inv psegs m /\ stk psegs m lo (usp + -160)
      /\ 0 <= dsl_tin (dp_ds za x) <= k * N /\ 0 <= dsl_tout (dp_ds za x) <= k * N.
    (* [comment removed for export] *)
    Definition PUBc (m : mem) (x : dphL za) (NI : Z) (inp : list Z) (p1 p2 : list byte) : Prop :=
      rw_cells psegs m SS (zs_pub NI (zlength inp) (dsl_tin (dp_ds za x)) (C + dp_n za x) (N - dp_n za x) (dsl_tout (dp_ds za x)) p1 p2).
    (* [comment removed for export] *)
    Definition INP (m : mem) (x : dphL za) (NI : Z) (inp : list Z) : Prop :=
      bytes_at psegs m NI (to_bytes inp) /\ Forall (fun c => 0 <= c < 256) inp
      /\ ((U <= NI /\ NI + zlength inp <= U + N) \/ (C <= NI /\ NI + zlength inp <= C + dp_n za x)).

    (* [comment removed for export] *)
    Lemma call_post : forall m m' x dcur pad dv k NI inp ds' c bs p1' p2',
      TDCORE m x dcur pad dv k -> INP m x NI inp -> zlength inp <= N ->
      munch ([(lo, usp + -160); (SS, SS + ZS_SIZEOF); (C + dp_n za x, C + dp_n za x + zlength bs)]
             ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) m m' ->
      wmono psegs m m' -> mem_inv psegs m' -> stk psegs m' lo (usp + -160) ->
      0 <= c <= zlength inp -> zlength bs <= N - dp_n za x -> Forall (fun b => 0 <= b < 256) bs ->
      0 <= dsl_tin ds' <= dsl_tin (dp_ds za x) + zlength inp -> 0 <= dsl_tout ds' <= dsl_tout (dp_ds za x) + (N - dp_n za x) ->
      rw_cells psegs m' SS (zs_pub (NI + c) (zlength inp - c) (dsl_tin ds') (C + dp_n za x + zlength bs) (N - dp_n za x - zlength bs) (dsl_tout ds') p1' p2') ->
      zrd R m' SS LBz ds' ->
      u8arr psegs m' (C + dp_n za x) (to_bytes (zstore (zrepeat 0 (N - dp_n za x)) 0 bs)) ->
      let x' := dp_after za x ds' c bs inp in
      TDCORE m' x' dcur pad dv (k + 1) /\ PUBc m' x' (NI + c) (dp_in za x') p1' p2' /\ INP m' x' (NI + c) (dp_in za x').
    Proof.
      intros until p2'. intros (ZR & CARR & DPN & DPR & OUTB & ZH & DCR & UZ & MU & WM & MI & ST & TIN & TOUT) (IB & IF & IR) IL
             MU' WM' MI' ST' CR' BSR BSF TIN' TOUT' PUB' ZR' OUT'.
      pose proof N_facts as NF. pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (BS0 : 0 <= zlength bs) by (unfold zlength; lia). assert (IL0 : 0 <= zlength inp) by (unfold zlength; lia).
      pose proof (agree_on_of_munch _ _ _ MU' WM') as AG.
      assert (OUTC : forall a, (C <= a < C + dp_n za x) \/ (U <= a < U + N) \/ (ZHS <= a < ZHS + 16) ->
                       outside ([(lo, usp + -160); (SS, SS + ZS_SIZEOF); (C + dp_n za x, C + dp_n za x + zlength bs)] ++ map (fun b => (blk_addr b, blk_addr b + blk_size b)) LBz) a).
      { intros a Ha. apply outside_app. split.
        - cbn [outside]. unfold ZS_SIZEOF. lia.
        - apply outside_blocks. intros b Hb. pose proof (LBZC b Hb). pose proof (LBZU b Hb). destruct (LBZR b Hb) as (_ & _ & _ & _ & BI). lia. }
      cbv zeta. unfold TDCORE, PUBc, INP. cbn [dp_after dp_ds dp_orev dp_n dp_in].
      rewrite rev_append_rev', rev_app_distr, rev_involutive.
      assert (LREV : zlength (rev (dp_orev za x) ++ bs) = dp_n za x + zlength bs) by (rewrite zlength_app'; lia).
      assert (LDROP : zlength (zdrop c inp) = zlength inp - c) by (unfold zdrop, zlength in *; rewrite length_skipn; lia).
      split; [| split].
      - split; [exact ZR'|].
        split. { rewrite <- app_assoc, to_bytes_app. apply (proj2 (u8arr_app_ _ _ _ _)). split.
                 - rewrite to_bytes_app in CARR. apply (proj1 (u8arr_app_ _ _ _ _)) in CARR. destruct CARR as [P _].
                   eapply u8arr_agree; [exact AG| exact P|]. intros a Ha. rewrite to_bytes_len in Ha. apply OUTC. left. unfold zlength in DPN. lia.
                 - rewrite to_bytes_len. replace (C + Z.of_nat (length (rev (dp_orev za x)))) with (C + dp_n za x) by (unfold zlength in DPN; lia).
                   replace (N - (dp_n za x + zlength bs)) with (N - dp_n za x - zlength bs) by lia.
                   rewrite <- (zstore_zrepeat0 bs (N - dp_n za x)) by lia. exact OUT'. }
        split; [first [exact LREV| symmetry; exact LREV]|]. split; [lia|].
        split; [apply Forall_app; split; [exact OUTB| exact BSF]|].
        split; [eapply rw_cells_agree; [exact AG| exact ZH| intros a Ha; cbn in Ha; apply OUTC; right; right; lia]|].
        split; [exact DCR|].
        split. { eapply u8arr_agree; [exact AG| exact UZ|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zrepeat in Ha. rewrite repeat_length in Ha. apply OUTC. right; left. lia. }
        split. { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU']. apply fp_sub; lia. }
        split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. lia.
      - rewrite LDROP. replace (C + (dp_n za x + zlength bs)) with (C + dp_n za x + zlength bs) by lia.
        replace (N - (dp_n za x + zlength bs)) with (N - dp_n za x - zlength bs) by lia. exact PUB'.
      - split.
        + unfold zdrop. rewrite to_bytes_skipn.
          assert (IB' : bytes_at psegs m' NI (to_bytes inp)).
          { eapply bytes_at_agree; [exact AG| exact IB|]. intros a Ha. rewrite to_bytes_len in Ha. apply OUTC. unfold zlength in IR. lia. }
          rewrite <- (firstn_skipn (Z.to_nat c) (to_bytes inp)) in IB'. apply bytes_at_app in IB'. destruct IB' as [_ IB'].
          rewrite length_firstn, to_bytes_len, Nat.min_l in IB' by (unfold zlength in *; lia). rewrite Z2Nat.id in IB' by lia. exact IB'.
        + split; [unfold zdrop; apply Forall_skipn_; exact IF|]. rewrite LDROP. lia.
    Qed.

    Notation TDS pc x1 a0v a1v t0 t1 t2 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 m :=
      (MS (mkR x1 (wz (usp + -160)) gp tp t0 t1 t2 (wz N) (wz U) a0v a1v a2 a3 a4 a5 a6 a7 s2v (wz N) S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F pc fc None m (seg_rom psegs)).

    (* [comment removed for export] *)
    Lemma call_pre : forall m x dcur pad dv k NI inp,
      TDCORE m x dcur pad dv k -> INP m x NI inp ->
      u8arr psegs m (C + dp_n za x) (to_bytes (zrepeat 0 (N - dp_n za x))) /\ zlength (zrepeat 0 (N - dp_n za x)) = N - dp_n za x
      /\ 0 < NI /\ NI + zlength inp < 2^63 /\ 0 < C + dp_n za x /\ C + dp_n za x + (N - dp_n za x) < 2^63
      /\ C + dp_n za x + (N - dp_n za x) <= lo /\ NI + zlength inp <= lo /\ (C + dp_n za x + (N - dp_n za x) <= 0x10000 \/ 0x5c000 <= C + dp_n za x)
      /\ (forall b, In b LBz -> blk_addr b + blk_size b <= C + dp_n za x \/ C + dp_n za x + (N - dp_n za x) <= blk_addr b)
      /\ (forall b, In b LBz -> blk_addr b + blk_size b <= NI \/ NI + zlength inp <= blk_addr b)
      /\ (NI + zlength inp <= C + dp_n za x \/ C + dp_n za x + (N - dp_n za x) <= NI)
      /\ zl_statics m /\ strm_in_frame (wz (usp + -160)) SS B.
    Proof.
      intros m x dcur pad dv k NI inp (ZR & CARR & DPN & DPR & OUTB & ZH & DCR & UZ & MU & WM & MI & ST & TIN & TOUT) (IB & IF & IR).
      pose proof N_facts as NF. pose proof CR as (C0 & _ & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (IL0 : 0 <= zlength inp) by (unfold zlength; lia).
      split. { rewrite to_bytes_app in CARR. apply (proj1 (u8arr_app_ _ _ _ _)) in CARR. destruct CARR as [_ P]. rewrite to_bytes_len in P.
               replace (C + Z.of_nat (length (rev (dp_orev za x)))) with (C + dp_n za x) in P by (unfold zlength in DPN; lia). exact P. }
      split; [apply zlength_zrepeat'; lia|].
      split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      split; [intros b Hb; pose proof (LBZC b Hb); lia|].
      split; [intros b Hb; pose proof (LBZC b Hb); pose proof (LBZU b Hb); lia|].
      split; [lia|].
      split; [eapply zls_inv; [exact MU| exact WM| exact ZH]|].
      unfold strm_in_frame, ZS_SIZEOF. cbv delta [MallocRep.wz]. rewrite unsigned_lit by lia. repeat split; try lia; try (clear - SP16 RSP; Z.div_mod_to_equations; lia).
    Qed.

    (* [comment removed for export] *)
    Lemma td_call : forall (Q : machine_state -> Prop) (x1 : word) (flush : Z) m x dcur pad dv k NI inp p1 p2
        (t0 t1 t2 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 : word),
      TDCORE m x dcur pad dv k -> PUBc m x NI inp p1 p2 -> INP m x NI inp -> zlength inp <= N -> 0 <= k <= 8 ->
      (flush = Z_NO_FLUSH \/ flush = Z_FINISH) ->
      (forall m' (x' : dphL za) rc c p1' p2' (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         d_callL za N flush inp x = (x', rc) -> cint rc -> 0 <= c <= zlength inp ->
         TDCORE m' x' dcur pad dv (k + 1) -> PUBc m' x' (NI + c) (dp_in za x') p1' p2' -> INP m' x' (NI + c) (dp_in za x') ->
         evt psegs Q (TDS (ret_pc x1) x1 (wint rc) a1' t0' t1' t2' a2' a3' a4' a5' a6' a7' s2v t3' t4' t5' t6' m')) ->
      evt psegs Q (TDS (wz Z_DEFLATE) x1 (wz SS) (wz flush) t0 t1 t2 a2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 m).
    Proof.
      destruct ZOK as (_ & DEFL & _).
      intros until t6. intros CORE PUB IN IL KR FL K.
      pose proof (call_pre _ _ _ _ _ _ _ _ CORE IN) as (OROOM & OLEN & NI0 & NI63 & NO0 & NO63 & NOLO & NILO & NOIMG & SEPO & SEPI & SEPIO & ZLS & SIF).
      pose proof CORE as (ZR & CARR & DPN & DPR & OUTB & ZH & DCR & UZ & MU & WM & MI & ST & TIN & TOUT). pose proof IN as (IB & IF & IR).
      pose proof N_facts as NF. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (IL0 : 0 <= zlength inp) by (unfold zlength; lia). assert (KN : k * N <= 8 * N) by (clear - KR NF; nia).
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
      destruct (dl_deflate za inp (dp_ds za x) (N - dp_n za x) flush) as [[[ds' c] bs] rc] eqn:ED.
      eapply evt_cut.
      { eapply DEFL with (S := SS) (NI := NI) (NO := C + dp_n za x) (LBz := LBz) (inp := inp) (oldc := zrepeat 0 (N - dp_n za x)) (ds := dp_ds za x)
                         (ao := N - dp_n za x) (flush := flush) (p1 := p1) (p2 := p2) (lo := lo) (B := B);
          unfold Z_DEFLATE_STACK; cbv delta [MallocRep.wz]; rewrite ?E160;
          [ nm 1 ltac:(exact PUB) | nm 2 ltac:(exact ZR) | nm 3 ltac:(exact IB) | nm 4 ltac:(exact IF) | nm 5 ltac:(exact NI0) | nm 6 ltac:(exact NI63)
          | nm 7 ltac:(exact OROOM) | nm 8 ltac:(exact OLEN) | nm 9 ltac:(exact NO0) | nm 10 ltac:(exact NO63)
          | nm 11 ltac:(lia) | nm 12 ltac:(lia) | nm 13 ltac:(lia) | nm 14 ltac:(lia) | nm 15 ltac:(lia) | nm 16 ltac:(lia)
          | nm 17 ltac:(exact FL) | nm 18 ltac:(exact NOLO) | nm 19 ltac:(exact NILO) | nm 20 ltac:(exact NOIMG)
          | nm 21 ltac:(exact SEPO) | nm 22 ltac:(exact SEPI) | nm 23 ltac:(exact SEPIO) | nm 24 ltac:(exact ZLS) | nm 25 ltac:(exact SIF)
          | nm 26 ltac:(exact ST) | nm 27 ltac:(exact LOC) | nm 28 ltac:(unfold GLOBALS_TOP; lia) | nm 29 ltac:(lia) | nm 30 ltac:(exact SPM)
          | nm 31 ltac:(lia) | nm 32 ltac:(exact B63) | nm 33 ltac:(exact MI) | nm 34 ltac:(reflexivity) | nm 35 ltac:(reflexivity) ]. }
      cbv beta. intros ms' PO. unfold deflate_postL in PO. rewrite ED in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & p1' & p2' & -> & MU' & WM' & MI' & ST' & -> &
                      CRG & BSR & BSF & TIN' & TOUT' & PUB' & ZR' & OUT').
      rewrite ?E160 in MU', ST'.
      pose proof (zo_drcL za the_zapiL_ok inp (dp_ds za x) (N - dp_n za x) flush) as RCR. rewrite ED in RCR. cbn [snd] in RCR.
      pose proof (call_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ CORE IN IL MU' WM' MI' ST' CRG BSR BSF TIN' TOUT' PUB' ZR' OUT') as (CORE' & PUBn & INn).
      eapply (K m' (dp_after za x ds' c bs inp) rc c p1' p2'); [| exact RCR| exact CRG| exact CORE'| exact PUBn| exact INn].
      unfold d_callL. rewrite ED. reflexivity.
    Qed.

    (* [comment removed for export] *)
    Lemma tp_call : forall (Q : machine_state -> Prop) (x1 : word) (level strategy : Z) m x dcur pad dv k ni p1 p2
        (t0 t1 t2 a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 : word),
      TDCORE m x dcur pad dv k -> PUBc m x ni (dp_in za x) p1 p2 -> INP m x ni (dp_in za x) -> zlength (dp_in za x) <= N -> 0 <= k <= 8 ->
      ((level = Z_NO_COMPRESSION /\ strategy = Z_DEFAULT_STRATEGY) \/ (level = Z_BEST_COMPRESSION /\ strategy = Z_FILTERED)) ->
      (forall m' (x' : dphL za) rc c p1' p2' (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
         p_callL za N level strategy x = (x', rc) -> 0 <= c <= zlength (dp_in za x) ->
         TDCORE m' x' dcur pad dv (k + 1) -> PUBc m' x' (ni + c) (dp_in za x') p1' p2' -> INP m' x' (ni + c) (dp_in za x') ->
         evt psegs Q (TDS (ret_pc x1) x1 (wint rc) a1' t0' t1' t2' a2' a3' a4' a5' a6' a7' s2v t3' t4' t5' t6' m')) ->
      evt psegs Q (TDS (wz Z_DEFLATEPARAMS) x1 (wz SS) (wz level) t0 t1 t2 (wz strategy) a3 a4 a5 a6 a7 s2v t3 t4 t5 t6 m).
    Proof.
      destruct ZOK as (_ & _ & DPAR & _).
      intros until t6. intros CORE PUB IN IL KR LS K.
      pose proof (call_pre _ _ _ _ _ _ _ _ CORE IN) as (OROOM & OLEN & NI0 & NI63 & NO0 & NO63 & NOLO & NILO & NOIMG & SEPO & SEPI & SEPIO & ZLS & SIF).
      pose proof CORE as (ZR & CARR & DPN & DPR & OUTB & ZH & DCR & UZ & MU & WM & MI & ST & TIN & TOUT). pose proof IN as (IB & IF & IR).
      pose proof N_facts as NF. pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (IL0 : 0 <= zlength (dp_in za x)) by (unfold zlength; lia). assert (KN : k * N <= 8 * N) by (clear - KR NF; nia).
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
      destruct (dl_params za (dp_in za x) (dp_ds za x) (N - dp_n za x) level strategy) as [[[ds' c] bs] rc] eqn:ED.
      eapply evt_cut.
      { eapply DPAR with (S := SS) (NI := ni) (NO := C + dp_n za x) (LBz := LBz) (inp := dp_in za x) (oldc := zrepeat 0 (N - dp_n za x)) (ds := dp_ds za x)
                         (ao := N - dp_n za x) (level := level) (strategy := strategy) (p1 := p1) (p2 := p2) (lo := lo) (B := B);
          unfold Z_DEFLATEPARAMS_STACK, Z_DEFLATE_STACK; cbv delta [MallocRep.wz]; rewrite ?E160;
          [ nm 1 ltac:(exact PUB) | nm 2 ltac:(exact ZR) | nm 3 ltac:(exact IB) | nm 4 ltac:(exact IF) | nm 5 ltac:(exact NI0) | nm 6 ltac:(exact NI63)
          | nm 7 ltac:(exact OROOM) | nm 8 ltac:(exact OLEN) | nm 9 ltac:(exact NO0) | nm 10 ltac:(exact NO63)
          | nm 11 ltac:(lia) | nm 12 ltac:(lia) | nm 13 ltac:(lia) | nm 14 ltac:(lia) | nm 15 ltac:(lia) | nm 16 ltac:(lia)
          | nm 17 ltac:(exact LS) | nm 18 ltac:(exact NOLO) | nm 19 ltac:(exact NILO) | nm 20 ltac:(exact NOIMG)
          | nm 21 ltac:(exact SEPO) | nm 22 ltac:(exact SEPI) | nm 23 ltac:(exact SEPIO) | nm 24 ltac:(exact ZLS) | nm 25 ltac:(exact SIF)
          | nm 26 ltac:(exact ST) | nm 27 ltac:(exact LOC) | nm 28 ltac:(unfold GLOBALS_TOP; lia) | nm 29 ltac:(lia) | nm 30 ltac:(exact SPM)
          | nm 31 ltac:(lia) | nm 32 ltac:(exact B63) | nm 33 ltac:(exact MI) | nm 34 ltac:(reflexivity) | nm 35 ltac:(reflexivity) | nm 36 ltac:(reflexivity) ]. }
      cbv beta. intros ms' PO. unfold deflateParams_post in PO. rewrite ED in PO.
      destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m' & p1' & p2' & -> & MU' & WM' & MI' & ST' & -> &
                      CRG & BSR & BSF & TIN' & TOUT' & PUB' & ZR' & OUT').
      rewrite ?E160 in MU', ST'.
      pose proof (call_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ CORE IN IL MU' WM' MI' ST' CRG BSR BSF TIN' TOUT' PUB' ZR' OUT') as (CORE' & PUBn & INn).
      eapply (K m' (dp_after za x ds' c bs (dp_in za x)) rc c p1' p2'); [| exact CRG| exact CORE'| exact PUBn| exact INn].
      unfold p_callL. rewrite ED. reflexivity.
    Qed.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma zh_recast : forall m (v1 v2 : word) d, rw_cells psegs m ZHS [C8 v1; C8 v2] -> rw_cells psegs m ZHS [C4 (wz d)] ->
      rw_cells psegs m ZHS [C4 (wz d); CB 4 (skipn 4 (le8 v1)); C8 v2].
    Proof.
      intros m v1 v2 d H16 H4.
      pose proof (rw_cells_bytes_at' _ _ _ _ H16) as B16. pose proof (rw_cells_bytes_at' _ _ _ _ H4) as B4. cbn [cells_bytes cbytes] in B16, B4.
      rewrite app_nil_r in B4.
      assert (E : firstn 4 (le8 v1) = le4 (wz d)).
      { rewrite <- (firstn_skipn 4 (le8 v1)), <- app_assoc in B16. apply bytes_at_app in B16. destruct B16 as [B16 _].
        eapply bytes_at_inj; [exact B16| exact B4|]. rewrite length_firstn, Mem.length_le8, Mem.length_le4. reflexivity. }
      eapply rw_cells_recast; [exact H16| |].
      - cbn [cells_wf cell_wf]. rewrite length_skipn, Mem.length_le8. repeat split.
      - cbn [cells_bytes cbytes]. rewrite <- E, app_assoc, firstn_skipn. reflexivity.
    Qed.
    Lemma zh_c8 : forall m d pad (dv : word), rw_cells psegs m ZHS [C4 (wz d); CB 4 pad; C8 dv] -> exists v1 v2 : word, rw_cells psegs m ZHS [C8 v1; C8 v2].
    Proof.
      intros m d pad dv ZH. pose proof ZH as [[WF _] _]. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LP & _).
      destruct (le8_of_bytes (le4 (wz d) ++ pad) ltac:(rewrite length_app, Mem.length_le4, LP; reflexivity)) as (v & _ & Ev).
      exists (Z_to_bv 64 v), dv. eapply rw_cells_recast; [exact ZH| cbn [cells_wf cell_wf]; repeat split| ].
      cbn [cells_bytes cbytes]. rewrite Ev, <- app_assoc. reflexivity.
    Qed.
    Lemma zh_c4 : forall m d pad (dv : word), rw_cells psegs m ZHS [C4 (wz d); CB 4 pad; C8 dv] -> rw_cells psegs m ZHS [C4 (wz d)].
    Proof. intros m d pad dv ZH. apply (proj1 (rw_cells_app psegs _ _ [_] _)) in ZH. exact (proj1 ZH). Qed.

    (* [comment removed for export] *)
    Lemma stream_cells : forall m ds NI inp x p1 p2, zrd R m SS LBz ds -> PUBc m x NI inp p1 p2 ->
      exists scs, rw_cells psegs m SS scs /\ cells_size scs = 112%nat.
    Proof.
      intros m ds NI inp x p1 p2 ZR PUB. destruct (zrd_stream R _ _ _ _ ZR) as [j PRIV].
      exists (zs_pub NI (zlength inp) (dsl_tin (dp_ds za x)) (C + dp_n za x) (N - dp_n za x) (dsl_tout (dp_ds za x)) p1 p2 ++ [CB 64 j]). split; [| reflexivity].
      apply (proj2 (rw_cells_app psegs _ _ _ _)). split; [exact PUB|]. eapply rw_cells_addr_eq; [exact PRIV|]. unfold ZS_PUB. cbn. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma core_einv : forall m0 s0 s2 errv2 (fcq : bv 32) m x dcur pad dv k,
      lx_env m2 s2 LBz LB (Z_to_bv 64 (usp + -160)) tp B lo errv2 canary -> FRLO m2 -> FRHI m2 ->
      lx_pres LB usp XX m0 m2 -> ps_so s2 = ps_so s0 -> ps_fa s2 = ps_fa s0 -> frm0 fcq ->
      RHEAP s2 (LBz ++ LB) m2 ->
      TDCORE m x dcur pad dv k -> EINV m0 s0 m s2 fcq LBz (rev (dp_orev za x) ++ zrepeat 0 (N - dp_n za x)) dcur.
    Proof.
      intros m0 s0 s2 errv2 fcq m x dcur pad dv k ENV2 (j0 & FRL2) FRH2 PRES2 ESO EFA FRM HP2 (ZR & CARR & DPN & DPR & OUTB & ZH & DCR & UZ & MU & WM & MI & ST & TIN & TOUT).
      pose proof N_facts as NF. pose proof CR as (C0 & _ & _ & CC & CI).
      pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
      unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
      assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
      pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
      unfold EINV. split.
      { exists errv2. eapply (lx_env_munch_gen W0 m2 m); [exact HFRAME| exact ENV2| exact MU| exact WM| exact MI| rewrite E160; exact ST| rewrite E160; lia| | | |].
        - unfold W0. apply Forall_app. split; [| apply blocks_write_ok].
          constructor; [left; cbn [fst]; lia|]. constructor; [left; cbn [fst]; lia|]. constructor; [| constructor; [| constructor]].
          + right; right. exists (cp, C, N). split; [apply in_or_app; right; exact INC| cbn [fst snd blk_addr blk_size]; lia].
          + right; left. cbn [fst snd]. unfold RMallocRep.RLIBC, RMallocRep.RCTX, RMallocRep.RSSP_GUARD, RMallocRep.RGOT_SSP. lia.
        - intros a [Ha|(Ha & Hs & Hz)]; [apply W0_high; exact Ha| apply W0_image; [exact Ha| exact Hz]].
        - destruct ENV2 as (_ & _ & _ & SEW2 & _). eapply stderr_wfile0_agree; [exact AG| | exact SEW2]. intros a Ha. apply W0_image; unfold stderr_addr in Ha; lia.
        - exact (zh_c8 _ _ _ _ ZH). }
      split. { exists j0. eapply rw_cells_agree; [exact AG| exact FRL2|]. intros a Ha. cbn in Ha. apply W0_stack; unfold ZS_SIZEOF; lia. }
      split. { unfold FRHI in *. eapply rw_cells_agree; [exact AG| exact FRH2|]. intros a Ha. cbn in Ha. apply W0_stack; unfold ZS_SIZEOF; lia. }
      split; [exact CARR|]. split; [rewrite zlength_app', zlength_zrepeat' by lia; unfold zlength in *; lia|].
      split; [exact (zh_c4 _ _ _ _ ZH)|]. split; [exact DCR|].
      split. { eapply lx_pres_trans; [exact PRES2|]. eapply pres_munch; [exact MU| exact WM|]. intros a [Ha|[(Ha & _ & Hz)|(Ha & Hi & Hc & (b & Hb & Hr))]].
               - apply W0_stack; unfold ZS_SIZEOF; lia.
               - apply W0_image; [exact Ha| exact Hz].
               - apply W0_heap; [exact Ha| exact Hc| exact Hi|]. intros bz Hbz Hin. pose proof (heap_sep _ _ _ _ bz b HND HBD HP2 Hbz Hb). lia. }
      split; [exact ESO|]. split; [exact EFA| exact FRM].
    Qed.
  End Live.

  Notation POSTD s0 m0 := (rtest_large_deflate_post ra sp gp tp S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s0 LB C N lo B canary m0).

  Lemma wz_wint9 : Z_to_bv 64 9 = wz Z_BEST_COMPRESSION. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Theorem td_main : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) (s : PState) (errv : word),
    lx_env m0 s [] LB sp tp B lo errv canary -> rw_cells psegs m0 ZHS [C4 (wz diff0)] ->
    u8arr psegs m0 C (to_bytes (zrepeat 0 N)) -> u8arr psegs m0 U (to_bytes (zrepeat 0 N)) -> frm0 fc ->
    implM psegs (test_large_deflateM lops za N diff0) s (POSTD s m0)
      (MS (mkR ra sp gp tp t0 t1 t2 S0 S1 (wz C) (wz N) (wz U) (wz N) a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz ZHL_TEST_DEFLATE) fc None m0 (seg_rom psegs)).
  Proof.
    intros until errv. intros ENV0 DIF0 CARR0 UZ0 FRM.
    pose proof ENV0 as (HP0 & _ & ZLS0 & _ & _ & _ & _ & _ & ST0 & _ & _ & _ & _ & MI0).
    pose proof N_facts as NF.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof CR as (C0 & C16 & _ & CC & CI). pose proof UR as (U0 & _ & _ & UC & UI).
    unfold ZHL_TEST_STACK, ZH_TEST_STACK, LX_PRINTF_STACK, GLOBALS_TOP in LOSP, LOG.
    destruct ZOK as (DINIT & _ & _ & DEND & _).
    unfold test_large_deflateM. cbn [bind ret lops Target.ops out_stderr out_stderr_fw].
    unfold ZHL_TEST_DEFLATE. cbv beta delta [MallocRep.wz] in DIF0 |- *.
    assert (LC0 : Z.of_nat (length (to_bytes (zrepeat 0 N))) = N) by (rewrite to_bytes_len; unfold zrepeat; rewrite repeat_length; lia).
    pose proof (munch_refl [(usp + -160, usp)] m0) as MU. pose proof (wmono_refl psegs m0) as WM.
    unfold implM. iprefix.
    zstep. carve_frame 160%nat ST0.
    apply (rw_cells_split_CB psegs _ _ [] 160 junk [] [8; 48; 8; 8; 8; 8; 8; 24; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    do 5 zstep. do 4 zstep. do 3 zs. do 5 zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    destruct (frame_split m1 _ _ _ _ _ FR) as (FRL1 & FRH1 & (ni & ai & ti & no & ao & to & p1 & p2 & jmsg & jstate & FRS1)). clear FR.
    destruct FRL1 as [j0 FRL1].
    assert (SPM : (usp + -160) mod 16 = 0) by (clear - SP16 RSP; Z.div_mod_to_equations; lia).
    assert (E160 : bv_unsigned (Z_to_bv 64 (usp + -160)) = usp + -160) by (apply unsigned_lit; lia).
    (* [comment removed for export] *)
    assert (ENV1 : lx_env m1 s [] LB (Z_to_bv 64 (usp + -160)) tp B lo errv canary).
    { eapply (lx_env_munch [(usp + -160, usp)] m0 m1); [exact HFRAME| exact ENV0| exact MU| exact WM| assumption| rewrite E160; assumption| rewrite E160; lia| |].
      - constructor; [left; cbn [fst]; lia| constructor].
      - intros a Ha. cbn [outside]. lia. }
    assert (PRES1 : lx_pres LB usp XX m0 m1).
    { eapply pres_munch; [exact MU| exact WM|]. intros a Ha. cbn [outside]. lia. }
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG1.
    assert (DIF1 : rw_cells psegs m1 ZHS [C4 (Z_to_bv 64 diff0)]) by (first [exact DIF0| eapply rw_cells_agree; [exact AG1| exact DIF0| intros a Ha; cbn in Ha; cbn [outside]; lia]]).
    assert (CARR1 : u8arr psegs m1 C (to_bytes (zrepeat 0 N))) by (first [exact CARR0| eapply u8arr_agree; [exact AG1| exact CARR0| intros a Ha; rewrite LC0 in Ha; cbn [outside]; lia]]).
    assert (UZ1 : u8arr psegs m1 U (to_bytes (zrepeat 0 N))) by (first [exact UZ0| eapply u8arr_agree; [exact AG1| exact UZ0| intros a Ha; rewrite LC0 in Ha; cbn [outside]; lia]]).
    clear DIF0 CARR0 UZ0.
    clear AG1 MU WM.
    rewrite wz_wint9.
    apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s (POSTD s m0) msx) end.
    eapply implM_bind.
    { eapply DINIT with (S := SS) (lo := lo) (B := B) (errv := errv) (canary := canary);
        [ exact ENV1 | exact FRS1
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E160; repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia
        | rewrite E160; unfold Z_DEFLATEINIT_STACK, RMALLOC_STACK; lia | rewrite E160; exact SPM | exact FRM
        | f_equal; lia | reflexivity | reflexivity | reflexivity ]. }
    cbv beta. intros r s2 ms2 PO. unfold deflateInit9_post in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & PO).
    replace (ret_pc (Z_to_bv 64 0x15eb8)) with (Z_to_bv 64 0x15eb8) by (symmetry; rpc).
    destruct r as [blk|].
    2:{ (* [comment removed for export] *)
      destruct PO as (((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & (js & STR2)).
      rewrite E160 in LXP2. pose proof (agree_of_lx_pres _ _ _ _ _ LXP2) as AG2.
      pose proof (fr_lx _ _ _ _ LXP2 FRL1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRL2.
      pose proof (fr_lx _ _ _ _ LXP2 FRH1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRH2.
      assert (CARR2 : u8arr psegs m2 C (to_bytes (zrepeat 0 N))).
      { eapply u8arr_agree; [exact AG2| exact CARR1|]. intros a Ha.
        eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      assert (DIF2 : rw_cells psegs m2 ZHS [C4 (Z_to_bv 64 diff0)]).
      { eapply rw_cells_agree; [exact AG2| exact DIF1|]. intros a Ha. cbn in Ha. apply zls_addr_client; [unfold zls_addr, ZH_STATICS; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      assert (EI2 : EINV m0 s m2 s2 fc2 [] (zrepeat 0 N) diff0).
      { unfold EINV. split; [exists errv2; exact ENV2|]. split; [exists j0; exact FRL2|]. split; [exact FRH2|]. split; [exact CARR2|]. split; [apply zlength_zrepeat'; lia|].
        split; [exact DIF2|]. split; [exact DIFR0|]. split; [| split; [exact ESO2| split; [exact EFA2| exact FRM2]]].
        eapply lx_pres_trans; [exact PRES1|]. eapply lx_pres_sub; [exact LXP2| apply client_inner]. }
      change (wint Z_MEM_ERROR) with (Z_to_bv 64 18446744073709551612).
      unfold implM. iprefix. zstep. if_true. apply evt_done.
      change (Z_to_bv 64 18446744073709551612) with (wint Z_MEM_ERROR).
      eapply (td_check m0 s 0x102ae NL_deflateInit Z_MEM_ERROR 0x15f88); [exists [105; 110; 118; 97; 108; 105]; unfold harness_names; cbn [In]; left; reflexivity| unfold Z_MEM_ERROR; lia| exact EI2| exact STR2| reflexivity| cbn; lia|].
      intros Q mm (GS1 & GS2) MIm KK. unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2 |- *.
      do 10 zstep. exact KK. }
    (* [comment removed for export] *)
    destruct PO as (As & Aw & Ap & Ah & Ab & ((errv2 & ENV2) & FRM2 & LXP2 & ESO2 & EFA2) & -> & PUB2 & TI0 & TO0 & ZR2).
    rewrite E160 in LXP2.
    assert (LBZ5 : (length (blk5L blk As Aw Ap Ah Ab) <= 5)%nat) by (destruct blk as [[[[? ?] ?] ?] ?]; cbn; lia).
    set (LBz := blk5L blk As Aw Ap Ah Ab) in *.
    pose proof ENV2 as (HP2 & _ & ZLS2 & _ & _ & _ & _ & _ & ST2 & _ & _ & _ & _ & MI2). rewrite E160 in ST2.
    (* [comment removed for export] *)
    pose proof (fr_lx _ _ _ _ LXP2 FRL1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRL2.
    pose proof (fr_lx _ _ _ _ LXP2 FRH1 ltac:(lia) ltac:(cbn; unfold ZS_SIZEOF; lia)) as FRH2.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP2) as AG2.
    assert (CARR2 : u8arr psegs m2 C (to_bytes (zrepeat 0 N))).
    { eapply u8arr_agree; [exact AG2| exact CARR1|]. intros a Ha.
      eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    assert (UZ2 : u8arr psegs m2 U (to_bytes (zrepeat 0 N))).
    { eapply u8arr_agree; [exact AG2| exact UZ1|]. intros a Ha.
      eapply block_client; [exact INU| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    assert (DIF2 : rw_cells psegs m2 ZHS [C4 (Z_to_bv 64 diff0)]).
    { eapply rw_cells_agree; [exact AG2| exact DIF1|]. intros a Ha. cbn in Ha. apply zls_addr_client; [unfold zls_addr, ZH_STATICS; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
    pose proof ZLS2 as (_ & _ & (v1 & v2 & ZHC2) & _). unfold ZH_STATICS in ZHC2.
    pose proof (zh_recast _ _ _ _ ZHC2 DIF2) as ZH2. set (pad := skipn 4 (le8 v1)) in ZH2. clear ZHC2 DIF2.
    assert (PRES2 : lx_pres LB usp XX m0 m2) by (eapply lx_pres_trans; [exact PRES1| eapply lx_pres_sub; [exact LXP2| apply client_inner]]).
    assert (LBZR : forall b, In b LBz -> rblock_range (blk_addr b) (blk_size b)).
    { intros b Hb. apply (HBR _ _ _ _ HP2). apply in_or_app. left. exact Hb. }
    assert (LBZC : forall b, In b LBz -> blk_addr b + blk_size b <= C \/ C + N <= blk_addr b).
    { intros b Hb. exact (heap_sep _ _ _ _ b (cp, C, N) HND HBD HP2 Hb INC). }
    assert (LBZU : forall b, In b LBz -> blk_addr b + blk_size b <= U \/ U + N <= blk_addr b).
    { intros b Hb. exact (heap_sep _ _ _ _ b (up, U, N) HND HBD HP2 Hb INU). }
    (* [comment removed for export] *)
    pose proof (fun m x dcur pad' dv k fcq (CORE : TDCORE LBz m2 m x dcur pad' dv k) (FRMq : frm0 fcq) =>
                  core_einv LBz m2 LBZR m0 s s2 errv2 fcq m x dcur pad' dv k ENV2 (ex_intro _ j0 FRL2) FRH2 PRES2 ESO2 EFA2 FRMq HP2 CORE) as EINV_of.
    clear FRL2 FRH2 FRL1 FRH1.
    (* [comment removed for export] *)
    destruct (test_large_deflate_pure za N) as [[[comprc ex] od] ended] eqn:TDP.
    unfold test_large_deflate_pure, tdeflL in TDP. cbv zeta in TDP.
    set (x0 := mkDPL za (dl_init9 za) [] 0 []) in TDP.
    (* [comment removed for export] *)
    rewrite TI0, TO0 in PUB2. unfold zs_pub in PUB2. cbv beta delta [MallocRep.wz] in PUB2. change (wint Z_OK) with (Z_to_bv 64 0).
    pose proof (munch_refl [(SS, SS + 48); (ZHS, ZHS + 4)] m2) as MUz. pose proof (wmono_refl psegs m2) as WMz.
    unfold implM. iprefix.
    zstep. if_false. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (CORE3 : TDCORE LBz m2 m3 x0 diff0 pad v2 0).
    { unfold TDCORE. subst x0. cbn [dp_ds dp_orev dp_n dp_in rev app]. rewrite Z.sub_0_r, TI0, TO0.
      split; [eapply (zrd_own LBz LBZR); [exact ZR2| exact MUz| exact WMz| intros a Ha; exact Ha]|].
      split; [assumption|]. split; [reflexivity|]. split; [lia|]. split; [constructor|].
      split; [assumption|]. split; [exact DIFR0|]. split; [assumption|].
      split; [eapply munch_weaken; [apply (fp_pubzh LBz)| exact MUz]|]. split; [exact WMz|]. split; [assumption|]. split; [assumption|]. lia. }
    pose proof CORE3 as (_ & _ & _ & _ & _ & ZH3 & _ & UZ3 & _).
    eapply (td_call LBz m2 F2 fc2 LBZR LBZC LBZU ZLS2 _ _ Z_NO_FLUSH m3 x0 diff0 pad v2 0 U (zrepeat 0 N) p1 p2);
      [exact CORE3| | | rewrite zlength_zrepeat' by lia; lia| lia| left; reflexivity|].
    { unfold PUBc, zs_pub. subst x0. cbn [dp_ds dp_n]. rewrite zlength_zrepeat', TI0, TO0, Z.add_0_r, Z.sub_0_r by lia. cbv beta delta [MallocRep.wz]. exact PUB2. }
    { unfold INP. subst x0. cbn [dp_n]. split; [exact (proj1 UZ3)|]. split; [unfold zrepeat; apply Forall_forall; intros c Hc; apply repeat_spec in Hc; lia|].
      left. rewrite zlength_zrepeat' by lia. lia. }
    clear PUB2 ZH3 UZ3 CORE3 MUz WMz ZR2 CARR2 UZ2.
    intros m4 x1 rc1 c1 q1 q2 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 ED1 RCR1 C1R CORE4 PUB4 INP4.
    replace (ret_pc (Z_to_bv 64 0x15ed8)) with (Z_to_bv 64 0x15ed8) by (symmetry; rpc). unfold cint in RCR1. cbv beta delta [MallocRep.wz].
    rewrite ED1 in TDP. cbv beta iota zeta in TDP.
    rewrite zlength_zrepeat' in C1R by lia.
    (* [comment removed for export] *)
    destruct (Z.eq_dec rc1 Z_OK) as [->|RNZ1].
    2:{ replace (rc1 =? Z_OK) with false in TDP by (symmetry; apply Z.eqb_neq; exact RNZ1). cbv beta iota zeta in TDP.
        injection TDP as <- <- <- <-. cbn [emit_dexit out_stderr lops Target.ops].
        zstep; if_cases KB; zify_cond KB; [| exfalso; destruct (wint_cases rc1 RCR1) as [[RC0 ERC]|[RC0 ERC]]; rewrite ERC in KB; unfold Z_OK in *; lia];
          apply evt_done; apply implM_ret_bind;
          pose proof CORE4 as (ZR4 & _ & DPN4 & DPR4 & _);
          destruct (stream_cells LBz _ _ _ _ _ _ _ ZR4 PUB4) as (scs & STR4 & SZ4);
          rewrite (comprL_eq x1 N DPN4 DPR4);
          (eapply (td_check m0 s AL_N_DEFLATE1 NL_deflate1 rc1 0x15fac);
            [exists [0; 46; 0]; unfold harness_names; cbn [In]; do 1 right; left; reflexivity| exact RCR1| exact (EINV_of _ _ _ _ _ _ _ CORE4 FRM2)| exact STR4| exact SZ4| exact LBZ5|]);
          intros Q mm (GS1 & GS2) MIm KK; unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2; cbv beta delta [MallocRep.wz] in GS1, GS2 |- *;
          do 10 zstep; exact KK. }
    replace (Z_OK =? Z_OK) with true in TDP by reflexivity. cbv beta iota zeta in TDP.
    change (wint Z_OK) with (Z_to_bv 64 0).
    zstep. if_false.
    (* [comment removed for export] *)
    pose proof PUB4 as PUB4c. unfold PUBc, zs_pub in PUB4c. cbv beta delta [MallocRep.wz] in PUB4c.
    pose proof INP4 as (_ & _ & IR4). assert (DIL : 0 <= zlength (dp_in za x1) <= N) by (pose proof CORE4 as (_ & _ & _ & DPR4' & _); unfold zlength in *; lia).
    zstep. rewrite (sx32_small (zlength (dp_in za x1))) by lia. zstep. if_cases KG; zify_cond KG.
    { (* [comment removed for export] *)
      replace (zlength (dp_in za x1) =? 0) with false in TDP by (symmetry; apply Z.eqb_neq; lia). cbv beta iota zeta in TDP.
      injection TDP as <- <- <- <-. cbn [emit_dexit out_stderr_fw lops Target.ops].
      apply evt_done. apply implM_ret_bind.
      pose proof CORE4 as (ZR4 & _ & DPN4 & DPR4 & _).
      destruct (stream_cells LBz _ _ _ _ _ _ _ ZR4 PUB4) as (scs & STR4 & SZ4).
      rewrite (comprL_eq x1 N DPN4 DPR4).
      pose proof (EINV_of _ _ _ _ _ _ _ CORE4 FRM2) as EI4.
      pose proof EI4 as ((errvq & ENVq) & _). pose proof ENVq as (_ & (GS1 & GS2) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIq).
      unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2.
      unfold implM. iprefix. do 7 zstep. apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s2 (POSTD s m0) msx) end.
      change (Z_to_bv 64 19) with (wz (zlength MSGL_GREEDY)). change (Z_to_bv 64 66589) with (wz AL_GREEDY). change (Z_to_bv 64 173152) with (wz 0x2a460).
      eapply (td_fwtail m0 s AL_GREEDY MSGL_GREEDY); [exact greedy_bytes| exact greedy_range| change (zlength MSGL_GREEDY) with 19; lia
        | unfold AL_GREEDY; lia| unfold AL_GREEDY; change (zlength MSGL_GREEDY) with 19; lia| exact EI4| exact STR4| exact SZ4| exact LBZ5]. }
    (* [comment removed for export] *)
    replace (zlength (dp_in za x1) =? 0) with true in TDP by (symmetry; apply Z.eqb_eq; exact KG). cbv beta iota zeta in TDP.
    do 4 zstep.
    eapply (tp_call LBz m2 F2 fc2 LBZR LBZC LBZU ZLS2 _ _ Z_NO_COMPRESSION Z_DEFAULT_STRATEGY m4 x1 diff0 pad v2 1 (U + c1) q1 q2);
      [exact CORE4| exact PUB4| exact INP4| lia| lia| left; split; reflexivity|].
    clear PUB4 PUB4c INP4 CORE4 IR4.
    intros m5 x2 rc2 c2 r1 r2 w0' w1' w2' e1' e2' e3' e4' e5' e6' e7' w3' w4' w5' w6' EP1 C2R CORE5 PUB5 INP5.
    replace (ret_pc (Z_to_bv 64 0x15ef4)) with (Z_to_bv 64 0x15ef4) by (symmetry; rpc). cbv beta delta [MallocRep.wz].
    rewrite EP1 in TDP. cbv beta iota zeta in TDP.
    (* [comment removed for export] *)
    pose proof CORE5 as (ZR5 & CARR5 & DPN5 & DPR5 & OUTB5 & ZH5 & _ & UZ5 & MU5 & WM5 & MI5 & ST5 & TIN5 & TOUT5). clear CORE5.
    pose proof PUB5 as PUB5c. unfold PUBc, zs_pub in PUB5c. cbv beta delta [MallocRep.wz] in PUB5c.
    pose proof (munch_refl [(SS, SS + 48); (ZHS, ZHS + 4)] m5) as MUz. pose proof (wmono_refl psegs m5) as WMz.
    zidle1 MU5. zidle1 WM5. zidle1 CARR5. zidle1 UZ5. pose proof INP5 as (IB5 & _). zidle1 IB5. clear INP5.
    zstep. zstep. zstep.
    replace (bv_swrap 32 (C + dp_n za x2 - C)) with (dp_n za x2) by (rewrite swrap32_id'; lia).
    zstep. zstep. zstep. do 3 zstep.
    unfold zidle in MU5, WM5, CARR5, UZ5, IB5.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m6 end.
    pose proof (agree_on_of_munch _ _ _ MUz WMz) as AGz.
    assert (CARR6 : u8arr psegs m6 C (to_bytes (rev (dp_orev za x2) ++ zrepeat 0 (N - dp_n za x2)))).
    { eapply u8arr_agree; [exact AGz| exact CARR5|]. intros a Ha. rewrite to_bytes_len in Ha.
      pose proof (zlength_app' (rev (dp_orev za x2)) (zrepeat 0 (N - dp_n za x2))) as LL. rewrite zlength_zrepeat' in LL by lia.
      unfold zlength in LL, DPN5. cbn [outside]. lia. }
    assert (UZ6 : u8arr psegs m6 U (to_bytes (zrepeat 0 N))).
    { eapply u8arr_agree; [exact AGz| exact UZ5|]. intros a Ha. rewrite LC0 in Ha. cbn [outside]. lia. }
    clear CARR5 UZ5 IB5 AGz.
    assert (CORE6 : TDCORE LBz m2 m6 x2 (dp_n za x2) pad v2 2).
    { unfold TDCORE. split; [eapply (zrd_own LBz LBZR); [exact ZR5| exact MUz| exact WMz| intros a Ha; exact Ha]|].
      split; [exact CARR6|]. split; [exact DPN5|]. split; [exact DPR5|]. split; [exact OUTB5|].
      split; [assumption|]. split; [lia|]. split; [exact UZ6|].
      split; [eapply munch_trans; [exact MU5| eapply munch_weaken; [apply (fp_pubzh LBz)| exact MUz]]|]. split; [eapply wmono_trans; [exact WM5| exact WMz]|].
      split; [assumption|]. split; [assumption|]. lia. }
    (* [comment removed for export] *)
    eapply (td_call LBz m2 F2 fc2 LBZR LBZC LBZU ZLS2 _ _ Z_NO_FLUSH m6 x2 (dp_n za x2) pad v2 2 C (rev_append (dp_orev za x2) []) r1 r2);
      [exact CORE6| | | rewrite rev_append_rev', app_nil_r; unfold zlength in *; lia| lia| left; reflexivity|].
    { unfold PUBc, zs_pub. rewrite rev_append_rev', app_nil_r, <- DPN5. cbv beta delta [MallocRep.wz]. hba. }
    { unfold INP. rewrite rev_append_rev', app_nil_r. split; [| split; [exact OUTB5| right; unfold zlength in *; lia]].
      lazymatch goal with H : u8arr psegs m6 C _ |- _ => rewrite to_bytes_app in H; apply (proj1 (u8arr_app_ _ _ _ _)) in H; exact (proj1 (proj1 H)) end. }
    clear PUB5 PUB5c CORE6 MUz WMz ZR5 CARR6 UZ6 ZH5 MU5 WM5 MI5 ST5.
    intros m7 x3 rc3 c3 q3 q4 n0 n1 n2 f1 f2 f3 f4 f5 f6 f7 n3 n4 n5 n6 ED3 RCR3 C3R CORE7 PUB7 INP7.
    replace (ret_pc (Z_to_bv 64 0x15f18)) with (Z_to_bv 64 0x15f18) by (symmetry; rpc). unfold cint in RCR3. cbv beta delta [MallocRep.wz].
    rewrite ED3 in TDP. cbv beta iota zeta in TDP.
    (* [comment removed for export] *)
    destruct (Z.eq_dec rc3 Z_OK) as [->|RNZ3].
    2:{ replace (rc3 =? Z_OK) with false in TDP by (symmetry; apply Z.eqb_neq; exact RNZ3). cbv beta iota zeta in TDP.
        injection TDP as <- <- <- <-. cbn [emit_dexit out_stderr lops Target.ops].
        zstep; if_cases KB; zify_cond KB; [| exfalso; destruct (wint_cases rc3 RCR3) as [[RC0 ERC]|[RC0 ERC]]; rewrite ERC in KB; unfold Z_OK in *; lia];
          apply evt_done; apply implM_ret_bind;
          pose proof CORE7 as (ZR7 & _ & DPN7 & DPR7 & _);
          destruct (stream_cells LBz _ _ _ _ _ _ _ ZR7 PUB7) as (scs & STR7 & SZ7);
          rewrite (comprL_eq x3 N DPN7 DPR7);
          (eapply (td_check m0 s AL_N_DEFLATE2 NL_deflate2 rc3 0x15fec);
            [exists [105; 110; 118; 97; 108; 105]; unfold harness_names; cbn [In]; do 2 right; left; reflexivity| exact RCR3| exact (EINV_of _ _ _ _ _ _ _ CORE7 FRM2)| exact STR7| exact SZ7| exact LBZ5|]);
          intros Q mm (GS1 & GS2) MIm KK; unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2; cbv beta delta [MallocRep.wz] in GS1, GS2 |- *;
          do 10 zstep; exact KK. }
    replace (Z_OK =? Z_OK) with true in TDP by reflexivity. cbv beta iota zeta in TDP.
    change (wint Z_OK) with (Z_to_bv 64 0).
    zstep. if_false.
    (* [comment removed for export] *)
    assert (DIL3 : zlength (dp_in za x3) <= N) by (pose proof INP7 as (_ & _ & IR7); pose proof CORE7 as (_ & _ & _ & DPR7 & _); unfold zlength in *; lia).
    do 5 zstep.
    eapply (tp_call LBz m2 F2 fc2 LBZR LBZC LBZU ZLS2 _ _ Z_BEST_COMPRESSION Z_FILTERED m7 x3 (dp_n za x2) pad v2 3 (C + c3) q3 q4);
      [exact CORE7| exact PUB7| exact INP7| exact DIL3| lia| right; split; reflexivity|].
    clear PUB7 INP7 CORE7.
    intros m8 x4 rc4 c4 r3 r4 n0' n1' n2' f1' f2' f3' f4' f5' f6' f7' n3' n4' n5' n6' EP2 C4R CORE8 PUB8 INP8.
    replace (ret_pc (Z_to_bv 64 0x15f30)) with (Z_to_bv 64 0x15f30) by (symmetry; rpc). cbv beta delta [MallocRep.wz].
    rewrite EP2 in TDP. cbv beta iota zeta in TDP.
    (* [comment removed for export] *)
    pose proof CORE8 as (ZR8 & CARR8 & DPN8 & DPR8 & OUTB8 & ZH8 & _ & UZ8 & MU8 & WM8 & MI8 & ST8 & TIN8 & TOUT8). clear CORE8.
    pose proof PUB8 as PUB8c. unfold PUBc, zs_pub in PUB8c. cbv beta delta [MallocRep.wz] in PUB8c.
    pose proof (munch_refl [(SS, SS + 48); (ZHS, ZHS + 4)] m8) as MUz. pose proof (wmono_refl psegs m8) as WMz.
    zidle1 MU8. zidle1 WM8. zidle1 CARR8. zidle1 UZ8. pose proof INP8 as (IB8 & _). zidle1 IB8. clear INP8.
    zstep. zstep. do 3 zstep.
    unfold zidle in MU8, WM8, CARR8, UZ8. clear IB8.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m9 end.
    pose proof (agree_on_of_munch _ _ _ MUz WMz) as AGz.
    assert (CARR9 : u8arr psegs m9 C (to_bytes (rev (dp_orev za x4) ++ zrepeat 0 (N - dp_n za x4)))).
    { eapply u8arr_agree; [exact AGz| exact CARR8|]. intros a Ha. rewrite to_bytes_len in Ha.
      pose proof (zlength_app' (rev (dp_orev za x4)) (zrepeat 0 (N - dp_n za x4))) as LL. rewrite zlength_zrepeat' in LL by lia.
      unfold zlength in LL, DPN8. cbn [outside]. lia. }
    assert (UZ9' : u8arr psegs m9 U (to_bytes (zrepeat 0 N))).
    { eapply u8arr_agree; [exact AGz| exact UZ8|]. intros a Ha. rewrite LC0 in Ha. cbn [outside]. lia. }
    clear CARR8 UZ8 AGz.
    assert (CORE9 : TDCORE LBz m2 m9 x4 (dp_n za x2) pad v2 4).
    { unfold TDCORE. split; [eapply (zrd_own LBz LBZR); [exact ZR8| exact MUz| exact WMz| intros a Ha; exact Ha]|].
      split; [exact CARR9|]. split; [exact DPN8|]. split; [exact DPR8|]. split; [exact OUTB8|].
      split; [assumption|]. split; [lia|]. split; [exact UZ9'|].
      split; [eapply munch_trans; [exact MU8| eapply munch_weaken; [apply (fp_pubzh LBz)| exact MUz]]|]. split; [eapply wmono_trans; [exact WM8| exact WMz]|].
      split; [assumption|]. split; [assumption|]. lia. }
    pose proof CORE9 as (_ & _ & _ & _ & _ & _ & _ & UZ9 & _).
    eapply (td_call LBz m2 F2 fc2 LBZR LBZC LBZU ZLS2 _ _ Z_NO_FLUSH m9 x4 (dp_n za x2) pad v2 4 U (zrepeat 0 N) r3 r4);
      [exact CORE9| | | rewrite zlength_zrepeat' by lia; lia| lia| left; reflexivity|].
    { unfold PUBc, zs_pub. rewrite zlength_zrepeat' by lia. cbv beta delta [MallocRep.wz]. hba. }
    { unfold INP. split; [exact (proj1 UZ9)|]. split; [unfold zrepeat; apply Forall_forall; intros c Hc; apply repeat_spec in Hc; lia|].
      left. rewrite zlength_zrepeat' by lia. lia. }
    clear PUB8 PUB8c CORE9 MUz WMz ZR8 CARR9 UZ9' ZH8 MU8 WM8 MI8 ST8 UZ9.
    intros m10 x5 rc5 c5 q5 q6 y0 y1 y2 g1 g2 g3 g4 g5 g6 g7 y3 y4 y5 y6 ED5 RCR5 C5R CORE10 PUB10 INP10.
    replace (ret_pc (Z_to_bv 64 0x15f44)) with (Z_to_bv 64 0x15f44) by (symmetry; rpc). unfold cint in RCR5. cbv beta delta [MallocRep.wz].
    rewrite ED5 in TDP. cbv beta iota zeta in TDP.
    rewrite zlength_zrepeat' in C5R by lia.
    (* [comment removed for export] *)
    destruct (Z.eq_dec rc5 Z_OK) as [->|RNZ5].
    2:{ replace (rc5 =? Z_OK) with false in TDP by (symmetry; apply Z.eqb_neq; exact RNZ5). cbv beta iota zeta in TDP.
        injection TDP as <- <- <- <-. cbn [emit_dexit out_stderr lops Target.ops].
        zstep; if_cases KB; zify_cond KB; [| exfalso; destruct (wint_cases rc5 RCR5) as [[RC0 ERC]|[RC0 ERC]]; rewrite ERC in KB; unfold Z_OK in *; lia];
          apply evt_done; apply implM_ret_bind;
          pose proof CORE10 as (ZR10 & _ & DPN10 & DPR10 & _);
          destruct (stream_cells LBz _ _ _ _ _ _ _ ZR10 PUB10) as (scs & STR10 & SZ10);
          rewrite (comprL_eq x5 N DPN10 DPR10);
          (eapply (td_check m0 s AL_N_DEFLATE3 NL_deflate3 rc5 0x16010);
            [exists [115; 116]; unfold harness_names; cbn [In]; do 3 right; left; reflexivity| exact RCR5| exact (EINV_of _ _ _ _ _ _ _ CORE10 FRM2)| exact STR10| exact SZ10| exact LBZ5|]);
          intros Q mm (GS1 & GS2) MIm KK; unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2; cbv beta delta [MallocRep.wz] in GS1, GS2 |- *;
          do 9 zstep; exact KK. }
    replace (Z_OK =? Z_OK) with true in TDP by reflexivity. cbv beta iota zeta in TDP.
    change (wint Z_OK) with (Z_to_bv 64 0).
    zstep. if_false.
    (* [comment removed for export] *)
    assert (DIL5 : zlength (dp_in za x5) <= N) by (pose proof INP10 as (_ & _ & IR10); pose proof CORE10 as (_ & _ & _ & DPR10 & _); unfold zlength in *; lia).
    do 3 zstep.
    eapply (td_call LBz m2 F2 fc2 LBZR LBZC LBZU ZLS2 _ _ Z_FINISH m10 x5 (dp_n za x2) pad v2 5 (U + c5) (dp_in za x5) q5 q6);
      [exact CORE10| exact PUB10| exact INP10| exact DIL5| lia| right; reflexivity|].
    clear PUB10 INP10 CORE10.
    intros m11 x6 rc6 c6 q7 q8 y0' y1' y2' g1' g2' g3' g4' g5' g6' g7' y3' y4' y5' y6' ED6 RCR6 C6R CORE11 PUB11 INP11.
    replace (ret_pc (Z_to_bv 64 0x15f54)) with (Z_to_bv 64 0x15f54) by (symmetry; rpc). unfold cint in RCR6. cbv beta delta [MallocRep.wz].
    rewrite ED6 in TDP. cbv beta iota zeta in TDP.
    pose proof CORE11 as (ZR11 & CARR11 & DPN11 & DPR11 & _).
    destruct (stream_cells LBz _ _ _ _ _ _ _ ZR11 PUB11) as (scs & STR11 & SZ11).
    (* [comment removed for export] *)
    destruct (Z.eq_dec rc6 Z_STREAM_END) as [->|RNZ6].
    2:{ replace (rc6 =? Z_STREAM_END) with false in TDP by (symmetry; apply Z.eqb_neq; exact RNZ6). cbv beta iota zeta in TDP.
        injection TDP as <- <- <- <-. cbn [emit_dexit out_stderr_fw lops Target.ops].
        pose proof (EINV_of _ _ _ _ _ _ _ CORE11 FRM2) as EI11.
        pose proof EI11 as ((errvq & ENVq) & _). pose proof ENVq as (_ & (GS1 & GS2) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIq).
        unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2.
        rewrite (comprL_eq x6 N DPN11 DPR11).
        zstep; if_cases KB; zify_cond KB; [| exfalso; destruct (wint_cases rc6 RCR6) as [[RC0 ERC]|[RC0 ERC]]; rewrite ERC in KB; unfold Z_STREAM_END in *; lia];
          apply evt_done; apply implM_ret_bind;
          unfold implM; iprefix; do 6 zstep; apply evt_done;
          lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s2 (POSTD s m0) msx) end;
          change (Z_to_bv 64 41) with (wz (zlength MSGL_FINISH)); change (Z_to_bv 64 66609) with (wz AL_FINISH); change (Z_to_bv 64 173152) with (wz 0x2a460);
          (eapply (td_fwtail m0 s AL_FINISH MSGL_FINISH); [exact finish_bytes| exact finish_range| change (zlength MSGL_FINISH) with 41; lia
             | unfold AL_FINISH; lia| unfold AL_FINISH; change (zlength MSGL_FINISH) with 41; lia| exact EI11| exact STR11| exact SZ11| exact LBZ5]). }
    replace (Z_STREAM_END =? Z_STREAM_END) with true in TDP by reflexivity. cbv beta iota zeta in TDP.
    change (wint Z_STREAM_END) with (Z_to_bv 64 1).
    zstep. if_false.
    (* [comment removed for export] *)
    cbv beta iota zeta in TDP. injection TDP as <- <- <- <-.
    pose proof (EINV_of _ _ _ _ _ _ _ CORE11 FRM2) as EI11.
    pose proof EI11 as ((errv11 & ENV11) & (j11 & FRL11) & FRH11 & CARRe & CCLe & ZHe & DCRe & PRES11 & ESO11 & EFA11 & _).
    pose proof ENV11 as (_ & _ & _ & _ & _ & _ & _ & _ & ST11 & _ & _ & _ & _ & MI11). rewrite E160 in ST11.
    pose proof PUB11 as PUB11c. unfold PUBc in PUB11c.
    rewrite (comprL_eq x6 N DPN11 DPR11).
    zstep. zstep. apply evt_done.
    lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s2 (POSTD s m0) msx) end.
    eapply implM_bind.
    { eapply DEND with (S := SS) (ds := dp_ds za x6) (lo := lo) (B := B) (errv := errv11) (canary := canary);
        [ exact ENV11 | exact PUB11c | exact ZR11
        | unfold strm_in_frame, ZS_SIZEOF; rewrite E160; repeat split; try lia; clear - SP16 RSP; Z.div_mod_to_equations; lia
        | rewrite E160; unfold Z_DEFLATEEND_STACK, RFREE_STACK; lia | rewrite E160; exact SPM | exact FRM2
        | f_equal; lia ]. }
    cbv beta. intros [] s6 ms6 PO6. unfold deflateEnd_postL in PO6.
    destruct PO6 as (k0 & k1 & k2 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & k3 & k4 & k5 & k6 & F6 & fc6 & m12 & -> & ((errv6 & ENV6) & FRM6 & LXP6 & ESO6 & EFA6) & -> & (js & STR6)).
    rewrite E160 in LXP6.
    replace (ret_pc (Z_to_bv 64 0x15f60)) with (Z_to_bv 64 0x15f60) by (symmetry; rpc).
    pose proof ENV6 as (_ & _ & _ & _ & _ & _ & _ & _ & ST6 & _ & _ & _ & _ & MI6). rewrite E160 in ST6.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXP6) as AG6.
    assert (EI12 : EINV m0 s m12 s6 fc6 [] (rev (dp_orev za x6) ++ zrepeat 0 (N - dp_n za x6)) (dp_n za x2)).
    { unfold EINV. split; [exists errv6; exact ENV6|].
      split. { exists j11. eapply (fr_lx _ _ _ _ LXP6 FRL11); [lia| cbn; unfold ZS_SIZEOF; lia]. }
      split. { unfold FRHI in *. eapply (fr_lx _ _ _ _ LXP6 FRH11); [lia| cbn; unfold ZS_SIZEOF; lia]. }
      split. { eapply u8arr_agree; [exact AG6| exact CARRe|]. intros a Ha. rewrite to_bytes_len in Ha. unfold zlength in CCLe.
               eapply block_client; [exact INC| cbn [blk_addr blk_size fst snd]; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      split; [exact CCLe|].
      split. { eapply rw_cells_agree; [exact AG6| exact ZHe|]. intros a Ha. cbn in Ha. apply zls_addr_client; [unfold zls_addr, ZH_STATICS; lia| cbn [rin_ivs fst snd]; unfold ZS_SIZEOF; lia]. }
      split; [exact DCRe|].
      split; [eapply lx_pres_trans; [exact PRES11| eapply lx_pres_sub; [exact LXP6| apply client_inner]]|].
      split; [rewrite ESO6; exact ESO11|]. split; [rewrite EFA6; exact EFA11| exact FRM6]. }
    pose proof (zo_dendL za the_zapiL_ok (dp_ds za x6)) as RCRE. unfold cint in RCRE.
    (* [comment removed for export] *)
    destruct (Z.eq_dec (dl_end za (dp_ds za x6)) Z_OK) as [EOK|ENZ].
    - rewrite EOK. replace (Z_OK =? Z_OK) with true by reflexivity. cbn [emit_dexit ret lops Target.ops].
      apply implM_ret_bind. apply implM_ret. change (wint Z_OK) with (Z_to_bv 64 0).
      zstep. if_true.
      eapply (td_tail m0 s); [exact EI12| exact STR6| reflexivity| cbn; lia].
    - replace (dl_end za (dp_ds za x6) =? Z_OK) with false by (symmetry; apply Z.eqb_neq; exact ENZ). cbn [emit_dexit out_stderr lops Target.ops].
      apply implM_ret_bind.
      unfold implM. iprefix.
      zstep; if_cases KB; zify_cond KB; [exfalso; destruct (wint_cases _ RCRE) as [[RC0 ERC]|[RC0 ERC]]; rewrite ERC in KB; unfold Z_OK in *; lia|].
      apply evt_done.
      lazymatch goal with |- impl _ _ (?tm _) _ ?msx => change (implM psegs tm s6 (POSTD s m0) msx) end.
      eapply (td_check m0 s A_N_DEFLATEEND NL_deflateEnd (dl_end za (dp_ds za x6)) 0x15f64);
        [exists [105; 110; 118; 97]; unfold harness_names; cbn [In]; do 4 right; left; reflexivity| exact RCRE| exact EI12| exact STR6| reflexivity| cbn; lia|].
      intros Q mm (GS1 & GS2) MIm KK. unfold LX_GOT_STDERR, LX_STDERR_PTR, LX_STDERR_FILE in GS1, GS2. cbv beta delta [MallocRep.wz] in GS1, GS2 |- *.
      do 10 zstep. exact KK.
  Qed.
End TD.

(* [comment removed for export] *)
Theorem rtest_large_deflate_proof : forall R : zrepsL, zlib_okL R -> @check_err_stmt PState -> @fwrite_diag_stmt PState ->
  RHEAP_frame_stmt -> RHEAP_block_range_stmt -> RHEAP_blocks_nodup_stmt -> RHEAP_blocks_disjoint_stmt ->
  rtest_large_deflate_stmt.
Proof.
  intros R ZOK CHK FWR HFRAME HBR HND HBD. unfold rtest_large_deflate_stmt. intros until canary.
  intros ENV DIF DIFR SZ EN INC CARR INU UARR NEQ LOSP SP16 FRM -> -> -> ->.
  pose proof ENV as (HP & _ & _ & _ & _ & _ & SPB & B63 & _ & LOC & LOG & _ & TP & _). cbn [app] in HP.
  pose proof (HBR _ _ _ _ HP INC) as CR. cbn [blk_addr blk_size fst snd] in CR.
  pose proof (HBR _ _ _ _ HP INU) as UR. cbn [blk_addr blk_size fst snd] in UR.
  assert (CU : U + N <= C \/ C + N <= U).
  { pose proof (HBD _ _ _ _ _ HP INU INC) as D. cbn [blk_id blk_addr blk_size fst snd] in D. apply D. intros E. apply NEQ. symmetry. exact E. }
  assert (LBR : forall b, In b LB -> rblock_range (blk_addr b) (blk_size b)) by (intros b Hb; exact (HBR _ _ _ _ HP Hb)).
  unfold zhl_diff, ZHL_DIFF, ZH_STATICS in DIF.
  eapply (td_main R) with (cp := cp) (up := up) (errv := errv); eassumption.
Qed.
End WithCeiling0.
