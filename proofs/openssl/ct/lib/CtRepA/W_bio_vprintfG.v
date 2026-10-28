(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac ZBridge RzCPS Arr FP Frame Cells Step Mem. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog BnBase BnModel BnTree ApBase ApLogic ApErr PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs I_lkit FX_lib F_pop_arg F_printf_iface I_vsnstmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem BnTacX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA ImplA ImplAX BnIfaceA AsStruct RtCallA UnwindA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_bio_ctrl W_bio_push Fr_bio_write_intern W_bio_write Fr_BIO_vprintf Fr_BIO_printf W_bio_printf W_bio_printf2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bwG_post (AR' : ARun) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts (@ar_RT AR')) (OW LB : list block) (XW : list (Z * Z)) (POST : mem -> Prop) (CST n lo : Z) (m : mem) (Σ' : rts (@ar_RT AR')) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside XW a) m m'
    /\ @BnHeapA.AHEAP AR' Σ' OW LB m'
    /\ rt_live (@ar_RT AR') Σ' = rt_live (@ar_RT AR') Σ /\ rt_credit (@ar_RT AR') Σ - CST <= rt_credit (@ar_RT AR') Σ'
    /\ POST m'.

(* [comment removed for export] *)
Definition bio_write_calleeG (AR' : ARun) (OW : list block) (bio : Z) (PRE POST : mem -> Prop) (XW : list (Z * Z)) (CST BWS : Z) (NFR : nat) (o : list Z) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts (@ar_RT AR')) (LB : list block) (lo : Z) (pd : bptr) (D : Z),
    @BnHeapA.AHEAP AR' Σ OW LB m -> In (pd, D, 512) LB ->
    stk ctasegs m lo (bv_unsigned sp) -> @BnHeapA.ACEIL AR' <= lo -> lo + BWS <= bv_unsigned sp ->
    bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
    mem_inv ctasegs m -> tp = wz TP_A -> (length (@ar_FR AR') + NFR <= FRAMES_MAX)%nat -> CST <= rt_credit (@ar_RT AR') Σ ->
    PRE m -> bytes_at ctasegs m D (zb o ++ [Z_to_bv 8 0]) ->
    a0 = wz bio -> a1 = wz D -> a2 = wz (zlength o) ->
    cps ctasegs (ASTA (@ar_RT AR') Σ (@ar_PMc AR') (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                     F (wz BIO_WRITE) fc None m (seg_rom ctasegs))))
        (fun c => exists Σ', ASTA (@ar_RT AR') Σ' (@ar_PMc AR') (bwG_post AR' ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB XW POST CST (zlength o) lo m Σ') c
                  /\ rt_live (@ar_RT AR') Σ' = rt_live (@ar_RT AR') Σ).

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition bio_vprintfG_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (XW : list (Z * Z)) (POST : mem -> Prop) (CST n lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside XW a) m m'
    /\ AHEAP Σ' OW LB m'
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - (1 + CST) <= rt_credit RT Σ'
    /\ POST m'.

Section WithPFC.
Hypothesis PFC : printf_contracts RT.

(* [comment removed for export] *)
Lemma BIO_vprintf_gen_cpsA : forall
    (bio : Z) (PRE POST : mem -> Prop) (XW : list (Z * Z)) (CST BWS : Z) (NFR : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (A VA : Z)
    (fmt : list Z) (slots : list word) (args : list parg) (o : list Z),
  (forall m1 m2, agree_on (in_block (OW ++ LB)) m1 m2 -> PRE m1 -> PRE m2) ->
  (forall m1 m2, agree_on (in_block (OW ++ LB)) m1 m2 -> POST m1 -> POST m2) ->
  Forall (fun iv => exists b, In b (OW ++ LB) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) XW ->
  0 <= CST -> RT_STACK <= BWS ->
  (forall f, bio_write_calleeG (push AR f 4) OW bio PRE POST XW CST BWS NFR o) ->
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + BVPF_FRAME + BWS <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (length FR) + NFR <= FRAMES_MAX)%nat -> 1 + CST <= rt_credit RT Σ ->
  PRE m ->
  vfmtA_ok A fmt args o -> 0 <= zlength o < 512 ->
  va_area m VA slots -> bv_unsigned sp <= VA -> VA + 8 * zlength slots <= USTACK_TOP - 16 -> vargsA_ok OW LB m slots args ->
  a0 = wz bio -> a1 = wz A -> a2 = wz VA ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz BIO_VPRINTF) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (bio_vprintfG_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB XW POST CST (zlength o) lo m Σ') c
                /\ rt_live RT Σ' = rt_live RT Σ)      (* [comment removed for export] *).
Proof.
  intros until o. intros PREAG POSTAG XWOK CST0 BWSR HBW HEAP ST CEIL LO SPT SP16 MI TP FLEN CRED HPRE VF OLEN VAA VA1 VA2 VARGS -> -> ->.
  unfold BVPF_FRAME, RT_STACK, BIO_VPRINTF, MallocRep.wz in *.
  remember (zlength o) as n eqn:En.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3. unfold USTACK_TOP in SPT, VA2.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (XWS : forall a, lo <= a -> outside XW a).
  { intros a Ha. clear - XWOK HEAP Ha CEIL. induction XWOK as [|[x y] XW (b & Hb & R1 & R2) HW IH]; [exact I|]. cbn [outside fst snd] in *. split; [| exact IH].
    pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in *. lia. }
  (* [comment removed for export] *)
  eapply (bvpf_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold BVPF_FRAME, RT_STACK; clear - LO BWSR; lia | unfold USTACK_TOP; clear - SPT; lia | exact SP16
    | exact MI | exact TP | clear - FLEN; lia | clear - CRED CST0; lia |].
  intros Σ1 m3 f spa g jk gj ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 j8 jf24 jf32 jf40 jf64 jf72 jf96 jf608 jst
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold BVPF_BODY, MallocRep.wz.
  (* [comment removed for export] *)
  pose proof (@AH_ceil (push AR f 4) _ _ _ _ HEAP3) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3. cbn [ar_SP0 push amb] in D1, D2, D3.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 4) with 1024 in G3, G5. unfold SEGTOP_A in G4.
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 D3; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0 BWSR; lia).
  assert (SHR : 2147450880 <= shad f /\ shad f + 128 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)) as DP.
    assert (DQ : f / 8 + 128 <= 2 ^ 44).
    { assert (DR : f / 8 < 2 ^ 44 - 128); [apply Z.div_lt_upper_bound; [clear; lia|]; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; clear - G3 D3; lia | clear - DR; lia]. }
    clear - DP DQ; lia. }
  assert (ESH12 : bv_unsigned (Z_to_bv 64 (shad f + 12)) = shad f + 12) by (apply unsigned_lit; clear - SHR; lia).
  assert (BLK : forall a lo' hi', in_block (OW ++ LB) a -> (shad f <= lo' /\ hi' <= shad f + 128) \/ (f <= lo' /\ hi' <= f + 1024) ->
                 (aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a) /\ ~ (lo' <= a < hi')).
  { intros a lo' hi' (b & Hb & Hr) Hlh. split; [left; right; right; exists b; split; [exact Hb| exact Hr]|].
    pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 4) with 1024 in O.
    pose proof (AH_offsh _ _ _ _ _ HEAP Hb) as OS. unfold SHLO, SHHI in OS. clear - Hr Hlh O OS SHR. lia. }
  assert (BLKW : forall W m1 m2, munch W m1 m2 -> Forall (fun iv => (shad f <= fst iv /\ snd iv <= shad f + 128) \/ (f <= fst iv /\ snd iv <= f + 1024)) W ->
                 agree_on (in_block (OW ++ LB)) m1 m2).
  { intros W m1 m2 MU HW. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. clear MU. intros a Ha.
    induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn [outside fst snd] in H1 |- *.
    split; [exact (proj2 (BLK a lo' hi' Ha H1))| exact (IH H2)]. }
  assert (ACL : forall a lo' hi', aclient_addr (OW ++ LB) (bv_unsigned sp) a -> (shad f <= lo' /\ hi' <= shad f + 128) \/ (f <= lo' /\ hi' <= f + 1024) ->
                 (aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a) /\ ~ (lo' <= a < hi')).
  { intros a lo' hi' [Hs|[Hst|Hb]] Hlh.
    - split; [left; left; clear - Hs SPAH; lia| clear - Hs Hlh SHR G3 CEIL LO D2 BWSR; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia].
    - split; [left; right; left; exact Hst|]. destruct Hst as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
      clear - Hin Hr Hlh G4 SHR. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
    - exact (BLK a lo' hi' Hb Hlh). }
  assert (ACLW : forall W m1 m2, munch W m1 m2 -> Forall (fun iv => (shad f <= fst iv /\ snd iv <= shad f + 128) \/ (f <= fst iv /\ snd iv <= f + 1024)) W ->
                 agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m1 m2).
  { intros W m1 m2 MU HW. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. clear MU. intros a Ha.
    induction W as [|[lo' hi'] W IH]; [exact I|]. apply Forall_cons_iff in HW as [H1 H2]. cbn [outside fst snd] in H1 |- *.
    split; [exact (proj2 (ACL a lo' hi' Ha H1))| exact (IH H2)]. }
  apply (PREAG m m3) in HPRE; [| eapply agree_on_mono; [exact AGF|]; intros a Ha; right; right; exact Ha].
  apply (bytes_at_agree _ _ _ _ _ AGF) in VAA; [| intros a Ha; rewrite u64s_length in Ha; left; unfold USTACK_TOP; clear - Ha VA1 VA2; unfold zlength in *; lia].
  apply (fun H => vargsA_ok_agree OW LB m m3 slots args H (agree_on_mono _ _ _ _ AGF ltac:(intros a Ha; right; right; exact Ha))) in VARGS.
  pose proof (munch_refl [(spa, spa)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step. step.
  (* [comment removed for export] *)
  assert (OFFL : forall b, In b LB -> off_fr f 4 b) by (intros b Hb; apply FRESH; apply in_or_app; right; exact Hb).
  apply evt_done. eapply cps_step_same.
  { eapply (@set_shadow_cpsA (push AR f 4) 248) with (lo := lo) (OW := OW) (LB := LB) (f := f) (k := 4%nat) (d := shad f + 12) (n := 64);
      try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP, BnHeapA.ACEIL; cbn [ar_SP0 push amb];
      first [cbn; tauto | left; reflexivity | clear - CEIL LO SPAL BWSR; lia | clear - SPT SPAH; lia | clear - SPA32; Z.div_mod_to_equations; lia
            | change (fs_size 4) with 1024; clear; lia | clear; lia | f_equal; clear - SHR; lia]. }
  intros msb (v0 & v1 & v2 & w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & v3 & v4 & v5 & v6 & Fb & fcb & m4 & -> & MI4 & ST4 & HEAP4 & WM4 & AG4 & BZ4 & WR4).
  rewrite ?ESPA in *. unfold BVPF_SS1_RA, MallocRep.wz. rewrite (ret_pc_even 0x23aee0) by (clear; lia).
  (* [comment removed for export] *)
  assert (STK4 : forall x, spa <= x < 140737488355328 -> (aclient_addr (OW ++ LB) spa x \/ @fr_addr (push AR f 4) x) /\ ~ (shad f + 12 <= x < shad f + 12 + 64)).
  { intros x Hx. split; [left; left; unfold USTACK_TOP; exact Hx| clear - Hx SHR D2 CEIL LO SPAL BWSR; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]. }
  apply (PREAG m3 m4) in HPRE; [| eapply agree_on_mono; [exact AG4|]; intros a Ha; apply BLK; [exact Ha| left; clear; lia]].
  apply (bytes_at_agree _ _ _ _ _ AG4) in VAA; [| intros a Ha; rewrite u64s_length in Ha; apply STK4; clear - Ha VA1 VA2 SPAH; unfold zlength in *; lia].
  apply (fun H => vargsA_ok_agree OW LB m3 m4 slots args H (agree_on_mono _ _ _ _ AG4 ltac:(intros a Ha; apply BLK; [exact Ha| left; clear; lia]))) in VARGS.
  apply (rw_cells_agree _ _ _ _ _ AG4) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG4) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG4) in FRF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; clear - Ha; lia]| clear - Ha SHR G5; lia]].
  unfold bvpf_shadow_pro in FRS.
  apply (rw_cells_split_CB ctasegs _ _ [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 248); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242); C1 (Z_to_bv 8 242)]
           116 jst [] [64; 1; 1; 1; 1; 1; 1; 1; 1; 44]%nat) in FRS; [| reflexivity]. cbn [mk_CB_cells app] in FRS.
  lazymatch type of FRS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: CB 64 ?jm :: ?tl) =>
    apply (shadow_mid_update m3 m4 (shad f) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] tl 64 jm 248 (fun a => aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a)) in FRS;
    [| cbn [cells_size csize Nat.add]; exact AG4
     | intros a Ha; cbn [cells_size csize Nat.add app] in Ha; right; right; exists f, 4%nat; split; [left; reflexivity| rewrite shad_fr_end; change (fs_size 4 / 8) with 128; clear - Ha; lia]
     | cbn [cells_size csize Nat.add]; exact BZ4 | cbn [cells_size csize Nat.add]; exact WR4 ] end.
  cbn [app] in FRS.
  pose proof (munch_refl [(f + 32, f + 40); (f + 64, f + 72); (shad f + 8, shad f + 9); (shad f + 76, shad f + 84)]%Z m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4'.
  clear MU3 WM3.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. do 8 sbstep.
  step. sbstep.
  (* [comment removed for export] *)
  step. step. step.
  name_mem m5.
  match goal with H : munch _ m4 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m4 m5 |- _ => rename H into WM5 end.
  assert (FRW5 : Forall (@fr_write_ok (push AR f 4) (OW ++ LB) f 4) [(f + 32, f + 40); (f + 64, f + 72); (shad f + 8, shad f + 9); (shad f + 76, shad f + 84)]%Z).
  { change (fs_size 4) with 1024. clear.
    constructor; [right; left; cbn [fst snd]; change (fs_size 4) with 1024; lia|]. constructor; [right; left; cbn [fst snd]; change (fs_size 4) with 1024; lia|].
    constructor; [right; right; cbn [fst snd]; change (fs_size 4 / 8) with 128; lia|]. constructor; [right; right; cbn [fst snd]; change (fs_size 4 / 8) with 128; lia| constructor]. }
  assert (HEAP5 : @BnHeapA.AHEAP (push AR f 4) Σ1 OW LB m5).
  { eapply (@AH_frame_fr (push AR f 4) Σ1 OW LB m4 m5 _ f 4%nat (or_introl eq_refl) HEAP4 MU5 WM5 FRW5 OFFL). }
  apply (fun H => vargsA_ok_agree OW LB m4 m5 slots args H (BLKW _ m4 m5 MU5 ltac:(clear; repeat constructor; cbn [fst snd]; lia))) in VARGS.
  apply (PREAG m4 m5) in HPRE; [| exact (BLKW _ m4 m5 MU5 ltac:(clear; repeat constructor; cbn [fst snd]; lia))].
  apply evt_done. eapply cps_step_same.
  { eapply (@set_shadow_cpsA (push AR f 4) 0) with (lo := lo) (OW := OW) (LB := LB) (f := f) (k := 4%nat) (d := shad f + 12) (n := 64);
      try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP, BnHeapA.ACEIL; cbn [ar_SP0 push amb];
      first [cbn; tauto | left; reflexivity | clear - CEIL LO SPAL BWSR; lia | clear - SPT SPAH; lia | clear - SPA32; Z.div_mod_to_equations; lia
            | change (fs_size 4) with 1024; clear; lia | clear; lia | f_equal; clear - SHR; lia]. }
  intros msc (v0' & v1' & v2' & w0' & w1' & w2' & w3' & w4' & w5' & w6' & w7' & v3' & v4' & v5' & v6' & Fc & fcc & m6 & -> & MI6 & ST6 & HEAP6 & WM6 & AG6 & BZ6 & WR6).
  rewrite ?ESPA in *. unfold BVPF_SS2_RA, MallocRep.wz. rewrite (ret_pc_even 0x23af18) by (clear; lia).
  apply (PREAG m5 m6) in HPRE; [| eapply agree_on_mono; [exact AG6|]; intros a Ha; apply BLK; [exact Ha| left; clear; lia]].
  apply (bytes_at_agree _ _ _ _ _ AG6) in VAA; [| intros a Ha; rewrite u64s_length in Ha; apply STK4; clear - Ha VA1 VA2 SPAH; unfold zlength in *; lia].
  apply (fun H => vargsA_ok_agree OW LB m5 m6 slots args H (agree_on_mono _ _ _ _ AG6 ltac:(intros a Ha; apply BLK; [exact Ha| left; clear; lia]))) in VARGS.
  apply (rw_cells_agree _ _ _ _ _ AG6) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG6) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG6) in FRF; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [right; left; exists f, 4%nat; split; [left; reflexivity| change (fs_size 4) with 1024; clear - Ha; lia]| clear - Ha SHR G5; lia]].
  lazymatch type of FRS with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: CB 64 ?jm :: ?tl) =>
    apply (shadow_mid_update m5 m6 (shad f) [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] tl 64 jm 0 (fun a => aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a)) in FRS;
    [| cbn [cells_size csize Nat.add]; exact AG6
     | intros a Ha; cbn [cells_size csize Nat.add app] in Ha; right; right; exists f, 4%nat; split; [left; reflexivity| rewrite shad_fr_end; change (fs_size 4 / 8) with 128; clear - Ha; lia]
     | cbn [cells_size csize Nat.add]; exact BZ6 | cbn [cells_size csize Nat.add]; exact WR6 ] end.
  cbn [app] in FRS.
  pose proof (munch_refl [(f + 64, f + 72)]%Z m6) as MU6. pose proof (wmono_refl ctasegs m6) as WM6'.
  try clear MU4; try clear WM4'. clear WM5.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step. step. step. step. step.
  name_mem m7.
  match goal with H : munch _ m6 m7 |- _ => rename H into MU7 end. match goal with H : wmono ctasegs m6 m7 |- _ => rename H into WM7 end.
  assert (FRW7 : Forall (@fr_write_ok (push AR f 4) (OW ++ LB) f 4) [(f + 64, f + 72)]%Z).
  { constructor; [right; left; cbn [fst snd]; change (fs_size 4) with 1024; clear; lia| constructor]. }
  assert (HEAP7 : @BnHeapA.AHEAP (push AR f 4) Σ1 OW LB m7).
  { eapply (@AH_frame_fr (push AR f 4) Σ1 OW LB m6 m7 _ f 4%nat (or_introl eq_refl) HEAP6 MU7 WM7 FRW7 OFFL). }
  apply (fun H => vargsA_ok_agree OW LB m6 m7 slots args H (BLKW _ m6 m7 MU7 ltac:(clear; repeat constructor; cbn [fst snd]; lia))) in VARGS.
  apply (PREAG m6 m7) in HPRE; [| exact (BLKW _ m6 m7 MU7 ltac:(clear; repeat constructor; cbn [fst snd]; lia))].
  (* [comment removed for export] *)
  assert (ACCB : acc ctasegs m7 (f + 96) 512).
  { eapply (acc_of_shadow_cells m7 (shad f) _ 12 (f + 96) 512 FRS); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
      | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity]. }
  apply evt_done. eapply cps_step_same.
  { eapply (vsnprintf_cpsA (push AR f 4) PFC) with (lo := lo) (OW := OW) (LB := LB) (f := f) (k := 4%nat) (D := f + 96) (nD := 512) (A := A) (VA := VA) (fmt := fmt) (slots := slots) (args := args) (o := o);
      try reflexivity; rewrite ?ESPA;
      [exact HEAP7| assumption| exact CEIL| unfold RT_STACK in *; clear - LO SPAL BWSR; lia| unfold USTACK_TOP; clear - SPT SPAH; lia| clear - SPA32; Z.div_mod_to_equations; lia
      | assumption| cbn [ar_FR push amb]; left; reflexivity| exact FRESH| clear; lia| change (fs_size 4) with 1024; clear; lia| exact ACCB| exact VF
      | rewrite <- En; clear - OLEN; lia| clear; lia| exact VAA| clear - VA1 SPAH SPAL; lia| unfold USTACK_TOP; clear - VA2; lia| exact VARGS]. }
  intros msd (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & Fd & fcd & m8 & -> & MI8 & ST8 & HEAP8 & WM8 & AG8 & BZ8).
  rewrite <- ?En in *. rewrite ?ESPA in *. unfold MallocRep.wz. rewrite (ret_pc_even 0x23af34) by (clear; lia).
  (* [comment removed for export] *)
  apply (PREAG m7 m8) in HPRE; [| eapply agree_on_mono; [exact AG8|]; intros a Ha; apply BLK; [exact Ha| right; clear - OLEN; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply STK4; clear - Ha GSZ SPT SPAH; lia| clear - Ha G3 CEIL LO SPAL GSZ OLEN BWSR; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; split; [apply STK4; clear - Ha SPT SPAH; lia| clear - Ha G3 CEIL LO SPAL SPAH OLEN BWSR; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia]].
  clear VAA FRF.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG8) in FRS;
    [| intros a Ha; cbn [cells_size csize Nat.add app] in Ha; split;
       [right; right; exists f, 4%nat; split; [left; reflexivity| rewrite shad_fr_end; change (fs_size 4 / 8) with 128; clear - Ha; lia]| clear - Ha SHR G5 OLEN; lia]].
  assert (ACCB8 : acc ctasegs m8 (f + 96) 512).
  { eapply (acc_of_shadow_cells m8 (shad f) _ 12 (f + 96) 512 FRS); [clear - G2; Z.div_mod_to_equations; lia| clear - G1; lia| clear; lia
      | unfold shad; clear - G2; Z.div_mod_to_equations; lia| cbn; clear; lia| reflexivity]. }
  clear ACCB FRS.
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [pd Hpd].
  assert (HEAP8' : @BnHeapA.AHEAP (push AR f 4) Σ1 OW ((pd, f + 96, 512) :: LB) m8).
  { apply (@frame_obj_open (push AR f 4) Σ1 OW LB m8 f 4%nat pd (f + 96) 512 (or_introl eq_refl) HEAP8);
      [clear; lia| change (fs_size 4) with 1024; clear; lia| clear; lia| exact ACCB8| exact Hpd|].
    intros b Hb. pose proof (OFFL b Hb) as O. unfold off_fr in O. unfold blk_apart. change (fs_size 4) with 1024 in O. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
  pose proof (munch_refl []%Z m8) as MU8. pose proof (wmono_refl ctasegs m8) as WM8'.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. if_cases Hqn; zify_cond Hqn; [exfalso; clear - Hqn OLEN; lia|]. clear Hqn.
  step. step. if_cases Hqm; zify_cond Hqm; [| exfalso; clear - Hqm OLEN; lia]. clear Hqm.
  step. step. step.
  (* [comment removed for export] *)
  apply evt_done. eapply cps_step_rt.
  { pose proof (HBW f) as HP. unfold bio_write_calleeG in HP. cbn [ar_RT ar_PMc ar_FR push amb] in HP.
    eapply HP with (lo := lo) (LB := (pd, f + 96, 512) :: LB) (pd := pd); clear HP; rewrite ?ESPA;
      [exact HEAP8'| left; reflexivity| exact ST8| exact CEIL| clear - LO SPAL BWSR; lia| unfold USTACK_TOP; clear - SPT SPAH; lia
      | clear - SPA32; Z.div_mod_to_equations; lia| exact MI8| reflexivity| cbn [length]; exact FLEN| rewrite CR1; clear - CRED; lia| exact HPRE| first [exact BZ8| rewrite <- En; exact BZ8| rewrite En; exact BZ8]
      | reflexivity| reflexivity| first [reflexivity| rewrite En; reflexivity| rewrite <- En; reflexivity]]. }
  clear MU8 WM8'. intros Σ2 mse PO EL2. cbv beta in PO. unfold bwG_post in PO.
  destruct PO as (y0' & y1' & y2' & z1' & z2' & z3' & z4' & z5' & z6' & z7' & y3' & y4' & y5' & y6' & Fe & fce & m9 & -> & MI9 & ST9 & APX9 & HEAP9' & EL9 & CR9 & HPOST).
  rewrite <- ?En in *.
  unfold MallocRep.wz in *. rewrite (ret_pc_even 0x23afac) by (clear; lia). rewrite ?ESPA in *.
  assert (STW9 : forall a, spa <= a < 140737488355328 -> aclient_addr (OW ++ (pd, f + 96, 512) :: LB) spa a /\ outside XW a).
  { intros a Ha. split; [left; exact Ha|]. apply XWS. clear - Ha CEIL LO SPAL BWSR; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia. }
  (* [comment removed for export] *)
  pose proof (@frame_obj_close (push AR f 4) Σ2 OW LB m9 f 4%nat (pd, f + 96, 512) (or_introl eq_refl) HEAP9' ltac:(unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 4) with 1024; clear; lia)) as HEAP9.
  apply (rw_cells_agree _ _ _ _ _ APX9) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW9; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ APX9) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW9; clear - Ha SPT SPAH; lia].
  pose proof (munch_refl []%Z m9) as MU9. pose proof (wmono_refl ctasegs m9) as WM9'.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step. step. step. step.
  apply evt_done. eapply cps_step_same.
  { eapply (@set_shadow_cpsA (push AR f 4) 248) with (lo := lo) (OW := OW) (LB := LB) (f := f) (k := 4%nat) (d := shad f + 12) (n := 64);
      try reflexivity; rewrite ?ESPA; try eassumption; unfold RT_STACK, USTACK_TOP, BnHeapA.ACEIL; cbn [ar_SP0 push amb];
      first [cbn; tauto | left; reflexivity | clear - CEIL LO SPAL BWSR; lia | clear - SPT SPAH; lia | clear - SPA32; Z.div_mod_to_equations; lia
            | change (fs_size 4) with 1024; clear; lia | clear; lia | f_equal; clear - SHR; lia]. }
  clear MU9 WM9'. intros msg (v0'' & v1'' & v2'' & w0'' & w1'' & w2'' & w3'' & w4'' & w5'' & w6'' & w7'' & v3'' & v4'' & v5'' & v6'' & Fg & fcg & m10 & -> & MI10 & ST10 & HEAP10 & WM10 & AG10 & BZ10 & WR10).
  rewrite ?ESPA in *. unfold BVPF_SS3_RA, MallocRep.wz. rewrite (ret_pc_even 0x23afbc) by (clear; lia).
  apply (POSTAG m9 m10) in HPOST; [| eapply agree_on_mono; [exact AG10|]; intros a Ha; apply BLK; [exact Ha| left; clear; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG10) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ AG10) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STK4; clear - Ha SPT SPAH; lia].
  (* [comment removed for export] *)
  destruct (@AH_fr_wr (push AR f 4) _ _ _ _ f 4%nat HEAP10 (or_introl eq_refl)) as [_ WS10]. change (fs_size 4) with 1024 in WS10.
  destruct (wr_at_rw_CB m10 (shad f) _ WS10 ltac:(clear; lia)) as (js10 & FRS10). change (Z.to_nat (1024 / 8)) with 128%nat in FRS10.
  apply (rw_cells_split_CB ctasegs _ _ [] 128 _ [] [8; 1; 119]%nat) in FRS10; [| reflexivity]. cbn [mk_CB_cells app] in FRS10.
  pose proof (munch_refl [(shad f + 8, shad f + 9)]%Z m10) as MU10. pose proof (wmono_refl ctasegs m10) as WM10'.
  apply cps_from_evt'.
  sbstep.
  name_mem m11.
  match goal with H : munch _ m10 m11 |- _ => rename H into MU11 end. match goal with H : wmono ctasegs m10 m11 |- _ => rename H into WM11 end.
  assert (FRW11 : Forall (@fr_write_ok (push AR f 4) (OW ++ LB) f 4) [(shad f + 8, shad f + 9)]%Z).
  { constructor; [right; right; cbn [fst snd]; change (fs_size 4 / 8) with 128; clear; lia| constructor]. }
  assert (HEAP11 : @BnHeapA.AHEAP (push AR f 4) Σ2 OW LB m11).
  { eapply (@AH_frame_fr (push AR f 4) Σ2 OW LB m10 m11 _ f 4%nat (or_introl eq_refl) HEAP10 MU11 WM11 FRW11 OFFL). }
  apply (POSTAG m10 m11) in HPOST; [| exact (BLKW _ m10 m11 MU11 ltac:(clear; repeat constructor; cbn [fst snd]; lia))].
  (* [comment removed for export] *)
  apply evt_done.
  eapply (bvpf_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []); rewrite ?ESPA;
    [exact HEAP11 | exact OFFL | assumption | exact CEIL | clear - LO SPAL BWSR; lia | unfold RT_STACK; clear - LO SPAL BWSR; lia | exact SPA32 | unfold USTACK_TOP; clear - SPT; lia
    | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | assumption | exact FRL | exact FRH | reflexivity |].
  intros Σ' m' x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x28' x29' x30' x31' F3 fc3 HEAP' CR' EL' ST' MI' AG'.
  apply (POSTAG m11 m') in HPOST; [| eapply agree_on_mono; [exact AG'|]; intros a Ha; right; right; exact Ha].
  apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL9, EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold bio_vprintfG_post, MallocRep.wz.
  do 16 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { (* [comment removed for export] *)
    assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    assert (INC' : forall b : block, In b (OW ++ LB) -> In b (OW ++ (pd, f + 96, 512) :: LB)).
    { intros b Hb. apply in_app_iff in Hb. apply in_or_app. destruct Hb as [Hb|Hb]; [left; exact Hb| right; right; exact Hb]. }
    assert (STEPA : forall (mA mB : mem) lo' hi', agree_on (fun a => (aclient_addr (OW ++ LB) spa a \/ @fr_addr (push AR f 4) a) /\ ~ (lo' <= a < hi')) mA mB ->
                    (shad f <= lo' /\ hi' <= shad f + 128) \/ (f <= lo' /\ hi' <= f + 1024) ->
                    agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside XW a) mA mB).
    { intros mA mB lo' hi' AGx Hlh. eapply agree_on_mono; [exact AGx|]. intros a [Ha _]. exact (ACL a lo' hi' Ha Hlh). }
    assert (STEPW : forall (mA mB : mem) W, munch W mA mB -> Forall (fun iv => (shad f <= fst iv /\ snd iv <= shad f + 128) \/ (f <= fst iv /\ snd iv <= f + 1024)) W ->
                    agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside XW a) mA mB).
    { intros mA mB W MU HW. eapply agree_on_mono; [exact (ACLW W mA mB MU HW)|]. intros a [Ha _]. exact Ha. }
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha|].
    eapply agree_on_trans; [eapply (STEPA m3 m4); [exact AG4| left; clear; lia]|].
    eapply agree_on_trans; [eapply (STEPW m4 m5); [exact MU5| clear; repeat constructor; cbn [fst snd]; lia]|].
    eapply agree_on_trans; [eapply (STEPA m5 m6); [exact AG6| left; clear; lia]|].
    eapply agree_on_trans; [eapply (STEPW m6 m7); [exact MU7| clear; repeat constructor; cbn [fst snd]; lia]|].
    eapply agree_on_trans; [eapply (STEPA m7 m8); [exact AG8| right; clear - OLEN; lia]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact APX9|]; intros a [Ha Hx]; split; [eapply acl_sub; [exact INC'| | exact Ha]; clear - SPAH; lia| exact Hx]|].
    eapply agree_on_trans; [eapply (STEPA m9 m10); [exact AG10| left; clear; lia]|].
    eapply agree_on_trans; [eapply (STEPW m10 m11); [exact MU11| clear; repeat constructor; cbn [fst snd]; lia]|].
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. eapply acl_sub; [exact INC| | exact Ha]. clear - SPAH; lia. }
  split; [exact HEAP'|].
  split; [rewrite EL', EL9, EL1; reflexivity|]. split; [rewrite CR'; clear - CR9 CR1; cbn [ar_RT push amb] in *; lia|].
  exact HPOST.
Qed.

End WithPFC.
End WithRT.

Section WithRT2.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Section WithPFC2.
Hypothesis PFC : printf_contracts RT.

(* [comment removed for export] *)
Definition bio_printfG_post (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (Σ : rts RT) (OW LB : list block) (XW : list (Z * Z)) (POST : mem -> Prop) (CST n lo : Z) (m : mem) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m',
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 n) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ outside XW a) m m'
    /\ AHEAP Σ' OW LB m'
    /\ rt_live RT Σ' = rt_live RT Σ /\ rt_credit RT Σ - (2 + CST) <= rt_credit RT Σ'
    /\ POST m'.

(* [comment removed for export] *)
Lemma BIO_printf_gen_cpsA : forall
    (bio : Z) (PRE POST : mem -> Prop) (XW : list (Z * Z)) (CST BWS : Z) (NFR : nat)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (A : Z)
    (fmt : list Z) (args : list parg) (o : list Z),
  (forall m1 m2, agree_on (in_block (OW ++ LB)) m1 m2 -> PRE m1 -> PRE m2) ->
  (forall m1 m2, agree_on (in_block (OW ++ LB)) m1 m2 -> POST m1 -> POST m2) ->
  Forall (fun iv => exists b, In b (OW ++ LB) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b) XW ->
  0 <= CST -> RT_STACK <= BWS ->
  (forall f f', bio_write_calleeG (push (push AR f 0) f' 4) OW bio PRE POST XW CST BWS NFR o) ->
  AHEAP Σ OW LB m ->
  stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + BPRF_FRAME + BVPF_FRAME + BWS <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> (S (S (length FR)) + NFR <= FRAMES_MAX)%nat -> 2 + CST <= rt_credit RT Σ ->
  PRE m ->
  vfmtA_ok A fmt args o -> 0 <= zlength o < 512 -> vargsA_ok OW LB m [a2; a3; a4; a5; a6; a7] args ->
  a0 = wz bio -> a1 = wz A ->
  cps ctasegs (ASTA RT Σ PMc (eq (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                   F (wz BIO_PRINTF_A) fc None m (seg_rom ctasegs))))
      (fun c => exists Σ', ASTA RT Σ' PMc (bio_printfG_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB XW POST CST (zlength o) lo m Σ') c
                /\ rt_live RT Σ' = rt_live RT Σ)      (* [comment removed for export] *).
Proof.
  intros until o. intros PREAG POSTAG XWOK CST0 BWSR HBW HEAP ST CEIL LO SPT SP16 MI TP FLEN CRED HPRE VF OLEN VARGS -> ->.
  unfold BPRF_FRAME, BVPF_FRAME, RT_STACK, BIO_PRINTF_A, MallocRep.wz in *.
  remember (zlength o) as n eqn:En.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (CL1 & CL2 & CL3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CL1, CL2, CL3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (XWS : forall a, lo <= a -> outside XW a).
  { intros a Ha. clear - XWOK HEAP Ha CEIL. induction XWOK as [|[x y] XW (b & Hb & R1 & R2) HW IH]; [exact I|]. cbn [outside fst snd] in *. split; [| exact IH].
    pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in *. lia. }
  (* [comment removed for export] *)
  change (Z_to_bv 64 2337804) with (Z_to_bv 64 BPRF_ENTRY).
  eapply (bprf_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP | exact ST | exact CEIL | unfold BPRF_FRAME, RT_STACK; clear - LO BWSR; lia | unfold USTACK_TOP; clear - SPT; lia | exact SP16
    | exact MI | exact TP | clear - FLEN; lia | clear - CRED CST0; lia |].
  intros Σ1 m3 f spa g jk gj ra' t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' j0 jf24 jf40
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  unfold BPRF_BODY, MallocRep.wz.
  pose proof (@AH_ceil (push AR f 0) _ _ _ _ HEAP3) as (D1 & D2 & D3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in D1, D2, D3. cbn [ar_SP0 push amb] in D1, D2, D3.
  destruct GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 0) with 64 in G3, G5. unfold SEGTOP_A in G4.
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - SPAL SPAH SPR LO LO0 BWSR; lia).
  apply (PREAG m m3) in HPRE; [| eapply agree_on_mono; [exact AGF|]; intros a Ha; right; right; exact Ha].
  apply (fun H => vargsA_ok_agree OW LB m m3 _ args H (agree_on_mono _ _ _ _ AGF ltac:(intros a Ha; right; right; exact Ha))) in VARGS.
  (* [comment removed for export] *)
  pose proof (rw_cells_skip m3 (bv_unsigned sp + -64) [C8 s0; C8 ra] [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7] _ FRH eq_refl) as FRV.
  cbn [cells_size csize Nat.add app] in FRV. replace (bv_unsigned sp + -64 + Z.of_nat 16) with (bv_unsigned sp + -48) in FRV by (clear; lia).
  pose proof (munch_refl []%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  apply cps_from_evt'.
  (* [comment removed for export] *)
  step.
  apply evt_done. eapply cps_step_rt.
  { pose proof (@BIO_vprintf_gen_cpsA (push AR f 0) PFC bio PRE POST XW CST BWS NFR) as HP. cbn [ar_RT ar_PMc ar_FR push amb] in HP.
    eapply HP with (lo := lo) (OW := OW) (LB := LB) (A := A) (VA := bv_unsigned sp + -48)
                   (fmt := fmt) (slots := [a2; a3; a4; a5; a6; a7]) (args := args) (o := o); clear HP; rewrite ?ESPA;
      [exact PREAG| exact POSTAG| exact XWOK| exact CST0| exact BWSR| intros f'; exact (HBW f f')
      | exact HEAP3| exact ST3| exact CEIL| unfold BVPF_FRAME; clear - LO SPAL BWSR; lia
      | unfold USTACK_TOP; clear - SPT SPAH; lia| clear - SPA32; Z.div_mod_to_equations; lia| exact MI3| reflexivity| cbn [length]; exact FLEN
      | rewrite CR1; clear - CRED; lia| exact HPRE| exact VF| rewrite <- En; exact OLEN| exact (proj2 (proj1 FRV))
      | clear - SPAH; lia| unfold USTACK_TOP, zlength in *; cbn [length]; clear - SPT; lia| exact VARGS| reflexivity| reflexivity| reflexivity]. }
  clear MU3 WM3. intros Σ2 mse PO EL2. cbv beta in PO.
  unfold bio_vprintfG_post in PO.
  destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & Fe & fce & m4 & -> & MI4 & ST4 & APX4 & HEAP4 & EL4 & CR4 & HPOST).
  unfold MallocRep.wz in *. rewrite (ret_pc_even 0x23ad24) by (clear; lia). rewrite ?ESPA in *. rewrite <- ?En in *.
  assert (STW4 : forall a, spa <= a < 140737488355328 -> aclient_addr (OW ++ LB) spa a /\ outside XW a).
  { intros a Ha. split; [left; exact Ha|]. apply XWS. clear - Ha CEIL LO SPAL BWSR; unfold BnHeapA.ACEIL in *; cbn [ar_SP0 push amb] in *; lia. }
  apply (rw_cells_agree _ _ _ _ _ APX4) in FRL; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW4; clear - Ha GSZ SPT SPAH; lia].
  apply (rw_cells_agree _ _ _ _ _ APX4) in FRH; [| intros a Ha; cbn [cells_size csize Nat.add] in Ha; apply STW4; clear - Ha SPT SPAH; lia].
  clear FRV FRF FRS.
  (* [comment removed for export] *)
  change (Z_to_bv 64 2338084) with (Z_to_bv 64 BPRF_EXIT).
  eapply (bprf_epi_cps _) with (lo := lo) (LB := LB) (gj := gj) (hrest := [C8 a2; C8 a3; C8 a4; C8 a5; C8 a6; C8 a7]); rewrite ?ESPA;
    [exact HEAP4 | intros b Hb; apply FRESH; apply in_or_app; right; exact Hb | exact ST4 | exact CEIL | clear - LO SPAL BWSR; lia | unfold USTACK_TOP; clear - SPT; lia
    | exact SPAL | exact SPAH | exact GSZ | exact SAVJ | exact MI4 | exact FRL | exact FRH | reflexivity |].
  intros Σ' m' x11' HEAP' CR' EL' ST' MI' AG'.
  apply (POSTAG m4 m') in HPOST; [| eapply agree_on_mono; [exact AG'|]; intros a Ha; right; right; exact Ha].
  apply cps_post. intros c Hc. exists Σ'. split; [| rewrite EL', EL4, EL1; reflexivity].
  eapply ASTA_conseq; [exact Hc|]. intros ms0 <-. unfold bio_printfG_post, MallocRep.wz.
  do 16 eexists. exists m'. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split.
  { assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    eapply agree_on_trans; [eapply agree_on_mono; [exact AGF|]; intros a [Ha _]; exact Ha|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact APX4|]; intros a [Ha Hx]; split; [eapply acl_sub; [exact INC| | exact Ha]; clear - SPAH; lia| exact Hx]|].
    eapply agree_on_mono; [exact AG'|]. intros a [Ha _]. eapply acl_sub; [exact INC| | exact Ha]. clear - SPAH; lia. }
  split; [exact HEAP'|].
  split; [rewrite EL', EL4, EL1; reflexivity|]. split; [rewrite CR'; clear - CR4 CR1; cbn [ar_RT push amb] in *; lia|].
  exact HPOST.
Qed.
End WithPFC2.
End WithRT2.
