(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.openssl.bignum.lib.BgLib Require Import ImageBgA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.openssl.bignum.lib.Lib Require Import Tac ZBridge RzCPS. 
From OSSVerify.Proofs.openssl.bignum.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.bignum.lib.Spec Require Import Malloc Prog BnBase BnModel BnTree BnInv BgState BgInv BgLib.
From OSSVerify.Proofs.openssl.bignum.lib.A Require Import Shadow.
From OSSVerify.Proofs.openssl.bignum.lib.BgA Require Import Layout R_unwind_chain RT_iface RT_iface2 RT_client_kit D_defs I_lkit.
From OSSVerify.Proofs.openssl.bignum.lib.BnW Require Import BnTac BnMem BnTacX.
From OSSVerify.Proofs.openssl.bignum.lib.BnP Require Import BnKit BnKit2.
From OSSVerify.Proofs.openssl.bignum.lib.BnAsan Require Import AsKit.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require Import LibKitA ARun BnHeapA ImplA UnwindA.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnAsan Require BnRepDefs BnRepA BnIfaceA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgRepDefs BgRep BgLayer BgIface.
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnCallAF.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rw_cells_app_l : forall (m : mem) a cs1 cs2, rw_cells bgasegs m a (cs1 ++ cs2) -> rw_cells bgasegs m a cs1.
Proof.
  intros m a cs1 cs2 ((Hwf & Hb) & Hw). apply cells_wf_app in Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb as [Hb1 _].
  split; [split; [exact W1 | exact Hb1]|].
  destruct Hw as (X1 & X2 & X3). rewrite cells_size_app, Nat2Z.inj_add in X2, X3.
  split; [exact X1|]. split; [lia|]. intros i Hi. apply X3. lia.
Qed.

Lemma rw_cells_app_join : forall (m : mem) a cs1 cs2,
  rw_cells bgasegs m a cs1 -> rw_cells bgasegs m (a + Z.of_nat (cells_size cs1)) cs2 -> rw_cells bgasegs m a (cs1 ++ cs2).
Proof.
  intros m a cs1 cs2 ((W1 & B1) & (X1 & X2 & X3)) ((W2 & B2) & (Y1 & Y2 & Y3)).
  split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite (cells_bytes_length cs1 W1). exact B2.
  - rewrite cells_size_app, Nat2Z.inj_add. split; [exact X1|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_dec i (Z.of_nat (cells_size cs1))) as [L|L]; [apply X3; lia|].
    replace (a + i) with (a + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply Y3. lia.
Qed.

Fixpoint cb_first (n : nat) (cs : list cell) : list cell :=
  match n, cs with S n', c :: cs' => CB (csize c) (cbytes c) :: cb_first n' cs' | _, _ => cs end.

Lemma cb_first_props : forall n cs, cells_wf cs -> cells_wf (cb_first n cs) /\ cells_bytes (cb_first n cs) = cells_bytes cs /\ cells_size (cb_first n cs) = cells_size cs.
Proof.
  induction n as [|n IH]; intros cs W; [cbn; auto|]. destruct cs as [|c cs]; [cbn; auto|].
  cbn [cells_wf] in W. destruct W as [Wc Wr]. destruct (IH cs Wr) as (I1 & I2 & I3).
  cbn [cb_first cells_wf cells_bytes cells_size cell_wf csize cbytes]. rewrite I2, I3.
  split; [split; [exact (cbytes_length c Wc) | exact I1]|]. split; reflexivity.
Qed.

Definition fr_list (nl ns : nat) (cs : list cell) : list cell :=
  cb_first nl (firstn nl cs) ++ CB (cells_size (firstn ns (skipn nl cs))) (cells_bytes (firstn ns (skipn nl cs))) :: skipn ns (skipn nl cs).

Lemma rw_cells_fr_list : forall (m : mem) a cs nl ns, rw_cells bgasegs m a cs -> rw_cells bgasegs m a (fr_list nl ns cs).
Proof.
  intros m a cs nl ns H. unfold fr_list.
  rewrite <- (firstn_skipn nl cs) in H. rewrite <- (firstn_skipn ns (skipn nl cs)) in H.
  apply (rw_cells_merge bgasegs m a (firstn nl cs) (firstn ns (skipn nl cs)) (skipn ns (skipn nl cs))) in H.
  pose proof H as [[W _] _]. apply cells_wf_app in W as [W1 W2].
  destruct (cb_first_props nl (firstn nl cs) W1) as (P1 & P2 & P3).
  apply (rw_cells_recast m a _ _ H).
  - apply cells_wf_app. split; [exact P1 | exact W2].
  - rewrite !cells_bytes_app, P2. reflexivity.
  - rewrite !cells_size_app, P3. reflexivity.
Qed.

Lemma fr_saved : forall (m : mem) spa loc g junk gj (sav tail : list cell) SPv,
  rw_cells bgasegs m spa ((loc ++ [CB g junk]) ++ tail) ->
  junk = gj ++ cells_bytes sav -> cells_wf sav ->
  Z.of_nat (cells_size (loc ++ [CB g junk])) = SPv - spa - Z.of_nat (cells_size tail) ->
  rw_cells bgasegs m (SPv - Z.of_nat (cells_size sav) - Z.of_nat (cells_size tail)) (sav ++ tail).
Proof.
  intros m spa loc g junk gj sav tail SPv H EJ WS SZ.
  rewrite <- app_assoc in H. pose proof (rw_cells_app_r m spa loc _ H) as R. cbn [app] in R.
  pose proof R as [[WR _] _]. cbn [cells_wf cell_wf] in WR. destruct WR as [LJ WT].
  assert (LG : (g = length gj + cells_size sav)%nat) by (rewrite <- LJ, EJ, length_app, (cells_bytes_length sav WS); reflexivity).
  assert (R2 : rw_cells bgasegs m (spa + Z.of_nat (cells_size loc)) ([CB (length gj) gj] ++ (sav ++ tail))).
  { apply (rw_cells_recast m _ _ _ R).
    - cbn [app cells_wf cell_wf]. split; [reflexivity|]. apply cells_wf_app. split; assumption.
    - cbn [app cells_bytes cbytes]. rewrite cells_bytes_app, EJ, <- app_assoc. reflexivity.
    - cbn [app cells_size csize]. rewrite cells_size_app, LG. lia. }
  pose proof (rw_cells_app_r m _ [CB (length gj) gj] _ R2) as R3. cbn [cells_size csize] in R3.
  rewrite cells_size_app in SZ. cbn [cells_size csize] in SZ.
  replace (SPv - Z.of_nat (cells_size sav) - Z.of_nat (cells_size tail)) with (spa + Z.of_nat (cells_size loc) + Z.of_nat (length gj + 0)) by lia.
  exact R3.
Qed.

Lemma fr_whole : forall (m : mem) spa cs n, rw_cells bgasegs m spa cs -> Z.of_nat (cells_size cs) = n -> exists jall, rw_cells bgasegs m spa [CB (Z.to_nat n) jall].
Proof.
  intros m spa cs n H <-. destruct (rw_cells_forget bgasegs m spa cs H) as (j & R). exists j. rewrite Nat2Z.id. exact R.
Qed.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma implA_post : forall {A} (t : btree bptr A) Σ (Q1 Q : A -> rts RT -> machine_state -> Prop) ms,
  implA t Σ Q1 ms -> (forall a Σ' ms', Q1 a Σ' ms' -> implA (TRet a) Σ' Q ms') -> implA t Σ Q ms.
Proof.
  intros A t Σ Q1 Q ms H HK X Φ S T c Hc Hk.
  apply (H X Φ S T c Hc).
  intros c' (a & X' & Σ' & HΦ & Hc').
  destruct (ASTA_unpack RT Σ' PMc _ c' Hc') as (ms' & HQ1 & Hc'').
  exact (HK a Σ' ms' HQ1 X' Φ HΦ T c' Hc'' Hk).
Qed.

Lemma fr3_heap : forall Σ OW LB m m' f k spl sph n1 n2,
  In (f, k) FR -> AHEAP Σ OW LB m -> munch [(spl, sph); (f, f + n1); (shad f, shad f + n2)] m m' -> wmono bgasegs m m' ->
  ACEIL <= spl -> sph <= USTACK_TOP -> n1 <= fs_size k - 8 -> n2 <= fs_size k / 8 ->
  (forall b, In b LB -> off_fr f k b) -> AHEAP Σ OW LB m'.
Proof.
  intros Σ OW LB m m' f k spl sph n1 n2 Hf H MU WM L1 L2 N1 N2 OFF.
  eapply (AH_frame_fr Σ OW LB m m' _ f k Hf H MU WM); [| exact OFF].
  constructor; [left; left; cbn [fst snd]; lia|].
  constructor; [right; left; cbn [fst snd]; lia|].
  constructor; [right; right; cbn [fst snd]; lia| constructor].
Qed.

Lemma fr3_outside : forall Σ OW LB m0 f k spl sph (L : list block) a,
  AHEAP Σ OW LB m0 -> fr_geo f k -> ACEIL <= spl -> spl <= sph ->
  (forall b, In b L -> In b (OW ++ LB)) -> (forall b, In b L -> off_fr f k b) ->
  aclient_addr L sph a ->
  ~ (spl <= a < sph) /\ ~ (f <= a < f + fs_size k) /\ ~ (shad f <= a < shad f + fs_size k / 8).
Proof.
  intros Σ OW LB m0 f k spl sph L a H (G1 & G2 & G3 & G4 & G5) L1 L2 INC OFF Ha.
  pose proof (AH_ceil _ _ _ _ H) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in *.
  pose proof (fs_size_pos k) as (FS1 & _). destruct (fs_size_div8 k) as (FS2 & FS3).
  assert (SHR : 2147450880 <= shad f /\ shad f + fs_size k / 8 <= 17594333495296).
  { rewrite <- shad_fr_end. unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(lia) ltac:(lia)).
    assert ((f + fs_size k) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia. }
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - clear - Ha G3 SHR C2 L1 L2 FS1. lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    clear - Hin Hr G4 SHR C1 L1 L2. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (OFF b Hb) as O. pose proof (AH_offsh _ _ _ _ b H (INC b Hb)) as OS. pose proof (AH_range_gen _ _ _ _ b H (INC b Hb)) as (_ & _ & _ & BC & _).
    unfold off_fr, SHLO, SHHI in *. clear - O OS BC Hr SHR L1 L2. lia.
Qed.

Lemma fr3_agree : forall Σ OW LB m0 m m' f k spl sph n1 n2 (L : list block),
  AHEAP Σ OW LB m0 -> munch [(spl, sph); (f, f + n1); (shad f, shad f + n2)] m m' ->
  fr_geo f k -> n1 <= fs_size k -> n2 <= fs_size k / 8 ->
  ACEIL <= spl -> spl <= sph -> (forall b, In b L -> In b (OW ++ LB)) -> (forall b, In b L -> off_fr f k b) ->
  agree_on (aclient_addr L sph) m m'.
Proof.
  intros Σ OW LB m0 m m' f k spl sph n1 n2 L H MU GEO N1 N2 L1 L2 INC OFF.
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. cbn [outside].
  pose proof (fr3_outside Σ OW LB m0 f k spl sph L a H GEO L1 L2 INC OFF Ha) as NF.
  clear - NF N1 N2. lia.
Qed.

Lemma stack_munch_agree : forall Σ OW LB m m1 W sp, AHEAP Σ OW LB m -> munch W m m1 -> Forall (fun iv => ACEIL <= fst iv /\ snd iv <= sp) W ->
  agree_on (aclient_addr (OW ++ LB) sp) m m1.
Proof.
  intros Σ OW LB m m1 W sp HEAP MU HW. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a Ha. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _). unfold SEGTOP_A in C1. clear MU.
  induction HW as [|[x y] W [H1 H2] HW IH]; [exact I|]. cbn [outside fst snd] in *. split; [|exact IH].
  intros Hx. destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [lia | |].
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP Hb) as (_ & _ & _ & BC & _). lia.
Qed.

Lemma AH_ow_off_fr : forall Σ OW LB m f k b, AHEAP Σ OW LB m -> In (f, k) FR -> In b OW -> off_fr f k b.
Proof.
  intros Σ OW LB m f k b H Hf Hb. pose proof (AH_live_ow _ _ _ _ b H Hb) as HL.
  destruct (AH_fr_range _ _ _ _ f k H Hf) as (_ & _ & _ & _ & R). specialize (R _ _ HL). unfold off_fr. lia.
Qed.

Lemma fl_agree : forall Σ OW LB m0 m m' fl sph (L : list block),
  AHEAP Σ OW LB m0 -> munch [(fl, fl + 1)] m m' ->
  fl + 1 <= ACEIL -> ACEIL <= sph -> (fl + 1 <= 0x10000 \/ SEGTOP_A <= fl) ->
  (forall b, In b L -> fl < blk_addr b \/ blk_addr b + blk_size b <= fl) ->
  agree_on (aclient_addr L sph) m m'.
Proof.
  intros Σ OW LB m0 m m' fl sph L H MU L1 L2 L3 OFF.
  eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. cbn [outside]. split; [| exact I].
  destruct Ha as [Ha|[Ha|(b & Hb & Hr)]].
  - clear - Ha L1 L2. lia.
  - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. unfold SEGTOP_A in L3.
    clear - Hin Hr L3. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
  - pose proof (OFF b Hb) as O. clear - O Hr. lia.
Qed.

End WithRT.

Section Env.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Definition fr_env (Fb : Z) (d : nat) (f : Z) (k : nat) (objs : list block)
    (Σ : rts RT) (ls : bstate bptr) (m : mem) (OW LB : list block) (PL : placement) (EA : BnRepDefs.err_addrs) (sp : word) (lo : Z) (K C : Z)
    (s0v : Z) (ras : list Z) (spa : Z) (Σ1 : rts RT) (m1 : mem) : Prop :=
  @BnHeapA.AHEAP (push AR f k) Σ1 OW (objs ++ LB) m1
  /\ lib_state ls m1 OW PL EA
  /\ frames_ok (objs ++ LB) PL (bv_unsigned sp) USTACK_TOP
  /\ stk bgasegs m1 lo spa
  /\ ACEIL <= lo /\ lo <= spa - K
  /\ bv_unsigned sp + 16 <= USTACK_TOP /\ bv_unsigned sp mod 16 = 0
  /\ mem_inv bgasegs m1
  /\ cnt_ok ls OW (objs ++ LB) /\ C <= rt_credit RT Σ1
  /\ frames_al PL /\ frames_lb PL (objs ++ LB)
  /\ @fr_room (push AR f k) d ls OW (objs ++ LB)
  /\ spa mod 32 = 0 /\ bv_unsigned sp - Fb - 16 <= spa /\ spa <= bv_unsigned sp - Fb
  /\ rt_credit RT Σ1 = rt_credit RT Σ - 1
  /\ ax_pres LB (bv_unsigned sp) (XW PL) m m1
  /\ uw_chain USTACK_TOP m1 (bv_unsigned sp) s0v ras
  /\ (forall b, In b LB -> off_fr f k b) /\ fr_geo f k.

Lemma pro_close : forall Fb d f k objs Σ ls m OW LB PL EA sp lo STACK COST s0v ras spa Σ1 m1,
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST -> fr_room (S d) ls OW LB -> uw_chain USTACK_TOP m (bv_unsigned sp) s0v ras ->
  (length objs <= 2)%nat ->
  @BnHeapA.AHEAP (push AR f k) Σ1 OW (objs ++ LB) m1 -> stk bgasegs m1 lo spa -> mem_inv bgasegs m1 ->
  agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1 ->
  rt_credit RT Σ1 = rt_credit RT Σ - 1 -> (forall b, In b (OW ++ LB) -> off_fr f k b) -> fr_geo f k ->
  spa mod 32 = 0 -> bv_unsigned sp - Fb - 16 <= spa -> spa <= bv_unsigned sp - Fb ->
  fr_env Fb d f k objs Σ ls m OW LB PL EA sp lo (STACK - Fb - 16) (COST - 1) s0v ras spa Σ1 m1.
Proof.
  intros Fb d f k objs Σ ls m OW LB PL EA sp lo STACK COST s0v ras spa Σ1 m1
         (HEAP & LS & FROK & ST & CEIL & LOSP & TOP & AL16 & MI & CNT & CRED & FAL & NOFR) ROOM UW LEN HEAP1 ST1 MI1 AG CR1 FRESH GEO SPA32 SPAL SPAH.
  destruct (fr_room_push d f k ls OW LB objs ROOM LEN) as (_ & ROOM1 & CNT1).
  assert (INC : forall b, In b LB -> In b (objs ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
  unfold fr_env.
  split; [exact HEAP1|].
  split. { unfold lib_state in *. eapply lib_state_h_heap_pres with (L := OW ++ LB) (SP := bv_unsigned sp) (SPX := bv_unsigned sp) (BX := USTACK_TOP); [exact LS | exact FROK | lia | lia | exact AG | |];
           intros b Hb; apply in_or_app; [left | right]; exact Hb. }
  split; [exact (frames_ok_incl LB (objs ++ LB) PL _ _ FROK INC)|].
  split; [exact ST1|]. split; [exact CEIL|]. split; [clear - LOSP SPAL; lia|]. split; [exact TOP|]. split; [exact AL16|]. split; [exact MI1|].
  split; [exact CNT1|]. split; [clear - CRED CR1; lia|]. split; [exact FAL|]. split; [exact (frames_lb_incl PL LB (objs ++ LB) NOFR INC)|].
  split; [exact ROOM1|]. split; [exact SPA32|]. split; [exact SPAL|]. split; [exact SPAH|]. split; [exact CR1|].
  split. { eapply agree_on_mono; [exact AG|]. intros a [_ [Ha|[Ha|(b & Hb & Hr)]]]; [left; exact Ha | right; left; exact Ha |].
           right; right. exists b. split; [apply in_or_app; right; exact Hb | exact Hr]. }
  split. { apply (uw_chain_agree m m1 ras _ _ UW). eapply agree_on_mono; [exact AG|]. intros a Ha. left. exact Ha. }
  split; [| exact GEO]. intros b Hb. apply FRESH. apply in_or_app. right. exact Hb.
Qed.

Lemma fr_env_cenv0 : forall Fb d f k objs Σ ls m OW LB PL EA sp lo K C (s0w raw : word) ras spa Σ1 m1 pre,
  fr_env Fb d f k objs Σ ls m OW LB PL EA sp lo K C (bv_unsigned s0w) ras spa Σ1 m1 -> 16 <= Fb -> 0 <= K ->
  rw_cells bgasegs m1 spa (pre ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre) = bv_unsigned sp - spa - 16 ->
  @cenvA (push AR f k) (objs ++ LB) PL lo (bv_unsigned sp) spa s0w raw (Some ras) C Σ1 ls OW m1 pre 0 Σ1 ls m1 OW.
Proof.
  intros Fb d f k objs Σ ls m OW LB PL EA sp lo K C s0w raw ras spa Σ1 m1 pre
         (HEAP1 & LS1 & FROK1 & ST1 & CEIL & LOK & SPT & SP16 & MI1 & CNT1 & CRED1 & FAL & NOFR1 & ROOM1 & SPA32 & SPAL & SPAH & CR1 & AXO & UW1 & FRESH & GEO) HF HK FRC SZ.
  unfold cenvA, cenv_ok.
  split. { split; [exact CEIL|]. split; [clear - LOK HK; lia|]. split; [clear - SPAH HF; lia|]. split; [exact SPT|]. split; [exact SP16|].
           split; [clear - SPA32; Z.div_mod_to_equations; lia|]. split; [exact CNT1|]. split; [exact CRED1|]. split; [exact FROK1|]. split; [exact FAL | exact NOFR1]. }
  split; [exact HEAP1|]. split; [exact ST1|]. split; [exact MI1|]. split; [apply ax_pres_refl|]. split; [lia|].
  split; [apply cnt_eq_refl|]. split; [apply refs_stable_refl|]. split; [exact FRC|]. split; [exact SZ|]. exact UW1.
Qed.

Lemma ax_pres_outer : forall (objs LB : list block) SP X m m', ax_pres (objs ++ LB) SP X m m' -> ax_pres LB SP X m m'.
Proof.
  intros objs LB SP X m m' H. eapply agree_on_mono; [exact H|]. intros a [H1 [H2|[H2|(b & Hb & Hr)]]]; (split; [exact H1|]);
    [left; exact H2 | right; left; exact H2 | right; right; exists b; split; [apply in_or_app; right; exact Hb | exact Hr]].
Qed.

Definition w_fown (objs : list block) (PL : placement) (lo SPv : Z) (iv : Z * Z) : Prop :=
  (lo <= fst iv /\ snd iv <= SPv)
  \/ (exists b, In b objs /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b /\ forall x, fst iv <= x < snd iv -> ~ rin_ivs (pl_frames PL) x).

Lemma cenv_own_storeA : forall (objs LB : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre pre' used Σ (ls : bstate bptr) m m' OW W,
  cenvA (objs ++ LB) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_state ls m OW PL EA ->
  munch W m m' -> wmono bgasegs m m' -> Forall (w_fown objs PL lo SPv) W ->
  stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
  rw_cells bgasegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
  cenvA (objs ++ LB) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m' pre' used Σ ls m' OW
  /\ lib_state ls m' OW PL EA
  /\ ax_pres LB SPv (XW PL) m0 m'.
Proof.
  intros objs LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre pre' used Σ ls m m' OW W
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) LS MU WM HW ST' MI' FR' FSZ'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _).
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN in C1, C2, C3.
  assert (OBJ : forall b, In b objs -> In b (OW ++ objs ++ LB)) by (intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb).
  assert (HEAP' : AHEAP Σ OW (objs ++ LB) m').
  { eapply (AH_frame Σ OW (objs ++ LB) m m' W HEAP MU WM). eapply Forall_impl; [| exact HW].
    intros [x y] [[H1 H2]|(b & Hb & H1 & H2 & _)]; cbn [fst snd] in *; [left; cbn [fst snd]; unfold USTACK_TOP in *; lia|].
    right; right. exists b. split; [exact (OBJ b Hb) | cbn [fst snd]; lia]. }
  assert (LS' : lib_state ls m' OW PL EA).
  { unfold lib_state in *. eapply (lib_state_frame_lb Σ (objs ++ LB) SPv USTACK_TOP false [] ls m m' OW PL EA W HEAP LS MU WM FROK).
    eapply Forall_impl; [| exact HW]. intros [x y] [[H1 H2]|(b & Hb & H1 & H2 & H3)]; cbn [fst snd] in *.
    - left. apply w_stack; cbn [fst snd]; lia.
    - right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn [fst snd]. auto. }
  assert (AXS : ax_pres LB SPv (XW PL) m m').
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a [_ Ha]. clear MU.
    induction HW as [|[x y] W' Hiv HW' IH]; [exact I|]. cbn [outside]. split; [| exact IH].
    destruct Hiv as [[H1 H2]|(b & Hb & H1 & H2 & _)]; cbn [fst snd] in *; intros Hx.
    - destruct Ha as [Ha|[Ha|(b' & Hb' & Hr)]]; [lia | |].
      + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
      + pose proof (AH_range_gen _ _ _ _ b' HEAP ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb')) as (_ & _ & _ & BC & _). lia.
    - pose proof (AH_range_gen _ _ _ _ b HEAP (OBJ b Hb)) as (B0 & _ & _ & BC & BI).
      destruct Ha as [Ha|[Ha|(b' & Hb' & Hr)]]; [lia | |].
      + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
      + assert (NE : blk_id b <> blk_id b').
        { intros E. pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite !map_app in ND. apply NoDup_app_remove_l in ND.
          eapply (nodup_app_disj _ _ (blk_id b) ND); [apply in_map; exact Hb | rewrite E; apply in_map; exact Hb']. }
        pose proof (AH_disjoint_gen _ _ _ _ b b' HEAP (OBJ b Hb) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb') NE) as DJ. lia. }
  split; [| split; [exact LS' | exact (ax_pres_trans _ _ _ _ _ _ (ax_pres_outer objs LB _ _ _ _ AXP) AXS)]].
  unfold cenvA. split; [exact OK|]. split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|]. split; [apply ax_pres_refl|].
  split; [exact CR|]. split; [exact CNT|]. split; [exact RS|]. split; [exact FR'|]. split; [exact FSZ'|].
  unfold uw_opt in *. destruct rasO as [ras|]; [| exact I].
  eapply uw_chain_munch_nw; [exact UW | exact MU |]. eapply Forall_impl; [| exact HW].
  intros [x y] [[H1 H2]|(b & Hb & H1 & H2 & _)]; cbn [fst snd] in *; [exact H2|].
  pose proof (AH_range_gen _ _ _ _ b HEAP (OBJ b Hb)) as (_ & _ & _ & BC & _). unfold BnHeapA.ACEIL in *. lia.
Qed.

Lemma cenv_scope_openA : forall (news LB : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre pre' used Σ (ls : bstate bptr) m m' OW W f k,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_state ls m OW PL EA ->
  In (f, k) FR -> (forall b, In b LB -> off_fr f k b) ->
  munch W m m' -> wmono bgasegs m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= SPv) \/ (shad f <= fst iv /\ snd iv <= shad f + fs_size k / 8)) W ->
  AHEAP Σ OW (news ++ LB) m' ->
  cnt_ok ls0 OW0 (news ++ LB) ->
  stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
  rw_cells bgasegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
  cenvA (news ++ LB) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m' pre' used Σ ls m' OW
  /\ lib_state ls m' OW PL EA
  /\ ax_pres LB SPv (XW PL) m0 m'.
Proof.
  intros news LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre pre' used Σ ls m m' OW W f k
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) LS Hf OFF MU WM HW HEAP' CNT' ST' MI' FR' FSZ'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & _ & CRED0 & FROK & FAL & NOFR).
  pose proof (AH_fr_geo _ _ _ _ f k HEAP Hf) as GEO.
  assert (INC : forall b, In b LB -> In b (news ++ LB)) by (intros b Hb; apply in_or_app; right; exact Hb).
  assert (AG : agree_on (aclient_addr (OW ++ LB) SPv) m m').
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. clear MU.
    assert (OFFA : forall b, In b (OW ++ LB) -> off_fr f k b).
    { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (AH_ow_off_fr Σ OW LB m f k b HEAP Hf Hb) | exact (OFF b Hb)]. }
    pose proof (fr3_outside Σ OW LB m f k lo SPv (OW ++ LB) a HEAP GEO CEIL ltac:(lia) ltac:(intros b Hb; exact Hb) OFFA Ha) as (N1 & _ & N3).
    induction HW as [|[x y] W' Hiv HW' IH]; [exact I|]. cbn [outside]. split; [| exact IH].
    destruct Hiv as [[H1 H2]|[H1 H2]]; cbn [fst snd] in *; lia. }
  assert (LS' : lib_state ls m' OW PL EA).
  { unfold lib_state in *. eapply lib_state_h_heap_pres with (L := OW ++ LB) (SP := SPv) (SPX := SPv) (BX := USTACK_TOP); [exact LS | exact FROK | lia | lia | exact AG | |];
      intros b Hb; apply in_or_app; [left | right]; exact Hb. }
  assert (AXS : ax_pres LB SPv (XW PL) m m').
  { eapply agree_on_mono; [exact AG|]. intros a [_ [Ha|[Ha|(b & Hb & Hr)]]]; [left; exact Ha | right; left; exact Ha |].
    right; right. exists b. split; [apply in_or_app; right; exact Hb | exact Hr]. }
  split; [| split; [exact LS' | exact (ax_pres_trans _ _ _ _ _ _ AXP AXS)]].
  unfold cenvA, cenv_ok.
  split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|]. split; [exact CNT'|].
           split; [exact CRED0|]. split; [exact (frames_ok_incl LB (news ++ LB) PL _ _ FROK INC)|]. split; [exact FAL | exact (frames_lb_incl PL LB (news ++ LB) NOFR INC)]. }
  split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|]. split; [apply ax_pres_refl|].
  split; [exact CR|]. split; [exact CNT|]. split; [exact RS|]. split; [exact FR'|]. split; [exact FSZ'|].
  unfold uw_opt in *. destruct rasO as [ras|]; [| exact I].
  apply (uw_chain_agree m m' ras _ _ UW). eapply agree_on_mono; [exact AG|]. intros a Ha. left. exact Ha.
Qed.

Lemma cenv_scope_closeA : forall (olds LB : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre pre' used Σ (ls : bstate bptr) m m' OW W f k,
  cenvA (olds ++ LB) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_state ls m OW PL EA ->
  In (f, k) FR -> (forall b, In b LB -> off_fr f k b) ->
  munch W m m' -> wmono bgasegs m m' ->
  Forall (fun iv => (lo <= fst iv /\ snd iv <= SPv) \/ (shad f <= fst iv /\ snd iv <= shad f + fs_size k / 8)) W ->
  AHEAP Σ OW LB m -> AHEAP Σ OW LB m' ->
  frames_ok LB PL SPv USTACK_TOP -> frames_lb PL LB ->
  stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
  rw_cells bgasegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m' pre' used Σ ls m' OW
  /\ lib_state ls m' OW PL EA
  /\ ax_pres LB SPv (XW PL) m0 m'.
Proof.
  intros olds LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre pre' used Σ ls m m' OW W f k
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FR & FSZ & UW) LS Hf OFF MU WM HW HEAPc HEAP' FROK' NOFR' ST' MI' FR' FSZ'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  pose proof (AH_fr_geo _ _ _ _ f k HEAPc Hf) as GEO.
  assert (AG : agree_on (aclient_addr (OW ++ LB) SPv) m m').
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. clear MU.
    assert (OFFA : forall b, In b (OW ++ LB) -> off_fr f k b).
    { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (AH_ow_off_fr Σ OW LB m f k b HEAPc Hf Hb) | exact (OFF b Hb)]. }
    pose proof (fr3_outside Σ OW LB m f k lo SPv (OW ++ LB) a HEAPc GEO CEIL ltac:(lia) ltac:(intros b Hb; exact Hb) OFFA Ha) as (N1 & _ & N3).
    induction HW as [|[x y] W' Hiv HW' IH]; [exact I|]. cbn [outside]. split; [| exact IH].
    destruct Hiv as [[H1 H2]|[H1 H2]]; cbn [fst snd] in *; lia. }
  assert (LS' : lib_state ls m' OW PL EA).
  { unfold lib_state in *. eapply lib_state_h_heap_pres with (L := OW ++ LB) (SP := SPv) (SPX := SPv) (BX := USTACK_TOP); [exact LS | exact FROK' | lia | lia | exact AG | |];
      intros b Hb; apply in_or_app; [left | right]; exact Hb. }
  assert (AXS : ax_pres LB SPv (XW PL) m m').
  { eapply agree_on_mono; [exact AG|]. intros a [_ [Ha|[Ha|(b & Hb & Hr)]]]; [left; exact Ha | right; left; exact Ha |].
    right; right. exists b. split; [apply in_or_app; right; exact Hb | exact Hr]. }
  split; [| split; [exact LS' | exact (ax_pres_trans _ _ _ _ _ _ (ax_pres_outer olds LB _ _ _ _ AXP) AXS)]].
  unfold cenvA, cenv_ok.
  split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|].
           split. { unfold cnt_ok in *. rewrite length_app in CNT0. lia. }
           split; [exact CRED0|]. split; [exact FROK'|]. split; [exact FAL | exact NOFR']. }
  split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|]. split; [apply ax_pres_refl|].
  split; [exact CR|]. split; [exact CNT|]. split; [exact RS|]. split; [exact FR'|]. split; [exact FSZ'|].
  unfold uw_opt in *. destruct rasO as [ras|]; [| exact I].
  apply (uw_chain_agree m m' ras _ _ UW). eapply agree_on_mono; [exact AG|]. intros a Ha. left. exact Ha.
Qed.

Lemma fr_no_placed : forall PL (LB : list block) f k x,
  frames_lb PL LB -> (forall b, In b LB -> off_fr f k b) -> f <= x < f + fs_size k -> ~ rin_ivs (pl_frames PL) x.
Proof.
  intros PL LB f k x [H _] OFF Hx Hr. apply rin_ivs_In in Hr as (iv & Hiv & Hi).
  destruct (H iv Hiv) as (b & Hb & B1 & B2). pose proof (OFF b Hb) as O. unfold off_fr in O. lia.
Qed.

Lemma epi_close : forall Fb d f k objs Σ ls m OW LB PL EA sp lo STACK COST (s0w raw : word) ras spa Σ1 m1 mb pre used Σk (lsk : bstate bptr) mk OWk Σ' m',
  bn_preA Σ ls m OW LB PL EA sp lo STACK COST ->
  fr_env Fb d f k objs Σ ls m OW LB PL EA sp lo (STACK - Fb - 16) (COST - 1) (bv_unsigned s0w) ras spa Σ1 m1 ->
  ax_pres LB (bv_unsigned sp) (XW PL) m mb ->
  @cenvA (push AR f k) (objs ++ LB) PL lo (bv_unsigned sp) spa s0w raw (Some ras) (COST - 1) Σ1 ls OW mb pre used Σk lsk mk OWk ->
  lib_state lsk mk OWk PL EA -> used <= COST - 1 ->
  AHEAP Σ' OWk LB m' -> stk bgasegs m' lo (bv_unsigned sp) -> mem_inv bgasegs m' -> rt_credit RT Σ' = rt_credit RT Σk ->
  agree_on (aclient_addr (OWk ++ LB) (bv_unsigned sp)) mk m' ->
  AHEAP Σ' OWk LB m' /\ lib_state lsk m' OWk PL EA /\ stk bgasegs m' lo (bv_unsigned sp) /\ mem_inv bgasegs m'
  /\ ax_pres LB (bv_unsigned sp) (XW PL) m m' /\ rt_credit RT Σ - COST <= rt_credit RT Σ'
  /\ cnt_eq ls OW lsk OWk /\ refs_stable ls OW lsk OWk.
Proof.
  intros Fb d f k objs Σ ls m OW LB PL EA sp lo STACK COST s0w raw ras spa Σ1 m1 mb pre used Σk lsk mk OWk Σ' m'
         (_ & _ & FROK & _) FE AXO EV LSk USED HEAP' ST' MI' CR' AGE.
  pose proof FE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CR1 & _).
  pose proof EV as (_ & _ & _ & _ & AXPk & CRk & CNTk & RSk & _).
  split; [exact HEAP'|].
  split. { unfold lib_state in *. eapply lib_state_h_heap_pres with (L := OWk ++ LB) (SP := bv_unsigned sp) (SPX := bv_unsigned sp) (BX := USTACK_TOP); [exact LSk | exact FROK | lia | lia | exact AGE | |];
           intros b Hb; apply in_or_app; [left | right]; exact Hb. }
  split; [exact ST'|]. split; [exact MI'|].
  split. { eapply ax_pres_trans; [exact AXO|]. eapply ax_pres_trans; [exact (ax_pres_outer objs LB _ _ _ _ AXPk)|].
           eapply agree_on_mono; [exact AGE|]. intros a [_ [Ha|[Ha|(b & Hb & Hr)]]]; [left; exact Ha | right; left; exact Ha |].
           right; right. exists b. split; [apply in_or_app; right; exact Hb | exact Hr]. }
  split; [cbn [ar_RT push amb] in CRk; clear - CR' CRk CR1 USED; lia|]. split; [exact CNTk | exact RSk].
Qed.

End Env.
