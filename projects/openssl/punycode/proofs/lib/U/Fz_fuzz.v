(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require StoreOk.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Tac Arr Bytes Image ZBridge SysStep ITree Nodes Decode FP MonadX.
From OSSVerify.Proofs.openssl.punycode.lib.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.openssl.punycode.lib.MallocU Require Import RMallocRep RMallocTree RMalloc_iface RMalloc_word.
From OSSVerify.Proofs.openssl.punycode.lib.Spec Require Import Prelim STree Malloc Monad Stdio Harness Target Prog StrFun.
From OSSVerify.Proofs.openssl.punycode.lib.U Require Import Layout Exit Printf_wfile F_memcpy F_memset Fz_iface Drv_kit Fz_kit Fz_ckit Fz_voc Fz_regions Fz_w1 Fz_w2.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require WpEngine LibKit StrKit KBridge.
From OSSVerify.Proofs.openssl.punycode.lib.LibU Require UCode UImg UDecode UA2u.
From OSSVerify.Proofs.openssl.punycode.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.openssl.punycode.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma implM_pre_evt : forall {A} (c : M PState A) s Q ms,
  evt usegs (fun ms' => implM usegs c s Q ms') ms -> implM usegs c s Q ms.
Proof. intros A c s Q ms H. unfold implM in *. apply impl_from_evt. exact H. Qed.

Lemma bytes_at_same : forall m A (bs bs' : list byte),
  bytes_at usegs m A bs -> bytes_at usegs m A bs' -> length bs = length bs' -> bs = bs'.
Proof.
  intros m A bs bs' (_ & _ & H1) (_ & _ & H2) L. apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (H1 i Hi), <- (H2 i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by lia. reflexivity.
Qed.

Lemma ssp_canary_0 : forall s LB m c, RHEAP s LB m -> ssp_cells m c -> c = rr_guard.
Proof.
  intros s LB m c HR [_ H2]. pose proof (RHEAP_ssp _ _ _ HR) as [_ G2].
  destruct H2 as [[_ B2] _]. destruct G2 as [[_ C2] _]. cbn [cells_bytes cbytes app] in B2, C2. rewrite app_nil_r in B2, C2.
  pose proof (bytes_at_same _ _ _ _ B2 C2 ltac:(rewrite !length_le8; reflexivity)) as E.
  rewrite <- (le_bytes_to_word_le8 c), <- (le_bytes_to_word_le8 rr_guard), E. reflexivity.
Qed.

Section FZ.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.
  Variables (ra gp : word) (S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Variables (usp : Z) (s : PState) (LB : list block) (D : Z) (d : list Z) (lo B : Z) (canary : word) (m0 : mem).
  Hypothesis SPB : usp <= B.
  Hypothesis B63 : B < 2^63.
  Hypothesis LOC : alloc_ceiling <= lo.
  Hypothesis LOG : GLOBALS_TOP <= lo.
  Hypothesis LOSP : lo <= usp - LX_FUZZ_STACK.
  Hypothesis SP16 : usp mod 16 = 0.

  Definition FX : list (Z * Z) := [LXW_FLAGS; LXW_MSGBUF; LXW_STDERR].
  Notation POST := (rfuzz_one_post ra (wz usp) gp (wz RATP) S0 S1 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 s LB D d lo B canary m0).

  (* [comment removed for export] *)
  Definition FENV (mX : mem) (sX : PState) (OW : list block) (q : Z) : Prop :=
    RHEAP sX (OW ++ LB) mX /\ lx_statics mX /\ lx_flags0 mX /\ stderr_wfile mX /\ rauxv_ok mX B
    /\ (exists errv : word, rw_cells usegs mX LX_ERRNO [C4 errv]) /\ mem_inv usegs mX /\ stk usegs mX lo q
    /\ lx_pres LB usp FX m0 mX /\ ps_so sX = ps_so s /\ ps_fa sX = ps_fa s /\ payload_ok mX LB D d.

  (* [comment removed for export] *)
  Definition wok (OW : list block) (iv : Z * Z) : Prop :=
    (alloc_ceiling <= fst iv /\ snd iv <= usp) \/ iv = LXW_FLAGS
    \/ (exists b, In b OW /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

  Lemma nodup_app_in : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
  Proof.
    induction l1 as [|y l1 IH]; intros l2 x ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|? ? N1 N2]; subst.
    destruct H1 as [->|H1]; [apply N1; apply in_or_app; right; exact H2| exact (IH l2 x N2 H1 H2)].
  Qed.

  Lemma wok_outside : forall sX OW mX W a, RHEAP sX (OW ++ LB) mX -> Forall (wok OW) W ->
    (usp <= a \/ (0x2c1000 <= a < GLOBALS_TOP /\ ~ flags_addr a) \/ in_block LB a) -> outside W a.
  Proof.
    intros sX OW mX W a HP FW Ha. unfold LX_FUZZ_STACK, GLOBALS_TOP in *.
    induction FW as [|[l h] W Hiv FW IH]; [exact I|]. cbn [outside]. split; [| exact IH].
    intros Hin. destruct Hiv as [(H1 & H2)|[E|(b & Hb & H1 & H2)]]; cbn [fst snd] in *.
    - destruct Ha as [Ha|[(Ha & _)|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_block_range _ _ _ b' HP ltac:(apply in_or_app; right; exact Hb')) as (_ & _ & _ & R4 & _). lia.
    - injection E as -> ->. unfold LX_FLAGS in *. destruct Ha as [Ha|[(Ha & NF)|(b' & Hb' & Hr)]]; [lia| apply NF; unfold flags_addr, LX_FLAGS; lia|].
      pose proof (LH_block_range _ _ _ b' HP ltac:(apply in_or_app; right; exact Hb')) as (_ & _ & _ & _ & R5). lia.
    - pose proof (LH_block_range _ _ _ b HP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & R4 & R5).
      destruct Ha as [Ha|[(Ha & _)|(b' & Hb' & Hr)]]; [lia| lia|].
      pose proof (LH_nodup _ _ _ HP) as ND. rewrite map_app in ND.
      assert (NE : blk_id b <> blk_id b').
      { intros EQ. apply (nodup_app_in _ _ (blk_id b) ND); [apply in_map; exact Hb| rewrite EQ; apply in_map; exact Hb']. }
      pose proof (LH_disjoint _ _ _ b b' HP ltac:(apply in_or_app; left; exact Hb) ltac:(apply in_or_app; right; exact Hb') NE) as DJ. lia.
  Qed.
  Lemma wok_heap : forall OW iv b, wok OW iv -> wok (b :: OW) iv.
  Proof. intros OW iv b [H|[H|(b' & Hb & H)]]; [left; exact H| right; left; exact H| right; right; exists b'; split; [right; exact Hb| exact H]]. Qed.

  (* [comment removed for export] *)
  Lemma FENV_munch : forall mX mY sX OW q q' W,
    FENV mX sX OW q -> munch W mX mY -> wmono usegs mX mY -> mem_inv usegs mY -> stk usegs mY lo q' -> lx_flags0 mY ->
    Forall (wok OW) W -> FENV mY sX OW q'.
  Proof.
    intros mX mY sX OW q q' W (HP & LXS & LXF & SEW & AUX & (errv & ERR) & MI & ST & PRES & SO & FA & PAY) MU WM MI' ST' LXF' FW.
    pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, usp <= a \/ (0x2c1000 <= a < GLOBALS_TOP /\ ~ flags_addr a) \/ in_block LB a -> outside W a)
      by (intros a Ha; exact (wok_outside sX OW mX W a HP FW Ha)).
    destruct (statics_munch W mX mY canary MU WM ltac:(intros a Ha NF; apply OUT; right; left; split; assumption)) as (T1 & T2 & _).
    split.
    { eapply LH_frame; [exact HP| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros iv [H|[->|(b & Hb & H1 & H2)]].
      - left. exact (proj1 H).
      - apply W_ok_latch.
      - apply (W_ok_block _ b); [apply in_or_app; left; exact Hb| exact H1| exact H2]. }
    split; [exact (T1 LXS)|]. split; [exact LXF'|]. split; [exact (T2 SEW)|].
    split.
    { eapply rauxv_ok_frame; [exact AUX| exact MU| exact WM|]. eapply Forall_impl; [| exact FW]. intros [l h] Hiv. cbn [fst snd].
      pose proof AUX as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & _ & _ & _ & AUXB & _).
      unfold RAUXV_CELL. destruct Hiv as [(H1 & H2)|[E|(b & Hb & H1 & H2)]]; cbn [fst snd] in *.
      - split; [lia|]. right. lia.
      - injection E as -> ->. unfold LX_FLAGS. split; [lia|]. left. lia.
      - pose proof (LH_block_range _ _ _ b HP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & R4 & R5). split; [lia|]. lia. }
    split.
    { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. cbn in Ha. apply OUT. right; left.
      unfold LX_ERRNO, RATP, GLOBALS_TOP, flags_addr, LX_FLAGS in *. lia. }
    split; [exact MI'|]. split; [exact ST'|].
    split.
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_of_munch; [exact MU| exact WM|]. intros a Ha [HX Hc]. apply OUT.
      destruct Hc as [Hc|[Hc|(Hc & _)]]; [left; exact Hc| right; right; exact Hc| right; left].
      split; [unfold GLOBALS_TOP; lia|]. intros NF. apply HX. left. unfold LXW_FLAGS, flags_addr in *. cbn [fst snd]. lia. }
    split; [exact SO|]. split; [exact FA|].
    eapply payload_ok_agree; [exact AG| exact PAY|]. intros b a Hb Ha. apply OUT. right; right. exists b. split; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma FENV_heap : forall mX mY sX sY OW OW' LBX q (errv' : word),
    FENV mX sX OW q -> q <= usp -> (forall b, In b LB -> In b LBX) ->
    mem_inv usegs mY -> stk usegs mY lo q -> rw_cells usegs mY LX_ERRNO [C4 errv'] -> rauxv_ok mY B ->
    rheap_pres LBX q mX mY -> ps_fa sY = ps_fa sX -> ps_so sY = ps_so sX ->
    RHEAP sY (OW' ++ LB) mY ->
    FENV mY sY OW' q.
  Proof.
    intros mX mY sX sY OW OW' LBX q errv' (HP & LXS & LXF & SEW & AUX & _ & MI & ST & PRES & SO & FA & PAY) QU SUB MI' ST' ERR' AUX' HPR FA' SO' HP'.
    destruct (statics_heap _ _ _ _ HPR) as (T1 & T2 & T3).
    split; [exact HP'|]. split; [exact (T1 LXS)|]. split; [exact (T2 LXF)|]. split; [exact (T3 SEW)|]. split; [exact AUX'|].
    split; [exists errv'; exact ERR'|]. split; [exact MI'|]. split; [exact ST'|].
    split.
    { eapply lx_pres_trans; [exact PRES|]. eapply lx_pres_weaken; [exact (lx_pres_of_heap_pres LBX q FX mX mY HPR)| exact QU| exact SUB| auto]. }
    split; [rewrite SO'; exact SO|]. split; [rewrite FA'; exact FA|].
    eapply payload_ok_agree; [exact (agree_of_heap_pres _ _ _ _ HPR)| exact PAY|]. intros b a Hb Ha. right; right. exists b. split; [exact (SUB b Hb)| exact Ha].
  Qed.
  Hypothesis CAN : canary = rr_guard.
  Hypothesis USP0 : 0 <= usp.

  Lemma usp_range : 0x354000 + LX_FUZZ_STACK <= usp /\ usp < 2^63.
  Proof. unfold GLOBALS_TOP in LOG. lia. Qed.

  (* [comment removed for export] *)
  Lemma st5 : forall (mX : mem) (sX : PState) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32),
    FENV mX sX [] (usp + -128) -> frm0 fc ->
    wr_at usegs mX (usp + -128) 96 -> rw_cells usegs mX (usp + -128 + 96) [C8 S2; C8 S1; C8 S0; C8 ra] ->
    implM usegs (mret 0) sX POST
      (MS (mkR x1 (wz (usp + -128)) gp (wz RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 S3 S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31)
          F (wz 0xe1b2c) fc None mX (seg_rom usegs)).
  Proof.
    intros until fc. intros (HP & LXS & LXF & SEW & AUX & (errv & ERR) & MI & ST & PRES & SO & FA & PAY) FRM WRF SAVF.
    pose proof usp_range as (UR1 & UR2). unfold LX_FUZZ_STACK in *. unfold GLOBALS_TOP in LOG.
    destruct (wr_at_rw_CB mX (usp + -128) 96 WRF ltac:(lia)) as (jx & FB). change (Z.to_nat 96) with 96%nat in FB.
    assert (FR : rw_cells usegs mX (usp + -128) [CB 96 jx; C8 S2; C8 S1; C8 S0; C8 ra]).
    { apply (proj2 (rw_cells_app mX (usp + -128) [CB 96 jx] [C8 S2; C8 S1; C8 S0; C8 ra])). split; [exact FB| exact SAVF]. }
    apply implM_ret. unfold wz.
    eapply evt_mono.
    { apply (fzp_w9 usp lo x1 gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 S3 S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31
               F fc mX jx S2 S1 S0 ra ST ltac:(lia) ltac:(lia) ltac:(lia) MI FR). }
    intros ms' (-> & ST').
    assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
    unfold rfuzz_one_post. do 15 eexists. exists F, fc, mX. split; [reflexivity|].
    split.
    { unfold lx_post_env. rewrite EU. split.
      { exists errv. unfold lx_env. rewrite EU. cbn [app].
        split; [exact HP|]. split; [exact LXS|]. split; [exact LXF|]. split; [exact SEW|]. split; [rewrite CAN; exact (RHEAP_ssp _ _ _ HP)|].
        split; [exact AUX|]. split; [exact SPB|]. split; [exact B63|]. split; [exact ST'|]. split; [exact LOC|]. split; [unfold GLOBALS_TOP; exact LOG|].
        split; [| split; [reflexivity| exact MI]].
        unfold errno_addr. unfold LX_ERRNO, RATP in *. rewrite unsigned_lit by lia. exact ERR. }
      split; [exact FRM|]. split; [exact PRES|]. split; [exact SO| exact FA]. }
    split; [reflexivity|]. split; [reflexivity| exact PAY].
  Qed.
  Lemma implM_evt_cut : forall {A} (c : M PState A) sX Q (P : machine_state -> Prop) ms,
    evt usegs P ms -> (forall ms', P ms' -> implM usegs c sX Q ms') -> implM usegs c sX Q ms.
  Proof. intros A c sX Q P ms H K. apply implM_pre_evt. eapply evt_mono; [exact H| exact K]. Qed.

  Lemma flags_munch : forall W mX mY, lx_flags0 mX -> munch W mX mY -> wmono usegs mX mY -> outside W LX_FLAGS -> lx_flags0 mY.
  Proof.
    intros W mX mY LF MU WM HO. eapply lx_flags_agree; [exact (agree_on_of_munch _ _ _ MU WM)| | exact LF].
    intros a Ha. unfold flags_addr in Ha. replace a with LX_FLAGS by lia. exact HO.
  Qed.

  Notation S := (usp + -128).

  (* [comment removed for export] *)
  Lemma st4 : forall (mX : mem) (sX : PState) (pb : bptr) (A : Z)
      (x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 y4 y5 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (jf jl : list byte) (g3 g2 g1 : word),
    FENV mX sX [(pb, A, zlength d + 1)] (S + -2288) -> frm0 fc ->
    rw_cells usegs mX (S + -2288) (cmp_frame jf g3 g2 g1 (wz S) (wz 0x215b98)) ->
    rw_cells usegs mX (S + -2240) [CB 2136 jl; C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 (wz D);
                                   C8 (wz (A + zlength d)); C8 (wz A); C8 (wz 0xe1b18)] ->
    wr_at usegs mX S 96 -> rw_cells usegs mX (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra] ->
    implM usegs (mbind (raw_free pb) (fun _ => mret 0)) sX POST
      (MS (mkR x1 (wz (S + -2288)) gp (wz RATP) x5 x6 x7 x8 (wz (S + -2216)) x10 x11 x12 x13 x14 x15 x16 x17 x18 (wz 0) y4 y5 y6 y7 y8 y9 y10 y11
               x28 x29 x30 x31) F (wz 0x1295c8) fc None mX (seg_rom usegs)).
  Proof.
    intros until g1. intros ENV FRM FRC FRA WRF SAVF.
    pose proof ENV as (HP & LXS & LXF & SEW & AUX & (errv & ERR) & MI & ST & PRES & SO & FA & PAY).
    pose proof usp_range as (UR1 & UR2). unfold LX_FUZZ_STACK in *. unfold GLOBALS_TOP in LOG. unfold wz in *.
    eapply implM_evt_cut.
    { apply (a2p_w8 S lo x1 gp (Z_to_bv 64 RATP) x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x18 y4 y5 y6 y7 y8 y9 y10 y11 x28 x29 x30 x31
               F fc mX jf jl g3 g2 g1 S11 S10 S9 S8 S7 S6 S5 S4 S3 (Z_to_bv 64 D) (Z_to_bv 64 (A + zlength d)) (Z_to_bv 64 A)
               ST ltac:(lia) ltac:(lia) ltac:(lia) MI FRC FRA). }
    intros ms1 (m1 & -> & MU1 & WM1 & MI1 & ST1).
    assert (ENV1 : FENV m1 sX [(pb, A, zlength d + 1)] S).
    { apply (FENV_munch mX m1 sX _ (S + -2288) S [(S + -2288, S)] ENV MU1 WM1 MI1 ST1).
      - apply (flags_munch _ mX m1 LXF MU1 WM1). cbn [outside]. unfold LX_FLAGS. split; [lia| exact I].
      - constructor; [| constructor]. left. cbn [fst snd]. lia. }
    pose proof (wr_at_transport usegs mX m1 _ _ WRF WM1) as WRF1.
    assert (SAVF1 : rw_cells usegs m1 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU1 WM1)| exact SAVF|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      cbn [outside]. split; [lia| exact I]. }
    clear ENV HP LXS LXF SEW AUX ERR MI ST PRES SO FA PAY FRC FRA WRF SAVF MU1 WM1.
    pose proof ENV1 as (HP & LXS & LXF & SEW & AUX & (errv1 & ERR) & MI & ST & PRES & SO & FA & PAY).
    pose proof (LH_block_range _ _ _ (pb, A, zlength d + 1) HP ltac:(left; reflexivity)) as (BA0 & BA16 & _ & BAC & BAI).
    cbn [blk_addr blk_size fst snd] in *.
    destruct LXS as (_ & _ & _ & _ & GOTF & HKF).
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (cf_w S lo (Z_to_bv 64 0xe1b2c) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 (A + zlength d)) (Z_to_bv 64 A) (Z_to_bv 64 0x2ce58)
               (Z_to_bv 64 35) x13 x14 x15 x16 x17 (Z_to_bv 64 D) S3 S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31 F fc m1
               ST ltac:(lia) ltac:(lia) ltac:(lia) MI HKF GOTF). }
    intros ms2 (m2 & t1' & a3' & a4' & -> & MU2 & WM2 & MI2 & ST2).
    assert (ENV2 : FENV m2 sX [(pb, A, zlength d + 1)] S).
    { apply (FENV_munch m1 m2 sX _ S S [(S + -16, S)] ENV1 MU2 WM2 MI2 ST2).
      - apply (flags_munch _ m1 m2 LXF MU2 WM2). cbn [outside]. unfold LX_FLAGS. split; [lia| exact I].
      - constructor; [| constructor]. left. cbn [fst snd]. lia. }
    pose proof (wr_at_transport usegs m1 m2 _ _ WRF1 WM2) as WRF2.
    assert (SAVF2 : rw_cells usegs m2 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact (agree_on_of_munch _ _ _ MU2 WM2)| exact SAVF1|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha.
      cbn [outside]. split; [lia| exact I]. }
    clear ENV1 HP LXF SEW AUX ERR MI ST PRES SO FA PAY WRF1 SAVF1 MU2 WM2 GOTF HKF.
    pose proof ENV2 as (HP & LXS & LXF & SEW & AUX & (errv2 & ERR) & MI & ST & PRES & SO & FA & PAY).
    eapply implM_bind.
    { eapply (free_callZ HF) with (B := B) (lo := lo) (A := A) (n := zlength d + 1) (errv := errv2);
        [exact HP| left; reflexivity| exact AUX| lia| exact ST| exact LOC| unfold RFREE_STACK; lia| exact ERR| exact MI| lia]. }
    cbv beta. intros [] s3 ms3 PO. unfold free_postZ in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FA3 & SO3 & HP3).
    pose proof (LH_nodup _ _ _ HP) as ND. cbn [app] in ND, HPR3, HP3. rewrite (lb_remove_head pb A (zlength d + 1) LB ND) in HPR3, HP3.
    replace (ret_pc (Z_to_bv 64 0xe1b2c)) with (Z_to_bv 64 0xe1b2c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (st5 m3 s3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc).
    - apply (FENV_heap m2 m3 sX s3 _ [] LB S errv2 ENV2 ltac:(lia) ltac:(auto) MI3 ST3 ERR3 AUX3 HPR3 FA3 SO3). exact HP3.
    - exact FRM.
    - eapply wr_at_agree; [exact (agree_of_heap_pres _ _ _ _ HPR3)| exact WRF2|]. intros a Ha. left. lia.
    - eapply rw_cells_agree; [exact (agree_of_heap_pres _ _ _ _ HPR3)| exact SAVF2|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. left. lia.
  Qed.
  Notation L := (S + -2240).
  Definition A2SAVES (A : Z) : list cell :=
    [C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 (wz D); C8 (wz (A + zlength d)); C8 (wz A); C8 (wz 0xe1b18)].

  (* [comment removed for export] *)
  Lemma st3b : forall (mX : mem) (sX : PState) (pb pq : bptr) (A Aq : Z)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (j7 : list byte) (eb : byte),
    FENV mX sX [(pq, Aq, 40); (pb, A, zlength d + 1)] L -> frm0 fc ->
    wr_at usegs mX L 2136 -> rw_cells usegs mX (S + -104) (A2SAVES A) ->
    rw_cells usegs mX (S + -2216) (pkp_cells1 (S + 12) Aq j7 eb) -> bv_unsigned eb mod 2 = 0 ->
    wr_at usegs mX S 96 -> rw_cells usegs mX (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra] ->
    rw_cells usegs mX (A + zlength d) [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs mX Aq [CB 40 (repeat (Z_to_bv 8 0) 40)] ->
    implM usegs (mbind (raw_free pq) (fun _ => mbind (raw_free pb) (fun _ => mret 0))) sX POST
      (MS (mkR (wz 0x2158e8) (wz L) gp (wz RATP) x5 x6 x7 (wz S) (wz (-1)) (wz 1) x11 x12 x13 x14 x15 x16 x17 (wz D) (wz A) S4 S5 S6 S7 S8 S9 S10 S11
               x28 x29 x30 x31) F (wz 0x2158ec) fc None mX (seg_rom usegs)).
  Proof.
    intros until eb. intros ENV FRM WRA SAVA PKT EBE WRF SAVF NUL QZ.
    pose proof ENV as (HP & LXS & LXF & SEW & AUX & (errv & ERR) & MI & ST & PRES & SO & FA & PAY).
    pose proof usp_range as (UR1 & UR2). unfold LX_FUZZ_STACK in *. unfold GLOBALS_TOP in LOG. unfold wz, A2SAVES in *.
    pose proof alloc_ceiling_range as CR.
    destruct PAY as (_ & _ & _ & _ & HD31 & _).
    assert (Hn : 0 <= zlength d) by (unfold zlength; lia). set (n := zlength d) in *.
    pose proof (LH_block_range _ _ _ (pb, A, n + 1) HP ltac:(right; left; reflexivity)) as (BA0 & BA16 & _ & BAC & BAI).
    pose proof (LH_block_range _ _ _ (pq, Aq, 40) HP ltac:(left; reflexivity)) as (QA0 & QA16 & _ & QAC & QAI).
    cbn [blk_addr blk_size fst snd] in *.
    pose proof (RHEAP_block_word sX _ mX pb A (n + 1) HP ltac:(right; left; reflexivity) ltac:(lia)) as WB.
    replace (n + 1 - 1) with n in WB by lia.
    set (N := n / 8 * 8 + 8) in *.
    assert (HN : n + 1 <= N <= n + 8) by (unfold N; Z.div_mod_to_equations; lia).
    pose proof (wr_at_stk mX A N WB) as STB.
    assert (STKA : stk usegs mX lo (S + -104)).
    { apply (stk_merge usegs mX lo L (S + -104) ST); [| lia]. pose proof (wr_at_stk mX L 2136 WRA) as H. replace (L + 2136) with (S + -104) in H by lia. exact H. }
    (* [comment removed for export] *)
    unfold pkp_cells1 in PKT.
    assert (K0 : LibKit.cell UCode.USEGS mX (S - 2216) 8 (Z_to_bv 64 0)) by exact (KBridge.cell_C8 usegs mX _ _ (proj1 (rw_cells_head mX _ _ _ PKT))).
    assert (K8 : LibKit.cell UCode.USEGS mX (S - 2216 + 8) 8 (Z_to_bv 64 (S + 12))).
    { pose proof (rw_cells_head mX _ _ _ (rw_cells_skip mX (S + -2216) [C8 (Z_to_bv 64 0)] _ PKT)) as H. cbn [cells_size csize Nat.add] in H.
      replace (S + -2216 + Z.of_nat 8) with (S - 2216 + 8) in H by lia. exact (KBridge.cell_C8 usegs mX _ _ (proj1 H)). }
    assert (K16 : LibKit.cell UCode.USEGS mX (S - 2216 + 16) 8 (Z_to_bv 64 0)).
    { pose proof (rw_cells_head mX _ _ _ (rw_cells_skip mX (S + -2216) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (S + 12))] _ PKT)) as H. cbn [cells_size csize Nat.add] in H.
      replace (S + -2216 + Z.of_nat 16) with (S - 2216 + 16) in H by lia. exact (KBridge.cell_C8 usegs mX _ _ (proj1 H)). }
    assert (K24 : LibKit.cell UCode.USEGS mX (S - 2216 + 24) 8 (Z_to_bv 64 0)).
    { pose proof (rw_cells_head mX _ _ _ (rw_cells_skip mX (S + -2216) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (S + 12)); C8 (Z_to_bv 64 0)] _ PKT)) as H. cbn [cells_size csize Nat.add] in H.
      replace (S + -2216 + Z.of_nat 24) with (S - 2216 + 24) in H by lia. exact (KBridge.cell_C8 usegs mX _ _ (proj1 H)). }
    assert (K32 : LibKit.cell UCode.USEGS mX (S - 2216 + 32) 8 (Z_to_bv 64 16)).
    { pose proof (rw_cells_head mX _ _ _ (rw_cells_skip mX (S + -2216) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (S + 12)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] _ PKT)) as H. cbn [cells_size csize Nat.add] in H.
      replace (S + -2216 + Z.of_nat 32) with (S - 2216 + 32) in H by lia. exact (KBridge.cell_C8 usegs mX _ _ (proj1 H)). }
    assert (SUBS : rw_cells usegs mX (S + -2176) [C8 (Z_to_bv 64 Aq)]).
    { pose proof (rw_cells_head mX _ _ _ (rw_cells_skip mX (S + -2216) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (S + 12)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16)] _ PKT)) as H.
      cbn [cells_size csize Nat.add] in H. replace (S + -2216 + Z.of_nat 40) with (S + -2176) in H by lia. exact H. }
    assert (K40 : LibKit.cell UCode.USEGS mX (S - 2216 + 40) 8 (Z_to_bv 64 Aq)).
    { replace (S - 2216 + 40) with (S + -2176) by lia. exact (KBridge.cell_C8 usegs mX _ _ (proj1 SUBS)). }
    assert (K48 : LibKit.cell UCode.USEGS mX (S - 2216 + 48) 1 (zxb eb)).
    { pose proof (rw_cells_head mX _ _ _ (rw_cells_skip mX (S + -2216) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (S + 12)); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 16); C8 (Z_to_bv 64 Aq)] _ PKT)) as H.
      cbn [cells_size csize Nat.add] in H. replace (S + -2216 + Z.of_nat 48) with (S - 2216 + 48) in H by lia. exact (KBridge.cell_C1 usegs mX _ _ (proj1 H)). }
    assert (EB8 : (bv_unsigned (zxb eb) mod 2 ^ 8) mod 2 = 0).
    { unfold zxb. pose proof (bv_unsigned_in_range _ eb) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
      change (2 ^ 8) with 256. rewrite unsigned_lit by (clear - R; lia). rewrite (Z.mod_small (bv_unsigned eb) 256) by (clear - R; lia). exact EBE. }
    assert (BOFF : A + N <= 0x10000 \/ 0x354000 <= A) by (unfold N; clear - BAI BA16 Hn; Z.div_mod_to_equations; lia).
    assert (RDB : LibKit.rd_ok mX A N) by (apply (rd_ok_stkU mX A (A + N)); [exact STB| exact BOFF| lia| lia]).
    assert (NULM : mX (Z_to_bv 64 (A + n)) = Some (Z_to_bv 8 0)).
    { pose proof (bytes_offU mX (A + n) [Z_to_bv 8 0] 0 (proj2 (proj1 NUL)) ltac:(cbn [length]; clear - BOFF HN Hn; lia) ltac:(cbn; lia)) as H.
      rewrite Z.add_0_r in H. exact H. }
    pose proof (a2u_evt (Z_to_bv 64 0x2158e8) (Z_to_bv 64 L) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 (-1)) (Z_to_bv 64 1)
                  x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 A) S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31 F fc mX
                  S A n N (S + 12) Aq (zxb eb) eq_refl eq_refl eq_refl K0 K8 K16 K24 K32 K40 K48 EB8 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) RDB NULM
                  ltac:(unfold N; clear - BA16 Hn; Z.div_mod_to_equations; lia)
                  (img_ok_ro mX 0x3a628 0x3a630 MI ltac:(lia) ltac:(lia)) (img_ok_ro mX 0x3a660 0x3a668 MI ltac:(lia) ltac:(lia)) (img_ok_ro mX 0x1e107 0x1e10c MI ltac:(lia) ltac:(lia))
                  ltac:(lia) ltac:(lia)
                  (KBridge.wr_ok_stk usegs mX lo (S + -104) (S - 2400) 184 STKA ltac:(lia) ltac:(lia))
                  (KBridge.wr_ok_stk usegs mX lo (S + -104) (S - 2200) 16 STKA ltac:(lia) ltac:(lia))
                  (KBridge.wr_ok_stk usegs mX lo (S + -104) (S - 2160) 2048 STKA ltac:(lia) ltac:(lia))
                  ltac:(lia) ltac:(lia)
                  (KBridge.wr_ok_wr_at usegs mX S 96 (S + 12) 16 WRF ltac:(lia) ltac:(lia))
                  ltac:(right; lia) ltac:(left; lia) ltac:(left; lia) ltac:(clear - SP16; Z.div_mod_to_equations; lia)) as W9.
    eapply implM_evt_cut; [exact W9|]. clear W9.
    intros ms9 (y1 & y5 & y6 & y7 & y9 & y10 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y18 & y19 & y20 & y21 & y22 & y23 & y24 & y25 & y26 & y27
                & y28 & y29 & y30 & y31 & m9 & -> & HU9 & HG9).
    set (W9l := [(S - 2400, S - 2216); (S - 2200, S - 2184); (S - 2160, S - 112); (S + 12, S + 28)]).
    assert (MU9 : munch W9l mX m9).
    { apply (KBridge.munch_of_unch W9l mX m9 _ HU9). intros x Hx Ho. unfold UA2u.a2u_FP, LibKit.inr in Hx. unfold W9l in Ho. cbn [outside] in Ho. lia. }
    pose proof (KBridge.wmono_of_grows usegs mX m9 HG9) as WM9.
    assert (MI9 : mem_inv usegs m9).
    { apply (KBridge.mem_inv_unch usegs mX m9 _ MI HU9). intros x Hx. unfold UA2u.a2u_FP, LibKit.inr in Hx.
      destruct Hx as [Hx|[Hx|[Hx|Hx]]]; [apply (stk_wview mX lo (S + -104)); [exact STKA| lia]| apply (stk_wview mX lo (S + -104)); [exact STKA| lia]
        | apply (stk_wview mX lo (S + -104)); [exact STKA| lia]| apply (wr_at_wview mX S 96); [exact WRF| lia]]. }
    pose proof (KBridge.stk_grows usegs mX m9 lo L ST HG9) as ST9.
    assert (OUT9 : forall a, (a < S - 2400 \/ S - 2216 <= a) -> (a < S - 2200 \/ S - 2184 <= a) -> (a < S - 2160 \/ S - 112 <= a) -> (a < S + 12 \/ S + 28 <= a) -> outside W9l a).
    { intros a H1 H2 H3 H4. unfold W9l. cbn [outside]. lia. }
    assert (ENV9 : FENV m9 sX [(pq, Aq, 40); (pb, A, n + 1)] L).
    { apply (FENV_munch mX m9 sX _ L L W9l ENV MU9 WM9 MI9 ST9).
      - apply (flags_munch _ mX m9 LXF MU9 WM9). apply OUT9; unfold LX_FLAGS; lia.
      - unfold W9l. repeat (constructor; [left; cbn [fst snd]; lia|]). constructor. }
    pose proof (agree_on_of_munch _ _ _ MU9 WM9) as AG9.
    assert (SUBS9 : rw_cells usegs m9 (S + -2176) [C8 (Z_to_bv 64 Aq)]).
    { eapply rw_cells_agree; [exact AG9| exact SUBS|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT9; lia. }
    assert (Q09 : rw_cells usegs m9 Aq [C8 (Z_to_bv 64 0)]).
    { apply (rw_cells_split_CB usegs _ _ [] 40 _ [] [8; 32]%nat) in QZ; [| reflexivity]. cbn [mk_CB_cells app] in QZ.
      apply rw_cells_head in QZ.
      assert (QC : rw_cells usegs mX Aq [C8 (Z_to_bv 64 0)]).
      { apply (rw_cells_recast mX Aq _ _ QZ); [cbn; split; [reflexivity| exact I]| vm_compute; reflexivity]. }
      eapply rw_cells_agree; [exact AG9| exact QC|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT9; lia. }
    pose proof (wr_at_transport usegs mX m9 _ _ WRF WM9) as WRF9. pose proof (wr_at_transport usegs mX m9 _ _ WRA WM9) as WRA9.
    assert (SAVF9 : rw_cells usegs m9 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG9| exact SAVF|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT9; lia. }
    assert (SAVA9 : rw_cells usegs m9 (S + -104) [C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 (Z_to_bv 64 D);
                                                   C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 0xe1b18)]).
    { eapply rw_cells_agree; [exact AG9| exact SAVA|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT9; lia. }
    clear ENV HP LXS LXF SEW AUX ERR MI ST PRES SO FA K0 K8 K16 K24 K32 K40 K48 RDB NULM STKA STB WB PKT SUBS QZ NUL WRF WRA SAVF SAVA HU9 HG9 MU9 WM9 AG9 OUT9.
    pose proof ENV9 as (HP & LXS & LXF & SEW & AUX & (errv9 & ERR) & MI & ST & PRES & SO & FA & PAY).
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (a2p_w7 S lo Aq y1 gp (Z_to_bv 64 RATP) y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
               F fc m9 ST ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) ltac:(lia) ltac:(left; lia) ltac:(clear - SP16; Z.div_mod_to_equations; lia) ltac:(clear - QA16; Z.div_mod_to_equations; lia) SUBS9 Q09). }
    intros ms10 (m10 & jf & -> & MU10 & WM10 & MI10 & ST10 & FRC10).
    pose proof (agree_on_of_munch _ _ _ MU10 WM10) as AG10.
    assert (ENV10 : FENV m10 sX [(pq, Aq, 40); (pb, A, n + 1)] (S + -2288)).
    { apply (FENV_munch m9 m10 sX _ L (S + -2288) [(S + -2288, S + -2240)] ENV9 MU10 WM10 MI10 ST10).
      - apply (flags_munch _ m9 m10 LXF MU10 WM10). cbn [outside]. unfold LX_FLAGS. split; [lia| exact I].
      - constructor; [| constructor]. left. cbn [fst snd]. lia. }
    pose proof (wr_at_transport usegs m9 m10 _ _ WRF9 WM10) as WRF10. pose proof (wr_at_transport usegs m9 m10 _ _ WRA9 WM10) as WRA10.
    assert (SAVF10 : rw_cells usegs m10 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG10| exact SAVF9|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. split; [lia| exact I]. }
    assert (SAVA10 : rw_cells usegs m10 (S + -104) [C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 (Z_to_bv 64 D);
                                                    C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 0xe1b18)]).
    { eapply rw_cells_agree; [exact AG10| exact SAVA9|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. split; [lia| exact I]. }
    clear ENV9 HP LXS LXF SEW AUX ERR MI ST PRES SO FA PAY SUBS9 Q09 WRF9 WRA9 SAVF9 SAVA9 MU10 WM10 AG10.
    pose proof ENV10 as (HP & LXS & LXF & SEW & AUX & (errv10 & ERR) & MI & ST & PRES & SO & FA & PAY).
    destruct LXS as (_ & _ & _ & _ & GOTF & HKF).
    eapply implM_evt_cut.
    { apply (cf_w (S + -2288) lo (Z_to_bv 64 0x1295c8) gp (Z_to_bv 64 RATP) y5 y6 y7 (Z_to_bv 64 (S + -2240)) (Z_to_bv 64 (S + -2216)) (Z_to_bv 64 Aq)
               (Z_to_bv 64 0x255ff) (Z_to_bv 64 540) y13 y14 y15 y16 y17 (Z_to_bv 64 0x255ff) (Z_to_bv 64 0) y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31
               F fc m10 ST ltac:(lia) ltac:(lia) ltac:(lia) MI HKF GOTF). }
    intros ms11 (m11 & t1' & a3' & a4' & -> & MU11 & WM11 & MI11 & ST11).
    pose proof (agree_on_of_munch _ _ _ MU11 WM11) as AG11.
    assert (ENV11 : FENV m11 sX [(pq, Aq, 40); (pb, A, n + 1)] (S + -2288)).
    { apply (FENV_munch m10 m11 sX _ (S + -2288) (S + -2288) [(S + -2288 + -16, S + -2288)] ENV10 MU11 WM11 MI11 ST11).
      - apply (flags_munch _ m10 m11 LXF MU11 WM11). cbn [outside]. unfold LX_FLAGS. split; [lia| exact I].
      - constructor; [| constructor]. left. cbn [fst snd]. lia. }
    pose proof (wr_at_transport usegs m10 m11 _ _ WRF10 WM11) as WRF11. pose proof (wr_at_transport usegs m10 m11 _ _ WRA10 WM11) as WRA11.
    assert (SAVF11 : rw_cells usegs m11 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG11| exact SAVF10|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. split; [lia| exact I]. }
    assert (SAVA11 : rw_cells usegs m11 (S + -104) [C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 (Z_to_bv 64 D);
                                                    C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 0xe1b18)]).
    { eapply rw_cells_agree; [exact AG11| exact SAVA10|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. split; [lia| exact I]. }
    assert (FRC11 : rw_cells usegs m11 (S + -2288) (cmp_frame jf y19 y18 y9 (Z_to_bv 64 S) (Z_to_bv 64 0x215b98))).
    { eapply rw_cells_agree; [exact AG11| exact FRC10|]. intros a Ha. cbn [cmp_frame cells_size csize Nat.add] in Ha. cbn [outside]. split; [lia| exact I]. }
    clear ENV10 HP LXF SEW AUX ERR MI ST PRES SO FA PAY WRF10 WRA10 SAVF10 SAVA10 FRC10 MU11 WM11 AG11 GOTF HKF.
    pose proof ENV11 as (HP & LXS & LXF & SEW & AUX & (errv11 & ERR) & MI & ST & PRES & SO & FA & PAY).
    eapply implM_bind.
    { eapply (free_callZ HF) with (B := B) (lo := lo) (A := Aq) (n := 40) (errv := errv11);
        [exact HP| left; reflexivity| exact AUX| lia| exact ST| exact LOC| unfold RFREE_STACK; lia| exact ERR| exact MI| lia]. }
    cbv beta. intros [] s12 ms12 PO. unfold free_postZ in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m12 & -> & MI12 & ST12 & ERR12 & AUX12 & HPR12 & FA12 & SO12 & HP12).
    pose proof (LH_nodup _ _ _ HP) as ND. cbn [app] in ND, HPR12, HP12. rewrite (lb_remove_head pq Aq 40 _ ND) in HPR12, HP12.
    replace (ret_pc (Z_to_bv 64 0x1295c8)) with (Z_to_bv 64 0x1295c8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HPR12) as AG12.
    destruct (wr_at_rw_CB m11 L 2136 WRA11 ltac:(lia)) as (jl & FBL). change (Z.to_nat 2136) with 2136%nat in FBL.
    assert (FRA11 : rw_cells usegs m11 L [CB 2136 jl; C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 (Z_to_bv 64 D);
                                          C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 0xe1b18)]).
    { apply (proj2 (rw_cells_app m11 L [CB 2136 jl] _)). split; [exact FBL|]. cbn [cells_size csize Nat.add].
      replace (L + Z.of_nat 2136) with (S + -104) by lia. exact SAVA11. }
    apply (st4 m12 s12 pb A _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc jf jl y19 y18 y9).
    - apply (FENV_heap m11 m12 sX s12 _ [(pb, A, n + 1)] ((pb, A, n + 1) :: LB) (S + -2288) errv11 ENV11 ltac:(lia) ltac:(intros b Hb; right; exact Hb) MI12 ST12 ERR12 AUX12 HPR12 FA12 SO12). exact HP12.
    - exact FRM.
    - eapply rw_cells_agree; [exact AG12| exact FRC11|]. intros a Ha. cbn [cmp_frame cells_size csize Nat.add] in Ha. left. lia.
    - eapply rw_cells_agree; [exact AG12| exact FRA11|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. left. lia.
    - eapply wr_at_agree; [exact AG12| exact WRF11|]. intros a Ha. left. lia.
    - eapply rw_cells_agree; [exact AG12| exact SAVF11|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. left. lia.
  Qed.
  (* [comment removed for export] *)
  Lemma st3a : forall (mX : mem) (sX : PState) (pb pq : bptr) (A Aq : Z)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (jf jz jf2 j5 j7 junk : list byte) (eb : byte),
    FENV mX sX [(pq, Aq, 40); (pb, A, zlength d + 1)] (L + -80 + -48) -> frm0 fc ->
    rw_cells usegs mX (L + -80 + -48) (cmp_frame jf (wz 0) (wz D) (wz 40) (wz (L + -48)) (wz 0xe1c38)) ->
    rw_cells usegs mX (L + -80) (z32_frame jz (wz (S + -2216)) (wz L) (wz 0x128c10)) ->
    rw_cells usegs mX (L + -48) (cmp_frame jf2 (wz A) (wz D) (wz (-1)) (wz S) (wz 0x2158e8)) ->
    wr_at usegs mX L 2136 -> rw_cells usegs mX (S + -104) (A2SAVES A) ->
    rw_cells usegs mX (S + -2216) (pkp_cells (S + 12) j5 j7 eb) -> bv_unsigned eb mod 2 = 0 ->
    wr_at usegs mX S 96 -> rw_cells usegs mX (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra] ->
    rw_cells usegs mX (A + zlength d) [C1 (Z_to_bv 8 0)] ->
    rw_cells usegs mX Aq [CB (Z.to_nat 40) junk] ->
    implM usegs (mbind (raw_free pq) (fun _ => mbind (raw_free pb) (fun _ => mret 0))) sX POST
      (MS (mkR (wz 0xe1bc8) (wz (L + -80 + -48)) gp (wz RATP) x5 x6 x7 (wz (L + -80)) (wz 110) (wz Aq) x11 x12 x13 x14 x15 x16 x17 (wz 0x255ff) (wz 40)
               S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31) F (wz 0xe1bc8) fc None mX (seg_rom usegs)).
  Proof.
    intros until eb. intros ENV FRM CMF ZF IFR WRA SAVA PKT EBE WRF SAVF NUL QJ.
    pose proof ENV as (HP & LXS & LXF & SEW & AUX & (errv & ERR) & MI & ST & PRES & SO & FA & PAY).
    pose proof usp_range as (UR1 & UR2). unfold LX_FUZZ_STACK in *. unfold GLOBALS_TOP in LOG. unfold wz in *.
    pose proof alloc_ceiling_range as CR.
    assert (Hn : 0 <= zlength d) by (unfold zlength; lia). set (n := zlength d) in *.
    pose proof (LH_block_range _ _ _ (pb, A, n + 1) HP ltac:(right; left; reflexivity)) as (BA0 & BA16 & _ & BAC & BAI).
    pose proof (LH_block_range _ _ _ (pq, Aq, 40) HP ltac:(left; reflexivity)) as (QA0 & QA16 & _ & QAC & QAI).
    cbn [blk_addr blk_size fst snd] in *.
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (cm_w2 (L + -80) lo Aq 0xe1c38 gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (L + -80)) (Z_to_bv 64 110) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 0x255ff) (Z_to_bv 64 40) S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31 F fc mX jf (Z_to_bv 64 0) (Z_to_bv 64 D) (Z_to_bv 64 40) (Z_to_bv 64 (L + -48))
               ST ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) CMF). }
    intros ms1 (-> & ST1).
    replace (ret_pc (Z_to_bv 64 0xe1c38)) with (Z_to_bv 64 0xe1c38) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (zl_w (L + -80) lo Aq (Z_to_bv 64 0xe1c38) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 (L + -48)) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 D) (Z_to_bv 64 0) S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31 F fc mX jz (Z_to_bv 64 (S + -2216)) (Z_to_bv 64 L) (Z_to_bv 64 0x128c10)
               ST1 ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) ZF). }
    intros ms2 (t1' & -> & ST2). replace (L + -80 + 32) with (L + -48) in * by lia.
    eapply implM_evt_cut.
    { apply (memset_callZ (Z_to_bv 64 0x128c10) (Z_to_bv 64 (L + -48)) gp (Z_to_bv 64 RATP) x5 t1' x7 (Z_to_bv 64 L) (Z_to_bv 64 (S + -2216))
               x13 x14 x15 x16 x17 (Z_to_bv 64 D) (Z_to_bv 64 0) S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31 F fc mX Aq 0 40 junk QJ MI); lia. }
    intros ms3 PO. unfold memset_postZ in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m3 & -> & MU3 & WM3 & MI3 & QZ3).
    replace (ret_pc (Z_to_bv 64 0x128c10)) with (Z_to_bv 64 0x128c10) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    change (Z.to_nat 40) with 40%nat in QZ3. change (0 mod 256) with 0 in QZ3.
    pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
    assert (OUT3 : forall a, lo <= a -> outside [(Aq, Aq + 40)] a) by (intros a Ha; cbn [outside]; split; [lia| exact I]).
    assert (ST3 : stk usegs m3 lo (L + -48)) by (apply (stk_munch _ mX m3 lo _ ST2 MU3 WM3); intros x Hx; apply OUT3; lia).
    assert (ENV3 : FENV m3 sX [(pq, Aq, 40); (pb, A, n + 1)] (L + -48)).
    { apply (FENV_munch mX m3 sX _ (L + -80 + -48) (L + -48) [(Aq, Aq + 40)] ENV MU3 WM3 MI3 ST3).
      - apply (flags_munch _ mX m3 LXF MU3 WM3). cbn [outside]. unfold LX_FLAGS. split; [lia| exact I].
      - constructor; [| constructor]. right; right. exists (pq, Aq, 40). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity| lia]. }
    pose proof (wr_at_transport usegs mX m3 _ _ WRF WM3) as WRF3. pose proof (wr_at_transport usegs mX m3 _ _ WRA WM3) as WRA3.
    assert (TR3 : forall a cs, rw_cells usegs mX a cs -> lo <= a -> rw_cells usegs m3 a cs).
    { intros a cs H Ha. eapply rw_cells_agree; [exact AG3| exact H|]. intros y Hy. apply OUT3. lia. }
    pose proof (TR3 _ _ SAVF ltac:(lia)) as SAVF3. pose proof (TR3 _ _ SAVA ltac:(lia)) as SAVA3.
    pose proof (TR3 _ _ IFR ltac:(lia)) as IFR3. pose proof (TR3 _ _ PKT ltac:(lia)) as PKT3.
    assert (NUL3 : rw_cells usegs m3 (A + n) [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_agree; [exact AG3| exact NUL|]. intros y Hy. cbn [cells_size csize Nat.add] in Hy. cbn [outside]. split; [| exact I].
      pose proof (LH_nodup _ _ _ HP) as ND. cbn [app map] in ND. inversion ND as [|? ? N1 _]; subst.
      pose proof (LH_disjoint _ _ _ (pq, Aq, 40) (pb, A, n + 1) HP ltac:(left; reflexivity) ltac:(right; left; reflexivity)) as DJ.
      cbn [blk_id blk_addr blk_size fst snd] in DJ. specialize (DJ ltac:(intros E; apply N1; left; symmetry; exact E)). lia. }
    clear ENV HP LXS LXF SEW AUX ERR MI ST PRES SO FA PAY CMF ZF IFR PKT WRF WRA SAVF SAVA NUL QJ ST1 ST2 MU3 WM3 AG3 OUT3 TR3.
    pose proof ENV3 as (HP & LXS & LXF & SEW & AUX & (errv3 & ERR) & MI & ST & PRES & SO & FA & PAY).
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (a2p_w6 L lo (S + -2216) (S + 12) Aq (Z_to_bv 64 0x128c10) gp (Z_to_bv 64 RATP) v0 v1 v2 c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 D) S4 S5 S6 S7 S8 S9 S10 S11
               v3 v4 v5 v6 F fc m3 jf2 j5 j7 eb (Z_to_bv 64 A) (Z_to_bv 64 D) (Z_to_bv 64 (-1)) (Z_to_bv 64 S)
               ST ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) ltac:(lia) ltac:(lia) IFR3 PKT3). }
    intros ms4 (m4 & -> & MU4 & WM4 & MI4 & ST4 & PKT4).
    pose proof (agree_on_of_munch _ _ _ MU4 WM4) as AG4.
    assert (OUT4 : forall a, (a < S + -2216 + 40 \/ S + -2216 + 48 <= a) -> outside [(S + -2216 + 40, S + -2216 + 48)] a) by (intros a Ha; cbn [outside]; split; [lia| exact I]).
    assert (ENV4 : FENV m4 sX [(pq, Aq, 40); (pb, A, n + 1)] L).
    { apply (FENV_munch m3 m4 sX _ (L + -48) L [(S + -2216 + 40, S + -2216 + 48)] ENV3 MU4 WM4 MI4 ST4).
      - apply (flags_munch _ m3 m4 LXF MU4 WM4). apply OUT4. unfold LX_FLAGS. lia.
      - constructor; [| constructor]. left. cbn [fst snd]. lia. }
    apply (st3b m4 sX pb pq A Aq _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc j7 eb ENV4 FRM).
    - exact (wr_at_transport usegs m3 m4 _ _ WRA3 WM4).
    - eapply rw_cells_agree; [exact AG4| exact SAVA3|]. intros y Hy. cbn [cells_size csize Nat.add] in Hy. apply OUT4. lia.
    - exact PKT4.
    - exact EBE.
    - exact (wr_at_transport usegs m3 m4 _ _ WRF3 WM4).
    - eapply rw_cells_agree; [exact AG4| exact SAVF3|]. intros y Hy. cbn [cells_size csize Nat.add] in Hy. apply OUT4. lia.
    - eapply rw_cells_agree; [exact AG4| exact NUL3|]. intros y Hy. cbn [cells_size csize Nat.add] in Hy. apply OUT4. lia.
    - eapply rw_cells_agree; [exact AG4| exact QZ3|]. intros y Hy. cbn [cells_size csize Nat.add] in Hy. apply OUT4. lia.
  Qed.
  (* [comment removed for export] *)
  Definition REST (pb : bptr) : M PState Z :=
    mbind (raw_malloc WPACKET_SUB_SIZE) (fun r2 => match r2 with
      | None => munr
      | Some q => mbind (raw_free q) (fun _ => mbind (raw_free pb) (fun _ => mret 0)) end).

  (* [comment removed for export] *)
  Lemma st2 : forall (mX : mem) (sX : PState) (pb : bptr) (A : Z)
      (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (jf j0 jc jo junk : list byte),
    FENV mX sX [(pb, A, zlength d + 1)] (S + -48) -> frm0 fc ->
    rw_cells usegs mX (S + -48) (cmp_frame jf S3 (wz D) (wz (zlength d)) S0 (wz 0xe1ac0)) ->
    rw_cells usegs mX S (fzp_frame j0 jc jo (wz 16) S2 S1 S0 ra) ->
    rw_cells usegs mX A [CB (Z.to_nat (zlength d + 1)) junk] ->
    implM usegs (REST pb) sX POST
      (MS (mkR (wz 0xe1bc8) (wz (S + -48)) gp (wz RATP) x5 x6 x7 (wz S) (wz 29) (wz A) x11 x12 x13 x14 x15 x16 x17 (wz 0x2ce58) (wz (zlength d + 1))
               S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31) F (wz 0xe1bc8) fc None mX (seg_rom usegs)).
  Proof.
    intros until junk. intros ENV FRM CMF FZF BLK.
    pose proof ENV as (HP & LXS & LXF & SEW & AUX & (errv & ERR) & MI & ST & PRES & SO & FA & PAY).
    pose proof usp_range as (UR1 & UR2). unfold LX_FUZZ_STACK in *. unfold GLOBALS_TOP in LOG. unfold wz in *.
    pose proof alloc_ceiling_range as CR.
    pose proof PAY as (PBY & _ & PD0 & PD63 & HD31 & PIN).
    assert (Hn : 0 <= zlength d) by (unfold zlength; lia). set (n := zlength d) in *.
    pose proof (LH_block_range _ _ _ (pb, A, n + 1) HP ltac:(left; reflexivity)) as (BA0 & BA16 & _ & BAC & BAI).
    cbn [blk_addr blk_size fst snd] in *.
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (cm_w2 S lo A 0xe1ac0 gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 29) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 0x2ce58) (Z_to_bv 64 (n + 1)) S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31 F fc mX jf S3 (Z_to_bv 64 D) (Z_to_bv 64 n) S0
               ST ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) CMF). }
    intros ms1 (-> & ST1).
    replace (ret_pc (Z_to_bv 64 0xe1ac0)) with (Z_to_bv 64 0xe1ac0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply implM_evt_cut.
    { apply (fzp_w2 usp D n A gp (Z_to_bv 64 RATP) x5 x6 x7 S0 x11 x12 x13 x14 x15 x16 x17 S3 S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31 F fc mX); lia. }
    intros ms2 ->.
    (* [comment removed for export] *)
    unfold fzp_frame in FZF.
    assert (WRF : wr_at usegs mX S 96).
    { apply (wr_at_sub mX S 128); [| lia| lia| lia]. apply (rw_cells_wr_at usegs mX S _ 128 FZF). reflexivity. }
    assert (SAVF : rw_cells usegs mX (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { pose proof (rw_cells_skip mX S [CB 12 j0; CB 16 jc; C4 (Z_to_bv 64 16); CB 64 jo] _ FZF) as H. cbn [cells_size csize Nat.add] in H. exact H. }
    assert (KLEN : LibKit.cell UCode.USEGS mX (usp + -100) 4 (Z_to_bv 64 16)).
    { pose proof (rw_cells_head mX _ _ _ (rw_cells_skip mX S [CB 12 j0; CB 16 jc] _ FZF)) as H. cbn [cells_size csize Nat.add] in H.
      replace (S + Z.of_nat 28) with (usp + -100) in H by lia. exact (KBridge.cell_C4 usegs mX _ _ (proj1 H)). }
    assert (RDD : LibKit.rd_ok mX D n).
    { destruct PIN as [E|(b & Hb & Hb1 & Hb2)]; [intros i Hi; unfold n in Hi; rewrite E in Hi; unfold zlength in Hi; cbn [length Z.of_nat] in Hi; lia|].
      pose proof (LH_block_range _ _ _ b HP ltac:(right; exact Hb)) as (_ & _ & _ & _ & RI).
      pose proof (rd_ok_bytesU mX D (to_bytes d) PBY) as R. rewrite to_bytes_length in R. fold (zlength d) in R. fold n in R.
      apply R. fold n in Hb2. lia. }
    eapply implM_evt_cut.
    { apply (decode_evt (Z_to_bv 64 0xe1ae0) (Z_to_bv 64 S) gp (Z_to_bv 64 RATP) x5 x6 x7 (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 D) (Z_to_bv 64 n)
               (Z_to_bv 64 (usp + -96)) (Z_to_bv 64 (usp + -100)) x14 x15 x16 x17 (Z_to_bv 64 D) S3 S4 S5 S6 S7 S8 S9 S10 S11 x28 x29 x30 x31 F fc mX
               S D n (usp + -96) (usp + -100) 16 eq_refl eq_refl eq_refl eq_refl eq_refl
               (LibKit.v_jalr_even (Z_to_bv 64 0xe1ae0) ltac:(reflexivity)) ltac:(lia) ltac:(lia) ltac:(lia) RDD ltac:(lia) KLEN
               ltac:(lia) ltac:(lia) (KBridge.wr_ok_stk usegs mX lo S (S - 160) 160 ST1 ltac:(lia) ltac:(lia))
               ltac:(lia) ltac:(lia) (KBridge.wr_ok_wr_at usegs mX S 96 (usp + -96) (4 * 16) WRF ltac:(lia) ltac:(lia))
               ltac:(lia) ltac:(lia) (KBridge.wr_ok_wr_at usegs mX S 96 (usp + -100) 4 WRF ltac:(lia) ltac:(lia))
               ltac:(right; lia) ltac:(right; lia) ltac:(right; lia) ltac:(clear - SP16; Z.div_mod_to_equations; lia) ltac:(clear - SP16; Z.div_mod_to_equations; lia)). }
    intros ms3 (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & -> & HU3 & HG3).
    set (W3l := [(S - 160, S); (usp + -96, usp + -96 + 64); (usp + -100, usp + -100 + 4)]).
    assert (MU3 : munch W3l mX m3).
    { apply (KBridge.munch_of_unch W3l mX m3 _ HU3). intros x Hx Ho. unfold UDecode.dec_FP, LibKit.inr in Hx. unfold W3l in Ho. cbn [outside] in Ho. lia. }
    pose proof (KBridge.wmono_of_grows usegs mX m3 HG3) as WM3.
    assert (MI3 : mem_inv usegs m3).
    { apply (KBridge.mem_inv_unch usegs mX m3 _ MI HU3). intros x Hx. unfold UDecode.dec_FP, LibKit.inr in Hx.
      destruct Hx as [Hx|[Hx|Hx]]; [apply (stk_wview mX lo S); [exact ST1| lia]| apply (wr_at_wview mX S 96); [exact WRF| lia]
        | apply (wr_at_wview mX S 96); [exact WRF| lia]]. }
    pose proof (KBridge.stk_grows usegs mX m3 lo S ST1 HG3) as ST3.
    assert (OUT3 : forall a, (a < S - 160 \/ S + 96 <= a) -> outside W3l a) by (intros a Ha; unfold W3l; cbn [outside]; lia).
    assert (ENV3 : FENV m3 sX [(pb, A, n + 1)] S).
    { apply (FENV_munch mX m3 sX _ (S + -48) S W3l ENV MU3 WM3 MI3 ST3).
      - apply (flags_munch _ mX m3 LXF MU3 WM3). apply OUT3. unfold LX_FLAGS. lia.
      - unfold W3l. repeat (constructor; [left; cbn [fst snd]; lia|]). constructor. }
    pose proof (agree_on_of_munch _ _ _ MU3 WM3) as AG3.
    pose proof (wr_at_transport usegs mX m3 _ _ WRF WM3) as WRF3.
    assert (SAVF3 : rw_cells usegs m3 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG3| exact SAVF|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT3. lia. }
    assert (BLK3 : rw_cells usegs m3 A [CB (Z.to_nat (n + 1)) junk]).
    { eapply rw_cells_agree; [exact AG3| exact BLK|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite Nat.add_0_r, Z2Nat.id in Ha by lia. apply OUT3. lia. }
    clear ENV HP LXS LXF SEW AUX ERR MI ST PRES SO FA PAY PBY PIN CMF FZF BLK WRF SAVF KLEN RDD ST1 HU3 HG3 MU3 WM3 AG3 OUT3.
    pose proof ENV3 as (HP & LXS & LXF & SEW & AUX & (errv3 & ERR) & MI & ST & PRES & SO & FA & PAY).
    pose proof PAY as (PBY & _ & _ & _ & _ & PIN).
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (fzp_w3 usp D n A (Z_to_bv 64 0xe1ae0) gp (Z_to_bv 64 RATP) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' S3 S4 S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6' F fc m3). }
    intros ms4 ->.
    assert (SPLIT : exists j1 j2, rw_cells usegs m3 A [CB (Z.to_nat n) j1] /\ rw_cells usegs m3 (A + n) [CB 1 j2]).
    { apply (rw_cells_split_CB usegs _ _ [] (Z.to_nat (n + 1)) _ [] [Z.to_nat n; 1%nat]) in BLK3; [| cbn; lia]. cbn [mk_CB_cells app] in BLK3.
      exists (firstn (Z.to_nat n) junk), (firstn 1 (skipn (Z.to_nat n) junk)). split; [exact (rw_cells_head m3 _ _ _ BLK3)|].
      pose proof (rw_cells_tail m3 _ _ _ BLK3) as H. cbn [csize] in H. rewrite Z2Nat.id in H by lia. exact H. }
    destruct SPLIT as (j1 & j2 & BLKN & BLK1).
    destruct (wr_at_rw_C1 m3 (A + n) (rw_cells_wr_at usegs m3 (A + n) _ 1 BLK1 ltac:(cbn; lia))) as (bz & NUL3).
    assert (DSEP : D + n <= A \/ A + n <= D).
    { destruct PIN as [E|(b & Hb & Hb1 & Hb2)]; [unfold n; rewrite E; unfold zlength; cbn [length Z.of_nat]; lia|].
      pose proof (LH_nodup _ _ _ HP) as ND. cbn [app map] in ND. inversion ND as [|? ? N1 _]; subst.
      pose proof (LH_disjoint _ _ _ (pb, A, n + 1) b HP ltac:(left; reflexivity) ltac:(right; exact Hb)) as DJ.
      cbn [blk_id blk_addr blk_size fst snd] in DJ. specialize (DJ ltac:(intros E; apply N1; cbn [blk_id fst]; rewrite E; apply in_map; exact Hb)). fold n in Hb2. lia. }
    eapply implM_evt_cut.
    { apply (memcpy_callZ (Z_to_bv 64 0xe1af4) (Z_to_bv 64 S) gp (Z_to_bv 64 RATP) t0' t1' t2' (Z_to_bv 64 A) (Z_to_bv 64 n) a3' a4' a5' a6' a7'
               (Z_to_bv 64 D) S3 S4 S5 S6 S7 S8 S9 S10 S11 t3' t4' t5' t6' F fc m3 A D n (to_bytes d) j1 PBY);
        [rewrite to_bytes_length; unfold n, zlength; lia| exact BLKN| lia| lia| lia| lia| exact MI]. }
    intros ms5 PO. unfold memcpy_postZ in PO.
    destruct PO as (v0 & v1 & v2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m5 & -> & MU5 & WM5 & MI5 & BLK5 & _).
    replace (ret_pc (Z_to_bv 64 0xe1af4)) with (Z_to_bv 64 0xe1af4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_on_of_munch _ _ _ MU5 WM5) as AG5.
    assert (OUT5 : forall a, lo <= a -> outside [(A, A + n)] a) by (intros a Ha; cbn [outside]; split; [lia| exact I]).
    assert (ST5 : stk usegs m5 lo S) by (apply (stk_munch _ m3 m5 lo _ ST MU5 WM5); intros x Hx; apply OUT5; lia).
    assert (ENV5 : FENV m5 sX [(pb, A, n + 1)] S).
    { apply (FENV_munch m3 m5 sX _ S S [(A, A + n)] ENV3 MU5 WM5 MI5 ST5).
      - apply (flags_munch _ m3 m5 LXF MU5 WM5). cbn [outside]. unfold LX_FLAGS. split; [lia| exact I].
      - constructor; [| constructor]. right; right. exists (pb, A, n + 1). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity| lia]. }
    pose proof (wr_at_transport usegs m3 m5 _ _ WRF3 WM5) as WRF5.
    assert (SAVF5 : rw_cells usegs m5 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG5| exact SAVF3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT5. lia. }
    assert (NUL5 : rw_cells usegs m5 (A + n) [C1 bz]).
    { eapply rw_cells_agree; [exact AG5| exact NUL3|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. split; [lia| exact I]. }
    clear ENV3 HP LXS LXF SEW AUX ERR MI ST PRES SO FA PAY PBY PIN BLK3 BLKN BLK1 NUL3 WRF3 SAVF3 DSEP MU5 WM5 AG5 OUT5 BLK5.
    pose proof ENV5 as (HP & LXS & LXF & SEW & AUX & (errv5 & ERR) & MI & ST & PRES & SO & FA & PAY).
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (fzp_w4a S A n lo (Z_to_bv 64 0xe1af4) gp (Z_to_bv 64 RATP) v0 v1 v2 (Z_to_bv 64 A) c1 c2 c3 c4 c5 c6 c7 (Z_to_bv 64 D) S3 S4 S5 S6 S7 S8 S9 S10 S11
               v3 v4 v5 v6 F fc m5 bz ST ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) ltac:(lia) ltac:(lia) NUL5 ltac:(left; lia)). }
    intros ms6 (m6 & jA & jp & jbuf & jpad & -> & MU6 & WM6 & MI6 & ST6 & FRA6 & NUL6).
    pose proof (agree_on_of_munch _ _ _ MU6 WM6) as AG6.
    assert (ENV6 : FENV m6 sX [(pb, A, n + 1)] L).
    { apply (FENV_munch m5 m6 sX _ S L [(S + -2240, S); (A + n, A + n + 1)] ENV5 MU6 WM6 MI6 ST6).
      - apply (flags_munch _ m5 m6 LXF MU6 WM6). cbn [outside]. unfold LX_FLAGS. split; [lia| split; [lia| exact I]].
      - constructor; [left; cbn [fst snd]; lia|]. constructor; [| constructor]. right; right. exists (pb, A, n + 1). cbn [blk_addr blk_size fst snd]. split; [left; reflexivity| lia]. }
    pose proof (wr_at_transport usegs m5 m6 _ _ WRF5 WM6) as WRF6.
    assert (SAVF6 : rw_cells usegs m6 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG6| exact SAVF5|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. split; [lia| split; [lia| exact I]]. }
    unfold a2p_frame in FRA6.
    assert (WRA6 : wr_at usegs m6 L 2136).
    { apply (wr_at_sub m6 L 2240); [| lia| lia| lia]. apply (rw_cells_wr_at usegs m6 L _ 2240 FRA6). reflexivity. }
    assert (SAVA6 : rw_cells usegs m6 (S + -104) [C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 (Z_to_bv 64 D);
                                                  C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 0xe1b18)]).
    { pose proof (rw_cells_skip m6 L [CB 24 jA; CB 56 jp; CB 2048 jbuf; CB 8 jpad] _ FRA6) as H. cbn [cells_size csize Nat.add] in H.
      replace (L + Z.of_nat 2136) with (S + -104) in H by lia. exact H. }
    assert (PKJ6 : rw_cells usegs m6 (S + -2216) [CB 56 jp]).
    { pose proof (rw_cells_head m6 _ _ _ (rw_cells_skip m6 L [CB 24 jA] _ FRA6)) as H. cbn [cells_size csize Nat.add] in H.
      replace (L + Z.of_nat 24) with (S + -2216) in H by lia. exact H. }
    clear ENV5 HP LXS LXF SEW AUX ERR MI ST PRES SO FA PAY WRF5 SAVF5 NUL5 MU6 WM6 AG6 FRA6.
    pose proof ENV6 as (HP & LXS & LXF & SEW & AUX & (errv6 & ERR) & MI & ST & PRES & SO & FA & PAY).
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (a2p_w4b L lo (S + -2216) (S + 12) gp (Z_to_bv 64 RATP) v0 v1 v2 (Z_to_bv 64 S) (Z_to_bv 64 (-1)) c4 c5 c6 c7 (Z_to_bv 64 D) (Z_to_bv 64 A)
               S4 S5 S6 S7 S8 S9 S10 S11 v3 v4 v5 v6 F fc m6 jp ST ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) ltac:(lia) ltac:(clear - SP16; Z.div_mod_to_equations; lia) ltac:(lia) PKJ6). }
    intros ms7 (m7 & jf2 & jz & j5 & j7 & eb & u1' & b3 & b4 & b5 & b6 & -> & MU7 & WM7 & MI7 & ST7 & IFR7 & ZF7 & PKT7 & EBE).
    pose proof (agree_on_of_munch _ _ _ MU7 WM7) as AG7.
    assert (OUT7 : forall a, (a < L + -80 \/ L <= a) -> (a < S + -2216 \/ S + -2216 + 56 <= a) -> outside [(L + -80, L); (S + -2216, S + -2216 + 56)] a)
      by (intros a H1 H2; cbn [outside]; lia).
    assert (ENV7 : FENV m7 sX [(pb, A, n + 1)] (L + -80)).
    { apply (FENV_munch m6 m7 sX _ L (L + -80) [(L + -80, L); (S + -2216, S + -2216 + 56)] ENV6 MU7 WM7 MI7 ST7).
      - apply (flags_munch _ m6 m7 LXF MU7 WM7). apply OUT7; unfold LX_FLAGS; lia.
      - constructor; [left; cbn [fst snd]; lia|]. constructor; [left; cbn [fst snd]; lia| constructor]. }
    pose proof (wr_at_transport usegs m6 m7 _ _ WRF6 WM7) as WRF7. pose proof (wr_at_transport usegs m6 m7 _ _ WRA6 WM7) as WRA7.
    assert (SAVF7 : rw_cells usegs m7 (S + 96) [C8 S2; C8 S1; C8 S0; C8 ra]).
    { eapply rw_cells_agree; [exact AG7| exact SAVF6|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT7; lia. }
    assert (SAVA7 : rw_cells usegs m7 (S + -104) [C8 S11; C8 S10; C8 S9; C8 S8; C8 S7; C8 S6; C8 S5; C8 S4; C8 S3; C8 (Z_to_bv 64 D);
                                                  C8 (Z_to_bv 64 (A + n)); C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 0xe1b18)]).
    { eapply rw_cells_agree; [exact AG7| exact SAVA6|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT7; lia. }
    assert (NUL7 : rw_cells usegs m7 (A + n) [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_agree; [exact AG7| exact NUL6|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply OUT7; lia. }
    clear ENV6 HP LXS LXF SEW AUX ERR MI ST PRES SO FA PAY WRF6 WRA6 SAVF6 SAVA6 NUL6 PKJ6 MU7 WM7 AG7 OUT7.
    pose proof ENV7 as (HP & LXS & LXF & SEW & AUX & (errv7 & ERR) & MI & ST & PRES & SO & FA & PAY).
    destruct LXF as (lv & LAT).
    pose proof LXS as (_ & _ & GOTM & HKM & _ & _).
    (* [comment removed for export] *)
    eapply implM_evt_cut.
    { apply (cm_w1 (L + -80) lo 40 (Z_to_bv 64 0xe1c38) gp (Z_to_bv 64 RATP) v0 u1' v2 (Z_to_bv 64 (L + -48)) (Z_to_bv 64 40) (Z_to_bv 64 0x255ff) (Z_to_bv 64 110)
               b3 b4 b5 b6 c7 (Z_to_bv 64 D) (Z_to_bv 64 0) S4 S5 S6 S7 S8 S9 S10 S11 v3 v4 v5 v6 F fc m7 lv
               ST ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) HKM GOTM LAT). }
    intros ms8 (m8 & jf8 & lv' & e1 & e2 & e3 & -> & MU8 & WM8 & MI8 & ST8 & CMF8 & LAT8).
    pose proof (agree_on_of_munch _ _ _ MU8 WM8) as AG8.
    assert (OUT8 : forall a, L + -80 <= a -> outside [(L + -80 + -48, L + -80); (0x32f7d0, 0x32f7d1)] a) by (intros a Ha; cbn [outside]; lia).
    assert (ENV8 : FENV m8 sX [(pb, A, n + 1)] (L + -80 + -48)).
    { apply (FENV_munch m7 m8 sX _ (L + -80) (L + -80 + -48) [(L + -80 + -48, L + -80); (0x32f7d0, 0x32f7d1)] ENV7 MU8 WM8 MI8 ST8).
      - exists lv'. exact LAT8.
      - constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; reflexivity| constructor]. }
    assert (TR8 : forall a cs, rw_cells usegs m7 a cs -> L + -80 <= a -> rw_cells usegs m8 a cs).
    { intros a cs H Ha. eapply rw_cells_agree; [exact AG8| exact H|]. intros y Hy. apply OUT8. lia. }
    pose proof (TR8 _ _ SAVF7 ltac:(lia)) as SAVF8. pose proof (TR8 _ _ SAVA7 ltac:(lia)) as SAVA8.
    pose proof (TR8 _ _ IFR7 ltac:(lia)) as IFR8. pose proof (TR8 _ _ ZF7 ltac:(lia)) as ZF8. pose proof (TR8 _ _ PKT7 ltac:(lia)) as PKT8.
    pose proof (wr_at_transport usegs m7 m8 _ _ WRF7 WM8) as WRF8. pose proof (wr_at_transport usegs m7 m8 _ _ WRA7 WM8) as WRA8.
    assert (NUL8 : rw_cells usegs m8 (A + n) [C1 (Z_to_bv 8 0)]).
    { eapply rw_cells_agree; [exact AG8| exact NUL7|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. cbn [outside]. lia. }
    clear ENV7 HP LXS SEW AUX ERR MI ST PRES SO FA PAY WRF7 WRA7 SAVF7 SAVA7 NUL7 IFR7 ZF7 PKT7 MU8 WM8 AG8 OUT8 TR8 LAT GOTM HKM LAT8.
    pose proof ENV8 as (HP & LXS & LXF & SEW & AUX & (errv8 & ERR) & MI & ST & PRES & SO & FA & PAY).
    unfold REST, WPACKET_SUB_SIZE.
    eapply implM_bind.
    { eapply (malloc_callZ HM) with (B := B) (lo := lo) (errv := errv8);
        [exact HP| exact AUX| lia| exact ST| exact LOC| unfold RMALLOC_STACK; lia| exact ERR| exact MI| lia| lia]. }
    cbv beta. intros r s9 ms9 PO. unfold malloc_postZ in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m9 & errv9 & -> & MI9 & ST9 & ERR9 & AUX9 & HPR9 & FA9 & SO9 & RES).
    destruct r as [pq|]; [| apply implM_unr].
    destruct RES as (Aq & junkq & -> & QR & HP9 & QJ9).
    replace (ret_pc (Z_to_bv 64 0xe1bc8)) with (Z_to_bv 64 0xe1bc8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HPR9) as AG9.
    assert (TR9 : forall a cs, rw_cells usegs m8 a cs -> L + -80 + -48 <= a -> rw_cells usegs m9 a cs).
    { intros a cs H Ha. eapply rw_cells_agree; [exact AG9| exact H|]. intros y Hy. left. lia. }
    apply (st3a m9 s9 pb pq A Aq _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc jf8 jz jf2 j5 j7 junkq eb).
    - apply (FENV_heap m8 m9 sX s9 _ [(pq, Aq, 40); (pb, A, n + 1)] ((pb, A, n + 1) :: LB) (L + -80 + -48) errv9 ENV8 ltac:(lia) ltac:(intros b Hb; right; exact Hb) MI9 ST9 ERR9 AUX9 HPR9 FA9 SO9). exact HP9.
    - exact FRM.
    - exact (TR9 _ _ CMF8 ltac:(lia)).
    - exact (TR9 _ _ ZF8 ltac:(lia)).
    - exact (TR9 _ _ IFR8 ltac:(lia)).
    - eapply wr_at_agree; [exact AG9| exact WRA8|]. intros a Ha. left. lia.
    - exact (TR9 _ _ SAVA8 ltac:(lia)).
    - exact (TR9 _ _ PKT8 ltac:(lia)).
    - exact EBE.
    - eapply wr_at_agree; [exact AG9| exact WRF8|]. intros a Ha. left. lia.
    - exact (TR9 _ _ SAVF8 ltac:(lia)).
    - eapply rw_cells_agree; [exact AG9| exact NUL8|]. intros a Ha. cbn [cells_size csize Nat.add] in Ha. right; right. exists (pb, A, n + 1).
      cbn [blk_addr blk_size fst snd]. split; [left; reflexivity| lia].
    - exact QJ9.
  Qed.
  (* [comment removed for export] *)
  Lemma st1 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
    FENV m0 s [] usp -> frm0 fc ->
    implM usegs (fuzz_one lops d) s POST
      (MS (mkR ra (wz usp) gp (wz RATP) t0 t1 t2 S0 S1 (wz D) (wz (zlength d)) a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6)
          F (wz LX_FUZZ) fc None m0 (seg_rom usegs)).
  Proof.
    intros until fc. intros ENV FRM.
    pose proof ENV as (HP & LXS & LXF & SEW & AUX & (errv & ERR) & MI & ST & PRES & SO & FA & PAY).
    pose proof usp_range as (UR1 & UR2). unfold LX_FUZZ_STACK in *. unfold GLOBALS_TOP in LOG. unfold wz, LX_FUZZ in *.
    pose proof alloc_ceiling_range as CR.
    pose proof PAY as (_ & _ & _ & _ & HD31 & _).
    assert (Hn : 0 <= zlength d) by (unfold zlength; lia). set (n := zlength d) in *.
    eapply implM_evt_cut.
    { apply (fzp_w1 usp lo D n ra gp (Z_to_bv 64 RATP) t0 t1 t2 S0 S1 a2 a3 a4 a5 a6 a7 S2 S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6 F fc m0
               ST ltac:(lia) ltac:(lia) ltac:(lia) MI). }
    intros ms1 (m1 & j0 & jc & jo & -> & MU1 & WM1 & MI1 & ST1 & FZF1).
    assert (ENV1 : FENV m1 s [] S).
    { apply (FENV_munch m0 m1 s _ usp S [(usp + -128, usp)] ENV MU1 WM1 MI1 ST1).
      - apply (flags_munch _ m0 m1 LXF MU1 WM1). cbn [outside]. unfold LX_FLAGS. split; [lia| exact I].
      - constructor; [left; cbn [fst snd]; lia| constructor]. }
    clear ENV HP LXS LXF SEW AUX ERR MI ST PRES SO FA PAY MU1 WM1.
    pose proof ENV1 as (HP & LXS & LXF & SEW & AUX & (errv1 & ERR) & MI & ST & PRES & SO & FA & PAY).
    destruct LXF as (lv & LAT).
    pose proof LXS as (_ & _ & GOTM & HKM & _ & _).
    eapply implM_evt_cut.
    { apply (cm_w1 S lo (n + 1) (Z_to_bv 64 0xe1ac0) gp (Z_to_bv 64 RATP) t0 t1 t2 S0 (Z_to_bv 64 n) (Z_to_bv 64 0x2ce58) (Z_to_bv 64 29)
               a3 a4 a5 a6 a7 (Z_to_bv 64 D) S3 S4 S5 S6 S7 S8 S9 S10 S11 t3 t4 t5 t6 F fc m1 lv
               ST ltac:(lia) ltac:(lia) ltac:(lia) MI ltac:(lia) HKM GOTM LAT). }
    intros ms2 (m2 & jf & lv' & e1 & e2 & e3 & -> & MU2 & WM2 & MI2 & ST2 & CMF2 & LAT2).
    pose proof (agree_on_of_munch _ _ _ MU2 WM2) as AG2.
    assert (ENV2 : FENV m2 s [] (S + -48)).
    { apply (FENV_munch m1 m2 s _ S (S + -48) [(S + -48, S); (0x32f7d0, 0x32f7d1)] ENV1 MU2 WM2 MI2 ST2).
      - exists lv'. exact LAT2.
      - constructor; [left; cbn [fst snd]; lia|]. constructor; [right; left; reflexivity| constructor]. }
    assert (FZF2 : rw_cells usegs m2 S (fzp_frame j0 jc jo (Z_to_bv 64 16) S2 S1 S0 ra)).
    { eapply rw_cells_agree; [exact AG2| exact FZF1|]. intros y Hy. cbn [fzp_frame cells_size csize Nat.add] in Hy. cbn [outside]. lia. }
    clear ENV1 HP LXS SEW AUX ERR MI ST PRES SO FA PAY MU2 WM2 AG2 FZF1 LAT GOTM HKM LAT2.
    pose proof ENV2 as (HP & LXS & LXF & SEW & AUX & (errv2 & ERR) & MI & ST & PRES & SO & FA & PAY).
    unfold fuzz_one, lops, Target.ops. cbn [bind lib_malloc lib_free ret unreachable].
    eapply implM_bind.
    { eapply (malloc_callZ HM) with (B := B) (lo := lo) (errv := errv2);
        [exact HP| exact AUX| lia| exact ST| exact LOC| unfold RMALLOC_STACK; lia| exact ERR| exact MI| lia| lia]. }
    cbv beta. intros r s3 ms3 PO. unfold malloc_postZ in PO.
    destruct PO as (w0 & w1 & w2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & w3 & w4 & w5 & w6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & HPR3 & FA3 & SO3 & RES).
    destruct r as [pb|]; [| apply implM_unr].
    destruct RES as (A & junk & -> & BR & HP3 & BLK3).
    replace (ret_pc (Z_to_bv 64 0xe1bc8)) with (Z_to_bv 64 0xe1bc8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (agree_of_heap_pres _ _ _ _ HPR3) as AG3.
    apply (st2 m3 s3 pb A _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc jf j0 jc jo junk).
    - apply (FENV_heap m2 m3 s s3 _ [(pb, A, n + 1)] LB (S + -48) errv3 ENV2 ltac:(lia) ltac:(auto) MI3 ST3 ERR3 AUX3 HPR3 FA3 SO3). exact HP3.
    - exact FRM.
    - eapply rw_cells_agree; [exact AG3| exact CMF2|]. intros y Hy. cbn [cmp_frame cells_size csize Nat.add] in Hy. left. lia.
    - eapply rw_cells_agree; [exact AG3| exact FZF2|]. intros y Hy. cbn [fzp_frame cells_size csize Nat.add] in Hy. left. lia.
    - exact BLK3.
  Qed.
End FZ.
(* [comment removed for export] *)
Theorem rfuzz_one_proof : rmalloc_stmt -> rfree_stmt -> rfuzz_one_stmt.
Proof.
  intros HM HF. unfold rfuzz_one_stmt. intros until canary.
  intros HEAP STAT FLG SERR SSP AUX SPB B63 ST CEIL LOG LOSP ERR TP MI SP16 PAY FRM -> ->. subst tp.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (ssp_canary_0 _ _ _ _ HEAP SSP) as CAN.
  assert (ESP : sp = wz (bv_unsigned sp)) by (unfold wz; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP at 2. rewrite ESP at 1.
  apply (st1 HM HF ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (bv_unsigned sp) s LB D d lo B canary m SPB B63 CEIL LOG LOSP SP16 CAN ltac:(lia)).
  - split; [exact HEAP|]. split; [exact STAT|]. split; [destruct FLG as (b & Hb); exists b; exact Hb|]. split; [exact SERR|]. split; [exact AUX|].
    split. { exists errv. unfold errno_addr in ERR. unfold LX_ERRNO, RATP in *. unfold wz in ERR. rewrite unsigned_lit in ERR by lia. exact ERR. }
    split; [exact MI|]. split; [exact ST|]. split; [apply lx_pres_refl|]. split; [reflexivity|]. split; [reflexivity| exact PAY].
  - exact FRM.
Qed.
End WithCeiling0.
