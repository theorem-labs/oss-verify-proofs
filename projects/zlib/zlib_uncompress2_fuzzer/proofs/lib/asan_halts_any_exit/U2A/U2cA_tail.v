(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps Harness.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AShadow U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AObj U2AClient U2AIface U2AGlue U2AIfaceS InfABase InfAIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2cA_glue.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2cA_pre U2cA_loop U2cA_epi U2cA_inv U2cA_loopA.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.

Lemma uc_byte_of_c1 : forall m s b, rw_cells asegs m s [C1 b] -> 0x67e000 <= s -> m (wa s) = Some b.
Proof.
  intros m s b [[_ (A & B & H)] _] Hs. cbn [cells_bytes cbytes app length] in B, H.
  specialize (H 0%nat ltac:(lia)). cbn in H. rewrite Z.add_0_r in H.
  rewrite <- (mrd_no_image asegs m s (s + 1) s (no_image_asan s (s + 1) Hs)) by lia.
  rewrite H. cbn. reflexivity.
Qed.
Lemma uc_mem_eq_single : forall (mp m' : amem) A b, 0 <= A -> A + 1 <= 2^64 ->
  munch [(A, A + 1)] mp m' -> m' (wa A) = Some b -> m' = write_to_mem mp (wa A) [b].
Proof.
  intros mp m' A b HA HB MU Hb. apply functional_extensionality. intros x.
  rewrite write_to_mem_spec by (cbn; lia). cbn [length]. change (Z.of_nat 1) with 1.
  pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  destruct (Z.eq_dec (bv_unsigned x) A) as [E|NE].
  - replace x with (wa A) by (rewrite <- E; unfold wa; apply Z_to_bv_bv_unsigned). rewrite Hb, wa_unsigned by lia.
    replace (A <=? A) with true by (symmetry; apply Z.leb_le; lia). replace (A <? A + 1) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.sub_diag. reflexivity.
  - rewrite MU by (cbn; lia).
    destruct (Z.leb_spec0 A (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (A + 1)); cbn [andb]; try reflexivity. exfalso; lia.
Qed.

Lemma lb_remove_hd : forall p A n LB, ~ In p (hb_ids LB) -> lb_remove p (HB p A n :: LB) = LB.
Proof.
  intros p A n LB NI. unfold lb_remove. rewrite filter_cons. destruct (decide _) as [Y|N].
  { exfalso. cbn [ab_kind abkind_eqb] in Y. rewrite N.eqb_refl in Y. exact Y. }
  clear N. induction LB as [|b LB IH]; [reflexivity|].
  unfold hb_ids in NI. cbn [flat_map] in NI. fold (hb_ids LB) in NI.
  rewrite filter_cons. destruct (decide _) as [Y|N].
  - f_equal. apply IH. intros X. apply NI. apply in_or_app. right. exact X.
  - exfalso. apply N. destruct b as [[q|c] bA bn]; cbn [ab_kind abkind_eqb] in *; [| exact I].
    destruct (N.eqb_spec q p) as [->|NE]; [exfalso; apply NI; left; reflexivity| exact I].
Qed.

Lemma f8arr_blob : forall m A n f, f8arr asegs m A n f -> exists bs, rw_cells asegs m A [CB n bs].
Proof.
  intros m A n f [HB HW]. exists (map (fun i => Z_to_bv 8 (f (Z.of_nat i))) (seq 0 n)).
  rewrite length_map, length_seq in HW.
  split; [split|].
  - cbn. split; [rewrite length_map, length_seq; reflexivity| exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HB.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact HW.
Qed.

Section Tail.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation FB2 F := (mkABlock (ABFake 2) F 256).
Variable fflag : alayout -> Z -> Z -> Z.
Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Hypothesis END : forall withwin, inflateEnd_stmtA AI withwin.

Variables (gp tp : word) (FR : bvmap 5 word) (fc : bv 32).
Variables (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
Variables (L : alayout) (SPA Fu F1 FLG lo : Z).
Variables (S D n : Z) (payload : list Z) (ps : AsanCtrl.aptr) (LB0 : list ablock).
Variables (j8 j16 : list byte) (n0 : Z) (trc : list Z) (m0 : amem) (RNG0 : footprint) (sR : APS).
Notation SP := (bv_unsigned sp).
Variable SL : Z.
Hypothesis ESL : SL = SP + 8.
Notation DL := (SP + 16).
Notation Zs := (Fu + 32).
Notation SHF := (Z.shiftr Fu 3 + 2147450880).
Notation OB := A_OUTBUF.

Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis LOS : lo <= SP - UC_STACK.
Hypothesis ESPA : SPA = SP - 160 - SP mod 32.
Hypothesis SP16 : SP mod 16 = 0.
Hypothesis SPTOP : SP + 48 < al_top L.
Hypothesis FU256 : Fu mod 256 = 0.
Hypothesis FUB : ablk Fu (Fu + 256).
Hypothesis F1128 : F1 mod 128 = 0.
Hypothesis F1B : ablk F1 (F1 + 128).
Hypothesis F1IN : In (FB1 F1) LB0.
Hypothesis LBH : forall b, In b LB0 -> ablk (ab_addr b) (ab_addr b + ab_size b).
Hypothesis SBK : ablk S (S + 7176).
Hypothesis OBC : exists iv, In iv CI /\ fst iv <= OB /\ OB + 262144 <= snd iv.
Hypothesis S0SP : bv_unsigned s0 <= SP.
Hypothesis TPE : tp = Z_to_bv 64 ATP.
Hypothesis EFLG : FLG = fflag L 2 Fu.
Hypothesis UF1 : In [AFREE_PC; RA_END_ZFREE_W] (al_U L).
Hypothesis UF2 : In [AFREE_PC; RA_END_ZFREE_S] (al_U L).
Hypothesis RFU0 : rng RNG0 Fu 256.
Hypothesis RSFU0 : rng RNG0 SHF 32.
Hypothesis RF10 : rng RNG0 F1 128.
Hypothesis RSDL0 : rng RNG0 (Z.shiftr DL 3 + 2147450880) 1.
Hypothesis RSSL0 : rng RNG0 (Z.shiftr SL 3 + 2147450880) 1.
Hypothesis RSTK0 : rng RNG0 lo (al_top L - lo).
Hypothesis RIMG0 : rng_aimg RNG0.
Hypothesis N26 : 0 <= n < 67108864.
Hypothesis N0R : 0 <= n0 < 67108864.

Notation UINV := (uc_inv AI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu FLG lo S D n payload ps LB0 j8 j16 n0 trc m0 RNG0 sR SL).
Notation LBN := (LBn Fu S ps LB0).
Notation UEND := (uc_end AI gp tp FR fc ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu FLG lo S D n payload ps LB0 j8 j16 n0 trc m0 RNG0 sR SL).
Notation UPF := (uc_PF AI sp LB0 SL).

Lemma uspa_facts : SP - 176 <= SPA <= SP - 160 /\ SPA mod 32 = 0.
Proof. rewrite ESPA. Z.div_mod_to_equations. lia. Qed.

Definition uc_final (u : unit) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG0 RNG' /\ exists (av q5 q6 q7 q11 q12 q13 q14 q15 q16 q17 q28 q29 q30 q31 : word) (m' : amem),
    ms' = MS (mkR ra sp gp tp q5 q6 q7 s0 s1 av q11 q12 q13 q14 q15 q16 q17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 q28 q29 q30 q31)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo SP /\ aps_rest s' = aps_rest sR
    /\ AHEAP AI L RNG' (aps_m s') LB0 m'
    /\ magree asegs UPF m0 m'
    /\ (exists obr, rw_cells asegs m' OB [CB (Z.to_nat 262144) obr])
    /\ (exists slv, rw_cells asegs m' SL [C8 slv]) /\ (exists dlv, rw_cells asegs m' DL [C8 dlv]).

Lemma uc_keep2_client : forall a,
  In (FB2 Fu) (FB2 Fu :: LB0) ->
  (SPA <= a < 2^47 \/ Fu <= a < Fu + 32 \/ Fu + 144 <= a < Fu + 256 \/ SHF <= a < SHF + 32) ->
  aclient_addr CI (FB2 Fu :: LB0) SPA a /\ ~ in_ranges [(Zs, Zs + 112)] a.
Proof.
  intros a FIN KP. pose proof (ablk_lin _ _ FUB) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in *.
  pose proof uspa_facts as (SPAB & _). atop_facts. unfold UC_STACK in LOS.
  assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
  split.
  - destruct KP as [K|[K|[K|K]]].
    + left. lia.
    + right. right. left. exists (FB2 Fu). split; [exact FIN| cbn [ab_addr ab_size]; lia].
    + right. right. left. exists (FB2 Fu). split; [exact FIN| cbn [ab_addr ab_size]; lia].
    + right. right. right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right. right. exists 2, Fu, 256. split; [exact FIN|]. unfold ASHOFF. revert K. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      intros K. Z.div_mod_to_equations. lia.
  - intros (iv & Hiv & Hr). cbn [In] in Hiv. destruct Hiv as [<-|[]]. cbn [fst snd] in Hr.
    destruct KP as [K|[K|[K|K]]]; [lia| lia| lia|].
    apply (ablk_clear_band _ _ a FUB); [| lia]. unfold KLS. revert K. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. intros K. Z.div_mod_to_equations. lia.
Qed.

Lemma uc_tail : forall (withwin : bool) Wd RNG s LB pw ms,
  (if withwin then LB = HB pw Wd 32768 :: LBN else LB = LBN /\ Wd = 0) ->
  UEND Wd RNG s LB ms ->
  implMA RNG (free_all afree_M (if withwin then [pw; ps] else [ps])) s uc_final ms.
Proof.
  intros withwin Wd RNG s LB pw ms SHW (site & rcode & st & v & m & x5 & x6 & x7 & x11 & x12 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 & -> & RC & INV).
  pose proof INV as (AH & IO & AV & MD & EM & ST & MI & FRM & PFA & OK & RS & FP & SH).
  destruct (uc_shape_facts AI L Fu F1 S ps LB0 Wd RNG _ LB m AH SH)
    as (SUB & FIN & FNI & SIN & SNI & WIN).
  pose proof uspa_facts as (SPAB & SPA32).
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. atop_facts.
  pose proof (ablk_lin _ _ FUB) as (FL1 & FL2 & FL3 & FL4). pose proof (ablk_lin _ _ F1B) as (GL1 & GL2 & GL3 & GL4).
  pose proof (ablk_lin _ _ SBK) as (SL1 & SL2 & SL3 & SL4). unfold AIMG_HI in FL1, GL1, SL1.
  assert (F1IN' : In (FB1 F1) LB) by (apply SUB; exact F1IN).
  assert (SEPF : F1 + 128 <= Fu \/ Fu + 256 <= F1).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (FB2 Fu) (FB1 F1) AH FIN F1IN' ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia. }
  assert (SEPSG : S + 7176 <= F1 \/ F1 + 128 <= S).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB ps S 7176) (FB1 F1) AH SIN F1IN' ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia. }
  assert (USPA : bv_unsigned (Z_to_bv 64 SPA) = SPA) by (apply unsigned_lit; unfold UC_STACK in LOS; lia).
  assert (RFU : rng RNG Fu 256) by (eapply rng_fp_le; [exact FP| exact RFU0]).
  assert (RSFU : rng RNG SHF 32) by (eapply rng_fp_le; [exact FP| exact RSFU0]).
  assert (RF1 : rng RNG F1 128) by (eapply rng_fp_le; [exact FP| exact RF10]).
  assert (RDLCp : rng RNG DL 8) by (eapply rng_sub'; [eapply rng_fp_le; [exact FP| exact RSTK0]| unfold UC_STACK in LOS; lia]).
  assert (RSDL : rng RNG (Z.shiftr DL 3 + 2147450880) 1) by (eapply rng_fp_le; [exact FP| exact RSDL0]).
  assert (RSSL : rng RNG (Z.shiftr SL 3 + 2147450880) 1) by (eapply rng_fp_le; [exact FP| exact RSSL0]).
  assert (RSTK : rng RNG lo (al_top L - lo)) by (eapply rng_fp_le; [exact FP| exact RSTK0]).
  assert (RFRM : rng RNG SPA 56) by (eapply rng_sub'; [exact RSTK| unfold UC_STACK in LOS; lia]).
  assert (RSLCp : rng RNG SL 8) by (eapply rng_sub'; [exact RSTK| unfold UC_STACK in LOS; lia]).
  assert (SLRp : SL mod 8 = 0 /\ SPA + 56 <= SL /\ SL + 8 <= 2^47) by (rewrite ESL; unfold UC_STACK in LOS; Z.div_mod_to_equations; lia).
  unfold uc_emem, inf_emem in EM. cbn [ucx icx_of c_p c_q c_n c_ob c_osz c_w] in EM.
  destruct EM as (STRM & ISTC & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10).
  destruct FRM as (FRA & FRB & STG & FH & FFL & FSH & DLC & SLC & SHD & SHS & UC).
  destruct (f8arr_blob _ _ _ _ E7) as (obr & OBB).
  pose proof AV as (RG2 & _). unfold IDefs.RNG in RG2. cbn [ucx icx_of c_n c_osz] in RG2. destruct RG2 as (G1 & G2 & G3 & G4 & _).
  pose proof (mode_range _ _ _ _ AV) as MR.
  eapply implMA_evtF.
  { eapply (uc_exit gp tp sp FR fc D F1 Fu S lo SPA RNG SL ESL FU256 FUB RFU RSFU RSDL RSSL RFRM ltac:(unfold UC_STACK in LOS; lia)
                    ltac:(unfold UC_STACK in LOS; lia) SP16 RSLCp RDLCp);
      [exact MI| exact FRA| exact STRM| exact DLC| exact SLC| exact SHD| exact SHS| exact RC]. }
  cbv beta. intros ms1 (m1 & slv & dlv & y11 & y12 & q27 & -> & MU1 & WM1 & MI1 & DLC1 & SLC1).
  pose proof LOS as LOS'. unfold UC_STACK in LOS'.
  assert (FW1 : Forall wclr [(DL, DL + 8); (SL, SL + 8)]).
  { constructor; [apply wclr_high; lia|]. constructor; [apply wclr_high; lia | constructor]. }
  assert (AH1 : AHEAP AI L RNG (aps_m s) LB m1).
  { eapply (AI_frame AI _ _ _ _ m m1 _ AH MU1 WM1).
    constructor; [cbn [fst snd]; apply acr_stack; lia|].
    constructor; [cbn [fst snd]; apply acr_stack; lia | constructor]. }
  assert (IO1 : inf_objs AI RNG LB (ucx S D n Wd st) Fu Zs payload m1) by exact (inf_objs_wclr AI L Fu F1 payload _ RNG _ LB _ m m1 AH IO MU1 WM1 FW1).
  assert (SHBND : KLS <= SHF /\ SHF + 32 <= 0x10007fff8000).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold KLS. Z.div_mod_to_equations. lia. }
  assert (STRM1 := STRM). eapply rw_cells_transport in STRM1; [| exact MU1| exact WM1| rewrite strm_cells_size; cbn [disjoint_from]; repeat split; try exact I; lia].
  assert (ISTC1 := ISTC). eapply rw_cells_transport in ISTC1; [| exact MU1| exact WM1| rewrite istate_cells_size; cbn [disjoint_from]; repeat split; try exact I; lia].
  assert (ST1 : stk asegs m1 lo SPA) by (eapply stk_transport_disjoint; [exact ST| exact MU1| exact WM1| cbn [disjoint_from]; repeat split; try exact I; lia]).
  assert (STG1 : stk asegs m1 (SPA + 56) (SP + -104)) by (eapply stk_transport_disjoint; [exact STG| exact MU1| exact WM1| cbn [disjoint_from]; repeat split; try exact I; lia]).
  assert (FRA1 := FRA). eapply rw_cells_transport in FRA1; [| exact MU1| exact WM1| unfold UFRA; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (FRB1 := FRB). eapply rw_cells_transport in FRB1; [| exact MU1| exact WM1| unfold UFRB; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (FH1 := FH). eapply rw_cells_transport in FH1; [| exact MU1| exact WM1| unfold UFHD; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (FFL1 := FFL). eapply rw_cells_transport in FFL1; [| exact MU1| exact WM1| cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (FSH1 : rw_cells asegs m1 SHF UFSH) by (eapply rw_cells_transport_band; [exact FSH| exact MU1| exact WM1| exact FW1| lia| unfold UFSH; cbn [cells_size csize Nat.add]; lia]).
  assert (OBB1 := OBB). eapply rw_cells_transport in OBB1; [| exact MU1| exact WM1| unfold A_OUTBUF; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia].
  assert (PFA1 : magree asegs UPF m0 m1).
  { eapply magree_trans; [exact PFA|]. eapply magree_mono; [exact (magree_of_munch asegs _ m m1 MU1 WM1)|].
    intros a [_ NW]. cbn [outside]. split; [intros X; apply NW; exists (DL, DL + 8); split; [right; left; reflexivity| cbn [fst snd]; lia]|].
    split; [intros X; apply NW; exists (SL, SL + 8); split; [right; right; left; reflexivity| cbn [fst snd]; lia]| exact I]. }
  clear STRM ISTC ST STG FRA FRB FH FFL FSH OBB PFA E3 E4 E5 E6 E7 E8 E10 DLC SLC SHD SHS UC.
  set (LB' := if withwin then lb_remove ps (lb_remove pw LB) else lb_remove ps LB).
  assert (ELB : LB' = FB2 Fu :: LB0).
  { pose proof (AI_hb_ids AI _ _ _ _ _ AH) as NDI. subst LB'. destruct withwin.
    - subst LB. unfold LBn in *. unfold hb_ids in NDI. cbn [flat_map ab_kind app] in NDI. fold (hb_ids LB0) in NDI.
      apply NoDup_cons_iff in NDI. destruct NDI as [NI1 NDI]. apply NoDup_cons_iff in NDI. destruct NDI as [NI2 _].
      rewrite lb_remove_hd; [rewrite lb_remove_hd; [reflexivity|]|]; unfold hb_ids; cbn [flat_map ab_kind app]; fold (hb_ids LB0); assumption.
    - destruct SHW as [-> _]. unfold LBn in *. unfold hb_ids in NDI. cbn [flat_map ab_kind app] in NDI. fold (hb_ids LB0) in NDI.
      apply NoDup_cons_iff in NDI. destruct NDI as [NI2 _].
      rewrite lb_remove_hd; [reflexivity|]. unfold hb_ids; cbn [flat_map ab_kind app]; fold (hb_ids LB0); assumption. }
  pose proof IO1 as (SHM1 & SSH1 & _).
  eapply implMA_post_evtF.
  { eapply (END withwin) with (Fu := Fu) (S := S) (Wd := Wd) (pw := pw) (ps := ps) (mode := t_mode st) (lo := lo) (LB := LB);
      [exact AH1| exact SHM1| exact SSH1| exact SIN
      | destruct withwin; [subst LB; left; reflexivity| destruct SHW as [_ X]; exact X]
      | exact STRM1| exact ISTC1| exact MR| rewrite USPA; exact ST1| exact LOC| rewrite USPA; unfold END_STACK; lia
      | rewrite USPA; Z.div_mod_to_equations; lia| exact MI1| exact TPE| reflexivity| rewrite USPA; lia
      | destruct withwin; [exact UF1| exact I]| exact UF2| exact RSTK| eapply rng_fp_le; [exact FP| exact RIMG0]| exact OK]. }
  fold LB'. rewrite ELB.
  intros u s' RNG' ms' PE. unfold end_post in PE. rewrite USPA in PE.
  destruct PE as (FPL & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m2 & -> & MI2 & ST2 & RS' & CA & AH2 & STRM2).
  assert (FIN2 : In (FB2 Fu) (FB2 Fu :: LB0)) by (left; reflexivity).
  unfold client_agree in CA.
  assert (K2 : forall A N, (forall a, A <= a < A + N -> SPA <= a < 2^47 \/ Fu <= a < Fu + 32 \/ Fu + 144 <= a < Fu + 256 \/ SHF <= a < SHF + 32) ->
               forall a, A <= a < A + N -> aclient_addr CI (FB2 Fu :: LB0) SPA a /\ ~ in_ranges [(Zs, Zs + 112)] a).
  { intros A N HK a Ha. apply (uc_keep2_client a FIN2). apply HK. exact Ha. }
  assert (FRA2 : rw_cells asegs m2 SPA (UFRA sp Fu j8 j16)).
  { eapply rw_cells_magree; [exact CA| exact FRA1|]. apply K2. unfold UFRA; cbn [cells_size csize Nat.add]. intros a Ha. left. lia. }
  assert (FRB2 : rw_cells asegs m2 (SP + -104) (UFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { eapply rw_cells_magree; [exact CA| exact FRB1|]. apply K2. unfold UFRB; cbn [cells_size csize Nat.add]. intros a Ha. left. lia. }
  assert (STG2 : stk asegs m2 (SPA + 56) (SP + -104)).
  { eapply stk_magree; [exact CA| exact STG1|]. intros a Ha. apply (uc_keep2_client a FIN2). left. lia. }
  assert (FH2 : rw_cells asegs m2 Fu UFHD).
  { eapply rw_cells_magree; [exact CA| exact FH1|]. apply K2. unfold UFHD; cbn [cells_size csize Nat.add]. intros a Ha. right. left. lia. }
  assert (FFL2 : rw_cells asegs m2 (Fu + 248) [C8 (Z_to_bv 64 FLG)]).
  { eapply rw_cells_magree; [exact CA| exact FFL1|]. apply K2. cbn [cells_size csize Nat.add]. intros a Ha. right. right. left. lia. }
  assert (FSH2 : rw_cells asegs m2 SHF UFSH).
  { eapply rw_cells_magree; [exact CA| exact FSH1|]. apply K2. unfold UFSH; cbn [cells_size csize Nat.add]. intros a Ha. right. right. right. lia. }
  assert (OBB2 : rw_cells asegs m2 OB [CB (Z.to_nat 262144) obr]).
  { eapply rw_cells_magree; [exact CA| exact OBB1|]. cbn [cells_size csize Nat.add]. intros a Ha. split.
    - right. left. destruct OBC as (iv & Hiv & I1 & I2). exists iv. split; [exact Hiv| lia].
    - intros (iv & Hiv & Hr). cbn [In] in Hiv. destruct Hiv as [<-|[]]. cbn [fst snd] in Hr. unfold A_OUTBUF in *. lia. }
  assert (SLC2 : rw_cells asegs m2 SL [C8 slv]).
  { eapply rw_cells_magree; [exact CA| exact SLC1|]. apply K2. cbn [cells_size csize Nat.add]. intros a Ha. left. lia. }
  assert (DLC2 : rw_cells asegs m2 DL [C8 dlv]).
  { eapply rw_cells_magree; [exact CA| exact DLC1|]. apply K2. cbn [cells_size csize Nat.add]. intros a Ha. left. lia. }
  assert (PFA2 : magree asegs UPF m0 m2).
  { eapply magree_trans; [exact PFA1|]. eapply magree_mono; [exact CA|]. intros a [HC _]. split.
    - eapply aclient_addr_weaken; [| | exact HC]; [intros b Hb; right; exact Hb| lia].
    - intros (iv & Hiv & Hr). cbn [In] in Hiv. destruct Hiv as [<-|[]]. cbn [fst snd] in Hr.
      apply (client_outside_blk AI L RNG' _ (FB2 Fu :: LB0) LB0 m2 (FB2 Fu) SP a AH2 FIN2 FNI ltac:(intros b Hb; right; exact Hb) FUB ltac:(lia) HC).
      cbn [ab_addr ab_size]. lia. }
  destruct (AI_fake_flag _ _ _ _ _ 2 Fu 256 AH2 FIN2) as (FLC2 & RG & GB & GTOP & GBL & GCI). rewrite <- EFLG in FLC2, RG, GB, GTOP, GBL, GCI.
  pose proof (ablk_lin _ _ GB) as (GB1 & GB2 & GB3 & GB4). unfold AIMG_HI in GB1.
  assert (GF : FLG + 1 <= Fu \/ Fu + 256 <= FLG).
  { pose proof (GBL (FB2 Fu) FIN2) as X. cbn [ab_addr ab_size] in X. exact X. }
  assert (FP' : fp_le RNG0 RNG') by (eapply fp_le_trans; [exact FP| exact FPL]).
  assert (RFU' : rng RNG' Fu 256) by (eapply rng_fp_le; [exact FP'| exact RFU0]).
  assert (RSFU' : rng RNG' SHF 32) by (eapply rng_fp_le; [exact FP'| exact RSFU0]).
  assert (RSTK' : rng RNG' lo (SP - lo)) by (eapply rng_sub'; [eapply rng_fp_le; [exact FP'| exact RSTK0]| lia]).
  assert (RFRM' : rng RNG' SPA 56) by (eapply rng_sub'; [exact RSTK'| lia]).
  assert (SPT : SP + 16 < KEND) by (unfold KEND; lia).
  replace (ret_pc (Z_to_bv 64 577980)) with (Z_to_bv 64 577980) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  eapply evtF_cut.
  { eapply (uc_sel ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc F1 Fu FLG lo SPA RNG' SL ESL LOS LOC SP16 SPT ESPA RSTK' RFRM' FU256 FUB RFU' RSFU' GB GF RG). }
  cbv beta. intros ms3 (av & z11 & ->).
  eapply evtF_mono.
  { eapply (uc_epi ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc F1 Fu FLG lo SPA RNG' SL ESL LOS LOC SP16 SPT ESPA RSTK' RFRM' FU256 FUB RFU' RSFU' GB GF RG);
      [exact ST2| exact STG2| exact MI2| exact FRA2| exact FRB2| exact FH2| exact FFL2| exact FLC2| exact FSH2]. }
  cbv beta. intros ms4 (mp & m4 & q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & -> & MUp & WMp & MIp & MU4 & WM4 & MI4 & ST4 & FLC4).
  assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (AHp : AHEAP AI L RNG' (aps_m s') (FB2 Fu :: LB0) mp).
  { eapply (AI_frame AI _ _ _ _ m2 mp _ AH2 MUp WMp).
    constructor; [cbn [fst snd]; apply (acr_fake_sh AI _ 2 Fu 256 Fu 32); [exact FIN2| exact F8| lia| lia| lia]|].
    constructor; [cbn [fst snd]; eapply (acr_fake AI _ 2 Fu 256); [exact FIN2| lia| lia]| constructor]. }
  assert (EQ4 : m4 = write_to_mem mp (wa FLG) [Z_to_bv 8 0]).
  { apply uc_mem_eq_single; [lia| lia| exact MU4|]. apply uc_byte_of_c1; [exact FLC4| lia]. }
  assert (AH4 : AHEAP AI L RNG' (aps_m s') LB0 m4).
  { rewrite EQ4, EFLG. apply (AI_fake_release L RNG' (aps_m s') LB0 mp 2 Fu 256 AHp). }
  assert (PFA4 : magree asegs UPF m0 m4).
  { eapply magree_trans; [exact PFA2|]. eapply magree_trans.
    - eapply magree_mono; [exact (magree_of_munch asegs _ m2 mp MUp WMp)|]. intros a [HC _]. cbn [outside].
      split; [apply (client_outside_fsh AI L RNG' _ (FB2 Fu :: LB0) LB0 m2 2 Fu 256 SP a AH2 FIN2 FNI ltac:(intros b Hb; right; exact Hb) LBH FUB F8
                       ltac:(reflexivity) ltac:(lia) ltac:(lia) HC)|].
      split; [| exact I].
      pose proof (client_outside_blk AI L RNG' _ (FB2 Fu :: LB0) LB0 m2 (FB2 Fu) SP a AH2 FIN2 FNI ltac:(intros b Hb; right; exact Hb) FUB ltac:(lia) HC) as X.
      cbn [ab_addr ab_size] in X. lia.
    - eapply magree_mono; [exact (magree_of_munch asegs _ mp m4 MU4 WM4)|]. intros a [HC _]. cbn [outside]. split; [| exact I].
      pose proof (client_outside_flag AI L RNG' _ (FB2 Fu :: LB0) LB0 m2 FLG SP a AH2 ltac:(intros b Hb; right; exact Hb) GB GBL GCI ltac:(lia) HC) as X. lia. }
  assert (OBB4 : rw_cells asegs m4 OB [CB (Z.to_nat 262144) obr]).
  { eapply rw_cells_transport; [eapply rw_cells_transport; [exact OBB2| exact MUp| exact WMp|]| exact MU4| exact WM4|];
      unfold A_OUTBUF, KLS in *; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia. }
  assert (SLC4 : rw_cells asegs m4 SL [C8 slv]).
  { eapply rw_cells_transport; [eapply rw_cells_transport; [exact SLC2| exact MUp| exact WMp|]| exact MU4| exact WM4|];
      unfold KLS in *; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia. }
  assert (DLC4 : rw_cells asegs m4 DL [C8 dlv]).
  { eapply rw_cells_transport; [eapply rw_cells_transport; [exact DLC2| exact MUp| exact WMp|]| exact MU4| exact WM4|];
      unfold KLS in *; cbn [disjoint_from cells_size csize Nat.add]; repeat split; try exact I; lia. }
  unfold uc_final. split; [exact FP'|].
  exists av, q5, q6, q7, q11, q12, q13, q14, q15, q16, q17, q28, q29, q30, q31, m4.
  split; [reflexivity|]. split; [exact MI4|]. split; [exact ST4|]. split; [rewrite RS'; exact RS|]. split; [exact AH4|]. split; [exact PFA4|].
  split; [exists obr; exact OBB4|]. split; [exists slv; exact SLC4| exists dlv; exact DLC4].
Qed.
End Tail.
End CANSEC1.
