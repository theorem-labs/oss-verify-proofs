(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW Require Import AImg RtCells AProto ABase ABytes AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2cA_glue.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.U3A Require Import U2AObj U2AClient U2AIface U2AGlue U2AIfaceS InfABase InfAIface U2cA_pre.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Section AI.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation FB2 F := (mkABlock (ABFake 2) F 256).

Lemma client_outside_blk : forall L RNG st LB LB0 m b SP a,
  AHEAP AI L RNG st LB m -> In b LB -> ~ In b LB0 -> (forall b', In b' LB0 -> In b' LB) ->
  ablk (ab_addr b) (ab_addr b + ab_size b) -> ATOP <= SP ->
  aclient_addr CI LB0 SP a -> ~ (ab_addr b <= a < ab_addr b + ab_size b).
Proof.
  intros L RNG st LB LB0 m b SP a AH HB NB SUB BK LOSP Ha.
  pose proof (ablk_lin _ _ BK) as (K1 & K2 & K3 & K4). unfold AIMG_HI in K1.
  assert (BB : forall b', In b' LB0 -> AIMG_HI <= ab_addr b' /\ 0 <= ab_size b' /\ ab_addr b' + ab_size b' <= ATOP).
  { intros b' Hb'. apply (AI_block_bounds AI _ _ _ _ _ b' AH). apply SUB. exact Hb'. }
  atop_facts.
  destruct Ha as [HSP|[(iv & Hiv & Hr)|[(b' & Hb' & Hr)|(a' & Ha' & ->)]]].
  - lia.
  - pose proof (AI_aci_img AI iv Hiv) as X. unfold AIMG_HI in *. lia.
  - assert (NE : b <> b') by (intros ->; exact (NB Hb')).
    pose proof (AI_blocks_disjoint AI _ _ _ _ _ b b' AH HB (SUB _ Hb') NE) as D. lia.
  - assert (A47 : 0 <= a' < 2^47).
    { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA & fn & Hb' & Hr)]];
        [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia
        | pose proof (BB _ Hb') as BX; cbn [ab_addr ab_size] in BX; unfold AIMG_HI in *; lia]. }
    pose proof (shad_in_band a' A47) as SB. apply (ablk_clear_band _ _ (shad a') BK). lia.
Qed.

Lemma client_outside_fsh : forall L RNG st LB LB0 m c F N SP a,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake c) F N) LB -> ~ In (mkABlock (ABFake c) F N) LB0 -> (forall b', In b' LB0 -> In b' LB) ->
  (forall b', In b' LB0 -> ablk (ab_addr b') (ab_addr b' + ab_size b')) ->
  ablk F (F + N) -> F mod 8 = 0 -> N mod 8 = 0 -> 0 <= N -> ATOP <= SP ->
  aclient_addr CI LB0 SP a -> ~ (Z.shiftr F 3 + 2147450880 <= a < Z.shiftr F 3 + 2147450880 + N / 8).
Proof.
  intros L RNG st LB LB0 m c F N SP a AH HB NB SUB LBH BK F8 N8 N0 LOSP Ha.
  pose proof (ablk_lin _ _ BK) as (K1 & K2 & K3 & K4). unfold AIMG_HI in K1.
  assert (BB : forall b', In b' LB0 -> AIMG_HI <= ab_addr b' /\ 0 <= ab_size b' /\ ab_addr b' + ab_size b' <= ATOP).
  { intros b' Hb'. apply (AI_block_bounds AI _ _ _ _ _ b' AH). apply SUB. exact Hb'. }
  atop_facts.
  assert (SHB : KLS <= Z.shiftr F 3 + 2147450880 /\ Z.shiftr F 3 + 2147450880 + N / 8 <= 0x10007fff8000).
  { rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold KLS. Z.div_mod_to_equations. lia. }
  destruct Ha as [HSP|[(iv & Hiv & Hr)|[(b' & Hb' & Hr)|(a' & Ha' & ->)]]].
  - lia.
  - pose proof (AI_aci_img AI iv Hiv) as X. unfold AIMG_HI, KLS in *. lia.
  - intros X. eapply (ablk_clear_band _ _ a (LBH _ Hb')); [unfold KLS in *; lia| exact Hr].
  - assert (A47 : 0 <= a' < 2^47).
    { destruct Ha' as [X|[(iv & Hiv & Hr)|(c' & FA & fn & Hb' & Hr)]];
        [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia
        | pose proof (BB _ Hb') as BX; cbn [ab_addr ab_size] in BX; unfold AIMG_HI in *; lia]. }
    assert (OUTF : ~ (F <= a' < F + N)).
    { destruct Ha' as [X|[(iv & Hiv & Hr)|(c' & FA & fn & Hb' & Hr)]];
        [lia| pose proof (AI_aci_img AI iv Hiv); unfold AIMG_HI in *; lia|].
      assert (NE : mkABlock (ABFake c) F N <> mkABlock (ABFake c') FA fn) by (intros E; apply NB; rewrite E; exact Hb').
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ _ _ AH HB (SUB _ Hb') NE) as D. cbn [ab_addr ab_size] in D. lia. }
    rewrite shad_div in *. unfold ASHOFF in *. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    clear - A47 OUTF F8 N8 N0 K1 K2. Z.div_mod_to_equations. lia.
Qed.

Lemma client_outside_flag : forall L RNG st LB LB0 m FLG SP a,
  AHEAP AI L RNG st LB m -> (forall b', In b' LB0 -> In b' LB) ->
  ablk FLG (FLG + 1) -> (forall b, In b LB -> FLG + 1 <= ab_addr b \/ ab_addr b + ab_size b <= FLG) -> ~ in_ranges CI FLG ->
  ATOP <= SP ->
  aclient_addr CI LB0 SP a -> a <> FLG.
Proof.
  intros L RNG st LB LB0 m FLG SP a AH SUB GB GBL GCI LOSP Ha.
  pose proof (ablk_lin _ _ GB) as (K1 & K2 & K3 & K4). unfold AIMG_HI in K1.
  assert (BB : forall b', In b' LB0 -> AIMG_HI <= ab_addr b' /\ 0 <= ab_size b' /\ ab_addr b' + ab_size b' <= ATOP).
  { intros b' Hb'. apply (AI_block_bounds AI _ _ _ _ _ b' AH). apply SUB. exact Hb'. }
  atop_facts.
  destruct Ha as [HSP|[(iv & Hiv & Hr)|[(b' & Hb' & Hr)|(a' & Ha' & ->)]]].
  - lia.
  - intros ->. apply GCI. exists iv. split; [exact Hiv| exact Hr].
  - pose proof (GBL b' (SUB _ Hb')). lia.
  - assert (A47 : 0 <= a' < 2^47).
    { destruct Ha' as [X|[(iv & Hiv & Hr)|(c' & FA & fn & Hb' & Hr)]];
        [lia| pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia
        | pose proof (BB _ Hb') as BX; cbn [ab_addr ab_size] in BX; unfold AIMG_HI in *; lia]. }
    pose proof (shad_in_band a' A47) as SB. intros X. apply (ablk_clear_band _ _ (shad a') GB); lia.
Qed.

Lemma aclient_addr_weaken : forall LB LB0 SP SP0 a,
  (forall b, In b LB0 -> In b LB) -> SP <= SP0 -> aclient_addr CI LB0 SP0 a -> aclient_addr CI LB SP a.
Proof.
  intros LB LB0 SP SP0 a SUB LE [H|[H|[(b & Hb & Hr)|(a' & [H|[H|(c & FA & fn & Hb & Hr)]] & ->)]]].
  - left. lia.
  - right. left. exact H.
  - right. right. left. exists b. split; [apply SUB; exact Hb| exact Hr].
  - right. right. right. exists a'. split; [left; exact H| reflexivity].
  - right. right. right. exists a'. split; [right; left; exact H| reflexivity].
  - right. right. right. exists a'. split; [right; right; exists c, FA, fn; split; [apply SUB; exact Hb| exact Hr]| reflexivity].
Qed.

Lemma u2_img_of_aheap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> u2_img m.
Proof.
  intros L RNG st LB m AH. pose proof (AI_relro AI L RNG st LB m AH) as R. unfold u2_img, AGOT_SUAR, AGOT_ZCALLOC, ASUAR, A_ZCALLOC, A_ZCFREE.
  split.
  - eapply rw_cells_recast; [apply (rw_cells_image0 asegs m 0xd01e8 (le8 (Z_to_bv 64 887168)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply R; rewrite length_le8 in Ha; unfold ARELRO_LO, ARELRO_HI; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ]
      | cbn; split; exact I | reflexivity | reflexivity].
  - (* 1.4: the second conjunct is True (no GOT words for zcalloc / zcfree, U2AIface) *) exact I.
Qed.

Lemma shadow_bytes_magree : forall P m m' s1 s2 f,
  magree asegs P m m' -> shadow_bytes m s1 s2 f -> (forall a, s1 <= a < s2 -> P a) -> shadow_bytes m' s1 s2 f.
Proof.
  intros P m m' s1 s2 f HP SB HR. pose proof SB as (A & B & _). eapply shadow_bytes_agree; [exact SB|].
  intros s Hs. destruct (HP s ltac:(lia) (HR s Hs)) as [E _]. exact E.
Qed.

(* a chain whose frame is not above prev stops at once, in every memory. *)
Lemma uchain_low : forall m m' top pc prev frame k tr,
  uchain m top pc prev frame k tr -> frame <= prev -> uchain m' top pc prev frame k tr.
Proof.
  intros m m' top pc prev frame k tr H LE. inversion H; subst; [apply uc_stop; assumption| lia| lia].
Qed.

Section Keep.
Variables (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
Variables (L : alayout) (SPA Fu F1 FLG : Z).
Notation SP := (bv_unsigned sp).
Variable SL : Z.
Hypothesis ESL : SL = SP + 8.
Notation DL := (SP + 16).   (* 1.4: &got in the 48-byte uncompress frame *)
Notation Zs := (Fu + 32).
Notation SHF := (Z.shiftr Fu 3 + 2147450880).

Definition uc_keep (a : Z) : Prop :=
     SPA <= a < 2^47
  \/ Fu <= a < Fu + 32 \/ Fu + 144 <= a < Fu + 256
  \/ SHF <= a < SHF + 32
  \/ DL <= a < DL + 8 \/ SL <= a < SL + 8
  \/ a = Z.shiftr DL 3 + 2147450880 \/ a = Z.shiftr SL 3 + 2147450880.

Definition uc_frame (j8 j16 : list byte) (n0 dl : Z) (trc : list Z) (m : amem) : Prop :=
     rw_cells asegs m SPA (UFRA sp Fu j8 j16)
  /\ rw_cells asegs m (SP + -104) (UFRB ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ stk asegs m (SPA + 56) (SP + -104)
  /\ rw_cells asegs m Fu UFHD /\ rw_cells asegs m (Fu + 248) [C8 (Z_to_bv 64 FLG)]
  /\ rw_cells asegs m SHF UFSH
  /\ rw_cells asegs m DL [C8 (Z_to_bv 64 dl)] /\ rw_cells asegs m SL [C8 (Z_to_bv 64 n0)]
  /\ shadow_bytes m (Z.shiftr DL 3 + 2147450880) (Z.shiftr DL 3 + 2147450880 + 1) (fun _ => 0)
  /\ shadow_bytes m (Z.shiftr SL 3 + 2147450880) (Z.shiftr SL 3 + 2147450880 + 1) (fun _ => 0)
  /\ (forall k, (2 <= k)%nat -> uchain m (al_top L) AMALLOC_PC SP (bv_unsigned s0) k trc).

Hypothesis SPAB : SP - 176 <= SPA <= SP - 160.
Hypothesis SPT : SP <= 2^47.
Hypothesis TOP : al_top L <= 2^47.
Hypothesis S0SP : bv_unsigned s0 <= SP.   (* 1.4: uncompress hands its s0 = destLen (a fake-frame address) through *)

Lemma uc_frame_agree : forall j8 j16 n0 dl trc m m',
  magree asegs uc_keep m m' -> uc_frame j8 j16 n0 dl trc m -> uc_frame j8 j16 n0 dl trc m'.
Proof using SPAB SPT TOP S0SP.
  intros j8 j16 n0 dl trc m m' AG (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11). unfold uc_frame.
  split; [eapply rw_cells_magree; [exact AG| exact A1|]; unfold UFRA; cbn [cells_size csize Nat.add]; intros a Ha; left; lia|].
  split; [eapply rw_cells_magree; [exact AG| exact A2|]; unfold UFRB; cbn [cells_size csize Nat.add]; intros a Ha; left; lia|].
  split; [eapply stk_magree; [exact AG| exact A3|]; intros a Ha; left; lia|].
  split; [eapply rw_cells_magree; [exact AG| exact A4|]; unfold UFHD; cbn [cells_size csize Nat.add]; intros a Ha; right; left; lia|].
  split; [eapply rw_cells_magree; [exact AG| exact A5|]; cbn [cells_size csize Nat.add]; intros a Ha; right; right; left; lia|].
  split; [eapply rw_cells_magree; [exact AG| exact A6|]; unfold UFSH; cbn [cells_size csize Nat.add]; intros a Ha; right; right; right; left; lia|].
  split; [eapply rw_cells_magree; [exact AG| exact A7|]; cbn [cells_size csize Nat.add]; intros a Ha; do 4 right; left; lia|].
  split; [eapply rw_cells_magree; [exact AG| exact A8|]; cbn [cells_size csize Nat.add]; intros a Ha; do 5 right; left; lia|].
  split; [eapply shadow_bytes_magree; [exact AG| exact A9|]; intros a Ha; do 6 right; left; lia|].
  split; [eapply shadow_bytes_magree; [exact AG| exact A10|]; intros a Ha; do 7 right; lia|].
  intros k Hk. eapply uchain_low; [exact (A11 k Hk)| exact S0SP].
Qed.
End Keep.

Section Inv.
Variables (ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
Variables (L : alayout) (SPA Fu F1 FLG lo : Z).
Variables (S D n dl : Z) (payload : list Z) (ps : AsanCtrl.aptr) (LB0 : list ablock).
Variables (j8 j16 : list byte) (n0 : Z) (trc : list Z) (m0 : amem) (RNG0 : footprint) (sR : APS).
Notation SP := (bv_unsigned sp).
Variable SL : Z.
Hypothesis ESL : SL = SP + 8.
Notation DL := (SP + 16).   (* 1.4: &got in the 48-byte uncompress frame *)
Notation Zs := (Fu + 32).
Notation SHF := (Z.shiftr Fu 3 + 2147450880).
Notation OB := A_OUTBUF.

Definition LBn : list ablock := HB ps S 7176 :: FB2 Fu :: LB0.
Definition ucx (Wd : Z) (st : ist) : ictx :=
  icx_of S D n OB dl Wd (t_cin st) (t_cout st) (8 * (n - t_cin st) + t_bits st + (dl - t_cout st)).
Definition umu (st : ist) : Z := (8 * (n - t_cin st) + t_bits st + (dl - t_cout st)) * 134217728 + (n - t_cin st).

Definition uc_WRf : list (Z * Z) := [(OB, OB + 262144); (DL, DL + 8); (SL, SL + 8); (0, 32768)].
Definition uc_PF (a : Z) : Prop := aclient_addr CI LB0 SP a /\ ~ in_ranges uc_WRf a.

Record uvw := UVW { v_lf : Z -> Z; v_cf : Z -> Z; v_wf : Z -> Z; v_fo : Z -> Z;
  v_zti : word; v_zto : word; v_zmsg : word; v_zopq : word; v_zdt : word; v_zadl : word; v_zres : word; v_zp1 : word; v_zp2 : word; v_zp3 : word;
  v_havedict : word; v_dmax : word; v_check : word; v_total : word; v_back : word; v_was : word; v_pad : word }.

Definition uc_emem (Wd : Z) (st : ist) (v : uvw) (m : amem) : Prop :=
  inf_emem (ucx Wd st) Zs st (v_lf v) (v_cf v) (v_wf v) (v_fo v) payload (v_zti v) (v_zto v) (v_zmsg v) (v_zopq v) (v_zdt v) (v_zadl v) (v_zres v)
           (v_zp1 v) (v_zp2 v) (v_zp3 v) (v_havedict v) (v_dmax v) (v_check v) (v_total v) (v_back v) (v_was v) (v_pad v) m.

Definition uc_shape (Wd : Z) (LB : list ablock) : Prop :=
  (Wd = 0 /\ LB = LBn) \/ (exists pw, LB = HB pw Wd 32768 :: LBn /\ Wd mod 16 = 0 /\ ablk Wd (Wd + 32768)).

Definition uc_inv (Wd : Z) (RNG : footprint) (s : APS) (LB : list ablock) (st : ist) (v : uvw) (m : amem) : Prop :=
     AHEAP AI L RNG (aps_m s) LB m
  /\ inf_objs AI RNG LB (ucx Wd st) Fu Zs payload m
  /\ ainv (ucx Wd st) st (v_lf v) (v_cf v) /\ t_mode st <> MEM
  /\ uc_emem Wd st v m
  /\ stk asegs m lo SPA /\ mem_inv asegs m
  /\ uc_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu FLG SL j8 j16 n0 dl trc m
  /\ magree asegs uc_PF m0 m
  /\ aps_ok L s /\ aps_rest s = aps_rest sR /\ fp_le RNG0 RNG
  /\ uc_shape Wd LB.

Hypothesis LOC : ATOP + 4096 <= lo.
Hypothesis LOSPA : lo <= SPA.
Hypothesis SPAB : SP - 176 <= SPA <= SP - 160.
Hypothesis SPT : SP + 48 <= 2^47.
Hypothesis FU256 : Fu mod 256 = 0.
Hypothesis FUB : ablk Fu (Fu + 256).
Hypothesis F1128 : F1 mod 128 = 0.
Hypothesis F1B : ablk F1 (F1 + 128).
Hypothesis F1IN : In (FB1 F1) LB0.
Hypothesis LBH : forall b, In b LB0 -> ablk (ab_addr b) (ab_addr b + ab_size b).
Hypothesis SBK : ablk S (S + 7176).
Hypothesis OBC : exists iv, In iv CI /\ fst iv <= OB /\ OB + 262144 <= snd iv.
Hypothesis DLR : 0 <= dl <= 262144.

Lemma uc_shape_facts : forall Wd RNG st LB m,
  AHEAP AI L RNG st LB m -> uc_shape Wd LB ->
     (forall b, In b LB0 -> In b LB)
  /\ In (FB2 Fu) LB /\ ~ In (FB2 Fu) LB0 /\ In (HB ps S 7176) LB /\ ~ In (HB ps S 7176) LB0
  /\ (Wd = 0 \/ exists pw, In (HB pw Wd 32768) LB /\ ~ In (HB pw Wd 32768) LB0 /\ ablk Wd (Wd + 32768)
                           /\ HB pw Wd 32768 <> FB2 Fu /\ HB pw Wd 32768 <> FB1 F1).
Proof.
  intros Wd RNG st LB m AH SH. pose proof (AI_blocks_nodup AI _ _ _ _ _ AH) as ND.
  destruct SH as [(-> & ->)|(pw & -> & W16 & WB)]; unfold LBn in *.
  - inversion ND as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst.
    split; [intros b Hb; right; right; exact Hb|].
    split; [right; left; reflexivity|]. split; [exact N2|]. split; [left; reflexivity|].
    split; [intros X; apply N1; right; exact X|]. left. reflexivity.
  - inversion ND as [|x0 l0 N0 ND0]; subst. inversion ND0 as [|x1 l1 N1 ND1]; subst. inversion ND1 as [|x2 l2 N2 ND2]; subst.
    split; [intros b Hb; right; right; right; exact Hb|].
    split; [right; right; left; reflexivity|]. split; [exact N2|]. split; [right; left; reflexivity|].
    split; [intros X; apply N1; right; exact X|]. right. exists pw.
    split; [left; reflexivity|]. split; [intros X; apply N0; right; right; exact X|]. split; [exact WB|].
    split; discriminate.
Qed.

Lemma uc_pf_step : forall Wd RNG st LB m a,
  AHEAP AI L RNG st LB m -> uc_shape Wd LB -> uc_PF a ->
  aclient_addr CI LB SPA a /\ ~ in_ranges [(Zs, Zs + 112); (S, S + 7176); (OB, OB + dl); (Wd, Wd + 32768); (0, 32768)] a.
Proof.
  intros Wd RNG st LB m a AH SH [HC HN].
  destruct (uc_shape_facts Wd RNG st LB m AH SH) as (SUB & FIN & FNI & SIN & SNI & WIN).
  assert (TSP : ATOP <= SP) by lia.
  split; [eapply aclient_addr_weaken; [exact SUB| | exact HC]; lia|].
  intros (iv & Hiv & Hr). cbn [In] in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr.
  5: { apply HN. exists (0, 32768). split; [right; right; right; left; reflexivity| exact Hr]. }
  - apply (client_outside_blk L RNG st LB LB0 m (FB2 Fu) SP a AH FIN FNI SUB FUB TSP HC). cbn [ab_addr ab_size]. lia.
  - apply (client_outside_blk L RNG st LB LB0 m (HB ps S 7176) SP a AH SIN SNI SUB SBK TSP HC). cbn [ab_addr ab_size]. lia.
  - apply HN. exists (OB, OB + 262144). split; [left; reflexivity| cbn [fst snd]; lia].
  - destruct WIN as [->|(pw & WI & WNI & WB & _)].
    + apply HN. exists (0, 32768). split; [right; right; right; left; reflexivity| exact Hr].
    + apply (client_outside_blk L RNG st LB LB0 m (HB pw Wd 32768) SP a AH WI WNI SUB WB TSP HC). cbn [ab_addr ab_size]. lia.
Qed.

Lemma uc_keep_step : forall Wd RNG st LB m a,
  AHEAP AI L RNG st LB m -> uc_shape Wd LB -> uc_keep sp SPA Fu SL a ->
  aclient_addr CI LB SPA a /\ ~ in_ranges [(Zs, Zs + 112); (S, S + 7176); (OB, OB + dl); (Wd, Wd + 32768); (0, 32768)] a.
Proof.
  intros Wd RNG st LB m a AH SH KP.
  destruct (uc_shape_facts Wd RNG st LB m AH SH) as (SUB & FIN & FNI & SIN & SNI & WIN).
  pose proof (ablk_lin _ _ FUB) as (FL1 & FL2 & FL3 & FL4). pose proof (ablk_lin _ _ F1B) as (GL1 & GL2 & GL3 & GL4).
  pose proof (ablk_lin _ _ SBK) as (SL1 & SL2 & SL3 & SL4). unfold AIMG_HI in *.
  assert (F1IN' : In (FB1 F1) LB) by (apply SUB; exact F1IN).
  assert (F8 : Fu mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (G8 : F1 mod 8 = 0) by (Z.div_mod_to_equations; lia).
  atop_facts.
  assert (LOCa : (SPA <= a < 2^47) \/ ((Fu <= a < Fu + 32 \/ Fu + 144 <= a < Fu + 256) \/ (F1 <= a < F1 + 128)
                  \/ (KLS <= a < 0x10007fff8000))).
  { unfold uc_keep in KP. destruct KP as [K|[K|[K|[K|[K|[K|[K|K]]]]]]]; [left; lia| right; left; lia| right; left; lia| | left; lia| left; lia | |].
    - right. right. right. unfold KLS. revert K. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. intros K. Z.div_mod_to_equations. lia.
    - right. right. right. unfold KLS. subst a. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia.
    - right. right. right. unfold KLS. subst a. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. lia. }
  split.
  - unfold uc_keep in KP. destruct KP as [K|[K|[K|[K|[K|[K|[K|K]]]]]]].
    + left. lia.
    + right. right. left. exists (FB2 Fu). split; [exact FIN| cbn [ab_addr ab_size]; lia].
    + right. right. left. exists (FB2 Fu). split; [exact FIN| cbn [ab_addr ab_size]; lia].
    + right. right. right. exists (8 * (a - ASHOFF)). split; [| symmetry; apply shad_unshad].
      right. right. exists 2, Fu, 256. split; [exact FIN|]. unfold ASHOFF. revert K. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
      intros K. Z.div_mod_to_equations. lia.
    + left. lia.
    + left. lia.
    + right. right. right. exists DL. split; [| rewrite shadE; exact K]. left. lia.
    + right. right. right. exists SL. split; [| rewrite shadE; exact K]. left. lia.
  - assert (SEPSF : S + 7176 <= Fu \/ Fu + 256 <= S).
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB ps S 7176) (FB2 Fu) AH SIN FIN ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia. }
    assert (SEPSG : S + 7176 <= F1 \/ F1 + 128 <= S).
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB ps S 7176) (FB1 F1) AH SIN F1IN' ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia. }
    assert (SEPFG : Fu + 256 <= F1 \/ F1 + 128 <= Fu).
    { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (FB2 Fu) (FB1 F1) AH FIN F1IN' ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia. }
    intros (iv & Hiv & Hr). cbn [In] in Hiv. destruct Hiv as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr.
    5: { unfold KLS in *. destruct LOCa as [K|[K|[K|K]]]; lia. }
    + destruct LOCa as [K|[K|[K|K]]]; [lia| lia| lia|]. apply (ablk_clear_band _ _ a FUB K). lia.
    + destruct LOCa as [K|[K|[K|K]]]; [lia| lia| lia|]. apply (ablk_clear_band _ _ a SBK K). lia.
    + unfold A_OUTBUF, KLS in *. destruct LOCa as [K|[K|[K|K]]]; lia.
    + destruct WIN as [->|(pw & WI & WNI & WB & NE1 & NE2)].
      * unfold KLS in *. destruct LOCa as [K|[K|[K|K]]]; lia.
      * pose proof (ablk_lin _ _ WB) as (WL1 & WL2 & WL3 & WL4).
        assert (SEPWF : Wd + 32768 <= Fu \/ Fu + 256 <= Wd).
        { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pw Wd 32768) (FB2 Fu) AH WI FIN NE1) as X. cbn [ab_addr ab_size] in X. lia. }
        assert (SEPWG : Wd + 32768 <= F1 \/ F1 + 128 <= Wd).
        { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pw Wd 32768) (FB1 F1) AH WI F1IN' NE2) as X. cbn [ab_addr ab_size] in X. lia. }
        destruct LOCa as [K|[K|[K|K]]]; [lia| lia| lia|]. apply (ablk_clear_band _ _ a WB K). lia.
Qed.

Lemma inf_objs_wclr : forall W RNG st LB cx m m',
  AHEAP AI L RNG st LB m ->
  inf_objs AI RNG LB cx Fu Zs payload m -> munch W m m' -> wmono asegs m m' -> Forall wclr W ->
  inf_objs AI RNG LB cx Fu Zs payload m'.
Proof.
  intros W RNG st LB cx m m' AH IO MU WM FW. unfold inf_objs in *.
  destruct IO as (SHM & (SS1 & SS2 & SS3 & SS4) & PB & WB & NL & EOB & OSZ & OBCL & SHOB & R1 & R2 & D1 & NR & D16 & PF & PL & UNP & R3 & R4 & TSH & REST).
  pose proof SHM as (FIN & EZ & F256 & FBK). pose proof (ablk_lin _ _ FBK) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
  assert (KZ : KLS <= Z.shiftr Zs 3 + 2147450880 /\ Z.shiftr Zs 3 + 2147450880 + 14 <= 0x10007fff8000).
  { rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold KLS. Z.div_mod_to_equations. lia. }
  split; [exact SHM|]. split.
  { split; [eapply shadow_bytes_munch_wclr; [exact SS1| exact MU| exact FW| lia| lia]|]. split; [exact SS2|].
    split; [eapply wr_at_transport; [exact SS3| exact WM]| exact SS4]. }
  split; [exact PB|]. split; [exact WB|]. split; [exact NL|]. split; [exact EOB|]. split; [exact OSZ|]. split; [exact OBCL|].
  split. { rewrite EOB in *. unfold A_OUTBUF in *. assert (E8 : Z.shiftr 6336512 3 = 792064) by reflexivity. rewrite E8 in *.
          eapply shadow_bytes_munch_wclr; [exact SHOB| exact MU| exact FW| unfold KLS; lia| lia]. }
  split; [exact R1|]. split; [exact R2|]. split; [exact D1|]. split; [exact NR|]. split; [exact D16|]. split; [exact PF|]. split; [exact PL|].
  split.
  { eapply unpoisoned_munch_wclr; [exact UNP| exact MU| exact FW|].
    destruct PB as (ps' & _ & [(pd & PDI & _)|(N0 & DE)]).
    - pose proof (AI_block_bounds AI _ _ _ _ _ _ AH PDI) as (_ & _ & X). cbn [ab_addr ab_size] in X. atop_facts. unfold KEND. lia.
    - unfold KEND. lia. }
  split; [exact R3|]. split; [exact R4|].
  split; [| exact REST]. unfold u2_tabsh in *. destruct TSH as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10).
  split; [eapply shadow_bytes_munch_wclr; [exact T1| exact MU| exact FW| unfold KLS; lia| lia]|].
  split; [eapply shadow_bytes_munch_wclr; [exact T2| exact MU| exact FW| unfold KLS; lia| lia]|].
  split; [eapply shadow_bytes_munch_wclr; [exact T3| exact MU| exact FW| unfold KLS; lia| lia]|].
  split; [eapply shadow_bytes_munch_wclr; [exact T4| exact MU| exact FW| unfold KLS; lia| lia]|].
  split; [eapply shadow_bytes_munch_wclr; [exact T5| exact MU| exact FW| unfold KLS; lia| lia]|].
  split; [eapply shadow_bytes_munch_wclr; [exact T6| exact MU| exact FW| unfold KLS; lia| lia]|].
  split; [eapply shadow_bytes_munch_wclr; [exact T7| exact MU| exact FW| unfold KLS; lia| lia]|].
  split; [eapply shadow_bytes_munch_wclr; [exact T8| exact MU| exact FW| unfold KLS; lia| lia]|].
  split; [eapply shadow_bytes_munch_wclr; [exact T9| exact MU| exact FW| unfold KLS; lia| lia]|].
  eapply shadow_bytes_munch_wclr; [exact T10| exact MU| exact FW| unfold KLS; lia| lia].
Qed.

Lemma uc_emem_strm : forall Wd RNG st' LB st v m m',
  AHEAP AI L RNG st' LB m -> uc_shape Wd LB ->
  inf_objs AI RNG LB (ucx Wd st) Fu Zs payload m ->
  uc_emem Wd st v m -> munch [(Zs, Zs + 112)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' Zs (strm_cells (Z_to_bv 64 (D + t_cin st)) (Z_to_bv 64 (n - t_cin st)) (v_zti v) (Z_to_bv 64 (OB + t_cout st))
                                   (Z_to_bv 64 (dl - t_cout st)) (v_zto v) (v_zmsg v) (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE)
                                   (v_zopq v) (v_zdt v) (v_zadl v) (v_zres v) (v_zp1 v) (v_zp2 v) (v_zp3 v)) ->
  uc_emem Wd st v m'.
Proof.
  intros Wd RNG st' LB st v m m' AH SH IO EM MU WM STRM.
  destruct (uc_shape_facts Wd RNG st' LB m AH SH) as (SUB & FIN & FNI & SIN & SNI & WIN).
  pose proof (ablk_lin _ _ FUB) as (FL1 & FL2 & FL3 & FL4). pose proof (ablk_lin _ _ SBK) as (SL1 & SL2 & SL3 & SL4). unfold AIMG_HI in *.
  assert (SEPSF : S + 7176 <= Fu \/ Fu + 256 <= S).
  { pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB ps S 7176) (FB2 Fu) AH SIN FIN ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia. }
  unfold inf_objs in IO. cbn [ucx icx_of c_p c_q c_n c_ob c_osz c_w] in IO.
  destruct IO as (_ & _ & (ps' & _ & PD) & _ & _ & _ & OSZR & _ & _ & _ & _ & D1 & NR & _ & _ & PL & _).
  assert (SEPD : D + n <= Fu \/ Fu + 256 <= D).
  { destruct PD as [(pd & PDI & _)|(N0 & DE)].
    - pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pd D n) (FB2 Fu) AH PDI FIN ltac:(discriminate)) as X. cbn [ab_addr ab_size] in X. lia.
    - left. lia. }
  unfold uc_emem, inf_emem in *. cbn [ucx icx_of c_p c_q c_n c_ob c_osz c_w] in *.
  destruct EM as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & (obr & E10) & E11).
  split; [exact STRM|].
  split; [eapply rw_cells_transport; [exact E2| exact MU| exact WM|]; rewrite istate_cells_size; cbn [disjoint_from]; split; [lia| exact I]|].
  split; [eapply f16arr_transport; [exact E3| exact MU| exact WM|]; cbn [disjoint_from]; split; [lia| exact I]|].
  split; [eapply f16arr_transport; [exact E4| exact MU| exact WM|]; cbn [disjoint_from]; split; [lia| exact I]|].
  split; [eapply f32arr_transport; [exact E5| exact MU| exact WM|]; cbn [disjoint_from]; split; [lia| exact I]|].
  split; [eapply rw_cells_transport; [exact E6| exact MU| exact WM|]; cbn [disjoint_from cells_size csize itail_cells Nat.add]; split; [lia| exact I]|].
  split; [eapply f8arr_transport; [exact E7| exact MU| exact WM|]; unfold A_OUTBUF; cbn [disjoint_from]; split; [lia| exact I]|].
  split; [eapply bytes_at_transport; [exact E8| exact MU|]; rewrite length_map; cbn [disjoint_from]; split; [lia| exact I]|].
  split; [exact E9|].
  split; [exists obr; eapply rw_cells_transport; [exact E10| exact MU| exact WM|]; unfold A_OUTBUF; cbn [disjoint_from cells_size csize Nat.add]; split; [lia| exact I]|].
  intros WNZ. destruct (E11 WNZ) as (fw & FWA). exists fw.
  destruct WIN as [W0|(pw & WI & _ & WB & NE1 & _)]; [exfalso; exact (WNZ W0)|].
  pose proof (AI_blocks_disjoint AI _ _ _ _ _ (HB pw Wd 32768) (FB2 Fu) AH WI FIN NE1) as X. cbn [ab_addr ab_size] in X.
  eapply f8arr_transport; [exact FWA| exact MU| exact WM|]. cbn [disjoint_from]. split; [lia| exact I].
Qed.

Hypothesis S0SP : bv_unsigned s0 <= SP.   (* 1.4: uncompress hands its s0 = destLen (a fake-frame address) through *)

Lemma not_in_ranges_hd : forall lo' hi' W a, ~ in_ranges ((lo', hi') :: W) a -> ~ (lo' <= a < hi').
Proof. intros lo' hi' W a H X. apply H. exists (lo', hi'). split; [left; reflexivity| exact X]. Qed.

Lemma uc_inv_strm : forall Wd RNG s LB st v m m',
  uc_inv Wd RNG s LB st v m -> munch [(Fu + 32, Fu + 144)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
  rw_cells asegs m' Zs (strm_cells (Z_to_bv 64 (D + t_cin st)) (Z_to_bv 64 (n - t_cin st)) (v_zti v) (Z_to_bv 64 (OB + t_cout st))
                                   (Z_to_bv 64 (dl - t_cout st)) (v_zto v) (v_zmsg v) (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE)
                                   (v_zopq v) (v_zdt v) (v_zadl v) (v_zres v) (v_zp1 v) (v_zp2 v) (v_zp3 v)) ->
  uc_inv Wd RNG s LB st v m'.
Proof.
  intros Wd RNG s LB st v m m' (AH & IO & AV & MD & EM & ST & MI & FR & PFA & OK & RS & FP & SH) MU WM MI' STRM.
  destruct (uc_shape_facts Wd RNG _ LB m AH SH) as (SUB & FIN & FNI & SIN & SNI & WIN).
  pose proof (ablk_lin _ _ FUB) as (FL1 & FL2 & FL3 & FL4). unfold AIMG_HI in FL1.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  assert (MU' : munch [(Zs, Zs + 112)] m m') by (replace (Zs + 112) with (Fu + 144) by lia; exact MU).
  pose proof (magree_of_munch asegs _ m m' MU WM) as AG.
  unfold uc_inv.
  split; [eapply (AI_frame AI _ _ _ _ m m' _ AH MU WM); constructor; [cbn [fst snd]; eapply (acr_fake AI _ 2 Fu 256); [exact FIN| lia| lia]| constructor]|].
  split; [eapply inf_objs_wclr; [exact AH| exact IO| exact MU| exact WM|]; constructor; [eapply wclr_ablk; [exact FUB| lia| lia]| constructor]|].
  split; [exact AV|]. split; [exact MD|].
  split; [eapply uc_emem_strm; [exact AH| exact SH| exact IO| exact EM| exact MU'| exact WM| exact STRM]|].
  split; [eapply stk_transport_disjoint; [exact ST| exact MU| exact WM|]; cbn [disjoint_from]; split; [lia| exact I]|].
  split; [exact MI'|].
  split.
  { eapply (uc_frame_agree ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu FLG SL SPAB ltac:(lia) TOP S0SP); [| exact FR].
    eapply magree_mono; [exact AG|]. intros a KP. cbn [outside]. split; [| exact I].
    destruct (uc_keep_step Wd RNG _ LB m a AH SH KP) as [_ NW]. pose proof (not_in_ranges_hd _ _ _ _ NW). lia. }
  split.
  { eapply magree_trans; [exact PFA|]. eapply magree_mono; [exact AG|]. intros a PA. cbn [outside]. split; [| exact I].
    destruct (uc_pf_step Wd RNG _ LB m a AH SH PA) as [_ NW]. pose proof (not_in_ranges_hd _ _ _ _ NW). lia. }
  split; [exact OK|]. split; [exact RS|]. split; [exact FP| exact SH].
Qed.

Lemma uc_inv_ret : forall Wd0 Wd RNG RNG' s s' LB LB' st v m st' v' m',
  uc_inv Wd0 RNG s LB st v m -> fp_le RNG RNG' -> aps_rest s' = aps_rest s -> uc_shape Wd LB' ->
  mem_inv asegs m' -> stk asegs m' lo SPA ->
  AHEAP AI L RNG' (aps_m s') LB' m' ->
  client_agree AI LB' SPA (inf_WR (ucx Wd st) (ILAY SPA 0 Zs 0 lo)) m m' ->
  inf_objs AI RNG' LB' (ucx Wd st) Fu Zs payload m' ->
  ainv (ucx Wd st) st' (v_lf v') (v_cf v') -> t_mode st' <> MEM ->
  inf_emem (ucx Wd st) Zs st' (v_lf v') (v_cf v') (v_wf v') (v_fo v') payload (v_zti v') (v_zto v') (v_zmsg v') (v_zopq v') (v_zdt v') (v_zadl v') (v_zres v')
           (v_zp1 v') (v_zp2 v') (v_zp3 v') (v_havedict v') (v_dmax v') (v_check v') (v_total v') (v_back v') (v_was v') (v_pad v') m' ->
  uc_inv Wd RNG' s' LB' st' v' m'.
Proof.
  intros Wd0 Wd RNG RNG' s s' LB LB' st v m st' v' m' (AH & IO & AV & MD & EM & ST & MI & FR & PFA & OK & RS & FP & SH)
         FPL RS' SH' MI' ST' AH' CA IO' AV' MD' EM'.
  pose proof (AI_layout AI _ _ _ _ _ AH) as (_ & _ & TOP & _).
  unfold client_agree in CA.
  unfold uc_inv.
  split; [exact AH'|]. split; [exact IO'|].
  split; [exact (ainv_rebase _ _ _ _ (8 * (n - t_cin st') + t_bits st' + (dl - t_cout st')) (fun _ => 0) AV')|].
  split; [exact MD'|]. split; [exact EM'|]. split; [exact ST'|]. split; [exact MI'|].
  split.
  { eapply (uc_frame_agree ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu FLG SL SPAB ltac:(lia) TOP S0SP); [| exact FR].
    eapply magree_mono; [exact CA|]. intros a KP. exact (uc_keep_step Wd RNG' _ LB' m' a AH' SH' KP). }
  split.
  { eapply magree_trans; [exact PFA|]. eapply magree_mono; [exact CA|]. intros a PA. exact (uc_pf_step Wd RNG' _ LB' m' a AH' SH' PA). }
  split; [eapply aps_ok_rest; [exact RS'| exact OK]|]. split; [rewrite RS'; exact RS|].
  split; [eapply fp_le_trans; [exact FP| exact FPL]| exact SH'].
Qed.

Lemma uc_link : forall m k prev,
  uc_frame ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 L SPA Fu FLG SL j8 j16 n0 dl trc m ->
  prev < SP -> SP < al_top L - 16 -> SP mod 8 = 0 -> (3 <= k)%nat ->
  4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  uchain m (al_top L) AMALLOC_PC prev SP k (bv_unsigned ra :: trc).
Proof.
  intros m k prev (_ & FRB & _ & _ & _ & _ & _ & _ & _ & _ & UC) PV TP S8 K3 RA4 RANE.
  unfold UFRB in FRB. rw_split FRB 11%nat FRx FRsr. clear FRx.
  destruct FRsr as [[_ BSR] _]. cbn [cells_bytes cbytes app] in BSR. rewrite app_nil_r in BSR.
  apply bytes_at_app in BSR. destruct BSR as [BS0 BRA]. rewrite length_le8 in BRA.
  replace (SP + -16 + Z.of_nat 8) with (SP - 8) in BRA by lia.
  replace (SP + -16) with (SP - 16) in BS0 by lia.
  pose proof (bv_unsigned_in_range 64 ra) as RRA. pose proof (bv_unsigned_in_range 64 s0) as RS0. unfold bv_modulus in *. cbn in RRA, RS0.
  replace (bv_unsigned ra :: trc) with ((if bv_unsigned ra =? AMALLOC_PC then [] else [bv_unsigned ra]) ++ trc)
    by (replace (bv_unsigned ra =? AMALLOC_PC) with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
  eapply (uc_step m (al_top L) AMALLOC_PC prev SP k (bv_unsigned s0) (bv_unsigned ra) trc); try lia.
  - rewrite Z_to_bv_bv_unsigned. exact BS0.
  - rewrite Z_to_bv_bv_unsigned. exact BRA.
  - replace (bv_unsigned ra =? AMALLOC_PC) with false by (symmetry; apply Z.eqb_neq; lia). apply UC. lia.
Qed.
End Inv.
End AI.
End CANSEC1.
