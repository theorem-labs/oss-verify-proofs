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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnCallAF AFrameComp PlaceRecpA.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma lib_state_obj_agree : forall Σ OW LB m m' (st : bstate bptr) PL EA SPX SP b d n,
  AHEAP Σ OW LB m -> lib_state st m OW PL EA -> frames_ok LB PL SPX USTACK_TOP -> SP <= SPX ->
  In b LB -> blk_addr b <= d -> d + n <= blk_addr b + blk_size b -> (forall x, d <= x < d + n -> ~ rin_ivs (pl_frames PL) x) ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d <= a < d + n)) m m' ->
  lib_state st m' OW PL EA.
Proof.
  intros Σ OW LB m m' st PL EA SPX SP b d n HEAP LS FROK LE Hb B1 B2 NF AG.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  unfold lib_state in *. eapply lib_state_hc_agreeA; [exact LS|]. eapply agree_on_mono; [exact AG|]. intros x Hx. split.
  - eapply (own_fp_clientA false [] st m OW LB PL EA SPX USTACK_TOP (OW ++ LB) SP x LS FROK); [| | exact Hx]; intros b0 Hb0; apply in_or_app; [left | right]; exact Hb0.
  - intros Hd. destruct (own_fp_blockA OW st PL EA PARTS false [] x Hx) as [HL|[(q & A & n0 & Hq & Hxq & _)|(iv & Hiv & Hxi)]].
    + pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact Hb)) as (_ & _ & _ & _ & BI).
      revert HL. unfold BnRepA.libw, libw, LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia.
    + pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite map_app in ND.
      assert (NE : blk_id (q, A, n0) <> blk_id b).
      { intros E. eapply (nodup_app_disj _ _ (blk_id b) ND); [rewrite <- E; apply in_map; exact Hq | apply in_map; exact Hb]. }
      pose proof (AH_disjoint_gen _ _ _ _ (q, A, n0) b HEAP ltac:(apply in_or_app; left; exact Hq) ltac:(apply in_or_app; right; exact Hb) NE) as DJ.
      cbn [blk_addr blk_size fst snd] in DJ. lia.
    + apply (NF x Hd). apply rin_ivs_In. exists iv. split; [exact Hiv | exact Hxi].
Qed.

Lemma cenv_obj_agreeA : forall (objs LBo : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m m' OW SP b d n,
  cenvA (objs ++ LBo) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_state ls m OW PL EA ->
  In b objs -> blk_addr b <= d -> d + n <= blk_addr b + blk_size b -> (forall x, d <= x < d + n -> ~ rin_ivs (pl_frames PL) x) ->
  SP <= FB ->
  agree_on (fun a => aclient_addr (OW ++ objs ++ LBo) SP a /\ ~ (d <= a < d + n)) m m' ->
  AHEAP Σ OW (objs ++ LBo) m' -> stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
  cenvA (objs ++ LBo) PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m' pre used Σ ls m' OW
  /\ lib_state ls m' OW PL EA
  /\ ax_pres LBo SPv (XW PL) m0 m'.
Proof.
  intros objs LBo PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m m' OW SP b d n
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRC & FSZ & UW) LS Hb B1 B2 NF LE AG HEAP' ST' MI'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & _ & _ & _ & _ & FROK & _).
  assert (HbL : In b (objs ++ LBo)) by (apply in_or_app; left; exact Hb).
  pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; right; exact HbL)) as (B0 & _ & _ & BC & BI).
  assert (STK : forall a, FB <= a < USTACK_TOP -> aclient_addr (OW ++ objs ++ LBo) SP a /\ ~ (d <= a < d + n)).
  { intros a Ha. split; [left; lia | unfold BnHeapA.ACEIL in *; lia]. }
  assert (AXS : ax_pres LBo SPv (XW PL) m m').
  { eapply agree_on_mono; [exact AG|]. intros a [_ Ha]. split.
    - destruct Ha as [Ha|[Ha|(b' & Hb' & Hr)]]; [left; lia | right; left; exact Ha |].
      right; right. exists b'. split; [apply in_or_app; right; apply in_or_app; right; exact Hb' | exact Hr].
    - intros Hd. destruct Ha as [Ha|[Ha|(b' & Hb' & Hr)]]; [unfold BnHeapA.ACEIL in *; lia | |].
      + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; lia.
      + assert (NE : blk_id b <> blk_id b').
        { intros E. pose proof (AH_nodup _ _ _ _ HEAP) as ND. rewrite !map_app in ND. apply NoDup_app_remove_l in ND.
          eapply (nodup_app_disj _ _ (blk_id b) ND); [apply in_map; exact Hb | rewrite E; apply in_map; exact Hb']. }
        pose proof (AH_disjoint_gen _ _ _ _ b b' HEAP ltac:(apply in_or_app; right; exact HbL) ltac:(apply in_or_app; right; apply in_or_app; right; exact Hb') NE) as DJ. lia. }
  split; [| split; [exact (lib_state_obj_agree Σ OW (objs ++ LBo) m m' ls PL EA SPv SP b d n HEAP LS FROK ltac:(lia) HbL B1 B2 NF AG)
                   | exact (ax_pres_trans _ _ _ _ _ _ (ax_pres_outer objs LBo _ _ _ _ AXP) AXS)]].
  unfold cenvA. split; [exact OK|]. split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|]. split; [apply ax_pres_refl|].
  split; [exact CR|]. split; [exact CNT|]. split; [exact RS|].
  split. { eapply rw_cells_agree; [exact AG | exact FRC |]. intros a Ha. apply STK. rewrite cells_size_app in Ha. cbn [cells_size csize Nat.add] in Ha. unfold USTACK_TOP in *. lia. }
  split; [exact FSZ|].
  unfold uw_opt in *. destruct rasO as [ras|]; [| exact I].
  apply (uw_chain_agree m m' ras _ _ UW). eapply agree_on_mono; [exact AG|]. intros a Ha. apply STK. lia.
Qed.

End WithRT.

Lemma pl_wf_place_recp_nf : forall PL an,
  pl_wf PL -> 0 < an -> (forall x, an <= x < an + 60 -> ~ rin_ivs (pl_frames PL) x) -> pl_wf (pl_place_recp PL an).
Proof.
  intros PL an (W1 & W2 & W3) A0 NF.
  assert (POS : forall r p iv, pl_bn PL r = Some p -> In iv (fr_ivs (Some p)) -> fst iv < snd iv).
  { intros r p iv E Hiv. destruct p as [| | |]; cbn [fr_ivs In] in Hiv;
      [destruct Hiv | destruct Hiv as [<-|[]]; unfold BN_STRUCT_SZ; cbn [fst snd]; lia
      | destruct Hiv as [<-|[<-|[]]]; unfold BN_STRUCT_SZ, TMOD_BUF_SZ; cbn [fst snd]; lia | destruct Hiv]. }
  assert (OLD : forall r p iv, pl_bn PL r = Some p -> In iv (fr_ivs (Some p)) -> snd iv <= an \/ an + 60 <= fst iv).
  { intros r p iv E Hiv. destruct (W1 r p E) as (Hr & _). pose proof (POS r p iv E Hiv) as P.
    destruct (Z_le_dec (snd iv) an) as [L|L]; [left; exact L|]. destruct (Z_le_dec (an + 60) (fst iv)) as [R|R]; [right; exact R|]. exfalso.
    apply (NF (Z.max (fst iv) an) ltac:(lia)). apply rin_ivs_In. exists iv. split; [| lia].
    apply pl_frames_In. left. exists r. rewrite E. split; [exact Hr | exact Hiv]. }
  assert (CASES : forall r p, pl_bn (pl_place_recp PL an) r = Some p ->
            (r = RRecpN /\ p = PFrame an) \/ (r = RRecpNr /\ p = PFrame (an + 24)) \/ (r <> RRecpN /\ r <> RRecpNr /\ pl_bn PL r = Some p)).
  { intros r p E. destruct (Nat.eq_dec r RRecpN) as [->|N1]; [left; rewrite pl_bn_place_recp_N in E; injection E as <-; auto|].
    destruct (Nat.eq_dec r RRecpNr) as [->|N2]; [right; left; rewrite pl_bn_place_recp_Nr in E; injection E as <-; auto|].
    right; right. rewrite pl_bn_place_recp_other in E by assumption. auto. }
  assert (NEW : forall r p iv, pl_bn (pl_place_recp PL an) r = Some p -> In iv (fr_ivs (Some p)) ->
            (r = RRecpN /\ iv = (an, an + 24)) \/ (r = RRecpNr /\ iv = (an + 24, an + 48)) \/ (r <> RRecpN /\ r <> RRecpNr /\ (snd iv <= an \/ an + 60 <= fst iv) /\ fst iv < snd iv /\ pl_bn PL r = Some p)).
  { intros r p iv E Hiv. destruct (CASES r p E) as [[-> ->]|[[-> ->]|(N1 & N2 & E')]].
    - left. cbn [fr_ivs In] in Hiv. destruct Hiv as [<-|[]]. unfold BN_STRUCT_SZ. auto.
    - right; left. cbn [fr_ivs In] in Hiv. destruct Hiv as [<-|[]]. unfold BN_STRUCT_SZ. split; [reflexivity| f_equal; lia].
    - right; right. split; [exact N1|]. split; [exact N2|]. split; [exact (OLD r p iv E' Hiv)|]. split; [exact (POS r p iv E' Hiv) | exact E']. }
  split; [|split].
  - intros r p E. destruct (CASES r p E) as [[-> ->]|[[-> ->]|(N1 & N2 & E')]]; [| | exact (W1 r p E')].
    + split; [unfold RRecpN, NFIX; lia|]. split; [unfold RRecpN, ROne; lia|]. split; [reflexivity| exact A0].
    + split; [unfold RRecpNr, NFIX; lia|]. split; [unfold RRecpNr, ROne; lia|]. split; [reflexivity| lia].
  - intros r r' p p' iv iv' NE E E' Hiv Hiv'. unfold iv_apart.
    destruct (NEW r p iv E Hiv) as [[-> ->]|[[-> ->]|(N1 & N2 & S1 & P1 & E1)]];
      destruct (NEW r' p' iv' E' Hiv') as [[-> ->]|[[-> ->]|(N1' & N2' & S1' & P1' & E1')]]; cbn [fst snd];
      first [ exfalso; apply NE; reflexivity | exact (W2 r r' p p' iv iv' NE E1 E1' Hiv Hiv') | lia ].
  - cbn [pl_recp pl_place_recp pl_set_recp]. split; [lia|]. intros r p iv E Hiv. unfold iv_apart, RECP_SC_SZ. cbn [fst snd].
    destruct (NEW r p iv E Hiv) as [[-> ->]|[[-> ->]|(N1 & N2 & S1 & P1 & E1)]]; cbn [fst snd]; lia.
Qed.

Section Place.
Context {AR : ARun}.
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma st_recp_init_eq : forall (st : bstate bptr) m OW PL EA, lib_state st m OW PL EA -> pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None ->
  st_recp_init st = set_recp 0 0 st.
Proof.
  intros st m OW PL EA (HC & HE & HO & (WF & PWF & IDS & (M1 & M2 & M3 & M4 & M5))) E1 E2.
  assert (G8 : getbn RRecpN st = bn_nil 0) by (apply M2; [unfold RRecpN, NFIX; lia| exact E1]).
  assert (G9 : getbn RRecpNr st = bn_nil 0) by (apply M2; [unfold RRecpNr, NFIX; lia| exact E2]).
  unfold st_recp_init.
  replace (setbn RRecpN (bn_nil 0) (set_recp 0 0 st)) with (set_recp 0 0 st).
  - rewrite <- G9 at 1. change (getbn RRecpNr st) with (getbn RRecpNr (set_recp 0 0 st)). apply setbn_getbn_id.
  - rewrite <- G8 at 1. change (getbn RRecpN st) with (getbn RRecpN (set_recp 0 0 st)). symmetry. apply setbn_getbn_id.
Qed.

Lemma cenv_place_recpA : forall (LB : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : bstate bptr) OW0 m0 pre used Σ (ls : bstate bptr) m OW an b,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW -> lib_state ls m OW PL EA ->
  pl_bn PL RRecpN = None -> pl_bn PL RRecpNr = None ->
  In b LB -> blk_addr b <= an -> an + 60 <= blk_addr b + blk_size b -> an mod 8 = 0 ->
  cenvA LB (pl_place_recp PL an) lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m pre used Σ (st_recp_init ls) m OW.
Proof.
  intros LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW an b
         (OK & HEAP & ST & MI & AXP & CR & CNT & RS & FRC & FSZ & UW) LS E1 E2 Hb B1 B2 A8.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  rewrite (st_recp_init_eq ls m OW PL EA LS E1 E2).
  assert (INC : forall x, In x (b :: LB) -> In x LB) by (intros x [<-|Hx]; assumption).
  unfold cenvA, cenv_ok.
  split. { split; [exact CEIL|]. split; [exact LOFB|]. split; [exact FBSP|]. split; [exact SPT|]. split; [exact SP16|]. split; [exact FB16|]. split; [exact CNT0|]. split; [exact CRED0|].
           split; [exact (frames_ok_incl (b :: LB) LB _ _ _ (frames_ok_place_recp LB PL an SPv USTACK_TOP b FROK B1 B2) INC)|].
           split; [exact (frames_al_place_recp PL an FAL A8) | exact (frames_lb_incl _ (b :: LB) LB (frames_lb_place_recp LB PL an b NOFR A8 B1 B2) INC)]. }
  split; [exact HEAP|]. split; [exact ST|]. split; [exact MI|]. split; [apply ax_pres_refl|]. split; [exact CR|].
  split; [exact CNT|].
  split. { eapply refs_stable_trans; [exact RS|]. intros PL1 i a H. apply ref_at_set_recp. exact H. }
  split; [exact FRC|]. split; [exact FSZ | exact UW].
Qed.

End Place.
