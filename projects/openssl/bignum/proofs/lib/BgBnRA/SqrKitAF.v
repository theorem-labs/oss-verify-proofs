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
From OSSVerify.Proofs.openssl.bignum.lib.BgBnRA Require Import AFrameKit AFrameCall AFrameTac AFrameEnv BnCallAF AFrameComp.
From OSSVerify.Proofs.openssl.bignum.lib.BgRepA Require Import BgLayerF BgIfaceF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Notation ST := (bstate bptr).

Section WithRT.
Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma w_lib_outside : forall Σ (st : ST) OW LB PL EA SPX (m : mem) lo sp x y (a : Z),
  AHEAP Σ OW LB m -> lib_parts st OW PL EA -> frames_ok LB PL SPX USTACK_TOP ->
  w_lib st OW PL lo sp (x, y) -> ACEIL <= lo -> lo <= sp -> 0 <= a < 2 ^ 64 ->
  ax_client LB sp (XW PL) a -> ~ (x <= a < y).
Proof.
  intros Σ st OW LB PL EA SPX m lo sp x y a HEAP PARTS FROK HW CEIL LOSP Ha HC Hin.
  set (m2 := fun v : word => if Z.eqb (bv_unsigned v) a then (match m v with Some _ => None | None => Some (Z_to_bv 8 0) end) else m v).
  assert (MU : munch [(x, y)] m m2).
  { intros v Hv. unfold m2. destruct (Z.eqb (bv_unsigned v) a) eqn:E; [| reflexivity].
    exfalso. apply Z.eqb_eq in E. cbn [outside] in Hv. rewrite E in Hv. destruct Hv as [Hv _]. apply Hv. exact Hin. }
  pose proof (seg_ax_pres' Σ st OW LB PL EA SPX m m2 [(x, y)] lo sp HEAP PARTS FROK MU ltac:(constructor; [exact HW | constructor]) CEIL LOSP) as AG.
  specialize (AG a Ha HC). unfold m2, wa in AG. rewrite unsigned_lit in AG by exact Ha. rewrite Z.eqb_refl in AG. destruct (m (Z_to_bv 64 a)); discriminate.
Qed.

Definition w_frmix (OW LB : list block) (st : ST) (PL : placement) (EA : BnRepDefs.err_addrs) (lo SPv : Z) (hs : list bnref) (f : Z) (k : nat) (iv : Z * Z) : Prop :=
  (w_lib st OW PL lo SPv iv /\ w_okc OW LB st PL EA SPv false hs iv)
  \/ (f <= fst iv /\ snd iv <= f + fs_size k - 8)
  \/ (shad f <= fst iv /\ snd iv <= shad f + fs_size k / 8).

Lemma cenv_frmixA : forall (LB : list block) PL EA lo SPv FB (s0w raw : word) rasO TOTAL Σ0 (ls0 : ST) OW0 m0 pre pre' used Σ (ls : ST) m m' OW W f k hs,
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre used Σ ls m OW ->
  lib_state_hc false hs ls m OW PL EA ->
  In (f, k) FR -> (forall b, In b LB -> off_fr f k b) ->
  munch W m m' -> wmono bgasegs m m' ->
  Forall (w_frmix OW LB ls PL EA lo SPv hs f k) W ->
  stk bgasegs m' lo FB -> mem_inv bgasegs m' ->
  rw_cells bgasegs m' FB (pre' ++ [C8 s0w; C8 raw]) -> Z.of_nat (cells_size pre') = SPv - FB - 16 ->
  cenvA LB PL lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre' used Σ ls m' OW
  /\ lib_state_hc false hs ls m' OW PL EA.
Proof.
  intros LB PL EA lo SPv FB s0w raw rasO TOTAL Σ0 ls0 OW0 m0 pre pre' used Σ ls m m' OW W f k hs
         (OK & HEAP & ST0 & MI & AXP & CR & CNT & RS & FRc & FSZ & UW) LS Hf OFF MU WM HW ST' MI' FR' FSZ'.
  pose proof OK as (CEIL & LOFB & FBSP & SPT & SP16 & FB16 & CNT0 & CRED0 & FROK & FAL & NOFR).
  pose proof (AH_fr_geo _ _ _ _ f k HEAP Hf) as GEO.
  pose proof (lib_state_h_parts _ _ _ _ _ _ LS) as PARTS.
  assert (LOSP : lo <= SPv) by (clear - LOFB FBSP; lia).
  assert (OFFA : forall b, In b (OW ++ LB) -> off_fr f k b).
  { intros b Hb. apply in_app_or in Hb as [Hb|Hb]; [exact (AH_ow_off_fr Σ OW LB m f k b HEAP Hf Hb) | exact (OFF b Hb)]. }

  assert (HEAP' : AHEAP Σ OW LB m').
  { eapply (AH_frame_fr Σ OW LB m m' W f k Hf HEAP MU WM); [| exact OFF].
    eapply Forall_impl; [| exact HW]. intros [x y] [[HL _]|[H|H]]; [| right; left; exact H | right; right; exact H].
    left. destruct HL as [[H1 H2]|[(b & Hb & H1 & H2)|(r & a & HA & NE & H1 & H2)]]; cbn [fst snd] in *.
    - left. cbn [fst snd]. unfold USTACK_TOP in *. clear - H1 H2 CEIL LOSP SPT. lia.
    - right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn [fst snd]. auto.
    - destruct (w_lib_struct_cases _ _ _ _ _ _ _ _ _ _ _ HEAP PARTS FROK HA NE) as [(b & Hb & B1 & B2)|(HF & b & Hb & B1 & B2)].
      + right; right. exists b. split; [apply in_or_app; left; exact Hb|]. cbn [fst snd]. clear - H1 H2 B1 B2. lia.
      + right; right. exists b. split; [apply in_or_app; right; exact Hb|]. cbn [fst snd]. clear - H1 H2 B1 B2. lia. }

  assert (AXS : ax_pres LB SPv (XW PL) m m').
  { intros a Ha Hw. apply MU. unfold wa. rewrite unsigned_lit by exact Ha. clear MU WM.
    pose proof (fr3_outside Σ OW LB m f k lo SPv LB a HEAP GEO CEIL LOSP
                  ltac:(intros b Hb; apply in_or_app; right; exact Hb) OFF (proj2 Hw)) as (_ & N2 & N3).
    induction HW as [|[x y] W' Hiv HW' IH]; [exact I|]. cbn [outside]. split; [| exact IH].
    destruct Hiv as [[HL _]|[[H1 H2]|[H1 H2]]]; cbn [fst snd] in *.
    - exact (w_lib_outside Σ ls OW LB PL EA SPv m lo SPv x y a HEAP PARTS FROK HL CEIL LOSP Ha Hw).
    - clear - N2 H1 H2. lia.
    - clear - N3 H1 H2. lia. }

  assert (LS' : lib_state_hc false hs ls m' OW PL EA).
  { eapply lib_state_hc_agree; [exact LS|]. eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|].
    intros a Ha. clear MU WM.
    assert (NFR : ~ (f <= a < f + fs_size k) /\ ~ (shad f <= a < shad f + fs_size k / 8)).
    { destruct (BgLayer.own_fp_block OW ls PL EA PARTS false hs a Ha) as [HL|[(q & A & n & Hq & Hxq & _)|(iv & Hiv & Hxi)]].
      - destruct GEO as (G1 & G2 & G3 & G4 & G5). unfold SEGTOP_A in G4.
        pose proof (fs_size_pos k) as (FS1 & _). destruct (fs_size_div8 k) as (FS2 & FS3).
        assert (SHR : 2147450880 <= shad f) by (unfold shad, SHB; pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)); lia).
        revert HL. unfold libw, LIBW_bgr, LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. clear - G4 SHR FS1. lia.
      - pose proof (fr3_outside Σ OW LB m f k lo SPv (OW ++ LB) a HEAP GEO CEIL LOSP ltac:(intros b Hb; exact Hb) OFFA
                      ltac:(right; right; exists (q, A, n); split; [apply in_or_app; left; exact Hq | cbn [blk_addr blk_size fst snd]; exact Hxq])) as (_ & N2 & N3).
        split; [exact N2 | exact N3].
      - destruct (frame_iv_blk LB PL SPv USTACK_TOP FROK iv Hiv) as (b & Hb & R1 & R2).
        pose proof (fr3_outside Σ OW LB m f k lo SPv (OW ++ LB) a HEAP GEO CEIL LOSP ltac:(intros b0 Hb0; exact Hb0) OFFA
                      ltac:(right; right; exists b; split; [apply in_or_app; right; exact Hb | clear - R1 R2 Hxi; lia])) as (_ & N2 & N3).
        split; [exact N2 | exact N3]. }
    destruct NFR as (N2 & N3).
    induction HW as [|[x y] W' Hiv HW' IH]; [exact I|]. cbn [outside]. split; [| exact IH].
    destruct Hiv as [[_ HK]|[[H1 H2]|[H1 H2]]]; cbn [fst snd] in *.
    - assert (FW : Forall (w_okc OW LB ls PL EA SPv false hs) [(x, y)]) by (constructor; [exact HK | constructor]).
      pose proof (own_fp_outside Σ OW LB m HEAP ls PL EA SPv USTACK_TOP PARTS FROK false hs [(x, y)] a FW Ha) as O. cbn [outside] in O. tauto.
    - clear - N2 H1 H2. lia.
    - clear - N3 H1 H2. lia. }
  split; [| exact LS'].
  assert (AGS : agree_on (fun a => SPv <= a < USTACK_TOP) m m').
  { eapply agree_on_mono; [exact AXS|]. intros a Ha. cbv beta in Ha. split; [| left; exact Ha].
    apply (xw_stack_out Σ OW LB m PL SPv USTACK_TOP a HEAP FROK). clear - Ha CEIL LOSP. lia. }
  unfold cenvA. split; [exact OK|]. split; [exact HEAP'|]. split; [exact ST'|]. split; [exact MI'|].
  split; [exact (ax_pres_trans _ _ _ _ _ _ AXP AXS)|].
  split; [exact CR|]. split; [exact CNT|]. split; [exact RS|]. split; [exact FR'|]. split; [exact FSZ'|].
  unfold uw_opt in *. destruct rasO as [ras|]; [| exact I].
  apply (uw_chain_agree m m' ras SPv (bv_unsigned s0w) UW). eapply agree_on_mono; [exact AGS|]. intros a Ha. cbv beta in *. clear - Ha. lia.
Qed.

End WithRT.
