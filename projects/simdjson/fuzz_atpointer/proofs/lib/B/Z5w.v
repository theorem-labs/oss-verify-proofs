(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2
     Zq3 Zqc Zqd Zqb I_lkit Z45 Z5k Z5q Z60 Z63 Z65 Z5o.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjG.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Variables (Σ Σ1 : rts RT) (I : objI).
  Hypothesis CTX : octx RT E d Σ Σ1 I.

  Local Ltac ul := lia_prep; unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.
  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -256 - dd) in *.

  Definition ownW (r : Z * Z) : Prop :=
    (oi_b I + -160 <= fst r /\ snd r <= oi_b I + 152) \/ (oi_f I + 24 <= fst r /\ snd r <= oi_f I + 120)
    \/ (shad (oi_f I) <= fst r /\ snd r <= shad (oi_f I) + 16) \/ (oi_out I <= fst r /\ snd r <= oi_out I + 24).

  Lemma obaseK_munch : forall (Σc : rts RT) (W : list (Z * Z)) (m m' : mem),
    obaseK RT E Σ I Σc m -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    munch W m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> Forall ownW W ->
    obaseK RT E Σ I Σc m'.
  Proof using AF CTX OK.
    intros Σc W m m' OB EF EL ES MU WM MI' HW.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    destruct OB as (MI & ART0 & AI & SAVED & HIGH & HDR & PRES).
    pose proof (fun a => obj_split RT AF E d Σ Σ1 I CTX Σc m a ART0 EF EL ES) as SPLIT.
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (NEWF : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> ~ (oi_f I <= a < oi_f I + 128) /\ ~ (shad (oi_f I) <= a < shad (oi_f I) + 16)).
    { intros a Ha. rewrite <- fs1, <- (fs1s (oi_f I)). rewrite fs1 at 2.
      apply (newframe_apartI RT AF Σ Σc m (oi_f I) 1%nat (oi_q I) a ART0 EF EL ES); [| exact Ha].
      pose proof (ok_lo E OK). lia. }
    assert (HinF : In (oi_f I, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    unfold ownW, oi_b in HW. cbn [oi_q oi_dd oi_f oi_out] in HW. fold q dd f out in HW. fold b in HW.

    assert (OW : forall a, ~ (b + -160 <= a < b + 152) -> ~ (f + 24 <= a < f + 120) -> ~ (shad f <= a < shad f + 16) -> ~ (out <= a < out + 24) -> outside W a).
    { intros a N1 N2 N3 N4. clear MU. induction W as [|[l h] W IH]; [exact Logic.I|]. inversion HW as [|x l' H1 H3]; subst. cbn [fst snd] in H1.
      cbn [outside]. split; [clear - H1 N1 N2 N3 N4; lia| exact (IH H3)]. }
    assert (AG : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a /\ ~ (out <= a < out + 24)) m m').
    { apply (agree_of_munch _ _ _ _ MU). intros x [Hx Ho]. destruct (NEWF x Hx) as [N1 N2]. destruct (SPLIT x Hx); (apply OW; flia). }
    split; [exact MI'|]. split.
    { apply (art_of_munch RT AF Σc m m' (ae_lo E) W ART0 ltac:(rewrite ES; exact LWIN)); [| exact MU| exact WM].
      clear MU OW AG. induction W as [|[l h] W IH]; [constructor|]. inversion HW as [|x l' H1 H3]; subst. cbn [fst snd] in H1.
      constructor; [| exact (IH H3)]. cbn [fst snd].
      destruct H1 as [H1|[H1|[H1|H1]]].
      - left. ul.
      - right; right; left. exists f, 1%nat. split; [exact HinF| rewrite fs1; lia].
      - right; right; right. exists f, 1%nat. split; [exact HinF| rewrite fs1s; lia].
      - left. ul. }
    split. { apply (AINV_A_agree E m m' AI). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX.
             pose proof (ainv_rng_lo E (bv_unsigned x) OK Hx). apply AG. split; [exact CX| flia]. }
    split. { apply (rw_cells_agree bsegs m m' _ _ SAVED); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn in Hx. apply OW; flia. }
    split. { apply (rw_cells_agree bsegs m m' _ _ HIGH); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn in Hx. apply OW; flia. }
    split. { apply (rw_cells_agree bsegs m m' _ _ HDR); [| exact WM]. apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbn in Hx. apply OW; [flia| flia| clear - Hx FSH; lia| flia]. }
    eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply AG. cbn [outside] in Ho. split; [exact Ha| flia].
  Qed.

  Lemma obaseK_call : forall (Σc : rts RT) (sp dst n : Z) (m m' : mem),
    obaseK RT E Σ I Σc m -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    ART RT Σc m' -> mem_inv bsegs m' -> oi_q I + -432 <= sp <= oi_b I ->
    rt_pres_ex (rt_live RT Σc) (rt_frames RT Σc) sp dst n m m' ->
    (forall a, dst <= a < dst + n -> aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_out I <= a < oi_out I + 24) ->
    (dst + n <= oi_b I + 152 \/ oi_q I <= dst \/ dst + n <= ae_lo E) -> (dst + n <= oi_f I \/ oi_f I + 24 <= dst \/ n <= 0) ->
    obaseK RT E Σ I Σc m'.
  Proof using AF CTX OK.
    intros Σc sp dst n m m' OB EF EL ES ART' MI' SPR PR NCL SEP1 SEP2.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR QHI (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof (obj_room RT E OK d Σ Σ1 I CTX) as (R1 & R2 & R3). unfold RT_STACK in R1.
    destruct OB as (MI & ART0 & AI & SAVED & HIGH & HDR & PRES).
    pose proof (fun a => obj_split RT AF E d Σ Σ1 I CTX Σc m a ART0 EF EL ES) as SPLIT.
    pose proof (fun sp' a => obj_mono RT Σ I Σc sp' a EF EL) as MONO.
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (HinF : In (oi_f I, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    assert (AGc : agree_on (fun a => aclient (rt_live RT Σc) (rt_frames RT Σc) sp a /\ ~ (dst <= a < dst + n)) m m').
    { apply (agree_of_pres_ex _ _ _ _ _ m m' _ PR). intros x Hx. exact Hx. }
    assert (AG : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a /\ ~ (out <= a < out + 24)) m m').
    { intros a [Ha Ho]. apply PR; [exact (MONO sp _ ltac:(lia) Ha)|]. intros Hd. exact (Ho (NCL _ Hd Ha)). }
    split; [exact MI'|]. split; [exact ART'|].
    split. { apply (AINV_A_agree E m m' AI). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX.
             pose proof (ainv_rng_lo E (bv_unsigned x) OK Hx). apply AG. split; [exact CX| flia]. }
    split. { xport_core SAVED AGc ltac:(fun Hx => split; [left; unfold USTACK_TOP in *; flia| clear - Hx SEP1 DDR R1 R2 R3 SPR; lia]). exact SAVED. }
    split. { xport_core HIGH AGc ltac:(fun Hx => split; [left; unfold USTACK_TOP in *; flia| clear - Hx SEP1 DDR R1 R2 R3 SPR; lia]). exact HIGH. }
    split. { xport_core HDR AGc ltac:(fun Hx => split; [right; right; right; left; exists f, 1%nat; split; [exact HinF| rewrite fs1; flia]| clear - Hx SEP2; lia]). exact HDR. }
    eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply AG. cbn [outside] in Ho. split; [exact Ha| flia].
  Qed.
End ObjG.
