From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YP0m YP09 YI04 YI09 YI08 YI00 YN3v YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0b YP0a YP0c YP0d YP07 YP0l YC80 YI0w YI0z YI12 YC4a YC1f YC8g YC8i YC44 YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YC1i YCbf YCj1 YCja YCjr YRo.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Y.Prog Require Import
DiscoYEntryInv DiscoYEntryShapes DiscoYEntProCuts.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma d_ev_fits : ev_fits.
Proof. unfold ev_fits, EV_PRO, EV_ITER, EV_EPI, EV_LIB, MAX_OPS. lia. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head} {LS : lib_shape}.
Section f.
Context {PI : PAImg lib_both3_0_listing}.
#[local] Notation SEGS := (@pa_segs _ lib_both3_0_listing PI).
Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.

Theorem d_loop_of_parts : loop_of_parts B MT XM_LIB RLO RHI tfib_K.
Proof.
  intros HHDR HARM3 HREC HCLS HHOBS HOBS HR27 HLAT cx h.
  set (Q := exit_pre B MT XM_LIB RLO RHI tfib_K cx h).
  set (P := fun i => loop_inv B MT XM_LIB RLO RHI tfib_K cx h i).
  set (G := fun i (W' : world SEGS) c' => Q W' c' \/ exists i', 0 <= MAX_OPS - i' < MAX_OPS - i /\ P i' W' c').
  assert (HL : forall i n now W c,
    lat_pre B MT XM_LIB RLO RHI tfib_K cx h i n now W c \/ l27_pre B MT XM_LIB RLO RHI tfib_K cx h i n now W c ->
    SRr SEGS W c (G i)).
  { intros i n now W c HP.
    eapply SRr_mono; [exact (HLAT cx h i n now W c HP)|].
    intros W' c' _ [(Hi & HN) | HX]; [right; exists (i + 1); split; [lia | exact HN] | left; exact HX]. }
  assert (HT : forall i n now nb fr len W c,
    r27_in B MT XM_LIB RLO RHI tfib_K cx h i n now nb fr len W c -> SRr SEGS W c (G i)).
  { intros i n now nb fr len W c HR.
    eapply SRr_bind; [exact (HR27 cx h i n now nb fr len W c HR)|].
    intros W' c' _ HP. exact (HL i n now W' c' (or_intror HP)). }
  apply (SRr_loopZ SEGS Z (fun i => MAX_OPS - i) P Q).
  intros i W c HI.
  eapply SRr_bind; [exact (HHDR cx h i W c HI)|].
  intros W1 c1 _ [HQ | (n & now & op & [(_ & HA) | (_ & HD)])].
  - apply SRr_ret. left. exact HQ.
  - eapply SRr_bind; [exact (HARM3 cx h i n now op W1 c1 HA)|].
    intros W2 c2 _ HP. exact (HL i n now W2 c2 (or_introl HP)).
  - eapply SRr_bind; [exact (HREC cx h i n now op W1 c1 HD)|].
    intros W2 c2 _ (nb & fr & len & _ & _ & [(_ & HC) | (_ & HH)]).
    + eapply SRr_bind; [exact (HCLS cx h i n now op nb fr len W2 c2 HC)|].
      intros W3 c3 _ [(Sg & HO) | HR].
      * eapply SRr_bind; [exact (HOBS cx h i n now op nb fr len Sg W3 c3 HO)|].
        intros W4 c4 _ HR. exact (HT i (nb - len) now nb fr len W4 c4 HR).
      * exact (HT i (nb - len) now nb fr len W3 c3 HR).
    + eapply SRr_bind; [exact (HHOBS cx h i n now op nb fr len W2 c2 HH)|].
      intros W3 c3 _ HR. exact (HT i (nb - len) now nb fr len W3 c3 HR).
Qed.

Theorem d_walk_of_parts : walk_of_parts B MT XM_LIB XN_LIB RLO RHI tfib_K.
Proof.
  intros _ HPRO HLOOP HEXIT fq ly S W regs mem md p n pl M HF HPRE HX.
  eapply SRr_bind; [exact (HPRO fq ly S W regs mem md p n pl M HF HPRE HX)|].
  intros W1 c1 _ (cx & h & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _ & E10 & HC).
  assert (HE : SRr SEGS W1 c1 (exit_pre B MT XM_LIB RLO RHI tfib_K cx h)).
  { destruct HC as [HL | HE]; [exact (HLOOP cx h 0 W1 c1 HL) | apply SRr_ret; exact HE]. }
  eapply SRr_bind; [exact HE|].
  intros W2 c2 _ HE2.
  pose proof (HEXIT cx h W2 c2 HE2) as HQ.
  rewrite E1, E2, E3, E4, E5, E6, E7, E8, E10 in HQ. exact HQ.
Qed.

Theorem d_walk_to_spec : walk_to_spec B MT XM_LIB XN_LIB RLO RHI tfib_K.
Proof.
  intros HLIBK HDX HWALK fx HF ly S W regs mem md p n pl M K HAI HPRE HK.
  rewrite HLIBK.
  pose proof (HDX regs ly S W mem md p n pl M HPRE) as HX.
  pose proof HPRE as (_ & Hra & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSORT & _ & _).
  eapply SRr_srealizes; [exact (HWALK fx ly S W regs mem md p n pl M HF HPRE HX) | exact HAI |].
  intros W' c' Hwle HAI' (fq' & Hfq' & fx' & ly' & S' & regs' & mem' & md' & Hc & _ & Hcsr & HJ & HPR & Ha0 & HPerm & HFD & HFS & HSNK & HAM & HMLE & HV).
  apply (HK (LL 0 (m_fs md) []) W' c' Hwle HAI').
  exists fx', ly', S', regs', mem', md', EV_LIB.
  split.
  { rewrite Hc. unfold cfg_at. rewrite <- Hra. unfold raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split; [destruct Hcsr as [Ecsr | Hz]; [rewrite Ecsr; exact Hfq' | exact Hz]|].
  unfold tfib_lib_post_x. cbn [ll_fs ll_ret ll_out].
  split; [exact HJ|]. split; [lia|]. split; [exact HPR|]. split; [exact Ha0|]. split; [exact HPerm|].
  split; [exact HFD|]. split; [exact HFS|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact HSORT|].
  split; [exact HSNK|]. split; [exact HAM|]. split; [exact HMLE|]. exact HV.
Qed.

Section pro.
Hypothesis HSA : pro_segA B MT XM_LIB RLO RHI tfib_K.
Hypothesis HSB : pro_segB B MT XM_LIB RLO RHI tfib_K.
Hypothesis HSC : pro_segC B MT XM_LIB RLO RHI tfib_K.
Hypothesis HSD : pro_segD B MT XM_LIB RLO RHI tfib_K.
Hypothesis HSE : pro_segE B MT XM_LIB RLO RHI tfib_K.

Theorem d_pro_of_segs : pro_spec B MT XM_LIB RLO RHI tfib_K.
Proof. exact (pro_of_segs B MT XM_LIB RLO RHI tfib_K HSA HSB HSC HSD HSE). Qed.
End pro.

Section comp.
Hypothesis HPRO : pro_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HHDR : hdr_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HARM3 : arm3_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HREC : rec_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HCLS : cls_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HHOBS : hobs_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HOBS : obs_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HR27 : r27_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HLAT : latch_spec B MT XM_LIB RLO RHI tfib_K.
Hypothesis HEXIT : exit_spec B MT XM_LIB XN_LIB RLO RHI tfib_K.

Theorem d_loop : loop_spec B MT XM_LIB RLO RHI tfib_K.
Proof. exact (d_loop_of_parts HHDR HARM3 HREC HCLS HHOBS HOBS HR27 HLAT). Qed.

Theorem d_walk : tLLVMFuzzerTestOneInput_walk B MT XM_LIB XN_LIB RLO RHI tfib_K.
Proof. exact (d_walk_of_parts d_ev_fits HPRO d_loop HEXIT). Qed.

Theorem d_entry_spec :
  (forall pl fs K, LIBK pl fs K = K (LL 0 fs [])) ->
  (forall regs ly S W mem md p n pl M,
     tfib_lib_pre_x B MT XM_LIB RLO RHI tfib_K regs ly S W mem md p n pl M -> dpre_extra W mem) ->
  tLLVMFuzzerTestOneInput_spec B MT XM_LIB XN_LIB RLO RHI tfib_K.
Proof. intros HLIBK HDX. exact (d_walk_to_spec HLIBK HDX d_walk). Qed.
End comp.

Theorem d_dentry_walk_of_parts : forall (SF6_ENTRY : Z)
  (P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 : Prop),
  let EnvP := dentry_env B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY
    (treac_disco_table_init_spec := P1) (treac_disco_gate_init_spec := P2)
    (treac_disco_peer_lock_init_spec := P3) (treac_hunt_init_spec := P4) (treac_hunt_pin_spec := P5)
    (treac_hunt_silence_proven_spec := P6) (treac_hunt_step_spec := P7)
    (treac_hunt_verdict_name_spec := P8) (treac_hunt_role_spec := P9)
    (treac_hunt_heard_anything_spec := P10) (treac_disco_classify_spec := P11)
    (treac_disco_classify_on_segment_spec := P12) (treac_hunt_observe_spec := P13)
    (tjson_scalar_spec := P14) (tjtok_is_spec := P15) (treac_box_name_spec := P16)
    (tcheck_sighting_spec := P17) (treac_disco_table_observe_spec := P18)
    (treac_disco_table_json_spec := P19) in
  (EnvP -> pro_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> hdr_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> arm3_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> rec_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> cls_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> hobs_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> obs_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> r27_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> latch_spec B MT XM_LIB RLO RHI tfib_K) ->
  (EnvP -> exit_spec B MT XM_LIB XN_LIB RLO RHI tfib_K) ->
  dentry_walk_ok B MT XM_LIB XN_LIB RLO RHI tfib_K SF6_ENTRY
    (treac_disco_table_init_spec := P1) (treac_disco_gate_init_spec := P2)
    (treac_disco_peer_lock_init_spec := P3) (treac_hunt_init_spec := P4) (treac_hunt_pin_spec := P5)
    (treac_hunt_silence_proven_spec := P6) (treac_hunt_step_spec := P7)
    (treac_hunt_verdict_name_spec := P8) (treac_hunt_role_spec := P9)
    (treac_hunt_heard_anything_spec := P10) (treac_disco_classify_spec := P11)
    (treac_disco_classify_on_segment_spec := P12) (treac_hunt_observe_spec := P13)
    (tjson_scalar_spec := P14) (tjtok_is_spec := P15) (treac_box_name_spec := P16)
    (tcheck_sighting_spec := P17) (treac_disco_table_observe_spec := P18)
    (treac_disco_table_json_spec := P19).
Proof.
  intros SF6_ENTRY P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 EnvP
    HP HH HA HR HC HHO HO HR7 HL HX E.
  exact (d_walk_of_parts d_ev_fits (HP E)
    (d_loop_of_parts (HH E) (HA E) (HR E) (HC E) (HHO E) (HO E) (HR7 E) (HL E)) (HX E)).
Qed.
End h.
End f.
End d.
