From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import Tac.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0 Contract FrameAPI KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec SlotModel SlotInv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import URzP.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import bcmp_c reac_box_family_of_c.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require reac_box_family_of.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.Seg Require Import Tac_scd.
Import ListNotations.
Open Scope Z_scope.

Lemma c03_none : forall hw, map bv_unsigned hw <> HWT 0 -> map bv_unsigned hw <> HWT 1 ->
  map bv_unsigned hw <> HWT 2 -> fam_cmp hw = 0.
Proof.
  intros hw H0 H1 H2. unfold fam_cmp. cbv zeta. cbn [HWT nth] in H0, H1, H2.
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) FAMOF_HW1); [contradiction|].
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) FAMOF_HW2); [contradiction|].
  destruct (list_eq_dec Z.eq_dec (map bv_unsigned hw) FAMOF_HW3); [contradiction|].
  reflexivity.
Qed.

Section C03.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {LS : lib_shape} {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Context {RzCi : RzC} {RzAi : RzA B (APIf rc)}.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis HBCMP : bcmp_contract.

Definition c03_K (g : ghost) (j : nat) (regs : bvmap 5 word) (mem : word -> option byte)
    (R : bvmap 5 word) (pc' : word) (mem' : word -> option byte) : Prop :=
  munch [] mem mem' /\ wmono rsegs mem mem' /\
  getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
  getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 20 = getr regs 20 /\
  getr R 26 = getr regs 26 /\
  ((pc' = Z_to_bv 64 0x13c68 /\ getr R 18 = getr regs 18 /\ map bv_unsigned (hwbT (g_in g)) = HWT j) \/
   (pc' = Z_to_bv 64 0x13508 /\ (S j < 3)%nat /\ getr R 8 = Z_to_bv 64 (3 - Z.of_nat (S j)) /\
    getr R 18 = Z_to_bv 64 (HWT_ADDR + 12 * Z.of_nat (S j)) /\ map bv_unsigned (hwbT (g_in g)) <> HWT j) \/
   (pc' = Z_to_bv 64 0x1353c /\ j = 2%nat /\ map bv_unsigned (hwbT (g_in g)) <> HWT j)).

Ltac c03_call HLn HR Hv m' HMU HWM :=
  eapply Exec.evt_cut;
  [ eapply HBCMP;
    [ rewrite MState.unsigned_lit by (unfold spk; lia); exact HLn
    | rewrite MState.unsigned_lit by lia; exact HR
    | change (Z.to_nat (bv_unsigned (Z_to_bv 64 8))) with 8%nat; exact Hv
    | apply mem_inv_normalize ]
  | let ms' := fresh "ms'" in let PO := fresh "PO" in
    intros ms' PO;
    destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                    ?E & HMU & HWM & _ & _ & _);
    subst ms';
    replace (MState.ret_pc (Z_to_bv 64 0x13518)) with (Z_to_bv 64 0x13518)
      by (apply bv_eq; vm_compute; reflexivity) ].

Lemma c03_step : forall g j,
  Hcut B APIf ra (Inv_K13c68 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1353c B APIf ra empty) ->
  (forall c', Inv_K13508_at B APIf ra empty g (S j) c' -> Rz (ms_segs B) c' (Post B APIf ra g)) ->
  forall c, Inv_K13508_at B APIf ra empty g j c -> Rz (ms_segs B) c (Post B APIf ra g).
Proof.
  intros g j H68 H53c IH c Hc.
  destruct Hc as (L & A & regs & mem & md & -> & HF & HP & HCB & Hhv & H9 & H19 & H8 & H18 & Hj & Hmiss).
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  destruct (sc_fr_facts B APIf ra empty FF g _ _ L A regs mem md HF)
    as (Hro & _ & Hfsp & HSK & HS47 & Ef & Hsp).
  pose proof alloc_ceiling_val as Hc.
  pose proof HCB as (HNR & HNRb & HG16 & (W1 & W2 & W3) & HCUR & HID).
  assert (Hlen : length (hwbT (g_in g)) = 8%nat) by apply sc_rec_hwb_len.
  assert (HLn : bytes_at rsegs (normalize rsegs mem) (fsp g + 116) (hwbT (g_in g)))
    by (apply bytes_at_normalize; [exact Hro | exact W3]).
  apply (sc_run_norm B APIf ra empty FF regs (Z_to_bv 64 0x13508) mem md L A (c03_K g j regs mem) _ HMR Hro).
  - unfold rmk, c03_K. rewrite H8, H18, H19.
    destruct j as [|[|[|j]]]; [| | | lia].
    + change (3 - Z.of_nat 0) with 3. change (HWT_ADDR + 12 * Z.of_nat 0) with 66988.
      assert (HR : bytes_at rsegs (normalize rsegs mem) 66988 (map (Z_to_bv 8) (HWT 0))).
      { apply bytes_at_normalize; [exact Hro|].
        apply sc_img_bytes; [exact Hro | lia | cbn; lia | vm_compute; reflexivity]. }
      destruct (memcmp_model_total (hwbT (g_in g)) (map (Z_to_bv 8) (HWT 0)) 8 ltac:(lia) ltac:(cbn; lia))
        as [v Hv].
      destruct (reac_box_family_of.famof_memcmp 8 (hwbT (g_in g)) (map (Z_to_bv 8) (HWT 0)) v Hlen eq_refl Hv)
        as [Rv Iv].
      change (map bv_unsigned (map (Z_to_bv 8) (HWT 0))) with (HWT 0) in Iv.
      step. step. step. step.
      c03_call HLn HR Hv m' HMU HWM.
      step. if_cases HC; zify_cond HC; rewrite ?MState.unsigned_lit_wrap in HC.
      * assert (V : v = 0) by (clear - HC Rv; Z.div_mod_to_equations; lia). apply Iv in V.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HRm Hs.
        destruct (sc_back mem m' mem' _ Hro HMU HWM HRm Hs) as [HM' HW'].
        split; [exact HM'|]. split; [exact HW'|]. repeat (split; [reflexivity|]).
        left. split; [reflexivity|]. split; [reflexivity | exact V].
      * assert (V : v <> 0) by (clear - HC Rv; Z.div_mod_to_equations; lia).
        assert (M : map bv_unsigned (hwbT (g_in g)) <> HWT 0) by (intros X; apply Iv in X; lia).
        step. step. step. if_true.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HRm Hs.
        destruct (sc_back mem m' mem' _ Hro HMU HWM HRm Hs) as [HM' HW'].
        split; [exact HM'|]. split; [exact HW'|]. repeat (split; [reflexivity|]).
        right. left. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity | exact M].
    + change (3 - Z.of_nat 1) with 2. change (HWT_ADDR + 12 * Z.of_nat 1) with 67000.
      assert (HR : bytes_at rsegs (normalize rsegs mem) 67000 (map (Z_to_bv 8) (HWT 1))).
      { apply bytes_at_normalize; [exact Hro|].
        apply sc_img_bytes; [exact Hro | lia | cbn; lia | vm_compute; reflexivity]. }
      destruct (memcmp_model_total (hwbT (g_in g)) (map (Z_to_bv 8) (HWT 1)) 8 ltac:(lia) ltac:(cbn; lia))
        as [v Hv].
      destruct (reac_box_family_of.famof_memcmp 8 (hwbT (g_in g)) (map (Z_to_bv 8) (HWT 1)) v Hlen eq_refl Hv)
        as [Rv Iv].
      change (map bv_unsigned (map (Z_to_bv 8) (HWT 1))) with (HWT 1) in Iv.
      step. step. step. step.
      c03_call HLn HR Hv m' HMU HWM.
      step. if_cases HC; zify_cond HC; rewrite ?MState.unsigned_lit_wrap in HC.
      * assert (V : v = 0) by (clear - HC Rv; Z.div_mod_to_equations; lia). apply Iv in V.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HRm Hs.
        destruct (sc_back mem m' mem' _ Hro HMU HWM HRm Hs) as [HM' HW'].
        split; [exact HM'|]. split; [exact HW'|]. repeat (split; [reflexivity|]).
        left. split; [reflexivity|]. split; [reflexivity | exact V].
      * assert (V : v <> 0) by (clear - HC Rv; Z.div_mod_to_equations; lia).
        assert (M : map bv_unsigned (hwbT (g_in g)) <> HWT 1) by (intros X; apply Iv in X; lia).
        step. step. step. if_true.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HRm Hs.
        destruct (sc_back mem m' mem' _ Hro HMU HWM HRm Hs) as [HM' HW'].
        split; [exact HM'|]. split; [exact HW'|]. repeat (split; [reflexivity|]).
        right. left. split; [reflexivity|]. split; [lia|]. split; [reflexivity|]. split; [reflexivity | exact M].
    + change (3 - Z.of_nat 2) with 1. change (HWT_ADDR + 12 * Z.of_nat 2) with 67012.
      assert (HR : bytes_at rsegs (normalize rsegs mem) 67012 (map (Z_to_bv 8) (HWT 2))).
      { apply bytes_at_normalize; [exact Hro|].
        apply sc_img_bytes; [exact Hro | lia | cbn; lia | vm_compute; reflexivity]. }
      destruct (memcmp_model_total (hwbT (g_in g)) (map (Z_to_bv 8) (HWT 2)) 8 ltac:(lia) ltac:(cbn; lia))
        as [v Hv].
      destruct (reac_box_family_of.famof_memcmp 8 (hwbT (g_in g)) (map (Z_to_bv 8) (HWT 2)) v Hlen eq_refl Hv)
        as [Rv Iv].
      change (map bv_unsigned (map (Z_to_bv 8) (HWT 2))) with (HWT 2) in Iv.
      step. step. step. step.
      c03_call HLn HR Hv m' HMU HWM.
      step. if_cases HC; zify_cond HC; rewrite ?MState.unsigned_lit_wrap in HC.
      * assert (V : v = 0) by (clear - HC Rv; Z.div_mod_to_equations; lia). apply Iv in V.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HRm Hs.
        destruct (sc_back mem m' mem' _ Hro HMU HWM HRm Hs) as [HM' HW'].
        split; [exact HM'|]. split; [exact HW'|]. repeat (split; [reflexivity|]).
        left. split; [reflexivity|]. split; [reflexivity | exact V].
      * assert (V : v <> 0) by (clear - HC Rv; Z.div_mod_to_equations; lia).
        assert (M : map bv_unsigned (hwbT (g_in g)) <> HWT 2) by (intros X; apply Iv in X; lia).
        step. step. step. if_false. step.
        apply Exec.evt_done. do 3 eexists. split; [reflexivity|]. intros mem' HRm Hs.
        destruct (sc_back mem m' mem' _ Hro HMU HWM HRm Hs) as [HM' HW'].
        split; [exact HM'|]. split; [exact HW'|]. repeat (split; [reflexivity|]).
        right. right. split; [reflexivity|]. split; [reflexivity | exact M].
  - intros R pc' mem' regs' (HM' & HW' & E2 & E3 & E4 & E9 & E19 & E20 & E26 & Hbr) Hg.
    assert (HM32 : munch [(fsp g - 32, fsp g)] mem mem') by (apply sc_munch_nil; exact HM').
    assert (HF' : FR B APIf ra empty g (2 * NR g) [] L A regs' mem' md).
    { apply (sc_FR_regs B APIf ra empty g _ _ L A regs regs' mem' md); [| rewrite Hg; assumption ..].
      apply (sc_after_call B APIf ra empty FF g _ _ L A regs mem md mem' 32 HF HP HM32 HW'). lia. }
    assert (HCB' : CB g regs' mem').
    { apply (sc_CB_regs g regs regs' mem'); [| rewrite Hg; assumption ..].
      exact (sc_CB_mem g regs mem mem' _ _ HCB HM32 ltac:(lia)). }
    destruct Hbr as [(-> & E18 & Hm) | [(-> & Hj' & E8 & E18 & Hm) | (-> & Ej & Hm)]].
    + apply H68. exists j. apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem' md HF' HP).
      split; [exact HCB'|]. split; [exact Hhv|]. rewrite !Hg.
      split; [rewrite E9; exact H9|]. split; [rewrite E18; exact H18|].
      split; [exact Hj|]. split; [exact Hm | exact Hmiss].
    + apply IH. apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem' md HF' HP).
      split; [exact HCB'|]. split; [exact Hhv|]. rewrite !Hg.
      split; [rewrite E9; exact H9|]. split; [rewrite E19; exact H19|].
      split; [exact E8|]. split; [exact E18|]. split; [exact Hj'|].
      intros j' Hj''. destruct (Nat.eq_dec j' j) as [->|Hne]; [exact Hm | apply Hmiss; lia].
    + apply H53c. apply (sc_cut B APIf ra empty g _ _ _ _ L A regs' mem' md HF' HP).
      destruct HCB' as (_ & _ & HG16' & _ & HCUR' & HID').
      split; [exact HCUR'|]. split; [split; assumption|].
      split; [rewrite Hg, E9; exact H9|].
      subst j. rewrite Hhv. unfold fam_hw. cbn [Z.eqb].
      apply c03_none; [apply Hmiss; lia | apply Hmiss; lia | exact Hm].
Qed.

Lemma seg_C03 :
  Hcut B APIf ra (Inv_K13c68 B APIf ra empty) ->
  Hcut B APIf ra (Inv_K1353c B APIf ra empty) ->
  Hcut B APIf ra (Inv_K13508 B APIf ra empty).
Proof.
  intros H68 H53c g c [j Hc].
  assert (Hind : forall k j' c', (3 - j' = k)%nat -> Inv_K13508_at B APIf ra empty g j' c' ->
                   Rz (ms_segs B) c' (Post B APIf ra g)).
  { induction k as [|k IHk]; intros j' c' Hk Hc'.
    - destruct Hc' as (L & A & regs & mem & md & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hj & _). lia.
    - apply (c03_step g j' H68 H53c); [|exact Hc'].
      intros c'' Hc''. apply (IHk (S j') c''); [lia | exact Hc'']. }
  exact (Hind (3 - j)%nat j c eq_refl Hc).
Qed.

End C03.
