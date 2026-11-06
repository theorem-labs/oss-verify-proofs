From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Exec MState PropExec.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0 AllocSlots AllocRoom.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c GrantSlotPlan SlotCompose
  UbsanHalts SlotImg SlotIntegration.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import SlotAgree AgreeLift.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantSlotPlanCf.
Import ListNotations.
Local Open Scope Z_scope.

(* Cut-free twin of SlotIntegration: the phase lemmas and the path of the slot end in SRcf, the allocator
   glue comes from the seg_*_cf segments, and the malloc room premises are room_cf facts. *)

Section ChainCf.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Variable B : malloc_syms.
Variable API : AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Hypothesis HB : ms_segs B = rsegs.
Hypothesis FA : frame_allocator B API.
Hypothesis Herr : errno_addr B + 4 <= alloc_ceiling.

Variables (L0 : layout) (A0 : astate) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
  (p n : Z).

Hypothesis HA0 : forall q k, In (q, k) (user_blocks A0) ->
  4096 <= ptr_addr L0 q /\ ptr_addr L0 q + k <= alloc_ceiling /\
  (forall i, 0 <= i < k -> ~ in_img B (ptr_addr L0 q + i)).

Local Abbreviation S0 := (SlotIntegration.S0 regs0).
Local Abbreviation St := (SlotIntegration.St B API L0 A0 regs0 mem0 md0).
Local Abbreviation own_ok := (SlotIntegration.own_ok B L0 A0).
Local Abbreviation xent := (SlotIntegration.xent regs0 p).
Local Abbreviation mpost := (SlotIntegration.mpost B API).
Local Abbreviation fpost := (SlotIntegration.fpost B API).
Local Abbreviation st_malloc_ok := (SlotIntegration.st_malloc_ok B API L0 A0 regs0 mem0 md0).
Local Abbreviation st_free_ok := (SlotIntegration.st_free_ok B API L0 A0 regs0 mem0 md0).
Local Abbreviation row_off := (SlotIntegration.row_off B).
Local Abbreviation glue_pre_of := (SlotIntegration.glue_pre_of B API HB FA Herr L0 A0 regs0 mem0 md0).
Local Abbreviation own_live := (SlotIntegration.own_live B L0 A0).
Local Abbreviation own_live' := (SlotIntegration.own_live' B L0 A0).
Local Abbreviation rel0_phase := (SlotIntegration.rel0_phase B API HB FA L0 A0 regs0 mem0 md0 HA0).

Lemma evt_SRcf_r : forall ms (Q : machine_state -> Prop) md (P : config -> Prop),
  Exec.evt rsegs Q ms -> m_halted md = None -> m_vm_lazy md = [] ->
  (forall ms', Q ms' -> SRcf B (mkCfg ms' md) P) -> SRcf B (mkCfg ms md) P.
Proof. intros ms Q md P H. rewrite <- HB in H. exact (evt_SRcf B ms Q md P H). Qed.

(* A Kind A phase run on the normalized memory, read back on the real memory. *)
Lemma phase_SRcf : forall (P Q : machine_state -> Prop) s md (R : config -> Prop),
  (forall s0, P s0 -> Exec.evt rsegs Q s0) ->
  norm_at P s -> MemNorm.ro_agree rsegs (ms_mem s) ->
  m_halted md = None -> m_vm_lazy md = [] ->
  (forall s', norm_at Q s' -> MemNorm.ro_same rsegs (ms_mem s) (ms_mem s') -> SRcf B (mkCfg s' md) R) ->
  SRcf B (mkCfg s md) R.
Proof.
  intros P Q s md R HE (s0 & HP & Hrel) HRO Hh Hl K.
  eapply evt_SRcf_r; [eapply MemNorm.evt_rel; [apply wx_apart_rsegs | exact Hrel | exact (HE s0 HP)] | exact Hh | exact Hl |].
  intros s' (s0' & HQ & Hrel' & Hsame). apply K; [exists s0'; split; assumption | exact Hsame].
Qed.

Lemma st_phase_cf : forall x W (P Q : machine_state -> Prop) s L A md b (R : config -> Prop),
  x_S x = S0 -> alloc_ceiling + SLOT_STACK <= S0 -> S0 <= 2 ^ 47 -> x_F x = fp_regs -> x_fc x = fp_csr ->
  St x s L A md b -> norm_at P s ->
  (forall s0, P s0 -> Exec.evt rsegs (fun s0' => kept x W s0 s0' /\ Q s0') s0) ->
  (forall s1, Q s1 -> ms_fregs s1 = x_F x /\ ms_fcsr s1 = x_fc x) ->
  (forall lo hi, In (lo, hi) W -> own_ok L A lo hi) ->
  (forall s', St x s' L A md b -> norm_at Q s' -> SRcf B (mkCfg s' md) R) ->
  SRcf B (mkCfg s md) R.
Proof.
  intros x W P Q s L A md b R HS HSc HS47 HF HFC (RO & Hfr & Hfc & AS & ER & PB & RL) (s0 & HP & Hrel) HE HQF HW K.
  pose proof (aa_laws API) as LAWS.
  destruct AS as (MR & WF & BD & INI & RES).
  destruct (mr_model B _ LAWS L A (ms_mem s) md MR) as (Hh & Hl & _).
  apply (phase_SRcf (fun s1 => P s1 /\ MemNorm.ms_rel rsegs s s1)
                    (fun s1' => exists s1, MemNorm.ms_rel rsegs s s1 /\ kept x W s1 s1' /\ Q s1') s md R).
  - intros s1 (HP1 & Hr1). eapply Exec.evt_mono; [exact (HE s1 HP1)|].
    intros s1' (Hk & HQ). exists s1. split; [exact Hr1 | split; assumption].
  - exists s0. split; [split; assumption | exact Hrel].
  - exact RO.
  - exact Hh.
  - exact Hl.
  - intros s' (s0' & (s1 & Hr1 & Hk & HQ) & Hr') Hsame.
    destruct (rel0_phase x W s s1 s0' s' L A md RL MR Hr1 Hr' Hsame Hk HS HSc HS47 HW) as (RL' & MR' & WM').
    apply K; [| exists s0'; split; assumption].
    split; [exact (MemNorm.ro_agree_same rsegs _ _ RO Hsame)|].
    destruct Hr' as (_ & Hf' & _ & _ & _ & Hc' & _ & _).
    destruct (HQF s0' HQ) as (Hq1 & Hq2).
    split; [rewrite Hf', Hq1; exact HF|].
    split; [rewrite Hc', Hq2; exact HFC|].
    split; [split; [exact MR' | split; [exact WF | split; [exact BD | split; [exact INI | exact RES]]]]|].
    split; [intros a Ha; pose proof (ER a Ha) as E1; unfold YP09.writable_at in *; rewrite HB in *;
            apply WM'; exact E1|].
    split; [exact PB | exact RL'].
Qed.

Section PathCf.
Variables (pl : list byte) (b0 : sbound).
Hypotheses (HEAD : seg_head) (INIT : seg_init) (NSET : seg_nset) (STURN : seg_set_turn)
  (UENT : seg_unset_enter) (UTURN : seg_unset_turn) (ADMIT : seg_admit) (SWEEP : seg_sweep) (RAW : seg_raw)
  (RAWSW : seg_rawsweep) (SSETUP : seg_sched_setup) (SCHED : seg_sched_turn) (EPI : seg_epilogue).
Hypotheses (GMT : seg_mallocT_cf B API) (GM1 : seg_mallocSW1_cf B API) (GM2 : seg_mallocSW2_cf B API)
  (GF1 : seg_freeSW1_cf B API) (GF2 : seg_freeSW2_cf B API) (GFT : seg_freeT_cf B API).
Hypotheses (STM : st_malloc_ok) (STF : st_free_ok).
Hypotheses (UB : unit_binding B) (HTP : x_tp (xent pl) = w64 (ms_tp B)) (ROW : row_off).
Hypotheses (HSc : alloc_ceiling + SLOT_STACK <= S0) (HS47 : S0 <= 2 ^ 47).

(* The room facts: the frame's budget law on the allocator relation, and the entry bound. *)
Hypothesis LIMLAW_AG : forall L A mem md, aa_MR API L A mem md -> 2 ^ 34 <= vm_limit (m_vmmaps md).
Hypothesis RB0 : sb_live b0 <= 64 /\ 0 <= sb_bytes b0 <= 2 ^ 28 /\ 128 <= sb_cap b0 <= CAP_AG.

Local Abbreviation b1 := (SlotIntegration.b1 b0).
Local Abbreviation res_end := (SlotIntegration.res_end b0).

Variable R : config -> Prop.
Hypothesis K : forall s L A md b, St (xent pl) s L A md b -> norm_at (Ep (xent pl)) s -> res_end b -> R (mkCfg s md).

Let x := xent pl.

Lemma st_lim : forall s L A md b, St x s L A md b -> 2 ^ 34 <= vm_limit (m_vmmaps md).
Proof. intros s L A md b (_ & _ & _ & (MR & _) & _). exact (LIMLAW_AG _ _ _ _ MR). Qed.

Lemma RTc : forall md, 2 ^ 34 <= vm_limit (m_vmmaps md) -> room_cf md b0 460.
Proof. intros md Hv. destruct RB0 as (H1 & H2 & H3). apply (room_cf_of md b0 460 0); lia. Qed.

Lemma R1c : forall md, 2 ^ 34 <= vm_limit (m_vmmaps md) -> room_cf md b1 (sw1_size x).
Proof.
  intros md Hv. destruct RB0 as (H1 & H2 & H3). pose proof (sw1_rng x).
  apply (room_cf_of md _ _ 1); unfold SlotIntegration.b1, sb_malloc; cbn [sb_live sb_bytes sb_cap]; lia.
Qed.

Lemma R2c : forall md, 2 ^ 34 <= vm_limit (m_vmmaps md) -> room_cf md b1 4352.
Proof.
  intros md Hv. destruct RB0 as (H1 & H2 & H3).
  apply (room_cf_of md _ _ 1); unfold SlotIntegration.b1, sb_malloc; cbn [sb_live sb_bytes sb_cap]; lia.
Qed.

Lemma HSxc : x_S x = S0. Proof. reflexivity. Qed.
Lemma HSTc : alloc_ceiling + LLVM_STACK <= x_S x.
Proof. rewrite HSxc. unfold LLVM_STACK, LLVM_FRAME, YO0d.ALLOC_STACK, SLOT_STACK in *. lia. Qed.
Lemma HSPLc : 0 <= SPL x < 2 ^ 64.
Proof. unfold SPL, LLVM_FRAME. rewrite HSxc. pose proof alloc_ceiling_value as (Hc & _). unfold SLOT_STACK in *. lia. Qed.

Lemma sp_bodyc : forall pc (P : machine_state -> Prop) s, (forall s0, P s0 -> body x pc s0) -> norm_at P s ->
  spZ (ms_regs s) = S0 - LLVM_FRAME.
Proof.
  intros pc P s HP N. rewrite (sp_of x P s (fun s0 H => body_sp _ _ _ (HP s0 H)) HSPLc N). unfold SPL. rewrite HSxc.
  reflexivity.
Qed.

(* Epilogue: from At_ret0 to the return. *)
Lemma path_epi_cf : forall s L A md b, res_end b -> St x s L A md b -> norm_at (At_ret0 x) s -> SRcf B (mkCfg s md) R.
Proof.
  intros s L A md b Hb S1 N1.
  apply (st_phase_cf x [] (At_ret0 x) (Ep x) s L A md b R HSxc HSc HS47 eq_refl eq_refl S1 N1).
  - intros s0 H0. eapply Exec.evt_mono; [exact (EPI x s0 H0)|].
    intros s0' (Hm & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12). split.
    + apply kept_of_mem. exact Hm.
    + repeat split; assumption.
  - intros s1 (_ & HF & HC & _). split; assumption.
  - intros lo hi [].
  - intros s' S' N'. apply SRcf_ret. exact (K s' L A md b S' N' Hb).
Qed.

Ltac to_bodyc H :=
  repeat match type of H with
  | body _ _ _ => fail 1
  | _ /\ _ => destruct H as [H _]
  | _ \/ _ => destruct H as [H|H]
  | _ => progress unfold At_ret0, At_mallocT, At_mallocT_ret, At_mallocSW1, At_mallocSW1_ret, At_freeSW1,
           At_raw, At_mallocSW2, At_mallocSW2_ret, At_freeSW2, At_freeSW2_ret, At_freeT, at_after_admit in H
  end.

Ltac frqc := let s1 := fresh "s1" in let Hq := fresh "Hq" in
  intros s1 Hq; to_bodyc Hq; exact (body_fr _ _ _ Hq).
Ltac frq2c := let s1 := fresh "s1" in let Hq := fresh "Hq" in
  intros s1 [[_ Hq] | [_ Hq]]; to_bodyc Hq; exact (body_fr _ _ _ Hq).

Ltac stc_go W P Q := eapply (st_phase_cf x W P Q);
  [exact HSxc | exact HSc | exact HS47 | reflexivity | reflexivity | eassumption | eassumption | | | |].

Lemma path_freeT_cf : forall s L A md b t, res_end (sb_free b 460) -> St x s L A md b -> own_ok L A t (t + 460) ->
  norm_at (At_freeT x t) s -> SRcf B (mkCfg s md) R.
Proof.
  intros s L A md b t Hb S1 Ot N1.
  destruct (own_live L A t 460 Ot) as (q & Hq & Hp).
  apply (SRcf_bind B _ (fpost x no_live t 460 (At_ret0 x) s md L A b q)).
  - exact (GFT x t HSTc s md L A b q (glue_pre_of x _ s md L A b UB HTP ROW S1 N1) I Hq Hp).
  - intros c' Hc.
    destruct (STF x no_live t 460 (At_ret0 x) s md L A b q [] c' HSxc
                (sp_bodyc _ (At_freeT x t) s (fun s0 H => proj1 H) N1) HSc HS47 S1 ltac:(lia) Ot Hq Hp
                (fun lo hi H => match H with end) Hc) as (s' & md' & L' & A' & -> & N' & S' & _ & _).
    exact (path_epi_cf s' L' A' md' (sb_free b 460) Hb S' N').
Qed.

Lemma path_E5_cf : forall s L A md b t, res_end (sb_free b 460) -> St x s L A md b -> own_ok L A t (t + 460) ->
  norm_at (At_freeSW2_ret x t) s -> SRcf B (mkCfg s md) R.
Proof.
  intros s L A md b t Hb S1 Ot N1.
  stc_go [(t, t + 460)] (At_freeSW2_ret x t) (At_freeT x t).
  - intros s0 H0. exact (phase_E5 SSETUP SCHED x t s0 H0).
  - frqc.
  - intros lo hi [E|[]]. inversion E; subst. exact Ot.
  - intros s' S' N'. exact (path_freeT_cf s' L A md b t Hb S' Ot N').
Qed.

Lemma path_freeSW2_cf : forall s L A md b t sw, res_end (sb_free (sb_free b 4352) 460) -> St x s L A md b ->
  own_ok L A t (t + 460) -> own_ok L A sw (sw + 4352) -> norm_at (At_freeSW2 x t sw) s -> SRcf B (mkCfg s md) R.
Proof.
  intros s L A md b t sw Hb S1 Ot Os N1.
  destruct (own_live L A sw 4352 Os) as (q & Hq & Hp).
  assert (OW : forall lo hi, In (lo, hi) [(t, t + 460)] -> own_ok L A lo hi /\ hi - lo <> 4352)
    by (intros lo hi [E|[]]; inversion E; subst; split; [exact Ot | lia]).
  apply (SRcf_bind B _ (fpost x (fun L A => live_blk L A t 460) sw 4352 (At_freeSW2_ret x t) s md L A b q)).
  - exact (GF2 x t sw HSTc s md L A b q (glue_pre_of x _ s md L A b UB HTP ROW S1 N1) (own_live' L A t 460 Ot)
             Hq Hp).
  - intros c' Hc.
    destruct (STF x (fun L A => live_blk L A t 460) sw 4352 (At_freeSW2_ret x t) s md L A b q [(t, t + 460)] c' HSxc
                (sp_bodyc _ (At_freeSW2 x t sw) s (fun s0 H => proj1 H) N1) HSc HS47 S1 ltac:(lia) Os Hq Hp
                OW Hc)
      as (s' & md' & L' & A' & -> & N' & S' & _ & Own').
    exact (path_E5_cf s' L' A' md' (sb_free b 4352) t Hb S' (Own' t (t + 460) (or_introl eq_refl)) N').
Qed.

Lemma path_SW2ret_cf : forall s L A md b t sw, res_end (sb_free (sb_free b 4352) 460) -> St x s L A md b ->
  own_ok L A t (t + 460) -> own_ok L A sw (sw + 4352) -> norm_at (At_mallocSW2_ret x t sw) s ->
  SRcf B (mkCfg s md) R.
Proof.
  intros s L A md b t sw Hb S1 Ot Os N1.
  stc_go [(sw, sw + 4352)] (At_mallocSW2_ret x t sw) (At_freeSW2 x t sw).
  - intros s0 H0. exact (RAWSW x t sw s0 H0).
  - frqc.
  - intros lo hi [E|[]]. inversion E; subst. exact Os.
  - intros s' S' N'. exact (path_freeSW2_cf s' L A md b t sw Hb S' Ot Os N').
Qed.

Lemma path_mallocSW2_cf : forall s L A md t, St x s L A md b1 ->
  own_ok L A t (t + 460) -> norm_at (At_mallocSW2 x t) s -> SRcf B (mkCfg s md) R.
Proof.
  intros s L A md t S1 Ot N1.
  assert (OW : forall lo hi, In (lo, hi) [(t, t + 460)] -> own_ok L A lo hi)
    by (intros lo hi [E|[]]; inversion E; subst; exact Ot).
  apply (SRcf_bind B _ (mpost x (fun L A => live_blk L A t 460) 4352 (fun s => At_mallocSW2_ret x t s) s md L A b1)).
  - exact (GM2 x t HSTc s md L A b1 (glue_pre_of x _ s md L A b1 UB HTP ROW S1 N1) (own_live' L A t 460 Ot)
             (R2c md (st_lim s L A md b1 S1))).
  - intros c' Hc.
    destruct (STM x (fun L A => live_blk L A t 460) 4352 (fun s => At_mallocSW2_ret x t s) s md L A b1
                [(t, t + 460)] c' HSxc (sp_bodyc _ (At_mallocSW2 x t) s (fun s0 H => proj1 H) N1) HSc HS47 S1
                OW Hc)
      as (s' & md' & L' & A' & sw & -> & N' & S' & _ & Osw & Own').
    apply (path_SW2ret_cf s' L' A' md' (sb_malloc b1 4352) t sw); [| exact S' | exact (Own' t (t + 460) (or_introl eq_refl)) |
           exact Osw | exact N'].
    unfold SlotIntegration.res_end, SlotIntegration.b1. rewrite !sb_free_malloc. reflexivity.
Qed.

Lemma path_raw_cf : forall s L A md t pc, St x s L A md b1 ->
  own_ok L A t (t + 460) -> norm_at (At_raw x t pc) s -> SRcf B (mkCfg s md) R.
Proof.
  intros s L A md t pc S1 Ot N1.
  stc_go (@nil (Z * Z)) (At_raw x t pc) (At_mallocSW2 x t).
  - intros s0 H0. exact (RAW x t pc s0 H0).
  - frqc.
  - intros lo hi [].
  - intros s' S' N'. exact (path_mallocSW2_cf s' L A md t S' Ot N').
Qed.

Lemma sw1_nec : 460 <> sw1_size x.
Proof. unfold sw1_size. pose proof (Z.le_max_r (h_rows (hd x)) 1). lia. Qed.

Lemma path_freeSW1_cf : forall s L A md t sw, St x s L A md (sb_malloc b1 (sw1_size x)) ->
  own_ok L A t (t + 460) -> own_ok L A sw (sw + sw1_size x) -> norm_at (At_freeSW1 x t sw) s ->
  SRcf B (mkCfg s md) R.
Proof.
  intros s L A md t sw S1 Ot Os N1.
  destruct (own_live L A sw (sw1_size x) Os) as (q & Hq & Hp).
  assert (Hpos : 0 < sw1_size x) by (unfold sw1_size; pose proof (Z.le_max_r (h_rows (hd x)) 1); lia).
  assert (OW : forall lo hi, In (lo, hi) [(t, t + 460)] -> own_ok L A lo hi /\ hi - lo <> sw1_size x)
    by (intros lo hi [E|[]]; inversion E; subst; split; [exact Ot | pose proof sw1_nec; lia]).
  apply (SRcf_bind B _ (fpost x (fun L A => live_blk L A t 460) sw (sw1_size x) (At_raw x t PC_FREE_SW1_RET)
                          s md L A (sb_malloc b1 (sw1_size x)) q)).
  - exact (GF1 x t sw HSTc s md L A (sb_malloc b1 (sw1_size x)) q
             (glue_pre_of x _ s md L A _ UB HTP ROW S1 N1) (own_live' L A t 460 Ot) Hq Hp).
  - intros c' Hc.
    destruct (STF x (fun L A => live_blk L A t 460) sw (sw1_size x) (At_raw x t PC_FREE_SW1_RET) s md L A
                (sb_malloc b1 (sw1_size x)) q [(t, t + 460)] c' HSxc
                (sp_bodyc _ (At_freeSW1 x t sw) s (fun s0 H => proj1 (proj1 H)) N1) HSc HS47 S1 Hpos Os Hq Hp
                OW Hc)
      as (s' & md' & L' & A' & -> & N' & S' & _ & Own').
    rewrite sb_free_malloc in S'.
    exact (path_raw_cf s' L' A' md' t PC_FREE_SW1_RET S' (Own' t (t + 460) (or_introl eq_refl)) N').
Qed.

Lemma path_SW1ret_cf : forall s L A md t sw, St x s L A md (sb_malloc b1 (sw1_size x)) ->
  own_ok L A t (t + 460) -> own_ok L A sw (sw + sw1_size x) -> norm_at (At_mallocSW1_ret x t sw) s ->
  SRcf B (mkCfg s md) R.
Proof.
  intros s L A md t sw S1 Ot Os N1.
  stc_go [(sw, sw + sw1_size x)] (At_mallocSW1_ret x t sw) (At_freeSW1 x t sw).
  - intros s0 H0. exact (SWEEP x t sw s0 H0).
  - frqc.
  - intros lo hi [E|[]]. inversion E; subst. exact Os.
  - intros s' S' N'. exact (path_freeSW1_cf s' L A md t sw S' Ot Os N').
Qed.

Lemma path_mallocSW1_cf : forall s L A md t, St x s L A md b1 -> own_ok L A t (t + 460) ->
  norm_at (At_mallocSW1 x t) s -> SRcf B (mkCfg s md) R.
Proof.
  intros s L A md t S1 Ot N1.
  assert (OW : forall lo hi, In (lo, hi) [(t, t + 460)] -> own_ok L A lo hi)
    by (intros lo hi [E|[]]; inversion E; subst; exact Ot).
  apply (SRcf_bind B _ (mpost x (fun L A => live_blk L A t 460) (sw1_size x) (fun s => At_mallocSW1_ret x t s)
                          s md L A b1)).
  - exact (GM1 x t HSTc s md L A b1 (glue_pre_of x _ s md L A b1 UB HTP ROW S1 N1) (own_live' L A t 460 Ot)
             (R1c md (st_lim s L A md b1 S1))).
  - intros c' Hc.
    destruct (STM x (fun L A => live_blk L A t 460) (sw1_size x) (fun s => At_mallocSW1_ret x t s) s md L A b1
                [(t, t + 460)] c' HSxc (sp_bodyc _ (At_mallocSW1 x t) s (fun s0 H => proj1 (proj1 H)) N1) HSc HS47
                S1 OW Hc)
      as (s' & md' & L' & A' & sw & -> & N' & S' & _ & Osw & Own').
    exact (path_SW1ret_cf s' L' A' md' t sw S' (Own' t (t + 460) (or_introl eq_refl)) Osw N').
Qed.

Lemma path_E1_cf : forall s L A md t, St x s L A md b1 -> own_ok L A t (t + 460) ->
  norm_at (At_mallocT_ret x t) s -> SRcf B (mkCfg s md) R.
Proof.
  intros s L A md t S1 Ot N1.
  stc_go [(t, t + 460)] (At_mallocT_ret x t)
    (fun s0 => (ok (x_pl x) = true /\ At_mallocSW1 x t s0) \/ (ok (x_pl x) = false /\ At_raw x t PC_RAW_NOK s0)).
  - intros s0 H0. exact (phase_E1 INIT NSET STURN UENT UTURN ADMIT x t s0 H0).
  - frq2c.
  - intros lo hi [E|[]]. inversion E; subst. exact Ot.
  - intros s' S' (s0' & [[_ H1] | [_ H1]] & Hr).
    + exact (path_mallocSW1_cf s' L A md t S' Ot (ex_intro _ s0' (conj H1 Hr))).
    + exact (path_raw_cf s' L A md t PC_RAW_NOK S' Ot (ex_intro _ s0' (conj H1 Hr))).
Qed.

Lemma path_mallocT_cf : forall s, St x s L0 A0 md0 b0 -> norm_at (At_mallocT x) s -> SRcf B (mkCfg s md0) R.
Proof.
  intros s S1 N1.
  apply (SRcf_bind B _ (mpost x no_live 460 (fun t => At_mallocT_ret x t) s md0 L0 A0 b0)).
  - exact (GMT x HSTc s md0 L0 A0 b0 (glue_pre_of x _ s md0 L0 A0 b0 UB HTP ROW S1 N1) I
             (RTc md0 (st_lim s L0 A0 md0 b0 S1))).
  - intros c' Hc.
    destruct (STM x no_live 460 (fun t => At_mallocT_ret x t) s md0 L0 A0 b0 [] c' HSxc
                (sp_bodyc _ (At_mallocT x) s (fun s0 H => proj1 H) N1) HSc HS47 S1
                (fun lo hi H => match H with end) Hc)
      as (s' & md' & L' & A' & t & -> & N' & S' & _ & Ot & _).
    exact (path_E1_cf s' L' A' md' t S' Ot N').
Qed.

Theorem path_all_cf : forall se, St x se L0 A0 md0 b0 -> norm_at (At_entry x) se -> SRcf B (mkCfg se md0) R.
Proof.
  intros se S1 N1.
  stc_go (@nil (Z * Z)) (At_entry x)
    (fun s0 => (2 ^ 26 <= x_n x /\ At_ret0 x s0) \/ (x_n x < 2 ^ 26 /\ At_mallocT x s0)).
  - intros s0 H0. exact (HEAD x s0 H0).
  - frq2c.
  - intros lo hi [].
  - intros s' S' (s0' & [[_ H1] | [_ H1]] & Hr).
    + exact (path_epi_cf s' L0 A0 md0 b0 eq_refl S' (ex_intro _ s0' (conj H1 Hr))).
    + exact (path_mallocT_cf s' S' (ex_intro _ s0' (conj H1 Hr))).
Qed.

End PathCf.
End ChainCf.
