(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Lemma at0_lit8 : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_lit8 : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_lit8. exact Hc. Qed.

(* [comment removed for export] *)
Lemma jal_50f08 : forall regs mem rom,
  msteps ASEGS (mkst regs (0x50f10 : word) mem rom) (mkst (regupd regs 1 (at_ ARB 0x50f14)) (at_ ARB 0x77588) mem rom).
Proof using.
  intros regs mem rom. rewrite !ARB_lit8 by lia.
  an F_50f08 D_50f08. close_eq.
Qed.

(* [comment removed for export] *)
Definition pam_1 (M : word -> option byte) (sp stats : word) (RIz SPB c slot : Z) : word -> option byte :=
  wbytes (ps_frame M (at_ sp (-64)) (Z_to_bv 64 0x50f10) (Z_to_bv 64 RIz) stats (Z_to_bv 64 (SPB + c * 2 ^ 32)) (Z_to_bv 64 (2 ^ 18))
                   (Z_to_bv 64 slot) (Z_to_bv 64 (csize c)))
         (Z_to_bv 64 (shad (Z_to_bv 64 slot))) (repeat (cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 (2 ^ 18))))).
Definition pam_2 (M : word -> option byte) (sp stats : word) (RIz SPB c slot : Z) : word -> option byte :=
  wbytes (wbytes (pam_1 M sp stats RIz SPB c slot) (at_ (at_ sp (-64)) (-8)) (LE8 (at_ ARB 0x50f14)))
         (at_ (at_ sp (-64)) (-24)) (LE8 (at_ ARB 0x77594)).
Definition pam_3 (M : word -> option byte) (sp thr v72 v80 vst : word) (RIz SPB c slot mu : Z) : word -> option byte :=
  pf_ms (pam_2 M sp (at_ thr 2768) RIz SPB c slot) thr RIz mu v72 v80 vst.

Section AFTERMAP.
  Variables (M rom : word -> option byte) (sp thr tp gp tsdp ctxw v72 v80 vst midend : word) (cpm : byte) (RIz SPB c au mu nf T thr0 : Z).
  #[local] Abbreviation slot := (SPB + c * 2 ^ 32 + mu)%Z.
  #[local] Abbreviation stats := (at_ thr 2768).
  Variable regs : bvmap 5 word.
  Hypothesis HR : pf_regs sp RIz SPB c regs.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H9 : getr regs 9 = stats.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 slot.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (2 ^ 18).
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 slot.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 0x103f18.
  Hypothesis Hsp : (2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hc : (1 <= c <= 30)%Z.
  Hypothesis Hau : (0 <= au <= mu /\ mu + 2 ^ 18 <= 0xE0000000)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis HSPB : (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 63)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 64)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 64 /\ T mod 8 = 0)%Z.
  Hypothesis HTRI : (T + 4096 <= RIz \/ RIz + 128 <= T)%Z.
  (* [comment removed for export] *)
  Hypothesis PH : poisonH ASEGS asan_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x50f10) (at_ sp (-64)) cpm midend thr0.
  (* [comment removed for export] *)
  #[local] Abbreviation P1 := (pam_1 M sp stats RIz SPB c slot).
  #[local] Abbreviation P2 := (pam_2 M sp stats RIz SPB c slot).
  #[local] Abbreviation P3 := (pam_3 M sp thr v72 v80 vst RIz SPB c slot mu).
  Hypothesis GH : gctH ASEGS asan_gct_tab P1 (at_ (at_ sp (-64)) (-16)) tp tsdp ctxw thr.
  Hypothesis SOK_g : store_ok ASEGS P1 (at_ (at_ sp (-64)) (-8)) 8 = true.
  (* [comment removed for export] *)
  Hypothesis R_72 : rdn ASEGS P2 (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn ASEGS P2 (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis R_st : rdn ASEGS P2 (at_ thr 2792) 8 = Some (LE8 vst).
  Hypothesis R_au : rdn ASEGS P2 (Z_to_bv 64 (RIz + 32)) 8 = Some (LE8 (Z_to_bv 64 au)).
  Hypothesis R_mu : rdn ASEGS P2 (Z_to_bv 64 (RIz + 48)) 8 = Some (LE8 (Z_to_bv 64 mu)).
  Hypothesis SOK_T : store_ok ASEGS P2 thr 4096 = true.
  Hypothesis SOK_RI : store_ok ASEGS P2 (Z_to_bv 64 RIz) 128 = true.
  (* [comment removed for export] *)
  Hypothesis R_nf : rdn ASEGS P3 (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)).

  Theorem pf_after_map :
    exists r, msteps ASEGS (mkst regs (0x50ef4 : word) M rom) (mkst r (0x4ea98 : word) P3 rom)
      /\ pf_regs sp RIz SPB c r /\ getr r 1 = Z_to_bv 64 0x50f68
      /\ getr r 10 = Z_to_bv 64 0x103f18 /\ getr r 11 = Z_to_bv 64 RIz /\ getr r 12 = Z_to_bv 64 (SPB + c * 2 ^ 32)
      /\ getr r 13 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c)
      /\ getr r 9 = Z_to_bv 64 (nf + (mu + 2 ^ 18 - au) / csize c) /\ getr r 19 = Z_to_bv 64 ((mu + 2 ^ 18 - au) / csize c)
      /\ getr r 20 = Z_to_bv 64 (mu + 2 ^ 18 - au) /\ getr r 4 = tp /\ getr r 3 = gp.
  Proof using R_nf SOK_RI SOK_T R_mu R_au R_st R_80 R_72 SOK_g GH PH HTRI HT HRI HSPB Hnf Hau Hc Hsp H22 H20 H19 H10 H9 H3 H4 HR thr0 T cpm midend ctxw tsdp.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HSPB as [S1 S2]. destruct Hau as [AU1 AU2].
    destruct HT as (UT & T1 & T2 & T3).
    (* [comment removed for export] *)
    destruct (pf_mapped M rom sp RIz SPB c slot regs HR H19 H20 ltac:(lia) H10) as (r1 & RUN1 & A1 & A10 & A11 & A12 & AG1).
    assert (K1 : forall i : reg, ~ In i [1%bv; 10%bv; 11%bv; 12%bv; 14%bv] -> getr r1 i = getr regs i) by (intros i Hi; apply AG1; exact Hi).
    destruct HR as (R2 & R8 & R18 & R21).
    (* [comment removed for export] *)
    destruct (asan_poison_shadow M rom (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x50f10) (at_ sp (-64)) cpm midend thr0 r1
                PH A1 ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact R2) A10 A11 A12)
      as (r2 & RUN2 & AG2).
    assert (K2 : forall i : reg, In i [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv] -> getr r2 i = getr regs i).
    { intros i Hi. rewrite (AG2 i), K1; [reflexivity | |];
        cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [(lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); destruct Hi. }
    rewrite !K1 in RUN2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
    rewrite R8, H9, R18, H19, H20, R21 in RUN2.
    change (wbytes (ps_frame M _ _ _ _ _ _ _ _) _ _) with P1 in RUN2.
    replace (Z_to_bv 64 0x50f10 : word) with (0x50f10%bv : word) in RUN2 by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    pose proof (jal_50f08 r2 P1 rom) as RUNJ.
    assert (RETg : ret_ok (at_ ARB 0x50f14)) by (rewrite ARB_lit8 by lia; apply ret_ok_lit; [lia | reflexivity]).
    destruct (gts_run ASEGS ARB asan_HGTS ARB_ok asan_gct_tab P1 rom (regupd r2 1 (at_ ARB 0x50f14)) (at_ ARB 0x50f14) (at_ sp (-64)) tp tsdp ctxw thr
                asan_gct_tab_ok asan_GTRB GH SOK_g ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(lia) ltac:(lia) RETg
                ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity)
                ltac:(rewrite getr_other by (intros E; discriminate E); rewrite (K2 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact R2)
                ltac:(rewrite getr_other by (intros E; discriminate E); rewrite (K2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H4))
      as (r3 & RUN3 & D10 & AG3).
    change (wbytes (wbytes P1 _ _) _ _) with P2 in RUN3.
    assert (K3 : forall i : reg, In i [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv] -> getr r3 i = getr regs i).
    { intros i Hi. rewrite (AG3 i); [rewrite getr_other; [exact (K2 i Hi)|] |];
        cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [first [intros X; discriminate X | (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X]|]); destruct Hi. }
    rewrite (ARB_lit8 0x50f14) in RUN3, RUNJ by lia.
    replace (Z_to_bv 64 0x50f14 : word) with (0x50f14%bv : word) in RUN3, RUNJ by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    destruct (pf_stats P2 rom sp thr v72 v80 vst RIz SPB c au mu T r3
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold pf_regs in G in change_no_check G' end); rewrite !K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); repeat split; assumption)
                ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H9) D10
                ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H19) ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H22)
                ltac:(lia) (conj AU1 AU2) HRI (conj UT (conj T1 (conj T2 T3))) HTRI R_72 R_80 R_st R_au R_mu SOK_T SOK_RI)
      as (r4 & RUN4 & PR4 & B10 & B13 & B20 & AG4).
    change (pf_ms P2 thr RIz mu v72 v80 vst) with P3 in RUN4.
    (* [comment removed for export] *)
    destruct (pf_efs_call P3 rom sp RIz SPB c au (mu + 2 ^ 18) nf r4 PR4 B10 B13 B20 ltac:(lia) Hc ltac:(lia) Hnf HRI R_nf)
      as (r5 & RUN5 & PR5 & C1 & C10 & C11 & C12 & C13 & C9 & C19 & C20 & AG5).
    exists r5. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUNJ|].
      eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. exact RUN5.
    - repeat (split; [assumption|]).
      split.
      + rewrite (AG5 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
        rewrite (AG4 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
        rewrite (K3 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). exact H4.
      + rewrite (AG5 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
        rewrite (AG4 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
        rewrite (K3 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). exact H3.
  Qed.
End AFTERMAP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma jal_4eb4c : forall regs mem rom,
  msteps ASEGS (mkst regs (0x4eb54 : word) mem rom) (mkst (regupd regs 1 (at_ ARB 0x4eb58)) (at_ ARB 0x77588) mem rom).
Proof using.
  intros regs mem rom. rewrite !ARB_lit8 by lia.
  an F_4eb4c D_4eb4c. close_eq.
Qed.

Definition eam_1 (M : word -> option byte) (sp s4x s5x : word) (RIz slot mfa : Z) : word -> option byte :=
  wbytes (ps_frame M (at_ sp (-48)) (Z_to_bv 64 0x4eb54) (Z_to_bv 64 (mfa + 2 ^ 18)) (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 RIz) s4x s5x)
         (Z_to_bv 64 (shad (Z_to_bv 64 slot))) (repeat (cbyte (Z_to_bv 64 250)) (Z.to_nat (shlen (Z_to_bv 64 (2 ^ 18))))).
Definition eam_2 (M : word -> option byte) (sp s4x s5x : word) (RIz slot mfa : Z) : word -> option byte :=
  wbytes (wbytes (eam_1 M sp s4x s5x RIz slot mfa) (at_ (at_ sp (-48)) (-8)) (LE8 (at_ ARB 0x4eb58)))
         (at_ (at_ sp (-48)) (-24)) (LE8 (at_ ARB 0x77594)).
Definition eam_3 (M : word -> option byte) (sp s4x s5x thr v72 v80 : word) (RIz slot mfa : Z) : word -> option byte :=
  efs_ms (eam_2 M sp s4x s5x RIz slot mfa) thr RIz mfa v72 v80.

Section EFSAFTERMAP.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v s3v s4x s5x thr tp gp tsdp ctxw v72 v80 midend : word) (cpm : byte)
            (RIz slot mfa T thr0 : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-48).
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 (mfa + 2 ^ 18).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 slot.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 slot.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 (2 ^ 18).
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 RIz.
  Hypothesis H20 : getr regs 20 = s4x.
  Hypothesis H21 : getr regs 21 = s5x.
  Hypothesis Hsp : (2 ^ 32 + 4096 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hslot : (0 < slot < 2 ^ 64)%Z.
  Hypothesis Hmfa : (0 <= mfa <= 2 ^ 29)%Z.
  Hypothesis HRI : (AIMGHI <= RIz /\ RIz + 128 <= U sp - 48)%Z.
  Hypothesis HT : (U thr = T /\ 4096 <= T /\ T + 4096 <= U sp - 48 /\ T mod 8 = 0)%Z.
  Hypothesis HTRI : (T + 4096 <= RIz \/ RIz + 128 <= T)%Z.
  Hypothesis PH : poisonH ASEGS asan_poison_tab M (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4eb54) (at_ sp (-48)) cpm midend thr0.
  #[local] Abbreviation E1 := (eam_1 M sp s4x s5x RIz slot mfa).
  #[local] Abbreviation E2 := (eam_2 M sp s4x s5x RIz slot mfa).
  #[local] Abbreviation E3 := (eam_3 M sp s4x s5x thr v72 v80 RIz slot mfa).
  Hypothesis GH : gctH ASEGS asan_gct_tab E1 (at_ (at_ sp (-48)) (-16)) tp tsdp ctxw thr.
  Hypothesis SOK_g : store_ok ASEGS E1 (at_ (at_ sp (-48)) (-8)) 8 = true.
  Hypothesis R_72 : rdn ASEGS E2 (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn ASEGS E2 (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis SOK_T : store_ok ASEGS E2 thr 4096 = true.
  Hypothesis SOK_RI : store_ok ASEGS E2 (Z_to_bv 64 RIz) 128 = true.
  Hypothesis S_ra : rdn ASEGS E2 (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis S_s0 : rdn ASEGS E2 (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis S_s1 : rdn ASEGS E2 (at_ sp (-24)) 8 = Some (LE8 s1v).
  Hypothesis S_s2 : rdn ASEGS E2 (at_ sp (-32)) 8 = Some (LE8 s2v).
  Hypothesis S_s3 : rdn ASEGS E2 (at_ sp (-40)) 8 = Some (LE8 s3v).

  Theorem efs_after_map :
    exists r, msteps ASEGS (mkst regs (0x4eb38 : word) M rom) (mkst r ra E3 rom)
      /\ getr r 10 = Z_to_bv 64 1 /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4x /\ getr r 21 = s5x /\ getr r 4 = tp /\ getr r 3 = gp.
  Proof using S_s3 S_s2 S_s1 S_s0 S_ra SOK_RI SOK_T R_80 R_72 SOK_g GH PH HTRI HT HRI Hmfa Hslot Hret Hsp H21 H20 H19 H18 H10 H9 H8 H3 H4 H2 thr0 T cpm midend ctxw tsdp.
    pose proof (u64_range sp) as Hspr. destruct Hsp as [SP1 SP2]. destruct HT as (UT & T1 & T2 & T3).
    destruct (efs_mapped M rom sp slot regs H10 H9 H18 Hslot) as (r1 & RUN1 & A1 & A10 & A11 & A12 & AG1).
    assert (K1 : forall i : reg, ~ In i [1%bv; 10%bv; 11%bv; 12%bv; 14%bv] -> getr r1 i = getr regs i) by (intros i Hi; apply AG1; exact Hi).
    destruct (asan_poison_shadow M rom (Z_to_bv 64 slot) (Z_to_bv 64 (2 ^ 18)) (Z_to_bv 64 250) (Z_to_bv 64 0x4eb54) (at_ sp (-48)) cpm midend thr0 r1
                PH A1 ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); exact H2) A10 A11 A12)
      as (r2 & RUN2 & AG2).
    assert (K2 : forall i : reg, In i [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv] -> getr r2 i = getr regs i).
    { intros i Hi. rewrite (AG2 i), K1; [reflexivity | |];
        cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [(lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X|]); destruct Hi. }
    rewrite !K1 in RUN2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X).
    rewrite H8, H9, H18, H19, H20, H21 in RUN2.
    change (wbytes (ps_frame M _ _ _ _ _ _ _ _) _ _) with E1 in RUN2.
    replace (Z_to_bv 64 0x4eb54 : word) with (0x4eb54%bv : word) in RUN2 by (apply bv_eq; reflexivity).
    pose proof (jal_4eb4c r2 E1 rom) as RUNJ.
    assert (RETg : ret_ok (at_ ARB 0x4eb58)) by (rewrite ARB_lit8 by lia; apply ret_ok_lit; [lia | reflexivity]).
    destruct (gts_run ASEGS ARB asan_HGTS ARB_ok asan_gct_tab E1 rom (regupd r2 1 (at_ ARB 0x4eb58)) (at_ ARB 0x4eb58) (at_ sp (-48)) tp tsdp ctxw thr
                asan_gct_tab_ok asan_GTRB GH SOK_g ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(lia) ltac:(lia) RETg
                ltac:(rewrite getr_same by (intros E; discriminate E); reflexivity)
                ltac:(rewrite getr_other by (intros E; discriminate E); rewrite (K2 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H2)
                ltac:(rewrite getr_other by (intros E; discriminate E); rewrite (K2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H4))
      as (r3 & RUN3 & D10 & AG3).
    change (wbytes (wbytes E1 _ _) _ _) with E2 in RUN3.
    assert (K3 : forall i : reg, In i [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv] -> getr r3 i = getr regs i).
    { intros i Hi. rewrite (AG3 i); [rewrite getr_other; [exact (K2 i Hi)|] |];
        cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [first [intros X; discriminate X | (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X]|]); destruct Hi. }
    rewrite (ARB_lit8 0x4eb58) in RUN3, RUNJ by lia.
    replace (Z_to_bv 64 0x4eb58 : word) with (0x4eb58%bv : word) in RUN3, RUNJ by (apply bv_eq; reflexivity).
    destruct (efs_stats E2 rom sp ra s0v s1v s2v s3v thr v72 v80 RIz mfa T r3
                ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H2) ltac:(lia) Hret S_ra S_s0 S_s1 S_s2 S_s3 HRI (conj UT (conj T1 (conj T2 T3)))
                R_72 R_80 SOK_T SOK_RI D10
                ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H8) ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H18)
                ltac:(rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H19))
      as (r4 & RUN4 & P4).
    change (efs_ms E2 thr RIz mfa v72 v80) with E3 in RUN4.
    destruct P4 as (B10 & B2 & B1 & B8 & B9 & B18 & B19 & AG4).
    exists r4. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUNJ|].
      eapply msteps_trans; [exact RUN3|]. exact RUN4.
    - repeat (split; [assumption|]).
      split; [rewrite (AG4 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); rewrite (K3 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H20|].
      split; [rewrite (AG4 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X); rewrite (K3 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H21|].
      split.
      + rewrite (AG4 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X). rewrite (K3 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). exact H4.
      + rewrite (AG4 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X). rewrite (K3 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto). exact H3.
  Qed.
End EFSAFTERMAP.
End FPGen.
