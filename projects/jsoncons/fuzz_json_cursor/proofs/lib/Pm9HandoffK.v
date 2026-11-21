(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the reserved-interval ledger, the launch input's kernel build): changed AH, M_KSPACE, M_PTRARR and 12 more; added Hapc, Hbrk, Hfit and 22 more; internal commit ids in comments replaced by public commits or removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AgentLib BackingAlgebra AsanPlacement AsanCeil AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm9DefsK Pm9PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK ArtRuns ArtBridge.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.

(* the fresh indices are the regenerated HS_0/HS_1's: KSPACE 224 -> 228, PTRARR 250 -> 254
   (a build round; same in all eight states).  Lengths unchanged. *)
Definition M_KSPACE : amap := {| am_base := EMd M_MUL (ELit 4096) (EVar 228); am_len := ELit 0x2000011000; am_kind := KRW |}.
Definition M_PTRARR : amap := {| am_base := EMd M_MUL (ELit 4096) (EVar 254); am_len := ELit 0x800000; am_kind := KNONELAZY |}.
Definition RESm0 : list amap := [M_KSPACE; M_PTRARR].

Definition as0_chk (cs : acs) : bool :=
  (no_fog (a_maps cs) && hops_in_maps (a_maps cs) (a_hna cs) && hops_in_maps (a_maps cs) (a_hlz cs)
   && forallb (vis_sh_wr ASAN0 (kn cs)) (a_vis cs) && forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs)
   && existsb (amap_eqb M_LOW) (a_maps cs) && existsb (amap_eqb M_GAP) (a_maps cs) && existsb (amap_eqb M_HIGH) (a_maps cs)
   && forallb (fun m => existsb (amap_eqb m) (a_maps cs)) RESm0
   && forallb (fun m => match xlo (kn cs) (am_base m) with Some lo => Z.ltb 0 lo | None => false end) RESm0)%bool.

Lemma asan0_resv_pos : forall b s, In (b, s) (segments_reserved ASEGS0) -> 0 < bv_unsigned s.
Proof.
  intros b s H. rewrite asan0_res_eq in H.
  destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <-; rewrite u64_lit by lia; lia.
Qed.

Section As0Handoff.
  (* THE SECTION'S PARAMETERS, old beside new: as Pm8HandoffK (its twin).
       OLD  sp brk0 rdraw argv envp uid hw fs, with Hsp Hva;
            SINV0 APH0 sp rdraw brk0 argv envp uid hw, argH0 APH0 sp rdraw argv envp uid hw.
       NEW  the launch's whole input, in [HandoffBridgeK]'s Section Image order. *)
  Variables (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)).
  Variables (ifs : Fs.Fs) (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue).
  Variables (nofile sigmask : word) (abrt : bool) (urnd : InputStream) (tmp0 : Fs.Fs).
  Variables (kb : KernelBuild) (execfn : list byte) (sdf : bool) (apc : N) (fs : Fs.Fs).
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk ASEGS0 brk0.
  Hypothesis Hmb : valid_mmap_base mbase.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hhw : valid_hwcap hw.
  Hypothesis Hapc : Z.of_N apc = a_entry ASAN0.
  #[local] Notation INP := (AsanInitK.inp argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  Hypothesis Hlaunch : valid_launch INP.
  Hypothesis Hlau : entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw) INP.
  #[local] Notation SINV := (SINV0 APH0 sp rdraw brk0 mbase argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc).
  #[local] Notation argH := (argH0 sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf).
  #[local] Notation CSOK := (cs_ok ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs).
  Let AH := argH0_high sp rdraw argv envp ifs stdin uid gid hw groups net nofile sigmask abrt urnd tmp0 kb execfn sdf apc Hsp Hva.

  Variables BUDGET LENMAX KMAX : Z.
  Hypothesis BUD : 0 <= BUDGET /\ 0 <= KMAX /\ 0 <= LENMAX < 2 ^ 62.
  Variable EXTRA : list (Z * Z).
  Hypothesis EXTRA_wf : A_wf EXTRA.

  Variable cs : acs.
  Hypothesis CHK : as0_chk cs = true.
  Hypothesis BUD_le : a_eager cs + a_abytes cs + A_bytes EXTRA + BUDGET <= AsanInitK.LIMIT.
  (* STATEMENT CHANGED, old beside new: the reserved count the bridge's gap obligation
     takes now includes the launch's vDSO/vvar pair.
       OLD  Z.of_nat (length (segments_reserved ASEGS0) + length (a_maps cs))
       NEW  Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs))
     This is HandoffBInvK's own Hypothesis GAP at 75d69e00 (HandoffBInvK.v:79-80), which
     [hb_bridge_static] below is applied to positionally. *)
  Hypothesis GAP : AsanCeil.bottomup_floor + LENMAX + (a_totsz cs + BUDGET)
                   + (Z.of_nat (length (segments_reserved ASEGS0) + n_resx ASAN0 + length (a_maps cs)) + KMAX) * (LENMAX + 4095) <= AsanCeil.alloc_ceiling.

  Lemma as0_chk_parts :
    no_fog (a_maps cs) = true /\ hops_in_maps (a_maps cs) (a_hna cs) = true /\ hops_in_maps (a_maps cs) (a_hlz cs) = true
    /\ forallb (vis_sh_wr ASAN0 (kn cs)) (a_vis cs) = true /\ forallb (vis_off_band (kn cs)) (a_vis cs ++ a_ghost cs) = true
    /\ In M_LOW (a_maps cs) /\ In M_GAP (a_maps cs) /\ In M_HIGH (a_maps cs)
    /\ (forall m, In m RESm0 -> In m (a_maps cs))
    /\ (forall m, In m RESm0 -> exists lo, xlo (kn cs) (am_base m) = Some lo /\ 0 < lo).
  Proof.
    unfold as0_chk in CHK. repeat (apply andb_prop in CHK as [CHK ?]).
    repeat split; try assumption; try (apply hl_in_amapb; assumption).
    - intros m Hm. apply hl_in_amapb. exact (proj1 (forallb_forall _ _) H0 m Hm).
    - intros m Hm. pose proof (proj1 (forallb_forall _ _) H m Hm) as Hx. cbn beta in Hx.
      destruct (xlo (kn cs) (am_base m)) as [lo|]; [|discriminate]. exists lo. split; [reflexivity | apply Z.ltb_lt; exact Hx].
  Qed.

  Definition as0_RES (E : env) : list (Z * Z) := RES_of RESm0 E.
  Definition as0_BASE : Z := BASE_of cs EXTRA.
  Definition as0_A0 (E : env) : list (Z * Z) := A0_of ASAN0 cs EXTRA E.

  Theorem as0_bridge_static : forall E R FULL model, CSOK E cs R FULL model ->
    bridge_static ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model)) (as0_RES E)
                  (uE E e_sp0 - 8388608) BUDGET LENMAX KMAX.
  Proof.
    intros E R FULL model HC. destruct as0_chk_parts as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    exact (hb_bridge_static ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok ltac:(cbn; unfold SHB_LO; lia) asan0_res_hull asan0_resv_pos
             cs C1 C6 C7 C8 RESm0 C9 C10 BUDGET LENMAX KMAX BUD GAP E R FULL model HC).
  Qed.

  Theorem as0_binv_main : forall E R FULL model, CSOK E cs R FULL model ->
    BInv ASEGS0 (vm_maps (m_vmmaps model)) (vm_reserved (m_vmmaps model)) (vm_noaccess (m_vmmaps model))
         (uE E e_sp0 - 8388608) as0_BASE BUDGET [] (as0_A0 E) FULL model.
  Proof.
    intros E R FULL model HC. destruct as0_chk_parts as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    exact (hb_binv_main ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs asan0_in_hull asan0_hull_ok asan0_shadow_ok AH ltac:(cbn; unfold SHB_LO; lia)
             cs C1 C2 C3 C4 C5 C6 C8 BUDGET LENMAX KMAX BUD EXTRA EXTRA_wf BUD_le E R FULL model HC).
  Qed.
End As0Handoff.
