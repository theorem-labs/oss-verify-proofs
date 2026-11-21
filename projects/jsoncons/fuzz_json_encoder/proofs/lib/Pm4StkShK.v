(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition left free, the launch input's kernel build): changed SINV, argH, argv and 13 more; added Hapc, Hbrk, Hhw and 24 more; taken in part from projects/jsoncons/fuzz_json_cursor/proofs/lib/Pm8StkShK.v, 49 lines within its lines 17-161. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import AsanAcct.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AgentLib AxSymExec3K AxSymExec3SoundK AxSymRun3K
  AsanPlanCoreK AsanPlanK AsanPlanSoundK AsanInitK Pm4DefsK Pm4PlanImagesK HandoffBridgeK HandoffLedgerK HandoffBInvK HandoffCellsK HandoffRolesK
  Pm4HandoffK Pm4HSK_0 Pm4HSK_1 Pm4MainTableK Pm4HandoffInstK Pm4ArtHandoffK Pm4ArtHandoffInstK.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import HeapIface HeapIfaceA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AxSymExec3K.AX2K AxSymExec3SoundK.AX2SK AsanPlanK.APK AsanPlanSoundK.APSK.
Open Scope Z_scope.
Local Ltac vmc_refl := first [ lazymatch goal with |- _ = ?b => vm_cast_no_check (@eq_refl _ b) end | vm_compute; reflexivity ].
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition E_SHB : expr := EAlu ALU_ADD (EMd M_MUL (ELit 4096) (EVar 0)) (EMd M_MUL (ELit 512) (EVar 10)).
Definition E_SHL : expr := EAlu ALU_ADD (EAlu ALU_ADD (EMd M_MUL (ELit (-4096)) (EVar 0)) (EMd M_MUL (ELit (-512)) (EVar 10))) (ELit 17592187092992).
Definition K_STKSH : kentry := KZero (SA E_SHB 2146402304) E_SHL.

Definition stksh_chk (cs : acs) : bool :=
  let k := kn cs in (existsb (kentry_eqb K_STKSH) k && lin_nowrapR k E_SHB && lin_nowrapR k E_SHL)%bool.

(* STATEMENT CHANGED: the hand-off states are indexed by the run's CONFIG_RSEQ flag
   (OLD HS_0 / HS_1, NEW HS_0 b / HS_1 b; see Pm4HandoffInstK). *)
Lemma stksh_chk_0 : forall b, stksh_chk (HS_0 b) = true.   Proof. intros [|]; vmc_refl. Qed.
Lemma stksh_chk_1 : forall b, stksh_chk (HS_1 b) = true.   Proof. intros [|]; vmc_refl. Qed.

(* THE SECTION'S PARAMETERS, old beside new.
     OLD  sp brk0 rdraw argv envp uid hw fs, with Hsp Hva Hve Hfit; the two closing
          theorems quantified those eight and four positionally.
     NEW  the launch's whole input in [HandoffBridgeK]'s Section Image order ([ifs] the
          input's filesystem, [fs] the plan's FS0).  [hbi_sp0] (HandoffBridgeK Section
          Image) and [geo_stk] (Pm4ArtHandoffInstK Section Geo) are generalised over only
          what their proofs read, so they are called by [eapply ...; sec]; the closing
          theorems are now Section theorems, and consumers call them the same way. *)
Section StkSh.
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
  #[local] Notation usp := (bv_unsigned sp).
  Local Ltac sec := first [ eassumption | exact asan0_in_hull | exact asan0_hull_ok | exact asan0_img_facts ].

  Section One.
  Variable cs : acs.
  Hypothesis SCHK : stksh_chk cs = true.
  Hypothesis GCHK : geo_chk cs = true.
  Variables (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis HC : CSOK E cs R FULL model.

  Ltac LINEQS e H :=
    let Hn := fresh in
    assert (Hn : lin_nowrapR (kn cs) e = true)
      by (let G := fresh in pose proof SCHK as G; unfold stksh_chk in G; repeat (let X := fresh in apply andb_prop in G as [G X]); assumption);
    pose proof (hb_lin ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model e HC Hn) as H; clear Hn;
    unfold LZ in H;
    match type of H with context [lin_of ?x] => let l := eval vm_compute in (lin_of x) in change (lin_of x) with l in H end;
    cbv [AX2SK.lden AX2SK.tden fst snd AX2SK.uE] in H; cbn [edenot] in H;
    repeat match type of H with context [bv_unsigned (ev E ?n)] => change (bv_unsigned (ev E n)) with (VZ E n) in H end;
    rewrite ?Z.add_0_r in H.

  Lemma stk_sp0 : 32768 * VZ E 0 + 16 * VZ E 6 + 4096 * VZ E 10 = usp.
  Proof. eapply hbi_sp0; sec. Qed.

  Lemma stk_geo : uE E (topE cs) = uE E (botE cs) + 8388608 /\ uE E (botE cs) mod 4096 = 0
                  /\ uE E e_sp0 - 8388608 <= uE E (botE cs) + 4096 /\ uE E (botE cs) <= uE E e_sp0 - 8388608 + 4096 /\ uE E (topE cs) <= 2 ^ 47.
  Proof. eapply geo_stk; sec. Qed.

  Theorem stksh_main : forall x,
    in_shadow_of (usp - 8388608) (Z.max usp (uE E (topE cs)) - (usp - 8388608)) x -> byte_at FULL x 0.
  Proof.
    intros x Hx.
    assert (Hin : In K_STKSH (kn cs)).
    { apply hb_knb_In. pose proof SCHK as G. unfold stksh_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]). assumption. }
    destruct (hb_zero_k ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as [Hf Hz].
    unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
    remember (bv_unsigned (edenot E E_SHB)) as shb eqn:Eb. remember (bv_unsigned (edenot E E_SHL)) as shl eqn:El.
    LINEQS E_SHB L1. rewrite <- Eb in L1. LINEQS E_SHL L2. rewrite <- El in L2.
    pose proof stk_sp0 as U0.
    destruct stk_geo as (_ & _ & _ & _ & TOP).
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
    pose proof (Z.ge_le _ _ (Z.le_ge _ _ (proj1 (u64_range (ev E 6))))) as V6. change (bv_unsigned (ev E 6)) with (VZ E 6) in V6.
    unfold in_shadow_of, S, SB in Hx.
    set (mx := Z.max usp (uE E (topE cs))) in *.
    replace (usp - 8388608 + (mx - (usp - 8388608)) - 1) with (mx - 1) in Hx by ring.
    assert (D1 : shb - 1048576 <= (usp - 8388608) / 8).
    { replace (shb - 1048576) with ((8 * shb - 8388608) / 8) by (replace (8 * shb - 8388608) with ((shb - 1048576) * 8) by ring; apply Z.div_mul; lia).
      apply Z.div_le_mono; lia. }
    assert (D2 : (mx - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
    unfold byte_at. replace x with (shb + 2146402304 + (x - (shb + 2146402304))) by ring. apply Hz. lia.
  Qed.

  Theorem stksh_main_hi : forall x,
    in_shadow_of (usp - 8388608) (2 ^ 47 - (usp - 8388608)) x -> byte_at FULL x 0.
  Proof.
    intros x Hx.
    assert (Hin : In K_STKSH (kn cs)).
    { apply hb_knb_In. pose proof SCHK as G. unfold stksh_chk in G. repeat (let X := fresh in apply andb_prop in G as [G X]). assumption. }
    destruct (hb_zero_k ASEGS0 ASAN0 AsanInitK.LIMIT SINV argH fs E cs R FULL model _ _ HC Hin) as [Hf Hz].
    unfold estart, elenZ in Hz. cbn [a_base a_off] in Hz.
    remember (bv_unsigned (edenot E E_SHB)) as shb eqn:Eb. remember (bv_unsigned (edenot E E_SHL)) as shl eqn:El.
    LINEQS E_SHB L1. rewrite <- Eb in L1. LINEQS E_SHL L2. rewrite <- El in L2.
    pose proof stk_sp0 as U0.
    destruct stk_geo as (_ & _ & _ & _ & TOP).
    assert (SR : 0x7fff80000000 <= usp <= 2 ^ 47) by (destruct Hsp as (H1 & H2 & H3); unfold sp_window_lo, sp_window_hi in H1, H2; lia).
    pose proof (Z.ge_le _ _ (Z.le_ge _ _ (proj1 (u64_range (ev E 6))))) as V6. change (bv_unsigned (ev E 6)) with (VZ E 6) in V6.
    unfold in_shadow_of, S, SB in Hx.
    set (mx := 2 ^ 47) in *.
    replace (usp - 8388608 + (mx - (usp - 8388608)) - 1) with (mx - 1) in Hx by ring.
    assert (D1 : shb - 1048576 <= (usp - 8388608) / 8).
    { replace (shb - 1048576) with ((8 * shb - 8388608) / 8) by (replace (8 * shb - 8388608) with ((shb - 1048576) * 8) by ring; apply Z.div_mul; lia).
      apply Z.div_le_mono; lia. }
    assert (D2 : (mx - 1) / 8 <= (2 ^ 47 - 1) / 8) by (apply Z.div_le_mono; lia).
    change ((2 ^ 47 - 1) / 8) with 17592186044415 in D2.
    unfold byte_at. replace x with (shb + 2146402304 + (x - (shb + 2146402304))) by ring. apply Hz. lia.
  Qed.
  End One.

  (* STATEMENT CHANGED, old beside new:
       OLD  forall sp brk0 rdraw argv envp uid hw fs, valid_sp sp -> valid_argv argv ->
              valid_envp envp -> entry_stack_fits sp argv envp ->
            forall h, (h < 2)%nat -> forall E R FULL model, cs_ok .. (HSA h) .. -> ...
       NEW  over this Section's launch, and [forall b h, ... (HSA b h) ...] *)
  Theorem as0_stksh_main : forall b h, (h < 2)%nat -> forall E R FULL model,
    CSOK E (HSA b h) R FULL model ->
    forall x, in_shadow_of (bv_unsigned sp - 8388608) (Z.max (bv_unsigned sp) (APSK.uE E (topE (HSA b h))) - (bv_unsigned sp - 8388608)) x -> byte_at FULL x 0.
  Proof.
    intros b h Hh E R FULL model HC.
    destruct h as [|[|h]]; [| |lia].
    - exact (stksh_main (HS_0 b) (stksh_chk_0 b) (geo_chk_0 b) E R FULL model HC).
    - exact (stksh_main (HS_1 b) (stksh_chk_1 b) (geo_chk_1 b) E R FULL model HC).
  Qed.

  Theorem as0_stksh_main_hi : forall b h, (h < 2)%nat -> forall E R FULL model,
    CSOK E (HSA b h) R FULL model ->
    forall x, in_shadow_of (bv_unsigned sp - 8388608) (2 ^ 47 - (bv_unsigned sp - 8388608)) x -> byte_at FULL x 0.
  Proof.
    intros b h Hh E R FULL model HC.
    destruct h as [|[|h]]; [| |lia].
    - exact (stksh_main_hi (HS_0 b) (stksh_chk_0 b) (geo_chk_0 b) E R FULL model HC).
    - exact (stksh_main_hi (HS_1 b) (stksh_chk_1 b) (geo_chk_1 b) E R FULL model HC).
  Qed.
End StkSh.
