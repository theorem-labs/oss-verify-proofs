(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbStrnlen.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section FPGen1.
Context {fx : FPState}.


Section SNL.
  Variable mem : word -> option byte.
  Variables s sp : word.
  Variable buf : list byte.
  Variables K n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mchrH mem s buf K n.
  Hypothesis HsK : (0 < bv_unsigned s + K)%Z.
  Hypothesis Hstk : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true.
  Hypothesis Hspr : (0x13058 <= bv_unsigned sp - 32)%Z.
  Hypothesis Hdisj : (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32
                      \/ bv_unsigned sp <= bv_unsigned s)%Z.

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation W8 v := (word_to_le_bytes 8 v).

  (* [comment removed for export] *)
  Definition mem1 (ra s0 s1 : word) : word -> option byte :=
    wbytes (wbytes (wbytes mem (Z_to_bv 64 (usp - 8)) (W8 ra)) (Z_to_bv 64 (usp - 16)) (W8 s0))
           (Z_to_bv 64 (usp - 24)) (W8 s1).

  Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
  Proof using. intros v. apply length_N_to_le_bytes. Qed.

  Lemma mem1_out : forall ra s0 s1 (a : word),
    (bv_unsigned a < usp - 24 \/ usp <= bv_unsigned a)%Z -> mem1 ra s0 s1 a = mem a.
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1 a Ha. pose proof (u64_range sp). unfold mem1.
    rewrite !wbytes_outside; rewrite ?lenW8; unfold in_rng; u_norm; try lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma HOK1 : forall ra s0 s1, mchrH (mem1 ra s0 s1) s buf K n.
  Proof using Hdisj Hspr HsK HOK.
    intros ra s0 s1. pose proof (u64_range sp). pose proof (u64_range s). destruct HOK. split; try assumption.
    - rewrite <- Hbuf. apply rdn_ext; [lia|]. intros x Hx. apply mem1_out. lia.
    - intros i Hi. rewrite mem1_out; [apply Hro; exact Hi | u_norm; lia].
  Qed.

  Lemma frame1 : forall ra s0 s1, frame_mod mem (mem1 ra s0 s1) [(Z_to_bv 64 (usp - 32), 32%Z)].
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1. pose proof (u64_range sp). split.
    - intros a [Ha _]. unfold in_rng in Ha. revert Ha. u_norm. intros Ha. apply mem1_out. lia.
    - unfold mem1. eapply mem_grows_trans; [| apply wbytes_grows].
      eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
  Qed.

  (* [comment removed for export] *)
  Lemma rd_ra : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 8)) 8 = Some (W8 ra).
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  Lemma rd_s0 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 16)) 8 = Some (W8 s0).
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  Lemma rd_s1 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 24)) 8 = Some (W8 s1).
  Proof using Hspr.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1. apply rdn_wbytes_hit8. u_norm. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac okstk :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
      [u_norm; lia | exact Hstk | u_norm; lia | u_norm; cbn; lia].

  Ltac kept_cs := cbv [callee_saved In]; tauto.

  (* [comment removed for export] *)
  Ltac msd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
        | gres; rwH; reflexivity
        | okstk ]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mld8 F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
          exact RD
        | apply bytes_le_to_Z_8 ]
      | step_simpl]; vnorm.

  Lemma strnlen_run : forall regs (ret : word),
    ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
    getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
    exists regs',
      msteps RSEGS (mkst regs (0x739f0 : word) mem rom)
                   (mkst regs' ret (mem1 ret (getr regs 8) (getr regs 9)) rom)
      /\ keeps_cs regs regs' /\ getr regs' 10 = Z_to_bv 64 K.
  Proof using Hdisj Hspr Hstk HsK HOK buf.
    intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs.
    pose proof (KL _ _ _ _ _ HOK) as HKL.
    destruct HOK as [Hbuf Hwin Hnw HK0 _ _ HKn Hn64 Hro].
    set (s0 := getr regs 8). set (s1 := getr regs 9).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x731b4 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 1 = (0x73a14 : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
                       /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = s
                       /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 n
                       /\ (forall x : reg, In x callee_saved -> x <> 1 -> x <> 2 -> x <> 8 -> x <> 9 -> getr r x = getr regs x))).
    { eexists. split.
      - stepiv F_7399c D_7399c (Z_to_bv 64 (usp - 32))
          ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).   (* [comment removed for export] *)
        msd F_739a0 D_739a0 (Z_to_bv 64 (usp - 8)).                 (* [comment removed for export] *)
        msd F_739a4 D_739a4 (Z_to_bv 64 (usp - 16)).                (* [comment removed for export] *)
        msd F_739a8 D_739a8 (Z_to_bv 64 (usp - 24)).                (* [comment removed for export] *)
        stepn F_739ac D_739ac.                                       (* [comment removed for export] *)
        stepn F_739b0 D_739b0.                                       (* [comment removed for export] *)
        stepn F_739b4 D_739b4.                                       (* [comment removed for export] *)
        stepn F_739b8 D_739b8.                                       (* [comment removed for export] *)
        stepn F_739bc D_739bc.                                       (* [comment removed for export] *)
        rwH. fold s0 s1. unfold mem1. pu_refl.
      - cbv beta. repeat split; gres; rwH; try reflexivity; try bveq.
        intros x Hx N1 N2 N8 N9. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [first [ exfalso; match goal with N : ?a <> ?a |- _ => apply N; reflexivity end
                 | gres; reflexivity ] |]).
        destruct Hx. }
    cbv beta. intros r1 (R1 & R2 & R8 & R9 & R10 & R11 & R12 & RK).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x73a14 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 10 = Z_to_bv 64 (bv_unsigned s + K) /\ keeps_cs r1 r)).
    { destruct (ref_memchr0 (mem1 ret s0 s1) s buf K n rom r1 (0x73a14 : word) (HOK1 ret s0 s1)
                  ltac:(apply ret_ok_even; reflexivity) R1 R10 R11 R12) as (r & RUN & KC & A10).
      exists r. split; [exact RUN | split; [exact A10 | exact KC]]. }
    cbv beta. intros r2 (A10 & KC).
    assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (KC 2) by kept_cs; exact R2).
    assert (S9 : getr r2 9 = s) by (rewrite (KC 9) by kept_cs; exact R9).
    (* [comment removed for export] *)
    eexists. split.
    - stepb_ft F_739c0 D_739c0 ltac:(rwH; apply c_eq_neq; unorm; lia).  (* [comment removed for export] *)
      stepiv F_739c4 D_739c4 (Z_to_bv 64 K)
        ltac:(gres; rwH; unfold v_sub; unorm; f_equal; lia).          (* [comment removed for export] *)
      stepn F_739c8 D_739c8.                                         (* [comment removed for export] *)
      mld8 F_739cc D_739cc ret (rd_ra ret s0 s1).                    (* [comment removed for export] *)
      mld8 F_739d0 D_739d0 s0 (rd_s0 ret s0 s1).                     (* [comment removed for export] *)
      mld8 F_739d4 D_739d4 s1 (rd_s1 ret s0 s1).                     (* [comment removed for export] *)
      stepiv F_739d8 D_739d8 sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                     (* [comment removed for export] *)
      stepret F_739dc D_739dc ret ltac:(reflexivity).
      pu_refl.
    - split.
      + intros x Hx. pose proof Hx as Hx'. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ gres; subst s0 s1; first [ symmetry; assumption | reflexivity
                  | rewrite (KC _ Hx'); apply (RK _ Hx'); intros E; discriminate E ] |]).
        destruct Hx.
      + gres. reflexivity.
  Qed.
End SNL.

Theorem ref_strnlen : forall mem (s sp : word) buf K n rom regs (ret : word),
  mchrH mem s buf K n ->
  (0 < bv_unsigned s + K)%Z ->
  store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true ->
  (0x13058 <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned s + Z.of_nat (length buf) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned s)%Z ->
  ret_ok ret -> getr regs 1 = ret -> getr regs 2 = sp ->
  getr regs 10 = s -> getr regs 11 = Z_to_bv 64 n ->
  exists regs' mem',
    msteps RSEGS (mkst regs (0x739f0 : word) mem rom) (mkst regs' ret mem' rom)
    /\ keeps_cs regs regs'
    /\ getr regs' 10 = Z_to_bv 64 K
    /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 32), 32%Z)].
Proof using.
  intros mem s sp buf K n rom regs ret HOK HsK Hstk Hspr Hdisj Hret H1 H2 H10 H11.
  destruct (strnlen_run mem s sp buf K n rom HOK HsK Hstk Hspr Hdisj regs ret Hret H1 H2 H10 H11)
    as (r & RUN & KC & A10).
  exists r, (mem1 mem sp ret (getr regs 8) (getr regs 9)).
  split; [exact RUN | split; [exact KC | split; [exact A10 | apply frame1; exact Hspr]]].
Qed.
End FPGen1.
End UbStrnlen.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbStartupFacts.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup.
Import ListNotations.
Open Scope bv_scope.

Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.PuPeel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac peel ::= peel_fast.
#[local] Ltac SumsLib.StartupTac.addr_norm ::= addr_norm_fast.
#[local] Existing Instance fx0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition D_main_cells : list (Z * nat) :=
  [(0x8aac0%Z, 8%nat); (0xaae28%Z, 8%nat); (0xaae88%Z, 8%nat); (0xaae50%Z, 8%nat); (0xaae18%Z, 8%nat); (0xaae10%Z, 8%nat); (0xaabb8%Z, 8%nat); (0xaabc8%Z, 8%nat); (0xaabc0%Z, 8%nat); (0xaae38%Z, 8%nat); (0xaae40%Z, 8%nat); (0x8aba0%Z, 8%nat); (0x8ab88%Z, 8%nat); (0x8aac8%Z, 8%nat); (0xaae20%Z, 1%nat); (0x8aaf0%Z, 4%nat); (0x8aae8%Z, 4%nat); (0x8ab60%Z, 8%nat); (0x8ab40%Z, 8%nat); (0x8aad0%Z, 8%nat); (0x8aad8%Z, 8%nat); (0x8aae0%Z, 8%nat); (0xaae00%Z, 4%nat); (0xaae04%Z, 4%nat); (0xaae01%Z, 1%nat); (0x8ab80%Z, 8%nat); (0x79fd0%Z, 1%nat)].

Definition range_disjoint_b (a : Z) (n : nat) (c : Z * nat) : bool :=
  ((a + Z.of_nat n <=? fst c) || (fst c + Z.of_nat (snd c) <=? a))%Z.

Definition D_main_missb (a : Z) (n : nat) : bool :=
  forallb (range_disjoint_b a n) D_main_cells && (0 <=? a)%Z && (a + Z.of_nat n <=? 0x100000)%Z.

(* [comment removed for export] *)
Definition djw (P : Prop) : Prop := P.

Lemma range_disjoint_djw : forall a n c,
  range_disjoint_b a n c = true ->
  djw (a + Z.of_nat n <= fst c \/ fst c + Z.of_nat (snd c) <= a)%Z.
Proof.
  intros a n [c l] H. unfold range_disjoint_b in H. cbn [fst snd] in *.
  apply orb_true_iff in H. unfold djw. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Section Facts.
  Variable sp0 : word.
  Variables av ev : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Hypothesis Hva : valid_argv av.
  Hypothesis Hlo : (0x7fff80000000 <= bv_unsigned sp0)%Z.
  Hypothesis Hhi : (bv_unsigned sp0 <= 0x800000000000)%Z.

  Let D := D_main sp0 av ev hw rdraw tid.

  Lemma len_av : (1 <= Z.of_nat (length av) <= 1024)%Z.
  Proof using Hva. destruct Hva as [[H1 H2] _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma D_main_miss : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs (D_main sp0 av ev hw rdraw tid) (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof using.
    intros segs a n Hb. pose proof (u64_range tid).
    unfold D_main_missb, D_main_cells in Hb. cbn [forallb] in Hb.
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H; destruct H as [? ?]
           end.
    repeat match goal with
           | H : range_disjoint_b _ _ _ = true |- _ =>
               apply range_disjoint_djw in H; cbn [fst snd Z.of_nat Pos.of_succ_nat Pos.succ] in H
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : true = true |- _ => clear H
           end.
    cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in *.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc.
    repeat (rewrite rdn_wbytes_out by
      (rewrite ?length_N_to_le_bytes, ?length_rnd_lo4, ?length_rnd_hi4; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; imm_norm; unorm;
       lazymatch goal with
       | |- (?A \/ ?B) => match goal with H : djw _ |- _ => exact H end
       | |- _ => lia
       end)).
    reflexivity.
  Qed.

  Ltac hitD :=
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc;
    pose proof len_av;
    peel; first [ apply rdn_wbytes_hit8; unorm; lia
                | match goal with |- rdn _ (wbytes _ ?a ?bs) ?a _ = _ =>
                    rewrite <- (length_N_to_le_bytes 4) at 1; apply rdn_wbytes_hit; rewrite length_N_to_le_bytes; unorm; lia end ].

  (* [comment removed for export] *)
  Lemma D_main_tid : forall segs,
    rdn segs D (Z_to_bv 64 0x8aae8) 4 = Some (word_to_le_bytes 4 tid).
  Proof using.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    pose proof (rdn_wbytes_hit segs (word_to_le_bytes 4 tid)) as Hh.
    rewrite length_N_to_le_bytes in Hh. apply Hh. unorm; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_guard : forall segs,
    rdn segs D (Z_to_bv 64 0xaae00) 8 = Some (canary_bytes rdraw).
  Proof using.
    intros segs. pose proof (u64_range tid). subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply (rdn_guard_canary segs rdraw); lia.
  Qed.

  (* [comment removed for export] *)
  Lemma D_main_pagesize : forall segs,
    rdn segs D (Z_to_bv 64 0xaae50) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
  Proof using Hva.
    intros segs. pose proof (u64_range tid). pose proof len_av. subst D.
    unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel.
    apply rdn_wbytes_hit8. unorm; lia.
  Qed.





  (* [comment removed for export] *)
  Variable regs : bvmap 5 word.
  Variable mem : word -> option byte.
  Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

  Lemma main_entry_rdn_image : forall segs (a : Z) (n : nat),
    D_main_missb a n = true ->
    rdn segs mem (Z_to_bv 64 a) n = rdn segs (fun _ => None) (Z_to_bv 64 a) n.
  Proof using ME regs Hlo tid rdraw hw uid ev av sp0.
    intros segs a n Hb.
    assert (Hr : (0 <= a /\ a + Z.of_nat n <= 0x100000)%Z).
    { unfold D_main_missb in Hb. apply andb_true_iff in Hb as [Hb H2]. apply andb_true_iff in Hb as [_ H1].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia).
    apply D_main_miss. exact Hb.
  Qed.

  Lemma main_entry_tid : forall segs,
    rdn segs mem (Z_to_bv 64 0x8aae8) 4 = Some (word_to_le_bytes 4 tid).
  Proof using ME regs D Hlo rdraw hw uid ev av sp0.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_tid.
  Qed.

  Lemma main_entry_guard : forall segs,
    rdn segs mem (Z_to_bv 64 0xaae00) 8 = Some (canary_bytes rdraw).
  Proof using ME regs D Hlo tid hw uid ev av sp0.
    intros segs. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME)
      by (rewrite stack_max_size_val; unorm; lia). apply D_main_guard.
  Qed.
End Facts.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
End UbStartupFacts.
Require Stdlib.NArith.NArith LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvNodes2Sound.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.ShapeNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzCallLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzKnowLib OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesBlob OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStdioDefs.UbExitBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound.UbStdioWrite OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound.UbExit OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes2 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesLibc OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemchr UbStrnlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation RSEGS := USEGS (only parsing).

(* [comment removed for export] *)
Lemma file_syms_sound : forall E M k f fd buf bsz wb wp,
  know_ok RSEGS E M k -> DN2.file_syms RSEGS k f = Some (fd, buf, bsz, wb, wp) -> 0 <= f -> f + 232 <= 2 ^ 64 ->
  sw_file M f (uE E wb) (uE E wp) fd (edenot E buf) (edenot E bsz) /\ 0 <= fd < two64.
Proof.
  intros E M k f fd buf bsz wb wp HK H Hf0 Hf8. unfold DN2.file_syms in H.
  destruct (kreadZ RSEGS k (ELit 0) (f + 120) 4) as [x1|] eqn:H1; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) (f + 88)) as [x2|] eqn:H2; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) (f + 96)) as [x3|] eqn:H3; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) (f + 56)) as [x4|] eqn:H4; [|discriminate].
  destruct (kread8e RSEGS k (ELit 0) (f + 40)) as [x5|] eqn:H5; [|discriminate].
  injection H as <- <- <- <- <-.
  destruct (kreadZ_lit0_sound E M k _ _ _ HK H1 ltac:(lia) ltac:(lia) ltac:(lia)) as [R1 B1].
  pose proof (kread8e_lit0_sound E M k _ _ HK H2 ltac:(lia) ltac:(lia)) as R2.
  pose proof (kread8e_lit0_sound E M k _ _ HK H3 ltac:(lia) ltac:(lia)) as R3.
  pose proof (kread8e_lit0_sound E M k _ _ HK H4 ltac:(lia) ltac:(lia)) as R4.
  pose proof (kread8e_lit0_sound E M k _ _ HK H5 ltac:(lia) ltac:(lia)) as R5.
  split; [| lia]. constructor; unfold uE; rewrite ?Z_to_bv_bv_unsigned; assumption.
Qed.

(* [comment removed for export] *)
Lemma know_after_sw2 : forall E M M' k spb spk (su f : Z) (buf bsz : expr),
  know_ok RSEGS E M k ->
  bv_unsigned (edenot E spb) + spk = su -> 112 <= su -> 0 <= f -> f + 232 <= 2 ^ 64 ->
  sw_post M su f (edenot E buf) (edenot E bsz) M' ->
  know_ok RSEGS E M'
    ([KWord (SA (ELit 0) (f + 32)) 8 (eadd buf bsz); KWord (SA (ELit 0) (f + 40)) 8 buf; KWord (SA (ELit 0) (f + 56)) 8 buf]
     ++ kn_havoc (kn_havoc k spb (spk - DN.FR_SW) (ELit DN.FR_SW)) (ELit 0) (f + 32) (ELit 32)).
Proof.
  intros E M M' k spb spk su f buf bsz HK Hsu Hsu112 Hf0 Hf8 [AG GR WE WP WB].
  apply Forall_app. split.
  - repeat apply Forall_cons; try apply Forall_nil; cbn [kentry_ok]; (split; [lia|]); (split; [unfold flat; rewrite estart_lit0; lia|]);
      rewrite GCL.adenot_SA, estart_lit0.
    + rewrite WE. do 2 f_equal. unfold eadd. rewrite mkAlu_denot. reflexivity.
    + exact WP.
    + exact WB.
  - set (M1 := fun x : word => if (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool then M x else M' x).
    apply (know_ok_havoc RSEGS E M1 M').
    + apply (know_ok_havoc RSEGS E M M1); [exact HK| |].
      * intros x Hx. rewrite estart_SA in Hx. unfold elenZ, DN.FR_SW in Hx. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia.
        unfold M1. destruct (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool eqn:Hc; [reflexivity|].
        apply Bool.andb_false_iff in Hc. apply AG; [lia| |]; destruct Hc as [Hc|Hc]; [apply Z.leb_gt in Hc| apply Z.ltb_ge in Hc|apply Z.leb_gt in Hc| apply Z.ltb_ge in Hc]; lia.
      * intros x Hmx HM1. unfold M1 in HM1.
        destruct ((f + 32 <=? bv_unsigned x) && (bv_unsigned x <? f + 64))%bool; [exact (Hmx HM1) | exact (GR x Hmx HM1)].
    + intros x Hx. rewrite estart_lit0 in Hx. unfold elenZ in Hx. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia.
      unfold M1. destruct (Z.leb (f + 32) (bv_unsigned x) && Z.ltb (bv_unsigned x) (f + 64))%bool eqn:Hc; [|reflexivity].
      apply andb_prop in Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
    + intros x HM1 Hm'. unfold M1 in HM1.
      destruct ((f + 32 <=? bv_unsigned x) && (bv_unsigned x <? f + 64))%bool; [exact (GR x HM1 Hm') | exact (HM1 Hm')].
Qed.

Section Sound.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Variable nx0 : nat.
Variable SWIN : list (Z * Z).
Variable PERMc : list (Z * Z).
Variable SPTOPc : Z.
Variable FS0 : Fs.Fs.
Variable FDS0 : list (word * FdEntry).
Variable AINV : list (Z * Z) -> Z -> Z -> (word -> option byte) -> Model -> Prop.
Hypothesis AINV_frame : forall Lc B C M M' mdl,
  AINV Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN PERMc SPTOPc Lc a /\ M' a <> None) -> AINV Lc B C M' mdl.
Variable FXOK : FX -> Prop.
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree nx0 E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable NZB : list nat.
Hypothesis UINV_nz : forall E j, UINV E -> In j NZB -> ~ In (Z_to_bv 8 0) (eb E j).
Hypothesis SR_det : forall c T T', sr_rel RSEGS SR c T -> realizes RSEGS c T' -> t_eq T T'.
Hypothesis SWINc : forall a, (DN.FILE1 <= a < DN.FILE1 + 232 \/ DN.FILE2 <= a < DN.FILE2 + 232) -> in_wins SWIN a.
Hypothesis FDS1 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FDS2 : fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).

#[local] Notation RZ := (sr_rel RSEGS SR).
#[local] Notation cs_ok := (GPS.cs_ok RSEGS PERMc SPTOPc FS0 FDS0 AINV FXOK UINV).
#[local] Notation cfg := (cfgF RSEGS).

Theorem node_stdio_write2_sound : forall cs fd ps cs' E fx R M model T,
  cs_ok E cs fx R M model -> DN2.node_stdio_write2 RSEGS nx0 cs = Some (fd, ps, cs') -> T [] ->
  (forall E' fx' R' M' model',
      env_agree nx0 E E' /\ env_agree (nxt cs) E E' -> cs_ok E' cs' fx' R' M' model' -> m_fs model' = m_fs model ->
      RZ (cfg fx' R' (pc cs') M' model') T) ->
  RZ (cfg fx R (pc cs) M model) (t_emit (Wp E fd ps) T).
Proof.
  intros cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN2.node_stdio_write2 in Hn.
  destruct (Z.eqb (pc cs) DN.P_STDIO_WRITE) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 10) as [f|] eqn:R10; [|discriminate].
  destruct (ret_lit cs) as [ret|] eqn:Rret; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg1; [|discriminate] end. cbn [negb] in Hn.
  destruct (DN2.file_syms RSEGS (kn cs) f) as [[[[[fdv buf] bsz] wb] wp]|] eqn:Hfl; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hfd; [|discriminate] end. cbn [negb] in Hn.
  destruct (split_lit wb) as [wbb wbk] eqn:Hsqw.
  destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hsqs.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  cbv zeta in Hn.
  destruct (GNB.kgather RSEGS (kn cs) wb wp) as [pend|] eqn:Hpend; [|discriminate].
  destruct (GNB.kgather RSEGS (kn cs) (reg cs 11) (eadd (reg cs 11) (reg cs 12))) as [ext|] eqn:Hext; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg3; [|discriminate] end. cbn [negb] in Hn.
  match type of Hn with context [after_call ?a ?b ?c ?d ?e] => destruct (after_call a b c d e) as [cs1|] eqn:Hac; [|discriminate] end.
  injection Hn as <- <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hg1 as [Hg1 Hlen]. apply andb_prop in Hg1 as [Hg1 Hfresh]. apply andb_prop in Hg1 as [Hg1 Hssp].
  apply andb_prop in Hg1 as [Hg1 Hfr]. apply andb_prop in Hg1 as [Hf12 Hspok]. apply Nat.eqb_eq in Hlen.
  apply andb_prop in Hg3 as [Hg3 Hdisj]. apply andb_prop in Hg3 as [Hg3 Hbflat]. apply andb_prop in Hg3 as [Hg3 Hwdisj].
  apply andb_prop in Hg3 as [Hg3 Hwflat]. apply andb_prop in Hg3 as [Hg3 Ltot]. apply andb_prop in Hg3 as [Lwp Lsl].
  assert (Hfdv : (fdv = 1 \/ fdv = 2) /\ (f = DN.FILE1 \/ f = DN.FILE2)).
  { apply orb_prop in Hfd as [H|H]; apply andb_prop in H as [H1 H2]; apply Z.eqb_eq in H1; apply Z.eqb_eq in H2; subst; tauto. }
  destruct Hfdv as [Hfdv Hf]. clear Hfd Hf12.
  assert (Hfb : 0x79000 <= f /\ f + 232 <= 0xaae00) by (unfold DN.FILE1, DN.FILE2 in Hf; lia).
  (* [comment removed for export] *)
  pose proof (co_know HC) as HK.
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 f HC ltac:(lia) R10) as [G10 _].
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 HC ltac:(lia)) as G11.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 12 HC ltac:(lia)) as G12.
  change (Z.of_nat 10) with 10 in G10. change (Z.of_nat 11) with 11 in G11. change (Z.of_nat 12) with 12 in G12.
  destruct (GCL.ret_lit_sound E cs R ret (co_regs HC) Rret) as (G1 & Hretok & Hretr & _).
  destruct (sp_ok_sound PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model DN.FR_SW HC Hspok ltac:(unfold DN.FR_SW; lia)) as (Hsp & Hst & G2 & Hsu).
  specialize (Hsu spb spk Hsq).
  set (su := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (file_syms_sound E M (kn cs) f fdv buf bsz wb wp HK Hfl ltac:(lia) ltac:(lia)) as [SWF Bfd].
  destruct (ssp_ok_sound E M (kn cs) HK Hssp) as [can Hcan].
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Lwp) as Bwp. rewrite !GNB.xt_den1 in Bwp.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Lsl) as Bsl. rewrite GNB.xt_den1, GNB.xt_den2 in Bsl.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Ltot) as Btot. rewrite GNB.xt_den1, GNB.xt_den2 in Btot.
  change (uE E (ELit 0)) with 0 in Bwp, Bsl.
  destruct (bflat_x_sound RSEGS E M (kn cs) sb sk (reg cs 12) HK Hbflat) as (Fs0 & Fsl & Fs64).
  pose proof (u_of_split E (reg cs 11) sb sk Hsqs ltac:(lia)) as Us. rewrite estart_SA in Us.
  pose proof (APS.disj_x_sound RSEGS E M (kn cs) sb sk (reg cs 12) spb (spk - DN.FR_SW) (ELit DN.FR_SW) HK Hdisj) as DISJ.
  rewrite !estart_SA in DISJ. unfold elenZ, DN.FR_SW in DISJ. cbn [edenot] in DISJ. rewrite u64_lit in DISJ by lia.
  destruct (bflat_x_sound RSEGS E M (kn cs) wbb wbk (esub wp wb) HK Hwflat) as (Fw0 & Fwl & Fw64).
  pose proof (u_of_split E wb wbb wbk Hsqw ltac:(lia)) as Uwb. rewrite estart_SA in Uwb.
  pose proof (APS.disj_x_sound RSEGS E M (kn cs) wbb wbk (esub wp wb) spb (spk - DN.FR_SW) (ELit DN.FR_SW) HK Hwdisj) as WDISJ.
  rewrite !estart_SA in WDISJ. unfold elenZ, DN.FR_SW in WDISJ. cbn [edenot] in WDISJ. rewrite u64_lit in WDISJ by lia.
  (* [comment removed for export] *)
  destruct (GNB.kgather_sound RSEGS E M (kn cs) wb wp pend HK Hpend) as (Kp1 & Kp2 & Kp3 & _).
  destruct (GNB.kgather_sound RSEGS E M (kn cs) (reg cs 11) (eadd (reg cs 11) (reg cs 12)) ext HK Hext) as (Ke1 & Ke2 & Ke3 & _).
  set (pbs := flat_map (piece_den E) pend) in *. set (extra := flat_map (piece_den E) ext) in *.
  pose proof (u64_range (edenot E (reg cs 11))) as U11. pose proof (u64_range (edenot E (reg cs 12))) as U12.
  pose proof (u64_range (edenot E wp)) as Uwp. pose proof (u64_range (edenot E wb)) as Uwb'.
  assert (Ule : uE E (eadd (reg cs 11) (reg cs 12)) = uE E (reg cs 11) + uE E (reg cs 12)).
  { unfold eadd, uE in *. rewrite mkAlu_denot. rewrite u_add64. apply Z.mod_small. unfold DN.SPHI in Bsl. lia. }
  rewrite Ule in Ke1.
  assert (Usub : uE E (esub wp wb) = uE E wp - uE E wb).
  { unfold esub, uE in *. rewrite mkAlu_denot. rewrite u_sub64. apply Z.mod_small. lia. }
  unfold uE in Usub. rewrite Usub in Fwl, WDISJ.
  (* [comment removed for export] *)
  assert (HW : Wp E fdv (pend ++ ext) = map (WriteEv (Z_to_bv 64 fdv)) (pbs ++ extra)).
  { unfold Wp. f_equal. rewrite flat_map_app. reflexivity. }
  rewrite HW. unfold cfgF, mkstF. rewrite Hpc.
  replace (Z_to_bv 64 DN.P_STDIO_WRITE) with (0x69010%bv : word) by (apply bv_eq; reflexivity).
  unfold uE in *.
  apply (ref_stdio_write_R (fx:=fx) SR R M model su f (bv_unsigned (edenot E wb)) (bv_unsigned (edenot E wp)) fdv (edenot E (reg cs 11)) (edenot E (reg cs 12))
           (edenot E buf) (edenot E bsz) can (Z_to_bv 64 ret) pbs extra T).
  all: try assumption.
  all: try (subst su; rewrite Z_to_bv_bv_unsigned; reflexivity).
  all: try (rewrite (co_fds HC); destruct Hfdv as [-> | ->]; [exact FDS1 | exact FDS2]).
  all: try exact (co_halt HC). all: try exact (co_lazy HC).
  all: try (rewrite Z_to_bv_bv_unsigned; exact Kp3).
  all: try (unfold DN.SPLO, DN.SPHI, DN.FR_SW in *; lia).
  - (* [comment removed for export] *)
    intros regs' mem' Q10 Q2 Q1 Q8 Q9 Q18 Q19 Q20 Q21 Q22 Q23 Q24 Q25 Q26 Q27 Q3 Q4 POST.
    unfold after_call in Hac.
    match type of Hac with context [if ?c then _ else _] => destruct c eqn:Hcc; [|discriminate] end.
    apply andb_prop in Hcc as [Hcc Hrvv]. apply andb_prop in Hcc as [_ Hkv]. injection Hac as Ecs1.
    destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (E' := GCL.ext_call E (nxt cs) regs').
    pose proof (GCL.ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
    specialize (Hk E' fx regs' mem' model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
    rewrite <- Ecs1 in Hk. unfold cfgF, mkstF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
    pose proof (GPS.cs_ok_agree RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC1.
    assert (KEPT : GCL.kept_ok R regs').
    { apply kept_ok_intro. intros r Hr. cbn [In] in Hr.
      repeat match type of Hr with _ \/ _ => destruct Hr as [<-|Hr] end; [| | | | | | | | | | | | | | | destruct Hr]; try assumption.
      rewrite Q2. subst su. rewrite Z_to_bv_bv_unsigned. reflexivity. }
    eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC1 | | reflexivity | | exact (co_fx HC) |].
    + cbn [mk_ss s_regs]. apply (GCL.regs_after_call E _ R regs' (nxt cs) (Some (reg cs 12)) (co_regs HC) Fsr KEPT).
      split; [exact Hrvv | replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity); exact Q10].
    + cbn [mk_ss s_know]. eapply know_ok_agree'; [exact Hag | exact Hkv |].
      apply (know_after_sw2 E M mem' (kn cs) spb spk su f buf bsz HK); try assumption; try lia.
      unfold DN.SPLO, DN.FR_SW in Hsp. lia.
    + intros a Ha. cbn [a_vis]. rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
      destruct POST as [AG GR _ _ _]. pose proof (u64_range a) as Hau.
      split.
      2:{ intros Hn0. apply Ha. rewrite Hn0. destruct (M a) eqn:Hma; [|reflexivity]. exfalso. exact (GR a ltac:(congruence) Hn0). }
      destruct (Z_lt_le_dec (bv_unsigned a) (su - 112)) as [Hlow|Hhigh]; [|destruct (Z_lt_le_dec (bv_unsigned a) su) as [Hin|Habove]].
      * (* [comment removed for export] *) right. right. right. apply SWINc.
        assert (~ (~ f + 32 <= bv_unsigned a < f + 48 /\ ~ f + 56 <= bv_unsigned a < f + 64)) as Hx by (intros [X1 X2]; apply Ha; apply AG; lia).
        unfold DN.FILE1, DN.FILE2 in *. lia.
      * (* [comment removed for export] *) right. right. left. rewrite <- (co_top HC).
        unfold DN.frame_ok in Hfr. rewrite Hsq in Hfr.
        assert (Hrng : estart E (SA spb (spk - DN.FR_SW)) <= bv_unsigned a < estart E (SA spb (spk - DN.FR_SW)) + elenZ E (ELit DN.FR_SW)).
        { rewrite estart_SA. unfold elenZ, DN.FR_SW in *. cbn [edenot]. rewrite u64_lit by lia. lia. }
        exact (proj1 (GPS.in_floor_sound RSEGS E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - DN.FR_SW) (ELit DN.FR_SW) a (co_know HC) Hfr (co_floor HC) Hrng)).
      * exfalso. unfold DN.SPLO, DN.FR_SW, DN.FILE1, DN.FILE2 in *. apply Ha. apply AG; lia.
Qed.

(* [comment removed for export] *)
Lemma rdn_cons_inv : forall M (a : word) n b bs, rdn RSEGS M a (S n) = Some (b :: bs) ->
  GxSymExec3Sound.AX2S.rd1 RSEGS M a = Some b /\ rdn RSEGS M (a + 1)%bv n = Some bs.
Proof.
  intros M a n b bs H. cbn [rdn] in H. unfold GxSymExec3Sound.AX2S.rd1.
  destruct (match M a with Some b0 => Some b0 | None => seg_rom RSEGS a end) as [b0|]; [|discriminate].
  destruct (rdn RSEGS M (a + 1)%bv n) as [r|]; [|discriminate]. injection H as <- <-. split; reflexivity.
Qed.
Lemma rdn_nth1 : forall n M (a : word) bs i, rdn RSEGS M a n = Some bs -> (i < n)%nat ->
  bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn RSEGS M (Z_to_bv 64 (bv_unsigned a + Z.of_nat i)) 1%nat = Some [nth i bs (Z_to_bv 8 0)].
Proof.
  induction n as [|n IH]; intros M a bs i H Hi Hnw; [lia|].
  destruct bs as [|b bs']; [pose proof (rdn_length _ _ _ _ _ H) as L; cbn in L; lia|].
  destruct (rdn_cons_inv M a n b bs' H) as [H1 H2].
  destruct i as [|i].
  - cbn [nth]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. cbn [rdn]. unfold GxSymExec3Sound.AX2S.rd1 in H1. rewrite H1. reflexivity.
  - cbn [nth]. pose proof (u64_range a) as Ha.
    assert (U1 : bv_unsigned (a + 1)%bv = bv_unsigned a + 1) by (apply u_add1; lia).
    replace (bv_unsigned a + Z.of_nat (S i)) with (bv_unsigned (a + 1)%bv + Z.of_nat i) by lia.
    apply (IH M (a + 1)%bv bs' i H2 ltac:(lia)). lia.
Qed.

Theorem node_strnlen_sound :
  GPS.node1_stmtN RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ GPS.always (DN2.node_strnlen nx0 NZB).
Proof.
  intros cs cs' E fx R M model T HT HC _ Hn Hk. unfold DN2.node_strnlen in Hn.
  destruct (Z.eqb (pc cs) DN2.P_STRNLEN) eqn:Hpc; [|discriminate]. cbn [negb] in Hn. apply Z.eqb_eq in Hpc.
  destruct (reg_lit cs 11) as [n|] eqn:R11; [|discriminate].
  destruct (ret_lit cs) as [ret|] eqn:Rret; [|discriminate].
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg1; [|discriminate] end. cbn [negb] in Hn.
  destruct (split_lit (reg cs 10)) as [sb sk] eqn:Hsqs.
  destruct (split_lit (reg cs 2)) as [spb spk] eqn:Hsq.
  destruct (find _ (kn cs)) as [K|] eqn:HF; [|discriminate].
  destruct K as [| | ba L jb| | | | | | |]; try discriminate.
  cbv zeta in Hn.
  match type of Hn with (if negb ?c then _ else _) = _ => destruct c eqn:Hg2; [|discriminate] end. cbn [negb] in Hn.
  (* [comment removed for export] *)
  apply andb_prop in Hg1 as [Hg1 Hn64]. apply andb_prop in Hg1 as [Hg1 Hn0]. apply andb_prop in Hg1 as [Hg1 Hro].
  apply andb_prop in Hg1 as [Hg1 Hlen]. apply andb_prop in Hg1 as [Hg1 Hfresh]. apply andb_prop in Hg1 as [Hspok Hfr].
  apply Nat.eqb_eq in Hlen. apply Z.leb_le in Hn0. apply Z.ltb_lt in Hn64.
  apply andb_prop in Hg2 as [Hg2 Ls1]. apply andb_prop in Hg2 as [Hg2 Lhi]. apply andb_prop in Hg2 as [Hg2 Hdisj].
  apply andb_prop in Hg2 as [Hg2 Hbflat]. apply andb_prop in Hg2 as [Hg2 HLn]. apply andb_prop in Hg2 as [Hnul Hunk].
  (* [comment removed for export] *)
  apply find_some in HF as [HinB HB]. destruct ba as [bb bo]. apply andb_prop in HB as [HB Hj]. apply andb_prop in HB as [Hbb Hbo].
  apply expr_eqb_eq in Hbb. apply Z.eqb_eq in Hbo. subst bb bo. apply existsb_exists in Hj as (j0 & Hj0 & Hjj). apply Nat.eqb_eq in Hjj. subst j0.
  pose proof (co_know HC) as HK.
  pose proof (proj1 (Forall_forall _ _) HK _ HinB) as KB. cbn [kentry_ok] in KB. destruct KB as (FB & LEN & BY). unfold flat in FB. rewrite !estart_SA in FB, BY.
  (* [comment removed for export] *)
  apply existsb_exists in Hnul as (K' & HK' & HKK). apply kentry_eqb_eq in HKK. subst K'.
  pose proof (proj1 (Forall_forall _ _) HK _ HK') as KW. cbn [kentry_ok] in KW. destruct KW as (_ & FW & RW).
  (* [comment removed for export] *)
  apply existsb_exists in Hunk as (K' & HKu & HKU). destruct K' as [| | | | | | | | |[ub uo] um]; try discriminate.
  apply andb_prop in HKU as [HKU Lum]. apply andb_prop in HKU as [Hub Huo]. apply expr_eqb_eq in Hub. apply Z.eqb_eq in Huo. subst ub uo.
  pose proof (proj1 (Forall_forall _ _) HK _ HKu) as KU. cbn [kentry_ok] in KU. destruct KU as [FU DU]. unfold flat in FU. rewrite !estart_SA in FU, DU.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Lum) as Bum. rewrite !GNB.xt_den1 in Bum.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Lhi) as Bhi. rewrite GNB.xt_den1, GNB.xt_den2 in Bhi. change (uE E (ELit 0)) with 0 in Bhi.
  pose proof (lin_ge0_sound RSEGS E M (kn cs) _ _ HK Ls1) as Bs1. rewrite !GNB.xt_den1 in Bs1. change (uE E (ELit 1)) with 1 in Bs1.
  destruct (xhi (kn cs) L) as [lh|] eqn:Hlh; [|discriminate]. apply Z.leb_le in HLn.
  pose proof (xhi_sound RSEGS E M (kn cs) _ _ HK Hlh) as Blh.
  (* [comment removed for export] *)
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 n HC ltac:(lia) R11) as [G11 _].
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 HC ltac:(lia)) as G10.
  change (Z.of_nat 11) with 11 in G11. change (Z.of_nat 10) with 10 in G10.
  destruct (GCL.ret_lit_sound E cs R ret (co_regs HC) Rret) as (G1 & Hretok & Hretr & _).
  destruct (sp_ok_sound PERMc SPTOPc FS0 FDS0 AINV FXOK UINV E cs fx R M model DN2.FR_SNL HC Hspok ltac:(unfold DN2.FR_SNL; lia)) as (Hsp & Hst & G2 & Hsu).
  specialize (Hsu spb spk Hsq).
  set (su := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
  destruct (bflat_x_sound RSEGS E M (kn cs) sb sk (eadd L (ELit 8)) HK Hbflat) as (Fs0 & Fsl & Fs64).
  pose proof (u_of_split E (reg cs 10) sb sk Hsqs ltac:(lia)) as Us. rewrite estart_SA in Us.
  pose proof (APS.disj_x_sound RSEGS E M (kn cs) sb sk (eadd L (ELit 8)) spb (spk - DN2.FR_SNL) (ELit DN2.FR_SNL) HK Hdisj) as DISJ.
  rewrite !estart_SA in DISJ. unfold elenZ, DN2.FR_SNL in DISJ. cbn [edenot] in DISJ. rewrite u64_lit in DISJ by lia.
  assert (UL8 : uE E (eadd L (ELit 8)) = uE E L + 8).
  { unfold eadd, uE in *. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite u64_lit by lia. apply Z.mod_small.
    pose proof (u64_range (edenot E L)). unfold DN.SPHI in Bhi. lia. }
  unfold uE in UL8. rewrite UL8 in Fsl, DISJ. unfold uE in *.
  set (sz := bv_unsigned (edenot E sb) + sk) in *. set (Lz := bv_unsigned (edenot E L)) in *.
  unfold elenZ in *.
  (* [comment removed for export] *)
  destruct (rdn_defined RSEGS M (Z.to_nat (Lz + 8)) (edenot E (reg cs 10))) as (buf & Hbuf & Lbuf).
  { rewrite Us. pose proof (u64_range (edenot E L)). lia. }
  { intros j Hj. unfold GxSymExec3Sound.AX2S.rd1. rewrite Us.
    pose proof (DU (Z.of_nat j) ltac:(pose proof (u64_range (edenot E L)); lia)) as D. destruct (M (Z_to_bv 64 (sz + Z.of_nat j))); [discriminate | exfalso; apply D; reflexivity]. }
  assert (MCH : mchrH M (edenot E (reg cs 10)) buf Lz n).
  { constructor.
    - rewrite Lbuf. exact Hbuf.
    - rewrite Lbuf, Us. pose proof (u64_range (edenot E L)). rewrite Z2Nat.id by lia.
      pose proof (Z.mul_div_le (sz + Lz) 8 ltac:(lia)). lia.
    - rewrite Lbuf, Us. pose proof (u64_range (edenot E L)). rewrite Z2Nat.id by lia. unfold DN.SPHI in Bhi. lia.
    - pose proof (u64_range (edenot E L)). lia.
    - (* [comment removed for export] *)
      pose proof (u64_range (edenot E L)) as UL.
      pose proof (rdn_nth1 (Z.to_nat (Lz + 8)) M (edenot E (reg cs 10)) buf (Z.to_nat Lz) Hbuf ltac:(lia) ltac:(rewrite Us; lia)) as X.
      rewrite Us, Z2Nat.id in X by lia.
      rewrite (adenot_flatZ' E) in RW || idtac.
      assert (AW : adenot E (SA (eadd (reg cs 10) L) 0) = Z_to_bv 64 (sz + Lz)).
      { apply bv_eq. rewrite (flat_u E _ _ FW), estart_SA, u64_lit by lia. unfold eadd. rewrite mkAlu_denot, u_add64. fold Lz. rewrite Us.
        rewrite Z.mod_small by lia. lia. }
      rewrite AW in RW. rewrite RW in X. injection X as X. rewrite <- X. reflexivity.
    - (* [comment removed for export] *)
      intros j Hj. pose proof (u64_range (edenot E L)) as UL.
      pose proof (rdn_nth1 (Z.to_nat (Lz + 8)) M (edenot E (reg cs 10)) buf j Hbuf ltac:(lia) ltac:(rewrite Us; lia)) as X.
      rewrite Us in X. pose proof (BY (Z.of_nat j) ltac:(lia)) as Y. rewrite Nat2Z.id in Y. replace (sz + 0 + Z.of_nat j) with (sz + Z.of_nat j) in Y by lia.
      cbn [rdn] in X. rewrite Y in X. injection X as X. rewrite <- X.
      intros Z0. apply (UINV_nz E jb (co_uinv HC) Hj0).
      assert (EQ : nth j (eb E jb) (Z_to_bv 8 0) = Z_to_bv 8 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite <- EQ. apply nth_In. lia.
    - lia.
    - exact Hn64.
    - intros i Hi. exact (kimg_covers_sound E M (kn cs) 0x13038 32 HK Hro i Hi). }
  (* [comment removed for export] *)
  assert (E1 : Z_to_bv 5 1 = (1%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E2 : Z_to_bv 5 2 = (2%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 10 = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 11 = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  pose proof G1 as G1'. rewrite E1 in G1'. pose proof G10 as G10'. rewrite E10 in G10'. pose proof G11 as G11'. rewrite E11 in G11'.
  destruct (ref_strnlen (fx:=fx) M (edenot E (reg cs 10)) (getr R (Z_to_bv 5 2)) buf Lz n (seg_rom RSEGS) R (Z_to_bv 64 ret) MCH
              ltac:(lia) ltac:(exact Hst) ltac:(unfold DN.SPLO, DN2.FR_SNL in Hsp; lia) ltac:(rewrite Lbuf, Us, Z2Nat.id by lia; unfold DN2.FR_SNL in *; lia)
              Hretok G1' ltac:(rewrite E2; reflexivity) G10' G11')
    as (regs' & mem' & RUN & KC & A10 & FM).
  unfold cfgF, mkstF. rewrite Hpc. replace (Z_to_bv 64 DN2.P_STRNLEN) with (0x739f0%bv : word) by (apply bv_eq; reflexivity).
  eapply (sr_msteps RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | exact RUN |].
  (* [comment removed for export] *)
  unfold after_call in Hn.
  match type of Hn with context [if ?c then _ else _] => destruct c eqn:Hcc; [|discriminate] end.
  apply andb_prop in Hcc as [Hcc Hrvv]. apply andb_prop in Hcc as [_ Hkv]. injection Hn as Ecs1.
  destruct (fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (E' := GCL.ext_call E (nxt cs) regs').
  pose proof (GCL.ext_call_agree E (nxt cs) regs') as Hag. fold E' in Hag.
  specialize (Hk E' fx regs' mem' model (conj (env_agree_le _ _ _ _ Hag Fle) Hag)).
  rewrite <- Ecs1 in Hk. unfold cfgF, mkstF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. apply Hk; [|reflexivity].
  pose proof (GPS.cs_ok_agree RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV UINV_agree E E' cs fx R M model Hag Hfresh HC) as HC1.
  pose proof (GNL.keeps_cs_kept_ok R regs' KC) as KEPT.
  destruct FM as [AGR GRW]. subst su.
  eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV); [exact HC1 | | reflexivity | | exact (co_fx HC) |].
  + cbn [mk_ss s_regs]. apply (GCL.regs_after_call E _ R regs' (nxt cs) (Some L) (co_regs HC) Fsr KEPT).
    split; [exact Hrvv | rewrite E10, A10; unfold Lz; rewrite Z_to_bv_bv_unsigned; reflexivity].
  + cbn [mk_ss s_know]. eapply know_ok_agree'; [exact Hag | exact Hkv |].
    apply (know_ok_havoc RSEGS E M mem'); [exact HK | | exact GRW].
    intros x Hx. apply AGR. cbn [outside]. split; [|exact I]. unfold in_rng. rewrite u64_lit by (unfold DN.SPLO, DN.SPHI, DN2.FR_SNL in Hsp; lia).
    rewrite estart_SA in Hx. unfold elenZ, DN2.FR_SNL in Hx |- *. cbn [edenot] in Hx. rewrite u64_lit in Hx by lia. lia.
  + intros a Ha. cbn [a_vis]. rewrite (blocks_den_agree (nxt cs) E E' (a_vis cs) Hag (pairs_vars_lt_app_l _ _ _ Fallow)).
    pose proof (u64_range a) as Hau.
    split.
    2:{ intros Hn0'. apply Ha. rewrite Hn0'. destruct (M a) eqn:Hma; [|reflexivity]. exfalso. exact (GRW a ltac:(congruence) Hn0'). }
    set (su := bv_unsigned (getr R (Z_to_bv 5 2))) in *.
    assert (Hin : su - 32 <= bv_unsigned a < su).
    { destruct (Z_lt_le_dec (bv_unsigned a) (su - 32)) as [Hlow|Hhigh]; [|destruct (Z_lt_le_dec (bv_unsigned a) su) as [Hi'|Habove]; [lia|]];
        exfalso; apply Ha; apply AGR; cbn [outside]; (split; [|exact I]); unfold in_rng; rewrite u64_lit by (unfold DN.SPLO, DN.SPHI, DN2.FR_SNL in Hsp; lia); lia. }
    right. right. left. rewrite <- (co_top HC).
    unfold DN.frame_ok in Hfr. rewrite Hsq in Hfr.
    assert (Hrng : estart E (SA spb (spk - DN2.FR_SNL)) <= bv_unsigned a < estart E (SA spb (spk - DN2.FR_SNL)) + elenZ E (ELit DN2.FR_SNL)).
    { rewrite estart_SA. unfold elenZ, DN2.FR_SNL in *. cbn [edenot]. rewrite u64_lit by lia. lia. }
    exact (proj1 (GPS.in_floor_sound RSEGS E M (kn cs) (acs_floor (a_maps cs)) (a_brk cs) (a_ylo cs) spb (spk - DN2.FR_SNL) (ELit DN2.FR_SNL) a (co_know HC) Hfr (co_floor HC) Hrng)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma read_dir_node : forall ms model x8,
  m_halted model = None -> m_vm_lazy model = [] ->
  ms_svc_pending ms = Some x8 -> bv_unsigned x8 = 63 ->
  fd_lookup (m_fds model) (ms_gpr ms 0) = Some State.FdDir -> fd32 (ms_gpr ms 0) = ms_gpr ms 0 ->
  access_okb (ms_gpr ms 1) (bv_unsigned (ms_gpr ms 2)) = true ->
  node_ok RSEGS (mkCfg ms model) unit (fun _ => []) (fun _ => mkCfg (advance_past_svc (set_gpr0 ms (errno_ret EISDIR))) model).
Proof.
  intros ms model x8 Hh Hlazy Hsvc Hno Hfd Hfd32 Haok.
  apply (node_ret_only RSEGS ms model x8 (errno_ret EISDIR) _ [] Hh Hsvc); [| exact Hh | exact Hlazy].
  intros eff. rewrite (check_syscall_63 RSEGS ms x8 eff model Hno). unfold check_read. rewrite Hfd32, Hfd, Haok. reflexivity.
Qed.

Variable DIRD : bool.
Hypothesis FDS3d : DIRD = true -> fd_lookup FDS0 (Z_to_bv 64 3) = Some State.FdDir.

Theorem node_read_dir_sound : DIRD = true ->
  GPS.node1_stmtN RSEGS nx0 PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ GPS.always (DN2.node_read_dir RSEGS).
Proof.
  intros HD cs cs' E fx R M model T HT HC _ Hn Hk.
  unfold DN2.node_read_dir in Hn.
  destruct (reg_lit cs 11) as [b|] eqn:R11; [|discriminate].
  destruct (reg_lit cs 12) as [c|] eqn:R12; [|discriminate].
  match type of Hn with (if ?x then _ else _) = _ => destruct x eqn:Hc; [|discriminate] end.
  injection Hn as <-.
  apply andb_prop in Hc as [Hc Hbc]. apply andb_prop in Hc as [Hc Hc0]. apply andb_prop in Hc as [Hc Hb0]. apply andb_prop in Hc as [Hsys H10].
  apply Z.leb_le in Hbc. apply Z.leb_le in Hc0. apply Z.leb_le in Hb0.
  unfold DN.at_sys in Hsys. apply andb_prop in Hsys as [Hec H17].
  unfold DN.reg_is in H17, H10.
  destruct (reg_lit cs 17) as [a7|] eqn:R17; [|discriminate]. apply Z.eqb_eq in H17. subst a7.
  destruct (reg_lit cs 10) as [fd|] eqn:R10; [|discriminate]. apply Z.eqb_eq in H10. subst fd.
  destruct (GPS.is_ecall_at_sound RSEGS cs Hec) as (w & HF & HE & Hpc0 & Hpc4).
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 17 63 HC ltac:(lia) R17) as [G17 _].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 10 3 HC ltac:(lia) R10) as [G10 _].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 11 b HC ltac:(lia) R11) as [G11 U11].
  destruct (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E cs fx R M model 12 c HC ltac:(lia) R12) as [G12 U12].
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
  (* [comment removed for export] *)
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) (getr R 17))
    with (@epend fx R (Z_to_bv 64 (pc cs)) M (seg_rom RSEGS) (getr R 17)).
  (* [comment removed for export] *)
  eapply (sr_silent1 RSEGS SR).
  { eapply (read_dir_node _ model (getr R 17)); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | | | |].
    - rewrite G17. apply u64_lit. lia.
    - rewrite ms_gpr_epend0, G10, (co_fds HC). exact (FDS3d HD).
    - rewrite ms_gpr_epend0, G10. vm_compute. reflexivity.
    - rewrite ms_gpr_epend1, ms_gpr_epend2, G11, G12. unfold access_okb, TASK_SIZE.
      rewrite !u64_lit by (unfold two64 in *; lia). apply andb_true_intro. split; apply Z.leb_le; lia. }
  (* [comment removed for export] *)
  rewrite adv_set_epend. rewrite v_addi_pc4 by (unfold two64 in *; lia).
  specialize (Hk E fx (regupd R 10 (errno_ret EISDIR)) M model (conj (env_agree_refl _ _) (env_agree_refl _ _))).
  rewrite set_pc_set_reg_eq in Hk. unfold cfgF, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk. unfold pc.
  apply Hk; [|reflexivity].
  eapply (GPS.cs_ok_frame RSEGS SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV);
    [exact HC | | reflexivity | exact (co_know HC) | exact (co_fx HC) | intros a Ha; exfalso; exact (Ha eq_refl)].
  cbn [mk_ss s_regs].
  apply (regs_ok_set_n E (s_regs (a_ss cs)) R 10 (ELit (two64 - 21)) (errno_ret EISDIR) (co_regs HC) ltac:(lia)).
  cbn [edenot]. apply bv_eq. reflexivity.
Qed.

Theorem XEe_sound : GPS.emit_stmt RSEGS nx0 (DN2.XEe RSEGS nx0) PERMc SPTOPc FS0 FDS0 AINV FXOK UINV RZ.
Proof.
  intros id args cs fd ps cs' E fx R M model T HC Hn HT Hk. unfold DN2.XEe in Hn.
  do 66 (destruct id as [|id]; [exact (XEd_sound SR nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree SR_det SWINc FDS1 FDS2 _ args cs fd ps cs' E fx R M model T HC Hn HT Hk)|]).
  destruct id as [|id]; [exact (node_stdio_write2_sound cs fd ps cs' E fx R M model T HC Hn HT Hk)|].
  exact (XEd_sound SR nx0 SWIN PERMc SPTOPc FS0 FDS0 AINV AINV_frame FXOK UINV UINV_agree SR_det SWINc FDS1 FDS2 _ args cs fd ps cs' E fx R M model T HC Hn HT Hk).
Qed.
End Sound.
End UbDrvNodes2Sound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvESound.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesLibc OSSVerify.Proofs.glaze.binary_reflection.lib.GlzNodesLibcUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesBlob OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.UbDrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes2 UbDrvNodes2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ERRW : Z * Z := (ERRNO, ERRNO + 4).
Definition PERM_Ec : list (Z * Z) := PERM_Tc ++ [ERRW].
Definition SWIN_E : list (Z * Z) := SWIN_T ++ [ERRW].
(* [comment removed for export] *)
Definition priv_minus_errno (ps : list (Z * Z)) : list (Z * Z) :=
  flat_map (fun lh : Z * Z => let '(lo, hi) := lh in
              if ((lo <=? ERRNO) && (ERRNO + 4 <=? hi))%bool
              then (if lo <? ERRNO then [(lo, ERRNO)] else []) ++ (if ERRNO + 4 <? hi then [(ERRNO + 4, hi)] else [])
              else [(lo, hi)]) ps.
Definition GE : gtable :=
  {| g_ro_lo := g_ro_lo GUBSAN; g_ro_hi := g_ro_hi GUBSAN; g_img_lo := g_img_lo GUBSAN; g_img_hi := g_img_hi GUBSAN;
     g_newh_got := g_newh_got GUBSAN; g_newh_cell := g_newh_cell GUBSAN; g_newh_val := g_newh_val GUBSAN;
     g_priv := priv_minus_errno (g_priv GUBSAN);
     g_tp := g_tp GUBSAN; g_malloc := g_malloc GUBSAN; g_free := g_free GUBSAN; g_malloc_thunk := g_malloc_thunk GUBSAN; g_free_thunk := g_free_thunk GUBSAN;
     g_opnew := g_opnew GUBSAN; g_opdel := g_opdel GUBSAN; g_opdel_sized := g_opdel_sized GUBSAN; g_memcpy := g_memcpy GUBSAN; g_memset := g_memset GUBSAN;
     g_memmove := g_memmove GUBSAN; g_strlen := g_strlen GUBSAN; g_hello := g_hello GUBSAN; g_str_resize := g_str_resize GUBSAN |}.


Lemma PERM_Ec_den : forall E, wins_den E PERM_E = PERM_Ec. Proof. reflexivity. Qed.
Lemma GE_ro_img : g_img_lo GE <= g_ro_lo GE /\ g_ro_lo GE <= g_ro_hi GE <= g_img_hi GE. Proof. cbn. lia. Qed.
Lemma GE_img_ceil {RC : run_ceil} : g_img_hi GE <= CEIL_run. Proof. pose proof ceil_rng. cbn [g_img_hi GE GUBSAN]. lia. Qed.




Lemma SWIN_Ec : forall a, (DN.FILE1 <= a < DN.FILE1 + 232 \/ DN.FILE2 <= a < DN.FILE2 + 232) -> in_wins SWIN_E a.
Proof. intros a H. destruct (SWIN_Tc a H) as (lo & hi & Hin & Hz). exists lo, hi. split; [|exact Hz]. unfold SWIN_E. apply in_app_iff. left. exact Hin. Qed.
Lemma PERM_E_SWIN : forall z, in_wins PERM_Ec z -> in_wins SWIN_E z.
Proof.
  intros z (lo & hi & Hin & Hz). unfold PERM_Ec in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (PERM_T_SWIN z ltac:(exists lo, hi; split; [exact Hin | exact Hz])) as (lo' & hi' & Hin' & Hz'). exists lo', hi'. split; [|exact Hz']. unfold SWIN_E. apply in_app_iff. left. exact Hin'.
  - exists lo, hi. split; [|exact Hz]. unfold SWIN_E. apply in_app_iff. right. exact Hin.
Qed.

(* [comment removed for export] *)
Section SHP.
Context {RC : run_ceil}.
Definition SHP (L : list (Z * Z)) (B C : Z) (M : mem) (mdl : Model) : Prop :=
  (forall b m, In (b, m) L -> GlzSpecsStr.GlzContracts.blk_ok GE b m)
  /\ (forall L1 L2 b m b' m', L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b).
Lemma SHP_frame : forall L B C M M' mdl,
  SHP L B C M mdl ->
  (forall a, M' a <> M a -> (in_blocks L (bv_unsigned a) \/ CEIL_run <= bv_unsigned a \/ in_wins SWIN_E (bv_unsigned a)) /\ M' a <> None) ->
  SHP L B C M' mdl.
Proof. intros L B C M M' mdl H _. exact H. Qed.
Lemma SHP_zone : forall L B C M mdl b m, SHP L B C M mdl -> In (b, m) L -> GlzSpecsStr.GlzContracts.blk_ok GE b m.
Proof. intros L B C M mdl b m [H _]. apply H. Qed.
Lemma SHP_disj : forall L B C M mdl L1 L2 b m b' m',
  SHP L B C M mdl -> L = L1 ++ (b, m) :: L2 -> In (b', m') (L1 ++ L2) -> b + m <= b' \/ b' + m' <= b.
Proof. intros L B C M mdl L1 L2 b m b' m' [_ H]. apply H. Qed.

Lemma SHP_of_AINV_R : forall L B C M mdl, AINV_R L B C M mdl -> SHP L B C M mdl.
Proof.
  intros L B C M mdl H. split.
  - intros b m Hin. pose proof (AINV_R_zone_T L B C M mdl b m H Hin) as X. unfold GlzSpecsStr.GlzContracts.blk_ok in *. cbn [g_img_lo g_img_hi GE GDRV GUBSAN] in *. exact X.
  - intros L1 L2 b m b' m'. exact (AINV_R_disj_T L B C M mdl L1 L2 b m b' m' H).
Qed.

End SHP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section ESound.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
#[local] Notation AINVe TOP M0 := (AINV_f SWIN_E GE SHP PERM_Ec TOP [] M0 0 0).
#[local] Notation cs_okE TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok U).

Lemma AF_E : forall TOP M0 Lc B C M M' mdl,
  AINVe TOP M0 Lc B C M mdl -> (forall a, M' a <> M a -> owned SWIN_E PERM_Ec TOP Lc a /\ M' a <> None) -> AINVe TOP M0 Lc B C M' mdl.
Proof. intros TOP M0. exact (AINV_f_frame SWIN_E GE SHP SHP_frame SHP_zone SHP_disj GE_ro_img GE_img_ceil PERM_Ec TOP [] M0 0 0). Qed.

Section Inst.
Variables (TOP : Z) (FS0 : Fs.Fs) (FDS0 : list (word * FdEntry)) (M0 : word -> option byte).
Hypothesis FDS1 : fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)).
Hypothesis FDS2 : fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)).
Variable UINV : env -> Prop.
Hypothesis UINV_agree : forall E E', env_agree NXD E E' -> UINV E -> UINV E'.
(* [comment removed for export] *)
Variable NZBc : list nat.
Hypothesis UINV_nz : forall E j, UINV E -> In j NZBc -> ~ In (Z_to_bv 8 0) (eb E j).

(* [comment removed for export] *)
Variable DIRD : bool.
Hypothesis FDS3d : DIRD = true -> fd_lookup FDS0 (Z_to_bv 64 3) = Some State.FdDir.

Lemma XNE_sound : GPS.ext_stmt RSEGS NXD (XNE NZBc DIRD) PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV RZ.
Proof.
  intros id args cs cs' E fx R M model T HT HC Hp Hn Hk. unfold XNE, DN2.XNe in Hn.
  pose proof (AF_E TOP M0) as AF.
  destruct id as [|id]; [discriminate Hn|].
  destruct id as [|id].
  { exact (ubsan_OBL_memcpy ADRV NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV UINV_agree RZ (sr_msteps RSEGS SR) GDRV eq_refl
             cs cs' E fx R M model T HC Hp Hn Hk). }
  do 3 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id].
  { exact (GNB.node_memcpy_blob_sound RSEGS ADRV NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV UINV_agree RZ (sr_msteps RSEGS SR) GDRV
             ubsan_copy_spec cs cs' E fx R M model T HC Hp Hn Hk). }
  do 57 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id].
  { exact (node_ioctl_sound SR NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV FDS1 FDS2 cs cs' E fx R M model T HT HC Hp Hn Hk). }
  do 3 (destruct id as [|id]; [discriminate Hn|]).
  destruct id as [|id].
  { exact (node_strnlen_sound SR NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV UINV_agree NZBc UINV_nz cs cs' E fx R M model T HT HC Hp Hn Hk). }
  destruct id as [|id]; [| discriminate Hn].
  pose proof FDS3d as F3. destruct DIRD; [| discriminate Hn].
  exact (node_read_dir_sound SR NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV true F3 eq_refl cs cs' E fx R M model T HT HC Hp Hn Hk).
Qed.

Lemma XEE_sound : GPS.emit_stmt RSEGS NXD XEE PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV RZ.
Proof.
  unfold XEE. pose proof (AF_E TOP M0) as AF.
  exact (XEe_sound SR NXD SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF fx_ok UINV UINV_agree (SR_det_of_exact SR SRX) SWIN_Ec FDS1 FDS2).
Qed.

Lemma XB0_sound_E : GPS.ext2_stmt RSEGS NXD XB0 PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV RZ.
Proof. intros id args cs csa csb E1 fx1 R1 M1 m1 T1 HC1 Hn. discriminate Hn. Qed.
Lemma XC0_sound_E : GPS.alt2x_stmt RSEGS NXD XC0 PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV RZ.
Proof. intros id args cs csa csb E1 fx1 R1 M1 m1 Ta Tb HX Hn. discriminate Hn. Qed.

Theorem drvE_cert_sound : forall (HS : nat -> option acs) (HOLES : nat -> env -> Fs.Fs -> TSet),
  (forall h E E' fs, env_agree NXD E E' -> HOLES h E fs = HOLES h E' fs) ->
  (forall h E fs, HOLES h E fs []) ->
  (forall h E fs, HOLES h E fs = HOLES 0%nat E fs) ->
  GPS.holes_stmt RSEGS HS PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok UINV HOLES RZ ->
  forall bf fuel p cs s E fx R M model,
  gplan_ok p = true -> CHKe NZBc DIRD HS bf fuel cs p = COk s ->
  cs_okE TOP FS0 FDS0 M0 UINV E cs fx R M model -> m_fs model = FS0 ->
  RZ (cfgF RSEGS fx R (pc cs) M model) (sd HOLES t_nil E FS0 s).
Proof.
  intros HS HOLES Hag Hnil Hsame HST bf fuel p cs s E fx R M model Hp CERT HC Hfs.
  pose proof (AF_E TOP M0) as AF. rewrite <- Hfs.
  refine (GPS.check_sound RSEGS ITE ITE_ok ADRV NXD LIMIT HS (XNE NZBc DIRD) XEE XB0 XC0 0%nat SWIN_E PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) AF
            fx_ok UINV UINV_agree HOLES Hag Hnil Hsame
            RZ (sr_step RSEGS SR) (sr_msteps RSEGS SR) (sr_exit RSEGS SR) (sr_conseq RSEGS SR) (RUN_sound_fx RSEGS) ubsan_in_hull ubsan_hull_ok
            XNE_sound XEE_sound XB0_sound_E XC0_sound_E HST
            fuel bf None p cs s Hp CERT E fx R M model t_nil HC I eq_refl).
Qed.
End Inst.
End ESound.
End UbDrvESound.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvS0Sound.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupTac OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup UbStartupFacts OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0.UbMhImgR0 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0.UbMhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.PuPeel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac peel ::= peel_fast.
#[local] Ltac SumsLib.StartupTac.addr_norm ::= addr_norm_fast.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
#[local] Existing Instance fx0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma bytes_le_to_Z_cons' : forall (b : byte) bs,
  bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256.
Proof.
  intros b bs. cbn [bytes_le_to_Z]. pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
  rewrite <- Z.lxor_lor.
  - rewrite Z.add_nocarry_lxor; [reflexivity|].
    apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
  - apply Z.bits_inj'; intros i Hi; rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases i 8) as [Hi8|Hi8].
    + change 256 with (2 ^ 8). rewrite Z.mul_pow2_bits_low by lia. apply andb_false_r.
    + rewrite (Z_testbit_high 8 (bv_unsigned b) i) by lia. reflexivity.
Qed.
Lemma Z_to_le_bytes_to_Z' : forall bs, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|].
  cbn [length Z_to_le_bytes]. rewrite bytes_le_to_Z_cons'.
  pose proof (u8_range b) as Hb. pose proof (bytes_le_to_Z_nonneg bs) as Hr.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. lia.
  - rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 8) with 256.
    replace ((bv_unsigned b + bytes_le_to_Z bs * 256) / 256) with (bytes_le_to_Z bs) by lia. exact IH.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma le8_word : forall bs, length bs = 8%nat -> word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros bs Hl. unfold word_to_le_bytes. pose proof (bytes_le_to_Z_bound bs) as B. rewrite Hl in B. pose proof (bytes_le_to_Z_nonneg bs).
  rewrite u64_lit by (cbn in B; lia). rewrite <- Hl. apply Z_to_le_bytes_to_Z'.
Qed.

(* [comment removed for export] *)
Lemma rdn1_overlay : forall M (a : word) b, seg_rom RSEGS a = None -> rdn RSEGS M a 1 = Some [b] -> M a = Some b.
Proof.
  intros M a b Hs H. cbn [rdn] in H. destruct (M a) as [b'|]; [| rewrite Hs in H; discriminate H].
  injection H as <-. reflexivity.
Qed.
Lemma seg_rom_high : forall a : word, 0xac000 <= bv_unsigned a -> seg_rom RSEGS a = None.
Proof.
  intros a Ha. apply (APS.seg_rom_off_hull RSEGS AUBSAN ubsan_in_hull). unfold APS.in_hull. cbn [img_lo img_hi AUBSAN].
  apply Bool.andb_false_iff. right. apply Z.ltb_ge. exact Ha.
Qed.

(* [comment removed for export] *)
Lemma missb_point : forall cells lo n i,
  forallb (range_disjoint_b lo n) cells = true -> lo <= i < lo + Z.of_nat n -> forallb (range_disjoint_b i 1) cells = true.
Proof.
  intros cells lo n i H Hi. induction cells as [|c cells IH]; [reflexivity|].
  cbn [forallb] in H |- *. apply andb_prop in H as [Hc Hr]. rewrite (IH Hr), Bool.andb_true_r.
  unfold range_disjoint_b in Hc |- *. apply Bool.orb_true_iff in Hc. apply Bool.orb_true_iff. cbn [Z.of_nat Pos.of_succ_nat].
  destruct Hc as [Hc|Hc]; apply Z.leb_le in Hc; [left | right]; apply Z.leb_le; lia.
Qed.
Lemma D_main_missb_point : forall lo n i, D_main_missb lo n = true -> lo <= i < lo + Z.of_nat n -> D_main_missb i 1 = true.
Proof.
  intros lo n i H Hi. unfold D_main_missb in H |- *. apply andb_prop in H as [H H2]. apply andb_prop in H as [H H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  rewrite (missb_point _ lo n i H Hi). cbn [Z.of_nat Pos.of_succ_nat andb]. apply Bool.andb_true_iff. split; apply Z.leb_le; lia.
Qed.

(* [comment removed for export] *)
Lemma img_78c50_8 : rdn RSEGS (fun _ => None) (Z_to_bv 64 0x78ca0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x8a050)).
Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Bridge.
Context {RC : run_ceil}.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.

#[local] Notation s0 := (bv_unsigned sp0).
#[local] Notation stk := (stack_to_mem sp0 (entry_stack_image RPH sp0 av ev uid hw rdraw)).
#[local] Notation DM := (D_main sp0 av ev hw rdraw tid).

Lemma Hlo : 0x7fff80000000 <= s0. Proof using Hvsp. destruct Hvsp as (H & _). unfold sp_window_lo in H. exact H. Qed.
Lemma Hhi : s0 <= 0x800000000000. Proof using Hvsp. destruct Hvsp as (_ & H & _). unfold sp_window_hi in H. exact H. Qed.
Lemma Hal : s0 mod 16 = 0. Proof using Hvsp. destruct Hvsp as (_ & _ & H). exact H. Qed.
Lemma Hsplo : (sp_window_lo <= s0)%Z. Proof using Hvsp. exact (proj1 Hvsp). Qed.
Lemma Hsphi : (s0 <= sp_window_hi)%Z. Proof using Hvsp. exact (proj1 (proj2 Hvsp)). Qed.
Lemma len_av' : (1 <= length av <= 1024)%nat. Proof using Hva. destruct Hva as [[H1 H2] _]. lia. Qed.
Lemma len_ev' : (length ev <= 256)%nat. Proof using Hve. destruct Hve as [H1 _]. lia. Qed.

(* [comment removed for export] *)
Definition TOPm : Z := s0 - 48.
Definition SSZ : Z := Z.of_nat (cat_struct_size av ev).            (* [comment removed for export] *)
Definition P0 : Z := s0 + SSZ.                                        (* [comment removed for export] *)
Definition L0v : Z := Z.of_nat (length (nth 0 av [])).
Definition P1 : Z := s0 + SSZ + L0v + 1.                              (* [comment removed for export] *)
Definition L1v : Z := Z.of_nat (length (nth 1 av [])).
Definition ENVv : Z := s0 + 16 + 8 * Z.of_nat (length av).
Definition AUXW : Z := s0 + Z.of_nat (auxv_off av ev).
Definition RNDP : Z := bv_unsigned (at_random_ptr sp0 av ev).
(* [comment removed for export] *)
Definition AUXWORDS : list word :=
  [AT_PHDR; Z_to_bv 64 (Z.of_N (ph_addr RPH)); AT_PHENT; Z_to_bv 64 (Z.of_N (ph_ent RPH)); AT_PHNUM; Z_to_bv 64 (Z.of_N (ph_num RPH));
   AT_HWCAP; hw; AT_PAGESZ; Z_to_bv 64 4096; AT_UID; uid; AT_EUID; uid; AT_SECURE; Z_to_bv 64 0; AT_RANDOM; at_random_ptr sp0 av ev; AT_NULL; Z_to_bv 64 0].
Definition avp (j : nat) : Z * Z := (bv_unsigned (nth (2 * j) AUXWORDS (Z_to_bv 64 0)), bv_unsigned (nth (2 * j + 1) AUXWORDS (Z_to_bv 64 0))).
Definition AVL : list (Z * Z) := [avp 0; avp 1; avp 2; avp 3; avp 4; avp 5; avp 6; avp 7; avp 8].

Lemma SSZ_val : SSZ = 8 + 8 * (Z.of_nat (length av) + 1) + 8 * (Z.of_nat (length ev) + 1) + 160.
Proof using. unfold SSZ, cat_struct_size, auxv_size. lia. Qed.
Lemma SSZ_rng : 192 <= SSZ <= 10424.
Proof using Hve Hva. rewrite SSZ_val. pose proof len_av'. pose proof len_ev'. lia. Qed.
Lemma L0_rng : 0 <= L0v <= 131071.
Proof using Hva. unfold L0v. pose proof (valid_argv_str_len av 0 Hva ltac:(pose proof len_av'; lia)). lia. Qed.
Lemma P0_val : bv_unsigned (cat_argv_ptr sp0 av ev 0) = P0.
Proof using Hvsp Hve Hva rdraw hw uid.
  unfold P0, SSZ. rewrite (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve Hsplo Hsphi 0 ltac:(pose proof len_av'; lia)).
  replace (total_arg_bytes_nat (firstn 0 av)) with 0%nat by reflexivity. lia.
Qed.
Lemma bsb_len : Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) <= 2240000.
Proof using Hve Hva. exact (lay_bsb_len RPH sp0 rdraw av ev uid hw Hva Hve). Qed.
Lemma bsb_nw' : s0 + Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) < 2 ^ 64.
Proof using Hvsp Hve Hva. exact (lay_bsb_nw RPH sp0 rdraw av ev uid hw Hva Hve Hsphi). Qed.


(* [comment removed for export] *)
Lemma rd_above : forall (a : word) n, s0 <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= 2 ^ 64 ->
  rdn RSEGS mem a n = rdn RSEGS stk a n.
Proof using ME regs tid.
  intros a n Ha Hn. rewrite (main_entry_rdn_above sp0 av ev uid hw rdraw tid regs mem ME RSEGS a n Ha Hn).
  exact (rdn_wmem_stack RSEGS RPH sp0 av ev uid hw rdraw a n Ha Hn).
Qed.
Lemma rd_aboveZ : forall (a : Z) n, s0 <= a -> a + Z.of_nat n < 2 ^ 64 ->
  rdn RSEGS mem (Z_to_bv 64 a) n = rdn RSEGS stk (Z_to_bv 64 a) n.
Proof using ME Hvsp regs tid. intros a n Ha Hn. pose proof Hlo. apply rd_above; rewrite u64_lit; lia. Qed.
Lemma rd_image : forall (a : Z) (n : nat), D_main_missb a n = true ->
  rdn RSEGS mem (Z_to_bv 64 a) n = rdn RSEGS (fun _ => None) (Z_to_bv 64 a) n.
Proof using ME Hvsp regs tid rdraw hw uid ev av sp0. intros a n Hb. exact (main_entry_rdn_image sp0 av ev uid hw rdraw tid Hlo regs mem ME RSEGS a n Hb). Qed.
Lemma mem_none : forall lo (n : nat), D_main_missb lo n = true -> forall i, lo <= i < lo + Z.of_nat n -> mem (Z_to_bv 64 i) = None.
Proof using ME Hvsp regs tid rdraw hw uid ev av sp0.
  intros lo n Hb i Hi.
  pose proof (D_main_missb_point lo n i Hb Hi) as Hb1.
  assert (Hr : 0 <= i /\ i + 1 <= 0x100000).
  { unfold D_main_missb in Hb1. apply andb_prop in Hb1 as [H H2]. apply andb_prop in H as [_ H1]. apply Z.leb_le in H1. apply Z.leb_le in H2. cbn in H2. lia. }
  pose proof Hlo. rewrite (main_entry_mem_data sp0 av ev uid hw rdraw tid regs mem ME) by (rewrite u64_lit, stack_max_size_val by lia; lia).
  pose proof (D_main_miss sp0 av ev hw rdraw tid [] i 1%nat Hb1) as DMM.
  cbn [rdn] in DMM. destruct (DM (Z_to_bv 64 i)) as [b|]; [|reflexivity].
  unfold seg_rom in DMM. cbn in DMM. discriminate DMM.
Qed.
Lemma mem_win : forall i, s0 - 8388608 <= i < s0 -> mem (Z_to_bv 64 i) <> None.
Proof using ME Hvsp regs tid rdraw hw uid ev av.
  intros i Hi. pose proof Hlo. pose proof Hhi. apply (main_entry_win_mapped sp0 av ev uid hw rdraw tid regs mem ME). rewrite u64_lit, stack_max_size_val by lia. lia.
Qed.
Lemma store_win : forall i (m : nat), s0 - 8388608 <= i -> i + Z.of_nat m <= s0 -> store_ok RSEGS mem (Z_to_bv 64 i) m = true.
Proof using ME Hvsp regs tid rdraw hw uid ev av.
  intros i m H1 H2. pose proof Hlo. pose proof Hhi. apply (main_entry_store_ok_win sp0 av ev uid hw rdraw tid regs mem ME); rewrite u64_lit, ?stack_max_size_val by lia; lia.
Qed.
(* [comment removed for export] *)
Lemma rd_argv_byte : forall k j, (k < length av)%nat -> (j <= length (nth k av []))%nat ->
  rdn RSEGS mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp0 av ev k) + Z.of_nat j)) 1%nat = Some [nth j (nth k av [] ++ [Z_to_bv 8 0]) (Z_to_bv 8 0)].
Proof using ME Hvsp Hve Hva regs tid rdraw hw uid.
  intros k j Hk Hj.
  pose proof (argv_ptr_bounds_at sp0 av ev Hva Hve Hsphi k Hk) as [B1 B2].
  rewrite rd_aboveZ by lia. rewrite <- word_add_nat.
  exact (read_argv_byte_k RPH RSEGS sp0 av ev k j uid hw rdraw Hk Hj bsb_nw').
Qed.
Lemma mem_argv_byte : forall k j, (k < length av)%nat -> (j < length (nth k av []))%nat ->
  mem (Z_to_bv 64 (bv_unsigned (cat_argv_ptr sp0 av ev k) + Z.of_nat j)) = Some (nth j (nth k av []) (Z_to_bv 8 0)).
Proof using ME Hvsp Hve Hva regs tid rdraw hw uid.
  intros k j Hk Hj.
  pose proof (argv_ptr_bounds_at sp0 av ev Hva Hve Hsphi k Hk) as [B1 B2]. pose proof Hlo.
  apply rdn1_overlay; [apply seg_rom_high; rewrite u64_lit; lia|].
  rewrite (rd_argv_byte k j Hk ltac:(lia)). rewrite app_nth1 by exact Hj. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rd_argv_ptr : forall k, (k < length av)%nat ->
  rdn RSEGS mem (Z_to_bv 64 (s0 + 8 + 8 * Z.of_nat k)) 8%nat = Some (word_to_le_bytes 8 (cat_argv_ptr sp0 av ev k)).
Proof using ME Hvsp Hve Hva regs tid rdraw hw uid.
  intros k Hk. pose proof Hlo. pose proof Hhi. pose proof len_av'.
  rewrite (main_entry_rdn_above sp0 av ev uid hw rdraw tid regs mem ME RSEGS) by (rewrite u64_lit; lia).
  replace (Z_to_bv 64 (s0 + 8 + 8 * Z.of_nat k)) with (sp0 + nat_to_word (8 + 8 * k))%bv by (rewrite word_add_nat; f_equal; lia).
  rewrite <- n_to_le_8_spec. exact (read_argv_ptr_w RSEGS RPH sp0 av ev uid hw rdraw Hva Hve Hsplo Hsphi k Hk).
Qed.
Lemma rd_argc : rdn RSEGS mem (Z_to_bv 64 s0) 8%nat = Some (word_to_le_bytes 8 (argcN av)).
Proof using ME Hvsp Hve Hva regs tid rdraw hw uid ev.
  pose proof Hlo. pose proof Hhi.
  rewrite (main_entry_rdn_above sp0 av ev uid hw rdraw tid regs mem ME RSEGS) by (rewrite u64_lit; lia).
  rewrite Z_to_bv_bv_unsigned, <- n_to_le_8_spec. exact (read_argc_w RSEGS RPH sp0 av ev uid hw rdraw Hva Hve Hsphi).
Qed.
(* [comment removed for export] *)
Lemma rd_auxv : forall j, (j < 20)%nat ->
  rdn RSEGS mem (Z_to_bv 64 (AUXW + 8 * Z.of_nat j)) 8%nat
  = Some (word_to_le_bytes 8 (nth j (auxv_words RPH (at_random_ptr sp0 av ev) uid hw) (Z_to_bv 64 0))).
Proof using ME Hvsp Hve Hva regs tid rdraw.
  intros j Hj. pose proof Hlo. pose proof Hhi. pose proof bsb_nw'.
  pose proof (auxv_off_bound RPH sp0 rdraw av ev uid hw) as AB. unfold AUXW.
  rewrite rd_aboveZ by lia.
  replace (Z_to_bv 64 (s0 + Z.of_nat (auxv_off av ev) + 8 * Z.of_nat j)) with (sp0 + nat_to_word (auxv_off av ev + 8 * j))%bv by (rewrite word_add_nat; f_equal; lia).
  rewrite <- n_to_le_8_spec. exact (read_auxv_word RSEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsphi j Hj).
Qed.
Lemma AUXW_rng : s0 + 32 <= AUXW /\ AUXW + 176 <= s0 + 2240000 /\ AUXW mod 8 = 0.
Proof using Hvsp Hve Hva rdraw hw uid.
  pose proof (auxv_off_bound RPH sp0 rdraw av ev uid hw) as AB. pose proof bsb_len as BL. pose proof len_av'. pose proof Hal.
  unfold AUXW. split; [unfold auxv_off; lia|]. split; [lia|]. unfold auxv_off.
  rewrite Z.add_mod by lia. replace (s0 mod 8) with 0.
  2:{ symmetry. rewrite <- (Z.mod_mod_divide _ 16 8) by (exists 2; reflexivity). rewrite Hal. reflexivity. }
  replace (Z.of_nat (8 + 8 * (length av + 1) + 8 * (length ev + 1))) with (8 * (Z.of_nat (length av) + Z.of_nat (length ev) + 3)) by lia.
  rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.
Lemma RND_facts : s0 <= RNDP /\ RNDP + 16 <= s0 + 2240000 /\ RNDP mod 8 = 0 /\
  rdn RSEGS mem (Z_to_bv 64 (RNDP + 8)) 8%nat = Some (firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw)))).
Proof using ME Hvsp Hve Hva regs tid hw uid.
  destruct (rnd_facts RSEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsplo Hsphi Hal) as (R1 & R2 & R3 & R4 & R5).
  pose proof bsb_len. unfold RNDP. split; [lia|]. split; [lia|]. split; [exact R4|].
  pose proof Hlo. rewrite rd_aboveZ by lia. replace (bv_unsigned (at_random_ptr sp0 av ev) + 8) with (bv_unsigned (at_random_ptr sp0 av ev) + Z.of_nat 8) by lia.
  apply R5. lia.
Qed.

(* [comment removed for export] *)
Lemma targ_firstn_S : forall (l : list (list byte)) k, (k < length l)%nat ->
  (total_arg_bytes_nat (firstn (S k) l) = total_arg_bytes_nat (firstn k l) + length (nth k l []) + 1)%nat.
Proof using.
  intros l k. revert l. induction k as [|k IH]; intros l Hk.
  - destruct l as [|a l]; [cbn in Hk; lia|]. change (firstn 1 (a :: l)) with [a]. change (firstn 0 (a :: l)) with (@nil (list byte)). cbn [nth].
    rewrite total_arg_bytes_cons. change (total_arg_bytes_nat []) with 0%nat. lia.
  - destruct l as [|a l]; [cbn in Hk; lia|]. change (firstn (S (S k)) (a :: l)) with (a :: firstn (S k) l). change (firstn (S k) (a :: l)) with (a :: firstn k l).
    cbn [nth]. rewrite !total_arg_bytes_cons. rewrite (IH l) by (cbn in Hk; lia). lia.
Qed.
Lemma str_end_le : forall k, (k < length av)%nat ->
  bv_unsigned (cat_argv_ptr sp0 av ev k) + Z.of_nat (length (nth k av [])) + 1 <= s0 + SSZ + Z.of_nat (total_arg_bytes_nat av).
Proof using Hvsp Hve Hva rdraw hw uid.
  intros k Hk. rewrite (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve Hsplo Hsphi k Hk). unfold SSZ.
  pose proof (total_arg_bytes_firstn_le (S k) av) as B. rewrite (targ_firstn_S av k Hk) in B. lia.
Qed.
Lemma RNDP_ge : s0 + SSZ + Z.of_nat (total_arg_bytes_nat av) <= RNDP.
Proof using Hvsp Hve Hva rdraw hw uid.
  unfold RNDP, at_random_ptr, SSZ, cat_struct_size. rewrite word_add_nat.
  pose proof (struct_av_bound RPH sp0 rdraw av ev uid hw Hva Hve) as SB. unfold cat_struct_size in SB. pose proof Hlo. pose proof Hhi.
  pose proof (length_flatten_strings av) as FA. pose proof (length_flatten_strings ev) as FE.
  destruct Hve as [He1 [He2 _]]. rewrite total_arg_bytes_Z in He2.
  pose proof (Z.mod_pos_bound (8 - Z.of_nat (8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size + length (flatten_strings av) + length (flatten_strings ev)) mod 8) 8 ltac:(lia)) as MB.
  unfold auxv_size in *.
  match goal with |- _ <= bv_unsigned (Z_to_bv 64 ?x) => assert (XR : 0 <= x < 2 ^ 64) by lia end.
  rewrite u64_lit by exact XR. lia.
Qed.
Lemma BE_le : s0 + Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) <= 2 ^ 47.
Proof using Hfits.
  pose proof (build_stack_bytes_within_span RPH sp0 av ev uid hw rdraw) as B. unfold entry_stack_fits, sp_window_hi in Hfits. lia.
Qed.
(* [comment removed for export] *)
Lemma mem_block : forall a, s0 <= a < s0 + Z.of_nat (length (build_stack_bytes RPH sp0 av ev uid hw rdraw)) -> mem (Z_to_bv 64 a) <> None.
Proof using ME Hfits Hvsp regs tid.
  intros a Ha. pose proof Hlo. pose proof BE_le.
  rewrite (main_entry_mem_above sp0 av ev uid hw rdraw tid regs mem ME) by (rewrite u64_lit; lia).
  unfold wrap_mem, stack_to_mem. rewrite u64_lit by lia.
  replace (s0 <=? a) with true by (symmetry; apply Z.leb_le; lia).
  unfold entry_stack_image. rewrite length_app.
  match goal with |- context [(?x <? ?y)] => replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia) end.
  destruct (nth_error _ _) as [b|] eqn:Hn; [discriminate|].
  apply nth_error_None in Hn. rewrite length_app in Hn. lia.
Qed.

(* [comment removed for export] *)
Lemma rd_newh_got : rdn RSEGS mem (Z_to_bv 64 0x78ca0) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0x8a050)).
Proof using ME Hvsp regs tid rdraw hw uid ev av sp0. rewrite rd_image by (vm_compute; reflexivity). exact img_78c50_8. Qed.
Lemma rd_need_locks : rdn RSEGS mem (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some (word_to_le_bytes 1 (Z_to_bv 64 0)).
Proof using ME Hvsp regs tid rdraw hw uid ev av sp0. unfold A_NEED_LOCKS. rewrite rd_image by (vm_compute; reflexivity). exact UbMhMallocR0.UbMhImgR0.img_8ae53_1. Qed.
Lemma rd_tid : rdn RSEGS mem (Z_to_bv 64 0x8aae8) 4%nat = Some (word_to_le_bytes 4 tid).
Proof using ME Hvsp regs rdraw hw uid ev av sp0. exact (main_entry_tid sp0 av ev uid hw rdraw tid Hlo regs mem ME RSEGS). Qed.
Lemma rd_guard : rdn RSEGS mem (Z_to_bv 64 0xaae00) 8%nat = Some (canary_bytes rdraw).
Proof using ME Hvsp regs tid hw uid ev av sp0. exact (main_entry_guard sp0 av ev uid hw rdraw tid Hlo regs mem ME RSEGS). Qed.
Lemma rd_pagesize : rdn RSEGS mem (Z_to_bv 64 0xaae50) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)).
Proof using ME Hvsp Hva regs tid rdraw hw uid ev av sp0.
  pose proof Hlo. rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME) by (rewrite u64_lit, stack_max_size_val by lia; cbn; lia).
  exact (D_main_pagesize sp0 av ev hw rdraw tid Hva RSEGS).
Qed.
Lemma rd_libc_auxv : rdn RSEGS mem (Z_to_bv 64 0xaae28) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 AUXW)).
Proof using ME Hvsp Hve Hva regs tid rdraw hw uid.
  pose proof Hlo. pose proof Hhi. pose proof len_av'. pose proof len_ev'. pose proof (u64_range tid).
  rewrite (main_entry_rdn_data sp0 av ev uid hw rdraw tid regs mem ME) by (rewrite u64_lit, stack_max_size_val by lia; cbn; lia).
  replace (Z_to_bv 64 AUXW) with (auxv_w sp0 av ev) by (unfold auxv_w, AUXW, auxv_off; f_equal; lia).
  unfold D_main, D_fd, D_ssp, D_tls, D_tlsB, D_tlsA, D_libc. peel. apply rdn_wbytes_hit8. unorm; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EM (v4 : Z) (b7 : list byte) : env :=
  Env (fun n => match n with
                | 0 => Z_to_bv 64 TOPm | 1 => argcN av | 2 => Z_to_bv 64 (P0 - TOPm) | 3 => Z_to_bv 64 L0v | 4 => Z_to_bv 64 v4
                | 5 => Z_to_bv 64 (P1 - TOPm) | 6 => Z_to_bv 64 L1v | 7 => tid | 8 => Z_to_bv 64 (bytes_le_to_Z (canary_bytes rdraw))
                | 10 => getr regs 5 | 11 => getr regs 6 | 12 => getr regs 7
                | 15 => getr regs 13 | 16 => getr regs 14 | 17 => getr regs 15 | 18 => getr regs 16 | 19 => getr regs 17
                | 21 => getr regs 28 | 22 => getr regs 29 | 23 => getr regs 30 | 24 => getr regs 31
                | 25 => Z_to_bv 64 ENVv
                | _ => Z_to_bv 64 0 end%nat)
      (fun j => match j with 1 => nth 0 av [] | 2 => nth 1 av [] | 7 => b7 | _ => [] end%nat).

Section WithVal.
Variables (v4 : Z) (b7 : list byte).
#[local] Notation E := (EM v4 b7).

Lemma uE0 : uE E SP0 = TOPm. Proof using Hvsp. unfold uE. cbn. pose proof Hlo. pose proof Hhi. unfold TOPm. apply u64_lit. lia. Qed.
Lemma uE_add : forall a b, uE E a + uE E b < 2 ^ 64 -> uE E (EAlu Instr.ALU_ADD a b) = uE E a + uE E b.
Proof using.
  intros a b H. unfold uE in *. cbn [edenot]. pose proof (u64_range (edenot E a)). pose proof (u64_range (edenot E b)).
  rewrite u_add64. apply Z.mod_small. lia.
Qed.
Lemma uE_STR0 : uE E STR0 = P0.
Proof using Hvsp Hve Hva.
  pose proof Hlo. pose proof Hhi. pose proof SSZ_rng.
  assert (U2 : uE E D0 = P0 - TOPm) by (unfold uE; cbn; apply u64_lit; unfold P0, TOPm; lia).
  unfold STR0. rewrite uE_add by (rewrite uE0, U2; unfold P0, TOPm; lia). rewrite uE0, U2. lia.
Qed.
Lemma uE_L0 : uE E L0 = L0v. Proof using Hva. unfold uE. cbn. pose proof L0_rng. apply u64_lit. lia. Qed.
Lemma uE_END0 : uE E END0 = P0 + L0v.
Proof using Hvsp Hve Hva.
  pose proof Hlo. pose proof Hhi. pose proof SSZ_rng. pose proof L0_rng.
  assert (U2 : uE E D0 = P0 - TOPm) by (unfold uE; cbn; apply u64_lit; unfold P0, TOPm; lia).
  assert (I1 : uE E (EAlu Instr.ALU_ADD D0 L0) = P0 - TOPm + L0v).
  { rewrite uE_add by (rewrite U2, uE_L0; unfold P0, TOPm; lia). rewrite U2, uE_L0. lia. }
  unfold END0. rewrite uE_add by (rewrite uE0, I1; unfold P0, TOPm; lia). rewrite uE0, I1. lia.
Qed.
Lemma word_of_uE : forall e z, uE E e = z -> edenot E e = Z_to_bv 64 z.
Proof using. intros e z H. apply bv_eq. pose proof (u64_range (edenot E e)). unfold uE in H. rewrite u64_lit by lia. first [exact H | symmetry; exact H]. Qed.
Lemma estart_SA' : forall b o, estart E (SA b o) = uE E b + o. Proof using. intros. reflexivity. Qed.
Lemma adenot_flatZ : forall a n, flat E a n -> adenot E a = Z_to_bv 64 (estart E a).
Proof using. intros a n F. apply bv_eq. rewrite (flat_u E a n F). destruct F as (F1 & F2 & _). rewrite u64_lit by lia. reflexivity. Qed.
Lemma uE_litE : forall z, 0 <= z < 2 ^ 64 -> uE E (ELit z) = z. Proof using. intros z Hz. unfold uE. cbn. apply u64_lit. exact Hz. Qed.

(* [comment removed for export] *)
Lemma regs_M : regs_ok E regsM regs.
Proof using ME Hvsp Hva mem hw uid.
  pose proof Hlo as LO. pose proof Hhi as HI. pose proof len_av' as LA.
  destruct ME as [Mra Msp Mgp Mtp Ms0 Ms1 Ma0 Ma1 Ma2 Ms2 Ms3 Mz _].
  apply regs_ok_intro; [reflexivity|]. intros i Hi.
  assert (E8 : edenot E (eaddz SP0 56) = Z_to_bv 64 (s0 + 8)).
  { change (eaddz SP0 56) with (EAlu Instr.ALU_ADD SP0 (ELit 56)). apply word_of_uE. rewrite uE_add by (rewrite uE0, uE_litE by lia; unfold TOPm; lia). rewrite uE0, uE_litE by lia. unfold TOPm. lia. }
  assert (E25 : edenot E ENVP = Z_to_bv 64 (s0 + 16 + 8 * Z.of_nat (length av))) by reflexivity.
  do 32 (try (destruct i as [|i]; [cbn [nth regsM Z.of_nat Pos.of_succ_nat Pos.succ] |])). all: try lia.
  all: first [ exact Mra | etransitivity; [exact Msp|]; symmetry; apply word_of_uE; exact uE0 | exact Mgp | exact Mtp
          | etransitivity; [exact Ms0|]; symmetry; exact E8 | exact Ms1 | exact Ma0 | etransitivity; [exact Ma1|]; symmetry; exact E8
          | etransitivity; [exact Ma2|]; symmetry; exact E25 | exact Ms2 | etransitivity; [exact Ms3|]; symmetry; exact E25
          | etransitivity; [apply Mz; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]) |]; reflexivity
          | reflexivity ].
Qed.


(* [comment removed for export] *)
Lemma wseg1 : wseg_ok RSEGS (Z_to_bv 64 0x79dd8) 0x1e0 = true. Proof using. vm_compute. reflexivity. Qed.
Lemma wseg2 : wseg_ok RSEGS (Z_to_bv 64 0x8a020) 0x38 = true. Proof using. vm_compute. reflexivity. Qed.
Lemma wseg3 : wseg_ok RSEGS (Z_to_bv 64 0xab260) 0x408 = true. Proof using. vm_compute. reflexivity. Qed.
Lemma wseg4 : wseg_ok RSEGS (Z_to_bv 64 0x7a018) 0x1 = true. Proof using. vm_compute. reflexivity. Qed.     (* [comment removed for export] *)
Lemma wseg5 : wseg_ok RSEGS (Z_to_bv 64 0xaabd8) 0x224 = true. Proof using. vm_compute. reflexivity. Qed.   (* [comment removed for export] *)
Lemma store_static : forall M a (n : nat),
  (0x79dd8 <= a /\ a + Z.of_nat n <= 0x79fb8) \/ (0x8a020 <= a /\ a + Z.of_nat n <= 0x8a058) \/ (0xab260 <= a /\ a + Z.of_nat n <= 0xab668) \/ (0x7a018 <= a /\ a + Z.of_nat n <= 0x7a019) \/ (0xaabd8 <= a /\ a + Z.of_nat n <= 0xaadfc) ->
  store_ok RSEGS M (Z_to_bv 64 a) n = true.
Proof using.
  intros M a n [H|[H|[H|[H|H]]]].
  - eapply (store_ok_window RSEGS M (Z_to_bv 64 0x79dd8) (Z_to_bv 64 a) 0x1e0 n 0x79dd8 0x79fb8);
      [apply u64_lit; lia | reflexivity | lia | exact wseg1 | rewrite u64_lit; lia | rewrite u64_lit; lia].
  - eapply (store_ok_window RSEGS M (Z_to_bv 64 0x8a020) (Z_to_bv 64 a) 0x38 n 0x8a020 0x8a058);
      [apply u64_lit; lia | reflexivity | lia | exact wseg2 | rewrite u64_lit; lia | rewrite u64_lit; lia].
  - eapply (store_ok_window RSEGS M (Z_to_bv 64 0xab260) (Z_to_bv 64 a) 0x408 n 0xab260 0xab668);
      [apply u64_lit; lia | reflexivity | lia | exact wseg3 | rewrite u64_lit; lia | rewrite u64_lit; lia].
  - eapply (store_ok_window RSEGS M (Z_to_bv 64 0x7a018) (Z_to_bv 64 a) 0x1 n 0x7a018 0x7a019);
      [apply u64_lit; lia | reflexivity | lia | exact wseg4 | rewrite u64_lit; lia | rewrite u64_lit; lia].
  - eapply (store_ok_window RSEGS M (Z_to_bv 64 0xaabd8) (Z_to_bv 64 a) 0x224 n 0xaabd8 0xaadfc);
      [apply u64_lit; lia | reflexivity | lia | exact wseg5 | rewrite u64_lit; lia | rewrite u64_lit; lia].
Qed.
Lemma kn_static : forall c n,
  (0x79dd8 <= c /\ c + n <= 0x79fb8) \/ (0x8a020 <= c /\ c + n <= 0x8a058) \/ (0xab260 <= c /\ c + n <= 0xab668) \/ (0x7a018 <= c /\ c + n <= 0x7a019) \/ (0xaabd8 <= c /\ c + n <= 0xaadfc) -> 0 <= n ->
  kentry_ok RSEGS E mem (KWr (SA (ELit 0) c) (ELit n)).
Proof using.
  intros c n H Hn. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_SA', !uE_litE by lia. cbn [edenot]. rewrite u64_lit by lia.
  split; [lia|]. intros d m Hd Hdm. apply store_static. lia.
Qed.

(* [comment removed for export] *)
Definition missbZ (lo hi : Z) : bool :=
  forallb (fun c => (hi <=? fst c) || (fst c + Z.of_nat (snd c) <=? lo))%Z D_main_cells && (0 <=? lo) && (hi <=? 0x100000).
Lemma missbZ_point : forall lo hi i, missbZ lo hi = true -> lo <= i < hi -> D_main_missb i 1 = true.
Proof using.
  intros lo hi i H Hi. unfold missbZ in H. unfold D_main_missb. apply andb_prop in H as [H H2]. apply andb_prop in H as [H H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  assert (G : forall cells, forallb (fun c : Z * nat => (hi <=? fst c) || (fst c + Z.of_nat (snd c) <=? lo)) cells = true ->
                            forallb (range_disjoint_b i 1) cells = true).
  { intros cells. induction cells as [|c cells IH]; intros Hc; [reflexivity|]. cbn [forallb] in Hc |- *. apply andb_prop in Hc as [Hc Hr].
    rewrite (IH Hr), Bool.andb_true_r. unfold range_disjoint_b. apply Bool.orb_true_iff in Hc. apply Bool.orb_true_iff. cbn [Z.of_nat Pos.of_succ_nat].
    destruct Hc as [Hc|Hc]; apply Z.leb_le in Hc; [left | right]; apply Z.leb_le; lia. }
  rewrite (G _ H). cbn [Z.of_nat Pos.of_succ_nat andb]. apply Bool.andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma mem_noneZ : forall lo hi, missbZ lo hi = true -> forall i, lo <= i < hi -> mem (Z_to_bv 64 i) = None.
Proof using ME Hvsp regs tid rdraw hw uid ev av sp0.
  intros lo hi Hb i Hi. apply (mem_none i 1%nat); [exact (missbZ_point lo hi i Hb Hi) | cbn; lia].
Qed.
Lemma kn_img : forall lo hi, missbZ lo hi = true -> kentry_ok RSEGS E mem (KImg lo hi).
Proof using ME Hvsp hw uid.
  intros lo hi Hb. pose proof Hb as Hb'. unfold missbZ in Hb'. apply andb_prop in Hb' as [H H2]. apply andb_prop in H as [_ H1].
  apply Z.leb_le in H1. apply Z.leb_le in H2.
  apply kentry_ok_KImg; [lia | lia | exact (mem_noneZ lo hi Hb)].
Qed.

Lemma word1_zero : word_to_le_bytes 1 (Z_to_bv 64 0) = [Z_to_bv 8 0]. Proof using. reflexivity. Qed.
Lemma canary_len : length (canary_bytes rdraw) = 8%nat. Proof using. reflexivity. Qed.

Lemma know_M : know_ok RSEGS E mem (kn tM).
Proof using ME Htid Hvsp Hve Hva hw uid.
  pose proof Hlo as LO. pose proof Hhi as HI. pose proof Hal as AL. pose proof len_av' as LA. pose proof SSZ_rng as SR. pose proof L0_rng as LR.
  pose proof (u_argcN av Hva) as UA.
  assert (U1 : uE E ARGC = Z.of_nat (length av)) by (unfold uE; cbn; exact UA).
  assert (U2 : uE E D0 = P0 - TOPm) by (unfold uE; cbn; apply u64_lit; unfold P0, TOPm; lia).
  assert (U7 : uE E TID = bv_unsigned tid) by reflexivity.
  pose proof uE0 as U0. pose proof uE_STR0 as US. pose proof uE_END0 as UE. pose proof uE_L0 as UL.
  change (kn tM) with knM. unfold knM. apply know_ok_app.
  - apply know_ok_cons. { apply kentry_ok_KRange. fold (uE E SP0). rewrite U0. unfold TOPm, APC.CEIL, YLO, HI47. lia. }
    apply know_ok_cons. { apply kentry_ok_KAlign; [lia|]. fold (uE E SP0). rewrite U0. unfold TOPm.
                          rewrite Zminus_mod, AL. reflexivity. }
    apply know_ok_cons. { apply kentry_ok_KRange. fold (uE E TID). rewrite U7. lia. }
    apply know_ok_cons. { apply kentry_ok_KRange. fold (uE E ARGC). rewrite U1. lia. }
    apply know_ok_cons. { apply kentry_ok_KRange. fold (uE E D0). rewrite U2. unfold P0, TOPm. lia. }
    apply know_ok_cons. { apply kentry_ok_KRange. fold (uE E L0). rewrite UL. lia. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      assert (F : flat E (SA SP0 48) (Z.of_nat 8)) by (unfold flat; rewrite estart_SA', U0; unfold TOPm; cbn; lia).
      apply kentry_ok_KWord; [lia | exact F |]. rewrite (adenot_flatZ _ _ F), estart_SA', U0. unfold TOPm.
      replace (s0 - 48 + 48) with s0 by lia. rewrite rd_argc. reflexivity. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      assert (F : flat E (SA SP0 56) (Z.of_nat 8)) by (unfold flat; rewrite estart_SA', U0; unfold TOPm; cbn; lia).
      apply kentry_ok_KWord; [lia | exact F |]. rewrite (adenot_flatZ _ _ F), estart_SA', U0. unfold TOPm.
      replace (s0 - 48 + 56) with (s0 + 8 + 8 * Z.of_nat 0) by lia. rewrite (rd_argv_ptr 0) by lia. do 2 f_equal.
      rewrite <- (Z_to_bv_bv_unsigned 64 (cat_argv_ptr sp0 av ev 0)). symmetry. apply word_of_uE. rewrite US. symmetry. exact P0_val. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      assert (F : flat E (SA END0 0) (Z.of_nat 1)) by (unfold flat; rewrite estart_SA', UE; unfold P0; cbn; lia).
      apply kentry_ok_KWord; [lia | exact F |]. rewrite (adenot_flatZ _ _ F), estart_SA', UE.
      replace (P0 + L0v + 0) with (bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (length (nth 0 av []))) by (rewrite P0_val; unfold L0v; lia).
      rewrite (rd_argv_byte 0 (length (nth 0 av []))) by lia. rewrite nth_middle. reflexivity. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      cbn [kentry_ok]. unfold elenZ. fold (uE E L0). rewrite UL.
      split; [unfold flat; rewrite estart_SA', US; unfold P0; lia|]. split; [cbn [eb EM]; unfold L0v; lia|].
      intros i Hi. rewrite estart_SA', US. cbn [eb EM].
      replace (P0 + 0 + i) with (bv_unsigned (cat_argv_ptr sp0 av ev 0) + Z.of_nat (Z.to_nat i)) by (rewrite P0_val; lia).
      apply (mem_argv_byte 0 (Z.to_nat i)); [lia | unfold L0v in Hi; lia]. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      assert (F : flat E (SA (ELit 0) TID_CELL) (Z.of_nat 4)) by (unfold flat; rewrite estart_SA', uE_litE by lia; unfold TID_CELL; cbn; lia).
      apply kentry_ok_KWord; [lia | exact F |]. rewrite (adenot_flatZ _ _ F), estart_SA', uE_litE by lia. unfold TID_CELL. exact rd_tid. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      assert (F : flat E (SA (ELit 0) CANARY) (Z.of_nat 8)) by (unfold flat; rewrite estart_SA', uE_litE by lia; unfold CANARY; cbn; lia).
      apply kentry_ok_KWord; [lia | exact F |]. rewrite (adenot_flatZ _ _ F), estart_SA', uE_litE by lia. unfold CANARY.
      match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => replace a with 0xaae00 by reflexivity end.
      rewrite rd_guard. cbn [edenot EM AX2.ev CAN]. rewrite (le8_word _ canary_len). reflexivity. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      assert (F : flat E (SA (ELit 0) NEWH_GOT) (Z.of_nat 8)) by (unfold flat; rewrite estart_SA', uE_litE by lia; unfold NEWH_GOT; cbn; lia).
      apply kentry_ok_KWord; [lia | exact F |]. rewrite (adenot_flatZ _ _ F), estart_SA', uE_litE by lia. unfold NEWH_GOT, NEWH_CELL. exact rd_newh_got. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      cbn [kentry_ok]. unfold elenZ, flat. fold (uE E (ELit YLO)). rewrite !estart_SA', !U0, !uE_litE by (unfold YLO; lia). unfold TOPm, YLO.
      split; [lia|]. intros d m Hd Hdm. apply store_win; lia. }
    apply know_ok_cons.
    { (* [comment removed for export] *)
      cbn [kentry_ok]. unfold elenZ, flat. fold (uE E (ELit YLO)). rewrite !estart_SA', !U0, !uE_litE by (unfold YLO; lia). unfold TOPm, YLO.
      split; [lia|]. intros i Hi. apply mem_win. lia. }
    apply know_ok_cons; [apply kn_static; unfold FILE1; lia|].
    apply know_ok_cons; [apply kn_static; unfold FILE2; lia|].
    apply know_ok_cons; [apply kn_static; unfold SBUF0; lia|].
    apply know_ok_cons; [apply kn_static; unfold INIT_BYTE; lia|].
    apply know_ok_cons; [apply kn_static; unfold NEWH_CELL; lia|].
    apply know_ok_cons; [apply kn_static; unfold COMPLETED; lia|].                   (* [comment removed for export] *)
    apply know_ok_cons; [apply kn_static; unfold ATEXIT_LO, ATEXIT_WLEN; lia|].       (* [comment removed for export] *)
    apply know_ok_nil.
  - unfold KIMG_M. repeat (apply know_ok_cons; [apply kn_img; vm_compute; reflexivity|]). apply know_ok_nil.
Qed.

(* [comment removed for export] *)
Lemma W0_main : forall model B C, VM0 model -> W0 [] B C mem model.
Proof using ME Hvsp regs tid rdraw hw uid ev av sp0.
  intros model B C HV. split; [reflexivity|]. split; [|split; [|exact HV]].
  - intros i Hi. apply (mem_noneZ 0xaae90 0xab240); [vm_compute; reflexivity | unfold MLOCK, CTX_END, CTX in Hi; lia].
  - intros i Hi. apply (mem_noneZ 0x8aaec 0x8aaf0); [vm_compute; reflexivity | unfold A_ERRNO, TPV in Hi; lia].
Qed.

(* [comment removed for export] *)
Theorem main_cs_ok : forall (U : env -> Prop) model,
  U E -> m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] -> m_fds model = fds_std ->
  VM0 model -> CEIL_run <= s0 - 8388608 ->
  GPS.cs_ok RSEGS PERM_Tc TOPm (m_fs model) fds_std (AINV_f SWIN_T GUBSAN W0 PERM_Tc TOPm [] mem 0 0) fx_ok U E tM fx0 regs mem model.
Proof using ME Htid Hvsp Hve Hva hw uid.
  intros U model HU Hh Hl Hm Hfd HV HC. pose proof Hlo. pose proof Hhi.
  assert (TOP : sptop_den E (a_brk tM) = TOPm).
  { change (a_brk tM) with SP0. unfold sptop_den. fold (uE E SP0). rewrite uE0. unfold TOPm.
    destruct (Z.eqb_spec (s0 - 48) 0); [lia | reflexivity]. }
  apply cs_ok_intro.
  - exact regs_M.
  - reflexivity.
  - exact know_M.
  - exact Hh. - exact Hl. - exact Hm. - reflexivity. - exact Hfd.
  - change (a_vis tM) with (@nil (expr * expr)). cbn [blocks_den bcost bcount map length Z.of_nat fold_right].
    split; [exact (W0_main model _ _ HV)|]. split; [intros z Hz; right; right; exact (PERM_T_SWIN z Hz)|]. split; [unfold TOPm; lia|].
    split; [intros; reflexivity | intros a _ HH; exact HH].
  - exact HU.
  - exact fx_ok_fx0.
  - exact (PERM_Tc_den E).
  - exact TOP.
  - change (acs_floor (a_maps tM)) with (@None expr). cbn [floor_sem]. rewrite TOP. change (a_ylo tM) with YLO. unfold TOPm, YLO. lia.
Qed.

(* [comment removed for export] *)
Lemma L1_rng : length av = 2%nat -> 0 <= L1v <= 131071.
Proof using Hva. intros H2. unfold L1v. pose proof (valid_argv_str_len av 1 Hva ltac:(lia)). lia. Qed.
Lemma P1_val : length av = 2%nat -> bv_unsigned (cat_argv_ptr sp0 av ev 1) = P1.
Proof using ME Hfits Hvsp Hve Hva mem regs tid rdraw hw uid.
  intros H2. unfold P1, SSZ, L0v. rewrite (u_cat_argv_ptr RPH sp0 rdraw av ev uid hw Hva Hve Hsplo Hsphi 1 ltac:(lia)).
  destruct av as [|a0 [|a1 l]]; try discriminate H2. cbn [firstn nth]. rewrite total_arg_bytes_cons.
  replace (total_arg_bytes_nat []) with 0%nat by reflexivity. lia.
Qed.
Lemma uE_STR1 : length av = 2%nat -> uE E STR1 = P1.
Proof using Hvsp Hve Hva.
  intros H2. pose proof Hlo. pose proof Hhi. pose proof SSZ_rng. pose proof L0_rng.
  assert (U5 : uE E D1 = P1 - TOPm) by (unfold uE; cbn; apply u64_lit; unfold P1, TOPm; lia).
  unfold STR1. rewrite uE_add by (rewrite uE0, U5; unfold P1, TOPm; lia). rewrite uE0, U5. lia.
Qed.
Lemma uE_L1 : length av = 2%nat -> uE E L1 = L1v. Proof using Hva. intros H2. unfold uE. cbn. pose proof (L1_rng H2). apply u64_lit. lia. Qed.
Lemma uE_END1 : length av = 2%nat -> uE E END1 = P1 + L1v.
Proof using Hvsp Hve Hva.
  intros H2. pose proof Hlo. pose proof Hhi. pose proof SSZ_rng. pose proof L0_rng. pose proof (L1_rng H2).
  assert (U5 : uE E D1 = P1 - TOPm) by (unfold uE; cbn; apply u64_lit; unfold P1, TOPm; lia).
  assert (I1 : uE E (EAlu Instr.ALU_ADD D1 L1) = P1 - TOPm + L1v).
  { rewrite uE_add by (rewrite U5, (uE_L1 H2); unfold P1, TOPm; lia). rewrite U5, (uE_L1 H2). lia. }
  unfold END1. rewrite uE_add by (rewrite uE0, I1; unfold P1, TOPm; lia). rewrite uE0, I1. lia.
Qed.

Lemma know_O : length av = 2%nat -> know_ok RSEGS E mem knO.
Proof using ME Hfits Hvsp Hve Hva hw uid.
  intros H2. pose proof Hlo as LO. pose proof Hhi as HI. pose proof SSZ_rng as SR. pose proof L0_rng as LR. pose proof (L1_rng H2) as LR1.
  pose proof (u_argcN av Hva) as UA.
  assert (U1 : uE E ARGC = Z.of_nat (length av)) by (unfold uE; cbn; exact UA).
  assert (U5 : uE E D1 = P1 - TOPm) by (unfold uE; cbn; apply u64_lit; unfold P1, TOPm; lia).
  pose proof uE0 as U0. pose proof (uE_STR1 H2) as US. pose proof (uE_END1 H2) as UE. pose proof (uE_L1 H2) as UL. pose proof (P1_val H2) as PV.
  unfold knO.
  apply know_ok_cons. { apply kentry_ok_KRange. fold (uE E ARGC). rewrite U1. lia. }
  apply know_ok_cons. { apply kentry_ok_KRange. fold (uE E D1). rewrite U5. unfold P1, TOPm. lia. }
  apply know_ok_cons. { apply kentry_ok_KRange. fold (uE E L1). rewrite UL. lia. }
  apply know_ok_cons.
  { assert (F : flat E (SA SP0 64) (Z.of_nat 8)) by (unfold flat; rewrite estart_SA', U0; unfold TOPm; cbn; lia).
    apply kentry_ok_KWord; [lia | exact F |]. rewrite (adenot_flatZ _ _ F), estart_SA', U0. unfold TOPm.
    replace (s0 - 48 + 64) with (s0 + 8 + 8 * Z.of_nat 1) by lia. rewrite (rd_argv_ptr 1) by lia. do 2 f_equal.
    rewrite <- (Z_to_bv_bv_unsigned 64 (cat_argv_ptr sp0 av ev 1)). symmetry. apply word_of_uE. rewrite US. symmetry. exact PV. }
  apply know_ok_cons.
  { assert (F : flat E (SA END1 0) (Z.of_nat 1)) by (unfold flat; rewrite estart_SA', UE; unfold P1; cbn; lia).
    apply kentry_ok_KWord; [lia | exact F |]. rewrite (adenot_flatZ _ _ F), estart_SA', UE.
    replace (P1 + L1v + 0) with (bv_unsigned (cat_argv_ptr sp0 av ev 1) + Z.of_nat (length (nth 1 av []))) by (rewrite PV; unfold L1v; lia).
    rewrite (rd_argv_byte 1 (length (nth 1 av []))) by lia. rewrite nth_middle. reflexivity. }
  apply know_ok_cons.
  { cbn [kentry_ok]. unfold elenZ. fold (uE E L1). rewrite UL.
    split; [unfold flat; rewrite estart_SA', US; unfold P1; lia|]. split; [cbn [eb EM]; unfold L1v; lia|].
    intros i Hi. rewrite estart_SA', US. cbn [eb EM].
    replace (P1 + 0 + i) with (bv_unsigned (cat_argv_ptr sp0 av ev 1) + Z.of_nat (Z.to_nat i)) by (rewrite PV; lia).
    apply (mem_argv_byte 1 (Z.to_nat i)); [lia | unfold L1v in Hi; lia]. }
  pose proof (str_end_le 1 ltac:(lia)) as SE. rewrite PV in SE. change (nth 1 av []) with (nth 1 av []) in SE. fold L1v in SE || idtac.
  pose proof RNDP_ge as RG. pose proof RND_facts as (R1 & R2 & R3 & R4). pose proof BE_le as BE. pose proof bsb_len as BL.
  destruct (rnd_facts RSEGS RPH sp0 rdraw av ev uid hw Hva Hve Hsplo Hsphi Hal) as (_ & R2' & _). fold RNDP in R2' || idtac. unfold RNDP in *.
  apply know_ok_cons.
  { apply kentry_ok_KRange. fold (uE E END1'). unfold END1'. rewrite uE_add by (rewrite US, UL; unfold P1; lia). rewrite US, UL.
    unfold HI47, L1v, P1 in *. lia. }
  apply know_ok_cons.
  { cbn [kentry_ok]. unfold elenZ, flat. rewrite !estart_SA', !US.
    assert (U8 : bv_unsigned (edenot E (EAlu Instr.ALU_ADD L1 (ELit 8))) = L1v + 8).
    { fold (uE E (EAlu Instr.ALU_ADD L1 (ELit 8))). rewrite uE_add by (rewrite UL, uE_litE by lia; lia). rewrite UL, uE_litE by lia. lia. }
    rewrite U8. unfold L1v, P1 in *. split; [lia|]. intros i Hi. apply mem_block. lia. }
  apply know_ok_nil.
Qed.

Theorem main_cs_ok2 : forall (U : env -> Prop) model,
  length av = 2%nat ->
  U E -> m_halted model = None -> m_vm_lazy model = [] -> m_vm_materialized model = [] -> m_fds model = fds_std ->
  VM0 model -> CEIL_run <= s0 - 8388608 ->
  GPS.cs_ok RSEGS PERM_Tc TOPm (m_fs model) fds_std (AINV_f SWIN_T GUBSAN W0 PERM_Tc TOPm [] mem 0 0) fx_ok U E tMo fx0 regs mem model.
Proof using ME Htid Hfits Hvsp Hve Hva hw uid.
  intros U model H2 HU Hh Hl Hm Hfd HV HC. change tMo with (set_kn tM (knO ++ kn tM)).
  apply (cs_ok_set_kn RSEGS PERM_Tc TOPm (m_fs model) fds_std _ fx_ok U E tM fx0 regs mem model); [exact (main_cs_ok U model HU Hh Hl Hm Hfd HV HC)|].
  apply know_ok_app; [exact (know_O H2) | exact know_M].
Qed.
End WithVal.

(* [comment removed for export] *)
Lemma firstn8_len : length (firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw)))) = 8%nat.
Proof using. rewrite firstn_length_le; [reflexivity|]. rewrite length_skipn, length_at_random_bytes. lia. Qed.

Theorem main_fe_cells : fe_cells mem AUXW AVL.
Proof using ME Hvsp Hve Hva regs tid rdraw.
  pose proof Hlo as LO. pose proof Hhi as HI. pose proof AUXW_rng as (A1 & A2 & A3). pose proof RND_facts as (R1 & R2 & R3 & R4).
  pose proof (auxv_words_eq RPH uid hw (at_random_ptr sp0 av ev)) as WEQ.
  assert (RD : forall j, (j < 20)%nat -> rdn RSEGS mem (Z_to_bv 64 (AUXW + 8 * Z.of_nat j)) 8%nat = Some (word_to_le_bytes 8 (nth j AUXWORDS (Z_to_bv 64 0)))).
  { intros j Hj. rewrite (rd_auxv j Hj), WEQ. reflexivity. }
  assert (KEYS : forall j, (j < 9)%nat -> 0 < bv_unsigned (nth (2 * j) AUXWORDS (Z_to_bv 64 0)) /\ (bv_unsigned (nth (2 * j) AUXWORDS (Z_to_bv 64 0)) = 25 -> j = 8%nat)).
  { intros j Hj. do 9 (destruct j as [|j]; [cbn [nth Nat.mul Nat.add AUXWORDS]; unfold AT_PHDR, AT_PHENT, AT_PHNUM, AT_HWCAP, AT_PAGESZ, AT_UID, AT_EUID, AT_SECURE, AT_RANDOM;
      rewrite u64_lit by lia; split; [lia | intros; first [reflexivity | lia]] |]). lia. }
  assert (ENTRY : forall j, (j < 9)%nat ->
            cell mem (AUXW + 16 * Z.of_nat j) 8 (fst (avp j)) /\ cell mem (AUXW + 16 * Z.of_nat j + 8) 8 (snd (avp j))
            /\ 0 < fst (avp j) < 2 ^ 64 /\ 0 <= snd (avp j) < 2 ^ 64).
  { intros j Hj. unfold avp, cell. cbn [fst snd]. rewrite !Z_to_bv_bv_unsigned.
    split. { replace (AUXW + 16 * Z.of_nat j) with (AUXW + 8 * Z.of_nat (2 * j)) by lia. apply RD. lia. }
    split. { replace (AUXW + 16 * Z.of_nat j + 8) with (AUXW + 8 * Z.of_nat (2 * j + 1)) by lia. apply RD. lia. }
    pose proof (u64_range (nth (2 * j) AUXWORDS (Z_to_bv 64 0))). pose proof (u64_range (nth (2 * j + 1) AUXWORDS (Z_to_bv 64 0))).
    pose proof (proj1 (KEYS j Hj)). lia. }
  unfold fe_cells.
  split; [exact rd_libc_auxv|].
  split; [change (Z.of_nat (length AVL)) with 9; lia|].
  split.
  { intros i kv Hi. unfold AVL in Hi.
    do 9 (destruct i as [|i]; [cbn [nth_error] in Hi; injection Hi as <-; apply ENTRY; lia |]). destruct i; cbn in Hi; discriminate Hi. }
  split. { change (Z.of_nat (length AVL)) with 9. unfold cell. replace (AUXW + 16 * 9) with (AUXW + 8 * Z.of_nat 18) by lia. rewrite RD by lia. reflexivity. }
  split.
  { intros kv Hin H25.
    assert (HJ : exists j, (j < 9)%nat /\ kv = avp j).
    { unfold AVL in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [<-|Hin]; [eexists; split; [| reflexivity]; lia|]). destruct Hin. }
    destruct HJ as (j & Hj & ->). unfold avp in H25 |- *. cbn [fst snd] in H25 |- *.
    pose proof (proj2 (KEYS j Hj) H25) as ->. cbn [nth Nat.mul Nat.add AUXWORDS]. fold RNDP.
    split; [lia|]. exists (firstn 8 (skipn 8 (at_random_bytes (ed_random rdraw)))). split; [exact firstn8_len | exact R4]. }
  split; [exact rd_pagesize|]. split; [unfold cell; rewrite word1_zero; pose proof rd_need_locks as NL; rewrite word1_zero in NL; exact NL|].
  split. { exists (bytes_le_to_Z (canary_bytes rdraw)). unfold cell, A_CANARY. rewrite rd_guard, (le8_word _ canary_len). reflexivity. }
  split; [| split]; intros i Hi.
  - apply (mem_noneZ 0x78d60 0x78d68); [vm_compute; reflexivity | unfold A_GOT_CANARY in Hi; lia].
  - apply (mem_noneZ 0x2394c 0x2396c); [vm_compute; reflexivity | unfold A_TAB_CTZ in Hi; lia].
  - apply (mem_noneZ 0x2396c 0x239eb); [vm_compute; reflexivity | unfold A_TAB_SC, A_TAB_MED in Hi; lia].
Qed.

Theorem main_env_above : env_above_sp AUXW AVL TOPm.
Proof using ME Hvsp Hve Hva mem regs tid rdraw.
  pose proof Hlo as LO. pose proof AUXW_rng as (A1 & _). pose proof RND_facts as (R1 & _). unfold TOPm. split; [lia|].
  intros kv Hin H25.
  assert (HJ : exists j, (j < 9)%nat /\ kv = avp j).
  { unfold AVL in Hin. cbn [In] in Hin. repeat (destruct Hin as [<-|Hin]; [eexists; split; [| reflexivity]; lia|]). destruct Hin. }
  destruct HJ as (j & Hj & ->). unfold avp in H25 |- *. cbn [fst snd] in H25 |- *.
  assert (K : bv_unsigned (nth (2 * j) AUXWORDS (Z_to_bv 64 0)) = 25 -> j = 8%nat).
  { do 9 (destruct j as [|j]; [cbn [nth Nat.mul Nat.add AUXWORDS]; unfold AT_PHDR, AT_PHENT, AT_PHNUM, AT_HWCAP, AT_PAGESZ, AT_UID, AT_EUID, AT_SECURE, AT_RANDOM;
      rewrite u64_lit by lia; intros; first [reflexivity | lia] |]). lia. }
  rewrite (K H25). cbn [nth Nat.mul Nat.add AUXWORDS]. fold RNDP. lia.
Qed.

End Bridge.
End UbDrvS0Sound.
Require LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Glue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvS1Open.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup UbStartupFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.ShapeLaws OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0.UbMhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.UbDrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound.UbDrvGSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound UbDrvS0Sound OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma ecall_O : is_ecall_at RSEGS hOPEN = true /\ reg_lit hOPEN 17 = Some 56 /\ reg_lit hOPEN 10 = Some (2 ^ 64 - 100) /\ reg_lit hOPEN 12 = Some 32768
                /\ reg hOPEN 11 = STR1 /\ pc hOPEN = P_ECALL.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma sub_O : forallb (fun K => existsb (kentry_eqb K) (kn hOPEN))
                [KBlob (SA STR1 0) L1 2; KWord (SA END1 0) 1 (ELit 0); KRange SP0 (APC.CEIL + YLO) (HI47 - 48); KRange D1 64 4194304; KRange L1 0 131071] = true.
Proof. vm_compute. reflexivity. Qed.
Lemma tAO_regs : s_regs (a_ss tAO) = sr_upd (s_regs (a_ss hOPEN)) 10 (ELit 3). Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma tAO_parts : kn tAO = kn hOPEN /\ a_vis tAO = a_vis hOPEN /\ a_ghost tAO = a_ghost hOPEN /\ a_brk tAO = a_brk hOPEN
                  /\ a_ylo tAO = a_ylo hOPEN /\ a_maps tAO = a_maps hOPEN /\ s_log (a_ss tAO) = [] /\ pc tAO = P_AFTER_ECALL.
Proof. vm_compute. repeat split; reflexivity. Qed.
Lemma alloc_fd_std : alloc_fd fds_std = Z_to_bv 64 3. Proof. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma fd_insert_std : forall p, fd_insert fds_std (Z_to_bv 64 3) (State.FdFile p (Z_to_bv 64 0)) = FDS3 p (Z_to_bv 64 0). Proof. intros p. reflexivity. Qed.
Lemma AT_FDCWD_val : AT_FDCWD = Z_to_bv 64 (2 ^ 64 - 100). Proof. apply bv_eq. vm_compute. reflexivity. Qed.

Section Open.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
Hypothesis HFR : forall fx : FPState, @FREE_R fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.
Hypothesis HMA : forall fx : FPState, @MALLOC_ALT_F fx RC MSTK_M.
Hypothesis HM1 : forall fx : FPState, @MALLOC_FIRST_ALT3 RC fx MSTK_M.
#[local] Notation AINVcT TOP M0 := (AINV_f SWIN_T GUBSAN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GUBSAN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVc H TOP M0 := (AINV_f SWIN_T GUBSAN H PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okI H TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVc H TOP M0) fx_ok U).
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD AUBSAN NXD PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE RZ GUBSAN BCAP CCAP.
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GUBSAN fx_ok RZ AINV FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GUBSAN fx_ok RZ AINV FuzzE.ce.
Variables (p : Fs.path) (a0v : list byte) (data : list byte) (TOP : Z) (M0 : mem) (auxw : Z) (avl : list (Z * Z)).
Hypothesis REF_sound : forall M1 len E fx R M model,
  GPS.cs_ok RSEGS PERM_Tc TOP (m_fs model) (FDSr p (len + (2 ^ 26 - len))) (AINVcS TOP M1) fx_ok (U_rd data len (2 ^ 26)) E tVRb fx R M model ->
  RZ (cfgF RSEGS fx R (pc tVRb) M model) (t_die msg_refused (m_fs model)).
Hypothesis FEC : fe_cells M0 auxw avl.
Hypothesis ENV : env_above_sp auxw avl TOP.
(* [comment removed for export] *)
Hypothesis Hp0 : ~ In (Z_to_bv 8 0) p.
Hypothesis HpL : (length p <= 4095)%nat.
Hypothesis Hpn : path_eqb p [] = false.
Hypothesis Hplain : openat_plain_name p = true.
(* [comment removed for export] *)
Hypothesis CANTOPEN_sound : forall E fx R M model e,
  cs_okI W0 TOP (m_fs model) fds_std M0 (fun E => U_1 data E /\ eb E 2 = p /\ eb E 1 = a0v) E hOPEN fx R M model -> In e openat_errnos ->
  RZ (cfgF RSEGS fx (regupd R (Z_to_bv 5 10) (errno_ret e)) P_AFTER_ECALL M model) (t_die (msg_cannot_open p) (m_fs model)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition U_S1 (E : env) : Prop := U_1 data E /\ eb E 2 = p /\ eb E 1 = a0v.
Lemma U_S1_agree : forall E E', env_agree NXD E E' -> U_S1 E -> U_S1 E'.
Proof. intros E E' Hag (HU & HB & HA). split; [exact (U_1_agree data E E' Hag HU)|]. destruct Hag as [_ EB]. rewrite <- EB. split; [exact HB | exact HA]. Qed.
Lemma U_S1_U1 : forall E, U_S1 E -> U_1 data E. Proof. intros E [H _]. exact H. Qed.

Lemma kn_hit : forall E M K ks k, forallb (fun K => existsb (kentry_eqb K) k) ks = true -> In K ks -> know_ok RSEGS E M k -> kentry_ok RSEGS E M K.
Proof.
  intros E M K ks k Hsub HK HKN. pose proof (proj1 (forallb_forall _ _) Hsub K HK) as HX.
  apply existsb_exists in HX as (K' & HK' & HKK). apply kentry_eqb_eq in HKK. subst K'. exact (proj1 (Forall_forall _ _) HKN K HK').
Qed.

(* [comment removed for export] *)
Lemma path_rdn : forall FDS E fx R M model,
  cs_okI W0 TOP (m_fs model) FDS M0 U_S1 E hOPEN fx R M model ->
  rdn RSEGS M (edenot E STR1) (length p + 1) = Some (p ++ [Z_to_bv 8 0]).
Proof.
  clear Hp0 HpL Hpn Hplain. intros FDS E fx R M model HC. pose proof (co_know HC) as HK. destruct (co_uinv HC) as (_ & EB2 & _).
  pose proof (kn_hit E M (KBlob (SA STR1 0) L1 2) _ _ sub_O ltac:(cbn; tauto) HK) as KB.
  pose proof (kn_hit E M (KWord (SA END1 0) 1 (ELit 0)) _ _ sub_O ltac:(cbn; tauto) HK) as KW.
  pose proof (kn_hit E M (KRange SP0 (APC.CEIL + YLO) (HI47 - 48)) _ _ sub_O ltac:(cbn; tauto) HK) as K0.
  pose proof (kn_hit E M (KRange D1 64 4194304) _ _ sub_O ltac:(cbn; tauto) HK) as K5.
  pose proof (kn_hit E M (KRange L1 0 131071) _ _ sub_O ltac:(cbn; tauto) HK) as K6.
  cbn [kentry_ok] in KB, KW, K0, K5, K6. rewrite EB2 in KB. unfold elenZ in KB. fold (uE E L1) in KB.
  fold (uE E SP0) in K0. fold (uE E D1) in K5. fold (uE E L1) in K6. unfold APC.CEIL, YLO, HI47 in K0.
  destruct KB as (FB & LEN & BY). destruct KW as (_ & FW & RW). rewrite !estart_SA in *.
  assert (US : uE E STR1 = uE E SP0 + uE E D1).
  { unfold STR1, uE. cbn [edenot]. pose proof (u64_range (edenot E SP0)). pose proof (u64_range (edenot E D1)). unfold uE in *.
    rewrite u_add64. apply Z.mod_small. lia. }
  assert (UE : uE E END1 = uE E STR1 + uE E L1).
  { rewrite US. unfold END1, uE in *. cbn [edenot]. pose proof (u64_range (edenot E SP0)). pose proof (u64_range (edenot E D1)). pose proof (u64_range (edenot E L1)).
    rewrite !u_add64. rewrite (Z.mod_small (bv_unsigned (edenot E D1) + _)) by lia. rewrite Z.mod_small by lia. lia. }
  assert (EA : edenot E STR1 = Z_to_bv 64 (uE E STR1)) by (unfold uE; rewrite Z_to_bv_bv_unsigned; reflexivity).
  rewrite EA. apply rdn_of_mem; [rewrite length_app; cbn; lia | rewrite u64_lit by (unfold uE; apply u64_range); lia |].
  intros i Hi. rewrite u64_lit by (unfold uE; apply u64_range).
  destruct (Nat.lt_ge_cases i (length p)) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt. specialize (BY (Z.of_nat i) ltac:(lia)). rewrite Nat2Z.id in BY. rewrite Z.add_0_r in BY. exact BY.
  - assert (Hi' : i = length p) by lia. subst i. rewrite nth_middle.
    apply rdn1_overlay; [apply seg_rom_high; rewrite u64_lit; lia|].
    replace (Z_to_bv 64 (uE E STR1 + Z.of_nat (length p))) with (adenot E (SA END1 0)).
    + exact RW.
    + apply bv_eq. rewrite (flat_u E _ _ FW), estart_SA, u64_lit by lia. fold (uE E END1). unfold uE in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma W0_vm : forall L B C M mdl mdl', W0 L B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> W0 L B C M mdl'.
Proof. intros L B C M mdl mdl' (HL & HC & HE & HV) Hvm. split; [exact HL|]. split; [exact HC|]. split; [exact HE|]. unfold VM0 in *. rewrite Hvm. exact HV. Qed.
Lemma AINVcW0_vm : forall TOP' M0' Lc B C M mdl mdl', AINVc W0 TOP' M0' Lc B C M mdl -> m_vmmaps mdl' = m_vmmaps mdl -> AINVc W0 TOP' M0' Lc B C M mdl'.
Proof. intros TOP' M0' Lc B C M mdl mdl' (HA & HP & HT & HZ & HD) Hvm. split; [exact (W0_vm _ _ _ _ _ _ HA Hvm)|]. split; [exact HP|]. split; [exact HT|]. split; [exact HZ | exact HD]. Qed.

(* [comment removed for export] *)
Lemma open_xfer : forall FS U ent E fx R M model,
  cs_okI W0 TOP FS fds_std M0 U E hOPEN fx R M model ->
  cs_okI W0 TOP FS ((Z_to_bv 64 3, ent) :: fds_std) M0 U E tAO fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 3)) M (with_fds ((Z_to_bv 64 3, ent) :: fds_std) model).
Proof.
  clear Hp0 HpL Hpn Hplain. intros FS U ent E fx R M model HC. destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL].
  destruct tAO_parts as (Pkn & Pvis & Pgh & Pbrk & Pylo & Pmaps & Plog & Ppc).
  constructor.
  - rewrite tAO_regs. change (Z_to_bv 5 10) with (Z_to_bv 5 (Z.of_nat 10)). apply regs_ok_set_n; [exact CR | lia | reflexivity].
  - exact Plog.
  - rewrite Pkn. exact CK.
  - cbn [m_halted with_fds]. exact CH.
  - cbn [m_vm_lazy with_fds]. exact CZ.
  - cbn [m_fs with_fds]. exact CF.
  - reflexivity.
  - rewrite Pvis. apply (AINVcW0_vm TOP M0 _ _ _ M model); [exact CA | reflexivity].
  - exact CU.
  - exact CX.
  - rewrite Pgh. exact CP.
  - rewrite Pbrk. exact CT.
  - cbn [m_vm_materialized with_fds]. exact CM.
  - rewrite Pmaps, Pbrk, Pylo. exact CFL.
Qed.

Lemma open_step : forall E fx R M model B,
  cs_okI W0 TOP (m_fs model) fds_std M0 U_S1 E hOPEN fx R M model ->
  fs_lookup (m_fs model) p = Some data ->
  RZ (cfgF RSEGS fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 3)) P_AFTER_ECALL M (with_fds (FDS3 p (Z_to_bv 64 0)) model)) B ->
  RZ (cfgF RSEGS fx R (pc hOPEN) M model) (t_alt2 (t_die (msg_cannot_open p) (m_fs model)) B).
Proof.
  intros E fx R M model B HC Hfs HB.
  destruct ecall_O as (Hec & H17 & H10 & H12 & H11 & Hpc).
  destruct (GPS.is_ecall_at_sound RSEGS hOPEN Hec) as (w & HF & HE & Hpc0 & Hpc4).
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 17 56 HC ltac:(lia) H17)) as G17.
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 10 _ HC ltac:(lia) H10)) as G10.
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 12 _ HC ltac:(lia) H12)) as G12.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 11 HC ltac:(lia)) as G11. rewrite H11 in G11.
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)) with (@epend fx R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)).
  set (ms := @epend fx R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)).
  set (mk := fun fd : word => with_fds (fd_insert (m_fds model) fd (State.FdFile p (Z_to_bv 64 0))) model).
  apply (sr_alt2 RSEGS SR (mkCfg ms model) {e : Z | In e openat_errnos} unit (open_nx ms model mk) _ B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - apply (node_open RSEGS ms model (getr R 17) (open_copyins ms) mk (co_halt HC) (co_lazy HC) (epend_svc _ _ _ _ _)).
    + apply (openat_rd_check RSEGS ms (getr R 17) model p data).
      * rewrite G17. apply u64_lit. lia.
      * unfold ms. rewrite ms_gpr_epend0, G10. symmetry. exact AT_FDCWD_val.
      * unfold ms. rewrite (@ms_read_byte_epend fx RSEGS), ms_gpr_epend1, G11. apply read_cstr_of_rdn; [exact HpL | exact Hp0 | exact (path_rdn _ E fx R M model HC)].
      * exact Hpn.
      * unfold ms. rewrite ms_gpr_epend2, G12, u64_lit by lia. reflexivity.
      * exact Hplain.
      * exact Hfs.
    + intros fd. unfold mk. cbn [m_halted with_fds]. exact (co_halt HC).
    + intros fd. unfold mk. cbn [m_vm_lazy with_fds]. exact (co_lazy HC).
    + rewrite (co_fds HC). reflexivity.
    + rewrite G17. reflexivity.
  - intros [e He]. cbn [open_nx]. unfold ms. rewrite adv_set_epend, v_addi_pc4 by (unfold two64; lia). rewrite Hpc.
    exact (CANTOPEN_sound E fx R M model e HC He).
  - intros []. cbn [open_nx]. unfold ms, mk. rewrite (co_fds HC), alloc_fd_std, fd_insert_std.
    rewrite adv_set_epend, v_addi_pc4 by (unfold two64; lia). rewrite Hpc. exact HB.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem AO_gen : forall FDS0 (U : env -> Prop) (B : Fs.Fs -> TSet),
  fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) -> fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  (forall E E', env_agree NXD E E' -> U E -> U E') -> (forall fs, B fs []) ->
  forall E fx R M model,
  (forall E' fx' R' M' model', cs_okI W0 TOP (m_fs model) FDS0 M0 U E' hM1 fx' R' M' model' -> RZ (cfgF RSEGS fx' R' (pc hM1) M' model') (B (m_fs model))) ->
  cs_okI W0 TOP (m_fs model) FDS0 M0 U E tAO fx R M model ->
  RZ (cfgF RSEGS fx R (pc tAO) M model) (B (m_fs model)).
Proof.
  intros FDS0 U B F1 F2 Uag Bnil E fx R M model HK HC.
  refine (drvG_cert_sound SR SRX W0 W0_frame W0_zone W0_disj TOP (m_fs model) FDS0 M0 F1 F2 U Uag
            (HSof1 hM1) (fun _ _ fs => B fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => Bnil fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planH tAO (SHole 1) E fx R M model eq_refl certAO HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. pose proof (co_fs HC') as Hfs'. rewrite Hfs'. exact (HK E' fx' R' M' model' HC').
Qed.
Theorem MO_gen : forall (U : env -> Prop) (B : Fs.Fs -> TSet),
  (forall E E', env_agree NXD E E' -> U E -> U E') -> (forall fs, B fs []) ->
  forall E fx R M model,
  (forall E' fx' R' M' model', cs_okI W0 TOP (m_fs model) fds_std M0 U E' hOPEN fx' R' M' model' -> RZ (cfgF RSEGS fx' R' (pc hOPEN) M' model') (B (m_fs model))) ->
  cs_okI W0 TOP (m_fs model) fds_std M0 U E tMo fx R M model ->
  RZ (cfgF RSEGS fx R (pc tMo) M model) (B (m_fs model)).
Proof.
  intros U B Uag Bnil E fx R M model HK HC.
  refine (drvG_cert_sound SR SRX W0 W0_frame W0_zone W0_disj TOP (m_fs model) fds_std M0 eq_refl eq_refl U Uag
            (HSof1 hOPEN) (fun _ _ fs => B fs) (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => Bnil fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planH tMo (SHole 1) E fx R M model eq_refl certO HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. pose proof (co_fs HC') as Hfs'. rewrite Hfs'. exact (HK E' fx' R' M' model' HC').
Qed.

Definition HOLE_AO (h : nat) (E : env) (fs : Fs.Fs) : TSet := t_opened data fs.
Definition HOLE_O (h : nat) (E : env) (fs : Fs.Fs) : TSet := t_alt2 (t_die (msg_cannot_open p) fs) (t_opened data fs).

Theorem AO_sound : forall E fx R M model,
  fs_lookup (m_fs model) p = Some data ->
  cs_okI W0 TOP (m_fs model) (FDS3 p (Z_to_bv 64 0)) M0 U_S1 E tAO fx R M model ->
  RZ (cfgF RSEGS fx R (pc tAO) M model) (t_opened data (m_fs model)).
Proof.
  intros E fx R M model Hfs HC.
  refine (drvG_cert_sound SR SRX W0 W0_frame W0_zone W0_disj TOP (m_fs model) (FDS3 p (Z_to_bv 64 0)) M0 (fds3_1 _ _) (fds3_2 _ _) U_S1 U_S1_agree
            (HSof1 hM1) HOLE_AO (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => t_opened_has_nil data fs) (fun _ _ _ => eq_refl)
            _ BF FUEL planH tAO (SHole 1) E fx R M model eq_refl certAO HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. unfold HOLE_AO. pose proof (co_fs HC') as Hfs'.
  apply (M1_sound SR SRX HFR HMB HMA HM1 GC_T FZN_sound FZE_sound p data TOP M0 REF_sound auxw avl FEC ENV E' fx' R' M' model').
  - rewrite Hfs'. exact Hfs.
  - apply (cs_ok_uinv PERM_Tc TOP _ _ _ U_S1 (U_1 data)); [| apply U_S1_U1]. rewrite Hfs'. unfold FDSr. exact HC'.
Qed.

Theorem O_sound : forall E fx R M model,
  fs_lookup (m_fs model) p = Some data ->
  cs_okI W0 TOP (m_fs model) fds_std M0 U_S1 E hOPEN fx R M model ->
  RZ (cfgF RSEGS fx R (pc hOPEN) M model) (t_alt2 (t_die (msg_cannot_open p) (m_fs model)) (t_opened data (m_fs model))).
Proof.
  intros E fx R M model Hfs HC. apply (open_step E fx R M model _ HC Hfs).
  pose proof (AO_sound E fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 3)) M (with_fds (FDS3 p (Z_to_bv 64 0)) model)) as X.
  cbn [m_fs with_fds] in X. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 tAO_parts))))))) in X.
  apply X; [exact Hfs|]. exact (open_xfer _ U_S1 (State.FdFile p (Z_to_bv 64 0)) E fx R M model HC).
Qed.

Theorem MO_sound : forall E fx R M model,
  fs_lookup (m_fs model) p = Some data ->
  cs_okI W0 TOP (m_fs model) fds_std M0 U_S1 E tMo fx R M model ->
  RZ (cfgF RSEGS fx R (pc tMo) M model) (t_alt2 (t_die (msg_cannot_open p) (m_fs model)) (t_opened data (m_fs model))).
Proof.
  intros E fx R M model Hfs HC.
  refine (drvG_cert_sound SR SRX W0 W0_frame W0_zone W0_disj TOP (m_fs model) fds_std M0 eq_refl eq_refl U_S1 U_S1_agree
            (HSof1 hOPEN) HOLE_O (fun _ _ _ _ _ => eq_refl) (fun _ _ fs => or_introl (t_die_has_nil _ fs)) (fun _ _ _ => eq_refl)
            _ BF FUEL planH tMo (SHole 1) E fx R M model eq_refl certO HC eq_refl).
  apply HSof1_stmt. intros E' fx' R' M' model' HC'. unfold HOLE_O. pose proof (co_fs HC') as Hfs'.
  apply (O_sound E' fx' R' M' model'); [rewrite Hfs'; exact Hfs|]. rewrite Hfs'. exact HC'.
Qed.
End Open.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainFile.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
Hypothesis HFR : forall fx : FPState, @FREE_R fx RC MSTK_M.
Hypothesis HMB : forall fx : FPState, @MALLOC_BIG_R fx RC MSTK_M.
Hypothesis HMA : forall fx : FPState, @MALLOC_ALT_F fx RC MSTK_M.
Hypothesis HM1 : forall fx : FPState, @MALLOC_FIRST_ALT3 RC fx MSTK_M.
#[local] Notation AINVcT TOP M0 := (AINV_f SWIN_T GUBSAN AINV PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GUBSAN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVc H TOP M0 := (AINV_f SWIN_T GUBSAN H PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okI H TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVc H TOP M0) fx_ok U).
Hypothesis GC_T : forall TOP FS0 M0, gcontracts RSEGS ITD AUBSAN NXD PERM_Tc TOP FS0 fds_std (AINVcT TOP M0) fx_ok UTRUE RZ GUBSAN BCAP CCAP.
Hypothesis FZN_sound : callee_contract RSEGS SWIN_T GUBSAN fx_ok RZ AINV FuzzN.ce.
Hypothesis FZE_sound : callee_contract RSEGS SWIN_T GUBSAN fx_ok RZ AINV FuzzE.ce.

(* [comment removed for export] *)
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Variable model : Model.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.
Hypothesis Mh : m_halted model = None.
Hypothesis Ml : m_vm_lazy model = [].
Hypothesis Mm : m_vm_materialized model = [].
Hypothesis Mfd : m_fds model = fds_std.
Hypothesis MV : VM0 model.
Hypothesis MC : CEIL_run <= bv_unsigned sp0 - 8388608.
(* [comment removed for export] *)
Variables (a0 p : Fs.path) (data : list byte).
Hypothesis Hav : av = [a0; p].
Hypothesis Hp0 : ~ In (Z_to_bv 8 0) p.
Hypothesis HpL : (length p <= 4095)%nat.
Hypothesis Hpn : path_eqb p [] = false.
Hypothesis Hplain : openat_plain_name p = true.
Hypothesis Hfs : fs_lookup (m_fs model) p = Some data.
#[local] Notation TOP := (TOPm sp0).
(* [comment removed for export] *)
Hypothesis REF_sound : forall M1 len E fx R M model',
  GPS.cs_ok RSEGS PERM_Tc TOP (m_fs model') (FDSr p (len + (2 ^ 26 - len))) (AINVcS TOP M1) fx_ok (U_rd data len (2 ^ 26)) E tVRb fx R M model' ->
  RZ (cfgF RSEGS fx R (pc tVRb) M model') (t_die msg_refused (m_fs model')).
Hypothesis CANTOPEN_sound : forall E fx R M model' e,
  cs_okI W0 TOP (m_fs model') fds_std mem (fun E => U_1 data E /\ eb E 2 = p /\ eb E 1 = a0) E hOPEN fx R M model' -> In e openat_errnos ->
  RZ (cfgF RSEGS fx (regupd R (Z_to_bv 5 10) (errno_ret e)) P_AFTER_ECALL M model') (t_die (msg_cannot_open p) (m_fs model')).

Theorem main_file_sound :
  RZ (cfgF RSEGS fx0 regs P_MAIN mem model) (t_alt2 (t_die (msg_cannot_open p) (m_fs model)) (t_opened data (m_fs model))).
Proof.
  assert (H2 : length av = 2%nat) by (rewrite Hav; reflexivity).
  set (E := EM sp0 av ev rdraw tid regs (LB data) (hdr data)).
  assert (HU : U_S1 p a0 data E).
  { split; [split|split].
    - unfold uE, E. cbn. pose proof (Z.le_min_r (L data) (2 ^ 40)). pose proof (Zle_0_nat (length data)). unfold LB, L in *. apply u64_lit. lia.
    - reflexivity.
    - unfold E. cbn. rewrite Hav. reflexivity.
    - unfold E. cbn. rewrite Hav. reflexivity. }
  pose proof (main_cs_ok2 sp0 av ev uid hw rdraw tid regs mem Hva Hve Hvsp Hfits Htid ME (LB data) (hdr data) (U_S1 p a0 data) model H2 HU Mh Ml Mm Mfd MV MC) as HC.
  exact (MO_sound SR SRX HFR HMB HMA HM1 GC_T FZN_sound FZE_sound p a0 data TOP mem (AUXW sp0 av ev) (AVL sp0 av ev uid hw)
           REF_sound (main_fe_cells sp0 av ev uid hw rdraw tid regs mem Hva Hve Hvsp ME) (main_env_above sp0 av ev uid hw rdraw tid regs mem Hva Hve Hvsp ME)
           Hp0 HpL Hpn Hplain CANTOPEN_sound E fx0 regs mem model Hfs HC).
Qed.
End MainFile.
End UbDrvS1Open.
Require Stdlib.Strings.String Stdlib.Strings.Ascii OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbDrvS0Glue.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String Stdlib.Strings.Ascii.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.
Import LinuxProcessSemantics.LinuxProcessSem.Checks.ExecutableSpecs.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup UbStartupFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.ShapeLaws OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0.UbMhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.UbDrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound.UbDrvGSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound UbDrvS0Sound UbDrvS1Open OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes2 UbDrvNodes2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Plan UbDrvESound OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition U_D (a0 p : list byte) (E : env) : Prop := eb E 1 = a0 /\ eb E 2 = p.
Lemma U_D_agree : forall a0 p E E', env_agree NXD E E' -> U_D a0 p E -> U_D a0 p E'.
Proof. intros a0 p E E' [_ EB] [H1 H2]. unfold U_D. rewrite <- EB. split; assumption. Qed.
Lemma U_D_nz : forall a0 p, ~ In (Z_to_bv 8 0) a0 -> ~ In (Z_to_bv 8 0) p -> forall E j, U_D a0 p E -> In j NZB -> ~ In (Z_to_bv 8 0) (eb E j).
Proof.
  intros a0 p H0 H1 E j [E1 E2] Hj. unfold NZB in Hj. cbn in Hj.
  destruct Hj as [<-|[<-|[]]]; [rewrite E1; exact H0 | rewrite E2; exact H1].
Qed.

(* [comment removed for export] *)
Lemma emit1_nil : forall fs, t_eq (t_emit (map (WriteEv (Z_to_bv 64 1)) []) (t_exit (Z_to_bv 64 2) fs)) (t_exit (exit_code 2) fs).
Proof. intros fs. cbn [map]. unfold exit_code. apply t_emit_nil_eq. apply t_exit_has_nil. Qed.
Lemma sd_shS3 : forall HOLES D E fs L a b pre j suf,
  t_eq (sd HOLES D E fs (shS3 L a b pre j suf)) (t_die (map (Z_to_bv 8) pre ++ eb E j ++ map (Z_to_bv 8) suf) fs).
Proof.
  intros HOLES D E fs L a b pre j suf. unfold shS3, t_die. cbn [sd]. unfold Wp, Spec4.W. cbn [flat_map piece_den]. rewrite !app_nil_r.
  set (MSG := map (Z_to_bv 8) pre ++ eb E j ++ map (Z_to_bv 8) suf).
  destruct (Z.leb (bv_unsigned (edenot E L)) a); [| destruct (Z.leb (bv_unsigned (edenot E L)) b)].
  - apply Spec4.AgentLib.t_emit_congr. apply emit1_nil.
  - apply Spec4.AgentLib.t_emit_congr. cbn [map]. eapply t_eq_trans; [apply t_emit_nil_eq; apply t_emit_has_nil | apply emit1_nil].
  - eapply t_eq_trans; [| apply Spec4.AgentLib.t_emit_congr; apply emit1_nil].
    eapply t_eq_trans; [| apply t_eq_sym; unfold MSG; rewrite app_assoc, map_app; apply Spec4.AgentLib.t_emit_app].
    apply Spec4.AgentLib.t_emit_congr. apply Spec4.AgentLib.t_emit_congr. apply emit1_nil || apply t_eq_refl.
Qed.

Lemma zUSAGE1_ok : map (Z_to_bv 8) zUSAGE1 = s2b "usage: "%string. Proof. vm_compute. reflexivity. Qed.
Lemma zUSAGE2_ok : map (Z_to_bv 8) zUSAGE2 = s2b " INPUT"%string ++ [LF]. Proof. vm_compute. reflexivity. Qed.
Lemma zCO_ok : map (Z_to_bv 8) zCO = s2b "cli: cannot open "%string. Proof. vm_compute. reflexivity. Qed.
Lemma zNL_ok : map (Z_to_bv 8) zNL = [LF]. Proof. vm_compute. reflexivity. Qed.
Lemma errno_wseg : wseg_ok RSEGS (Z_to_bv 64 ERRNO) 4 = true. Proof. vm_compute. reflexivity. Qed.
Lemma kn_errno : forall E M, kentry_ok RSEGS E M (KWr (SA (ELit 0) ERRNO) (ELit 4)).
Proof.
  intros E M. cbn [kentry_ok]. unfold flat, elenZ. rewrite estart_lit0. cbn [edenot]. rewrite u64_lit by lia. unfold ERRNO.
  split; [lia|]. intros d m Hd Hdm.
  eapply (store_ok_window RSEGS M (Z_to_bv 64 0x8aaec) _ 4 m 0x8aaec 0x8aaf0);
    [apply u64_lit; lia | reflexivity | lia | exact errno_wseg | rewrite u64_lit; lia | rewrite u64_lit; lia].
Qed.

Section Dies.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
#[local] Notation AINVe TOP M0 := (AINV_f SWIN_E GE SHP PERM_Ec TOP [] M0 0 0).
#[local] Notation cs_okE TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok U).
#[local] Notation cs_okW TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINV_f SWIN_T GUBSAN W0 PERM_Tc TOP [] M0 0 0) fx_ok U).
Definition HOLE_0 (h : nat) (E : env) (fs : Fs.Fs) : TSet := t_nil.

(* [comment removed for export] *)
Lemma die_cert_sound : forall TOP M0 FDS0 (a0 p : list byte) (dird : bool) cs pl (L : expr) a b pre j suf E fx R M model,
  fd_lookup FDS0 (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)) -> fd_lookup FDS0 (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)) ->
  (dird = true -> fd_lookup FDS0 (Z_to_bv 64 3) = Some State.FdDir) ->
  ~ In (Z_to_bv 8 0) a0 -> ~ In (Z_to_bv 8 0) p ->
  gplan_ok pl = true -> CHKe NZB dird HS0 BF FUEL cs pl = COk (shS3 L a b pre j suf) ->
  cs_okE TOP (m_fs model) FDS0 M0 (U_D a0 p) E cs fx R M model ->
  RZ (cfgF RSEGS fx R (pc cs) M model) (t_die (map (Z_to_bv 8) pre ++ eb E j ++ map (Z_to_bv 8) suf) (m_fs model)).
Proof using SRX.
  intros TOP M0 FDS0 a0 p dird cs pl L a b pre j suf E fx R M model F1 F2 F3 N0 N1 Hpl CERT HC.
  eapply (sr_conseq RSEGS SR); [| apply (sd_shS3 HOLE_0 t_nil E (m_fs model) L a b pre j suf)].
  exact (drvE_cert_sound SR SRX TOP (m_fs model) FDS0 M0 F1 F2 (U_D a0 p) (U_D_agree a0 p) NZB (U_D_nz a0 p N0 N1) dird F3
           HS0 HOLE_0 (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun h ch Hh => ltac:(discriminate Hh))
           BF FUEL pl cs _ E fx R M model Hpl CERT HC eq_refl).
Qed.
Lemma nodir : false = true -> fd_lookup fds_std (Z_to_bv 64 3) = Some State.FdDir. Proof using. intros H. discriminate H. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Usage.
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Variable model : Model.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.
Hypothesis Mh : m_halted model = None.
Hypothesis Ml : m_vm_lazy model = [].
Hypothesis Mm : m_vm_materialized model = [].
Hypothesis Mfd : m_fds model = fds_std.
Hypothesis MC : CEIL_run <= bv_unsigned sp0 - 8388608.
#[local] Notation E := (EM sp0 av ev rdraw tid regs 0 []).
#[local] Notation s0 := (bv_unsigned sp0).

Lemma know_Xu : know_ok RSEGS E mem knXu.
Proof using ME Hfits Hvsp Hve Hva hw uid.
  pose proof (L0_rng av Hva) as LR. pose proof (SSZ_rng av ev Hva Hve) as SR'. pose proof (P0_val sp0 av ev uid hw rdraw Hva Hve Hvsp) as PV.
  pose proof (uE_STR0 sp0 av ev rdraw tid regs Hva Hve Hvsp 0 []) as US. pose proof (uE_L0 sp0 av ev rdraw tid regs Hva 0 []) as UL.
  pose proof (str_end_le sp0 av ev uid hw rdraw Hva Hve Hvsp 0%nat ltac:(pose proof (valid_argv_nonempty av Hva); lia)) as SE. rewrite PV in SE.
  pose proof (RNDP_ge sp0 av ev uid hw rdraw Hva Hve Hvsp) as RG. pose proof (BE_le sp0 av ev uid hw rdraw Hfits) as BE.
  destruct (rnd_facts RSEGS RPH sp0 rdraw av ev uid hw Hva Hve (proj1 Hvsp) (proj1 (proj2 Hvsp)) (proj2 (proj2 Hvsp))) as (_ & R2 & _). unfold RNDP in RG.
  destruct Hvsp as (LO & HI & AL). unfold sp_window_lo in LO. unfold sp_window_hi in HI.
  unfold knXu. apply know_ok_cons.
  { apply kentry_ok_KRange. fold (uE E END0'). unfold END0'. rewrite (uE_add sp0 av ev rdraw tid regs 0 []) by (rewrite US, UL; unfold P0; lia). rewrite US, UL.
    unfold HI47, L0v, P0 in *. lia. }
  apply know_ok_cons.
  { cbn [kentry_ok]. unfold elenZ, flat. rewrite !estart_SA. fold (uE E STR0). rewrite !US.
    assert (U8 : bv_unsigned (edenot E (EAlu Instr.ALU_ADD L0 (ELit 8))) = L0v av + 8).
    { fold (uE E (EAlu Instr.ALU_ADD L0 (ELit 8))). rewrite (uE_add sp0 av ev rdraw tid regs 0 []) by (rewrite UL, (uE_litE sp0 av ev rdraw tid regs 0 []) by lia; lia).
      rewrite UL, (uE_litE sp0 av ev rdraw tid regs 0 []) by lia. lia. }
    rewrite U8. unfold L0v, P0 in *. split; [lia|]. intros i Hi. apply (mem_block sp0 av ev uid hw rdraw tid regs mem (conj LO (conj HI AL)) Hfits ME). lia. }
  apply know_ok_cons; [apply kn_errno | apply know_ok_nil].
Qed.

Lemma usage_cs_ok : forall argc : kentry,
  kentry_ok RSEGS E mem argc ->
  cs_okE (TOPm sp0) (m_fs model) fds_std mem (U_D (nth 0 av []) (nth 1 av [])) E (tMu argc) fx0 regs mem model.
Proof using MC Mfd Mm Ml Mh ME Htid Hfits Hvsp Hve Hva hw uid.
  intros argc Hargc. pose proof Hvsp as (LO & HI & AL). unfold sp_window_lo in LO. unfold sp_window_hi in HI.
  assert (TOP : sptop_den E (a_brk (tMu argc)) = TOPm sp0).
  { change (a_brk (tMu argc)) with SP0. unfold sptop_den. rewrite (uE0 sp0 av ev rdraw tid regs Hvsp 0 []). unfold TOPm.
    destruct (Z.eqb_spec (s0 - 48) 0); [lia | reflexivity]. }
  apply cs_ok_intro.
  - exact (regs_M sp0 av ev uid hw rdraw tid regs mem Hva Hvsp ME 0 []).
  - reflexivity.
  - change (kn (tMu argc)) with (argc :: knXu ++ kn tM). apply know_ok_cons; [exact Hargc|]. apply know_ok_app; [exact know_Xu|].
    exact (know_M sp0 av ev uid hw rdraw tid regs mem Hva Hve Hvsp Htid ME 0 []).
  - exact Mh. - exact Ml. - exact Mm. - reflexivity. - exact Mfd.
  - change (a_vis (tMu argc)) with (@nil (expr * expr)). cbn [blocks_den bcost bcount map length Z.of_nat fold_right].
    split; [split; [intros b m [] | intros L1 L2 b m b' m' EQ; destruct L1; discriminate EQ]|].
    split; [intros z Hz; right; right; exact (PERM_E_SWIN z Hz)|]. split; [unfold TOPm; lia|].
    split; [intros; reflexivity | intros a _ HH; exact HH].
  - split; reflexivity.
  - exact fx_ok_fx0.
  - exact (PERM_Ec_den E).
  - exact TOP.
  - change (acs_floor (a_maps (tMu argc))) with (@None expr). cbn [floor_sem]. rewrite TOP. change (a_ylo (tMu argc)) with YLO. unfold TOPm, YLO. lia.
Qed.

Theorem usage_sound : length av <> 2%nat ->
  RZ (cfgF RSEGS fx0 regs P_MAIN mem model) (t_die (msg_usage (nth 0 av [])) (m_fs model)).
Proof using MC Mfd Mm Ml Mh ME Htid Hfits Hvsp Hve Hva tid rdraw hw uid ev sp0 SRX RC.
  intros Hne. pose proof (valid_argv_len av Hva) as LA. pose proof (valid_argv_nonempty av Hva) as LA1.
  assert (UA : uE E ARGC = Z.of_nat (length av)) by (unfold uE; cbn; exact (u_argcN av Hva)).
  assert (N0 : ~ In (Z_to_bv 8 0) (nth 0 av [])) by (apply (valid_argv_str_nz av 0 Hva); lia).
  assert (N1 : ~ In (Z_to_bv 8 0) (nth 1 av [])).
  { destruct (Nat.lt_ge_cases 1 (length av)); [apply (valid_argv_str_nz av 1 Hva); lia | rewrite nth_overflow by lia; intros []]. }
  unfold msg_usage. rewrite <- zUSAGE1_ok, <- zUSAGE2_ok, app_assoc.
  change (nth 0 av []) with (eb E 1) at 1.
  replace (map (Z_to_bv 8) zUSAGE1 ++ eb E 1 ++ map (Z_to_bv 8) zUSAGE2) with (map (Z_to_bv 8) zUSAGE1 ++ eb E 1 ++ map (Z_to_bv 8) zUSAGE2) by reflexivity.
  destruct (Nat.eq_dec (length av) 1) as [H1|H3].
  - change P_MAIN with (pc tMu1).
    rewrite <- app_assoc.
    apply (die_cert_sound (TOPm sp0) mem fds_std (nth 0 av []) (nth 1 av []) false tMu1 planU L0 66 73 zUSAGE1 1 zUSAGE2 E fx0 regs mem model eq_refl eq_refl nodir N0 N1 eq_refl certU1).
    apply usage_cs_ok. apply kentry_ok_KRange. fold (uE E ARGC). rewrite UA. lia.
  - change P_MAIN with (pc tMu3).
    rewrite <- app_assoc.
    apply (die_cert_sound (TOPm sp0) mem fds_std (nth 0 av []) (nth 1 av []) false tMu3 planU L0 66 73 zUSAGE1 1 zUSAGE2 E fx0 regs mem model eq_refl eq_refl nodir N0 N1 eq_refl certU3).
    apply usage_cs_ok. apply kentry_ok_KRange. fold (uE E ARGC). rewrite UA. lia.
Qed.
End Usage.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CO.
Variables (p a0v data : list byte) (TOP : Z) (M0 : mem).
Hypothesis Hp0 : ~ In (Z_to_bv 8 0) p.
Hypothesis Ha0 : ~ In (Z_to_bv 8 0) a0v.

(* [comment removed for export] *)
Definition Eplus (E : env) (v : word) : env := Env (fun n => if Nat.eqb n (nxt hOPEN) then v else AX2.ev E n) (eb E).
Lemma Eplus_agree : forall E v, env_agree (nxt hOPEN) E (Eplus E v).
Proof using. intros E v. split; [|reflexivity]. intros n Hn. cbn [Eplus AX2.ev]. destruct (Nat.eqb_spec n (nxt hOPEN)); [lia | reflexivity]. Qed.

(* [comment removed for export] *)
Lemma CO_xfer : forall E fx R M model (v : word),
  cs_okW TOP (m_fs model) fds_std M0 (U_S1 p a0v data) E hOPEN fx R M model ->
  two64 - 4095 <= bv_unsigned v <= two64 - 1 ->
  cs_okE TOP (m_fs model) fds_std M (U_D a0v p) (Eplus E v) tCO fx (regupd R (Z_to_bv 5 10) v) M model.
Proof using.
  intros E fx R M model v HC Hv.
  destruct tCO_parts as (Pkn & Pvis & Pbrk & Pylo & Pmaps & Plog & Ppc & Pregs & Pfresh & Pvis0 & Pnx).
  pose proof (GPS.cs_ok_agree RSEGS NXD PERM_Tc TOP (m_fs model) fds_std (AINV_f SWIN_T GUBSAN W0 PERM_Tc TOP [] M0 0 0) fx_ok (U_S1 p a0v data) (U_S1_agree p a0v data)
                E (Eplus E v) hOPEN fx R M model (Eplus_agree E v) Pfresh HC) as HC1.
  destruct HC1 as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL].
  constructor.
  - rewrite Pregs. change (Z_to_bv 5 10) with (Z_to_bv 5 (Z.of_nat 10)). apply regs_ok_set_n; [exact CR | lia |].
    unfold AERR. cbn [edenot Eplus AX2.ev]. rewrite Nat.eqb_refl. reflexivity.
  - exact Plog.
  - rewrite Pkn. apply know_ok_app; [| exact CK]. unfold knXo. apply know_ok_cons.
    + apply kentry_ok_KRange. unfold AERR. cbn [edenot Eplus AX2.ev]. rewrite Nat.eqb_refl. exact Hv.
    + apply know_ok_cons; [apply kn_errno | apply know_ok_nil].
  - exact CH. - exact CZ. - exact CF. - exact CD.
  - rewrite Pvis. cbn [blocks_den bcost bcount map length Z.of_nat fold_right].
    destruct CA as (_ & _ & HT & _).
    split; [split; [intros b m [] | intros L1 L2 b m b' m' EQ; destruct L1; discriminate EQ]|].
    split; [intros z Hz; right; right; exact (PERM_E_SWIN z Hz)|]. split; [exact HT|].
    split; [intros; reflexivity | intros a _ HH; exact HH].
  - destruct CU as (_ & E2 & E1). split; [exact E1 | exact E2].
  - exact CX.
  - exact (PERM_Ec_den _).
  - rewrite Pbrk. exact CT.
  - exact CM.
  - rewrite Pmaps, Pbrk, Pylo. exact CFL.
Qed.

(* [comment removed for export] *)
Lemma CO_sound : forall E fx R M model,
  cs_okE TOP (m_fs model) fds_std M (U_D a0v p) E tCO fx R M model ->
  RZ (cfgF RSEGS fx R (pc tCO) M model) (t_die (msg_cannot_open p) (m_fs model)).
Proof using Ha0 Hp0 SRX.
  intros E fx R M model HC. unfold msg_cannot_open. rewrite <- zCO_ok, <- zNL_ok.
  replace p with (eb E 2) at 1 by exact (proj2 (co_uinv HC)).
  exact (die_cert_sound TOP M fds_std a0v p false tCO planCO L1 62 63 zCO 2 zNL E fx R M model eq_refl eq_refl nodir Ha0 Hp0 eq_refl certCO HC).
Qed.

(* [comment removed for export] *)
Theorem open_fail_die : forall E fx R M model (v : word),
  cs_okW TOP (m_fs model) fds_std M0 (U_S1 p a0v data) E hOPEN fx R M model ->
  two64 - 4095 <= bv_unsigned v <= two64 - 1 ->
  RZ (cfgF RSEGS fx (regupd R (Z_to_bv 5 10) v) P_AFTER_ECALL M model) (t_die (msg_cannot_open p) (m_fs model)).
Proof using Ha0 Hp0 SRX.
  intros E fx R M model v HC Hv.
  destruct tCO_parts as (_ & _ & _ & _ & _ & _ & Ppc & _). rewrite <- Ppc.
  exact (CO_sound (Eplus E v) fx _ M model (CO_xfer E fx R M model v HC Hv)).
Qed.

Theorem cantopen_sound : forall E fx R M model e,
  cs_okW TOP (m_fs model) fds_std M0 (U_S1 p a0v data) E hOPEN fx R M model -> In e openat_errnos ->
  RZ (cfgF RSEGS fx (regupd R (Z_to_bv 5 10) (errno_ret e)) P_AFTER_ECALL M model) (t_die (msg_cannot_open p) (m_fs model)).
Proof using Ha0 Hp0 SRX.
  intros E fx R M model e HC He. pose proof (openat_errno_range e He) as Hr.
  apply (open_fail_die E fx R M model _ HC). unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, two64.
  change (bv_modulus 64) with (2 ^ 64). rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma openat_noent_check : forall ms x8 model q,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk q ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  (path_eqb q [] = true \/ (openat_plain_name q = true /\ fs_lookup (m_fs model) q = None)) ->
  forall eff, check_syscall (sys_input RSEGS ms x8) eff model = check_ret_only_copyins (open_copyins ms) eff (errno_ret ENOENT) model [].
Proof using.
  intros ms x8 model q Hno Hdirfd Hpath Hfl Hcase eff.
  rewrite (check_syscall_56 RSEGS ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  destruct (path_eqb q []) eqn:Hpe; cbv beta iota.
  - apply check_copyins_after_ret_only.
  - destruct Hcase as [Hc|[Hdot Hfs]]; [discriminate Hc|].
    pose proof (openat_plain_name_noslash _ Hdot) as Hunw. apply openat_plain_name_nodirref in Hdot.
    rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
    unfold Open.check_openat_resolved. rewrite Hunw. cbv beta iota. rewrite Hfl, Z.eqb_refl. cbv beta iota.
    unfold Open.check_openat_read. rewrite Hdot, Hfs. apply check_copyins_after_ret_only.
Qed.

(* [comment removed for export] *)
Lemma open_det_fail : forall E fx R M model e,
  cs_okW TOP (m_fs model) fds_std M0 (U_S1 p a0v data) E hOPEN fx R M model ->
  1 <= e <= 4095 ->
  (forall eff, check_syscall (sys_input RSEGS (LibWritevF.epend (fx:=fx) R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)) (getr R 17)) eff model
               = check_ret_only_copyins (open_copyins (LibWritevF.epend (fx:=fx) R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17))) eff (errno_ret e) model []) ->
  RZ (cfgF RSEGS fx R (pc hOPEN) M model) (t_die (msg_cannot_open p) (m_fs model)).
Proof using Ha0 Hp0 SRX.
  intros E fx R M model e HC He Hchk.
  destruct ecall_O as (Hec & H17 & H10 & H12 & H11 & Hpc).
  destruct (GPS.is_ecall_at_sound RSEGS hOPEN Hec) as (w & HF & HE & Hpc0 & Hpc4).
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)) with (LibWritevF.epend (fx:=fx) R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)).
  eapply (sr_silent1 RSEGS SR).
  { apply (node_ret_only_copyins RSEGS _ model (getr R 17) _ (errno_ret e) model [] (co_halt HC) (epend_svc _ _ _ _ _) Hchk (co_halt HC) (co_lazy HC)). }
  rewrite adv_set_epend, v_addi_pc4 by (unfold two64; lia). rewrite Hpc.
  apply (open_fail_die E fx R M model _ HC). unfold errno_ret. rewrite Z_to_bv_unsigned. unfold bv_wrap, two64.
  change (bv_modulus 64) with (2 ^ 64). rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.

(* [comment removed for export] *)
Theorem open_toolong_sound : forall E fx R M model,
  cs_okW TOP (m_fs model) fds_std M0 (U_S1 p a0v data) E hOPEN fx R M model -> (4096 <= length p)%nat ->
  RZ (cfgF RSEGS fx R (pc hOPEN) M model) (t_die (msg_cannot_open p) (m_fs model)).
Proof using Ha0 Hp0 SRX.
  intros E fx R M model HC HL.
  destruct ecall_O as (Hec & H17 & H10 & H12 & H11 & Hpc).
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 17 56 HC ltac:(lia) H17)) as G17.
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 12 _ HC ltac:(lia) H12)) as G12.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 11 HC ltac:(lia)) as G11. rewrite H11 in G11.
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E11 in G11. rewrite E12 in G12.
  apply (open_det_fail E fx R M model ENAMETOOLONG HC ltac:(unfold ENAMETOOLONG; lia)).
  apply (openat_toolong_check RSEGS _ (getr R 17) model).
  - rewrite G17. apply u64_lit. lia.
  - rewrite ms_gpr_epend2, G12. apply modeled_open_flags_rd. rewrite u64_lit by lia. reflexivity.
  - rewrite (@ms_read_byte_epend fx RSEGS), ms_gpr_epend1, G11.
    apply (read_cstr_toolong_of_rdn RSEGS M (edenot E STR1) (firstn 4096 p)).
    + rewrite firstn_length_le; [reflexivity | lia].
    + intros Hin. apply Hp0. rewrite <- (firstn_skipn 4096 p). apply in_app_iff. left. exact Hin.
    + pose proof (path_rdn p a0v data TOP M0 fds_std E fx R M model HC) as RD.
      pose proof (Mh32.RefLayout.rdn_skipn RSEGS M (length p + 1) (edenot E STR1) (p ++ [Z_to_bv 8 0]) 0%nat 4096%nat RD ltac:(lia)) as X.
      rewrite word_add_nat_0 in X.
      rewrite X. f_equal. change (skipn 0 (p ++ [Z_to_bv 8 0])) with (p ++ [Z_to_bv 8 0]).
      rewrite firstn_app. replace (4096 - length p)%nat with 0%nat by (first [ (clear - HC HL Hp0 RD X; lia) | lia ]). cbn [firstn]. apply app_nil_r.
Qed.

(* [comment removed for export] *)
Theorem open_noent_sound : forall E fx R M model,
  cs_okW TOP (m_fs model) fds_std M0 (U_S1 p a0v data) E hOPEN fx R M model -> (length p <= 4095)%nat ->
  (path_eqb p [] = true \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
  RZ (cfgF RSEGS fx R (pc hOPEN) M model) (t_die (msg_cannot_open p) (m_fs model)).
Proof using Ha0 Hp0 SRX.
  intros E fx R M model HC HL Hcase.
  destruct ecall_O as (Hec & H17 & H10 & H12 & H11 & Hpc).
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 17 56 HC ltac:((first [ ((repeat match goal with H : _ |- _ => clear H end); lia) | lia ])) H17)) as G17.
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 10 _ HC ltac:(lia) H10)) as G10.
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 12 _ HC ltac:(lia) H12)) as G12.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 11 HC ltac:(lia)) as G11. rewrite H11 in G11.
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
  apply (open_det_fail E fx R M model ENOENT HC ltac:(unfold ENOENT; lia)).
  apply (openat_noent_check _ (getr R 17) model p).
  - rewrite G17. apply u64_lit. lia.
  - rewrite ms_gpr_epend0, G10. symmetry. exact AT_FDCWD_val.
  - rewrite (@ms_read_byte_epend fx RSEGS), ms_gpr_epend1, G11. apply read_cstr_of_rdn; [exact HL | exact Hp0 | exact (path_rdn p a0v data TOP M0 fds_std E fx R M model HC)].
  - rewrite ms_gpr_epend2, G12, u64_lit by lia. reflexivity.
  - exact Hcase.
Qed.
End CO.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section RF.
Variables (p : Fs.path) (data : list byte) (TOP : Z) (M1 : mem) (len : Z).
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GUBSAN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okS TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVcS TOP M0) fx_ok U).
#[local] Notation FDSR := (FDSr p (len + (2 ^ 26 - len))).

(* [comment removed for export] *)
Lemma sd_lit1 : forall HOLES D E fs z,
  t_eq (sd HOLES D E fs (SEmitP 2 [SPLit z] (SEmitP 1 [] (SExit 2)))) (t_die (map (Z_to_bv 8) z) fs).
Proof using.
  intros HOLES D E fs z. unfold t_die. cbn [sd]. unfold Wp, Spec4.W. cbn [flat_map piece_den]. rewrite !app_nil_r.
  apply Spec4.AgentLib.t_emit_congr. apply emit1_nil.
Qed.
Lemma zRF_ok : map (Z_to_bv 8) zRF = msg_refused. Proof using. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma RF_xfer : forall E fx R M model,
  cs_okS TOP (m_fs model) FDSR M1 (U_rd data len (2 ^ 26)) E tVRb fx R M model ->
  cs_okE TOP (m_fs model) FDSR M (U_rd data len (2 ^ 26)) E tRF fx R M model.
Proof using.
  intros E fx R M model HC.
  destruct tRF_parts as (Pkn & Pvis & Pbrk & Pylo & Pmaps & Plog & Ppc & Pregs & Pnx).
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL].
  constructor.
  - rewrite Pregs. exact CR.
  - exact Plog.
  - rewrite Pkn. apply know_ok_cons; [apply kn_errno | exact CK].
  - exact CH. - exact CZ. - exact CF. - exact CD.
  - rewrite Pvis. destruct CA as (HA & _ & HT & _).
    split; [exact (SHP_of_AINV_R _ _ _ _ _ HA)|].
    split; [intros z Hz; right; right; exact (PERM_E_SWIN z Hz)|]. split; [exact HT|].
    split; [intros; reflexivity | intros a _ HH; exact HH].
  - exact CU.
  - exact CX.
  - exact (PERM_Ec_den _).
  - rewrite Pbrk. exact CT.
  - exact CM.
  - rewrite Pmaps, Pbrk, Pylo. exact CFL.
Qed.

(* [comment removed for export] *)
Lemma RF_sound : forall E fx R M model,
  cs_okE TOP (m_fs model) FDSR M (U_rd data len (2 ^ 26)) E tRF fx R M model ->
  RZ (cfgF RSEGS fx R (pc tRF) M model) (t_die msg_refused (m_fs model)).
Proof using SRX.
  intros E fx R M model HC. rewrite <- zRF_ok.
  eapply (sr_conseq RSEGS SR); [| apply (sd_lit1 HOLE_0 t_nil E (m_fs model) zRF)].
  exact (drvE_cert_sound SR SRX TOP (m_fs model) FDSR M (fds3_1 _ _) (fds3_2 _ _) (U_rd data len (2 ^ 26)) (U_rd_agree data len (2 ^ 26))
           [] (fun E j _ Hj => match Hj with end) false (fun H : false = true => ltac:(discriminate H))
           HS0 HOLE_0 (fun _ _ _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun h ch Hh => ltac:(discriminate Hh))
           BF FUEL planRF tRF _ E fx R M model eq_refl certRF HC eq_refl).
Qed.

(* [comment removed for export] *)
Theorem refused_sound : forall E fx R M model,
  cs_okS TOP (m_fs model) FDSR M1 (U_rd data len (2 ^ 26)) E tVRb fx R M model ->
  RZ (cfgF RSEGS fx R (pc tVRb) M model) (t_die msg_refused (m_fs model)).
Proof using SRX.
  intros E fx R M model HC.
  destruct tRF_parts as (_ & _ & _ & _ & _ & _ & Ppc & _). rewrite <- Ppc.
  exact (RF_sound E fx R M model (RF_xfer E fx R M model HC)).
Qed.
End RF.
End Dies.
End UbDrvS0Glue.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Fs Require Import Open.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Plan OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.ExitSim.SimInv OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.FileSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.AgentNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.ZStores OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.ArgvEnv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.RefLayout OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup1.UbStartupDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbStartup UbStartupFacts OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.ShapeLaws OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRel OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.ShapeRetry OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymStepR OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3B OSSVerify.Proofs.glaze.binary_reflection.lib.GxSymExec3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxSymRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlanCore OSSVerify.Proofs.glaze.binary_reflection.lib.GxPlan OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound.GxPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzPlanSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzIface OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzContracts OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall.GlzFrame OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzEntry OSSVerify.Proofs.glaze.binary_reflection.lib.GlzCall OSSVerify.Proofs.glaze.binary_reflection.lib.B2JCutShare.GlzCallCert OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.GlzNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs.UbImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzImageUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.MhKInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0.UbMhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocR0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.GuFuzzT OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks.UbDrvIT OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvNodesSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvHooks OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan.UbDrvHooksS OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound.UbDrvTInst OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS3Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvSSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS2Glue OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Plan OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound.UbDrvGSound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS1Sound UbDrvS0Sound UbDrvS1Open OSSVerify.Proofs.glaze.binary_reflection.lib.GlzSpecsStr.UbDrvNodes2 UbDrvNodes2Sound OSSVerify.Proofs.glaze.binary_reflection.lib.UbDrvS0Plan UbDrvESound UbDrvS0Glue OSSVerify.Proofs.glaze.binary_reflection.lib.LibWritevF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S. Import AP. Import APS. Import GPS.
Open Scope Z_scope.

#[local] Notation RSEGS := USEGS.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition FDSd : list (word * FdEntry) := (Z_to_bv 64 3, State.FdDir) :: fds_std.
Lemma fdsd_1 : fd_lookup FDSd (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1)). Proof. reflexivity. Qed.
Lemma fdsd_2 : fd_lookup FDSd (Z_to_bv 64 2) = Some (FdChannel (Z_to_bv 64 2)). Proof. reflexivity. Qed.
Lemma fdsd_3 : true = true -> fd_lookup FDSd (Z_to_bv 64 3) = Some State.FdDir. Proof. intros _. reflexivity. Qed.
Lemma fd_insert_std_dir : fd_insert fds_std (Z_to_bv 64 3) State.FdDir = FDSd. Proof. reflexivity. Qed.
Lemma zRE_ok : map (Z_to_bv 8) zRE = s2b "cli: read error on "%string. Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma hM1_more : a_brk hM1 = SP0
  /\ forallb (fun K => existsb (kentry_eqb K) (kn hM1))
       [KBlob (SA STR1 0) L1 2; KRange SP0 (APC.CEIL + YLO) (HI47 - 48); KRange D1 64 4194304; KRange L1 0 131071] = true.
Proof. vm_compute. split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma openat_dir_check : forall ms x8 model q,
  bv_unsigned x8 = 56%Z ->
  ms_gpr ms 0 = AT_FDCWD ->
  read_cstr (ms_read_byte ms) (ms_gpr ms 1) = CstrOk q ->
  path_eqb q [] = false ->
  Z.ldiff (bv_unsigned (ms_gpr ms 2)) open_ignored_flags = 0%Z ->
  path_is_dirref q = true ->
  forall eff, check_syscall (sys_input RSEGS ms x8) eff model
              = check_open_result_copyins (open_copyins ms) eff model (fun fd => with_fds (fd_insert (m_fds model) fd State.FdDir) model).
Proof.
  intros ms x8 model q Hno Hdirfd Hpath Hpe Hfl Hdir eff.
  rewrite (check_syscall_56 RSEGS ms x8 eff model Hno). unfold check_openat.
  rewrite (modeled_open_flags_rd _ Hfl). cbn [negb]. cbv beta iota.
  unfold Prelude.check_copyins_after, Open.check_openat_body.
  rewrite in_mem_si, Hpath. cbv beta iota zeta.
  rewrite Hpe. cbv beta iota.
  rewrite Hdirfd; norm_fd32; rewrite bv_eqb_refl. cbn [negb]. cbv beta iota.
  unfold Open.check_openat_resolved. rewrite (path_is_dirref_no_slash _ Hdir). cbv beta iota. rewrite Hfl, Z.eqb_refl. cbv beta iota.
  unfold Open.check_openat_read. rewrite Hdir.
  unfold check_open_result_copyins, open_copyins.
  destruct (check_open_result (clear_copyins eff) model (fun fd : word => with_fds (fd_insert (m_fds model) fd State.FdDir) model)) eqn:Hresult.
  - reflexivity.
  - reflexivity.
  - exfalso. now apply check_open_result_never_unmodeled in Hresult.
Qed.

Section Dir.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
(* [comment removed for export] *)
Hypothesis HM1 : forall fx : FPState, @MALLOC_FIRST_ALT3 RC fx MSTK_M.
#[local] Notation AINVcS TOP M0 := (AINV_f SWIN_T GUBSAN AINV_R PERM_Tc TOP [] M0 0 0).
#[local] Notation AINVc H TOP M0 := (AINV_f SWIN_T GUBSAN H PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okI H TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVc H TOP M0) fx_ok U).
#[local] Notation AINVe TOP M0 := (AINV_f SWIN_E GE SHP PERM_Ec TOP [] M0 0 0).
#[local] Notation cs_okE TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Ec TOP FS0 FDS0 (AINVe TOP M0) fx_ok U).

Variables (p a0v : list byte) (TOP : Z) (M0 : mem) (auxw : Z) (avl : list (Z * Z)).
Hypothesis FEC : fe_cells M0 auxw avl.
Hypothesis ENV : env_above_sp auxw avl TOP.
Hypothesis Hp0 : ~ In (Z_to_bv 8 0) p.
Hypothesis Ha0 : ~ In (Z_to_bv 8 0) a0v.
Hypothesis HpL : (length p <= 4095)%nat.
#[local] Notation U := (U_S1 p a0v []).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition BLOB (E : env) (M : mem) : Prop := kentry_ok RSEGS E M (KBlob (SA STR1 0) L1 2).

Lemma blob_env : forall E E' M,
  ev E' 0%nat = ev E 0%nat -> ev E' 5%nat = ev E 5%nat -> ev E' 6%nat = ev E 6%nat -> eb E' 2%nat = eb E 2%nat ->
  BLOB E M -> BLOB E' M.
Proof.
  intros E E' M H0 H5 H6 HB X. unfold BLOB, kentry_ok, flat, estart, elenZ in *. cbn [a_base a_off edenot STR1 SP0 D1 L1] in *.
  rewrite H0, H5, H6, HB. exact X.
Qed.

Lemma blob_mem : forall E M M',
  (forall i, 0 <= i < elenZ E L1 -> M' (Z_to_bv 64 (estart E (SA STR1 0) + i)) = M (Z_to_bv 64 (estart E (SA STR1 0) + i))) ->
  BLOB E M -> BLOB E M'.
Proof.
  intros E M M' HM (F & LEN & BY). split; [exact F|]. split; [exact LEN|]. intros i Hi. rewrite (HM i Hi). exact (BY i Hi).
Qed.

(* [comment removed for export] *)
Lemma hM1_blob : forall FS FDS E fx R M model,
  cs_okI W0 TOP FS FDS M0 U E hM1 fx R M model ->
  BLOB E M0 /\ TOP <= estart E (SA STR1 0) /\ estart E (SA STR1 0) + elenZ E L1 <= 2 ^ 64.
Proof.
  intros FS FDS E fx R M model HC. pose proof (co_know HC) as HK. destruct hM1_more as [Hbrk Hsub].
  pose proof (kn_hit E M (KBlob (SA STR1 0) L1 2) _ _ Hsub ltac:(cbn; tauto) HK) as KB.
  pose proof (kn_hit E M (KRange SP0 (APC.CEIL + YLO) (HI47 - 48)) _ _ Hsub ltac:(cbn; tauto) HK) as K0.
  pose proof (kn_hit E M (KRange D1 64 4194304) _ _ Hsub ltac:(cbn; tauto) HK) as K5.
  cbn [kentry_ok] in K0, K5. fold (uE E SP0) in K0. fold (uE E D1) in K5. unfold APC.CEIL, YLO, HI47 in K0.
  assert (US : estart E (SA STR1 0) = uE E SP0 + uE E D1).
  { rewrite estart_SA. unfold STR1, uE. cbn [edenot]. pose proof (u64_range (edenot E SP0)). pose proof (u64_range (edenot E D1)). unfold uE in *.
    rewrite u_add64. rewrite Z.mod_small by lia. lia. }
  assert (HT : TOP = uE E SP0).
  { pose proof (co_top HC) as CT. rewrite Hbrk in CT. unfold sptop_den in CT. destruct (Z.eqb_spec (uE E SP0) 0); [lia | exact (eq_sym CT)]. }
  destruct KB as (F & LEN & BY).
  split; [| split; [lia | destruct F as (_ & _ & _ & F4); exact F4]].
  apply (blob_mem E M M0); [| exact (conj F (conj LEN BY))].
  intros i Hi. destruct (co_ainv HC) as (_ & _ & HCT & HZ & _). symmetry. apply HZ.
  destruct F as (F1 & F2 & F3 & F4). apply zone_top; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RDe_xfer : forall FS E fx R M model,
  cs_okI AINV_R TOP FS FDSd M0 U E tR0d' fx R M model -> BLOB E M ->
  cs_okE TOP FS FDSd M (U_D a0v p) E tR0e fx R M model.
Proof.
  intros FS E fx R M model HC HB.
  destruct tR0e_parts as (Pkn & Pvis & Pbrk & Pylo & Pmaps & Plog & Ppc & Pregs & Pnx).
  destruct HC as [CR CL CK CH CZ CF CD CA CU CX CP CT CM CFL].
  constructor.
  - rewrite Pregs. exact CR.
  - exact Plog.
  - rewrite Pkn. apply know_ok_cons; [apply kn_errno |]. apply know_ok_cons; [exact HB | exact CK].
  - exact CH. - exact CZ. - exact CF. - exact CD.
  - rewrite Pvis. destruct CA as (HA & _ & HT & _).
    split; [exact (SHP_of_AINV_R _ _ _ _ _ HA)|].
    split; [intros z Hz; right; right; exact (PERM_E_SWIN z Hz)|]. split; [exact HT|].
    split; [intros; reflexivity | intros a _ HH; exact HH].
  - destruct CU as (_ & E2 & E1). split; [exact E1 | exact E2].
  - exact CX.
  - exact (PERM_Ec_den _).
  - rewrite Pbrk. exact CT.
  - exact CM.
  - rewrite Pmaps, Pbrk, Pylo. exact CFL.
Qed.

(* [comment removed for export] *)
Lemma dir_die : forall E fx R M model,
  cs_okE TOP (m_fs model) FDSd M (U_D a0v p) E tR0e fx R M model ->
  RZ (cfgF RSEGS fx R (pc tR0e) M model) (t_die (msg_read_error p) (m_fs model)).
Proof.
  intros E fx R M model HC. unfold msg_read_error. rewrite <- zRE_ok, <- zNL_ok.
  replace p with (eb E 2) at 1 by exact (proj2 (co_uinv HC)).
  exact (die_cert_sound SR SRX TOP M FDSd a0v p true tR0e planD L1 60 61 zRE 2 zNL E fx R M model fdsd_1 fdsd_2 fdsd_3 Ha0 Hp0 eq_refl certD HC).
Qed.

(* [comment removed for export] *)
Theorem M1d_sound : forall E fx R M model,
  cs_okI W0 TOP (m_fs model) FDSd M0 U E hM1 fx R M model ->
  RZ (cfgF RSEGS fx R (pc hM1) M model) (t_opened_dir p (m_fs model)).
Proof.
  intros E fx R M model HC. unfold t_opened_dir.
  destruct (hM1_blob _ _ E fx R M model HC) as (HB0 & HT0 & HF0).
  refine (M1_gen SR SRX HM1 TOP M0 auxw avl FEC ENV FDSd U tR0d' (fun fs => t_die (msg_read_error p) fs) fdsd_1 fdsd_2
            (U_S1_agree p a0v []) entN1d _ E fx R M model _ HC).
  - intros E0 ((UF & UB) & U2 & U1). destruct thN1d as (T4 & _).
    split; [split; [rewrite (tenv_uE _ _ _ _ T4); exact UF | rewrite tenv_eb; exact UB] | rewrite !tenv_eb; split; [exact U2 | exact U1]].
  - intros E' fx' R' M' mdl' Hag HC'. destruct thN1d as (T4 & T0 & T5 & T6).
    destruct (tR0e_parts) as (_ & _ & _ & _ & _ & _ & Ppc & _). rewrite <- Ppc.
    pose proof (co_fs HC') as Hfs'. rewrite <- Hfs'.
    apply (dir_die (tenv E' (TH29 hN1 tR0d' [])) fx' R' M' mdl'). rewrite Hfs'. apply (RDe_xfer _ _ fx' R' M' mdl' HC').
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (A0 : ev (tenv E' (TH29 hN1 tR0d' [])) 0%nat = ev E 0%nat) by (etransitivity; [exact (tenv_ev _ _ _ _ T0)|]; cbn [edenot]; symmetry; apply (proj1 Hag); unfold NXD; lia).
    assert (A5 : ev (tenv E' (TH29 hN1 tR0d' [])) 5%nat = ev E 5%nat) by (etransitivity; [exact (tenv_ev _ _ _ _ T5)|]; cbn [edenot]; symmetry; apply (proj1 Hag); unfold NXD; lia).
    assert (A6 : ev (tenv E' (TH29 hN1 tR0d' [])) 6%nat = ev E 6%nat) by (etransitivity; [exact (tenv_ev _ _ _ _ T6)|]; cbn [edenot]; symmetry; apply (proj1 Hag); unfold NXD; lia).
    assert (AB : eb (tenv E' (TH29 hN1 tR0d' [])) 2%nat = eb E 2%nat) by (rewrite tenv_eb; rewrite <- (proj2 Hag); reflexivity).
    apply (blob_env E _ M' A0 A5 A6 AB).
    apply (blob_mem E M0 M'); [| exact HB0].
    intros i Hi. destruct (co_ainv HC') as (_ & _ & HCT & HZ & _). apply HZ. apply zone_top; lia.
Qed.

(* [comment removed for export] *)
Theorem AOd_sound : forall E fx R M model,
  cs_okI W0 TOP (m_fs model) FDSd M0 U E tAO fx R M model ->
  RZ (cfgF RSEGS fx R (pc tAO) M model) (t_opened_dir p (m_fs model)).
Proof.
  intros E fx R M model HC.
  exact (AO_gen SR SRX TOP M0 FDSd U (t_opened_dir p) fdsd_1 fdsd_2 (U_S1_agree p a0v []) (fun fs => t_opened_dir_has_nil p fs)
           E fx R M model (fun E' fx' R' M' model' HC' =>
             ltac:(pose proof (co_fs HC') as Hfs'; rewrite <- Hfs' in HC' |- *; exact (M1d_sound E' fx' R' M' model' HC'))) HC).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis Hdir : path_is_dirref p = true.
Lemma Hpn : path_eqb p [] = false.
Proof. unfold path_is_dirref in Hdir. destruct p; [discriminate Hdir | reflexivity]. Qed.

Lemma open_step_d : forall E fx R M model B,
  cs_okI W0 TOP (m_fs model) fds_std M0 U E hOPEN fx R M model ->
  RZ (cfgF RSEGS fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 3)) P_AFTER_ECALL M (with_fds FDSd model)) B ->
  RZ (cfgF RSEGS fx R (pc hOPEN) M model) (t_alt2 (t_die (msg_cannot_open p) (m_fs model)) B).
Proof.
  intros E fx R M model B HC HB.
  destruct ecall_O as (Hec & H17 & H10 & H12 & H11 & Hpc).
  destruct (GPS.is_ecall_at_sound RSEGS hOPEN Hec) as (w & HF & HE & Hpc0 & Hpc4).
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 17 56 HC ltac:(lia) H17)) as G17.
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 10 _ HC ltac:(lia) H10)) as G10.
  pose proof (proj1 (GPS.reg_lit_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 12 _ HC ltac:(lia) H12)) as G12.
  pose proof (GPS.reg_sound _ _ _ _ _ _ _ _ E hOPEN fx R M model 11 HC ltac:(lia)) as G11. rewrite H11 in G11.
  assert (E17 : Z_to_bv 5 (Z.of_nat 17) = (17%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E10 : Z_to_bv 5 (Z.of_nat 10) = (10%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E11 : Z_to_bv 5 (Z.of_nat 11) = (11%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  assert (E12 : Z_to_bv 5 (Z.of_nat 12) = (12%bv : Prelude.reg)) by (apply bv_eq; reflexivity).
  rewrite E17 in G17. rewrite E10 in G10. rewrite E11 in G11. rewrite E12 in G12.
  unfold cfgF.
  eapply (sr_step RSEGS SR); [exact (co_halt HC) | exact (co_lazy HC) | reflexivity | eapply GPS.step_ecallF; eassumption |].
  change (GPS.ependF fx R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)) with (@epend fx R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)).
  set (ms := @epend fx R (Z_to_bv 64 (pc hOPEN)) M (seg_rom RSEGS) (getr R 17)).
  set (mk := fun fd : word => with_fds (fd_insert (m_fds model) fd State.FdDir) model).
  apply (sr_alt2 RSEGS SR (mkCfg ms model) {e : Z | In e openat_errnos} unit (open_nx ms model mk) _ B (exist _ ENOMEM ENOMEM_in_openat_errnos) tt).
  - apply (node_open RSEGS ms model (getr R 17) (open_copyins ms) mk (co_halt HC) (co_lazy HC) (epend_svc _ _ _ _ _)).
    + apply (openat_dir_check ms (getr R 17) model p).
      * rewrite G17. apply u64_lit. lia.
      * unfold ms. rewrite ms_gpr_epend0, G10. symmetry. exact AT_FDCWD_val.
      * unfold ms. rewrite (@ms_read_byte_epend fx RSEGS), ms_gpr_epend1, G11. apply read_cstr_of_rdn; [exact HpL | exact Hp0 | exact (path_rdn _ _ _ _ _ _ E fx R M model HC)].
      * exact Hpn.
      * unfold ms. rewrite ms_gpr_epend2, G12, u64_lit by lia. reflexivity.
      * exact Hdir.
    + intros fd. unfold mk. cbn [m_halted with_fds]. exact (co_halt HC).
    + intros fd. unfold mk. cbn [m_vm_lazy with_fds]. exact (co_lazy HC).
    + rewrite (co_fds HC). reflexivity.
    + rewrite G17. reflexivity.
  - intros [e He]. cbn [open_nx]. unfold ms. rewrite adv_set_epend, v_addi_pc4 by (unfold two64; lia). rewrite Hpc.
    exact (cantopen_sound SR SRX p a0v [] TOP M0 Hp0 Ha0 E fx R M model e HC He).
  - intros []. cbn [open_nx]. unfold ms, mk. rewrite (co_fds HC), alloc_fd_std, fd_insert_std_dir.
    rewrite adv_set_epend, v_addi_pc4 by (unfold two64; lia). rewrite Hpc. exact HB.
Qed.

Theorem Od_sound : forall E fx R M model,
  cs_okI W0 TOP (m_fs model) fds_std M0 U E hOPEN fx R M model ->
  RZ (cfgF RSEGS fx R (pc hOPEN) M model) (t_alt2 (t_die (msg_cannot_open p) (m_fs model)) (t_opened_dir p (m_fs model))).
Proof.
  intros E fx R M model HC. apply (open_step_d E fx R M model _ HC).
  pose proof (AOd_sound E fx (regupd R (Z_to_bv 5 10) (Z_to_bv 64 3)) M (with_fds FDSd model)) as X.
  cbn [m_fs with_fds] in X. rewrite (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 tAO_parts))))))) in X.
  apply X. exact (open_xfer TOP M0 _ U State.FdDir E fx R M model HC).
Qed.

Theorem MOd_sound : forall E fx R M model,
  cs_okI W0 TOP (m_fs model) fds_std M0 U E tMo fx R M model ->
  RZ (cfgF RSEGS fx R (pc tMo) M model) (t_alt2 (t_die (msg_cannot_open p) (m_fs model)) (t_opened_dir p (m_fs model))).
Proof.
  intros E fx R M model HC.
  exact (MO_gen SR SRX TOP M0 U (fun fs => t_alt2 (t_die (msg_cannot_open p) fs) (t_opened_dir p fs)) (U_S1_agree p a0v [])
           (fun fs => or_introl (t_die_has_nil _ fs)) E fx R M model (fun E' fx' R' M' model' HC' =>
             ltac:(pose proof (co_fs HC') as Hfs'; rewrite <- Hfs' in HC' |- *; exact (Od_sound E' fx' R' M' model' HC'))) HC).
Qed.
End Dir.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MainOther.
Context {RC : run_ceil}.
Variable SR : shape_rel RSEGS.
Hypothesis SRX : sr_exactness RSEGS SR.
#[local] Notation RZ := (sr_rel RSEGS SR).
Hypothesis HM1 : forall fx : FPState, @MALLOC_FIRST_ALT3 RC fx MSTK_M.
#[local] Notation AINVc H TOP M0 := (AINV_f SWIN_T GUBSAN H PERM_Tc TOP [] M0 0 0).
#[local] Notation cs_okI H TOP FS0 FDS0 M0 U := (GPS.cs_ok RSEGS PERM_Tc TOP FS0 FDS0 (AINVc H TOP M0) fx_ok U).
Variable sp0 : word.
Variables av ev : list (list byte).
Variables uid hw : word.
Variable rdraw : EntryDraw.
Variable tid : word.
Variable regs : bvmap 5 word.
Variable mem : word -> option byte.
Variable model : Model.
Hypothesis Hva : valid_argv av.
Hypothesis Hve : valid_envp ev.
Hypothesis Hvsp : valid_sp sp0.
Hypothesis Hfits : entry_stack_fits sp0 av ev.
Hypothesis Htid : 0 < bv_unsigned tid < 4194304.
Hypothesis ME : main_entry sp0 av ev uid hw rdraw tid regs mem.
Hypothesis Mh : m_halted model = None.
Hypothesis Ml : m_vm_lazy model = [].
Hypothesis Mm : m_vm_materialized model = [].
Hypothesis Mfd : m_fds model = fds_std.
Hypothesis MV : VM0 model.
Hypothesis MC : CEIL_run <= bv_unsigned sp0 - 8388608.
#[local] Notation TOP := (TOPm sp0).
Variables (a0 p : Fs.path).
Hypothesis Hav : av = [a0; p].

#[local] Notation E := (EM sp0 av ev rdraw tid regs (LB []) (hdr [])).
Lemma main_U : U_S1 p a0 [] E.
Proof.
  split; [split|split].
  - unfold uE. cbn. pose proof (Z.le_min_r (L []) (2 ^ 40)). pose proof (Zle_0_nat (@length byte [])). unfold LB, L in *. apply u64_lit. lia.
  - reflexivity.
  - cbn. rewrite Hav. reflexivity.
  - cbn. rewrite Hav. reflexivity.
Qed.
Lemma main_HC : cs_okI W0 TOP (m_fs model) fds_std mem (U_S1 p a0 []) E tMo fx0 regs mem model.
Proof.
  assert (H2 : length av = 2%nat) by (rewrite Hav; reflexivity).
  exact (main_cs_ok2 sp0 av ev uid hw rdraw tid regs mem Hva Hve Hvsp Hfits Htid ME (LB []) (hdr []) (U_S1 p a0 []) model H2 main_U Mh Ml Mm Mfd MV MC).
Qed.
Lemma Hp0 : ~ In (Z_to_bv 8 0) p.
Proof. pose proof (valid_argv_str_nz av 1 Hva ltac:(rewrite Hav; cbn; lia)) as X. rewrite Hav in X. exact X. Qed.
Lemma Ha0 : ~ In (Z_to_bv 8 0) a0.
Proof. pose proof (valid_argv_str_nz av 0 Hva ltac:(rewrite Hav; cbn; lia)) as X. rewrite Hav in X. exact X. Qed.

(* [comment removed for export] *)
Theorem main_dir_sound : (length p <= 4095)%nat -> path_is_dirref p = true ->
  RZ (cfgF RSEGS fx0 regs P_MAIN mem model) (t_alt2 (t_die (msg_cannot_open p) (m_fs model)) (t_opened_dir p (m_fs model))).
Proof.
  intros HpL Hdir.
  exact (MOd_sound SR SRX HM1 p a0 TOP mem (AUXW sp0 av ev) (AVL sp0 av ev uid hw)
           (main_fe_cells sp0 av ev uid hw rdraw tid regs mem Hva Hve Hvsp ME) (main_env_above sp0 av ev uid hw rdraw tid regs mem Hva Hve Hvsp ME)
           Hp0 Ha0 HpL Hdir E fx0 regs mem model main_HC).
Qed.

(* [comment removed for export] *)
Theorem main_toolong_sound : (4096 <= length p)%nat ->
  RZ (cfgF RSEGS fx0 regs P_MAIN mem model) (t_die (msg_cannot_open p) (m_fs model)).
Proof.
  intros HL.
  exact (MO_gen SR SRX TOP mem (U_S1 p a0 []) (fun fs => t_die (msg_cannot_open p) fs) (U_S1_agree p a0 []) (fun fs => t_die_has_nil _ fs)
           E fx0 regs mem model (fun E' fx' R' M' model' HC' =>
             ltac:(pose proof (co_fs HC') as Hfs'; rewrite <- Hfs' in HC' |- *; exact (open_toolong_sound SR SRX p a0 [] TOP mem Hp0 Ha0 E' fx' R' M' model' HC' HL))) main_HC).
Qed.

(* [comment removed for export] *)
Theorem main_noent_sound : (length p <= 4095)%nat ->
  (path_eqb p [] = true \/ (openat_plain_name p = true /\ fs_lookup (m_fs model) p = None)) ->
  RZ (cfgF RSEGS fx0 regs P_MAIN mem model) (t_die (msg_cannot_open p) (m_fs model)).
Proof.
  intros HL Hcase.
  exact (MO_gen SR SRX TOP mem (U_S1 p a0 []) (fun fs => t_die (msg_cannot_open p) fs) (U_S1_agree p a0 []) (fun fs => t_die_has_nil _ fs)
           E fx0 regs mem model (fun E' fx' R' M' model' HC' =>
             ltac:(pose proof (co_fs HC') as Hfs'; rewrite <- Hfs' in HC' |- *;
                   exact (open_noent_sound SR SRX p a0 [] TOP mem Hp0 Ha0 E' fx' R' M' model' HC' HL ltac:(rewrite Hfs'; exact Hcase)))) main_HC).
Qed.
End MainOther.
