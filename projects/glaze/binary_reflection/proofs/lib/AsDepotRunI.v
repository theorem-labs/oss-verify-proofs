(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsDepotBlk.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.

Section FPGen.
Context {fx : FPState}.

Lemma land_m4 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x (2 ^ 64 - 4) = (x - x mod 4)%Z.
Proof using.
  intros x Hx. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  assert (Em : (2 ^ 64 - 4 = Z.shiftl (2 ^ 62 - 1) 2)%Z) by reflexivity. rewrite Em.
  assert (Ex : (x - x mod 4 = Z.shiftl (x / 2 ^ 2) 2)%Z).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2)%Z with 4%Z. pose proof (Z.div_mod x 4 ltac:(lia)). lia. }
  rewrite Ex. destruct (Z.lt_ge_cases k 2) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. destruct (Z.lt_ge_cases k 64) as [Hl2|Hg2].
    + assert (Ht : Z.testbit (2 ^ 62 - 1) (k - 2) = true) by (replace (2 ^ 62 - 1)%Z with (Z.ones 62) by reflexivity; apply Z.ones_spec_low; lia).
      rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite (Mh32.LibMaskBits.testbit_high 64 x k) by lia.
      rewrite (Mh32.LibMaskBits.testbit_high 62 (x / 2 ^ 2) (k - 2)); [reflexivity | lia | | lia].
      change (2 ^ 2)%Z with 4%Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma v_andi_m4_aligned : forall x : word, (U x mod 4 = 0)%Z -> v_andi x (-4) = x.
Proof using.
  intros x Hx. pose proof (u64_range x). (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end). change (bv_wrap 64 (-4)) with (2 ^ 64 - 4)%Z.
  rewrite land_m4 by lia. rewrite Hx, Z.sub_0_r. apply Z_to_bv_bv_unsigned.
Qed.

Definition bi_frame (M : word -> option byte) (sp ra s0v s1v s2v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)) (at_ sp (-24)) (LE8 s1v)) (at_ sp (-32)) (LE8 s2v).
Definition bi_m1 (M : word -> option byte) (sp ra s0v s1v s2v BI S alv : word) (b1 b2 b3 : byte) : word -> option byte :=
  wbytes (wbytes (bi_frame M sp ra s0v s1v s2v) (at_ BI 12) [Z_to_bv 8 1; b1; b2; b3]) (at_ S 8) (LE8 (v_add alv (Z_to_bv 64 8388608))).

Section BIPRE.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v BI S alv lkw : word) (b1 b2 b3 : byte).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H10 : getr regs 10 = BI.
  Hypothesis H11 : getr regs 11 = S.
  Hypothesis Hsp : (2 ^ 32 + 32 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis HS : (U S mod 8 = 0 /\ U S + 16 <= U BI)%Z.
  Hypothesis HBI : (U BI mod 8 = 0 /\ U BI + 16 <= 2 ^ 32)%Z.
  Hypothesis R_lock : rdn ASEGS M (at_ BI 12) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw.
  Hypothesis Rdata : rdn ASEGS M BI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Ralloc : rdn ASEGS M (at_ S 8) 8 = Some (LE8 alv).
  Hypothesis SOKl : store_ok ASEGS M (at_ BI 12) 4 = true.
  Hypothesis SOKa : store_ok ASEGS M (at_ S 8) 8 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-32)) 32 = true.

  Lemma bi_pre :
    exists r, msteps ASEGS (mkst regs (0x8cf90 : word) M rom) (mkst r (0x82340 : word) (bi_m1 M sp ra s0v s1v s2v BI S alv b1 b2 b3) rom)
      /\ getr r 1 = (0x8d000 : word) /\ getr r 2 = at_ sp (-32) /\ getr r 10 = Z_to_bv 64 8388608 /\ getr r 11 = Z_to_bv 64 0x21f70
      /\ getr r 8 = at_ BI 12 /\ getr r 9 = BI
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 15]) regs r.
  Proof using Hstk SOKa SOKl Ralloc Rdata V_lock R_lock HBI HS Hsp H11 H10 H18 H9 H8 H2 H1 lkw.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range BI) as HBr.
    destruct Hsp as [S1 S2]. destruct HS as [S8 SB]. destruct HBI as [B8 B32].
    assert (UL : U (at_ BI 12) = (U BI + 12)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UA : U (at_ S 8) = (U S + 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (AL : (U (at_ BI 12) mod 4 = 0)%Z).
    { rewrite UL. pose proof (Z.div_mod (U BI) 8 ltac:(lia)) as E. rewrite B8 in E. rewrite E.
      replace (8 * (U BI / 8) + 0 + 12)%Z with ((2 * (U BI / 8) + 3) * 4)%Z by lia. apply Z_mod_mult. }
    assert (AA : (U (at_ S 8) mod 8 = 0)%Z).
    { rewrite UA. pose proof (Z.div_mod (U S) 8 ltac:(lia)) as E. rewrite S8 in E. rewrite E.
      replace (8 * (U S / 8) + 0 + 8)%Z with ((U S / 8 + 1) * 8)%Z by lia. apply Z_mod_mult. }
    set (MF := bi_frame M sp ra s0v s1v s2v).
    assert (OUTF : forall x : word, (U x < U sp - 32 \/ U sp <= U x)%Z -> MF x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MF, bi_frame in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GRF : mem_grows M MF) by ((lazymatch goal with |- ?G => let G' := eval unfold MF, bi_frame in G in change_no_check G' end); do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (R_lockF : rdn ASEGS MF (at_ BI 12) 4 = Some [Z_to_bv 8 0; b1; b2; b3]).
    { rewrite <- R_lock. apply rdn_ext; [rewrite UL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite UL in Hx. cbn in Hx. apply OUTF. lia. }
    set (ML := wbytes MF (at_ BI 12) [Z_to_bv 8 1; b1; b2; b3]).
    assert (OUTL : forall x : word, (U x < U BI + 12 \/ U BI + 16 <= U x)%Z -> ML x = MF x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold ML in G in change_no_check G' end). rewrite wbytes_outside; rewrite ?UL; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GRL : mem_grows M ML) by (eapply mem_grows_trans; [exact GRF | apply wbytes_grows]).
    assert (RdataL : rdn ASEGS ML BI 8 = Some (LE8 (Z_to_bv 64 0))).
    { rewrite <- Rdata. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. rewrite OUTL by lia. apply OUTF. lia. }
    assert (RallocL : rdn ASEGS ML (at_ S 8) 8 = Some (LE8 alv)).
    { rewrite <- Ralloc. apply rdn_ext; [rewrite UA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite UA in Hx. cbn in Hx. rewrite OUTL by lia. apply OUTF. lia. }
    wd_eexists. split.
    - an F_8cf88 D_8cf88.                              (* [comment removed for export] *)
      fsd F_8cf8c D_8cf8c (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8cf90 D_8cf90 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_8cf94 D_8cf94 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_8cf98 D_8cf98 (at_ sp (-32)).              (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _) with MF.
      an F_8cf9c D_8cf9c.                              (* [comment removed for export] *)
      an F_8cfa0 D_8cfa0.                              (* [comment removed for export] *)
      an F_8cfa4 D_8cfa4.                              (* [comment removed for export] *)
      an F_8cfa8 D_8cfa8. rewrite (v_andi_m4_aligned (at_ BI 12) AL).   (* [comment removed for export] *)
      an F_8cfac D_8cfac.                              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (xchg_byte_run ASEGS _ (0x8cfb8 : word) (0x8cfbc : word) (0x8cfc0 : word) (0x8cfc4 : word)
                  (0x8cfc8 : word) (0x8cfcc : word) (0x8cfd0 : word) (0x8cfd4 : word) _ rom
                  _ _ _ _ _ _ _ _ _ _ _ 14 12 15 13 10 _ [Z_to_bv 8 0; b1; b2; b3] lkw 0%nat 1%Z
                  F_8cfb0 eq_refl D_8cfb0 F_8cfb4 eq_refl D_8cfb4 F_8cfb8 eq_refl D_8cfb8 F_8cfbc eq_refl D_8cfbc
                  F_8cfc0 eq_refl D_8cfc0 F_8cfc4 eq_refl D_8cfc4 F_8cfc8 eq_refl D_8cfc8).
        all: lazymatch goal with
             | |- v_addi _ _ = _ => first [reflexivity | apply bv_eq; vm_compute; reflexivity]
             | |- _ <> _ => first [regneq | intros X; discriminate X]
             | |- (_ mod 4 = 0)%Z => gres; rwH; exact AL
             | |- rdn _ _ _ _ = _ => gres; rwH; exact R_lockF
             | |- bytes_le_to_Z _ = _ => exact V_lock
             | |- store_ok _ _ _ _ = true => gres; rwH; eapply store_ok_mono; [exact GRF | exact SOKl]
             | |- (_ < _)%nat => lia
             | |- (_ <= _ < _)%Z => lia
             | |- U _ = _ => gres; rwH; unorm; reflexivity
             end. }
      gres. rwH. (lazymatch goal with |- ?G => let G' := eval cbn [firstn skipn app] in G in change_no_check G' end). change (wbytes MF (at_ BI 12) _) with ML.
      av F_8cfcc D_8cfcc (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ V_lock); unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_8cfd0 D_8cfd0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_8cfd4 D_8cfd4 (Z_to_bv 64 0) RdataL.      (* [comment removed for export] *)
      ab_ft F_8cfd8 D_8cfd8 ltac:(condz).              (* [comment removed for export] *)
      an F_8cfdc D_8cfdc.                              (* [comment removed for export] *)
      an F_8cfe0 D_8cfe0.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 alv) (v := alv);
          [exact F_8cfe4 | reflexivity | exact D_8cfe4
          | gres; rwH; rewrite ?at_addi; exact AA
          | gres; rwH; rewrite ?at_addi; exact RallocL
          | apply bytes_le_to_Z_8
          | gres; rwH; rewrite ?at_addi; eapply store_ok_mono; [exact GRL | exact SOKa]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. rewrite ?at_addi.
      change (wbytes ML (at_ S 8) _) with (bi_m1 M sp ra s0v s1v s2v BI S alv b1 b2 b3).
      an F_8cfe8 D_8cfe8.                              (* [comment removed for export] *)
      an F_8cfec D_8cfec.                              (* [comment removed for export] *)
      an F_8cff0 D_8cff0.                              (* [comment removed for export] *)
      an F_8cff4 D_8cff4.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; vm_compute; reflexivity).
  Qed.
End BIPRE.

Definition bi_m2 (MB : word -> option byte) (BI newblk : word) : word -> option byte :=
  wbytes (wbytes MB BI (LE8 newblk)) (at_ BI 12) [Z_to_bv 8 0].

Section BIPOST.
  Variables (MB rom : word -> option byte) (sp ra s0v s1v s2v BI newblk : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-32).
  Hypothesis H8 : getr regs 8 = at_ BI 12.
  Hypothesis H9 : getr regs 9 = BI.
  Hypothesis H10 : getr regs 10 = newblk.
  Hypothesis Hsp : (2 ^ 32 + 32 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HBI : (U BI + 16 <= 2 ^ 32)%Z.
  Hypothesis SOKd : store_ok ASEGS MB BI 8 = true.
  Hypothesis SOKl : store_ok ASEGS MB (at_ BI 12) 1 = true.
  Hypothesis SL : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)]%Z -> rdn ASEGS MB (at_ sp k) 8 = Some (LE8 v).

  Lemma bi_post :
    exists r, msteps ASEGS (mkst regs (0x8d000 : word) MB rom) (mkst r ra (bi_m2 MB BI newblk) rom)
      /\ getr r 10 = newblk /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 18]) regs r.
  Proof using SL SOKl SOKd HBI Hret Hsp H10 H9 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range BI) as HBr. destruct Hsp as [S1 S2].
    assert (UL : U (at_ BI 12) = (U BI + 12)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (SLF : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)]%Z ->
              rdn ASEGS (bi_m2 MB BI newblk) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (K : (-32 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite <- (SL k v Hin). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. (lazymatch goal with |- ?G => let G' := eval unfold bi_m2 in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UL; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    wd_eexists. split.
    - afence F_8cff8 D_8cff8.                          (* [comment removed for export] *)
      fsd F_8cffc D_8cffc BI.                          (* [comment removed for export] *)
      afence F_8d000 D_8d000.                          (* [comment removed for export] *)
      fsb F_8d004 D_8d004 (at_ BI 12) (Z_to_bv 8 0).   (* [comment removed for export] *)
      change (wbytes (wbytes MB BI _) (at_ BI 12) _) with (bi_m2 MB BI newblk).
      cld8 F_8d008 D_8d008 ra (SLF (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8d00c D_8d00c s0v (SLF (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8d010 D_8d010 s1v (SLF (-24)%Z s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8d014 D_8d014 s2v (SLF (-32)%Z s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      an F_8d018 D_8d018.                              (* [comment removed for export] *)
      aret F_8d01c D_8d01c ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End BIPOST.
End FPGen.
End AsDepotBlk.
Module AsDepotLock.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition dl_frame (M : word -> option byte) (sp ra s0v s1v s2v s3v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)) (at_ sp (-24)) (LE8 s1v)) (at_ sp (-32)) (LE8 s2v)) (at_ sp (-40)) (LE8 s3v).
(* [comment removed for export] *)
Definition dl_mem (M : word -> option byte) (sp ra s0v s1v s2v s3v b : word) (v : Z) : word -> option byte :=
  wbytes (dl_frame M sp ra s0v s1v s2v s3v) b (word_to_le_bytes 4 (v_or (Z_to_bv 64 v) (Z_to_bv 64 18446744071562067968))).

Section LOCK.
  Variables (M rom : word -> option byte) (sp ra b s0v s1v s2v s3v : word) (v : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = b.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hb : (U b mod 4 = 0 /\ (U b + 4 <= U sp - 48 \/ U sp <= U b) /\ U b + 4 < 2 ^ 64)%Z.
  Hypothesis Hv : (0 <= v < 2 ^ 31)%Z.                                   (* [comment removed for export] *)
  Hypothesis Rb : rdn ASEGS M b 4 = Some (LE4 v).
  Hypothesis SOKb : store_ok ASEGS M b 4 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-48)) 48 = true.

  Lemma dl_frame_outside : forall x : word, (U x < U sp - 48 \/ U sp <= U x)%Z -> dl_frame M sp ra s0v s1v s2v s3v x = M x.
  Proof using Hsp b.
    intros x Hx. pose proof (u64_range sp). destruct Hsp as [S1 S2]. (lazymatch goal with |- ?G => let G' := eval unfold dl_frame in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma dl_frame_grows : mem_grows M (dl_frame M sp ra s0v s1v s2v s3v).
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold dl_frame in G in change_no_check G' end). do 5 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

  Lemma dl_lock :
    exists r, msteps ASEGS (mkst regs (0x8f214 : word) M rom) (mkst r ra (dl_mem M sp ra s0v s1v s2v s3v b v) rom)
      /\ getr r 10 = Z_to_bv 64 v /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19]) regs r.
  Proof using Hstk SOKb Rb Hv Hb Hret Hsp H19 H18 H9 H8 H10 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range b) as Hbr. destruct Hsp as [S1 S2]. destruct Hb as (B1 & B2 & B3).
    set (MF := dl_frame M sp ra s0v s1v s2v s3v).
    assert (RbF : rdn ASEGS MF b 4 = Some (LE4 v)).
    { rewrite <- Rb. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply dl_frame_outside. lia. }
    assert (Vlw : v_lw (Z_to_bv 64 v) = Z_to_bv 64 v).
    { apply SumsLib.StartupAux.v_lw_small. unorm. lia. }
    assert (SLF : forall (k : Z) (vv : word), In (k, vv) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v)]%Z ->
              rdn ASEGS (dl_mem M sp ra s0v s1v s2v s3v b v) (at_ sp k) 8 = Some (LE8 vv)).
    { intros k vv Hin.
      assert (K : (-40 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      (lazymatch goal with |- ?G => let G' := eval unfold dl_mem in G in change_no_check G' end). rewrite rdn_wbytes_out; [ | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia
                                              | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]
                                              | rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia].
      (lazymatch goal with |- ?G => let G' := eval unfold dl_frame in G in change_no_check G' end). cbn [In] in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    wd_eexists. split.
    - an F_8f20c D_8f20c.                              (* [comment removed for export] *)
      fsd F_8f210 D_8f210 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8f214 D_8f214 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_8f218 D_8f218 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_8f21c D_8f21c (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_8f220 D_8f220 (at_ sp (-40)).              (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _) _ _) with MF.
      an F_8f224 D_8f224.                              (* [comment removed for export] *)
      an F_8f228 D_8f228.                              (* [comment removed for export] *)
      an F_8f22c D_8f22c.                              (* [comment removed for export] *)
      an F_8f230 D_8f230.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 v) (v := Z_to_bv 64 v);
          [exact F_8f234 | reflexivity | exact D_8f234 | gres; rwH; imm_norm; rewrite ?at_addi, ?v_addi_0; exact RbF
          | apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      rewrite Vlw.
      ab_tk F_8f238 D_8f238 ltac:(condzs).             (* [comment removed for export] *)
      an F_8f24c D_8f24c.                              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (cas_w_run ASEGS _ (0x8f258 : word) (0x8f25c : word) (0x8f260 : word) (0x8f264 : word) (0x8f268 : word) MF rom
                  _ _ _ _ _ _ _ _ 13 8 14 12 13 10 BC_NE _ _ (LE4 v) (Z_to_bv 64 v)
                  F_8f250 eq_refl D_8f250 F_8f254 eq_refl D_8f254 F_8f258 eq_refl D_8f258 F_8f25c eq_refl D_8f25c);
          try reflexivity.
        all: lazymatch goal with
             | |- v_addi _ _ = _ => apply bv_eq; vm_compute; reflexivity
             | |- _ <> _ => intros X; discriminate X
             | |- (_ mod 4 = 0)%Z => gres; rwH; exact B1
             | |- rdn _ _ _ _ = _ => gres; rwH; exact RbF
             | |- store_ok _ _ _ _ = true => gres; rwH; eapply store_ok_mono; [apply dl_frame_grows | exact SOKb]
             | |- branch_taken _ _ _ = false => (lazymatch goal with |- ?G => let G' := eval cbn [branch_taken] in G in change_no_check G' end); gres; rewrite Vlw, bv_eqb_refl; reflexivity
             | |- _ => apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia
             end. }
      gres. rwH. rewrite ?Vlw.
      ab_tk F_8f260 D_8f260 ltac:(rewrite ?Vlw; (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
      change (wbytes MF b _) with (dl_mem M sp ra s0v s1v s2v s3v b v).
      cld8 F_8f280 D_8f280 ra (SLF (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).      (* [comment removed for export] *)
      cld8 F_8f284 D_8f284 s0v (SLF (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).   (* [comment removed for export] *)
      cld8 F_8f288 D_8f288 s1v (SLF (-24)%Z s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).   (* [comment removed for export] *)
      cld8 F_8f28c D_8f28c s2v (SLF (-32)%Z s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).   (* [comment removed for export] *)
      cld8 F_8f290 D_8f290 s3v (SLF (-40)%Z s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).   (* [comment removed for export] *)
      an F_8f294 D_8f294.                              (* [comment removed for export] *)
      aret F_8f298 D_8f298 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End LOCK.
End FPGen.
End AsDepotLock.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotIns.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit AsDepotLock.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Ltac di_in_l := (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
Ltac di_incl := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv beta in Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [di_in_l|]); destruct Hr.

Section FPGen.
Context {fx : FPState}.

Definition di_mem (M : word -> option byte) (nd b hd idw : word) : word -> option byte :=
  wbytes (wbytes M (at_ nd 8) (word_to_le_bytes 4 hd)) b (word_to_le_bytes 4 idw).

Section POST.
  Variables (M rom : word -> option byte) (sp ra nd b hd idw : word) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-112).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0.            (* [comment removed for export] *)
  Hypothesis H9 : getr regs 9 = nd.                       (* [comment removed for export] *)
  Hypothesis H18 : getr regs 18 = b.                      (* [comment removed for export] *)
  Hypothesis H21 : getr regs 21 = hd.                     (* [comment removed for export] *)
  Hypothesis H23 : getr regs 23 = idw.                    (* [comment removed for export] *)
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hnd : ((U nd + 12 <= U sp - 112 \/ U sp <= U nd) /\ U nd + 16 < 2 ^ 64)%Z.
  Hypothesis Hb : ((U b + 4 <= U sp - 112 \/ U sp <= U b) /\ U b + 4 < 2 ^ 64)%Z.
  Hypothesis SOKn : store_ok ASEGS M (at_ nd 8) 4 = true.
  Hypothesis SOKb : store_ok ASEGS M b 4 = true.
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v); (-72, s7v); (-80, s8v); (-88, s9v)]%Z ->
    rdn ASEGS M (at_ sp k) 8 = Some (LE8 v).

  Lemma di_mem_outside : forall x : word, (U x < U nd + 8 \/ U nd + 12 <= U x)%Z -> (U x < U b \/ U b + 4 <= U x)%Z -> di_mem M nd b hd idw x = M x.
  Proof using Hb Hnd sp.
    intros x X1 X2. pose proof (u64_range nd). pose proof (u64_range b). destruct Hnd as [_ N2]. destruct Hb as [_ B2]. (lazymatch goal with |- ?G => let G' := eval unfold di_mem in G in change_no_check G' end).
    rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
  Qed.


  Lemma di_post :
    exists r, msteps ASEGS (mkst regs (0x8eca8 : word) M rom) (mkst r ra (di_mem M nd b hd idw) rom)
      /\ getr r 10 = idw /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 18; 19; 20; 21; 22; 23; 24; 25]) regs r.
  Proof using SL SOKb SOKn Hb Hnd Hret Hsp H23 H21 H18 H9 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range nd) as Hndr. pose proof (u64_range b) as Hbr.
    destruct Hsp as [S1 S2]. destruct Hnd as [N1 N2]. destruct Hb as [B1 B2].
    assert (SLF : forall (k : Z) (v : word),
              In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v); (-72, s7v); (-80, s8v); (-88, s9v)]%Z ->
              rdn ASEGS (di_mem M nd b hd idw) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (K : (-88 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite <- (SL k v Hin). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply di_mem_outside; lia. }
    wd_eexists. split.
    - fsw F_8eca0 D_8eca0 (at_ nd 8).                  (* [comment removed for export] *)
      afence F_8eca4 D_8eca4.                          (* [comment removed for export] *)
      an F_8eca8 D_8eca8.                              (* [comment removed for export] *)
      fsw F_8ecac D_8ecac b.                           (* [comment removed for export] *)
      change (wbytes (wbytes M _ _) _ _) with (di_mem M nd b hd idw).
      ab_tk F_8ecb0 D_8ecb0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_8ecbc D_8ecbc ra (SLF (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ecc0 D_8ecc0 s0v (SLF (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ecc4 D_8ecc4 s1v (SLF (-24)%Z s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ecc8 D_8ecc8 s2v (SLF (-32)%Z s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8eccc D_8eccc s3v (SLF (-40)%Z s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ecd0 D_8ecd0 s4v (SLF (-48)%Z s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ecd4 D_8ecd4 s5v (SLF (-56)%Z s5v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ecd8 D_8ecd8 s6v (SLF (-64)%Z s6v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ecdc D_8ecdc s7v (SLF (-72)%Z s7v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ece0 D_8ece0 s8v (SLF (-80)%Z s8v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8ece4 D_8ece4 s9v (SLF (-88)%Z s9v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      an F_8ece8 D_8ece8.                              (* [comment removed for export] *)
      aret F_8ecec D_8ecec ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. ra_solve.
  Qed.
End POST.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section PRE2.
  Variables (M rom : word -> option byte) (sp D hsh blk : word) (hd NIDS : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation idz := (NIDS + 1)%Z.
  #[local] Abbreviation cntA := (at_ D 0x400000).
  Definition di_node (blk : word) (NIDS : Z) : word := Z_to_bv 64 (U blk + 16 * ((NIDS + 1) mod 2 ^ 16)).
  Hypothesis H2 : getr regs 2 = at_ sp (-112).
  Hypothesis H9 : getr regs 9 = D.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 hd.
  Hypothesis H19 : getr regs 19 = hsh.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 65535.
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 (U D + 4194320).
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 hd.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis HD : (U D mod 4 = 0 /\ U D + 0x500000 <= 2 ^ 32)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis Hblk : (U blk <> 0 /\ U blk + 2 ^ 20 < 2 ^ 64)%Z.
  Hypothesis Rcnt : rdn ASEGS M cntA 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 NIDS)).
  Hypothesis SOKc : store_ok ASEGS M cntA 4 = true.
  Hypothesis Rmap : rdn ASEGS M (Z_to_bv 64 (U D + 0x400010 + 8 * (idz / 2 ^ 16))) 8 = Some (LE8 blk).

  Definition di_cmem (M : word -> option byte) (D : word) (NIDS : Z) : word -> option byte :=
    wbytes M (at_ D 0x400000) (word_to_le_bytes 4 (v_add (Z_to_bv 64 NIDS) (Z_to_bv 64 1))).

  Lemma di_pre2 :
    exists r, msteps ASEGS (mkst regs (0x8ec20 : word) M rom) (mkst r (0x8e798 : word) (di_cmem M D NIDS) rom)
      /\ getr r 1 = (0x8eca8 : word) /\ getr r 2 = at_ sp (-112)
      /\ getr r 10 = di_node blk NIDS /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = at_ sp (-104) /\ getr r 13 = hsh
      /\ getr r 9 = di_node blk NIDS /\ getr r 21 = Z_to_bv 64 hd /\ getr r 23 = Z_to_bv 64 idz
      /\ regs_agree (fun i : reg => In i [1; 9; 10; 11; 12; 13; 21; 23]) regs r.
  Proof using Rmap SOKc Rcnt Hblk Hn HD Hsp H25 H24 H22 H19 H10 H9 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range D) as HDr. pose proof (u64_range blk) as Hbr.
    destruct Hsp as [S1 S2]. destruct HD as [D4 D32]. destruct Hblk as [BK0 BK1]. destruct Hn as [N0 N1].
    assert (UcA : U cntA = (U D + 0x400000)%Z) by (rewrite at_u by lia; reflexivity).
    assert (Vn : v_lw (Z_to_bv 64 NIDS) = Z_to_bv 64 NIDS) by (apply SumsLib.StartupAux.v_lw_small; wd_ulia).
    assert (M16 : (0 <= idz mod 2 ^ 16 < 2 ^ 16)%Z) by (apply Z.mod_pos_bound; lia).
    assert (I16 : (0 <= idz / 2 ^ 16 < 2 ^ 15)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (RmapC : rdn ASEGS (di_cmem M D NIDS) (Z_to_bv 64 (U D + 4194320 + 8 * (idz / 2 ^ 16))) 8 = Some (LE8 blk)).
    { (lazymatch goal with |- ?G => let G' := eval unfold di_cmem in G in change_no_check G' end). rewrite rdn_wbytes_out; [exact Rmap | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia ]. }
    wd_eexists. split.
    - an F_8ec18 D_8ec18.                              (* [comment removed for export] *)
      ab_tk F_8ec1c D_8ec1c ltac:((lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); gres; rwH; rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
      an F_8ec48 D_8ec48.                              (* [comment removed for export] *)
      av F_8ec4c D_8ec4c (at_ D 0x400000) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      an F_8ec50 D_8ec50.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 NIDS)) (v := Z_to_bv 64 NIDS);
          [exact F_8ec54 | reflexivity | exact D_8ec54
          | gres; rwH; rewrite UcA, Z.add_mod, D4 by lia; reflexivity
          | gres; rwH; exact Rcnt
          | apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia
          | gres; rwH; exact SOKc]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. rewrite ?Vn. change (wbytes M cntA _) with (di_cmem M D NIDS).
      av F_8ec58 D_8ec58 (Z_to_bv 64 idz) ltac:(apply bv_eq; rewrite v_addiw_small by (wd_ulia); wd_ulia).   (* [comment removed for export] *)
      av F_8ec5c D_8ec5c (Z_to_bv 64 (idz * 2 ^ 32)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; unorm; reflexivity).   (* [comment removed for export] *)
      av F_8ec60 D_8ec60 (Z_to_bv 64 idz) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite Z.div_mul by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft F_8ec64 D_8ec64 ltac:(condzs).             (* [comment removed for export] *)
      an F_8ec68 D_8ec68.                              (* [comment removed for export] *)
      av F_8ec6c D_8ec6c (Z_to_bv 64 (idz / 2 ^ 16)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (NIDS + 1)) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8ec70 D_8ec70 (Z_to_bv 64 (8 * (idz / 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv ((NIDS + 1) / 2 ^ 16)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8ec74 D_8ec74 (Z_to_bv 64 (U D + 4194320 + 8 * (idz / 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      cld8 F_8ec78 D_8ec78 blk RmapC.                  (* [comment removed for export] *)
      ab_ft F_8ec7c D_8ec7c ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; unorm; exact BK0).   (* [comment removed for export] *)
      an F_8ec80 D_8ec80. rewrite (v_and_bw16 idz (Z_to_bv 64 idz)) by (lia || (unorm; reflexivity)).   (* [comment removed for export] *)
      av F_8ec84 D_8ec84 (Z_to_bv 64 (16 * (idz mod 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv ((NIDS + 1) mod 2 ^ 16)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8ec88 D_8ec88 (di_node blk NIDS) ltac:((lazymatch goal with |- ?G => let G' := eval unfold di_node, v_add in G in change_no_check G' end); rewrite (u_Z2bv (16 * ((NIDS + 1) mod 2 ^ 16))) by lia; reflexivity).   (* [comment removed for export] *)
      an F_8ec8c D_8ec8c.                              (* [comment removed for export] *)
      an F_8ec90 D_8ec90.                              (* [comment removed for export] *)
      an F_8ec94 D_8ec94.                              (* [comment removed for export] *)
      an F_8ec98 D_8ec98.                              (* [comment removed for export] *)
      an F_8ec9c D_8ec9c.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; reflexivity).
  Qed.
End PRE2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ns_m1 (M : word -> option byte) (sp ra s0v nd hsh : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)) nd (LE8 hsh)) (at_ sp (-24)) (LE8 (Z_to_bv 64 0)).

Section NSPRE.
  Variables (M rom : word -> option byte) (sp ra s0v nd args hsh : word).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H10 : getr regs 10 = nd.
  Hypothesis H12 : getr regs 12 = args.
  Hypothesis H13 : getr regs 13 = hsh.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hnd : ((U nd + 8 <= U sp - 32 \/ U sp <= U nd) /\ U nd + 16 < 2 ^ 64)%Z.
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-32)) 32 = true.
  Hypothesis SOKn : store_ok ASEGS M nd 8 = true.

  Lemma ns_pre :
    exists r, msteps ASEGS (mkst regs (0x8e798 : word) M rom) (mkst r (0x8c484 : word) (ns_m1 M sp ra s0v nd hsh) rom)
      /\ getr r 1 = (0x8e7c4 : word) /\ getr r 2 = at_ sp (-32) /\ getr r 8 = nd
      /\ getr r 10 = Z_to_bv 64 0x1d9448 /\ getr r 11 = args /\ getr r 12 = at_ sp (-24)
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 10; 11; 12]) regs r.
  Proof using SOKn Hstk Hnd Hsp H13 H12 H10 H8 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range nd) as Hndr. destruct Hsp as [S1 S2]. destruct Hnd as [N1 N2].
    wd_eexists. split.
    - an F_8e790 D_8e790.                              (* [comment removed for export] *)
      fsd F_8e794 D_8e794 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8e798 D_8e798 (at_ sp (-16)).              (* [comment removed for export] *)
      an F_8e79c D_8e79c.                              (* [comment removed for export] *)
      an F_8e7a0 D_8e7a0.                              (* [comment removed for export] *)
      fsd F_8e7a4 D_8e7a4 nd.                          (* [comment removed for export] *)
      fsd F_8e7a8 D_8e7a8 (at_ sp (-24)).              (* [comment removed for export] *)
      an F_8e7ac D_8e7ac.                              (* [comment removed for export] *)
      an F_8e7b0 D_8e7b0.                              (* [comment removed for export] *)
      an F_8e7b4 D_8e7b4.                              (* [comment removed for export] *)
      an F_8e7b8 D_8e7b8.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; vm_compute; reflexivity).
  Qed.
End NSPRE.

Section NSPOST.
  Variables (MS rom : word -> option byte) (sp ra s0v nd sid : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-32).
  Hypothesis H8 : getr regs 8 = nd.
  Hypothesis H10 : getr regs 10 = sid.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hnd : ((U nd + 16 <= U sp - 32 \/ U sp <= U nd) /\ U nd + 16 < 2 ^ 64)%Z.
  Hypothesis SOKs : store_ok ASEGS MS (at_ nd 12) 4 = true.
  Hypothesis Rpack : rdn ASEGS MS (at_ sp (-24)) 8 = Some (LE8 (Z_to_bv 64 0)).          (* [comment removed for export] *)
  Hypothesis Rra : rdn ASEGS MS (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis Rs0 : rdn ASEGS MS (at_ sp (-16)) 8 = Some (LE8 s0v).

  Definition ns_m2 (MS : word -> option byte) (nd sid : word) : word -> option byte := wbytes MS (at_ nd 12) (word_to_le_bytes 4 sid).

  Lemma ns_post :
    exists r, msteps ASEGS (mkst regs (0x8e7c4 : word) MS rom) (mkst r ra (ns_m2 MS nd sid) rom)
      /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 11]) regs r.
  Proof using Rs0 Rra Rpack SOKs Hnd Hret Hsp H10 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range nd) as Hndr. destruct Hsp as [S1 S2]. destruct Hnd as [N1 N2].
    assert (OUT : forall (k : Z) (v : word), (-24 <= k <= -8)%Z -> rdn ASEGS MS (at_ sp k) 8 = Some (LE8 v) -> rdn ASEGS (ns_m2 MS nd sid) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v K Hr. (lazymatch goal with |- ?G => let G' := eval unfold ns_m2 in G in change_no_check G' end). rewrite rdn_wbytes_out; [exact Hr | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia. }
    wd_eexists. split.
    - cld8 F_8e7bc D_8e7bc (Z_to_bv 64 0) Rpack.       (* [comment removed for export] *)
      fsw F_8e7c0 D_8e7c0 (at_ nd 12).                 (* [comment removed for export] *)
      change (wbytes MS _ _) with (ns_m2 MS nd sid).
      ab_ft F_8e7c4 D_8e7c4 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_8e7c8 D_8e7c8 ra (OUT (-8)%Z ra ltac:(lia) Rra).      (* [comment removed for export] *)
      cld8 F_8e7cc D_8e7cc s0v (OUT (-16)%Z s0v ltac:(lia) Rs0).   (* [comment removed for export] *)
      an F_8e7d0 D_8e7d0.                              (* [comment removed for export] *)
      aret F_8e7d4 D_8e7d4 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End NSPOST.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section MISSPRE.
  Variables (M rom : word -> option byte) (sp D hsh blk : word) (hd NIDS BIX : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation spP := (at_ sp (-112)).
  #[local] Abbreviation b := (Z_to_bv 64 (U D + 4 * BIX)).
  #[local] Abbreviation ML := (dl_mem M spP (0x8ec20 : word) (Z_to_bv 64 0) D b hsh b hd).
  Hypothesis H2 : getr regs 2 = spP.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0.
  Hypothesis H9 : getr regs 9 = D.
  Hypothesis H18 : getr regs 18 = b.
  Hypothesis H19 : getr regs 19 = hsh.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 65535.
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 (U D + 4194320).
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 hd.
  Hypothesis Hsp : (2 ^ 32 + 160 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis HD : (U D mod 4 = 0 /\ U D + 0x500000 <= 2 ^ 32)%Z.
  Hypothesis HBIX : (0 <= BIX < 2 ^ 20)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis Hblk : (U blk <> 0 /\ U blk + 2 ^ 20 < 2 ^ 64)%Z.
  Hypothesis Rb : rdn ASEGS M b 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 hd)).
  Hypothesis SOKb : store_ok ASEGS M b 4 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ spP (-48)) 48 = true.
  Hypothesis Rcnt : rdn ASEGS M (at_ D 0x400000) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 NIDS)).
  Hypothesis SOKc : store_ok ASEGS M (at_ D 0x400000) 4 = true.
  Hypothesis Rmap : rdn ASEGS M (Z_to_bv 64 (U D + 0x400010 + 8 * ((NIDS + 1) / 2 ^ 16))) 8 = Some (LE8 blk).

  Lemma di_miss_pre :
    exists r, msteps ASEGS (mkst regs (0x8ec18 : word) M rom) (mkst r (0x8e798 : word) (di_cmem ML D NIDS) rom)
      /\ getr r 1 = (0x8eca8 : word) /\ getr r 2 = spP
      /\ getr r 10 = di_node blk NIDS /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = at_ sp (-104) /\ getr r 13 = hsh
      /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = di_node blk NIDS /\ getr r 18 = b /\ getr r 21 = Z_to_bv 64 hd /\ getr r 23 = Z_to_bv 64 (NIDS + 1)
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19; 21; 23]) regs r.
  Proof using Rmap SOKc Rcnt Hstk SOKb Rb Hblk Hn Hhd HBIX HD Hsp H25 H24 H22 H19 H18 H9 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range D) as HDr. destruct Hsp as [S1 S2]. destruct HD as [D4 D32].
    assert (UspP : U spP = (U sp - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Ub : U b = (U D + 4 * BIX)%Z) by (rewrite u_Z2bv by lia; reflexivity).
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps ASEGS (mkst regs (0x8ec18 : word) M rom) (mkst r1 (0x8f214 : word) M rom)
                   /\ getr r1 1 = (0x8ec20 : word) /\ getr r1 10 = b /\ regs_agree (fun i : reg => In i [1; 10]) regs r1).
    { wd_eexists. split.
      - an F_8ec10 D_8ec10.                            (* [comment removed for export] *)
        an F_8ec14 D_8ec14.                            (* [comment removed for export] *)
        wd_refl.
      - post. all: try ra_solve. all: try (apply bv_eq; reflexivity). }
    destruct W1 as (r1 & RUN1 & A1 & A10 & AG1).
    assert (NI : forall i : reg, In i [2; 8; 9; 18; 19; 22; 24; 25] -> ~ In i [1; 10]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (dl_lock M rom spP (0x8ec20 : word) b (Z_to_bv 64 0) D b hsh hd r1 A1
                ltac:(rewrite (AG1 2%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H2) A10
                ltac:(rewrite (AG1 8%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H8)
                ltac:(rewrite (AG1 9%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H9)
                ltac:(rewrite (AG1 18%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H18)
                ltac:(rewrite (AG1 19%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H19)
                ltac:(rewrite UspP; lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Ub, UspP; split; [rewrite Z.add_mod, D4, Z.mul_comm, Z_mod_mult by lia; reflexivity | lia]) Hhd Rb SOKb Hstk)
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & AG2).
    assert (NI2 : forall i : reg, In i [22; 24; 25] -> ~ In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    assert (OUTL : forall x : word, (U sp - 112 <= U x \/ U x < U sp - 160)%Z -> U x <> U b -> (U x < U b \/ U b + 4 <= U x)%Z -> ML x = M x).
    { intros x X1 _ X3. (lazymatch goal with |- ?G => let G' := eval unfold dl_mem in G in change_no_check G' end). rewrite wbytes_outside; [| rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia
                                                                  | rewrite length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia].
      apply (dl_frame_outside M spP (0x8ec20 : word) b (Z_to_bv 64 0) D b hsh ltac:(rewrite UspP; lia)). rewrite UspP. lia. }
    assert (RDL : forall (a : word) (n : nat) bs, (U a + Z.of_nat n <= 2 ^ 32)%Z -> (U D + 0x400000 <= U a)%Z -> rdn ASEGS M a n = Some bs -> rdn ASEGS ML a n = Some bs).
    { intros a n bs A1' A2' Hr. rewrite <- Hr. apply rdn_ext; [lia|]. intros x Hx. apply OUTL; rewrite ?Ub; lia. }
    destruct (di_pre2 ML rom sp D hsh blk hd NIDS r2 B2 B9 B10 B19
                ltac:(rewrite (AG2 22%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG1 22%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H22)
                ltac:(rewrite (AG2 24%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG1 24%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H24)
                ltac:(rewrite (AG2 25%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG1 25%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H25)
                ltac:(lia) (conj D4 D32) Hn Hblk)
      as (r3 & RUN3 & C1 & C2 & C10 & C11 & C12 & C13 & C9 & C21 & C23 & AG3).
    { apply RDL; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Rcnt]. }
    { eapply store_ok_mono; [| exact SOKc]. (lazymatch goal with |- ?G => let G' := eval unfold dl_mem in G in change_no_check G' end). eapply mem_grows_trans; [apply dl_frame_grows | apply wbytes_grows]. }
    { assert (I16 : (0 <= (NIDS + 1) / 2 ^ 16 < 2 ^ 15)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
      apply RDL; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact Rmap]. }
    exists r3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    assert (NI3 : forall i : reg, In i [8; 18] -> ~ In i [1; 9; 10; 11; 12; 13; 21; 23]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    repeat (split; [assumption|]).
    split; [rewrite (AG3 8%bv) by (apply NI3; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B8|].
    split; [exact C9|]. split; [rewrite (AG3 18%bv) by (apply NI3; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B18|]. split; [exact C21|]. split; [exact C23|].
    apply (regs_agree_trans _ regs r1); [eapply regs_agree_mono; [|exact AG1]; di_incl|].
    apply (regs_agree_trans _ r1 r2); [eapply regs_agree_mono; [|exact AG2]; di_incl|].
    eapply regs_agree_mono; [|exact AG3]. di_incl.
  Qed.
End MISSPRE.
End FPGen.
End AsDepotIns.
Module AsDepotIns2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit AsDepotLock AsDepotIns.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Section NULL.
  Variables (M rom : word -> option byte) (sp D hsh : word) (hd NIDS : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation idz := (NIDS + 1)%Z.
  #[local] Abbreviation cntA := (at_ D 0x400000).
  Hypothesis H2 : getr regs 2 = at_ sp (-112).
  Hypothesis H9 : getr regs 9 = D.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 hd.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 (U D + 4194312).
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 (U D + 4194320).
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 hd.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis HD : (U D mod 4 = 0 /\ U D + 0x500000 <= 2 ^ 32)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis Rcnt : rdn ASEGS M cntA 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 NIDS)).
  Hypothesis SOKc : store_ok ASEGS M cntA 4 = true.
  Hypothesis Rmap : rdn ASEGS M (Z_to_bv 64 (U D + 0x400010 + 8 * (idz / 2 ^ 16))) 8 = Some (LE8 (Z_to_bv 64 0)).

  Lemma di_pre2_null :
    exists r, msteps ASEGS (mkst regs (0x8ec20 : word) M rom) (mkst r (0x8f2a4 : word) (di_cmem M D NIDS) rom)
      /\ getr r 1 = (0x8ed20 : word) /\ getr r 2 = at_ sp (-112)
      /\ getr r 10 = Z_to_bv 64 (U D + 4194312) /\ getr r 11 = Z_to_bv 64 (idz / 2 ^ 16)
      /\ getr r 9 = Z_to_bv 64 idz /\ getr r 21 = Z_to_bv 64 hd /\ getr r 23 = Z_to_bv 64 idz
      /\ regs_agree (fun i : reg => In i [1; 9; 10; 11; 21; 23]) regs r.
  Proof using Rmap SOKc Rcnt Hn HD Hsp H25 H24 H20 H10 H9 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range D) as HDr.
    destruct Hsp as [S1 S2]. destruct HD as [D4 D32]. destruct Hn as [N0 N1].
    assert (UcA : U cntA = (U D + 0x400000)%Z) by (rewrite at_u by lia; reflexivity).
    assert (Vn : v_lw (Z_to_bv 64 NIDS) = Z_to_bv 64 NIDS) by (apply SumsLib.StartupAux.v_lw_small; wd_ulia).
    assert (I16 : (0 <= idz / 2 ^ 16 < 2 ^ 15)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (RmapC : rdn ASEGS (di_cmem M D NIDS) (Z_to_bv 64 (U D + 4194320 + 8 * (idz / 2 ^ 16))) 8 = Some (LE8 (Z_to_bv 64 0))).
    { (lazymatch goal with |- ?G => let G' := eval unfold di_cmem in G in change_no_check G' end). rewrite rdn_wbytes_out; [exact Rmap | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia ]. }
    wd_eexists. split.
    - an F_8ec18 D_8ec18.                              (* [comment removed for export] *)
      ab_tk F_8ec1c D_8ec1c ltac:((lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); gres; rwH; rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
      an F_8ec48 D_8ec48.                              (* [comment removed for export] *)
      av F_8ec4c D_8ec4c (at_ D 0x400000) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      an F_8ec50 D_8ec50.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_w with (bs := word_to_le_bytes 4 (Z_to_bv 64 NIDS)) (v := Z_to_bv 64 NIDS);
          [exact F_8ec54 | reflexivity | exact D_8ec54
          | gres; rwH; rewrite UcA, Z.add_mod, D4 by lia; reflexivity
          | gres; rwH; exact Rcnt
          | apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia
          | gres; rwH; exact SOKc]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. rewrite ?Vn. change (wbytes M cntA _) with (di_cmem M D NIDS).
      av F_8ec58 D_8ec58 (Z_to_bv 64 idz) ltac:(apply bv_eq; rewrite v_addiw_small by (wd_ulia); wd_ulia).   (* [comment removed for export] *)
      av F_8ec5c D_8ec5c (Z_to_bv 64 (idz * 2 ^ 32)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; unorm; reflexivity).   (* [comment removed for export] *)
      av F_8ec60 D_8ec60 (Z_to_bv 64 idz) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite Z.div_mul by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft F_8ec64 D_8ec64 ltac:(condzs).             (* [comment removed for export] *)
      an F_8ec68 D_8ec68.                              (* [comment removed for export] *)
      av F_8ec6c D_8ec6c (Z_to_bv 64 (idz / 2 ^ 16)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (NIDS + 1)) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8ec70 D_8ec70 (Z_to_bv 64 (8 * (idz / 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv ((NIDS + 1) / 2 ^ 16)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8ec74 D_8ec74 (Z_to_bv 64 (U D + 4194320 + 8 * (idz / 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); unorm; reflexivity).   (* [comment removed for export] *)
      cld8 F_8ec78 D_8ec78 (Z_to_bv 64 0) RmapC.       (* [comment removed for export] *)
      ab_tk F_8ec7c D_8ec7c ltac:(condz).              (* [comment removed for export] *)
      an F_8ed10 D_8ed10.                              (* [comment removed for export] *)
      an F_8ed14 D_8ed14.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; reflexivity).
  Qed.
End NULL.

Section CONT.
  Variables (MC rom : word -> option byte) (sp hsh blk : word) (NIDS : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation idz := (NIDS + 1)%Z.
  Hypothesis H2 : getr regs 2 = at_ sp (-112).
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 idz.
  Hypothesis H10 : getr regs 10 = blk.
  Hypothesis H19 : getr regs 19 = hsh.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 65535.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis Hblk : (U blk + 2 ^ 20 < 2 ^ 64)%Z.

  Lemma di_pre2_cont :
    exists r, msteps ASEGS (mkst regs (0x8ed20 : word) MC rom) (mkst r (0x8e798 : word) MC rom)
      /\ getr r 1 = (0x8eca8 : word) /\ getr r 2 = at_ sp (-112)
      /\ getr r 10 = di_node blk NIDS /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = at_ sp (-104) /\ getr r 13 = hsh
      /\ getr r 9 = di_node blk NIDS
      /\ regs_agree (fun i : reg => In i [1; 9; 10; 11; 12; 13]) regs r.
  Proof using Hn Hsp H22 H19 H10 H9 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range blk) as Hbr. destruct Hsp as [S1 S2]. destruct Hn as [N0 N1].
    assert (M16 : (0 <= idz mod 2 ^ 16 < 2 ^ 16)%Z) by (apply Z.mod_pos_bound; lia).
    wd_eexists. split.
    - an F_8ed18 D_8ed18.                              (* [comment removed for export] *)
      an F_8ec80 D_8ec80. rewrite (v_and_bw16 idz (Z_to_bv 64 idz)) by (lia || (unorm; reflexivity)).   (* [comment removed for export] *)
      av F_8ec84 D_8ec84 (Z_to_bv 64 (16 * (idz mod 2 ^ 16))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv ((NIDS + 1) mod 2 ^ 16)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8ec88 D_8ec88 (di_node blk NIDS) ltac:((lazymatch goal with |- ?G => let G' := eval unfold di_node, v_add in G in change_no_check G' end); rewrite (u_Z2bv (16 * ((NIDS + 1) mod 2 ^ 16))) by lia; reflexivity).   (* [comment removed for export] *)
      an F_8ec8c D_8ec8c.                              (* [comment removed for export] *)
      an F_8ec90 D_8ec90.                              (* [comment removed for export] *)
      an F_8ec94 D_8ec94.                              (* [comment removed for export] *)
      an F_8ec98 D_8ec98.                              (* [comment removed for export] *)
      an F_8ec9c D_8ec9c.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; reflexivity).
  Qed.
End CONT.
End FPGen.
End AsDepotIns2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotMap.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtFlush OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 AsDepotBlk.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.

Section FPGen.
Context {fx : FPState}.

Definition tl_slot (MU : word) (idx : Z) : word := Z_to_bv 64 (U MU + 8 + 8 * idx).
Definition tl_m1 (M : word -> option byte) (sp ra s0v s1v s2v MU : word) (b1 b2 b3 : byte) : word -> option byte :=
  wbytes (bi_frame M sp ra s0v s1v s2v) MU [Z_to_bv 8 1; b1; b2; b3].

Section TLPRE.
  Variables (M rom : word -> option byte) (sp ra s0v s1v s2v MU lkw : word) (b1 b2 b3 : byte) (idx PGP : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H10 : getr regs 10 = MU.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 idx.
  Hypothesis Hsp : (2 ^ 32 + 32 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis HMU : (U MU mod 8 = 0 /\ 0xff258 <= U MU /\ U MU + 8 + 8 * 2 ^ 15 <= 2 ^ 32)%Z.
  Hypothesis Hidx : (0 <= idx < 2 ^ 15)%Z.
  Hypothesis HPGP : (0 <= PGP /\ (PGP + 8 <= U MU \/ U MU + 4 <= PGP) /\ PGP + 8 <= 2 ^ 32)%Z.
  Hypothesis R_lock : rdn ASEGS M MU 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw.
  Hypothesis Rslot : rdn ASEGS M (tl_slot MU idx) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rgpg : rdn ASEGS M (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS M (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis SOKl : store_ok ASEGS M MU 4 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-32)) 32 = true.

  Lemma tl_pre :
    exists r, msteps ASEGS (mkst regs (0x8f2a4 : word) M rom) (mkst r (0x81e08 : word) (tl_m1 M sp ra s0v s1v s2v MU b1 b2 b3) rom)
      /\ getr r 1 = (0x8f348 : word) /\ getr r 2 = at_ sp (-32)
      /\ getr r 10 = Z_to_bv 64 1048576 /\ getr r 11 = Z_to_bv 64 0x21dae /\ getr r 12 = Z_to_bv 64 0
      /\ getr r 8 = MU /\ getr r 9 = Z_to_bv 64 (U MU + 8 * idx)
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 18; 10; 11; 12; 13; 14; 15]) regs r.
  Proof using Hstk SOKl Rpg Rgpg Rslot V_lock R_lock HPGP Hidx HMU Hsp H11 H10 H18 H9 H8 H2 H1 PGP lkw.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range MU) as HMr.
    destruct Hsp as [S1 S2]. destruct HMU as (M8 & MLO & M32). destruct HPGP as (PG0 & PGD & PG32).
    assert (AL : (U MU mod 4 = 0)%Z).
    { pose proof (Z.div_mod (U MU) 8 ltac:(lia)) as E. rewrite M8 in E. rewrite E.
      replace (8 * (U MU / 8) + 0)%Z with ((2 * (U MU / 8)) * 4)%Z by lia. apply Z_mod_mult. }
    assert (Uslot : U (tl_slot MU idx) = (U MU + 8 + 8 * idx)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    set (MF := bi_frame M sp ra s0v s1v s2v).
    assert (OUTF : forall x : word, (U x < U sp - 32 \/ U sp <= U x)%Z -> MF x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MF, bi_frame in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GRF : mem_grows M MF) by ((lazymatch goal with |- ?G => let G' := eval unfold MF, bi_frame in G in change_no_check G' end); do 4 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (R_lockF : rdn ASEGS MF MU 4 = Some [Z_to_bv 8 0; b1; b2; b3]).
    { rewrite <- R_lock. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply OUTF. lia. }
    set (ML := tl_m1 M sp ra s0v s1v s2v MU b1 b2 b3).
    assert (OUTL : forall x : word, (U x < U MU \/ U MU + 4 <= U x)%Z -> (U x < U sp - 32 \/ U sp <= U x)%Z -> ML x = M x).
    { intros x Hx Hx2. (lazymatch goal with |- ?G => let G' := eval unfold ML, tl_m1 in G in change_no_check G' end). rewrite wbytes_outside; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. apply OUTF. exact Hx2. }
    assert (RslotL : rdn ASEGS ML (tl_slot MU idx) 8 = Some (LE8 (Z_to_bv 64 0))).
    { rewrite <- Rslot. apply rdn_ext; [rewrite Uslot; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite Uslot in Hx. cbn in Hx. apply OUTL; lia. }
    assert (RgpgL : rdn ASEGS ML (Z_to_bv 64 0xff250) 8 = Some (LE8 (Z_to_bv 64 PGP))).
    { rewrite <- Rgpg. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUTL; lia. }
    assert (RpgL : rdn ASEGS ML (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096))).
    { rewrite <- Rpg. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUTL; lia. }
    wd_eexists. split.
    - an F_8f29c D_8f29c.                              (* [comment removed for export] *)
      fsd F_8f2a0 D_8f2a0 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8f2a4 D_8f2a4 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_8f2a8 D_8f2a8 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_8f2ac D_8f2ac (at_ sp (-32)).              (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _) with MF.
      an F_8f2b0 D_8f2b0.                              (* [comment removed for export] *)
      an F_8f2b4 D_8f2b4. rewrite (v_andi_m4_aligned MU AL).   (* [comment removed for export] *)
      an F_8f2b8 D_8f2b8.                              (* [comment removed for export] *)
      an F_8f2bc D_8f2bc.                              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (xchg_byte_run ASEGS _ (0x8f2c8 : word) (0x8f2cc : word) (0x8f2d0 : word) (0x8f2d4 : word)
                  (0x8f2d8 : word) (0x8f2dc : word) (0x8f2e0 : word) (0x8f2e4 : word) _ rom
                  _ _ _ _ _ _ _ _ _ _ _ 14 10 15 13 12 _ [Z_to_bv 8 0; b1; b2; b3] lkw 0%nat 1%Z
                  F_8f2c0 eq_refl D_8f2c0 F_8f2c4 eq_refl D_8f2c4 F_8f2c8 eq_refl D_8f2c8 F_8f2cc eq_refl D_8f2cc
                  F_8f2d0 eq_refl D_8f2d0 F_8f2d4 eq_refl D_8f2d4 F_8f2d8 eq_refl D_8f2d8).
        all: lazymatch goal with
             | |- v_addi _ _ = _ => first [reflexivity | apply bv_eq; vm_compute; reflexivity]
             | |- _ <> _ => first [regneq | intros X; discriminate X]
             | |- (_ mod 4 = 0)%Z => gres; rwH; exact AL
             | |- rdn _ _ _ _ = _ => gres; rwH; exact R_lockF
             | |- bytes_le_to_Z _ = _ => exact V_lock
             | |- store_ok _ _ _ _ = true => gres; rwH; eapply store_ok_mono; [exact GRF | exact SOKl]
             | |- (_ < _)%nat => lia
             | |- (_ <= _ < _)%Z => lia
             | |- U _ = _ => gres; rwH; unorm; reflexivity
             end. }
      gres. rwH. (lazymatch goal with |- ?G => let G' := eval cbn [firstn skipn app] in G in change_no_check G' end). change (wbytes MF MU _) with ML.
      av F_8f2dc D_8f2dc (Z_to_bv 64 0) ltac:(rewrite (lock_byte0 (Z_to_bv 8 0) b1 b2 b3 _ V_lock); unorm; reflexivity).   (* [comment removed for export] *)
      ab_ft F_8f2e0 D_8f2e0 ltac:(condz).              (* [comment removed for export] *)
      av F_8f2e4 D_8f2e4 (Z_to_bv 64 (8 * idx)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv idx) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8f2e8 D_8f2e8 (Z_to_bv 64 (U MU + 8 * idx)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (8 * idx)) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8f2ec D_8f2ec (Z_to_bv 64 0) RslotL.      (* [comment removed for export] *)
      afence F_8f2f0 D_8f2f0.                          (* [comment removed for export] *)
      ab_ft F_8f2f4 D_8f2f4 ltac:(condz).              (* [comment removed for export] *)
      an F_8f2f8 D_8f2f8.                              (* [comment removed for export] *)
      cld8 F_8f2fc D_8f2fc (Z_to_bv 64 PGP) RgpgL.     (* [comment removed for export] *)
      cld8 F_8f300 D_8f300 (Z_to_bv 64 4096) RpgL.     (* [comment removed for export] *)
      ab_tk F_8f304 D_8f304 ltac:(condz).              (* [comment removed for export] *)
      an F_8f310 D_8f310.                              (* [comment removed for export] *)
      an F_8f314 D_8f314.                              (* [comment removed for export] *)
      ab_ft F_8f318 D_8f318 ltac:(condz).              (* [comment removed for export] *)
      an F_8f31c D_8f31c.                              (* [comment removed for export] *)
      av F_8f320 D_8f320 (Z_to_bv 64 1048575) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av F_8f324 D_8f324 (Z_to_bv 64 1052671) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av F_8f328 D_8f328 (Z_to_bv 64 (2 ^ 64 - 4096)) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      av_and F_8f32c D_8f32c (Z_to_bv 64 1048576) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      an F_8f330 D_8f330.                              (* [comment removed for export] *)
      an F_8f334 D_8f334.                              (* [comment removed for export] *)
      an F_8f338 D_8f338.                              (* [comment removed for export] *)
      an F_8f33c D_8f33c.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; vm_compute; reflexivity).
  Qed.
End TLPRE.

Definition tl_m2 (MB : word -> option byte) (MU newblk : word) (idx : Z) : word -> option byte :=
  wbytes (wbytes MB (tl_slot MU idx) (LE8 newblk)) MU [Z_to_bv 8 0].

Section TLPOST.
  Variables (MB rom : word -> option byte) (sp ra s0v s1v s2v MU newblk : word) (idx : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-32).
  Hypothesis H8 : getr regs 8 = MU.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (U MU + 8 * idx).
  Hypothesis H10 : getr regs 10 = newblk.
  Hypothesis Hsp : (2 ^ 32 + 32 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HMU : (U MU + 8 + 8 * 2 ^ 15 <= 2 ^ 32)%Z.
  Hypothesis Hidx : (0 <= idx < 2 ^ 15)%Z.
  Hypothesis SOKs : store_ok ASEGS MB (tl_slot MU idx) 8 = true.
  Hypothesis SOKl : store_ok ASEGS MB MU 1 = true.
  Hypothesis SL : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)]%Z -> rdn ASEGS MB (at_ sp k) 8 = Some (LE8 v).

  Lemma tl_post :
    exists r, msteps ASEGS (mkst regs (0x8f348 : word) MB rom) (mkst r ra (tl_m2 MB MU newblk idx) rom)
      /\ getr r 10 = newblk /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 18]) regs r.
  Proof using SL SOKl SOKs Hidx HMU Hret Hsp H10 H9 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range MU) as HMr. destruct Hsp as [S1 S2].
    assert (Uslot : U (tl_slot MU idx) = (U MU + 8 + 8 * idx)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (SLF : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v)]%Z ->
              rdn ASEGS (tl_m2 MB MU newblk idx) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (K : (-32 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite <- (SL k v Hin). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. (lazymatch goal with |- ?G => let G' := eval unfold tl_m2 in G in change_no_check G' end).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uslot; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    wd_eexists. split.
    - afence F_8f340 D_8f340.                          (* [comment removed for export] *)
      fsd F_8f344 D_8f344 (tl_slot MU idx).            (* [comment removed for export] *)
      afence F_8f348 D_8f348.                          (* [comment removed for export] *)
      fsb F_8f34c D_8f34c MU (Z_to_bv 8 0).            (* [comment removed for export] *)
      change (wbytes (wbytes MB _ _) MU _) with (tl_m2 MB MU newblk idx).
      cld8 F_8f350 D_8f350 ra (SLF (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8f354 D_8f354 s0v (SLF (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8f358 D_8f358 s1v (SLF (-24)%Z s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8f35c D_8f35c s2v (SLF (-32)%Z s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      an F_8f360 D_8f360.                              (* [comment removed for export] *)
      aret F_8f364 D_8f364 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End TLPOST.
End FPGen.
End AsDepotMap.
Module AsDepotNotify.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit AsDepotLock AsDepotIns.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Ltac in_l := (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
Ltac incl_l := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv beta in Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [in_l|]); destruct Hr.

Section FPGen.
Context {fx : FPState}.

Definition nw_mem (M : word -> option byte) (sp ra s0v : word) : word -> option byte :=
  wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v).
Lemma nw_mem_outside : forall M sp ra s0v (x : word), (16 <= U sp)%Z -> (U x < U sp - 16 \/ U sp <= U x)%Z -> nw_mem M sp ra s0v x = M x.
Proof using.
  intros M sp ra s0v x Hsp Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold nw_mem in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
Qed.
Lemma nw_mem_grows : forall M sp ra s0v, mem_grows M (nw_mem M sp ra s0v).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold nw_mem in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

Section NW.
  Variables (M rom : word -> option byte) (sp ra s0v CF : word).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis Hsp : (2 ^ 32 + 16 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HCF : (U CF + 244 <= 2 ^ 32)%Z.
  Hypothesis Rcfp : rdn ASEGS M (Z_to_bv 64 0xff260) 8 = Some (LE8 CF).
  Hypothesis Rflag : rdn ASEGS M (at_ CF 240) 4 = Some (LE4 (Z_to_bv 64 0)).       (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-16)) 16 = true.

  Lemma nw_run :
    exists r, msteps ASEGS (mkst regs (0x8e7f4 : word) M rom) (mkst r ra (nw_mem M sp ra s0v) rom)
      /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 10]) regs r.
  Proof using Hstk Rflag Rcfp HCF Hret Hsp H8 H2 H1 CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range CF) as HCr. destruct Hsp as [S1 S2].
    set (MF := nw_mem M sp ra s0v).
    assert (RcfpF : rdn ASEGS MF (Z_to_bv 64 0xff260) 8 = Some (LE8 CF)).
    { rewrite <- Rcfp. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply nw_mem_outside; lia. }
    assert (RflagF : rdn ASEGS MF (at_ CF 240) 4 = Some (LE4 (Z_to_bv 64 0))).
    { rewrite <- Rflag. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply nw_mem_outside; lia. }
    assert (B40 : bytes_le_to_Z (LE4 (Z_to_bv 64 0)) = U (Z_to_bv 64 0)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (V0 : v_lw (Z_to_bv 64 0) = Z_to_bv 64 0) by (apply SumsLib.StartupAux.v_lw_small; wd_ulia).
    assert (SLF : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v)]%Z -> rdn ASEGS MF (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold MF, nw_mem in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    wd_eexists. split.
    - an F_8e7ec D_8e7ec.                              (* [comment removed for export] *)
      fsd F_8e7f0 D_8e7f0 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8e7f4 D_8e7f4 (at_ sp (-16)).              (* [comment removed for export] *)
      change (wbytes (wbytes M _ _) _ _) with MF.
      an F_8e7f8 D_8e7f8.                              (* [comment removed for export] *)
      cld8 F_8e7fc D_8e7fc CF RcfpF.                   (* [comment removed for export] *)
      clw F_8e800 D_8e800 (LE4 (Z_to_bv 64 0)) (Z_to_bv 64 0) RflagF B40.   (* [comment removed for export] *)
      rewrite ?V0.
      ab_tk F_8e804 D_8e804 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_8e86c D_8e86c ra (SLF (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).     (* [comment removed for export] *)
      cld8 F_8e870 D_8e870 s0v (SLF (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).  (* [comment removed for export] *)
      an F_8e874 D_8e874.                              (* [comment removed for export] *)
      aret F_8e878 D_8e878 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End NW.

(* [comment removed for export] *)
Section NSPOST1.
  Variables (MS rom : word -> option byte) (sp ra s0v nd sid CF : word) (pk : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-32).
  Hypothesis H8 : getr regs 8 = nd.
  Hypothesis H10 : getr regs 10 = sid.
  Hypothesis Hsp : (2 ^ 32 + 48 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hnd : ((U nd + 16 <= U sp - 48 \/ U sp <= U nd) /\ U nd + 16 < 2 ^ 64)%Z.
  Hypothesis Hpk : (1 <= pk < 2 ^ 32)%Z.
  Hypothesis HCF : (U CF + 244 <= 2 ^ 32)%Z.
  Hypothesis SOKs : store_ok ASEGS MS (at_ nd 12) 4 = true.
  Hypothesis Rpack : rdn ASEGS MS (at_ sp (-24)) 8 = Some (LE8 (Z_to_bv 64 pk)).
  Hypothesis Rra : rdn ASEGS MS (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis Rs0 : rdn ASEGS MS (at_ sp (-16)) 8 = Some (LE8 s0v).
  Hypothesis Rcfp : rdn ASEGS MS (Z_to_bv 64 0xff260) 8 = Some (LE8 CF).
  Hypothesis Rflag : rdn ASEGS MS (at_ CF 240) 4 = Some (LE4 (Z_to_bv 64 0)).
  Hypothesis HndI : (U nd + 16 <= U CF \/ U CF + 244 <= U nd)%Z.                   (* [comment removed for export] *)
  Hypothesis HndP : (U nd + 16 <= 0xff260 \/ 0xff268 <= U nd)%Z.
  Hypothesis Hstk : store_ok ASEGS MS (at_ sp (-48)) 16 = true.

  Definition ns_m3 (MS : word -> option byte) (sp nd sid : word) : word -> option byte :=
    nw_mem (ns_m2 MS nd sid) (at_ sp (-32)) (0x8e7e4 : word) nd.

  Lemma ns_post1 :
    exists r, msteps ASEGS (mkst regs (0x8e7c4 : word) MS rom) (mkst r ra (ns_m3 MS sp nd sid) rom)
      /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 10; 11]) regs r.
  Proof using Hstk HndP HndI Rflag Rcfp Rs0 Rra Rpack SOKs HCF Hpk Hnd Hret Hsp H10 H8 H2 pk CF.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range nd) as Hndr. pose proof (u64_range CF) as HCr.
    destruct Hsp as [S1 S2]. destruct Hnd as [N1 N2].
    set (M2 := ns_m2 MS nd sid).
    assert (OUT2 : forall x : word, (U x < U nd + 12 \/ U nd + 16 <= U x)%Z -> M2 x = MS x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M2, ns_m2 in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GR2 : mem_grows MS M2) by ((lazymatch goal with |- ?G => let G' := eval unfold M2, ns_m2 in G in change_no_check G' end); apply wbytes_grows).
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps ASEGS (mkst regs (0x8e7c4 : word) MS rom) (mkst r1 (0x8e7f4 : word) M2 rom)
                   /\ getr r1 1 = (0x8e7e4 : word) /\ getr r1 2 = at_ sp (-32) /\ getr r1 8 = nd
                   /\ regs_agree (fun i : reg => In i [1; 11]) regs r1).
    { wd_eexists. split.
      - cld8 F_8e7bc D_8e7bc (Z_to_bv 64 pk) Rpack.    (* [comment removed for export] *)
        fsw F_8e7c0 D_8e7c0 (at_ nd 12).               (* [comment removed for export] *)
        change (wbytes MS _ _) with M2.
        ab_tk F_8e7c4 D_8e7c4 ltac:(condz).            (* [comment removed for export] *)
        an F_8e7d8 D_8e7d8.                            (* [comment removed for export] *)
        wd_refl.
      - post. all: try ra_solve. all: try (apply bv_eq; reflexivity). }
    destruct W1 as (r1 & RUN1 & A1 & A2 & A8 & AG1).
    assert (UspB : U (at_ sp (-32)) = (U sp - 32)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    destruct (nw_run M2 rom (at_ sp (-32)) (0x8e7e4 : word) nd CF r1 A1 A2 A8
                ltac:(rewrite UspB; lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity) HCF)
      as (r2 & RUN2 & B2 & B1 & B8 & AG2).
    { rewrite <- Rcfp. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUT2. lia. }
    { rewrite <- Rflag. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT2. lia. }
    { eapply store_ok_mono; [exact GR2|]. rewrite at_at. exact Hstk. }
    fold (ns_m3 MS sp nd sid) in RUN2. set (M3 := ns_m3 MS sp nd sid) in *.
    assert (OUT3 : forall (k : Z) (v : word), (-16 <= k <= -8)%Z -> rdn ASEGS MS (at_ sp k) 8 = Some (LE8 v) -> rdn ASEGS M3 (at_ sp k) 8 = Some (LE8 v)).
    { intros k v K Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
      (lazymatch goal with |- ?G => let G' := eval unfold M3, ns_m3 in G in change_no_check G' end). rewrite nw_mem_outside by (rewrite ?UspB; lia). apply OUT2. lia. }
    assert (W3 : exists r3, msteps ASEGS (mkst r2 (0x8e7e4 : word) M3 rom) (mkst r3 ra M3 rom)
                   /\ getr r3 2 = sp /\ getr r3 1 = ra /\ getr r3 8 = s0v
                   /\ regs_agree (fun i : reg => In i [1; 2; 8]) r2 r3).
    { wd_eexists. split.
      - cld8 F_8e7dc D_8e7dc ra (OUT3 (-8)%Z ra ltac:(lia) Rra).      (* [comment removed for export] *)
        cld8 F_8e7e0 D_8e7e0 s0v (OUT3 (-16)%Z s0v ltac:(lia) Rs0).   (* [comment removed for export] *)
        an F_8e7e4 D_8e7e4.                            (* [comment removed for export] *)
        aret F_8e7e8 D_8e7e8 ra.                       (* [comment removed for export] *)
        wd_refl.
      - post. all: try ra_solve. }
    destruct W3 as (r3 & RUN3 & C2 & C1 & C8 & AG3).
    exists r3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    repeat (split; [assumption|]).
    apply (regs_agree_trans _ regs r1); [eapply regs_agree_mono; [|exact AG1]; incl_l|].
    apply (regs_agree_trans _ r1 r2); [eapply regs_agree_mono; [|exact AG2]; incl_l|].
    eapply regs_agree_mono; [|exact AG3]. incl_l.
  Qed.
End NSPOST1.
End FPGen.
End AsDepotNotify.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotRunT.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit AsDepotLock AsDepotIns AsDepotNotify OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

(* [comment removed for export] *)
Definition put_clob : list reg := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 28; 29; 30; 31].
Ltac in_l := (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
Ltac incl_pc := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv beta in Hr; cbn [In] in Hr; (lazymatch goal with |- ?G => let G' := eval unfold put_clob in G in change_no_check G' end); repeat (destruct Hr as [<-|Hr]; [in_l|]); destruct Hr.
Ltac ra_pc AG := eapply regs_agree_mono; [| exact AG]; incl_pc.

Section FPGen.
Context {fx : FPState}.

Section TAIL.
  Variables (MS rom : word -> option byte) (P ra nd b sid hd idw CF : word) (pk : Z) (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  Hypothesis H2 : getr regs 2 = at_ Q (-32).
  Hypothesis H8 : getr regs 8 = nd.
  Hypothesis H9 : getr regs 9 = nd.
  Hypothesis H10 : getr regs 10 = sid.
  Hypothesis H18 : getr regs 18 = b.
  Hypothesis H21 : getr regs 21 = hd.
  Hypothesis H23 : getr regs 23 = idw.
  Hypothesis HP : (2 ^ 32 + 160 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hnd : (U nd + 16 <= U P - 160 /\ (U nd + 16 <= U CF \/ U CF + 244 <= U nd) /\ (U nd + 16 <= 1045088 \/ 1045096 <= U nd))%Z.
  Hypothesis Hb : (U b + 4 <= U P - 160 /\ (U b + 4 <= U nd \/ U nd + 16 <= U b))%Z.
  Hypothesis Hpk : (0 <= pk < 2 ^ 32)%Z.
  Hypothesis HCF : (U CF + 244 <= 2 ^ 32)%Z.
  Hypothesis Rpack : rdn ASEGS MS (at_ Q (-24)) 8 = Some (LE8 (Z_to_bv 64 pk)).
  Hypothesis Rra : rdn ASEGS MS (at_ Q (-8)) 8 = Some (LE8 (0x8eca8 : word)).
  Hypothesis Rs0 : rdn ASEGS MS (at_ Q (-16)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis Rcfp : rdn ASEGS MS (Z_to_bv 64 1045088) 8 = Some (LE8 CF).
  Hypothesis Rflag : rdn ASEGS MS (at_ CF 240) 4 = Some (LE4 (Z_to_bv 64 0)).
  Hypothesis SOKs : store_ok ASEGS MS (at_ nd 12) 4 = true.
  Hypothesis SOKn : store_ok ASEGS MS (at_ nd 8) 4 = true.
  Hypothesis SOKb : store_ok ASEGS MS b 4 = true.
  Hypothesis Hstk : store_ok ASEGS MS (at_ Q (-48)) 16 = true.
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v); (-72, s7v); (-80, s8v); (-88, s9v)]%Z ->
    rdn ASEGS MS (at_ P k) 8 = Some (LE8 v).

  Definition tail_W (P nd b : word) : Z -> Prop := wun (ivl (U P - 160) 16) (wun (ivl (U nd + 8) 8) (ivl (U b) 4)).

  Lemma put_tail :
    exists r M', msteps ASEGS (mkst regs (0x8e7c4 : word) MS rom) (mkst r ra M' rom)
      /\ msum (tail_W P nd b) MS M'
      /\ getr r 10 = idw /\ getr r 2 = P /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
      /\ rdn ASEGS M' (at_ nd 8) 4 = Some (LE4 hd) /\ rdn ASEGS M' (at_ nd 12) 4 = Some (LE4 sid) /\ rdn ASEGS M' b 4 = Some (LE4 idw)
      /\ regs_agree (fun i : reg => In i put_clob) regs r.
  Proof using SL Hstk SOKb SOKn SOKs Rflag Rcfp Rs0 Rra Rpack HCF Hpk Hb Hnd Hret HP H23 H21 H18 H10 H9 H8 H2 pk CF.
    pose proof (u64_range P) as HPr. pose proof (u64_range nd) as Hndr. pose proof (u64_range b) as Hbr. pose proof (u64_range CF) as HCr.
    destruct HP as [P1 P2]. destruct Hnd as (N1 & N2 & N3). destruct Hb as [B1 B2].
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Un8 : U (at_ nd 8) = (U nd + 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Un12 : U (at_ nd 12) = (U nd + 12)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    (* [comment removed for export] *)
    assert (W1 : exists r1 M1, msteps ASEGS (mkst regs (0x8e7c4 : word) MS rom) (mkst r1 (0x8eca8 : word) M1 rom)
                   /\ msum (wun (ivl (U P - 160) 16) (ivl (U nd + 12) 4)) MS M1
                   /\ getr r1 2 = Q /\ getr r1 8 = Z_to_bv 64 0 /\ rdn ASEGS M1 (at_ nd 12) 4 = Some (LE4 sid)
                   /\ regs_agree (fun i : reg => In i [1; 2; 8; 10; 11]) regs r1).
    { destruct (Z.eq_dec pk 0) as [E0 | NE0].
      - subst pk.
        destruct (ns_post MS rom Q (0x8eca8 : word) (Z_to_bv 64 0) nd sid regs H2 H8 H10 ltac:(rewrite UQ; lia)
                    ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity) ltac:(rewrite UQ; lia) SOKs Rpack Rra Rs0)
          as (r1 & RUN1 & A2 & A1 & A8 & AG1).
        exists r1, (ns_m2 MS nd sid). split; [exact RUN1|]. split.
        { eapply msum_weaken; [| (lazymatch goal with |- ?G => let G' := eval unfold ns_m2 in G in change_no_check G' end); apply msum_wbytes; rewrite length_N_to_le_bytes, Un12; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
          intros z Hz. right. unfold ivl in *. rewrite length_N_to_le_bytes, Un12 in Hz. cbn in Hz. lia. }
        split; [exact A2|]. split; [exact A8|].
        split; [(lazymatch goal with |- ?G => let G' := eval unfold ns_m2 in G in change_no_check G' end); apply (rdn_wbytes_hit ASEGS (LE4 sid)); rewrite length_N_to_le_bytes, Un12; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
        eapply regs_agree_mono; [| exact AG1]. intros r Hr. cbn [In] in Hr |- *. clear - Hr. tauto.
      - destruct (ns_post1 MS rom Q (0x8eca8 : word) (Z_to_bv 64 0) nd sid CF pk regs H2 H8 H10 ltac:(rewrite UQ; lia)
                    ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity) ltac:(rewrite UQ; lia) ltac:(lia) HCF SOKs Rpack Rra Rs0 Rcfp Rflag N2 N3 Hstk)
          as (r1 & RUN1 & A2 & A1 & A8 & AG1).
        exists r1, (ns_m3 MS Q nd sid). split; [exact RUN1|].
        assert (UQ32 : U (at_ Q (-32)) = (U P - 144)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
        assert (Sa : msum (ivl (U nd + 12) 4) MS (ns_m2 MS nd sid)).
        { eapply msum_weaken; [| (lazymatch goal with |- ?G => let G' := eval unfold ns_m2 in G in change_no_check G' end); apply msum_wbytes; rewrite length_N_to_le_bytes, Un12; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
          intros z Hz. unfold ivl in *. rewrite length_N_to_le_bytes, Un12 in Hz. cbn in Hz. lia. }
        assert (Sb : msum (ivl (U P - 160) 16) (ns_m2 MS nd sid) (ns_m3 MS Q nd sid)).
        { (lazymatch goal with |- ?G => let G' := eval unfold ns_m3 in G in change_no_check G' end). apply msum_outside; [| apply nw_mem_grows]. intros x Hx. apply nw_mem_outside; [lia|]. unfold ivl in Hx. rewrite UQ32. lia. }
        split.
        { eapply msum_weaken; [| exact (msum_trans _ _ _ _ _ Sa Sb)]. (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). intros z Hz. lia. }
        split; [exact A2|]. split; [exact A8|]. split; [| exact AG1].
        apply (msum_rdn_eq ASEGS _ _ _ _ _ _ Sb); [rewrite Un12; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; rewrite Un12 in Hz; cbn in Hz; (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end); lia |].
        (lazymatch goal with |- ?G => let G' := eval unfold ns_m2 in G in change_no_check G' end). apply (rdn_wbytes_hit ASEGS (LE4 sid)). rewrite length_N_to_le_bytes, Un12. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    destruct W1 as (r1 & M1 & RUN1 & S1 & A2 & A8 & Rsid & AG1).
    assert (NI : forall i : reg, In i [9; 18; 21; 23] -> ~ In i [1; 2; 8; 10; 11]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (di_post M1 rom P ra nd b hd idw s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v r1 A2 A8
                ltac:(rewrite (AG1 9%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact H9)
                ltac:(rewrite (AG1 18%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact H18)
                ltac:(rewrite (AG1 21%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact H21)
                ltac:(rewrite (AG1 23%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact H23)
                ltac:(lia) Hret ltac:(lia) ltac:(lia)
                (msum_store_ok ASEGS _ MS M1 _ _ S1 SOKn) (msum_store_ok ASEGS _ MS M1 _ _ S1 SOKb))
      as (r2 & RUN2 & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & AG2).
    { intros k v Hin.
      assert (K : (-88 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply (msum_rdn_eq ASEGS _ MS M1 _ _ _ S1); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | | exact (SL k v Hin)].
      intros z Hz. rewrite at_u in Hz by lia. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). lia. }
    exists r2, (di_mem M1 nd b hd idw). split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    assert (S2 : msum (wun (ivl (U nd + 8) 4) (ivl (U b) 4)) M1 (di_mem M1 nd b hd idw)).
    { (lazymatch goal with |- ?G => let G' := eval unfold di_mem in G in change_no_check G' end). eapply msum_weaken; [| eapply msum_trans; apply msum_wbytes; rewrite length_N_to_le_bytes, ?Un8; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      intros z [Hz|Hz]; unfold ivl in *; rewrite length_N_to_le_bytes, ?Un8 in Hz; cbn in Hz; [left | right]; lia. }
    split.
    { eapply msum_weaken; [| exact (msum_trans _ _ _ _ _ S1 S2)]. (lazymatch goal with |- ?G => let G' := eval unfold tail_W, wun, ivl in G in change_no_check G' end). intros z Hz. lia. }
    repeat (split; [assumption|]).
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold di_mem in G in change_no_check G' end). rewrite rdn_wbytes_out; [apply (rdn_wbytes_hit ASEGS (LE4 hd)) | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Un8; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    split.
    { apply (msum_rdn_eq ASEGS _ M1 _ _ _ _ S2); [rewrite Un12; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact Rsid].
      intros z Hz. rewrite Un12 in Hz. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). lia. }
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold di_mem in G in change_no_check G' end). apply (rdn_wbytes_hit ASEGS (LE4 idw)). rewrite length_N_to_le_bytes. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    apply (regs_agree_trans _ regs r1); [ra_pc AG1 | ra_pc AG2].
  Qed.
End TAIL.
End FPGen.
End AsDepotRunT.
Module AsDepotRunH.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit AsDepotLock AsDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum AsDepotRunT.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition head_W (P D b nd : word) : Z -> Prop :=
  wun (ivl (U P - 160) 48) (wun (ivl (U b) 4) (wun (ivl (U D + 4194304) 4) (ivl (U nd) 8))).

(* [comment removed for export] *)
Definition at_store (P nd b hsh : word) (hd idz : Z) (r : bvmap 5 word) (M1 : word -> option byte) : Prop :=
  getr r 1 = (0x8e7c4 : word) /\ getr r 2 = at_ (at_ P (-112)) (-32) /\ getr r 8 = nd
  /\ getr r 10 = Z_to_bv 64 1938504 /\ getr r 11 = at_ P (-104) /\ getr r 12 = at_ (at_ P (-112)) (-24)
  /\ getr r 9 = nd /\ getr r 18 = b /\ getr r 21 = Z_to_bv 64 hd /\ getr r 23 = Z_to_bv 64 idz
  /\ rdn ASEGS M1 nd 8 = Some (LE8 hsh)
  /\ rdn ASEGS M1 (at_ (at_ P (-112)) (-8)) 8 = Some (LE8 (0x8eca8 : word))
  /\ rdn ASEGS M1 (at_ (at_ P (-112)) (-16)) 8 = Some (LE8 (Z_to_bv 64 0)).

Section HEAD.
  Variables (M rom : word -> option byte) (P D hsh blk : word) (hd NIDS BIX : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation b := (Z_to_bv 64 (U D + 4 * BIX)).
  #[local] Abbreviation nd := (di_node blk NIDS).
  Hypothesis H2 : getr regs 2 = Q.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0.
  Hypothesis H9 : getr regs 9 = D.
  Hypothesis H18 : getr regs 18 = b.
  Hypothesis H19 : getr regs 19 = hsh.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 65535.
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 (U D + 4194320).
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 hd.
  Hypothesis HP : (2 ^ 32 + 160 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis HD : (U D mod 4 = 0 /\ U D + 0x500000 <= 2 ^ 32)%Z.
  Hypothesis HBIX : (0 <= BIX < 2 ^ 20)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis Hblk : (U blk <> 0 /\ U blk + 2 ^ 20 <= U P - 160 /\ (U blk + 2 ^ 20 <= U D \/ U D + 0x440010 <= U blk))%Z.
  Hypothesis Rb : rdn ASEGS M b 4 = Some (LE4 (Z_to_bv 64 hd)).
  Hypothesis SOKb : store_ok ASEGS M b 4 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ Q (-48)) 48 = true.
  Hypothesis Rcnt : rdn ASEGS M (at_ D 0x400000) 4 = Some (LE4 (Z_to_bv 64 NIDS)).
  Hypothesis SOKc : store_ok ASEGS M (at_ D 0x400000) 4 = true.
  Hypothesis Rmap : rdn ASEGS M (Z_to_bv 64 (U D + 0x400010 + 8 * ((NIDS + 1) / 2 ^ 16))) 8 = Some (LE8 blk).
  Hypothesis SOKn : store_ok ASEGS M nd 8 = true.

  Lemma put_head :
    exists r M1, msteps ASEGS (mkst regs (0x8ec18 : word) M rom) (mkst r (0x8c484 : word) M1 rom)
      /\ msum (head_W P D b nd) M M1
      /\ at_store P nd b hsh hd (NIDS + 1) r M1
      /\ rdn ASEGS M1 (at_ D 0x400000) 4 = Some (LE4 (v_add (Z_to_bv 64 NIDS) (Z_to_bv 64 1)))
      /\ regs_agree (fun i : reg => In i put_clob) regs r.
  Proof using SOKn Rmap SOKc Rcnt Hstk SOKb Rb Hblk Hn Hhd HBIX HD HP H25 H24 H22 H19 H18 H9 H8 H2.
    pose proof (u64_range P) as HPr. pose proof (u64_range D) as HDr. pose proof (u64_range blk) as Hbr.
    destruct HP as [P1 P2]. destruct HD as [D4 D32]. destruct Hblk as (BK0 & BK1 & BK2). destruct Hn as [N0 N1].
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Ub : U b = (U D + 4 * BIX)%Z) by (rewrite u_Z2bv by lia; reflexivity).
    assert (M16 : (0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Und : U nd = (U blk + 16 * ((NIDS + 1) mod 2 ^ 16))%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold di_node in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (UcA : U (at_ D 0x400000) = (U D + 4194304)%Z) by (rewrite at_u by lia; reflexivity).
    destruct (di_miss_pre M rom P D hsh blk hd NIDS BIX regs H2 H8 H9 H18 H19 H22 H24 H25 ltac:(lia) (conj D4 D32) HBIX Hhd (conj N0 N1)
                ltac:(lia) Rb SOKb Hstk Rcnt SOKc Rmap)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A13 & A8 & A9 & A18 & A21 & A23 & AG1).
    set (ML := dl_mem M Q (0x8ec20 : word) (Z_to_bv 64 0) D b hsh b hd) in *.
    set (Mc := di_cmem ML D NIDS) in *.
    assert (SL : msum (wun (ivl (U P - 160) 48) (ivl (U b) 4)) M ML).
    { (lazymatch goal with |- ?G => let G' := eval unfold ML, dl_mem in G in change_no_check G' end). eapply msum_weaken; [| eapply (msum_trans _ _ M (dl_frame M Q (0x8ec20 : word) (Z_to_bv 64 0) D b hsh));
                                                  [| apply msum_wbytes; rewrite length_N_to_le_bytes, Ub; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]].
      2:{ apply (msum_outside (ivl (U P - 160) 48)); [| apply dl_frame_grows]. intros x Hx.
          apply (dl_frame_outside M Q (0x8ec20 : word) b (Z_to_bv 64 0) D b hsh ltac:(rewrite UQ; lia)). unfold ivl in Hx. rewrite UQ. lia. }
      intros z [Hz|Hz]; [left; exact Hz | right]. unfold ivl in *. rewrite length_N_to_le_bytes, Ub in Hz. cbn in Hz. rewrite Ub. lia. }
    assert (Sc : msum (ivl (U D + 4194304) 4) ML Mc).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mc, di_cmem in G in change_no_check G' end). eapply msum_weaken; [| apply msum_wbytes; rewrite length_N_to_le_bytes, UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      intros z Hz. unfold ivl in *. rewrite length_N_to_le_bytes, UcA in Hz. cbn in Hz. lia. }
    assert (RcntC : rdn ASEGS Mc (at_ D 0x400000) 4 = Some (LE4 (v_add (Z_to_bv 64 NIDS) (Z_to_bv 64 1)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mc, di_cmem in G in change_no_check G' end). apply (rdn_wbytes_hit ASEGS (LE4 (v_add (Z_to_bv 64 NIDS) (Z_to_bv 64 1)))). rewrite length_N_to_le_bytes, UcA. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    assert (S1 : msum (wun (wun (ivl (U P - 160) 48) (ivl (U b) 4)) (ivl (U D + 4194304) 4)) M Mc) by exact (msum_trans _ _ _ _ _ SL Sc).
    (* [comment removed for export] *)
    destruct (ns_pre Mc rom Q (0x8eca8 : word) (Z_to_bv 64 0) nd (at_ P (-104)) hsh r1 A1 A2 A8 A10 A12 A13 ltac:(rewrite UQ; lia)
                ltac:(rewrite UQ, Und; lia))
      as (r2 & RUN2 & B1 & B2 & B8 & B10 & B11 & B12 & AG2).
    { apply (msum_store_ok ASEGS _ M Mc _ _ S1). eapply (store_ok_sub ASEGS M (at_ Q (-48)) _ 48); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { exact (msum_store_ok ASEGS _ M Mc _ _ S1 SOKn). }
    set (M1 := ns_m1 Mc Q (0x8eca8 : word) (Z_to_bv 64 0) nd hsh) in *.
    assert (UQ8 : U (at_ Q (-8)) = (U P - 120)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UQ16 : U (at_ Q (-16)) = (U P - 128)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UQ24 : U (at_ Q (-24)) = (U P - 136)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (S2 : msum (wun (ivl (U P - 160) 48) (ivl (U nd) 8)) Mc M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, ns_m1 in G in change_no_check G' end).
      eapply msum_weaken; [| eapply msum_trans; [eapply msum_trans; [eapply msum_trans |] |]; apply msum_wbytes; rewrite length_N_to_le_bytes, ?UQ8, ?UQ16, ?UQ24, ?Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). intros z Hz. rewrite !length_N_to_le_bytes, ?UQ8, ?UQ16, ?UQ24 in Hz. cbn in Hz. lia. }
    exists r2, M1. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split.
    { eapply msum_weaken; [| exact (msum_trans _ _ _ _ _ S1 S2)]. (lazymatch goal with |- ?G => let G' := eval unfold head_W, wun, ivl in G in change_no_check G' end). intros z Hz. rewrite Ub. rewrite Ub in Hz. lia. }
    assert (NI : forall i : reg, In i [9; 18; 21; 23] -> ~ In i [1; 2; 8; 10; 11; 12]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold at_store in G in change_no_check G' end). repeat (split; [assumption|]).
      split; [rewrite (AG2 9%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact A9|].
      split; [rewrite (AG2 18%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact A18|].
      split; [rewrite (AG2 21%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact A21|].
      split; [rewrite (AG2 23%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact A23|].
      (lazymatch goal with |- ?G => let G' := eval unfold M1, ns_m1 in G in change_no_check G' end).
      split. { rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; rewrite Und; lia | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UQ24, ?Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
      split. { do 3 (rewrite rdn_wbytes_out; [ | wd_lenlit; rewrite ?length_N_to_le_bytes, ?UQ8, ?UQ16, ?UQ24, ?Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ..]). apply rdn_wbytes_hit8. rewrite UQ8. lia. }
      do 2 (rewrite rdn_wbytes_out; [ | wd_lenlit; rewrite ?length_N_to_le_bytes, ?UQ8, ?UQ16, ?UQ24, ?Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ..]). apply rdn_wbytes_hit8. rewrite UQ16. lia. }
    split.
    { apply (msum_rdn_eq ASEGS _ Mc M1 _ _ _ S2); [rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact RcntC].
      intros z Hz. rewrite UcA in Hz. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). rewrite Und. lia. }
    apply (regs_agree_trans _ regs r1); [ra_pc AG1 | ra_pc AG2].
  Qed.
End HEAD.
End FPGen.
End AsDepotRunH.
Module AsDepotRunN.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit AsDepotLock AsDepotIns AsDepotIns2 AsDepotBlk AsDepotMap OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum AsDepotRunT AsDepotRunH.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition n1post_W (P MU nd : word) (idx : Z) : Z -> Prop :=
  wun (ivl (U P - 144) 32) (wun (ivl (U MU + 8 + 8 * idx) 8) (wun (ivl (U MU) 1) (ivl (U nd) 8))).

Section N1POST.
  Variables (MB rom : word -> option byte) (P MU hsh newblk b : word) (hd NIDS : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation idx := ((NIDS + 1) / 2 ^ 16)%Z.
  #[local] Abbreviation nd := (di_node newblk NIDS).
  Hypothesis H2 : getr regs 2 = at_ Q (-32).
  Hypothesis H8 : getr regs 8 = MU.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (U MU + 8 * idx).
  Hypothesis H10 : getr regs 10 = newblk.
  Hypothesis H19 : getr regs 19 = hsh.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 hd.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 65535.
  Hypothesis H23 : getr regs 23 = Z_to_bv 64 (NIDS + 1).
  Hypothesis HP : (2 ^ 32 + 160 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis HMU : (U MU + 8 + 8 * 2 ^ 15 <= 2 ^ 32)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis Hblk : (2 ^ 32 <= U newblk \/ U MU + 8 + 8 * 2 ^ 15 <= U newblk)%Z.
  Hypothesis Hblk2 : (U newblk + 2 ^ 20 <= U P - 160)%Z.
  Hypothesis SOKs : store_ok ASEGS MB (tl_slot MU idx) 8 = true.
  Hypothesis SOKl : store_ok ASEGS MB MU 1 = true.
  Hypothesis SOKn : store_ok ASEGS MB nd 8 = true.
  Hypothesis Hstk : store_ok ASEGS MB (at_ Q (-32)) 32 = true.
  Hypothesis SL : forall (k : Z) (v : word), In (k, v) [(-8, (0x8ed20%bv : word)); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 (NIDS + 1)); (-32, b)]%Z -> rdn ASEGS MB (at_ Q k) 8 = Some (LE8 v).

  Lemma put_n1_post :
    exists r M1, msteps ASEGS (mkst regs (0x8f348 : word) MB rom) (mkst r (0x8c484 : word) M1 rom)
      /\ msum (n1post_W P MU nd idx) MB M1
      /\ at_store P nd b hsh hd (NIDS + 1) r M1
      /\ rdn ASEGS M1 (tl_slot MU idx) 8 = Some (LE8 newblk)
      /\ rdn ASEGS M1 MU 1 = Some [Z_to_bv 8 0]
      /\ regs_agree (fun i : reg => In i put_clob) regs r.
  Proof using SL Hstk SOKn SOKl SOKs Hblk2 Hblk Hn HMU HP H23 H22 H21 H19 H10 H9 H8 H2.
    pose proof (u64_range P) as HPr. pose proof (u64_range MU) as HMr. pose proof (u64_range newblk) as Hbr.
    destruct HP as [P1 P2]. destruct Hn as [N0 N1].
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (I16 : (0 <= idx < 2 ^ 15)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M16 : (0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Und : U nd = (U newblk + 16 * ((NIDS + 1) mod 2 ^ 16))%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold di_node in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Uslot : U (tl_slot MU idx) = (U MU + 8 + 8 * idx)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    (* [comment removed for export] *)
    destruct (tl_post MB rom Q (0x8ed20 : word) (Z_to_bv 64 0) (Z_to_bv 64 (NIDS + 1)) b MU newblk idx regs H2 H8 H9 H10
                ltac:(rewrite UQ; lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity) HMU I16 SOKs SOKl SL)
      as (r1 & RUN1 & A10 & A2 & A1 & A8 & A9 & A18 & AG1).
    set (Mt := tl_m2 MB MU newblk idx) in *.
    assert (St : msum (wun (ivl (U MU + 8 + 8 * idx) 8) (ivl (U MU) 1)) MB Mt).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mt, tl_m2 in G in change_no_check G' end). eapply msum_weaken; [| eapply msum_trans; apply msum_wbytes; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uslot; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). intros z Hz. wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uslot in Hz. cbn in Hz. lia. }
    assert (NI1 : forall i : reg, In i [19; 21; 22; 23] -> ~ In i [1; 2; 8; 9; 18]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (di_pre2_cont Mt rom P hsh newblk NIDS r1 A2 A9 A10
                ltac:(rewrite (AG1 19%bv) by (apply NI1; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H19)
                ltac:(rewrite (AG1 22%bv) by (apply NI1; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H22)
                ltac:(lia) (conj N0 N1))
      as (r2 & RUN2 & B1 & B2 & B10 & B11 & B12 & B13 & B9 & AG2).
    assert (NI2 : forall i : reg, In i [8; 18; 21; 23] -> ~ In i [1; 9; 10; 11; 12; 13]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (ns_pre Mt rom Q (0x8eca8 : word) (Z_to_bv 64 0) nd (at_ P (-104)) hsh r2 B1 B2
                ltac:(rewrite (AG2 8%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact A8) B10 B12 B13 ltac:(rewrite UQ; lia)
                ltac:(rewrite UQ, Und; lia)
                (msum_store_ok ASEGS _ MB Mt _ _ St Hstk) (msum_store_ok ASEGS _ MB Mt _ _ St SOKn))
      as (r3 & RUN3 & C1 & C2 & C8 & C10 & C11 & C12 & AG3).
    set (M1 := ns_m1 Mt Q (0x8eca8 : word) (Z_to_bv 64 0) nd hsh) in *.
    assert (UQ8 : U (at_ Q (-8)) = (U P - 120)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UQ16 : U (at_ Q (-16)) = (U P - 128)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UQ24 : U (at_ Q (-24)) = (U P - 136)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (S2 : msum (wun (ivl (U P - 144) 32) (ivl (U nd) 8)) Mt M1).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, ns_m1 in G in change_no_check G' end).
      eapply msum_weaken; [| eapply msum_trans; [eapply msum_trans; [eapply msum_trans |] |]; apply msum_wbytes; rewrite length_N_to_le_bytes, ?UQ8, ?UQ16, ?UQ24, ?Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). intros z Hz. rewrite !length_N_to_le_bytes, ?UQ8, ?UQ16, ?UQ24 in Hz. cbn in Hz. lia. }
    exists r3, M1. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    split.
    { eapply msum_weaken; [| exact (msum_trans _ _ _ _ _ St S2)]. (lazymatch goal with |- ?G => let G' := eval unfold n1post_W, wun, ivl in G in change_no_check G' end). intros z Hz. lia. }
    assert (NI3 : forall i : reg, In i [9; 18; 21; 23] -> ~ In i [1; 2; 8; 10; 11; 12]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold at_store in G in change_no_check G' end). repeat (split; [assumption|]).
      split; [rewrite (AG3 9%bv) by (apply NI3; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B9|].
      split; [rewrite (AG3 18%bv) by (apply NI3; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG2 18%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact A18|].
      split; [rewrite (AG3 21%bv) by (apply NI3; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG2 21%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto);
              rewrite (AG1 21%bv) by (apply NI1; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H21|].
      split; [rewrite (AG3 23%bv) by (apply NI3; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG2 23%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto);
              rewrite (AG1 23%bv) by (apply NI1; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H23|].
      (lazymatch goal with |- ?G => let G' := eval unfold M1, ns_m1 in G in change_no_check G' end).
      split. { rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; rewrite Und; lia | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UQ24, ?Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
      split. { do 3 (rewrite rdn_wbytes_out; [ | wd_lenlit; rewrite ?length_N_to_le_bytes, ?UQ8, ?UQ16, ?UQ24, ?Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ..]). apply rdn_wbytes_hit8. rewrite UQ8. lia. }
      do 2 (rewrite rdn_wbytes_out; [ | wd_lenlit; rewrite ?length_N_to_le_bytes, ?UQ8, ?UQ16, ?UQ24, ?Und; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ..]). apply rdn_wbytes_hit8. rewrite UQ16. lia. }
    split.
    { apply (msum_rdn_eq ASEGS _ Mt M1 _ _ _ S2); [rewrite Uslot; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; rewrite Uslot in Hz; cbn in Hz; (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end); rewrite Und; lia |].
      (lazymatch goal with |- ?G => let G' := eval unfold Mt, tl_m2 in G in change_no_check G' end). rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; rewrite Uslot; lia | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?Uslot; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    split.
    { apply (msum_rdn_eq ASEGS _ Mt M1 _ _ _ S2); [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; cbn in Hz; (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end); rewrite Und; lia |].
      (lazymatch goal with |- ?G => let G' := eval unfold Mt, tl_m2 in G in change_no_check G' end). apply (rdn_wbytes_hit ASEGS [Z_to_bv 8 0]). (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    apply (regs_agree_trans _ regs r1); [ra_pc AG1|]. apply (regs_agree_trans _ r1 r2); [ra_pc AG2 | ra_pc AG3].
  Qed.
End N1POST.
(* [comment removed for export] *)
Definition n1pre_W (P D b : word) : Z -> Prop :=
  wun (ivl (U P - 160) 48) (wun (ivl (U b) 4) (wun (ivl (U D + 4194304) 4) (ivl (U D + 4194312) 4))).

Section N1PRE.
  Variables (M rom : word -> option byte) (P D hsh lkw : word) (b1 b2 b3 : byte) (hd NIDS BIX PGP : Z).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation b := (Z_to_bv 64 (U D + 4 * BIX)).
  #[local] Abbreviation MU := (Z_to_bv 64 (U D + 4194312)).
  #[local] Abbreviation idx := ((NIDS + 1) / 2 ^ 16)%Z.
  Hypothesis H2 : getr regs 2 = Q.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0.
  Hypothesis H9 : getr regs 9 = D.
  Hypothesis H18 : getr regs 18 = b.
  Hypothesis H19 : getr regs 19 = hsh.
  Hypothesis H20 : getr regs 20 = MU.
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 (U D + 4194320).
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 hd.
  Hypothesis HP : (2 ^ 32 + 160 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis HD : (U D mod 8 = 0 /\ 1045080 <= U D /\ U D + 0x500000 <= 2 ^ 32)%Z.
  Hypothesis HBIX : (0 <= BIX < 2 ^ 20)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis HPGP : (0 <= PGP /\ PGP + 8 <= U D)%Z.
  Hypothesis Rb : rdn ASEGS M b 4 = Some (LE4 (Z_to_bv 64 hd)).
  Hypothesis SOKb : store_ok ASEGS M b 4 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ Q (-48)) 48 = true.
  Hypothesis Rcnt : rdn ASEGS M (at_ D 0x400000) 4 = Some (LE4 (Z_to_bv 64 NIDS)).
  Hypothesis SOKc : store_ok ASEGS M (at_ D 0x400000) 4 = true.
  Hypothesis Rmap : rdn ASEGS M (Z_to_bv 64 (U D + 0x400010 + 8 * idx)) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis R_lock : rdn ASEGS M MU 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw.
  Hypothesis SOKl : store_ok ASEGS M MU 4 = true.
  Hypothesis Rgpg : rdn ASEGS M (Z_to_bv 64 1045072) 8 = Some (LE8 (Z_to_bv 64 PGP)).
  Hypothesis Rpg : rdn ASEGS M (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)).

  Lemma put_n1_pre :
    exists r Mt, msteps ASEGS (mkst regs (0x8ec18 : word) M rom) (mkst r (0x81e08 : word) Mt rom)
      /\ msum (n1pre_W P D b) M Mt
      /\ getr r 1 = (0x8f348 : word) /\ getr r 2 = at_ Q (-32)
      /\ getr r 10 = Z_to_bv 64 1048576 /\ getr r 11 = Z_to_bv 64 138670 /\ getr r 12 = Z_to_bv 64 0
      /\ getr r 8 = MU /\ getr r 9 = Z_to_bv 64 (U MU + 8 * idx)
      /\ getr r 19 = hsh /\ getr r 21 = Z_to_bv 64 hd /\ getr r 22 = getr regs 22 /\ getr r 23 = Z_to_bv 64 (NIDS + 1)
      /\ rdn ASEGS Mt (at_ D 0x400000) 4 = Some (LE4 (v_add (Z_to_bv 64 NIDS) (Z_to_bv 64 1)))
      /\ (forall (k : Z) (v : word), In (k, v) [(-8, (0x8ed20%bv : word)); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 (NIDS + 1)); (-32, b)]%Z -> rdn ASEGS Mt (at_ Q k) 8 = Some (LE8 v))
      /\ regs_agree (fun i : reg => In i put_clob) regs r.
  Proof using Rpg Rgpg SOKl V_lock R_lock Rmap SOKc Rcnt Hstk SOKb Rb HPGP Hn Hhd HBIX HD HP H25 H24 H20 H19 H18 H9 H8 H2 PGP b3 b2 b1 lkw.
    pose proof (u64_range P) as HPr. pose proof (u64_range D) as HDr.
    destruct HP as [P1 P2]. destruct HD as (D8 & DLO & D32). destruct Hn as [N0 N1]. destruct HPGP as [PG0 PG1].
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Ub : U b = (U D + 4 * BIX)%Z) by (rewrite u_Z2bv by lia; reflexivity).
    assert (UMU : U MU = (U D + 4194312)%Z) by (rewrite u_Z2bv by lia; reflexivity).
    assert (UcA : U (at_ D 0x400000) = (U D + 4194304)%Z) by (rewrite at_u by lia; reflexivity).
    assert (I16 : (0 <= idx < 2 ^ 15)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (D4 : (U D mod 4 = 0)%Z).
    { pose proof (Z.div_mod (U D) 8 ltac:(lia)) as E. rewrite D8 in E. rewrite E. replace (8 * (U D / 8) + 0)%Z with ((2 * (U D / 8)) * 4)%Z by lia. apply Z_mod_mult. }
    (* [comment removed for export] *)
    assert (W1 : exists r1, msteps ASEGS (mkst regs (0x8ec18 : word) M rom) (mkst r1 (0x8f214 : word) M rom)
                   /\ getr r1 1 = (0x8ec20 : word) /\ getr r1 10 = b /\ regs_agree (fun i : reg => In i [1; 10]) regs r1).
    { wd_eexists. split.
      - an F_8ec10 D_8ec10.                            (* [comment removed for export] *)
        an F_8ec14 D_8ec14.                            (* [comment removed for export] *)
        wd_refl.
      - post. all: try ra_solve. all: try (apply bv_eq; reflexivity). }
    destruct W1 as (r1 & RUN1 & A1 & A10 & AG1).
    assert (NI : forall i : reg, In i [2; 8; 9; 18; 19; 20; 24; 25] -> ~ In i [1; 10]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (dl_lock M rom Q (0x8ec20 : word) b (Z_to_bv 64 0) D b hsh hd r1 A1
                ltac:(rewrite (AG1 2%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H2) A10
                ltac:(rewrite (AG1 8%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H8)
                ltac:(rewrite (AG1 9%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H9)
                ltac:(rewrite (AG1 18%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H18)
                ltac:(rewrite (AG1 19%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H19)
                ltac:(rewrite UQ; lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite Ub, UQ; split; [rewrite Z.add_mod, D4, Z.mul_comm, Z_mod_mult by lia; reflexivity | lia]) Hhd Rb SOKb Hstk)
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & AG2).
    set (ML := dl_mem M Q (0x8ec20 : word) (Z_to_bv 64 0) D b hsh b hd) in *.
    assert (SL : msum (wun (ivl (U P - 160) 48) (ivl (U b) 4)) M ML).
    { (lazymatch goal with |- ?G => let G' := eval unfold ML, dl_mem in G in change_no_check G' end). eapply msum_weaken; [| eapply (msum_trans _ _ M (dl_frame M Q (0x8ec20 : word) (Z_to_bv 64 0) D b hsh));
                                                  [| apply msum_wbytes; rewrite length_N_to_le_bytes, Ub; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]].
      2:{ apply (msum_outside (ivl (U P - 160) 48)); [| apply dl_frame_grows]. intros x Hx.
          apply (dl_frame_outside M Q (0x8ec20 : word) b (Z_to_bv 64 0) D b hsh ltac:(rewrite UQ; lia)). unfold ivl in Hx. rewrite UQ. lia. }
      intros z [Hz|Hz]; [left; exact Hz | right]. unfold ivl in *. rewrite length_N_to_le_bytes, Ub in Hz. cbn in Hz. rewrite Ub. lia. }
    assert (THRUL : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U a + Z.of_nat n <= U P - 160 \/ U P - 112 <= U a)%Z ->
              (U a + Z.of_nat n <= U D \/ U D + 4194304 <= U a)%Z -> rdn ASEGS M a n = Some v -> rdn ASEGS ML a n = Some v).
    { intros a n v B0 X1 X2 Hr. apply (msum_rdn_eq ASEGS _ M ML _ _ _ SL B0); [| exact Hr]. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). rewrite Ub. lia. }
    assert (NI2 : forall i : reg, In i [20; 24; 25] -> ~ In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (di_pre2_null ML rom P D hd NIDS r2 B2 B9 B10
                ltac:(rewrite (AG2 20%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG1 20%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H20)
                ltac:(rewrite (AG2 24%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG1 24%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H24)
                ltac:(rewrite (AG2 25%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG1 25%bv) by (apply NI; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact H25)
                ltac:(lia) (conj D4 D32) (conj N0 N1))
      as (r3 & RUN3 & C1 & C2 & C10 & C11 & C9 & C21 & C23 & AG3).
    { apply THRUL; [rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rcnt]. }
    { exact (msum_store_ok ASEGS _ M ML _ _ SL SOKc). }
    { apply THRUL; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rmap]. }
    set (Mc := di_cmem ML D NIDS) in *.
    assert (Sc : msum (ivl (U D + 4194304) 4) ML Mc).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mc, di_cmem in G in change_no_check G' end). eapply msum_weaken; [| apply msum_wbytes; rewrite length_N_to_le_bytes, UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      intros z Hz. unfold ivl in *. rewrite length_N_to_le_bytes, UcA in Hz. cbn in Hz. lia. }
    assert (RcntC : rdn ASEGS Mc (at_ D 0x400000) 4 = Some (LE4 (v_add (Z_to_bv 64 NIDS) (Z_to_bv 64 1)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mc, di_cmem in G in change_no_check G' end). apply (rdn_wbytes_hit ASEGS (LE4 (v_add (Z_to_bv 64 NIDS) (Z_to_bv 64 1)))). rewrite length_N_to_le_bytes, UcA. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    assert (S12 : msum (wun (wun (ivl (U P - 160) 48) (ivl (U b) 4)) (ivl (U D + 4194304) 4)) M Mc) by exact (msum_trans _ _ _ _ _ SL Sc).
    assert (THRUC : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U a + Z.of_nat n <= U P - 160 \/ U P - 112 <= U a)%Z ->
              (U a + Z.of_nat n <= U D \/ U D + 4194308 <= U a)%Z -> rdn ASEGS M a n = Some v -> rdn ASEGS Mc a n = Some v).
    { intros a n v B0 X1 X2 Hr. apply (msum_rdn_eq ASEGS _ M Mc _ _ _ S12 B0); [| exact Hr]. intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). rewrite Ub. lia. }
    assert (NI3 : forall i : reg, In i [8; 18; 19; 22] -> ~ In i [1; 9; 10; 11; 21; 23]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    (* [comment removed for export] *)
    destruct (tl_pre Mc rom Q (0x8ed20 : word) (Z_to_bv 64 0) (Z_to_bv 64 (NIDS + 1)) b MU lkw b1 b2 b3 idx PGP r3 C1 C2
                ltac:(rewrite (AG3 8%bv) by (apply NI3; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B8) C9
                ltac:(rewrite (AG3 18%bv) by (apply NI3; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B18) C10 C11
                ltac:(rewrite UQ; lia)
                ltac:(rewrite UMU; split; [rewrite Z.add_mod, D8 by lia; reflexivity | lia]) I16 ltac:(rewrite UMU; lia))
      as (r4 & RUN4 & E1 & E2 & E10 & E11 & E12 & E8 & E9 & AG4).
    { apply THRUC; [rewrite UMU; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UMU; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UMU; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_lock]. }
    { exact V_lock. }
    { (lazymatch goal with |- ?G => let G' := eval unfold tl_slot in G in change_no_check G' end). replace (U MU + 8 + 8 * idx)%Z with (U D + 0x400010 + 8 * idx)%Z by (rewrite UMU; lia).
      apply THRUC; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rmap]. }
    { apply THRUC; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rgpg]. }
    { apply THRUC; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rpg]. }
    { exact (msum_store_ok ASEGS _ M Mc _ _ S12 SOKl). }
    { apply (msum_store_ok ASEGS _ M Mc _ _ S12). eapply (store_ok_sub ASEGS M (at_ Q (-48)) _ 48); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    set (Mt := tl_m1 Mc Q (0x8ed20 : word) (Z_to_bv 64 0) (Z_to_bv 64 (NIDS + 1)) b MU b1 b2 b3) in *.
    assert (St : msum (wun (ivl (U P - 144) 32) (ivl (U D + 4194312) 4)) Mc Mt).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mt, tl_m1 in G in change_no_check G' end). eapply msum_weaken; [| eapply (msum_trans _ _ Mc (bi_frame Mc Q (0x8ed20 : word) (Z_to_bv 64 0) (Z_to_bv 64 (NIDS + 1)) b));
                                                  [| apply msum_wbytes; rewrite UMU; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]].
      2:{ (lazymatch goal with |- ?G => let G' := eval unfold bi_frame in G in change_no_check G' end). eapply msum_trans; [eapply msum_trans; [eapply msum_trans |] |]; apply msum_wbytes; rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
      (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end). intros z Hz. rewrite !length_N_to_le_bytes, !at_u, ?UMU in Hz by lia. cbn in Hz. lia. }
    exists r4, Mt. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3 | exact RUN4]|].
    split.
    { eapply msum_weaken; [| exact (msum_trans _ _ _ _ _ S12 St)]. (lazymatch goal with |- ?G => let G' := eval unfold n1pre_W, wun, ivl in G in change_no_check G' end). rewrite Ub. intros z Hz. lia. }
    assert (NI4 : forall i : reg, In i [19; 21; 22; 23] -> ~ In i [1; 2; 8; 9; 18; 10; 11; 12; 13; 14; 15]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    assert (NI3' : forall i : reg, In i [19; 22] -> ~ In i [1; 9; 10; 11; 21; 23]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    assert (NI2' : forall i : reg, In i [22] -> ~ In i [1; 2; 8; 9; 10; 11; 12; 13; 14; 18; 19]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    assert (NI1' : forall i : reg, In i [22] -> ~ In i [1; 10]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    repeat (split; [assumption|]).
    split; [rewrite (AG4 19%bv) by (apply NI4; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG3 19%bv) by (apply NI3'; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact B19|].
    split; [rewrite (AG4 21%bv) by (apply NI4; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact C21|].
    split; [rewrite (AG4 22%bv) by (apply NI4; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); rewrite (AG3 22%bv) by (apply NI3'; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto);
            rewrite (AG2 22%bv) by (apply NI2'; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); apply (AG1 22%bv); apply NI1'; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto|].
    split; [rewrite (AG4 23%bv) by (apply NI4; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact C23|].
    split.
    { apply (msum_rdn_eq ASEGS _ Mc Mt _ _ _ St); [rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros z Hz; rewrite UcA in Hz; cbn in Hz; (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end); lia | exact RcntC]. }
    split.
    { intros k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold Mt, tl_m1 in G in change_no_check G' end).
      assert (K : (-32 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite rdn_wbytes_out; [| rewrite at_u, UMU by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite UMU; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      (lazymatch goal with |- ?G => let G' := eval unfold bi_frame in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    apply (regs_agree_trans _ regs r1); [ra_pc AG1|]. apply (regs_agree_trans _ r1 r2); [ra_pc AG2|].
    apply (regs_agree_trans _ r2 r3); [ra_pc AG3 | ra_pc AG4].
  Qed.
End N1PRE.

End FPGen.
End AsDepotRunN.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotStoreR.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsDepotStore.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Ltac in_l := (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]).
Ltac incl_l := let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; cbv beta in Hr; unfold imemcpy_clob in Hr; cbn [In] in Hr; repeat (destruct Hr as [<-|Hr]; [in_l|]); destruct Hr.
Ltac nin := let Hx := fresh "Hx" in intro Hx; cbn [In] in Hx; repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx.

Section FPGen.
Context {fx : FPState}.

Lemma sa_mem_outside : forall (M : word -> option byte) (sp ra s0v S idxp : word) tot cnt (x : word),
  (16 <= U sp)%Z -> (U S + 8 < 2 ^ 64)%Z -> (U idxp + 8 < 2 ^ 64)%Z ->
  (U x < U sp - 16 \/ U sp <= U x)%Z -> (U x < U S \/ U S + 8 <= U x)%Z -> (U x < U idxp \/ U idxp + 8 <= U x)%Z ->
  sa_mem M sp ra s0v S idxp tot cnt x = M x.
Proof using.
  intros M sp ra s0v S idxp tot cnt x Hsp HS Hi X1 X2 X3. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold sa_mem in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
Qed.
Lemma sa_mem_grows : forall (M : word -> option byte) (sp ra s0v S idxp : word) tot cnt, mem_grows M (sa_mem M sp ra s0v S idxp tot cnt).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold sa_mem in G in change_no_check G' end). do 4 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma st_m5_outside : forall (M4 : word -> option byte) (S packp : word) tot cnt sov pk (x : word),
  (U (st_cell S tot) + 4 < 2 ^ 64)%Z -> (U packp + 8 < 2 ^ 64)%Z ->
  (U x < U (st_cell S tot) \/ U (st_cell S tot) + 4 <= U x)%Z -> (U x < U packp \/ U packp + 8 <= U x)%Z ->
  st_m5 M4 S packp tot cnt sov pk x = M4 x.
Proof using.
  intros M4 S packp tot cnt sov pk x Hc Hp X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold st_m5 in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
Qed.
Lemma st_m5_grows : forall (M4 : word -> option byte) (S packp : word) tot cnt sov pk, mem_grows M4 (st_m5 M4 S packp tot cnt sov pk).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold st_m5 in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.

Definition st_dst (blkd : word) (tot : Z) : word := Z_to_bv 64 (U blkd + 8 * (tot mod 2 ^ 20)).
Definition st_mem (M : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v S packp blkd : word) (tot sz tag sov : Z) (bs : list byte) : word -> option byte :=
  st_m5 (wbytes (wbytes (sa_mem (st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp) (at_ sp (-64)) (0x8c4fc : word) packp S (at_ sp (-64)) tot (sz + 1))
                        (st_dst blkd tot) (LE8 (st_hdr sz tag))) (at_ (st_dst blkd tot) 8) bs)
        S packp tot (sz + 1) sov 0.

Section STRUN.
  Variables (M rom : word -> option byte) (sp ra S args packp tr blkd s0v s1v s2v s3v s4v s5v : word) (sz tag tot sov : Z) (bs : list byte).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation cnt := (sz + 1)%Z.
  #[local] Abbreviation spA := (at_ sp (-64)).
  #[local] Abbreviation dst := (st_dst blkd tot).
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H10 : getr regs 10 = S.
  Hypothesis H11 : getr regs 11 = args.
  Hypothesis H12 : getr regs 12 = packp.
  Hypothesis Hsp : (2 ^ 32 + 80 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hargs : (U sp <= U args /\ U args + 16 < 2 ^ 64)%Z.
  Hypothesis Hpack : (U sp <= U packp /\ U packp + 8 < 2 ^ 64 /\ (U args + 16 <= U packp \/ U packp + 8 <= U args))%Z.
  Hypothesis Htr : (U sp <= U tr /\ U tr + 8 * sz < 2 ^ 64 /\ (U tr + 8 * sz <= U packp \/ U packp + 8 <= U tr))%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + sz + 1 <= 2 ^ 32)%Z.
  Hypothesis Hsame : (tot / 2 ^ 20 = (tot + sz) / 2 ^ 20)%Z.                       (* [comment removed for export] *)
  Hypothesis Hsov : (0 <= sov < 2 ^ 32)%Z.
  Hypothesis HS : (U S mod 8 = 0 /\ U S + 2 ^ 20 <= 2 ^ 32)%Z.
  Hypothesis Hblk : (U S + 2 ^ 20 <= U blkd /\ U blkd + 2 ^ 23 <= U sp - 80)%Z.       (* [comment removed for export] *)
  Hypothesis Hbs : length bs = Z.to_nat (8 * sz).
  Hypothesis Rsz : rdn ASEGS M (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz)).
  Hypothesis Rtag : rdn ASEGS M (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Hypothesis Rtr : rdn ASEGS M args 8 = Some (LE8 tr).
  Hypothesis Rws : rdn ASEGS M tr (length bs) = Some bs.
  Hypothesis Rtot : rdn ASEGS M S 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rblk : rdn ASEGS M (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkd).
  Hypothesis Rso : rdn ASEGS M (st_cell S tot) 4 = Some (LE4 (Z_to_bv 64 sov)).
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-80)) 80 = true.
  Hypothesis SOKp : store_ok ASEGS M packp 8 = true.
  Hypothesis SOKS : store_ok ASEGS M S 8 = true.
  Hypothesis SOKso : store_ok ASEGS M (st_cell S tot) 4 = true.
  Hypothesis SOKd : store_ok ASEGS M dst (8 + length bs) = true.

  Lemma st_run :
    exists r, msteps ASEGS (mkst regs (0x8c484 : word) M rom)
                (mkst r ra (st_mem M sp ra s0v s1v s2v s3v s4v s5v S packp blkd tot sz tag sov bs) rom)
      /\ getr r 10 = st_id tot /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20; 21]) regs r.
  Proof using SOKd SOKso SOKS SOKp Hstk Rso Rblk Rtot Rws Rtr Rtag Rsz Hbs Hblk HS Hsov Hsame Htot Htag Hsz Htr Hpack Hargs Hret Hsp H12 H11 H10 H21 H20 H19 H18 H9 H8 H2 H1 tr args.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range packp) as Hpr.
    pose proof (u64_range args) as Har. pose proof (u64_range tr) as Htrr. pose proof (u64_range blkd) as Hbr.
    destruct Hsp as [S1 S2]. destruct Hargs as [A1' A2']. destruct Hpack as (P1 & P2 & P3). destruct Htr as (T1 & T2 & T3).
    destruct Htot as [T0 T32]. destruct HS as [S8 S32]. destruct Hblk as [BK1 BK2].
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : (0 <= tot mod 2 ^ 20 /\ tot mod 2 ^ 20 + sz < 2 ^ 20)%Z).
    { pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as E1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as B1.
      pose proof (Z.div_mod (tot + sz) (2 ^ 20) ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (tot + sz) (2 ^ 20) ltac:(lia)) as B2.
      rewrite <- Hsame in E2. lia. }
    assert (Lbs : Z.of_nat (length bs) = (8 * sz)%Z) by (rewrite Hbs, Z2Nat.id by lia; reflexivity).
    assert (UspA : U spA = (U sp - 64)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Udst : U dst = (U blkd + 8 * (tot mod 2 ^ 20))%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Udst8 : U (at_ dst 8) = (U blkd + 8 * (tot mod 2 ^ 20) + 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Ucell : U (st_cell S tot) = (U S + 16 * (tot / 2 ^ 20) + 24)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    set (M1 := st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp).
    set (M2 := sa_mem M1 spA (0x8c4fc : word) packp S spA tot cnt).
    set (M3 := wbytes M2 dst (LE8 (st_hdr sz tag))).
    set (M4 := wbytes M3 (at_ dst 8) bs).
    assert (P_1 : forall x : word, (U x < U sp - 64 \/ U sp <= U x)%Z -> (U x < U packp \/ U packp + 8 <= U x)%Z -> M1 x = M x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply st_m1_outside; lia. }
    assert (P_2 : forall x : word, (U x < U sp - 80 \/ U sp - 56 <= U x)%Z -> (U x < U S \/ U S + 8 <= U x)%Z -> M2 x = M1 x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end). apply sa_mem_outside; rewrite ?UspA; lia. }
    assert (P_3 : forall x : word, (U x < U dst \/ U dst + 8 <= U x)%Z -> M3 x = M2 x).
    { intros x X1. (lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (P_4 : forall x : word, (U x < U dst + 8 \/ U dst + 8 + 8 * sz <= U x)%Z -> M4 x = M3 x).
    { intros x X1. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). rewrite wbytes_outside; rewrite ?Lbs, ?Udst8; try lia. reflexivity. }
    assert (GR1 : mem_grows M M1) by apply st_m1_grows.
    assert (GR2 : mem_grows M M2) by (eapply mem_grows_trans; [exact GR1 | apply sa_mem_grows]).
    assert (GR3 : mem_grows M M3) by (eapply mem_grows_trans; [exact GR2 | apply wbytes_grows]).
    assert (GR4 : mem_grows M M4) by (eapply mem_grows_trans; [exact GR3 | apply wbytes_grows]).
    (* [comment removed for export] *)
    destruct (st_pre M rom sp ra S args packp s0v s1v s2v s3v s4v s5v sz tag regs H1 H2 H8 H9 H18 H19 H20 H21 H10 H11 H12
                ltac:(lia) ltac:(lia) ltac:(lia) Hsz Htag Rsz Rtag)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A13 & A8 & A9 & A18 & A19 & A20 & A21 & AG1).
    { eapply (store_ok_sub ASEGS M (at_ sp (-80)) _ 80); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { exact SOKp. }
    (* [comment removed for export] *)
    destruct (sa_fast M1 rom spA (0x8c4fc : word) packp S spA blkd tot cnt r1 A1 A2 A8 A10 A11 A12
                ltac:(rewrite UspA; lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity) ltac:(lia) ltac:(lia)
                ltac:(replace (tot + cnt - 1)%Z with (tot + sz)%Z by lia; exact Hsame)
                ltac:(rewrite UspA; lia) ltac:(rewrite UspA; lia))
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & AG2).
    { rewrite <- Rtot. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply P_1; lia. }
    { eapply store_ok_mono; [exact GR1 | exact SOKS]. }
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub ASEGS M (at_ sp (-80)) _ 80); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { eapply store_ok_mono; [exact GR1|]. rewrite at_at. eapply (store_ok_sub ASEGS M (at_ sp (-80)) _ 80); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { rewrite <- Rblk. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply P_1; lia. }
    { lia. }
    fold M2 in RUN2. fold dst in B10.
    (* [comment removed for export] *)
    destruct (st_mid M2 rom args tr dst sz tag r2 B10
                ltac:(rewrite (AG2 19%bv) by nin; exact A19) ltac:(rewrite (AG2 20%bv) by nin; exact A20) ltac:(rewrite (AG2 21%bv) by nin; exact A21)
                Hsz Htag ltac:(rewrite Udst; lia))
      as (r3 & RUN3 & C1 & C10 & C11 & C12 & AG3).
    { rewrite <- Rtr. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. rewrite P_2 by lia. apply P_1; lia. }
    { eapply store_ok_mono; [exact GR2|]. eapply (store_ok_sub ASEGS M dst _ (8 + length bs)); [rewrite Udst; lia | exact SOKd | lia | lia]. }
    fold M3 in RUN3.
    (* [comment removed for export] *)
    destruct (asan_imemcpy M3 (at_ dst 8) tr (8 * sz) bs rom r3 (0x8c51c : word)) as (r4 & RUN4 & AG4).
    { constructor.
      - lia.
      - exact Hbs.
      - rewrite <- Rws. apply rdn_ext; [rewrite Lbs; lia|]. intros x Hx. rewrite Lbs in Hx. rewrite P_3 by (rewrite Udst; lia). rewrite P_2 by lia. apply P_1; lia.
      - eapply store_ok_mono; [exact GR3|]. eapply (store_ok_sub ASEGS M dst _ (8 + length bs)); [rewrite Udst; lia | exact SOKd | rewrite Udst8, Udst; lia | rewrite Udst8, Udst; lia].
      - left. rewrite Udst8. lia.
      - lia.
      - rewrite Udst8. lia. }
    { (lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end). apply bv_eq. vm_compute. reflexivity. }
    { exact C1. } { exact C10. } { exact C11. } { exact C12. }
    fold M4 in RUN4.
    (* [comment removed for export] *)
    assert (S4 : (U S mod 4 = 0)%Z).
    { pose proof (Z.div_mod (U S) 8 ltac:(lia)) as E. rewrite S8 in E. rewrite E.
      replace (8 * (U S / 8) + 0)%Z with ((2 * (U S / 8)) * 4)%Z by lia. apply Z_mod_mult. }
    destruct (st_post M4 rom sp ra S packp s0v s1v s2v s3v s4v s5v tot cnt sov 0 r4
                ltac:(rewrite (AG4 2%bv) by nin; rewrite (AG3 2%bv) by nin; exact B2)
                ltac:(rewrite (AG4 8%bv) by nin; rewrite (AG3 8%bv) by nin; exact B8)
                ltac:(rewrite (AG4 9%bv) by nin; rewrite (AG3 9%bv) by nin; rewrite (AG2 9%bv) by nin; exact A9)
                ltac:(rewrite (AG4 18%bv) by nin; rewrite (AG3 18%bv) by nin; rewrite (AG2 18%bv) by nin; exact A18)
                ltac:(lia) Hret ltac:(lia) ltac:(lia) Hsov ltac:(lia)
                ltac:(split; [exact S4 | lia])
                ltac:(lia))
      as (r5 & RUN5 & D10 & D2 & D1 & D8 & D9 & D18 & D19 & D20 & D21 & AG5).
    { transitivity (rdn ASEGS M2 spA 8).
      - apply rdn_ext; [rewrite UspA; lia|]. intros x Hx. rewrite UspA in Hx. cbn in Hx. rewrite P_4 by (rewrite Udst; lia). apply P_3. rewrite Udst. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold M2, sa_mem in G in change_no_check G' end). apply rdn_wbytes_hit8. rewrite UspA. lia. }
    { rewrite <- Rso. apply rdn_ext; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. rewrite Ucell in Hx. cbn in Hx.
      rewrite P_4 by (rewrite Udst; lia). rewrite P_3 by (rewrite Udst; lia). rewrite P_2 by lia. apply P_1; lia. }
    { eapply store_ok_mono; [exact GR4 | exact SOKso]. }
    { transitivity (rdn ASEGS M1 packp 8).
      - apply rdn_ext; [lia|]. intros x Hx. cbn in Hx. rewrite P_4 by (rewrite Udst; lia). rewrite P_3 by (rewrite Udst; lia). apply P_2; lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold M1, st_m1 in G in change_no_check G' end). apply rdn_wbytes_hit8. lia. }
    { eapply store_ok_mono; [exact GR4 | exact SOKp]. }
    { intros k v Hin.
      assert (K : (-56 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      transitivity (rdn ASEGS (st_frame M sp ra s0v s1v s2v s3v s4v s5v) (at_ sp k) 8).
      - apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
        rewrite P_4 by (rewrite Udst; lia). rewrite P_3 by (rewrite Udst; lia). rewrite P_2 by lia. (lazymatch goal with |- ?G => let G' := eval unfold M1, st_m1 in G in change_no_check G' end).
        rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
      - (lazymatch goal with |- ?G => let G' := eval unfold st_frame in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    exists r5. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. exact RUN5. }
    repeat (split; [assumption|]).
    apply (regs_agree_trans _ regs r1); [eapply regs_agree_mono; [|exact AG1]; incl_l|].
    apply (regs_agree_trans _ r1 r2); [eapply regs_agree_mono; [|exact AG2]; incl_l|].
    apply (regs_agree_trans _ r2 r3); [eapply regs_agree_mono; [|exact AG3]; incl_l|].
    apply (regs_agree_trans _ r3 r4); [eapply regs_agree_mono; [|exact AG4]; incl_l|].
    eapply regs_agree_mono; [|exact AG5]. incl_l.
  Qed.
End STRUN.
End FPGen.
End AsDepotStoreR.
Module AsDepotRunS.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsDepotStore AsDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition store_W (sp S packp : word) (cellz dstz n : Z) : Z -> Prop :=
  wun (ivl (U sp - 80) 80) (wun (ivl (U packp) 8) (wun (ivl (U S) 8) (wun (ivl cellz 4) (ivl dstz n)))).

Section SUM.
  Variables (M : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v S packp blkd : word) (tot sz tag sov : Z) (bs : list byte).
  Hypothesis Hsp : (2 ^ 32 + 80 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hpack : (U sp <= U packp /\ U packp + 8 < 2 ^ 64)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + sz + 1 <= 2 ^ 32)%Z.
  Hypothesis HS : (U S + 2 ^ 20 <= 2 ^ 32)%Z.
  Hypothesis Hblk : (U S + 2 ^ 20 <= U blkd /\ U blkd + 2 ^ 23 <= U sp - 80)%Z.
  Hypothesis Hbs : length bs = Z.to_nat (8 * sz).
  Hypothesis Hfit : (tot mod 2 ^ 20 + sz < 2 ^ 20)%Z.

  #[local] Abbreviation MM := (st_mem M sp ra s0v s1v s2v s3v s4v s5v S packp blkd tot sz tag sov bs).
  #[local] Abbreviation dstz := (U blkd + 8 * (tot mod 2 ^ 20))%Z.
  #[local] Abbreviation cellz := (U S + 16 * (tot / 2 ^ 20) + 24)%Z.

  Lemma st_mem_sum :
    msum (store_W sp S packp cellz dstz (8 + 8 * sz)) M MM
    /\ rdn ASEGS MM S 8 = Some (LE8 (v_add (Z_to_bv 64 tot) (Z_to_bv 64 (sz + 1))))
    /\ rdn ASEGS MM (st_cell S tot) 4 = Some (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 (sz + 1))))
    /\ rdn ASEGS MM packp 8 = Some (LE8 (Z_to_bv 64 (0 + st_full sov (sz + 1)))).
  Proof using Hfit Hbs Hblk HS Htot Hsz Hpack Hsp.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range packp) as Hpr. pose proof (u64_range blkd) as Hbr.
    destruct Hsp as [S1 S2]. destruct Hpack as [P1 P2]. destruct Htot as [T0 T32]. destruct Hblk as [BK1 BK2].
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : (0 <= tot mod 2 ^ 20 < 2 ^ 20)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Lbs : Z.of_nat (length bs) = (8 * sz)%Z) by (rewrite Hbs, Z2Nat.id by lia; reflexivity).
    assert (UspA : U (at_ sp (-64)) = (U sp - 64)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Udst : U (st_dst blkd tot) = dstz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Udst8 : U (at_ (st_dst blkd tot) 8) = (dstz + 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Ucell : U (st_cell S tot) = cellz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    set (M1 := st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp).
    set (M2 := sa_mem M1 (at_ sp (-64)) (0x8c4fc : word) packp S (at_ sp (-64)) tot (sz + 1)).
    set (M3 := wbytes M2 (st_dst blkd tot) (LE8 (st_hdr sz tag))).
    set (M4 := wbytes M3 (at_ (st_dst blkd tot) 8) bs).
    assert (E1 : msum (wun (ivl (U sp - 64) 64) (ivl (U packp) 8)) M M1).
    { apply msum_outside; [| apply st_m1_grows]. intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). apply st_m1_outside; try lia; unfold wun, ivl in Hx; lia. }
    assert (E2 : msum (wun (ivl (U sp - 80) 24) (ivl (U S) 8)) M1 M2).
    { apply msum_outside; [| apply sa_mem_grows]. intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end). apply sa_mem_outside; rewrite ?UspA; try lia; unfold wun, ivl in Hx; lia. }
    assert (E3 : msum (ivl dstz 8) M2 M3).
    { (lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end). eapply msum_weaken; [| apply msum_wbytes; rewrite length_N_to_le_bytes, Udst; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      intros z Hz. unfold ivl in *. rewrite length_N_to_le_bytes, Udst in Hz. cbn in Hz. lia. }
    assert (E4 : msum (ivl (dstz + 8) (8 * sz)) M3 M4).
    { (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). eapply msum_weaken; [| apply msum_wbytes; rewrite Lbs, Udst8; lia]. intros z Hz. unfold ivl in *. rewrite Lbs, Udst8 in Hz. lia. }
    assert (E5 : msum (wun (ivl cellz 4) (ivl (U packp) 8)) M4 MM).
    { apply msum_outside; [| apply st_m5_grows]. intros x Hx. apply st_m5_outside; rewrite ?Ucell; try lia; unfold wun, ivl in Hx; lia. }
    split.
    { eapply msum_weaken; [| exact (msum_trans _ _ _ _ _ (msum_trans _ _ _ _ _ (msum_trans _ _ _ _ _ (msum_trans _ _ _ _ _ E1 E2) E3) E4) E5)].
      (lazymatch goal with |- ?G => let G' := eval unfold store_W, wun, ivl in G in change_no_check G' end). intros z Hz. lia. }
    split.
    { apply (msum_rdn_eq ASEGS _ M4 MM _ _ _ E5); [lia | (lazymatch goal with |- ?G => let G' := eval unfold wun, ivl in G in change_no_check G' end); intros z Hz; lia |].
      apply (msum_rdn_eq ASEGS _ M3 M4 _ _ _ E4); [lia | (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end); intros z Hz; lia |].
      apply (msum_rdn_eq ASEGS _ M2 M3 _ _ _ E3); [lia | (lazymatch goal with |- ?G => let G' := eval unfold ivl in G in change_no_check G' end); intros z Hz; lia |].
      (lazymatch goal with |- ?G => let G' := eval unfold M2, sa_mem in G in change_no_check G' end). rewrite rdn_wbytes_out; [apply rdn_wbytes_hit8; lia | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?UspA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    split.
    { (lazymatch goal with |- ?G => let G' := eval unfold st_mem, st_m5 in G in change_no_check G' end). rewrite rdn_wbytes_out; [| wd_lenlit; rewrite ?length_N_to_le_bytes, ?Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ..].
      apply (rdn_wbytes_hit ASEGS (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 (sz + 1))))). rewrite length_N_to_le_bytes, Ucell. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    (lazymatch goal with |- ?G => let G' := eval unfold st_mem, st_m5 in G in change_no_check G' end). apply rdn_wbytes_hit8. lia.
  Qed.
End SUM.
End FPGen.
End AsDepotRunS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsDepotHit AsDepotLock AsDepotIns OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4.AsDepotStore AsDepotStoreR OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum AsDepotRunT AsDepotRunH AsDepotRunS.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Definition SSW : word := Z_to_bv 64 1938504.            (* [comment removed for export] *)
Definition ins_W (P D b nd : word) (cellz dstz n : Z) : Z -> Prop :=
  wun (ivl (U P - 224) 112) (wun (ivl (U b) 4) (wun (ivl (U D + 4194304) 4) (wun (ivl (U nd) 16) (wun (ivl 1938504 8) (wun (ivl cellz 4) (ivl dstz n)))))).

Section INS.
  Variables (M rom : word -> option byte) (P ra D hsh blk tr blkd CF : word) (hd NIDS BIX sz tag tot sov : Z) (bs : list byte).
  Variables (s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v : word).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation Q := (at_ P (-112)).
  #[local] Abbreviation b := (Z_to_bv 64 (U D + 4 * BIX)).
  #[local] Abbreviation nd := (di_node blk NIDS).
  #[local] Abbreviation spS := (at_ Q (-32)).
  #[local] Abbreviation packp := (at_ Q (-24)).
  #[local] Abbreviation args := (at_ P (-104)).
  #[local] Abbreviation cellz := (1938504 + 16 * (tot / 2 ^ 20) + 24)%Z.
  #[local] Abbreviation dstz := (U blkd + 8 * (tot mod 2 ^ 20))%Z.
  Hypothesis H2 : getr regs 2 = Q.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0.
  Hypothesis H9 : getr regs 9 = D.
  Hypothesis H18 : getr regs 18 = b.
  Hypothesis H19 : getr regs 19 = hsh.
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 65535.
  Hypothesis H24 : getr regs 24 = Z_to_bv 64 (U D + 4194320).
  Hypothesis H25 : getr regs 25 = Z_to_bv 64 hd.
  Hypothesis HP : (2 ^ 32 + 224 <= U P /\ U P + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis HD : (U D mod 4 = 0 /\ U D + 0x500000 <= 2 ^ 32 /\ 1938504 + 65552 <= U D)%Z.
  Hypothesis HCF : (U CF + 244 <= 1938504)%Z.
  Hypothesis HBIX : (0 <= BIX < 2 ^ 20)%Z.
  Hypothesis Hhd : (0 <= hd < 2 ^ 31)%Z.
  Hypothesis Hn : (0 <= NIDS /\ NIDS + 1 < 2 ^ 31)%Z.
  Hypothesis Hblk : (U D + 0x440010 <= U blk /\ U blk + 2 ^ 20 <= U P - 224)%Z.
  Hypothesis Hblkd : (U D + 0x440010 <= U blkd /\ U blkd + 2 ^ 23 <= U P - 224 /\ (U blk + 2 ^ 20 <= U blkd \/ U blkd + 2 ^ 23 <= U blk))%Z.
  Hypothesis HtrP : (U P <= U tr /\ U tr + 8 * sz < 2 ^ 64)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + sz + 1 <= 2 ^ 32)%Z.
  Hypothesis Hsame : (tot / 2 ^ 20 = (tot + sz) / 2 ^ 20)%Z.
  Hypothesis Hsov : (0 <= sov < 2 ^ 32)%Z.
  Hypothesis Hbs : length bs = Z.to_nat (8 * sz).
  Hypothesis Rb : rdn ASEGS M b 4 = Some (LE4 (Z_to_bv 64 hd)).
  Hypothesis Rcnt : rdn ASEGS M (at_ D 0x400000) 4 = Some (LE4 (Z_to_bv 64 NIDS)).
  Hypothesis Rmap : rdn ASEGS M (Z_to_bv 64 (U D + 0x400010 + 8 * ((NIDS + 1) / 2 ^ 16))) 8 = Some (LE8 blk).
  Hypothesis Rsz : rdn ASEGS M (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz)).
  Hypothesis Rtag : rdn ASEGS M (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Hypothesis Rtr : rdn ASEGS M args 8 = Some (LE8 tr).
  Hypothesis Rws : rdn ASEGS M tr (length bs) = Some bs.
  Hypothesis Rtot : rdn ASEGS M SSW 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rblk : rdn ASEGS M (Z_to_bv 64 (U SSW + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkd).
  Hypothesis Rso : rdn ASEGS M (st_cell SSW tot) 4 = Some (LE4 (Z_to_bv 64 sov)).
  Hypothesis Rcfp : rdn ASEGS M (Z_to_bv 64 1045088) 8 = Some (LE8 CF).
  Hypothesis Rflag : rdn ASEGS M (at_ CF 240) 4 = Some (LE4 (Z_to_bv 64 0)).
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v); (-64, s6v); (-72, s7v); (-80, s8v); (-88, s9v)]%Z ->
    rdn ASEGS M (at_ P k) 8 = Some (LE8 v).
  Hypothesis SOKb : store_ok ASEGS M b 4 = true.
  Hypothesis SOKc : store_ok ASEGS M (at_ D 0x400000) 4 = true.
  Hypothesis SOKn : store_ok ASEGS M nd 16 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ P (-224)) 112 = true.
  Hypothesis SOKS : store_ok ASEGS M SSW 8 = true.
  Hypothesis SOKso : store_ok ASEGS M (st_cell SSW tot) 4 = true.
  Hypothesis SOKd : store_ok ASEGS M (st_dst blkd tot) (8 + length bs) = true.

  Lemma put_ins_run :
    exists r M', msteps ASEGS (mkst regs (0x8ec18 : word) M rom) (mkst r ra M' rom)
      /\ msum (ins_W P D b nd cellz dstz (8 + 8 * sz)) M M'
      /\ getr r 10 = Z_to_bv 64 (NIDS + 1) /\ getr r 2 = P /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ getr r 22 = s6v /\ getr r 23 = s7v /\ getr r 24 = s8v /\ getr r 25 = s9v
      /\ rdn ASEGS M' b 4 = Some (LE4 (Z_to_bv 64 (NIDS + 1)))
      /\ rdn ASEGS M' (at_ D 0x400000) 4 = Some (LE4 (v_add (Z_to_bv 64 NIDS) (Z_to_bv 64 1)))
      /\ rdn ASEGS M' nd 8 = Some (LE8 hsh) /\ rdn ASEGS M' (at_ nd 8) 4 = Some (LE4 (Z_to_bv 64 hd)) /\ rdn ASEGS M' (at_ nd 12) 4 = Some (LE4 (st_id tot))
      /\ rdn ASEGS M' SSW 8 = Some (LE8 (v_add (Z_to_bv 64 tot) (Z_to_bv 64 (sz + 1))))
      /\ rdn ASEGS M' (st_cell SSW tot) 4 = Some (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 (sz + 1))))
      /\ regs_agree (fun i : reg => In i put_clob) regs r.
  Proof using SOKd SOKso SOKS Hstk SOKn SOKc SOKb SL Rflag Rcfp Rso Rblk Rtot Rws Rtr Rtag Rsz Rmap Rcnt Rb Hbs Hsov Hsame Htot Htag Hsz HtrP Hblkd Hblk Hn Hhd HBIX HCF HD Hret HP H25 H24 H22 H19 H18 H9 H8 H2 bs tag CF tr.
    pose proof (u64_range P) as HPr. pose proof (u64_range D) as HDr. pose proof (u64_range blk) as Hbr. pose proof (u64_range blkd) as Hbdr.
    pose proof (u64_range tr) as Htrr. pose proof (u64_range CF) as HCr.
    destruct HP as [P1 P2]. destruct HD as (D4 & D32 & DS). destruct Hblk as [BK1 BK2]. destruct Hblkd as (BD1 & BD2 & BD3).
    destruct HtrP as [T1 T2]. destruct Htot as [T0 T32]. destruct Hn as [N0 N1].
    assert (USS : U SSW = 1938504%Z) by reflexivity.
    assert (UQ : U Q = (U P - 112)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UspS : U spS = (U P - 144)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Upk : U packp = (U P - 136)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Uargs : U args = (U P - 104)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Ub : U b = (U D + 4 * BIX)%Z) by (rewrite u_Z2bv by lia; reflexivity).
    assert (M16 : (0 <= (NIDS + 1) mod 2 ^ 16 < 2 ^ 16)%Z) by (apply Z.mod_pos_bound; lia).
    assert (Und : U nd = (U blk + 16 * ((NIDS + 1) mod 2 ^ 16))%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold di_node in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Un8 : U (at_ nd 8) = (U nd + 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Un12 : U (at_ nd 12) = (U nd + 12)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (UcA : U (at_ D 0x400000) = (U D + 4194304)%Z) by (rewrite at_u by lia; reflexivity).
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : (0 <= tot mod 2 ^ 20 /\ tot mod 2 ^ 20 + sz < 2 ^ 20)%Z).
    { pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as E1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as B1.
      pose proof (Z.div_mod (tot + sz) (2 ^ 20) ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (tot + sz) (2 ^ 20) ltac:(lia)) as B2.
      rewrite <- Hsame in E2. lia. }
    assert (Lbs : Z.of_nat (length bs) = (8 * sz)%Z) by (rewrite Hbs, Z2Nat.id by lia; reflexivity).
    assert (Ucell : U (st_cell SSW tot) = cellz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite USS; rewrite u_Z2bv by lia; reflexivity).
    assert (Udst : U (st_dst blkd tot) = dstz) by ((lazymatch goal with |- ?G => let G' := eval unfold st_dst in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    (* [comment removed for export] *)
    destruct (put_head M rom P D hsh blk hd NIDS BIX regs H2 H8 H9 H18 H19 H22 H24 H25 ltac:(lia) (conj D4 D32) HBIX Hhd (conj N0 N1)
                ltac:(lia) Rb SOKb)
      as (r1 & M1 & RUN1 & SH & AT & RcntH & AG1).
    { eapply (store_ok_sub ASEGS M (at_ P (-224)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { exact Rcnt. } { exact SOKc. } { exact Rmap. }
    { eapply (store_ok_sub ASEGS M nd _ 16); [lia | exact SOKn | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct AT as (A1 & A2 & A8 & A10 & A11 & A12 & A9 & A18 & A21 & A23 & RhshH & RraH & Rs0H).
    assert (THRU1 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U a + Z.of_nat n <= U P - 160 \/ U P - 112 <= U a)%Z -> (U a + Z.of_nat n <= U D \/ U D + 0x440010 <= U a)%Z ->
              (U a + Z.of_nat n <= U nd \/ U nd + 8 <= U a)%Z -> rdn ASEGS M a n = Some v -> rdn ASEGS M1 a n = Some v).
    { intros a n v B1 X1 X2 X3 Hr. apply (msum_rdn_eq ASEGS _ M M1 _ _ _ SH B1); [| exact Hr].
      intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold head_W, wun, ivl in G in change_no_check G' end). rewrite Ub. lia. }
    (* [comment removed for export] *)
    destruct (st_run M1 rom spS (0x8e7c4 : word) SSW args packp tr blkd nd nd b (getr r1 19) (getr r1 20) (getr r1 21) sz tag tot sov bs r1
                A1 A2 A8 A9 A18 eq_refl eq_refl eq_refl A10 A11 A12
                ltac:(rewrite UspS; lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold ret_ok in G in change_no_check G' end); apply bv_eq; vm_compute; reflexivity)
                ltac:(rewrite UspS, Uargs; lia) ltac:(rewrite UspS, Upk, Uargs; lia) ltac:(rewrite UspS, Upk; lia)
                Hsz Htag (conj T0 T32) Hsame Hsov ltac:(rewrite USS; split; [reflexivity | lia]) ltac:(rewrite USS, UspS; lia) Hbs)
      as (r2 & RUN2 & B10 & B2 & B1 & B8 & B9 & B18 & B19 & B20 & B21 & AG2).
    { apply THRU1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rsz]. }
    { apply THRU1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rtag]. }
    { apply THRU1; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtr]. }
    { apply THRU1; [rewrite Lbs; lia | rewrite Lbs; lia | rewrite Lbs; lia | rewrite Lbs; lia | exact Rws]. }
    { apply THRU1; [rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtot]. }
    { apply THRU1; [rewrite USS, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rblk]. }
    { apply THRU1; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rso]. }
    { apply (msum_store_ok ASEGS _ M M1 _ _ SH). rewrite at_at. eapply (store_ok_sub ASEGS M (at_ P (-224)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { apply (msum_store_ok ASEGS _ M M1 _ _ SH). eapply (store_ok_sub ASEGS M (at_ P (-224)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | rewrite Upk, at_u by lia; lia | rewrite Upk, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact (msum_store_ok ASEGS _ M M1 _ _ SH SOKS). }
    { exact (msum_store_ok ASEGS _ M M1 _ _ SH SOKso). }
    { exact (msum_store_ok ASEGS _ M M1 _ _ SH SOKd). }
    set (M2 := st_mem M1 spS (0x8e7c4 : word) nd nd b (getr r1 19) (getr r1 20) (getr r1 21) SSW packp blkd tot sz tag sov bs) in *.
    destruct (st_mem_sum M1 spS (0x8e7c4 : word) nd nd b (getr r1 19) (getr r1 20) (getr r1 21) SSW packp blkd tot sz tag sov bs
                ltac:(rewrite UspS; lia) ltac:(rewrite UspS, Upk; lia) Hsz (conj T0 T32) ltac:(rewrite USS; lia) ltac:(rewrite USS, UspS; lia) Hbs ltac:(lia))
      as (SS & RtotS & RsoS & RpkS).
    fold M2 in SS, RtotS, RsoS, RpkS.
    assert (THRU2 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U a + Z.of_nat n <= U P - 224 \/ U P - 128 <= U a)%Z -> (U a + Z.of_nat n <= 1938504 \/ 1938504 + 8 <= U a)%Z ->
              (U a + Z.of_nat n <= cellz \/ cellz + 4 <= U a)%Z -> (U a + Z.of_nat n <= dstz \/ dstz + 8 + 8 * sz <= U a)%Z ->
              rdn ASEGS M1 a n = Some v -> rdn ASEGS M2 a n = Some v).
    { intros a n v B0 X1 X2 X3 X4 Hr. apply (msum_rdn_eq ASEGS _ M1 M2 _ _ _ SS B0); [| exact Hr].
      intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold store_W, wun, ivl in G in change_no_check G' end). rewrite USS, UspS, Upk. lia. }
    pose proof (msum_trans _ _ _ _ _ SH SS) as S12.
    (* [comment removed for export] *)
    assert (NI2 : forall i : reg, In i [23] -> ~ In i [1; 2; 5; 6; 8; 9; 10; 11; 12; 13; 14; 15; 18; 19; 20; 21]).
    { intros i Hi Hx. cbn [In] in Hi, Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    destruct (put_tail M2 rom P ra nd b (st_id tot) (Z_to_bv 64 hd) (Z_to_bv 64 (NIDS + 1)) CF (0 + st_full sov (sz + 1))
                s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v r2 B2 B8 B9 B10 B18 ltac:(rewrite B21; exact A21)
                ltac:(rewrite (AG2 23%bv) by (apply NI2; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto); exact A23)
                ltac:(lia) Hret ltac:(rewrite Und; lia) ltac:(rewrite Ub, Und; lia)
                ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); destruct (sz + 1 + sov =? 1048576)%Z; lia) ltac:(lia) RpkS)
      as (r3 & M3 & RUN3 & ST & C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & Rlink & Rsid & Rbk & AG3).
    { apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact RraH]. }
    { apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rs0H]. }
    { apply THRU2; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      apply THRU1; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rcfp]. }
    { apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      apply THRU1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Rflag]. }
    { apply (msum_store_ok ASEGS _ M M2 _ _ S12). eapply (store_ok_sub ASEGS M nd _ 16); [lia | exact SOKn | rewrite Un12; lia | rewrite Un12; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { apply (msum_store_ok ASEGS _ M M2 _ _ S12). eapply (store_ok_sub ASEGS M nd _ 16); [lia | exact SOKn | rewrite Un8; lia | rewrite Un8; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact (msum_store_ok ASEGS _ M M2 _ _ S12 SOKb). }
    { apply (msum_store_ok ASEGS _ M M2 _ _ S12). rewrite at_at. eapply (store_ok_sub ASEGS M (at_ P (-224)) _ 112); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. }
    { intros k v Hin.
      assert (K : (-88 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply THRU2; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] |].
      apply THRU1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact (SL k v Hin)]. }
    assert (THRU3 : forall (a : word) (n : nat) v, (U a + Z.of_nat n <= 2 ^ 64)%Z ->
              (U a + Z.of_nat n <= U P - 160 \/ U P - 144 <= U a)%Z -> (U a + Z.of_nat n <= U nd + 8 \/ U nd + 16 <= U a)%Z ->
              (U a + Z.of_nat n <= U b \/ U b + 4 <= U a)%Z -> rdn ASEGS M2 a n = Some v -> rdn ASEGS M3 a n = Some v).
    { intros a n v B0 X1 X2 X3 Hr. apply (msum_rdn_eq ASEGS _ M2 M3 _ _ _ ST B0); [| exact Hr].
      intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold tail_W, wun, ivl in G in change_no_check G' end). lia. }
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    split.
    { eapply msum_weaken; [| exact (msum_trans _ _ _ _ _ S12 ST)]. (lazymatch goal with |- ?G => let G' := eval unfold ins_W, head_W, store_W, tail_W, wun, ivl in G in change_no_check G' end). rewrite USS, UspS, Upk. intros z Hz. lia. }
    repeat (split; [assumption|]).
    split. { apply THRU3; [rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA, Ub; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
             apply THRU2; [rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite UcA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact RcntH]. }
    split. { apply THRU3; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ub; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
             apply THRU2; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact RhshH]. }
    split; [exact Rlink|]. split; [exact Rsid|].
    split. { apply THRU3; [rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite USS, Ub; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact RtotS]. }
    split. { apply THRU3; [rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Ucell, Ub; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact RsoS]. }
    apply (regs_agree_trans _ regs r1 r3 AG1). apply (regs_agree_trans _ r1 r2 r3); [ra_pc AG2 | exact AG3].
  Qed.
End INS.
End FPGen.
