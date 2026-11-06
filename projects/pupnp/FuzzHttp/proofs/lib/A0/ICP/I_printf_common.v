(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Ceiling Arr.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts ATac IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import StoreFast.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ICP Require Import IcptKit F_irt F_rip I_printf_lib.
Import ListNotations.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Local Ltac mem_after_store ::= cbv beta; try rewrite le1_unsigned8; mem_after_store_fast.

Lemma align8_walk0 : forall z, (0 <= z < 2^47)%Z -> Z.land (2147450880 + Z.shiftr z 3) 18446744073709551608 = (sh z - sh z mod 8)%Z.
Proof. intros z Hz. rewrite <- (align8_walk z Hz). rewrite shiftr3_div. rewrite Z.mod_small; [reflexivity|]. Z.div_mod_to_equations. lia. Qed.
Tactic Notation "probe8_reg0" constr(r) constr(RD) constr(x) ident(w) ident(Pw) :=
  let a := reg_val r in
  lazymatch a with Z_to_bv 64 ?e =>
    lazymatch type of RD with sh_readable ?mm ?A ?nn =>
      destruct (probe8_at mm A nn x e RD ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(first [ apply align8_walk0; lia | apply align8_walk; lia | apply align8_walk'; lia ])) as [w Pw]
    end end.

Local Ltac zs ::= zstep; fix_lit_store; norm_sub.

Section PC.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (FMT : Z) (fstr : list byte).
  Hypothesis MI : mem_inv asegs m.
  Hypothesis ST : stk asegs m lo (bv_unsigned sp).
  Hypothesis LO : (lo <= bv_unsigned sp - 2320)%Z.
  Hypothesis KLO : (17594333495296 <= lo)%Z.
  Hypothesis GOT : rw_cells asegs m 696528 [C8 (Z_to_bv 64 735480)].
  Hypothesis SHB : rw_cells asegs m 735480 [C8 (Z_to_bv 64 2147450880)].
  Hypothesis A1 : a1 = Z_to_bv 64 FMT.
  Hypothesis FB : bytes_at asegs m FMT (fstr ++ [Z_to_bv 8 0]).
  Hypothesis NOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) fstr.
  Notation L := (Z.of_nat (length fstr)).
  Hypothesis FL : (1 <= L <= 62)%Z.
  Hypothesis FIMG : (0x10000 <= FMT /\ FMT + L + 1 <= 0x609000)%Z.
  Hypothesis ACCF : accessible m FMT (L + 1).
  Hypothesis RDF : sh_readable m FMT (L + 1).

  Notation W := [(bv_unsigned sp + -2320, bv_unsigned sp)]%Z.
  Notation SAVES := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Notation PAT := 12297829382473034410%Z.

  Definition INV (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -104) SAVES
    /\ (exists j0, rw_cells asegs mc (bv_unsigned sp + -2240) [CB 8 j0; C8 (Z_to_bv 64 (bv_unsigned sp + -120)); C8 a0])
    /\ stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ stk asegs mc lo (bv_unsigned sp + -2240)
    /\ munch W m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rw_cells asegs mc 696528 [C8 (Z_to_bv 64 735480)] /\ rw_cells asegs mc 735480 [C8 (Z_to_bv 64 2147450880)].

  Definition BL : Prop :=
    (0 <= lo /\ lo <= bv_unsigned sp - 2320 /\ 17594333495296 <= lo /\ bv_unsigned sp < 2^64
     /\ 65536 <= FMT /\ FMT + L + 1 <= 6328320 /\ 1 <= L <= 62
     /\ 8192 <= Z.shiftr FMT 3 /\ Z.shiftr FMT 3 <= Z.shiftr (FMT + L) 3 /\ Z.shiftr (FMT + L) 3 <= Z.shiftr FMT 3 + 8 /\ Z.shiftr (FMT + L) 3 <= 791039)%Z.
  #[using="m ST LO KLO FL FIMG"] Lemma BL_ok : BL.
  Proof.
    unfold BL. pose proof (bv_unsigned_in_range 64 sp) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64)%Z with (2^64)%Z in R.
    destruct ST as (L0 & _). rewrite !Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia.
  Qed.

  Ltac hide_sec :=
    change (?P) with (sf_hide P) in MI; change (?P) with (sf_hide P) in ST; change (?P) with (sf_hide P) in GOT;
    change (?P) with (sf_hide P) in SHB; change (?P) with (sf_hide P) in FB;
    change (?P) with (sf_hide P) in LO; change (?P) with (sf_hide P) in KLO.
  Ltac inv_open H := let j0 := fresh "j0" in destruct H as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
  Ltac prep IV :=
    inv_open IV;
    let B := fresh "B" in pose proof BL_ok as B; unfold BL in B;
    hide_sec.

  #[using="lo ST LO KLO FB FL FIMG"] Lemma fmt_rd : forall mc (i : Z) b, mem_inv asegs mc -> munch W m mc ->
    nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat i) = Some b -> (0 <= i)%Z ->
    ov_read_bytes asegs mc (wa (FMT + i)) 1 = Some [b].
  Proof.
    intros mc i b MIc MUc Hn Hi. pose proof BL_ok as B; unfold BL in B.
    eapply u8ro_read; [| exact Hn | exact Hi | reflexivity].
    eapply bytes_at_transport; [exact FB | exact MUc |]. rewrite length_app; cbn [length disjoint_from]. lia.
  Qed.

  Ltac fmt_read i b Hn :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      lazymatch goal with MUc : munch _ m mc, MIc : mem_inv _ mc |- _ =>
        let H := fresh "RD" in
        pose proof (fmt_rd mc i b MIc MUc ltac:(rewrite nth_error_app1 by lia; exact Hn) ltac:(lia)) as H
    end end.

  Ltac prem :=
    lazymatch goal with
    | |- evt _ _ _ => idtac
    | |- mem_inv _ _ => first [assumption | eassumption | idtac "prem: mem_inv"; fail]
    | |- context [bv_unsigned (Z_to_bv 64 _)] => rewrite !unsigned_lit by lia; prem
    | |- stk _ _ _ _ => first [assumption | eassumption | idtac "prem: stk"; fail]
    | |- ifind_byte _ _ = _ => first [eassumption | idtac "prem: ifind_byte"; fail]
    | |- rw_cells _ _ _ _ => first [eassumption | idtac "prem: rw_cells"; fail]
    | |- u8arr _ _ _ _ => first [eassumption | idtac "prem: u8arr"; fail]
    | |- bytes_at _ _ _ _ => first [eassumption | first [apply flags_bytes | apply jzt_bytes | apply ccss_bytes | apply aefg_bytes | apply dioux_bytes | apply cs_bytes | apply csb_bytes | apply ss_bytes | idtac "prem: bytes_at"; fail]; assumption]
    | |- Forall _ _ => first [exact flags_noz | exact jzt_noz | exact ccss_noz | exact aefg_noz | exact dioux_noz | exact cs_noz | exact csb_noz | exact ss_noz | assumption | idtac "prem: Forall"; fail]
    | |- _ = Z_to_bv 64 _ => first [reflexivity | idtac "prem: eq"; fail]
    | |- ?g => unfold sf_hide in *; first [lia | cbv; discriminate | cbn; lia | idtac "prem: other" g; fail]
    end.

  Ltac br CC := let K := fresh "K" in if_cases K; zify_cond K; try (exfalso; clear -K CC; lia); [clear K].

  Notation CONT Q x19v x21v mc dcs :=
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evt asegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) x19v (Z_to_bv 64 0x15411) x21v y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
             F (Z_to_bv 64 0x48b30) fc None mc (seg_rom asegs))) (only parsing).

  Definition INV0 (mc : word -> option byte) : Prop :=
    rw_cells asegs mc (bv_unsigned sp + -104) SAVES
    /\ (exists dj, rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj])
    /\ (exists j1, rw_cells asegs mc (bv_unsigned sp + -2240) [CB 24 j1])
    /\ stk asegs mc (bv_unsigned sp + -2176) (bv_unsigned sp + -104)
    /\ stk asegs mc lo (bv_unsigned sp + -2240)
    /\ munch W m mc /\ wmono asegs m mc /\ mem_inv asegs mc
    /\ rw_cells asegs mc 696528 [C8 (Z_to_bv 64 735480)] /\ rw_cells asegs mc 735480 [C8 (Z_to_bv 64 2147450880)].
  Ltac inv0_open H := let dj := fresh "dj" in let j1 := fresh "j1" in
    destruct H as (FR & (dj & FR0) & (j1 & FR1) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).

  Notation KHYP Q :=
    (forall mc dj, INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) [CB 40 dj] ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evt asegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 FMT) (Z_to_bv 64 0x15411) a2 y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
             F (Z_to_bv 64 0x48b30) fc None mc (seg_rom asegs))) (only parsing).

  #[using="lo ST LO KLO FL FIMG ACCF RDF"] Lemma fmt_facts : forall mc, munch W m mc -> accessible mc FMT (L + 1) /\ sh_readable mc FMT (L + 1).
  Proof.
    intros mc MUc. pose proof BL_ok as B; unfold BL in B.
    assert (CW : cwin FMT (L + 1)) by (unfold cwin; lia).
    assert (HO : forall s, (0x7fff7000 <= s < 0x10007fff8000)%Z -> outside W s) by (intros s Hs; cbn [outside]; lia).
    split; [eapply accessible_munch; [exact ACCF| exact MUc| exact CW| intros s Hs; apply HO; lia]
           | eapply sh_readable_munch; [exact RDF| exact MUc| exact CW| exact HO]].
  Qed.

  #[using="fstr ST LO KLO FB NOZ FL FIMG"] Lemma L_fc : forall Q, KHYP Q ->
    forall mc y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y20 y22 y25 y26 y27 y28 y29 y30 y31,
    INV0 mc ->
    evt asegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
                 y18 (Z_to_bv 64 FMT) y20 a2 y22 a0 (Z_to_bv 64 (bv_unsigned sp + -2184)) y25 y26 y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x48ac4) fc None mc (seg_rom asegs)).
  Proof.
    intros Q K. intros until y31. intros IV0. inv0_open IV0. pose proof BL_ok as B; unfold BL in B. hide_sec.
    do 3 zs.

    destruct (nth_error fstr 0) as [c0|] eqn:E0. 2:{ exfalso. apply nth_error_None in E0. lia. }
    assert (NZ0 : bv_unsigned c0 <> 0%Z) by (eapply (proj1 (Forall_forall _ _) NOZ); eapply nth_error_In; exact E0).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m mc, MIc : mem_inv _ mc |- _ =>
      pose proof (fmt_rd mc 0 c0 MIc MUc ltac:(rewrite nth_error_app1 by lia; exact E0) ltac:(lia)) as RD0; rewrite Z.add_0_r in RD0 end end.
    zs. zs. if_cases K4; zify_cond K4. { exfalso. clear - K4 NZ0. pose proof (bv_unsigned_in_range 8 c0). cbn in *. lia. } clear K4 RD0.
    do 17 zs.
    eapply K. 2:{ exact FR0. }
    split; [exact FR|]. split; [eexists; exact FR1|]. unfold sf_hide in *. repeat (split; [assumption|]). assumption.
  Qed.

  #[using="ST LO KLO FB NOZ FL FIMG ACCF RDF"] Lemma L_fwl : forall Q, KHYP Q ->
    forall mc (k : nat) (cur : Z) y1 y5 y6 y7 y9 y13 y14 y15 y16 y17 y18 y20 y22 y25 y26 y27 y28 y29 y30 y31,
    INV0 mc ->
    Z.to_nat (sh (FMT + L) - cur) = k -> (sh FMT <= cur < sh (FMT + L))%Z ->
    evt asegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9
                 (Z_to_bv 64 cur) (Z_to_bv 64 (2147450880 + Z.shiftr (FMT + L) 3)) (Z_to_bv 64 0) y13 y14 y15 y16 y17
                 y18 (Z_to_bv 64 FMT) y20 a2 y22 a0 (Z_to_bv 64 (bv_unsigned sp + -2184)) y25 y26 y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x493e0) fc None mc (seg_rom asegs)).
  Proof.
    intros Q K. intros until y31. intros IV0 Hk Hc. pose proof IV0 as IV00. inv0_open IV0. pose proof BL_ok as B; unfold BL in B.
    destruct (fmt_facts mc MU1) as (ACC1 & RDF1).
    revert cur y13 Hk Hc. induction k as [|k IH]; intros cur y13 Hk Hc; [exfalso; lia|].
    assert (SL : sh (FMT + L) = (2147450880 + Z.shiftr (FMT + L) 3)%Z) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; lia).
    pose proof (sh_div8 (FMT + L)) as D1.
    pose proof (ov_read1_mrd mc cur _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc FMT (L + 1) cur ACC1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply L_fc; [exact K| exact IV00].
  Qed.

  #[using="ST LO KLO FB NOZ FL FIMG ACCF RDF"] Lemma L_fws : forall Q, KHYP Q ->
    forall mc y1 y5 y6 y7 y9 y13 y14 y15 y16 y17 y18 y20 y22 y25 y26 y27 y28 y29 y30 y31,
    INV0 mc ->
    evt asegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9
                 (Z_to_bv 64 (2147450880 + Z.shiftr FMT 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (FMT + L) 3)) (Z_to_bv 64 (FMT + L)) y13 y14 y15 y16 y17
                 y18 (Z_to_bv 64 FMT) y20 a2 y22 a0 (Z_to_bv 64 (bv_unsigned sp + -2184)) y25 y26 y27 y28 y29 y30 y31)
             F (Z_to_bv 64 0x493c4) fc None mc (seg_rom asegs)).
  Proof.
    intros Q K. intros until y31. intros IV0. pose proof IV0 as IV00. inv0_open IV0. pose proof BL_ok as B; unfold BL in B.
    destruct (fmt_facts mc MU1) as (ACC1 & RDF1).
    destruct (acc_byte_rd mc FMT (L + 1) (FMT + L) ACC1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((FMT + L) mod 8) k2) by (pose proof (Z.mod_pos_bound (FMT + L) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply L_fc; [exact K| exact IV00].
    - eapply L_fwl; [exact K| exact IV00 | reflexivity |].
      rewrite !shiftr3_div in *. unfold sh, SHADOW_OFF.
      assert (0 <= FMT / 8 < 2^44 /\ 0 <= (FMT + L) / 8 < 2^44)%Z as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="fstr MI ST LO KLO GOT SHB A1 FB NOZ FL FIMG ACCF RDF"] Lemma L_entry : forall Q, KHYP Q ->
    evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x48a1c) fc None m (seg_rom asegs)).
  Proof.
    intros Q K.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof BL_ok as B; unfold BL in B.
    pose proof MI as MIc. pose proof FB as FBc. pose proof GOT as GOTc. pose proof SHB as SHBc. pose proof ST as ST0.
    hide_sec.
    subst a1.
    carve_frame 104%nat ST0.
    destruct (stk_split _ _ lo (bv_unsigned sp + -2176) _ ST0 ltac:(lia)) as [ST1 STM]. clear ST0.
    carve_frame 40%nat ST1. carve_frame 24%nat ST1.
    do 16 zstep. do 6 zstep. zstep.
    call istrlen_spec; [ exact MIc | rewrite unsigned_lit by lia; exact FBc | exact NOZ | ].
    zstep. zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear - K1 B. lia. } clear K1.
    zstep. zstep. if_cases K2; zify_cond K2. { exfalso. clear - K2 B. lia. } clear K2.
    do 4 zstep. replace (L + FMT)%Z with (FMT + L)%Z by lia. do 6 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => lazymatch goal with MUc : munch _ m mc |- _ =>
      destruct (fmt_facts mc MUc) as (ACC1 & RDF1) end end.
    assert (AW0 : forall z, (0 <= z < 2^47)%Z -> Z.land (2147450880 + Z.shiftr z 3) 18446744073709551608 = (sh z - sh z mod 8)%Z).
    { intros z Hz. rewrite <- (align8_walk z Hz). rewrite shiftr3_div. rewrite Z.mod_small; [reflexivity|]. Z.div_mod_to_equations. lia. }
    destruct (probe8_at _ FMT (L + 1) FMT _ RDF1 ltac:(lia) ltac:(lia) ltac:(lia) (AW0 FMT ltac:(lia))) as [w1 P1].
    destruct (probe8_at _ FMT (L + 1) (FMT + L)%Z _ RDF1 ltac:(lia) ltac:(lia) ltac:(lia) (AW0 (FMT + L)%Z ltac:(lia))) as [w2 P2].
    clear AW0.
    do 4 zstep. if_cases K5; zify_cond K5.
    - eapply L_fws; [exact K|].
      split; [exact FR|]. split; [eexists; exact FR0|]. split; [eexists; exact FR1|]. unfold sf_hide in *. repeat (split; [assumption|]). assumption.
    - eapply L_fc; [exact K|].
      split; [exact FR|]. split; [eexists; exact FR0|]. split; [eexists; exact FR1|]. unfold sf_hide in *. repeat (split; [assumption|]). assumption.
  Qed.

  Notation dcells1 :=
    ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).

  Definition lregs (y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 : word) (p aq : word) (y22 y28 y29 y30 y31 : word) :=
    mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp y9 y10 y11 y12 y13 y14 y15 y16 y17
        (Z_to_bv 64 10) p (Z_to_bv 64 0x15411) aq y22 (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
        (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31.

  #[using="FMT fstr ST LO KLO FL FIMG"] Lemma L_head : forall Q mc dcs p aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcells1 ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evt asegs Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x48b5c) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evt asegs Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 p aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x48b30) fc None mc (seg_rom asegs)).
  Proof.
    intros Q mc dcs p aq IV DIR SZ K. intros. unfold lregs. prep IV.
    destruct (rw_cells_forget _ _ _ _ DIR) as [dj DJ]. rewrite SZ in DJ. clear DIR.
    do 5 zs. do 5 zs.
    destruct (u8arr_of_chunk _ _ _ _ DJ) as (dj2 & DA & DL). cbn in DL. clear DJ.
    call imemset_specZ; [ exact MI1 | exact DA | rewrite DL; reflexivity | lia | lia | lia | cbv; discriminate | ].
    match goal with H : u8arr asegs ?mc _ _ |- _ => rewrite ?unsigned_lit in H by lia;
      apply rw_cells_of_u8arr in H; recell H 0%nat 1%nat (zcells0 : list cell); rename H into DIR end.
    zs.
    eapply K. 2:{ exact DIR. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  #[using="lo ST LO KLO FB NOZ FL FIMG"] Lemma fmt_char : forall mc (i : Z), mem_inv asegs mc -> munch W m mc -> (0 <= i < L)%Z ->
    exists b, nth_error fstr (Z.to_nat i) = Some b /\ bv_unsigned b <> 0%Z /\ (0 <= bv_unsigned b < 256)%Z /\
              ov_read_bytes asegs mc (wa (FMT + i)) 1 = Some [b].
  Proof.
    intros mc i MIc MUc Hi.
    destruct (nth_error fstr (Z.to_nat i)) as [b|] eqn:E. 2:{ exfalso. apply nth_error_None in E. lia. }
    exists b. split; [reflexivity|]. split.
    { eapply (proj1 (Forall_forall _ _) NOZ). eapply nth_error_In; exact E. }
    split. { pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
    eapply fmt_rd; [exact MIc | exact MUc | rewrite nth_error_app1 by lia; exact E | lia].
  Qed.

  #[using="lo ST LO KLO FB NOZ FL FIMG"] Lemma L_skip : forall Q mc (k : nat) (i : Z) aq,
    mem_inv asegs mc -> munch W m mc -> (0 <= i)%Z -> (i + Z.of_nat k <= L)%Z ->
    (forall j b, (Z.to_nat i <= j < Z.to_nat i + k)%nat -> nth_error fstr j = Some b -> bv_unsigned b <> 37%Z) ->
    (forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evt asegs Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + (i + Z.of_nat k))) aq y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x48b5c) fc None mc (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evt asegs Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x48b5c) fc None mc (seg_rom asegs)).
  Proof.
    intros Q mc k. induction k as [|k IH]; intros i aq MIc MUc Hi Hk NP K; intros.
    - specialize (K y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31).
      rewrite Z.add_0_r in K. exact K.
    - pose proof BL_ok as B; unfold BL in B. unfold lregs.
      destruct (fmt_char mc i MIc MUc ltac:(lia)) as (b & Hn & NZ & RB & RD).
      assert (NP0 : bv_unsigned b <> 37%Z) by (eapply NP; [|exact Hn]; lia).
      zs. zs. if_cases K1; zify_cond K1. { exfalso. clear -K1 NP0 RB. lia. }
      zs. if_cases K2; zify_cond K2. { exfalso. clear -K2 NZ RB. lia. }
      zs. zs. zs.
      replace (FMT + i + 1)%Z with (FMT + (i + 1))%Z by lia.
      eapply (IH (i + 1)%Z); [exact MIc | exact MUc | lia | lia | | ].
      { intros j b' Hj Hb'. eapply NP; [|exact Hb']. lia. }
      intros. replace (i + 1 + Z.of_nat k)%Z with (i + Z.of_nat (S k))%Z by lia. apply K.
  Qed.

  Definition dirA_ok (c : Z) : Prop :=
    ifind_byte c B_FLAGS = None /\ ifind_byte c B_JZT = None /\ (58 <= c < 256)%Z /\ c <> 108%Z /\ c <> 104%Z.

  Definition intconv (c : Z) : Prop := c = 100%Z \/ c = 117%Z.
  #[using="fstr"] Lemma cfacts : forall c, intconv c ->
    dirA_ok c /\ ifind_byte c B_CCSS = None /\ ifind_byte c B_AEFG = None
    /\ (exists ix, ifind_byte c B_DIOUX = Some ix) /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z.
  Proof. intros c [-> | ->]; repeat split; try (cbv; reflexivity); try lia; eexists; cbv; reflexivity. Qed.

  Definition sconv (c : Z) : Prop := c = 115%Z.
  #[using="fstr"] Lemma sfacts : forall c, sconv c ->
    dirA_ok c /\ (58 <= c < 256)%Z /\ c <> 109%Z /\ c <> 110%Z
    /\ ifind_byte c B_CCSS = Some 2%nat /\ ifind_byte c B_CS = None /\ ifind_byte c B_CSB = Some 1%nat /\ ifind_byte c B_SS = Some 0%nat.
  Proof. intros c ->; repeat split; try (cbv; reflexivity); lia. Qed.

  #[using="Type"] Lemma istrchr_res_none : forall A str c, ifind_byte c str = None -> istrchr_res A str c = 0%Z.
  Proof. intros A str c H. unfold istrchr_res. rewrite H. reflexivity. Qed.

  Notation dcellsA p bc :=
    ([C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 18446744073709551615); C8 (Z_to_bv 64 p); C8 (Z_to_bv 64 (p + 2));
     C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 bc; CB 3 (repeat (Z_to_bv 8 0) 3)]) (only parsing).

  #[using="ST LO KLO FB FL FIMG"] Lemma L_dirA : forall Q mc (i : Z) aq b37 bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    (0 <= i)%Z -> (i + 2 <= L)%Z ->
    nth_error fstr (Z.to_nat i) = Some b37 -> bv_unsigned b37 = 37%Z ->
    nth_error fstr (Z.to_nat (i + 1)) = Some bc -> dirA_ok (bv_unsigned bc) ->
    (forall mc', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
       forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
       evt asegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15411) aq (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                           F (Z_to_bv 64 0x48cd8) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evt asegs Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i)) aq y22 y28 y29 y30 y31)
                       F (Z_to_bv 64 0x48b5c) fc None mc (seg_rom asegs)).
  Proof.
    intros Q mc i aq b37 bc IV DIR Hi HiL H37 E37 Hc HC K. intros. unfold lregs. prep IV.
    destruct HC as (NF1 & NF2 & CR & N108 & N104).
    pose proof (conj CR (conj N108 N104)) as CC.
    fmt_read i b37 H37. zs. clear RD. cbv beta. rewrite E37. zs. br CC.
      zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta.
    zs. br CC.
      zs. br CC.
    zs. zs. zs. br CC.
      zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply flags_bytes; assumption | exact flags_noz | reflexivity | clear -CC; lia | ].
    rewrite (istrchr_res_none _ _ _ NF1).
      zs. zs. zs. br CC.
    replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
      zs. replace (FMT + (i + 1) + 1 + -1)%Z with (FMT + (i + 1))%Z by lia.
    zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. br CC.
      zs. zs. br CC.
      zs. fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    call istrchr_spec; [ eassumption | apply jzt_bytes; assumption | exact jzt_noz | reflexivity | clear -CC; lia | ].
    rewrite (istrchr_res_none _ _ _ NF2).
      fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. br CC.
      zs. zs. br CC. zs. zs. br CC.
      fmt_read (i + 1)%Z bc Hc. zs. clear RD. cbv beta. zs. zs. zs.
    zs. br CC.
    replace (FMT + (i + 1) + 1)%Z with (FMT + i + 2)%Z by lia. replace (FMT + (i + 1))%Z with (FMT + i + 1)%Z by lia.
    eapply K. 2:{ match goal with H : rw_cells asegs _ (bv_unsigned sp + -2216) _ |- _ => exact H end. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  #[using="ST LO KLO FL FIMG"] Lemma L_dirB : forall Q mc (i : Z) aq bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> intconv (bv_unsigned bc) ->
    (forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evt asegs Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 (bv_unsigned aq + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x48b28) fc None mc' (seg_rom asegs))) ->
    forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    evt asegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15411) aq (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x48cd8) fc None mc (seg_rom asegs)).
  Proof.
    intros Q mc i aq bc IV DIR Hi HiL HC K. intros. prep IV.
    destruct (cfacts _ HC) as (_ & NF3 & NF4 & (ix & HF) & CR & N109 & N110).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
      zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
      zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
      zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF3).
      zs. cbv beta. zs. br CC.
      zs. zs. zs. zs. zs.
    chunk_split DIR 8%nat DIR2. chunk_split DIR2 1%nat DIR3.
    call fgvs_specq. all: prem.
      zs. zs. zs. br CC.
      zs. cbv beta. zs. zs. br CC.
      zs. zs. br CC. zs. br CC.
      zs. zs. zs.
    call istrchr_spec. all: prem.
    rewrite (istrchr_res_none _ _ _ NF4).
    zs. br CC.
      zs. zs. zs. br CC. zs. zs. br CC. zs. zs. br CC.
      zs.
    chunk_join DIR DIR2. chunk_join DIR DIR3.
    unfold lregs in K. eapply K. 2:{ exact DIR. } 2:{ reflexivity. }
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  Ltac norm_stk H tgt :=
    lazymatch type of H with stk _ _ _ ?hi =>
      replace hi with tgt in H by (cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Pos.add Pos.mul]; lia) end.

  Notation POST := (printf_common_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m).

  #[using="ST LO KLO FB FL FIMG"] Lemma L_last : forall mc aq,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcells1 ->
    forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
    evt asegs POST (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + L)) aq y22 y28 y29 y30 y31)
                          F (Z_to_bv 64 0x48b5c) fc None mc (seg_rom asegs)).
  Proof.
    intros mc aq IV DIR. intros. unfold lregs. prep IV.
    assert (HL : nth_error (fstr ++ [Z_to_bv 8 0]) (Z.to_nat L) = Some (Z_to_bv 8 0)) by (rewrite nth_error_app2, Nat2Z.id, Nat.sub_diag by lia; reflexivity).
    assert (CC : True) by exact I.
    pose proof (fmt_rd mc L (Z_to_bv 8 0) MI1 MU1 HL ltac:(lia)) as RD.
    zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs. br CC.
      zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC. zs.
      zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
      clear RD. zs. do 13 zs. zs. zs.

    pose proof (stk_release _ _ _ _ _ ST1 FRL ltac:(lia)) as SK1. norm_stk SK1 (bv_unsigned sp + -2216)%Z.
    pose proof (stk_release _ _ _ _ _ SK1 DIR ltac:(lia)) as SK2. norm_stk SK2 (bv_unsigned sp + -2176)%Z.
    pose proof (stk_merge _ _ _ _ _ SK2 STM ltac:(lia)) as SK3.
    pose proof (stk_release _ _ _ _ _ SK3 FRT ltac:(lia)) as SK4. norm_stk SK4 (bv_unsigned sp).
    replace (bv_unsigned sp + -2320)%Z with (bv_unsigned sp - 2320)%Z in MU1 by lia.
    finish.
  Qed.

  #[using="FMT MI ST LO KLO GOT SHB A1 FB NOZ FL FIMG ACCF RDF"] Theorem printf_common_int1 : forall pre b37 bc post,
    fstr = pre ++ b37 :: bc :: post ->
    Forall (fun b : byte => bv_unsigned b <> 37%Z) pre -> Forall (fun b : byte => bv_unsigned b <> 37%Z) post ->
    bv_unsigned b37 = 37%Z -> intconv (bv_unsigned bc) -> post <> [] ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x48a1c) fc None m (seg_rom asegs)).
  Proof.
    intros pre b37 bc post EF NP1 NP2 E37 HC NE.
    assert (LEN : length fstr = (length pre + 2 + length post)%nat) by (rewrite EF, length_app; cbn; lia).
    assert (NE' : (1 <= length post)%nat) by (destruct post; [congruence | cbn; lia]).
    set (np := Z.of_nat (length pre)).
    eapply L_entry. intros mc dj IV DIR. intros.
    eapply (L_head _ mc [CB 40 dj]); [exact IV | exact DIR | reflexivity |]. clear mc dj IV DIR. intros mc IV DIR. intros.
    replace (Z_to_bv 64 FMT) with (Z_to_bv 64 (FMT + 0)) by (f_equal; lia).
    pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
    eapply (L_skip _ mc (length pre) 0); [exact MIc | exact MUc | lia | lia | |].
    { intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP1). eapply nth_error_In. rewrite EF, nth_error_app1 in Hb by lia. exact Hb. }
    clear MUc MIc. intros. rewrite Z.add_0_l.
    eapply (L_dirA _ mc np _ b37 bc); [exact IV | exact DIR | lia | lia | | exact E37 | | exact (proj1 (cfacts _ HC)) |].
    { rewrite EF. replace (Z.to_nat np) with (length pre) by lia. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    { rewrite EF. replace (Z.to_nat (np + 1)) with (length pre + 1)%nat by lia. rewrite nth_error_app2 by lia.
      replace (length pre + 1 - length pre)%nat with 1%nat by lia. reflexivity. }
    clear mc IV DIR. intros mc IV DIR. intros.
    eapply (L_dirB _ mc np); [exact IV | exact DIR | lia | lia | exact HC |].
    clear mc IV DIR. intros mc dcs IV DIR SZ. intros. unfold lregs.

    destruct (nth_error post 0) as [b2|] eqn:E2. 2:{ exfalso. apply nth_error_None in E2. lia. }
    assert (H2 : nth_error fstr (Z.to_nat (np + 2)) = Some b2).
    { rewrite EF. replace (Z.to_nat (np + 2)) with (length pre + 2)%nat by lia. rewrite nth_error_app2 by lia.
      replace (length pre + 2 - length pre)%nat with 2%nat by lia. exact E2. }
    pose proof IV as IV'. prep IV'.
    destruct (fmt_char mc (np + 2) MI1 MU1 ltac:(lia)) as (b2' & Hb2 & NZ2 & RB2 & RD2). rewrite H2 in Hb2. injection Hb2 as <-.
    replace (FMT + np + 2)%Z with (FMT + (np + 2))%Z by lia.
    zs. cbv beta. zs. assert (CC : True) by exact I. br NZ2.

    eapply (L_head _ mc dcs); [exact IV | exact DIR | exact SZ |].
    clear mc IV DIR SZ FRT FRL STM ST1 MU1 WM1 MI1 GOT1 SHB1 RD2. intros mc IV DIR. intros.
    pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
    eapply (L_skip _ mc (length post) (np + 2)); [exact MIc | exact MUc | lia | lia | |].
    { intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP2). eapply nth_error_In with (n := (j - (length pre + 2))%nat).
      rewrite EF, nth_error_app2 in Hb by lia.
      replace (j - length pre)%nat with (S (S (j - (length pre + 2)))) in Hb by lia. exact Hb. }
    intros. replace (np + 2 + Z.of_nat (length post))%Z with L by lia.
    eapply L_last; [exact IV | exact DIR].
  Qed.

  Variables (Sa : Z) (sstr : list byte).
  Hypothesis LG : rw_cells asegs m 696536 [C8 (Z_to_bv 64 738792); C8 (Z_to_bv 64 738800); C8 (Z_to_bv 64 738784)].
  Hypothesis LC : rw_cells asegs m 738784 [C8 (Z_to_bv 64 140737488355327); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  Hypothesis VAQ : rw_cells asegs m (bv_unsigned a2) [C8 (Z_to_bv 64 Sa)].
  Hypothesis SEPV : (bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z.
  Hypothesis SSTR : bytes_at asegs m Sa (sstr ++ [Z_to_bv 8 0]).
  Hypothesis SNOZ : Forall (fun b : byte => bv_unsigned b <> 0%Z) sstr.
  Notation LS := (Z.of_nat (length sstr)).
  Notation NS := (Z.of_nat (length sstr) + 1)%Z.
  Hypothesis SEPS : (Sa + NS <= bv_unsigned sp - 2320 \/ bv_unsigned sp <= Sa)%Z.
  Hypothesis WINS : cwin Sa NS.
  Hypothesis WIN2S : (Sa + NS < 2^47)%Z.
  Hypothesis SPOS : (0 < Sa)%Z.
  Hypothesis ACCS : accessible m Sa NS.
  Hypothesis RDS : sh_readable m Sa NS.
  Hypothesis NSZ : (NS <= 2^43)%Z.

  Definition INVS (mc : word -> option byte) : Prop :=
    INV mc /\ (rw_cells asegs mc 696536 [C8 (Z_to_bv 64 738792); C8 (Z_to_bv 64 738800); C8 (Z_to_bv 64 738784)]
               /\ rw_cells asegs mc 738784 [C8 (Z_to_bv 64 140737488355327); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)])
    /\ accessible mc Sa NS /\ sh_readable mc Sa NS
    /\ bytes_at asegs mc Sa (sstr ++ [Z_to_bv 8 0]) /\ rw_cells asegs mc (bv_unsigned a2) [C8 (Z_to_bv 64 Sa)].

  Definition BLS : Prop :=
    (1 <= NS /\ NS <= 2^43 /\ 0 < Sa /\ Sa + NS < 2^47
     /\ 0 <= Z.shiftr Sa 3 < 2^44 /\ 0 <= Z.shiftr (Sa + NS + -1) 3 < 2^44
     /\ bv_unsigned sp <= bv_unsigned a2 /\ bv_unsigned a2 + 8 <= 2^64)%Z.
  #[using="lo fstr LO KLO SEPV WINS WIN2S SPOS NSZ"] Lemma BLS_ok : BLS.
  Proof. unfold BLS. destruct WINS as [Hn W]. rewrite !Z.shiftr_div_pow2 by lia. Z.div_mod_to_equations. lia. Qed.

  #[using="FMT fstr ST LO KLO FL FIMG LG LC VAQ SEPV SSTR SEPS WINS WIN2S SPOS ACCS RDS NSZ"] Lemma invs_of : forall mc, INV mc -> INVS mc.
  Proof.
    intros mc IV. pose proof IV as (FRT & (j0 & FRL) & STM & ST1 & MU1 & WM1 & MI1 & GOT1 & SHB1).
    pose proof BLS_ok as B. unfold BLS in B. pose proof BL_ok as B0. unfold BL in B0.
    assert (HO : forall s, (0x7fff7000 <= s < 0x10007fff8000)%Z -> outside W s) by (intros s Hs; cbn [outside]; lia).
    split; [exact IV|].
    split. { split; (eapply rw_cells_transport; [first [exact LG | exact LC] | exact MU1 | exact WM1 |]; cbn [disjoint_from cells_size csize Nat.add]; lia). }
    split. { eapply accessible_munch; [exact ACCS | exact MU1 | exact WINS | intros s Hs; apply HO; lia]. }
    split. { eapply sh_readable_munch; [exact RDS | exact MU1 | exact WINS | exact HO]. }
    split. { eapply bytes_at_transport; [exact SSTR | exact MU1 |]. rewrite length_app. cbn [length disjoint_from]. lia. }
    eapply rw_cells_transport; [exact VAQ | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Nat.add]. lia.
  Qed.

  Ltac preps IV :=
    let IVS := fresh "IVS" in pose proof (invs_of _ IV) as IVS;
    destruct IVS as (_ & (LG1 & LC1) & ACS1 & RDS1 & SSTR1 & VAQ1);
    prep IV;
    let B := fresh "BS" in pose proof BLS_ok as B; unfold BLS in B;
    change (?P) with (sf_hide P) in SEPS; change (?P) with (sf_hide P) in SEPV;
    change (?P) with (sf_hide P) in SSTR; change (?P) with (sf_hide P) in NSZ.

  Ltac unland K :=
    change 18446744073709551615%Z with (Z.ones 64) in K; rewrite ?Z.land_ones in K by lia;
    change (2 ^ 64)%Z with 18446744073709551616%Z in K.

  Definition KS (Q : machine_state -> Prop) (i : Z) : Prop :=
    forall mc' dcs', INV mc' -> rw_cells asegs mc' (bv_unsigned sp + -2216) dcs' -> cells_size dcs' = 40%nat ->
       forall y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 y22 y28 y29 y30 y31,
       evt asegs Q (MS (lregs y1 y5 y6 y7 y9 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 (bv_unsigned a2 + 8)) y22 y28 y29 y30 y31)
                           F (Z_to_bv 64 0x48b28) fc None mc' (seg_rom asegs)).

  Definition sregs (i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word) :=
    mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 sp (Z_to_bv 64 (-1)) x10 x11 x12 x13 x14 x15 x16 x17
        (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15411) (Z_to_bv 64 (bv_unsigned a2 + 8)) x22 x23
        (Z_to_bv 64 (bv_unsigned sp + -2184)) (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) x28 x29 x30 x31.

  #[using="fstr ST LO KLO FL FIMG"] Lemma LS_X : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31,
    evt asegs Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x48ea8) fc None mc (seg_rom asegs)).
  Proof.
    intros Q i mc dcs K IV DIR SZ. intros. unfold sregs. prep IV.
    zs. zs. unfold KS, lregs in K. eapply K; [| exact DIR | exact SZ].
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  #[using="fstr ST LO KLO FL FIMG LG LC VAQ SEPV SSTR SEPS WINS WIN2S SPOS ACCS RDS NSZ"] Lemma LS_L : forall Q i mc dcs (k : nat) (c : Z), KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (NS <= 64)%Z -> Z.to_nat (sh (Sa + NS - 1) - c) = k -> (sh Sa <= c < sh (Sa + NS - 1))%Z ->
    forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 c) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3)) (Z_to_bv 64 0) x13 x14 x15 x16 x17
                              (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x48fb8) fc None mc (seg_rom asegs)).
  Proof.
    intros Q i mc dcs k c K IV DIR SZ N1 Hk Hc. intros. unfold sregs. pose proof IV as IV0. preps IV.
    revert c x13 Hk Hc. induction k as [|k IH]; intros c x13 Hk Hc; [exfalso; lia|].
    assert (SL : (sh (Sa + NS - 1) = 2147450880 + Z.shiftr (Sa + NS + -1) 3)%Z) by (unfold sh, SHADOW_OFF; rewrite shiftr3_div; replace (Sa + NS + -1)%Z with (Sa + NS - 1)%Z by lia; lia).
    pose proof (sh_div8 (Sa + NS - 1)) as D1.
    pose proof (ov_read1_mrd mc c _ ltac:(unfold sh, SHADOW_OFF in *; lia) ltac:(unfold sh, SHADOW_OFF in *; lia)
                  (acc_full_zero mc Sa NS c ACS1 ltac:(lia) ltac:(lia))) as RDc.
    zstep. cbv beta. zsimp. zstep. zstep. fold_lits. zstep. if_cases K1; zify_cond K1.
    - apply IH; lia.
    - zstep. zstep. if_cases K'; zify_cond K'. 2:{ exfalso. clear - K'. cbv in K'. lia. }
      eapply LS_X; eassumption.
  Qed.

  #[using="fstr ST LO KLO FL FIMG LG LC VAQ SEPV SSTR SEPS WINS WIN2S SPOS ACCS RDS NSZ"] Lemma LS_E : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    (NS <= 64)%Z ->
    forall x1 x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs Q (MS (sregs i x1 x5 x6 x7 (Z_to_bv 64 (2147450880 + Z.shiftr Sa 3)) (Z_to_bv 64 (2147450880 + Z.shiftr (Sa + NS + -1) 3))
                              (Z_to_bv 64 (Sa + NS + -1)) x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x48f9c) fc None mc (seg_rom asegs)).
  Proof.
    intros Q i mc dcs K IV DIR SZ N1. intros. unfold sregs. pose proof IV as IV0. preps IV.
    destruct (acc_byte_rd mc Sa NS (Sa + NS + -1) ACS1 ltac:(lia) ltac:(lia) ltac:(lia)) as (k2 & RD2 & CK2).
    unfold sh, SHADOW_OFF in RD2. rewrite <- shiftr3_div in RD2.
    zstep. rewrite (sxb_small k2) by lia. do 5 zstep.
    rewrite land7_mod8. rewrite (aip_zero ((Sa + NS + -1) mod 8) k2) by (pose proof (Z.mod_pos_bound (Sa + NS + -1) 8 ltac:(lia)); lia).
    zstep. if_cases K6; zify_cond K6.
    - zstep. zstep. if_cases K7; zify_cond K7. 2:{ exfalso. clear - K7. cbv in K7. lia. }
      eapply LS_X; eassumption.
    - eapply (LS_L Q i mc dcs); [exact K | exact IV0 | exact DIR | exact SZ | exact N1 | reflexivity |].
      rewrite !shiftr3_div in *. replace (Sa + NS - 1)%Z with (Sa + NS + -1)%Z by lia. unfold sh, SHADOW_OFF.
      assert (0 <= Sa / 8 < 2^44 /\ 0 <= (Sa + NS + -1) / 8 < 2^44)%Z as [B1 B2] by (split; Z.div_mod_to_equations; lia).
      rewrite ?Z.mod_small in K6 by lia. lia.
  Qed.

  #[using="fstr ST LO KLO FL FIMG LG LC VAQ SEPV SSTR SEPS WINS WIN2S SPOS ACCS RDS NSZ"] Lemma LS_C : forall Q i mc dcs, KS Q i -> INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) dcs -> cells_size dcs = 40%nat ->
    forall x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    evt asegs Q (MS (sregs i x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 Sa) (Z_to_bv 64 NS) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x48f4c) fc None mc (seg_rom asegs)).
  Proof.
    intros Q i mc dcs K IV DIR SZ. intros. unfold sregs. pose proof IV as IV0. preps IV.
    zstep. rewrite zb_lxor_ones by lia. zstep. if_cases K1; zify_cond K1. { exfalso. clear -K1 BS. lia. }
    zstep. zstep. zstep. if_cases K2; zify_cond K2.
    -
      assert (N1 : (64 < NS)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
      zstep. if_cases K3; zify_cond K3. 2:{ exfalso. clear -K3 BS. lia. }
      zstep. zstep. zstep.
      unfold sf_hide in LO, KLO.
      call rip_spec; [ exact MI1 | exact ST1 | lia | lia | lia | split; assumption | split; assumption | reflexivity | reflexivity
                     | destruct WINS as [_ W9]; unfold rwin; lia | exact ACS1 | lia |].
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. clear -K4. cbv in K4. lia. }
      eapply LS_X; [exact K | | eassumption | exact SZ].
      split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
    -
      assert (N1 : (NS <= 64)%Z) by (unland K2; clear - K2 BS; Z.div_mod_to_equations; lia).
      do 11 zstep.
      probe8_reg0 13%Z RDS1 Sa w1 P1. probe8_reg0 14%Z RDS1 (Sa + NS + -1)%Z w2 P2.
      do 4 zstep. if_cases K5; zify_cond K5.
      + eapply LS_X; eassumption.
      + eapply LS_E; eassumption.
  Qed.

  #[using="ST LO KLO FL FIMG Sa sstr LG LC VAQ SEPV SSTR SNOZ SEPS WINS WIN2S SPOS ACCS RDS NSZ"] Lemma L_dirS : forall Q mc (i : Z) bc,
    INV mc -> rw_cells asegs mc (bv_unsigned sp + -2216) (dcellsA (FMT + i) bc) ->
    (0 <= i)%Z -> (i + 2 <= L)%Z -> sconv (bv_unsigned bc) -> KS Q i ->
    forall y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
    evt asegs Q (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp y5 y6 y7 sp (Z_to_bv 64 (FMT + i)) (Z_to_bv 64 (bv_unsigned bc)) y11 y12 y13 y14 y15 y16 y17
                 (Z_to_bv 64 10) (Z_to_bv 64 (FMT + i + 2)) (Z_to_bv 64 0x15411) a2 (Z_to_bv 64 (FMT + i + 1)) (Z_to_bv 64 9) (Z_to_bv 64 (bv_unsigned sp + -2184))
                 (Z_to_bv 64 PAT) (Z_to_bv 64 (-1)) (Z_to_bv 64 37) y28 y29 y30 y31)
                       F (Z_to_bv 64 0x48cd8) fc None mc (seg_rom asegs)).
  Proof.
    intros Q mc i bc IV DIR Hi HiL HC K. intros. pose proof IV as IV0. preps IV.
    destruct (sfacts _ HC) as (_ & CR & N109 & N110 & F3 & F4 & F5 & F6).
    pose proof (conj CR (conj N109 N110)) as CC.
    recell DIR 2%nat 1%nat [C4 (Z_to_bv 64 4294967295); C4 (Z_to_bv 64 4294967295)].
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
    zs. change (sx32 (Z_to_bv 64 4294967295)) with (Z_to_bv 64 (-1)). zs. br CC.
      zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
      zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
      zs. cbv beta. zs. zs. br CC. zs. zs. zs.
    call istrchr_spec. all: prem. unfold istrchr_res. rewrite F3. rewrite unsigned_lit by (cbn; lia).
      zs. cbv beta. zs. br CC.
      zs. zs. zs. zs. call istrchr_spec. all: prem. rewrite (istrchr_res_none _ _ _ F4).
      zs. zs. zs. br CC.
      zs. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F5. rewrite unsigned_lit by (cbn; lia).
      zs. zs. br CC. zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
      zs. zs.
      zs. cbv beta. zs. zs. zs. call istrchr_spec. all: prem. unfold istrchr_res. rewrite F6. rewrite unsigned_lit by (cbn; lia).
      zs. br CC. zs.
      zs. cbv beta. zs. zs. br CC.
      zs. zs. br CC. zs. br CC.
      zs. zs. zs. br BS.
      zs. cbv beta. rewrite unsigned_lit8 by lia. zs. br CC.
    zs. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0). zs. br CC.
      zs. zs.
    unfold sf_hide in SSTR1.
    call istrlen_spec. all: prem.
    zs.
    cbn [app] in DIR.
    eapply (LS_C Q i); [exact K | | exact DIR | reflexivity].
    split; [exact FRT|]. split; [eexists; exact FRL|]. repeat (split; [assumption|]). assumption.
  Qed.

  #[using="FMT MI ST LO KLO GOT SHB A1 FB NOZ FL FIMG ACCF RDF Sa sstr LG LC VAQ SEPV SSTR SNOZ SEPS WINS WIN2S SPOS ACCS RDS NSZ"] Theorem printf_common_str1 : forall pre b37 bc post,
    fstr = pre ++ b37 :: bc :: post ->
    Forall (fun b : byte => bv_unsigned b <> 37%Z) pre -> Forall (fun b : byte => bv_unsigned b <> 37%Z) post ->
    bv_unsigned b37 = 37%Z -> sconv (bv_unsigned bc) -> post <> [] ->
    evt asegs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x48a1c) fc None m (seg_rom asegs)).
  Proof.
    intros pre b37 bc post EF NP1 NP2 E37 HC NE.
    assert (LEN : length fstr = (length pre + 2 + length post)%nat) by (rewrite EF, length_app; cbn; lia).
    assert (NE' : (1 <= length post)%nat) by (destruct post; [congruence | cbn; lia]).
    set (np := Z.of_nat (length pre)).
    eapply L_entry. intros mc dj IV DIR. intros.
    eapply (L_head _ mc [CB 40 dj]); [exact IV | exact DIR | reflexivity |]. clear mc dj IV DIR. intros mc IV DIR. intros.
    replace (Z_to_bv 64 FMT) with (Z_to_bv 64 (FMT + 0)) by (f_equal; lia).
    pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
    eapply (L_skip _ mc (length pre) 0); [exact MIc | exact MUc | lia | lia | |].
    { intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP1). eapply nth_error_In. rewrite EF, nth_error_app1 in Hb by lia. exact Hb. }
    clear MUc MIc. intros. rewrite Z.add_0_l.
    eapply (L_dirA _ mc np _ b37 bc); [exact IV | exact DIR | lia | lia | | exact E37 | | exact (proj1 (sfacts _ HC)) |].
    { rewrite EF. replace (Z.to_nat np) with (length pre) by lia. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. }
    { rewrite EF. replace (Z.to_nat (np + 1)) with (length pre + 1)%nat by lia. rewrite nth_error_app2 by lia.
      replace (length pre + 1 - length pre)%nat with 1%nat by lia. reflexivity. }
    clear mc IV DIR. intros mc IV DIR. intros.
    eapply (L_dirS _ mc np); [exact IV | exact DIR | lia | lia | exact HC |].
    clear mc IV DIR. unfold KS. intros mc dcs IV DIR SZ. intros. unfold lregs.
    destruct (nth_error post 0) as [b2|] eqn:E2. 2:{ exfalso. apply nth_error_None in E2. lia. }
    assert (H2 : nth_error fstr (Z.to_nat (np + 2)) = Some b2).
    { rewrite EF. replace (Z.to_nat (np + 2)) with (length pre + 2)%nat by lia. rewrite nth_error_app2 by lia.
      replace (length pre + 2 - length pre)%nat with 2%nat by lia. exact E2. }
    pose proof IV as IV'. prep IV'.
    destruct (fmt_char mc (np + 2) MI1 MU1 ltac:(lia)) as (b2' & Hb2 & NZ2 & RB2 & RD2). rewrite H2 in Hb2. injection Hb2 as <-.
    replace (FMT + np + 2)%Z with (FMT + (np + 2))%Z by lia.
    zs. cbv beta. zs. assert (CC : True) by exact I. br NZ2.
    eapply (L_head _ mc dcs); [exact IV | exact DIR | exact SZ |].
    clear mc IV DIR SZ FRT FRL STM ST1 MU1 WM1 MI1 GOT1 SHB1 RD2. intros mc IV DIR. intros.
    pose proof IV as IV'. destruct IV' as (_ & _ & _ & _ & MUc & _ & MIc & _).
    eapply (L_skip _ mc (length post) (np + 2)); [exact MIc | exact MUc | lia | lia | |].
    { intros j b Hj Hb. eapply (proj1 (Forall_forall _ _) NP2). eapply nth_error_In with (n := (j - (length pre + 2))%nat).
      rewrite EF, nth_error_app2 in Hb by lia.
      replace (j - length pre)%nat with (S (S (j - (length pre + 2)))) in Hb by lia. exact Hb. }
    intros. replace (np + 2 + Z.of_nat (length post))%Z with L by lia.
    eapply L_last; [exact IV | exact DIR].
  Qed.

End PC.
