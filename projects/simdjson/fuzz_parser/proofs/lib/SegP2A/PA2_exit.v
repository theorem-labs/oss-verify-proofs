(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge Mem Cells Step Frame.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface AU_client_kit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegExplore SegTmpl SegGhost SegProg.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import PIosRegs PIosKit.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require Import S2Entry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require Import APS2_iface A2Lib.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2A Require PA2_t0c.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegA2 Require A2_defs.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.
Local Notation u := bv_unsigned.
Local Notation M64 := 18446744073709551616.

Section CANSEC. Context {rc : runConstT}.

Lemma u_rngE : forall (w : word), 0 <= u w < M64.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. exact H. Qed.

(* [comment removed for export] *)
Lemma xsf_regs : forall (ZL : list Z) (E' : env) (R' : bvmap 5 word),
  SP.gagree 35 (mkEZ ZL) E' -> eb (mkEZ ZL) = eb E' -> rfull R' -> regs_ok E' (ST.t_regs A2_defs.XSF) R' ->
  exists x5 x6 x7 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x24 x25 x26 x27 x28 x29 x30 x31,
    R' = mkR (Z_to_bv 64 0xa8500) (Z_to_bv 64 (16 * nth 1 ZL 0 + -384 - 16 * nth 29 ZL 0)) (Z_to_bv 64 (nth 2 ZL 0)) (Z_to_bv 64 (nth 3 ZL 0))
             x5 x6 x7 (Z_to_bv 64 (16 * nth 1 ZL 0)) (Z_to_bv 64 (16 * nth 1 ZL 0 + -384 - 16 * nth 29 ZL 0))
             (Z_to_bv 64 (2048 * nth 28 ZL 0)) (Z_to_bv 64 1312) x12 x13 x14 x15 x16 x17 x18
             (Z_to_bv 64 (256 * nth 28 ZL 0 + 2147450880)) x20 x21 x22 (edenot E' (EVar 35)) x24 x25 x26 x27 x28 x29 x30 x31.
Proof.
  intros ZL E' R' Hg Hb HF HR.
  rewrite (regs_ok_canon E' _ R' HF HR).
  assert (EV : forall k, (k < 35)%nat -> edenot E' (EVar k) = Z_to_bv 64 (nth k ZL 0)).
  { intros k Hk. rewrite <- (SP.edenot_gagree 35 _ _ (EVar k) Hg Hb ltac:(cbn; apply Nat.leb_le; lia)). reflexivity. }
  assert (EZ : forall e, AxSymRun3.expr_vars_lt 35 e = true -> zok e = true -> edenot E' e = Z_to_bv 64 (zden ZL e)).
  { intros e H1 H2. rewrite <- (SP.edenot_gagree 35 _ _ e Hg Hb H1), zden_ok by exact H2. reflexivity. }
  change (sr_get (ST.t_regs A2_defs.XSF) 1) with (ELit 0xa8500);
  change (sr_get (ST.t_regs A2_defs.XSF) 2) with
    (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-384))) (EMd M_MUL (ELit 16) (EVar 29)));
  change (sr_get (ST.t_regs A2_defs.XSF) 3) with (EVar 2); change (sr_get (ST.t_regs A2_defs.XSF) 4) with (EVar 3);
  change (sr_get (ST.t_regs A2_defs.XSF) 8) with (EMd M_MUL (ELit 16) (EVar 1));
  change (sr_get (ST.t_regs A2_defs.XSF) 9) with
    (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-384))) (EMd M_MUL (ELit 16) (EVar 29)));
  change (sr_get (ST.t_regs A2_defs.XSF) 10) with (EMd M_MUL (ELit 2048) (EVar 28));
  change (sr_get (ST.t_regs A2_defs.XSF) 11) with (ELit 1312);
  change (sr_get (ST.t_regs A2_defs.XSF) 19) with (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit 2147450880));
  change (sr_get (ST.t_regs A2_defs.XSF) 23) with (EVar 35).
  rewrite !(EZ (EAlu ALU_SUB (EAlu ALU_ADD (EMd M_MUL (ELit 16) (EVar 1)) (ELit (-384))) (EMd M_MUL (ELit 16) (EVar 29)))) by reflexivity.
  rewrite !(EZ (EMd M_MUL (ELit 16) (EVar 1))) by reflexivity.
  rewrite !(EZ (EMd M_MUL (ELit 2048) (EVar 28))) by reflexivity.
  rewrite !(EZ (EAlu ALU_ADD (EMd M_MUL (ELit 256) (EVar 28)) (ELit 2147450880))) by reflexivity.
  rewrite !EV by lia. cbn [zden edenot]. do 21 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma xsf_kfacts : forall (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z) (E' : env) (m3 : amem),
  SP.gagree 35 (mkEZ (PA2_t0c.ZL_t0'' zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                             T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest)) E' ->
  eb (mkEZ (PA2_t0c.ZL_t0'' zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                   T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest)) = eb E' ->
  know_ok asegs E' m3 (ST.t_know A2_defs.XSF) ->
  0 <= 16 * SP16 < M64 ->
  0 <= u (edenot E' (EVar 35)) <= 63
  /\ (forall k, 0 <= k < 13 -> bytes_at asegs m3 (16 * SP16 - 8 - 8 * k)
                 (word_to_le_bytes 8 (Z_to_bv 64 (nth (Z.to_nat k) [zra; zs0; zs1; zs2; zs3; zs4; zs5; zs6; zs7; zs8; zs9; zs10; zs11] 0)))).
Proof.
  intros until m3. intros Hg Hb HK HSP.
  split.
  - pose proof (know_nth _ _ _ _ 0 _ HK eq_refl) as K. cbn [kentry_ok] in K. cbv [A2_defs.V] in K. exact K.
  - intros k Hk.
    assert (Hk' : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12) by lia.
    destruct Hk' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| -> ]]]]]]]]]]]];
    match goal with |- bytes_at _ _ (16 * SP16 - 8 - 8 * ?k) _ =>
      let j := eval vm_compute in (Z.to_nat (2 + k)) in
      pose proof (know_nth _ _ _ _ j _ HK eq_refl) as K;
      lazymatch type of K with kentry_ok _ _ _ (KWord (SA ?b ?kk) ?w ?v) =>
        pose proof (kx_word_g asegs 35 _ E' m3 b kk w v Hg Hb eq_refl eq_refl eq_refl K) as B end; cbn [zden nth PA2_t0c.ZL_t0'' app] in B;
      rewrite (Z.mod_small (16 * SP16)) in B by lia;
      let o := eval vm_compute in (-8 - 8 * k) in
      replace (16 * SP16 - 8 - 8 * k) with (16 * SP16 + o) by lia; exact B
    end.
Qed.

(* [comment removed for export] *)
Lemma a2_munch : forall (zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11 : Z)
    (T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG : Z) (rest : list Z) (m m' : amem),
  8608 <= 16 * SP16 <= 2 ^ 47 -> 0 <= 8 * T8 /\ 8 * T8 + 96 < M64 -> 0 <= 8 * TB8 /\ 8 * TB8 + 8 * CAPT < M64 -> 0 <= CAPT ->
  0 <= 8 * SB8 /\ 8 * SB8 + CAPS < M64 -> 0 <= CAPS -> 0 <= 8 * OC8 /\ 8 * OC8 + 8192 < M64 -> 0 <= 8 * IA8 /\ 8 * IA8 + 1024 < M64 ->
  0 <= 2048 * F11 /\ 2048 * F11 + 2048 < M64 -> 0 <= 256 * F11 + 2147450880 /\ 256 * F11 + 2147450880 + 256 < M64 ->
  0 <= PB <= 1 ->
  (forall x : word, SP.outside_wins (mkEZ (PA2_t0c.ZL_t0'' zra SP16 zgp ztp zs0 zs1 zs2 zs3 zs4 zs5 zs6 zs7 zs8 zs9 zs10 zs11
                                         T8 DOC8 B8 LEN I8 N TB8 CAPT SB8 CAPS OC8 IA8 F11 PB FLAG BO BG IG SG rest))
                        (SP.p_W A2_defs.A2) (u x) -> m' x = m x) ->
  munch [(16 * SP16 - 8608, 16 * SP16); (8 * T8 + 24, 8 * T8 + 28); (8 * T8 + 88, 8 * T8 + 96); (8 * TB8, 8 * TB8 + 8 * CAPT);
         (8 * SB8, 8 * SB8 + CAPS); (8 * OC8, 8 * OC8 + 8192); (8 * IA8, 8 * IA8 + 1024); (2048 * F11, 2048 * F11 + 2048);
         (256 * F11 + 2147450880, 256 * F11 + 2147450880 + 256)] m m'.
Proof.
  intros until m'. intros H1 H2 H3 H3' H4 H4' H5 H6 H7 H8 HPB FR x Hx. apply FR. unfold SP.outside_wins.
  cbn [SP.p_W A2_defs.A2 SP.PGCA SP.PGH SP.PGX].
  pose proof (u_rngE x). cbn [outside] in Hx.
  cbv [A2_defs.vSP A2_defs.vSP16 A2_defs.vTHIS A2_defs.vT8 A2_defs.vTBASE A2_defs.vTB8 A2_defs.vCAPT A2_defs.vSBASE A2_defs.vSB8
       A2_defs.vCAPS A2_defs.vOCB A2_defs.vOC8 A2_defs.vIAB A2_defs.vIA8 A2_defs.vF A2_defs.vF11 A2_defs.vSHF A2_defs.V A2_defs.mul
       A2_defs.add A2_defs.vSPA A2_defs.vPB A2_defs.sub].
  repeat constructor; cbn [SP.win_den]; rewrite ?u_zden by reflexivity; cbn [zden nth PA2_t0c.ZL_t0'' app];
    rewrite ?(Z.mod_small _ M64) by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma a2_pres_W : forall (AI : AMallocIface) L RNG st LB (m m2 m3 : amem) (sp SPAX F THIS TPA ntp SBA nsb AOC AIA : Z),
  AHEAP AI L RNG st (mkABlock (ABFake 5) F 2048 :: LB) m2 ->
  (forall FA FN, ~ In (mkABlock (ABFake 5) FA FN) LB) ->
  ablk F (F + 2048) -> F + 2048 <= ATOP -> ATOP + 8608 <= sp -> sp <= 2^47 -> SPAX <= sp ->
  (forall a, aclient_addr (aci AI) LB SPAX a -> a < shad F \/ shad F + 256 <= a) ->
  aheap_pres (aci AI) LB sp m m2 ->
  munch [(sp - 8608, sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
         (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256)] m2 m3 ->
  wmono asegs m2 m3 ->
  aheap_pres_W (aci AI) LB sp (s2_winA THIS TPA ntp SBA nsb AOC AIA) m m3.
Proof.
  intros AI L RNG st LB m m2 m3 sp SPAX F THIS TPA ntp SBA nsb AOC AIA AH2 NO5 HFb HFt Hsp1 Hsp2 HSPX HSHF PRES MU WM a Ha Hc Hout.
  atop_facts.
  destruct (PRES a Ha Hc) as [E1 W1].
  assert (HSX : a < shad F \/ shad F + 256 <= a).
  { apply HSHF. destruct Hc as [X|[X|[X|X]]]; [left; lia | right; left; exact X | right; right; left; exact X | right; right; right; exact X]. }
  assert (SF : KLS <= shad F < 0x10007fff8000) by (apply shad_band1; unfold ablk, AIMG_HI, KLS, KEND in *; lia).
  assert (HO3 : ~ (sp - 8608 <= a < sp) /\ ~ (F <= a < F + 2048)).
  { destruct Hc as [X|[(iv & Hiv & Hr)|[(b & Hb & Hr)|(a' & Ha' & ->)]]].
    - lia.
    - pose proof (AI_aci_img AI iv Hiv). unfold ablk, AIMG_HI in *. lia.
    - pose proof (AI_block_bounds AI _ _ _ _ _ b AH2 (or_intror Hb)) as BB.
      assert (NE : b <> mkABlock (ABFake 5) F 2048) by (intros ->; exact (NO5 F 2048 Hb)).
      pose proof (AI_blocks_disjoint AI _ _ _ _ _ b (mkABlock (ABFake 5) F 2048) AH2 (or_intror Hb) (or_introl eq_refl) NE) as DJ.
      cbn [ab_addr ab_size] in DJ. lia.
    - assert (A47 : 0 <= a' < KEND).
      { destruct Ha' as [X|[(iv & Hiv & Hr)|(c & FA' & fn & Hb' & Hr)]]; unfold KEND;
          [lia | pose proof (AI_aci_img AI iv Hiv); pose proof (AI_aci_lo AI iv Hiv); unfold AIMG_HI in *; lia |].
        pose proof (AI_block_bounds AI _ _ _ _ _ _ AH2 (or_intror Hb')) as BB. cbn [ab_addr ab_size] in BB. unfold AIMG_HI in BB. lia. }
      pose proof (shad_band1 a' (proj1 A47) (proj2 A47)) as SB. unfold ablk, KLS in *. lia. }
  assert (HO : outside [(sp - 8608, sp); (THIS + 24, THIS + 28); (THIS + 88, THIS + 96); (TPA, TPA + ntp); (SBA, SBA + nsb);
                        (AOC, AOC + 8192); (AIA, AIA + 1024); (F, F + 2048); (shad F, shad F + 256)] a).
  { unfold s2_winA in Hout. cbn [outside] in Hout |- *. destruct Hout as (O1 & O2 & O3 & O4 & O5 & O6 & _).
    destruct HO3 as [O7 O8]. repeat split; try assumption. lia. }
  split.
  - rewrite <- E1. apply MU. rewrite wa_unsigned by lia. exact HO.
  - intros Hw. apply WM. apply W1. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma stage2_uchain : forall (m m' : amem) top pc sp s0 ra spc tr0,
  uchain m top pc sp s0 (Nat.pred UDEPTH) tr0 -> (s0 < sp \/ sp + 16 <= s0) ->
  (forall a, sp <= a < top -> m' (wa a) = m (wa a)) ->
  spc < sp -> sp < top - 16 -> sp mod 8 = 0 ->
  bytes_at asegs m' (sp - 16) (le8 (Z_to_bv 64 s0)) -> bytes_at asegs m' (sp - 8) (le8 (Z_to_bv 64 ra)) ->
  4096 <= ra < 2^64 -> 0 <= s0 < 2^64 -> ra <> pc ->
  uchain m' top pc spc sp UDEPTH (ra :: tr0).
Proof.
  intros m m' top pc sp s0 ra spc tr0 HC HS HM H1 H2 H3 B1 B2 Hra Hs0 Hne.
  eapply uchain_fp_step; [exact H1 | exact H2 | exact H3 | unfold UDEPTH; lia | exact B1 | exact B2 | exact Hra | exact Hs0 | exact Hne |].
  destruct HS as [HS|HS].
  - inversion HC; subst; [apply uc_stop; assumption | exfalso; lia | exfalso; lia].
  - eapply uchain_frame; [exact HC|]. intros a Ha. apply HM. lia.
Qed.

End CANSEC.
