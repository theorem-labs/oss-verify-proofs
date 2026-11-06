(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac Frame.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit RCode_17000_18000 RCode_18000_19000.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac MemcpyBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import PFLib.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Reloc Require Import RelocKit .
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Musl Require Import MuslTac PFBase PFFwx PFStr PFCore PFInv PFCoreLit PFPop PFCoreConv PFCoreS PFCoreD PFCoreD2.
Import ListNotations.
Open Scope bv_scope.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation W8 v := (word_to_le_bytes 8 (Z_to_bv 64 v)).
Abbreviation X8 w := (word_to_le_bytes 8 w).

Ltac indec := apply in_regs_dec; reflexivity.

Section TOP.
  Context {fx : FPState} {RL : Reloc} {RLC : RelocCode RL} {RLS : RelocSites RL} {RLD : RelocData RL} {RLI : RelocImg RL} {RLW : RelocRW RL RLD} {RLP : RelocPF RL}.
  Variables (sp0 : Z) (mem0 : word -> option byte) (cv : Z) (rom : word -> option byte).
  Hypothesis CTX : ctxH sp0 mem0 cv.
  Let Hcsp : (IMG_TOP + FR <= sp0 <= 0x800000000000)%Z := Csp _ _ _ CTX.
  Variables (g3 g4 : word).     (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma conv_int_run : forall (c : fconv) m1 (v : word) r regs (ret : word) (p cnt' u j apv : Z),
    c <> Cs ->
    FRM sp0 mem0 m1 -> PCc m1 sp0 cv regs ret -> FILEc m1 sp0 -> FILEst m1 sp0 u j ->
    rdn SEGS m1 (Z_to_bv 64 (sp0 - 3200)) 8 = Some (X8 v) ->
    rdn SEGS m1 (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 apv) ->
    (0 <= cnt')%Z -> (cnt' + 22 <= INT_MAX)%Z ->
    getr r 2 = Z_to_bv 64 (sp0 - 3312) -> getr r 5 = Z_to_bv 64 0 -> getr r 8 = Z_to_bv 64 37 -> getr r 9 = Z_to_bv 64 INT_MAX ->
    getr r 18 = Z_to_bv 64 (INT_MAX - cnt') -> getr r 19 = Z_to_bv 64 cnt' -> getr r 20 = Z_to_bv 64 (sp0 - 2400) ->
    getr r 21 = Z_to_bv 64 p -> getr r 22 = Z_to_bv 64 0 -> getr r 24 = Z_to_bv 64 0 ->
    getr r 25 = Z_to_bv 64 18446744073709551615 -> getr r 3 = g3 -> getr r 4 = g4 ->
    exists r' m' (W : Z),
      msteps SEGS (mkst r (conv_tgt c) m1 rom) (mkst r' (rl dF_17f6c 0x1801c) m' rom)
      /\ ((1 <= W <= 22)%Z /\ pcR sp0 g3 g4 r' (sp0 - 2400) p cnt' W
          /\ frame_mod m1 m' (pc_regions sp0)
          /\ (exists u' j', FILEst m' sp0 u' j' /\ (j <= j')%Z)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 apv)).
  Proof.
    intros c m1 v r regs ret p cnt' u j apv Hc F1 PC1 FC1 FS1 ARG AP2 Hc0 Hck R2 R5 R8 R9 R18 R19 R20 R21 R22 R24 R25 R3 R4.
    pose proof Hcsp as Hsp0. lay.
    assert (ENTRY : exists r' m' (x pl : Z),
      msteps SEGS (mkst r (conv_tgt c) m1 rom) (mkst r' (rl dF_17f6c 0x18808) m' rom)
      /\ ((0 <= x < 2 ^ 64)%Z /\ (pl = 0 \/ pl = 1)%Z
          /\ getr r' 10 = Z_to_bv 64 x /\ getr r' 14 = Z_to_bv 64 10 /\ getr r' 17 = rl dS_102e7 0x102e7
          /\ (forall x0 : reg, In x0 [3; 4; 2; 5; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x0 = getr r x0)
          /\ low_frame sp0 m1 m' /\ frame_mod m1 m' (pc_regions sp0)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 3288)) 8 = Some (W8 pl)
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 3200)) 8 = Some (W8 x)
          /\ (forall a n vv, (sp0 - 3280 <= a)%Z -> (a + Z.of_nat n <= sp0 - 3200)%Z ->
                 rdn SEGS m1 (Z_to_bv 64 a) n = Some vv -> rdn SEGS m' (Z_to_bv 64 a) n = Some vv))).
    { destruct c; [exfalso; apply Hc; reflexivity | | |]; cbn [conv_tgt].
      - exact (int_entry_d sp0 mem0 cv rom CTX m1 v r F1 ARG R2 R24).
      - exact (int_entry_u sp0 mem0 cv rom CTX m1 v r F1 ARG R2).
      - exact (int_entry_u sp0 mem0 cv rom CTX m1 v r F1 ARG R2). }
    destruct ENTRY as (rA & mA & x & pl & RUNA & Hx & Hpl & A10 & A14 & A17 & AK & LFA & PMA & PLA & ARGA & KEEPA).
    assert (FA : FRM sp0 mem0 mA) by (eapply FRM_sub; [exact F1 | exact PMA | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (PCA : PCc mA sp0 cv regs ret) by (eapply PCc_frame; [lia | exact PC1 | exact PMA]).
    assert (FCA : FILEc mA sp0) by (eapply FILEc_low; [lia | exact FC1 | exact LFA]).
    assert (FSA : FILEst mA sp0 u j) by (eapply FILEst_low; [lia | exact FS1 | exact LFA]).
    assert (AP2A : rdn SEGS mA (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 apv)) by (eapply cell_low; [exact LFA | lia | lia | cbn; lia | exact AP2]).
    Ltac tr AK H := rewrite AK by indec; exact H.
    destruct (int_tail sp0 mem0 cv rom CTX mA x pl cnt' u j apv rA regs ret Hx Hpl Hc0 Hck FA PCA FCA FSA ARGA PLA AP2A
                ltac:(tr AK R2) ltac:(tr AK R5) ltac:(tr AK R8) ltac:(tr AK R9) A10 A14 A17
                ltac:(tr AK R18) ltac:(tr AK R19) ltac:(tr AK R20) ltac:(tr AK R22) ltac:(tr AK R24) ltac:(tr AK R25))
      as (rZ & mZ & RUNZ & ZK & Z26 & PMZ & FSZ & APZ).
    pose proof (ndz_range x Hx) as [NR NR1].
    exists rZ, mZ, (pl + (ndz x + ez x))%Z. split.
    - eapply msteps_trans; [exact RUNA | exact RUNZ].
    - split.
      { unfold ez. destruct (Z.eqb_spec x 0); [|specialize (NR1 n)]; lia. }
      split.
      { unfold pcR. repeat split; try (rewrite ZK by indec; rewrite AK by indec; assumption). exact Z26. }
      split; [eapply frame_mod_trans_same; [exact PMA | exact PMZ]|].
      split; [exact FSZ | exact APZ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (regs0 : bvmap 5 word) (ret0 : word).     (* [comment removed for export] *)
  Variable va : Z -> word.                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (nS : Z) (saddr slen : Z -> Z).
  Hypothesis SARGS : forall q, (0 <= q < nS)%Z ->
    va q = Z_to_bv 64 (saddr q) /\ rostr mem0 (saddr q) (slen q) /\ (slen q <= 200)%Z.

  Record INV2 (m : word -> option byte) (k u j : Z) : Prop := MKINV2 {
    I_frm : FRM sp0 mem0 m;
    I_pc  : PCc m sp0 cv regs0 ret0;
    I_fc  : FILEc m sp0;
    I_fs  : FILEst m sp0 u j;
    I_ap  : rdn SEGS m (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56 + 8 * k));
    I_va  : forall q, (0 <= q < 7)%Z -> VAslot m sp0 q (va q) }.

  (* [comment removed for export] *)
  Lemma FILEc_popM : forall m k v, FILEc m sp0 -> FILEc (popM sp0 m k v) sp0.
  Proof.
    intros m k v FC. pose proof Hcsp as Hsp0. lay. destruct FC. unfold popM.
    split; (rewrite !rdn_wbytes_out; [assumption | zlen; unorm; lia | unorm; lia | zlen; unorm; lia
                                                  | zlen; unorm; lia | unorm; lia | zlen; unorm; lia]).
  Qed.
  Lemma FILEst_popM : forall m k v u j, FILEst m sp0 u j -> FILEst (popM sp0 m k v) sp0 u j.
  Proof.
    intros m k v u j (A & B & (C1 & C2 & C3) & D & E). pose proof Hcsp as Hsp0. lay. unfold popM.
    Ltac pp := rewrite !rdn_wbytes_out; [assumption | zlen; unorm; lia | unorm; lia | zlen; unorm; lia
                                                   | zlen; unorm; lia | unorm; lia | zlen; unorm; lia].
    split; [pp|]. split; [pp|]. split; [split; [pp | split; [pp | exact C3]]|]. split; [exact D|].
    eapply defined_grows; [|exact E]. eapply mem_grows_trans; apply wbytes_grows.
  Qed.

  (* [comment removed for export] *)
  Variables (fa : Z) (fbs : list Z).      (* [comment removed for export] *)
  Hypothesis FMT0 : forall i, (0 <= i < Z.of_nat (length fbs))%Z ->
    mem0 (Z_to_bv 64 (fa + i)) = None /\ seg_rom SEGS (Z_to_bv 64 (fa + i)) = Some (Z_to_bv 8 (nth (Z.to_nat i) fbs 0%Z)).
  Hypothesis FMTR : (IMG_LO <= fa /\ fa + Z.of_nat (length fbs) <= IMG_TOP)%Z.
  Hypothesis FBYTE : forall i, (0 <= i < Z.of_nat (length fbs))%Z -> (0 <= nth (Z.to_nat i) fbs 0%Z <= 255)%Z.

  Definition fbyte (q : Z) : Z := nth (Z.to_nat (q - fa)) fbs 0%Z.

  Lemma fmt_rd : forall m q, FRM sp0 mem0 m -> (fa <= q < fa + Z.of_nat (length fbs))%Z ->
    rdn SEGS m (Z_to_bv 64 q) 1 = Some [Z_to_bv 8 (fbyte q)].
  Proof.
    intros m q F Hq. pose proof Hcsp as Hsp0. lay.
    destruct (FMT0 (q - fa)%Z ltac:(lia)) as [N R]. replace (fa + (q - fa))%Z with q in N, R by lia.
    rewrite (FRM_rdn sp0 mem0 cv CTX m q 1 F); [| lia | lay; cbn; lia | cbn; lia].
    apply rdn1_rom; [exact N | exact R].
  Qed.

  Ltac inreg Hx := cbv [In] in Hx; repeat (destruct Hx as [<-|Hx]; [|]); try destruct Hx.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma conv_iter_p2 : forall (c : fconv) m r (p cnt l k u j : Z),
    (IMG_LO <= p /\ p + conv_len c < IMG_TOP)%Z ->
    rdn SEGS m (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 37] ->
    rdn SEGS m (Z_to_bv 64 (p + 1)) 1 = Some [Z_to_bv 8 (conv_c1 c)] ->
    (c = Czu -> rdn SEGS m (Z_to_bv 64 (p + 2)) 1 = Some [Z_to_bv 8 117]) ->
    INV2 m k u j -> (0 <= k < 7)%Z ->
    ((c = Cs /\ (k < nS)%Z) \/ (c <> Cs)) ->
    pcR sp0 g3 g4 r (sp0 - 2400) p cnt l -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + 256 <= INT_MAX)%Z ->
    exists r' m' (W u' j' : Z),
      msteps SEGS (mkst r (rl dF_17f6c 0x1801c) m rom) (mkst r' (rl dF_17f6c 0x1801c) m' rom)
      /\ ((0 <= W <= 200)%Z /\ pcR sp0 g3 g4 r' (sp0 - 2400) (p + conv_len c) (cnt + l) W
          /\ INV2 m' (k + 1) u' j' /\ (j <= j')%Z /\ frame_mod m m' (pc_regions sp0)).
  Proof.
    intros c m r p cnt l k u j Hp B0 B1 B2 INV Hk Hcls PR Hc0 Hl Hcl.
    pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    destruct INV as [F PC FC FS AP VA].
    assert (CL : (2 <= conv_len c <= 3)%Z) by (destruct c; cbn; lia).
    pose proof PR as (R3 & R4 & R2 & R8 & R9 & R19 & R20 & R21 & R26).
    (* [comment removed for export] *)
    destruct (conv_head sp0 mem0 cv rom CTX g3 g4 m p c Hp B0 B1 B2 r (sp0 - 2400) cnt l PR Hc0 Hl ltac:(unfold INT_MAX; lia) ltac:(lia))
      as (r1 & RUN1 & Q3 & Q4 & Q2 & Q8 & Q9 & Q19 & Q20 & Q21 & Q23 & Q26 & Q22 & Q18).
    (* [comment removed for export] *)
    destruct (conv_out0_p2 sp0 mem0 cv rom CTX m p c Hp B1 B2 r1 u j F FC FS Q2 Q20 Q22 Q23)
      as (r2 & m2 & RUN2 & AB2 & T2 & FM2 & [u2 [j2 [FS2 Hj2]]]).
    assert (PM2 : frame_mod m m2 (pc_regions sp0)).
    { eapply frame_mod_weaken; [|exact FM2]. intros x0 Ho. apply fwx_sub_pc; [lia | exact Ho]. }
    assert (F2 : FRM sp0 mem0 m2) by (eapply FRM_sub; [exact F | exact PM2 | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (PC2 : PCc m2 sp0 cv regs0 ret0) by (eapply PCc_frame; [lia | exact PC | exact PM2]).
    assert (FC2 : FILEc m2 sp0) by (eapply (FILEc_fwx m m2 sp0 (sp0 - 3312)); [lia | lia | exact FC | exact FM2]).
    assert (AP2' : rdn SEGS m2 (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56 + 8 * k))).
    { unfold fwx_regions in FM2. frame_rdn_keep FM2. exact AP. }
    assert (VA2 : forall q, (0 <= q < 7)%Z -> VAslot m2 sp0 q (va q)).
    { intros q Hq. eapply VAslot_pc; [lia | exact Hq | apply VA; exact Hq | exact PM2]. }
    assert (C0 : rdn SEGS m2 (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 37]).
    { rewrite (FRM_rdn sp0 mem0 cv CTX m2 p 1 F2); [|lia|lay; cbn; lia|cbn; lia].
      rewrite <- (FRM_rdn sp0 mem0 cv CTX m p 1 F); [exact B0|lia|lay; cbn; lia|cbn; lia]. }
    assert (C1 : rdn SEGS m2 (Z_to_bv 64 (p + 1)) 1 = Some [Z_to_bv 8 (conv_c1 c)]).
    { rewrite (FRM_rdn sp0 mem0 cv CTX m2 (p + 1) 1 F2); [|lia|lay; cbn; lia|cbn; lia].
      rewrite <- (FRM_rdn sp0 mem0 cv CTX m (p + 1) 1 F); [exact B1|lia|lay; cbn; lia|cbn; lia]. }
    assert (C2 : c = Czu -> rdn SEGS m2 (Z_to_bv 64 (p + 2)) 1 = Some [Z_to_bv 8 117]).
    { intros E. rewrite (FRM_rdn sp0 mem0 cv CTX m2 (p + 2) 1 F2); [|lia|lay; cbn; lia|cbn; lia].
      rewrite <- (FRM_rdn sp0 mem0 cv CTX m (p + 2) 1 F); [exact (B2 E)|lia|lay; cbn; lia|cbn; lia]. }
    (* [comment removed for export] *)
    Ltac viaAB AB H := rewrite AB; [exact H | apply in_regs_dec; reflexivity | apply not_in_regs_dec; reflexivity].
    assert (T21 : getr r2 21 = Z_to_bv 64 p) by (viaAB AB2 Q21).
    (* [comment removed for export] *)
    destruct (conv_parse sp0 mem0 cv rom CTX m2 p c Hp C1 C2 r2 regs0 ret0 F2 PC2 T2 T21)
      as (r3 & RUN3 & P11 & P27 & P21 & P5 & P25 & P24 & P22 & P10 & PK).
    assert (U2 : getr r3 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite PK by indec; exact T2).
    assert (U20 : getr r3 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite PK by indec; viaAB AB2 Q20).
    (* [comment removed for export] *)
    destruct (conv_pop sp0 mem0 cv rom CTX m2 p c Hp C1 C2 r3 regs0 ret0 k (va k) F2 PC2 AP2' (VA2 k Hk) Hk U2 U20 P11 P5)
      as (r4 & v & RUN4 & Hv & V5 & VK).
    set (m4 := popM sp0 m2 k v) in *.
    assert (PM4 : frame_mod m2 m4 (pc_regions sp0)) by (unfold m4, popM, pc_regions; frame_tac Hsp0; apply frame_mod_refl).
    assert (F4 : FRM sp0 mem0 m4) by (eapply FRM_sub; [exact F2 | exact PM4 | apply (pc_regions_sub sp0 mem0 cv CTX)]).
    assert (PC4 : PCc m4 sp0 cv regs0 ret0) by (eapply PCc_frame; [lia | exact PC2 | exact PM4]).
    assert (FC4 : FILEc m4 sp0) by (unfold m4; apply FILEc_popM; exact FC2).
    assert (FS4 : FILEst m4 sp0 u2 j2) by (unfold m4; apply FILEst_popM; exact FS2).
    assert (ARG4 : rdn SEGS m4 (Z_to_bv 64 (sp0 - 3200)) 8 = Some (X8 v)) by (unfold m4, popM; rdn_solve).
    assert (AP4 : rdn SEGS m4 (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56 + 8 * (k + 1)))) by (unfold m4, popM; rdn_solve).
    assert (D1 : rdn SEGS m4 (Z_to_bv 64 (p + 1)) 1 = Some [Z_to_bv 8 (conv_c1 c)]) by (unfold m4, popM; repeat rdn_peel1; exact C1).
    assert (D2 : c = Czu -> rdn SEGS m4 (Z_to_bv 64 (p + 2)) 1 = Some [Z_to_bv 8 117]) by (intros E; unfold m4, popM; repeat rdn_peel1; exact (C2 E)).
    assert (W2 : getr r4 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite VK by indec; exact U2).
    assert (W20 : getr r4 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite VK by indec; exact U20).
    assert (W21 : getr r4 21 = Z_to_bv 64 (p + conv_len c)) by (rewrite VK by indec; exact P21).
    assert (W24 : getr r4 24 = Z_to_bv 64 0) by (rewrite VK by indec; exact P24).
    assert (W27 : getr r4 27 = Z_to_bv 64 (conv_ps c)) by (rewrite VK by indec; exact P27).
    (* [comment removed for export] *)
    destruct (conv_dispatch sp0 mem0 cv rom CTX m2 p c Hp C1 C2 m4 r4 regs0 ret0 F4 PC4 FC4 D1 D2 W2 W20 W21 W24 W27)
      as (r5 & RUN5 & X26 & X16 & XK).
    (* [comment removed for export] *)
    assert (Y2 : getr r5 2 = Z_to_bv 64 (sp0 - 3312)) by (rewrite XK by indec; exact W2).
    assert (Y5 : getr r5 5 = Z_to_bv 64 0) by (rewrite XK by indec; exact V5).
    assert (Y8 : getr r5 8 = Z_to_bv 64 37) by (rewrite XK by indec; rewrite VK by indec; rewrite PK by indec; viaAB AB2 Q8).
    assert (Y9 : getr r5 9 = Z_to_bv 64 2147483647) by (rewrite XK by indec; rewrite VK by indec; rewrite PK by indec; viaAB AB2 Q9).
    assert (Y18 : getr r5 18 = Z_to_bv 64 (2147483647 - (cnt + l))) by (rewrite XK by indec; rewrite VK by indec; rewrite PK by indec; viaAB AB2 Q18).
    assert (Y19 : getr r5 19 = Z_to_bv 64 (cnt + l)) by (rewrite XK by indec; rewrite VK by indec; rewrite PK by indec; viaAB AB2 Q19).
    assert (Y20 : getr r5 20 = Z_to_bv 64 (sp0 - 2400)) by (rewrite XK by indec; exact W20).
    assert (Y21 : getr r5 21 = Z_to_bv 64 (p + conv_len c)) by (rewrite XK by indec; exact W21).
    assert (Y22 : getr r5 22 = Z_to_bv 64 0) by (rewrite XK by indec; rewrite VK by indec; exact P22).
    assert (Y24 : getr r5 24 = Z_to_bv 64 0) by (rewrite XK by indec; exact W24).
    assert (Y25 : getr r5 25 = Z_to_bv 64 18446744073709551615) by (rewrite XK by indec; rewrite VK by indec; exact P25).
    assert (Y3 : getr r5 3 = g3) by (rewrite XK by indec; rewrite VK by indec; rewrite PK by indec; viaAB AB2 Q3).
    assert (Y4 : getr r5 4 = g4) by (rewrite XK by indec; rewrite VK by indec; rewrite PK by indec; viaAB AB2 Q4).
    (* [comment removed for export] *)
    assert (BODY : exists r' m' (W u' j' : Z),
      msteps SEGS (mkst r5 (conv_tgt c) m4 rom) (mkst r' (rl dF_17f6c 0x1801c) m' rom)
      /\ ((0 <= W <= 200)%Z /\ pcR sp0 g3 g4 r' (sp0 - 2400) (p + conv_len c) (cnt + l) W
          /\ frame_mod m4 m' (pc_regions sp0) /\ FILEst m' sp0 u' j' /\ (j2 <= j')%Z
          /\ rdn SEGS m' (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56 + 8 * (k + 1))))).
    { destruct Hcls as [[-> Hks] | Hns].
      - (* [comment removed for export] *)
        destruct (SARGS k ltac:(lia)) as (Eva & RSk & Hkk).
        assert (ARGs : rdn SEGS m4 (Z_to_bv 64 (sp0 - 3200)) 8 = Some (X8 (Z_to_bv 64 (saddr k)))).
        { rewrite <- Eva. rewrite <- (Hv ltac:(left; reflexivity)). exact ARG4. }
        destruct (conv_s_run sp0 mem0 cv rom CTX g3 g4 (saddr k) (slen k) RSk Hkk m4 r5 regs0 ret0 (sp0 - 2400) (p + 2) (cnt + l) u2 j2
                    (sp0 - 56 + 8 * (k + 1)) F4 PC4 FC4 FS4 ARGs AP4 eq_refl ltac:(lia) ltac:(unfold INT_MAX; lia)
                    Y2 Y8 ltac:(unfold INT_MAX; exact Y9) ltac:(unfold INT_MAX; exact Y18) Y19 Y20 Y21 Y22 Y24 Y25 X26 Y3 Y4)
          as (r' & m' & RUN' & PR' & PM' & [u' [j' [FS' Hj']]] & AP').
        assert (K0 : (0 <= slen k)%Z) by (destruct RSk as [K0 _]; exact K0).
        exists r', m', (slen k), u', j'. split; [exact RUN'|]. split; [lia|]. split; [exact PR'|].
        split; [exact PM'|]. split; [exact FS'|]. split; [exact Hj'|]. exact AP'.
      - destruct (conv_int_run c m4 v r5 regs0 ret0 (p + conv_len c) (cnt + l) u2 j2 (sp0 - 56 + 8 * (k + 1)) Hns
                    F4 PC4 FC4 FS4 ARG4 AP4 ltac:(lia) ltac:(unfold INT_MAX; lia)
                    Y2 Y5 Y8 ltac:(unfold INT_MAX; exact Y9) ltac:(unfold INT_MAX; exact Y18) Y19 Y20 Y21 Y22 Y24 Y25 Y3 Y4)
          as (r' & m' & W & RUN' & HW & PR' & PM' & [u' [j' [FS' Hj']]] & AP').
        exists r', m', W, u', j'. split; [exact RUN'|]. split; [lia|]. split; [exact PR'|].
        split; [exact PM'|]. split; [exact FS'|]. split; [exact Hj'|]. exact AP'. }
    destruct BODY as (r' & m' & W & u' & j' & RUN' & HW & PR' & PM' & FS' & Hj' & AP').
    exists r', m', W, u', j'. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. exact RUN'.
    - split; [exact HW|]. split; [exact PR'|]. split.
      + split.
        * eapply FRM_sub; [exact F4 | exact PM' | apply (pc_regions_sub sp0 mem0 cv CTX)].
        * eapply PCc_frame; [lia | exact PC4 | exact PM'].
        * eapply FILEc_pc; [lia | exact FC4 | exact PM'].
        * exact FS'.
        * exact AP'.
        * intros q Hq. eapply VAslot_pc; [lia | exact Hq | | exact PM'].
          unfold m4, popM. apply VAslot_wb; [lia | lia | zlen; lia | exact Hq |]. apply VAslot_wb; [lia | lia | zlen; lia | exact Hq |].
          apply VA2. exact Hq.
      + split; [lia|].
        eapply frame_mod_trans_same; [exact PM2|]. eapply frame_mod_trans_same; [exact PM4 | exact PM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma lit_iter_p2 : forall m r (p n c cnt l k u j : Z),
    (1 <= n)%Z -> (fa <= p)%Z -> (p + n < fa + Z.of_nat (length fbs))%Z ->
    (forall q, (p <= q < p + n)%Z -> (1 <= fbyte q <= 255 /\ fbyte q <> 37)%Z) ->
    fbyte (p + n)%Z = c ->
    (c = 0%Z \/ (c = 37%Z /\ (p + n + 1 < fa + Z.of_nat (length fbs))%Z /\ fbyte (p + n + 1)%Z <> 37%Z)) ->
    INV2 m k u j ->
    pcR sp0 g3 g4 r (sp0 - 2400) p cnt l -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + n <= INT_MAX)%Z ->
    exists r' m' (u' j' : Z),
      msteps SEGS (mkst r (rl dF_17f6c 0x1801c) m rom) (mkst r' (rl dF_17f6c 0x1801c) m' rom)
      /\ (pcR sp0 g3 g4 r' (sp0 - 2400) (p + n) (cnt + l) n
          /\ INV2 m' k u' j' /\ (j <= j')%Z /\ frame_mod m m' (pc_regions sp0)).
  Proof.
    intros m r p n c cnt l k u j Hn Hfp Hpn BL BE Hc INV PR Hc0 Hl Hcl.
    pose proof Hcsp as Hsp0. lay. unfold INT_MAX in *.
    destruct INV as [F PC FC FS AP VA].
    assert (Hp : (IMG_LO <= p /\ p + n < IMG_TOP)%Z) by (lay; lia).
    assert (BYrd : forall q, (p <= q <= p + n)%Z -> rdn SEGS m (Z_to_bv 64 q) 1 = Some [Z_to_bv 8 (fbyte q)]).
    { intros q Hq. apply fmt_rd; [exact F | lia]. }
    assert (Hc' : c = 0%Z \/ (c = 37%Z /\ exists d, rdn SEGS m (Z_to_bv 64 (p + n + 1)) 1 = Some [Z_to_bv 8 d] /\ (0 <= d <= 255)%Z /\ d <> 37%Z)).
    { destruct Hc as [C0 | (C37 & Hq & D37)]; [left; exact C0 | right]. split; [exact C37|].
      exists (fbyte (p + n + 1)%Z). split; [apply fmt_rd; [exact F | lia]|]. split; [|exact D37].
      unfold fbyte. apply FBYTE. lia. }
    pose proof PR as (R3 & R4 & R2 & R8 & R9 & R19 & R20 & R21 & R26).
    destruct (lit_scan sp0 mem0 cv rom CTX g3 g4 m p n c fbyte Hn Hp BYrd BL BE Hc' r (sp0 - 2400) cnt l PR Hc0 Hl
                ltac:(unfold INT_MAX; lia) ltac:(lia))
      as (r1 & RUN1 & Q3 & Q4 & Q2 & Q8 & Q9 & Q19 & Q20 & Q21 & Q23 & Q26 & Q22 & Q18).
    destruct (lit_tail2 sp0 mem0 cv rom CTX g3 g4 m p n fbyte Hn Hp BYrd r1 (cnt + l) u j F FC FS
                ltac:(unfold INT_MAX; lia) ltac:(lia) Q2 Q8 Q9 Q19 Q20 Q21 Q26 Q22 Q23 Q3 Q4)
      as (r2 & m2 & RUN2 & PR2 & FM2 & [u2 [j2 [FS2 Hj2]]]).
    assert (PM2 : frame_mod m m2 (pc_regions sp0)).
    { eapply frame_mod_weaken; [|exact FM2]. intros x0 Ho. apply fwx_sub_pc; [lia | exact Ho]. }
    exists r2, m2, u2, j2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [exact PR2|]. split; [|split; [exact Hj2 | exact PM2]].
    split.
    - eapply FRM_sub; [exact F | exact PM2 | apply (pc_regions_sub sp0 mem0 cv CTX)].
    - eapply PCc_frame; [lia | exact PC | exact PM2].
    - eapply (FILEc_fwx m m2 sp0 (sp0 - 3312)); [lia | lia | exact FC | exact FM2].
    - exact FS2.
    - unfold fwx_regions in FM2. frame_rdn_keep FM2. exact AP.
    - intros q Hq. eapply VAslot_pc; [lia | exact Hq | apply VA; exact Hq | exact PM2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Fixpoint convs_ok (k : Z) (cs : list fconv) : Prop :=
    match cs with
    | [] => True
    | c :: r => ((c = Cs /\ (k < nS)%Z) \/ c <> Cs) /\ convs_ok (k + 1) r
    end.

  Definition rem (its : list fitem) : Z := (lit_total its + 256 * Z.of_nat (length (convs its)))%Z.

  (* [comment removed for export] *)
  Definition suffix_at (p : Z) (rest : list fitem) : Prop :=
    (forall i, (i < length (flat rest))%nat -> fbyte (p + Z.of_nat i) = nth i (flat rest) 0%Z)
    /\ (p + Z.of_nat (length (flat rest)) = fa + Z.of_nat (length fbs))%Z /\ (fa <= p)%Z.

  Lemma lit_total_nonneg : forall its, (0 <= lit_total its)%Z.
  Proof. induction its as [|[bs|c] r IH]; cbn; lia. Qed.

  Lemma flat_len_pos : forall its, (1 <= length (flat its))%nat.
  Proof. induction its as [|[bs|c] r IH]; cbn; [lia| |]; rewrite length_app; lia. Qed.

  Lemma pass2_loop : forall rest m r (p cnt l k u j : Z),
    wf_items rest = true -> convs_ok k (convs rest) -> (0 <= k)%Z -> (k + Z.of_nat (length (convs rest)) <= 7)%Z ->
    suffix_at p rest ->
    INV2 m k u j -> pcR sp0 g3 g4 r (sp0 - 2400) p cnt l -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + rem rest + 56 <= INT_MAX)%Z ->
    exists r' m' (k' u' j' : Z),
      msteps SEGS (mkst r (rl dF_17f6c 0x1801c) m rom) (mkst r' (rl dF_17f6c 0x18d48) m' rom)
      /\ (getr r' 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r' 3 = g3 /\ getr r' 4 = g4
          /\ INV2 m' k' u' j' /\ (j <= j')%Z /\ frame_mod m m' (pc_regions sp0)).
  Proof.
    pose proof Hcsp as Hsp0.
    induction rest as [|[bs|c] rest IH]; intros m r p cnt l k u j WF COK Hk0 Hk7 (SUF & LEN & FAP) INV PR Hc0 Hl Hbd.
    - (* [comment removed for export] *)
      cbn [flat length] in SUF, LEN. unfold rem in Hbd. cbn in Hbd.
      pose proof INV as [F PC FC FS AP VA].
      assert (B0 : rdn SEGS m (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 0]).
      { pose proof (SUF 0%nat ltac:(lia)) as E. cbn in E. rewrite Z.add_0_r in E.
        rewrite <- E. apply fmt_rd; [exact F | lia]. }
      destruct (head_end_run sp0 mem0 cv rom CTX g3 g4 m r (sp0 - 2400) p cnt l PR Hc0 Hl ltac:(unfold INT_MAX in *; lia)
                  ltac:(lay; lia) ltac:(lay; lia) B0) as [RUNf _].
      destruct (RUNf ltac:(lay; lia)) as (r' & RUN & R2' & R19' & R3' & R4').
      exists r', m, k, u, j. split; [exact RUN|]. split; [exact R2'|]. split; [exact R3'|]. split; [exact R4'|].
      split; [exact INV|]. split; [lia | apply frame_mod_refl].
    - (* [comment removed for export] *)
      cbn [wf_items] in WF. apply andb_prop in WF as [WF WFr]. apply andb_prop in WF as [WF NOLIT]. apply andb_prop in WF as [NE LB].
      cbn [convs] in COK, Hk7. unfold rem in Hbd. cbn [lit_total convs] in Hbd. fold (rem rest) in Hbd.
      set (n := Z.of_nat (length bs)) in *.
      assert (Hn : (1 <= n)%Z) by (destruct bs; [discriminate NE | cbn in *; lia]).
      cbn [flat] in SUF, LEN. rewrite length_app in SUF, LEN.
      pose proof (flat_len_pos rest) as FLP. pose proof (lit_total_nonneg rest) as LT0.
      assert (REM0 : (0 <= rem rest)%Z) by (unfold rem; lia).
      (* [comment removed for export] *)
      assert (BL : forall q, (p <= q < p + n)%Z -> (1 <= fbyte q <= 255 /\ fbyte q <> 37)%Z).
      { intros q Hq. pose proof (SUF (Z.to_nat (q - p)) ltac:(lia)) as E.
        replace (p + Z.of_nat (Z.to_nat (q - p)))%Z with q in E by lia. rewrite E.
        rewrite app_nth1 by lia.
        assert (LBq := proj1 (forallb_forall _ _) LB (nth (Z.to_nat (q - p)) bs 0%Z) ltac:(apply nth_In; lia)).
        unfold lit_byte in LBq. apply andb_prop in LBq as [LBq N37]. apply andb_prop in LBq as [L1 L255].
        apply Z.leb_le in L1. apply Z.leb_le in L255. destruct (Z.eqb_spec (nth (Z.to_nat (q - p)) bs 0%Z) 37); [discriminate N37|]. lia. }
      assert (BEc : fbyte (p + n)%Z = nth 0 (flat rest) 0%Z).
      { pose proof (SUF (length bs) ltac:(lia)) as E. fold n in E. rewrite E. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
      assert (Hc : nth 0 (flat rest) 0%Z = 0%Z
                   \/ (nth 0 (flat rest) 0%Z = 37%Z /\ (p + n + 1 < fa + Z.of_nat (length fbs))%Z /\ fbyte (p + n + 1)%Z <> 37%Z)).
      { destruct rest as [|[bs'|c'] rest'].
        - left. reflexivity.
        - discriminate NOLIT.
        - right. cbn [flat]. assert (CL : (2 <= conv_len c')%Z) by (destruct c'; cbn; lia).
          pose proof (conv_bytes_len c') as CBL. cbn [flat] in LEN. rewrite length_app in LEN.
          split; [destruct c'; reflexivity|]. split; [lia|].
          pose proof (SUF (length bs + 1)%nat ltac:(cbn [flat]; rewrite length_app; lia)) as E.
          replace (p + Z.of_nat (length bs + 1))%Z with (p + n + 1)%Z in E by lia. rewrite E.
          rewrite app_nth2 by lia. replace (length bs + 1 - length bs)%nat with 1%nat by lia.
          cbn [flat]. destruct c'; cbn; lia. }
      destruct (lit_iter_p2 m r p n (nth 0 (flat rest) 0%Z) cnt l k u j Hn FAP ltac:(lia) BL BEc Hc INV PR Hc0 Hl
                  ltac:(unfold INT_MAX in *; lia)) as (r1 & m1 & u1 & j1 & RUN1 & PR1 & INV1 & Hj1 & PM1).
      assert (SUF' : suffix_at (p + n) rest).
      { split; [|split; [lia|lia]]. intros i Hi. pose proof (SUF (length bs + i)%nat ltac:(lia)) as E.
        replace (p + Z.of_nat (length bs + i))%Z with (p + n + Z.of_nat i)%Z in E by lia. rewrite E.
        rewrite app_nth2 by lia. f_equal. lia. }
      destruct PR1 as (X3 & X4 & X2 & X8 & X9 & X19 & X20 & X21 & X26).
      destruct (IH m1 r1 (p + n)%Z (cnt + l)%Z n k u1 j1 WFr COK Hk0 Hk7 SUF' INV1
                  ltac:(unfold pcR; repeat split; assumption) ltac:(lia) ltac:(lia) ltac:(unfold rem, INT_MAX in *; lia))
        as (r' & m' & k' & u' & j' & RUN & R2' & R3' & R4' & INV' & Hj' & PM').
      exists r', m', k', u', j'. split; [eapply msteps_trans; [exact RUN1 | exact RUN]|].
      split; [exact R2'|]. split; [exact R3'|]. split; [exact R4'|]. split; [exact INV'|]. split; [lia|].
      eapply frame_mod_trans_same; [exact PM1 | exact PM'].
    - (* [comment removed for export] *)
      cbn [wf_items] in WF. cbn [convs length] in COK, Hk7. destruct COK as [Hcls COK].
      unfold rem in Hbd. cbn [lit_total convs length] in Hbd.
      pose proof (lit_total_nonneg rest) as LT0.
      cbn [flat] in SUF, LEN. rewrite length_app in SUF, LEN.
      pose proof (conv_bytes_len c) as CBL. assert (CL : (2 <= conv_len c <= 3)%Z) by (destruct c; cbn; lia).
      pose proof (flat_len_pos rest) as FLP.
      pose proof INV as [F PC FC FS AP VA].
      assert (Hp : (IMG_LO <= p /\ p + conv_len c < IMG_TOP)%Z) by (lay; lia).
      assert (B0 : rdn SEGS m (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 37]).
      { pose proof (SUF 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E.
        replace (nth 0 (conv_bytes c ++ flat rest) 0%Z) with 37%Z in E by (destruct c; reflexivity).
        rewrite <- E. apply fmt_rd; [exact F | lia]. }
      assert (B1 : rdn SEGS m (Z_to_bv 64 (p + 1)) 1 = Some [Z_to_bv 8 (conv_c1 c)]).
      { pose proof (SUF 1%nat ltac:(lia)) as E.
        replace (nth 1 (conv_bytes c ++ flat rest) 0%Z) with (conv_c1 c) in E by (destruct c; reflexivity).
        replace (p + Z.of_nat 1)%Z with (p + 1)%Z in E by lia. rewrite <- E. apply fmt_rd; [exact F | lia]. }
      assert (B2 : c = Czu -> rdn SEGS m (Z_to_bv 64 (p + 2)) 1 = Some [Z_to_bv 8 117]).
      { intros ->. pose proof (SUF 2%nat ltac:(cbn in *; lia)) as E. cbn [conv_bytes app nth] in E.
        replace (p + Z.of_nat 2)%Z with (p + 2)%Z in E by lia. rewrite <- E. apply fmt_rd; [exact F | cbn in *; lia]. }
      destruct (conv_iter_p2 c m r p cnt l k u j Hp B0 B1 B2 INV ltac:(lia) Hcls PR Hc0 Hl ltac:(unfold INT_MAX in *; lia))
        as (r1 & m1 & W & u1 & j1 & RUN1 & HW & PR1 & INV1 & Hj1 & PM1).
      assert (SUF' : suffix_at (p + conv_len c) rest).
      { split; [|split; [lia|lia]]. intros i Hi. pose proof (SUF (length (conv_bytes c) + i)%nat ltac:(lia)) as E.
        replace (p + Z.of_nat (length (conv_bytes c) + i))%Z with (p + conv_len c + Z.of_nat i)%Z in E by lia. rewrite E.
        rewrite app_nth2 by lia. f_equal. lia. }
      destruct (IH m1 r1 (p + conv_len c)%Z (cnt + l)%Z W (k + 1)%Z u1 j1 WF COK ltac:(lia) ltac:(lia) SUF' INV1 PR1
                  ltac:(lia) ltac:(lia) ltac:(unfold rem, INT_MAX in *; lia))
        as (r' & m' & k' & u' & j' & RUN & R2' & R3' & R4' & INV' & Hj' & PM').
      exists r', m', k', u', j'. split; [eapply msteps_trans; [exact RUN1 | exact RUN]|].
      split; [exact R2'|]. split; [exact R3'|]. split; [exact R4'|]. split; [exact INV'|]. split; [lia|].
      eapply frame_mod_trans_same; [exact PM1 | exact PM'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pcall_regions : list (word * Z) := (Z_to_bv 64 (sp0 - 3312), 544%Z) :: pc_regions sp0.

  Variable its : list fitem.
  Hypothesis ITS : flat its = fbs.
  Hypothesis WF : wf_items its = true.
  Hypothesis COK0 : convs_ok 0 (convs its).
  Hypothesis NC7 : (Z.of_nat (length (convs its)) <= 7)%Z.
  Hypothesis REM : (rem its + 56 <= INT_MAX)%Z.

  Theorem printf_core_p2 : forall m regs (ret : word) (u j : Z),
    regs = regs0 -> ret = ret0 -> ret_ok ret ->
    FRM sp0 mem0 m -> FILEc m sp0 -> FILEst m sp0 u j ->
    rdn SEGS m (Z_to_bv 64 (sp0 - 2768)) 8 = Some (W8 (sp0 - 56)) ->
    (forall q, (0 <= q < 7)%Z -> VAslot m sp0 q (va q)) ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 (sp0 - 2768) ->
    getr regs 10 = Z_to_bv 64 (sp0 - 2400) -> getr regs 11 = Z_to_bv 64 fa -> getr regs 12 = Z_to_bv 64 (sp0 - 2768) ->
    getr regs 3 = g3 -> getr regs 4 = g4 ->
    exists r' m',
      msteps SEGS (mkst regs (rl dF_17f6c 0x17f6c) m rom) (mkst r' ret m' rom)
      /\ (getr r' 2 = Z_to_bv 64 (sp0 - 2768)
          /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr regs x)
          /\ frame_mod m m' pcall_regions
          /\ FILEc m' sp0
          /\ (exists u' j', FILEst m' sp0 u' j' /\ (j <= j')%Z)).
  Proof.
    intros m regs ret u j -> -> Hret F FC FS AP VA H1 H2 H10 H11 H12 H3 H4. pose proof Hcsp as Hsp0.
    destruct (prologue_run sp0 mem0 cv rom CTX g3 g4 m regs0 ret0 (sp0 - 2400) fa F H3 H4 H1 H2 H10 H11 H12) as (r1 & RUN1 & PR1).
    set (m1 := proM sp0 cv m regs0 ret0) in *.
    pose proof (proM_PCc sp0 mem0 cv CTX m regs0 ret0) as PC1. fold m1 in PC1.
    pose proof (proM_frame sp0 mem0 cv CTX m regs0 ret0) as FM1. fold m1 in FM1.
    assert (LF1 : low_frame sp0 m m1).
    { eapply low_frame_sub; [exact FM1|]. intros x Hx. cbn [outside]. unfold in_rng. lay. unorm. lia. }
    assert (F1 : FRM sp0 mem0 m1).
    { eapply FRM_sub; [exact F | exact FM1|]. intros a Ho. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (INV1 : INV2 m1 0 u j).
    { split.
      - exact F1.
      - exact PC1.
      - eapply FILEc_low; [lay; lia | exact FC | exact LF1].
      - eapply FILEst_low; [lay; lia | exact FS | exact LF1].
      - rewrite Z.mul_0_r, Z.add_0_r. eapply cell_low; [exact LF1 | lay; lia | lia | cbn; lay; lia | exact AP].
      - intros q Hq. unfold VAslot. eapply cell_low; [exact LF1 | lay; lia | lia | cbn; lay; lia | apply VA; exact Hq]. }
    assert (SUF0 : suffix_at fa its).
    { split; [|split; [rewrite ITS; lia | lia]]. intros i Hi. unfold fbyte. rewrite <- ITS. f_equal. lia. }
    destruct (pass2_loop its m1 r1 fa 0 0 0 u j WF COK0 ltac:(lia) ltac:(lia) SUF0 INV1 PR1 ltac:(lia) ltac:(lia) ltac:(lia))
      as (r2 & m2 & k2 & u2 & j2 & RUN2 & R2' & R3' & R4' & INV2' & Hj2 & PM2).
    destruct INV2' as [F2 PC2 FC2 FS2 AP2 VA2].
    destruct (epilogue_run sp0 mem0 cv rom CTX g3 g4 m2 r2 regs0 ret0 (getr r2 19) F2 PC2 Hret R2' eq_refl R3' R4')
      as (r3 & RUN3 & A10 & S2 & S1 & SK & S3 & S4).
    exists r3, m2. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2 | exact RUN3].
    - split; [exact S2|].
      split; [intros x Hx; cbv [In] in Hx; destruct Hx as [<-|[<-|Hx]];
              [rewrite S3; symmetry; exact H3 | rewrite S4; symmetry; exact H4 | apply SK; exact Hx] |]. split.
      + unfold pcall_regions. eapply (frame_mod_trans _ _ _ [(Z_to_bv 64 (sp0 - 3312), 544%Z)] (pc_regions sp0)); [exact FM1 | exact PM2].
      + split; [exact FC2|]. exists u2, j2. split; [exact FS2 | exact Hj2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma pass1_nolit : forall rest m r (p cnt l : Z) regs ret,
    match rest with FLit _ :: _ => False | _ => True end ->
    suffix_at p rest -> FRM sp0 mem0 m -> PCc m sp0 cv regs ret ->
    pcR sp0 g3 g4 r 0 p cnt l -> (0 <= cnt)%Z -> (0 <= l)%Z -> (cnt + l + 256 <= INT_MAX)%Z ->
    exists r', msteps SEGS (mkst r (rl dF_17f6c 0x1801c) m rom) (mkst r' (rl dF_17f6c 0x18d48) m rom)
               /\ getr r' 2 = Z_to_bv 64 (sp0 - 3312) /\ getr r' 19 = Z_to_bv 64 0 /\ getr r' 3 = g3 /\ getr r' 4 = g4.
  Proof.
    intros rest m r p cnt l regs ret NL (SUF & LEN & FAP) F PC PR Hc0 Hl Hbd. pose proof Hcsp as Hsp0.
    pose proof PR as (R3 & R4 & R2 & R8 & R9 & R19 & R20 & R21 & R26).
    destruct rest as [|[bs|c] rest]; [| destruct NL |].
    - (* [comment removed for export] *)
      cbn [flat length] in SUF, LEN.
      assert (B0 : rdn SEGS m (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 0]).
      { pose proof (SUF 0%nat ltac:(lia)) as E. cbn in E. rewrite Z.add_0_r in E. rewrite <- E. apply fmt_rd; [exact F | lia]. }
      destruct (head_end_run sp0 mem0 cv rom CTX g3 g4 m r 0 p cnt l PR Hc0 Hl ltac:(unfold INT_MAX in *; lia)
                  ltac:(lia) ltac:(lay; lia) B0) as [_ RUN0].
      destruct (RUN0 eq_refl (Pc88 _ _ _ _ _ PC)) as (r' & RUN & R2' & R19' & R3' & R4').
      exists r'. split; [exact RUN|]. repeat split; assumption.
    - (* [comment removed for export] *)
      cbn [flat] in SUF, LEN. rewrite length_app in SUF, LEN.
      pose proof (conv_bytes_len c) as CBL. assert (CL : (2 <= conv_len c <= 3)%Z) by (destruct c; cbn; lia).
      pose proof (flat_len_pos rest) as FLP.
      assert (Hp : (IMG_LO <= p /\ p + conv_len c < IMG_TOP)%Z) by (lay; lia).
      assert (B0 : rdn SEGS m (Z_to_bv 64 p) 1 = Some [Z_to_bv 8 37]).
      { pose proof (SUF 0%nat ltac:(lia)) as E. rewrite Z.add_0_r in E.
        replace (nth 0 (conv_bytes c ++ flat rest) 0%Z) with 37%Z in E by (destruct c; reflexivity).
        rewrite <- E. apply fmt_rd; [exact F | lia]. }
      assert (B1 : rdn SEGS m (Z_to_bv 64 (p + 1)) 1 = Some [Z_to_bv 8 (conv_c1 c)]).
      { pose proof (SUF 1%nat ltac:(lia)) as E.
        replace (nth 1 (conv_bytes c ++ flat rest) 0%Z) with (conv_c1 c) in E by (destruct c; reflexivity).
        replace (p + Z.of_nat 1)%Z with (p + 1)%Z in E by lia. rewrite <- E. apply fmt_rd; [exact F | lia]. }
      assert (B2 : c = Czu -> rdn SEGS m (Z_to_bv 64 (p + 2)) 1 = Some [Z_to_bv 8 117]).
      { intros ->. pose proof (SUF 2%nat ltac:(cbn in *; lia)) as E. cbn [conv_bytes app nth] in E.
        replace (p + Z.of_nat 2)%Z with (p + 2)%Z in E by lia. rewrite <- E. apply fmt_rd; [exact F | cbn in *; lia]. }
      destruct (conv_head sp0 mem0 cv rom CTX g3 g4 m p c Hp B0 B1 B2 r 0 cnt l PR Hc0 Hl ltac:(unfold INT_MAX in *; lia) ltac:(lia))
        as (r1 & RUN1 & Q3 & Q4 & Q2 & Q8 & Q9 & Q19 & Q20 & Q21 & Q23 & Q26 & Q22 & Q18).
      destruct (conv_out0_p1 rom m r1 Q20 Q22) as (r2 & RUN2 & K2).
      destruct (conv_parse sp0 mem0 cv rom CTX m p c Hp B1 B2 r2 regs ret F PC ltac:(rewrite K2; exact Q2) ltac:(rewrite K2; exact Q21))
        as (r3 & RUN3 & P11 & P27 & P21 & P5 & P25 & P24 & P22 & P10 & PK).
      destruct (conv_pass1_exit rom m r3 ltac:(rewrite PK by indec; rewrite K2; exact Q20)) as (r4 & RUN4 & Z19 & ZK).
      exists r4. split.
      + eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3 | exact RUN4].
      + split; [rewrite ZK by (intros E; discriminate E); rewrite PK by indec; rewrite K2; exact Q2 |].
        split; [exact Z19|].
        split; [rewrite ZK by (intros E; discriminate E); rewrite PK by indec; rewrite K2; exact Q3
              | rewrite ZK by (intros E; discriminate E); rewrite PK by indec; rewrite K2; exact Q4].
  Qed.

  Theorem printf_core_p1 : forall m regs (ret : word),
    ret_ok ret -> FRM sp0 mem0 m ->
    getr regs 1 = ret -> getr regs 2 = Z_to_bv 64 (sp0 - 2768) ->
    getr regs 10 = Z_to_bv 64 0 -> getr regs 11 = Z_to_bv 64 fa -> getr regs 12 = Z_to_bv 64 (sp0 - 2768) ->
    getr regs 3 = g3 -> getr regs 4 = g4 ->
    exists r',
      msteps SEGS (mkst regs (rl dF_17f6c 0x17f6c) m rom) (mkst r' ret (proM sp0 cv m regs ret) rom)
      /\ (getr r' 2 = Z_to_bv 64 (sp0 - 2768) /\ getr r' 10 = Z_to_bv 64 0
          /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r' x = getr regs x)).
  Proof.
    intros m regs ret Hret F H1 H2 H10 H11 H12 H3 H4. pose proof Hcsp as Hsp0.
    destruct (prologue_run sp0 mem0 cv rom CTX g3 g4 m regs ret 0 fa F H3 H4 H1 H2 H10 H11 H12) as (r1 & RUN1 & PR1).
    set (m1 := proM sp0 cv m regs ret) in *.
    pose proof (proM_PCc sp0 mem0 cv CTX m regs ret) as PC1. fold m1 in PC1.
    pose proof (proM_frame sp0 mem0 cv CTX m regs ret) as FM1. fold m1 in FM1.
    assert (F1 : FRM sp0 mem0 m1).
    { eapply FRM_sub; [exact F | exact FM1|]. intros a Ho. cbn [outside] in Ho |- *. unfold in_rng in *. lay. revert Ho. unorm. intros Ho. repeat split; lia. }
    assert (SUF0 : suffix_at fa its).
    { split; [|split; [rewrite ITS; lia | lia]]. intros i Hi. unfold fbyte. rewrite <- ITS. f_equal. lia. }
    pose proof REM as REM'. unfold rem in REM'. pose proof (lit_total_nonneg its) as LT0.
    (* [comment removed for export] *)
    assert (MID : exists r2 p cnt l, msteps SEGS (mkst r1 (rl dF_17f6c 0x1801c) m1 rom) (mkst r2 (rl dF_17f6c 0x1801c) m1 rom)
             /\ pcR sp0 g3 g4 r2 0 p cnt l /\ (0 <= cnt)%Z /\ (0 <= l)%Z /\ (cnt + l + 256 <= INT_MAX)%Z
             /\ exists rest, suffix_at p rest /\ match rest with FLit _ :: _ => False | _ => True end).
    { destruct its as [|[bs|c] rest] eqn:EI.
      - exists r1, fa, 0%Z, 0%Z. split; [apply mst_refl|]. split; [exact PR1|]. split; [lia|]. split; [lia|].
        split; [unfold INT_MAX; lia|]. exists []. split; [exact SUF0 | exact I].
      - (* [comment removed for export] *)
        cbn [wf_items] in WF. apply andb_prop in WF as [WF0 WFr]. apply andb_prop in WF0 as [WF0 NOLIT]. apply andb_prop in WF0 as [NE LB].
        destruct SUF0 as (SUF & LEN & FAP). cbn [flat] in SUF, LEN. rewrite length_app in SUF, LEN.
        cbn [lit_total convs] in REM', NC7.
        set (n := Z.of_nat (length bs)) in *.
        assert (Hn : (1 <= n)%Z) by (destruct bs; [discriminate NE | cbn in *; lia]).
        pose proof (flat_len_pos rest) as FLP. pose proof (lit_total_nonneg rest) as LT1.
        assert (Hp : (rl_img_lo <= fa /\ fa + n < rl_img_hi)%Z) by (lay; lia). pf_bounds.
        assert (BL : forall q, (fa <= q < fa + n)%Z -> (1 <= fbyte q <= 255 /\ fbyte q <> 37)%Z).
        { intros q Hq. pose proof (SUF (Z.to_nat (q - fa)) ltac:(lia)) as E.
          replace (fa + Z.of_nat (Z.to_nat (q - fa)))%Z with q in E by lia. rewrite E. rewrite app_nth1 by lia.
          assert (LBq := proj1 (forallb_forall _ _) LB (nth (Z.to_nat (q - fa)) bs 0%Z) ltac:(apply nth_In; lia)).
          unfold lit_byte in LBq. apply andb_prop in LBq as [LBq N37]. apply andb_prop in LBq as [L1 L255].
          apply Z.leb_le in L1. apply Z.leb_le in L255. destruct (Z.eqb_spec (nth (Z.to_nat (q - fa)) bs 0%Z) 37); [discriminate N37|]. lia. }
        assert (BYrd : forall q, (fa <= q <= fa + n)%Z -> rdn SEGS m1 (Z_to_bv 64 q) 1 = Some [Z_to_bv 8 (fbyte q)]).
        { intros q Hq. apply fmt_rd; [exact F1 | lia]. }
        assert (BEc : fbyte (fa + n)%Z = nth 0 (flat rest) 0%Z).
        { pose proof (SUF (length bs) ltac:(lia)) as E. fold n in E. rewrite E. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. }
        assert (Hc : nth 0 (flat rest) 0%Z = 0%Z
                     \/ (nth 0 (flat rest) 0%Z = 37%Z /\ exists d, rdn SEGS m1 (Z_to_bv 64 (fa + n + 1)) 1 = Some [Z_to_bv 8 d] /\ (0 <= d <= 255)%Z /\ d <> 37%Z)).
        { destruct rest as [|[bs'|c'] rest'].
          - left. reflexivity.
          - discriminate NOLIT.
          - right. assert (CL : (2 <= conv_len c')%Z) by (destruct c'; cbn; lia).
            pose proof (conv_bytes_len c') as CBL. cbn [flat] in LEN. rewrite length_app in LEN.
            split; [destruct c'; reflexivity|].
            exists (fbyte (fa + n + 1)%Z). split; [apply fmt_rd; [exact F1 | lia]|].
            pose proof (SUF (length bs + 1)%nat ltac:(cbn [flat]; rewrite length_app; lia)) as E.
            replace (fa + Z.of_nat (length bs + 1))%Z with (fa + n + 1)%Z in E by lia. rewrite E.
            rewrite app_nth2 by lia. replace (length bs + 1 - length bs)%nat with 1%nat by lia.
            cbn [flat]. destruct c'; cbn; lia. }
        pose proof PR1 as (R3 & R4 & R2 & R8 & R9 & R19 & R20 & R21 & R26).
        destruct (lit_scan sp0 mem0 cv rom CTX g3 g4 m1 fa n (nth 0 (flat rest) 0%Z) fbyte Hn Hp BYrd BL BEc Hc r1 0 0 0 PR1
                    ltac:(lia) ltac:(lia) ltac:(unfold INT_MAX in *; lia) ltac:(lia))
          as (q1 & RUNa & Q3 & Q4 & Q2 & Q8 & Q9 & Q19 & Q20 & Q21 & Q23 & Q26 & Q22 & Q18).
        destruct (lit_tail1 sp0 mem0 cv rom CTX g3 g4 m1 fa n Hn Hp q1 (0 + 0) Q2 Q8 Q9 Q19 Q20 Q21 Q26 Q22 Q3 Q4) as (q2 & RUNb & PR2).
        exists q2, (fa + n)%Z, (0 + 0)%Z, n. split; [eapply msteps_trans; [exact RUNa | exact RUNb]|].
        split; [exact PR2|]. split; [lia|]. split; [lia|]. split; [unfold INT_MAX in *; lia|].
        exists rest. split.
        + split; [|split; [lia|lia]]. intros i Hi. pose proof (SUF (length bs + i)%nat ltac:(lia)) as E.
          replace (fa + Z.of_nat (length bs + i))%Z with (fa + n + Z.of_nat i)%Z in E by lia. rewrite E.
          rewrite app_nth2 by lia. f_equal. lia.
        + destruct rest as [|[bs'|c'] rest']; [exact I | discriminate NOLIT | exact I].
      - exists r1, fa, 0%Z, 0%Z. split; [apply mst_refl|]. split; [exact PR1|]. split; [lia|]. split; [lia|].
        split; [unfold INT_MAX; lia|]. exists (FConv c :: rest). split; [exact SUF0 | exact I]. }
    destruct MID as (r2 & p & cnt & l & RUN2 & PR2 & Hc0 & Hl & Hbd & rest & SUFr & NL).
    destruct (pass1_nolit rest m1 r2 p cnt l regs ret NL SUFr F1 PC1 PR2 Hc0 Hl Hbd) as (r3 & RUN3 & S2 & S19 & S3 & S4).
    destruct (epilogue_run sp0 mem0 cv rom CTX g3 g4 m1 r3 regs ret (Z_to_bv 64 0) F1 PC1 Hret S2 S19 S3 S4)
      as (r4 & RUN4 & A10 & T2 & T1 & TK & T3 & T4).
    exists r4. split.
    - eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3 | exact RUN4].
    - split; [exact T2|]. split; [exact A10 |].
      intros x Hx; cbv [In] in Hx; destruct Hx as [<-|[<-|Hx]];
        [rewrite T3; symmetry; exact H3 | rewrite T4; symmetry; exact H4 | apply TK; exact Hx].
  Qed.
End TOP.
