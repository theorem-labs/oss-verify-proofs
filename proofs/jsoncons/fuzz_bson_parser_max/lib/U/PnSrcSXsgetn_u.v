(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.LeanFeed.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core L5CoreKit
     PmLayout. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnLayoutS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmModel PmModelFacts PmStatics PmSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmStep PmKeep. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnKitS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmFrame PmParSpecs. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnParSpecsS_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PmParKit.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.U Require Import PnSrcSMemmove_u PnSrcSXsgetnP_u Bs0_code_r5b260_5b264_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import BMode.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PMSXG.
Import PMS.

(* [comment removed for export] *)
Ltac tr64 M0 AG := lazymatch goal with |- L5.u64_at ?sg ?M2 ?a ?v =>
  let X := fresh "X" in assert (X : L5.u64_at sg M0 a v) by PMK.gmem;
  apply (L5C.u64_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.
Ltac tr32 M0 AG := lazymatch goal with |- L5.u32_at ?sg ?M2 ?a ?v =>
  let X := fresh "X" in assert (X : L5.u32_at sg M0 a v) by PMK.gmem;
  apply (PMF.u32_at_agree sg M0 M2 a v); [apply AG; lia | lia | lia | exact X] end.

Section WithHeap.
Context {SCFG_P : ScfgP}. Context {bmK : BMode}.   (* [comment removed for export] *)
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : PMS.layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Let KL := PMKS.klayout_S L LY.

Theorem xsgetn_ok : PMPSS.xsgetn_spec L HI.
Proof.
  unfold PMPSS.xsgetn_spec, PMPS.xsgetn_spec.
  intros fx R M model K LB cr sp r ois dst str sm HH MOK K0 ENT A10 A11 A12 Hsp Htop Hal ISS BASE OWN DSTB APART KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & STK).
  pose proof MOK as (Mh & Ml & Mm). pose proof STK as (A16 & SLO & SHI & STOP & SDEF). pose proof RAok as (Hr1 & Hr2).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  change (PMSP.pm_scr 2) with 16384 in *. unfold PM.CHUNK in *.
  assert (SC0 : 0 <= 16384) by lia.
  assert (BR : PMFR.brange L LB) by (apply (PMFR.brange_of_heap L HI HIok LB LB cr M _ HH); apply incl_refl).
  pose proof (L5C.stk_writable RSEGS _ M sp 16384 STK) as WR.
  destruct BASE as (IMG & _).
  cbn [pa_rw_lo AD PnLayoutS_u.ADDR_S] in IMG.
  destruct sm as [g eg st]. cbn [PM.sm_g PM.sm_eg PM.sm_st] in *.
  pose proof (PMPK.iss_size_lt RSEGS AD M ois str _ ISS) as SZ. cbn [PM.sm_g PM.sm_eg] in SZ.
  pose proof ISS as (I0 & IDEF & _ & I16 & I24 & I32 & I40 & I48 & I64 & IVS & I104 & I112 & IIOS & IE1 & IE2).
  cbn [PM.sm_g PM.sm_eg PM.sm_st pa_vp_strbuf AD PnLayoutS_u.ADDR_S] in *.
  clear IE1.
  destruct DSTB as (B & m & DIN & DLO & DHI). destruct (BR B m DIN) as (BQ0 & BQ1 & BQ4). unfold hl_ceil in BQ4. rewrite (ly_img_lo L LY), (ly_img_hi L LY) in BQ1.
  assert (G0 : 4096 <= g).
  { pose proof (PMPK.iss_unread_where RSEGS AD M ois str _ ISS) as [(X1 & X2)|(c & n & p & -> & X1 & X2)]; cbn [PM.sm_g PM.sm_eg] in *; [lia|].
    destruct (BR p c (OWN _ (or_introl eq_refl))) as (Q0 & _). lia. }
  assert (GHI : eg <= 2 ^ 47).
  { pose proof (PMPK.iss_unread_where RSEGS AD M ois str _ ISS) as [(X1 & X2)|(c & n & p & -> & X1 & X2)]; cbn [PM.sm_g PM.sm_eg] in *; [lia|].
    destruct (BR p c (OWN _ (or_introl eq_refl))) as (_ & _ & Q4). unfold hl_ceil in Q4. lia. }
  destruct (Z.eq_dec eg g) as [EQ|NE].
  - (* [comment removed for export] *)
    subst eg.
    LeanFeed.pfeed P (PMSXGP.xgA0_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => g | 36%nat => ois + 16 | 37%nat => dst | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSXGP.aligned; first [exact A16 | apply (PMPK.m8_add ois 2 Hal)]]).
    PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & X10 & _)); PMK.pvz_clrT.
    set (P := fun a => sp - 80 <= a < sp - 80 + 80).
    assert (PF : forall a, P a -> sp - 16384 <= a < sp) by (intros a X; unfold P in X; lia).
    unfold PMSP.cfg. cbn [pa_xsgetn AD PnLayoutS_u.ADDR_S].
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x5d574 R1 0x5d67c M1 P K HH Mh Ml ltac:(lia) MS MG FRZ).
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 16384 a STK). apply PF in Pa. lia. }
    { intros a. apply PMK.rng_dec. }
    intros HH1.
    assert (EK1 : PMK.ek L LB sp 16384 [] M M1) by (apply (PMFR.ek_of_piece RSEGS L KL LB sp 16384 M M1 P FRZ STK (PMFR.brange_hi L LB BR) PF)).
    assert (WHI0 : forall a, PMK.inW [] a -> sp <= a \/ hl_img_lo L <= a < hl_img_hi L) by (intros a I; destruct (PMFR.inW_nil a I)).
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
    { apply (PMK.ret_to RSEGS fx1 R1 M1 0x5d67c W_5c03c r F_5c03c eq_refl D_5c03c); [rewrite (KS 1%nat) by PMK.inl; exact Rra| lia| exact Hr2]. }
    apply (KONT fx1 R1 M1 0).
    + apply PMK.preserved_by_index. intros k Hk. apply KS. revert k Hk. apply (PMPK.cs_in PMSXGP.KS_xgA0). vm_compute. reflexivity.
    + rewrite L5K.rl10. exact X10.
    + lia.
    + replace (g + 0) with g by lia.
      apply (PMFR.iss_keep RSEGS AD L KL LB sp 16384 [] M M1 EK1 STK SC0 BR WHI0); [lia|lia| intros i _; apply PMFR.inW_nil| exact OWN| exact ISS].
    + intros i Hi. lia.
    + apply (PMK.hpres_of L LB sp 16384 _ M M1).
      * apply (PMK.ek_weaken L LB LB sp 16384 sp 16384 _ [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
      * apply (L5.defined_grows M M1 _ _ MG). exact SDEF.
      * apply (PMK.dk_grows L LB sp 16384 M M1 MG).
    + exact HH1.
  - (* [comment removed for export] *)
    set (len := Z.min 16384 (eg - g)).
    assert (LEN : 1 <= len <= 16384) by (unfold len; lia).
    assert (DSTW : L5.writable RSEGS M dst 16384).
    { pose proof (proj1 (hio_wf L SCFG HI HIok LB cr M _ HH) (B, m) DIN) as (_ & DB & _). cbn [fst snd] in DB.
      apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M B m); [exact DB|lia|lia]| lia| lia]. }
    pose proof (PMPK.iss_unread_defined RSEGS AD M ois str _ ISS) as SRCD. cbn [PM.sm_g PM.sm_eg] in SRCD.
    (* [comment removed for export] *)
    assert (HEAD : exists fx1 R1 M1, msteps RSEGS (@mkst fx R (Z_to_bv 64 0x5d574) M (seg_rom RSEGS)) (@mkst fx1 R1 (Z_to_bv 64 0xab884) M1 (seg_rom RSEGS))
              /\ mem_grows M M1 /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i))
              /\ (forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R1 (PMK.reg x) = getr R (PMK.reg x))
              /\ getr R1 (PMK.reg 1) = Z_to_bv 64 382536 /\ getr R1 (PMK.reg 2) = Z_to_bv 64 (sp - 64)
              /\ getr R1 (PMK.reg 8) = Z_to_bv 64 0 /\ getr R1 (PMK.reg 9) = Z_to_bv 64 16384
              /\ getr R1 (PMK.reg 10) = Z_to_bv 64 dst /\ getr R1 (PMK.reg 11) = Z_to_bv 64 g /\ getr R1 (PMK.reg 12) = Z_to_bv 64 len
              /\ getr R1 (PMK.reg 19) = Z_to_bv 64 (ois + 16) /\ getr R1 (PMK.reg 20) = Z_to_bv 64 len
              /\ getr R1 (PMK.reg 21) = Z_to_bv 64 2147483647 /\ getr R1 (PMK.reg 22) = Z_to_bv 64 18446744073709551615
              /\ L5.u64_at RSEGS M1 (sp - 64) (bv_unsigned (getr R (PMK.reg 22))) /\ L5.u64_at RSEGS M1 (sp - 56) (bv_unsigned (getr R (PMK.reg 21)))
              /\ L5.u64_at RSEGS M1 (sp - 48) (bv_unsigned (getr R (PMK.reg 20))) /\ L5.u64_at RSEGS M1 (sp - 40) (bv_unsigned (getr R (PMK.reg 19)))
              /\ L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (PMK.reg 18))) /\ L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (PMK.reg 9)))
              /\ L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (PMK.reg 8))) /\ L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (PMK.reg 1)))).
    { destruct (Z_le_gt_dec (eg - g) 16384) as [LE|GT].
      - assert (len = eg - g) as -> by (unfold len; lia).
        pose proof (PMSXGP.xgA1_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => g | 35%nat => eg - g | 36%nat => ois + 16 | 37%nat => dst | _ => 0 end)) as P. cbn beta iota in P.
        replace (g + (eg - g)) with eg in P by lia.
        PMK.feed P ltac:(first [PMK.sc | unfold PMSXGP.aligned; first [exact A16 | apply (PMPK.m8_add ois 2 Hal)]]).
        PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X18 & X19 & X20 & X21 & X22 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7)); PMK.pvz_clrT.
        exists fx1, R1, M1. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
        split. { intros x Hx. apply KS. revert x Hx. apply (PMPK.sub_in PMSXGP.KS_xgA1). vm_compute. reflexivity. }
        repeat (split; [assumption|]). assumption.
      - assert (len = 16384) as -> by (unfold len; lia).
        pose proof (PMSXGP.xgA2_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => g | 35%nat => eg - g | 36%nat => ois + 16 | 37%nat => dst | _ => 0 end)) as P. cbn beta iota in P.
        replace (g + (eg - g)) with eg in P by lia.
        PMK.feed P ltac:(first [PMK.sc | unfold PMSXGP.aligned; first [exact A16 | apply (PMPK.m8_add ois 2 Hal)]]).
        PMK.pvz_hg ltac:(idtac; destruct P as (fx1 & R1 & M1 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & X1 & X2 & X8 & X9 & X10 & X11 & X18 & X19 & X20 & X21 & X22 & C0 & C1 & C2 & C3 & C4 & C5 & C6 & C7)); PMK.pvz_clrT.
        assert (X12 : getr R1 (PMK.reg 12) = Z_to_bv 64 16384) by (rewrite (KS 12%nat) by PMK.inl; exact A12).
        exists fx1, R1, M1. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
        split. { intros x Hx. apply KS. revert x Hx. apply (PMPK.sub_in PMSXGP.KS_xgA2). vm_compute. reflexivity. }
        repeat (split; [assumption|]). assumption. }
    destruct HEAD as (fx1 & R1 & M1 & MS1 & MG1 & FRZ1 & KS1 & X1 & X2 & X8 & X9 & X10 & X11 & X12 & X19 & X20 & X21 & X22 & S64 & S56 & S48 & S40 & S32 & S24 & S16 & S8).
    set (P1 := fun a => sp - 80 <= a < sp - 80 + 80).
    assert (PF1 : forall a, P1 a -> sp - 16384 <= a < sp) by (intros a X; unfold P1 in X; lia).
    unfold PMSP.cfg. cbn [pa_xsgetn AD PnLayoutS_u.ADDR_S].
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M model fx fx1 R 0x5d574 R1 0xab884 M1 P1 K HH Mh Ml ltac:(lia) MS1 MG1 FRZ1).
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 16384 a STK). apply PF1 in Pa. lia. }
    { intros a. apply PMK.rng_dec. }
    intros HH1.
    assert (STK1 : L5C.stk (hl_sptop L) M1 sp 16384) by (apply (PMK.stk_grows L M M1 sp 16384 MG1 STK)).
    assert (EK1 : PMK.ek L LB sp 16384 [] M M1) by (apply (PMFR.ek_of_piece RSEGS L KL LB sp 16384 M M1 P1 FRZ1 STK (PMFR.brange_hi L LB BR) PF1)).
    (* [comment removed for export] *)
    destruct (PMCPS.memmove_run fx1 R1 M1 dst g len 382536 X10 X11 X12 X1 ltac:(split; [lia| reflexivity]) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold len in *; lia)
                ltac:(apply (L5.writable_grows RSEGS M M1 _ _ MG1); apply (L5.writable_sub RSEGS M dst 16384); [exact DSTW|lia|lia])
                ltac:(apply (L5.defined_grows M M1 _ _ MG1); apply (L5.defined_sub M g (eg - g)); [exact SRCD|lia|unfold len; lia]))
      as (R2 & M2 & MS2 & MG2 & FRZ2 & DD2 & KS2 & Y10).
    set (P2 := fun a => dst <= a < dst + len).
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M1 model fx1 fx1 R1 0xab884 R2 382536 M2 P2 K HH1 Mh Ml ltac:(lia) MS2 MG2 FRZ2).
    { intros a Pa. apply (PMK.cwr_block L LB B m a DIN). unfold P2 in Pa. lia. }
    { intros a. apply PMK.rng_dec. }
    intros HH2.
    set (W := [(ois + 40, 8); (dst, 16384)] : list L5.range).
    assert (STK2 : L5C.stk (hl_sptop L) M2 sp 16384) by (apply (PMK.stk_grows L M1 M2 sp 16384 MG2 STK1)).
    assert (EK2 : PMK.ek L LB sp 16384 W M1 M2).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 16384 W M1 M2 P2 FRZ2 STK1 (PMFR.brange_hi L LB BR)). intros a Pa. right. unfold W.
      apply PMK.inW_next. apply PMK.inW_here. unfold P2 in Pa. lia. }
    assert (AG02 : forall a n, sp - 80 <= a -> a + n <= 2 ^ 64 -> (sp <= a \/ a + n <= sp) -> L5C.agree_on M M2 a n \/ True) by (intros; right; exact I).
    assert (HIAG : forall a n, sp <= a -> a + n <= 2 ^ 64 -> L5C.agree_on M M2 a n).
    { intros a n H1 H2 i Hi. rewrite FRZ2 by (unfold P2; lia). apply FRZ1; unfold P1; lia. }
    assert (FRAG : forall a n, sp - 80 <= a -> a + n <= sp -> L5C.agree_on M1 M2 a n).
    { intros a n H1 H2 i Hi. apply FRZ2; unfold P2; lia. }
    assert (IMG2 : L5.img_clear M2 65536 754672).
    { intros i Hi. rewrite FRZ2 by (unfold P2; lia). rewrite FRZ1 by (unfold P1; lia). apply IMG. exact Hi. }
    pose proof (HIAG ois 272 ltac:(lia) ltac:(lia)) as AGI.
    assert (WR2 : L5.writable RSEGS M2 (sp - 80) 80).
    { apply (L5.writable_grows RSEGS M1 M2 _ _ MG2). apply (L5.writable_grows RSEGS M M1 _ _ MG1). apply (L5.writable_sub RSEGS M (sp - 16384) 16384); [exact WR|lia|lia]. }
    assert (WG2 : L5.writable RSEGS M2 (ois + 16 + 24) 8).
    { apply (L5.writable_grows RSEGS M1 M2 _ _ MG2). apply (L5.writable_grows RSEGS M M1 _ _ MG1).
      apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M ois 120); [exact IDEF|lia|lia]|lia|lia]. }
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 8))) as B8.
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 18))) as B18.
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 20))) as B20.
    pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (PMK.reg 22))) as B22.
    change (bv_modulus 64) with (2 ^ 64) in *.
    assert (TAIL : exists fx3 R3 M3, msteps RSEGS (@mkst fx1 R2 (Z_to_bv 64 0x5d648) M2 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0x5d67c) M3 (seg_rom RSEGS))
              /\ mem_grows M2 M3
              /\ (forall i : Z, 0 <= i < 2 ^ 64 -> ~ (sp - 80 <= i < sp - 80 + 80) -> ~ (ois + 16 + 24 <= i < ois + 16 + 24 + 8) -> M3 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i))
              /\ (forall x, In x [3; 4; 23; 24; 25; 26; 27]%nat -> getr R3 (PMK.reg x) = getr R2 (PMK.reg x))
              /\ getr R3 (PMK.reg 1) = getr R (PMK.reg 1) /\ getr R3 (PMK.reg 2) = Z_to_bv 64 sp
              /\ getr R3 (PMK.reg 8) = getr R (PMK.reg 8) /\ getr R3 (PMK.reg 9) = getr R (PMK.reg 9)
              /\ getr R3 (PMK.reg 18) = getr R (PMK.reg 18) /\ getr R3 (PMK.reg 19) = getr R (PMK.reg 19) /\ getr R3 (PMK.reg 20) = getr R (PMK.reg 20)
              /\ getr R3 (PMK.reg 21) = getr R (PMK.reg 21) /\ getr R3 (PMK.reg 22) = getr R (PMK.reg 22)
              /\ getr R3 (PMK.reg 10) = Z_to_bv 64 len /\ L5.u64_at RSEGS M3 (ois + 40) (g + len)).
    { destruct (Z.eq_dec len 16384) as [E16|N16].
      - idtac.
        rewrite E16 in X20.
        LeanFeed.pfeed P (PMSXGP.xgC1_conc fx1 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => g | 34%nat => eg | 36%nat => ois + 16
                     | 37%nat => bv_unsigned (getr R (PMK.reg 1)) | 38%nat => bv_unsigned (getr R (PMK.reg 8)) | 39%nat => bv_unsigned (getr R (PMK.reg 9))
                     | 40%nat => bv_unsigned (getr R (PMK.reg 18)) | 41%nat => bv_unsigned (getr R (PMK.reg 19)) | 42%nat => bv_unsigned (getr R (PMK.reg 20))
                     | 43%nat => bv_unsigned (getr R (PMK.reg 21)) | 44%nat => bv_unsigned (getr R (PMK.reg 22)) | _ => 0 end)) ltac:(first [PMK.sc | unfold PMSXGP.aligned; first [exact A16 | apply (PMPK.m8_add ois 2 Hal)] | tr64 M HIAG | tr32 M HIAG | tr64 M1 FRAG]).
        PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & T1 & T2 & T8 & T9 & T10 & T11 & T18 & T19 & T20 & T21 & T22 & CG & _)); PMK.pvz_clrT.
        rewrite PMPK.word_id in T1, T8, T9, T18, T19, T20, T21, T22.
        exists fx3, R3, M3. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
        split. { intros x Hx. apply KS. revert x Hx. apply (PMPK.sub_in PMSXGP.KS_xgC1). vm_compute. reflexivity. }
        rewrite E16. replace (ois + 40) with (ois + 16 + 24) by lia. repeat (split; [assumption|]). assumption.
      - assert (ELEN : eg = g + len) by (unfold len in *; lia).
        pose proof (PMSXGP.xgC2_conc fx1 R2 M2 (fun j => match j with 2%nat => sp | 33%nat => g | 35%nat => len | 36%nat => ois + 16
                     | 37%nat => bv_unsigned (getr R (PMK.reg 1)) | 38%nat => bv_unsigned (getr R (PMK.reg 8)) | 39%nat => bv_unsigned (getr R (PMK.reg 9))
                     | 40%nat => bv_unsigned (getr R (PMK.reg 18)) | 41%nat => bv_unsigned (getr R (PMK.reg 19)) | 42%nat => bv_unsigned (getr R (PMK.reg 20))
                     | 43%nat => bv_unsigned (getr R (PMK.reg 21)) | 44%nat => bv_unsigned (getr R (PMK.reg 22)) | _ => 0 end)) as P. cbn beta iota in P.
        rewrite <- ELEN in P.
        PMK.feed P ltac:(first [PMK.sc | unfold PMSXGP.aligned; first [exact A16 | apply (PMPK.m8_add ois 2 Hal)] | tr64 M HIAG | tr32 M HIAG | tr64 M1 FRAG]).
        PMK.pvz_hg ltac:(idtac; destruct P as (fx3 & R3 & M3 & pvzP); PMK.pvz_lin pvzP; destruct pvzP as (MG & FR & FRZ & MS & KS & T1 & T2 & T8 & T9 & T10 & T11 & T12 & T13 & T18 & T19 & T20 & T21 & T22 & CA & CB & CG & _)); PMK.pvz_clrT.
        rewrite PMPK.word_id in T1, T8, T9, T18, T19, T20, T21, T22.
        exists fx3, R3, M3. split; [exact MS|]. split; [exact MG|]. split; [exact FRZ|].
        split. { intros x Hx. apply KS. revert x Hx. apply (PMPK.sub_in PMSXGP.KS_xgC2). vm_compute. reflexivity. }
        rewrite ELEN in CG. replace (ois + 40) with (ois + 16 + 24) by lia. repeat (split; [assumption|]). assumption. }
    destruct TAIL as (fx3 & R3 & M3 & MS3 & MG3 & FRZ3 & KS3 & T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & T10 & CG).
    set (P3 := fun a => (sp - 80 <= a < sp - 80 + 80) \/ (ois + 16 + 24 <= a < ois + 16 + 24 + 8)).
    assert (FRZ3' : forall a, 0 <= a < 2 ^ 64 -> ~ P3 a -> M3 (Z_to_bv 64 a) = M2 (Z_to_bv 64 a)).
    { intros a Ha N. apply FRZ3; [exact Ha| |]; intros X; apply N; [left|right]; exact X. }
    apply (PMK.spiece RSEGS L HI KL HIok LB cr M2 model fx1 fx3 R2 0x5d648 R3 0x5d67c M3 P3 K HH2 Mh Ml ltac:(lia) MS3 MG3 FRZ3').
    { intros a Pa. apply (PMK.cwr_stack L LB M sp 16384 a STK). unfold P3 in Pa. lia. }
    { intros a. apply PMK.or_dec; apply PMK.rng_dec. }
    intros HH3.
    assert (EK3 : PMK.ek L LB sp 16384 W M2 M3).
    { apply (PMK.ek_piece_in RSEGS L KL LB sp 16384 W M2 M3 P3 FRZ3' STK2 (PMFR.brange_hi L LB BR)). intros a [Pa|Pa]; [left; lia|]. right. unfold W.
      apply PMK.inW_here. lia. }
    eapply (L5.cps_of_msteps RSEGS); [exact Mh| exact Ml| |].
    { apply (PMK.ret_to RSEGS fx3 R3 M3 0x5d67c W_5c03c r F_5c03c eq_refl D_5c03c); [rewrite T1; exact Rra| lia| exact Hr2]. }
    assert (MG03 : mem_grows M M3) by (apply (mem_grows_trans M M1 M3 MG1); apply (mem_grows_trans M1 M2 M3 MG2 MG3)).
    assert (AG03 : forall a n, sp <= a -> a + n <= 2 ^ 64 -> (a + n <= ois + 40 \/ ois + 48 <= a) -> L5C.agree_on M M3 a n).
    { intros a n H1 H2 H3 i Hi. rewrite FRZ3 by lia. apply (HIAG a n H1 H2 i Hi). }
    apply (KONT fx3 R3 M3 len).
    + apply PMK.preserved_by_index. intros k Hk. cbn in Hk.
      repeat (destruct Hk as [<-|Hk]; [first [ rewrite T2; symmetry; exact Rsp | assumption
                | (rewrite (KS3 _) by PMK.inl; rewrite (KS2 _) by PMK.inl; apply KS1; PMK.inl) ] |]). destruct Hk.
    + rewrite L5K.rl10. exact T10.
    + reflexivity.
    + apply (PMPK.iss_upd RSEGS AD M M3 ois str (PM.STRM g eg st) (g + len) st ISS); cbn [PM.sm_g PM.sm_eg PM.sm_st].
      * lia.
      * lia.
      * apply AG03; lia.
      * apply AG03; lia.
      * apply AG03; lia.
      * apply PMPK.dkr_grows. exact MG03.
      * apply PMPK.dkr_grows. exact MG03.
      * intros c n p _. apply PMPK.dkr_grows. exact MG03.
      * exact CG.
      * destruct IIOS as (_ & J32 & _). apply (PMF.u32_at_agree RSEGS M M3); [apply AG03; lia|lia|lia|].
        replace (ois + 152) with (ois + 120 + 32) by lia. exact J32.
      * unfold len. clear - IE2 LEN NE SZ. Lia.lia.
      * destruct IIOS as (_ & _ & _ & _ & _ & _ & _ & _ & ST). exact ST.
    + apply (L5.defined_grows M2 M3 _ _ MG3). exact DD2.
    + apply (PMK.hpres_of L LB sp 16384 _ M M3).
      * apply (PMK.ek_trans L LB sp 16384 W M M1 M3); [|apply (PMK.ek_trans L LB sp 16384 W M1 M2 M3 EK2 EK3)].
        apply (PMK.ek_weaken L LB LB sp 16384 sp 16384 W [] M M1 EK1); [apply incl_refl| intros x Hx; exact Hx|]. intros a _. apply L5C.outside_nil.
      * apply (L5.defined_grows M M3 _ _ MG03). exact SDEF.
      * apply (PMK.dk_grows L LB sp 16384 M M3 MG03).
    + exact HH3.
Qed.

End WithHeap.
End PMSXG.
