(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
#[local] Ltac Zify.zify ::= WdZS.wd_zs_stock.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemB2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemB2.AsAllocMMemB OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma jal_66fa4 : forall regs mem rom,
  msteps ASEGS (mkst regs (at_ ARB 0x4c070) mem rom) (mkst (regupd regs 1 (at_ ARB 0x4c074)) (at_ ARB 0x77588) mem rom).
Proof using.
  intros regs mem rom. rewrite !ARB_lit by lia. lit_pc.
  an F_4c068 D_4c068. close_eq.
Qed.

(* [comment removed for export] *)
Ltac notinB := try (lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); try (lazymatch goal with |- ?G => let G' := eval unfold ms_clob in G in change_no_check G' end); notin.
Ltac rchB := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]) end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, ~ In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by notinB end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notinB end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : ms_agree _ r |- _ => rewrite (AG i) by notinB end end
                          | match goal with |- getr (regupd _ ?i _) ?i = _ => rewrite getr_same by (intros E; discriminate E) end
                          | match goal with |- getr (regupd _ ?j _) ?i = _ => rewrite getr_other by (intros E; discriminate E) end ]).

(* [comment removed for export] *)
Ltac xfer L C := eapply rd_same; [intros x Hx; apply L; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact C].

(* [comment removed for export] *)
Ltac xferh G L C := unfold hideW in G; xfer L C.
(* [comment removed for export] *)
Lemma store_ok1_off : forall (m : mem) (a : word),
  (bv_unsigned a + 1 <= 0x10000 \/ 0x65d000 <= bv_unsigned a)%Z -> store_ok ASEGS m a 1%nat = true -> m a <> None.
Proof using.
  intros m a Ha S. pose proof (store_ok_all ASEGS m 1 a ltac:(pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) S a ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)) as W.
  unfold wview in W. destruct (m a); [discriminate | ].
  rewrite (find_segment1_none_outside ASEGS 0x10000 0x65d000 (bv_unsigned a) asanF_segs_in_hull) in W; [exact W|].
  destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

Section RUNB1.
  Variables (M rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp m : word) (T tctx n id FL MIDEND TSDP : Z) (h1 sb0 : byte).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation c := (class_of (needed n)).
  #[local] Abbreviation p := (at_ m (rz n)).
  (* [comment removed for export] *)
  Hypothesis H2 : getr r0 2 = sp2.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H8 : getr r0 8 = Z_to_bv 64 1.
  Hypothesis H9 : getr r0 9 = Z_to_bv 64 n.
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 id.
  Hypothesis H18 : getr r0 18 = m.
  Hypothesis H19 : getr r0 19 = Z_to_bv 64 (needed n).
  Hypothesis H20 : getr r0 20 = at_ m (rz n).
  Hypothesis H21 : getr r0 21 = at_ m (rz n - 16).
  Hypothesis H22 : getr r0 22 = Z_to_bv 64 0x103f18.
  Hypothesis H23 : getr r0 23 = at_ S (-2128).
  Hypothesis H24 : getr r0 24 = Z_to_bv 64 0.
  Hypothesis H25 : getr r0 25 = at_ m (rz n + n).
  Hypothesis H26 : getr r0 26 = thr.
  Hypothesis H27 : getr r0 27 = Z_to_bv 64 1.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis Hret : ret_ok (getr R 1).
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis Hid : (0 <= id < 2 ^ 32)%Z.
  (* [comment removed for export] *)
  Hypothesis GT : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584 /\ T mod 8 = 0)%Z.
  Hypothesis Gctx : ((1 <= tctx /\ hideW (tctx + 0x10000 <= 0x7fff7000 \/ 0x10007fff8000 <= tctx)) /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 0x40 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= TSDP /\ TSDP + 8 <= AIMGHI)%Z.
  Hypothesis GFL : (AIMGLO <= FL /\ FL + 4096 < AIMGHI)%Z.
  Hypothesis GME : (0 <= MIDEND < 2 ^ 64)%Z.
  Hypothesis Gm : (0x10007fff8000 <= U m /\ U m + needed n <= U S - 3584 /\ U m mod 16 = 0)%Z.
  Hypothesis Gm4 : (U m + 2 ^ 17 <= 2 ^ 47)%Z.
  Hypothesis GmT : (U m + needed n <= T \/ T + 4096 <= U m)%Z.
  Hypothesis Gmctx : (U m + needed n <= tctx \/ tctx + 4096 <= U m)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS M (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_inited : rdn ASEGS M (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn ASEGS M (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_fum : rdn ASEGS M (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn ASEGS M (Z_to_bv 64 0x10827c) 4 = Some (LE4 30).
  Hypothesis C_thr64 : rdn ASEGS M (Z_to_bv 64 (0x1990a8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615)).
  Hypothesis C_kif : rdn ASEGS M (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn ASEGS M (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn ASEGS M (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP)).
  Hypothesis C_tctx : rdn ASEGS M (Z_to_bv 64 TSDP) 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn ASEGS M (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_gsb : rdn ASEGS M (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578)).
  Hypothesis C_sb : rdn ASEGS M (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 SB)).
  Hypothesis C_cpm : rdn ASEGS M (Z_to_bv 64 0x106ddc) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gmb : rdn ASEGS M (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268)).
  Hypothesis C_mb : rdn ASEGS M (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn ASEGS M (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270)).
  Hypothesis C_me : rdn ASEGS M (Z_to_bv 64 0x108270) 8 = Some (LE8 (Z_to_bv 64 MIDEND)).
  Hypothesis C_ghe : rdn ASEGS M (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260)).
  Hypothesis C_he : rdn ASEGS M (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_gfl : rdn ASEGS M (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 FL)).
  Hypothesis C_pp : rdn ASEGS M (at_ (Z_to_bv 64 FL) 85) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mfs : rdn ASEGS M (at_ (Z_to_bv 64 FL) 44) 4 = Some (LE4 4096).
  Hypothesis C_fill : rdn ASEGS M (at_ (Z_to_bv 64 FL) 52) 4 = Some (LE4 0xbe).
  Hypothesis C_grm : rdn ASEGS M (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0)).
  Hypothesis C_rm : rdn ASEGS M (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4)).
  Hypothesis C_glsn : rdn ASEGS M (Z_to_bv 64 0xffec8) 8 = Some (LE8 (Z_to_bv 64 0x10)).
  Hypothesis C_lsn : rdn ASEGS M (at_ tp 0x10) 4 = Some (LE4 0).
  Hypothesis C_magic : rdn ASEGS M (Z_to_bv 64 0x103b8) 8 = Some (LE8 (Z_to_bv 64 MAGIC)).
  Hypothesis C_hook : rdn ASEGS M (Z_to_bv 64 0x199040) 8 = Some (LE8 (Z_to_bv 64 0)).
  (* [comment removed for export] *)
  Hypothesis C_Tw : store_ok ASEGS M thr 4096 = true.
  (* [comment removed for export] *)
  Hypothesis C_chunk : store_ok ASEGS M m (Z.to_nat (needed n)) = true.
  Hypothesis C_h1 : rdn ASEGS M (at_ m (rz n - 15)) 1 = Some [h1].
  Hypothesis C_sb0 : rdn ASEGS M (Z_to_bv 64 (SB + U m / 8)) 1 = Some [sb0].
  Hypothesis C_sb0nz : U sb0 <> 0%Z.
  Hypothesis C_shw : store_ok ASEGS M (Z_to_bv 64 (SB + (U m + rz n) / 8)) (Z.to_nat ((n + 7) / 8)) = true.
  (* [comment removed for export] *)
  Hypothesis C_fflag : rdn ASEGS M (at_ sp2 8) 8 = Some (LE8 (Z_to_bv 64 1)).

  Lemma nfB : (24 <= needed n <= 65536)%Z /\ (16 <= rz n <= 1024)%Z /\ (rz n + 8 <= needed n)%Z /\ (needed n = rounded n + rz n)%Z
              /\ (Z.max n 8 <= rounded n)%Z /\ (1 <= c <= 30)%Z /\ (rz n = 16 <-> rz_log n = 0)%Z /\ (0 <= n mod 8 < 8)%Z /\ (n mod 8 <= n)%Z.
  Proof using Gm Gn m S. exact (mbn S m n Gn Gm). Qed.

  (* [comment removed for export] *)
  Theorem run_mB1a :
    exists (r3 : bvmap 5 word),
      msteps ASEGS (mkst r0 (Z_to_bv 64 0x4bed0) M rom) (mkst r3 (Z_to_bv 64 0x4c070) (mb_3 M S m n id) rom)
      /\ (forall i : reg, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27] -> getr r3 i = getr r0 i).
  Proof using C_shw C_sb0nz C_sb0 C_chunk C_rm C_grm C_pp C_gfl C_he C_ghe C_me C_gme C_mb C_gmb C_cpm C_sb C_gsb C_thr64 C_gcf Hstk Gm4 Gm GME GFL Gtsdp Gtp Gctx GT Hid Gn GS H24 H21 H20 H19 H18 H10 H9 H8 H2 sb0 TSDP MIDEND FL tctx T tp.
    pose proof (u64_range S) as HSr. pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as ([GT1 GTS] & GT2 & GT3). destruct Gctx as ([Gc1 GcB] & Gc2 & Gc3). destruct Gtp as [Gtp1 Gtp2].
    destruct Gm as (Gm1 & Gm2 & Gm3). pose proof nfB as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6 & NF7 & NF8 & NF9).
    assert (GT' : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z) by exact (conj (conj GT1 GTS) GT2).
    assert (GS' : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z) by lia.
    assert (Gm' : (0x10007fff8000 <= U m /\ U m + needed n <= U S - 3584 /\ U m mod 16 = 0)%Z) by lia.
    pose proof (mb_shad S m n GS' Gn Gm') as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    pose proof (mb_shadow_range S m n GS' Gn Gm') as [SR1 SR2].
    assert (Nd8 : (0 <= n / 8 /\ n / 8 <= 8064 /\ 8 * (n / 8) = n - n mod 8)%Z) by (first [ solve [ clear - Gn; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]).
    assert (Nd8' : (n / 8 <= (n + 7) / 8 /\ (n + 7) / 8 <= n / 8 + 1 /\ (n mod 8 <> 0 -> (n + 7) / 8 = n / 8 + 1))%Z) by (first [ solve [ clear - Gn; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]).
    assert (Hif : (0 <= (if (n mod 8 =? 0)%Z then 0 else 1) <= 1)%Z) by (destruct (n mod 8 =? 0)%Z; lia).
    hidehyp NF7. hidehyp Nd8'.
    hidehyp Gc3. hidehyp GmT. hidehyp Gmctx.
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Uctx : U ctxw = tctx) by (unorm; reflexivity).
    assert (Hbsz : bytes_le_to_Z (LE8 (Z_to_bv 64 0)) = U (Z_to_bv 64 0) /\ length (LE8 (Z_to_bv 64 0)) = 8%nat) by (split; [apply bytes_le_to_Z_8 | apply length_N_to_le_bytes]).
    (* [comment removed for export] *)
    destruct (amD1 ASEGS ARB asan_HAL2 rom m (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n 0 Gn ltac:(lia)
                ltac:(lia) Hbsz
                0xff270 asan_GLSB (Z_to_bv 64 0x107578) SB sb0 ltac:(lia) ltac:(wd_ulia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); split; [lia | first [ solve [ clear - Gn Gm' GS'; Z.div_mod_to_equations; lia ] | solve [ let Hr := fresh "Hr" in pose proof (u64_range m) as Hr; clear - Hr; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]])
                M r0 id Hid H10 H8 H9 H18 H20 H21 H24)
      as (r1 & RUN1 & A22 & AK & AG1).
    { eapply (store_ok_sub ASEGS M m _ (Z.to_nat (needed n))); [lia | exact C_chunk | rewrite at_u; lia | rewrite at_u by lia; rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact C_gsb. } { exact C_sb. } { exact C_sb0. } { exact C_sb0nz. }
    change (amD_mem m n 0 M id) with (mb_1 M m n id) in RUN1.
    (* [comment removed for export] *)
    assert (RETA : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ ARB d)).
    { intros d Hd Hdr. pose proof ARB_ok as [E1 E2]. pose proof (u64_range ARB). apply ret_ok_at; [exact E1 | exact Hd | lia]. }
    assert (RET7c : ret_ok (at_ ARB 0x4bfdc)) by (apply RETA; [reflexivity | lia]).
    assert (W2 : exists r2, msteps ASEGS (mkst r1 (at_ ARB 0x4bfc8) (mb_1 M m n id) rom) (mkst r2 (at_ ARB 0x4bfdc) (mb_2 M S m n id) rom)
                 /\ (forall i : reg, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r2 i = getr r1 i)).
    { (lazymatch goal with |- ?G => let G' := eval unfold mb_2 in G in change_no_check G' end). destruct (n <? 8)%Z eqn:E8.
      - apply Z.ltb_lt in E8. exists r1. split; [| intros; reflexivity].
        exact (amD2z ASEGS ARB asan_HAL2 rom m (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n Gn Hbsz (mb_1 M m n id) r1 E8 A22).
      - apply Z.ltb_ge in E8.
        destruct (amD2 ASEGS ARB asan_HAL2 rom m (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n Gn ltac:(lia) Hbsz (mb_1 M m n id) r1 E8 A22 ltac:(rchB))
          as (r2 & RUN2 & B1 & B10 & B11 & B12 & AG2).
        assert (PH : poisonH ASEGS asan_poison_tab (mb_1 M m n id) (at_ m (rz n)) (Z_to_bv 64 (n - n mod 8)) (Z_to_bv 64 0) (at_ ARB 0x4bfdc) sp2
                       (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 18446744073709551615).
        { pose proof (mb_1_outside M S m n id GS' Gn Gm') as MB1out.
          split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
          - xfer MB1out C_gsb. - unfold SB in C_sb. xfer MB1out C_sb. - xfer MB1out C_gmb. - xfer MB1out C_mb. - xfer MB1out C_gme. - xfer MB1out C_me. - xfer MB1out C_ghe. - xfer MB1out C_he. - xfer MB1out C_grm.
          - replace (word_to_le_bytes 8 (1005284 : word)) with (LE8 (Z_to_bv 64 0xf56e4)) by reflexivity. xfer MB1out C_rm.
          - vm_compute. discriminate.
          - apply ret_ok_even. reflexivity.
          - intros NZ. exfalso. apply NZ. reflexivity.
          - intros _. split; [xfer MB1out C_gcf|]. split; [replace (Z_to_bv 64 (1675432 + 120)) with (Z_to_bv 64 (0x1990a8 + 120) : word) by (apply bv_eq; reflexivity); xfer MB1out C_thr64|].
            (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. split; [first [ solve [ clear - Gn; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ] | lia].
          - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
            rewrite at_u by lia. repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
          - rewrite at_u by lia. exact SH3.
          - unorm. first [ solve [ clear - Gn; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ].
          - left. rewrite at_u by lia. unorm. lia.
          - rewrite at_u by lia. lia.
          - eapply store_ok_mono; [apply (mb_9_grows_1 M m n id) |]. rewrite !at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end).
            eapply (store_ok_sub ASEGS M (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
          - eapply store_ok_mono; [apply (mb_9_grows_1 M m n id) |]. rewrite SH1, SH2.
            unfold hide in Nd8'. eapply (store_ok_sub ASEGS M (Z_to_bv 64 (SB + (U m + rz n) / 8)) _ (Z.to_nat ((n + 7) / 8))); [unorm; rewrite Z2Nat.id by lia; lia | exact C_shw | lia | rewrite !Z2Nat.id by lia; lia].
          - exact RET7c. }
        destruct (asan_poison_shadow (mb_1 M m n id) rom (at_ m (rz n)) (Z_to_bv 64 (n - n mod 8)) (Z_to_bv 64 0) (at_ ARB 0x4bfdc) sp2
                    (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 18446744073709551615 r2 PH B1 ltac:(rchB) B10 B11 B12) as (r3 & RUN3 & AG3).
        rewrite (ARB_lit 456208) in RUN2 by lia. replace (456208 : word) with (Z_to_bv 64 456208 : word) in RUN3 by (apply bv_eq; reflexivity).
        exists r3. split.
        + eapply msteps_trans; [exact RUN2|].
          replace (getr r2 8) with (Z_to_bv 64 1 : word) in RUN3 by (symmetry; rchB).
          replace (getr r2 9) with (Z_to_bv 64 n : word) in RUN3 by (symmetry; rchB).
          replace (getr r2 18) with m in RUN3 by (symmetry; rchB).
          replace (getr r2 19) with (Z_to_bv 64 (needed n) : word) in RUN3 by (symmetry; rchB).
          replace (getr r2 20) with (at_ m (rz n)) in RUN3 by (symmetry; rchB).
          replace (getr r2 21) with (at_ m (rz n - 16)) in RUN3 by (symmetry; rchB).
          exact RUN3.
        + intros i Hi. cbn [In] in Hi.
          repeat (destruct Hi as [<-|Hi]; [rewrite (AG3 _) by notinB; rewrite (AG2 _) by notinB; reflexivity|]). destruct Hi. }
    destruct W2 as (r2 & RUN2 & K2). clear RET7c.
    set (M2 := mb_2 M S m n id) in RUN2.
    pose proof (mb_2_outside M S m n id GS' Gn Gm') as MB2out. fold M2 in MB2out.
    (* [comment removed for export] *)
    assert (W3 : exists r3, msteps ASEGS (mkst r2 (at_ ARB 0x4bfdc) M2 rom) (mkst r3 (at_ ARB 0x4c070) (mb_3 M S m n id) rom)
                 /\ (forall i : reg, In i [2; 3; 4; 8; 9; 18; 19; 20; 21; 23; 24; 25; 26; 27] -> getr r3 i = getr r2 i)).
    { (lazymatch goal with |- ?G => let G' := eval unfold mb_3 in G in change_no_check G' end). fold M2. destruct (n mod 8 =? 0)%Z eqn:Em.
      - apply Z.eqb_eq in Em. exists r2. split; [| intros; reflexivity].
        apply (amE1z ASEGS ARB asan_HAL2 rom m (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n Gn Hbsz M2 r2 Em); rchB.
      - apply Z.eqb_neq in Em.
        destruct (amE1 ASEGS ARB asan_HAL2 ARB_ok rom m (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n Gn ltac:(lia) Hbsz
                    0xff270 (Z_to_bv 64 0x107578) SB ltac:((lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); split; [lia | first [ solve [ clear - Gn Gm' GS'; Z.div_mod_to_equations; lia ] | solve [ let Hr := fresh "Hr" in pose proof (u64_range m) as Hr; clear - Hr; Z.div_mod_to_equations; lia ] | Z.div_mod_to_equations; lia ]])
                    0x106ddc 0xff278 0xff280 0xff288 0xff268 (Z_to_bv 64 0x108268) (Z_to_bv 64 0x108270) (Z_to_bv 64 0x108260) (Z_to_bv 64 FL) (Z_to_bv 64 MIDEND)
                    asan_CPM asan_GCPM asan_GLSB2 asan_GLMB asan_GLME asan_GLHE asan_GLFL
                    ltac:(split; [repeat constructor; lia | wd_ulia]) M2 r2 Em ltac:(rchB) ltac:(rchB) ltac:(rchB))
          as (r3 & RUN3 & AG3).
        { xfer MB2out C_cpm. } { xfer MB2out C_gsb. } { xfer MB2out C_sb. } { xfer MB2out C_gmb. } { xfer MB2out C_mb. }
        { xfer MB2out C_gme. } { xfer MB2out C_me. } { xfer MB2out C_ghe. } { xfer MB2out C_he. } { xfer MB2out C_gfl. }
        { xfer MB2out C_pp. }
        { eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end); apply mb_9_grows_2 |].
          rewrite SH4. unfold hide in Nd8'. eapply (store_ok_sub ASEGS M (Z_to_bv 64 (SB + (U m + rz n) / 8)) _ (Z.to_nat ((n + 7) / 8)));
            [unorm; rewrite Z2Nat.id by lia; lia | exact C_shw | wd_ulia | unorm; rewrite !Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
        exists r3. split; [exact RUN3|].
        intros i Hi. cbn [In] in Hi. repeat (destruct Hi as [<-|Hi]; [rewrite (AG3 _) by notinB; reflexivity|]). destruct Hi. }
    destruct W3 as (r3 & RUN3 & K3).
    exists r3. split.
    - rewrite <- (ARB_lit 0x4bed0) by lia. rewrite <- (ARB_lit 0x4c070) by lia.
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. exact RUN3.
    - intros i Hi. rewrite (K3 i Hi). rewrite (K2 i) by (cbn [In] in Hi |- *; clear - Hi; tauto). apply AK. cbn [In] in Hi |- *. clear - Hi. tauto.
  Qed.
End RUNB1.
End FPGen.
