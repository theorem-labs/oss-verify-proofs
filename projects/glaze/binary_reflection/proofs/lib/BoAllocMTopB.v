(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemB2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunB1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0 OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMRunB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMuslMemset OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemB2.BoAllocMMemB OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunB1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM0.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI.BoRtLeafI.   (* [comment removed for export] *)
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
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
Lemma jal_67a1c : forall regs mem rom,
  msteps BSEGS (mkst regs (at_ ARB 0x4cae0) mem rom) (mkst (regupd regs 1 (at_ ARB 0x4cae4)) (at_ ARB 0x77ff8) mem rom).
Proof using.
  intros regs mem rom. rewrite !ARB_lit by lia. lit_pc.
  an F_4cae0 D_4cae0. close_eq.
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
  (bv_unsigned a + 1 <= 0x10000 \/ 0x663000 <= bv_unsigned a)%Z -> store_ok BSEGS m a 1%nat = true -> m a <> None.
Proof using.
  intros m a Ha S. pose proof (store_ok_all BSEGS m 1 a ltac:(pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) S a ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)) as W.
  unfold wview in W. destruct (m a); [discriminate | ].
  rewrite (find_segment1_none_outside BSEGS 0x10000 0x663000 (bv_unsigned a) asanF_segs_in_hull) in W; [exact W|].
  destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

Section RUNB.
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
  Hypothesis H22 : getr r0 22 = Z_to_bv 64 0x10ab58.
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
  Hypothesis Hstk : store_ok BSEGS M (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_inited : rdn BSEGS M (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn BSEGS M (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS M (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn BSEGS M (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  Hypothesis C_thr64 : rdn BSEGS M (Z_to_bv 64 (0x19fce8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615)).
  Hypothesis C_kif : rdn BSEGS M (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn BSEGS M (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn BSEGS M (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP)).
  Hypothesis C_tctx : rdn BSEGS M (Z_to_bv 64 TSDP) 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn BSEGS M (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_gsb : rdn BSEGS M (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sb : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 SB)).
  Hypothesis C_cpm : rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gmb : rdn BSEGS M (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS M (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND)).
  Hypothesis C_ghe : rdn BSEGS M (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_gfl : rdn BSEGS M (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 FL)).
  Hypothesis C_pp : rdn BSEGS M (at_ (Z_to_bv 64 FL) 85) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mfs : rdn BSEGS M (at_ (Z_to_bv 64 FL) 44) 4 = Some (LE4 4096).
  Hypothesis C_fill : rdn BSEGS M (at_ (Z_to_bv 64 FL) 52) 4 = Some (LE4 0xbe).
  Hypothesis C_grm : rdn BSEGS M (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS M (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_glsn : rdn BSEGS M (Z_to_bv 64 0x106b70) 8 = Some (LE8 (Z_to_bv 64 0x10)).
  Hypothesis C_lsn : rdn BSEGS M (at_ tp 0x10) 4 = Some (LE4 0).
  Hypothesis C_magic : rdn BSEGS M (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 MAGIC)).
  Hypothesis C_hook : rdn BSEGS M (Z_to_bv 64 0x19fc80) 8 = Some (LE8 (Z_to_bv 64 0)).
  (* [comment removed for export] *)
  Hypothesis C_Tw : store_ok BSEGS M thr 4096 = true.
  (* [comment removed for export] *)
  Hypothesis C_chunk : store_ok BSEGS M m (Z.to_nat (needed n)) = true.
  Hypothesis C_h1 : rdn BSEGS M (at_ m (rz n - 15)) 1 = Some [h1].
  Hypothesis C_sb0 : rdn BSEGS M (Z_to_bv 64 (SB + U m / 8)) 1 = Some [sb0].
  Hypothesis C_sb0nz : U sb0 <> 0%Z.
  Hypothesis C_shw : store_ok BSEGS M (Z_to_bv 64 (SB + (U m + rz n) / 8)) (Z.to_nat ((n + 7) / 8)) = true.
  (* [comment removed for export] *)
  Hypothesis C_fflag : rdn BSEGS M (at_ sp2 8) 8 = Some (LE8 (Z_to_bv 64 1)).

  Lemma nfB : (24 <= needed n <= 65536)%Z /\ (16 <= rz n <= 1024)%Z /\ (rz n + 8 <= needed n)%Z /\ (needed n = rounded n + rz n)%Z
              /\ (Z.max n 8 <= rounded n)%Z /\ (1 <= c <= 30)%Z /\ (rz n = 16 <-> rz_log n = 0)%Z /\ (0 <= n mod 8 < 8)%Z /\ (n mod 8 <= n)%Z.
  Proof using Gm Gn m S. exact (mbn S m n Gn Gm). Qed.

  (* [comment removed for export] *)
  Theorem run_mB1 :
    exists (r : bvmap 5 word) (w0 w8 w16 wc : word),
      msteps BSEGS (mkst r0 (Z_to_bv 64 0x4c940) M rom)
                   (mkst r (Z_to_bv 64 0x4ccc8) (mb_9 M S m T n id 0xbe h1 w0 w8 w16 wc) rom)
      /\ getr r 2 = sp2 /\ getr r 20 = at_ m (rz n) /\ getr r 3 = getr R 3 /\ getr r 4 = tp.
  Proof using C_fflag C_shw C_sb0nz C_sb0 C_h1 C_chunk C_Tw C_hook C_magic C_lsn C_glsn C_rm C_grm C_fill C_mfs C_pp C_gfl C_he C_ghe C_me C_gme C_mb C_gmb C_cpm C_sb C_gsb C_thr C_tctx C_tsdp C_key C_kif C_thr64 C_gcf Hstk Gmctx GmT Gm4 Gm GME GFL Gtsdp Gtp Gctx GT Hid Gn GS H24 H21 H20 H19 H18 H10 H9 H8 H4 H3 H2 sb0 TSDP MIDEND FL tctx.
    pose proof (u64_range S) as HSr. pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as ([GT1 GTS] & GT2 & GT3). destruct Gctx as ([Gc1 GcB] & Gc2 & Gc3). destruct Gtp as [Gtp1 Gtp2].
    destruct Gm as (Gm1 & Gm2 & Gm3). pose proof nfB as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6 & NF7 & NF8 & NF9).
    assert (GT' : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z) by exact (conj (conj GT1 GTS) GT2).
    assert (GS' : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z) by lia.
    assert (Gm' : (0x10007fff8000 <= U m /\ U m + needed n <= U S - 3584 /\ U m mod 16 = 0)%Z) by lia.
    pose proof (mb_shad S m n GS' Gn Gm') as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    pose proof (mb_shadow_range S m n GS' Gn Gm') as [SR1 SR2].
    assert (Nd8 : (0 <= n / 8 /\ n / 8 <= 8064 /\ 8 * (n / 8) = n - n mod 8)%Z) by (first [clear - Gn | idtac]; (Z.div_mod_to_equations; lia)).
    assert (Nd8' : (n / 8 <= (n + 7) / 8 /\ (n + 7) / 8 <= n / 8 + 1 /\ (n mod 8 <> 0 -> (n + 7) / 8 = n / 8 + 1))%Z) by (repeat match goal with H : _ |- _ => clear H end; (Z.div_mod_to_equations; lia)).
    assert (Hif : (0 <= (if (n mod 8 =? 0)%Z then 0 else 1) <= 1)%Z) by (destruct (n mod 8 =? 0)%Z; lia).
    hidehyp NF7. hidehyp Nd8'.
    hidehyp Gc3. hidehyp GmT. hidehyp Gmctx.
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Uctx : U ctxw = tctx) by (unorm; reflexivity).
    assert (Hbsz : bytes_le_to_Z (LE8 (Z_to_bv 64 0)) = U (Z_to_bv 64 0) /\ length (LE8 (Z_to_bv 64 0)) = 8%nat) by (split; [apply bytes_le_to_Z_8 | apply length_N_to_le_bytes]).
    (* [comment removed for export] *)
    assert (RETA : forall d, (d mod 2 = 0)%Z -> (0 <= d < 2 ^ 24)%Z -> ret_ok (at_ ARB d)).
    { intros d Hd Hdr. pose proof ARB_ok as [E1 E2]. pose proof (u64_range ARB). apply ret_ok_at; [exact E1 | exact Hd | lia]. }
    pose proof (run_mB1a M rom r0 S tp m T tctx n id FL MIDEND TSDP sb0 H2 H8 H9 H10 H18 H19 H20 H21 H24 GS Gn Hid GT Gctx Gtp Gtsdp GFL GME
                  Gm Gm4 Hstk C_gcf C_thr64 C_gsb C_sb C_cpm C_gmb C_mb C_gme C_me C_ghe C_he C_gfl C_pp C_grm C_rm
                  C_chunk C_sb0 C_sb0nz C_shw) as W3.
    destruct W3 as (r3 & RUN3 & K3). rewrite <- (ARB_lit 0x4cae0) in RUN3 by lia.
    set (M3 := mb_3 M S m n id) in RUN3.
    pose proof (mb_3_outside M S m n id GS' Gn Gm') as MB3out. fold M3 in MB3out.
    (* [comment removed for export] *)
    pose proof (jal_67a1c r3 M3 rom) as RUNJ.
    assert (GH : gctH BSEGS both_gct_tab M3 (at_ sp2 (-16)) tp (Z_to_bv 64 TSDP) ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - xfer MB3out C_kif. - xfer MB3out C_key. - xfer MB3out C_tsdp. - xfer MB3out C_tctx.
      - unfold hide in Gmctx. xferh GcB MB3out C_thr.
      - unorm. lia.
      - rewrite !at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end). eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end); apply mb_9_grows_3 |].
        eapply (store_ok_sub BSEGS M (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]].
      - rewrite at_at, at_u by lia. lia.
      - unorm. rewrite at_at, at_u by lia. lia.
      - rewrite at_at, at_u by lia. lia.
      - unorm. rewrite at_at, at_u by lia. lia.
      - unorm. rewrite at_at, at_u by lia. lia. }
    destruct (gts_run BSEGS ARB both_HGTS ARB_ok both_gct_tab M3 rom (regupd r3 1 (at_ ARB 0x4cae4)) (at_ ARB 0x4cae4) sp2 tp (Z_to_bv 64 TSDP) ctxw thr
                both_gct_tab_ok both_GTRB GH) as (r4 & RUN4 & D10 & AG4).
    { eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M3 in G in change_no_check G' end); apply mb_9_grows_3 |].
      eapply (store_ok_sub BSEGS M (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_at, !at_u by lia; lia | rewrite !at_at, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite at_u by lia. lia. } { rewrite Uthr. lia. } { rewrite Uthr. lia. }
    { apply RETA; [reflexivity | lia]. }
    { rchB. } { rchB. } { rchB. }
    change (wbytes (wbytes M3 _ _) _ _) with (mb_4 M S m n id) in RUN4.
    set (M4 := mb_4 M S m n id) in RUN4.
    (* [comment removed for export] *)
    assert (T24 : forall k, (0 <= k /\ k + 8 <= 4096)%Z -> exists w : word, rdn BSEGS M4 (at_ thr k) 8 = Some (LE8 w)).
    { intros k Hk. destruct (rdn_defined_ex BSEGS M4 (at_ thr k) 8) as (bs & Rb & Lb).
      - intros i Hi. rewrite at_u, Uthr in Hi by (rewrite Uthr; lia). (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). apply mb_9_grows_4.
        apply (store_ok1_off M); [unfold hideW in GTS; unorm; (first [clear - Hi Hk GTS | idtac]; lia)|].
        eapply (store_ok_sub BSEGS M thr _ 4096 1); [rewrite Uthr; (first [clear - GT GS | idtac]; lia) | exact C_Tw | rewrite Uthr; unorm; (first [clear - Hi Hk | idtac]; lia) | rewrite Uthr; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - Hi Hk | idtac]; lia)].
      - rewrite at_u, Uthr by (rewrite Uthr; lia). lia.
      - exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite (word_to_le_bytes_of_bytes8 bs Lb). exact Rb. }
    destruct (T24 2800%Z ltac:(lia)) as [v0 Rv0]. destruct (T24 2808%Z ltac:(lia)) as [v8 Rv8]. destruct (T24 2816%Z ltac:(lia)) as [v16 Rv16].
    destruct (amE2a BSEGS ARB both_HAL2 rom m thr (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n Gn ltac:(rewrite Uthr; (first [clear - GT GS | idtac]; hlia)) Hbsz M4 r4 v0 v8 v16 D10 ltac:(rchB) ltac:(rchB) Rv0 Rv8 Rv16)
      as (r5 & w0 & w8 & w16 & RUN5 & E10 & E11 & AG5).
    { eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end); apply mb_9_grows_4 |].
      eapply (store_ok_sub BSEGS M thr _ 4096); [rewrite Uthr; lia | exact C_Tw | rewrite at_u, Uthr; lia | rewrite at_u, Uthr by (rewrite Uthr; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    change (amE2a_mem thr M4 w0 w8 w16) with (mb_5 M S m T n id w0 w8 w16) in RUN5.
    set (M5 := mb_5 M S m T n id w0 w8 w16) in RUN5.
    pose proof (mb_5_outside M S m T n id w0 w8 w16 GS' GT' Gn Gm') as MB5out. fold M5 in MB5out.
    (* [comment removed for export] *)
    assert (W6 : exists r6, msteps BSEGS (mkst r5 (at_ ARB 0x4cb38) M5 rom) (mkst r6 (at_ ARB 0x4cc24) M5 rom)
                 /\ getr r6 11 = Z_to_bv 64 c /\ regs_agree (fun x : reg => In x [11; 12; 13; 14; 15; 16]) r5 r6).
    { destruct (Z.leb_spec (needed n) 512) as [Hle|Hgt].
      - exact (amE2lo BSEGS ARB both_HAL2 rom m (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n Gn Hbsz M5 r5 Hle E11 ltac:(rchB)).
      - exact (amE2hi BSEGS ARB both_HAL2 rom m (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n Gn Hbsz M5 r5 ltac:(lia) E11 ltac:(rchB)). }
    destruct W6 as (r6 & RUN6 & F11 & AG6).
    (* [comment removed for export] *)
    assert (T24' : exists w : word, rdn BSEGS M5 (at_ thr (2912 + 8 * c)) 8 = Some (LE8 w)).
    { destruct (rdn_defined_ex BSEGS M5 (at_ thr (2912 + 8 * c)) 8) as (bs & Rb & Lb).
      - intros i Hi. rewrite at_u, Uthr in Hi by (rewrite Uthr; lia). (lazymatch goal with |- ?G => let G' := eval unfold M5 in G in change_no_check G' end). apply mb_9_grows_5.
        apply (store_ok1_off M); [unfold hideW in GTS; unorm; (first [clear - Hi NF6 GTS | idtac]; lia)|].
        eapply (store_ok_sub BSEGS M thr _ 4096 1); [rewrite Uthr; (first [clear - GT GS | idtac]; lia) | exact C_Tw | rewrite Uthr; unorm; (first [clear - Hi NF6 | idtac]; lia) | rewrite Uthr; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - Hi NF6 | idtac]; lia)].
      - rewrite at_u, Uthr by (rewrite Uthr; lia). lia.
      - exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite (word_to_le_bytes_of_bytes8 bs Lb). exact Rb. }
    destruct T24' as [vbs Rvbs].
    assert (MSOK : ret_ok (Z_to_bv 64 0xfc38c)) by (apply ret_ok_lit; [lia | reflexivity]).
    destruct (amE2c BSEGS ARB both_HAL2 ARB_ok rom sp2 m (at_ S (-2128)) thr ctxw (Z_to_bv 64 0) (LE8 (Z_to_bv 64 0)) n 0 Gn ltac:((repeat match goal with H : _ |- _ => clear H end; lia))
                ltac:((first [clear - Gm4 Gm | idtac]; lia)) ltac:(rewrite at_u by (first [clear - GS | idtac]; lia); (first [clear - GS | idtac]; lia)) ltac:(rewrite Uthr; (first [clear - GT GS | idtac]; hlia)) Hbsz
                ltac:(rewrite at_u by (first [clear - GS | idtac]; lia); (first [clear - NF2 NF1 Gm | idtac]; lia)) ltac:(unfold hide in GmT; rewrite Uthr; (first [clear - NF3 NF2 GmT | idtac]; lia)) ltac:(unfold hide in Gmctx; rewrite Uctx; (first [clear - NF3 NF2 Gmctx | idtac]; lia)) ltac:(rewrite at_u by (first [clear - GS | idtac]; lia); (first [clear - NF2 NF1 Gm | idtac]; lia))
                0x105f18 (Z_to_bv 64 0x10e1b8) SB ltac:((repeat match goal with H : _ |- _ => clear H end; lia)) ltac:(unorm; (repeat match goal with H : _ |- _ => clear H end; lia)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); split; [(repeat match goal with H : _ |- _ => clear H end; lia) | (first [clear - Gm4 | idtac]; Z.div_mod_to_equations; lia)])
                0x10da1c 0x105f20 0x105f28 0x105f30 0x105f10 (Z_to_bv 64 0x10eea8) (Z_to_bv 64 0x10eeb0) (Z_to_bv 64 0x10eea0) (Z_to_bv 64 FL)
                ltac:(split; [repeat constructor; (repeat match goal with H : _ |- _ => clear H end; lia) | unorm; (first [clear - GFL | idtac]; lia)])
                0x105f10 0x105f38 (Z_to_bv 64 0x107e58) (Z_to_bv 64 0xfc38c) 0xbe both_GLFL3 both_GLRMS
                ltac:(unorm; (repeat match goal with H : _ |- _ => clear H end; lia)) ltac:(rewrite Uthr, at_u by (first [clear - GS | idtac]; lia); (first [clear - GT | idtac]; lia)) MSOK
                M5 r6 vbs ltac:(rchB) F11 ltac:(rchB) ltac:(rchB) ltac:(rchB) Rvbs)
      as (r7 & wc & RUN7 & G1 & G10 & G11 & G12 & G13 & AG7).
    { eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M5 in G in change_no_check G' end); apply mb_9_grows_5 |].
      eapply (store_ok_sub BSEGS M thr _ 4096); [rewrite Uthr; (first [clear - GT GS | idtac]; lia) | exact C_Tw | rewrite at_u, Uthr; (first [clear - NF6 Uthr GT GS | idtac]; lia) | rewrite at_u, Uthr by (rewrite Uthr; (first [clear - NF6 GT GS | idtac]; lia)); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - NF6 | idtac]; lia)]. }
    { xfer MB5out C_fflag. }
    { xferh GTS MB5out C_gfl. } { xferh GTS MB5out C_mfs. } { xferh GTS MB5out C_fill. } { xferh GTS MB5out C_grm. } { xferh GTS MB5out C_rm. }
    change (wbytes M5 _ _) with (mb_6 M S m T n id w0 w8 w16 wc) in RUN7.
    set (M6 := mb_6 M S m T n id w0 w8 w16 wc) in RUN7.
    (* [comment removed for export] *)
    destruct (both_memset M6 (at_ m (rz n)) (Z_to_bv 64 0xbe) (at_ ARB 0x4cc74) (Z.min n 4096) rom r7 ltac:(lia) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]))
      as (r8 & RUN8 & I10 & MSA).
    { eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M6 in G in change_no_check G' end); apply mb_9_grows_6 |].
      eapply (store_ok_sub BSEGS M m _ (Z.to_nat (needed n))); [(first [clear - Gm4 Gm GS | idtac]; lia) | exact C_chunk | rewrite at_u; (first [clear - NF2 Gm Gm4 | idtac]; lia) | rewrite at_u by (first [clear - NF2 Gm Gm4 | idtac]; lia); rewrite !Z2Nat.id by (first [clear - Gn NF1 | idtac]; lia); (first [clear - NF5 NF4 | idtac]; lia)]. }
    { apply RETA; [reflexivity | lia]. }
    { exact G10. } { exact G11. } { exact G12. } { exact G1. }
    unfold both_memset_entry in RUN8. replace (1033100 : word) with (Z_to_bv 64 0xfc38c : word) in RUN8 by (apply bv_eq; reflexivity).
    change (wbytes M6 _ _) with (mb_7 M S m T n id 0xbe w0 w8 w16 wc) in RUN8.
    set (M7 := mb_7 M S m T n id 0xbe w0 w8 w16 wc) in RUN8.
    pose proof (mb_7_outside M S m T n id 0xbe w0 w8 w16 wc GS' GT' Gn Gm') as MB7out. fold M7 in MB7out.
    (* [comment removed for export] *)
    destruct (amE3 BSEGS ARB both_HAL3 ARB_ok 0x106b70 0x103b0 both_HLSN both_GLSN both_GMAG ltac:((repeat match goal with H : _ |- _ => clear H end; lia)) rom sp2 m tp n 0x10 h1 Gn ltac:((first [clear - Gm4 Gm | idtac]; lia))
                ltac:(rewrite at_u by (first [clear - GS | idtac]; lia); (first [clear - GS | idtac]; lia)) ltac:((first [clear - Gtp | idtac]; lia)) M7 r8 ltac:(rchB) ltac:(rchB) ltac:(rchB) ltac:(rchB) ltac:(rchB) ltac:(rchB))
      as (r9 & RUN9 & J1 & J10 & J11 & AG9).
    { xferh GTS MB7out C_glsn. } { xferh GTS MB7out C_lsn. }
    { unfold hide in GmT. xfer MB7out C_h1. }
    { eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M7 in G in change_no_check G' end); apply mb_9_grows_7 |].
      eapply (store_ok_sub BSEGS M m _ (Z.to_nat (needed n))); [(first [clear - Gm4 Gm GS | idtac]; lia) | exact C_chunk | rewrite at_u; (first [clear - NF2 Gm Gm4 | idtac]; lia) | rewrite at_u by (first [clear - NF2 Gm Gm4 | idtac]; lia); rewrite Z2Nat.id by (first [clear - NF1 | idtac]; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (first [clear - NF3 | idtac]; lia)]. }
    { eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M7 in G in change_no_check G' end); apply mb_9_grows_7 |].
      eapply (store_ok_sub BSEGS M m _ (Z.to_nat (needed n))); [lia | exact C_chunk | lia | rewrite Z2Nat.id by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { intros _. xferh GTS MB7out C_magic. }
    change (amE3_mem m n h1 M7) with (mb_8 M S m T n id 0xbe h1 w0 w8 w16 wc) in RUN9.
    set (M8 := mb_8 M S m T n id 0xbe h1 w0 w8 w16 wc) in RUN9.
    pose proof (mb_8_outside M S m T n id 0xbe h1 w0 w8 w16 wc GS' GT' Gn Gm') as MB8out. fold M8 in MB8out.
    (* [comment removed for export] *)
    destruct (rmh_run BSEGS ARB (Z_to_bv 64 0x19fc80) both_HRMH both_GRMH both_HHK ARB_ok M8 rom r9 (at_ ARB 0x4ccc8) sp2)
      as (r10 & RUN10 & AG10).
    { xferh GTS MB8out C_hook. }
    { unorm. lia. }
    { eapply store_ok_mono; [(lazymatch goal with |- ?G => let G' := eval unfold M8 in G in change_no_check G' end); apply mb_9_grows_8 |].
      eapply (store_ok_sub BSEGS M (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_at, !at_u by lia; lia | rewrite !at_at, !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { rewrite at_u by lia. lia. }
    { apply RETA; [reflexivity | lia]. }
    { exact J1. } { rchB. }
    replace (getr r9 8) with (Z_to_bv 64 1 : word) in RUN10 by (symmetry; rchB).
    replace (getr r9 9) with (Z_to_bv 64 n : word) in RUN10 by (first [clear - AG9 MSA AG7 AG6 AG5 AG4 K3 H9 | idtac]; (symmetry; rchB)).
    replace (getr r9 18) with m in RUN10 by (first [clear - AG9 MSA AG7 AG6 AG5 AG4 K3 H18 | idtac]; (symmetry; rchB)).
    change (wbytes (wbytes (wbytes (wbytes M8 _ _) _ _) _ _) _ _) with (mb_9 M S m T n id 0xbe h1 w0 w8 w16 wc) in RUN10.
    (* [comment removed for export] *)
    exists r10, w0, w8, w16, wc.
    rewrite (ARB_lit 0x4ccc8) in RUN10 by lia.
    split; [| split; [rchB | split; [rchB | split; rchB]]].
    eapply msteps_trans; [exact RUN3|].
    eapply msteps_trans; [exact RUNJ|]. eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|].
    eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
    eapply msteps_trans; [exact RUN9|]. exact RUN10.
  Qed.
End RUNB.
End FPGen.
End BoAllocMRunB.
Module BoAllocMRunB2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunA BoAllocMRunB.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Ltac notinB := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin.
Ltac rchB := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]) end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, ~ In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by notinB end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notinB end end ]).

Section FPGen.
Context {fx : FPState}.

Section RUNB2.
  Variables (M rom : word -> option byte) (r0 R : bvmap 5 word).
  Variables (S tp m : word) (T n : Z) (x18 x19 : word).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis H2 : getr r0 2 = sp2.
  Hypothesis H3 : getr r0 3 = getr R 3.
  Hypothesis H4 : getr r0 4 = tp.
  Hypothesis H20 : getr r0 20 = at_ m (rz n).
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis Hret : ret_ok (getr R 1).
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis GT : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)%Z.   (* [comment removed for export] *)
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 0x40 <= AIMGHI)%Z.
  Hypothesis Gm : (0x10007fff8000 <= U m /\ U m + needed n <= U S - 3584 /\ U m mod 16 = 0 /\ U m + 2 ^ 17 <= 2 ^ 47)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS M (at_ S (-3584)) 3584 = true.
  Hypothesis C_inited : rdn BSEGS M (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gcf : rdn BSEGS M (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_fum : rdn BSEGS M (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_mcs : rdn BSEGS M (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30).
  (* [comment removed for export] *)
  Hypothesis C_slots4 : forall (k : Z) (v : word),
    In (k, v) (amE4_slots ARB S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81)) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S) ->
    rdn BSEGS M (at_ sp2 k) 8 = Some (LE8 v).
  Hypothesis C_slotsI : forall (k : Z) (v : word),
    In (k, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
    rdn BSEGS M (at_ S k) 8 = Some (LE8 v).

  Theorem run_mB2 :
    exists (r : bvmap 5 word),
      msteps BSEGS (mkst r0 (Z_to_bv 64 0x4ccc8) M rom) (mkst r (getr R 1) M rom)
      /\ getr r 10 = at_ m (rz n) /\ getr r 1 = getr R 1 /\ getr r 2 = S /\ getr r 3 = getr R 3 /\ getr r 4 = tp
      /\ getr r 8 = getr R 8 /\ getr r 9 = getr R 9 /\ getr r 18 = getr R 18 /\ getr r 19 = getr R 19
      /\ getr r 20 = getr R 20 /\ getr r 21 = getr R 21 /\ getr r 22 = getr R 22 /\ getr r 23 = getr R 23
      /\ getr r 24 = getr R 24 /\ getr r 25 = getr R 25 /\ getr r 26 = getr R 26 /\ getr r 27 = getr R 27.
  Proof using C_slotsI C_slots4 C_mcs C_fum C_gcf C_inited Hstk Gm Gtp GT Gn GS Hret H20 H4 H3 H2 x19 x18 T.
    pose proof (u64_range S) as HSr. pose proof (u64_range m) as Hmr. pose proof (u64_range tp) as Htpr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2). destruct Gtp as [Gtp1 Gtp2]. destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4).
    pose proof (needed_facts n Gn) as [NF1 NF2].
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    (* [comment removed for export] *)
    destruct (amE4 BSEGS ARB both_HAL3 both_HAM2 ARB_ok 0x106b70 0x103b0 ltac:(lia) rom sp2 m tp n 0x10 Gn ltac:(lia)
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(lia) M r0 S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81))
                (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S H2 H20 C_slots4)
      as (r1 & RUN1 & A10 & A2 & A1 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26 & A27 & AG1).
    rewrite (ARB_lit 0x4ccc8) in RUN1 by lia.
    rewrite at_at in A2. cbn [Z.add Z.opp Pos.add Z.pos_sub] in A2.
    (* [comment removed for export] *)
    assert (MH : mpH BSEGS both_mp_tab M S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs both_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x19fce8) 34) with (Z_to_bv 64 0x19fd0a : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub BSEGS M (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    destruct (mp_epi BSEGS both_mp_tab both_mp_tab_ok R M rom (getr R 1) S (Z_to_bv 64 0x19fce8) thr (Z_to_bv 64 4096) (Z_to_bv 8 1)
                Hret MH ltac:(wd_ulia) M r1 A2 C_slotsI)
      as (r2 & RUN2 & B10 & B1 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & BK).
    cbn [mt_rb both_mp_tab] in RUN2. rewrite (ARB_lit 0x6f070) in RUN2 by lia. rewrite (ARB_lit 0x6f070) in A1 by lia.
    exists r2. split.
    { eapply msteps_trans; [exact RUN1|]. exact RUN2. }
    rewrite B10, A10.
    repeat match goal with |- _ /\ _ => split end; try assumption; try reflexivity;
      try rchB.
  Qed.
End RUNB2.
End FPGen.
End BoAllocMRunB2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsKInst OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemB2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemB2.BoAllocMMemB OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemB2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunA BoAllocMRunB BoAllocMRunB2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTop.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wc_has_or T := lazymatch T with
  | _ \/ _ => idtac
  | ?A /\ ?B => first [wc_has_or A | wc_has_or B]
  | ?A <-> ?B => first [wc_has_or A | wc_has_or B]
  | _ -> ?B => wc_has_or B
  end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wc_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Fixpoint hb12_check (k : nat) (z : Z) : bool :=
  match k with
  | O => true
  | S k' => andb (Z.eqb (U (Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U (Z_to_bv 8 (U (hb1w (Z_to_bv 64 z)))))))))) (17 + 128 * (z / 128))) (hb12_check k' (z + 1))
  end.
Lemma hb12_check_ok : forall k z0, hb12_check k z0 = true ->
  forall z, z0 <= z < z0 + Z.of_nat k -> U (Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U (Z_to_bv 8 (U (hb1w (Z_to_bv 64 z))))))))) = 17 + 128 * (z / 128).
Proof.
  induction k as [|k IH]; intros z0 Hc z Hz; [cbn [Z.of_nat] in Hz; lia|].
  cbn [hb12_check] in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2].
  destruct (Z.eq_dec z z0) as [->|NE]; [apply Z.eqb_eq; exact H1|].
  apply (IH (z0 + 1) H2). rewrite Nat2Z.inj_succ in Hz. lia.
Qed.
Local Set Warnings "-abstract-large-number".
Lemma hb12_val : forall z, 0 <= z < 256 ->
  Z_to_bv 8 (U (hb2w (Z_to_bv 64 (U (Z_to_bv 8 (U (hb1w (Z_to_bv 64 z)))))))) = Z_to_bv 8 (17 + 128 * (z / 128)).
Proof.
  intros z Hz. apply bv_eq. rewrite (hb12_check_ok 256 0); [| vm_compute; reflexivity | change (0 + Z.of_nat 256) with 256; lia].
  symmetry. apply Z_to_bv_small. change (bv_modulus 8) with 256. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma le8_high_zero : forall v, 0 <= v < 2 ^ 32 -> skipn 4 (word_to_le_bytes 8 (Z_to_bv 64 v)) = word_to_le_bytes 4 (Z_to_bv 64 0).
Proof.
  intros v Hv. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end). rewrite !u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn [Z_to_le_bytes skipn] in G in change_no_check G' end).
  rewrite !Z.shiftr_shiftr by lia.
  assert (E : forall k, 32 <= k -> Z.shiftr v k = 0).
  { intros k Hk. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. split; [lia|]. eapply Z.lt_le_trans with (2 ^ 32); [lia|]. apply Z.pow_le_mono_r; lia. }
  rewrite !E by lia. rewrite !Z.shiftr_0_l. reflexivity.
Qed.

Section TOPB.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HTP : TP = ia_tp both_addrs.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).

  Theorem malloc_partB : partB_stmt bt FXOK.
  Proof using HTP G_KD GEOM CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros h fx R M mdl Lc FF B C K ret n sp st ks kk c' HLT HFX BD HL HO CP HR10 Hn FPC HB HCb HK HC HF RPOST.
    destruct RPOST as (fx' & R' & M' & M0 & mdl' & d' & naa & id & b1 & x18 & x19 & Ec' & HFX' & HH' & MW' & W' & RP' & DX & CHG & SLA & SLI
                       & H15 & H14 & H12 & HCNT & Y2 & Y4 & Y3 & Y8 & Y9 & Y10 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & Hid & SEV & LZ).
    subst c'. pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    set (S := getr R 2) in *. set (c := class_of (needed n)) in *. set (ab := chunk_of_compact SBEG c kk) in *.
    set (st' := runA_st st d' naa) in *.
    set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. rewrite <- HTP in CP4.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & OBL_freed_private & OBL_rt_private & _ & _ & _ & _ & _ & OBL_store_private).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_freed_private_stmt in OBL_freed_private. unfold OBL_rt_private_stmt in OBL_rt_private.
    unfold OBL_store_private_stmt in OBL_store_private.
    (* [comment removed for export] *)
    assert (HC' : a_cache st' c = ks ++ [kk]) by ((lazymatch goal with |- ?G => let G' := eval unfold st', runA_st in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [a_cache] in G in change_no_check G' end); exact HC).
    pose proof (mc_needed n Hn) as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6 & NF7 & NF8). fold c in NF3, NF4.
    pose proof (mc_chunk bt st' Lc FF M0 mdl' n ks kk W' RP' Hn HC') as (CV & A1 & A2 & A16 & Hkk & AT & ACT & ALIV & ABAT & ANL & AW & APRIV).
    fold c in CV, A1, A2, A16, AT, ACT, ALIV, ABAT, ANL, AW, APRIV. fold ab in CV, A1, A2, A16, AT, ACT, ALIV, ABAT, ANL, AW, APRIV.
    destruct (mc_shadow_ab bt st' Lc FF M0 mdl' n ks kk W' RP' Hn HC') as (sbv & Psb & Hsbv). fold c ab in Psb.
    hidehyp AT. hidehyp ACT. hidehyp GCT. hidehyp Hsbv.
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st' Lc FF W') as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & SB0 & SB1).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, KSPACE, NMAX in *.
    assert (GTS : TSIDE T) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact (conj GTI GTB)). hidehyp GTB.
    assert (GCBh : hideW (CTX + 0x10000 <= 0x7fff7000 \/ 0x10007fff8000 <= CTX)) by ((lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact GCB). hidehyp GCB.
    assert (RB8 : region_beg SBEG c mod 8 = 0).
    { pose proof (fixed_facts bt st' Lc FF W') as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SB16).
      (lazymatch goal with |- ?G => let G' := eval unfold region_beg, KREGION in G in change_no_check G' end). clear - SB16 NF3. Z.div_mod_to_equations. lia. }
    (* [comment removed for export] *)
    set (Hd := HID st' mdl').
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdl' z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - Hz. am_tauto. }
    assert (NHab : forall z, ab <= z < ab + csize c -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. exact (ANL z Hz). }
    destruct R14 as (Bw1 & Bw2 & Bw3 & Bw4 & Bw5 & _).
    (* [comment removed for export] *)
    assert (NHsh : forall z, SB + ab / 8 <= z < SB + ab / 8 + csize c / 8 -> Hd (Z_to_bv 64 z) = false /\ M0 (Z_to_bv 64 z) <> None).
    { intros z Hz. destruct (carved_range bt st' Lc FF W' c ab NF3 CV) as (Q1 & Q2 & Q3 & Q4 & Q5).
      pose proof W' as ((WR & _) & _). destruct (WR c NF3) as (Q6 & _).
      destruct R12 as (_ & _ & _ & _ & SHD & _).
      pose proof (csize_pos c NF3) as ((Cz1 & Cz2) & Cz3).
      assert (G : region_beg SBEG c / 8 <= z - SB < (region_beg SBEG c + r_mapped_user (a_reg st' c)) / 8).
      { clear - Hz Q1 Q2 Q6 Cz1 Cz3 A16. Z.div_mod_to_equations. lia. }
      split.
      - apply HID_allowed. destruct (Bw5 c NF3) as [RA _]. apply RA.
        (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). clear - G Q1 Q2 Q6 Hz Cz1 RB8. Z.div_mod_to_equations. lia.
      - replace z with (SB + (z - SB)) by lia. exact (SHD c (z - SB) NF3 G). }
    set (Mr := mrestrict Hd M').
    (* [comment removed for export] *)
    assert (EQ0 : forall a : word, ~ Xm (U S) T c (ab + rz n) (U a) -> M' a = M0 a).
    { intros a NX. destruct (decide (M' a = M0 a)) as [E|NE]; [exact E|]. exfalso. exact (NX (proj1 (DX a NE))). }
    Ltac hoff NH := apply hid_off_of; intros z Hz; unfold T_UNW, T_QC, T_PC, PC_SZ in *; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    assert (XMr : forall (z : Z) (k : nat) bs,
              (forall i, z <= i < z + Z.of_nat k -> ~ Xm (U S) T c (ab + rz n) i /\ Hd (Z_to_bv 64 i) = false) -> 0 <= z -> z + Z.of_nat k < 2 ^ 64 ->
              rdn BSEGS M0 (Z_to_bv 64 z) k = Some bs -> rdn BSEGS Mr (Z_to_bv 64 z) k = Some bs).
    { intros z k bs F Hz Hk Hr. apply (rd_same BSEGS Mr M0); [| wd_ulia | exact Hr].
      intros x Hx. revert Hx; unorm; intros Hx. destruct (F (U x) Hx) as [NX NHx]. rewrite Z_to_bv_bv_unsigned in NHx.
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (mrestrict_off Hd M' x NHx). apply EQ0. exact NX. }
    Ltac xm0 XMr C := eapply XMr; [ | | | exact C]; [intros i Hi; split; [(lazymatch goal with |- ?G => let G' := eval unfold Xm, T_PC, PC_SZ in G in change_no_check G' end); unfold SB in *; lia | ] | unfold SB in *; lia | unfold SB in *; lia].
    Ltac konst XMr M0 R1 NHs C := xm0 XMr (const_cell _ M0 _ _ _ R1 C); apply NHs; lia.
    rewrite CP2 in *.
    (* [comment removed for export] *)
    assert (K_inited : rdn BSEGS Mr (Z_to_bv 64 0x10ee98) 1 = Some [Z_to_bv 8 1]) by (rewrite <- w2b1 by lia; konst XMr M0 R1 NHs CELL_inited).
    assert (K_gcf : rdn BSEGS Mr (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8))) by konst XMr M0 R1 NHs CELL_gcf.
    assert (K_fum : rdn BSEGS Mr (Z_to_bv 64 0x19fd0a) 1 = Some [Z_to_bv 8 1]) by (rewrite <- w2b1 by lia; konst XMr M0 R1 NHs CELL_fum).
    assert (K_mcs : rdn BSEGS Mr (Z_to_bv 64 0x10eebc) 4 = Some (LE4 30)) by konst XMr M0 R1 NHs CELL_mcs.
    assert (K_thr64 : rdn BSEGS Mr (Z_to_bv 64 (0x19fce8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615))) by konst XMr M0 R1 NHs CELL_thr64.
    assert (K_kif : rdn BSEGS Mr (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by (rewrite <- w2b1 by lia; konst XMr M0 R1 NHs CELL_kif).
    assert (K_key : rdn BSEGS Mr (at_ (Z_to_bv 64 0x10da20) 4) 4 = Some (LE4 0)).
    { replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (apply bv_eq; reflexivity). konst XMr M0 R1 NHs CELL_key. }
    assert (K_tsdp : rdn BSEGS Mr (at_ tp (-88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))).
    { replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite CP4; wd_ulia); rewrite CP4; wd_ulia). konst XMr M0 R1 NHs CELL_tsdp. }
    assert (K_tctx : rdn BSEGS Mr (Z_to_bv 64 TSDP) 8 = Some (LE8 (Z_to_bv 64 CTX))) by konst XMr M0 R1 NHs CELL_tctx.
    assert (K_gsb : rdn BSEGS Mr (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by konst XMr M0 R1 NHs CELL_gsh.
    assert (K_sb : rdn BSEGS Mr (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 SB))).
    { pose proof R17 as Csb. cbn [ia_rtc_sb both_addrs] in Csb. xm0 XMr Csb. apply NHs; lia. }
    assert (K_cpm : rdn BSEGS Mr (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 1]) by (rewrite <- w2b1 by lia; konst XMr M0 R1 NHs CELL_cpm).
    assert (K_gmb : rdn BSEGS Mr (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by konst XMr M0 R1 NHs CELL_gmb.
    assert (K_mb : rdn BSEGS Mr (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by konst XMr M0 R1 NHs CELL_mb.
    assert (K_gme : rdn BSEGS Mr (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by konst XMr M0 R1 NHs CELL_gme.
    assert (K_me : rdn BSEGS Mr (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by konst XMr M0 R1 NHs CELL_me.
    assert (K_ghe : rdn BSEGS Mr (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by konst XMr M0 R1 NHs CELL_ghe.
    assert (K_he : rdn BSEGS Mr (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by konst XMr M0 R1 NHs CELL_he.
    assert (K_gfl : rdn BSEGS Mr (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 FL))) by konst XMr M0 R1 NHs CELL_gfl.
    assert (K_pp : rdn BSEGS Mr (at_ (Z_to_bv 64 FL) 85) 1 = Some [Z_to_bv 8 1]).
    { replace (at_ (Z_to_bv 64 FL) 85) with (Z_to_bv 64 (FL + 85)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). rewrite <- w2b1 by lia. konst XMr M0 R1 NHs CELL_pp. }
    assert (K_mfs : rdn BSEGS Mr (at_ (Z_to_bv 64 FL) 44) 4 = Some (LE4 4096)).
    { replace (at_ (Z_to_bv 64 FL) 44) with (Z_to_bv 64 (FL + 44)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). konst XMr M0 R1 NHs CELL_mfs. }
    assert (K_fill : rdn BSEGS Mr (at_ (Z_to_bv 64 FL) 52) 4 = Some (LE4 0xbe)).
    { replace (at_ (Z_to_bv 64 FL) 52) with (Z_to_bv 64 (FL + 52)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). konst XMr M0 R1 NHs CELL_fill. }
    assert (K_grm : rdn BSEGS Mr (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by konst XMr M0 R1 NHs CELL_grm.
    assert (K_rm : rdn BSEGS Mr (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by konst XMr M0 R1 NHs CELL_rm.
    assert (K_glsn : rdn BSEGS Mr (Z_to_bv 64 0x106b70) 8 = Some (LE8 (Z_to_bv 64 0x10))) by konst XMr M0 R1 NHs CELL_glsn.
    assert (K_lsn : rdn BSEGS Mr (at_ tp 0x10) 4 = Some (LE4 0)).
    { replace (at_ tp 0x10) with (Z_to_bv 64 (TP + 0x10)) by (apply bv_eq; rewrite at_u by (rewrite CP4; wd_ulia); rewrite CP4; wd_ulia). konst XMr M0 R1 NHs CELL_lsn. }
    assert (K_magic : rdn BSEGS Mr (Z_to_bv 64 0x103b0) 8 = Some (LE8 (Z_to_bv 64 MAGIC))) by konst XMr M0 R1 NHs CELL_magic.
    assert (K_hook : rdn BSEGS Mr (Z_to_bv 64 0x19fc80) 8 = Some (LE8 (Z_to_bv 64 0))) by konst XMr M0 R1 NHs CELL_hook.
    (* [comment removed for export] *)
    Ltac thr_cell XMr NHrt C := xm0 XMr C; apply NHrt; unfold T_UNW, T_QC, T_PC, PC_SZ in *; lia.
    assert (K_thr : rdn BSEGS Mr (at_ (Z_to_bv 64 CTX) 152) 8 = Some (LE8 (Z_to_bv 64 T))).
    { replace (at_ (Z_to_bv 64 CTX) 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). unfold hide in GCT, ACT. thr_cell XMr NHrt Tback. }
    hidehyp GCT. hidehyp ACT.
    (* [comment removed for export] *)
    assert (GRM : mem_grows M M').
    { intros a Ha. destruct (decide (M' a = M a)) as [E|NE]; [rewrite E; exact Ha | exact (proj2 (CHG a NE))]. }
    assert (GR0 : mem_grows M0 M').
    { intros a Ha. destruct (decide (M' a = M0 a)) as [E|NE]; [rewrite E; exact Ha | exact (proj2 (DX a NE))]. }
    assert (SOKstk : store_ok BSEGS Mr (at_ S (-3584)) 3584 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      eapply store_ok_mono; [exact GRM|]. apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia. apply CPstk. cbn in Hx. lia. }
    assert (SOKT : store_ok BSEGS Mr (Z_to_bv 64 T) 4096 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHrt].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ TW); wd_ulia_c. }
    assert (SOKab : store_ok BSEGS Mr (Z_to_bv 64 ab) (Z.to_nat (needed n)) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| unorm; rewrite Z2Nat.id by lia; lia | unorm; rewrite Z2Nat.id by lia; hoff NHab].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ AW); unorm; rewrite ?Z2Nat.id by lia; lia. }
    pose proof (csize_pos c NF3) as ((Cz1 & Cz2) & Cz3).
    assert (P8 : (ab + rz n) mod 8 = 0) by (clear - A16 NF6 NF8; pose proof (rz_mod16 n); Z.div_mod_to_equations; lia).
    pose proof (up8_rounded n ltac:(lia)) as (UR1 & UR2 & UR3). unfold up8 in UR1.
    assert (DB : 0 <= ab / 8 /\ ab / 8 + csize c / 8 <= 17592184995840 /\ (ab + rz n) / 8 = ab / 8 + rz n / 8 /\ 2 <= rz n / 8
                 /\ rz n / 8 + (n + 7) / 8 <= csize c / 8 /\ n / 8 <= (n + 7) / 8 <= n / 8 + 1 /\ 0 <= n / 8 /\ 8 * (n / 8) <= n).
    { pose proof (rz_mod16 n) as RZ16. clear - A1 A2 A16 NF4 NF6 NF7 NF8 Hn Cz1 Cz3 UR1 RZ16 CR. Z.div_mod_to_equations. lia. }
    assert (SOKsh : store_ok BSEGS Mr (Z_to_bv 64 (SB + (ab + rz n) / 8)) (Z.to_nat ((n + 7) / 8)) = true).
    { assert (RG : forall i, SB + (ab + rz n) / 8 <= i < SB + (ab + rz n) / 8 + (n + 7) / 8 -> SB + ab / 8 <= i < SB + ab / 8 + csize c / 8).
      { intros i Hi. clear - Hi NF4 NF6 NF7 NF8 A16 Hn Cz3 UR1. Z.div_mod_to_equations. lia. }
      assert (Hnn : 0 <= (n + 7) / 8) by (apply Z.div_pos; lia).
      (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite store_ok_mrestrict; [| unfold SB in *; unorm; rewrite Z2Nat.id by lia; lia
        | unfold SB in *; unorm; rewrite Z2Nat.id by lia; apply hid_off_of; intros z Hz; split; [lia | apply (proj1 (NHsh z ltac:(apply RG; exact Hz)))] ].
      apply store_ok_bytes; [| unfold SB in *; unorm; rewrite Z2Nat.id by lia; lia]. intros x Hx. revert Hx. unfold SB in *. unorm. rewrite Z2Nat.id by lia. intros Hx.
      apply store_ok1_some. apply GR0. pose proof (proj2 (NHsh (U x) ltac:(apply RG; exact Hx))) as Dx. rewrite Z_to_bv_bv_unsigned in Dx. exact Dx. }
    (* [comment removed for export] *)
    assert (K_h1 : rdn BSEGS Mr (at_ (Z_to_bv 64 ab) (rz n - 15)) 1 = Some [Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1))))]).
    { replace (at_ (Z_to_bv 64 ab) (rz n - 15)) with (Z_to_bv 64 (ab + rz n - 15)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia).
      apply heap_rdn1; [wd_ulia|]. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite mrestrict_off; [exact H15|]. apply NHab. lia. }
    assert (K_sb0 : rdn BSEGS Mr (Z_to_bv 64 (SB + U (Z_to_bv 64 ab) / 8)) 1 = Some [Z_to_bv 8 sbv]).
    { unfold hideW in GTS. replace (U (Z_to_bv 64 ab)) with ab by (unorm; reflexivity). rewrite <- w2b1 by (unfold hide, FD, FA in Hsbv; lia).
      xm0 XMr Psb. apply (proj1 (NHsh i ltac:(unfold SB in *; lia))). }
    assert (VISstk : forall x : word, U S - 3584 <= U x < U S -> Mr x = M' x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). apply mrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia|]. left. lia. }
    assert (STK : forall k0 bs (w : nat), -3584 <= k0 -> k0 + Z.of_nat w <= 0 -> rdn BSEGS M' (at_ S k0) w = Some bs -> rdn BSEGS Mr (at_ S k0) w = Some bs).
    { intros k0 bs w Hk1 Hk2 Hr. apply (rd_same BSEGS Mr M'); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact Hr]. intros x Hx. rewrite at_u in Hx by lia. apply VISstk. lia. }
    assert (K_fflag : rdn BSEGS Mr (at_ (at_ S (-2272)) 8) 8 = Some (LE8 (Z_to_bv 64 1))).
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end). apply STK; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. apply SLA. (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). repeat (first [left; reflexivity | right]). }
    assert (K_slots4 : forall (k0 : Z) (v : word),
              In (k0, v) (amE4_slots ARB S (Z_to_bv 64 n) x18 x19 (at_ S (-2128)) (at_ S (-81)) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) S) ->
              rdn BSEGS Mr (at_ (at_ S (-2272)) k0) 8 = Some (LE8 v)).
    { intros k0 v Hin. rewrite at_at. unfold amE4_slots in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [E|Hin]; [injection E as <- <-; (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end); apply STK; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]; apply SLA; (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right]) |]).
      destruct Hin. }
    assert (K_slotsI : forall (k0 : Z) (v : word),
              In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
              rdn BSEGS Mr (at_ S k0) 8 = Some (LE8 v)).
    { intros k0 v Hin. assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply STK; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact (SLI k0 v Hin)]. }
    (* [comment removed for export] *)
    set (m := Z_to_bv 64 ab : word) in *.
    assert (Um : U m = ab) by ((lazymatch goal with |- ?G => let G' := eval unfold m in G in change_no_check G' end); unorm; reflexivity).
    set (hb := Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1))))) in *.
    assert (GSx3 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (split; [lia | split; [lia | rewrite CP2; exact CP16]]).
    assert (GSx2 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by lia.
    assert (GTx3 : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584 /\ T mod 8 = 0)) by (split; [split; [exact GT4 | exact GTS] | split; [lia | apply mod4096_mod8; exact TPG]]).
    assert (GTx2 : ((4096 <= T /\ TSIDE T) /\ T + 4096 <= U S - 3584)) by (split; [split; [exact GT4 | exact GTS] | lia]).
    assert (Gm3 : 0x10007fff8000 <= U m /\ U m + needed n <= U S - 3584 /\ U m mod 16 = 0) by (rewrite Um; lia).
    assert (Gm4 : U m + 2 ^ 17 <= 2 ^ 47) by (rewrite Um; lia).
    assert (GmT : U m + needed n <= T \/ T + 4096 <= U m) by (rewrite Um; unfold hide in AT; lia).
    assert (Gmctx : U m + needed n <= CTX \/ CTX + 4096 <= U m) by (rewrite Um; unfold hide in ACT; lia).
    assert (RETR : ret_ok (getr R 1)) by (fold ra0; rewrite CP1; apply ret_ok_lit; [lia | exact CPe]).
    destruct (run_mB1 Mr (seg_rom BSEGS) R' R S tp m T CTX n id FL MIDEND TSDP hb (Z_to_bv 8 sbv)
                Y2 Y3 ltac:(rewrite Y4; reflexivity) Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y24 GSx3 Hn Hid GTx3
                ltac:(unfold hide in GCT; split; [split; [lia | exact GCBh] | split; lia]) ltac:(rewrite CP4; wd_ulia_c) ltac:(lia) ltac:(lia) ltac:(lia) Gm3 Gm4 GmT Gmctx SOKstk
                K_gcf K_thr64 K_kif K_key K_tsdp K_tctx K_thr K_gsb K_sb K_cpm K_gmb K_mb K_gme K_me K_ghe K_he K_gfl K_pp K_mfs K_fill K_grm K_rm K_glsn K_lsn K_magic K_hook
                SOKT SOKab K_h1)
      as (rB & w0 & w8 & w16 & wc & RUN1 & Q2 & Q20 & Q3 & Q4).
    { first [exact K_sb0 | rewrite Um; exact K_sb0 | rewrite Um in K_sb0; exact K_sb0]. }
    { unfold hide, FD, FA in Hsbv. destruct Hsbv as [E|E]; rewrite E; vm_compute; lia. }
    { rewrite Um. exact SOKsh. }
    { exact K_fflag. }
    set (M9 := mb_9 Mr S m T n id 0xbe hb w0 w8 w16 wc) in RUN1.
    pose proof (mb_9_stack Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3) as M9stk. fold M9 in M9stk.
    pose proof (mb_9_img Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3) as M9img. fold M9 in M9img.
    assert (GR9 : mem_grows Mr M9) by ((lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end); apply mb_9_grows).
    Ltac img9 L C := eapply (rd_same BSEGS); [intros x Hx; apply L; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                        | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact C].
    destruct (run_mB2 M9 (seg_rom BSEGS) rB R S tp m T n x18 x19 Q2 Q3 Q4 Q20 RETR GSx3 Hn GTx2 ltac:(rewrite CP4; wd_ulia)
                (conj (proj1 Gm3) (conj (proj1 (proj2 Gm3)) (conj (proj2 (proj2 Gm3)) Gm4))))
      as (rF & RUN2 & F10 & F1 & F2 & F3 & F4 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & F23 & F24 & F25 & F26 & F27).
    { eapply store_ok_mono; [exact GR9 | exact SOKstk]. }
    { img9 M9img K_inited. } { img9 M9img K_gcf. } { img9 M9img K_fum. } { img9 M9img K_mcs. }
    { intros k0 v Hin. pose proof (K_slots4 k0 v Hin) as Kk.
      assert (Hk : 24 <= k0 /\ k0 + 8 <= 144).
      { unfold amE4_slots in Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      revert Kk. rewrite at_at. intros Kk. eapply (rd_same BSEGS); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Kk].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply M9stk. lia. }
    { intros k0 v Hin. pose proof (K_slotsI k0 v Hin) as Kk.
      assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      eapply (rd_same BSEGS); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Kk]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply M9stk. lia. }
    (* [comment removed for export] *)
    apply (katD_msteps_acct BSEGS Hd (HID_off_segments bt st' Lc FF M0 mdl' BT_ia RP') asanF_segs_wx (a_aa st')
             (@mkst fx' R' (Z_to_bv 64 0x4c940) M' (seg_rom BSEGS)) (@mkst fx' rF (getr R 1) M9 (seg_rom BSEGS)) mdl').
    { apply lazy_cover_HID. }
    { exact Bw1. }
    { exact Bw2. }
    { exact HH'. }
    { rewrite restrict_mkst'. eapply msteps_trans; [exact RUN1 | exact RUN2]. }
    clear RUN1 RUN2 K_gcf K_thr64 K_kif K_key K_tsdp K_tctx K_thr K_gsb K_sb K_cpm K_gmb K_mb K_gme K_me K_ghe K_he K_gfl K_pp K_mfs K_fill K_grm K_rm K_glsn K_lsn K_magic K_hook K_inited K_fum K_mcs K_slots4 K_slotsI.
    intros mdl2 MI2 SBM2 HC2. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx' R' (Z_to_bv 64 0x4c940) M' (seg_rom BSEGS))) with M' by reflexivity.
    pose proof (same_but_materialized_frame mdl' mdl2 SBM2) as SF2.
    destruct SF2 as (_ & Evm2 & Elz2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh2 & _ & _ & _ & Eeg2).
    set (Mfin := munrestrict Hd M' M9).
    assert (VIS : forall a : word, Hd a = false -> Mfin a = M9 a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> Mfin a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mfin in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM' : forall a : word, Hd a = false -> Mr a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end); apply mrestrict_off; exact Ha).
    assert (GRfin' : mem_grows M' Mfin).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GR9. rewrite (MrM' a Eh). exact Ha. }
    assert (GRfin : mem_grows M Mfin) by (eapply mem_grows_trans; [exact GRM | exact GRfin']).
    assert (GRfin0 : mem_grows M0 Mfin) by (eapply mem_grows_trans; [exact GR0 | exact GRfin']).
    (* [comment removed for export] *)
    assert (DIFF9 : forall a : word, Mfin a <> M' a -> mb_foot S m T n a).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM' a Eh) in NE. unfold M9 in NE.
      exact (mb_9_foot Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3 a NE). }
    (* [comment removed for export] *)
    pose proof (OPS_WF_cache_pop_pf bt st' Lc FF c ks kk n W' NF3 HC' ltac:((lazymatch goal with |- ?G => let G' := eval unfold NMAX in G in change_no_check G' end); lia) NF5 eq_refl
                  ltac:(clear - BD HCb; destruct BD as (_ & BDb & _); lia) ltac:(clear - BD HB; destruct BD as (BDa & _ & _); lia)) as W2. cbv zeta in W2. fold ab in W2.
    assert (PRIVblk : forall z, (ab + rz n - 16 <= z < ab + rz n + up8 n \/ sh_lo (ab + rz n) <= z < sh_hi (ab + rz n) n) ->
                      rt_priv both_addrs Lc FF z).
    { intros z Hz. pose proof (OBL_freed_private (op_cache_pop st' c) ((ab + rz n, n) :: Lc) FF [] Lc (ab + rz n) n z W2 eq_refl Hz) as X.
      rewrite ?BT_ia in X. exact X. }
    assert (PRIVT : forall z, T <= z < T + 4096 -> rt_priv both_addrs Lc FF z).
    { intros z Hz. pose proof (OBL_rt_private st' Lc FF z W' ltac:(left; (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); exact Hz)) as X. rewrite ?BT_ia in X. exact X. }
    clear OBL_freed_private OBL_rt_private.
    pose proof (up8_facts n ltac:(lia)) as (U8a & U8b & U8c & U8d).
    assert (Up : U (at_ m (rz n)) = ab + rz n) by (rewrite at_u by (rewrite Um; lia); rewrite Um; reflexivity).
    (* [comment removed for export] *)
    apply katD_refl. (lazymatch goal with |- ?G => let G' := eval unfold malloc_ok, cfg in G in change_no_check G' end).
    exists fx', rF, Mfin, mdl2, (at_ m (rz n)).
    split; [rewrite <- CP1; reflexivity|].
    split; [exact HFX'|].
    repeat match goal with |- _ /\ _ => split end.
    - (* [comment removed for export] *) apply regs_kept_intro; rewrite ?F2, ?F3, ?F4, ?F8, ?F9, ?F18, ?F19, ?F20, ?F21, ?F22, ?F23, ?F24, ?F25, ?F26, ?F27; try reflexivity;
      (lazymatch goal with |- ?G => let G' := eval unfold tp in G in change_no_check G' end); reflexivity.
    - exact F10.
    - rewrite Up. clear - A16 NF8. pose proof (rz_mod16 n). Z.div_mod_to_equations. lia.
    - (* [comment removed for export] *) rewrite Up. (lazymatch goal with |- ?G => let G' := eval unfold ablk_ok, PTRLO in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold AS_LO, AS_HEAPLO in G in change_no_check G' end). lia.
    - intros Hbig. exfalso. lia.
    - (* [comment removed for export] *) intros b mm Hin. rewrite Up. destruct (ALIV b mm Hin) as [D|D]; [left; lia|]. right.
      pose proof (up8_facts mm ltac:(destruct (live_range bt st' Lc FF W' b mm Hin) as (_ & _ & X & _); unfold NMAX in X; lia)). lia.
    - (* [comment removed for export] *) intros f k Hin. rewrite Up.
      pose proof (fake_frame_facts bt st' Lc FF W' f k Hin) as (Ff1 & Ff2 & _).
      pose proof W' as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & INFS & _) & _).
      destruct (carved_range bt st' Lc FF W' c ab NF3 CV) as (_ & _ & Sa1 & Sa2 & _).
      destruct (space_vs_fixed bt st' Lc FF W' _ _ INFS ltac:((lazymatch goal with |- ?G => let G' := eval unfold FAKE_SIZE, KSPACE in G in change_no_check G' end); lia)); unfold KSPACE, PG, FAKE_SIZE in *; lia.
    - (* [comment removed for export] *) intros a Ha. rewrite Up in Ha.
      assert (Eh : Hd a = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 a); apply NHab; lia).
      assert (D9 : M9 a <> None).
      { apply GR9. rewrite (MrM' a Eh). apply GR0. apply (writableZ_def M0 _ _ _ AW) || (pose proof (writableZ_def M0 _ _ (U a) AW ltac:(lia)) as X; rewrite Z_to_bv_bv_unsigned in X; exact X). }
      split; [rewrite (VIS a Eh); exact D9 | apply store_ok1_some; rewrite (VIS a Eh); exact D9].
    - (* [comment removed for export] *) intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). rewrite Up.
      assert (Eh : Hd (Z_to_bv 64 (SB + (ab + rz n) / 8 + i)) = false) by (apply (proj1 (NHsh (SB + (ab + rz n) / 8 + i) ltac:(unfold SB in *; lia)))).
      rewrite (VIS _ Eh). (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end). rewrite <- Um. apply (mb_9_shadow0 Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3). exact Hi.
    - (* [comment removed for export] *) intros Hm8. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end). rewrite Up.
      assert (Eh : Hd (Z_to_bv 64 (SB + (ab + rz n) / 8 + n / 8)) = false) by (apply (proj1 (NHsh (SB + (ab + rz n) / 8 + n / 8) ltac:(unfold SB in *; clear - Hm8 DB Hn; Z.div_mod_to_equations; lia)))).
      rewrite (VIS _ Eh). (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end). rewrite <- Um. apply (mb_9_shadowp Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3). exact Hm8.
    - (* [comment removed for export] *) intros a Ha. unfold sh_lo, sh_hi in Ha. rewrite Up in Ha.
      assert (RGa : SB + ab / 8 <= U a < SB + ab / 8 + csize c / 8) by (clear - Ha DB NF4 NF6 NF7 NF8 A16 Hn Cz3 UR1; Z.div_mod_to_equations; lia).
      destruct (NHsh (U a) RGa) as [Eh Da]. rewrite Z_to_bv_bv_unsigned in Eh, Da.
      apply store_ok1_some. rewrite (VIS a Eh). apply GR9. rewrite (MrM' a Eh). apply GR0. exact Da.
    - (* [comment removed for export] *)
      intros a NE. pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval unfold as_changed in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold MSTK_A in G in change_no_check G' end).
      destruct (decide (Mfin a = M' a)) as [E|N].
      { rewrite E in NE. destruct (CHG a NE) as [[X|[X|[XR|X]]] _].
        - unfold Xm, T_PC, PC_SZ in X. destruct X as [X|[X|[X|X]]].
          + left. lia.
          + right; left. apply PRIVT. lia.
          + right; left. apply PRIVT. lia.
          + right; left. apply APRIV. lia.
        - left. lia.
        - right; left. exact XR.
        - right; right; left. exact X. }
      pose proof (DIFF9 a N) as X. unfold mb_foot in X. rewrite Um in X.
      destruct X as [X|[[_ X]|[X|[X|[X|X]]]]].
      + right; left. apply APRIV. lia.
      + right; left. apply APRIV. lia.
      + right; left. apply PRIVblk. right. unfold sh_lo, sh_hi, SB in *. destruct (n mod 8 =? 0) eqn:Em; [apply Z.eqb_eq in Em|apply Z.eqb_neq in Em]; clear - X Em Hn A16 NF8; pose proof (rz_mod16 n); Z.div_mod_to_equations; lia.
      + left. lia.
      + right; left. apply PRIVT. lia.
      + right; left. apply PRIVT. lia.
    - (* [comment removed for export] *)
      intros a _ D. exact (GRfin a D).
    - (* [comment removed for export] *)
      intros a Ha. unfold MSTK_A in Ha. split.
      + apply GRfin. apply store_ok1_heap; [lia|]. apply CPstk. lia.
      + eapply store_ok_mono; [exact GRfin|]. apply CPstk. lia.
    - (* [comment removed for export] *)
      (lazymatch goal with |- ?G => let G' := eval unfold AAINV_HS, AAINVP in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [holes_lsopt] in G in change_no_check G' end). exists (op_cache_pop st' c). rewrite Up.
      split; [exact W2 | split; [| split; [split | exact (model_ivs_wf_sbm mdl' mdl2 SBM2 MW')]]].
      + (* [comment removed for export] *)
        apply (OPS_REP_cache_hit_pf bt st' Lc FF M0 Mfin mdl' mdl2 c ks kk n W' RP' NF3 HC' ltac:((lazymatch goal with |- ?G => let G' := eval unfold NMAX in G in change_no_check G' end); lia) NF5 eq_refl).
        all: (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end); fold ab.
        * (* [comment removed for export] *)
          intros a NE. pose proof (u64_range a) as Ha. split; cycle 1.
          { destruct (Mfin a) eqn:EF; [discriminate|]. exfalso. apply NE. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
            assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GRfin0 in D. rewrite EF in D. exact (D eq_refl). }
          (lazymatch goal with |- ?G => let G' := eval unfold foot_cache_hit in G in change_no_check G' end). fold ab. rewrite ?BT_segs. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end).
          destruct (decide (Mfin a = M' a)) as [E|N].
          { rewrite E in NE. destruct (DX a NE) as [X _]. unfold Xm, T_PC, PC_SZ in X.
            destruct X as [X|[X|[X|X]]]; [do 4 right; lia | left; lia | right; left; lia | right; right; left; lia]. }
          pose proof (DIFF9 a N) as X. unfold mb_foot in X. rewrite Um in X.
          destruct X as [X|[[_ X]|[X|[X|[X|X]]]]].
          { right; right; left. lia. }
          { right; right; left. lia. }
          { right; right; right; left. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end). destruct (n mod 8 =? 0) eqn:Em; [apply Z.eqb_eq in Em|apply Z.eqb_neq in Em]; clear - X Em Hn A16 NF8; pose proof (rz_mod16 n); Z.div_mod_to_equations; lia. }
          { do 4 right. lia. }
          { right; left. lia. }
          { right; left. lia. }
        * (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite ?BT_segs.
          apply (rd_same BSEGS Mfin M'); [| (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); wd_ulia_c | exact HCNT].
          intros x Hx. revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx.
          assert (Eh : Hd x = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHrt; lia).
          rewrite (VIS x Eh). rewrite <- (MrM' x Eh). (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end). apply (mb_9_Tlow Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3 x GmT). lia.
        * (* [comment removed for export] *)
          pose proof (mb_9_state Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3) as [ST0 ST1]. fold M9 in ST0, ST1.
          assert (E16 : Hd (at_ m (rz n - 16)) = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)); rewrite at_u by (rewrite Um; lia); apply NHab; rewrite Um; lia).
          assert (E15 : Hd (at_ m (rz n - 15)) = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)); rewrite at_u by (rewrite Um; lia); apply NHab; rewrite Um; lia).
          (lazymatch goal with |- ?G => let G' := eval unfold rep_hdr in G in change_no_check G' end). rewrite ?BT_segs. split; [| split; [| split; [| split; [| split; [| split]]]]].
          -- (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite w2b1 by lia. apply heap_rdn1; [wd_ulia|].
             replace (Z_to_bv 64 (ab + rz n - 16)) with (at_ m (rz n - 16)) by (apply bv_eq; rewrite at_u by (rewrite Um; lia); rewrite Um; wd_ulia).
             rewrite (VIS _ E16). exact ST0.
          -- exists (17 + 128 * (U b1 / 128)). split.
             { (lazymatch goal with |- ?G => let G' := eval unfold hdr1_ok in G in change_no_check G' end). pose proof (u8_range b1). assert (C2 : U b1 / 128 = 0 \/ U b1 / 128 = 1) by (clear - H; Z.div_mod_to_equations; lia). destruct C2 as [C2|C2]; rewrite C2; [left | right]; reflexivity. }
             (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite w2b1 by (pose proof (u8_range b1); clear - H; Z.div_mod_to_equations; lia). apply heap_rdn1; [wd_ulia|].
             replace (Z_to_bv 64 (ab + rz n - 15)) with (at_ m (rz n - 15)) by (apply bv_eq; rewrite at_u by (rewrite Um; lia); rewrite Um; wd_ulia).
             rewrite (VIS _ E15). rewrite ST1. (lazymatch goal with |- ?G => let G' := eval unfold hb in G in change_no_check G' end). rewrite (hb12_val (U b1) (u8_range b1)). reflexivity.
          -- (* [comment removed for export] *) replace (n / 2 ^ 32) with 0 by (symmetry; apply Z.div_small; lia). (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
             apply (rd_same BSEGS Mfin M'); [| wd_ulia_c | exact H14].
             intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx.
             assert (Eh : Hd x = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHab; lia).
             rewrite (VIS x Eh). rewrite <- (MrM' x Eh). (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end). apply (mb_9_hdr_mid Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3 x GmT). rewrite Um. lia.
          -- (* [comment removed for export] *) replace (n mod 2 ^ 32) with n by (symmetry; apply Z.mod_small; lia). (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
             apply (rd_same BSEGS Mfin M'); [| wd_ulia_c | exact H12].
             intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx.
             assert (Eh : Hd x = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHab; lia).
             rewrite (VIS x Eh). rewrite <- (MrM' x Eh). (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end). apply (mb_9_hdr_mid Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3 x GmT). rewrite Um. lia.
          -- (* [comment removed for export] *) intros i Hi.
             assert (Eh : Hd (Z_to_bv 64 i) = false) by (apply NHab; lia).
             assert (D9 : M9 (Z_to_bv 64 i) <> None).
             { apply GR9. rewrite (MrM' _ Eh). apply GR0. exact (writableZ_def M0 _ _ i AW ltac:(lia)). }
             split; [rewrite (VIS _ Eh); exact D9 | apply store_ok1_some; rewrite (VIS _ Eh); exact D9].
          -- (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
             pose proof (mb_9_ctx Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3 GmT Hid) as CTX8. fold M9 in CTX8.
             pose proof (rdn_skip BSEGS M9 (at_ m (rz n - 8)) 8 _ 4 CTX8 ltac:(lia) ltac:(rewrite at_u by (rewrite Um; lia); rewrite Um; lia)) as C4.
             rewrite (le8_high_zero id Hid) in C4. rewrite at_at in C4. change (8 - 4)%nat with 4%nat in C4.
             replace (Z_to_bv 64 (ab + rz n - 4)) with (at_ m (rz n - 8 + Z.of_nat 4)) by (apply bv_eq; rewrite at_u by (rewrite Um; lia); rewrite Um; wd_ulia).
             apply (rd_same BSEGS Mfin M9); [| rewrite at_u by (rewrite Um; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact C4].
             intros x Hx. rewrite at_u in Hx by (rewrite Um; lia). apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHab. rewrite Um in Hx. cbn in Hx. lia.
          -- (* [comment removed for export] *) intros Hrz.
             assert (Hrl : rz_log n <> 0).
             { intros E0. unfold rz in Hrz. rewrite E0 in Hrz. cbn in Hrz. lia. }
             destruct (mb_9_lch Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3 Hrl) as [L1 L2]. fold M9 in L1, L2.
             assert (XF : forall z bs0, ab <= z -> z + 8 <= ab + 16 -> rdn BSEGS M9 (Z_to_bv 64 z) 8 = Some bs0 -> rdn BSEGS Mfin (Z_to_bv 64 z) 8 = Some bs0).
             { intros z bs0 Hz1 Hz2 Hr. apply (rd_same BSEGS Mfin M9); [| wd_ulia_c | exact Hr].
               intros x Hx. revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx. apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHab. lia. }
             (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). split.
             ++ apply XF; [lia | lia |]. replace (Z_to_bv 64 (ab + rz n - rz n)) with m by (apply bv_eq; rewrite Um; wd_ulia). exact L1.
             ++ apply XF; [lia | lia |]. replace (Z_to_bv 64 (ab + rz n - rz n + 8)) with (at_ m 8) by (apply bv_eq; rewrite at_u by (rewrite Um; lia); rewrite Um; wd_ulia).
                replace (Z_to_bv 64 (ab + rz n - 16)) with (at_ m (rz n - 16)) by (apply bv_eq; rewrite at_u by (rewrite Um; lia); rewrite Um; wd_ulia). exact L2.
        * (* [comment removed for export] *) intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end).
          assert (Eh : Hd (Z_to_bv 64 (SB + (ab + rz n) / 8 + i)) = false) by (apply (proj1 (NHsh (SB + (ab + rz n) / 8 + i) ltac:(unfold SB in *; lia)))).
          rewrite (VIS _ Eh). (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end). rewrite <- Um. apply (mb_9_shadow0 Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3). exact Hi.
        * (* [comment removed for export] *) intros Hm8. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo in G in change_no_check G' end).
          assert (Eh : Hd (Z_to_bv 64 (SB + (ab + rz n) / 8 + n / 8)) = false) by (apply (proj1 (NHsh (SB + (ab + rz n) / 8 + n / 8) ltac:(unfold SB in *; clear - Hm8 DB Hn; Z.div_mod_to_equations; lia)))).
          rewrite (VIS _ Eh). (lazymatch goal with |- ?G => let G' := eval unfold M9 in G in change_no_check G' end). rewrite <- Um. apply (mb_9_shadowp Mr S m T n id 0xbe hb w0 w8 w16 wc GSx2 GTx2 Hn Gm3). exact Hm8.
        * exact SBM2.
        * exact MI2.
      + (* [comment removed for export] *)
        unfold bounds in BD |- *. (lazymatch goal with |- ?G => let G' := eval unfold op_cache_pop, set_cache in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval unfold st', runA_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_kact a_reg a_cinit a_cache a_tq a_gq a_sec a_nres a_dep a_hint a_ialloc a_aa a_shsec] in G in change_no_check G' end).
        assert (PH0 : 0 <= PHI Lc) by (apply PHI_nonneg; intros q mm Hin; destruct (live_range bt st' Lc FF W' q mm Hin) as (_ & _ & X & _); lia).
        (lazymatch goal with |- ?G => let G' := eval cbn [PHI length snd] in G in change_no_check G' end). unfold kcost_malloc, MBLK, EVT in *. destruct BD as (BDa & BDb & BDc). split; [lia|]. split; [lia|]. lia.
      + (* [comment removed for export] *)
        intros c0 Hfl. exfalso. unfold op_cache_pop, set_cache in Hfl. unfold st', runA_st in Hfl. cbn [a_reg] in Hfl.
        destruct (HL c0 Hfl) as (n0 & En0 & _ & Ec0).
        destruct HO as [HO'|HO']; [rewrite HO' in En0; discriminate En0|]. rewrite HO' in En0. injection En0 as En. subst n0.
        unfold hole_flags in HF. fold c in HF, Ec0. subst c0. apply Bool.orb_false_iff in HF. destruct HF as [HF1 HF2].
        destruct Hfl as [Hfl|Hfl]; [rewrite Hfl in HF1; discriminate HF1 | rewrite Hfl in HF2; discriminate HF2].
    - eapply same_except_vm_trans; [exact SEV | apply same_but_materialized_except_vm; exact SBM2].
    - intros a Ha. transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz2; reflexivity|]. apply LZ. exact Ha.
    - rewrite Eh2. exact HH'.
  Qed.
End TOPB.
