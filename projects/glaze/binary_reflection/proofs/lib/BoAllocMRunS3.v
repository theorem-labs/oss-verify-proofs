(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9d OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM9f OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocMSumS.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia AmLiaKD.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | am_lia_kd ].   (* [comment removed for export] *)
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section HEAD.
  Variables (M rom : word -> option byte) (regs : bvmap 5 word).
  Variables (S thr tp gp tsdp ctxw midend v72 v80 lkw : word) (cpm b1 b2 b3 : byte) (n mb thr0 nch nres cz : Z).
  #[local] Abbreviation size := (sec_needed n).
  #[local] Abbreviation msz := (la_msz (sec_needed n)).
  #[local] Abbreviation spL := (at_ S (-2320)).
  #[local] Abbreviation stats := (Z_to_bv 64 0x10ae08 : word).
  #[local] Abbreviation fsp := (at_ spL (-96)).
  Hypothesis HR : la_regs spL stats size regs.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 mb.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 8.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H3 : getr regs 3 = gp.
  Hypothesis GS : 2 ^ 32 + 8192 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Hmb : AIMGHI <= mb /\ mb + msz <= 2 ^ 47 /\ mb mod 4096 = 0.
  Hypothesis Hmbsp : mb + msz <= U S - 3584 \/ U S <= mb.
  Hypothesis Hmbband : mb + msz <= AS_LO \/ AS_HEAPLO <= mb.
  Hypothesis GT : 4096 <= U thr /\ U thr + 4096 <= U S - 3584 /\ U thr mod 8 = 0.
  Hypothesis GTimg : U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr.
  Hypothesis GTband : U thr + 4096 <= AS_LO \/ AS_HEAPLO <= U thr.
  Hypothesis GTmb : U thr + 4096 <= mb \/ mb + msz <= U thr.
  Hypothesis Hnch : 0 <= nch < 2 ^ 20 /\ 0 <= nres < 2 ^ 64.
  Hypothesis Hclz : U (AsAllocM9z.swar_clz (Z_to_bv 64 msz)) = cz /\ 0 <= cz <= 63.
  (* [comment removed for export] *)
  Hypothesis PH1 : poisonH BSEGS both_poison_tab M (Z_to_bv 64 mb) (Z_to_bv 64 4096) (Z_to_bv 64 250) (Z_to_bv 64 0x510d8) fsp cpm midend thr0.
  Hypothesis PH2 : poisonH BSEGS both_poison_tab M (Z_to_bv 64 (la_tb size mb)) (Z_to_bv 64 (mb + msz - la_tb size mb)) (Z_to_bv 64 250)
                           (Z_to_bv 64 0x510e8) fsp cpm midend thr0.
  Hypothesis GH : gctH BSEGS both_gct_tab M (at_ fsp (-16)) tp tsdp ctxw thr.
  Hypothesis GHoff : (AIMGLO <= U (gt_tsd both_gct_tab) /\ U (gt_tsd both_gct_tab) + 8 <= AIMGHI) /\ (AIMGLO + 88 <= U tp /\ U tp <= AIMGHI)
                     /\ (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)
                     /\ (U ctxw + 160 <= U S - 3584 /\ (U ctxw + 160 <= AS_LO \/ AS_HEAPLO <= U ctxw) /\ 0 <= U ctxw).
  Hypothesis SOK_g : store_ok BSEGS M (at_ fsp (-8)) 8 = true.
  Hypothesis C_pg : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis R_72 : rdn BSEGS M (at_ thr 2872) 8 = Some (LE8 v72).
  Hypothesis R_80 : rdn BSEGS M (at_ thr 2880) 8 = Some (LE8 v80).
  Hypothesis R_lock : rdn BSEGS M (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = U lkw.
  Hypothesis SOK_T : store_ok BSEGS M thr 4096 = true.
  Hypothesis SOK_h : store_ok BSEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_lk : store_ok BSEGS M (Z_to_bv 64 0x10ae00) 4 = true.
  Hypothesis R_nch : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

  Definition sh_m3 : word -> option byte := lam_3 M spL stats size mb.
  Definition sh_mem : word -> option byte := la_m1 sh_m3 thr v72 v80 size mb b1 b2 b3.

  (* [comment removed for export] *)
  Definition W_sec1 (z : Z) : Prop := (U S - 2480 <= z < U S - 2416) \/ (SB + mb / 8 <= z < SB + (mb + msz) / 8).
  Definition W_sec2 (z : Z) : Prop := (U thr + 2872 <= z < U thr + 2888) \/ (mb <= z < mb + 24) \/ (0x10ae00 <= z < 0x10ae04).
  Definition W_seca (z : Z) : Prop := W_sec1 z \/ W_sec2 z.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma la_geo : msz mod 4096 = 0 /\ size + 4096 <= msz <= size + 8191 /\ n + 4096 <= size <= n + 4103
                 /\ mb + 4096 + size - 7 <= la_tb size mb <= mb + 4096 + size /\ la_tb size mb mod 8 = 0
                 /\ SB + mb / 8 + 512 <= SB + la_tb size mb / 8 /\ SB + la_tb size mb / 8 + (mb + msz - la_tb size mb) / 8 <= SB + (mb + msz) / 8.
  Proof using GT Hmb Gn lkw thr S rom. clear - GT Hmb Gn lkw thr S rom.
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb. destruct Hmb as (MB1 & MB2 & MB3).
    (lazymatch goal with |- ?G => let G' := eval unfold la_msz, la_tb in G in change_no_check G' end). repeat split; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Ltac sec1_side :=
    wd_lenlit; rewrite ?length_N_to_le_bytes, ?length_repeat_Z, ?at_at, ?at_u, ?u_Z2bv by ((lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia);
    (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end);
    first [(lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia | intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold W_sec1 in G in change_no_check G' end); unfold SB in *; lia].
  Lemma sh_m3_sum : msum W_sec1 M sh_m3.
  Proof using GT Hmb Gn GS lkw thr rom.
    destruct GS as [S1 S2]. destruct Hmb as (MB1 & MB2 & MB3). pose proof (u64_range S) as HSr.
    pose proof la_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (E512 : shlen (Z_to_bv 64 4096) = 512) by reflexivity.
    assert (Etl : shlen (Z_to_bv 64 (mb + msz - la_tb size mb)) = (mb + msz - la_tb size mb) / 8) by ((lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Esh1 : shad (Z_to_bv 64 mb) = SB + mb / 8) by ((lazymatch goal with |- ?G => let G' := eval unfold shad, SB in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]).
    assert (Esh2 : shad (Z_to_bv 64 (la_tb size mb)) = SB + la_tb size mb / 8) by ((lazymatch goal with |- ?G => let G' := eval unfold shad, SB in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]).
    assert (P0 : 0 <= (mb + msz - la_tb size mb) / 8) by (apply Z.div_pos; lia).
    assert (P1 : 0 <= mb / 8 /\ (mb + msz) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    (lazymatch goal with |- ?G => let G' := eval unfold sh_m3, lam_3, lam_2, lam_1, ps_frame in G in change_no_check G' end). rewrite E512, Etl, Esh1, Esh2.
    clear - S1 S2 HSr MB1 MB2 MB3 G1 G2 G3 G4 G5 G6 G7 P0 P1.
    do 18 (apply msum_wbytes_in; [| solve [sec1_side] | solve [sec1_side]]). apply msum_refl.
  Qed.
  Lemma sh_mem_sum2 : msum W_sec2 sh_m3 sh_mem.
  Proof using GT Hmb Gn GS lkw rom.
    destruct GT as (T1 & T2 & T3). pose proof la_geo as (G1 & G2 & G3 & _). destruct Hmb as (MB1 & MB2 & MB3). pose proof (u64_range thr) as Hthr. pose proof (u64_range S) as HSr. destruct GS as [S1 S2].
    (lazymatch goal with |- ?G => let G' := eval unfold sh_mem, la_m1 in G in change_no_check G' end).
    do 6 (apply msum_wbytes_in; [| solve [wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia]
                                 | solve [wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u, ?u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold W_sec2 in G in change_no_check G' end); lia]]).
    apply msum_refl.
  Qed.
  Lemma sh_mem_sum : msum W_seca M sh_mem.
  Proof using GT Hmb Gn GS lkw rom. eapply msum_trans; [exact sh_m3_sum | exact sh_mem_sum2]. Qed.

  Theorem sec_run_a :
    exists (r : bvmap 5 word),
      msteps BSEGS (mkst regs (0x51080 : word) M rom) (mkst r (0x51224 : word) sh_mem rom)
      /\ (getr r 2 = at_ spL (-96) /\ getr r 8 = stats /\ getr r 9 = Z_to_bv 64 (0x10ab58 + 64) /\ getr r 18 = Z_to_bv 64 msz)
      /\ getr r 19 = Z_to_bv 64 cz
      /\ getr r 13 = Z_to_bv 64 nch /\ getr r 14 = Z_to_bv 64 nres /\ getr r 21 = Z_to_bv 64 mb /\ getr r 10 = Z_to_bv 64 (mb + 4096)
      /\ getr r 4 = tp /\ getr r 3 = gp /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using R_nres R_nch SOK_lk SOK_h SOK_T V_lock R_lock R_80 R_72 C_pg SOK_g GHoff GH PH2 PH1 Hclz Hnch GTmb GTband GTimg GT Hmbband Hmbsp Hmb Gn GS H3 H4 H21 H10 HR thr0 cpm lkw midend ctxw tsdp.
    destruct GS as [S1 S2]. destruct GT as (T1 & T2 & T3). pose proof (u64_range S) as HSr. pose proof (u64_range thr) as Hthr.
    pose proof Hmb as (MB1 & MB2 & MB3).
    pose proof la_geo as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
    assert (UspL : U spL = U S - 2320) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Ufsp : U fsp = U S - 2416) by (rewrite at_at, at_u by lia; lia).
    pose proof sh_m3_sum as SUM1. pose proof sh_mem_sum2 as SUM2.
    assert (P1 : 0 <= mb / 8 /\ (mb + msz) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    (* [comment removed for export] *)
    set (L1 := lam_1 M spL stats size mb). set (L2 := lam_2 M spL stats size mb).
    assert (SUML1 : msum W_sec1 M L1 /\ msum W_sec1 M L2).
    { (* [comment removed for export] *)
      assert (E512 : shlen (Z_to_bv 64 4096) = 512) by reflexivity.
      assert (Etl : shlen (Z_to_bv 64 (mb + msz - la_tb size mb)) = (mb + msz - la_tb size mb) / 8) by ((lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
      assert (Esh1 : shad (Z_to_bv 64 mb) = SB + mb / 8) by ((lazymatch goal with |- ?G => let G' := eval unfold shad, SB in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]).
      assert (Esh2 : shad (Z_to_bv 64 (la_tb size mb)) = SB + la_tb size mb / 8) by ((lazymatch goal with |- ?G => let G' := eval unfold shad, SB in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]).
      assert (P0 : 0 <= (mb + msz - la_tb size mb) / 8) by (apply Z.div_pos; lia).
      split; (lazymatch goal with |- ?G => let G' := eval unfold L1, L2, lam_2, lam_1, ps_frame in G in change_no_check G' end); rewrite ?E512, ?Etl, ?Esh1, ?Esh2; clear - S1 S2 HSr MB1 MB2 MB3 G1 G2 G3 G4 G5 G6 G7 P0 P1.
      - do 8 (apply msum_wbytes_in; [| solve [sec1_side] | solve [sec1_side]]). apply msum_refl.
      - do 16 (apply msum_wbytes_in; [| solve [sec1_side] | solve [sec1_side]]). apply msum_refl. }
    destruct SUML1 as [SUML1 SUML2].
    assert (IMG1 : forall z, AIMGLO <= z < AIMGHI -> ~ W_sec1 z) by (intros z Hz Wz; unfold W_sec1, SB in Wz; lia).
    assert (KEEP1 : forall x : word, ~ W_sec1 (U x) -> L1 x = M x) by (intros x Hx; exact (proj1 SUML1 x Hx)).
    assert (KEEP2 : forall x : word, ~ W_sec1 (U x) -> L2 x = M x) by (intros x Hx; exact (proj1 SUML2 x Hx)).
    assert (PH2' : poisonH BSEGS both_poison_tab L1 (Z_to_bv 64 (la_tb size mb)) (Z_to_bv 64 (mb + msz - la_tb size mb)) (Z_to_bv 64 250)
                           (Z_to_bv 64 0x510e8) fsp cpm midend thr0).
    { apply (poisonH_keep_P BSEGS both_poison_tab M L1 _ _ _ _ _ cpm midend thr0 (fun z => ~ W_sec1 z) PH2 KEEP1 (proj2 SUML1)).
      (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [intros z Hz Wz; unfold W_sec1, SB in Wz; clear - Hz Wz S1 P1; lia|]). constructor. }
    assert (GH' : gctH BSEGS both_gct_tab L2 (at_ fsp (-16)) tp tsdp ctxw thr).
    { destruct GHoff as ((O1 & O1') & (O2 & O2') & (O3 & O3') & (O4 & O4' & O4'')).
      unfold AS_LO, AS_HEAPLO in O4'.
      apply (gctH_keep_P BSEGS both_gct_tab M L2 _ tp tsdp ctxw thr (fun z => ~ W_sec1 z) GH KEEP2 (proj2 SUML2));
        intros z Hz Wz; unfold W_sec1, SB in Wz.
      - clear - Hz Wz O1 O1' S1 P1. lia.
      - clear - Hz Wz O2 O2' S1 P1. lia.
      - clear - Hz Wz O3 O3' S1 P1. lia.
      - clear - Hz Wz O4 O4' O4'' S1 P1. lia. }
    assert (SOK_g' : store_ok BSEGS L2 (at_ fsp (-8)) 8 = true) by exact (msum_store_ok BSEGS W_sec1 M L2 _ _ SUML2 SOK_g).
    (* [comment removed for export] *)
    destruct (la_after_grant M rom spL stats thr tp gp tsdp ctxw midend cpm size mb thr0 regs HR H10 H21 H4 H3
                ltac:(rewrite UspL; lia) ltac:(lia) ltac:(lia) C_pg ltac:(lia) PH1 PH2' GH' SOK_g')
      as (r1 & RUN1 & PR1 & A10 & A4 & A3 & A26 & A27).
    change (lam_3 M spL stats size mb) with sh_m3 in RUN1.
    (* [comment removed for export] *)
    assert (XF1 : forall (a : word) (k : nat) v, U a + Z.of_nat k <= 2 ^ 64 -> (forall z, U a <= z < U a + Z.of_nat k -> ~ W_sec1 z) ->
              rdn BSEGS M a k = Some v -> rdn BSEGS sh_m3 a k = Some v).
    { intros a k v Hnw Hd Hr. exact (msum_rdn_eq BSEGS W_sec1 M sh_m3 a k v SUM1 Hnw Hd Hr). }
    (* [comment removed for export] *)
    assert (THR1 : forall z, U thr <= z < U thr + 4096 -> ~ W_sec1 z) by (intros z Hz Wz; unfold W_sec1 in Wz; destruct Wz as [W|W]; [ clear - Hz W GT; lia | unfold SB, AS_LO, AS_HEAPLO in *; lia ]).
    destruct (la_t1 sh_m3 rom spL stats thr v72 v80 lkw size mb (U thr) b1 b2 b3 r1 PR1 A10
                ltac:(rewrite UspL; lia) ltac:(lia) ltac:(lia) ltac:(split; [reflexivity | rewrite UspL; lia]) GTimg)
      as (r2 & RUN2 & PR2 & B21 & B10 & AG2).
    { apply XF1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros z Hz; rewrite at_u in Hz by lia; cbn in Hz; apply THR1; lia | exact R_72]. }
    { apply XF1; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros z Hz; rewrite at_u in Hz by lia; cbn in Hz; apply THR1; lia | exact R_80]. }
    { apply XF1; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros z Hz; rewrite u_Z2bv in Hz by lia; cbn in Hz; apply IMG1; lia | exact C_pg]. }
    { apply XF1; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros z Hz; rewrite u_Z2bv in Hz by lia; cbn in Hz; apply IMG1; lia | exact R_lock]. }
    { exact V_lock. }
    { exact (msum_store_ok BSEGS W_sec1 M sh_m3 _ _ SUM1 SOK_T). }
    { exact (msum_store_ok BSEGS W_sec1 M sh_m3 _ _ SUM1 SOK_h). }
    { exact (msum_store_ok BSEGS W_sec1 M sh_m3 _ _ SUM1 SOK_lk). }
    change (la_m1 sh_m3 thr v72 v80 size mb b1 b2 b3) with sh_mem in RUN2.
    (* [comment removed for export] *)
    destruct Hclz as [CZ1 CZ2].
    assert (XF2 : forall (a : word) (k : nat) v, U a + Z.of_nat k <= 2 ^ 64 -> (forall z, U a <= z < U a + Z.of_nat k -> ~ W_seca z) ->
              rdn BSEGS M a k = Some v -> rdn BSEGS sh_mem a k = Some v).
    { intros a k v Hnw Hd Hr. exact (msum_rdn_eq BSEGS W_seca M sh_mem a k v sh_mem_sum Hnw Hd Hr). }
    destruct (la_t2ag sh_mem rom spL stats size nch nres cz r2 PR2 ltac:(rewrite UspL; lia) ltac:(lia) Hnch (conj CZ1 CZ2)) as (r3 & RUN3 & C19 & C13 & C14 & AG3).
    { apply XF2; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros z Hz; rewrite u_Z2bv in Hz by lia; cbn in Hz; intros [Wz|Wz]; [exact (IMG1 z ltac:(lia) Wz) | unfold W_sec2 in Wz; clear - Hz Wz T1 GTimg MB1; lia] | exact R_nch]. }
    { apply XF2; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros z Hz; rewrite u_Z2bv in Hz by lia; cbn in Hz; intros [Wz|Wz]; [exact (IMG1 z ltac:(lia) Wz) | unfold W_sec2 in Wz; clear - Hz Wz T1 GTimg MB1; lia] | exact R_nres]. }
    assert (K3 : forall i : reg, In i [2; 3; 4; 8; 9; 10; 18; 21; 24; 26; 27]%bv -> getr r3 i = getr r2 i).
    { intros i Hi. apply AG3. cbn [In] in Hi |- *. intros Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    assert (K2 : forall i : reg, In i [3; 4; 26; 27]%bv -> getr r2 i = getr r1 i).
    { intros i Hi. apply AG2. cbn [In] in Hi |- *. intros Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    exists r3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    split. { destruct PR2 as (Q2 & Q8 & Q9 & Q18 & Q19 & Q24). rewrite !K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12). repeat split; assumption. }
    split; [exact C19|]. split; [exact C13|]. split; [exact C14|].
    split; [rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact B21|]. split; [rewrite K3 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact B10|].
    split; [rewrite K3, K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A4|]. split; [rewrite K3, K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A3|].
    split; [rewrite K3, K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A26 | rewrite K3, K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A27].
  Qed.
End HEAD.
End FPGen.
