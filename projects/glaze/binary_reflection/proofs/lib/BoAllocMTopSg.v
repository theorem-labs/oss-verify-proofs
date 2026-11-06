(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS3 OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMRunS4.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u.BoAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9d OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM9f OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocMSumS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS3.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
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
#[local] Ltac lia ::= am_lia.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Section NG.
  Variables (M rom : word -> option byte) (regs : bvmap 5 word).
  Variables (S thr tp gp tsdp ctxw midend v72 v80 lkw tr szw naw curw mxw blw w16 w24 : word) (cpm k1 k2 k3 b1 : byte) (bsz : list byte)
            (n mb thr0 nch nres cz PA tid : Z).
  #[local] Abbreviation size := (sec_needed n).
  #[local] Abbreviation msz := (la_msz (sec_needed n)).
  #[local] Abbreviation spL := (at_ S (-2320)).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation stats := (Z_to_bv 64 0x10ae08 : word).
  #[local] Abbreviation fsp := (at_ spL (-96)).
  #[local] Abbreviation m := (Z_to_bv 64 (mb + 4096)).
  #[local] Abbreviation idx := (63 - cz).
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
  Hypothesis R_lock : rdn BSEGS M (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; k1; k2; k3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; k1; k2; k3] = U lkw.
  Hypothesis SOK_T : store_ok BSEGS M thr 4096 = true.
  Hypothesis SOK_h : store_ok BSEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_lk : store_ok BSEGS M (Z_to_bv 64 0x10ae00) 4 = true.
  Hypothesis R_nch : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

  Hypothesis Hne : nch <> nres.
  Hypothesis GSband : AS_HEAPLO <= U S - 3584.
  Hypothesis GctxT : U ctxw + 4096 <= U thr \/ U thr + 4096 <= U ctxw.
  Hypothesis H26 : getr regs 26 = thr.
  Hypothesis H27 : getr regs 27 = Z_to_bv 64 1.
  (* [comment removed for export] *)
  Hypothesis Htid : 0 <= tid < 2 ^ 31.
  Hypothesis HPA : AIMGHI <= PA /\ PA + 2 ^ 23 < 2 ^ 63.
  Hypothesis HPAmb : PA + 2 ^ 23 <= mb \/ mb + msz <= PA.
  Hypothesis HPAsp : PA + 2 ^ 23 <= U S - 3584 \/ U S <= PA.
  Hypothesis GTPA : U thr + 4096 <= PA \/ PA + 2 ^ 23 <= U thr.
  Hypothesis Gctx : 1 <= U ctxw /\ U ctxw + 4096 <= U S - 3584 /\ (U ctxw + 4096 <= AIMGLO \/ AIMGHI <= U ctxw).
  Hypothesis Gctxmb : U ctxw + 4096 <= mb \/ mb + msz <= U ctxw.
  Hypothesis GctxPA : U ctxw + 4096 <= PA \/ PA + 2 ^ 23 <= U ctxw.
  (* [comment removed for export] *)
  Hypothesis R_pa : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 PA)).
  Hypothesis R_na : rdn BSEGS M (Z_to_bv 64 0x10abe0) 8 = Some (LE8 naw).
  Hypothesis R_cur : rdn BSEGS M (Z_to_bv 64 0x10abf0) 8 = Some (LE8 curw).
  Hypothesis R_mx : rdn BSEGS M (Z_to_bv 64 0x10abf8) 8 = Some (LE8 mxw).
  Hypothesis R_bl : rdn BSEGS M (Z_to_bv 64 (0x10ac00 + 8 * idx)) 8 = Some (LE8 blw).
  Hypothesis R_16 : rdn BSEGS M (Z_to_bv 64 0x10ae18) 8 = Some (LE8 w16).
  Hypothesis R_24 : rdn BSEGS M (Z_to_bv 64 0x10ae20) 8 = Some (LE8 w24).
  Hypothesis SOK_pa : store_ok BSEGS M (Z_to_bv 64 (PA + 8 * nch)) 8 = true.
  Hypothesis SOK_inst : store_ok BSEGS M (Z_to_bv 64 0x10ab98) 728 = true.
  Hypothesis FLA : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 size); (-48, Z_to_bv 64 2048);
               (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)] ->
    rdn BSEGS M (at_ spL o) 8 = Some (LE8 v).
  Hypothesis FC : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 size); (-48, Z_to_bv 64 2048)] ->
    rdn BSEGS M (at_ sp2 o) 8 = Some (LE8 v).
  Hypothesis Rb1 : rdn BSEGS M (at_ m (rz n - 15)) 1 = Some [b1].
  Hypothesis SOKh : store_ok BSEGS M (at_ m (rz n - 16)) 16 = true.
  Hypothesis R16 : rdn BSEGS M (at_ sp2 16) 8 = Some (LE8 (Z_to_bv 64 16)).
  Hypothesis RT0 : rdn BSEGS M thr 8 = Some (LE8 ctxw).
  Hypothesis Rtid : rdn BSEGS M (at_ ctxw 8) 4 = Some (LE4 tid).
  Hypothesis Rtr : rdn BSEGS M (at_ S (-2128)) 8 = Some (LE8 tr).
  Hypothesis Rsz : rdn BSEGS M (at_ (at_ S (-2128)) 8) 8 = Some bsz.
  Hypothesis Hsz : bytes_le_to_Z bsz = U szw /\ length bsz = 8%nat.


  #[local] Abbreviation MH := (sh_mem M S thr v72 v80 k1 k2 k3 n mb).
  Definition ng_mem : word -> option byte := st_mem MH naw curw mxw blw w16 w24 b1 n mb nch PA cz.
  Definition W_ng (z : Z) : Prop := W_seca S thr n mb z \/ W_sect mb nch PA z.

  Lemma ng_mem_sum : msum W_ng M ng_mem.
  Proof using Hsz HPA Htid Hclz Hnch GT Hmb Gn GS tid nres bsz szw lkw rom.
    (lazymatch goal with |- ?G => let G' := eval unfold ng_mem, W_ng in G in change_no_check G' end). eapply msum_trans.
    - exact (sh_mem_sum M rom S thr v72 v80 lkw k1 k2 k3 n mb GS Gn Hmb GT).
    - exact (st_mem_sum MH rom szw naw curw mxw blw w16 w24 bsz b1 n mb nch PA cz tid Gn (proj1 Hnch) (proj2 Hclz) Htid Hmb HPA Hsz).
  Qed.

  Theorem sec_run_ng :
    exists r : bvmap 5 word,
      msteps BSEGS (mkst regs (0x51080 : word) M rom) (mkst r (Z_to_bv 64 0x8f4f0) ng_mem rom)
      /\ getr r 1 = Z_to_bv 64 0x4c940 /\ getr r 2 = sp2 /\ getr r 10 = tr /\ getr r 11 = szw
      /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = m /\ getr r 19 = Z_to_bv 64 size
      /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 22 = Z_to_bv 64 0x10ab58 /\ getr r 23 = at_ S (-2128)
      /\ getr r 24 = Z_to_bv 64 (tid * 2 ^ 32) /\ getr r 25 = at_ m (rz n + n)
      /\ getr r 4 = tp /\ getr r 3 = gp /\ getr r 26 = thr /\ getr r 27 = Z_to_bv 64 1.
  Proof using Hsz Rsz Rtr Rtid RT0 R16 SOKh Rb1 FC FLA SOK_inst SOK_pa R_24 R_16 R_bl R_mx R_cur R_na R_pa GctxPA Gctxmb Gctx GTPA HPAsp HPAmb HPA Htid H27 H26 GctxT GSband Hne R_nres R_nch SOK_lk SOK_h SOK_T V_lock R_lock R_80 R_72 C_pg SOK_g GHoff GH PH2 PH1 Hclz Hnch GTmb GTband GTimg GT Hmbband Hmbsp Hmb Gn GS H3 H4 H21 H10 HR nres thr0 bsz cpm lkw midend ctxw tsdp.
    destruct (sec_run_a M rom regs S thr tp gp tsdp ctxw midend v72 v80 lkw cpm k1 k2 k3 n mb thr0 nch nres cz
                HR H10 H21 H4 H3 GS Gn Hmb Hmbsp Hmbband GT GTimg GTband GTmb Hnch Hclz PH1 PH2 GH GHoff SOK_g C_pg R_72 R_80 R_lock V_lock SOK_T SOK_h SOK_lk R_nch R_nres)
      as (r1 & RUN1 & (A2 & A8 & A9 & A18) & A19 & A13 & A14 & A21 & A10 & A4 & A3 & A26 & A27).
    pose proof (la_beq_nt MH rom nch nres r1 A13 A14 (conj (proj1 Hnch) (conj Hne (proj2 Hnch)))) as RUNB.
    pose proof (sh_mem_sum M rom S thr v72 v80 lkw k1 k2 k3 n mb GS Gn Hmb GT) as SUMH.
    destruct GS as [S1 S2]. pose proof Hmb as (MB1 & MB2 & MB3). pose proof GT as (T1 & T2 & T3). destruct Gctx as (C1 & C2 & C3).
    destruct HPA as [PA1 PA2]. destruct Hclz as [CZ1 CZ2].
    pose proof (u64_range S) as HSr. pose proof (u64_range thr) as Hthr. pose proof (u64_range ctxw) as Hcr.
    pose proof (rz_sec n ltac:(lia)) as Erz. pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    assert (LF : msz mod 4096 = 0 /\ size + 4096 <= msz <= size + 8191) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    destruct LF as [LF1 LF2].
    assert (P1 : 0 <= mb / 8 /\ (mb + msz) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    unfold AS_LO, AS_HEAPLO in *.
    (* [comment removed for export] *)
    assert (XH : forall (a : word) (k : nat) v, U a + Z.of_nat k <= 2 ^ 64 -> (forall z, U a <= z < U a + Z.of_nat k -> ~ W_seca S thr n mb z) ->
              rdn BSEGS M a k = Some v -> rdn BSEGS MH a k = Some v).
    { intros a k v Hnw Hd Hr. exact (msum_rdn_eq BSEGS _ M MH a k v SUMH Hnw Hd Hr). }
    assert (XI : forall (c : Z) (k : nat) v, AIMGLO <= c -> c + Z.of_nat k <= AIMGHI -> (c + Z.of_nat k <= 0x10ae00 \/ 0x10ae04 <= c) ->
              rdn BSEGS M (Z_to_bv 64 c) k = Some v -> rdn BSEGS MH (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc1 Hc2 Hlk Hr. apply XH; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | | exact Hr].
      intros z Hz. rewrite u_Z2bv in Hz by lia. (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2, SB in G in change_no_check G' end). clear - Hz Hc1 Hc2 Hlk S1 P1 T1 GTimg MB1. lia. }
    assert (XS : forall (k : Z) (w : nat) v, -2416 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS M (at_ S k) w = Some v -> rdn BSEGS MH (at_ S k) w = Some v).
    { intros k w v Kl Kh Hr. apply XH; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | | exact Hr].
      intros z Hz. rewrite at_u in Hz by lia. (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2, SB in G in change_no_check G' end). clear - Hz Kl Kh S1 S2 P1 GSband T1 T2 MB1 MB2 LF2 Hsnb Gn Hmbsp. lia. }
    destruct (sec_run_tail MH rom r1 S thr ctxw tr szw naw curw mxw blw w16 w24 bsz b1 n mb nch PA cz tid
                A2 A8 A9 A18 A19 A21 A13 A10 ltac:(rewrite A26; exact H26) ltac:(rewrite A27; exact H27)
                ltac:(lia) Gn (proj1 Hnch) CZ2 Htid Hmb Hmbsp (conj PA1 PA2) HPAmb HPAsp
                ltac:(split; [split; [exact T1 | (lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); exact GTimg] | exact T2]) GTmb GTPA (conj C1 (conj C2 C3)) Gctxmb GctxPA)
      as (r2 & RUN2 & E1 & E2 & E10 & E11 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & EK).
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_pa]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_na]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_cur]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_mx]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_bl]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; lia | exact R_16]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; lia | exact R_24]. }
    { exact (msum_store_ok BSEGS _ M MH _ _ SUMH SOK_h). }
    { exact (msum_store_ok BSEGS _ M MH _ _ SUMH SOK_pa). }
    { exact (msum_store_ok BSEGS _ M MH _ _ SUMH SOK_inst). }
    { intros o v Hin.
      assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FLA o v Hin). }
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC o v Hin). }
    { assert (Um : U m = mb + 4096) by (rewrite u_Z2bv by lia; reflexivity).
      apply XH; [rewrite at_u by (rewrite Um; lia); rewrite Um; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact Rb1].
      intros z Hz. rewrite at_u in Hz by (rewrite Um; lia). rewrite Um, Erz in Hz. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2, SB in G in change_no_check G' end).
      clear - Hz MB1 MB2 LF2 Hsnb Gn Hmbsp Hmbband GTmb P1 S1. lia. }
    { exact (msum_store_ok BSEGS _ M MH _ _ SUMH SOKh). }
    { rewrite at_at. apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact R16. }
    { apply XH; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact RT0]. intros z Hz. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2, SB in G in change_no_check G' end). clear - Hz T1 T2 GTimg GTband GTmb P1 S1 MB1 LF2 Hsnb Gn. lia. }
    { apply XH; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | | exact Rtid]. intros z Hz. rewrite at_u in Hz by lia. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2, SB in G in change_no_check G' end).
      destruct GHoff as (_ & _ & _ & (O4 & O4' & O4'')). clear - Hz C1 C2 C3 O4' GctxT Gctxmb P1 S1 MB1 T1 LF2 Hsnb Gn. lia. }
    { apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtr]. }
    { rewrite at_at. apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact Rsz. }
    { exact Hsz. }
    exists r2. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUNB | exact RUN2]. }
    repeat (split; [assumption|]).
    split; [rewrite (EK 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10); exact A4|].
    split; [rewrite (EK 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10); exact A3|].
    split; [rewrite (EK 26%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10); rewrite A26; exact H26|].
    rewrite (EK 27%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). rewrite A27. exact H27.
  Qed.
End NG.

(* [comment removed for export] *)
Section G1.
  Variables (M rom : word -> option byte) (regs : bvmap 5 word).
  Variables (S thr tp gp tsdp ctxw midend v72 v80 lkw : word) (cpm k1 k2 k3 : byte) (n mb thr0 nch nres cz PAb : Z).
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
  Hypothesis R_lock : rdn BSEGS M (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; k1; k2; k3].
  Hypothesis V_lock : bytes_le_to_Z [Z_to_bv 8 0; k1; k2; k3] = U lkw.
  Hypothesis SOK_T : store_ok BSEGS M thr 4096 = true.
  Hypothesis SOK_h : store_ok BSEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_lk : store_ok BSEGS M (Z_to_bv 64 0x10ae00) 4 = true.
  Hypothesis R_nch : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis R_nres : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).

  Hypothesis Heq : nch = nres.
  Hypothesis HPAb : 0 <= PAb /\ PAb + 2 ^ 23 < 2 ^ 63.
  Hypothesis R_pab : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 80)) 8 = Some (LE8 (Z_to_bv 64 PAb)).
  #[local] Abbreviation MH := (sh_mem M S thr v72 v80 k1 k2 k3 n mb).

  Theorem sec_run_g1 :
    exists r : bvmap 5 word,
      msteps BSEGS (mkst regs (0x51080 : word) M rom) (mkst r (0x8b244 : word) MH rom)
      /\ getr r 1 = Z_to_bv 64 0x51420 /\ getr r 2 = fsp /\ getr r 11 = Z_to_bv 64 (PAb + 8 * nch) /\ getr r 12 = Z_to_bv 64 0x20000 /\ getr r 13 = Z_to_bv 64 0
      /\ getr r 8 = stats /\ getr r 9 = Z_to_bv 64 (0x10ab58 + 64) /\ getr r 18 = Z_to_bv 64 msz /\ getr r 19 = Z_to_bv 64 cz
      /\ getr r 20 = Z_to_bv 64 (mb + 4096) /\ getr r 21 = Z_to_bv 64 mb
      /\ getr r 4 = tp /\ getr r 3 = gp /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using R_pab HPAb Heq R_nres R_nch SOK_lk SOK_h SOK_T V_lock R_lock R_80 R_72 C_pg SOK_g GHoff GH PH2 PH1 Hclz Hnch GTmb GTband GTimg GT Hmbband Hmbsp Hmb Gn GS H3 H4 H21 H10 HR nres thr0 cpm lkw midend ctxw tsdp.
    destruct (sec_run_a M rom regs S thr tp gp tsdp ctxw midend v72 v80 lkw cpm k1 k2 k3 n mb thr0 nch nres cz
                HR H10 H21 H4 H3 GS Gn Hmb Hmbsp Hmbband GT GTimg GTband GTmb Hnch Hclz PH1 PH2 GH GHoff SOK_g C_pg R_72 R_80 R_lock V_lock SOK_T SOK_h SOK_lk R_nch R_nres)
      as (r1 & RUN1 & (A2 & A8 & A9 & A18) & A19 & A13 & A14 & A21 & A10 & A4 & A3 & A26 & A27).
    pose proof (sh_mem_sum M rom S thr v72 v80 lkw k1 k2 k3 n mb GS Gn Hmb GT) as SUMH.
    destruct GS as [S1 S2]. pose proof Hmb as (MB1 & MB2 & MB3). pose proof GT as (T1 & T2 & T3).
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    assert (LF2 : size + 4096 <= msz <= size + 8191) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    assert (P1 : 0 <= mb / 8 /\ (mb + msz) / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (R_pab' : rdn BSEGS MH (Z_to_bv 64 (0x10ab58 + 80)) 8 = Some (LE8 (Z_to_bv 64 PAb))).
    { apply (msum_rdn_eq BSEGS _ M MH _ _ _ SUMH); [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | | exact R_pab].
      intros z Hz. rewrite u_Z2bv in Hz by lia. cbn in Hz. (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2, SB in G in change_no_check G' end). clear - Hz S1 P1 T1 GTimg MB1. lia. }
    subst nres.
    destruct (la_grow_pre MH rom nch PAb r1 A9 A13 A14 (proj1 Hnch) HPAb R_pab') as (r2 & RUN2 & B1 & B11 & B12 & B13 & B20 & AG2).
    assert (K2 : forall i : reg, In i [2; 3; 4; 8; 9; 18; 19; 21; 26; 27]%bv -> getr r2 i = getr r1 i).
    { intros i Hi. apply AG2. cbn [In] in Hi |- *. intros Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [exact B1|]. split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A2|]. split; [exact B11|]. split; [exact B12|]. split; [exact B13|].
    split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A8|]. split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A9|].
    split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A18|]. split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A19|].
    split; [rewrite B20; exact A10|]. split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A21|].
    split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A4|]. split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A3|].
    split; [rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A26 | rewrite K2 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact A27].
  Qed.
End G1.

(* [comment removed for export] *)
Section G2.
  Variables (M rom : word -> option byte) (regs : bvmap 5 word).
  Variables (S thr ctxw tr szw naw curw mxw blw w16 w24 : word) (bsz : list byte) (b1 : byte) (n mb nch nres PA cz tid : Z).
  #[local] Abbreviation size := (sec_needed n).
  #[local] Abbreviation msz := (la_msz (sec_needed n)).
  #[local] Abbreviation spL := (at_ S (-2320)).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation m := (Z_to_bv 64 (mb + 4096)).
  #[local] Abbreviation idx := (63 - cz).
  Hypothesis H2 : getr regs 2 = at_ spL (-96).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 0x10ae08.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 (0x10ab58 + 64).
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 msz.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 cz.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 mb.
  Hypothesis H20 : getr regs 20 = m.
  Hypothesis H26 : getr regs 26 = thr.
  Hypothesis H27 : getr regs 27 = Z_to_bv 64 1.
  (* [comment removed for export] *)
  Hypothesis GS : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Hnch : 0 <= nch < 2 ^ 20.
  Hypothesis Hcz : 0 <= cz <= 63.
  Hypothesis Htid : 0 <= tid < 2 ^ 31.
  Hypothesis Hmb : AIMGHI <= mb /\ mb + msz <= 2 ^ 47 /\ mb mod 4096 = 0.
  Hypothesis Hmbsp : mb + msz <= U S - 3584 \/ U S <= mb.
  Hypothesis HPA : AIMGHI <= PA /\ PA + 2 ^ 23 < 2 ^ 63.
  Hypothesis HPAmb : PA + 2 ^ 23 <= mb \/ mb + msz <= PA.
  Hypothesis HPAsp : PA + 2 ^ 23 <= U S - 3584 \/ U S <= PA.
  Hypothesis GT : (4096 <= U thr /\ hideW (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr)) /\ U thr + 4096 <= U S - 3584.
  Hypothesis GTmb : U thr + 4096 <= mb \/ mb + msz <= U thr.
  Hypothesis GTPA : U thr + 4096 <= PA \/ PA + 2 ^ 23 <= U thr.
  Hypothesis Gctx : 1 <= U ctxw /\ U ctxw + 4096 <= U S - 3584 /\ (U ctxw + 4096 <= AIMGLO \/ AIMGHI <= U ctxw).
  Hypothesis Gctxmb : U ctxw + 4096 <= mb \/ mb + msz <= U ctxw.
  Hypothesis GctxPA : U ctxw + 4096 <= PA \/ PA + 2 ^ 23 <= U ctxw.
  (* [comment removed for export] *)
  Hypothesis R_pa : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 PA)).
  Hypothesis R_na : rdn BSEGS M (Z_to_bv 64 0x10abe0) 8 = Some (LE8 naw).
  Hypothesis R_cur : rdn BSEGS M (Z_to_bv 64 0x10abf0) 8 = Some (LE8 curw).
  Hypothesis R_mx : rdn BSEGS M (Z_to_bv 64 0x10abf8) 8 = Some (LE8 mxw).
  Hypothesis R_bl : rdn BSEGS M (Z_to_bv 64 (0x10ac00 + 8 * idx)) 8 = Some (LE8 blw).
  Hypothesis R_16 : rdn BSEGS M (Z_to_bv 64 0x10ae18) 8 = Some (LE8 w16).
  Hypothesis R_24 : rdn BSEGS M (Z_to_bv 64 0x10ae20) 8 = Some (LE8 w24).
  Hypothesis SOK_h : store_ok BSEGS M (Z_to_bv 64 mb) 32 = true.
  Hypothesis SOK_pa : store_ok BSEGS M (Z_to_bv 64 (PA + 8 * nch)) 8 = true.
  Hypothesis SOK_inst : store_ok BSEGS M (Z_to_bv 64 0x10ab98) 728 = true.
  Hypothesis FLA : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 size); (-48, Z_to_bv 64 2048);
               (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)] ->
    rdn BSEGS M (at_ spL o) 8 = Some (LE8 v).
  Hypothesis FC : forall (o : Z) (v : word),
    In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 size); (-48, Z_to_bv 64 2048)] ->
    rdn BSEGS M (at_ sp2 o) 8 = Some (LE8 v).
  Hypothesis Rb1 : rdn BSEGS M (at_ m (rz n - 15)) 1 = Some [b1].
  Hypothesis SOKh : store_ok BSEGS M (at_ m (rz n - 16)) 16 = true.
  Hypothesis R16 : rdn BSEGS M (at_ sp2 16) 8 = Some (LE8 (Z_to_bv 64 16)).
  Hypothesis RT0 : rdn BSEGS M thr 8 = Some (LE8 ctxw).
  Hypothesis Rtid : rdn BSEGS M (at_ ctxw 8) 4 = Some (LE4 tid).
  Hypothesis Rtr : rdn BSEGS M (at_ S (-2128)) 8 = Some (LE8 tr).
  Hypothesis Rsz : rdn BSEGS M (at_ (at_ S (-2128)) 8) 8 = Some bsz.
  Hypothesis Hsz : bytes_le_to_Z bsz = U szw /\ length bsz = 8%nat.

  Hypothesis Hnres : 0 <= nres < 2 ^ 32.
  Hypothesis R_nres : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres)).
  Hypothesis R_nch : rdn BSEGS M (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch)).
  Hypothesis SOK_nres : store_ok BSEGS M (Z_to_bv 64 (0x10ab58 + 112)) 8 = true.
  #[local] Abbreviation MG := (la_mg M nres).
  Definition g2_mem : word -> option byte := st_mem MG naw curw mxw blw w16 w24 b1 n mb nch PA cz.
  Definition W_g2 (z : Z) : Prop := (0x10abc8 <= z < 0x10abd0) \/ W_sect mb nch PA z.

  Lemma la_mg_sum : msum (fun z => 0x10abc8 <= z < 0x10abd0) M MG.
  Proof using Hsz mb bsz szw.
    (lazymatch goal with |- ?G => let G' := eval unfold la_mg in G in change_no_check G' end). apply msum_wbytes_in; [apply msum_refl | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia
                                        | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros z Hz; lia].
  Qed.
  Lemma g2_mem_sum : msum W_g2 M g2_mem.
  Proof using Hsz HPA Hmb Htid Hcz Hnch Gn tid bsz szw rom.
    (lazymatch goal with |- ?G => let G' := eval unfold g2_mem, W_g2 in G in change_no_check G' end). eapply msum_trans; [exact la_mg_sum|].
    exact (st_mem_sum MG rom szw naw curw mxw blw w16 w24 bsz b1 n mb nch PA cz tid Gn Hnch Hcz Htid Hmb HPA Hsz).
  Qed.

  Theorem sec_run_g2 :
    exists r : bvmap 5 word,
      msteps BSEGS (mkst regs (0x51420 : word) M rom) (mkst r (Z_to_bv 64 0x8f4f0) g2_mem rom)
      /\ getr r 1 = Z_to_bv 64 0x4c940 /\ getr r 2 = sp2 /\ getr r 10 = tr /\ getr r 11 = szw
      /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = m /\ getr r 19 = Z_to_bv 64 size
      /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 22 = Z_to_bv 64 0x10ab58 /\ getr r 23 = at_ S (-2128)
      /\ getr r 24 = Z_to_bv 64 (tid * 2 ^ 32) /\ getr r 25 = at_ m (rz n + n)
      /\ (forall i : reg, In i [3; 4; 26; 27]%bv -> getr r i = getr regs i).
  Proof using SOK_nres R_nch R_nres Hnres Hsz Rsz Rtr Rtid RT0 R16 SOKh Rb1 FC FLA SOK_inst SOK_pa SOK_h R_24 R_16 R_bl R_mx R_cur R_na R_pa GctxPA Gctxmb Gctx GTPA GTmb GT HPAsp HPAmb HPA Hmbsp Hmb Htid Hcz Hnch Gn GS H27 H26 H20 H21 H19 H18 H9 H8 H2 bsz ctxw thr.
    destruct (la_grow_post M rom nres nch m regs H9 H20 Hnres R_nres R_nch SOK_nres) as (r1 & RUN1 & A10 & A13 & AG1).
    assert (K1 : forall i : reg, In i [2; 3; 4; 8; 9; 18; 19; 21; 26; 27]%bv -> getr r1 i = getr regs i).
    { intros i Hi. apply AG1. cbn [In] in Hi |- *. intros Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi. }
    pose proof la_mg_sum as SUMG.
    destruct GS as [S1 S2]. pose proof Hmb as (MB1 & MB2 & MB3). destruct GT as ((T1 & T1b) & T2). destruct Gctx as (C1 & C2 & C3). destruct HPA as [PA1 PA2].
    pose proof (u64_range S) as HSr. pose proof (u64_range thr) as Hthr. pose proof (u64_range ctxw) as Hcr.
    pose proof (rz_sec n ltac:(lia)) as Erz. pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
    assert (LF2 : size + 4096 <= msz <= size + 8191) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); Z.div_mod_to_equations; lia).
    assert (XG : forall (a : word) (k : nat) v, U a + Z.of_nat k <= 2 ^ 64 -> (forall z, U a <= z < U a + Z.of_nat k -> ~ (0x10abc8 <= z < 0x10abd0)) ->
              rdn BSEGS M a k = Some v -> rdn BSEGS MG a k = Some v).
    { intros a k v Hnw Hd Hr. exact (msum_rdn_eq BSEGS _ M MG a k v SUMG Hnw Hd Hr). }
    assert (XI : forall (c : Z) (k : nat) v, 0 <= c -> c + Z.of_nat k <= AIMGHI -> (c + Z.of_nat k <= 0x10abc8 \/ 0x10abd0 <= c) ->
              rdn BSEGS M (Z_to_bv 64 c) k = Some v -> rdn BSEGS MG (Z_to_bv 64 c) k = Some v).
    { intros c k v Hc1 Hc2 Hlk Hr. apply XG; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | | exact Hr]. intros z Hz. rewrite u_Z2bv in Hz by lia. clear - Hz Hlk. lia. }
    assert (XS : forall (k : Z) (w : nat) v, -3584 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS M (at_ S k) w = Some v -> rdn BSEGS MG (at_ S k) w = Some v).
    { intros k w v Kl Kh Hr. apply XG; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | | exact Hr]. intros z Hz. rewrite at_u in Hz by lia. clear - Hz Kl S1. lia. }
    destruct (sec_run_tail MG rom r1 S thr ctxw tr szw naw curw mxw blw w16 w24 bsz b1 n mb nch PA cz tid
                ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact H2) ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact H8)
                ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact H9) ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact H18)
                ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact H19) ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact H21) A13 A10
                ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact H26) ltac:(rewrite K1 by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 12); exact H27)
                (conj S1 S2) Gn Hnch Hcz Htid Hmb Hmbsp (conj PA1 PA2) HPAmb HPAsp (conj (conj T1 T1b) T2) GTmb GTPA (conj C1 (conj C2 C3)) Gctxmb GctxPA)
      as (r2 & RUN2 & E1 & E2 & E10 & E11 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & EK).
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact R_pa]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; lia | exact R_na]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; lia | exact R_cur]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; lia | exact R_mx]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; lia | exact R_bl]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; lia | exact R_16]. }
    { apply XI; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | right; lia | exact R_24]. }
    { exact (msum_store_ok BSEGS _ M MG _ _ SUMG SOK_h). }
    { exact (msum_store_ok BSEGS _ M MG _ _ SUMG SOK_pa). }
    { exact (msum_store_ok BSEGS _ M MG _ _ SUMG SOK_inst). }
    { intros o v Hin.
      assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FLA o v Hin). }
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact (FC o v Hin). }
    { assert (Um : U m = mb + 4096) by (rewrite u_Z2bv by lia; reflexivity).
      apply XG; [rewrite at_u by (rewrite Um; lia); rewrite Um; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact Rb1].
      intros z Hz. rewrite at_u in Hz by (rewrite Um; lia). rewrite Um, Erz in Hz. cbn in Hz. clear - Hz MB1. lia. }
    { exact (msum_store_ok BSEGS _ M MG _ _ SUMG SOKh). }
    { rewrite at_at. apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact R16. }
    { apply XG; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | | exact RT0]. intros z Hz. cbn in Hz. unfold hideW in T1b. clear - Hz T1 T1b. lia. }
    { apply XG; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | | exact Rtid]. intros z Hz. rewrite at_u in Hz by lia. cbn in Hz. clear - Hz C1 C3. lia. }
    { apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact Rtr]. }
    { rewrite at_at. apply XS; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. rewrite <- at_at. exact Rsz. }
    { exact Hsz. }
    exists r2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    repeat (split; [assumption|]).
    intros i Hi. rewrite (EK i Hi). apply K1. cbn [In] in Hi |- *. clear - Hi. repeat (destruct Hi as [<-|Hi]; [auto 12|]). destruct Hi.
  Qed.
End G2.
End FPGen.
End BoAllocMRunS4.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMRunS5.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM9f OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocMSumS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS3 BoAllocMRunS4.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Ltac s5_side :=
  wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u, ?u_Z2bv by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite ?u_Z2bv by lia; lia ]);
  (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia.
Ltac s5_peel := rewrite rdn_wbytes_out; [| solve [s5_side] | solve [s5_side] | solve [s5_side]].
Ltac s5_peel1 := rewrite wb_out; [| solve [s5_side] | solve [s5_side]].

(* [comment removed for export] *)
Section SH.
  Variables (M : word -> option byte) (S thr v72 v80 : word) (k1 k2 k3 : byte) (n mb : Z).
  #[local] Abbreviation size := (sec_needed n).
  #[local] Abbreviation msz := (la_msz (sec_needed n)).
  #[local] Abbreviation spL := (at_ S (-2320)).
  #[local] Abbreviation stats := (Z_to_bv 64 0x10ae08 : word).
  #[local] Abbreviation MH := (sh_mem M S thr v72 v80 k1 k2 k3 n mb).
  Hypothesis GS : 2 ^ 32 + 8192 <= U S /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Hmb : AIMGHI <= mb /\ mb + msz <= 2 ^ 47 /\ mb mod 4096 = 0.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma la_geo5 : msz mod 4096 = 0 /\ size + 4096 <= msz <= size + 8191 /\ n + 4096 <= size <= n + 4103
                  /\ mb + 4096 + size - 7 <= la_tb size mb <= mb + 4096 + size
                  /\ mb / 8 + 512 <= la_tb size mb / 8 /\ 0 <= mb / 8 /\ (mb + msz) / 8 <= 2 ^ 44 /\ la_tb size mb / 8 <= (mb + msz) / 8.
  Proof using Hmb Gn v80 M.
    pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb. destruct Hmb as (MB1 & MB2 & MB3).
    assert (A1 : msz mod 4096 = 0 /\ size + 4096 <= msz <= size + 8191) by ((lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end); lia).
    assert (A2 : mb + 4096 + size - 7 <= la_tb size mb <= mb + 4096 + size) by ((lazymatch goal with |- ?G => let G' := eval unfold la_tb in G in change_no_check G' end); lia).
    destruct A1 as [A1 A1']. split; [exact A1|]. split; [exact A1'|]. split; [exact Hsnb|]. split; [exact A2|].
    generalize dependent (la_tb size mb). generalize dependent msz. intros z _ Hz _ t Ht.
    split; [lia|]. split; [lia|]. split; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma sh_mem_hdr :
    rdn BSEGS MH (Z_to_bv 64 mb) 8 = Some (LE8 (Z_to_bv 64 mb))
    /\ rdn BSEGS MH (Z_to_bv 64 (mb + 8)) 8 = Some (LE8 (Z_to_bv 64 msz))
    /\ rdn BSEGS MH (Z_to_bv 64 (mb + 16)) 8 = Some (LE8 (Z_to_bv 64 size)).
  Proof using Hmb Gn.
    destruct Hmb as (MB1 & MB2 & MB3). pose proof la_geo5 as (G1 & G2 & G3 & _).
    (lazymatch goal with |- ?G => let G' := eval unfold sh_mem, la_m1 in G in change_no_check G' end). split; [| split].
    - do 3 s5_peel. apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - do 2 s5_peel. apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - s5_peel. apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  Qed.

  Hypothesis Hmbband : mb + msz <= AS_LO \/ AS_HEAPLO <= mb.
  Hypothesis GT : 4096 <= U thr /\ U thr + 4096 <= U S - 3584.
  Hypothesis GTband : U thr + 4096 <= AS_LO \/ AS_HEAPLO <= U thr.
  Hypothesis GSband : AS_HEAPLO <= U S - 3584.

  Lemma sh_mem_fa : forall x : word, SB + mb / 8 <= U x < SB + mb / 8 + 512 -> MH x = Some (Z_to_bv 8 250).
  Proof using GSband GTband GT Hmbband Hmb Gn GS.
    intros x Hx. destruct GS as [S1 S2]. destruct Hmb as (MB1 & MB2 & MB3). destruct GT as [T1 T2].
    pose proof la_geo5 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
    pose proof (u64_range S) as HSr. pose proof (u64_range thr) as Hthr. pose proof (u64_range x) as Hxr.
    unfold SB, AS_LO, AS_HEAPLO in *.
    set (q := mb / 8) in *. set (qt := la_tb size mb / 8) in *. set (qe := (mb + msz) / 8) in *.
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold sh_mem, la_m1 in G in change_no_check G' end).
    rewrite wb_out; [| solve [s5_side] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite u_Z2bv by lia; clear - Hx G5 G6 G7 G8; lia].
    rewrite wb_out; [| solve [s5_side] | rewrite length_N_to_le_bytes, u_Z2bv by lia; clear - Hx G5 G6 G7 G8 MB1 MB2 Hmbband G2 G3 Gn; lia].
    rewrite wb_out; [| solve [s5_side] | rewrite length_N_to_le_bytes, u_Z2bv by lia; clear - Hx G5 G6 G7 G8 MB1 MB2 Hmbband G2 G3 Gn; lia].
    rewrite wb_out; [| solve [s5_side] | rewrite length_N_to_le_bytes, u_Z2bv by lia; clear - Hx G5 G6 G7 G8 MB1 MB2 Hmbband G2 G3 Gn; lia].
    rewrite wb_out; [| solve [s5_side] | rewrite length_N_to_le_bytes, at_u by lia; clear - Hx G5 G6 G7 G8 T1 T2 GTband; lia].
    rewrite wb_out; [| solve [s5_side] | rewrite length_N_to_le_bytes, at_u by lia; clear - Hx G5 G6 G7 G8 T1 T2 GTband; lia].
    (* [comment removed for export] *)
    (lazymatch goal with |- ?G => let G' := eval unfold sh_m3, lam_3 in G in change_no_check G' end).
    rewrite wb_out; [| solve [s5_side] | rewrite length_N_to_le_bytes, !at_at, at_u by lia; clear - Hx G5 G6 G7 G8 S1 S2 GSband; lia].
    rewrite wb_out; [| solve [s5_side] | rewrite length_N_to_le_bytes, !at_at, at_u by lia; clear - Hx G5 G6 G7 G8 S1 S2 GSband; lia].
    (* [comment removed for export] *)
    assert (Ufsp : U (at_ spL (-96)) = U S - 2416) by (rewrite at_at, at_u by lia; lia).
    pose proof (psm_facts (lam_1 M spL stats size mb) (at_ spL (-96)) (Z_to_bv 64 0x510e8) stats (Z_to_bv 64 (0x10ab58 + 64)) (Z_to_bv 64 msz)
                  (Z_to_bv 64 size) (Z_to_bv 64 mb) (Z_to_bv 64 (mb + 4096 + size)) (la_tb size mb) (mb + msz - la_tb size mb) 250
                  ltac:(rewrite Ufsp; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as PF2.
    cbv zeta in PF2. destruct PF2 as (OUT2 & _ & _).
    pose proof (psm_facts M (at_ spL (-96)) (Z_to_bv 64 0x510d8) stats (Z_to_bv 64 (0x10ab58 + 64)) (Z_to_bv 64 msz)
                  (Z_to_bv 64 size) (Z_to_bv 64 mb) (Z_to_bv 64 (mb + 4096 + size)) mb 4096 250
                  ltac:(rewrite Ufsp; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as PF1.
    cbv zeta in PF1. destruct PF1 as (_ & IN1 & _). change (4096 / 8) with 512 in IN1.
    transitivity (lam_1 M spL stats size mb x).
    - apply OUT2; [rewrite Ufsp; clear - Hx G5 G6 G7 G8 S1 S2 GSband; lia | left; fold qt; clear - Hx G5; lia].
    - unfold psm in IN1. (lazymatch goal with |- ?G => let G' := eval unfold lam_1 in G in change_no_check G' end). rewrite IN1 by (fold q; clear - Hx; lia). reflexivity.
  Qed.
End SH.

(* [comment removed for export] *)
Section ST.
  Variables (M : word -> option byte) (naw curw mxw blw w16 w24 : word) (b1 : byte) (n mb nch PA cz : Z).
  #[local] Abbreviation msz := (la_msz (sec_needed n)).
  #[local] Abbreviation MT := (st_mem M naw curw mxw blw w16 w24 b1 n mb nch PA cz).
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Hnch : 0 <= nch < 2 ^ 20.
  Hypothesis Hcz : 0 <= cz <= 63.
  Hypothesis Hmb : AIMGHI <= mb /\ mb + msz <= 2 ^ 47 /\ mb mod 4096 = 0.
  Hypothesis HPA : AIMGHI <= PA /\ PA + 2 ^ 23 < 2 ^ 63.
  Hypothesis HPAmb : PA + 2 ^ 23 <= mb \/ mb + msz <= PA.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma st_geo5 : n + 8192 <= msz.
  Proof using Hmb Hnch Gn nch mb w24 M. pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb. (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end). lia. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma st_mem_cells :
    rdn BSEGS MT (Z_to_bv 64 (mb + 24)) 8 = Some (LE8 (Z_to_bv 64 nch))
    /\ rdn BSEGS MT (Z_to_bv 64 (PA + 8 * nch)) 8 = Some (LE8 (Z_to_bv 64 mb))
    /\ rdn BSEGS MT (Z_to_bv 64 0x10abd0) 8 = Some (LE8 (Z_to_bv 64 (nch + 1)))
    /\ rdn BSEGS MT (Z_to_bv 64 0x10ae00) 1 = Some [Z_to_bv 8 0]
    /\ MT (Z_to_bv 64 (mb + 4096 + 2048 - 15)) = Some (Z_to_bv 8 (U (hb1w (Z_to_bv 64 (U b1)))))
    /\ rdn BSEGS MT (Z_to_bv 64 (mb + 4096 + 2048 - 14)) 2 = Some (LE2 (n / 2 ^ 32))
    /\ rdn BSEGS MT (Z_to_bv 64 (mb + 4096 + 2048 - 12)) 4 = Some (LE4 n).
  Proof using HPAmb HPA Hmb Hcz Hnch Gn.
    destruct Hmb as (MB1 & MB2 & MB3). destruct HPA as [PA1 PA2]. pose proof st_geo5 as G1.
    assert (Erz : rz n = 2048) by (apply rz_sec; lia).
    assert (E15 : at_ (Z_to_bv 64 (mb + 4096)) (2048 - 15) = Z_to_bv 64 (mb + 4096 + 2048 - 15)) by (apply bv_eq; rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]).
    assert (E14 : at_ (Z_to_bv 64 (mb + 4096)) (2048 - 14) = Z_to_bv 64 (mb + 4096 + 2048 - 14)) by (apply bv_eq; rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]).
    assert (E12 : at_ (Z_to_bv 64 (mb + 4096)) (2048 - 12) = Z_to_bv 64 (mb + 4096 + 2048 - 12)) by (apply bv_eq; rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]).
    (lazymatch goal with |- ?G => let G' := eval unfold st_mem, amCs_mem, st_m2, la_m2 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite Erz, E15, E14, E12.
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - do 14 s5_peel. apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - do 13 s5_peel. apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - do 12 s5_peel. apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - do 4 s5_peel. apply (rdn_wbytes_hit BSEGS [Z_to_bv 8 0]). rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - rewrite wbytes_inside; [| (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]].
      rewrite Z.sub_diag. reflexivity.
    - do 2 s5_peel. apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
    - s5_peel. apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  Qed.

  (* [comment removed for export] *)
  Lemma st_mem_below : forall (c : Z) (k : nat), AIMGLO <= c -> c + Z.of_nat k <= 0x10abd0 ->
    rdn BSEGS MT (Z_to_bv 64 c) k = rdn BSEGS M (Z_to_bv 64 c) k.
  Proof using HPA Hmb Hcz Hnch Gn.
    intros c k Hc1 Hc2. destruct Hmb as (MB1 & MB2 & MB3). destruct HPA as [PA1 PA2]. pose proof st_geo5 as G1.
    assert (Erz : rz n = 2048) by (apply rz_sec; lia).
    (lazymatch goal with |- ?G => let G' := eval unfold st_mem, amCs_mem, st_m2, la_m2 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite Erz.
    do 15 s5_peel. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma st_mem_tail8 : forall x : word, mb + 4096 + 2048 - 8 <= U x < mb + 4096 + 2048 -> MT x = M x.
  Proof using HPAmb HPA Hmb Hcz Hnch Gn.
    intros x Hx. destruct Hmb as (MB1 & MB2 & MB3). destruct HPA as [PA1 PA2]. pose proof st_geo5 as G1. pose proof (u64_range x) as Hxr.
    assert (Erz : rz n = 2048) by (apply rz_sec; lia).
    (lazymatch goal with |- ?G => let G' := eval unfold st_mem, amCs_mem, st_m2, la_m2 in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite Erz.
    do 15 s5_peel1. reflexivity.
  Qed.
End ST.

(* [comment removed for export] *)
Lemma g2_mem_nres : forall (M : word -> option byte) (naw curw mxw blw w16 w24 : word) (b1 : byte) (n mb nch nres PA cz : Z),
  64513 <= n <= 2 ^ 34 -> 0 <= nch < 2 ^ 20 -> 0 <= cz <= 63 ->
  (AIMGHI <= mb /\ mb + la_msz (sec_needed n) <= 2 ^ 47 /\ mb mod 4096 = 0) -> (AIMGHI <= PA /\ PA + 2 ^ 23 < 2 ^ 63) ->
  rdn BSEGS (g2_mem M naw curw mxw blw w16 w24 b1 n mb nch nres PA cz) (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 (nres + 0x4000))).
Proof.
  intros M naw curw mxw blw w16 w24 b1 n mb nch nres PA cz Gn Hnch Hcz Hmb HPA.
  (lazymatch goal with |- ?G => let G' := eval unfold g2_mem in G in change_no_check G' end). rewrite (st_mem_below (la_mg M nres) naw curw mxw blw w16 w24 b1 n mb nch PA cz Gn Hnch Hcz Hmb HPA (0x10ab58 + 112) 8%nat ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
  (lazymatch goal with |- ?G => let G' := eval unfold la_mg in G in change_no_check G' end). apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
Qed.
End BoAllocMRunS5.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSecGrow.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcGS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM9h OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Lemma store_ok1_defW : forall (m : mem) (a : word), m a <> None -> store_ok BSEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section GROW.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis BF : boot_facts bt.
  Hypothesis GROW_DIE :
    forall (fx : FPState) (regs : bvmap 5 word) (M rom : word -> option byte) (sp addr v44 : word),
      FXOK fx -> getr regs 2 = sp -> getr regs 18 = addr ->
      2 ^ 32 + 4096 <= U sp <= 2 ^ 47 - 16 -> U sp mod 16 = 0 -> 4096 <= U addr < 2 ^ 47 ->
      store_ok BSEGS M (at_ sp (-1072)) 1168 = true -> rdn BSEGS M (at_ sp 44) 4 = Some (word_to_le_bytes 4 v44) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1d5) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x612079726f6d656d)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1dd) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7365726464612074)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1e5) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x70252073)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1e9) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
      rdn BSEGS M (Z_to_bv 64 0x22730) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x613e0)) ->
      rdn BSEGS M (Z_to_bv 64 0x104a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa)) ->
      rdn BSEGS M (Z_to_bv 64 0x105f58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
      rdn BSEGS M (Z_to_bv 64 0x19fcdc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
      exists fx' r M', msteps BSEGS (@mkst fx regs (0x82fe8%bv : word) M rom) (@mkst fx' r (0x7ca24%bv : word) M' rom).

  #[local] Abbreviation P8 := (bt_ptrarr bt).

  Theorem sec_grow_node :
    forall fx (regs : bvmap 5 word) (MC : mem) (mdl mdlq mdl1 : Model) (st st1 : ast) (Lc FF : list (Z * Z)) (M0 : mem) (a : word) (n : Z)
           (S : word) (PGP CF : Z) (Q : config -> Prop) (s0v s1v s2v s3v s4v s5v : word),
      let msz := sec_map_size n in
      let A := a_aa st1 in
      let Hd := HID st1 mdlq in
      let sp := at_ S (-2416) in
      let ra : word := Z_to_bv 64 0x51420 in
      let addr : word := Z_to_bv 64 (P8 + 8 * a_nres st) in
      let size : word := Z_to_bv 64 (2 ^ 17) in
      let name : word := Z_to_bv 64 0 in
      let M1 := mfo_m1 MC sp ra s0v s1v s2v s3v s4v s5v addr size name PGP in
      FXOK fx -> WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> BackingAlgebra.model_ivs_wf mdl -> a_nres st + 2 ^ 14 <= 2 ^ 20 ->
      chunk_child mdl mdlq a (Z_to_bv 64 msz) -> 0 <= msz < 2 ^ 64 ->
      (U a + msz <= P8 \/ P8 + 2 ^ 23 <= U a) ->
      A_wf A -> eager_used mdl + msz + 2 ^ 17 + A_bytes A <= vm_limit (m_vmmaps mdl) ->
      same_but_materialized mdlq mdl1 -> MInv A mdl1 ->
      H_off_segments BSEGS Hd ->
      (forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false) ->
      getr regs 1 = ra -> getr regs 2 = sp -> getr regs 11 = addr -> getr regs 12 = size -> getr regs 13 = name ->
      getr regs 8 = s0v -> getr regs 9 = s1v -> getr regs 18 = s2v -> getr regs 19 = s3v -> getr regs 20 = s4v -> getr regs 21 = s5v ->
      CEIL + 3584 <= U S -> U S + 16 <= 2 ^ 47 -> U S mod 16 = 0 ->
      (forall x : word, U S - 3584 <= U x < U S -> MC x <> None /\ store_ok BSEGS MC x 1%nat = true) ->
      (AIMGLO <= PGP /\ PGP + 8 <= AIMGHI) -> (AIMGLO <= CF /\ CF + 264 <= AIMGHI) ->
      rdn BSEGS MC (Z_to_bv 64 0x105ef8) 8 = Some (LE8 (Z_to_bv 64 PGP)) ->
      rdn BSEGS MC (Z_to_bv 64 PGP) 8 = Some (LE8 (Z_to_bv 64 4096)) ->
      rdn BSEGS MC (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CF)) ->
      rdn BSEGS MC (Z_to_bv 64 (CF + 144)) 8 = Some (LE8 (Z_to_bv 64 0)) ->
      rdn BSEGS MC (Z_to_bv 64 0x1e1d5) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x612079726f6d656d)) ->
      rdn BSEGS MC (Z_to_bv 64 0x1e1dd) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7365726464612074)) ->
      rdn BSEGS MC (Z_to_bv 64 0x1e1e5) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x70252073)) ->
      rdn BSEGS MC (Z_to_bv 64 0x1e1e9) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
      rdn BSEGS MC (Z_to_bv 64 0x22730) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x613e0)) ->
      rdn BSEGS MC (Z_to_bv 64 0x104a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa)) ->
      rdn BSEGS MC (Z_to_bv 64 0x105f58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
      rdn BSEGS MC (Z_to_bv 64 0x19fcdc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
      (forall (r' : bvmap 5 word) (mdlm mdl4 : Model),
          same_but_materialized mdlq mdlm -> MInv A mdlm -> same_but_materialized (fixedin_ok_model 3 (Z_to_bv 64 50) addr size mdlm) mdl4 -> MInv A mdl4 ->
          mfi_ret regs r' sp ra s0v s1v s2v s3v s4v addr ->
          katD BSEGS (mkCfg (@mkst fx r' ra (wbytes (zfill addr size M1) (at_ sp (-52)) (LE4 0xffffffffaaaaaaaa)) (seg_rom BSEGS)) mdl4) Q) ->
      katD BSEGS (mkCfg (@mkst fx regs (Z_to_bv 64 0x8b244) MC (seg_rom BSEGS)) mdl1) Q.
  Proof using GROW_DIE BF BT_ia.
    intros fx regs MC mdl mdlq mdl1 st st1 Lc FF M0 a n S PGP CF Q s0v s1v s2v s3v s4v s5v msz A Hd sp ra addr size name M1
           HFX W RP MW GROW CC MSZR APC AW BUD SBM1 MI1 HOFF NHs X1 X2 X11 X12 X13 X8 X9 X18 X19 X20 X21 CEILS SHI S16 STK GPGP GCF
           C_gpg C_pg C_gcf C_lim D1 D2 D3 D4 D5 D6 D7 D8 CONT.
    pose proof ceil_rng as CR. pose proof (u64_range S) as HSr.
    assert (IMGLO' : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
    pose proof (ptrarr_geom bt st Lc FF W IMGLO') as (PA1 & PA2 & PA3 & _). rewrite BT_ia in PA1. cbn [ia_img_hi both_addrs] in PA1.
    pose proof W as (_ & _ & _ & (NR1 & NR2 & NR3 & _) & _).
    assert (Usz : U (Z_to_bv 64 msz : word) = msz) by (rewrite u_Z2bv by lia; reflexivity).
    pose proof (N8_pf bt BF st Lc FF M0 mdl mdlq a (Z_to_bv 64 msz) A (2 ^ 20) (2 ^ 28) W RP MW GROW CC
                  ltac:(rewrite Usz; exact APC) AW ltac:(rewrite Usz; exact BUD)) as N8.
    cbv zeta in N8. fold addr size in N8. destruct N8 as (P1 & P2 & P3 & P4 & NODEF & _).
    set (lo := P8 + 8 * a_nres st) in *.
    assert (LOR : AIMGHI <= lo /\ lo + 2 ^ 17 <= P8 + 2 ^ 23) by ((lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end); clear - PA1 GROW NR3; lia).
    assert (Usp : U sp = U S - 2416) by ((lazymatch goal with |- ?G => let G' := eval unfold sp in G in change_no_check G' end); rewrite at_u by (clear - CEILS HSr CR; lia); clear; lia).
    destruct CC as (EV1 & EN1 & EL1 & ER1 & EB1 & ES1 & EMB1 & EI1 & EM1 & EG1 & MW1 & HH1).
    pose proof (same_but_materialized_frame mdlq mdl1 SBM1) as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl1 & _).
    assert (LCq : lazy_cover Hd (m_vm_lazy mdl) A) by (rewrite <- EL1; (lazymatch goal with |- ?G => let G' := eval unfold Hd, A in G in change_no_check G' end); apply lazy_cover_HID).
    assert (OKm_eq : forall m, fixedin_ok_model 3 (Z_to_bv 64 50) addr size m = fixedin_ok_model 3 (Z_to_bv 64 50) addr size m) by reflexivity.
    replace (Z_to_bv 64 0x8b244 : word) with (0x8b244%bv : word) by (apply bv_eq; reflexivity).
    apply (@rarmapo_katD fx Hd HOFF asanF_segs_wx A regs MC (seg_rom BSEGS) mdl1 sp ra s0v s1v s2v s3v s4v s5v addr size name PGP CF Q
             (fixedin_ok_model 3 (Z_to_bv 64 50) addr size) (fun m => m) (fixedin_destroyed_model addr size) X1 X2 X11 X12 X13 X8 X9 X18 X19 X20 X21).
    - rewrite Usp. clear - CEILS CR SHI. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - rewrite P3. exact P1.
    - rewrite P4. split; [reflexivity | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold name in G in change_no_check G' end). rewrite u_Z2bv by lia. reflexivity.
    - exact GPGP.
    - exact GCF.
    - apply store_ok_bytes; [| rewrite at_u by (rewrite Usp; clear - CEILS HSr CR; lia); rewrite Usp; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HSr CEILS; lia].
      intros x Hx. rewrite at_u in Hx by (rewrite Usp; clear - CEILS HSr CR; lia). rewrite Usp in Hx. cbn in Hx. apply STK. clear - Hx. lia.
    - exact C_gpg.
    - exact C_pg.
    - exact C_gcf.
    - exact C_lim.
    - rewrite P3, P4, Usp. split; [exact (proj1 LOR)|]. split; [clear - LOR PA2 CR; lia | left; clear - LOR PA2 CEILS; lia].
    - intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | right; clear - Hx; lia].
    - intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | right; clear - Hx GPGP; lia].
    - intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | right; clear - Hx; lia].
    - intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | right; clear - Hx GCF; lia].
    - intros x Hx. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | left; rewrite Usp in Hx; clear - Hx CEILS; lia].
    - rewrite Ehl1. exact HH1.
    - rewrite Elz1, EL1. exact LCq.
    - exact AW.
    - exact MI1.
    - (* [comment removed for export] *)
      intros mdlm r1 SBm MIm HLm G10 G11 G12 G13 G14 G15 Q' K1 K2 K3.
      destruct (NODEF mdlm (same_but_materialized_trans _ _ _ SBM1 SBm) MIm) as (N1 & N2 & N3 & N4 & N5 & _).
      apply (@node3_of_fixedin3_dm fx r1 _ (seg_rom BSEGS) mdlm addr size Q' HLm G10 G11 G12 G13 G14 G15);
        [rewrite P3; exact P1 | rewrite P3; exact P2 | rewrite P4; lia | rewrite P4; reflexivity | exact N1 | exact N2 | exact N3 | exact N4 | exact N5 | exact K1 | exact K2 | exact K3].
    - (* [comment removed for export] *)
      intros mdlm SBm MIm.
      destruct (NODEF mdlm (same_but_materialized_trans _ _ _ SBM1 SBm) MIm) as (_ & _ & _ & _ & _ & HOK & MOKI & LZOK & HDS & MDSI & LZDS).
      pose proof (same_but_materialized_frame mdl1 mdlm SBm) as (_ & _ & Elzm & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehlm & _).
      split; [| split].
      + split; [exact HOK|]. split; [| exact MOKI]. exact (lazy_cover_sub Hd _ _ _ LCq LZOK).
      + split; [rewrite Ehlm, Ehl1; exact HH1|]. split; [| exact MIm]. rewrite Elzm, Elz1, EL1. exact LCq.
      + split; [exact HDS|]. split; [| exact MDSI]. exact (lazy_cover_sub Hd _ _ _ LCq LZDS).
    - (* [comment removed for export] *)
      intros r' mdlm mdl4 SBm MIm SB4 MI4 RET.
      exact (CONT r' mdlm mdl4 (same_but_materialized_trans _ _ _ SBM1 SBm) MIm SB4 MI4 RET).
    - (* [comment removed for export] *)
      intros MZ r2 HMZ G2 G8 G9 G18 G19.
      set (MW2 := wbytes (wbytes MZ (at_ sp (-52)) (LE4 0xffffffffaaaaaaaa)) (at_ sp (-52)) (LE4 12)).
      assert (U52 : U (at_ sp (-52)) = U S - 2468) by (rewrite at_u by (rewrite Usp; clear - CEILS HSr CR; lia); rewrite Usp; clear; lia).
      assert (U96 : U (at_ sp (-96)) = U S - 2512) by (rewrite at_u by (rewrite Usp; clear - CEILS HSr CR; lia); rewrite Usp; clear; lia).
      assert (MZout : forall x : word, (U x < U S - 3584 \/ U S <= U x) -> (U x < lo \/ lo + 2 ^ 17 <= U x) -> MZ x = MC x).
      { intros x Hs Hl. destruct HMZ as [-> | ->].
        - apply mfo_m1_outside; [rewrite Usp; clear - CEILS CR SHI; lia | rewrite Usp; clear - Hs; lia].
        - rewrite unfill_out by (rewrite P3, P4; exact Hl). apply mfo_m1_outside; [rewrite Usp; clear - CEILS CR SHI; lia | rewrite Usp; clear - Hs; lia]. }
      assert (MZstk : forall x : word, U S - 3584 <= U x < U S -> MZ x <> None).
      { intros x Hx. destruct HMZ as [-> | ->].
        - apply mfo_m1_grows. exact (proj1 (STK x Hx)).
        - rewrite unfill_out by (rewrite P3, P4; right; clear - Hx LOR PA2 CEILS; lia). apply mfo_m1_grows. exact (proj1 (STK x Hx)). }
      assert (IMGEQ : forall x : word, AIMGLO <= U x < AIMGHI -> mrestrict Hd MW2 x = MC x).
      { intros x Hx. pose proof (u64_range x) as Hxr.
        rewrite mrestrict_off by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHs; [exact Hxr | right; clear - Hx; lia]).
        (lazymatch goal with |- ?G => let G' := eval unfold MW2 in G in change_no_check G' end). rewrite !wb_out by (wd_lenlit; rewrite ?length_N_to_le_bytes, U52; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hx CEILS CR HSr; lia).
        apply MZout; [left; clear - Hx CEILS CR; lia | left; clear - Hx LOR; lia]. }
      assert (ROW : forall (c : Z) (k : nat) v, AIMGLO <= c -> c + Z.of_nat k <= AIMGHI -> rdn BSEGS MC (Z_to_bv 64 c) k = Some v ->
                rdn BSEGS (mrestrict Hd MW2) (Z_to_bv 64 c) k = Some v).
      { intros c k v Hc1 Hc2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply IMGEQ. clear - Hx Hc1 Hc2. lia. }
      apply (GROW_DIE fx r2 (mrestrict Hd MW2) (seg_rom BSEGS) (at_ sp (-96)) addr (Z_to_bv 64 12) HFX G2 G18).
      + rewrite U96. clear - CEILS CR SHI. lia.
      + rewrite U96. clear - S16. Z.div_mod_to_equations. lia.
      + rewrite P3. clear - LOR PA2 CR. lia.
      + (* [comment removed for export] *)
        assert (UA : U (at_ (at_ sp (-96)) (-1072)) = U S - 3584) by (rewrite at_u by (rewrite U96; clear - CEILS HSr CR; lia); rewrite U96; clear; lia).
        rewrite store_ok_mrestrict; [| rewrite UA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HSr; lia | rewrite UA; intros x Hx; cbn in Hx; pose proof (u64_range x);
                                       rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHs; [lia | left; clear - Hx CEILS; lia]].
        apply store_ok_bytes; [| rewrite UA; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HSr; lia]. intros x Hx. rewrite UA in Hx. cbn in Hx.
        apply store_ok1_defW. (lazymatch goal with |- ?G => let G' := eval unfold MW2 in G in change_no_check G' end). do 2 apply wbytes_grows. apply MZstk. clear - Hx. lia.
      + replace (at_ (at_ sp (-96)) 44) with (at_ sp (-52)) by (rewrite at_at; reflexivity).
        rewrite <- (rdn_wbytes_hitw BSEGS (wbytes MZ (at_ sp (-52)) (LE4 0xffffffffaaaaaaaa)) (at_ sp (-52)) (Z_to_bv 64 12) 4) by (rewrite U52; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HSr; lia).
        apply rdn_ext; [rewrite U52; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - HSr; lia|]. intros x Hx. rewrite U52 in Hx. cbn in Hx. pose proof (u64_range x).
        apply mrestrict_off. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [lia | left; clear - Hx CEILS; lia].
      + exact (ROW 0x1e1d5 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) D1).
      + exact (ROW 0x1e1dd 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) D2).
      + exact (ROW 0x1e1e5 4%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) D3).
      + exact (ROW 0x1e1e9 1%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) D4).
      + exact (ROW 0x22730 4%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) D5).
      + exact (ROW 0x104a8 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) D6).
      + exact (ROW 0x105f58 8%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) D7).
      + exact (ROW 0x19fcdc 4%nat _ ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) D8).
  Qed.
End GROW.
End WithCeil.
End BoAllocMSecGrow.
Module BoAllocMSecPh2.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Section PHZ.
  Variables (M : word -> option byte) (MIDEND : Z).
  Hypothesis C_gsb : rdn BSEGS M (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sb : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS M (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS M (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND)).
  Hypothesis C_ghe : rdn BSEGS M (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS M (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS M (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).

  Variables (addr size : Z) (ra fsp : word).
  Hypothesis Ha8 : addr mod 8 = 0.
  Hypothesis Hs8 : size mod 8 = 0.
  Hypothesis Hrng : (0x10007fff8000 <= addr /\ 0 <= size /\ 0x10007fff8008 <= addr + size /\ addr + size + 8 <= 0x800000000000)
                    \/ (8 <= addr /\ 0 <= size /\ addr + size <= 0x7fff7000).
  Hypothesis Hfsp : 2 ^ 32 + 64 <= U fsp /\ U fsp + 16 <= 2 ^ 47.
  Hypothesis Hstk : store_ok BSEGS M (at_ fsp (-64)) 64 = true.
  Hypothesis Hshw : store_ok BSEGS M (Z_to_bv 64 (0x7fff8000 + addr / 8)) (Z.to_nat (size / 8)) = true.
  Hypothesis Hret : ret_ok ra.

  Lemma phz_lits : 0 <= addr /\ addr + size <= 2 ^ 47 /\ 0 <= size.
  Proof using Hrng. destruct Hrng as [(A1 & A2 & A3 & A4) | (A1 & A2 & A3)]; lia. Qed.

  Lemma mk_poisonH_fa_z : forall thr0,
    rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 1] ->
    poisonH BSEGS both_poison_tab M (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 250) ra fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) thr0.
  Proof using Hret Hshw Hstk Hfsp Hrng Hs8 Ha8 C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sb C_gsb.
    intros thr0 C_cpm. pose proof phz_lits as (L1 & L2 & L3). destruct Hfsp as [F1 F2]. pose proof (u64_range fsp) as Hf.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
    all: [> exact C_gsb | exact C_sb | exact C_gmb | exact C_mb | exact C_gme | exact C_me | exact C_ghe | exact C_he | exact C_grm
          | replace (word_to_le_bytes 8 (1033100 : word)) with (LE8 (Z_to_bv 64 0xfc38c)) by reflexivity; exact C_rm
          | vm_compute; discriminate
          | apply ret_ok_even; reflexivity
          | ..].
    - intros _. split; [exact C_cpm | vm_compute; discriminate].
    - intros E0. exfalso. rewrite u_Z2bv in E0 by lia. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
    - rewrite u_Z2bv by lia. exact Ha8.
    - rewrite u_Z2bv by lia. exact Hs8.
    - rewrite !u_Z2bv by lia. destruct Hrng as [(A1 & A2 & A3 & A4) | (A1 & A2 & A3)]; [left; lia | right; lia].
    - lia.
    - exact Hstk.
    - (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia. replace (addr / 8 + 2147450880) with (0x7fff8000 + addr / 8) by lia. exact Hshw.
    - exact Hret.
  Qed.
End PHZ.
End FPGen.
End BoAllocMSecPh2.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSecRom.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcSN OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Definition romb (z : Z) : bool := match seg_rom BSEGS (Z_to_bv 64 z) with Some _ => true | None => false end.
Fixpoint romb_all (k : nat) (z : Z) : bool := match k with O => true | S k' => andb (romb z) (romb_all k' (z + 1)) end.
Lemma romb_all_ok : forall k z0, romb_all k z0 = true -> forall z, z0 <= z < z0 + Z.of_nat k -> seg_rom BSEGS (Z_to_bv 64 z) <> None.
Proof.
  induction k as [|k IH]; intros z0 Hc z Hz; [cbn [Z.of_nat] in Hz; lia|].
  cbn [romb_all] in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2].
  destruct (Z.eq_dec z z0) as [->|NE].
  - unfold romb in H1. destruct (seg_rom BSEGS (Z_to_bv 64 z0)); [discriminate | discriminate H1].
  - apply (IH (z0 + 1) H2). rewrite Nat2Z.inj_succ in Hz. lia.
Qed.
(* [comment removed for export] *)
Lemma sec_inst_rom : forall z, 0x10ab98 <= z < 0x10ae70 -> seg_rom BSEGS (Z_to_bv 64 z) <> None.
Proof. apply (romb_all_ok 728 0x10ab98). vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma sec_inst_word : forall (m : word -> option byte) (c : Z), 0x10ab98 <= c -> c + 8 <= 0x10ae70 ->
  exists w : word, rdn BSEGS m (Z_to_bv 64 c) 8 = Some (LE8 w).
Proof.
  intros m c H1 H2. destruct (rdn8_ex_img m c) as (bs & Cbs & Lbs); [intros k Hk; apply sec_inst_rom; lia | lia | lia |].
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite Cbs. f_equal. symmetry. exact (le8_word2 bs Lbs).
Qed.
End BoAllocMSecRom.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvXTrk3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcSN OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS BoAllocMSecRom OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKSL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocM9f OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9g OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i.BoAllocM9h OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9z OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocMSumS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS3 BoAllocMRunS4 BoAllocMRunS5 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.BoAllocMSecK OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.BoAllocMSecPh BoAllocMSecPh2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd.BoAllocMSecDefs OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSa OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopSd BoAllocMSecGrow OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKSL.BoAllocFRcGL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcGS OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac ha_prev := first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

From Stdlib Require Import FunctionalExtensionality.

Lemma restrict_mkst_g : forall {fx : FPState} (Hd : word -> bool) (r : bvmap 5 word) pc m rom,
  restrict Hd (@mkst fx r pc m rom) = @mkst fx r pc (mrestrict Hd m) rom.
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma store_ok1_defG : forall (m : mem) (a : word), m a <> None -> store_ok BSEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sec_tail_geo : forall n mb, 64513 <= n <= 2 ^ 34 -> 0 <= mb -> mb mod 4096 = 0 ->
  let size := sec_needed n in let msz := la_msz size in let tb := la_tb size mb in
  tb mod 8 = 0 /\ (mb + msz - tb) mod 8 = 0 /\ mb + 4096 + size - 7 <= tb <= mb + 4096 + size /\ size + 4096 <= msz
  /\ mb / 8 + 512 <= tb / 8 /\ tb / 8 + (mb + msz - tb) / 8 <= (mb + msz) / 8 /\ 0 <= (mb + msz - tb) / 8.
Proof.
  intros n mb Hn Hmb Hal. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). pose proof (sec_needed_bnd n ltac:(lia)) as Hsnb.
  (lazymatch goal with |- ?G => let G' := eval unfold la_msz, la_tb in G in change_no_check G' end). generalize dependent (sec_needed n). intros s Hs. repeat split; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section WithCeil.
Context {RC : run_ceil}.

Section TOPSG.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND KD : Z).
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Hypothesis SCELLS : sec_cells bt.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis BOOTG : boot_geom bt.
  Hypothesis BF : boot_facts bt.
  Hypothesis BTOT : boot_totals bt.
  Hypothesis HTP : TP = ia_tp both_addrs.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HPGP : PGP + 8 <= 0x10ae00 \/ 0x10ae04 <= PGP.                      (* [comment removed for export] *)
  Hypothesis HYP_DEPOT9 : BoDepotTop3.BoDepotHyp9.HYP_DEPOT9_stmt bt FXOK KD.
  (* [comment removed for export] *)
  Hypothesis GROW_DIE :
    forall (fx : FPState) (regs : bvmap 5 word) (M rom : word -> option byte) (sp addr v44 : word),
      FXOK fx -> getr regs 2 = sp -> getr regs 18 = addr ->
      2 ^ 32 + 4096 <= U sp <= 2 ^ 47 - 16 -> U sp mod 16 = 0 -> 4096 <= U addr < 2 ^ 47 ->
      store_ok BSEGS M (at_ sp (-1072)) 1168 = true -> rdn BSEGS M (at_ sp 44) 4 = Some (word_to_le_bytes 4 v44) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1d5) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x612079726f6d656d)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1dd) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x7365726464612074)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1e5) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x70252073)) ->
      rdn BSEGS M (Z_to_bv 64 0x1e1e9) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0)) ->
      rdn BSEGS M (Z_to_bv 64 0x22730) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0x613e0)) ->
      rdn BSEGS M (Z_to_bv 64 0x104a8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xaaaaaaaaaaaaaaaa)) ->
      rdn BSEGS M (Z_to_bv 64 0x105f58) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1)) ->
      rdn BSEGS M (Z_to_bv 64 0x19fcdc) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)) ->
      exists fx' r M', msteps BSEGS (@mkst fx regs (0x82fe8%bv : word) M rom) (@mkst fx' r (0x7ca24%bv : word) M' rom).

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation P8 := (bt_ptrarr bt).

  Theorem sec_granted :
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp n : Z) (st : ast) (h : option Z) (c' : config) (Qok : config -> Prop),
      FXOK fx -> m_halted mdl = None -> BackingAlgebra.model_ivs_wf mdl ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_le h st -> hole_ok h n ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> U (getr R 10) = n -> 64512 < n <= NMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      at_sec_grant bt fx R M mdl Lc FF n st c' ->
      (forall c'', runS_post bt FXOK st Lc FF R M mdl n c'' -> katD BSEGS c'' Qok) ->
      katD BSEGS c' Qok.
  Proof using GROW_DIE HYP_DEPOT9 HPGP G_KD HTP BF SCELLS PCELLS CELLS BT_ia BT_segs KD MIDEND FL PGP TSDP TP.
    intros fx R M mdl Lc FF B C K ret sp n st h c' Qok HFX HH MW W RP BD HLE HO CP HR10 Hn HB HC HK AG CONT.
    pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    destruct AG as (rq & Mq & mdlq & a & AG). cbv zeta in AG.
    destruct AG as (Ec & CC & MIq & DY & AL & AP & APM0 & Q10 & SF & DIFFq & ZEROq & GRq & SEVq). subst c'.
    destruct SF as (x18 & x19 & sz & bsz & SF). cbv zeta in SF.
    destruct SF as (PRL & Q21 & Q4 & Q3 & Q26 & Q27 & FA & FI & FS4 & FS8 & Lsz & SZ1 & FTR & FC & FLA & STKq).
    destruct CC as (LV & LN & LL & LR & LB & LSB & LMB & LIS & LLIM & LEG & LMW & HLq).
    set (S := getr R 2) in *. set (tp := getr R 4) in *.
    pose proof CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S in CP2. fold tp in CP4.
    pose proof BD as ((BP0 & BP1) & BC1 & (BK0 & BK1)).
    assert (Hn1 : 64512 < n) by lia.
    assert (Hn34 : 64513 <= n <= 2 ^ 34) by (unfold GBUDGET, MBLK in HB; lia).
    assert (KC : a_kact st <= KCAP) by (unfold kcost_malloc, EVT in HK; lia).
    set (mb := U a) in *. set (msz := sec_map_size n) in *.
    pose proof (u64_range a) as Har. fold mb in Har.
    assert (MSZ : la_msz (sec_needed n) = msz) by apply la_msz_sec.
    destruct (sec_msz_bnd n Hn1) as [MZ1 MZ2]. fold msz in MZ1, MZ2.
    pose proof (rz_sec n Hn1) as Erz. pose proof (sec_needed_bnd n Hn1) as Hsnb.
    pose proof DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4.
    assert (GA : AIMGHI <= mb) by lia.
    unfold PG in AL.
    (* [comment removed for export] *)
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & _ & SB1).
    rewrite BT_ia in GTI, GCI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI, GCI. unfold PG in GTC, GTI, GTB, TPG.
    assert (GT4 : 4096 <= T) by (clear - GT0 TPG; Z.div_mod_to_equations; lia).
    destruct (fixed_members bt st Lc FF W) as (IN6 & IN8 & _ & INT & _ & _ & INC).
    pose proof (AP _ _ (all_ranges_fixed bt st _ INT)) as APT. pose proof (AP _ _ (all_ranges_fixed bt st _ INC)) as APC.
    pose proof (AP _ _ (all_ranges_fixed bt st _ IN8)) as AP8. unfold PG in APT.
    pose proof W as (_ & _ & _ & (S1' & S2' & S3' & _) & _ & _ & _ & _ & (RNG & _) & _).
    destruct (RNG _ _ (all_ranges_fixed bt st _ IN8)) as ((D81 & D82 & D83 & D84 & D85) & _).
    rewrite BT_ia in D84. cbn [ia_img_lo ia_img_hi both_addrs] in D84.
    assert (GP8 : AIMGHI <= P8) by lia.
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold MSTK_A in CPlo, CPstk, STKq.
    assert (CEILS : CEIL + 3584 <= U S) by (rewrite CP2; lia).
    (* [comment removed for export] *)
    hidehypW Y4. hidehypW Y5. hidehypW GTI. hidehypW GTB. hidehypW GCI. hidehypW GCB. hidehypW APT. hidehypW APC. hidehypW AP8. hidehypW D84. hidehypW D85.
    (* [comment removed for export] *)
    set (naa := sec_naa mb n). set (shs := sec_hull mb n).
    pose proof (sec_shs_bnd mb n ltac:(clear - GA; lia) Hn1) as SH0. fold shs in SH0.
    set (st1 := op_meter st EVT naa 0).                                             (* [comment removed for export] *)
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R14 as (Bw1 & Bw2 & Bw3 & Bw4 & Bw5).
    rewrite BT_segs in *.
    pose proof (sec_pre_budget bt st Lc FF M mdl B C K n mb RP W BD Hn1 HB HK ltac:(clear - GA; lia)) as BUDG. fold msz in BUDG. fold shs in BUDG.
    set (A2 := a_aa st ++ naa).
    assert (AW2 : A_wf A2) by (apply sec_naa_wf; [exact Bw1 | lia | exact Hn1]).
    assert (AB2 : A_bytes A2 = A_bytes (a_aa st) + shs) by ((lazymatch goal with |- ?G => let G' := eval unfold A2, naa, shs in G in change_no_check G' end); rewrite A_bytes_app, sec_naa_bytes; reflexivity).
    assert (Usz : U (Z_to_bv 64 msz) = msz) by (rewrite u_Z2bv by lia; reflexivity).
    assert (MI2 : MInv A2 mdlq) by (apply MInv_snoc; [exact MIq | fold A2; rewrite AB2, LLIM; rewrite Usz in LEG; lia]).
    set (Hd2 := HID st1 mdlq).
    assert (HOFF2 : H_off_segments BSEGS Hd2) by exact (HID_off_segments_l bt st st1 mdl mdlq BT_ia R13 LL).
    assert (LC2 : lazy_cover Hd2 (m_vm_lazy mdlq) A2) by exact (lazy_cover_HID st1 mdlq).
    assert (LZQ : forall z, lzb mdlq z = lzb mdl z) by (intros z; (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite LL; reflexivity).
    assert (NH2 : forall z, 0 <= z < 2 ^ 64 -> lzb mdl z = false -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz L. apply HID_notlazy; [exact Hz | rewrite LZQ; exact L]. }
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply NH2; [exact Hz|]. destruct (lzb mdl z) eqn:E; [| reflexivity]. exfalso.
      destruct (lazy_zone bt st mdl z R13 Hz E) as [Z1 Z2]. rewrite BT_ia in Z2. cbn [ia_img_lo ia_img_hi both_addrs] in Z2. lia. }
    pose proof (free_obls_pf bt) as (OBL_nolazy_rt & _). unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt.
    assert (NHrt : forall z, (T <= z < T + 4096) \/ (CTX <= z < CTX + 0x10000) -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply NH2; [clear - Hz GT0 GTC GC0 GCC CR; lia|]. apply (OBL_nolazy_rt st Lc FF M mdl z W RP). (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end).
      destruct Hz as [Hz|Hz]; [left; exact Hz | right; left; exact Hz]. }
    assert (NHmap : forall z, mb <= z < mb + msz -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply NH2; [lia|]. exact (grant_not_lazy bt st Lc FF M mdl mb msz W RP DY AP z Hz). }
    assert (NHsh : forall z, sh_lo mb <= z < sh_hi mb msz -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. exact (sec_naa_allowed (a_aa st) mb n ltac:(lia) ltac:(fold msz; lia) Hn1 z Hz). }
    assert (NHp8 : forall z, P8 <= z < P8 + 8 * a_nres st -> Hd2 (Z_to_bv 64 z) = false).
    { intros z Hz. apply NH2; [lia|]. exact (rep_nolazy_ptrarr bt st Lc FF M mdl W RP z Hz). }
    (* [comment removed for export] *)
    set (Mr2 := mrestrict Hd2 Mq).
    set (thr := Z_to_bv 64 T : word). set (ctxw := Z_to_bv 64 CTX : word).
    assert (Uthr : U thr = T) by ((lazymatch goal with |- ?G => let G' := eval unfold thr in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Uctx : U ctxw = CTX) by ((lazymatch goal with |- ?G => let G' := eval unfold ctxw in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (EQq : forall x : word, ~ (U S - 2736 <= U x < U S) -> ~ (mb <= U x < mb + msz) -> Mq x = M x).
    { intros x N1 N2. destruct (decide (Mq x = M x)) as [E|NE]; [exact E|]. exfalso. destruct (DIFFq x NE) as [D|D]; [exact (N1 D) | exact (N2 D)]. }
    assert (NHw : forall x : word, Hd2 x = false -> Mr2 x = Mq x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold Mr2 in G in change_no_check G' end); apply mrestrict_off; exact Hx).
    (* [comment removed for export] *)
    assert (KQ : forall (z : Z) (k : nat) v, cellZ BSEGS M z k v -> 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 ->
              (z + Z.of_nat k <= U S - 2736 \/ U S <= z) -> (z + Z.of_nat k <= mb \/ mb + msz <= z) ->
              (forall i, z <= i < z + Z.of_nat k -> Hd2 (Z_to_bv 64 i) = false) ->
              rdn BSEGS Mr2 (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Cz Hz0 Hz1 NS NM NHz. unfold cellZ, cellN in Cz. rewrite <- Cz.
      apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
      rewrite NHw by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHz; lia). apply EQq; lia. }
    assert (KI : forall (z : Z) (k : nat) v, cellZ BSEGS M z k v -> AIMGLO <= z -> z + Z.of_nat k <= AIMGHI ->
              rdn BSEGS Mr2 (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Cz Hz0 Hz1. apply (KQ z k v Cz); [lia | lia | left; lia | left; lia |]. intros i Hi. apply NHs; [lia | right; lia]. }
    assert (KK : forall (z : Z) (k : nat) v, In (z, k, v) (bt_consts bt) -> AIMGLO <= z -> z + Z.of_nat k <= AIMGHI ->
              rdn BSEGS Mr2 (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hin Hz0 Hz1. exact (KI z k v (const_cell bt M _ _ _ R1 Hin) Hz0 Hz1). }
    assert (KT : forall (z : Z) (k : nat) v, cellZ BSEGS M z k v -> ((T <= z /\ z + Z.of_nat k <= T + 4096) \/ (CTX <= z /\ z + Z.of_nat k <= CTX + 0x10000)) ->
              rdn BSEGS Mr2 (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Cz Hr. unfold hideW in APT, APC.
      apply (KQ z k v Cz); [clear - Hr GT0 GC0 GTC GCC CR; lia | clear - Hr GTC GCC CR; lia | left; clear - Hr GTC GCC CEILS; lia | clear - Hr APT APC; lia |].
      intros i Hi. apply NHrt. clear - Hi Hr. lia. }
    pose proof CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx
                      & CELL_rss & CELL_lmag & CELL_tbl2 & CELL_t16 & CELL_t2048 & CELL_minrz & CELL_maxrz & CELL_maxsz & CELL_sbeg
                      & CELL_cpm & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he & CELL_gfl & CELL_pp & CELL_mfs & CELL_fill
                      & CELL_grm & CELL_rm & CELL_glsn & CELL_lsn & CELL_magic & CELL_hook & CELL_thr64 & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9).
    destruct SCELLS as (CELL_ipg & CELL_gnm & CELL_nm & CELL_pa & CELL_pab & CELL_d1 & CELL_d2 & CELL_s1 & CELL_s2 & CELL_s3 & CELL_s4 & CELL_jt & CELL_av).
    destruct R2 as (Inres & Inch & Ilock & _ & _ & _ & _ & Ichunks & Iptrw).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite ?BT_segs in *.
    unfold PG in TW. unfold IB in Inres, Inch, Ilock. rewrite BT_ia in Inres, Inch, Ilock, R17. cbn [ia_instance ia_rtc_sb both_addrs] in Inres, Inch, Ilock, R17.
    set (nch := Z.of_nat (length (a_sec st))) in *. set (nres := a_nres st) in *.
    pose proof W as (_ & _ & _ & (WS1 & WS2 & WS3 & WSrest) & _).
    (* [comment removed for export] *)
    assert (STr : forall x : word, U S - 3584 <= U x < U S -> Mr2 x = Mq x).
    { intros x Hx. apply NHw. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [pose proof (u64_range x); lia | left; lia]. }
    assert (RDr : forall (k : Z) (w : nat) (bs : list byte), -3584 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS Mq (at_ S k) w = Some bs -> rdn BSEGS Mr2 (at_ S k) w = Some bs).
    { intros k w bs K1 K2 Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]|]. intros x Hx. rewrite at_u in Hx by lia. apply STr. lia. }
    assert (SOKstk : forall (k : Z) (w : nat), -3584 <= k -> k + Z.of_nat w <= 0 -> store_ok BSEGS Mr2 (at_ S k) w = true).
    { intros k w K1 K2. apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. intros x Hx. rewrite at_u in Hx by lia.
      (lazymatch goal with |- ?G => let G' := eval unfold Mr2 in G in change_no_check G' end). rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); pose proof (u64_range x); lia | intros y Hy; cbn in Hy; assert (y = x) by (apply bv_eq; lia); subst y;
        rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHs; [pose proof (u64_range x); lia | left; lia]].
      exact (proj2 (STKq x ltac:(lia))). }
    (* [comment removed for export] *)
    assert (K_gsb : rdn BSEGS Mr2 (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8))) by exact (KK _ _ _ CELL_gsh ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_sb : rdn BSEGS Mr2 (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))) by (unfold SB in R17; exact (KI _ _ _ R17 ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))).
    assert (K_gmb : rdn BSEGS Mr2 (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8))) by exact (KK _ _ _ CELL_gmb ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_mb : rdn BSEGS Mr2 (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0))) by exact (KK _ _ _ CELL_mb ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_gme : rdn BSEGS Mr2 (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0))) by exact (KK _ _ _ CELL_gme ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_me : rdn BSEGS Mr2 (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by exact (KK _ _ _ CELL_me ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_ghe : rdn BSEGS Mr2 (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0))) by exact (KK _ _ _ CELL_ghe ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_he : rdn BSEGS Mr2 (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by exact (KK _ _ _ CELL_he ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_grm : rdn BSEGS Mr2 (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58))) by exact (KK _ _ _ CELL_grm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_rm : rdn BSEGS Mr2 (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c))) by exact (KK _ _ _ CELL_rm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_cpm : rdn BSEGS Mr2 (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 1]) by (rewrite <- (w2b1 1) by lia; exact (KK _ _ _ CELL_cpm ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))).
    assert (K_ipg : rdn BSEGS Mr2 (Z_to_bv 64 (0x10ab58 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096))) by exact (KK _ _ _ CELL_ipg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_pa : rdn BSEGS Mr2 (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 P8))) by exact (KK _ _ _ CELL_pa ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_pab : rdn BSEGS Mr2 (Z_to_bv 64 (0x10ab58 + 80)) 8 = Some (LE8 (Z_to_bv 64 P8))) by exact (KK _ _ _ CELL_pab ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_kif : rdn BSEGS Mr2 (Z_to_bv 64 0x10da20) 1 = Some [Z_to_bv 8 1]) by (rewrite <- (w2b1 1) by lia; exact (KK _ _ _ CELL_kif ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))).
    assert (K_key : rdn BSEGS Mr2 (Z_to_bv 64 0x10da24) 4 = Some (LE4 0)) by exact (KK _ _ _ CELL_key ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_tsdp : rdn BSEGS Mr2 (Z_to_bv 64 (TP - 88)) 8 = Some (LE8 (Z_to_bv 64 TSDP))) by exact (KK _ _ _ CELL_tsdp ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_tctx : rdn BSEGS Mr2 (Z_to_bv 64 TSDP) 8 = Some (LE8 ctxw)) by exact (KK _ _ _ CELL_tctx ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    (* [comment removed for export] *)
    assert (K_nres : rdn BSEGS Mr2 (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres))) by exact (KI _ _ _ Inres ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_nch : rdn BSEGS Mr2 (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch))) by exact (KI _ _ _ Inch ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (K_lk0 : rdn BSEGS Mr2 (Z_to_bv 64 0x10ae00) 1 = Some [Z_to_bv 8 0]).
    { unfold byteZ in Ilock. rewrite <- (w2b1 0) by lia. exact (KI _ _ _ Ilock ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). }
    destruct (rdn1_ex_10ae41 Mr2) as [k1 Hk1]. destruct (rdn1_ex_10ae42 Mr2) as [k2 Hk2]. destruct (rdn1_ex_10ae43 Mr2) as [k3 Hk3].
    assert (K_lock : rdn BSEGS Mr2 (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; k1; k2; k3]).
    { apply BoAllocFRcKS.rdn4_of_bytesS; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | exact K_lk0 | | | ].
      - replace (at_ (Z_to_bv 64 0x10ae00) 1) with (Z_to_bv 64 0x10ae01 : word) by (apply bv_eq; reflexivity). exact Hk1.
      - replace (at_ (Z_to_bv 64 0x10ae00) 2) with (Z_to_bv 64 0x10ae02 : word) by (apply bv_eq; reflexivity). exact Hk2.
      - replace (at_ (Z_to_bv 64 0x10ae00) 3) with (Z_to_bv 64 0x10ae03 : word) by (apply bv_eq; reflexivity). exact Hk3. }
    set (lkb := [Z_to_bv 8 0; k1; k2; k3]) in *.
    pose proof (bytes_le_to_Z_bound lkb) as Blk. cbn [length lkb] in Blk. pose proof (bytes_le_to_Z_nonneg lkb) as Blk0.
    assert (V_lock : bytes_le_to_Z lkb = U (Z_to_bv 64 (bytes_le_to_Z lkb))) by (rewrite u_Z2bv by (clear - Blk Blk0; lia); reflexivity).
    destruct (sec_inst_word Mr2 0x10abe0 ltac:(lia) ltac:(lia)) as [naw K_na].
    destruct (sec_inst_word Mr2 0x10abf0 ltac:(lia) ltac:(lia)) as [curw K_cur].
    destruct (sec_inst_word Mr2 0x10abf8 ltac:(lia) ltac:(lia)) as [mxw K_mx].
    destruct (sec_inst_word Mr2 0x10ae18 ltac:(lia) ltac:(lia)) as [w16 K_16].
    destruct (sec_inst_word Mr2 0x10ae20 ltac:(lia) ltac:(lia)) as [w24 K_24].
    assert (CZ : exists cz, U (AsAllocM9z.swar_clz (Z_to_bv 64 (la_msz (sec_needed n)))) = cz /\ 0 <= cz <= 63).
    { exists (U (AsAllocM9z.swar_clz (Z_to_bv 64 (la_msz (sec_needed n))))). split; [reflexivity|]. apply AsAllocM9z.swar_clz_bound. rewrite MSZ, Usz. lia. }
    destruct CZ as (cz & CZ1 & CZ2).
    destruct (sec_inst_word Mr2 (0x10ac00 + 8 * (63 - cz)) ltac:(lia) ltac:(lia)) as [blw K_bl].
    (* [comment removed for export] *)
    assert (K_T0 : rdn BSEGS Mr2 thr 8 = Some (LE8 ctxw)) by (exact (KT _ _ _ Tctx ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia))).
    assert (K_thr : rdn BSEGS Mr2 (at_ ctxw 152) 8 = Some (LE8 thr)).
    { replace (at_ ctxw 152) with (Z_to_bv 64 (CTX + 152)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Uctx; rewrite !u_Z2bv by lia; reflexivity).
      exact (KT _ _ _ Tback ltac:(right; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). }
    assert (K_tid : rdn BSEGS Mr2 (at_ ctxw 8) 4 = Some (LE4 0)).
    { replace (at_ ctxw 8) with (Z_to_bv 64 (CTX + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Uctx; rewrite !u_Z2bv by lia; reflexivity).
      exact (KT _ _ _ Ttid ltac:(right; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). }
    assert (TDEF : forall z, T <= z < T + 4096 -> Mr2 (Z_to_bv 64 z) <> None).
    { intros z Hz. rewrite NHw by (apply NHrt; left; exact Hz). apply GRq. exact (writableZ_def M _ _ _ TW Hz). }
    destruct (rdn_defined_ex BSEGS Mr2 (at_ thr 2872) 8) as (b72 & C72 & L72);
      [intros z Hz; rewrite at_u in Hz by (rewrite Uthr; lia); rewrite Uthr in Hz; cbn in Hz; apply TDEF; lia | rewrite at_u by (rewrite Uthr; lia); rewrite Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
    destruct (rdn_defined_ex BSEGS Mr2 (at_ thr 2880) 8) as (b80 & C80 & L80);
      [intros z Hz; rewrite at_u in Hz by (rewrite Uthr; lia); rewrite Uthr in Hz; cbn in Hz; apply TDEF; lia | rewrite at_u by (rewrite Uthr; lia); rewrite Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |].
    rewrite <- (le8_word2 b72 L72) in C72. rewrite <- (le8_word2 b80 L80) in C80.
    (* [comment removed for export] *)
    assert (SOK_T : store_ok BSEGS Mr2 thr 4096 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr2 in G in change_no_check G' end). rewrite store_ok_mrestrict; [| rewrite Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite Uthr; apply hid_off_of; intros z Hz; split; [lia | apply NHrt; left; cbn in Hz; lia]].
      eapply store_ok_mono; [exact GRq|]. apply (writableZ_store_ok M _ _ _ _ TW); rewrite ?Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (SOK_lk : store_ok BSEGS Mr2 (Z_to_bv 64 0x10ae00) 4 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (SOK_inst : store_ok BSEGS Mr2 (Z_to_bv 64 0x10ab98) 728 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (SOK_nres : store_ok BSEGS Mr2 (Z_to_bv 64 (0x10ab58 + 112)) 8 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (MAPOK : forall (lo : Z) (w : nat), mb <= lo -> lo + Z.of_nat w <= mb + msz -> store_ok BSEGS Mr2 (Z_to_bv 64 lo) w = true).
    { intros lo w L1 L2. apply store_ok_bytes; [| first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]]. intros x Hx. rewrite u_Z2bv in Hx by lia.
      apply store_ok1_defG. rewrite NHw by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHmap; lia). rewrite ZEROq by lia. discriminate. }
    (* [comment removed for export] *)
    destruct (sec_geo mb n Hn1 ltac:(lia) ltac:(lia) AL ltac:(fold msz; lia)) as (EOFF & GMSZ & GMSZ4 & GQ1 & GQ2 & GQ3 & GQ4 & GQ5 & GQ6 & GQ7).
    fold msz in GMSZ, GMSZ4, GQ3, GQ4, GQ6, GQ7.
    destruct (sec_tail_geo n mb Hn34 ltac:(lia) AL) as (TG1 & TG2 & TG3 & TG4 & TG5 & TG6 & TG7). rewrite MSZ in TG2, TG4, TG6, TG7.
    set (tb := la_tb (sec_needed n) mb) in *.
    set (q := mb / 8) in *. set (e := (mb + msz) / 8) in *. set (qt := tb / 8) in *. set (qs := (mb + msz - tb) / 8) in *.
    assert (SHM : forall z, 2147450880 + q <= z < 2147450880 + e -> shmaps z).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_LO, AS_GAPLO, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). unfold hideW in Y5. unfold AS_LO, AS_HEAPLO in Y5. destruct Y5 as [Y|Y].
      - left. assert (e <= 268430848) by ((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); apply Z.div_le_upper_bound; [lia | clear - Y; lia]). clear - Hz H GQ5. lia.
      - right. assert (2199291686912 <= q) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); apply Z.div_le_lower_bound; [lia | clear - Y; lia]). clear - Hz H GQ6. lia. }
    assert (SHDEF : forall x : word, 2147450880 + q <= U x < 2147450880 + e -> Mr2 x <> None).
    { intros x Hx. pose proof (u64_range x) as Hxr.
      rewrite NHw by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHsh; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end); fold q; rewrite GQ7; fold e; exact Hx).
      rewrite EQq; [| clear - Hx GQ6 CEILS CR; lia | unfold hideW in Y5; unfold AS_LO, AS_HEAPLO in Y5; clear - Hx Y5 GQ5 GQ6 GMSZ Hn1; lia].
      destruct R18 as (_ & SHD & _). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply SHD. apply SHM. exact Hx. }
    assert (SHW : forall (lo : Z) (w : nat), 2147450880 + q <= lo -> lo + Z.of_nat w <= 2147450880 + e -> store_ok BSEGS Mr2 (Z_to_bv 64 lo) w = true).
    { intros lo w L1 L2. apply store_ok_bytes; [| rewrite u_Z2bv by (clear - L1 L2 GQ5 GQ6; lia); clear - L1 L2 GQ5 GQ6; lia].
      intros x Hx. rewrite u_Z2bv in Hx by (clear - L1 L2 GQ5 GQ6; lia). apply store_ok1_defG. apply SHDEF. clear - Hx L1 L2. lia. }
    set (fsp := at_ (at_ S (-2320)) (-96)).
    assert (Ufsp : U fsp = U S - 2416) by ((lazymatch goal with |- ?G => let G' := eval unfold fsp in G in change_no_check G' end); rewrite at_at, at_u by (clear - CEILS HSr CR; lia); clear; lia).
    assert (PH1 : poisonH BSEGS both_poison_tab Mr2 (Z_to_bv 64 mb) (Z_to_bv 64 4096) (Z_to_bv 64 250) (Z_to_bv 64 0x510d8) fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0).
    { apply (mk_poisonH_fa_z Mr2 MIDEND K_gsb K_sb K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm mb 4096 (Z_to_bv 64 0x510d8) fsp); [ | | | | | | | exact K_cpm].
      - clear - AL. Z.div_mod_to_equations. lia.
      - reflexivity.
      - unfold hideW in Y5. unfold AS_LO, AS_HEAPLO in Y5. clear - Y5 Y3 CEILS HSr GMSZ Hn1 GA CPhi CP2. destruct Y5 as [Y|Y]; [right | left]; lia.
      - rewrite Ufsp. clear - CEILS CR CPhi CP2. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold fsp in G in change_no_check G' end). rewrite !at_at. apply SOKstk; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - change (4096 / 8) with 512. fold q. apply SHW; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GQ4 GMSZ4 GMSZ Hn1 TG5 TG6 TG7; lia].
      - apply ret_ok_lit; [lia | reflexivity]. }
    assert (PH2 : poisonH BSEGS both_poison_tab Mr2 (Z_to_bv 64 tb) (Z_to_bv 64 (mb + msz - tb)) (Z_to_bv 64 250) (Z_to_bv 64 0x510e8) fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0).
    { apply (mk_poisonH_fa_z Mr2 MIDEND K_gsb K_sb K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm tb (mb + msz - tb) (Z_to_bv 64 0x510e8) fsp); [ | | | | | | | exact K_cpm].
      - exact TG1.
      - exact TG2.
      - unfold hideW in Y5. unfold AS_LO, AS_HEAPLO in Y5. clear - Y5 Y3 CEILS HSr TG3 TG4 Hsnb GA CPhi CP2 Hn1. destruct Y5 as [Y|Y]; [right | left]; lia.
      - rewrite Ufsp. clear - CEILS CR CPhi CP2. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold fsp in G in change_no_check G' end). rewrite !at_at. apply SOKstk; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - fold qt qs. apply SHW; [clear - TG5; lia | rewrite Z2Nat.id by exact TG7; clear - TG6; lia].
      - apply ret_ok_lit; [lia | reflexivity]. }
    assert (Utp : U tp = TP) by (rewrite CP4, HTP; rewrite u_Z2bv by (rewrite <- HTP; clear - Gc8 Gc9; lia); reflexivity).
    assert (GH : gctH BSEGS both_gct_tab Mr2 (at_ fsp (-16)) tp (Z_to_bv 64 TSDP) ctxw thr).
    { assert (Ugsp : U (at_ fsp (-16)) = U S - 2432) by (rewrite at_u by (rewrite Ufsp; clear - CEILS HSr CR; lia); rewrite Ufsp; clear; lia).
      split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end).
      - exact K_kif.
      - replace (at_ (Z_to_bv 64 0x10da20) 4) with (Z_to_bv 64 0x10da24 : word) by (apply bv_eq; reflexivity). exact K_key.
      - replace (at_ tp (-88)) with (Z_to_bv 64 (TP - 88)) by (apply bv_eq; rewrite at_u by (rewrite Utp; clear - Gc8 Gc9; lia); rewrite Utp, u_Z2bv by (clear - Gc8 Gc9; lia); reflexivity).
        exact K_tsdp.
      - exact K_tctx.
      - exact K_thr.
      - rewrite Uctx. clear - GC0. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold fsp in G in change_no_check G' end). rewrite !at_at. apply SOKstk; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite Ugsp. clear - CEILS HSr CR. lia.
      - rewrite Ugsp, u_Z2bv by lia. clear - CEILS CR. lia.
      - rewrite Ugsp, Utp. clear - Gc8 Gc9 CEILS CR. lia.
      - rewrite Ugsp, u_Z2bv by (clear - Gc1 Gc2; lia). clear - Gc2 CEILS CR. lia.
      - rewrite Ugsp, Uctx. clear - GCC CEILS. lia. }
    (* [comment removed for export] *)
    assert (IMGLO' : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
    pose proof (ptrarr_geom bt st Lc FF W IMGLO') as (PA1 & PA2 & PA3 & PA4 & PA5 & PA6 & PA7 & PA8). unfold PG in PA6.
    hidehypW PA4. hidehypW PA5. hidehypW PA6. hidehypW PA7.
    pose proof (sec_len_le bt st Lc FF (2 ^ 20) (2 ^ 28) W ltac:(lia)) as SLEN. fold nch in SLEN. unfold LMAX in SLEN.
    replace QSECCNT with 4193 in SLEN by reflexivity.
    assert (NCH0 : 0 <= nch) by ((lazymatch goal with |- ?G => let G' := eval unfold nch in G in change_no_check G' end); lia).
    assert (H10q : getr rq 10 = Z_to_bv 64 mb) by (rewrite Q10; (lazymatch goal with |- ?G => let G' := eval unfold mb in G in change_no_check G' end); symmetry; apply Z_to_bv_bv_unsigned).
    assert (GSq : 2 ^ 32 + 8192 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - CEILS CR CPhi CP2; lia).
    assert (Hmbq : AIMGHI <= mb /\ mb + la_msz (sec_needed n) <= 2 ^ 47 /\ mb mod 4096 = 0) by (rewrite MSZ; clear - GA Y3 CR AL; lia).
    assert (Hmbspq : mb + la_msz (sec_needed n) <= U S - 3584 \/ U S <= mb) by (left; rewrite MSZ; clear - Y3 CEILS; lia).
    assert (Hmbbandq : mb + la_msz (sec_needed n) <= AS_LO \/ AS_HEAPLO <= mb) by (rewrite MSZ; unfold hideW in Y5; exact Y5).
    assert (GTq : 4096 <= U thr /\ U thr + 4096 <= U S - 3584 /\ U thr mod 8 = 0).
    { rewrite Uthr. split; [exact GT4|]. split; [clear - GTC CEILS; lia | clear - TPG; Z.div_mod_to_equations; lia]. }
    assert (GTimgq : U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr) by (rewrite Uthr; unfold hideW in GTI; exact GTI).
    assert (GTbandq : U thr + 4096 <= AS_LO \/ AS_HEAPLO <= U thr) by (rewrite Uthr; unfold hideW in GTB; exact GTB).
    assert (GTmbq : U thr + 4096 <= mb \/ mb + la_msz (sec_needed n) <= U thr) by (rewrite Uthr, MSZ; unfold hideW in APT; clear - APT; lia).
    assert (Hnchq : 0 <= nch < 2 ^ 20 /\ 0 <= nres < 2 ^ 64) by (clear - SLEN NCH0 WS3; (lazymatch goal with |- ?G => let G' := eval unfold nres in G in change_no_check G' end); lia).
    assert (Hclzq : U (AsAllocM9z.swar_clz (Z_to_bv 64 (la_msz (sec_needed n)))) = cz /\ 0 <= cz <= 63) by (split; [exact CZ1 | exact CZ2]).
    assert (GHoffq : (AIMGLO <= U (gt_tsd both_gct_tab) /\ U (gt_tsd both_gct_tab) + 8 <= AIMGHI) /\ (AIMGLO + 88 <= U tp /\ U tp <= AIMGHI)
                     /\ (AIMGLO <= U (Z_to_bv 64 TSDP : word) /\ U (Z_to_bv 64 TSDP : word) + 8 <= AIMGHI)
                     /\ (U ctxw + 160 <= U S - 3584 /\ (U ctxw + 160 <= AS_LO \/ AS_HEAPLO <= U ctxw) /\ 0 <= U ctxw)).
    { (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd both_gct_tab] in G in change_no_check G' end). rewrite Utp, Uctx. rewrite !u_Z2bv by (clear - Gc1 Gc2; lia).
      split; [lia|]. split; [clear - Gc8 Gc9; lia|]. split; [clear - Gc1 Gc2; lia|].
      split; [clear - GCC CEILS; lia|]. split; [unfold hideW in GCB; clear - GCB; lia | clear - GC0; lia]. }
    assert (SOK_gq : store_ok BSEGS Mr2 (at_ fsp (-8)) 8 = true) by ((lazymatch goal with |- ?G => let G' := eval unfold fsp in G in change_no_check G' end); rewrite !at_at; apply SOKstk; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]).
    assert (GSbandq : AS_HEAPLO <= U S - 3584) by ((lazymatch goal with |- ?G => let G' := eval unfold AS_HEAPLO in G in change_no_check G' end); clear - CEILS CR; lia).
    assert (GctxTq : U ctxw + 4096 <= U thr \/ U thr + 4096 <= U ctxw).
    { rewrite Uctx, Uthr.
      assert (NE1 : (T, T + PG) <> (CTX, CTX + 0x10000)) by (intros E; injection E; intros E1 E2; unfold PG in E1; clear - E1 E2; lia).
      pose proof (ar_disj_ne bt st Lc FF _ _ W (all_ranges_fixed bt st _ INT) (all_ranges_fixed bt st _ INC) NE1) as DT. hnf in DT. cbn in DT. unfold PG in DT. clear - DT. lia. }
    assert (HPAq : AIMGHI <= P8 /\ P8 + 2 ^ 23 < 2 ^ 63) by (clear - GP8 PA2 CR; lia).
    assert (HPAmbq : P8 + 2 ^ 23 <= mb \/ mb + la_msz (sec_needed n) <= P8) by (rewrite MSZ; unfold hideW in AP8; clear - AP8; lia).
    assert (HPAspq : P8 + 2 ^ 23 <= U S - 3584 \/ U S <= P8) by (left; clear - PA2 CEILS; lia).
    assert (GTPAq : U thr + 4096 <= P8 \/ P8 + 2 ^ 23 <= U thr) by (rewrite Uthr; unfold hideW in PA6; clear - PA6; lia).
    assert (Gctxq : 1 <= U ctxw /\ U ctxw + 4096 <= U S - 3584 /\ (U ctxw + 4096 <= AIMGLO \/ AIMGHI <= U ctxw)).
    { rewrite Uctx. split; [clear - GC0; lia|]. split; [clear - GCC CEILS; lia | unfold hideW in GCI; clear - GCI; lia]. }
    assert (Gctxmbq : U ctxw + 4096 <= mb \/ mb + la_msz (sec_needed n) <= U ctxw) by (rewrite Uctx, MSZ; unfold hideW in APC; clear - APC; lia).
    assert (GctxPAq : U ctxw + 4096 <= P8 \/ P8 + 2 ^ 23 <= U ctxw) by (rewrite Uctx; unfold hideW in PA7; clear - PA7; lia).
    assert (FLAq : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
                         (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)] ->
              rdn BSEGS Mr2 (at_ (at_ S (-2320)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [clear - Ho; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Ho; lia |]. rewrite <- at_at. exact (FLA o v Hin). }
    assert (FCq : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)] ->
              rdn BSEGS Mr2 (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite at_at. apply RDr; [clear - Ho; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Ho; lia |]. rewrite <- at_at. exact (FC o v Hin). }
    assert (Erzn : rz n = 2048) by exact Erz.
    assert (MBR : 0 <= mb /\ 0 <= n /\ mb + 8192 + n < 2 ^ 47) by (clear - GA Y3 CR GMSZ Hn1; lia).
    assert (Rb1q : rdn BSEGS Mr2 (at_ (Z_to_bv 64 (mb + 4096)) (rz n - 15)) 1 = Some [Z_to_bv 8 0]).
    { rewrite Erzn. assert (UA : U (at_ (Z_to_bv 64 (mb + 4096)) (2048 - 15)) = mb + 6129) by (rewrite at_u by (rewrite u_Z2bv by (clear - MBR; lia); clear - MBR; lia); rewrite u_Z2bv by (clear - MBR; lia); clear; lia).
      apply heap_rdn1; [rewrite UA; clear - GA; lia|].
      rewrite NHw by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)); rewrite UA; apply NHmap; clear - GMSZ Hn1; lia).
      apply ZEROq. rewrite UA. fold mb msz. clear - GMSZ Hn1. lia. }
    assert (SOKhq : store_ok BSEGS Mr2 (at_ (Z_to_bv 64 (mb + 4096)) (rz n - 16)) 16 = true).
    { rewrite Erzn. replace (at_ (Z_to_bv 64 (mb + 4096)) (2048 - 16)) with (Z_to_bv 64 (mb + 6128) : word)
        by (apply bv_eq; rewrite at_u by (rewrite u_Z2bv by (clear - MBR; lia); clear - MBR; lia); rewrite !u_Z2bv by (clear - MBR; lia); clear; lia).
      apply MAPOK; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GMSZ Hn1; lia]. }
    assert (R16q : rdn BSEGS Mr2 (at_ (at_ S (-2272)) 16) 8 = Some (LE8 (Z_to_bv 64 16))).
    { rewrite at_at. apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia |]. apply (FA (-2272 + 16) (Z_to_bv 64 16)). (lazymatch goal with |- ?G => let G' := eval unfold ma_slotsA in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). auto 20. }
    assert (Rtrq : rdn BSEGS Mr2 (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))) by (apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FTR]).
    assert (Rszq : rdn BSEGS Mr2 (at_ (at_ S (-2128)) 8) 8 = Some bsz) by (rewrite at_at; apply RDr; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact FS8]).
    assert (Hszq : bytes_le_to_Z bsz = U (Z_to_bv 64 sz : word) /\ length bsz = 8%nat).
    { split; [| exact Lsz]. rewrite u_Z2bv by (clear - SZ1; lia). exact (proj2 SZ1). }
    assert (SOK_hq : store_ok BSEGS Mr2 (Z_to_bv 64 mb) 32 = true) by (apply MAPOK; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GMSZ Hn1; lia]).
    (* [comment removed for export] *)
    destruct (ledger_R bt st Lc FF M mdl RP) as (_ & _ & _ & LOK & _ & _ & _ & _ & _ & _ & _ & NPOS).
    assert (EQ20 : at_ (Z_to_bv 64 (mb + 4096)) (rz n) = Z_to_bv 64 (mb + sec_user_off n)).
    { rewrite EOFF, Erzn. apply bv_eq. rewrite at_u by (rewrite u_Z2bv by (clear - MBR; lia); clear - MBR; lia). rewrite !u_Z2bv by (clear - MBR; lia). clear. lia. }
    assert (EQ21 : at_ (Z_to_bv 64 (mb + 4096)) (rz n - 16) = Z_to_bv 64 (mb + sec_user_off n - 16)).
    { rewrite EOFF, Erzn. apply bv_eq. rewrite at_u by (rewrite u_Z2bv by (clear - MBR; lia); clear - MBR; lia). rewrite !u_Z2bv by (clear - MBR; lia). clear. lia. }
    assert (EQ25 : at_ (Z_to_bv 64 (mb + 4096)) (rz n + n) = Z_to_bv 64 (mb + sec_user_off n + n)).
    { rewrite EOFF, Erzn. apply bv_eq. rewrite at_u by (rewrite u_Z2bv by (clear - MBR; lia); clear - MBR; lia). rewrite !u_Z2bv by (clear - MBR; lia). clear. lia. }
    assert (Usz8 : U (Z_to_bv 64 sz : word) = sz) by (rewrite u_Z2bv by (clear - SZ1; lia); reflexivity).
    assert (Wng_dec : forall PAx nchx, Wdec (W_ng S thr n mb nchx PAx)).
    { intros PAx nchx z. (lazymatch goal with |- ?G => let G' := eval unfold W_ng, W_seca, W_sec1, W_sec2, W_sect, W_sect2 in G in change_no_check G' end).
      repeat first [apply or_decT | apply ivl_decT]. }
    destruct (Z.eq_dec nch nres) as [EQN | NEQ]; cycle 1.
    { (* [comment removed for export] *)
      destruct (@sec_run_ng fx Mr2 (seg_rom BSEGS) rq S thr tp (getr R 3) (Z_to_bv 64 TSDP) ctxw (Z_to_bv 64 MIDEND)
                  (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (bytes_le_to_Z lkb)) (at_ S (-2112)) (Z_to_bv 64 sz)
                  naw curw mxw blw w16 w24 (Z_to_bv 8 1) k1 k2 k3 (Z_to_bv 8 0) bsz n mb 0 nch nres cz P8 0
                  PRL H10q Q21 Q4 Q3 GSq Hn34 Hmbq Hmbspq Hmbbandq GTq GTimgq GTbandq GTmbq Hnchq Hclzq
                  PH1 ltac:(rewrite MSZ; exact PH2) GH GHoffq SOK_gq K_ipg C72 C80 K_lock V_lock SOK_T SOK_hq SOK_lk K_nch K_nres NEQ
                  GSbandq GctxTq Q26 Q27 ltac:(lia) HPAq HPAmbq HPAspq GTPAq Gctxq Gctxmbq GctxPAq K_pa K_na K_cur K_mx K_bl K_16 K_24)
        as (r & RUN & E1 & E2 & E10 & E11 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E4 & E3 & E26 & E27).
      { (* [comment removed for export] *)
        apply store_ok_bytes; [| rewrite u_Z2bv by (clear - GP8 PA2 CR NCH0 SLEN; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GP8 PA2 CR NCH0 SLEN; lia].
        intros x Hx. rewrite u_Z2bv in Hx by (clear - GP8 PA2 CR NCH0 SLEN; lia). cbn in Hx. apply store_ok1_defG.
        assert (INP : P8 <= U x < P8 + 8 * nres) by (clear - Hx NEQ WS1 NCH0; fold nch nres in WS1; lia).
        rewrite NHw by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHp8; exact INP).
        rewrite EQq; [| clear - INP PA2 CEILS WS3; unfold nres in INP; lia | unfold hideW in AP8; clear - INP AP8 WS3; unfold nres in INP; lia].
        rewrite <- (Z_to_bv_bv_unsigned 64 x). exact (proj1 (Iptrw (U x) INP)). }
      { exact SOK_inst. } { exact FLAq. } { exact FCq. } { exact Rb1q. } { exact SOKhq. } { exact R16q. } { exact K_T0. } { exact K_tid. }
      { exact Rtrq. } { exact Rszq. } { exact Hszq. }
      set (MC := ng_mem Mr2 S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) naw curw mxw blw w16 w24 k1 k2 k3 (Z_to_bv 8 0) n mb nch cz P8) in *.
      apply (katD_msteps_acct BSEGS Hd2 HOFF2 asanF_segs_wx A2
               (@mkst fx rq (Z_to_bv 64 0x51080) Mq (seg_rom BSEGS)) (@mkst fx r (Z_to_bv 64 0x8f4f0) MC (seg_rom BSEGS)) mdlq).
      { exact LC2. } { exact AW2. } { exact MI2. } { exact HLq. }
      { rewrite restrict_mkst_g. replace (Z_to_bv 64 0x51080 : word) with (331904%bv : word) by (apply bv_eq; reflexivity). exact RUN. }
      intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
      replace (ms_mem (@mkst fx rq (Z_to_bv 64 0x51080) Mq (seg_rom BSEGS))) with Mq by reflexivity.
      pose proof (same_but_materialized_frame mdlq mdl1 SBM1) as SF1.
      destruct SF1 as (_ & Evm & Elz & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl & _ & _ & _ & Eeg).
      set (MD := munrestrict Hd2 Mq MC).
      pose proof (ng_mem_sum Mr2 (seg_rom BSEGS) S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (bytes_le_to_Z lkb)) (Z_to_bv 64 sz)
                    naw curw mxw blw w16 w24 k1 k2 k3 (Z_to_bv 8 0) bsz n mb nch nres cz P8 0 GSq Hn34 Hmbq GTq Hnchq Hclzq ltac:(lia) HPAq Hszq) as SUMr.
      fold MC in SUMr.
      (* [comment removed for export] *)
      assert (WVIS : forall x : word, W_ng S thr n mb nch P8 (U x) -> Hd2 x = false).
      { intros x Hw. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x).
        unfold W_ng, W_seca, W_sec1, W_sec2, W_sect, W_sect2 in Hw. rewrite MSZ, Uthr in Hw.
        destruct Hw as [[[F|F]|[F|[F|F]]]|[[F|[F|F]]|F]].
        - apply NHs; [exact Hxr | left; clear - F CEILS; lia].
        - apply NHsh. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end). fold q. rewrite GQ7. fold e. unfold SB in *. fold q e in F. exact F.
        - apply NHrt. left. clear - F. lia.
        - apply NHmap. clear - F GMSZ Hn1. lia.
        - apply NHs; [exact Hxr | right; clear - F; lia].
        - apply NHmap. clear - F GMSZ Hn1. lia.
        - apply NHp8. clear - F NEQ WS1 NCH0. fold nch nres in WS1. lia.
        - apply NHs; [exact Hxr | right; clear - F; lia].
        - apply NHmap. clear - F GMSZ Hn1. lia. }
      pose proof (msum_unrestrict Hd2 _ Mq MC WVIS SUMr) as SUMD. fold MD in SUMD.
      assert (WFOOT : forall z, W_ng S thr n mb nch P8 z -> sec_footA (U S) T mb msz P8 nch nres false z).
      { intros z Hw. unfold W_ng, W_seca, W_sec1, W_sec2, W_sect, W_sect2 in Hw. rewrite MSZ, Uthr in Hw. (lazymatch goal with |- ?G => let G' := eval unfold sec_footA in G in change_no_check G' end).
        destruct Hw as [[[F|F]|[F|[F|F]]]|[[F|[F|F]]|F]].
        - left. clear - F. lia.
        - right; right; left. exact F.
        - do 6 right. clear - F. lia.
        - right; left. clear - F GMSZ Hn1. lia.
        - do 3 right; left. clear - F. lia.
        - right; left. clear - F GMSZ Hn1. lia.
        - do 4 right; left. exact F.
        - do 3 right; left. clear - F. lia.
        - right; left. clear - F GMSZ Hn1. lia. }
      assert (FOOTD : forall x : word, MD x <> M x -> sec_footA (U S) T mb msz P8 nch nres false (U x)).
      { intros x NE. destruct (decide (MD x = Mq x)) as [E|N].
        - rewrite E in NE. destruct (DIFFq x NE) as [D|D]; [left; clear - D; lia | right; left; exact D].
        - apply WFOOT. exact (proj1 (msum_changed _ Mq MD (Wng_dec P8 nch) SUMD x N)). }
      assert (GRD : mem_grows M MD) by (eapply mem_grows_trans; [exact GRq | exact (proj2 SUMD)]).
      assert (RDV : forall (z : Z) (k : nat) bs, 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd2 (Z_to_bv 64 i) = false) ->
                rdn BSEGS MC (Z_to_bv 64 z) k = Some bs -> rdn BSEGS MD (Z_to_bv 64 z) k = Some bs).
      { intros z k bs Hz0 Hz1 Hv Hr. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end). rewrite (rdn_munrestrict BSEGS Hd2 Mq MC _ k); [exact Hr | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] |].
        intros x Hx. rewrite u_Z2bv in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hv. exact Hx. }
      assert (RDQ : forall (z : Z) (k : nat) bs, 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ W_ng S thr n mb nch P8 i) ->
                rdn BSEGS Mq (Z_to_bv 64 z) k = Some bs -> rdn BSEGS MD (Z_to_bv 64 z) k = Some bs).
      { intros z k bs Hz0 Hz1 Hoff Hr. apply (msum_rdn_eq BSEGS _ Mq MD _ k bs SUMD); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hoff | exact Hr]. }
      set (MH := sh_mem Mr2 S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) k1 k2 k3 n mb).
      assert (EMC : MC = st_mem MH naw curw mxw blw w16 w24 (Z_to_bv 8 0) n mb nch P8 cz) by reflexivity.
      pose proof (st_mem_sum MH (seg_rom BSEGS) (Z_to_bv 64 sz) naw curw mxw blw w16 w24 bsz (Z_to_bv 8 0) n mb nch P8 cz 0 Hn34 (proj1 Hnchq) CZ2 ltac:(lia) Hmbq HPAq Hszq) as SUMt.
      rewrite <- EMC in SUMt.
      pose proof (sh_mem_sum Mr2 (seg_rom BSEGS) S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (bytes_le_to_Z lkb)) k1 k2 k3 n mb GSq Hn34 Hmbq GTq) as SUMh.
      fold MH in SUMh.
      destruct (sh_mem_hdr Mr2 S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) k1 k2 k3 n mb Hn34 Hmbq) as (H_mb & H_msz & H_need). fold MH in H_mb, H_msz, H_need.
      destruct (st_mem_cells MH naw curw mxw blw w16 w24 (Z_to_bv 8 0) n mb nch P8 cz Hn34 (proj1 Hnchq) CZ2 Hmbq HPAq HPAmbq) as (T_idx & T_ptr & T_nch & T_lk & T_h15 & T_h14 & T_h12).
      rewrite <- EMC in T_idx, T_ptr, T_nch, T_lk, T_h15, T_h14, T_h12.
      (* [comment removed for export] *)
      assert (RDH : forall (z : Z) (k : nat) bs, 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ W_sect mb nch P8 i) ->
                rdn BSEGS MH (Z_to_bv 64 z) k = Some bs -> rdn BSEGS MC (Z_to_bv 64 z) k = Some bs).
      { intros z k bs Hz0 Hz1 Hoff Hr. apply (msum_rdn_eq BSEGS _ MH MC _ k bs SUMt); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hoff | exact Hr]. }
      assert (NWT_map : forall i, mb <= i < mb + 24 -> ~ W_sect mb nch P8 i).
      { intros i Hi. (lazymatch goal with |- ?G => let G' := eval unfold W_sect, W_sect2 in G in change_no_check G' end). unfold hideW in AP8. clear - Hi AP8 GA NCH0 SLEN GMSZ Hn1. lia. }
      (* [comment removed for export] *)
      assert (NWS : forall z, U S - 2400 <= z -> ~ W_ng S thr n mb nch P8 z).
      { intros z Hz Hw. unfold W_ng, W_seca, W_sec1, W_sec2, W_sect, W_sect2 in Hw. rewrite MSZ, Uthr in Hw. unfold SB in Hw. fold q e in Hw.
        destruct Hw as [[[F|F]|[F|[F|F]]]|[[F|[F|F]]|F]].
        - clear - F Hz. lia.
        - clear - F Hz GQ6 CEILS CR. lia.
        - clear - F Hz GTC CEILS. lia.
        - clear - F Hz Y3 CEILS GMSZ Hn1. lia.
        - clear - F Hz CEILS CR. lia.
        - clear - F Hz Y3 CEILS GMSZ Hn1. lia.
        - clear - F Hz PA2 CEILS NCH0 SLEN. lia.
        - clear - F Hz CEILS CR. lia.
        - clear - F Hz Y3 CEILS GMSZ Hn1. lia. }
      assert (VISD : forall x : word, Hd2 x = false -> MD x = MC x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end); apply munrestrict_off; exact Hx).
      assert (MAPV : forall x : word, mb <= U x < mb + msz -> MD x = MC x).
      { intros x Hx. apply VISD. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHmap. exact Hx. }
      assert (Ep15 : mb + sec_user_off n - 15 = mb + 4096 + 2048 - 15) by (rewrite EOFF; clear; lia).
      assert (Ep14 : mb + sec_user_off n - 14 = mb + 4096 + 2048 - 14) by (rewrite EOFF; clear; lia).
      assert (Ep12 : mb + sec_user_off n - 12 = mb + 4096 + 2048 - 12) by (rewrite EOFF; clear; lia).
      apply (sec_at_depot bt FXOK KD BT_segs BT_ia G_KD HYP_DEPOT9 fx R M mdl Lc FF B C K ret sp n st h Qok r MD mdl1 mb false x18 x19 sz
               HFX W RP BD HLE CP Hn HB HC HK AL DY AP APM0).
      - split; [intros E; discriminate E | intros E; exfalso; exact (NEQ E)].
      - rewrite Ehl. exact HLq.
      - exact (model_ivs_wf_sbm mdlq mdl1 SBM1 LMW).
      - exact MI1.
      - rewrite Evm, LV. (lazymatch goal with |- ?G => let G' := eval unfold mb in G in change_no_check G' end). rewrite Z_to_bv_bv_unsigned. reflexivity.
      - intros z. rewrite Evm, LN. split; [intros H0; split; [exact H0 | intros [E _]; discriminate E] | intros [H0 _]; exact H0].
      - rewrite Evm, LN. exact NPOS.
      - intros z. rewrite Elz, LL. split; [intros H0; split; [exact H0 | intros [E _]; discriminate E] | intros [H0 _]; exact H0].
      - rewrite Elz, LL. exact LOK.
      - rewrite Evm. exact LR.
      - rewrite Evm. exact LB.
      - rewrite Evm. exact LSB.
      - rewrite Evm. exact LMB.
      - rewrite Evm. exact LIS.
      - rewrite Evm. exact LLIM.
      - rewrite Eeg. rewrite Usz in LEG. fold msz. clear - LEG. lia.
      - exact (same_except_vm_trans _ _ _ SEVq (same_but_materialized_except_vm _ _ SBM1)).
      - intros z Hz _. (lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end). rewrite Elz, LL. reflexivity.
      - exact GRD.
      - exact FOOTD.
      - apply RDV; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NHmap; clear - Hi GMSZ Hn1; lia |].
        apply RDH; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NWT_map; clear - Hi; lia | exact H_mb].
      - apply RDV; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NHmap; clear - Hi GMSZ Hn1; lia |].
        apply RDH; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NWT_map; clear - Hi; lia | rewrite MSZ in H_msz; exact H_msz].
      - apply RDV; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NHmap; clear - Hi GMSZ Hn1; lia |].
        apply RDH; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NWT_map; clear - Hi; lia | exact H_need].
      - apply RDV; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NHmap; clear - Hi GMSZ Hn1; lia | exact T_idx].
      - apply RDV; [clear - GP8 PA2 CR NCH0 SLEN; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GP8 PA2 CR NCH0 SLEN; lia | | exact T_ptr].
        intros i Hi. cbn in Hi. apply NHp8. clear - Hi NEQ WS1 NCH0. fold nch nres in WS1. lia.
      - apply RDV; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply NHs; [clear - Hi; lia | right; clear - Hi; lia] |].
        rewrite EMC. rewrite (st_mem_below MH naw curw mxw blw w16 w24 (Z_to_bv 8 0) n mb nch P8 cz Hn34 (proj1 Hnchq) CZ2 Hmbq HPAq 0x10abc8 8%nat ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
        apply (msum_rdn_eq BSEGS _ Mr2 MH _ 8%nat _ SUMh); [rewrite u_Z2bv by (clear; lia); clear; lia | | exact K_nres].
        intros z Hz. rewrite u_Z2bv in Hz by (clear; lia). change (Z.of_nat 8) with 8 in Hz. (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end). rewrite MSZ, Uthr. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q e. unfold hideW in GTI.
        clear - Hz CEILS CR GQ5 GA GTI. lia.
      - apply RDV; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply NHs; [clear - Hi; lia | right; clear - Hi; lia] | exact T_nch].
      - apply RDV; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply NHs; [clear - Hi; lia | right; clear - Hi; lia] | exact T_lk].
      - (* [comment removed for export] *)
        intros x Hx. pose proof (u64_range x) as Hxr. unfold SB in Hx. fold q in Hx.
        rewrite VISD by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHsh; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end); fold q; rewrite GQ7; fold e; clear - Hx TG5 TG6 TG7; lia).
        rewrite (proj1 SUMt x) by ((lazymatch goal with |- ?G => let G' := eval unfold W_sect, W_sect2 in G in change_no_check G' end); unfold hideW in Y5, PA4; unfold AS_LO, AS_HEAPLO in Y5, PA4; clear - Hx Y5 PA4 GQ5 GQ6 TG5 TG6 TG7 GMSZ Hn1 NCH0 SLEN; lia).
        apply (sh_mem_fa Mr2 S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) k1 k2 k3 n mb GSq Hn34 Hmbq Hmbbandq
                 (conj (proj1 GTq) (proj1 (proj2 GTq))) GTbandq GSbandq x).
        (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q. exact Hx.
      - rewrite Ep15. rewrite MAPV by (rewrite u_Z2bv by (clear - MBR; lia); clear - GMSZ Hn1; lia). rewrite T_h15. reflexivity.
      - rewrite Ep14. apply RDV; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NHmap; clear - Hi GMSZ Hn1; lia | exact T_h14].
      - rewrite Ep12. apply RDV; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply NHmap; clear - Hi GMSZ Hn1; lia | exact T_h12].
      - (* [comment removed for export] *)
        intros x Hx. rewrite (MAPV x Hx). apply (proj2 SUMr). rewrite NHw by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHmap; exact Hx).
        rewrite ZEROq by exact Hx. discriminate.
      - (* [comment removed for export] *)
        intros x Hx. rewrite EOFF in Hx.
        rewrite MAPV by (clear - Hx GMSZ Hn1; lia). rewrite EMC.
        rewrite (st_mem_tail8 MH naw curw mxw blw w16 w24 (Z_to_bv 8 0) n mb nch P8 cz Hn34 (proj1 Hnchq) CZ2 Hmbq HPAq HPAmbq x) by (clear - Hx; lia).
        rewrite (proj1 SUMh x) by ((lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end); rewrite MSZ, Uthr; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); fold q e; unfold hideW in Y5, APT; unfold AS_LO, AS_HEAPLO in Y5;
                                   clear - Hx Y5 APT Y3 CEILS GQ5 GQ6 GMSZ Hn1 GA; lia).
        rewrite NHw by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHmap; clear - Hx GMSZ Hn1; lia).
        apply ZEROq. fold mb msz. clear - Hx GMSZ Hn1. lia.
      - intros E. discriminate E.
      - intros k0 v Hin. fold S.
        pose proof (ma_slotsA_range S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) k0 v Hin) as [Hka Hkb].
        apply (msum_rdn_eq BSEGS _ Mq MD _ 8%nat _ SUMD); [rewrite at_u by (clear - Hka Hkb CEILS HSr CR; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hka Hkb HSr; lia | | exact (FA k0 v Hin)].
        intros z Hz. rewrite at_u in Hz by (clear - Hka Hkb CEILS HSr CR; lia). apply NWS. clear - Hz Hka. lia.
      - intros k0 v Hin. fold S.
        assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
        apply (msum_rdn_eq BSEGS _ Mq MD _ 8%nat _ SUMD); [rewrite at_u by (clear - Hk CEILS HSr CR; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hk HSr; lia | | exact (FI k0 v Hin)].
        intros z Hz. rewrite at_u in Hz by (clear - Hk CEILS HSr CR; lia). apply NWS. clear - Hz Hk. lia.
      - exact E1.
      - exact E2.
      - exact E10.
      - exact E11.
      - exact (proj1 SZ1).
      - exact E4.
      - exact E3.
      - exact E8.
      - exact E9.
      - exact E18.
      - exact E19.
      - rewrite E20. exact EQ20.
      - rewrite E21. exact EQ21.
      - exact E22.
      - exact E23.
      - exact E24.
      - rewrite E25. exact EQ25.
      - rewrite E26. reflexivity.
      - exact E27.
      - exact CONT. }
    (* [comment removed for export] *)
    destruct (@sec_run_g1 fx Mr2 (seg_rom BSEGS) rq S thr tp (getr R 3) (Z_to_bv 64 TSDP) ctxw (Z_to_bv 64 MIDEND)
                (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (bytes_le_to_Z lkb)) (Z_to_bv 8 1) k1 k2 k3 n mb 0 nch nres cz P8
                PRL H10q Q21 Q4 Q3 GSq Hn34 Hmbq Hmbspq Hmbbandq GTq GTimgq GTbandq GTmbq Hnchq Hclzq
                PH1 ltac:(rewrite MSZ; exact PH2) GH GHoffq SOK_gq K_ipg C72 C80 K_lock V_lock SOK_T SOK_hq SOK_lk K_nch K_nres EQN
                ltac:(clear - GP8 PA2 CR; lia) K_pab)
      as (r1 & RUN1 & J1 & J2 & J11 & J12 & J13 & J8 & J9 & J18 & J19 & J20 & J21 & J4 & J3 & J26 & J27).
    set (MH1 := sh_mem Mr2 S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) k1 k2 k3 n mb) in *.
    pose proof (sh_mem_sum Mr2 (seg_rom BSEGS) S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) (Z_to_bv 64 (bytes_le_to_Z lkb)) k1 k2 k3 n mb GSq Hn34 Hmbq GTq) as SUMh.
    fold MH1 in SUMh.
    apply (katD_msteps_acct BSEGS Hd2 HOFF2 asanF_segs_wx A2
             (@mkst fx rq (Z_to_bv 64 0x51080) Mq (seg_rom BSEGS)) (@mkst fx r1 (Z_to_bv 64 0x8b244) MH1 (seg_rom BSEGS)) mdlq).
    { exact LC2. } { exact AW2. } { exact MI2. } { exact HLq. }
    { rewrite restrict_mkst_g. replace (Z_to_bv 64 0x51080 : word) with (331904%bv : word) by (apply bv_eq; reflexivity).
      replace (Z_to_bv 64 0x8b244 : word) with (569924%bv : word) by (apply bv_eq; reflexivity). exact RUN1. }
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx rq (Z_to_bv 64 0x51080) Mq (seg_rom BSEGS))) with Mq by reflexivity.
    set (MD1 := munrestrict Hd2 Mq MH1).
    (* [comment removed for export] *)
    assert (WVIS1 : forall x : word, W_seca S thr n mb (U x) -> Hd2 x = false).
    { intros x Hw. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      unfold W_seca, W_sec1, W_sec2 in Hw. rewrite MSZ, Uthr in Hw.
      destruct Hw as [[F|F]|[F|[F|F]]].
      - apply NHs; [exact Hxr | left; clear - F CEILS; lia].
      - apply NHsh. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi in G in change_no_check G' end). fold q. rewrite GQ7. fold e. unfold SB in *. fold q e in F. exact F.
      - apply NHrt. left. clear - F. lia.
      - apply NHmap. clear - F GMSZ Hn1. lia.
      - apply NHs; [exact Hxr | right; clear - F; lia]. }
    pose proof (msum_unrestrict Hd2 _ Mq MH1 WVIS1 SUMh) as SUM1. fold MD1 in SUM1.
    assert (VIS1 : forall x : word, Hd2 x = false -> MD1 x = MH1 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MD1 in G in change_no_check G' end); apply munrestrict_off; exact Hx).
    assert (GRQ1 : mem_grows Mq MD1) by exact (proj2 SUM1).
    (* [comment removed for export] *)
    assert (NRES0 : nres = 0).
    { clear - EQN SLEN WS2 WS3 NCH0. unfold nres in *. rewrite <- EQN in *. Z.div_mod_to_equations. lia. }
    assert (EFSP : fsp = at_ S (-2416)) by ((lazymatch goal with |- ?G => let G' := eval unfold fsp in G in change_no_check G' end); rewrite at_at; reflexivity).
    assert (KM1 : forall (z : Z) (k : nat) v, rdn BSEGS Mr2 (Z_to_bv 64 z) k = Some v -> AIMGLO <= z -> z + Z.of_nat k <= AIMGHI ->
              (z + Z.of_nat k <= 0x10ae00 \/ 0x10ae04 <= z) -> rdn BSEGS MD1 (Z_to_bv 64 z) k = Some v).
    { intros z k v Hr Hz0 Hz1 Hlk. (lazymatch goal with |- ?G => let G' := eval unfold MD1 in G in change_no_check G' end). rewrite (rdn_munrestrict BSEGS Hd2 Mq MH1 _ k);
        [| rewrite u_Z2bv by (clear - Hz0 Hz1; lia); clear - Hz0 Hz1; lia
         | intros x Hx; rewrite u_Z2bv in Hx by (clear - Hz0 Hz1; lia); pose proof (u64_range x) as Hxr; rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHs; [exact Hxr | right; clear - Hx Hz0 Hz1; lia]].
      apply (msum_rdn_eq BSEGS _ Mr2 MH1 _ k v SUMh); [rewrite u_Z2bv by (clear - Hz0 Hz1; lia); clear - Hz0 Hz1; lia | | exact Hr].
      intros i Hi. rewrite u_Z2bv in Hi by (clear - Hz0 Hz1; lia). (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end). rewrite MSZ, Uthr. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q e. unfold hideW in GTI.
      clear - Hi Hz0 Hz1 Hlk CEILS CR GQ5 GA GTI. lia. }
    destruct PCELLS as (PC_rel & PC_ri & PC_pre & PC_dpm & PC_lim).
    assert (STK1 : forall x : word, U S - 3584 <= U x < U S -> MD1 x <> None /\ store_ok BSEGS MD1 x 1%nat = true).
    { intros x Hx. destruct (STKq x ltac:(clear - Hx; lia)) as [D1 D2]. split; [exact (GRQ1 x D1) | eapply store_ok_mono; [exact GRQ1 | exact D2]]. }
    assert (KKr : forall (z : Z) (k : nat) v, In (z, k, v) (bt_consts bt) -> AIMGLO <= z -> z + Z.of_nat k <= AIMGHI -> (z + Z.of_nat k <= 0x10ae00 \/ 0x10ae04 <= z) ->
              rdn BSEGS MD1 (Z_to_bv 64 z) k = Some (word_to_le_bytes k (Z_to_bv 64 v))).
    { intros z k v Hin Hz0 Hz1 Hlk. exact (KM1 z k _ (KK z k v Hin Hz0 Hz1) Hz0 Hz1 Hlk). }
    replace (Z_to_bv 64 0x20000 : word) with (Z_to_bv 64 (2 ^ 17) : word) in J12 by reflexivity.
    replace (at_ (at_ S (-2320)) (-96)) with (at_ S (-2416)) in J2 by (rewrite at_at; reflexivity). rewrite EQN in J11.
    apply (sec_grow_node bt FXOK BT_ia BF GROW_DIE fx r1 MD1 mdl mdlq mdl1 st st1 Lc FF M a n S PGP 0x19fce8 Qok
             (Z_to_bv 64 0x10ae08) (Z_to_bv 64 (0x10ab58 + 64)) (Z_to_bv 64 (la_msz (sec_needed n))) (Z_to_bv 64 cz) (Z_to_bv 64 (mb + 4096)) (Z_to_bv 64 mb)
             HFX W RP MW ltac:(fold nres; rewrite NRES0; clear; lia) (conj LV (conj LN (conj LL (conj LR (conj LB (conj LSB (conj LMB (conj LIS (conj LLIM (conj LEG (conj LMW HLq)))))))))))
             ltac:(fold msz; clear - GMSZ Hn1 MBR; lia) ltac:(fold mb msz; unfold hideW in AP8; clear - AP8; lia) AW2
             ltac:(fold msz; change (a_aa st1) with A2; rewrite AB2; clear - BUDG; lia) SBM1 MI1 HOFF2 NHs J1 J2 J11 J12 J13 J8 J9 J18 J19 J20 J21
             CEILS ltac:(clear - CPhi CP2; lia) ltac:(rewrite CP2; exact CP16) STK1 (conj Gc3 Gc4) ltac:(clear; lia)).
    { exact (KKr _ _ _ CELL_pg ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { exact (KKr _ _ _ CELL_P ltac:(exact Gc3) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Gc4; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); exact HPGP)). }
    { exact (KKr _ _ _ CELL_gcf ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { change (0x19fce8 + 144) with 0x19fd78. exact (KKr _ _ _ PC_lim ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(right; clear; lia)). }
    { exact (KKr _ _ _ CELL_s1 ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { exact (KKr _ _ _ CELL_s2 ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { exact (KKr _ _ _ CELL_s3 ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { exact (KKr _ _ _ CELL_s4 ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { exact (KKr _ _ _ CELL_jt ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { exact (KKr _ _ _ CELL_av ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { exact (KKr _ _ _ CELL_d1 ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)). }
    { exact (KKr _ _ _ CELL_d2 ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(right; clear; lia)). }
    (* [comment removed for export] *)
    intros r' mdlm mdl4 SBMm MIm SBM4 MI4 RET.
    set (lo := P8 + 8 * a_nres st) in *. set (spn := at_ S (-2416)) in *.
    set (addr := Z_to_bv 64 lo : word) in *. set (size := Z_to_bv 64 (2 ^ 17) : word) in *.
    match goal with |- katD _ (mkCfg (mkst _ _ ?m _) _) _ => set (M4 := m) end.
    assert (LO0 : lo = P8) by ((lazymatch goal with |- ?G => let G' := eval unfold lo in G in change_no_check G' end); fold nres; rewrite NRES0; clear; lia).
    assert (Uspn : U spn = U S - 2416) by ((lazymatch goal with |- ?G => let G' := eval unfold spn in G in change_no_check G' end); rewrite at_u by (clear - CEILS HSr CR; lia); clear; lia).
    assert (Uaddr : U addr = lo) by ((lazymatch goal with |- ?G => let G' := eval unfold addr in G in change_no_check G' end); rewrite u_Z2bv by (clear - LO0 GP8 PA2 CR; lia); reflexivity).
    assert (Usize : U size = 2 ^ 17) by reflexivity.
    (* [comment removed for export] *)
    assert (Usz' : U (Z_to_bv 64 msz : word) = msz) by exact Usz.
    pose proof (N8_pf bt BF st Lc FF M mdl mdlq a (Z_to_bv 64 msz) A2 (2 ^ 20) (2 ^ 28) W RP MW ltac:(fold nres; rewrite NRES0; clear; lia)
                  (conj LV (conj LN (conj LL (conj LR (conj LB (conj LSB (conj LMB (conj LIS (conj LLIM (conj LEG (conj LMW HLq)))))))))))
                  ltac:(rewrite Usz'; fold mb; unfold hideW in AP8; clear - AP8; lia) AW2 ltac:(rewrite Usz', AB2; clear - BUDG; lia)) as N8.
    cbv zeta in N8. fold lo addr size in N8. destruct N8 as (_ & _ & _ & _ & NODEF & LED).
    destruct (NODEF mdlm SBMm MIm) as (_ & _ & _ & _ & _ & HOK & MOKI & LZOK & _).
    pose proof (same_but_materialized_frame _ mdl4 SBM4) as (_ & _ & Elz4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ehl4 & _).
    assert (HL4 : m_halted mdl4 = None) by (rewrite Ehl4; exact HOK).
    set (Hd3 := HID st1 mdl4).
    assert (HD23 : forall x : word, Hd2 x = false -> Hd3 x = false).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold Hd3, HID, mkH in G in change_no_check G' end). unfold Hd2, HID, mkH in Hx.
      destruct (page_in_ranges (page_base x) (m_vm_lazy mdl4)) eqn:E4; [| reflexivity]. (lazymatch goal with |- ?G => let G' := eval cbn [andb] in G in change_no_check G' end).
      assert (Eq : page_in_ranges (page_base x) (m_vm_lazy mdlq) = true) by (rewrite LL; apply LZOK; rewrite <- Elz4; exact E4).
      rewrite Eq in Hx. cbn [andb] in Hx. exact Hx. }
    assert (HOFF3 : H_off_segments BSEGS Hd3).
    { intros x Hx. apply HOFF2. destruct (Hd2 x) eqn:E; [reflexivity|]. rewrite (HD23 x E) in Hx. discriminate Hx. }
    destruct (LED mdlm mdl4 SBMm SBM4) as (_ & _ & _ & LZ4 & _).
    assert (NH3S : forall z, lo <= z < lo + 2 ^ 17 -> Hd3 (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [clear - Hz LO0 GP8 PA2 CR; lia|]. destruct (lzb mdl4 z) eqn:E; [| reflexivity]. exfalso.
      assert (PI : pg_in_ivz (m_vm_lazy mdl4) z) by (split; [clear - Hz LO0 GP8 PA2 CR; lia | exact E]).
      apply LZ4 in PI. exact (proj2 PI Hz). }
    (* [comment removed for export] *)
    assert (M4out : forall x : word, (U x < U S - 2784 \/ U S - 2416 <= U x) -> (U x < lo \/ lo + 2 ^ 17 <= U x) -> M4 x = MD1 x).
    { intros x Hf Hs. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end).
      rewrite wb_out by (wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by (rewrite Uspn; clear - CEILS HSr CR; lia); rewrite ?Uspn; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hf HSr CEILS CR; lia).
      rewrite zfill_out by (rewrite Uaddr, Usize; exact Hs).
      apply mfo_m1_outside; [rewrite Uspn; clear - CEILS CR CPhi CP2; lia | rewrite Uspn; clear - Hf; lia]. }
    assert (GR4 : mem_grows MD1 M4).
    { (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end). eapply mem_grows_trans; [| apply wbytes_grows]. eapply mem_grows_trans; [| apply zfill_grows_s]. apply mfo_m1_grows. }
    assert (M4z : forall x : word, lo <= U x < lo + 2 ^ 17 -> M4 x = Some (Z_to_bv 8 0)).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M4 in G in change_no_check G' end).
      rewrite wb_out by (wd_lenlit; rewrite ?length_N_to_le_bytes, at_u by (rewrite Uspn; clear - CEILS HSr CR; lia); rewrite ?Uspn; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hx LO0 PA2 CEILS HSr; lia).
      apply zfill_in_s. rewrite Uaddr, Usize. exact Hx. }
    set (Mr3 := mrestrict Hd3 M4).
    assert (NHw3 : forall x : word, Hd3 x = false -> Mr3 x = M4 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold Mr3 in G in change_no_check G' end); apply mrestrict_off; exact Hx).
    (* [comment removed for export] *)
    assert (TR3 : forall (z : Z) (k : nat) v, rdn BSEGS Mr2 (Z_to_bv 64 z) k = Some v -> 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 ->
              (forall i, z <= i < z + Z.of_nat k -> ~ W_seca S thr n mb i /\ (i < U S - 2784 \/ U S - 2416 <= i) /\ (i < lo \/ lo + 2 ^ 17 <= i) /\ Hd2 (Z_to_bv 64 i) = false) ->
              rdn BSEGS Mr3 (Z_to_bv 64 z) k = Some v).
    { intros z k v Hr Hz0 Hz1 Hc. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by (clear - Hz0; lia); exact Hz1|].
      intros x Hx. rewrite u_Z2bv in Hx by (clear - Hz0; lia). destruct (Hc _ Hx) as (C1 & C2 & C3 & C4). rewrite Z_to_bv_bv_unsigned in C4.
      rewrite NHw3 by (apply HD23; exact C4). rewrite M4out by assumption. rewrite VIS1 by exact C4. exact (proj1 SUMh x C1). }
    (* [comment removed for export] *)
    destruct RET as (C10 & C2 & C1 & C8 & C9 & C18 & C19 & C20 & AGL).
    Ltac nclob2 := (lazymatch goal with |- ?G => let G' := eval unfold mfi_clob2, mfi_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros X; repeat (destruct X as [X|X]; [discriminate X|]); exact X.
    assert (C21 : getr r' 21 = Z_to_bv 64 mb) by (rewrite (AGL 21%bv) by nclob2; exact J21).
    assert (C26 : getr r' 26 = thr) by (rewrite (AGL 26%bv) by nclob2; rewrite J26; exact Q26).
    assert (C27 : getr r' 27 = Z_to_bv 64 1) by (rewrite (AGL 27%bv) by nclob2; rewrite J27; exact Q27).
    assert (C4 : getr r' 4 = tp) by (rewrite (AGL 4%bv) by nclob2; exact J4).
    assert (C3 : getr r' 3 = getr R 3) by (rewrite (AGL 3%bv) by nclob2; exact J3).
    assert (C2' : getr r' 2 = at_ (at_ S (-2320)) (-96)) by (rewrite C2; (lazymatch goal with |- ?G => let G' := eval unfold spn in G in change_no_check G' end); rewrite at_at; reflexivity).
    (* [comment removed for export] *)
    assert (TRI : forall (z : Z) (k : nat) v, rdn BSEGS Mr2 (Z_to_bv 64 z) k = Some v -> AIMGLO <= z -> z + Z.of_nat k <= AIMGHI ->
              (z + Z.of_nat k <= 0x10ae00 \/ 0x10ae04 <= z) -> rdn BSEGS Mr3 (Z_to_bv 64 z) k = Some v).
    { intros z k v Hr Hz0 Hz1 Hlk. apply (TR3 z k v Hr); [clear - Hz0 Hz1; lia | clear - Hz0 Hz1; lia |].
      intros i Hi. split; [| split; [| split]].
      - (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end). rewrite MSZ, Uthr. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q e. unfold hideW in GTI. clear - Hi Hz0 Hz1 Hlk CEILS CR GQ5 GA GTI. lia.
      - left. clear - Hi Hz1 CEILS CR. lia.
      - left. clear - Hi Hz1 LO0 GP8. lia.
      - apply NHs; [clear - Hi Hz0 Hz1; lia | right; clear - Hi Hz0 Hz1; lia]. }
    assert (TRS : forall (k : Z) (w : nat) v, rdn BSEGS Mr2 (at_ S k) w = Some v -> -2416 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS Mr3 (at_ S k) w = Some v).
    { intros k w v Hr Hka Hkb.
      assert (EA : at_ S k = Z_to_bv 64 (U S + k)) by (apply bv_eq; rewrite at_u by (clear - Hka Hkb CEILS HSr CR; lia); rewrite u_Z2bv by (clear - Hka Hkb CEILS HSr CR; lia); reflexivity).
      rewrite EA in Hr |- *. apply (TR3 _ w v Hr); [clear - Hka Hkb CEILS HSr CR; lia | clear - Hka Hkb HSr; lia |].
      intros i Hi. split; [| split; [| split]].
      - (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end). rewrite MSZ, Uthr. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q e. clear - Hi Hka CEILS CR GQ6 GTC Y3 GMSZ Hn1. lia.
      - right. clear - Hi Hka. lia.
      - right. clear - Hi Hka LO0 PA2 CEILS. lia.
      - apply NHs; [clear - Hi Hka Hkb CEILS HSr CR; lia | left; clear - Hi Hka CEILS; lia]. }
    assert (MAPD3 : forall x : word, mb <= U x < mb + msz -> Mr3 x <> None).
    { intros x Hx. rewrite NHw3 by (apply HD23; rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHmap; exact Hx).
      apply GR4. apply GRQ1. rewrite ZEROq by exact Hx. discriminate. }
    assert (MAPOK3 : forall (l0 : Z) (w : nat), mb <= l0 -> l0 + Z.of_nat w <= mb + msz -> store_ok BSEGS Mr3 (Z_to_bv 64 l0) w = true).
    { intros l0 w L1 L2. apply store_ok_bytes; [| rewrite u_Z2bv by (clear - L1 L2 MBR GMSZ Y3 CR; lia); clear - L1 L2 MBR GMSZ Y3 CR; lia].
      intros x Hx. rewrite u_Z2bv in Hx by (clear - L1 L2 MBR GMSZ Y3 CR; lia). apply store_ok1_defG. apply MAPD3. clear - Hx L1 L2. lia. }
    assert (K3_pa : rdn BSEGS Mr3 (Z_to_bv 64 (0x10ab58 + 72)) 8 = Some (LE8 (Z_to_bv 64 P8))) by exact (TRI _ _ _ K_pa ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)).
    assert (K3_nres : rdn BSEGS Mr3 (Z_to_bv 64 (0x10ab58 + 112)) 8 = Some (LE8 (Z_to_bv 64 nres))) by exact (TRI _ _ _ K_nres ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)).
    assert (K3_nch : rdn BSEGS Mr3 (Z_to_bv 64 (0x10ab58 + 120)) 8 = Some (LE8 (Z_to_bv 64 nch))) by exact (TRI _ _ _ K_nch ltac:(clear; lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia) ltac:(left; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia)).
    destruct (sec_inst_word Mr3 0x10abe0 ltac:(clear; lia) ltac:(clear; lia)) as [naw3 K3_na].
    destruct (sec_inst_word Mr3 0x10abf0 ltac:(clear; lia) ltac:(clear; lia)) as [curw3 K3_cur].
    destruct (sec_inst_word Mr3 0x10abf8 ltac:(clear; lia) ltac:(clear; lia)) as [mxw3 K3_mx].
    destruct (sec_inst_word Mr3 0x10ae18 ltac:(clear; lia) ltac:(clear; lia)) as [w163 K3_16].
    destruct (sec_inst_word Mr3 0x10ae20 ltac:(clear; lia) ltac:(clear; lia)) as [w243 K3_24].
    destruct (sec_inst_word Mr3 (0x10ac00 + 8 * (63 - cz)) ltac:(clear - CZ2; lia) ltac:(clear - CZ2; lia)) as [blw3 K3_bl].
    assert (SOK3_pa : store_ok BSEGS Mr3 (Z_to_bv 64 (P8 + 8 * nch)) 8 = true).
    { apply store_ok_bytes; [| rewrite u_Z2bv by (clear - GP8 PA2 CR NCH0 SLEN; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GP8 PA2 CR NCH0 SLEN; lia].
      intros x Hx. rewrite u_Z2bv in Hx by (clear - GP8 PA2 CR NCH0 SLEN; lia). cbn in Hx. apply store_ok1_defG.
      assert (INS : lo <= U x < lo + 2 ^ 17) by (rewrite LO0; clear - Hx EQN NRES0; lia).
      rewrite NHw3 by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NH3S; exact INS). rewrite (M4z x INS). discriminate. }
    assert (SOK3_inst : store_ok BSEGS Mr3 (Z_to_bv 64 0x10ab98) 728 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (SOK3_nres : store_ok BSEGS Mr3 (Z_to_bv 64 (0x10ab58 + 112)) 8 = true) by (apply store_ok_wseg; vm_cast_no_check (eq_refl true)).
    assert (FLA3 : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
                         (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)] ->
              rdn BSEGS Mr3 (at_ (at_ S (-2320)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -88 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      pose proof (FLAq o v Hin) as Hr. rewrite at_at in Hr |- *. apply TRS; [exact Hr | clear - Ho; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Ho; lia]. }
    assert (FC3 : forall (o : Z) (v : word),
              In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)] ->
              rdn BSEGS Mr3 (at_ (at_ S (-2272)) o) 8 = Some (LE8 v)).
    { intros o v Hin.
      assert (Ho : -48 <= o <= -8) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      pose proof (FCq o v Hin) as Hr. rewrite at_at in Hr |- *. apply TRS; [exact Hr | clear - Ho; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Ho; lia]. }
    assert (Rb13 : rdn BSEGS Mr3 (at_ (Z_to_bv 64 (mb + 4096)) (rz n - 15)) 1 = Some [Z_to_bv 8 0]).
    { rewrite Erzn. assert (UA : U (at_ (Z_to_bv 64 (mb + 4096)) (2048 - 15)) = mb + 6129) by (rewrite at_u by (rewrite u_Z2bv by (clear - MBR; lia); clear - MBR; lia); rewrite u_Z2bv by (clear - MBR; lia); clear; lia).
      apply heap_rdn1; [rewrite UA; clear - GA; lia|].
      assert (INM : mb <= U (at_ (Z_to_bv 64 (mb + 4096)) (2048 - 15)) < mb + msz) by (rewrite UA; clear - GMSZ Hn1; lia).
      rewrite NHw3 by (apply HD23; rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)); apply NHmap; exact INM).
      rewrite M4out; [| left; rewrite UA; clear - Y3 CEILS GMSZ Hn1; lia | rewrite UA, LO0; unfold hideW in AP8; clear - AP8 GMSZ Hn1; lia].
      rewrite VIS1 by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)); apply NHmap; exact INM).
      rewrite (proj1 SUMh) by ((lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end); rewrite MSZ, Uthr, UA; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); fold q e; unfold hideW in Y5, APT; unfold AS_LO, AS_HEAPLO in Y5;
                                clear - Y5 APT Y3 CEILS GQ5 GQ6 GMSZ Hn1 GA; lia).
      rewrite NHw by (rewrite <- (Z_to_bv_bv_unsigned 64 (at_ _ _)); apply NHmap; exact INM).
      apply ZEROq. fold mb msz. exact INM. }
    assert (SOKh3 : store_ok BSEGS Mr3 (at_ (Z_to_bv 64 (mb + 4096)) (rz n - 16)) 16 = true).
    { rewrite Erzn. replace (at_ (Z_to_bv 64 (mb + 4096)) (2048 - 16)) with (Z_to_bv 64 (mb + 6128) : word)
        by (apply bv_eq; rewrite at_u by (rewrite u_Z2bv by (clear - MBR; lia); clear - MBR; lia); rewrite !u_Z2bv by (clear - MBR; lia); clear; lia).
      apply MAPOK3; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GMSZ Hn1; lia]. }
    assert (R163 : rdn BSEGS Mr3 (at_ (at_ S (-2272)) 16) 8 = Some (LE8 (Z_to_bv 64 16))).
    { pose proof R16q as Hr. rewrite at_at in Hr |- *. apply TRS; [exact Hr | clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia]. }
    assert (Rtr3 : rdn BSEGS Mr3 (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))) by (apply TRS; [exact Rtrq | clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia]).
    assert (Rsz3 : rdn BSEGS Mr3 (at_ (at_ S (-2128)) 8) 8 = Some bsz).
    { pose proof Rszq as Hr. rewrite at_at in Hr |- *. apply TRS; [exact Hr | clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia]. }
    assert (RT03 : rdn BSEGS Mr3 thr 8 = Some (LE8 ctxw)).
    { unfold thr in K_T0 |- *. apply (TR3 T 8%nat _ K_T0); [clear - GT0 GTC CR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GTC CR; lia |].
      intros i Hi. cbn in Hi. split; [| split; [| split]].
      - (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end). rewrite MSZ, Uthr. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q e. unfold hideW in GTI, GTB, APT. unfold AS_LO, AS_HEAPLO in GTB.
        clear - Hi GTC CEILS GTI GTB APT GQ5 GQ6 GMSZ Hn1. lia.
      - left. clear - Hi GTC CEILS. lia.
      - rewrite LO0. unfold hideW in PA6. clear - Hi PA6. lia.
      - apply NHrt. left. clear - Hi. lia. }
    assert (Rtid3 : rdn BSEGS Mr3 (at_ ctxw 8) 4 = Some (LE4 0)).
    { assert (EA : at_ ctxw 8 = Z_to_bv 64 (CTX + 8)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); rewrite Uctx; rewrite !u_Z2bv by (clear - GC0 GCC CR; lia); reflexivity).
      rewrite EA in K_tid |- *. apply (TR3 (CTX + 8) 4%nat _ K_tid); [clear - GC0 GCC CR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GCC CR; lia |].
      intros i Hi. cbn in Hi. split; [| split; [| split]].
      - (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end). rewrite MSZ, Uthr. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q e. unfold hideW in GCI, GCB, APC. unfold AS_LO, AS_HEAPLO in GCB.
        pose proof GctxTq as GX. rewrite Uctx, Uthr in GX. clear - Hi GCC CEILS GCI GCB APC GQ5 GQ6 GX GMSZ Hn1. lia.
      - left. clear - Hi GCC CEILS. lia.
      - rewrite LO0. unfold hideW in PA7. clear - Hi PA7. lia.
      - apply NHrt. right. clear - Hi. lia. }
    destruct (@sec_run_g2 fx Mr3 (seg_rom BSEGS) r' S thr ctxw (at_ S (-2112)) (Z_to_bv 64 sz) naw3 curw3 mxw3 blw3 w163 w243 bsz (Z_to_bv 8 0) n mb nch nres P8 cz 0
                C2' C8 C9 C18 C19 C21 C20 C26 C27 ltac:(clear - GSq; lia) Hn34 (proj1 Hnchq) CZ2 ltac:(clear; lia) Hmbq Hmbspq HPAq HPAmbq HPAspq
                (conj (conj (proj1 GTq) GTimgq) (proj1 (proj2 GTq))) GTmbq GTPAq Gctxq Gctxmbq GctxPAq K3_pa K3_na K3_cur K3_mx K3_bl K3_16 K3_24
                ltac:(apply MAPOK3; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GMSZ Hn1; lia]) SOK3_pa SOK3_inst FLA3 FC3 Rb13 SOKh3 R163 RT03 Rtid3 Rtr3 Rsz3 Hszq
                ltac:(rewrite NRES0; clear; lia) K3_nres K3_nch SOK3_nres)
      as (r & RUN2 & E1 & E2 & E10 & E11 & E8 & E9 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & EK).
    set (MC3 := g2_mem Mr3 naw3 curw3 mxw3 blw3 w163 w243 (Z_to_bv 8 0) n mb nch nres P8 cz) in *.
    apply (katD_msteps_acct BSEGS Hd3 HOFF3 asanF_segs_wx A2
             (@mkst fx r' (Z_to_bv 64 0x51420) M4 (seg_rom BSEGS)) (@mkst fx r (Z_to_bv 64 0x8f4f0) MC3 (seg_rom BSEGS)) mdl4).
    { apply lazy_cover_HID. } { exact AW2. } { exact MI4. } { exact HL4. }
    { rewrite restrict_mkst_g. replace (Z_to_bv 64 0x51420 : word) with (332832%bv : word) by (apply bv_eq; reflexivity). exact RUN2. }
    intros mdl5 MI5 SBM5 HC5. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx r' (Z_to_bv 64 0x51420) M4 (seg_rom BSEGS))) with M4 by reflexivity.
    set (MD := munrestrict Hd3 M4 MC3).
    (* [comment removed for export] *)
    pose proof (same_but_materialized_trans _ _ _ SBM4 SBM5) as SBM45.
    destruct (LED mdlm mdl5 SBMm SBM45) as (L_vm & L_na & L_np & L_lz & L_lf & L_rs & L_bk & L_sb & L_mb & L_is & L_lim & L_eg & L_sev & L_mw & L_hl & L_lzb).
    (* [comment removed for export] *)
    pose proof (g2_mem_sum Mr3 (seg_rom BSEGS) (Z_to_bv 64 sz) naw3 curw3 mxw3 blw3 w163 w243 bsz (Z_to_bv 8 0) n mb nch nres P8 cz 0
                  Hn34 (proj1 Hnchq) CZ2 ltac:(clear; lia) Hmbq HPAq Hszq) as SUMr3. fold MC3 in SUMr3.
    assert (WVIS3 : forall x : word, W_g2 mb nch P8 (U x) -> Hd3 x = false).
    { intros x Hw. pose proof (u64_range x) as Hxr. rewrite <- (Z_to_bv_bv_unsigned 64 x).
      unfold W_g2, W_sect, W_sect2 in Hw.
      destruct Hw as [F|[[F|[F|F]]|F]].
      - apply HD23. apply NHs; [exact Hxr | right; clear - F; lia].
      - apply HD23. apply NHmap. clear - F GMSZ Hn1. lia.
      - apply NH3S. rewrite LO0. clear - F EQN NRES0. lia.
      - apply HD23. apply NHs; [exact Hxr | right; clear - F; lia].
      - apply HD23. apply NHmap. clear - F GMSZ Hn1. lia. }
    pose proof (msum_unrestrict Hd3 _ M4 MC3 WVIS3 SUMr3) as SUMD3. fold MD in SUMD3.
    assert (VISD3 : forall x : word, Hd3 x = false -> MD x = MC3 x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end); apply munrestrict_off; exact Hx).
    assert (GRD : mem_grows M MD).
    { eapply mem_grows_trans; [exact GRq|]. eapply mem_grows_trans; [exact GRQ1|]. eapply mem_grows_trans; [exact GR4 | exact (proj2 SUMD3)]. }
    assert (Wg2_dec : Wdec (W_g2 mb nch P8)) by (intros z; (lazymatch goal with |- ?G => let G' := eval unfold W_g2, W_sect, W_sect2 in G in change_no_check G' end); repeat first [apply or_decT | apply ivl_decT]).
    assert (Wsa_dec : Wdec (W_seca S thr n mb)) by (intros z; (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end); repeat first [apply or_decT | apply ivl_decT]).
    assert (FOOTD : forall x : word, MD x <> M x -> sec_footA (U S) T mb msz P8 nch nres true (U x)).
    { intros x NE. (lazymatch goal with |- ?G => let G' := eval unfold sec_footA in G in change_no_check G' end). destruct (decide (MD x = M4 x)) as [E4|N4].
      - rewrite E4 in NE. destruct (decide (M4 x = MD1 x)) as [E1'|N1'].
        + rewrite E1' in NE. destruct (decide (MD1 x = Mq x)) as [Eq'|Nq'].
          * rewrite Eq' in NE. destruct (DIFFq x NE) as [D|D]; [left; clear - D; lia | right; left; exact D].
          * pose proof (proj1 (msum_changed _ Mq MD1 Wsa_dec SUM1 x Nq')) as Hw. unfold W_seca, W_sec1, W_sec2 in Hw. rewrite MSZ, Uthr in Hw.
            destruct Hw as [[F|F]|[F|[F|F]]].
            -- left. clear - F. lia.
            -- right; right; left. exact F.
            -- do 6 right. clear - F. lia.
            -- right; left. clear - F GMSZ Hn1. lia.
            -- do 3 right; left. clear - F. lia.
        + destruct (Z_lt_le_dec (U x) (U S - 2784)) as [L1|L1]; [| destruct (Z_lt_le_dec (U x) (U S - 2416)) as [L2|L2]; [left; clear - L1 L2; lia|]].
          * destruct (Z_lt_le_dec (U x) lo) as [L3|L3]; [exfalso; apply N1'; apply M4out; [left; exact L1 | left; exact L3]|].
            destruct (Z_lt_le_dec (U x) (lo + 2 ^ 17)) as [L4|L4]; [| exfalso; apply N1'; apply M4out; [left; exact L1 | right; exact L4]].
            do 5 right; left. split; [reflexivity|]. fold nres. fold lo. clear - L3 L4. lia.
          * exfalso. apply N1'. apply M4out; [right; exact L2 | right; clear - L2 LO0 PA2 CEILS; lia].
      - pose proof (proj1 (msum_changed _ M4 MD Wg2_dec SUMD3 x N4)) as Hw. unfold W_g2, W_sect, W_sect2 in Hw.
        destruct Hw as [F|[[F|[F|F]]|F]].
        + do 3 right; left. clear - F. lia.
        + right; left. clear - F GMSZ Hn1. lia.
        + do 4 right; left. exact F.
        + do 3 right; left. clear - F. lia.
        + right; left. clear - F GMSZ Hn1. lia. }
    (* [comment removed for export] *)
    assert (RD14 : forall (z : Z) (k : nat) v, rdn BSEGS MH1 (Z_to_bv 64 z) k = Some v -> 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 ->
              (forall i, z <= i < z + Z.of_nat k -> ~ W_g2 mb nch P8 i /\ (i < U S - 2784 \/ U S - 2416 <= i) /\ (i < lo \/ lo + 2 ^ 17 <= i) /\ Hd2 (Z_to_bv 64 i) = false) ->
              rdn BSEGS MD (Z_to_bv 64 z) k = Some v).
    { intros z k v Hr Hz0 Hz1 Hc. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by (clear - Hz0; lia); exact Hz1|].
      intros x Hx. rewrite u_Z2bv in Hx by (clear - Hz0; lia). destruct (Hc _ Hx) as (C1' & C2'' & C3' & C4'). rewrite Z_to_bv_bv_unsigned in C4'.
      rewrite (proj1 SUMD3 x C1'). rewrite M4out by assumption. exact (VIS1 x C4'). }
    assert (RDV3 : forall (z : Z) (k : nat) bs, 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd3 (Z_to_bv 64 i) = false) ->
              rdn BSEGS MC3 (Z_to_bv 64 z) k = Some bs -> rdn BSEGS MD (Z_to_bv 64 z) k = Some bs).
    { intros z k bs Hz0 Hz1 Hv Hr. (lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end). rewrite (rdn_munrestrict BSEGS Hd3 M4 MC3 _ k); [exact Hr | rewrite u_Z2bv by (clear - Hz0; lia); exact Hz1 |].
      intros x Hx. rewrite u_Z2bv in Hx by (clear - Hz0; lia). rewrite <- (Z_to_bv_bv_unsigned 64 x). apply Hv. exact Hx. }
    assert (MAP14 : forall i, mb <= i < mb + 24 -> ~ W_g2 mb nch P8 i /\ (i < U S - 2784 \/ U S - 2416 <= i) /\ (i < lo \/ lo + 2 ^ 17 <= i) /\ Hd2 (Z_to_bv 64 i) = false).
    { intros i Hi. split; [| split; [| split]].
      - (lazymatch goal with |- ?G => let G' := eval unfold W_g2, W_sect, W_sect2 in G in change_no_check G' end). unfold hideW in AP8. clear - Hi AP8 GA NCH0 SLEN GMSZ Hn1. lia.
      - left. clear - Hi Y3 CEILS GMSZ Hn1. lia.
      - rewrite LO0. unfold hideW in AP8. clear - Hi AP8 GMSZ Hn1. lia.
      - apply NHmap. clear - Hi GMSZ Hn1. lia. }
    destruct (sh_mem_hdr Mr2 S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) k1 k2 k3 n mb Hn34 Hmbq) as (H_mb & H_msz & H_need).
    fold MH1 in H_mb, H_msz, H_need. rewrite MSZ in H_msz.
    assert (EMC3 : MC3 = st_mem (la_mg Mr3 nres) naw3 curw3 mxw3 blw3 w163 w243 (Z_to_bv 8 0) n mb nch P8 cz) by reflexivity.
    destruct (st_mem_cells (la_mg Mr3 nres) naw3 curw3 mxw3 blw3 w163 w243 (Z_to_bv 8 0) n mb nch P8 cz Hn34 (proj1 Hnchq) CZ2 Hmbq HPAq HPAmbq) as (T_idx & T_ptr & T_nch & T_lk & T_h15 & T_h14 & T_h12).
    rewrite <- EMC3 in T_idx, T_ptr, T_nch, T_lk, T_h15, T_h14, T_h12.
    pose proof (g2_mem_nres Mr3 naw3 curw3 mxw3 blw3 w163 w243 (Z_to_bv 8 0) n mb nch nres P8 cz Hn34 (proj1 Hnchq) CZ2 Hmbq HPAq) as T_nres. fold MC3 in T_nres.
    assert (MAPV3 : forall x : word, mb <= U x < mb + msz -> MD x = MC3 x).
    { intros x Hx. apply VISD3. apply HD23. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHmap. exact Hx. }
    assert (Ep15 : mb + sec_user_off n - 15 = mb + 4096 + 2048 - 15) by (rewrite EOFF; clear; lia).
    assert (Ep14 : mb + sec_user_off n - 14 = mb + 4096 + 2048 - 14) by (rewrite EOFF; clear; lia).
    assert (Ep12 : mb + sec_user_off n - 12 = mb + 4096 + 2048 - 12) by (rewrite EOFF; clear; lia).
    (* [comment removed for export] *)
    assert (STKQ : forall (k0 : Z) (w : nat) v, -2400 <= k0 -> k0 + Z.of_nat w <= 0 -> rdn BSEGS Mq (at_ S k0) w = Some v -> rdn BSEGS MD (at_ S k0) w = Some v).
    { intros k0 w v Hka Hkb Hr. rewrite <- Hr. apply rdn_ext; [rewrite at_u by (clear - Hka Hkb CEILS HSr CR; lia); clear - Hka Hkb HSr; lia|].
      intros x Hx. rewrite at_u in Hx by (clear - Hka Hkb CEILS HSr CR; lia).
      rewrite (proj1 SUMD3 x) by ((lazymatch goal with |- ?G => let G' := eval unfold W_g2, W_sect, W_sect2 in G in change_no_check G' end); clear - Hx Hka CEILS CR Y3 PA2 NCH0 SLEN GMSZ Hn1; lia).
      rewrite M4out; [| right; clear - Hx Hka; lia | right; clear - Hx Hka LO0 PA2 CEILS; lia].
      apply (proj1 SUM1 x). (lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end). rewrite MSZ, Uthr. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q e. clear - Hx Hka CEILS CR GQ6 GTC Y3 GMSZ Hn1. lia. }
    apply (sec_at_depot bt FXOK KD BT_segs BT_ia G_KD HYP_DEPOT9 fx R M mdl Lc FF B C K ret sp n st h Qok r MD mdl5 mb true x18 x19 sz
             HFX W RP BD HLE CP Hn HB HC HK AL DY AP APM0).
    - split; [intros _; exact EQN | intros _; reflexivity].
    - exact L_hl.
    - exact L_mw.
    - exact MI5.
    - rewrite L_vm. (lazymatch goal with |- ?G => let G' := eval unfold mb in G in change_no_check G' end). rewrite Z_to_bv_bv_unsigned. reflexivity.
    - intros z. rewrite (L_na z). fold lo. split; [intros [H0 H1]; split; [exact H0 | intros [_ H2]; exact (H1 H2)] | intros [H0 H1]; split; [exact H0 | intros H2; exact (H1 (conj eq_refl H2))]].
    - exact L_np.
    - intros z. rewrite (L_lz z). fold lo. split; [intros [H0 H1]; split; [exact H0 | intros [_ H2]; exact (H1 H2)] | intros [H0 H1]; split; [exact H0 | intros H2; exact (H1 (conj eq_refl H2))]].
    - exact L_lf.
    - exact L_rs.
    - exact L_bk.
    - exact L_sb.
    - exact L_mb.
    - exact L_is.
    - exact L_lim.
    - rewrite Usz' in L_eg. fold msz. clear - L_eg. lia.
    - exact (same_except_vm_trans _ _ _ SEVq L_sev).
    - intros z Hz NS. apply (L_lzb z); [| exact Hz]. fold lo in NS. intros H2. exact (NS (conj eq_refl H2)).
    - exact GRD.
    - exact FOOTD.
    - apply (RD14 mb 8%nat _ H_mb); [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply MAP14; clear - Hi; lia].
    - apply (RD14 (mb + 8) 8%nat _ H_msz); [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply MAP14; clear - Hi; lia].
    - apply (RD14 (mb + 16) 8%nat _ H_need); [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply MAP14; clear - Hi; lia].
    - apply RDV3; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply HD23; apply NHmap; clear - Hi GMSZ Hn1; lia | exact T_idx].
    - apply RDV3; [clear - GP8 PA2 CR NCH0 SLEN; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GP8 PA2 CR NCH0 SLEN; lia | | exact T_ptr].
      intros i Hi. cbn in Hi. apply NH3S. rewrite LO0. clear - Hi EQN NRES0. lia.
    - apply RDV3; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | intros i Hi; cbn in Hi; apply HD23; apply NHs; [clear - Hi; lia | right; clear - Hi; lia] |].
      replace (a_nres st + 2 ^ 14) with (nres + 0x4000) by ((lazymatch goal with |- ?G => let G' := eval unfold nres in G in change_no_check G' end); reflexivity). exact T_nres.
    - apply RDV3; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | intros i Hi; cbn in Hi; apply HD23; apply NHs; [clear - Hi; lia | right; clear - Hi; lia] | exact T_nch].
    - apply RDV3; [clear; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear; lia | intros i Hi; cbn in Hi; apply HD23; apply NHs; [clear - Hi; lia | right; clear - Hi; lia] | exact T_lk].
    - (* [comment removed for export] *)
      intros x Hx. pose proof (u64_range x) as Hxr. unfold SB in Hx. fold q in Hx.
      assert (HV : Hd2 x = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHsh; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end); fold q; rewrite GQ7; fold e; clear - Hx TG5 TG6 TG7; lia).
      rewrite (proj1 SUMD3 x) by ((lazymatch goal with |- ?G => let G' := eval unfold W_g2, W_sect, W_sect2 in G in change_no_check G' end); unfold hideW in Y5, PA4; unfold AS_LO, AS_HEAPLO in Y5, PA4; clear - Hx Y5 PA4 GQ5 GQ6 TG5 TG6 TG7 GMSZ Hn1 NCH0 SLEN; lia).
      rewrite M4out; [| left; clear - Hx GQ6 TG5 TG6 TG7 CEILS CR; lia | rewrite LO0; unfold hideW in PA4; unfold AS_LO, AS_HEAPLO in PA4; clear - Hx PA4 GQ5 GQ6 TG5 TG6 TG7; lia].
      rewrite (VIS1 x HV).
      apply (sh_mem_fa Mr2 S thr (Z_to_bv 64 (bytes_le_to_Z b72)) (Z_to_bv 64 (bytes_le_to_Z b80)) k1 k2 k3 n mb GSq Hn34 Hmbq Hmbbandq
               (conj (proj1 GTq) (proj1 (proj2 GTq))) GTbandq GSbandq x).
      (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). fold q. exact Hx.
    - rewrite Ep15. rewrite MAPV3 by (rewrite u_Z2bv by (clear - MBR; lia); clear - GMSZ Hn1; lia). rewrite T_h15. reflexivity.
    - rewrite Ep14. apply RDV3; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply HD23; apply NHmap; clear - Hi GMSZ Hn1; lia | exact T_h14].
    - rewrite Ep12. apply RDV3; [clear - MBR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - MBR; lia | intros i Hi; cbn in Hi; apply HD23; apply NHmap; clear - Hi GMSZ Hn1; lia | exact T_h12].
    - intros x Hx. rewrite (MAPV3 x Hx). apply (proj2 SUMr3). exact (MAPD3 x Hx).
    - (* [comment removed for export] *)
      intros x Hx. rewrite EOFF in Hx.
      assert (INM : mb <= U x < mb + msz) by (clear - Hx GMSZ Hn1; lia).
      assert (HV : Hd2 x = false) by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NHmap; exact INM).
      rewrite (MAPV3 x INM). rewrite EMC3.
      rewrite (st_mem_tail8 (la_mg Mr3 nres) naw3 curw3 mxw3 blw3 w163 w243 (Z_to_bv 8 0) n mb nch P8 cz Hn34 (proj1 Hnchq) CZ2 Hmbq HPAq HPAmbq x) by (clear - Hx; lia).
      (lazymatch goal with |- ?G => let G' := eval unfold la_mg in G in change_no_check G' end). rewrite wb_out by (wd_lenlit; rewrite ?length_N_to_le_bytes, u_Z2bv by (clear; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hx GA; lia).
      rewrite NHw3 by (apply HD23; exact HV).
      rewrite M4out; [| left; clear - Hx Y3 CEILS GMSZ Hn1; lia | rewrite LO0; unfold hideW in AP8; clear - Hx AP8 GMSZ Hn1; lia].
      rewrite (VIS1 x HV).
      rewrite (proj1 SUMh x) by ((lazymatch goal with |- ?G => let G' := eval unfold W_seca, W_sec1, W_sec2 in G in change_no_check G' end); rewrite MSZ, Uthr; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); fold q e; unfold hideW in Y5, APT; unfold AS_LO, AS_HEAPLO in Y5;
                                 clear - Hx Y5 APT Y3 CEILS GQ5 GQ6 GMSZ Hn1 GA; lia).
      rewrite NHw by exact HV. apply ZEROq. fold mb msz. exact INM.
    - (* [comment removed for export] *)
      intros _ x Hx. fold nres lo in Hx.
      rewrite VISD3 by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NH3S; exact Hx).
      apply (proj2 SUMr3). rewrite NHw3 by (rewrite <- (Z_to_bv_bv_unsigned 64 x); apply NH3S; exact Hx). rewrite (M4z x Hx). discriminate.
    - intros k0 v Hin. fold S.
      pose proof (ma_slotsA_range S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) k0 v Hin) as [Hka Hkb].
      apply STKQ; [clear - Hka; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hkb; lia | exact (FA k0 v Hin)].
    - intros k0 v Hin. fold S.
      assert (Hk : -56 <= k0 /\ k0 + 8 <= 0) by (clear - Hin; cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply STKQ; [clear - Hk; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hk; lia | exact (FI k0 v Hin)].
    - exact E1.
    - exact E2.
    - exact E10.
    - exact E11.
    - exact (proj1 SZ1).
    - rewrite (EK 4%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). exact C4.
    - rewrite (EK 3%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). exact C3.
    - exact E8.
    - exact E9.
    - exact E18.
    - exact E19.
    - rewrite E20. exact EQ20.
    - rewrite E21. exact EQ21.
    - exact E22.
    - exact E23.
    - exact E24.
    - rewrite E25. exact EQ25.
    - rewrite (EK 26%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). rewrite C26. reflexivity.
    - rewrite (EK 27%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 10). exact C27.
    - exact CONT.
  Qed.
End TOPSG.
End WithCeil.
