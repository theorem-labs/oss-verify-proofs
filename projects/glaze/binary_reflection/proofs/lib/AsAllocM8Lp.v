(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM8Rp.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM7j OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM7r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section RFR.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HRF : code_ato segs rb 0x509cc rf_words.
  Hypothesis HGF : code_ato segs rb 0x50acc gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x50c74 0x50c84 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache pc alloc : word) (c mc SPB nf : Z) (msk stv : word) (faf : Z -> Z).
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (SPB + 2 ^ 37 + 128 * c)).
  #[local] Abbreviation FABz := (SPB + c * 2 ^ 32 + 3758096384)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = cache.
  Hypothesis H11 : getr regs 11 = pc.
  Hypothesis H12 : getr regs 12 = alloc.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 c.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-160)) 160 = true.          (* [comment removed for export] *)
  Hypothesis G1 : (SPB + 2 ^ 37 + 4096 + 160 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gpc : (U cache + 2640 <= U sp - 160)%Z /\ (U pc = U cache + 80 * c)%Z /\ (1 <= c <= 30)%Z /\ (U cache mod 4 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis GcT : (U cache + 2640 <= SPB \/ SPB + 2 ^ 37 + 4096 <= U cache)%Z.
  Hypothesis GcI : (AIMGHI <= U cache \/ U cache + 2640 <= AIMGLO)%Z.
  Hypothesis Galloc : (AIMGLO <= U alloc /\ U alloc + 56 <= AIMGHI)%Z.
  Hypothesis GSPB : (0 <= SPB)%Z /\ (SPB + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (SPB mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= SPB)%Z.
  (* [comment removed for export] *)
  Hypothesis Rspb : rdn segs mem (at_ alloc 32) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis Rrib : rdn segs mem (at_ alloc 48) 8 = Some (LE8 (Z_to_bv 64 (SPB + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis SOKpc : store_ok segs mem pc 48 = true.                      (* [comment removed for export] *)

  Hypothesis Hmc : (2 <= mc <= 16)%Z /\ (mc mod 2 = 0)%Z.
  Hypothesis Hmn : (mc / 2 <= nf)%Z.
  Hypothesis Hnf : (nf <= 2 ^ 27)%Z.
  Hypothesis Rmc : rdn segs mem (at_ pc 4) 4 = Some (LE4 mc).
  Hypothesis Hfaf : forall j, (nf - mc / 2 <= j < nf)%Z -> rdn segs mem (Z_to_bv 64 (FABz + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.

  Lemma gf_cp_gh : forall (r1 : bvmap 5 word) (M1 : word -> option byte) (ra1 sp1 chp : word) (m : Z) (i : nat),
    gf_cp r1 M1 ra1 sp1 chp c m SPB nf faf i = gh_cp (gf_m2 r1 M1 ra1 sp1 c m SPB nf) chp faf (nf - m) i.
  Proof using. intros r1 M1 ra1 sp1 chp m i. induction i as [|i IH]; [reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [gf_cp gh_cp] in G in change_no_check G' end). rewrite IH. reflexivity. Qed.

  Lemma gf_m5_gh : forall (r1 : bvmap 5 word) (M1 : word -> option byte) (ra1 sp1 chp : word) (m : Z),
    (0 <= RIz)%Z -> (RIz + 128 < 2 ^ 64)%Z ->
    gf_m5 r1 M1 ra1 sp1 chp c m SPB nf stv faf
    = gh_m5 (gfp_m1 M1 sp1 ra1 (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) (getr r1 22) (getr r1 23)
                    (getr r1 24) (getr r1 25) (getr r1 26) (getr r1 27) RIz) chp stv faf RIz nf m.
  Proof using mc cache rb.
    intros r1 M1 ra1 sp1 chp m R0 R1.
    assert (E16 : at_ RI 16 = Z_to_bv 64 (RIz + 16)) by (apply bv_eq; rewrite at_u by (wd_ulia); unorm; reflexivity).
    assert (E72 : at_ RI 72 = Z_to_bv 64 (RIz + 72)) by (apply bv_eq; rewrite at_u by (wd_ulia); unorm; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold gf_m5, gf_m4, gh_m5, gh_m4 in G in change_no_check G' end). rewrite gf_cp_gh. (lazymatch goal with |- ?G => let G' := eval unfold gf_m2, gh_m2, gfp_m1, gf_frame, gfp_frame in G in change_no_check G' end). rewrite E16, E72. reflexivity.
  Qed.

  Theorem refill_run_x :
    exists r',
      msteps segs (mkst regs (at_ rb 0x509cc) mem rom)
                  (mkst r' ra (r2_mem (r1_mem mem sp ra (getr regs 8) (getr regs 9) (at_ rb 0x50a0c) pc (Z_to_bv 64 (mc / 2))
                                              (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
                                              (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz)
                                      pc stv faf RIz nf (mc / 2)) rom)
      /\ getr r' 10 = Z_to_bv 64 1 /\ getr r' 2 = sp /\ getr r' 8 = getr regs 8 /\ getr r' 9 = getr regs 9 /\ getr r' 1 = ra
      /\ regs_agree (fun i : reg => In i rf_clob) regs r'.
  Proof using Hfaf Rmc Hnf Hmn Hmc SOKpc Rmsk SOKst Rst SOKnf Rnf SOKmu Rmu Rrib Rspb GSPB Galloc GcI GcT Gpc G1 Hstk H13 H12 H11 H10 H2 H1 Hret msk alloc cache Ggm GMSK gmsk RB HGF HRF.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3 & Gp4). destruct GSPB as (S1 & S2 & S3 & S4). destruct Galloc as [Ga1 Ga2]. destruct Ggm as [Gg1 Gg2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc). pose proof (u64_range alloc).
    assert (G1r : (2 ^ 32 + 32 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z) by lia.
    assert (Gpc' : (U cache + 2640 <= U sp - 32)%Z /\ (U pc = U cache + 80 * c)%Z /\ (1 <= c <= 30)%Z) by lia.
    assert (Hstk32 : store_ok segs mem (at_ sp (-32)) 32 = true).
    { eapply (store_ok_sub segs mem (at_ sp (-160)) _ 160); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (rf_pro segs rb HRF regs mem rom ra sp cache pc alloc c mc H1 H2 H10 H11 H12 H13 Hmc Hstk32 G1r Gpc' Rmc)
      as (r1 & RUN1 & A1 & A2 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & AG1).
    set (m := (mc / 2)%Z) in *.
    assert (Hm : (1 <= m <= 8)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold m in G in change_no_check G' end); clear - Hmc; Z.div_mod_to_equations; lia).
    set (M1 := rf_m1 regs mem ra sp) in *.
    assert (GR1 : mem_grows mem M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply rf_m1_grows).
    assert (OUT1 : forall x : word, (U x < U sp - 32 \/ U sp <= U x)%Z -> M1 x = mem x) by (intros x Hx; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply (rf_m1_outside rb regs mem ra sp G1r); exact Hx).
    assert (Hc : (1 <= c <= 30)%Z) by lia.
    assert (Hm' : (1 <= m <= 8)%Z /\ (m <= nf)%Z /\ (nf <= 2 ^ 27)%Z) by lia.
    assert (GSPB' : (0 <= SPB)%Z /\ (SPB + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (SPB mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= SPB)%Z) by lia.
    assert (G1' : (SPB + 2 ^ 37 + 4096 + 128 <= U (at_ sp (-32)))%Z /\ (U (at_ sp (-32)) + 16 <= 2 ^ 47)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Galloc' : (AIMGLO <= U alloc /\ U alloc + 56 <= AIMGHI)%Z) by lia.
    assert (Uchp : U (at_ pc 16) = (U cache + 80 * c + 16)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Gchp' : (U (at_ pc 16) mod 4 = 0)%Z /\ (U (at_ pc 16) + 64 <= U (at_ sp (-32)) - 128)%Z
                    /\ (U (at_ pc 16) + 64 <= SPB \/ SPB + 2 ^ 37 + 4096 <= U (at_ pc 16))%Z /\ (AIMGHI <= U (at_ pc 16) \/ U (at_ pc 16) + 64 <= AIMGLO)%Z).
    { rewrite Uchp, at_u by lia. split; [clear - Gp4 Hc; Z.div_mod_to_equations; lia|]. lia. }
    assert (Hret1 : ret_ok (at_ rb 0x50a0c)) by (pose proof RB as [Eb1 Eb2]; pose proof (u64_range rb); apply ret_ok_at; [exact Eb1 | reflexivity | lia]).
    Ltac cellM1x R OUT1 := rewrite <- R; apply rdn_ext; [rewrite ?at_u by (wd_ulia); wd_ulia_c | intros x Hx; rewrite ?at_u in Hx by (wd_ulia); revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; apply OUT1; lia].
    destruct (gf_run segs rb HGF RB gmsk GMSK (conj Gg1 Gg2) r1 M1 rom (at_ rb 0x50a0c) (at_ sp (-32)) alloc (at_ pc 16) c m SPB nf msk stv
                Hret1 A1 A2 A10 A12 A13 A14 Hc Hm' GSPB' G1' Galloc' Gchp') with (faf := faf) as (r2 & RUN2 & B10 & B2 & AG2).
    { rewrite at_at. eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub segs mem (at_ sp (-160)) _ 160); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { cellM1x Rspb OUT1. } { cellM1x Rrib OUT1. } { cellM1x Rmu OUT1. }
    { eapply store_ok_mono; [exact GR1 | exact SOKmu]. }
    { cellM1x Rnf OUT1. } { eapply store_ok_mono; [exact GR1 | exact SOKnf]. }
    { cellM1x Rst OUT1. } { eapply store_ok_mono; [exact GR1 | exact SOKst]. }
    { cellM1x Rmsk OUT1. }
    { eapply store_ok_mono; [exact GR1|]. eapply (store_ok_sub segs mem pc _ 48); [lia | exact SOKpc | rewrite at_u; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]. }
    { intros j Hj. destruct (Hfaf j Hj) as [R B]. split; [|exact B]. cellM1x R OUT1. }
    set (M2 := gf_m5 r1 M1 (at_ rb 0x50a0c) (at_ sp (-32)) (at_ pc 16) c m SPB nf stv faf) in RUN2.
    assert (OUT2 : forall x : word,
              (U x < U sp - 160 \/ U sp - 32 <= U x)%Z -> (U x < RIz \/ RIz + 8 <= U x)%Z -> (U x < RIz + 16 \/ RIz + 24 <= U x)%Z ->
              (U x < RIz + 72 \/ RIz + 80 <= U x)%Z -> (U x < U pc + 16 \/ U pc + 16 + 4 * m <= U x)%Z -> M2 x = M1 x).
    { intros x F1 F2 F3 F4 F5. (lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end). apply (gf_m5_outside rb r1 M1 (at_ rb 0x50a0c) (at_ sp (-32)) (at_ pc 16) c m SPB nf stv Hc Hm' GSPB' G1' Gchp' faf);
        first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ]. }
    assert (GR2 : mem_grows M1 M2) by ((lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end); apply gf_m5_grows).
    destruct (rf_epi segs rb HRF RB regs rom ra sp cache pc c (2 * m) Hret ltac:(clear - Hm; Z.div_mod_to_equations; lia) ltac:(lia) ltac:(lia)
                M2 r2 (Z_to_bv 64 1)) as (r3 & RUN3 & C10 & C2 & C8 & C9 & C1 & CK).
    { rewrite (AG2 1) by notin. exact A1. } { exact B2. } { rewrite (AG2 8) by notin. exact A8. }
    { rewrite (AG2 9) by notin. rewrite A9. f_equal. clear - Hm. Z.div_mod_to_equations. lia. }
    { exact B10. } { unorm. lia. }
    { rewrite at_0. eapply store_ok_mono; [eapply mem_grows_trans; [exact GR1 | exact GR2]|].
      eapply (store_ok_sub segs mem pc _ 48); [lia | exact SOKpc | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { intros k v Hin. rewrite <- (rf_m1_slots segs rb regs mem ra sp G1r k v Hin). fold M1.
      assert (Hk : (-24 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT2; lia. }
    { lia. }
    replace (2 * m / 2)%Z with m in RUN3 by (clear - Hm; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    assert (EM : wbytes M2 pc (LE4 m) = r2_mem (r1_mem mem sp ra (getr regs 8) (getr regs 9) (at_ rb 0x50a0c) pc (Z_to_bv 64 m)
                                              (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23)
                                              (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz) pc stv faf RIz nf m).
    { (lazymatch goal with |- ?G => let G' := eval unfold M2 in G in change_no_check G' end). rewrite gf_m5_gh by lia. rewrite A8, A9.
      rewrite !(AG1 _) by notin. reflexivity. }
    rewrite EM in RUN3.
    exists r3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]|].
    split; [exact C10|]. split; [exact C2|]. split; [exact C8|]. split; [exact C9|]. split; [exact C1|].
    intros i Hni. destruct (In_dec (fun x y : reg => decide (x = y)) i [1; 2; 8; 9]) as [Hin|Hnin].
    - cbn [In] in Hin. destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; [rewrite C1; symmetry; exact H1 | rewrite C2; symmetry; exact H2 | exact C8 | exact C9].
    - rewrite CK by exact Hnin. rewrite (AG2 i) by exact Hni. apply AG1. intros Hin; cbn [In] in Hin, Hnin; unfold rf_clob in Hni; cbn [In] in Hni; clear - Hin Hnin Hni; am_tauto.
  Qed.
End RFR.
End FPGen1.
End AsAllocM8Rp.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsanNodesLibE.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsR3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsP33 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleU3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvHoleP3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsRc73.AsAinvRepX3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocMHypR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM7j OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvOpsCI3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM8m OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8k OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e.AsAllocM8p OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9c.AsAllocM8q OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8r OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u.AsAllocM8t OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8u OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8v OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8w OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8x OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8y OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8z OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS2.AsAllocM8xp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8pa OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM8h OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8n OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8La OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Lb OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc.AsAllocM8Lk OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Ld OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg.AsAllocM8Le.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lh. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMRunS1.AsAllocM7r AsAllocM8Rp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lg OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Lh.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
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





Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).


Section WithCeil.
Context {RC : run_ceil}.
Context {fx : FPState}.

Section L3.
  Variable bt : as_boot.
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Variables (TP TSDP PGP FL MIDEND : Z).
  Hypothesis CELLS : malloc_cells bt TP TSDP PGP FL MIDEND.
  Hypothesis PCELLS : pop_cells bt.
  Variable X : Z -> Prop.
  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).
  #[local] Abbreviation SBEG := (bt_spacebeg bt).
  #[local] Abbreviation IA := (bt_ia bt).

  Theorem refill_plain_K :
    forall (K : config -> Prop), liftable K ->
    forall (c : Z) st Lc FF (M : mem) (rom : mem) mdl (regs : bvmap 5 word) (spR raR : word),
    1 <= c <= 30 -> WF bt st Lc FF -> RepX bt X st Lc FF M mdl -> m_halted mdl = None ->
    a_cinit st = true -> a_cache st c = [] ->
    let r := a_reg st c in let nf := Z.of_nat (length (r_free r)) in let m := cache_hint c in
    m <= nf ->
    (forall z, X z -> ~ (reginfo bt c <= z < reginfo bt c + 128) /\ ~ (AIMGLO <= z < AIMGHI) /\ ~ (fa_beg SBEG c <= z < fa_beg SBEG c + 4 * nf)
                      /\ ~ (T <= z < T + 2768)) ->
    getr regs 1 = raR -> getr regs 2 = spR -> getr regs 10 = Z_to_bv 64 (T + T_PC) -> getr regs 11 = Z_to_bv 64 (T + T_PC + PC_SZ * c) ->
    getr regs 12 = Z_to_bv 64 0x103f18 -> getr regs 13 = Z_to_bv 64 c ->
    (CEIL + 160 <= U spR /\ U spR + 16 <= 2 ^ 47) -> ret_ok raR ->
    writableZ ASEGS M (U spR - 160) (U spR) ->
    (forall (r' : bvmap 5 word) (M' : mem) mdl',
        WF bt (op_refill st c m) Lc FF -> RepX bt X (op_refill st c m) Lc FF M' mdl' -> a_cache (op_refill st c m) c <> [] ->
        same_but_materialized mdl mdl' -> MInv (a_aa st) mdl' ->
        (forall a : word, M' a <> M a ->
            ((U spR - 160 <= U a < U spR) \/ (reginfo bt c <= U a < reginfo bt c + 128) \/ (T + T_PC + PC_SZ * c <= U a < T + T_PC + PC_SZ * c + 80)) /\ M' a <> None) ->
        getr r' 10 = Z_to_bv 64 1 -> getr r' 2 = spR -> getr r' 1 = raR -> getr r' 8 = getr regs 8 -> getr r' 9 = getr regs 9 ->
        s_regs r' (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) -> getr r' 4 = getr regs 4 -> getr r' 3 = getr regs 3 ->
        K (mkCfg (mkst r' raR M' rom) mdl')) ->
    K (mkCfg (mkst regs (0x509cc%bv : word) M rom) mdl).
  Proof using PCELLS CELLS MIDEND FL PGP TSDP TP BT_ia BT_segs.
    intros K LK c st Lc FF M rom mdl regs spR raR Hc W RX HALT CINIT HC0 r nf m LE XOFF H1 H2 H10 H11 H12 H13 Hsp HretR WSTK CONT.
    pose proof ceil_rng as CR. destruct Hsp as [SP1 SP2]. pose proof (u64_range spR) as Hspr.
    pose proof RX as (M0 & RP & D).
    pose proof (region_facts bt st Lc FF W c Hc) as RF. cbn zeta in RF. fold r in RF.
    destruct RF as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & _). fold nf in E7.
    pose proof W as ((WR1 & _) & _). destruct (WR1 c Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & Y9 & _). fold r in Y9.
    pose proof (pk_thread_geom bt BT_ia st Lc FF W) as (T1 & T2 & _ & _ & T4k & TIMG & _).
    pose proof (pk_thread_geom2 bt st Lc FF W) as (_ & _ & TSP & _ & S1 & S2 & S3).
    pose proof (fixed_facts bt st Lc FF W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S16).
    pose proof CELLS as CREST. do 18 (destruct CREST as (_ & CREST)). destruct CREST as (CELL_sbeg & _).
    pose proof PCELLS as (_ & PC_rib & _).
    pose proof RP as (_ & _ & R3 & R4 & _ & _ & _ & _ & _ & _ & _ & _ & R13 & R14 & _).
    pose proof R3 as (_ & _ & _ & _ & _ & _ & _ & TPC & _). destruct (TPC c Hc) as (P1 & P2 & P3 & P4). rewrite CINIT in P2.
    destruct R3 as (_ & _ & _ & _ & _ & _ & _ & _ & TW & _).
    destruct (R4 c Hc) as [(G0 & _ & G16 & _ & _ & _ & _ & _ & _ & GW) (F1 & _ & _)]. fold r nf in G16, F1.
    rewrite BT_segs in *. destruct R14 as (Bw1 & Bw2 & _).
    unfold KSPACE, PG, AS_HEAPLO, T_PC, PC_SZ in *.
    set (RIz := reginfo bt c) in *. assert (ERI : RIz = SBEG + 2 ^ 37 + 128 * c) by reflexivity.
    assert (EFAB : fa_beg SBEG c = SBEG + c * 2 ^ 32 + 3758096384) by ((lazymatch goal with |- ?G => let G' := eval unfold fa_beg, region_beg, KREGION, KFAOFF in G in change_no_check G' end); reflexivity).
    assert (Hm : 1 <= m <= 8) by ((lazymatch goal with |- ?G => let G' := eval unfold m, cache_hint in G in change_no_check G' end); lia).
    assert (EMC : cache_max c = 2 * m) by reflexivity.
    assert (EMC2 : cache_max c / 2 = m) by (rewrite EMC, Z.mul_comm; apply Z.div_mul; lia).
    destruct (pos_mod4096 T T1 T4k) as [T4 T8].
    set (faf := fun j : Z => nth (Z.to_nat j) (r_free r) 0).
    assert (FAF : forall j, 0 <= j < nf -> nth_error (r_free r) (Z.to_nat j) = Some (faf j) /\ 0 <= faf j < 2 ^ 32).
    { intros j Hj. assert (NE : nth_error (r_free r) (Z.to_nat j) = Some (faf j)) by ((lazymatch goal with |- ?G => let G' := eval unfold faf in G in change_no_check G' end); apply nth_error_nth'; unfold nf in Hj; lia).
      split; [exact NE|]. exact (proj1 (Y9 (faf j) (nth_error_In _ _ NE))). }
    (* [comment removed for export] *)
    assert (YIMG : forall z, X z -> ~ (AIMGLO <= z < AIMGHI)) by (intros z Hz; exact (proj1 (proj2 (XOFF z Hz)))).
    assert (XRI : forall i, RIz <= i < RIz + 128 -> ~ X i) by (intros i Hi Hx; exact (proj1 (XOFF i Hx) Hi)).
    assert (XFA : forall i, fa_beg SBEG c <= i < fa_beg SBEG c + 4 * nf -> ~ X i) by (intros i Hi Hx; exact (proj1 (proj2 (proj2 (XOFF i Hx))) Hi)).
    assert (XT : forall i, T <= i < T + 2768 -> ~ X i) by (intros i Hi Hx; exact (proj2 (proj2 (proj2 (XOFF i Hx))) Hi)).
    assert (WRI : writableZ ASEGS M RIz (RIz + 128)) by (apply (repx_wr X M M0 D); [lia | lia | exact GW]).
    assert (WT : writableZ ASEGS M T (T + 4096)) by (apply (repx_wr X M M0 D); [lia | lia | exact TW]).
    destruct (pk_junk8 M RIz (RIz + 128) (RIz + 72) WRI ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (stv & RST).
    assert (KMC : rdn ASEGS M (Z_to_bv 64 (T + 208 + 80 * c + 4)) 4 = Some (LE4 (cache_max c)))
      by (apply (repx_rd X M M0 D _ 4 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XT; cbn in Hi; lia | exact P2]).
    assert (KSB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ CELL_sbeg ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)).
    assert (KRIB := pk_const bt BT_segs X st Lc FF M M0 mdl RP D YIMG _ _ _ PC_rib ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia)). unfold KSPACE in KRIB.
    assert (KMTX : rdn ASEGS M (Z_to_bv 64 RIz) 8 = Some (LE8 (Z_to_bv 64 0)))
      by (apply (repx_rd X M M0 D RIz 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G0]).
    assert (KNF : rdn ASEGS M (Z_to_bv 64 (RIz + 16)) 8 = Some (LE8 (Z_to_bv 64 nf)))
      by (apply (repx_rd X M M0 D (RIz + 16) 8 _); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact G16]).
    (* [comment removed for export] *)
    set (Hd := HID st mdl).
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ AIMGLO <= z < AIMGHI) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st mdl z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). clear - Hr. lia. }
    assert (NHri : forall z, RIz <= z < RIz + 128 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (rep_nolazy_reginfo bt st Lc FF M0 mdl W RP). (lazymatch goal with |- ?G => let G' := eval unfold KSPACE, PG in G in change_no_check G' end). lia. }
    assert (NHrt : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (pk_nolazy_rt bt st Lc FF M0 mdl W RP z). left. exact Hz. }
    assert (NHfa : forall z, fa_beg SBEG c <= z < fa_beg SBEG c + r_mapped_fa r -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [rewrite EFAB in Hz; lia|]. apply (rep_nolazy_fa bt st Lc FF M0 mdl W RP c); [exact Hc | exact Hz]. }
    assert (HOFF : forall lo0 n, (forall z, lo0 <= z < lo0 + n -> Hd (Z_to_bv 64 z) = false) -> hid_off Hd lo0 n).
    { intros lo0 n Hz x Hx. rewrite <- (Z_to_bv_bv_unsigned _ x). apply Hz. exact Hx. }
    set (Mr := mrestrict Hd M).
    assert (RDM : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) ->
               rdn ASEGS M (Z_to_bv 64 z) k = Some v -> rdn ASEGS Mr (Z_to_bv 64 z) k = Some v).
    { intros z k v Z0 Z1 Hh0 Hr. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite rdn_mrestrict; [exact Hr | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; apply HOFF; exact Hh0]. }
    assert (SOKM : forall z (k : nat) lo hi, writableZ ASEGS M lo hi -> 0 <= z -> lo <= z -> z + Z.of_nat k <= hi -> hi < 2 ^ 64 ->
               (forall i, z <= i < z + Z.of_nat k -> Hd (Z_to_bv 64 i) = false) -> store_ok ASEGS Mr (Z_to_bv 64 z) k = true).
    { intros z k lo hi WR Z0 L0 L1 H1' Hh0. (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end).
      rewrite store_ok_mrestrict; [apply (writableZ_sok M lo hi); [exact WR | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; lia | lia]
                                  | rewrite u_Z2bv by lia; lia | rewrite u_Z2bv by lia; apply HOFF; exact Hh0]. }
    set (cache := Z_to_bv 64 (T + 208) : word). set (pc := Z_to_bv 64 (T + 208 + 80 * c) : word). set (alloc := Z_to_bv 64 0x103f18 : word).
    assert (Ucache : U cache = T + 208) by ((lazymatch goal with |- ?G => let G' := eval unfold cache in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Upc : U pc = T + 208 + 80 * c) by ((lazymatch goal with |- ?G => let G' := eval unfold pc in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (Ualloc : U alloc = 0x103f18) by reflexivity.
    assert (EA : forall (b : word) k z, U b = z -> 0 <= z + k < 2 ^ 64 -> at_ b k = Z_to_bv 64 (z + k)).
    { intros b k z Eb Hk. apply bv_eq. pose proof (u64_range b). rewrite at_u by lia. rewrite u_Z2bv by lia. lia. }
    (* [comment removed for export] *)
    assert (Q_stk : store_ok ASEGS Mr (at_ spR (-160)) 160 = true).
    { rewrite (EA spR (-160) (U spR) eq_refl ltac:(lia)). apply (SOKM _ 160%nat (U spR - 160) (U spR) WSTK); [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia |]. intros i Hi. apply NHs; cbn in Hi; lia. }
    assert (Q_spb : rdn ASEGS Mr (at_ alloc 32) 8 = Some (LE8 (Z_to_bv 64 SBEG))).
    { rewrite (EA alloc 32 _ Ualloc ltac:(lia)). apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KSB]. }
    assert (Q_rib : rdn ASEGS Mr (at_ alloc 48) 8 = Some (LE8 (Z_to_bv 64 (SBEG + 2 ^ 37)))).
    { rewrite (EA alloc 48 _ Ualloc ltac:(lia)). apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHs; cbn in Hi; lia | exact KRIB]. }
    assert (URI : U (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c) : word) = RIz) by (rewrite u_Z2bv by lia; lia).
    assert (Q_mu : rdn ASEGS Mr (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 8 = Some (LE8 (Z_to_bv 64 0))).
    { rewrite <- ERI. apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KMTX]. }
    assert (Q_smu : store_ok ASEGS Mr (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 8 = true).
    { rewrite <- ERI. apply (SOKM _ 8%nat RIz (RIz + 128) WRI); [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia |]. intros i Hi. apply NHri; cbn in Hi; lia. }
    assert (Q_nf : rdn ASEGS Mr (at_ (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 16) 8 = Some (LE8 (Z_to_bv 64 nf))).
    { rewrite (EA _ 16 _ URI ltac:(lia)). apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHri; cbn in Hi; lia | exact KNF]. }
    assert (Q_snf : store_ok ASEGS Mr (at_ (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 16) 8 = true).
    { rewrite (EA _ 16 _ URI ltac:(lia)). apply (SOKM _ 8%nat RIz (RIz + 128) WRI); [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia |]. intros i Hi. apply NHri; cbn in Hi; lia. }
    assert (Q_st : rdn ASEGS Mr (at_ (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 72) 8 = Some (LE8 stv)).
    { rewrite (EA _ 72 _ URI ltac:(lia)). apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHri; cbn in Hi; lia | exact RST]. }
    assert (Q_sst : store_ok ASEGS Mr (at_ (Z_to_bv 64 (SBEG + 2 ^ 37 + 128 * c)) 72) 8 = true).
    { rewrite (EA _ 72 _ URI ltac:(lia)). apply (SOKM _ 8%nat RIz (RIz + 128) WRI); [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia |]. intros i Hi. apply NHri; cbn in Hi; lia. }
    destruct (asan_mask_rdn Mr) as (msk & RMSK).
    assert (Q_spc : store_ok ASEGS Mr pc 48 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold pc in G in change_no_check G' end). apply (SOKM _ 48%nat T (T + 4096) WT); [lia | lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | lia |]. intros i Hi. apply NHrt; cbn in Hi; lia. }
    assert (Q_mc : rdn ASEGS Mr (at_ pc 4) 4 = Some (LE4 (cache_max c))).
    { rewrite (EA pc 4 _ Upc ltac:(lia)). apply RDM; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHrt; cbn in Hi; lia | exact KMC]. }
    assert (Q_faf : forall j, nf - cache_max c / 2 <= j < nf ->
               rdn ASEGS Mr (Z_to_bv 64 (SBEG + c * 2 ^ 32 + 3758096384 + 4 * j)) 4 = Some (LE4 (faf j)) /\ 0 <= faf j < 2 ^ 32).
    { rewrite EMC2. intros j Hj. destruct (FAF j ltac:(lia)) as [NE BD]. split; [| exact BD].
      replace (SBEG + c * 2 ^ 32 + 3758096384 + 4 * j) with (fa_beg SBEG c + 4 * Z.of_nat (Z.to_nat j)) by (rewrite EFAB; lia).
      apply RDM; [rewrite EFAB; lia | rewrite EFAB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply NHfa; cbn in Hi; lia |].
      apply (repx_rd X M M0 D _ 4 _); [rewrite EFAB; lia | rewrite EFAB; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XFA; cbn in Hi; lia | exact (F1 _ _ NE)]. }
    destruct (refill_run_x ASEGS ARB asan_HRF asan_HGF ARB_ok 0x10470 asan_GMSK ltac:(lia) regs Mr rom raR spR cache pc alloc c (cache_max c) SBEG nf msk stv faf
                HretR H1 H2 H10 H11 H12 H13 Q_stk ltac:(lia)
                ltac:(rewrite Ucache, Upc; repeat split; try lia; clear - T4k; Z.div_mod_to_equations; lia)
                ltac:(rewrite Ucache; clear - TSP; lia) ltac:(rewrite Ucache; clear - TIMG; lia) ltac:(rewrite Ualloc; lia)
                ltac:(split; [lia | split; [lia | split; [exact S16 | lia]]])
                Q_spb Q_rib Q_mu Q_smu Q_nf Q_snf Q_st Q_sst RMSK Q_spc
                ltac:(rewrite EMC; split; [lia | rewrite Z.mul_comm; apply Z_mod_mult]) ltac:(rewrite EMC2; exact LE) ltac:(lia) Q_mc Q_faf)
      as (r2 & RUN & Q10 & Q2 & Q8 & Q9 & Q1 & QAG).
    rewrite EMC2 in RUN. rewrite <- ERI in RUN.
    set (MA := r1_mem M spR raR (getr regs 8) (getr regs 9) (at_ ARB 0x50a0c) pc (Z_to_bv 64 m) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                 (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz).
    set (M' := r2_mem MA pc stv faf RIz nf m).
    assert (EM : r2_mem (r1_mem Mr spR raR (getr regs 8) (getr regs 9) (at_ ARB 0x50a0c) pc (Z_to_bv 64 m) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                           (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz) pc stv faf RIz nf m = mrestrict Hd M').
    { (lazymatch goal with |- ?G => let G' := eval unfold Mr in G in change_no_check G' end). rewrite (r1_mem_mrestrict M spR raR (getr regs 8) (getr regs 9) (at_ ARB 0x50a0c) pc (Z_to_bv 64 m) (getr regs 18) (getr regs 19) (getr regs 20)
                            (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) RIz ltac:(lia) ltac:(lia) Hd
                            ltac:(apply HOFF; intros z Hz; apply NHs; lia) ltac:(apply HOFF; intros z Hz; apply NHri; lia)).
      fold MA. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). apply (r2_mem_mrestrict MA pc stv faf RIz nf m Hm ltac:(rewrite Upc; lia) ltac:(lia) Hd
                                  ltac:(rewrite Upc; apply HOFF; intros z Hz; apply NHrt; lia) ltac:(apply HOFF; intros z Hz; apply NHri; lia)). }
    rewrite EM in RUN.
    rewrite (ARB_lit8 0x509cc) in RUN by lia.
    replace (Z_to_bv 64 0x509cc : word) with (0x509cc%bv : word) in RUN by (apply bv_eq; reflexivity).
    assert (OUTM : forall a : word, (U a < U spR - 160 \/ U spR <= U a) -> (U a < RIz \/ RIz + 128 <= U a) ->
               (U a < T + 208 + 80 * c \/ T + 208 + 80 * c + 80 <= U a) -> M' a = M a).
    { intros a A1 A2 A3. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite r2_mem_outside by (rewrite ?Upc; first [exact Hm | lia]).
      (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). apply r1_mem_outside; first [lia | exact A1]. }
    assert (OUTM_ri : forall a : word, RIz + 8 <= U a < RIz + 128 -> (U a < RIz + 16 \/ RIz + 24 <= U a) -> (U a < RIz + 72 \/ RIz + 80 <= U a) -> M' a = M a).
    { intros a A1 A2 A3. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite r2_mem_outside by (rewrite ?Upc; first [exact Hm | lia | clear - A1 TSP ERI Hc; lia]).
      (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). apply r1_mem_outside; first [lia | clear - A1 E10 S2 SP1 ERI; lia]. }
    assert (OUTM_pc : forall a : word, T + 208 + 80 * c <= U a < T + 208 + 80 * c + 80 -> (U a < T + 208 + 80 * c \/ T + 208 + 80 * c + 4 <= U a) ->
               (U a < T + 208 + 80 * c + 16 \/ T + 208 + 80 * c + 16 + 4 * m <= U a) -> M' a = M a).
    { intros a A1 A2 A3. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite r2_mem_outside by (rewrite ?Upc; first [exact Hm | lia | clear - A1 TSP ERI Hc; lia]).
      (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). apply r1_mem_outside; first [lia | clear - A1 T2 SP1 Hc; lia | clear - A1 TSP ERI Hc; lia]. }
    assert (GRM : mem_grows M M').
    { apply (mem_grows_trans M MA M'); [(lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply r1_mem_grows | (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end); apply r2_mem_grows]. }
    apply (LK Hd (HID_off_segments bt st Lc FF M0 mdl BT_ia RP) asanF_segs_wx (a_aa st) regs _ r2 _ M M' rom mdl RUN); [ | exact HALT | apply lazy_cover_HID | exact Bw1 | exact Bw2 | ].
    - intros a Ha. apply OUTM.
      + pose proof (hid_true_off Hd a (U spR - 160) 160 Ha ltac:(apply HOFF; intros z Hz; apply NHs; lia)). lia.
      + pose proof (hid_true_off Hd a RIz 128 Ha ltac:(apply HOFF; intros z Hz; apply NHri; lia)). lia.
      + pose proof (hid_true_off Hd a (T + 208 + 80 * c) 80 Ha ltac:(apply HOFF; intros z Hz; apply NHrt; lia)). lia.
    - intros mdlm SBM MIm.
      assert (FOOTM : forall a : word, M' a <> M a ->
                ((U spR - 160 <= U a < U spR) \/ (RIz <= U a < RIz + 128) \/ (T + 208 + 80 * c <= U a < T + 208 + 80 * c + 80)) /\ M' a <> None).
      { intros a Ha.
        assert (IN : ((U spR - 160 <= U a < U spR) \/ (RIz <= U a < RIz + 128) \/ (T + 208 + 80 * c <= U a < T + 208 + 80 * c + 80))
                     \/ ((U a < U spR - 160 \/ U spR <= U a) /\ (U a < RIz \/ RIz + 128 <= U a) /\ (U a < T + 208 + 80 * c \/ T + 208 + 80 * c + 80 <= U a))) by (clear; lia).
        destruct IN as [IN | (O1 & O2 & O3)]; [| exfalso; exact (Ha (OUTM a O1 O2 O3))]. split; [exact IN|].
        apply GRM.
        destruct IN as [I1 | [I2 | I3]]; [destruct (WSTK (U a) I1) as [Dd _] | destruct (WRI (U a) I2) as [Dd _] | destruct (WT (U a) ltac:(clear - I3 Hc; lia)) as [Dd _]];
          rewrite Z_to_bv_bv_unsigned in Dd; exact Dd. }
      destruct (r2_mem_rd ASEGS MA pc stv faf RIz nf m Hm ltac:(rewrite Upc; lia) ltac:(lia) ltac:(rewrite Upc; clear - TSP ERI Hc; lia)) as (RDcnt & RDlock & RDnf & RDch).
      fold M' in RDcnt, RDlock, RDnf, RDch.
      assert (W2 : WF bt (op_refill st c m) Lc FF) by (apply (OPS_WF_refill_pf bt st Lc FF c m W Hc HC0 CINIT eq_refl); exact LE).
      apply (CONT r2 M' mdlm W2).
      + apply (AsAinvOpsRc73.AsAinvRepX3.RepX_mono bt (fun z => X z /\ ~ False) X); [intros z [Hx _]; exact Hx|].
        apply (repx_step bt X (fun _ => False)
                 (fun z => (U spR - 160 <= z < U spR) \/ (RIz <= z < RIz + 128) \/ (T + 208 + 80 * c <= z < T + 208 + 80 * c + 80)) Xdec_false
                 st (op_refill st c m) Lc Lc FF FF M M' mdl mdlm RX FOOTM); [intros a []|].
        intros N0 N0' RPn Dn DIFF EQ SAME.
        assert (EQF : forall a : word, ~ X (U a) -> N0' a = M' a) by (intros a Ha; apply EQ; left; exact Ha).
        assert (KEEP : forall a : word, ~ X (U a) -> M' a = M a -> N0' a = N0 a).
        { intros a NX EM'. rewrite (EQF a NX), EM'. exact (repx_off X M N0 Dn a NX). }
        assert (RDN : forall z (k : nat) v, 0 <= z -> z + Z.of_nat k < 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ X i) ->
                   rdn ASEGS M' (Z_to_bv 64 z) k = Some v -> rdn ASEGS N0' (Z_to_bv 64 z) k = Some v).
        { intros z k v Z0 Z1 OFF Hr. rewrite <- Hr. apply rdn_ext; [rewrite u_Z2bv by lia; lia|]. intros x Hx. rewrite u_Z2bv in Hx by lia. apply EQF. apply OFF. exact Hx. }
        apply (OPS_REP_refill_pf bt st Lc FF N0 N0' mdl mdlm c m W RPn Hc HC0 CINIT eq_refl LE); rewrite ?BT_segs; fold r nf RIz.
        * intros a Ha. destruct (DIFF a Ha) as [F Dd]. split; [| exact Dd]. (lazymatch goal with |- ?G => let G' := eval unfold foot_refill in G in change_no_check G' end). fold RIz. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end).
          destruct F as [[F | [F | F]] | []].
          -- right; right; right; right; right; right. lia.
          -- destruct (Z_lt_le_dec (U a) (RIz + 8)) as [C1|C1]; [left; lia|].
             destruct (Z_lt_le_dec (U a) (RIz + 16)) as [C2|C2].
             { exfalso. apply Ha. apply KEEP; [apply XRI; lia|]. apply OUTM_ri; lia. }
             destruct (Z_lt_le_dec (U a) (RIz + 24)) as [C3|C3]; [right; left; lia|].
             destruct (Z_lt_le_dec (U a) (RIz + 72)) as [C4|C4]; [| right; right; left; lia].
             exfalso. apply Ha. apply KEEP; [apply XRI; lia|]. apply OUTM_ri; lia.
          -- destruct (Z_lt_le_dec (U a) (T + 208 + 80 * c + 4)) as [C1|C1]; [right; right; right; left; lia|].
             destruct (Z_lt_le_dec (U a) (T + 208 + 80 * c + 16)) as [C2|C2].
             { exfalso. apply Ha. apply KEEP; [apply XT; clear - F Hc; lia|]. apply OUTM_pc; lia. }
             destruct (Z_lt_le_dec (U a) (T + 208 + 80 * c + 16 + 4 * m)) as [C3|C3]; [right; right; right; right; left; lia|].
             exfalso. apply Ha. apply KEEP; [apply XT; clear - F Hc; lia|]. apply OUTM_pc; lia.
        * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact RDlock].
        * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XRI; cbn in Hi; lia | exact RDnf].
        * (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, T_PC, PC_SZ in G in change_no_check G' end). apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; apply XT; cbn in Hi; clear - Hi Hc; lia | exact RDcnt].
        * intros i k Hnth.
          pose proof (split_keep_taken (r_free r) m ltac:(fold nf; lia)) as SPL. cbn zeta in SPL. fold nf in SPL. destruct SPL as (_ & _ & LT & _ & NT).
          rewrite NT in Hnth.
          assert (Hi : Z.of_nat i < m).
          { assert (Z.to_nat (nf - m) + i < length (r_free r))%nat by (apply nth_error_Some; rewrite Hnth; discriminate). unfold nf in *. lia. }
          assert (Ek : k = faf (nf - m + Z.of_nat i)).
          { (lazymatch goal with |- ?G => let G' := eval unfold faf in G in change_no_check G' end). replace (Z.to_nat (nf - m + Z.of_nat i)) with (Z.to_nat (nf - m) + i)%nat by lia. symmetry. apply nth_error_nth. exact Hnth. }
          (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, T_PC, PC_SZ in G in change_no_check G' end). rewrite Ek.
          pose proof (RDch i Hi) as RCh.
          replace (at_ pc (16 + 4 * Z.of_nat i)) with (Z_to_bv 64 (T + 208 + 80 * c + 16 + 4 * Z.of_nat i)) in RCh
            by (apply bv_eq; rewrite at_u by lia; rewrite Upc, u_Z2bv by lia; lia).
          apply RDN; [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros j Hj; apply XT; cbn in Hj; clear - Hj Hc Hi Hm; lia | exact RCh].
        * exact SBM.
        * exact MIm.
      + apply refill_cache_ne. fold r nf. lia.
      + exact SBM.
      + exact MIm.
      + intros a Ha. destruct (FOOTM a Ha) as [F Dd]. split; [| exact Dd]. fold RIz. (lazymatch goal with |- ?G => let G' := eval unfold T_PC, PC_SZ in G in change_no_check G' end). exact F.
      + exact Q10.
      + exact Q2.
      + exact Q1.
      + exact Q8.
      + exact Q9.
      + (lazymatch goal with |- ?G => let G' := eval unfold s_regs in G in change_no_check G' end). repeat split; apply QAG; (lazymatch goal with |- ?G => let G' := eval unfold AsAllocM8Rm.AsAllocM7g.rf_clob in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); intros Xi; repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]); exact Xi.
      + apply QAG. (lazymatch goal with |- ?G => let G' := eval unfold AsAllocM8Rm.AsAllocM7g.rf_clob in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros Xi. repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]). exact Xi.
      + apply QAG. (lazymatch goal with |- ?G => let G' := eval unfold AsAllocM8Rm.AsAllocM7g.rf_clob in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end). intros Xi. repeat (destruct Xi as [Xi|Xi]; [discriminate Xi|]). exact Xi.
  Qed.
End L3.
End WithCeil.
