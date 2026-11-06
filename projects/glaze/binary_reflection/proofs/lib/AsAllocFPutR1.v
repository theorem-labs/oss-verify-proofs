(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocF5s.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AsanAcctShape.DivergeSim.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Section ENQSPIN.
  Variables (mem rom : word -> option byte).
  Variable regs : bvmap 5 word.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0.
  Hypothesis Rg1 : rdn ASEGS mem (Z_to_bv 64 0xff2b0) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis Rg2 : rdn ASEGS mem (Z_to_bv 64 0xff2b8) 8 = Some (LE8 (Z_to_bv 64 0x19909c)).
  Hypothesis Rdy : rdn ASEGS mem (Z_to_bv 64 0x19909c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  Lemma enq_spin_run : exists r, msteps ASEGS (mkst regs (0x501ec : word) mem rom) (mkst r (0x50228 : word) mem rom).
  Proof using Rdy Rg2 Rg1 H10.
    assert (V0 : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 0)) = bv_unsigned (Z_to_bv 64 0)) by (apply bytes4_small; lia).
    wd_eexists.
    an F_501e4 D_501e4.                                (* [comment removed for export] *)
    ab_tk F_501e8 D_501e8 ltac:(condz).                (* [comment removed for export] *)
    an F_50204 D_50204.                                (* [comment removed for export] *)
    cld8 F_50208 D_50208 (Z_to_bv 64 1) Rg1.           (* [comment removed for export] *)
    ab_ft F_5020c D_5020c ltac:(condz).                (* [comment removed for export] *)
    an F_50210 D_50210.                                (* [comment removed for export] *)
    cld8 F_50214 D_50214 (Z_to_bv 64 0x19909c) Rg2.    (* [comment removed for export] *)
    clw F_50218 D_50218 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0) Rdy V0.   (* [comment removed for export] *)
    try (rewrite (v_lw_small 0) by lia).
    ab_ft F_5021c D_5021c ltac:(condz).                (* [comment removed for export] *)
    wd_refl.
  Qed.
End ENQSPIN.

(* [comment removed for export] *)
Lemma enq_spin_to_spin : forall (r : bvmap 5 word) (M rom : word -> option byte) (model : Model),
  to_spin ASEGS (mkst r (0x50228 : word) M rom) model.
Proof using.
  intros r M rom model.
  apply (ts_spin_of_step_j ASEGS (mkst r (0x50228 : word) M rom) model W_50220 0 0 4%Z);
    [reflexivity | exact F_50220 | reflexivity | exact D_50220 | reflexivity | reflexivity].
Qed.
End FPGen.
End AsAllocF5s.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemR OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRun3Rf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N.AsAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemR.AsAllocF5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemR.AsAllocFRun3R.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Ltac hidehypRf H := lazymatch type of H with ?T => change T with (hideR T) in H end.

Section FPGen.
Context {fx : FPState}.

Section RUN3Rf.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S p ra0 tp x22 s0v s1v s2v s3v s4v s5v : word) (T n n8 id fl last qb len : Z) (cpm : byte) (midend : word).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 2 = at_ S (-2176).
  Hypothesis D8 : getr rD 8 = at_ p (-16).
  Hypothesis D9 : getr rD 9 = at_ S (-2128).
  Hypothesis D10 : getr rD 10 = Z_to_bv 64 id.
  Hypothesis D18 : getr rD 18 = Z_to_bv 64 0x103f18.
  Hypothesis D19 : getr rD 19 = Z_to_bv 64 0.
  Hypothesis D20 : getr rD 20 = thr.
  Hypothesis D21 : getr rD 21 = at_ S (-81).
  Hypothesis D22 : getr rD 22 = x22.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + n8 <= T \/ T + 4096 <= U p - 16)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis Gid : (0 <= id < 2 ^ 32)%Z.
  Hypothesis Gfl : (0 <= fl /\ fl + 4096 <= AIMGHI)%Z.
  Hypothesis Glast : (0x10007fff8000 <= last /\ last + 8192 <= U S - 3584)%Z.
  Hypothesis GlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Glastp : (last + 8192 <= U p - 16 \/ U p + n8 <= last)%Z.
  Hypothesis Gqb : (0 <= qb /\ qb + n + 8192 <= 2 ^ 20)%Z.
  Hypothesis GT16 : (T mod 16 = 0)%Z.
  Hypothesis Glen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Gmid : (U midend < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS memD (at_ S (-2304)) 2304 = true.
  Hypothesis Okp : store_ok ASEGS memD p 8 = true.
  Hypothesis Oksh : store_ok ASEGS memD (Z_to_bv 64 (shad p)) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok ASEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  (* [comment removed for export] *)
  Hypothesis C_q0 : rdn ASEGS memD (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4)).
  Hypothesis C_q1 : rdn ASEGS memD (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C_q2 : rdn ASEGS memD (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C_q3 : rdn ASEGS memD (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434)).
  Hypothesis C_q4 : rdn ASEGS memD (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis C_q5 : rdn ASEGS memD (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).
  Hypothesis C_i0 : rdn ASEGS memD (at_ S (-8)) 8 = Some (LE8 ra0).
  Hypothesis C_i1 : rdn ASEGS memD (at_ S (-16)) 8 = Some (LE8 s0v).
  Hypothesis C_i2 : rdn ASEGS memD (at_ S (-24)) 8 = Some (LE8 s1v).
  Hypothesis C_i3 : rdn ASEGS memD (at_ S (-32)) 8 = Some (LE8 s2v).
  Hypothesis C_i4 : rdn ASEGS memD (at_ S (-40)) 8 = Some (LE8 s3v).
  Hypothesis C_i5 : rdn ASEGS memD (at_ S (-48)) 8 = Some (LE8 s4v).
  Hypothesis C_i6 : rdn ASEGS memD (at_ S (-56)) 8 = Some (LE8 s5v).
  Hypothesis C_nhi : rdn ASEGS memD (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn ASEGS memD (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_mcs : rdn ASEGS memD (Z_to_bv 64 (0x103f18 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis C_msz : rdn ASEGS memD (Z_to_bv 64 (0x103f18 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis C_gfl : rdn ASEGS memD (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 fl)).
  Hypothesis C_mff : rdn ASEGS memD (Z_to_bv 64 (fl + 48)) 4 = Some (LE4 0).
  Hypothesis C_gsh : rdn ASEGS memD (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578)).
  Hypothesis C_sh : rdn ASEGS memD (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn ASEGS memD (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268)).
  Hypothesis C_mb : rdn ASEGS memD (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn ASEGS memD (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270)).
  Hypothesis C_me : rdn ASEGS memD (Z_to_bv 64 0x108270) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn ASEGS memD (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260)).
  Hypothesis C_he : rdn ASEGS memD (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn ASEGS memD (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0)).
  Hypothesis C_rm : rdn ASEGS memD (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4)).
  Hypothesis C_cpm : rdn ASEGS memD (Z_to_bv 64 0x106ddc) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_qb : rdn ASEGS memD (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis C_cnt0 : rdn ASEGS memD (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).

  (* [comment removed for export] *)
  Theorem run_p3r1f :
    rdn ASEGS memD (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 last)) ->
    rdn ASEGS memD (Z_to_bv 64 (last + 16)) 8 = Some (LE8 (Z_to_bv 64 1021)) ->
    rdn ASEGS memD (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 len)) ->
    exists r,
      msteps ASEGS (mkst rD (0x4fdc8 : word) memD rom) (mkst r (0x509cc : word) (fr_P3r1 memD S p x22 T n n8 id) rom)
      /\ refill_call_regs S p tp T n rD r.
  Proof using C_cnt0 C_cpm1 C_cpm C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sh C_gsh C_mff C_gfl C_msz C_mcs C_nlo C_nhi C_q5 C_q4 C_q3 C_q2 C_q1 C_q0 Oksh Okp Hstk Glen Glastp Glast Gfl Gid Gn8 Gn GpT GT Gp GS D4 D22 D21 D20 D19 D18 D10 D9 D8 D1 midend cpm fl.
    intros C_last C_lcnt C_len. (lazymatch goal with |- ?G => let G' := eval unfold refill_call_regs in G in change_no_check G' end).
    clear Gqb C_qb.   (* [comment removed for export] *)
    hidehypRf GpT. hidehypRf GlastT. hidehypRf Glastp.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    destruct GS as (GS1 & GS2 & GS3). destruct Gp as (Gp1 & Gp2 & Gp3). destruct GT as (GT1 & GT2). destruct GT2 as [GTS GT2]. destruct Gp2 as [GpS Gp2]. destruct Gn8 as (N8a & N8b & N8c & N8d).
    Ltac grows_tac := repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    Ltac xqh TS Q H := unfold hideW in TS; xq Q H.
    Ltac rch := repeat (first [ reflexivity | assumption
                              | match goal with |- getr ?r ?n = _ => match goal with H : getr r n = _ |- _ => rewrite H end end ]).
    Ltac viac AG r := rewrite (AG r ltac:((lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); notin)); rch.
    (* [comment removed for export] *)
    destruct (c1_run memD rom S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 T n id fl n8 rD
                D1 D8 D9 D10 D18 D19 D20 D21 D22 ltac:(hlia) ltac:(hlia) ltac:(hlia) Gn Gid ltac:(hlia) N8a Hstk Okp
                C_q0 C_q1 C_q2 C_q3 C_q4 C_q5 C_nhi C_nlo C_mcs C_msz C_gfl C_mff)
      as (r1 & RUN1 & A1 & A2 & A10 & A11 & A12 & A8 & A9 & A18 & A19 & A20 & A21 & A22 & A3 & A4 & A23 & A24 & A25 & A26 & A27).
    set (M12t := fr_c1 memD S p (Z_to_bv 64 0x6e434) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T) in RUN1.
    assert (GR12 : mem_grows memD M12t) by ((lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end); grows_tac).
    assert (Q12 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M12t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M12t, fr_c1 in G in change_no_check G' end). intros x Hx. rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia. reflexivity. }
    remember M12t as M12 eqn:EM12 in RUN1, GR12, Q12. subst M12t.
    (* [comment removed for export] *)
    assert (PH : poisonH ASEGS asan_poison_tab M12 p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50074) (at_ S (-2208)) cpm midend 0).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm pt_base pt_mset asan_poison_tab] in G in change_no_check G' end).
      - xq Q12 C_gsh. - xq Q12 C_sh. - xq Q12 C_gmb. - xq Q12 C_mb. - xq Q12 C_gme. - xq Q12 C_me. - xq Q12 C_ghe. - xq Q12 C_he.
      - xq Q12 C_grm. - xq Q12 C_rm.
      - vm_compute. discriminate.
      - apply ret_ok_even. reflexivity.
      - intros _. split; [xq Q12 C_cpm | exact C_cpm1].
      - intros Hz. exfalso. revert Hz. unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm asan_poison_tab] in G in change_no_check G' end).
        repeat constructor; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite ?at_u by lia; lia ].
      - destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & M8 & _). exact M8.
      - unorm. exact N8c.
      - unorm. unfold hideW in GpS. destruct GpS as [PS|PS]; [right | left]; lia.
      - rewrite at_u by lia. lia.
      - eapply (store_ok_sub ASEGS M12 (at_ S (-2304)) _ 2304); [rewrite at_u; lia | eapply store_ok_mono; [exact GR12 | exact Hstk] | rewrite !at_at, !at_u; lia | rewrite !at_at, !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). unorm. eapply store_ok_mono; [exact GR12 | exact Oksh].
      - apply ret_ok_lit; [lia | reflexivity]. }
    destruct (asan_poison_shadow M12 rom p (Z_to_bv 64 n8) (Z_to_bv 64 253) (Z_to_bv 64 0x50074) (at_ S (-2208)) cpm midend 0 r1 PH A1 A2 A10 A11 A12)
      as (r2 & RUN2 & AGP).
    rewrite A8, A9, A18, A19, A20, A21 in RUN2.
    set (M13t := wbytes _ _ _) in RUN2.
    assert (EM13' : M13t = fr_PS M12 S p T n n8) by reflexivity.
    assert (GR13 : mem_grows memD M13t).
    { eapply mem_grows_trans; [exact GR12|]. (lazymatch goal with |- ?G => let G' := eval unfold M13t, ps_frame in G in change_no_check G' end). grows_tac. }
    (* [comment removed for export] *)
    destruct (p16_facts (U p) Gp3 ltac:(lia)) as (_ & _ & _ & Mp8 & _).
    destruct (shad_facts2 (U p) n8 ltac:(unfold hideW in GpS; lia) ltac:(lia) ltac:(lia) N8d Mp8 N8c) as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6). hidehypW SH1.
    assert (TSH : hideW (T + 4096 <= 0x7fff8000 + U p / 8 \/ 0x7fff8000 + U p / 8 + n8 / 8 <= T)%Z)
      by (unfold hideW in GTS, GpS |- *; clear -GTS GpS SH2 SH4 Hpr GT2 Gp2; lia).
    assert (Q13 : forall x : word, ((U x < U S - 2304)%Z /\ (U x < U p \/ U p + 8 <= U x)%Z /\ (U x < 0x7fff8000 + U p / 8 \/ 0x7fff8000 + U p / 8 + n8 / 8 <= U x)%Z) \/ (U S - 2128 <= U x)%Z -> M13t x = memD x).
    { (lazymatch goal with |- ?G => let G' := eval unfold M13t, ps_frame in G in change_no_check G' end). rewrite !at_at. intros x Hx. pose proof (u64_range p).
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?repeat_length; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); rewrite ?at_u by lia; try lia.
      1: apply Q12; lia.
      all: (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); unorm; rewrite ?Z2Nat.id by lia; lia. }
    (* [comment removed for export] *)
    Ltac dig := repeat (wd_rdstep rd8_side).
    Ltac slot13 E := (lazymatch goal with |- ?G => let G' := eval unfold ps_frame in G in change_no_check G' end); rewrite !at_at;
                   rewrite rdn_wbytes_out; [ | (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end); rewrite ?repeat_length; unorm; rewrite ?Z2Nat.id by lia; rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia .. ];
                   dig; rewrite E; (lazymatch goal with |- ?G => let G' := eval unfold fr_c1 in G in change_no_check G' end); dig.
    assert (P0 : rdn ASEGS M13t (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P1 : rdn ASEGS M13t (at_ S (-2144)) 8 = Some (LE8 S)) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P2 : rdn ASEGS M13t (at_ S (-2152)) 8 = Some (LE8 p)) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P3 : rdn ASEGS M13t (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P4 : rdn ASEGS M13t (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P5 : rdn ASEGS M13t (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P6 : rdn ASEGS M13t (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81)))) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    assert (P7 : rdn ASEGS M13t (at_ S (-2192)) 8 = Some (LE8 x22)) by ((lazymatch goal with |- ?G => let G' := eval unfold M13t in G in change_no_check G' end); slot13 EM12).
    remember M13t as M13 eqn:EM13 in RUN2, GR13, Q13, P0, P1, P2, P3, P4, P5, P6, P7. subst M13t.
    (* [comment removed for export] *)
    assert (V2 : getr r2 2 = at_ S (-2208)) by viac AGP (2:reg).
    assert (V8 : getr r2 8 = Z_to_bv 64 (0x103f18 + 728)) by viac AGP (8:reg).
    assert (V9 : getr r2 9 = at_ (Z_to_bv 64 T) 80) by viac AGP (9:reg).
    assert (V18 : getr r2 18 = Z_to_bv 64 n) by viac AGP (18:reg).
    assert (V19 : getr r2 19 = at_ S (-2128)) by viac AGP (19:reg).
    assert (V20 : getr r2 20 = at_ (Z_to_bv 64 T) 208) by viac AGP (20:reg).
    assert (V21 : getr r2 21 = at_ p (-16)) by viac AGP (21:reg).
    assert (V22 : getr r2 22 = Z_to_bv 64 (2 ^ 20)) by viac AGP (22:reg).
    (* [comment removed for export] *)
    assert (GTw : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z) by hlia.
    Ltac finish_r RUN1 RUN2 RUN3 M13 M12 AGP :=
      wd_eexists; split;
      [ subst M13 M12; (lazymatch goal with |- ?G => let G' := eval unfold fr_P3r1, fr_PS in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end);
        eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [| exact RUN3];
        replace (Z_to_bv 64 0x50074 : word) with (0x50074 : word) in RUN2 at 1 by (apply bv_eq; reflexivity);
        exact RUN2
      | repeat match goal with |- _ /\ _ => split end; try assumption; try rch;
        try (viac AGP (3:reg)); try (viac AGP (4:reg)); try (viac AGP (23:reg)); try (viac AGP (24:reg)); try (viac AGP (25:reg));
        try (viac AGP (26:reg)); try (viac AGP (27:reg)) ].
    destruct (er1f_run M13 rom S p T n last len r2 V2 V8 V9 V18 V19 V20 V21 V22 ltac:(hlia) GTw
                 ltac:(eapply store_ok_mono; [exact GR13 | exact Hstk]) ltac:(unfold hideR in GpT; xqh TSH Q13 C_cnt0) ltac:(hlia) Glen
                 ltac:(unfold hideR in GpT; xqh TSH Q13 C_last) ltac:(unfold hideR in Glastp; xqh TSH Q13 C_lcnt) ltac:(unfold hideR in GpT; xqh TSH Q13 C_len))
        as (r3 & RUN3 & B1 & B2 & B10 & B11 & B12 & B13 & B8 & B9 & B18 & B19 & B21 & B22 & B3 & B4 & B23 & B24 & B25 & B26 & B27).
    finish_r RUN1 RUN2 RUN3 M13 M12 AGP.
  Qed.

End RUN3Rf.

End FPGen.
End AsAllocFRun3Rf.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI.AsAllocF0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRunI.AsAllocF2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemR.AsAllocF5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFRun OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRun3N.AsAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemR.AsAllocFRun3R AsAllocFRun3Rf OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4R.AsAllocFMem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFMemR OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypD OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcK1.AsAllocFHypR AsAllocF5s OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTop0i.AsAllocFTopA.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AsAllocFFam.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation up8 := AsAinvOpsPf3d.AsAinvFreeS.up8.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma down8_up8R1 : forall n, AsRtRegion.down8 (n + 7) = up8 n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold AsRtRegion.down8, AsAinvOpsPf3d.AsAinvFreeS.up8 in G in change_no_check G' end). reflexivity. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sp_mod16_2272 : forall s, s mod 16 = 0 -> (s + -2272) mod 16 = 0.
Proof. intros s Hs. lia. Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section PUTR1.
  Context {RC : run_ceil}.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variables (TP TSDP PGP FL MIDEND CPM KD : Z).
  Hypothesis BT_segs : bt_segs bt = ASEGS.
  Hypothesis BT_ia : bt_ia bt = asan_addrs.
  Hypothesis CELLS : free_cells bt TP TSDP PGP FL MIDEND CPM.
  Hypothesis GEOM : free_boot_geom bt.
  Hypothesis G_KD : 0 <= KD <= 1408.
  Hypothesis HTP : TP = ia_tp asan_addrs.
  Variable KR : Z.
  Hypothesis G_KR : 0 <= KR <= 1312.
  Hypothesis HYP_REFILL : HYP_REFILL24K_stmt bt FXOK KR.            (* [comment removed for export] *)
  Hypothesis CELLSPIN : free_cells_spin bt.
  (* [comment removed for export] *)
  Variables (HP HPc : option Z -> ast -> Prop).
  Hypothesis FAM : hp_fam bt HP HPc.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation CTX := (bt_tctx bt).

  (* [comment removed for export] *)
  Definition putR1_post (h : option Z) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K1 m : Z) (p : word)
             (st' : ast) (c' : config) : Prop :=
    let S := getr R 2 in
    exists fx'' (R'' : bvmap 5 word) (M'' M0'' : mem) (mdl'' : Model) (st'' : ast) (ks : list Z) (k : Z),
      c' = mkCfg (@mkst fx'' R'' (Z_to_bv 64 0x501ec) M'' (seg_rom ASEGS)) mdl''
      /\ FXOK fx'' /\ m_halted mdl'' = None /\ BackingAlgebra.model_ivs_wf mdl''
      /\ WF bt st'' Lc FF /\ Rep bt st'' Lc FF M0'' mdl'' /\ bounds st'' Lc B C K1 /\ HPc h st''
      /\ a_cache st'' BATCHCLASS = ks ++ [k] /\ a_tq st'' = a_tq st' /\ a_gq st'' = a_gq st'
      /\ (forall a : word, M'' a <> M0'' a -> X2 (U S) (U p) T m (U a) /\ M'' a <> None)
      /\ (forall a : word, M'' a <> M a ->
            (X2 (U S) (U p) T m (U a) \/ (U S - 3584 <= U a < U S)
             \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
            /\ M'' a <> None)
      /\ M'' (at_ p (-16)) = Some (Z_to_bv 8 3)
      /\ (forall i, 0 <= i < up8 m / 8 -> M'' (Z_to_bv 64 (SB + U p / 8 + i)) = Some (Z_to_bv 8 0xfd))
      /\ (rdn ASEGS M'' (at_ S (-2216)) 8 = Some (LE8 (Z_to_bv 64 0x5008c)) /\ rdn ASEGS M'' (at_ S (-2224)) 8 = Some (LE8 (Z_to_bv 64 (0x103f18 + 728)))
          /\ rdn ASEGS M'' (at_ S (-2232)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 80)) /\ rdn ASEGS M'' (at_ S (-2240)) 8 = Some (LE8 (Z_to_bv 64 m))
          /\ rdn ASEGS M'' (at_ S (-2248)) 8 = Some (LE8 (at_ S (-2128))) /\ rdn ASEGS M'' (at_ S (-2256)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208))
          /\ rdn ASEGS M'' (at_ S (-2264)) 8 = Some (LE8 (at_ p (-16)))
          /\ rdn ASEGS M'' (at_ S (-2208)) 8 = Some (LE8 (at_ (Z_to_bv 64 T) 208)) /\ rdn ASEGS M'' (at_ S (-2200)) 8 = Some (LE8 (at_ S (-2128))))
      /\ (rdn ASEGS M'' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4)) /\ rdn ASEGS M'' (at_ S (-2144)) 8 = Some (LE8 S)
          /\ rdn ASEGS M'' (at_ S (-2152)) 8 = Some (LE8 p) /\ rdn ASEGS M'' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434))
          /\ rdn ASEGS M'' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) /\ rdn ASEGS M'' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))
          /\ rdn ASEGS M'' (at_ S (-2184)) 8 = Some (LE8 (at_ S (-81))) /\ rdn ASEGS M'' (at_ S (-2192)) 8 = Some (LE8 (getr R 22)))
      /\ (rdn ASEGS M'' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) /\ rdn ASEGS M'' (at_ S (-16)) 8 = Some (LE8 (getr R 8))
          /\ rdn ASEGS M'' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) /\ rdn ASEGS M'' (at_ S (-32)) 8 = Some (LE8 (getr R 18))
          /\ rdn ASEGS M'' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) /\ rdn ASEGS M'' (at_ S (-48)) 8 = Some (LE8 (getr R 20))
          /\ rdn ASEGS M'' (at_ S (-56)) 8 = Some (LE8 (getr R 21)))
      /\ (getr R'' 10 = Z_to_bv 64 1 /\ getr R'' 2 = at_ S (-2272) /\ getr R'' 8 = at_ (Z_to_bv 64 T) 2128 /\ getr R'' 9 = at_ (Z_to_bv 64 T) 208
          /\ getr R'' 18 = at_ p (-16) /\ getr R'' 19 = at_ (Z_to_bv 64 T) 80 /\ getr R'' 21 = Z_to_bv 64 m /\ getr R'' 22 = Z_to_bv 64 (2 ^ 20)
          /\ getr R'' 3 = getr R 3 /\ getr R'' 4 = getr R 4
          /\ getr R'' 23 = getr R 23 /\ getr R'' 24 = getr R 24 /\ getr R'' 25 = getr R 25 /\ getr R'' 26 = getr R 26 /\ getr R'' 27 = getr R 27)
      /\ same_except_vm mdl mdl'' /\ lazy_kept (bt_ia bt) Lc FF mdl mdl''.

  (* [comment removed for export] *)
  Definition free_putR1_stmt : Prop :=
    forall (h : option Z) fx' (R R' : bvmap 5 word) (M M' M0 : mem) (mdl mdl' : Model) (Lc FF L1 L2 : list (Z * Z)) (B C K1 ret sp m : Z) (p : word)
           (st' : ast) (id : Z),
      let S := getr R 2 in
      (* [comment removed for export] *)
      call_pre ASEGS asan_addrs R M ret sp MSTK_A -> getr R 10 = p ->
      Lc = L1 ++ (U p, m) :: L2 ->
      (* [comment removed for export] *)
      WF bt st' Lc FF -> Rep bt st' Lc FF M0 mdl' -> bounds st' Lc B C K1 -> HPc h st' ->
      (a_tq st' = [] \/ exists tq' b, a_tq st' = tq' ++ [b] /\ Z.of_nat (length (ba_items b)) = BATCHCAP) ->
      a_cache st' BATCHCLASS = [] -> m <= 2 ^ 28 -> K1 <= KCAP -> mu_room st' ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      FXOK fx' -> m_halted mdl' = None -> BackingAlgebra.model_ivs_wf mdl' ->
      (forall a : word, M' a <> M0 a -> Xd (U S) (U p) T (U a) /\ M' a <> None) ->
      (forall a : word, M' a <> M a ->
          (Xd (U S) (U p) T (U a) \/ (U S - 2176 - KD <= U a < U S - 2176)
           \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a))
          /\ M' a <> None) ->
      M' (at_ p (-16)) = Some (Z_to_bv 8 3) ->
      rdn ASEGS M' (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4)) -> rdn ASEGS M' (at_ S (-2144)) 8 = Some (LE8 S) ->
      rdn ASEGS M' (at_ S (-2152)) 8 = Some (LE8 p) -> rdn ASEGS M' (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434)) ->
      rdn ASEGS M' (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)) -> rdn ASEGS M' (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))) ->
      rdn ASEGS M' (at_ S (-8)) 8 = Some (LE8 (getr R 1)) -> rdn ASEGS M' (at_ S (-16)) 8 = Some (LE8 (getr R 8)) ->
      rdn ASEGS M' (at_ S (-24)) 8 = Some (LE8 (getr R 9)) -> rdn ASEGS M' (at_ S (-32)) 8 = Some (LE8 (getr R 18)) ->
      rdn ASEGS M' (at_ S (-40)) 8 = Some (LE8 (getr R 19)) -> rdn ASEGS M' (at_ S (-48)) 8 = Some (LE8 (getr R 20)) ->
      rdn ASEGS M' (at_ S (-56)) 8 = Some (LE8 (getr R 21)) ->
      getr R' 2 = at_ S (-2176) -> getr R' 8 = at_ p (-16) -> getr R' 9 = at_ S (-2128) -> getr R' 10 = Z_to_bv 64 id ->
      getr R' 18 = Z_to_bv 64 (IB bt) -> getr R' 19 = Z_to_bv 64 0 -> getr R' 20 = Z_to_bv 64 T -> getr R' 21 = at_ S (-81) ->
      getr R' 22 = getr R 22 -> getr R' 3 = getr R 3 -> getr R' 4 = getr R 4 ->
      getr R' 23 = getr R 23 -> getr R' 24 = getr R 24 -> getr R' 25 = getr R 25 -> getr R' 26 = getr R 26 -> getr R' 27 = getr R 27 ->
      0 <= id < 2 ^ 32 ->
      same_except_vm mdl mdl' -> lazy_kept (bt_ia bt) Lc FF mdl mdl' ->
      katD ASEGS (mkCfg (@mkst fx' R' (Z_to_bv 64 0x4fdc8) M' (seg_rom ASEGS)) mdl')
           (putR1_post h R M mdl Lc FF B C K1 m p st').

  Theorem free_putR1 : free_putR1_stmt.
  Proof using FAM HP CELLSPIN HYP_REFILL G_KR KR G_KD GEOM CELLS BT_ia BT_segs CPM MIDEND FL PGP TSDP TP.
    (lazymatch goal with |- ?G => let G' := eval unfold free_putR1_stmt in G in change_no_check G' end).
    intros h fx' R R' M M' M0 mdl mdl' Lc FF L1 L2 B C K1 ret sp m p st' id CP HR10 ELc W' RP' BD' HLE TQC ECA M28 KC1 MUR1
           HFX' HH' MW' DX CHG Hb16 Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6
           Y2 Y8 Y9 Y10 Y18 Y19 Y20 Y21 Y22 Y3 Y4 Y23 Y24 Y25 Y26 Y27 Hid SEV LZ.
    pose proof ceil_rng as CR.
    set (S := getr R 2) in *. set (ra0 := getr R 1). set (tp := getr R 4).
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S ra0 tp in CP1, CP2, CP4. fold tp in Y4.
    assert (Utp : U tp = 0x63a740) by (rewrite CP4; vm_compute; reflexivity).
    unfold IB in Y18. rewrite BT_ia in Y18. cbn [ia_instance asan_addrs] in Y18.
    destruct CELLS as (CELL_mcs & CELL_gcf & CELL_fum & CELL_inited & CELL_pg & CELL_P & CELL_kif & CELL_key & CELL_tsdp & CELL_tctx & CELL_hook
                      & CELL_mcsz & CELL_msz & CELL_gfl & CELL_mff & CELL_gsh & CELL_gmb & CELL_mb & CELL_gme & CELL_me & CELL_ghe & CELL_he
                      & CELL_grm & CELL_rm & CELL_cpm & G_consts).
    destruct G_consts as (Gc1 & Gc2 & Gc3 & Gc4 & Gc5 & Gc6 & Gc7 & Gc8 & Gc9 & Gc10).
    destruct GEOM as (GCT & Gtop & Gbot).
    pose proof (free_obls_pf bt) as
      (OBL_nolazy_rt & _ & _ & _ & OBL_blk_geom & OBL_batch_geom & OBL_hdr_writable & _ & _).
    unfold OBL_nolazy_rt_stmt in OBL_nolazy_rt. unfold OBL_batch_geom_stmt in OBL_batch_geom.
    unfold OBL_blk_geom_stmt in OBL_blk_geom. unfold OBL_hdr_writable_stmt in OBL_hdr_writable.
    assert (HinP : In (U p, m) Lc) by (rewrite ELc; apply in_app_iff; right; left; reflexivity).
    destruct (live_range bt st' Lc FF W' (U p) m HinP) as (Lp1 & Lp2 & Lp3 & Lp4).
    destruct (OBL_blk_geom st' Lc FF (U p) m W' HinP) as (GpT & GCp & (AB1 & AB2 & AB3 & AB4)).
    pose proof (blk_above_img bt st' Lc FF W' ltac:((lazymatch goal with |- ?G => let G' := eval unfold img_lo_small in G in change_no_check G' end); rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia) (U p) m HinP) as PIMG.
    destruct (up8_facts m ltac:(lia)) as (U8a & U8b & U8c & U8d).
    pose proof (thread_dyn bt st' Lc FF W') as (GT0 & GTC & GTI & GTB & TPG & GC0 & GCC & GCI & GCB & CPG' & GCT' & SB0 & SB1 & SBH & SB16).
    assert (GT4 : 4096 <= T) by (unfold PG in TPG; clear - GT0 TPG; Z.div_mod_to_equations; lia).
    clear AB3 GCT' GCB.
    clear OBL_blk_geom.
    assert (T16 : T mod 16 = 0) by (clear -TPG; unfold PG in TPG; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    pose proof RP' as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    destruct R8 as [RH _]. destruct (RH (U p) m HinP) as (Hst & H11 & Hnhi & Hnlo & Hw8 & Hz4 & _).
    destruct (R15 (U p) m HinP) as [WBLK WSH].
    destruct R14 as (B1 & B2 & B3 & B4 & B5).
    pose proof R17 as Csb.
    pose proof (OBL_hdr_writable st' Lc FF M0 mdl' (U p) m W' RP' HinP) as WHDR.
    destruct (TPC BATCHCLASS ltac:((lazymatch goal with |- ?G => let G' := eval unfold BATCHCLASS in G in change_no_check G' end); lia)) as (PCcnt & _ & _ & _). rewrite ECA in PCcnt. cbn [length Z.of_nat] in PCcnt.
    unfold T_PC, PC_SZ, BATCHCLASS in PCcnt.
    destruct TQ as (Qlen & _ & Qlast & Qbytes).
    clear R2 R4 R5 R6 R7 R9 R10 R12 R16 R18 RH TPC OBL_hdr_writable.
    rewrite BT_segs in *. rewrite BT_ia in *. cbn [ia_img_lo ia_img_hi asan_addrs] in GTI, GCI, PIMG.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr.
    unfold PTRHI in CPlo, CPhi. unfold AS_HEAPLO, AS_LO, MSTK_A, PG, NMAX, BATCHSZ, BATCHCAP, T_QC, SB, KSPACE, PTRLO in *.
    destruct (p16_facts (U p) Lp4 ltac:(lia)) as (_ & _ & _ & P8 & _ & _).
    destruct (sh_up8 (U p) m P8 ltac:(lia)) as [SHhi SHlo]. unfold SB in SHhi, SHlo.
    destruct (shad_facts2 (U p) (up8 m) ltac:(clear -AB4 Hpr U8a; lia) ltac:(clear - Hpr; lia) ltac:(clear - AB2 CR; lia) U8b P8 U8d) as (D81 & D82 & D83 & D84 & D85 & D86).
    (* [comment removed for export] *)
    assert (XdC : forall z, AIMGLO <= z < AIMGHI -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite CP2; clear -Hz GTI PIMG CPlo CR HSr; lia).
    assert (XdC2 : forall z, AIMGLO <= z < AIMGHI -> ~ X2 (U S) (U p) T m z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); rewrite <- SHhi, SHlo; rewrite CP2; clear -Hz GTI PIMG CPlo CR HSr D84; lia).
    assert (XdT : forall z, T <= z < T + 2800 -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b CP2 CPlo GTC; lia).
    assert (XdH : forall z, U p - 15 <= z < U p -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GpT U8b AB2 CP2 CPlo; lia).
    (* [comment removed for export] *)
    assert (GSm : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47) by (clear - CP2 CPlo CPhi CR; lia).
    assert (Gpm : AIMGHI + 16 <= U p /\ (PSIDE (U p) (up8 m) /\ U p + up8 m <= U S - 3584) /\ U p mod 16 = 0).
    { split; [clear - PIMG; lia|]. split; [split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear -AB4 U8a; lia | clear - AB2 U8a CP2 CPlo; lia] | exact Lp4]. }
    assert (GTm : 4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584)).
    { split; [exact GT4|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hideW in G in change_no_check G' end); clear - GTI GTB; split; lia | clear - GTC CP2 CPlo; lia]. }
    assert (Gn8m : 8 <= up8 m /\ up8 m mod 8 = 0 /\ up8 m <= 2 ^ 40) by (clear - U8a U8b U8c U8d M28 Lp3; lia).
    assert (GpTm : U p + up8 m <= T \/ T + 4096 <= U p - 16) by (clear - GpT; lia).
    (* [comment removed for export] *)
    assert (NST_stk : forall z, U S - 3584 <= z -> ~ (T + 2768 <= z < T + 3168)) by (intros z Hz; clear - Hz GTC CP2 CPlo; lia).
    assert (NST_p : forall z, U p - 16 <= z < U p + up8 m -> ~ (T + 2768 <= z < T + 3168)) by (intros z Hz; clear - Hz GpT; lia).
    assert (NST_sh : forall z, sh_lo (U p) <= z < sh_hi (U p) m -> ~ (T + 2768 <= z < T + 3168)).
    { intros z Hz. unfold sh_lo, sh_hi, SB in Hz. clear - Hz GTB Lp1 Lp2 Lp3 CR. Z.div_mod_to_equations. lia. }
    hidehyp GpT. hidehyp GCp. hidehyp GCT. hidehyp GpTm.
    hidehyp GTI. hidehyp GTB. hidehyp AB4. hidehyp D81. hidehyp GCI.
    (* [comment removed for export] *)
    assert (EQ0 : forall a : word, ~ Xd (U S) (U p) T (U a) -> M' a = M0 a).
    { intros a Ha. destruct (decide (M' a = M0 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX a N))). }
    assert (GR0 : mem_grows M0 M') by (intros a Ha; destruct (decide (M' a = M0 a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (DX a N))]).
    assert (GRM : mem_grows M M') by (intros a Ha; destruct (decide (M' a = M a)) as [E|N]; [rewrite E; exact Ha | exact (proj2 (CHG a N))]).
    (* [comment removed for export] *)
    set (Hd := HID st' mdl').
    assert (NHs : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz Hr. apply (HID_off_zone bt st' mdl' z R13 Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
    assert (NHT : forall z, T <= z < T + 4096 -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). exact Hz. }
    assert (NHp : forall z, U p - 16 <= z < U p + up8 m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; left. exists (U p), m. split; [exact HinP | exact Hz]. }
    assert (NHsh : forall z, sh_lo (U p) <= z < sh_hi (U p) m -> Hd (Z_to_bv 64 z) = false).
    { intros z Hz. apply HID_allowed. exact (B4 (U p) m HinP z Hz). }
    Ltac hoff NH := apply hid_off_of; intros z Hz; split; [lia | apply NH; lia].
    (* [comment removed for export] *)
    Ltac cell0 EQ0 NH XD C :=
      rewrite rdn_mrestrict; [ | wd_ulia_c | unorm; hoff NH ];
      eapply rd_same; [ intros x Hx; apply EQ0; apply XD; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | wd_ulia_c | exact C ].
    Ltac konst EQ0 R1 NHs XdC C := cell0 EQ0 NHs XdC (const_cell bt _ _ _ _ R1 C).
    assert (K_mcsz : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (0x103f18 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20)))) by konst EQ0 R1 NHs XdC CELL_mcsz.
    assert (K_msz : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (0x103f18 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28)))) by konst EQ0 R1 NHs XdC CELL_msz.
    assert (K_gfl : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff268) 8 = Some (LE8 (Z_to_bv 64 FL))) by konst EQ0 R1 NHs XdC CELL_gfl.
    assert (K_mff : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (FL + 48)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by konst EQ0 R1 NHs XdC CELL_mff.
    assert (K_gsh : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff270) 8 = Some (LE8 (Z_to_bv 64 0x107578))) by konst EQ0 R1 NHs XdC CELL_gsh.
    assert (K_sh : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x107578) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000))).
    { cbn [ia_rtc_sb asan_addrs] in Csb. cell0 EQ0 NHs XdC Csb. }
    assert (K_gmb : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff278) 8 = Some (LE8 (Z_to_bv 64 0x108268))) by konst EQ0 R1 NHs XdC CELL_gmb.
    assert (K_mb : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x108268) 8 = Some (LE8 (Z_to_bv 64 0))) by konst EQ0 R1 NHs XdC CELL_mb.
    assert (K_gme : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff280) 8 = Some (LE8 (Z_to_bv 64 0x108270))) by konst EQ0 R1 NHs XdC CELL_gme.
    assert (K_me : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x108270) 8 = Some (LE8 (Z_to_bv 64 MIDEND))) by konst EQ0 R1 NHs XdC CELL_me.
    assert (K_ghe : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff288) 8 = Some (LE8 (Z_to_bv 64 0x108260))) by konst EQ0 R1 NHs XdC CELL_ghe.
    assert (K_he : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x108260) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff))) by konst EQ0 R1 NHs XdC CELL_he.
    assert (K_grm : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0xff290) 8 = Some (LE8 (Z_to_bv 64 0x1011b0))) by konst EQ0 R1 NHs XdC CELL_grm.
    assert (K_rm : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x1011b0) 8 = Some (LE8 (Z_to_bv 64 0xf56e4))) by konst EQ0 R1 NHs XdC CELL_rm.
    assert (K_cpm : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 0x106ddc) 1 = Some [Z_to_bv 8 CPM]).
    { rewrite <- w2b1 by lia. konst EQ0 R1 NHs XdC CELL_cpm. }
    (* [comment removed for export] *)
    assert (K_cnt0 : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { replace (T + 2128) with (T + 208 + 80 * 24) by lia. cell0 EQ0 NHT XdT PCcnt. }
    assert (K_nhi : rdn ASEGS (mrestrict Hd M') (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (m / 2 ^ 32)))).
    { replace (at_ p (-14)) with (Z_to_bv 64 (U p - 14)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnhi. }
    assert (K_nlo : rdn ASEGS (mrestrict Hd M') (at_ p (-12)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (m mod 2 ^ 32)))).
    { replace (at_ p (-12)) with (Z_to_bv 64 (U p - 12)) by (apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia). cell0 EQ0 NHp XdH Hnlo. }
    (* [comment removed for export] *)
    assert (LCASE : rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 0))
                    \/ exists tq' b, a_tq st' = tq' ++ [b]
                        /\ rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 (ba_addr b)))
                        /\ rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (ba_addr b + 16)) 8 = Some (LE8 (Z_to_bv 64 1021))
                        /\ rdn ASEGS (mrestrict Hd M') (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 (Z.of_nat (length (a_tq st')))))
                        /\ (0x10007fff8000 <= ba_addr b /\ ba_addr b + 8192 <= U S - 3584)
                        /\ hide (ba_addr b + 8192 <= T \/ T + 4096 <= ba_addr b) /\ hide (ba_addr b + 8192 <= U p - 16 \/ U p + up8 m <= ba_addr b)
                        /\ 1 <= Z.of_nat (length (a_tq st')) < 2 ^ 40).
    { destruct TQC as [Etq | (tq' & b & Etq & FULL)].
      - left. rewrite Etq in Qlen. cbn [length Z.of_nat] in Qlen. cell0 EQ0 NHT XdT Qlen.
      - right. exists tq', b.
        assert (HinB : In b (a_tq st' ++ a_gq st')) by (apply in_app_iff; left; rewrite Etq; apply in_app_iff; right; left; reflexivity).
        destruct (OBL_batch_geom st' Lc FF b (U p) m W' HinB HinP) as (GBp & GBT & GBlo & GBhi).
        destruct (read_tq_last bt st' Lc FF M0 mdl' tq' b W' RP' Etq) as (Qlen' & Qlast' & _ & _ & _ & Bcnt & _ & _ & _ & Blen & Blob & Bhib).
        rewrite BT_segs in *. rewrite FULL in Bcnt. unfold BATCHCAP in Bcnt. unfold BATCHSZ in *.
        assert (NHbo : forall z, ba_addr b <= z < ba_addr b + 8192 -> Hd (Z_to_bv 64 z) = false).
        { intros z Hz. apply HID_notlazy; [lia|]. apply (OBL_nolazy_rt st' Lc FF M0 mdl' z W' RP'). right; right; right. exists b. split; [exact HinB | (lazymatch goal with |- ?G => let G' := eval unfold BATCHSZ in G in change_no_check G' end); exact Hz]. }
        assert (XdBo : forall z, ba_addr b <= z < ba_addr b + 8192 -> ~ Xd (U S) (U p) T z) by (intros z Hz; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); clear - Hz GBp GBT GBhi U8b CP2 CPlo; lia).
        split; [exact Etq|]. split; [replace (T + 96) with (T + 80 + 16) by lia; cell0 EQ0 NHT XdT Qlast'|].
        split; [cell0 EQ0 NHbo XdBo Bcnt|]. split; [cell0 EQ0 NHT XdT Qlen'|].
        assert (LEN1 : 1 <= Z.of_nat (length (a_tq st'))) by (rewrite Etq, length_app; (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); lia).
        pose proof W' as (_ & _ & (QT & _ & QTB & _) & _). rewrite Forall_forall in QT.
        assert (IT : forall b0, In b0 (a_tq st') -> forall m0 n0, In (m0, n0) (ba_items b0) -> 1 <= n0).
        { intros b0 Hb0 m0 n0 Hin. destruct (QT b0 Hb0) as (_ & _ & WI). destruct (WI m0 n0 Hin) as [X _]. lia. }
        pose proof (q_bytes_ge (a_tq st') IT) as G1. unfold BATCHSZ in G1.
        split; [clear - GBlo GBhi CP2 CPlo; lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hide in G in change_no_check G' end); clear - GBT; lia|]. split; [(lazymatch goal with |- ?G => let G' := eval unfold hide in G in change_no_check G' end); clear - GBp; lia|].
        clear - LEN1 G1 QTB. lia. }
    clear Qlen Qlast Qbytes Hnhi Hnlo Csb R1 PCcnt OBL_batch_geom.
    (* [comment removed for export] *)
    Ltac stk NHs C := rewrite rdn_mrestrict; [ exact C | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs ].
    assert (S_q0 : rdn ASEGS (mrestrict Hd M') (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6e4a4))) by stk NHs Cq0.
    assert (S_q1 : rdn ASEGS (mrestrict Hd M') (at_ S (-2144)) 8 = Some (LE8 S)) by stk NHs Cq1.
    assert (S_q2 : rdn ASEGS (mrestrict Hd M') (at_ S (-2152)) 8 = Some (LE8 p)) by stk NHs Cq2.
    assert (S_q3 : rdn ASEGS (mrestrict Hd M') (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6e434))) by stk NHs Cq3.
    assert (S_q4 : rdn ASEGS (mrestrict Hd M') (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1))) by stk NHs Cq4.
    assert (S_q5 : rdn ASEGS (mrestrict Hd M') (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128)))) by stk NHs Cq5.
    assert (S_i0 : rdn ASEGS (mrestrict Hd M') (at_ S (-8)) 8 = Some (LE8 (Z_to_bv 64 ret))) by (rewrite <- CP1; stk NHs Ci0).
    assert (S_i1 : rdn ASEGS (mrestrict Hd M') (at_ S (-16)) 8 = Some (LE8 (getr R 8))) by stk NHs Ci1.
    assert (S_i2 : rdn ASEGS (mrestrict Hd M') (at_ S (-24)) 8 = Some (LE8 (getr R 9))) by stk NHs Ci2.
    assert (S_i3 : rdn ASEGS (mrestrict Hd M') (at_ S (-32)) 8 = Some (LE8 (getr R 18))) by stk NHs Ci3.
    assert (S_i4 : rdn ASEGS (mrestrict Hd M') (at_ S (-40)) 8 = Some (LE8 (getr R 19))) by stk NHs Ci4.
    assert (S_i5 : rdn ASEGS (mrestrict Hd M') (at_ S (-48)) 8 = Some (LE8 (getr R 20))) by stk NHs Ci5.
    assert (S_i6 : rdn ASEGS (mrestrict Hd M') (at_ S (-56)) 8 = Some (LE8 (getr R 21))) by stk NHs Ci6.
    clear Cq0 Cq1 Cq2 Cq3 Cq4 Cq5 Ci0 Ci1 Ci2 Ci3 Ci4 Ci5 Ci6.
    (* [comment removed for export] *)
    assert (SOKstk : store_ok ASEGS (mrestrict Hd M') (at_ S (-2304)) 2304 = true).
    { rewrite store_ok_mrestrict; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; hoff NHs].
      apply store_ok_bytes; [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]]. intros x Hx. rewrite at_u in Hx by lia.
      eapply store_ok_mono; [exact GRM|]. apply CPstk. cbn in Hx. rewrite <- CP2. lia. }
    assert (SOKp : store_ok ASEGS (mrestrict Hd M') p 8 = true).
    { rewrite store_ok_mrestrict; [| (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); hoff NHp].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WHDR); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    assert (SOKsh : store_ok ASEGS (mrestrict Hd M') (Z_to_bv 64 (shad p)) (Z.to_nat (up8 m / 8)) = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold shad in G in change_no_check G' end). rewrite store_ok_mrestrict; [| unorm; rewrite Z2Nat.id by lia; lia | unorm; rewrite Z2Nat.id by lia; hoff NHsh].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ WSH); unorm; rewrite ?Z2Nat.id by lia; lia. }
    assert (SOKT : store_ok ASEGS (mrestrict Hd M') (Z_to_bv 64 T) (Z.to_nat 4096) = true).
    { rewrite store_ok_mrestrict; [| wd_ulia_c | unorm; hoff NHT].
      eapply store_ok_mono; [exact GR0|]. apply (writableZ_store_ok M0 _ _ _ _ TW); wd_ulia_c. }
    clear WHDR WSH WBLK TW.
    (* [comment removed for export] *)
    assert (GS3 : 2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0) by (rewrite CP2; lia).
    assert (Gn3 : 1 <= m <= 2 ^ 28) by lia.
    assert (Gn83 : AsRtRegion.down8 (m + 7) = up8 m /\ m <= up8 m <= m + 7 /\ up8 m mod 8 = 0 /\ 8 <= up8 m) by (split; [apply down8_up8R1 | lia]).
    assert (Gfl3 : 0 <= FL /\ FL + 4096 <= AIMGHI) by lia.
    assert (Gmid3 : U (Z_to_bv 64 MIDEND) < 2 ^ 64) by (wd_ulia).
    assert (Ccpm1 : U (Z_to_bv 8 CPM) <> 0) by (rewrite (Z_to_bv_small 8 CPM ltac:(change (bv_modulus 8) with 256; lia)); lia).
    assert (D20' : getr R' 20 = Z_to_bv 64 T) by exact Y20.
    (* [comment removed for export] *)
    assert (RUNX : exists rf, msteps ASEGS (mkst R' (0x4fdc8%bv : word) (mrestrict Hd M') (seg_rom ASEGS))
                                           (mkst rf (0x509cc%bv : word) (fr_P3r1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) (seg_rom ASEGS))
                              /\ refill_call_regs S p tp T m R' rf).
    { destruct LCASE as [C0 | (tq' & b & Etq & C1 & C2 & C3 & G1 & G2 & G3 & G4)].
      - destruct (run_p3r1e (mrestrict Hd M') (seg_rom ASEGS) R' S p tp (getr R 22)
                    T m (up8 m) id FL (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND))
          as (rf & RUN & REGS).
        all: try assumption.
        all: try reflexivity.
        all: try (unfold hide in *; assumption).
        all: let k := numgoals in guard k = 1.
        exists rf. exact (conj RUN REGS).
      - destruct (run_p3r1f (mrestrict Hd M') (seg_rom ASEGS) R' S p tp (getr R 22)
                    T m (up8 m) id FL (ba_addr b) (Z.of_nat (length (a_tq st'))) (Z_to_bv 8 CPM) (Z_to_bv 64 MIDEND))
          as (rf & RUN & REGS).
        all: try assumption.
        all: try reflexivity.
        all: try (unfold hide in *; assumption).
        all: let k := numgoals in guard k = 1.
        exists rf. exact (conj RUN REGS). }
    clear LCASE.
    destruct RUNX as (rf & RUN3 & Z1 & Z2 & Z10 & Z11 & Z12 & Z13 & Z8 & Z9 & Z18 & Z19 & Z21 & Z22 & Z3 & Z4 & Z23 & Z24 & Z25 & Z26 & Z27).
    (* [comment removed for export] *)
    replace (0x4fdc8%bv : word) with (Z_to_bv 64 0x4fdc8 : word) in RUN3 by (apply bv_eq; reflexivity).
    apply (katD_msteps_acct ASEGS Hd (HID_off_segments bt st' Lc FF M0 mdl' BT_ia RP') asanF_segs_wx (a_aa st')
             (@mkst fx' R' (Z_to_bv 64 0x4fdc8) M' (seg_rom ASEGS))
             (@mkst fx' rf (0x509cc%bv : word) (fr_P3r1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) (seg_rom ASEGS)) mdl').
    { apply lazy_cover_HID. }
    { exact B1. }
    { exact B2. }
    { exact HH'. }
    { rewrite restrict_mkstF. exact RUN3. }
    clear RUN3 K_mcsz K_msz K_gfl K_mff K_gsh K_sh K_gmb K_mb K_gme K_me K_ghe K_he K_grm K_rm K_cpm K_cnt0 K_nhi K_nlo
          S_q0 S_q1 S_q2 S_q3 S_q4 S_q5 SOKstk SOKp SOKsh SOKT.
    intros mdl1 MI1 SBM1 HC1. rewrite unrestrict_mkst.
    replace (ms_mem (@mkst fx' R' (Z_to_bv 64 0x4fdc8) M' (seg_rom ASEGS))) with M' by reflexivity.
    replace (0x509cc%bv : word) with (Z_to_bv 64 0x509cc : word) by (apply bv_eq; reflexivity).
    pose proof (same_but_materialized_frame mdl' mdl1 SBM1) as SF1.
    destruct SF1 as (_ & Evm1 & Elz1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh1 & _ & _ & _ & Eeg1).
    remember (fr_P3r1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as M13 eqn:EM13.
    set (M1 := munrestrict Hd M' M13).
    pose proof (Rep_sbm bt st' Lc FF M0 mdl' mdl1 RP' MI1 SBM1) as RP1.
    pose proof (fr_P3r1_grows (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as GR13. feed GR13. rewrite <- EM13 in GR13.
    assert (VIS : forall a : word, Hd a = false -> M1 a = M13 a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_off; exact Ha).
    assert (HIDv : forall a : word, Hd a = true -> M1 a = M' a) by (intros a Ha; (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end); apply munrestrict_on; exact Ha).
    assert (MrM' : forall a : word, Hd a = false -> mrestrict Hd M' a = M' a) by (intros a Ha; apply mrestrict_off; exact Ha).
    assert (GR1 : mem_grows M' M1).
    { intros a Ha. destruct (Hd a) eqn:Eh; [rewrite (HIDv a Eh); exact Ha | rewrite (VIS a Eh)]. apply GR13. rewrite (MrM' a Eh). exact Ha. }
    assert (GRM1 : mem_grows M M1) by (eapply mem_grows_trans; [exact GRM | exact GR1]).
    pose proof (fr_P3r1_foot (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as P3F. feed P3F. rewrite <- EM13 in P3F.
    assert (FOOT1 : forall a : word, M1 a <> M' a ->
              (U S - 2272 <= U a < U S - 2128) \/ (U p <= U a < U p + 8) \/ (0x7fff8000 + U p / 8 <= U a < 0x7fff8000 + U p / 8 + up8 m / 8)).
    { intros a NE. destruct (Hd a) eqn:Eh; [exfalso; apply NE; apply HIDv; exact Eh|].
      rewrite (VIS a Eh) in NE. rewrite <- (MrM' a Eh) in NE. exact (P3F a NE). }
    assert (DIFF1 : forall a : word, M1 a <> M0 a -> X2 (U S) (U p) T m (U a) /\ M1 a <> None).
    { intros a NE. pose proof (u64_range a) as Ha. split; cycle 1.
      { destruct (M1 a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M0 a) eqn:E0; [|reflexivity]. exfalso.
        assert (D : M0 a <> None) by (rewrite E0; discriminate). apply GR0, GR1 in D. rewrite E1 in D. exact (D eq_refl). }
      (lazymatch goal with |- ?G => let G' := eval unfold X2 in G in change_no_check G' end). destruct (decide (M1 a = M' a)) as [E|N].
      - left. rewrite E in NE. exact (proj1 (DX a NE)).
      - destruct (FOOT1 a N) as [F|[F|F]]; [left; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); rewrite CP2 in F; lia | left; (lazymatch goal with |- ?G => let G' := eval unfold Xd in G in change_no_check G' end); lia | right; unfold sh_lo, sh_hi, SB in *; lia]. }
    (* [comment removed for export] *)
    apply (katD_bind ASEGS _ (refill24_post_k bt FXOK KR (X2 (U S) (U p) T m) st' Lc FF M1 mdl1 rf (at_ S (-2272)) (Z_to_bv 64 0x501ec))).
    { apply (HYP_REFILL fx' (X2 (U S) (U p) T m) st' Lc FF M1 mdl1 rf (at_ S (-2272)) (Z_to_bv 64 0x501ec) HFX').
      { rewrite Eh1. exact HH'. }
      { exact (model_ivs_wf_sbm mdl' mdl1 SBM1 MW'). }
      { exact W'. }
      { exists M0. split; [exact RP1 | exact DIFF1]. }
      { intros a Ha. unfold X2, Xd in Ha. rewrite CP2 in Ha.
        destruct Ha as [[Ha|[Ha|[Ha|Ha]]]|Ha]; [right; right; exists (U p), m; split; [exact HinP | lia] | right; right; exists (U p), m; split; [exact HinP | lia]
                                            | right; left; lia | left; lia | right; right; exists (U p), m; split; [exact HinP | right; right; exact Ha]]. }
      { exact ECA. }
      { destruct BD' as (_ & _ & BK). clear - BK KC1. lia. }                                (* [comment removed for export] *)
      { exact MUR1. }                                                                           (* [comment removed for export] *)
      { exact Z1. }
      { exact Z2. }
      { rewrite Z10. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC in G in change_no_check G' end). unorm. reflexivity. }
      { rewrite Z11. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold at_, T_PC, PC_SZ, BATCHCLASS in G in change_no_check G' end). unorm. lia. }
      { rewrite Z12. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. reflexivity. }
      { rewrite Z13. reflexivity. }
      { rewrite Z4. rewrite ?BT_ia. exact CP4. }                                            (* [comment removed for export] *)
      { rewrite at_u by lia. rewrite CP2. apply sp_mod16_2272. exact CP16. }
      { rewrite at_u by lia. rewrite CP2. lia. }
      { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). lia. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { intros a Ha. rewrite at_u in Ha by lia. split.
        - apply GRM1. apply store_ok1_heap; [lia|]. apply CPstk. rewrite <- CP2. lia.
        - eapply store_ok_mono; [exact GRM1|]. apply CPstk. rewrite <- CP2. lia. }
      { (* [comment removed for export] *)
        intros c' FAIL.
        destruct FAIL as (fx2 & st2 & Mf & mdl2 & R2 & Ec' & HFX2 & HH2 & W2 & (M02 & RP2 & DX2) & A02).
        subst c'.
        pose proof RP2 as (R1f & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R13f & R14f & _).
        rewrite BT_segs in R1f.
        destruct R14f as (B1f & B2f & _).
        destruct CELLSPIN as (CSP1 & CSP2 & CSP3).
        set (Hd2 := HID st2 mdl2).
        assert (NHs2 : forall z, 0 <= z < 2 ^ 64 -> (CEIL <= z \/ (AIMGLO <= z /\ z < AIMGHI)) -> Hd2 (Z_to_bv 64 z) = false).
        { intros z Hz Hr. apply (HID_off_zone bt st2 mdl2 z R13f Hz). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi asan_addrs] in G in change_no_check G' end). lia. }
        assert (EQ2 : forall a : word, ~ X2 (U S) (U p) T m (U a) -> Mf a = M02 a).
        { intros a Ha. destruct (decide (Mf a = M02 a)) as [E|N]; [exact E|]. exfalso. exact (Ha (proj1 (DX2 a N))). }
        assert (KS1 : rdn ASEGS (mrestrict Hd2 Mf) (Z_to_bv 64 0xff2b0) 8 = Some (LE8 (Z_to_bv 64 1))) by konst EQ2 R1f NHs2 XdC2 CSP1.
        assert (KS2 : rdn ASEGS (mrestrict Hd2 Mf) (Z_to_bv 64 0xff2b8) 8 = Some (LE8 (Z_to_bv 64 0x19909c))) by konst EQ2 R1f NHs2 XdC2 CSP2.
        assert (KS3 : rdn ASEGS (mrestrict Hd2 Mf) (Z_to_bv 64 0x19909c) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))) by konst EQ2 R1f NHs2 XdC2 CSP3.
        destruct (enq_spin_run (mrestrict Hd2 Mf) (seg_rom ASEGS) R2 A02 KS1 KS2 KS3) as (rs & RUNS).
        replace (0x501ec%bv : word) with (Z_to_bv 64 0x501ec : word) in RUNS by (apply bv_eq; reflexivity).
        apply (doomed_msteps_acct ASEGS Hd2 (HID_off_segments bt st2 Lc FF M02 mdl2 BT_ia RP2) asanF_segs_wx (a_aa st2)
                 (@mkst fx2 R2 (Z_to_bv 64 0x501ec) Mf (seg_rom ASEGS)) (@mkst fx2 rs (0x50228%bv : word) (mrestrict Hd2 Mf) (seg_rom ASEGS)) mdl2).
        { apply lazy_cover_HID. }
        { exact B1f. }
        { exact B2f. }
        { exact HH2. }
        { rewrite restrict_mkstF. exact RUNS. }
        intros mdl3 MI3 SBM3 HC3. rewrite unrestrict_mkst.
        pose proof (same_but_materialized_frame mdl2 mdl3 SBM3) as SF3.
        destruct SF3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Eh3 & _).
        apply doomed_to_spin; [apply enq_spin_to_spin | rewrite Eh3; exact HH2]. } }
    (* [comment removed for export] *)
    intros c' POST.
    destruct POST as (fx'' & st'' & M'' & mdl'' & R'' & ks & k & Ec' & HFX'' & HH'' & W'' & RX'' & ECA'' & Etq & Egq & Esec & Edep & Eia & Ekact & Eaa
                      & KEPT & CHG'' & LZ'' & RK & A0 & SEV'' & MW'' & HOLES).
    subst c'. apply katD_refl.
    destruct RX'' as (M0'' & RP'' & DX'').
    (* [comment removed for export] *)
    assert (STK : forall kk bs0, -2272 <= kk -> kk + 8 <= 0 -> rdn ASEGS M13 (at_ S kk) 8 = Some bs0 -> rdn ASEGS M'' (at_ S kk) 8 = Some bs0).
    { intros kk bs0 Hk1 Hk2 Hr. apply (rd_same ASEGS M'' M13); [| first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | exact Hr].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. rewrite (KEPT x); [| (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); left; lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | apply NST_stk; clear - Hx Hk1; lia].
      apply VIS. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply NHs; [apply u64_range | lia]. }
    pose proof (fr_P3r1_rdn_out (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as P3O. feed P3O. rewrite <- EM13 in P3O.
    assert (STKi : forall kk bs0, -56 <= kk -> kk + 8 <= 0 -> rdn ASEGS (mrestrict Hd M') (at_ S kk) 8 = Some bs0 -> rdn ASEGS M'' (at_ S kk) 8 = Some bs0).
    { intros kk bs0 Hk1 Hk2 Hr. apply STK; [lia | lia |].
      rewrite P3O; [exact Hr | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); lia]. }
    Ltac incs := apply in_cs; reflexivity.
    Ltac viaRK RK k X := etransitivity; [| exact X];
      match goal with |- getr _ ?x = getr _ _ => replace x with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end; apply RK; incs.
    pose proof (fr_P3r1_hdr16 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as P3H. feed P3H. rewrite <- EM13 in P3H.
    pose proof (fr_P3r1_shadow (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as P3S. feed P3S. rewrite <- EM13 in P3S.
    pose proof (fr_P3r1_e0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe0. feed Pe0. rewrite <- EM13 in Pe0.
    pose proof (fr_P3r1_e1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe1. feed Pe1. rewrite <- EM13 in Pe1.
    pose proof (fr_P3r1_e2 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe2. feed Pe2. rewrite <- EM13 in Pe2.
    pose proof (fr_P3r1_e3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe3. feed Pe3. rewrite <- EM13 in Pe3.
    pose proof (fr_P3r1_e4 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe4. feed Pe4. rewrite <- EM13 in Pe4.
    pose proof (fr_P3r1_e5 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe5. feed Pe5. rewrite <- EM13 in Pe5.
    pose proof (fr_P3r1_e6 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pe6. feed Pe6. rewrite <- EM13 in Pe6.
    pose proof (fr_P3r1_cb0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pcb0. feed Pcb0. rewrite <- EM13 in Pcb0.
    pose proof (fr_P3r1_cb1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pcb1. feed Pcb1. rewrite <- EM13 in Pcb1.
    pose proof (fr_P3r1_q0 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq0. feed Pq0. rewrite <- EM13 in Pq0.
    pose proof (fr_P3r1_q1 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq1. feed Pq1. rewrite <- EM13 in Pq1.
    pose proof (fr_P3r1_q2 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq2. feed Pq2. rewrite <- EM13 in Pq2.
    pose proof (fr_P3r1_q3 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq3. feed Pq3. rewrite <- EM13 in Pq3.
    pose proof (fr_P3r1_q4 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq4. feed Pq4. rewrite <- EM13 in Pq4.
    pose proof (fr_P3r1_q5 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq5. feed Pq5. rewrite <- EM13 in Pq5.
    pose proof (fr_P3r1_q6 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq6. feed Pq6. rewrite <- EM13 in Pq6.
    pose proof (fr_P3r1_q7 (mrestrict Hd M') S p (getr R 22) T m (up8 m) id) as Pq7. feed Pq7. rewrite <- EM13 in Pq7.
    (lazymatch goal with |- ?G => let G' := eval unfold putR1_post in G in change_no_check G' end). fold S. rewrite BT_ia.
    exists fx'', R'', M'', M0'', mdl'', st'', ks, k.
    split; [reflexivity|]. split; [exact HFX''|]. split; [exact HH''|]. split; [exact MW''|]. split; [exact W''|]. split; [exact RP''|].
    split. { unfold bounds in BD' |- *. rewrite Ekact. exact BD'. }
    split; [exact (hp_neut bt HP HPc FAM h st' st'' HLE (proj1 HOLES) (proj2 HOLES) Ekact)|]. split; [exact ECA''|]. split; [exact Etq|]. split; [exact Egq|]. split; [exact DX''|].
    split.
    { (* [comment removed for export] *)
      intros a NE. pose proof (u64_range a) as Ha. destruct (decide (M'' a = M1 a)) as [E|N].
      + rewrite E in NE |- *. split; cycle 1.
        { destruct (M1 a) eqn:E1; [discriminate|]. exfalso. apply NE. destruct (M a) eqn:EMa; [|reflexivity]. exfalso.
          assert (X : M a <> None) by (rewrite EMa; discriminate). apply GRM1 in X. rewrite E1 in X. exact (X eq_refl). }
        destruct (decide (M1 a = M' a)) as [E2|N2].
        * rewrite E2 in NE. destruct (CHG a NE) as [Cg _]. rewrite CP2 in Cg |- *. (lazymatch goal with |- ?G => let G' := eval unfold X2 in G in change_no_check G' end).
          destruct Cg as [Cg|[Cg|[Cg|Cg]]]; [left; left; exact Cg | right; left; lia | right; right; left; exact Cg | right; right; right; exact Cg].
        * destruct (FOOT1 a N2) as [F|[F|F]]; (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); rewrite CP2 in *.
          -- right; left. lia.
          -- left; left. lia.
          -- left; right. unfold sh_lo, sh_hi, SB in *. lia.
      + destruct (CHG'' a N) as [Cg D]. split; [| exact D]. rewrite BT_ia in Cg. rewrite at_u in Cg by lia. rewrite CP2 in Cg |- *.
        destruct Cg as [Cg|[Cg|Cg]]; [right; left; lia | right; right; left; exact Cg | right; right; right; exact Cg]. }
    split.
    { (* [comment removed for export] *) rewrite (KEPT (at_ p (-16))); [| (lazymatch goal with |- ?G => let G' := eval unfold X2, Xd in G in change_no_check G' end); first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | apply NST_p; rewrite at_u by lia; clear - U8a Lp3; lia].
      rewrite VIS by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply NHp; wd_ulia). rewrite P3H. rewrite MrM' by ((lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); apply NHp; wd_ulia). exact Hb16. }
    split.
    { (* [comment removed for export] *) intros i Hi. rewrite KEPT; [| unfold X2, sh_lo, sh_hi, SB in *; right; wd_ulia | rewrite at_u by lia; unfold sh_lo, sh_hi, SB in *; wd_ulia | apply NST_sh; unfold sh_lo, sh_hi, SB in *; wd_ulia].
      rewrite VIS by (apply NHsh; unfold sh_lo, sh_hi, SB in *; lia). (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). apply P3S. exact Hi. }
    split. { repeat split; (apply STK; [lia | lia | assumption]). }
    split. { repeat split; (apply STK; [lia | lia | assumption]). }
    split. { split; [apply STKi; [lia | lia | fold ra0; rewrite CP1; exact S_i0] | repeat split; (apply STKi; [lia | lia | assumption])]. }
    split.
    { split; [exact A0|]. split; [viaRK RK 2 Z2|]. split; [viaRK RK 8 Z8|]. split; [viaRK RK 9 Z9|]. split; [viaRK RK 18 Z18|].
      split; [viaRK RK 19 Z19|]. split; [viaRK RK 21 Z21|]. split; [viaRK RK 22 Z22|]. split; [viaRK RK 3 (eq_trans Z3 Y3)|]. split; [viaRK RK 4 Z4|].
      split; [viaRK RK 23 (eq_trans Z23 Y23)|]. split; [viaRK RK 24 (eq_trans Z24 Y24)|]. split; [viaRK RK 25 (eq_trans Z25 Y25)|].
      split; [viaRK RK 26 (eq_trans Z26 Y26)|]. viaRK RK 27 (eq_trans Z27 Y27). }
    split.
    { eapply same_except_vm_trans; [exact SEV|]. eapply same_except_vm_trans; [apply same_but_materialized_except_vm; exact SBM1 | exact SEV'']. }
    intros a Ha. rewrite <- BT_ia in Ha. rewrite (LZ'' a Ha). rewrite BT_ia in Ha. transitivity (lzb mdl' a); [(lazymatch goal with |- ?G => let G' := eval unfold lzb in G in change_no_check G' end); rewrite Elz1; reflexivity | exact (LZ a Ha)].
  Qed.
End PUTR1.
