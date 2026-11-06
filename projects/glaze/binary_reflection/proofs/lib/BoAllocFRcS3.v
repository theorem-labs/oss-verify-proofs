(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFHs.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac hs_zbase e := lazymatch e with
  | (?x + _)%Z => hs_zbase x
  | (?x - _)%Z => hs_zbase x
  | _ => e
  end.
Ltac hs_sok_base a :=
  lazymatch a with
  | at_ ?s _ => s
  | Z_to_bv _ ?e => let z := hs_zbase e in lazymatch z with bv_unsigned ?s => s | _ => z end
  | _ => a
  end.
Ltac any_ok_r :=
  first [ repeat (eapply store_ok_mono; [apply wbytes_grows|]);
          lazymatch goal with
          | |- store_ok _ _ ?a _ = true =>
              let ba := hs_sok_base a in
              match goal with
              | H : store_ok ?sg ?m ?b ?N = true |- _ =>
                  let bb := hs_sok_base b in
                  constr_eq ba bb;
                  first [ exact H | apply (wd_store_ok_sub3 sg m b _ N); [ solve [sok_fast] | exact H ] ]
              end
          end
        | any_ok ].
End BoAllocFHs.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoDepotAlloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.Bo_code_8cef4_8dab4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoDepotStore.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import BoAllocFHs.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac stk_ok ::= any_ok_r.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section TAIL.
  Variables (MT rom : word -> option byte) (sp ra s0v S idxp blkd : word) (start : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-16).
  Hypothesis H5 : getr regs 5 = Z_to_bv 64 (start / 2 ^ 20).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 start.
  Hypothesis H11 : getr regs 11 = S.
  Hypothesis H12 : getr regs 12 = idxp.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hstart : (0 <= start < 2 ^ 32)%Z.
  Hypothesis HS : (U S + 2 ^ 20 <= 2 ^ 32 /\ (U S + 2 ^ 20 <= U sp - 16 \/ U sp <= U S))%Z.
  Hypothesis Hidx : ((U idxp + 8 <= U sp - 16 \/ U sp <= U idxp) /\ (U idxp + 8 <= U S \/ U S + 2 ^ 20 <= U idxp) /\ U idxp + 8 < 2 ^ 64)%Z.
  Hypothesis SOKi : store_ok BSEGS MT idxp 8 = true.
  Hypothesis Rblk : rdn BSEGS MT (Z_to_bv 64 (U S + 16 * (start / 2 ^ 20) + 16)) 8 = Some (LE8 blkd).
  Hypothesis Rra : rdn BSEGS MT (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis Rs0 : rdn BSEGS MT (at_ sp (-16)) 8 = Some (LE8 s0v).

  Definition sa_tmem (MT : word -> option byte) (idxp : word) (start : Z) : word -> option byte := wbytes MT idxp (LE8 (Z_to_bv 64 start)).

  Lemma sa_tmem_rd : forall (a : word) (n : nat) bs, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U a + Z.of_nat n <= U idxp \/ U idxp + 8 <= U a)%Z ->
    rdn BSEGS MT a n = Some bs -> rdn BSEGS (sa_tmem MT idxp start) a n = Some bs.
  Proof using Hidx S sp.
    intros a n bs A1 A2 Hr. destruct Hidx as (_ & _ & I3). (lazymatch goal with |- ?G => let G' := eval unfold sa_tmem in G in change_no_check G' end).
    rewrite rdn_wbytes_out; [exact Hr | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia.
  Qed.


  Lemma sa_tail_cpre : blkd = Z_to_bv 64 0 ->
    exists r, msteps BSEGS (mkst regs (0x8d044 : word) MT rom) (mkst r (0x8da00 : word) (sa_tmem MT idxp start) rom)
      /\ getr r 1 = (0x8d12c : word) /\ getr r 10 = Z_to_bv 64 (U S + 16 * (start / 2 ^ 20) + 16) /\ getr r 2 = at_ sp (-16) /\ getr r 8 = Z_to_bv 64 start
      /\ regs_agree (fun i : reg => In i [1; 10; 12]) regs r.
  Proof using Rblk SOKi Hidx HS Hstart Hsp H12 H11 H8 H5 H2.
    intros EB.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range idxp) as Hir.
    destruct Hsp as [S1 S2]. destruct HS as (S32 & SF). destruct Hidx as (I1 & I2 & I3).
    assert (Q20 : (0 <= start / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (sa_tmem_rd (Z_to_bv 64 (U S + 16 * (start / 2 ^ 20) + 16)) 8 _ ltac:(first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]) ltac:(first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]) Rblk) as RblkT.
    rewrite EB in RblkT.
    wd_eexists. split.
    - av F_8d044 D_8d044 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv start) by lia; rewrite Z.div_small by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk F_8d048 D_8d048 ltac:(condz).              (* [comment removed for export] *)
      fsd F_8d060 D_8d060 idxp.                        (* [comment removed for export] *)
      change (wbytes MT idxp _) with (sa_tmem MT idxp start).
      av F_8d064 D_8d064 (Z_to_bv 64 (16 * (start / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv (start / 2 ^ 20)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8d068 D_8d068 (Z_to_bv 64 (U S + 16 * (start / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (16 * (start / 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8d06c D_8d06c (Z_to_bv 64 0) RblkT.       (* [comment removed for export] *)
      ab_tk F_8d070 D_8d070 ltac:(condz).              (* [comment removed for export] *)
      av F_8d124 D_8d124 (Z_to_bv 64 (U S + 16 * (start / 2 ^ 20) + 16)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      an F_8d128 D_8d128.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; reflexivity).
  Qed.
End TAIL.

Section CPOST.
  Variables (MC rom : word -> option byte) (sp ra s0v newblk : word) (start : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-16).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 start.
  Hypothesis H10 : getr regs 10 = newblk.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hstart : (0 <= start < 2 ^ 32)%Z.
  Hypothesis Rra : rdn BSEGS MC (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis Rs0 : rdn BSEGS MC (at_ sp (-16)) 8 = Some (LE8 s0v).

  Lemma sa_tail_cpost :
    exists r, msteps BSEGS (mkst regs (0x8d12c : word) MC rom) (mkst r ra MC rom)
      /\ getr r 10 = Z_to_bv 64 (U newblk + 8 * (start mod 2 ^ 20)) /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 10]) regs r.
  Proof using Rs0 Rra Hstart Hret Hsp H10 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range newblk) as Hbr. destruct Hsp as [S1 S2].
    assert (M20 : (0 <= start mod 2 ^ 20 < 2 ^ 20)%Z) by (apply Z.mod_pos_bound; lia).
    wd_eexists. split.
    - an F_8d12c D_8d12c.                              (* [comment removed for export] *)
      an F_8d074 D_8d074. rewrite (sa_shl44 start Hstart).  (* [comment removed for export] *)
      an F_8d078 D_8d078. rewrite (sa_shr41 (start mod 2 ^ 20) M20).   (* [comment removed for export] *)
      av F_8d07c D_8d07c (Z_to_bv 64 (U newblk + 8 * (start mod 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (8 * (start mod 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8d080 D_8d080 ra Rra.                     (* [comment removed for export] *)
      cld8 F_8d084 D_8d084 s0v Rs0.                    (* [comment removed for export] *)
      an F_8d088 D_8d088.                              (* [comment removed for export] *)
      aret F_8d08c D_8d08c ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End CPOST.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sa_and20 : forall t, (0 <= t < 2 ^ 32)%Z -> v_and (Z_to_bv 64 t) (Z_to_bv 64 1048575) = Z_to_bv 64 (t mod 2 ^ 20).
Proof using. intros t Ht. (lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end). rewrite (u_Z2bv t), (u_Z2bv 1048575) by lia. change 1048575%Z with (Z.ones 20). rewrite Z.land_ones by lia. reflexivity. Qed.

Definition sa_inf (tot : Z) : Z := (2 ^ 20 - tot mod 2 ^ 20)%Z.
Definition sa_smem (M : word -> option byte) (sp ra s0v S packp : word) (tot cnt so0 so1 pk : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v))
    S (LE8 (Z_to_bv 64 (tot + cnt))))
    (st_cell S tot) (LE4 (v_add (Z_to_bv 64 so0) (Z_to_bv 64 (sa_inf tot)))))
    packp (LE8 (Z_to_bv 64 (pk + st_full so0 (sa_inf tot)))))
    (st_cell S (tot + cnt)) (LE4 (v_add (Z_to_bv 64 so1) (Z_to_bv 64 (cnt - sa_inf tot)))))
    packp (LE8 (Z_to_bv 64 (pk + st_full so0 (sa_inf tot) + st_full so1 (cnt - sa_inf tot)))))
    S (LE8 (Z_to_bv 64 (tot + cnt + cnt))).

Ltac wo := rewrite rdn_wbytes_out by (wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia).

Section STRAD.
  Variables (M rom : word -> option byte) (sp ra s0v S idxp packp : word) (tot cnt so0 so1 pk : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H10 : getr regs 10 = S.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 cnt.
  Hypothesis H12 : getr regs 12 = idxp.
  Hypothesis H13 : getr regs 13 = packp.
  Hypothesis Hsp : (2 ^ 32 + 16 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hcnt : (1 <= cnt <= 256)%Z.
  Hypothesis Htot : (0 <= tot /\ tot + cnt + cnt <= 2 ^ 32)%Z.
  Hypothesis Hq1 : ((tot + cnt - 1) / 2 ^ 20 = tot / 2 ^ 20 + 1)%Z.                 (* [comment removed for export] *)
  Hypothesis Hso : (0 <= so0 < 2 ^ 32 /\ 0 <= so1 < 2 ^ 32 /\ 0 <= pk < 2 ^ 32)%Z.
  Hypothesis HS : (U S mod 8 = 0 /\ U S + 2 ^ 20 <= 2 ^ 32)%Z.
  Hypothesis Hpack : ((U sp <= U packp \/ U packp + 8 <= U sp - 16) /\ 2 ^ 32 <= U packp /\ U packp + 8 < 2 ^ 64)%Z.
  Hypothesis Rtot : rdn BSEGS M S 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rso0 : rdn BSEGS M (st_cell S tot) 4 = Some (LE4 (Z_to_bv 64 so0)).
  Hypothesis Rso1 : rdn BSEGS M (st_cell S (tot + cnt)) 4 = Some (LE4 (Z_to_bv 64 so1)).
  Hypothesis Rpk : rdn BSEGS M packp 8 = Some (LE8 (Z_to_bv 64 pk)).
  Hypothesis SOKS : store_ok BSEGS M S 8 = true.
  Hypothesis SOK0 : store_ok BSEGS M (st_cell S tot) 4 = true.
  Hypothesis SOK1 : store_ok BSEGS M (st_cell S (tot + cnt)) 4 = true.
  Hypothesis SOKp : store_ok BSEGS M packp 8 = true.
  Hypothesis Hstk : store_ok BSEGS M (at_ sp (-16)) 16 = true.

  Lemma sa_strad_arith :
    (0 <= tot mod 2 ^ 20 < 2 ^ 20 /\ 1 <= sa_inf tot <= cnt - 1 /\ (tot + cnt) / 2 ^ 20 = tot / 2 ^ 20 + 1 /\ (tot + cnt + cnt - 1) / 2 ^ 20 = tot / 2 ^ 20 + 1
     /\ 0 <= tot / 2 ^ 20 /\ tot / 2 ^ 20 + 1 < 2 ^ 12)%Z.
  Proof using Hq1 Htot Hcnt S.
    destruct Htot as [T0 T1]. (lazymatch goal with |- ?G => let G' := eval unfold sa_inf in G in change_no_check G' end).
    pose proof (Z.div_mod tot (2 ^ 20) ltac:(lia)) as E1. pose proof (Z.mod_pos_bound tot (2 ^ 20) ltac:(lia)) as B1.
    pose proof (Z.div_mod (tot + cnt - 1) (2 ^ 20) ltac:(lia)) as E2. pose proof (Z.mod_pos_bound (tot + cnt - 1) (2 ^ 20) ltac:(lia)) as B2.
    rewrite Hq1 in E2.
    assert (Q0 : (0 <= tot / 2 ^ 20)%Z) by (apply Z.div_pos; lia).
    split; [exact B1|]. split; [lia|].
    split. { symmetry. apply (Z.div_unique (tot + cnt) (2 ^ 20) (tot / 2 ^ 20 + 1) (tot + cnt - 2 ^ 20 * (tot / 2 ^ 20 + 1))); lia. }
    split. { symmetry. apply (Z.div_unique (tot + cnt + cnt - 1) (2 ^ 20) (tot / 2 ^ 20 + 1) (tot + cnt + cnt - 1 - 2 ^ 20 * (tot / 2 ^ 20 + 1))); lia. }
    split; [exact Q0|].
    assert (tot / 2 ^ 20 < 2 ^ 12 - 1)%Z; [| lia]. apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma sa_head_strad :
    exists r, msteps BSEGS (mkst regs (0x8d018 : word) M rom) (mkst r (0x8d044 : word) (sa_smem M sp ra s0v S packp tot cnt so0 so1 pk) rom)
      /\ getr r 2 = at_ sp (-16) /\ getr r 5 = Z_to_bv 64 ((tot + cnt) / 2 ^ 20) /\ getr r 8 = Z_to_bv 64 (tot + cnt)
      /\ getr r 11 = S /\ getr r 12 = idxp
      /\ regs_agree (fun i : reg => In i [2; 5; 6; 7; 8; 10; 11; 14; 15; 16; 17; 28]) regs r.
  Proof using Hstk SOKp SOK1 SOK0 SOKS Rpk Rso1 Rso0 Rtot Hpack HS Hso Hq1 Htot Hcnt Hsp H13 H12 H11 H10 H8 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range packp) as Hpr.
    destruct Hsp as [S1 S2]. destruct Htot as [T0 T1]. destruct Hso as (SO0 & SO1 & PK). destruct HS as [S8 S32]. destruct Hpack as (P1 & P32 & P2).
    destruct sa_strad_arith as (M20 & INF & Q2 & Q3 & Q0 & Q12).
    set (inf := sa_inf tot) in *. set (q := (tot / 2 ^ 20)%Z) in *.
    assert (Uc0 : U (st_cell S tot) = (U S + 16 * q + 24)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); fold q; rewrite u_Z2bv by lia; reflexivity).
    assert (Uc1 : U (st_cell S (tot + cnt)) = (U S + 16 * (q + 1) + 24)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite Q2; rewrite u_Z2bv by lia; reflexivity).
    assert (Usp8 : U (at_ sp (-8)) = (U sp - 8)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (Usp16 : U (at_ sp (-16)) = (U sp - 16)%Z) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (S4 : (U S mod 4 = 0)%Z).
    { pose proof (Z.div_mod (U S) 8 ltac:(lia)) as E. rewrite S8 in E. rewrite E.
      replace (8 * (U S / 8) + 0)%Z with ((2 * (U S / 8)) * 4)%Z by lia. apply Z_mod_mult. }
    assert (AL0 : (U (st_cell S tot) mod 4 = 0)%Z).
    { rewrite Uc0. replace (U S + 16 * q + 24)%Z with (U S + (4 * q + 6) * 4)%Z by lia. rewrite Z_mod_plus_full. exact S4. }
    assert (AL1 : (U (st_cell S (tot + cnt)) mod 4 = 0)%Z).
    { rewrite Uc1. replace (U S + 16 * (q + 1) + 24)%Z with (U S + (4 * (q + 1) + 6) * 4)%Z by lia. rewrite Z_mod_plus_full. exact S4. }
    assert (F0 : (0 <= st_full so0 inf <= 1)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); destruct (inf + so0 =? 1048576)%Z; lia).
    assert (F1 : (0 <= st_full so1 (cnt - inf) <= 1)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); destruct (cnt - inf + so1 =? 1048576)%Z; lia).
    set (MF := wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)).
    set (MA := wbytes MF S (LE8 (Z_to_bv 64 (tot + cnt)))).
    set (MB := wbytes MA (st_cell S tot) (LE4 (v_add (Z_to_bv 64 so0) (Z_to_bv 64 inf)))).
    set (MC := wbytes MB packp (LE8 (Z_to_bv 64 (pk + st_full so0 inf)))).
    set (MD := wbytes MC (st_cell S (tot + cnt)) (LE4 (v_add (Z_to_bv 64 so1) (Z_to_bv 64 (cnt - inf))))).
    set (ME := wbytes MD packp (LE8 (Z_to_bv 64 (pk + st_full so0 inf + st_full so1 (cnt - inf))))).
    assert (GRF : mem_grows M MF) by ((lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end); do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (GRA : mem_grows M MA) by (eapply mem_grows_trans; [exact GRF | apply wbytes_grows]).
    assert (GRB : mem_grows M MB) by (eapply mem_grows_trans; [exact GRA | apply wbytes_grows]).
    assert (GRC : mem_grows M MC) by (eapply mem_grows_trans; [exact GRB | apply wbytes_grows]).
    assert (GRD : mem_grows M MD) by (eapply mem_grows_trans; [exact GRC | apply wbytes_grows]).
    assert (GRE : mem_grows M ME) by (eapply mem_grows_trans; [exact GRD | apply wbytes_grows]).
    assert (RtotF : rdn BSEGS MF S 8 = Some (LE8 (Z_to_bv 64 tot))) by ((lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end); do 2 wo; exact Rtot).
    assert (Rso0A : rdn BSEGS MA (st_cell S tot) 4 = Some (LE4 (Z_to_bv 64 so0))) by ((lazymatch goal with |- ?G => let G' := eval unfold MA, MF in G in change_no_check G' end); do 3 wo; exact Rso0).
    assert (RpkB : rdn BSEGS MB packp 8 = Some (LE8 (Z_to_bv 64 pk))) by ((lazymatch goal with |- ?G => let G' := eval unfold MB, MA, MF in G in change_no_check G' end); do 4 wo; exact Rpk).
    assert (Rso1C : rdn BSEGS MC (st_cell S (tot + cnt)) 4 = Some (LE4 (Z_to_bv 64 so1))) by ((lazymatch goal with |- ?G => let G' := eval unfold MC, MB, MA, MF in G in change_no_check G' end); do 5 wo; exact Rso1).
    assert (RpkD : rdn BSEGS MD packp 8 = Some (LE8 (Z_to_bv 64 (pk + st_full so0 inf)))) by ((lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end); wo; (lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end); apply rdn_wbytes_hit8; lia).
    assert (RtotE : rdn BSEGS ME S 8 = Some (LE8 (Z_to_bv 64 (tot + cnt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold ME, MD, MC, MB in G in change_no_check G' end); do 4 wo; (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply rdn_wbytes_hit8; lia).
    assert (B4a : bytes_le_to_Z (LE4 (Z_to_bv 64 so0)) = U (Z_to_bv 64 so0)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (B4b : bytes_le_to_Z (LE4 (Z_to_bv 64 so1)) = U (Z_to_bv 64 so1)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (EA : v_add (Z_to_bv 64 tot) (Z_to_bv 64 cnt) = Z_to_bv 64 (tot + cnt)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv tot), (u_Z2bv cnt) by lia; reflexivity).
    assert (EG : v_add (Z_to_bv 64 (tot + cnt)) (Z_to_bv 64 cnt) = Z_to_bv 64 (tot + cnt + cnt)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (tot + cnt)), (u_Z2bv cnt) by lia; reflexivity).
    wd_eexists. split.
    - an F_8d018 D_8d018.                              (* [comment removed for export] *)
      fsd F_8d01c D_8d01c (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8d020 D_8d020 (at_ sp (-16)).              (* [comment removed for export] *)
      change (wbytes (wbytes M _ _) _ _) with MF.
      an F_8d024 D_8d024.                              (* [comment removed for export] *)
      an F_8d028 D_8d028.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 (Z_to_bv 64 tot)) (v := Z_to_bv 64 tot);
          [exact F_8d02c | reflexivity | exact D_8d02c
          | gres; rwH; exact S8
          | gres; rwH; exact RtotF
          | apply bytes_le_to_Z_8
          | gres; rwH; eapply store_ok_mono; [exact GRF | exact SOKS]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. rewrite EA. change (wbytes MF S _) with MA.
      av F_8d030 D_8d030 (Z_to_bv 64 (cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d034 D_8d034 (Z_to_bv 64 q) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8d038 D_8d038 (Z_to_bv 64 (tot + cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d03c D_8d03c (Z_to_bv 64 (q + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt - 1)) by lia; rewrite Hq1; reflexivity).   (* [comment removed for export] *)
      ab_tk F_8d040 D_8d040 ltac:(condz).              (* [comment removed for export] *)
      an F_8d090 D_8d090.                              (* [comment removed for export] *)
      ab_ft F_8d094 D_8d094 ltac:(condz).              (* [comment removed for export] *)
      an F_8d098 D_8d098.                              (* [comment removed for export] *)
      av F_8d09c D_8d09c (Z_to_bv 64 1048575) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      an F_8d0a0 D_8d0a0. rewrite (sa_and20 tot ltac:(lia)).   (* [comment removed for export] *)
      av F_8d0a4 D_8d0a4 (Z_to_bv 64 (16 * q)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv q) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8d0a8 D_8d0a8 (Z_to_bv 64 inf) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub, inf, sa_inf in G in change_no_check G' end); rewrite (u_Z2bv (tot mod 2 ^ 20)) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8d0ac D_8d0ac (Z_to_bv 64 (U S + 16 + 16 * q)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d0b0 D_8d0b0 (st_cell S tot) ltac:(apply bv_eq; rewrite Uc0; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_w with (bs := LE4 (Z_to_bv 64 so0)) (v := Z_to_bv 64 so0);
          [exact F_8d0b4 | reflexivity | exact D_8d0b4
          | gres; rwH; exact AL0
          | gres; rwH; exact Rso0A
          | exact B4a
          | gres; rwH; eapply store_ok_mono; [exact GRA | exact SOK0]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. change (wbytes MA (st_cell S tot) _) with MB.
      av F_8d0b8 D_8d0b8 (Z_to_bv 64 (16 * (q + 1))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv (q + 1)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8d0bc D_8d0bc (Z_to_bv 64 (U S + 16 + 16 * (q + 1))) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d0c0 D_8d0c0 (Z_to_bv 64 (cnt - inf)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); rewrite (u_Z2bv cnt), (u_Z2bv inf) by lia; reflexivity).   (* [comment removed for export] *)
      an F_8d0c4 D_8d0c4.                              (* [comment removed for export] *)
      an F_8d0c8 D_8d0c8. rewrite (st_zext so0 SO0).   (* [comment removed for export] *)
      av F_8d0cc D_8d0cc (Z_to_bv 64 (inf + so0)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv inf), (u_Z2bv so0) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8d0d0 D_8d0d0 (Z_to_bv 64 pk) RpkB.       (* [comment removed for export] *)
      av F_8d0d4 D_8d0d4 (st_cell S (tot + cnt)) ltac:(apply bv_eq; rewrite Uc1; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      an F_8d0d8 D_8d0d8.                              (* [comment removed for export] *)
      av F_8d0dc D_8d0dc (Z_to_bv 64 (st_full so0 inf)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); apply st_seqz; lia).   (* [comment removed for export] *)
      av F_8d0e0 D_8d0e0 (Z_to_bv 64 (pk + st_full so0 inf)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv pk), (u_Z2bv (st_full so0 inf)) by lia; reflexivity).   (* [comment removed for export] *)
      fsd F_8d0e4 D_8d0e4 packp.                       (* [comment removed for export] *)
      change (wbytes MB packp _) with MC.
      chain_step; [reflexivity
        | eapply step_amoadd_w with (bs := LE4 (Z_to_bv 64 so1)) (v := Z_to_bv 64 so1);
          [exact F_8d0e8 | reflexivity | exact D_8d0e8
          | gres; rwH; exact AL1
          | gres; rwH; exact Rso1C
          | exact B4b
          | gres; rwH; eapply store_ok_mono; [exact GRC | exact SOK1]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. change (wbytes MC (st_cell S (tot + cnt)) _) with MD.
      cld8 F_8d0ec D_8d0ec (Z_to_bv 64 (pk + st_full so0 inf)) RpkD.   (* [comment removed for export] *)
      an F_8d0f0 D_8d0f0.                              (* [comment removed for export] *)
      an F_8d0f4 D_8d0f4. rewrite (st_zext so1 SO1).   (* [comment removed for export] *)
      av F_8d0f8 D_8d0f8 (Z_to_bv 64 (cnt - inf + so1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (cnt - inf)), (u_Z2bv so1) by lia; reflexivity).   (* [comment removed for export] *)
      an F_8d0fc D_8d0fc.                              (* [comment removed for export] *)
      av F_8d100 D_8d100 (Z_to_bv 64 (st_full so1 (cnt - inf))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); apply st_seqz; lia).   (* [comment removed for export] *)
      av F_8d104 D_8d104 (Z_to_bv 64 (pk + st_full so0 inf + st_full so1 (cnt - inf)))
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (pk + st_full so0 inf)), (u_Z2bv (st_full so1 (cnt - inf))) by lia; reflexivity).   (* [comment removed for export] *)
      fsd F_8d108 D_8d108 packp.                       (* [comment removed for export] *)
      change (wbytes MD packp _) with ME.
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 (Z_to_bv 64 (tot + cnt))) (v := Z_to_bv 64 (tot + cnt));
          [exact F_8d10c | reflexivity | exact D_8d10c
          | gres; rwH; exact S8
          | gres; rwH; exact RtotE
          | apply bytes_le_to_Z_8
          | gres; rwH; eapply store_ok_mono; [exact GRE | exact SOKS]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. rewrite EG. change (wbytes ME S _) with (sa_smem M sp ra s0v S packp tot cnt so0 so1 pk).
      av F_8d110 D_8d110 (Z_to_bv 64 ((tot + cnt) / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt)) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8d114 D_8d114 (Z_to_bv 64 (tot + cnt + cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8d118 D_8d118 (Z_to_bv 64 ((tot + cnt) / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt + cnt - 1)) by lia; rewrite Q3, Q2; reflexivity).   (* [comment removed for export] *)
      ab_tk F_8d11c D_8d11c ltac:((lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End STRAD.

End FPGen.
End BoDepotAlloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRc4c.BoAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.BoCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.Bo_code_77ff8_78b0c.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
Import BoAllocFHs.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac stk_ok ::= any_ok_r.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Ltac regneq := apply reg_neq_of_eqb; reflexivity.
Ltac pc4 := apply bv_eq; reflexivity.
Ltac fsb F D aa bb :=
  chain_step; [reflexivity
    | eapply MmapSim.step_sb_at with (a := aa) (b := bb);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; first [reflexivity | f_equal; lia | apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, at_ in G in change_no_check G' end); wd_ulia]
      | gres; rwH; reflexivity
      | first [reflexivity | apply bv_eq; unorm; reflexivity]
      | first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.
Ltac famo F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_amoadd_d with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [reflexivity | lia]
      | rd_addr Hr | exact Hv | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Lemma sok_secinst : forall m, store_ok BSEGS m (Z_to_bv 64 0x10ab98) 656 = true.
Proof using. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.
Lemma sok_seclock3 : forall m, store_ok BSEGS m (Z_to_bv 64 0x10ae00) 4 = true.
Proof using. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.

Lemma v_andi_255_andS3 : forall x : word, v_andi x 255 = v_and x (Z_to_bv 64 255).
Proof using.
  intros x. pose proof (u64_range x). rewrite <- (Z_to_bv_bv_unsigned 64 x) at 1. rewrite v_andi_Z by lia.
  rewrite <- (Z_to_bv_bv_unsigned 64 x) at 2. rewrite v_and_Z by lia. reflexivity.
Qed.
Lemma lock_byte0S3 : forall (b0 b1 b2 b3 : byte) (v : word),
  bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v -> v_andi (v_lw v) 255 = Z_to_bv 64 (bv_unsigned b0).
Proof using.
  intros b0 b1 b2 b3 v Hv. rewrite v_andi_255_andS3.
  rewrite (and_mask_byte [b0; b1; b2; b3] v (Z_to_bv 64 255) 0 eq_refl Hv ltac:(lia) ltac:(reflexivity)).
  (lazymatch goal with |- ?G => let G' := eval cbn [nth Z.of_nat Z.mul] in G in change_no_check G' end). rewrite Z.mul_1_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma sd_lock_4eea4 : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 16 = Z_to_bv 64 0x10ae00 -> getr regs 15 = Z_to_bv 64 255 -> getr regs 17 = Z_to_bv 64 1 ->
  rdn BSEGS mem (Z_to_bv 64 0x10ae00) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps BSEGS (mkst regs (0x4eea4 : word) mem rom)
    (mkst (regupd (regupd regs 5 (v_lw v)) 6 (Z_to_bv 64 0)) (0x4eec0 : word)
          (wbytes mem (Z_to_bv 64 0x10ae00) [Z_to_bv 8 1; b1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H16 H15 H17 Hrd Hv.
  pose proof (xchg_byte_run BSEGS regs (0x4eea4 : word) (0x4eea8 : word) (0x4eeac : word) (0x4eeb0 : word)
                (0x4eeb4 : word) (0x4eeb8 : word) (0x4eebc : word) (0x4eec0 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 5 16 6 17 15 _ [b0; b1; b2; b3] v 0%nat 1%Z
                F_4eea4 eq_refl D_4eea4 F_4eea8 eq_refl D_4eea8 F_4eeac eq_refl D_4eeac F_4eeb0 eq_refl D_4eeb0
                F_4eeb4 eq_refl D_4eeb4 F_4eeb8 eq_refl D_4eeb8 F_4eebc eq_refl D_4eebc) as R.
  rewrite H16, H15, H17 in R. cbn [firstn skipn app] in R.
  apply R; clear R; first [regneq | pc4 | apply sok_seclock3 | unorm; reflexivity | lia | assumption].
Qed.

(* [comment removed for export] *)
Definition fr_sd1 (mem : word -> option byte) (S ra0 s0v s1v s2v : word) (b1 b2 b3 : byte) (len ptr i last : Z) (wnf wca w16 w24 : word)
  : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2408)) (LE8 ra0))
    (at_ S (-2416)) (LE8 s0v))
    (at_ S (-2424)) (LE8 s1v))
    (at_ S (-2432)) (LE8 s2v))
    (Z_to_bv 64 0x10ae00) [Z_to_bv 8 1; b1; b2; b3])
    (Z_to_bv 64 (0x10ab98 + 56)) (LE8 (Z_to_bv 64 (len - 1))))
    (Z_to_bv 64 (0x10ab98 + 64)) [Z_to_bv 8 0])
    (Z_to_bv 64 (0x10ab98 + 80)) (LE8 wnf))
    (Z_to_bv 64 (0x10ab98 + 88)) (LE8 wca))
    (Z_to_bv 64 (ptr + 8 * i)) (LE8 (Z_to_bv 64 last)))
    (Z_to_bv 64 (last + 24)) (LE8 (Z_to_bv 64 i)))
    (Z_to_bv 64 (0x10ab58 + 688 + 16)) (LE8 w16))
    (Z_to_bv 64 (0x10ab58 + 688 + 24)) (LE8 w24))
    (Z_to_bv 64 0x10ae00) [Z_to_bv 8 0].
#[local] Hint Unfold fr_sd1 : asfr.

Section SD1.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v v : word) (b1 b2 b3 : byte) (h msz i len ptr last : Z).
  Variables (bnf bca b16 b24 : list byte).
  Variable regs : bvmap 5 word.
  #[local] Abbreviation fnf := (Z_to_bv 64 (bytes_le_to_Z bnf)).
  #[local] Abbreviation fca := (Z_to_bv 64 (bytes_le_to_Z bca)).
  #[local] Abbreviation f16 := (Z_to_bv 64 (bytes_le_to_Z b16)).
  #[local] Abbreviation f24 := (Z_to_bv 64 (bytes_le_to_Z b24)).
  Hypothesis H1 : getr regs 1 = ra0.
  Hypothesis H2 : getr regs 2 = at_ S (-2400).
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x10ab98.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 (0x10ab58 + 688).
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 (h + 4096).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hh : (AIMGHI <= h /\ h mod 4096 = 0 /\ 4096 <= msz /\ h + msz <= bv_unsigned S - 3584)%Z.
  Hypothesis Hi : (0 <= i < len /\ len <= 2 ^ 20)%Z.
  Hypothesis Hptr : (AIMGHI <= ptr /\ ptr + 8 * len <= bv_unsigned S - 3584)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 32 <= bv_unsigned S - 3584)%Z.
  Hypothesis HlastH : hideW (last = h \/ last + 32 <= h \/ h + msz <= last)%Z.
  Hypothesis HptrH : hideW (ptr + 8 * len <= h \/ h + msz <= ptr)%Z.
  Hypothesis HptrL : hideW (ptr + 8 * len <= last \/ last + 32 <= ptr)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2432)) 32 = true.
  Hypothesis Hokslot : store_ok BSEGS mem (Z_to_bv 64 (ptr + 8 * i)) 8 = true.
  Hypothesis Hoklast : store_ok BSEGS mem (Z_to_bv 64 (last + 24)) 8 = true.
  Hypothesis Rpg : rdn BSEGS mem (Z_to_bv 64 0x10ab98) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rlock : rdn BSEGS mem (Z_to_bv 64 0x10ae00) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned v.
  Hypothesis Ridx : rdn BSEGS mem (Z_to_bv 64 (h + 24)) 8 = Some (LE8 (Z_to_bv 64 i)).
  Hypothesis Rptr : rdn BSEGS mem (Z_to_bv 64 (0x10ab98 + 8)) 8 = Some (LE8 (Z_to_bv 64 ptr)).
  Hypothesis Rslot : rdn BSEGS mem (Z_to_bv 64 (ptr + 8 * i)) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis Rn : rdn BSEGS mem (Z_to_bv 64 (0x10ab98 + 56)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis Rmb : rdn BSEGS mem (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis Rms : rdn BSEGS mem (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)).
  Hypothesis Rlast : rdn BSEGS mem (Z_to_bv 64 (ptr + 8 * (len - 1))) 8 = Some (LE8 (Z_to_bv 64 last)).
  Hypothesis Rnf : rdn BSEGS mem (Z_to_bv 64 (0x10ab98 + 80)) 8 = Some bnf.
  Hypothesis Lnf : length bnf = 8%nat.
  Hypothesis Rca : rdn BSEGS mem (Z_to_bv 64 (0x10ab98 + 88)) 8 = Some bca.
  Hypothesis Lca : length bca = 8%nat.
  Hypothesis R16 : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 688 + 16)) 8 = Some b16.
  Hypothesis L16 : length b16 = 8%nat.
  Hypothesis R24 : rdn BSEGS mem (Z_to_bv 64 (0x10ab58 + 688 + 24)) 8 = Some b24.
  Hypothesis L24 : length b24 = 8%nat.

  #[local] Abbreviation negm := (v_sub (Z_to_bv 64 0) (Z_to_bv 64 msz)).
  #[local] Abbreviation wnf := (at_ fnf 1).
  #[local] Abbreviation wca := (v_sub fca (Z_to_bv 64 msz)).
  #[local] Abbreviation w16 := (v_add f16 negm).
  #[local] Abbreviation w24 := (v_add f24 negm).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma pg_and0p : v_and (Z_to_bv 64 4095) (Z_to_bv 64 (h + 4096)) = Z_to_bv 64 0.
  Proof using L24 L16 Lca Lnf Hh HS b24 b16 bca bnf msz v S rom.
    destruct Hh as (G1 & G2 & G3 & G4). pose proof (u64_range S). destruct HS.
    rewrite v_and_Z by lia. f_equal. change 4095%Z with (Z.ones 12). rewrite Z.land_comm, Z.land_ones by lia.
    change (2 ^ 12)%Z with 4096%Z. lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Definition sd1_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = Z_to_bv 64 0x4ef64 /\ getr r 2 = at_ S (-2432)
      /\ getr r 10 = Z_to_bv 64 h /\ getr r 11 = Z_to_bv 64 msz /\ getr r 12 = Z_to_bv 64 0
      /\ getr r 8 = Z_to_bv 64 h /\ getr r 9 = Z_to_bv 64 h /\ getr r 18 = Z_to_bv 64 msz
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma sd1_run :
    exists r, msteps BSEGS (mkst regs (0x4ee70 : word) mem rom)
                           (mkst r (0x70080 : word) (fr_sd1 mem S ra0 s0v s1v s2v b1 b2 b3 len ptr i last wnf wca w16 w24) rom)
      /\ sd1_regs r.
  Proof using L24 R24 L16 R16 Lca Rca Lnf Rnf Rlast Rms Rmb Rn Rslot Rptr Ridx HV Rlock Rpg Hoklast Hokslot Hstk HptrL HptrH HlastH Hlast Hptr Hi Hh HS H12 H11 H10 H18 H9 H8 H2 H1 v.
    (lazymatch goal with |- ?G => let G' := eval unfold sd1_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. destruct Hh as (G1 & G2 & G3 & G4). destruct Hi as (Hi1 & Hi2).
    destruct Hptr as (Hp1 & Hp2). destruct Hlast as (Hl1 & Hl2). unfold hideW in HlastH, HptrH, HptrL.
    pose proof (sok_secinst mem) as Hokinst. pose proof (sok_seclock3 mem) as Hoklk.
    assert (Bx : forall bs, length bs = 8%nat -> bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs))).
    { intros bs L. pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B.
      pose proof (bytes_le_to_Z_nonneg bs). rewrite u_Z2bv by lia. reflexivity. }
    pose proof (Bx _ Lnf) as Vnf. pose proof (Bx _ Lca) as Vca. pose proof (Bx _ L16) as V16. pose proof (Bx _ L24) as V24.
    wd_eexists. split.
    - an F_4ee70 D_4ee70.                              (* [comment removed for export] *)
      fsd F_4ee74 D_4ee74 (at_ S (-2408)).             (* [comment removed for export] *)
      fsd F_4ee78 D_4ee78 (at_ S (-2416)).             (* [comment removed for export] *)
      fsd F_4ee7c D_4ee7c (at_ S (-2424)).             (* [comment removed for export] *)
      fsd F_4ee80 D_4ee80 (at_ S (-2432)).             (* [comment removed for export] *)
      cld8 F_4ee84 D_4ee84 (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_4ee88 D_4ee88.                              (* [comment removed for export] *)
      an F_4ee8c D_4ee8c. rewrite pg_and0p.            (* [comment removed for export] *)
      ab_ft F_4ee90 D_4ee90 ltac:(condz).              (* [comment removed for export] *)
      an F_4ee94 D_4ee94.                              (* [comment removed for export] *)
      an F_4ee98 D_4ee98.                              (* [comment removed for export] *)
      an F_4ee9c D_4ee9c.                              (* [comment removed for export] *)
      an F_4eea0 D_4eea0.                              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (sd_lock_4eea4 _ _ rom v (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]. }
      av F_4eec0 D_4eec0 (Z_to_bv 64 0) ltac:(rewrite (lock_byte0S3 (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity).   (* [comment removed for export] *)
      av F_4eec4 D_4eec4 (Z_to_bv 64 h) ltac:(valz).   (* [comment removed for export] *)
      ab_ft F_4eec8 D_4eec8 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4eecc D_4eecc (Z_to_bv 64 i) Ridx.        (* [comment removed for export] *)
      cld8 F_4eed0 D_4eed0 (Z_to_bv 64 ptr) Rptr.      (* [comment removed for export] *)
      av F_4eed4 D_4eed4 (Z_to_bv 64 (8 * i)) ltac:(valz).          (* [comment removed for export] *)
      av F_4eed8 D_4eed8 (Z_to_bv 64 (ptr + 8 * i)) ltac:(valz).    (* [comment removed for export] *)
      cld8 F_4eedc D_4eedc (Z_to_bv 64 h) Rslot.       (* [comment removed for export] *)
      ab_ft F_4eee0 D_4eee0 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4eee4 D_4eee4 (Z_to_bv 64 len) Rn.        (* [comment removed for export] *)
      ab_ft F_4eee8 D_4eee8 ltac:(condz).              (* [comment removed for export] *)
      av F_4eeec D_4eeec (Z_to_bv 64 (8 * len)) ltac:(valz).        (* [comment removed for export] *)
      cld8 F_4eef0 D_4eef0 (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      av F_4eef4 D_4eef4 (Z_to_bv 64 (ptr + 8 * len)) ltac:(valz).  (* [comment removed for export] *)
      cld F_4eef8 D_4eef8 bnf (Z_to_bv 64 (bytes_le_to_Z bnf)) Rnf Vnf.             (* [comment removed for export] *)
      cld F_4eefc D_4eefc bca (Z_to_bv 64 (bytes_le_to_Z bca)) Rca Vca.             (* [comment removed for export] *)
      av F_4ef00 D_4ef00 (Z_to_bv 64 (len - 1)) ltac:(valz).        (* [comment removed for export] *)
      cld8 F_4ef04 D_4ef04 (Z_to_bv 64 last) Rlast.    (* [comment removed for export] *)
      an F_4ef08 D_4ef08.                              (* [comment removed for export] *)
      an F_4ef0c D_4ef0c.                              (* [comment removed for export] *)
      fsd F_4ef10 D_4ef10 (Z_to_bv 64 (0x10ab98 + 56)).   (* [comment removed for export] *)
      fsb F_4ef14 D_4ef14 (Z_to_bv 64 (0x10ab98 + 64)) (Z_to_bv 8 0).   (* [comment removed for export] *)
      fsd F_4ef18 D_4ef18 (Z_to_bv 64 (0x10ab98 + 80)).   (* [comment removed for export] *)
      fsd F_4ef1c D_4ef1c (Z_to_bv 64 (0x10ab98 + 88)).   (* [comment removed for export] *)
      an F_4ef20 D_4ef20.                              (* [comment removed for export] *)
      an F_4ef24 D_4ef24.                              (* [comment removed for export] *)
      fsd F_4ef28 D_4ef28 (Z_to_bv 64 (ptr + 8 * i)).  (* [comment removed for export] *)
      fsd F_4ef2c D_4ef2c (Z_to_bv 64 (last + 24)).    (* [comment removed for export] *)
      famo F_4ef30 D_4ef30 b16 (Z_to_bv 64 (bytes_le_to_Z b16)) R16 V16.            (* [comment removed for export] *)
      cld8 F_4ef34 D_4ef34 (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      an F_4ef38 D_4ef38.                              (* [comment removed for export] *)
      an F_4ef3c D_4ef3c.                              (* [comment removed for export] *)
      famo F_4ef40 D_4ef40 b24 (Z_to_bv 64 (bytes_le_to_Z b24)) R24 V24.            (* [comment removed for export] *)
      afence F_4ef44 D_4ef44.                          (* [comment removed for export] *)
      fsb F_4ef48 D_4ef48 (Z_to_bv 64 0x10ae00) (Z_to_bv 8 0).   (* [comment removed for export] *)
      cld8 F_4ef4c D_4ef4c (Z_to_bv 64 h) Rmb.         (* [comment removed for export] *)
      cld8 F_4ef50 D_4ef50 (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      an F_4ef54 D_4ef54.                              (* [comment removed for export] *)
      an F_4ef58 D_4ef58.                              (* [comment removed for export] *)
      an F_4ef5c D_4ef5c.                              (* [comment removed for export] *)
      an F_4ef60 D_4ef60.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_sd1 mem S ra0 s0v s1v s2v b1 b2 b3 len ptr i last wnf wca w16 w24). wd_refl.
    - post.
  Qed.
End SD1.

Section SD2.
  Variables (mem rom : word -> option byte) (h msz : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H9 : getr regs 9 = Z_to_bv 64 h.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 msz.
  Lemma sd2_run :
    exists r, msteps BSEGS (mkst regs (0x4ef64 : word) mem rom) (mkst r (0x6ea68 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x4ef70 /\ getr r 10 = Z_to_bv 64 h /\ getr r 11 = Z_to_bv 64 msz
      /\ getr r 2 = getr regs 2 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using H18 H9.
    wd_eexists. split.
    - an F_4ef64 D_4ef64.                              (* [comment removed for export] *)
      an F_4ef68 D_4ef68.                              (* [comment removed for export] *)
      an F_4ef6c D_4ef6c.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End SD2.

(* [comment removed for export] *)
Definition fr_sd3 (mem : word -> option byte) (S : word) : word -> option byte :=
  wbytes mem (at_ S (-2440)) (LE8 (Z_to_bv 64 0x4ef74)).
#[local] Hint Unfold fr_sd3 : asfr.

Section SD3.
  Variables (mem rom : word -> option byte) (S : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2432).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hstk : store_ok BSEGS mem (at_ S (-2448)) 16 = true.

  Lemma sd3_run :
    exists r, msteps BSEGS (mkst regs (0x4ef70 : word) mem rom) (mkst r (0x78e2c : word) (fr_sd3 mem S) rom)
      /\ getr r 1 = Z_to_bv 64 0x78004 /\ getr r 2 = at_ S (-2448)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk HS H2.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4ef70 D_4ef70.                              (* [comment removed for export] *)
      an F_77ff8 D_77ff8.                              (* [comment removed for export] *)
      fsd F_77ffc D_77ffc (at_ S (-2440)).             (* [comment removed for export] *)
      an F_78000 D_78000.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_sd3 mem S). wd_refl.
    - post.
  Qed.
End SD3.

(* [comment removed for export] *)
Definition fr_sd4 (mem : word -> option byte) (T : Z) (j0 j1 : word) : word -> option byte :=
  wbytes (wbytes mem (Z_to_bv 64 (T + 2888)) (LE8 j0)) (Z_to_bv 64 (T + 2896)) (LE8 j1).
#[local] Hint Unfold fr_sd4 : asfr.

Section SD4.
  Variables (mem rom : word -> option byte) (S ra0 s0v s1v s2v : word) (T h msz : Z) (bu0 bu1 : list byte).
  #[local] Abbreviation u0 := (Z_to_bv 64 (bytes_le_to_Z bu0)).
  #[local] Abbreviation u1 := (Z_to_bv 64 (bytes_le_to_Z bu1)).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2448).
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 T.
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 h.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 msz.
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hh : (AIMGHI <= h /\ 4096 <= msz /\ h + msz <= bv_unsigned S - 3584)%Z.
  Hypothesis HhT : hideW (h + msz <= T \/ T + 4096 <= h)%Z.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Rra : rdn BSEGS mem (at_ S (-2440)) 8 = Some (LE8 (Z_to_bv 64 0x4ef74)).
  Hypothesis Ru0 : rdn BSEGS mem (Z_to_bv 64 (T + 2888)) 8 = Some bu0.
  Hypothesis Lu0 : length bu0 = 8%nat.
  Hypothesis Ru1 : rdn BSEGS mem (Z_to_bv 64 (T + 2896)) 8 = Some bu1.
  Hypothesis Lu1 : length bu1 = 8%nat.
  Hypothesis HokT : store_ok BSEGS mem (Z_to_bv 64 (T + 2888)) 16 = true.
  Hypothesis Rmb : rdn BSEGS mem (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis Rms : rdn BSEGS mem (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)).
  Hypothesis Cra : rdn BSEGS mem (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn BSEGS mem (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn BSEGS mem (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn BSEGS mem (at_ S (-2432)) 8 = Some (LE8 s2v).

  Definition sd4_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = ra0 /\ getr r 2 = at_ S (-2400)
      /\ getr r 10 = Z_to_bv 64 h /\ getr r 11 = Z_to_bv 64 msz /\ getr r 12 = Z_to_bv 64 0
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma sd4_run :
    exists r, msteps BSEGS (mkst regs (0x78004 : word) mem rom)
                           (mkst r (0x829f8 : word) (fr_sd4 mem T (at_ u0 1) (v_add u1 (Z_to_bv 64 msz))) rom)
      /\ sd4_regs r.
  Proof using Cs2 Cs1 Cs0 Cra Rms Rmb HokT Lu1 Ru1 Lu0 Ru0 Rra Hh HT HS H18 H8 H10 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold sd4_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT3). unfold hideW in HT2, HhT.
    destruct Hh as (G1 & G3 & G4).
    assert (Bx : forall bs, length bs = 8%nat -> bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs))).
    { intros bs L. pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B.
      pose proof (bytes_le_to_Z_nonneg bs). rewrite u_Z2bv by lia. reflexivity. }
    pose proof (Bx _ Lu0) as Vu0. pose proof (Bx _ Lu1) as Vu1.
    wd_eexists. split.
    - ab_ft F_78004 D_78004 ltac:(condz).              (* [comment removed for export] *)
      an F_78008 D_78008.                              (* [comment removed for export] *)
      an F_7800c D_7800c.                              (* [comment removed for export] *)
      cld8 F_78010 D_78010 (Z_to_bv 64 0x4ef74) Rra.   (* [comment removed for export] *)
      an F_78014 D_78014.                              (* [comment removed for export] *)
      rt F_78018 D_78018.                              (* [comment removed for export] *)
      cld F_4ef74 D_4ef74 bu1 (Z_to_bv 64 (bytes_le_to_Z bu1)) Ru1 Vu1.              (* [comment removed for export] *)
      cld F_4ef78 D_4ef78 bu0 (Z_to_bv 64 (bytes_le_to_Z bu0)) Ru0 Vu0.              (* [comment removed for export] *)
      cld8 F_4ef7c D_4ef7c (Z_to_bv 64 h) Rmb.         (* [comment removed for export] *)
      cld8 F_4ef80 D_4ef80 (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      an F_4ef84 D_4ef84.                              (* [comment removed for export] *)
      an F_4ef88 D_4ef88.                              (* [comment removed for export] *)
      fsd F_4ef8c D_4ef8c (Z_to_bv 64 (T + 2888)).     (* [comment removed for export] *)
      fsd F_4ef90 D_4ef90 (Z_to_bv 64 (T + 2896)).     (* [comment removed for export] *)
      an F_4ef94 D_4ef94.                              (* [comment removed for export] *)
      an F_4ef98 D_4ef98.                              (* [comment removed for export] *)
      cld8 F_4ef9c D_4ef9c ra0 Cra.                    (* [comment removed for export] *)
      cld8 F_4efa0 D_4efa0 s0v Cs0. cld8 F_4efa4 D_4efa4 s1v Cs1. cld8 F_4efa8 D_4efa8 s2v Cs2.
      an F_4efac D_4efac.                              (* [comment removed for export] *)
      an F_4efb0 D_4efb0.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_sd4 mem T (at_ u0 1) (v_add u1 (Z_to_bv 64 msz))). wd_refl.
    - post.
  Qed.
End SD4.
End FPGen.
