(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFHs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.
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
End AsAllocFHs.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.glaze.binary_reflection.images.Asan OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocFRcS3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRc4a.AsAllocFBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFRcA OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import AsAllocFHs.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac stk_ok ::= any_ok_r.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.
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
Lemma sok_secinst : forall m, store_ok ASEGS m (Z_to_bv 64 0x103f58) 656 = true.
Proof using. intros m. apply store_ok_wseg. vm_compute. reflexivity. Qed.
Lemma sok_seclock3 : forall m, store_ok ASEGS m (Z_to_bv 64 0x1041c0) 4 = true.
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
Lemma sd_lock_4e42c : forall regs mem rom (v : word) b0 b1 b2 b3,
  getr regs 16 = Z_to_bv 64 0x1041c0 -> getr regs 15 = Z_to_bv 64 255 -> getr regs 17 = Z_to_bv 64 1 ->
  rdn ASEGS mem (Z_to_bv 64 0x1041c0) 4%nat = Some [b0; b1; b2; b3] -> bytes_le_to_Z [b0; b1; b2; b3] = bv_unsigned v ->
  msteps ASEGS (mkst regs (0x4e434 : word) mem rom)
    (mkst (regupd (regupd regs 5 (v_lw v)) 6 (Z_to_bv 64 0)) (0x4e450 : word)
          (wbytes mem (Z_to_bv 64 0x1041c0) [Z_to_bv 8 1; b1; b2; b3]) rom).
Proof using.
  intros regs mem rom v b0 b1 b2 b3 H16 H15 H17 Hrd Hv.
  pose proof (xchg_byte_run ASEGS regs (0x4e434 : word) (0x4e438 : word) (0x4e43c : word) (0x4e440 : word)
                (0x4e444 : word) (0x4e448 : word) (0x4e44c : word) (0x4e450 : word) mem rom
                _ _ _ _ _ _ _ _ _ _ _ 5 16 6 17 15 _ [b0; b1; b2; b3] v 0%nat 1%Z
                F_4e42c eq_refl D_4e42c F_4e430 eq_refl D_4e430 F_4e434 eq_refl D_4e434 F_4e438 eq_refl D_4e438
                F_4e43c eq_refl D_4e43c F_4e440 eq_refl D_4e440 F_4e444 eq_refl D_4e444) as R.
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
    (Z_to_bv 64 0x1041c0) [Z_to_bv 8 1; b1; b2; b3])
    (Z_to_bv 64 (0x103f58 + 56)) (LE8 (Z_to_bv 64 (len - 1))))
    (Z_to_bv 64 (0x103f58 + 64)) [Z_to_bv 8 0])
    (Z_to_bv 64 (0x103f58 + 80)) (LE8 wnf))
    (Z_to_bv 64 (0x103f58 + 88)) (LE8 wca))
    (Z_to_bv 64 (ptr + 8 * i)) (LE8 (Z_to_bv 64 last)))
    (Z_to_bv 64 (last + 24)) (LE8 (Z_to_bv 64 i)))
    (Z_to_bv 64 (0x103f18 + 688 + 16)) (LE8 w16))
    (Z_to_bv 64 (0x103f18 + 688 + 24)) (LE8 w24))
    (Z_to_bv 64 0x1041c0) [Z_to_bv 8 0].
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
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 0x103f58.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 (0x103f18 + 688).
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 (h + 4096).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hh : (AIMGHI <= h /\ h mod 4096 = 0 /\ 4096 <= msz /\ h + msz <= bv_unsigned S - 3584)%Z.
  Hypothesis Hi : (0 <= i < len /\ len <= 2 ^ 20)%Z.
  Hypothesis Hptr : (AIMGHI <= ptr /\ ptr + 8 * len <= bv_unsigned S - 3584)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 32 <= bv_unsigned S - 3584)%Z.
  Hypothesis HlastH : hideW (last = h \/ last + 32 <= h \/ h + msz <= last)%Z.
  Hypothesis HptrH : hideW (ptr + 8 * len <= h \/ h + msz <= ptr)%Z.
  Hypothesis HptrL : hideW (ptr + 8 * len <= last \/ last + 32 <= ptr)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2432)) 32 = true.
  Hypothesis Hokslot : store_ok ASEGS mem (Z_to_bv 64 (ptr + 8 * i)) 8 = true.
  Hypothesis Hoklast : store_ok ASEGS mem (Z_to_bv 64 (last + 24)) 8 = true.
  Hypothesis Rpg : rdn ASEGS mem (Z_to_bv 64 0x103f58) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis Rlock : rdn ASEGS mem (Z_to_bv 64 0x1041c0) 4 = Some [Z_to_bv 8 0; b1; b2; b3].
  Hypothesis HV : bytes_le_to_Z [Z_to_bv 8 0; b1; b2; b3] = bv_unsigned v.
  Hypothesis Ridx : rdn ASEGS mem (Z_to_bv 64 (h + 24)) 8 = Some (LE8 (Z_to_bv 64 i)).
  Hypothesis Rptr : rdn ASEGS mem (Z_to_bv 64 (0x103f58 + 8)) 8 = Some (LE8 (Z_to_bv 64 ptr)).
  Hypothesis Rslot : rdn ASEGS mem (Z_to_bv 64 (ptr + 8 * i)) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis Rn : rdn ASEGS mem (Z_to_bv 64 (0x103f58 + 56)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis Rmb : rdn ASEGS mem (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis Rms : rdn ASEGS mem (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)).
  Hypothesis Rlast : rdn ASEGS mem (Z_to_bv 64 (ptr + 8 * (len - 1))) 8 = Some (LE8 (Z_to_bv 64 last)).
  Hypothesis Rnf : rdn ASEGS mem (Z_to_bv 64 (0x103f58 + 80)) 8 = Some bnf.
  Hypothesis Lnf : length bnf = 8%nat.
  Hypothesis Rca : rdn ASEGS mem (Z_to_bv 64 (0x103f58 + 88)) 8 = Some bca.
  Hypothesis Lca : length bca = 8%nat.
  Hypothesis R16 : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 688 + 16)) 8 = Some b16.
  Hypothesis L16 : length b16 = 8%nat.
  Hypothesis R24 : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 688 + 24)) 8 = Some b24.
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
      getr r 1 = Z_to_bv 64 0x4e4f4 /\ getr r 2 = at_ S (-2432)
      /\ getr r 10 = Z_to_bv 64 h /\ getr r 11 = Z_to_bv 64 msz /\ getr r 12 = Z_to_bv 64 0
      /\ getr r 8 = Z_to_bv 64 h /\ getr r 9 = Z_to_bv 64 h /\ getr r 18 = Z_to_bv 64 msz
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma sd1_run :
    exists r, msteps ASEGS (mkst regs (0x4e400 : word) mem rom)
                           (mkst r (0x6f610 : word) (fr_sd1 mem S ra0 s0v s1v s2v b1 b2 b3 len ptr i last wnf wca w16 w24) rom)
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
    - an F_4e3f8 D_4e3f8.                              (* [comment removed for export] *)
      fsd F_4e3fc D_4e3fc (at_ S (-2408)).             (* [comment removed for export] *)
      fsd F_4e400 D_4e400 (at_ S (-2416)).             (* [comment removed for export] *)
      fsd F_4e404 D_4e404 (at_ S (-2424)).             (* [comment removed for export] *)
      fsd F_4e408 D_4e408 (at_ S (-2432)).             (* [comment removed for export] *)
      cld8 F_4e40c D_4e40c (Z_to_bv 64 4096) Rpg.      (* [comment removed for export] *)
      an F_4e410 D_4e410.                              (* [comment removed for export] *)
      an F_4e414 D_4e414. rewrite pg_and0p.            (* [comment removed for export] *)
      ab_ft F_4e418 D_4e418 ltac:(condz).              (* [comment removed for export] *)
      an F_4e41c D_4e41c.                              (* [comment removed for export] *)
      an F_4e420 D_4e420.                              (* [comment removed for export] *)
      an F_4e424 D_4e424.                              (* [comment removed for export] *)
      an F_4e428 D_4e428.                              (* [comment removed for export] *)
      eapply msteps_trans.
      { eapply (sd_lock_4e42c _ _ rom v (Z_to_bv 8 0) b1 b2 b3);
          [ gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | gres; rwH; first [reflexivity | apply bv_eq; reflexivity]
          | rd_addr Rlock
          | exact HV ]. }
      av F_4e448 D_4e448 (Z_to_bv 64 0) ltac:(rewrite (lock_byte0S3 (Z_to_bv 8 0) b1 b2 b3 _ HV); unorm; reflexivity).   (* [comment removed for export] *)
      av F_4e44c D_4e44c (Z_to_bv 64 h) ltac:(valz).   (* [comment removed for export] *)
      ab_ft F_4e450 D_4e450 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e454 D_4e454 (Z_to_bv 64 i) Ridx.        (* [comment removed for export] *)
      cld8 F_4e458 D_4e458 (Z_to_bv 64 ptr) Rptr.      (* [comment removed for export] *)
      av F_4e45c D_4e45c (Z_to_bv 64 (8 * i)) ltac:(valz).          (* [comment removed for export] *)
      av F_4e460 D_4e460 (Z_to_bv 64 (ptr + 8 * i)) ltac:(valz).    (* [comment removed for export] *)
      cld8 F_4e464 D_4e464 (Z_to_bv 64 h) Rslot.       (* [comment removed for export] *)
      ab_ft F_4e468 D_4e468 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_4e46c D_4e46c (Z_to_bv 64 len) Rn.        (* [comment removed for export] *)
      ab_ft F_4e470 D_4e470 ltac:(condz).              (* [comment removed for export] *)
      av F_4e474 D_4e474 (Z_to_bv 64 (8 * len)) ltac:(valz).        (* [comment removed for export] *)
      cld8 F_4e478 D_4e478 (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      av F_4e47c D_4e47c (Z_to_bv 64 (ptr + 8 * len)) ltac:(valz).  (* [comment removed for export] *)
      cld F_4e480 D_4e480 bnf (Z_to_bv 64 (bytes_le_to_Z bnf)) Rnf Vnf.             (* [comment removed for export] *)
      cld F_4e484 D_4e484 bca (Z_to_bv 64 (bytes_le_to_Z bca)) Rca Vca.             (* [comment removed for export] *)
      av F_4e488 D_4e488 (Z_to_bv 64 (len - 1)) ltac:(valz).        (* [comment removed for export] *)
      cld8 F_4e48c D_4e48c (Z_to_bv 64 last) Rlast.    (* [comment removed for export] *)
      an F_4e490 D_4e490.                              (* [comment removed for export] *)
      an F_4e494 D_4e494.                              (* [comment removed for export] *)
      fsd F_4e498 D_4e498 (Z_to_bv 64 (0x103f58 + 56)).   (* [comment removed for export] *)
      fsb F_4e49c D_4e49c (Z_to_bv 64 (0x103f58 + 64)) (Z_to_bv 8 0).   (* [comment removed for export] *)
      fsd F_4e4a0 D_4e4a0 (Z_to_bv 64 (0x103f58 + 80)).   (* [comment removed for export] *)
      fsd F_4e4a4 D_4e4a4 (Z_to_bv 64 (0x103f58 + 88)).   (* [comment removed for export] *)
      an F_4e4a8 D_4e4a8.                              (* [comment removed for export] *)
      an F_4e4ac D_4e4ac.                              (* [comment removed for export] *)
      fsd F_4e4b0 D_4e4b0 (Z_to_bv 64 (ptr + 8 * i)).  (* [comment removed for export] *)
      fsd F_4e4b4 D_4e4b4 (Z_to_bv 64 (last + 24)).    (* [comment removed for export] *)
      famo F_4e4b8 D_4e4b8 b16 (Z_to_bv 64 (bytes_le_to_Z b16)) R16 V16.            (* [comment removed for export] *)
      cld8 F_4e4bc D_4e4bc (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      an F_4e4c0 D_4e4c0.                              (* [comment removed for export] *)
      an F_4e4c4 D_4e4c4.                              (* [comment removed for export] *)
      famo F_4e4c8 D_4e4c8 b24 (Z_to_bv 64 (bytes_le_to_Z b24)) R24 V24.            (* [comment removed for export] *)
      afence F_4e4cc D_4e4cc.                          (* [comment removed for export] *)
      fsb F_4e4d0 D_4e4d0 (Z_to_bv 64 0x1041c0) (Z_to_bv 8 0).   (* [comment removed for export] *)
      cld8 F_4e4d4 D_4e4d4 (Z_to_bv 64 h) Rmb.         (* [comment removed for export] *)
      cld8 F_4e4d8 D_4e4d8 (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      an F_4e4dc D_4e4dc.                              (* [comment removed for export] *)
      an F_4e4e0 D_4e4e0.                              (* [comment removed for export] *)
      an F_4e4e4 D_4e4e4.                              (* [comment removed for export] *)
      an F_4e4e8 D_4e4e8.                              (* [comment removed for export] *)
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
    exists r, msteps ASEGS (mkst regs (0x4e4f4 : word) mem rom) (mkst r (0x6dff8 : word) mem rom)
      /\ getr r 1 = Z_to_bv 64 0x4e500 /\ getr r 10 = Z_to_bv 64 h /\ getr r 11 = Z_to_bv 64 msz
      /\ getr r 2 = getr regs 2 /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using H18 H9.
    wd_eexists. split.
    - an F_4e4ec D_4e4ec.                              (* [comment removed for export] *)
      an F_4e4f0 D_4e4f0.                              (* [comment removed for export] *)
      an F_4e4f4 D_4e4f4.                              (* [comment removed for export] *)
      wd_refl.
    - post.
  Qed.
End SD2.

(* [comment removed for export] *)
Definition fr_sd3 (mem : word -> option byte) (S : word) : word -> option byte :=
  wbytes mem (at_ S (-2440)) (LE8 (Z_to_bv 64 0x4e504)).
#[local] Hint Unfold fr_sd3 : asfr.

Section SD3.
  Variables (mem rom : word -> option byte) (S : word).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2432).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47 + 256)%Z.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2448)) 16 = true.

  Lemma sd3_run :
    exists r, msteps ASEGS (mkst regs (0x4e500 : word) mem rom) (mkst r (0x783bc : word) (fr_sd3 mem S) rom)
      /\ getr r 1 = Z_to_bv 64 0x77594 /\ getr r 2 = at_ S (-2448)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 8 = getr regs 8 /\ getr r 9 = getr regs 9 /\ getr r 18 = getr regs 18 /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20
      /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22 /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24
      /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Hstk HS H2.
    pose proof (u64_range S) as HSr.
    wd_eexists. split.
    - an F_4e4f8 D_4e4f8.                              (* [comment removed for export] *)
      an F_77580 D_77580.                              (* [comment removed for export] *)
      fsd F_77584 D_77584 (at_ S (-2440)).             (* [comment removed for export] *)
      an F_77588 D_77588.                              (* [comment removed for export] *)
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
  Hypothesis Rra : rdn ASEGS mem (at_ S (-2440)) 8 = Some (LE8 (Z_to_bv 64 0x4e504)).
  Hypothesis Ru0 : rdn ASEGS mem (Z_to_bv 64 (T + 2888)) 8 = Some bu0.
  Hypothesis Lu0 : length bu0 = 8%nat.
  Hypothesis Ru1 : rdn ASEGS mem (Z_to_bv 64 (T + 2896)) 8 = Some bu1.
  Hypothesis Lu1 : length bu1 = 8%nat.
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 (T + 2888)) 16 = true.
  Hypothesis Rmb : rdn ASEGS mem (Z_to_bv 64 h) 8 = Some (LE8 (Z_to_bv 64 h)).
  Hypothesis Rms : rdn ASEGS mem (Z_to_bv 64 (h + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)).
  Hypothesis Cra : rdn ASEGS mem (at_ S (-2408)) 8 = Some (LE8 ra0).
  Hypothesis Cs0 : rdn ASEGS mem (at_ S (-2416)) 8 = Some (LE8 s0v).
  Hypothesis Cs1 : rdn ASEGS mem (at_ S (-2424)) 8 = Some (LE8 s1v).
  Hypothesis Cs2 : rdn ASEGS mem (at_ S (-2432)) 8 = Some (LE8 s2v).

  Definition sd4_regs (r : bvmap 5 word) : Prop :=
      getr r 1 = ra0 /\ getr r 2 = at_ S (-2400)
      /\ getr r 10 = Z_to_bv 64 h /\ getr r 11 = Z_to_bv 64 msz /\ getr r 12 = Z_to_bv 64 0
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 19 = getr regs 19 /\ getr r 20 = getr regs 20 /\ getr r 21 = getr regs 21 /\ getr r 22 = getr regs 22
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25 /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  Lemma sd4_run :
    exists r, msteps ASEGS (mkst regs (0x77594 : word) mem rom)
                           (mkst r (0x81f88 : word) (fr_sd4 mem T (at_ u0 1) (v_add u1 (Z_to_bv 64 msz))) rom)
      /\ sd4_regs r.
  Proof using Cs2 Cs1 Cs0 Cra Rms Rmb HokT Lu1 Ru1 Lu0 Ru0 Rra Hh HT HS H18 H8 H10 H2.
    (lazymatch goal with |- ?G => let G' := eval unfold sd4_regs in G in change_no_check G' end). pose proof (u64_range S) as HSr. destruct HT as (HT1 & HT2 & HT3). unfold hideW in HT2, HhT.
    destruct Hh as (G1 & G3 & G4).
    assert (Bx : forall bs, length bs = 8%nat -> bytes_le_to_Z bs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bs))).
    { intros bs L. pose proof (bytes_le_to_Z_bound bs) as B. rewrite L in B. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in B.
      pose proof (bytes_le_to_Z_nonneg bs). rewrite u_Z2bv by lia. reflexivity. }
    pose proof (Bx _ Lu0) as Vu0. pose proof (Bx _ Lu1) as Vu1.
    wd_eexists. split.
    - ab_ft F_7758c D_7758c ltac:(condz).              (* [comment removed for export] *)
      an F_77590 D_77590.                              (* [comment removed for export] *)
      an F_77594 D_77594.                              (* [comment removed for export] *)
      cld8 F_77598 D_77598 (Z_to_bv 64 0x4e504) Rra.   (* [comment removed for export] *)
      an F_7759c D_7759c.                              (* [comment removed for export] *)
      rt F_775a0 D_775a0.                              (* [comment removed for export] *)
      cld F_4e4fc D_4e4fc bu1 (Z_to_bv 64 (bytes_le_to_Z bu1)) Ru1 Vu1.              (* [comment removed for export] *)
      cld F_4e500 D_4e500 bu0 (Z_to_bv 64 (bytes_le_to_Z bu0)) Ru0 Vu0.              (* [comment removed for export] *)
      cld8 F_4e504 D_4e504 (Z_to_bv 64 h) Rmb.         (* [comment removed for export] *)
      cld8 F_4e508 D_4e508 (Z_to_bv 64 msz) Rms.       (* [comment removed for export] *)
      an F_4e50c D_4e50c.                              (* [comment removed for export] *)
      an F_4e510 D_4e510.                              (* [comment removed for export] *)
      fsd F_4e514 D_4e514 (Z_to_bv 64 (T + 2888)).     (* [comment removed for export] *)
      fsd F_4e518 D_4e518 (Z_to_bv 64 (T + 2896)).     (* [comment removed for export] *)
      an F_4e51c D_4e51c.                              (* [comment removed for export] *)
      an F_4e520 D_4e520.                              (* [comment removed for export] *)
      cld8 F_4e524 D_4e524 ra0 Cra.                    (* [comment removed for export] *)
      cld8 F_4e528 D_4e528 s0v Cs0. cld8 F_4e52c D_4e52c s1v Cs1. cld8 F_4e530 D_4e530 s2v Cs2.
      an F_4e534 D_4e534.                              (* [comment removed for export] *)
      an F_4e538 D_4e538.                              (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_sd4 mem T (at_ u0 1) (v_add u1 (Z_to_bv 64 msz))). wd_refl.
    - post.
  Qed.
End SD4.
End FPGen.
End AsAllocFRcS3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDepotStore.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation U := bv_unsigned.

Section FPGen.
Context {fx : FPState}.

Lemma sa_shl44 : forall t, (0 <= t < 2 ^ 32)%Z -> v_slli (Z_to_bv 64 t) 44 = Z_to_bv 64 ((t mod 2 ^ 20) * 2 ^ 44).
Proof using.
  intros t Ht. (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. rewrite (u_Z2bv t) by lia. apply bv_eq.
  pose proof (Z.mod_pos_bound t (2 ^ 20) ltac:(lia)) as Hm. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap, bv_modulus in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_N] in G in change_no_check G' end).
  replace (t * 2 ^ 44)%Z with ((t mod 2 ^ 20) * 2 ^ 44 + (t / 2 ^ 20) * 2 ^ Z.pos 64)%Z by (pose proof (Z.div_mod t (2 ^ 20) ltac:(lia)); lia).
  apply Z_mod_plus_full.
Qed.
Lemma sa_shr41 : forall r, (0 <= r < 2 ^ 20)%Z -> v_srli (Z_to_bv 64 (r * 2 ^ 44)) 41 = Z_to_bv 64 (8 * r).
Proof using.
  intros r Hr. (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). rewrite Z.shiftr_div_pow2 by lia. rewrite (u_Z2bv (r * 2 ^ 44)) by lia. f_equal.
  replace (r * 2 ^ 44)%Z with (8 * r * 2 ^ 41)%Z by lia. apply Z.div_mul. lia.
Qed.

Definition sa_mem (M : word -> option byte) (sp ra s0v S idxp : word) (tot cnt : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)) S (LE8 (v_add (Z_to_bv 64 tot) (Z_to_bv 64 cnt)))) idxp (LE8 (Z_to_bv 64 tot)).

Section ALLOC.
  Variables (M rom : word -> option byte) (sp ra s0v S idxp packp blkd : word) (tot cnt : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H10 : getr regs 10 = S.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 cnt.
  Hypothesis H12 : getr regs 12 = idxp.
  Hypothesis H13 : getr regs 13 = packp.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hcnt : (1 <= cnt <= 256)%Z.
  Hypothesis Htot : (0 <= tot < 2 ^ 32)%Z.
  Hypothesis Hsame : (tot / 2 ^ 20 = (tot + cnt - 1) / 2 ^ 20)%Z.                 (* [comment removed for export] *)
  Hypothesis HS : (U S mod 8 = 0 /\ U S + 2 ^ 20 <= 2 ^ 32 /\ (U S + 2 ^ 20 <= U sp - 16 \/ U sp <= U S))%Z.
  Hypothesis Hidx : ((U idxp + 8 <= U sp - 16 \/ U sp <= U idxp) /\ (U idxp + 8 <= U S \/ U S + 2 ^ 20 <= U idxp) /\ U idxp + 8 < 2 ^ 64)%Z.
  Hypothesis Rtot : rdn ASEGS M S 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis SOKS : store_ok ASEGS M S 8 = true.
  Hypothesis SOKi : store_ok ASEGS M idxp 8 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-16)) 16 = true.
  Hypothesis Rblk : rdn ASEGS M (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkd).
  Hypothesis Hblk : (U blkd <> 0 /\ U blkd + 2 ^ 23 < 2 ^ 64)%Z.

  Lemma sa_fast :
    exists r, msteps ASEGS (mkst regs (0x8c5a8 : word) M rom) (mkst r ra (sa_mem M sp ra s0v S idxp tot cnt) rom)
      /\ getr r 10 = Z_to_bv 64 (U blkd + 8 * (tot mod 2 ^ 20)) /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v
      /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 8; 10; 11; 12; 14; 15]) regs r.
  Proof using Hblk Rblk Hstk SOKi SOKS Rtot Hidx HS Hsame Htot Hcnt Hret Hsp H12 H11 H10 H8 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range idxp) as Hir. pose proof (u64_range blkd) as Hbr.
    destruct Hsp as [S1 S2]. destruct HS as (S8 & S32 & SF). destruct Hidx as (I1 & I2 & I3). destruct Hblk as [BK0 BK1].
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (M20 : (0 <= tot mod 2 ^ 20 < 2 ^ 20)%Z) by (apply Z.mod_pos_bound; lia).
    set (MF := wbytes (wbytes M (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)).
    assert (OUTF : forall x : word, (U x < U sp - 16 \/ U sp <= U x)%Z -> MF x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GRF : mem_grows M MF) by ((lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end); do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl).
    assert (RtotF : rdn ASEGS MF S 8 = Some (LE8 (Z_to_bv 64 tot))).
    { rewrite <- Rtot. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply OUTF. lia. }
    assert (OUTA : forall x : word, (U x < U sp - 16 \/ U sp <= U x)%Z -> (U x < U S \/ U S + 8 <= U x)%Z -> (U x < U idxp \/ U idxp + 8 <= U x)%Z ->
              sa_mem M sp ra s0v S idxp tot cnt x = M x).
    { intros x X1 X2 X3. (lazymatch goal with |- ?G => let G' := eval unfold sa_mem in G in change_no_check G' end). fold MF.
      rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. apply OUTF. exact X1. }
    assert (RblkA : rdn ASEGS (sa_mem M sp ra s0v S idxp tot cnt) (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20) + 16)) 8 = Some (LE8 blkd)).
    { rewrite <- Rblk. apply rdn_ext; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply OUTA; lia. }
    assert (SLA : forall (k : Z) (v : word), In (k, v) [(-8, ra); (-16, s0v)]%Z -> rdn ASEGS (sa_mem M sp ra s0v S idxp tot cnt) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin. assert (K : (-16 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      (lazymatch goal with |- ?G => let G' := eval unfold sa_mem in G in change_no_check G' end). fold MF.
      rewrite !rdn_wbytes_out; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
      (lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end). cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; rd8_chain|]). destruct Hin. }
    wd_eexists. split.
    - an F_8c5a0 D_8c5a0.                              (* [comment removed for export] *)
      fsd F_8c5a4 D_8c5a4 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8c5a8 D_8c5a8 (at_ sp (-16)).              (* [comment removed for export] *)
      change (wbytes (wbytes M _ _) _ _) with MF.
      an F_8c5ac D_8c5ac.                              (* [comment removed for export] *)
      an F_8c5b0 D_8c5b0.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 (Z_to_bv 64 tot)) (v := Z_to_bv 64 tot);
          [exact F_8c5b4 | reflexivity | exact D_8c5b4
          | gres; rwH; exact S8
          | gres; rwH; exact RtotF
          | apply bytes_le_to_Z_8
          | gres; rwH; eapply store_ok_mono; [exact GRF | exact SOKS]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH.
      av F_8c5b8 D_8c5b8 (Z_to_bv 64 (cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8c5bc D_8c5bc (Z_to_bv 64 (tot / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8c5c0 D_8c5c0 (Z_to_bv 64 (tot + cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8c5c4 D_8c5c4 (Z_to_bv 64 ((tot + cnt - 1) / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt - 1)) by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft F_8c5c8 D_8c5c8 ltac:(rwH; rewrite Hsame; (lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
      av F_8c5cc D_8c5cc (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; rewrite Z.div_small by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk F_8c5d0 D_8c5d0 ltac:(condz).              (* [comment removed for export] *)
      fsd F_8c5e8 D_8c5e8 idxp.                        (* [comment removed for export] *)
      change (wbytes (wbytes MF S _) idxp _) with (sa_mem M sp ra s0v S idxp tot cnt).
      av F_8c5ec D_8c5ec (Z_to_bv 64 (16 * (tot / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv (tot / 2 ^ 20)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8c5f0 D_8c5f0 (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (16 * (tot / 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8c5f4 D_8c5f4 blkd RblkA.                 (* [comment removed for export] *)
      ab_ft F_8c5f8 D_8c5f8 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; unorm; exact BK0).   (* [comment removed for export] *)
      an F_8c5fc D_8c5fc. rewrite (sa_shl44 tot Htot).  (* [comment removed for export] *)
      an F_8c600 D_8c600. rewrite (sa_shr41 (tot mod 2 ^ 20) M20).   (* [comment removed for export] *)
      av F_8c604 D_8c604 (Z_to_bv 64 (U blkd + 8 * (tot mod 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (8 * (tot mod 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8c608 D_8c608 ra (SLA (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).     (* [comment removed for export] *)
      cld8 F_8c60c D_8c60c s0v (SLA (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).  (* [comment removed for export] *)
      an F_8c610 D_8c610.                              (* [comment removed for export] *)
      aret F_8c614 D_8c614 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End ALLOC.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Abbreviation LE4 v := (word_to_le_bytes 4 v).

Lemma w32_wrap64 : forall z, bv_wrap 32 (bv_wrap 64 z) = bv_wrap 32 z.
Proof using.
  intros z. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 32) with (2 ^ 32)%Z. change (bv_modulus 64) with (2 ^ 32 * 2 ^ 32)%Z.
  rewrite Z.rem_mul_r by lia.
  replace (z mod 2 ^ 32 + 2 ^ 32 * (z / 2 ^ 32 mod 2 ^ 32))%Z with (z mod 2 ^ 32 + (z / 2 ^ 32 mod 2 ^ 32) * 2 ^ 32)%Z by lia.
  rewrite Z_mod_plus_full. apply Z.mod_mod. lia.
Qed.
Lemma w32_swrap : forall z, bv_wrap 32 (bv_swrap 32 z) = bv_wrap 32 z.
Proof using.
  intros z. (lazymatch goal with |- ?G => let G' := eval unfold bv_swrap, bv_wrap in G in change_no_check G' end). change (bv_half_modulus 32) with (2 ^ 31)%Z. change (bv_modulus 32) with (2 ^ 32)%Z.
  rewrite Zminus_mod_idemp_l. f_equal. lia.
Qed.
Lemma u_lw_w32 : forall v : word, bv_wrap 32 (U (v_lw v)) = bv_wrap 32 (U v).
Proof using. intros v. (lazymatch goal with |- ?G => let G' := eval unfold v_lw in G in change_no_check G' end). rewrite Z_to_bv_unsigned, w32_wrap64, w32_swrap. reflexivity. Qed.
Lemma u_addiw_w32 : forall (x : word) i, bv_wrap 32 (U (v_addiw x i)) = bv_wrap 32 (U x + i).
Proof using. intros x i. (lazymatch goal with |- ?G => let G' := eval unfold v_addiw in G in change_no_check G' end). rewrite Z_to_bv_unsigned, w32_wrap64, w32_swrap. reflexivity. Qed.
Lemma le4_congr : forall v1 v2 : word, bv_wrap 32 (U v1) = bv_wrap 32 (U v2) -> LE4 v1 = LE4 v2.
Proof using.
  intros v1 v2 E. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end).
  rewrite <- (Z_to_le_bytes_wrap 4 32 (U v1)), <- (Z_to_le_bytes_wrap 4 32 (U v2)) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). f_equal. exact E.
Qed.
(* [comment removed for export] *)
Definition st_id (tot : Z) : word := v_addiw (v_lw (Z_to_bv 64 tot)) 1.
Lemma st_id_le4 : forall t, (0 <= t)%Z -> (t + 1 < 2 ^ 32)%Z -> LE4 (st_id t) = LE4 (Z_to_bv 64 (t + 1)).
Proof using.
  intros t T0 T1. apply le4_congr. (lazymatch goal with |- ?G => let G' := eval unfold st_id in G in change_no_check G' end). rewrite u_addiw_w32.
  unfold bv_wrap at 1. rewrite <- Zplus_mod_idemp_l. change (U (v_lw (Z_to_bv 64 t)) mod bv_modulus 32)%Z with (bv_wrap 32 (U (v_lw (Z_to_bv 64 t)))).
  rewrite u_lw_w32. rewrite (u_Z2bv t) by lia. rewrite (u_Z2bv (t + 1)) by lia. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma st_zext : forall a, (0 <= a < 2 ^ 32)%Z -> v_srli (v_slli (v_lw (Z_to_bv 64 a)) 32) 32 = Z_to_bv 64 a.
Proof using.
  intros a Ha.
  assert (E : v_slli (v_lw (Z_to_bv 64 a)) 32 = Z_to_bv 64 (a * 2 ^ 32)).
  { (lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. destruct (Z.lt_ge_cases a (2 ^ 31)) as [Hl|Hg].
    - rewrite Mh32.LibMaskBits.u_lw_lo by lia. reflexivity.
    - rewrite Mh32.LibMaskBits.u_lw_hi by lia. apply bv_eq. rewrite !Z_to_bv_unsigned. (lazymatch goal with |- ?G => let G' := eval unfold bv_wrap in G in change_no_check G' end). change (bv_modulus 64) with (2 ^ 64)%Z.
      replace ((a + 2 ^ 32 * (2 ^ 32 - 1)) * 2 ^ 32)%Z with (a * 2 ^ 32 + (2 ^ 32 - 1) * 2 ^ 64)%Z by lia. apply Z_mod_plus_full. }
  rewrite E. (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end). rewrite Z.shiftr_div_pow2 by lia. rewrite (u_Z2bv (a * 2 ^ 32)) by lia. rewrite Z.div_mul by lia. reflexivity.
Qed.
Lemma st_seqz : forall x, (0 <= x < 2 ^ 64)%Z ->
  v_sltiu (v_xor (Z_to_bv 64 x) (Z_to_bv 64 1048576)) 1 = Z_to_bv 64 (if (x =? 1048576)%Z then 1 else 0).
Proof using.
  intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold v_sltiu, v_xor in G in change_no_check G' end). rewrite (u_Z2bv x) by lia. rewrite (u_Z2bv 1048576) by lia.
  pose proof (Z_lxor_range x 1048576 Hx ltac:(lia)) as HR. rewrite (u_Z2bv (Z.lxor x 1048576)) by lia.
  change (bv_wrap 64 1) with 1%Z.
  destruct (Z.eqb_spec x 1048576) as [->|Hne]; [reflexivity|].
  destruct (Z.ltb_spec (Z.lxor x 1048576) 1) as [Hlt|Hge]; [|reflexivity].
  exfalso. apply Hne. apply Z.lxor_eq. lia.
Qed.
Lemma land_m16 : forall x, (0 <= x < 2 ^ 64)%Z -> Z.land x (2 ^ 64 - 16) = (x - x mod 16)%Z.
Proof using.
  intros x Hx. apply Z.bits_inj'. intros k Hk. rewrite Z.land_spec.
  assert (Em : (2 ^ 64 - 16 = Z.shiftl (2 ^ 60 - 1) 4)%Z) by reflexivity. rewrite Em.
  assert (Ex : (x - x mod 16 = Z.shiftl (x / 2 ^ 4) 4)%Z).
  { rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4)%Z with 16%Z. pose proof (Z.div_mod x 16 ltac:(lia)). lia. }
  rewrite Ex. destruct (Z.lt_ge_cases k 4) as [Hl|Hg].
  - rewrite !Z.shiftl_spec_low by lia. apply andb_false_r.
  - rewrite !Z.shiftl_spec_high by lia. destruct (Z.lt_ge_cases k 64) as [Hl2|Hg2].
    + assert (Ht : Z.testbit (2 ^ 60 - 1) (k - 4) = true) by (replace (2 ^ 60 - 1)%Z with (Z.ones 60) by reflexivity; apply Z.ones_spec_low; lia).
      rewrite Ht, andb_true_r. rewrite Z.div_pow2_bits by lia. f_equal. lia.
    + rewrite (Mh32.LibMaskBits.testbit_high 64 x k) by lia.
      rewrite (Mh32.LibMaskBits.testbit_high 60 (x / 2 ^ 4) (k - 4)); [reflexivity | lia | | lia].
      change (2 ^ 4)%Z with 16%Z. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.
Lemma st_andi16 : forall t, (0 <= t < 2 ^ 32)%Z -> v_andi (Z_to_bv 64 (t / 2 ^ 16)) (-16) = Z_to_bv 64 (16 * (t / 2 ^ 20)).
Proof using.
  intros t Ht. (lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end).
  assert (Q : (0 <= t / 2 ^ 16 < 2 ^ 16)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite (u_Z2bv (t / 2 ^ 16)) by lia. change (bv_wrap 64 (-16)) with (2 ^ 64 - 16)%Z. rewrite land_m16 by lia. f_equal.
  replace (t / 2 ^ 20)%Z with (t / 2 ^ 16 / 16)%Z by (rewrite Z.div_div by lia; reflexivity).
  pose proof (Z.div_mod (t / 2 ^ 16) 16 ltac:(lia)). lia.
Qed.

Definition st_frame (M : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v : word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M
    (at_ sp (-8)) (LE8 ra)) (at_ sp (-16)) (LE8 s0v)) (at_ sp (-24)) (LE8 s1v)) (at_ sp (-32)) (LE8 s2v))
    (at_ sp (-40)) (LE8 s3v)) (at_ sp (-48)) (LE8 s4v)) (at_ sp (-56)) (LE8 s5v).
Definition st_m1 (M : word -> option byte) (sp ra s0v s1v s2v s3v s4v s5v packp : word) : word -> option byte :=
  wbytes (wbytes (st_frame M sp ra s0v s1v s2v s3v s4v s5v) (at_ sp (-64)) (LE8 (Z_to_bv 64 0))) packp (LE8 (Z_to_bv 64 0)).

Lemma st_frame_outside : forall M sp ra s0v s1v s2v s3v s4v s5v (x : word), (64 <= U sp)%Z ->
  (U x < U sp - 56 \/ U sp <= U x)%Z -> st_frame M sp ra s0v s1v s2v s3v s4v s5v x = M x.
Proof using.
  intros M sp ra s0v s1v s2v s3v s4v s5v x Hsp Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold st_frame in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
Qed.
Lemma st_frame_grows : forall M sp ra s0v s1v s2v s3v s4v s5v, mem_grows M (st_frame M sp ra s0v s1v s2v s3v s4v s5v).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold st_frame in G in change_no_check G' end). do 7 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. Qed.
Lemma st_m1_outside : forall M sp ra s0v s1v s2v s3v s4v s5v packp (x : word), (64 <= U sp)%Z -> (U packp + 8 < 2 ^ 64)%Z ->
  (U x < U sp - 64 \/ U sp <= U x)%Z -> (U x < U packp \/ U packp + 8 <= U x)%Z -> st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp x = M x.
Proof using.
  intros M sp ra s0v s1v s2v s3v s4v s5v packp x Hsp Hp Hx Hxp. pose proof (u64_range sp). pose proof (u64_range packp). (lazymatch goal with |- ?G => let G' := eval unfold st_m1 in G in change_no_check G' end).
  rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia.
  apply st_frame_outside; lia.
Qed.
Lemma st_m1_grows : forall M sp ra s0v s1v s2v s3v s4v s5v packp, mem_grows M (st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp).
Proof using. intros. (lazymatch goal with |- ?G => let G' := eval unfold st_m1 in G in change_no_check G' end). do 2 (eapply mem_grows_trans; [|apply wbytes_grows]). apply st_frame_grows. Qed.

Section STPRE.
  Variables (M rom : word -> option byte) (sp ra S args packp s0v s1v s2v s3v s4v s5v : word) (sz tag : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H8 : getr regs 8 = s0v.
  Hypothesis H9 : getr regs 9 = s1v.
  Hypothesis H18 : getr regs 18 = s2v.
  Hypothesis H19 : getr regs 19 = s3v.
  Hypothesis H20 : getr regs 20 = s4v.
  Hypothesis H21 : getr regs 21 = s5v.
  Hypothesis H10 : getr regs 10 = S.
  Hypothesis H11 : getr regs 11 = args.
  Hypothesis H12 : getr regs 12 = packp.
  Hypothesis Hsp : (2 ^ 24 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hargs : ((U sp <= U args \/ U args + 16 <= U sp - 64) /\ U args + 16 < 2 ^ 64)%Z.
  Hypothesis Hpack : ((U sp <= U packp \/ U packp + 8 <= U sp - 64) /\ U packp + 8 < 2 ^ 64)%Z.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Rsz : rdn ASEGS M (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz)).
  Hypothesis Rtag : rdn ASEGS M (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag)).
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-64)) 64 = true.
  Hypothesis SOKp : store_ok ASEGS M packp 8 = true.

  Lemma st_pre :
    exists r, msteps ASEGS (mkst regs (0x8c484 : word) M rom) (mkst r (0x8c5a8 : word) (st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp) rom)
      /\ getr r 1 = (0x8c4fc : word) /\ getr r 2 = at_ sp (-64)
      /\ getr r 10 = S /\ getr r 11 = Z_to_bv 64 (sz + 1) /\ getr r 12 = at_ sp (-64) /\ getr r 13 = packp
      /\ getr r 8 = packp /\ getr r 9 = S /\ getr r 18 = Z_to_bv 64 (sz + 1) /\ getr r 19 = args /\ getr r 20 = Z_to_bv 64 sz /\ getr r 21 = Z_to_bv 64 tag
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21]) regs r.
  Proof using SOKp Hstk Rtag Rsz Htag Hsz Hpack Hargs Hsp H12 H11 H10 H21 H20 H19 H18 H9 H8 H2 H1.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range args) as Har. pose proof (u64_range packp) as Hpr.
    destruct Hsp as [S1 S2]. destruct Hargs as [A1 A2]. destruct Hpack as [P1 P2].
    set (MF := st_frame M sp ra s0v s1v s2v s3v s4v s5v).
    assert (GRF : mem_grows M MF) by apply st_frame_grows.
    assert (RszF : rdn ASEGS MF (at_ args 8) 4 = Some (LE4 (Z_to_bv 64 sz))).
    { rewrite <- Rsz. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply st_frame_outside; lia. }
    assert (RtagF : rdn ASEGS MF (at_ args 12) 4 = Some (LE4 (Z_to_bv 64 tag))).
    { rewrite <- Rtag. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply st_frame_outside; lia. }
    assert (Vsz : v_lw (Z_to_bv 64 sz) = Z_to_bv 64 sz) by (apply SumsLib.StartupAux.v_lw_small; wd_ulia).
    assert (Vtag : v_lw (Z_to_bv 64 tag) = Z_to_bv 64 tag) by (apply SumsLib.StartupAux.v_lw_small; wd_ulia).
    assert (B4s : bytes_le_to_Z (LE4 (Z_to_bv 64 sz)) = U (Z_to_bv 64 sz)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (B4t : bytes_le_to_Z (LE4 (Z_to_bv 64 tag)) = U (Z_to_bv 64 tag)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (ORNZ : U (v_or (Z_to_bv 64 sz) (Z_to_bv 64 tag)) <> 0%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold v_or in G in change_no_check G' end). rewrite (u_Z2bv sz), (u_Z2bv tag) by lia.
      pose proof (Z_lor_range sz tag ltac:(lia) ltac:(lia)) as LB.
      rewrite u_Z2bv by lia. intro E0. apply Z.lor_eq_0_iff in E0. lia. }
    wd_eexists. split.
    - an F_8c47c D_8c47c.                              (* [comment removed for export] *)
      fsd F_8c480 D_8c480 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8c484 D_8c484 (at_ sp (-16)).              (* [comment removed for export] *)
      fsd F_8c488 D_8c488 (at_ sp (-24)).              (* [comment removed for export] *)
      fsd F_8c48c D_8c48c (at_ sp (-32)).              (* [comment removed for export] *)
      fsd F_8c490 D_8c490 (at_ sp (-40)).              (* [comment removed for export] *)
      fsd F_8c494 D_8c494 (at_ sp (-48)).              (* [comment removed for export] *)
      fsd F_8c498 D_8c498 (at_ sp (-56)).              (* [comment removed for export] *)
      change (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes M _ _) _ _) _ _) _ _) _ _) _ _) _ _) with MF.
      an F_8c49c D_8c49c.                              (* [comment removed for export] *)
      clw F_8c4a0 D_8c4a0 (LE4 (Z_to_bv 64 sz)) (Z_to_bv 64 sz) RszF B4s.     (* [comment removed for export] *)
      rewrite ?Vsz.
      clw F_8c4a4 D_8c4a4 (LE4 (Z_to_bv 64 tag)) (Z_to_bv 64 tag) RtagF B4t.  (* [comment removed for export] *)
      rewrite ?Vtag.
      an F_8c4a8 D_8c4a8.                              (* [comment removed for export] *)
      ab_tk F_8c4ac D_8c4ac ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; unorm; exact ORNZ).   (* [comment removed for export] *)
      an F_8c4b8 D_8c4b8.                              (* [comment removed for export] *)
      an F_8c4bc D_8c4bc.                              (* [comment removed for export] *)
      ab_ft F_8c4c0 D_8c4c0 ltac:(condz).              (* [comment removed for export] *)
      an F_8c4c4 D_8c4c4.                              (* [comment removed for export] *)
      an F_8c4c8 D_8c4c8.                              (* [comment removed for export] *)
      ab_tk F_8c4cc D_8c4cc ltac:(condz).              (* [comment removed for export] *)
      fsd F_8c4d4 D_8c4d4 (at_ sp (-64)).              (* [comment removed for export] *)
      fsd F_8c4d8 D_8c4d8 packp.                       (* [comment removed for export] *)
      change (wbytes (wbytes MF _ _) packp _) with (st_m1 M sp ra s0v s1v s2v s3v s4v s5v packp).
      av F_8c4dc D_8c4dc (Z_to_bv 64 (sz + 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      an F_8c4e0 D_8c4e0.                              (* [comment removed for export] *)
      an F_8c4e4 D_8c4e4.                              (* [comment removed for export] *)
      an F_8c4e8 D_8c4e8.                              (* [comment removed for export] *)
      an F_8c4ec D_8c4ec.                              (* [comment removed for export] *)
      an F_8c4f0 D_8c4f0.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; reflexivity).
  Qed.
End STPRE.

Lemma st_slliw8 : forall tag, (0 <= tag < 256)%Z -> v_slliw (Z_to_bv 64 tag) 8 = Z_to_bv 64 (tag * 2 ^ 8).
Proof using.
  intros tag Htag. (lazymatch goal with |- ?G => let G' := eval unfold v_slliw in G in change_no_check G' end). rewrite Z.shiftl_mul_pow2 by lia. rewrite (u_Z2bv tag) by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31)%Z; lia). reflexivity.
Qed.
Definition st_hdr (sz tag : Z) : word := Z_to_bv 64 (tag * 2 ^ 8 + sz).

Section STMID.
  Variables (M2 rom : word -> option byte) (args tr dst : word) (sz tag : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H10 : getr regs 10 = dst.
  Hypothesis H19 : getr regs 19 = args.
  Hypothesis H20 : getr regs 20 = Z_to_bv 64 sz.
  Hypothesis H21 : getr regs 21 = Z_to_bv 64 tag.
  Hypothesis Hsz : (1 <= sz < 255)%Z.
  Hypothesis Htag : (0 <= tag < 256)%Z.
  Hypothesis Hdst : (U dst <> 0 /\ U dst + 8 < 2 ^ 64)%Z.
  Hypothesis Rtr : rdn ASEGS M2 args 8 = Some (LE8 tr).
  Hypothesis SOKd : store_ok ASEGS M2 dst 8 = true.

  Lemma st_mid :
    exists r, msteps ASEGS (mkst regs (0x8c4fc : word) M2 rom) (mkst r (0x7febc : word) (wbytes M2 dst (LE8 (st_hdr sz tag))) rom)
      /\ getr r 1 = (0x8c51c : word) /\ getr r 10 = at_ dst 8 /\ getr r 11 = tr /\ getr r 12 = Z_to_bv 64 (8 * sz)
      /\ regs_agree (fun i : reg => In i [1; 10; 11; 12]) regs r.
  Proof using SOKd Rtr Hdst Htag Hsz H21 H20 H19 H10 args.
    pose proof (u64_range dst) as Hdr. pose proof (u64_range args) as Har. destruct Hdst as [D0 D1].
    wd_eexists. split.
    - ab_ft F_8c4f4 D_8c4f4 ltac:(rwH; (lazymatch goal with |- ?G => let G' := eval unfold c_eq, bv_eqb in G in change_no_check G' end); apply Z.eqb_neq; unorm; exact D0).   (* [comment removed for export] *)
      an F_8c4f8 D_8c4f8. rewrite (st_slliw8 tag Htag).   (* [comment removed for export] *)
      cld8 F_8c4fc D_8c4fc tr Rtr.                     (* [comment removed for export] *)
      an F_8c500 D_8c500.                              (* [comment removed for export] *)
      rewrite (v_or_shl (Z_to_bv 64 sz) tag 8) by (wd_ulia). rewrite (u_Z2bv sz) by lia. change (Z_to_bv 64 (tag * 2 ^ 8 + sz)) with (st_hdr sz tag).
      fsd F_8c504 D_8c504 dst.                         (* [comment removed for export] *)
      an F_8c508 D_8c508.                              (* [comment removed for export] *)
      av F_8c50c D_8c50c (Z_to_bv 64 (8 * sz)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv sz) by lia; f_equal; lia).   (* [comment removed for export] *)
      an F_8c510 D_8c510.                              (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve. all: try (apply bv_eq; reflexivity).
  Qed.
End STMID.

Definition st_cell (S : word) (tot : Z) : word := Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20) + 24).
Definition st_full (sov cnt : Z) : Z := if (cnt + sov =? 1048576)%Z then 1%Z else 0%Z.
Definition st_m5 (M4 : word -> option byte) (S packp : word) (tot cnt sov pk : Z) : word -> option byte :=
  wbytes (wbytes M4 (st_cell S tot) (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 cnt)))) packp (LE8 (Z_to_bv 64 (pk + st_full sov cnt))).

Section STPOST.
  Variables (M4 rom : word -> option byte) (sp ra S packp s0v s1v s2v s3v s4v s5v : word) (tot cnt sov pk : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ sp (-64).
  Hypothesis H8 : getr regs 8 = packp.
  Hypothesis H9 : getr regs 9 = S.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 cnt.
  Hypothesis Hsp : (2 ^ 32 + 64 <= U sp /\ U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis Hcnt : (1 <= cnt <= 256)%Z.
  Hypothesis Htot : (0 <= tot < 2 ^ 32)%Z.
  Hypothesis Hsov : (0 <= sov < 2 ^ 32)%Z.
  Hypothesis Hpk : (0 <= pk < 2 ^ 32)%Z.
  Hypothesis HS : (U S mod 4 = 0 /\ U S + 2 ^ 20 <= 2 ^ 32)%Z.
  Hypothesis Hpack : ((U sp <= U packp \/ U packp + 8 <= U sp - 64) /\ 2 ^ 32 <= U packp /\ U packp + 8 < 2 ^ 64)%Z.
  Hypothesis Ridx : rdn ASEGS M4 (at_ sp (-64)) 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rso : rdn ASEGS M4 (st_cell S tot) 4 = Some (LE4 (Z_to_bv 64 sov)).
  Hypothesis SOKso : store_ok ASEGS M4 (st_cell S tot) 4 = true.
  Hypothesis Rpk : rdn ASEGS M4 packp 8 = Some (LE8 (Z_to_bv 64 pk)).
  Hypothesis SOKp : store_ok ASEGS M4 packp 8 = true.
  Hypothesis SL : forall (k : Z) (v : word),
    In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v)]%Z -> rdn ASEGS M4 (at_ sp k) 8 = Some (LE8 v).

  Lemma st_post :
    exists r, msteps ASEGS (mkst regs (0x8c51c : word) M4 rom) (mkst r ra (st_m5 M4 S packp tot cnt sov pk) rom)
      /\ getr r 10 = st_id tot /\ getr r 2 = sp /\ getr r 1 = ra
      /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v /\ getr r 20 = s4v /\ getr r 21 = s5v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21]) regs r.
  Proof using SL SOKp Rpk SOKso Rso Ridx Hpack HS Hpk Hsov Htot Hcnt Hret Hsp H18 H9 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range packp) as Hpr.
    destruct Hsp as [S1 S2]. destruct HS as [S4 S32]. destruct Hpack as (P1 & P32 & P2).
    assert (Q20 : (0 <= tot / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Q16 : (0 <= tot / 2 ^ 16 < 2 ^ 16)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Ucell : U (st_cell S tot) = (U S + 16 * (tot / 2 ^ 20) + 24)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_cell in G in change_no_check G' end); rewrite u_Z2bv by lia; reflexivity).
    assert (ALN : (U (st_cell S tot) mod 4 = 0)%Z).
    { rewrite Ucell. replace (U S + 16 * (tot / 2 ^ 20) + 24)%Z with (U S + (4 * (tot / 2 ^ 20) + 6) * 4)%Z by lia. rewrite Z_mod_plus_full. exact S4. }
    set (MA := wbytes M4 (st_cell S tot) (LE4 (v_add (Z_to_bv 64 sov) (Z_to_bv 64 cnt)))).
    assert (OUTA : forall x : word, (U x < U (st_cell S tot) \/ U (st_cell S tot) + 4 <= U x)%Z -> MA x = M4 x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity. }
    assert (GRA : mem_grows M4 MA) by ((lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply wbytes_grows).
    assert (RpkA : rdn ASEGS MA packp 8 = Some (LE8 (Z_to_bv 64 pk))).
    { rewrite <- Rpk. apply rdn_ext; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]. intros x Hx. cbn in Hx. apply OUTA. rewrite Ucell. lia. }
    assert (RidxA : rdn ASEGS MA (at_ sp (-64)) 4 = Some (LE4 (Z_to_bv 64 tot))).
    { apply (SumsLib.StartupAux.rdn_low_bytes ASEGS MA (at_ sp (-64)) (Z_to_bv 64 tot) 4 ltac:(lia)).
      rewrite <- Ridx. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUTA. rewrite Ucell. lia. }
    assert (B4so : bytes_le_to_Z (LE4 (Z_to_bv 64 sov)) = U (Z_to_bv 64 sov)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (B4t : bytes_le_to_Z (LE4 (Z_to_bv 64 tot)) = U (Z_to_bv 64 tot)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (FUL : (0 <= st_full sov cnt <= 1)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); destruct (cnt + sov =? 1048576)%Z; lia).
    assert (OUT5 : forall x : word, (U x < U (st_cell S tot) \/ U (st_cell S tot) + 4 <= U x)%Z -> (U x < U packp \/ U packp + 8 <= U x)%Z ->
              st_m5 M4 S packp tot cnt sov pk x = M4 x).
    { intros x X1 X2. (lazymatch goal with |- ?G => let G' := eval unfold st_m5 in G in change_no_check G' end). fold MA. rewrite wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. apply OUTA. exact X1. }
    assert (SLF : forall (k : Z) (v : word),
              In (k, v) [(-8, ra); (-16, s0v); (-24, s1v); (-32, s2v); (-40, s3v); (-48, s4v); (-56, s5v)]%Z ->
              rdn ASEGS (st_m5 M4 S packp tot cnt sov pk) (at_ sp k) 8 = Some (LE8 v)).
    { intros k v Hin.
      assert (K : (-56 <= k <= -8)%Z) by (cbn [In] in Hin; repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
      rewrite <- (SL k v Hin). apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|].
      intros x Hx. rewrite at_u in Hx by lia. cbn in Hx. apply OUT5; rewrite ?Ucell; lia. }
    wd_eexists. split.
    - cld8 F_8c514 D_8c514 (Z_to_bv 64 tot) Ridx.      (* [comment removed for export] *)
      av F_8c518 D_8c518 (Z_to_bv 64 (tot / 2 ^ 16)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8c51c D_8c51c (Z_to_bv 64 (16 * (tot / 2 ^ 20))) ltac:(apply st_andi16; lia).   (* [comment removed for export] *)
      av F_8c520 D_8c520 (Z_to_bv 64 (U S + 16 * (tot / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (16 * (tot / 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8c524 D_8c524 (st_cell S tot) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi, st_cell in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_w with (bs := LE4 (Z_to_bv 64 sov)) (v := Z_to_bv 64 sov);
          [exact F_8c528 | reflexivity | exact D_8c528
          | gres; rwH; exact ALN
          | gres; rwH; exact Rso
          | exact B4so
          | gres; rwH; exact SOKso]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. change (wbytes M4 (st_cell S tot) _) with MA.
      an F_8c52c D_8c52c.                              (* [comment removed for export] *)
      an F_8c530 D_8c530.                              (* [comment removed for export] *)
      an F_8c534 D_8c534. rewrite (st_zext sov Hsov).  (* [comment removed for export] *)
      av F_8c538 D_8c538 (Z_to_bv 64 (cnt + sov)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv cnt), (u_Z2bv sov) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8c53c D_8c53c (Z_to_bv 64 pk) RpkA.       (* [comment removed for export] *)
      an F_8c540 D_8c540.                              (* [comment removed for export] *)
      clw F_8c544 D_8c544 (LE4 (Z_to_bv 64 tot)) (Z_to_bv 64 tot) RidxA B4t.   (* [comment removed for export] *)
      av F_8c548 D_8c548 (Z_to_bv 64 (st_full sov cnt)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); apply st_seqz; lia).   (* [comment removed for export] *)
      av F_8c54c D_8c54c (Z_to_bv 64 (pk + st_full sov cnt)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv pk), (u_Z2bv (st_full sov cnt)) by lia; reflexivity).   (* [comment removed for export] *)
      fsd F_8c550 D_8c550 packp.                       (* [comment removed for export] *)
      change (wbytes MA packp _) with (st_m5 M4 S packp tot cnt sov pk).
      an F_8c554 D_8c554.                              (* [comment removed for export] *)
      cld8 F_8c558 D_8c558 ra (SLF (-8)%Z ra ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8c55c D_8c55c s0v (SLF (-16)%Z s0v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8c560 D_8c560 s1v (SLF (-24)%Z s1v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8c564 D_8c564 s2v (SLF (-32)%Z s2v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8c568 D_8c568 s3v (SLF (-40)%Z s3v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8c56c D_8c56c s4v (SLF (-48)%Z s4v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      cld8 F_8c570 D_8c570 s5v (SLF (-56)%Z s5v ltac:((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); tauto)).
      an F_8c574 D_8c574.                              (* [comment removed for export] *)
      aret F_8c578 D_8c578 ra.                         (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End STPOST.

End FPGen.
End AsDepotStore.
Module AsDepotAlloc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumsLib.StartupAux.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 AsDepotStore.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import AsAllocFHs.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac stk_ok ::= any_ok_r.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
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
  Hypothesis SOKi : store_ok ASEGS MT idxp 8 = true.
  Hypothesis Rblk : rdn ASEGS MT (Z_to_bv 64 (U S + 16 * (start / 2 ^ 20) + 16)) 8 = Some (LE8 blkd).
  Hypothesis Rra : rdn ASEGS MT (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis Rs0 : rdn ASEGS MT (at_ sp (-16)) 8 = Some (LE8 s0v).

  Definition sa_tmem (MT : word -> option byte) (idxp : word) (start : Z) : word -> option byte := wbytes MT idxp (LE8 (Z_to_bv 64 start)).

  Lemma sa_tmem_rd : forall (a : word) (n : nat) bs, (U a + Z.of_nat n <= 2 ^ 64)%Z -> (U a + Z.of_nat n <= U idxp \/ U idxp + 8 <= U a)%Z ->
    rdn ASEGS MT a n = Some bs -> rdn ASEGS (sa_tmem MT idxp start) a n = Some bs.
  Proof using Hidx S sp.
    intros a n bs A1 A2 Hr. destruct Hidx as (_ & _ & I3). (lazymatch goal with |- ?G => let G' := eval unfold sa_tmem in G in change_no_check G' end).
    rewrite rdn_wbytes_out; [exact Hr | | | ]; wd_lenlit; rewrite ?length_N_to_le_bytes; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia.
  Qed.


  Lemma sa_tail_cpre : blkd = Z_to_bv 64 0 ->
    exists r, msteps ASEGS (mkst regs (0x8c5d4 : word) MT rom) (mkst r (0x8cf90 : word) (sa_tmem MT idxp start) rom)
      /\ getr r 1 = (0x8c6bc : word) /\ getr r 10 = Z_to_bv 64 (U S + 16 * (start / 2 ^ 20) + 16) /\ getr r 2 = at_ sp (-16) /\ getr r 8 = Z_to_bv 64 start
      /\ regs_agree (fun i : reg => In i [1; 10; 12]) regs r.
  Proof using Rblk SOKi Hidx HS Hstart Hsp H12 H11 H8 H5 H2.
    intros EB.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range S) as HSr. pose proof (u64_range idxp) as Hir.
    destruct Hsp as [S1 S2]. destruct HS as (S32 & SF). destruct Hidx as (I1 & I2 & I3).
    assert (Q20 : (0 <= start / 2 ^ 20 < 2 ^ 12)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    pose proof (sa_tmem_rd (Z_to_bv 64 (U S + 16 * (start / 2 ^ 20) + 16)) 8 _ ltac:(first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]) ltac:(first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]) Rblk) as RblkT.
    rewrite EB in RblkT.
    wd_eexists. split.
    - av F_8c5cc D_8c5cc (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv start) by lia; rewrite Z.div_small by lia; reflexivity).   (* [comment removed for export] *)
      ab_tk F_8c5d0 D_8c5d0 ltac:(condz).              (* [comment removed for export] *)
      fsd F_8c5e8 D_8c5e8 idxp.                        (* [comment removed for export] *)
      change (wbytes MT idxp _) with (sa_tmem MT idxp start).
      av F_8c5ec D_8c5ec (Z_to_bv 64 (16 * (start / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv (start / 2 ^ 20)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8c5f0 D_8c5f0 (Z_to_bv 64 (U S + 16 * (start / 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (16 * (start / 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8c5f4 D_8c5f4 (Z_to_bv 64 0) RblkT.       (* [comment removed for export] *)
      ab_tk F_8c5f8 D_8c5f8 ltac:(condz).              (* [comment removed for export] *)
      av F_8c6ac D_8c6ac (Z_to_bv 64 (U S + 16 * (start / 2 ^ 20) + 16)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      an F_8c6b0 D_8c6b0.                              (* [comment removed for export] *)
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
  Hypothesis Rra : rdn ASEGS MC (at_ sp (-8)) 8 = Some (LE8 ra).
  Hypothesis Rs0 : rdn ASEGS MC (at_ sp (-16)) 8 = Some (LE8 s0v).

  Lemma sa_tail_cpost :
    exists r, msteps ASEGS (mkst regs (0x8c6bc : word) MC rom) (mkst r ra MC rom)
      /\ getr r 10 = Z_to_bv 64 (U newblk + 8 * (start mod 2 ^ 20)) /\ getr r 2 = sp /\ getr r 1 = ra /\ getr r 8 = s0v
      /\ regs_agree (fun i : reg => In i [1; 2; 8; 10]) regs r.
  Proof using Rs0 Rra Hstart Hret Hsp H10 H8 H2.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range newblk) as Hbr. destruct Hsp as [S1 S2].
    assert (M20 : (0 <= start mod 2 ^ 20 < 2 ^ 20)%Z) by (apply Z.mod_pos_bound; lia).
    wd_eexists. split.
    - an F_8c6b4 D_8c6b4.                              (* [comment removed for export] *)
      an F_8c5fc D_8c5fc. rewrite (sa_shl44 start Hstart).  (* [comment removed for export] *)
      an F_8c600 D_8c600. rewrite (sa_shr41 (start mod 2 ^ 20) M20).   (* [comment removed for export] *)
      av F_8c604 D_8c604 (Z_to_bv 64 (U newblk + 8 * (start mod 2 ^ 20))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (8 * (start mod 2 ^ 20))) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8c608 D_8c608 ra Rra.                     (* [comment removed for export] *)
      cld8 F_8c60c D_8c60c s0v Rs0.                    (* [comment removed for export] *)
      an F_8c610 D_8c610.                              (* [comment removed for export] *)
      aret F_8c614 D_8c614 ra.                         (* [comment removed for export] *)
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
  Hypothesis Rtot : rdn ASEGS M S 8 = Some (LE8 (Z_to_bv 64 tot)).
  Hypothesis Rso0 : rdn ASEGS M (st_cell S tot) 4 = Some (LE4 (Z_to_bv 64 so0)).
  Hypothesis Rso1 : rdn ASEGS M (st_cell S (tot + cnt)) 4 = Some (LE4 (Z_to_bv 64 so1)).
  Hypothesis Rpk : rdn ASEGS M packp 8 = Some (LE8 (Z_to_bv 64 pk)).
  Hypothesis SOKS : store_ok ASEGS M S 8 = true.
  Hypothesis SOK0 : store_ok ASEGS M (st_cell S tot) 4 = true.
  Hypothesis SOK1 : store_ok ASEGS M (st_cell S (tot + cnt)) 4 = true.
  Hypothesis SOKp : store_ok ASEGS M packp 8 = true.
  Hypothesis Hstk : store_ok ASEGS M (at_ sp (-16)) 16 = true.

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
    exists r, msteps ASEGS (mkst regs (0x8c5a8 : word) M rom) (mkst r (0x8c5d4 : word) (sa_smem M sp ra s0v S packp tot cnt so0 so1 pk) rom)
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
    assert (RtotF : rdn ASEGS MF S 8 = Some (LE8 (Z_to_bv 64 tot))) by ((lazymatch goal with |- ?G => let G' := eval unfold MF in G in change_no_check G' end); do 2 wo; exact Rtot).
    assert (Rso0A : rdn ASEGS MA (st_cell S tot) 4 = Some (LE4 (Z_to_bv 64 so0))) by ((lazymatch goal with |- ?G => let G' := eval unfold MA, MF in G in change_no_check G' end); do 3 wo; exact Rso0).
    assert (RpkB : rdn ASEGS MB packp 8 = Some (LE8 (Z_to_bv 64 pk))) by ((lazymatch goal with |- ?G => let G' := eval unfold MB, MA, MF in G in change_no_check G' end); do 4 wo; exact Rpk).
    assert (Rso1C : rdn ASEGS MC (st_cell S (tot + cnt)) 4 = Some (LE4 (Z_to_bv 64 so1))) by ((lazymatch goal with |- ?G => let G' := eval unfold MC, MB, MA, MF in G in change_no_check G' end); do 5 wo; exact Rso1).
    assert (RpkD : rdn ASEGS MD packp 8 = Some (LE8 (Z_to_bv 64 (pk + st_full so0 inf)))) by ((lazymatch goal with |- ?G => let G' := eval unfold MD in G in change_no_check G' end); wo; (lazymatch goal with |- ?G => let G' := eval unfold MC in G in change_no_check G' end); apply rdn_wbytes_hit8; lia).
    assert (RtotE : rdn ASEGS ME S 8 = Some (LE8 (Z_to_bv 64 (tot + cnt)))) by ((lazymatch goal with |- ?G => let G' := eval unfold ME, MD, MC, MB in G in change_no_check G' end); do 4 wo; (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply rdn_wbytes_hit8; lia).
    assert (B4a : bytes_le_to_Z (LE4 (Z_to_bv 64 so0)) = U (Z_to_bv 64 so0)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (B4b : bytes_le_to_Z (LE4 (Z_to_bv 64 so1)) = U (Z_to_bv 64 so1)) by (apply SumsLib.StartupAux.bytes_le_to_Z_4_small; wd_ulia).
    assert (EA : v_add (Z_to_bv 64 tot) (Z_to_bv 64 cnt) = Z_to_bv 64 (tot + cnt)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv tot), (u_Z2bv cnt) by lia; reflexivity).
    assert (EG : v_add (Z_to_bv 64 (tot + cnt)) (Z_to_bv 64 cnt) = Z_to_bv 64 (tot + cnt + cnt)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (tot + cnt)), (u_Z2bv cnt) by lia; reflexivity).
    wd_eexists. split.
    - an F_8c5a0 D_8c5a0.                              (* [comment removed for export] *)
      fsd F_8c5a4 D_8c5a4 (at_ sp (-8)).               (* [comment removed for export] *)
      fsd F_8c5a8 D_8c5a8 (at_ sp (-16)).              (* [comment removed for export] *)
      change (wbytes (wbytes M _ _) _ _) with MF.
      an F_8c5ac D_8c5ac.                              (* [comment removed for export] *)
      an F_8c5b0 D_8c5b0.                              (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 (Z_to_bv 64 tot)) (v := Z_to_bv 64 tot);
          [exact F_8c5b4 | reflexivity | exact D_8c5b4
          | gres; rwH; exact S8
          | gres; rwH; exact RtotF
          | apply bytes_le_to_Z_8
          | gres; rwH; eapply store_ok_mono; [exact GRF | exact SOKS]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. rewrite EA. change (wbytes MF S _) with MA.
      av F_8c5b8 D_8c5b8 (Z_to_bv 64 (cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8c5bc D_8c5bc (Z_to_bv 64 q) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv tot) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8c5c0 D_8c5c0 (Z_to_bv 64 (tot + cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8c5c4 D_8c5c4 (Z_to_bv 64 (q + 1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt - 1)) by lia; rewrite Hq1; reflexivity).   (* [comment removed for export] *)
      ab_tk F_8c5c8 D_8c5c8 ltac:(condz).              (* [comment removed for export] *)
      an F_8c618 D_8c618.                              (* [comment removed for export] *)
      ab_ft F_8c61c D_8c61c ltac:(condz).              (* [comment removed for export] *)
      an F_8c620 D_8c620.                              (* [comment removed for export] *)
      av F_8c624 D_8c624 (Z_to_bv 64 1048575) ltac:(apply bv_eq; reflexivity).   (* [comment removed for export] *)
      an F_8c628 D_8c628. rewrite (sa_and20 tot ltac:(lia)).   (* [comment removed for export] *)
      av F_8c62c D_8c62c (Z_to_bv 64 (16 * q)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv q) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8c630 D_8c630 (Z_to_bv 64 inf) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub, inf, sa_inf in G in change_no_check G' end); rewrite (u_Z2bv (tot mod 2 ^ 20)) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8c634 D_8c634 (Z_to_bv 64 (U S + 16 + 16 * q)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8c638 D_8c638 (st_cell S tot) ltac:(apply bv_eq; rewrite Uc0; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_w with (bs := LE4 (Z_to_bv 64 so0)) (v := Z_to_bv 64 so0);
          [exact F_8c63c | reflexivity | exact D_8c63c
          | gres; rwH; exact AL0
          | gres; rwH; exact Rso0A
          | exact B4a
          | gres; rwH; eapply store_ok_mono; [exact GRA | exact SOK0]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. change (wbytes MA (st_cell S tot) _) with MB.
      av F_8c640 D_8c640 (Z_to_bv 64 (16 * (q + 1))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_slli in G in change_no_check G' end); rewrite Z.shiftl_mul_pow2 by lia; rewrite (u_Z2bv (q + 1)) by lia; f_equal; lia).   (* [comment removed for export] *)
      av F_8c644 D_8c644 (Z_to_bv 64 (U S + 16 + 16 * (q + 1))) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add, at_ in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8c648 D_8c648 (Z_to_bv 64 (cnt - inf)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sub in G in change_no_check G' end); rewrite (u_Z2bv cnt), (u_Z2bv inf) by lia; reflexivity).   (* [comment removed for export] *)
      an F_8c64c D_8c64c.                              (* [comment removed for export] *)
      an F_8c650 D_8c650. rewrite (st_zext so0 SO0).   (* [comment removed for export] *)
      av F_8c654 D_8c654 (Z_to_bv 64 (inf + so0)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv inf), (u_Z2bv so0) by lia; reflexivity).   (* [comment removed for export] *)
      cld8 F_8c658 D_8c658 (Z_to_bv 64 pk) RpkB.       (* [comment removed for export] *)
      av F_8c65c D_8c65c (st_cell S (tot + cnt)) ltac:(apply bv_eq; rewrite Uc1; (lazymatch goal with |- ?G => let G' := eval unfold v_addi in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      an F_8c660 D_8c660.                              (* [comment removed for export] *)
      av F_8c664 D_8c664 (Z_to_bv 64 (st_full so0 inf)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); apply st_seqz; lia).   (* [comment removed for export] *)
      av F_8c668 D_8c668 (Z_to_bv 64 (pk + st_full so0 inf)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv pk), (u_Z2bv (st_full so0 inf)) by lia; reflexivity).   (* [comment removed for export] *)
      fsd F_8c66c D_8c66c packp.                       (* [comment removed for export] *)
      change (wbytes MB packp _) with MC.
      chain_step; [reflexivity
        | eapply step_amoadd_w with (bs := LE4 (Z_to_bv 64 so1)) (v := Z_to_bv 64 so1);
          [exact F_8c670 | reflexivity | exact D_8c670
          | gres; rwH; exact AL1
          | gres; rwH; exact Rso1C
          | exact B4b
          | gres; rwH; eapply store_ok_mono; [exact GRC | exact SOK1]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. change (wbytes MC (st_cell S (tot + cnt)) _) with MD.
      cld8 F_8c674 D_8c674 (Z_to_bv 64 (pk + st_full so0 inf)) RpkD.   (* [comment removed for export] *)
      an F_8c678 D_8c678.                              (* [comment removed for export] *)
      an F_8c67c D_8c67c. rewrite (st_zext so1 SO1).   (* [comment removed for export] *)
      av F_8c680 D_8c680 (Z_to_bv 64 (cnt - inf + so1)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (cnt - inf)), (u_Z2bv so1) by lia; reflexivity).   (* [comment removed for export] *)
      an F_8c684 D_8c684.                              (* [comment removed for export] *)
      av F_8c688 D_8c688 (Z_to_bv 64 (st_full so1 (cnt - inf))) ltac:((lazymatch goal with |- ?G => let G' := eval unfold st_full in G in change_no_check G' end); apply st_seqz; lia).   (* [comment removed for export] *)
      av F_8c68c D_8c68c (Z_to_bv 64 (pk + st_full so0 inf + st_full so1 (cnt - inf)))
         ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); rewrite (u_Z2bv (pk + st_full so0 inf)), (u_Z2bv (st_full so1 (cnt - inf))) by lia; reflexivity).   (* [comment removed for export] *)
      fsd F_8c690 D_8c690 packp.                       (* [comment removed for export] *)
      change (wbytes MD packp _) with ME.
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 (Z_to_bv 64 (tot + cnt))) (v := Z_to_bv 64 (tot + cnt));
          [exact F_8c694 | reflexivity | exact D_8c694
          | gres; rwH; exact S8
          | gres; rwH; exact RtotE
          | apply bytes_le_to_Z_8
          | gres; rwH; eapply store_ok_mono; [exact GRE | exact SOKS]]
        | step_simpl]; vn.                             (* [comment removed for export] *)
      gres. rwH. rewrite EG. change (wbytes ME S _) with (sa_smem M sp ra s0v S packp tot cnt so0 so1 pk).
      av F_8c698 D_8c698 (Z_to_bv 64 ((tot + cnt) / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt)) by lia; reflexivity).   (* [comment removed for export] *)
      av F_8c69c D_8c69c (Z_to_bv 64 (tot + cnt + cnt - 1)) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_add in G in change_no_check G' end); wd_ulia).   (* [comment removed for export] *)
      av F_8c6a0 D_8c6a0 (Z_to_bv 64 ((tot + cnt) / 2 ^ 20)) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; rewrite (u_Z2bv (tot + cnt + cnt - 1)) by lia; rewrite Q3, Q2; reflexivity).   (* [comment removed for export] *)
      ab_tk F_8c6a4 D_8c6a4 ltac:((lazymatch goal with |- ?G => let G' := eval unfold c_eq in G in change_no_check G' end); rewrite bv_eqb_refl; reflexivity).   (* [comment removed for export] *)
      wd_refl.
    - post. all: try ra_solve.
  Qed.
End STRAD.

End FPGen.
End AsDepotAlloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Import AsAllocFHs.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac stk_ok ::= any_ok_r.   (* [comment removed for export] *)
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
(* [comment removed for export] *)
Ltac wc_has_or T := lazymatch T with
  | _ \/ _ => idtac
  | ?A /\ ?B => first [wc_has_or A | wc_has_or B]
  | ?A <-> ?B => first [wc_has_or A | wc_has_or B]
  | _ -> ?B => wc_has_or B
  end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wc_clear_disj := am_wc_clear_disj.   (* [comment removed for export] *)
Ltac wc_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wc_clear_disj; wc_lia0] | wc_lia0 ].
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation ASEGS := Asan.M.loaded_segments.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Ltac famo F D bbs vv Hr Hv :=
  chain_step; [reflexivity
    | eapply step_amoadd_d with (bs := bbs) (v := vv);
      [exact F | reflexivity | exact D
      | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_ulia
      | rd_addr Hr | exact Hv | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; first [stk_ok | hyp_ok] ]
    | step_simpl]; vn.

(* [comment removed for export] *)
Definition fr_e1e (mem : word -> option byte) (S p : word) (T n cnt k ba qb : Z) (bst bcs : list byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (word_to_le_bytes 8 (Z_to_bv 64 0x5008c)))
    (at_ S (-2224)) (word_to_le_bytes 8 (Z_to_bv 64 (0x103f18 + 728))))
    (at_ S (-2232)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 80)))
    (at_ S (-2240)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (at_ S (-2248)) (word_to_le_bytes 8 (at_ S (-2128))))
    (at_ S (-2256)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 208)))
    (at_ S (-2264)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 (T + 2128)) (word_to_le_bytes 4 (Z_to_bv 64 (cnt - 1))))
    (at_ (Z_to_bv 64 T) 2784) (word_to_le_bytes 8 (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (Z_to_bv 64 (bytes_le_to_Z bcs)))))
    (Z_to_bv 64 ba) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (ba + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n + 8192))))
    (Z_to_bv 64 (ba + 16)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
    (Z_to_bv 64 (ba + 24)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 (T + 88)) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
    (Z_to_bv 64 (T + 80)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
    (Z_to_bv 64 (T + 96)) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
    (Z_to_bv 64 (T + 104)) (word_to_le_bytes 8 (Z_to_bv 64 (qb + (n + 8192)))).
(* [comment removed for export] *)
Definition fr_e1f (mem : word -> option byte) (S p : word) (T n cnt k ba qb last len : Z) (bst bcs : list byte) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes
  (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes mem
    (at_ S (-2216)) (word_to_le_bytes 8 (Z_to_bv 64 0x5008c)))
    (at_ S (-2224)) (word_to_le_bytes 8 (Z_to_bv 64 (0x103f18 + 728))))
    (at_ S (-2232)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 80)))
    (at_ S (-2240)) (word_to_le_bytes 8 (Z_to_bv 64 n)))
    (at_ S (-2248)) (word_to_le_bytes 8 (at_ S (-2128))))
    (at_ S (-2256)) (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 208)))
    (at_ S (-2264)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 (T + 2128)) (word_to_le_bytes 4 (Z_to_bv 64 (cnt - 1))))
    (at_ (Z_to_bv 64 T) 2784) (word_to_le_bytes 8 (v_add (Z_to_bv 64 (bytes_le_to_Z bst)) (Z_to_bv 64 (bytes_le_to_Z bcs)))))
    (Z_to_bv 64 ba) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (ba + 8)) (word_to_le_bytes 8 (Z_to_bv 64 (n + 8192))))
    (Z_to_bv 64 (ba + 16)) (word_to_le_bytes 8 (Z_to_bv 64 1)))
    (Z_to_bv 64 (ba + 24)) (word_to_le_bytes 8 (at_ p (-16))))
    (Z_to_bv 64 last) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
    (Z_to_bv 64 (T + 80)) (word_to_le_bytes 8 (Z_to_bv 64 (len + 1))))
    (Z_to_bv 64 (T + 96)) (word_to_le_bytes 8 (Z_to_bv 64 ba)))
    (Z_to_bv 64 (T + 104)) (word_to_le_bytes 8 (Z_to_bv 64 (qb + (n + 8192)))).
Hint Unfold fr_e1e fr_e1f : asfr.

Section E1.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 ra0 s0v s1v s2v s3v s4v s5v : word).
  Variables (T n cnt k spb ba qb last len : Z) (bst bcs : list byte).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2208).
  Hypothesis H8 : getr regs 8 = Z_to_bv 64 (0x103f18 + 728).
  Hypothesis H9 : getr regs 9 = at_ (Z_to_bv 64 T) 80.
  Hypothesis H18 : getr regs 18 = Z_to_bv 64 n.
  Hypothesis H19 : getr regs 19 = at_ S (-2128).
  Hypothesis H20 : getr regs 20 = at_ (Z_to_bv 64 T) 208.
  Hypothesis H21 : getr regs 21 = at_ p (-16).
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 (2 ^ 20).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (AIMGHI + 16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584) /\ T mod 16 = 0)%Z.
  Hypothesis Hn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Hcnt : (1 <= cnt <= 16)%Z.
  Hypothesis Hk : (0 <= k < 2 ^ 32)%Z.
  Hypothesis Hspb : (0 <= spb)%Z.
  Hypothesis Hbak : (spb + 3 * 2 ^ 35 + 16 * k)%Z = ba.
  Hypothesis Hba : (AIMGHI <= ba /\ ba + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis HbaT : (ba + 8192 <= T \/ T + 4096 <= ba)%Z.
  Hypothesis Hqb : (0 <= qb <= 2 ^ 20)%Z.   (* [comment removed for export] *)
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Hret : ret_ok ra0.
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-2304)) 2304 = true.
  Hypothesis HokT : store_ok ASEGS mem (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Hokba : store_ok ASEGS mem (Z_to_bv 64 ba) 32 = true.
  (* [comment removed for export] *)
  Hypothesis Rqb : rdn ASEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb)).
  Hypothesis Rcnt : rdn ASEGS mem (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 cnt)).
  Hypothesis Rcs : rdn ASEGS mem (Z_to_bv 64 (T + 2136)) 8 = Some bcs.
  Hypothesis Rk : rdn ASEGS mem (Z_to_bv 64 (T + 2144 + 4 * (cnt - 1))) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 k)).
  Hypothesis Rst : rdn ASEGS mem (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis Rspb : rdn ASEGS mem (Z_to_bv 64 0x103f38) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 spb)).
  (* [comment removed for export] *)
  Hypothesis Rq0 : rdn ASEGS mem (at_ S (-2136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e4a4)).
  Hypothesis Rq1 : rdn ASEGS mem (at_ S (-2144)) 8 = Some (word_to_le_bytes 8 S).
  Hypothesis Rq2 : rdn ASEGS mem (at_ S (-2152)) 8 = Some (word_to_le_bytes 8 p).
  Hypothesis Rq3 : rdn ASEGS mem (at_ S (-2160)) 8 = Some (word_to_le_bytes 8 x18).
  Hypothesis Rq4 : rdn ASEGS mem (at_ S (-2168)) 8 = Some (word_to_le_bytes 8 x19).
  Hypothesis Rq5 : rdn ASEGS mem (at_ S (-2176)) 8 = Some (word_to_le_bytes 8 x20).
  Hypothesis Rq6 : rdn ASEGS mem (at_ S (-2184)) 8 = Some (word_to_le_bytes 8 x21).
  Hypothesis Rq7 : rdn ASEGS mem (at_ S (-2192)) 8 = Some (word_to_le_bytes 8 x22).
  Hypothesis Ri0 : rdn ASEGS mem (at_ S (-8)) 8 = Some (word_to_le_bytes 8 ra0).
  Hypothesis Ri1 : rdn ASEGS mem (at_ S (-16)) 8 = Some (word_to_le_bytes 8 s0v).
  Hypothesis Ri2 : rdn ASEGS mem (at_ S (-24)) 8 = Some (word_to_le_bytes 8 s1v).
  Hypothesis Ri3 : rdn ASEGS mem (at_ S (-32)) 8 = Some (word_to_le_bytes 8 s2v).
  Hypothesis Ri4 : rdn ASEGS mem (at_ S (-40)) 8 = Some (word_to_le_bytes 8 s3v).
  Hypothesis Ri5 : rdn ASEGS mem (at_ S (-48)) 8 = Some (word_to_le_bytes 8 s4v).
  Hypothesis Ri6 : rdn ASEGS mem (at_ S (-56)) 8 = Some (word_to_le_bytes 8 s5v).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma cnt_facts : ((cnt - 1) * 2 ^ 32 / 2 ^ 30 = 4 * (cnt - 1) /\ (T + 2784) mod 8 = 0)%Z.
  Proof using Lbcs Lbst Hk HT bcs bst k s5v S rom. split; [| lia]. replace ((cnt - 1) * 2 ^ 32)%Z with (4 * (cnt - 1) * 2 ^ 30)%Z by lia. rewrite Z.div_mul by lia. reflexivity. Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  #[local] Definition mid_regs (r : bvmap 5 word) : Prop :=
      getr r 2 = at_ S (-2272) /\ getr r 22 = Z_to_bv 64 (2 ^ 20)
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.

  (* [comment removed for export] *)
  Ltac e1_prefix Rlen lenv :=
      an F_5006c D_5006c;                              (* [comment removed for export] *)
      an F_50070 D_50070;                              (* [comment removed for export] *)
      an F_50074 D_50074;                              (* [comment removed for export] *)
      an F_50078 D_50078;                              (* [comment removed for export] *)
      an F_5007c D_5007c;                              (* [comment removed for export] *)
      an F_50080 D_50080;                              (* [comment removed for export] *)
      an F_50090 D_50090;                              (* [comment removed for export] *)
      fsd F_50094 D_50094 (at_ S (-2216));             (* [comment removed for export] *)
      fsd F_50098 D_50098 (at_ S (-2224));             (* [comment removed for export] *)
      fsd F_5009c D_5009c (at_ S (-2232));             (* [comment removed for export] *)
      fsd F_500a0 D_500a0 (at_ S (-2240));             (* [comment removed for export] *)
      fsd F_500a4 D_500a4 (at_ S (-2248));             (* [comment removed for export] *)
      fsd F_500a8 D_500a8 (at_ S (-2256));             (* [comment removed for export] *)
      fsd F_500ac D_500ac (at_ S (-2264));             (* [comment removed for export] *)
      cld8 F_500b0 D_500b0 (Z_to_bv 64 lenv) Rlen.     (* [comment removed for export] *)

  Lemma e1e_run :
    rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)) ->
    exists r,
      msteps ASEGS (mkst regs (0x50074 : word) mem rom) (mkst r (0x50194 : word) (fr_e1e mem S p T n cnt k ba qb bst bcs) rom)
      /\ mid_regs r.
  Proof using Rspb Rst Rk Rcs Rcnt Rqb Hokba HokT Hstk Lbcs Lbst Hqb HbaT Hba Hbak Hspb Hk Hcnt Hn HT HS H22 H21 H20 H19 H18 H9 H8 H2 spb s5v.
    intros Rlen. (lazymatch goal with |- ?G => let G' := eval unfold mid_regs in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct cnt_facts as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 cnt)) = bv_unsigned (Z_to_bv 64 cnt)) by (apply bytes4_small; lia).
    assert (Vk : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 k)) = bv_unsigned (Z_to_bv 64 k)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - e1_prefix Rlen 0%Z.
      ab_tk F_500b4 D_500b4 ltac:(condz).              (* [comment removed for export] *)
      clw F_500c8 D_500c8 (word_to_le_bytes 4 (Z_to_bv 64 cnt)) (Z_to_bv 64 cnt) Rcnt Vcnt.   (* [comment removed for export] *)
      rewrite (v_lw_small cnt) by lia.
      ab_ft F_500cc D_500cc ltac:(condz).              (* [comment removed for export] *)
      av F_500d0 D_500d0 (Z_to_bv 64 (cnt - 1)) ltac:(valz).            (* [comment removed for export] *)
      av F_500d4 D_500d4 (Z_to_bv 64 ((cnt - 1) * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      fsw F_500d8 D_500d8 (Z_to_bv 64 (T + 2128)).    (* [comment removed for export] *)
      av F_500dc D_500dc (Z_to_bv 64 (4 * (cnt - 1))) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity).  (* [comment removed for export] *)
      av F_500e0 D_500e0 (Z_to_bv 64 (T + 208 + 4 * (cnt - 1))) ltac:(valz).   (* [comment removed for export] *)
      cld F_500e4 D_500e4 bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs.   (* [comment removed for export] *)
      an F_500e8 D_500e8.                              (* [comment removed for export] *)
      an F_500ec D_500ec.                              (* [comment removed for export] *)
      clwu F_500f0 D_500f0 (word_to_le_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 64 k) Rk Vk.   (* [comment removed for export] *)
      famo F_500f4 D_500f4 bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst.   (* [comment removed for export] *)
      an F_500f8 D_500f8.                              (* [comment removed for export] *)
      cld8 F_500fc D_500fc (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      an F_50100 D_50100.                              (* [comment removed for export] *)
      av F_50104 D_50104 (Z_to_bv 64 (16 * k)) ltac:(valz).               (* [comment removed for export] *)
      av F_50108 D_50108 (Z_to_bv 64 (3 * 2 ^ 35)) ltac:(valz).           (* [comment removed for export] *)
      av F_5010c D_5010c (Z_to_bv 64 (spb + 3 * 2 ^ 35)) ltac:(valz).     (* [comment removed for export] *)
      av F_50110 D_50110 (Z_to_bv 64 ba) ltac:(valz).                     (* [comment removed for export] *)
      ab_ft F_50114 D_50114 ltac:(condz).              (* [comment removed for export] *)
      an F_50118 D_50118.                              (* [comment removed for export] *)
      an F_5011c D_5011c.                              (* [comment removed for export] *)
      av F_50120 D_50120 (Z_to_bv 64 (n + 8192)) ltac:(valz).             (* [comment removed for export] *)
      cld8 F_50124 D_50124 (Z_to_bv 64 0) Rlen.        (* [comment removed for export] *)
      fsd F_50128 D_50128 (Z_to_bv 64 ba).             (* [comment removed for export] *)
      fsd F_5012c D_5012c (Z_to_bv 64 (ba + 8)).       (* [comment removed for export] *)
      fsd F_50130 D_50130 (Z_to_bv 64 (ba + 16)).      (* [comment removed for export] *)
      fsd F_50134 D_50134 (Z_to_bv 64 (ba + 24)).      (* [comment removed for export] *)
      ab_tk F_50138 D_50138 ltac:(condz).              (* [comment removed for export] *)
      fsd F_50174 D_50174 (Z_to_bv 64 (T + 88)).       (* [comment removed for export] *)
      fsd F_50178 D_50178 (Z_to_bv 64 (T + 80)).       (* [comment removed for export] *)
      fsd F_5017c D_5017c (Z_to_bv 64 (T + 96)).       (* [comment removed for export] *)
      cld8 F_50180 D_50180 (Z_to_bv 64 qb) Rqb.        (* [comment removed for export] *)
      av F_50184 D_50184 (Z_to_bv 64 (qb + (n + 8192))) ltac:(valz).     (* [comment removed for export] *)
      fsd F_50188 D_50188 (Z_to_bv 64 (T + 104)).      (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_e1e mem S p T n cnt k ba qb bst bcs). wd_refl.
    - post.
  Qed.

  (* [comment removed for export] *)
  Hypothesis Hlen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis HlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Hlastba : (last + 8192 <= ba \/ ba + 8192 <= last)%Z.
  Hypothesis Hoklast : store_ok ASEGS mem (Z_to_bv 64 last) 8 = true.
  Hypothesis Rlast : rdn ASEGS mem (Z_to_bv 64 (T + 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 last)).
  Hypothesis Rlcnt : rdn ASEGS mem (Z_to_bv 64 (last + 16)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 1021)).

  Lemma e1f_run :
    rdn ASEGS mem (Z_to_bv 64 (T + 80)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 len)) ->
    exists r,
      msteps ASEGS (mkst regs (0x50074 : word) mem rom) (mkst r (0x50194 : word) (fr_e1f mem S p T n cnt k ba qb last len bst bcs) rom)
      /\ mid_regs r.
  Proof using Rlcnt Rlast Hoklast Hlastba HlastT Hlast Hlen Rspb Rst Rk Rcs Rcnt Rqb Hokba HokT Hstk Lbcs Lbst Hqb HbaT Hba Hbak Hspb Hk Hcnt Hn HT HS H22 H21 H20 H19 H18 H9 H8 H2 spb s5v.
    intros Rlen. (lazymatch goal with |- ?G => let G' := eval unfold mid_regs in G in change_no_check G' end).
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HT as (HT1 & HT2 & HT16). unfold hideW in HT2. destruct cnt_facts as [Hc4 Hal8].
    pose proof (bytes_le_to_Z_bound bst) as Bst. rewrite Lbst in Bst. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bst.
    pose proof (bytes_le_to_Z_bound bcs) as Bcs. rewrite Lbcs in Bcs. change (2 ^ (8 * Z.of_nat 8))%Z with (2 ^ 64)%Z in Bcs.
    pose proof (bytes_le_to_Z_nonneg bst) as Bst'. pose proof (bytes_le_to_Z_nonneg bcs) as Bcs'.
    assert (Vst : bytes_le_to_Z bst = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bst))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcs : bytes_le_to_Z bcs = bv_unsigned (Z_to_bv 64 (bytes_le_to_Z bcs))) by (rewrite u_Z2bv by lia; reflexivity).
    assert (Vcnt : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 cnt)) = bv_unsigned (Z_to_bv 64 cnt)) by (apply bytes4_small; lia).
    assert (Vk : bytes_le_to_Z (word_to_le_bytes 4 (Z_to_bv 64 k)) = bv_unsigned (Z_to_bv 64 k)) by (apply bytes4_small; lia).
    wd_eexists. split.
    - e1_prefix Rlen len.
      ab_ft F_500b4 D_500b4 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_500b8 D_500b8 (Z_to_bv 64 last) Rlast.    (* [comment removed for export] *)
      cld8 F_500bc D_500bc (Z_to_bv 64 1021) Rlcnt.    (* [comment removed for export] *)
      an F_500c0 D_500c0.                              (* [comment removed for export] *)
      ab_ft F_500c4 D_500c4 ltac:(condz).              (* [comment removed for export] *)
      clw F_500c8 D_500c8 (word_to_le_bytes 4 (Z_to_bv 64 cnt)) (Z_to_bv 64 cnt) Rcnt Vcnt.   (* [comment removed for export] *)
      rewrite (v_lw_small cnt) by lia.
      ab_ft F_500cc D_500cc ltac:(condz).              (* [comment removed for export] *)
      av F_500d0 D_500d0 (Z_to_bv 64 (cnt - 1)) ltac:(valz).            (* [comment removed for export] *)
      av F_500d4 D_500d4 (Z_to_bv 64 ((cnt - 1) * 2 ^ 32)) ltac:(valz).   (* [comment removed for export] *)
      fsw F_500d8 D_500d8 (Z_to_bv 64 (T + 2128)).    (* [comment removed for export] *)
      av F_500dc D_500dc (Z_to_bv 64 (4 * (cnt - 1))) ltac:(apply bv_eq; (lazymatch goal with |- ?G => let G' := eval unfold v_srli in G in change_no_check G' end); rewrite Z.shiftr_div_pow2 by lia; unorm; rewrite <- Hc4; unorm; reflexivity).  (* [comment removed for export] *)
      av F_500e0 D_500e0 (Z_to_bv 64 (T + 208 + 4 * (cnt - 1))) ltac:(valz).   (* [comment removed for export] *)
      cld F_500e4 D_500e4 bcs (Z_to_bv 64 (bytes_le_to_Z bcs)) Rcs Vcs.   (* [comment removed for export] *)
      an F_500e8 D_500e8.                              (* [comment removed for export] *)
      an F_500ec D_500ec.                              (* [comment removed for export] *)
      clwu F_500f0 D_500f0 (word_to_le_bytes 4 (Z_to_bv 64 k)) (Z_to_bv 64 k) Rk Vk.   (* [comment removed for export] *)
      famo F_500f4 D_500f4 bst (Z_to_bv 64 (bytes_le_to_Z bst)) Rst Vst.   (* [comment removed for export] *)
      an F_500f8 D_500f8.                              (* [comment removed for export] *)
      cld8 F_500fc D_500fc (Z_to_bv 64 spb) Rspb.      (* [comment removed for export] *)
      an F_50100 D_50100.                              (* [comment removed for export] *)
      av F_50104 D_50104 (Z_to_bv 64 (16 * k)) ltac:(valz).               (* [comment removed for export] *)
      av F_50108 D_50108 (Z_to_bv 64 (3 * 2 ^ 35)) ltac:(valz).           (* [comment removed for export] *)
      av F_5010c D_5010c (Z_to_bv 64 (spb + 3 * 2 ^ 35)) ltac:(valz).     (* [comment removed for export] *)
      av F_50110 D_50110 (Z_to_bv 64 ba) ltac:(valz).                     (* [comment removed for export] *)
      ab_ft F_50114 D_50114 ltac:(condz).              (* [comment removed for export] *)
      an F_50118 D_50118.                              (* [comment removed for export] *)
      an F_5011c D_5011c.                              (* [comment removed for export] *)
      av F_50120 D_50120 (Z_to_bv 64 (n + 8192)) ltac:(valz).             (* [comment removed for export] *)
      cld8 F_50124 D_50124 (Z_to_bv 64 len) Rlen.      (* [comment removed for export] *)
      fsd F_50128 D_50128 (Z_to_bv 64 ba).             (* [comment removed for export] *)
      fsd F_5012c D_5012c (Z_to_bv 64 (ba + 8)).       (* [comment removed for export] *)
      fsd F_50130 D_50130 (Z_to_bv 64 (ba + 16)).      (* [comment removed for export] *)
      fsd F_50134 D_50134 (Z_to_bv 64 (ba + 24)).      (* [comment removed for export] *)
      ab_ft F_50138 D_50138 ltac:(condz).              (* [comment removed for export] *)
      cld8 F_5013c D_5013c (Z_to_bv 64 last) Rlast.    (* [comment removed for export] *)
      fsd F_50140 D_50140 (Z_to_bv 64 last).           (* [comment removed for export] *)
      av F_50144 D_50144 (Z_to_bv 64 (len + 1)) ltac:(valz).              (* [comment removed for export] *)
      an F_50148 D_50148.                              (* [comment removed for export] *)
      fsd F_50178 D_50178 (Z_to_bv 64 (T + 80)).       (* [comment removed for export] *)
      fsd F_5017c D_5017c (Z_to_bv 64 (T + 96)).       (* [comment removed for export] *)
      cld8 F_50180 D_50180 (Z_to_bv 64 qb) Rqb.        (* [comment removed for export] *)
      av F_50184 D_50184 (Z_to_bv 64 (qb + (n + 8192))) ltac:(valz).     (* [comment removed for export] *)
      fsd F_50188 D_50188 (Z_to_bv 64 (T + 104)).      (* [comment removed for export] *)
      change (wbytes _ _ _) with (fr_e1f mem S p T n cnt k ba qb last len bst bcs). wd_refl.
    - post.
  Qed.
End E1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section QTAIL.
  Variables (mem rom : word -> option byte) (S p x18 x19 x20 x21 x22 ra0 s0v s1v s2v s3v s4v s5v v1 v3 v4 v5 v6 : word) (T qb2 : Z).
  Variable regs : bvmap 5 word.
  Hypothesis H2 : getr regs 2 = at_ S (-2272).
  Hypothesis H22 : getr regs 22 = Z_to_bv 64 (2 ^ 20).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis Hp : (AIMGHI + 16 <= bv_unsigned p /\ bv_unsigned p + 8 <= bv_unsigned S - 3584)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hqb2 : (0 <= qb2 <= 2 ^ 20)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Re0 : rdn ASEGS mem (at_ S (-2216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x5008c)).
  Hypothesis Re1 : rdn ASEGS mem (at_ S (-2224)) 8 = Some (word_to_le_bytes 8 v1).
  Hypothesis Re2 : rdn ASEGS mem (at_ S (-2232)) 8 = Some (word_to_le_bytes 8 (at_ (Z_to_bv 64 T) 80)).
  Hypothesis Re3 : rdn ASEGS mem (at_ S (-2240)) 8 = Some (word_to_le_bytes 8 v3).
  Hypothesis Re4 : rdn ASEGS mem (at_ S (-2248)) 8 = Some (word_to_le_bytes 8 v4).
  Hypothesis Re5 : rdn ASEGS mem (at_ S (-2256)) 8 = Some (word_to_le_bytes 8 v5).
  Hypothesis Re6 : rdn ASEGS mem (at_ S (-2264)) 8 = Some (word_to_le_bytes 8 v6).
  Hypothesis Rqb2 : rdn ASEGS mem (Z_to_bv 64 (T + 104)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 qb2)).
  (* [comment removed for export] *)
  Hypothesis Rq0 : rdn ASEGS mem (at_ S (-2136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x6e4a4)).
  Hypothesis Rq1 : rdn ASEGS mem (at_ S (-2144)) 8 = Some (word_to_le_bytes 8 S).
  Hypothesis Rq2 : rdn ASEGS mem (at_ S (-2152)) 8 = Some (word_to_le_bytes 8 p).
  Hypothesis Rq3 : rdn ASEGS mem (at_ S (-2160)) 8 = Some (word_to_le_bytes 8 x18).
  Hypothesis Rq4 : rdn ASEGS mem (at_ S (-2168)) 8 = Some (word_to_le_bytes 8 x19).
  Hypothesis Rq5 : rdn ASEGS mem (at_ S (-2176)) 8 = Some (word_to_le_bytes 8 x20).
  Hypothesis Rq6 : rdn ASEGS mem (at_ S (-2184)) 8 = Some (word_to_le_bytes 8 x21).
  Hypothesis Rq7 : rdn ASEGS mem (at_ S (-2192)) 8 = Some (word_to_le_bytes 8 x22).
  Hypothesis Ri0 : rdn ASEGS mem (at_ S (-8)) 8 = Some (word_to_le_bytes 8 ra0).
  Hypothesis Ri1 : rdn ASEGS mem (at_ S (-16)) 8 = Some (word_to_le_bytes 8 s0v).
  Hypothesis Ri2 : rdn ASEGS mem (at_ S (-24)) 8 = Some (word_to_le_bytes 8 s1v).
  Hypothesis Ri3 : rdn ASEGS mem (at_ S (-32)) 8 = Some (word_to_le_bytes 8 s2v).
  Hypothesis Ri4 : rdn ASEGS mem (at_ S (-40)) 8 = Some (word_to_le_bytes 8 s3v).
  Hypothesis Ri5 : rdn ASEGS mem (at_ S (-48)) 8 = Some (word_to_le_bytes 8 s4v).
  Hypothesis Ri6 : rdn ASEGS mem (at_ S (-56)) 8 = Some (word_to_le_bytes 8 s5v).

  Lemma q_tail_run :
    exists r,
      msteps ASEGS (mkst regs (0x50194 : word) mem rom) (mkst r ra0 mem rom)
      /\ getr r 2 = S /\ getr r 1 = ra0 /\ getr r 8 = s0v /\ getr r 9 = s1v /\ getr r 18 = s2v /\ getr r 19 = s3v
      /\ getr r 20 = s4v /\ getr r 21 = s5v /\ getr r 22 = x22
      /\ getr r 3 = getr regs 3 /\ getr r 4 = getr regs 4
      /\ getr r 23 = getr regs 23 /\ getr r 24 = getr regs 24 /\ getr r 25 = getr regs 25
      /\ getr r 26 = getr regs 26 /\ getr r 27 = getr regs 27.
  Proof using Ri6 Ri5 Ri4 Ri3 Ri2 Ri1 Ri0 Rq7 Rq6 Rq5 Rq4 Rq3 Rq2 Rq1 Rq0 Rqb2 Re6 Re5 Re4 Re3 Re2 Re1 Re0 Hret Hqb2 HT HS H22 H2 qb2 T v6 v5 v4 v3 v1 x21 x20 x19 x18 p.
    pose proof (u64_range S) as HSr. pose proof (u64_range p) as Hpr. destruct HT as (HT1 & HT2). unfold hideW in HT2.
    wd_eexists. split.
    - cld8 F_5018c D_5018c (Z_to_bv 64 0x5008c) Re0.        (* [comment removed for export] *)
      cld8 F_50190 D_50190 v1 Re1.                           (* [comment removed for export] *)
      cld8 F_50194 D_50194 (at_ (Z_to_bv 64 T) 80) Re2.     (* [comment removed for export] *)
      cld8 F_50198 D_50198 v3 Re3.                           (* [comment removed for export] *)
      cld8 F_5019c D_5019c v4 Re4.                           (* [comment removed for export] *)
      cld8 F_501a0 D_501a0 v5 Re5.                           (* [comment removed for export] *)
      cld8 F_501a4 D_501a4 v6 Re6.                           (* [comment removed for export] *)
      an F_501a8 D_501a8.                              (* [comment removed for export] *)
      rt F_501ac D_501ac.                              (* [comment removed for export] *)
      cld8 F_50084 D_50084 (Z_to_bv 64 qb2) Rqb2.      (* [comment removed for export] *)
      ab_ft F_50088 D_50088 ltac:(condz).              (* [comment removed for export] *)
      an F_5008c D_5008c.                              (* [comment removed for export] *)
      cld8 F_4ffbc D_4ffbc (Z_to_bv 64 0x6e4a4) Rq0.   (* [comment removed for export] *)
      cld8 F_4ffc0 D_4ffc0 S Rq1.                      (* [comment removed for export] *)
      cld8 F_4ffc4 D_4ffc4 p Rq2.                      (* [comment removed for export] *)
      cld8 F_4ffc8 D_4ffc8 x18 Rq3.                    (* [comment removed for export] *)
      cld8 F_4ffcc D_4ffcc x19 Rq4.                    (* [comment removed for export] *)
      cld8 F_4ffd0 D_4ffd0 x20 Rq5.                    (* [comment removed for export] *)
      cld8 F_4ffd4 D_4ffd4 x21 Rq6.                    (* [comment removed for export] *)
      cld8 F_4ffd8 D_4ffd8 x22 Rq7.                    (* [comment removed for export] *)
      an F_4ffdc D_4ffdc.                              (* [comment removed for export] *)
      rt F_4ffe0 D_4ffe0.                              (* [comment removed for export] *)
      an F_6e49c D_6e49c.                              (* [comment removed for export] *)
      cld8 F_6e4a0 D_6e4a0 ra0 Ri0.                    (* [comment removed for export] *)
      cld8 F_6e4a4 D_6e4a4 s0v Ri1.                    (* [comment removed for export] *)
      cld8 F_6e4a8 D_6e4a8 s1v Ri2.                    (* [comment removed for export] *)
      cld8 F_6e4ac D_6e4ac s2v Ri3.                    (* [comment removed for export] *)
      cld8 F_6e4b0 D_6e4b0 s3v Ri4.                    (* [comment removed for export] *)
      cld8 F_6e4b4 D_6e4b4 s4v Ri5.                    (* [comment removed for export] *)
      cld8 F_6e4b8 D_6e4b8 s5v Ri6.                    (* [comment removed for export] *)
      an F_6e4bc D_6e4bc.                              (* [comment removed for export] *)
      aret F_6e4c0 D_6e4c0 ra0.                        (* [comment removed for export] *)
      rewrite ?at_0. wd_refl.
    - post.
  Qed.
End QTAIL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section E1MEM.
  Variables (M13 : word -> option byte) (S p : word) (T n cnt k ba qb last len : Z) (bst bcs : list byte).
  Hypothesis HS : (2 ^ 24 <= bv_unsigned S /\ bv_unsigned S + 16 <= 2 ^ 47)%Z.
  Hypothesis HT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= bv_unsigned S - 3584))%Z.
  Hypothesis Hba : (AIMGHI <= ba /\ ba + 8192 <= bv_unsigned S - 3584)%Z.
  Hypothesis Hlast : (AIMGHI <= last /\ last + 8192 <= bv_unsigned S - 3584)%Z.
  #[local] Abbreviation U := bv_unsigned.
  #[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
  #[local] Abbreviation Me := (fr_e1e M13 S p T n cnt k ba qb bst bcs).
  #[local] Abbreviation Mf := (fr_e1f M13 S p T n cnt k ba qb last len bst bcs).
  Ltac digE := (lazymatch goal with |- ?G => let G' := eval unfold fr_e1e, fr_e1f in G in change_no_check G' end); repeat (wd_rdstep rd8_side).




















End E1MEM.
End FPGen.
