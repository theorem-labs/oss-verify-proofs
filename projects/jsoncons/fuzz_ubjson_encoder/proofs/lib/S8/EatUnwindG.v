(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim RefMemcpyLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac EatLeaf EatPoison EatAllocG EatUnwind.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r80560_806c8.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Ltac uwf_prefix W Wt Cg Cps sp raw regs this pc top :=
  zstep F_9b284 D_9b284;
  zsd F_9b288 D_9b288 (sp - 8) (U raw) ltac:(rewok W); zsd F_9b28c D_9b28c (sp - 16) (U (getr regs 8)) ltac:(rewok W);
  zsd F_9b290 D_9b290 (sp - 24) (U (getr regs 9)) ltac:(rewok W); zsd F_9b294 D_9b294 (sp - 32) (U (getr regs 18)) ltac:(rewok W);
  zsd F_9b298 D_9b298 (sp - 40) (U (getr regs 19)) ltac:(rewok W); zsd F_9b29c D_9b29c (sp - 48) (U (getr regs 20)) ltac:(rewok W);
  zsd F_9b2a0 D_9b2a0 (sp - 56) (U (getr regs 21)) ltac:(rewok W); zsd F_9b2a4 D_9b2a4 (sp - 64) (U (getr regs 22)) ltac:(rewok W);
  zstep F_9b2a8 D_9b2a8; zstep F_9b2ac D_9b2ac; zstep F_9b2b0 D_9b2b0; zstep F_9b2b4 D_9b2b4;
  zbft F_9b2b8 D_9b2b8;
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    let Cg' := fresh "Cg'" in let Cps' := fresh "Cps'" in
    assert (Cg' : cellA X 0x139198 8 0x1d14a0) by (recell Cg); assert (Cps' : cellA X 0x1d14a0 8 4096) by (recell Cps);
    zstep F_9b2bc D_9b2bc; zld F_9b2c0 D_9b2c0 0x139198 Cg'; zld F_9b2c4 D_9b2c4 0x1d14a0 Cps' end;
  zbft F_9b2c8 D_9b2c8;
  zstep F_9b2cc D_9b2cc;
  stepn F_9b2d0 D_9b2d0; rwH; rewrite art_zb_srli by lia;
  zsw F_9b2d4 D_9b2d4 (this + 8) 1 ltac:(rewok Wt);
  zsd F_9b2d8 D_9b2d8 (this + 16) pc ltac:(rewok Wt).

Ltac uwf_epilogue sp raw regs :=
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    let C56 := fresh "C56" in let C48 := fresh "C48" in let C40 := fresh "C40" in let C32 := fresh "C32" in
    let C24 := fresh "C24" in let C16 := fresh "C16" in let C08 := fresh "C08" in let C00 := fresh "C00" in
    assert (C56 : cellA X (sp - 64 + 56) 8 (U raw)) by (replace (sp - 64 + 56) with (sp - 8) by lia; zcell);
    assert (C48 : cellA X (sp - 64 + 48) 8 (U (getr regs 8))) by (replace (sp - 64 + 48) with (sp - 16) by lia; zcell);
    assert (C40 : cellA X (sp - 64 + 40) 8 (U (getr regs 9))) by (replace (sp - 64 + 40) with (sp - 24) by lia; zcell);
    assert (C32 : cellA X (sp - 64 + 32) 8 (U (getr regs 18))) by (replace (sp - 64 + 32) with (sp - 32) by lia; zcell);
    assert (C24 : cellA X (sp - 64 + 24) 8 (U (getr regs 19))) by (replace (sp - 64 + 24) with (sp - 40) by lia; zcell);
    assert (C16 : cellA X (sp - 64 + 16) 8 (U (getr regs 20))) by (replace (sp - 64 + 16) with (sp - 48) by lia; zcell);
    assert (C08 : cellA X (sp - 64 + 8) 8 (U (getr regs 21))) by (replace (sp - 64 + 8) with (sp - 56) by lia; zcell);
    assert (C00 : cellA X (sp - 64 + 0) 8 (U (getr regs 22))) by (replace (sp - 64 + 0) with (sp - 64) by lia; zcell);
    zld F_9b380 D_9b380 (sp - 64 + 56) C56; rewrite Z_to_bv_bv_unsigned;
    zld F_9b384 D_9b384 (sp - 64 + 48) C48; rewrite Z_to_bv_bv_unsigned;
    zld F_9b388 D_9b388 (sp - 64 + 40) C40; rewrite Z_to_bv_bv_unsigned;
    zld F_9b38c D_9b38c (sp - 64 + 32) C32; rewrite Z_to_bv_bv_unsigned;
    zld F_9b390 D_9b390 (sp - 64 + 24) C24; rewrite Z_to_bv_bv_unsigned;
    zld F_9b394 D_9b394 (sp - 64 + 16) C16; rewrite Z_to_bv_bv_unsigned;
    zld F_9b398 D_9b398 (sp - 64 + 8) C08; rewrite Z_to_bv_bv_unsigned;
    zld F_9b39c D_9b39c (sp - 64 + 0) C00; rewrite Z_to_bv_bv_unsigned
  end;
  zstep F_9b3a0 D_9b3a0;
  stepret F_9b3a4 D_9b3a4 raw ltac:(rwH; reflexivity);
  apply mst_refl.

#[using="Type"] Lemma art_unwind_fast_exit : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 256 < 2 ^ 63 -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> 0 <= bp < 2 ^ 63 ->
  (bp <= bot \/ top - 16 <= bp) -> 0 <= pc < 2 ^ 64 -> 0x698000 + 64 <= sp ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x9b2d4 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> ~ (sp - 64 <= U x < sp) -> M' x = M x)
    /\ (exists sz, 1 <= sz <= 30 /\ cellA M' (this + 8) 4 sz /\ trace_cells M' this sz).
Proof.
  intros regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbt Htop4 Htop Hbp EXIT Hpc IMG W Wt Cg Cps.
  set (M1 := Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)))
               (sp - 40) (U (getr regs 19))) (sp - 48) (U (getr regs 20))) (sp - 56) (U (getr regs 21))) (sp - 64) (U (getr regs 22))) (this + 8) 1) (this + 16) pc).
  assert (Htop12 : 1 <= top / 2 ^ 12) by (apply Z.div_le_lower_bound; lia). assert (Htop12' : top / 2 ^ 12 < 2 ^ 52) by (apply Z.div_lt_upper_bound; lia).
  pose proof (art_u_lit top ltac:(lia)) as Utop.
  assert (RUN : exists regs', msteps ASEGS (mkst regs (0x9b2d4 : word) M rom) (mkst regs' raw M1 rom)
                 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
                 /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)).
  { destruct (Z_le_gt_dec bp bot) as [E1|E1].
    - eexists. split.
      + uwf_prefix W Wt Cg Cps sp raw regs this pc top.
        zbtk F_9b2dc D_9b2dc. zbft F_9b324 D_9b324. zbtk F_9b328 D_9b328.
        uwf_epilogue sp raw regs.
      + split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
        intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
          first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity].
    - assert (E2 : top - 16 <= bp) by lia.
      eexists. split.
      + uwf_prefix W Wt Cg Cps sp raw regs this pc top.
        zbtk F_9b2dc D_9b2dc. zbft F_9b324 D_9b324. zbft F_9b328 D_9b328. zstep F_9b32c D_9b32c. zbtk F_9b330 D_9b330.
        uwf_epilogue sp raw regs.
      + split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
        intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
          first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity]. }
  destruct RUN as (regs' & RUN & P2 & P1 & PK).
  exists regs', M1. split; [exact RUN|]. split; [exact P2|]. split; [exact P1|]. split; [exact PK|].
  split. { unfold M1. repeat (eapply mem_grows_trans; [|apply Wn_grows]). apply mem_grows_refl. }
  split. { intros x N1 N2 N3. unfold M1. rewrite !Wn_outside by (cbn; lia). reflexivity. }
  exists 1. split; [lia|]. split; [unfold M1; zcell|].
  intros i Hi. exists (Z_to_bv 64 pc). rewrite art_u_lit by lia. replace (this + 16 + 8 * i) with (this + 16) by lia. unfold M1. zcell.
Qed.

#[using="Type"] Lemma art_unwind_fast_any : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 2064 <= bp - 16 -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> bp < 2 ^ 63 -> bp mod 8 = 0 -> 0 <= pc < 2 ^ 64 ->
  0x698000 + 64 <= sp ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> (bot < bp -> bp < top - 16 -> readable8 M (bp - 16) top) -> cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x9b2d4 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ (forall x : word, ~ (this + 8 <= U x < this + 12) -> ~ (this + 16 <= U x < this + 256) -> ~ (sp - 64 <= U x < sp) -> M' x = M x)
    /\ (exists sz, 1 <= sz <= 30 /\ cellA M' (this + 8) 4 sz /\ trace_cells M' this sz).
Proof.
  intros regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot Hbt Htop4 Htop Hbp Hbp8 Hpc IMG W Wt RD Cg Cps.
  destruct (Z_lt_ge_dec bot bp) as [E1|E1]; [destruct (Z_lt_ge_dec bp (top - 16)) as [E2|E2]|].
  - apply (art_unwind_fast_run regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' Hthis Hbot E1 E2 Htop Hbp8 Hpc IMG W Wt (RD E1 E2) Cg Cps).
  - apply (art_unwind_fast_exit regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) ltac:(right; lia) Hpc IMG W Wt Cg Cps).
  - apply (art_unwind_fast_exit regs M rom raw sp this pc bp top bot H1 Hret H2 H10 H11 H12 H13 H14 H15 Hsp Hsp' ltac:(lia) Hbot Hbt Htop4 Htop ltac:(lia) ltac:(left; lia) Hpc IMG W Wt Cg Cps).
Qed.

End FPX.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
