(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim RefMemcpyLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac Pm8ArtLeaf Pm8ArtPoison Pm8ArtAllocG Pm8ArtUnwind.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm8_code_a1000_a2000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Ltac uwf_prefix W Wt Cg Cps sp raw regs this pc top :=
  zstep F_a1ae0 D_a1ae0;
  zsd F_a1ae4 D_a1ae4 (sp - 8) (U raw) ltac:(rewok W); zsd F_a1ae8 D_a1ae8 (sp - 16) (U (getr regs 8)) ltac:(rewok W);
  zsd F_a1aec D_a1aec (sp - 24) (U (getr regs 9)) ltac:(rewok W); zsd F_a1af0 D_a1af0 (sp - 32) (U (getr regs 18)) ltac:(rewok W);
  zsd F_a1af4 D_a1af4 (sp - 40) (U (getr regs 19)) ltac:(rewok W); zsd F_a1af8 D_a1af8 (sp - 48) (U (getr regs 20)) ltac:(rewok W);
  zsd F_a1afc D_a1afc (sp - 56) (U (getr regs 21)) ltac:(rewok W); zsd F_a1b00 D_a1b00 (sp - 64) (U (getr regs 22)) ltac:(rewok W);
  zstep F_a1b04 D_a1b04; zstep F_a1b08 D_a1b08; zstep F_a1b0c D_a1b0c; zstep F_a1b10 D_a1b10;
  zbft F_a1b14 D_a1b14;
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    let Cg' := fresh "Cg'" in let Cps' := fresh "Cps'" in
    assert (Cg' : cellA X 0x153118 8 0x1ec460) by (recell Cg); assert (Cps' : cellA X 0x1ec460 8 4096) by (recell Cps);
    zstep F_a1b18 D_a1b18; zld F_a1b1c D_a1b1c 0x153118 Cg'; zld F_a1b20 D_a1b20 0x1ec460 Cps' end;
  zbft F_a1b24 D_a1b24;
  zstep F_a1b28 D_a1b28;
  stepn F_a1b2c D_a1b2c; rwH; rewrite art_zb_srli by lia;
  zsw F_a1b30 D_a1b30 (this + 8) 1 ltac:(rewok Wt);
  zsd F_a1b34 D_a1b34 (this + 16) pc ltac:(rewok Wt).

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
    zld F_a1bdc D_a1bdc (sp - 64 + 56) C56; rewrite Z_to_bv_bv_unsigned;
    zld F_a1be0 D_a1be0 (sp - 64 + 48) C48; rewrite Z_to_bv_bv_unsigned;
    zld F_a1be4 D_a1be4 (sp - 64 + 40) C40; rewrite Z_to_bv_bv_unsigned;
    zld F_a1be8 D_a1be8 (sp - 64 + 32) C32; rewrite Z_to_bv_bv_unsigned;
    zld F_a1bec D_a1bec (sp - 64 + 24) C24; rewrite Z_to_bv_bv_unsigned;
    zld F_a1bf0 D_a1bf0 (sp - 64 + 16) C16; rewrite Z_to_bv_bv_unsigned;
    zld F_a1bf4 D_a1bf4 (sp - 64 + 8) C08; rewrite Z_to_bv_bv_unsigned;
    zld F_a1bf8 D_a1bf8 (sp - 64 + 0) C00; rewrite Z_to_bv_bv_unsigned
  end;
  zstep F_a1bfc D_a1bfc;
  stepret F_a1c00 D_a1c00 raw ltac:(rwH; reflexivity);
  apply mst_refl.

Lemma art_unwind_fast_exit : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 256 < 2 ^ 63 -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> 0 <= bp < 2 ^ 63 ->
  (bp <= bot \/ top - 16 <= bp) -> 0 <= pc < 2 ^ 64 -> 0x6b3000 + 64 <= sp ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0xa1b30 : word) M rom) (mkst regs' raw M' rom)
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
  assert (RUN : exists regs', msteps ASEGS (mkst regs (0xa1b30 : word) M rom) (mkst regs' raw M1 rom)
                 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
                 /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)).
  { destruct (Z_le_gt_dec bp bot) as [E1|E1].
    - eexists. split.
      + uwf_prefix W Wt Cg Cps sp raw regs this pc top.
        zbtk F_a1b38 D_a1b38. zbft F_a1b80 D_a1b80. zbtk F_a1b84 D_a1b84.
        uwf_epilogue sp raw regs.
      + split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
        intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
          first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity].
    - assert (E2 : top - 16 <= bp) by lia.
      eexists. split.
      + uwf_prefix W Wt Cg Cps sp raw regs this pc top.
        zbtk F_a1b38 D_a1b38. zbft F_a1b80 D_a1b80. zbft F_a1b84 D_a1b84. zstep F_a1b88 D_a1b88. zbtk F_a1b8c D_a1b8c.
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

Lemma art_unwind_fast_any : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 2064 <= bp - 16 -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> bp < 2 ^ 63 -> bp mod 8 = 0 -> 0 <= pc < 2 ^ 64 ->
  0x6b3000 + 64 <= sp ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> (bot < bp -> bp < top - 16 -> readable8 M (bp - 16) top) -> cellA M 0x153118 8 0x1ec460 -> cellA M 0x1ec460 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0xa1b30 : word) M rom) (mkst regs' raw M' rom)
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
