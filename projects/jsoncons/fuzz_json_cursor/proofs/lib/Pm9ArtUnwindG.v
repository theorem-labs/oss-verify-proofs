(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim RefMemcpyLib As0StepLib
     ArtMem ArtRegs ArtAtomics ArtTac Pm9ArtLeaf Pm9ArtPoison Pm9ArtAllocG Pm9ArtUnwind.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import Pm9_code_a1000_a2000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Ltac uwf_prefix W Wt Cg Cps sp raw regs this pc top :=
  zstep F_a1ea8 D_a1ea8;
  zsd F_a1eac D_a1eac (sp - 8) (U raw) ltac:(rewok W); zsd F_a1eb0 D_a1eb0 (sp - 16) (U (getr regs 8)) ltac:(rewok W);
  zsd F_a1eb4 D_a1eb4 (sp - 24) (U (getr regs 9)) ltac:(rewok W); zsd F_a1eb8 D_a1eb8 (sp - 32) (U (getr regs 18)) ltac:(rewok W);
  zsd F_a1ebc D_a1ebc (sp - 40) (U (getr regs 19)) ltac:(rewok W); zsd F_a1ec0 D_a1ec0 (sp - 48) (U (getr regs 20)) ltac:(rewok W);
  zsd F_a1ec4 D_a1ec4 (sp - 56) (U (getr regs 21)) ltac:(rewok W); zsd F_a1ec8 D_a1ec8 (sp - 64) (U (getr regs 22)) ltac:(rewok W);
  zstep F_a1ecc D_a1ecc; zstep F_a1ed0 D_a1ed0; zstep F_a1ed4 D_a1ed4; zstep F_a1ed8 D_a1ed8;
  zbft F_a1edc D_a1edc;
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    let Cg' := fresh "Cg'" in let Cps' := fresh "Cps'" in
    assert (Cg' : cellA X 0x1544e0 8 0x1ed7a0) by (recell Cg); assert (Cps' : cellA X 0x1ed7a0 8 4096) by (recell Cps);
    zstep F_a1ee0 D_a1ee0; zld F_a1ee4 D_a1ee4 0x1544e0 Cg'; zld F_a1ee8 D_a1ee8 0x1ed7a0 Cps' end;
  zbft F_a1eec D_a1eec;
  zstep F_a1ef0 D_a1ef0;
  stepn F_a1ef4 D_a1ef4; rwH; rewrite art_zb_srli by lia;
  zsw F_a1ef8 D_a1ef8 (this + 8) 1 ltac:(rewok Wt);
  zsd F_a1efc D_a1efc (this + 16) pc ltac:(rewok Wt).

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
    zld F_a1fa4 D_a1fa4 (sp - 64 + 56) C56; rewrite Z_to_bv_bv_unsigned;
    zld F_a1fa8 D_a1fa8 (sp - 64 + 48) C48; rewrite Z_to_bv_bv_unsigned;
    zld F_a1fac D_a1fac (sp - 64 + 40) C40; rewrite Z_to_bv_bv_unsigned;
    zld F_a1fb0 D_a1fb0 (sp - 64 + 32) C32; rewrite Z_to_bv_bv_unsigned;
    zld F_a1fb4 D_a1fb4 (sp - 64 + 24) C24; rewrite Z_to_bv_bv_unsigned;
    zld F_a1fb8 D_a1fb8 (sp - 64 + 16) C16; rewrite Z_to_bv_bv_unsigned;
    zld F_a1fbc D_a1fbc (sp - 64 + 8) C08; rewrite Z_to_bv_bv_unsigned;
    zld F_a1fc0 D_a1fc0 (sp - 64 + 0) C00; rewrite Z_to_bv_bv_unsigned
  end;
  zstep F_a1fc4 D_a1fc4;
  stepret F_a1fc8 D_a1fc8 raw ltac:(rwH; reflexivity);
  apply mst_refl.

Lemma art_unwind_fast_exit : forall regs (M rom : word -> option byte) (raw : word) (sp this pc bp top bot : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 this -> getr regs 11 = Z_to_bv 64 pc ->
  getr regs 12 = Z_to_bv 64 bp -> getr regs 13 = Z_to_bv 64 top -> getr regs 14 = Z_to_bv 64 bot -> getr regs 15 = Z_to_bv 64 30 ->
  64 <= sp -> sp + 64 <= this -> this + 256 < 2 ^ 63 -> 0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> 0 <= bp < 2 ^ 63 ->
  (bp <= bot \/ top - 16 <= bp) -> 0 <= pc < 2 ^ 64 -> 0x6b4000 + 64 <= sp ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> cellA M 0x1544e0 8 0x1ed7a0 -> cellA M 0x1ed7a0 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0xa1ef0 : word) M rom) (mkst regs' raw M' rom)
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
  assert (RUN : exists regs', msteps ASEGS (mkst regs (0xa1ef0 : word) M rom) (mkst regs' raw M1 rom)
                 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
                 /\ (forall r : reg, In r [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 3; 4]%bv -> getr regs' r = getr regs r)).
  { destruct (Z_le_gt_dec bp bot) as [E1|E1].
    - eexists. split.
      + uwf_prefix W Wt Cg Cps sp raw regs this pc top.
        zbtk F_a1f00 D_a1f00. zbft F_a1f48 D_a1f48. zbtk F_a1f4c D_a1f4c.
        uwf_epilogue sp raw regs.
      + split; [gres; f_equal; lia|]. split; [gres; reflexivity|].
        intros r Hr. cbn [In] in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]; gres;
          first [reflexivity | rewrite Z_to_bv_bv_unsigned; reflexivity].
    - assert (E2 : top - 16 <= bp) by lia.
      eexists. split.
      + uwf_prefix W Wt Cg Cps sp raw regs this pc top.
        zbtk F_a1f00 D_a1f00. zbft F_a1f48 D_a1f48. zbft F_a1f4c D_a1f4c. zstep F_a1f50 D_a1f50. zbtk F_a1f54 D_a1f54.
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
  0x6b4000 + 64 <= sp ->
  wrA M (sp - 64) 64 -> wrA M this 256 -> (bot < bp -> bp < top - 16 -> readable8 M (bp - 16) top) -> cellA M 0x1544e0 8 0x1ed7a0 -> cellA M 0x1ed7a0 8 4096 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0xa1ef0 : word) M rom) (mkst regs' raw M' rom)
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
