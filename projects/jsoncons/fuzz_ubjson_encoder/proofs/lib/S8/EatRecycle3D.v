(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac EatLeaf EatAllocG EatPoison ArtRuns ArtRunsMem EatFp EatRefill1 EatCellEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import EatRecycle3 EatRecycle3R.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_r3ef18_4052c Ea0_code_r731ac_733ac.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

Definition art_lcdrain_a_mem (M : word -> option byte) (sp : Z) (raw : word) (ca ia c cnt h : Z) : word -> option byte :=
  Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 24) 0) (sp - 16) 0) (sp - 56) ia) (sp - 48) 0) (sp - 40) 0) (sp - 32) 0) (ca + 80 * c) (cnt - h).

#[using="Type"] Lemma art_lcdrain_a_fn : forall regs (M rom : word -> option byte) (raw : word) (sp ca ia c cnt h : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 (ca + 80 * c) -> getr regs 12 = Z_to_bv 64 ia -> getr regs 13 = Z_to_bv 64 c ->
  0x698000 + 64 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 64) 64 -> 4096 <= ca -> ca + 2592 <= sp - 64 -> 1 <= c <= 31 -> 0 <= ia < 2 ^ 64 ->
  1 <= h -> h <= cnt -> cnt <= 16 -> wrA M ca 2592 ->
  cellA M (ca + 80 * c) 4 cnt -> cellA M (ca + 80 * c + 4) 4 (2 * h) ->
  msteps ASEGS (mkst regs (0x55874 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (Z_to_bv 64 0x558d8)) 2 (Z_to_bv 64 (sp - 64))) 10 (Z_to_bv 64 ia)) 11 (Z_to_bv 64 (sp - 56))) 12 (Z_to_bv 64 (ca + 2560))) 14 (Z_to_bv 64 (ca + 80 * c + 16 + 4 * (cnt - h)))) 15 (Z_to_bv 64 h)) 16 (Z_to_bv 64 (ca + 2560)))
       (0x55a18 : word) (art_lcdrain_a_mem M sp raw ca ia c cnt h) rom).
Proof.
  intros regs M rom raw sp ca ia c cnt h H1 H2 H10 H11 H12 H13 Hsp Hsp' W Hca Hca' Hc Hia Hh Hhc Hcnt Wca Ccnt Cmc.
  zstep F_55824 D_55824.
  zsd F_55828 D_55828 (sp - 8) (U raw) ltac:(rewok W).
  zsd F_5582c D_5582c (sp - 24) 0 ltac:(zwok'). zsd F_55830 D_55830 (sp - 16) 0 ltac:(zwok').
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Ccnt' : cellA X (ca + 80 * c) 4 cnt) by zcell; assert (Cmc' : cellA X (ca + 80 * c + 4) 4 (2 * h)) by zcell end.
  zlw F_55834 D_55834 (ca + 80 * c) Ccnt'.
  zlwu F_55838 D_55838 (ca + 80 * c + 4) Cmc'.
  zsd F_5583c D_5583c (sp - 56) ia ltac:(zwok'). zsd F_55840 D_55840 (sp - 48) 0 ltac:(zwok'). zsd F_55844 D_55844 (sp - 40) 0 ltac:(zwok'). zsd F_55848 D_55848 (sp - 32) 0 ltac:(zwok').
  stepn F_5584c D_5584c. rwH. rewrite (art_zb_srli_exact _ 1 h) by lia.
  zstep F_55850 D_55850.
  stepn F_55854 D_55854. rwH. rewrite (art_zb_srli_exact _ 32 cnt) by lia.
  zbft F_55858 D_55858.
  zstep F_5585c D_5585c. zstep F_55860 D_55860.
  zsw F_55864 D_55864 (ca + 80 * c) (cnt - h) ltac:(zwok').
  zstep F_55868 D_55868. zstep F_5586c D_5586c. zstep F_55870 D_55870. zstep F_55874 D_55874. zstep F_55878 D_55878. zstep F_5587c D_5587c. zstep F_55880 D_55880.
  stepn F_55884 D_55884.
  unfold art_lcdrain_a_mem. zret.
Qed.

Definition art_f32 (M : word -> option byte) (sp : Z) (raw : word) (regs : bvmap 5 word) : word -> option byte :=
  Wn 8 (Wn 8 (Wn 8 (Wn 8 M (sp - 8) (U raw)) (sp - 16) (U (getr regs 8))) (sp - 24) (U (getr regs 9))) (sp - 32) (U (getr regs 18)).

#[using="Type"] Lemma art_unmap_null_fn : forall regs (M rom : word -> option byte) (raw : word) (sp : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 0 -> 48 <= sp -> sp < 2 ^ 64 -> wrA M (sp - 48) 48 ->
  msteps ASEGS (mkst regs (0x8de50 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd regs 1 raw) 2 (Z_to_bv 64 sp)) 8 (getr regs 8)) 9 (getr regs 9)) 18 (getr regs 18)) raw (art_f32 M sp raw regs) rom).
Proof.
  intros regs M rom raw sp H1 Hret H2 H10 Hsp Hsp' W.
  zstep F_8de00 D_8de00.
  zsd F_8de04 D_8de04 (sp - 8) (U raw) ltac:(rewok W). zsd F_8de08 D_8de08 (sp - 16) (U (getr regs 8)) ltac:(rewok W).
  zsd F_8de0c D_8de0c (sp - 24) (U (getr regs 9)) ltac:(rewok W). zsd F_8de10 D_8de10 (sp - 32) (U (getr regs 18)) ltac:(rewok W).
  zbtk F_8de14 D_8de14.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (G1 : cellA X (sp - 8) 8 (U raw)) by zcell; assert (G8 : cellA X (sp - 16) 8 (U (getr regs 8))) by zcell;
     assert (G9 : cellA X (sp - 24) 8 (U (getr regs 9))) by zcell; assert (G18 : cellA X (sp - 32) 8 (U (getr regs 18))) by zcell end.
  zld F_8de50 D_8de50 (sp - 8) G1. rewrite Z_to_bv_bv_unsigned.
  zld F_8de54 D_8de54 (sp - 16) G8. rewrite Z_to_bv_bv_unsigned.
  zld F_8de58 D_8de58 (sp - 24) G9. rewrite Z_to_bv_bv_unsigned.
  zld F_8de5c D_8de5c (sp - 32) G18. rewrite Z_to_bv_bv_unsigned.
  zstep F_8de60 D_8de60.
  stepret F_8de64 D_8de64 raw ltac:(reflexivity).
  unfold art_f32. zret.
Qed.

Ltac inl4 := cbn [In]; repeat (first [left; reflexivity | right]).

#[using="Type"] Lemma art_lcdrain_run : forall ws regs (M rom : word -> option byte) (raw : word) (sp HI ca ia c cnt h spb ris qris nf mfa nfr : Z),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 ca -> getr regs 11 = Z_to_bv 64 (ca + 80 * c) -> getr regs 12 = Z_to_bv 64 ia -> getr regs 13 = Z_to_bv 64 c ->
  0x698000 <= HI -> HI <= sp - 272 -> sp < 2 ^ 64 -> HI + 8388608 <= 2 ^ 47 -> 0x10000 <= ia -> ia + 4096 <= 0x698000 -> 1 <= c <= 30 ->
  0x698000 <= spb -> ris = spb + 2 ^ 37 -> ris = 128 * qris -> ris + 4096 <= HI ->
  4096 <= ca -> ca + 2592 <= HI -> (ca + 2592 <= 0x10000 \/ 0x698000 <= ca) -> apart ca 2592 spb (2 ^ 37 + 4096) ->
  h = Z.of_nat (length ws) -> 1 <= h -> h <= cnt -> cnt <= 16 ->
  0 <= nf < 2 ^ 40 -> 4 * (nf + h) <= mfa -> mfa <= 2 ^ 29 -> 0 <= nfr < 2 ^ 64 ->
  wrA M (sp - 272) 272 -> wrA M ca 2592 -> wrA M (ris + 128 * c) 128 -> wrA M (spb + c * 2 ^ 32 + 3758096384) mfa ->
  cellA M (ca + 80 * c) 4 cnt -> cellA M (ca + 80 * c + 4) 4 (2 * h) ->
  cellA M (ia + 32) 8 spb -> cellA M (ia + 48) 8 ris -> cellA M (ia + 40) 4 0xffffffff -> cellA M 0x139198 8 0x1d14a0 -> cellA M 0x1d14a0 8 4096 -> cellA M 0x10428 8 0xafffff00000fffff ->
  cellA M (ris + 128 * c) 8 0 -> cellA M (ris + 128 * c + 16) 8 nf -> cellA M (ris + 128 * c + 24) 8 mfa -> cellA M (ris + 128 * c + 80) 8 nfr ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (ca + 80 * c + 16 + 4 * (cnt - h) + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x55874 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 2 = Z_to_bv 64 sp
    /\ (forall x : reg, In x [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M'
    /\ art_agree [(sp - 272, 272); (ca + 80 * c, 4); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * h); (ris + 128 * c, 8); (ris + 128 * c + 16, 8); (ris + 128 * c + 80, 8)] M M'
    /\ cellA M' (ca + 80 * c) 4 (cnt - h)
    /\ cellA M' (ris + 128 * c) 8 0 /\ cellA M' (ris + 128 * c + 16) 8 (nf + h) /\ cellA M' (ris + 128 * c + 80) 8 (nfr + h)
    /\ (forall j, (j < length ws)%nat -> cellA M' (spb + c * 2 ^ 32 + 3758096384 + 4 * (nf + Z.of_nat j)) 4 (nth j ws 0)).
Proof.
  intros ws regs M rom raw sp HI ca ia c cnt h spb ris qris nf mfa nfr H1 Hret H2 H10 H11 H12 H13 HHI Hsp Hsp' HHI' Hia Hia' Hc Hspb Eris Eq Hris' Hca Hca' Hcai Aca Eh Hh Hhc Hcnt
    Hnf Hmfa Hmfa' Hnfr W Wca Wr Wfa Ccnt Cmc Cspb Cris Crel Cpc Cpg Crd Cmx Cnf Cmfa Cnfr Cws.
  unfold apart in Aca.
  pose proof (art_lcdrain_a_fn regs M rom raw sp ca ia c cnt h H1 H2 H10 H11 H12 H13 ltac:(lia) Hsp' ltac:(eapply wr_sub; [exact W|lia|lia]) Hca ltac:(lia) ltac:(lia) ltac:(lia)
                Hh Hhc Hcnt Wca Ccnt Cmc) as RUN1.
  unfold art_lcdrain_a_mem in RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R1 _ ?X1 _) =>
    assert (F1 : mem_grows M X1 /\ art_agree [(sp - 272, 272); (ca + 80 * c, 4)] M X1) by (split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
    assert (C1 : cellA X1 (ia + 32) 8 spb /\ cellA X1 (ia + 48) 8 ris /\ cellA X1 (ia + 40) 4 0xffffffff /\ cellA X1 0x139198 8 0x1d14a0 /\ cellA X1 0x1d14a0 8 4096
                 /\ cellA X1 0x10428 8 0xafffff00000fffff /\ cellA X1 (ris + 128 * c) 8 0 /\ cellA X1 (ris + 128 * c + 16) 8 nf /\ cellA X1 (ris + 128 * c + 24) 8 mfa
                 /\ cellA X1 (ris + 128 * c + 80) 8 nfr /\ cellA X1 (sp - 8) 8 (U raw) /\ cellA X1 (sp - 32) 8 0 /\ cellA X1 (sp - 24) 8 0 /\ cellA X1 (ca + 80 * c) 4 (cnt - h))
      by (repeat split; zcell);
    assert (Cws1 : forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA X1 (ca + 80 * c + 16 + 4 * (cnt - h) + 4 * Z.of_nat j) 4 (nth j ws 0))
      by (intros j Hj; destruct (Cws j Hj) as [Rj Cj]; split; [exact Rj|]; pose proof (proj1 (Nat2Z.inj_lt _ _) Hj); zcell);
    assert (W1 : wrA X1 (sp - 272) 272 /\ wrA X1 (ris + 128 * c) 128 /\ wrA X1 (spb + c * 2 ^ 32 + 3758096384) mfa) by (repeat split; zwr);
    set (Ra := R1) in *; set (Xa := X1) in *
  end.
  destruct F1 as (G1 & AG1). destruct W1 as (W1a & W1r & W1f).
  destruct C1 as (Cspb1 & Cris1 & Crel1 & Cpc1 & Cpg1 & Crd1 & Cmx1 & Cnf1 & Cmfa1 & Cnfr1 & E8 & E32 & E24 & Ccnt1).
  clearbody Xa.
  destruct (art_rta_run ws Ra Xa rom (0x558d8 : bv 64)%bv (sp - 64) HI ia (sp - 56) (ca + 2560) c (ca + 80 * c + 16 + 4 * (cnt - h)) h spb ris qris nf mfa nfr
              ltac:(unfold Ra; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
              ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; exact H13) ltac:(unfold Ra; gres; reflexivity) ltac:(unfold Ra; gres; reflexivity)
              HHI ltac:(lia) ltac:(lia) HHI' Hia Hia' Hc Hspb Eris Eq Hris' Eh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold apart; lia)
              Hnf Hmfa Hmfa' Hnfr ltac:(lia) ltac:(lia) ltac:(eapply wr_sub; [exact W1a|lia|lia]) W1r W1f Cspb1 Cris1 Crel1 Cpc1 Cpg1 Crd1 Cmx1 Cnf1 Cmfa1 Cnfr1 Cws1)
    as (r2 & M2 & RUN2 & B2 & BK & G2 & AG2 & Cmx2 & Cnf2 & Cnfr2 & Cfa2).
  replace (sp - 64 - 208) with (sp - 272) in AG2 by lia.
  set (W2 := [(sp - 272, 208); (spb + c * 2 ^ 32 + 3758096384 + 4 * nf, 4 * h); (ris + 128 * c, 8); (ris + 128 * c + 16, 8); (ris + 128 * c + 80, 8)]) in *.
  assert (GF : forall a k, sp - 64 <= a -> a + k <= sp -> art_gap W2 a k).
  { intros a k Ha Hk. unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (GC : art_gap W2 (ca + 80 * c) 4).
  { unfold W2. cbn [art_gap fst snd]. unfold apart. repeat split; try exact I; lia. }
  assert (F8 : cellA M2 (sp - 8) 8 (U raw)) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E8]).
  assert (F32 : cellA M2 (sp - 32) 8 0) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E32]).
  assert (F24 : cellA M2 (sp - 24) 8 0) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [apply GF; cbn; lia|lia|cbn; lia|exact E24]).
  assert (Ccnt2 : cellA M2 (ca + 80 * c) 4 (cnt - h)) by (apply (art_cell_tr W2 Xa M2 _ _ _ AG2); [exact GC|lia|cbn; lia|exact Ccnt1]).
  assert (W2a : wrA M2 (sp - 64 - 48) 48) by (eapply wr_grows; [exact G2|]; eapply wr_sub; [exact W1a|lia|lia]).
  eassert (RUN3 : msteps ASEGS (mkst r2 (0x558d8 : bv 64)%bv M2 rom) _).
  { zld F_55888 D_55888 (sp - 32) F32.
    zld F_5588c D_5588c (sp - 24) F24.
    zstep F_55890 D_55890.
    stepn F_55894 D_55894.
    zcall (art_unmap_null_fn _ _ _ (0x558e8 : word) (sp - 64)).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (F8' : cellA X (sp - 8) 8 (U raw)) by (unfold art_f32; zcell) end.
    zld F_55898 D_55898 (sp - 8) F8'. rewrite Z_to_bv_bv_unsigned.
    zstep F_5589c D_5589c.
    stepret F_558a0 D_558a0 raw ltac:(reflexivity).
    apply mst_refl. }
  match type of RUN3 with msteps _ _ (mkst ?R3 _ ?X3 _) =>
    assert (F3 : mem_grows M2 X3 /\ art_agree [(sp - 96, 32)] M2 X3) by (unfold art_f32; split; [zgrows|eapply art_agree_sub; [zagree|]; zsub]);
    set (M3 := X3) in *
  end.
  destruct F3 as (G3 & AG3). clearbody M3.
  assert (T3 : forall a (k : nat) v, apart a (Z.of_nat k) (sp - 96) 32 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M2 a k v -> cellA M3 a k v).
  { intros a k v A Ha Hk C. apply (art_cell_tr _ M2 M3 a k v AG3); [cbn [art_gap fst snd]; split; [exact A|exact I]|exact Ha|exact Hk|exact C]. }
  eexists. exists M3.
  split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; exact RUN3|].
  split; [gres; f_equal; lia|].
  split. { intros x Hx. cbn [In] in Hx.
    repeat (destruct Hx as [<-|Hx]; [gres; rewrite ?BK by inl4; unfold Ra; gres; reflexivity|]). destruct Hx. }
  split. { eapply mem_grows_trans; [exact G1|]. eapply mem_grows_trans; [exact G2|]. exact G3. }
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AG1|]; eapply art_agree_trans; [exact AG2|]; exact AG3|].
           unfold W2. intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; lia. }
  split; [apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Ccnt2]|].
  split; [apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cmx2]|].
  split; [apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cnf2]|].
  split; [apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact Cnfr2]|].
  intros j Hj. pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. apply T3; [unfold apart; cbn; lia|lia|cbn; lia|exact (Cfa2 j Hj)].
Qed.
End FPX.
