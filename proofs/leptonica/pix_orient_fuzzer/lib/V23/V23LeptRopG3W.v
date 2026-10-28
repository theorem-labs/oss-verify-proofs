(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23LeptRop2Segs V23LeptRopGSpec V23LeptRopG3Segs.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Local Ltac nlia := cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
Local Ltac splitc := repeat match goal with |- _ /\ _ => split end.
Local Ltac gag AG := match goal with |- getr _ ?r = _ => rewrite (AG r ltac:(notin_list)) end.
Local Ltac feed G T :=
  lazymatch type of G with
  | ?P -> _ =>
      let HP := fresh "HP" in
      tryif (assert (HP : P) by T) then (specialize (G HP); clear HP; feed G T)
      else fail 0 "feed: cannot prove" P
  | _ => idtac
  end.

Lemma rg3w_bool : forall b : bool, b = true \/ b = false.
Proof. intros []; auto. Qed.
Lemma rg3w_if04 : forall b : bool, (0 <= (if b then 0 else 4) <= 4)%Z.
Proof. intros []; lia. Qed.
Lemma rg3w_if40 : forall b : bool, (0 <= (if b then 4 else 0) <= 4)%Z.
Proof. intros []; lia. Qed.
Lemma rg3w_wrr : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Section RG3.
Context {fx : FPState}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

  Variable MB : word -> option byte.
  Variable rom : word -> option byte.
  Variables s datad nd datas ns : Z.
  Variables dh swpl dwpl dxb sls nfw : Z.
  Variables psf pdf psF pdF psl pdl : Z.
  Variables fw f6 f7 nofull nolast f3 : bool.

  Hypothesis Hs : (250000 <= s /\ s + 64 < 2 ^ 64)%Z.
  Hypothesis Hdd : (4096 <= datad /\ 0 < nd /\ datad + nd + 2 ^ 27 <= 2 ^ 64 /\ datad mod 4 = 0)%Z.
  Hypothesis Hds : (4096 <= datas /\ 0 < ns /\ datas + ns + 2 ^ 27 <= 2 ^ 64 /\ datas mod 4 = 0)%Z.
  Hypothesis SOKd : store_ok SEGS MB (Z_to_bv 64 datad) (Z.to_nat nd) = true.
  Hypothesis SOKs : store_ok SEGS MB (Z_to_bv 64 datas) (Z.to_nat ns) = true.
  Hypothesis FR : disj_apart datad nd (s - 240) 240.
  Hypothesis Hgeo : (1 <= dh < 2 ^ 24 /\ 0 <= swpl < 2 ^ 24 /\ 0 <= dwpl < 2 ^ 24 /\ 1 <= sls <= 31 /\ 0 <= nfw < 2 ^ 26)%Z.
  Hypothesis Hdxb : (0 <= dxb < 32)%Z /\ (if fw then dxb <> 0 else dxb = 0)%Z.
  Hypothesis Hnf : nofull = false -> (1 <= nfw)%Z.

  Hypothesis C_nl : rdn SEGS MB (Z_to_bv 64 (s - 216)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nolast then 1 else 0))).
  Hypothesis C_nf : rdn SEGS MB (Z_to_bv 64 (s - 208)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if nofull then 1 else 0))).
  Hypothesis C_swpl : rdn SEGS MB (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)).
  Hypothesis C_z : rdn SEGS MB (Z_to_bv 64 (s - 120)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
  Hypothesis C_dh : rdn SEGS MB (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh)).
  Hypothesis C_rows : fw = true \/ nolast = false -> rg_rows MB s dh.
  Hypothesis C_f6 : fw = true -> rdn SEGS MB (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))).
  Hypothesis C_nfw : nofull = false -> rdn SEGS MB (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw)).
  Hypothesis C_f3 : nolast = false -> rdn SEGS MB (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))).
  Hypothesis C_psl : nolast = false -> rdn SEGS MB (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)).
  Hypothesis C_mk : nolast = false -> exists mk : word, rdn SEGS MB (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk).

  Hypothesis RF : fw = true -> (psf mod 4 = 0 /\ pdf mod 4 = 0)%Z /\
    (forall i, 0 <= i < dh -> datad <= pdf + 4 * dwpl * i /\ pdf + 4 * dwpl * i + 4 <= datad + nd /\
                              datas <= psf + 4 * swpl * i /\ psf + 4 * swpl * i + 4 + (if f6 && negb f7 then 4 else 0) <= datas + ns)%Z.
  Hypothesis RW : nofull = false -> (psF mod 4 = 0 /\ pdF mod 4 = 0)%Z /\
    (forall i, 0 <= i < dh -> datad <= pdF + 4 * dwpl * i /\ pdF + 4 * dwpl * i + 4 * nfw <= datad + nd /\
                              datas <= psF + 4 * swpl * i /\ psF + 4 * swpl * i + 4 * nfw + 4 <= datas + ns)%Z.
  Hypothesis RL : nolast = false -> (psl mod 4 = 0 /\ pdl mod 4 = 0)%Z /\
    (forall i, 0 <= i < dh -> datad <= pdl + 4 * dwpl * i /\ pdl + 4 * dwpl * i + 4 <= datad + nd /\
                              datas <= psl + 4 * swpl * i /\ psl + 4 * swpl * i + 4 + (if f3 then 0 else 4) <= datas + ns)%Z.

  Definition Inv3 (Mi : word -> option byte) : Prop :=
    (forall x : word, (u x < datad \/ datad + nd <= u x)%Z -> Mi x = MB x) /\ mem_grows MB Mi.

  Lemma Inv3_rdn_frame : forall Mi (a : Z) (n : nat) bs, Inv3 Mi -> (s - 240 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
    rdn SEGS MB (Z_to_bv 64 a) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros Mi a n bs [HI _] Ha Hn HM. pose proof FR as FR'. use_apart FR'. rewrite <- HM.
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply HI. lia.
  Qed.

  Lemma rg3_FR : (datad + nd <= s - 240 \/ s - 240 + 240 <= datad)%Z.
  Proof. exact FR. Qed.

  Lemma rg3_Inv_MB : Inv3 MB.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma rg3_Inv_store : forall Mi (a : Z) (bs : list byte),
    Inv3 Mi -> (datad <= a)%Z -> (a + Z.of_nat (length bs) <= datad + nd)%Z -> Inv3 (wbytes Mi (Z_to_bv 64 a) bs).
  Proof.
    intros Mi a bs [HI HG] Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb. split.
    - intros x Hx. rewrite MemSplit.wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI, Hx.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.

  Lemma rg3_Inv_sok : forall Mi (a : Z) (n : nat), Inv3 Mi -> (datad <= a)%Z -> (a + Z.of_nat n <= datad + nd)%Z ->
    store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi a n [_ HG] Ha Hn. eapply store_ok_mono; [exact HG|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS MB (Z_to_bv 64 datad) _ (Z.to_nat nd)); [ | exact SOKd | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma rg3_rd4 : forall Mi base RS (a : Z), Inv3 Mi -> store_ok SEGS MB (Z_to_bv 64 base) (Z.to_nat RS) = true ->
    (0 <= base /\ base + RS <= 2 ^ 64)%Z -> (base <= a)%Z -> (a + 4 <= base + RS)%Z ->
    exists bs, rdn SEGS Mi (Z_to_bv 64 a) 4 = Some bs /\ length bs = 4%nat.
  Proof.
    intros Mi base RS a [_ HG] SOK Hb Ha H4.
    apply (store_ok_rdn SEGS Mi 4 (Z_to_bv 64 a) rg3w_wrr).
    eapply store_ok_mono; [exact HG|].
    eapply (store_ok_sub SEGS MB (Z_to_bv 64 base) _ (Z.to_nat RS)); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma rg3_rows_Inv : forall Mi, Inv3 Mi -> rg_rows MB s dh -> rg_rows Mi s dh.
  Proof.
    intros Mi HI (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B).
    unfold rg_rows. exists c28, c30, c38, c40, c48, c50.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ B)))))).
    all: apply (Inv3_rdn_frame Mi _ 8 _ HI); [lia | nlia | assumption].
  Qed.

  Definition FInv3 (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 15 = Z_to_bv 64 psf /\ getr regs 13 = Z_to_bv 64 (4 * swpl) /\
    getr regs 7 = Z_to_bv 64 (4 * dwpl) /\ getr regs 20 = Z_to_bv 64 (psf + 4 * swpl) /\
    getr regs 19 = Z_to_bv 64 (if f6 then 1 else 0) /\ getr regs 24 = Z_to_bv 64 (if f7 then 1 else 0) /\
    getr regs 22 = Z_to_bv 64 1 /\ getr regs 23 = Z_to_bv 64 0 /\ getr regs 9 = Z_to_bv 64 0 /\ getr regs 1 = Z_to_bv 64 31 /\
    getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

  Definition IInv3 (i : Z) (regs : bvmap 5 word) : Prop :=
    getr regs 27 = Z_to_bv 64 (psF + 4 * swpl * i) /\ getr regs 6 = Z_to_bv 64 (psF + 4 * swpl * i) /\
    getr regs 1 = Z_to_bv 64 (pdF + 4 * dwpl * i) /\ getr regs 18 = Z_to_bv 64 (pdF + 4 * dwpl * i) /\
    getr regs 20 = Z_to_bv 64 (4 * nfw) /\ getr regs 16 = Z_to_bv 64 1 /\ getr regs 28 = Z_to_bv 64 1 /\
    getr regs 9 = Z_to_bv 64 1 /\ getr regs 21 = Z_to_bv 64 1 /\ getr regs 19 = Z_to_bv 64 32 /\
    getr regs 25 = Z_to_bv 64 18446744073709551611 /\ getr regs 26 = Z_to_bv 64 31 /\
    getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

  Definition WInv3 (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 5 = Z_to_bv 64 (4 * dwpl) /\ getr regs 7 = Z_to_bv 64 (4 * swpl) /\
    getr regs 20 = Z_to_bv 64 (4 * nfw) /\ getr regs 23 = Z_to_bv 64 0 /\ getr regs 19 = Z_to_bv 64 32 /\
    getr regs 25 = Z_to_bv 64 18446744073709551611 /\ getr regs 17 = Z_to_bv 64 1 /\ getr regs 22 = Z_to_bv 64 1 /\
    getr regs 26 = Z_to_bv 64 31 /\ getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

  Definition LInv3 (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 5 = Z_to_bv 64 (if f3 then 1 else 0) /\ getr regs 17 = Z_to_bv 64 0 /\
    getr regs 14 = Z_to_bv 64 0 /\ getr regs 7 = Z_to_bv 64 18446744073709551611 /\ getr regs 19 = Z_to_bv 64 31 /\
    getr regs 16 = Z_to_bv 64 32 /\ getr regs 28 = Z_to_bv 64 (psl + 4 * swpl) /\ getr regs 15 = Z_to_bv 64 (4 * dwpl) /\
    getr regs 6 = Z_to_bv 64 (4 * swpl) /\ getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

  Local Ltac inv_agree AG HI :=
    repeat match type of HI with _ /\ _ => let A := fresh "A" in destruct HI as [A HI] end;
    splitc; match goal with |- getr _ ?r = _ => rewrite (AG r ltac:(notin_list)); assumption end.

  Lemma FInv3_agree : forall r r', regs_agree (fun x : reg => In x [11; 12; 16; 21; 25; 26; 28]%list) r r' -> FInv3 r -> FInv3 r'.
  Proof. intros r r' AG HI. unfold FInv3 in *. inv_agree AG HI. Qed.
  Lemma IInv3_agree : forall i r r', regs_agree (fun x : reg => In x [12; 15; 24]%list) r r' -> IInv3 i r -> IInv3 i r'.
  Proof. intros i r r' AG HI. unfold IInv3 in *. inv_agree AG HI. Qed.
  Lemma WInv3_agree : forall r r', regs_agree (fun x : reg => In x [1; 6; 9; 11; 12; 15; 16; 18; 21; 24; 27; 28]%list) r r' -> WInv3 r -> WInv3 r'.
  Proof. intros r r' AG HI. unfold WInv3 in *. inv_agree AG HI. Qed.
  Lemma LInv3_agree : forall r r', regs_agree (fun x : reg => In x [9; 10; 11; 18; 20; 21; 22; 23]%list) r r' -> LInv3 r -> LInv3 r'.
  Proof. intros r r' AG HI. unfold LInv3 in *. inv_agree AG HI. Qed.

  Lemma rg3_F1 : forall (last : bool) regs Mi i, fw = true -> (0 <= i)%Z -> (if last then i = dh - 1 else i < dh - 1)%Z ->
    Inv3 Mi -> FInv3 regs ->
    getr regs 11 = Z_to_bv 64 (4 * swpl * i) -> getr regs 25 = Z_to_bv 64 (pdf + 4 * dwpl * i) ->
    getr regs 16 = Z_to_bv 64 (pdf + 4 * dwpl * i) -> getr regs 28 = Z_to_bv 64 (- (dh - i)) ->
    exists regs' M', msteps SEGS (mkst regs RG3_F Mi rom) (mkst regs' (if last then RG3_X1 else RG3_F) M' rom) /\ Inv3 M' /\
      FInv3 regs' /\ getr regs' 11 = Z_to_bv 64 (4 * swpl * (i + 1)) /\ getr regs' 25 = Z_to_bv 64 (pdf + 4 * dwpl * (i + 1)) /\
      getr regs' 16 = Z_to_bv 64 (pdf + 4 * dwpl * (i + 1)) /\ getr regs' 28 = Z_to_bv 64 (- (dh - (i + 1))) /\
      regs_agree (fun r : reg => In r [11; 12; 16; 21; 25; 26; 28]%list) regs regs'.
  Proof.
    intros last regs Mi i Efw Hi Hl HI FI H11 H25 H16 H28.
    assert (Hi' : (i < dh)%Z) by (destruct last; cbv iota in Hl; lia).
    pose proof rg3_FR as FRu.
    destruct (RF Efw) as ((ALs & ALd) & RB).
    destruct (RB 0%Z ltac:(lia)) as (B01 & _ & B03 & _). destruct (RB i ltac:(lia)) as (B1 & B2 & B3 & B4).
    pose proof (rg3w_if40 (f6 && negb f7)) as IF.
    assert (Mij : (0 <= 4 * swpl * i)%Z /\ (0 <= 4 * dwpl * i)%Z) by (split; apply Z.mul_nonneg_nonneg; lia).
    pose proof FI as (I2 & I15 & I13 & I7 & I20 & I19 & I24 & I22 & I23 & I9 & I1 & I30 & I8).
    destruct (rg3_rd4 Mi datas ns (psf + 4 * swpl * i) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs0 & R0 & L0).
    destruct (rg3_rd4 Mi datad nd (pdf + 4 * dwpl * i) HI SOKd ltac:(lia) ltac:(lia) ltac:(lia)) as (bd & Rd & Ld).
    pose proof (rg3_Inv_sok Mi (pdf + 4 * dwpl * i) 4 HI ltac:(lia) ltac:(nlia)) as SK.
    pose proof (Inv3_rdn_frame Mi (s - 120) 8 _ HI ltac:(lia) ltac:(nlia) C_z) as Cz.
    assert (X1 : exists bs1, f6 = true -> f7 = false ->
      (psf + 4 * swpl * i + 8 < 2 ^ 64 /\ rdn SEGS Mi (Z_to_bv 64 (psf + 4 * swpl * i + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z).
    { destruct (f6 && negb f7) eqn:E67.
      - assert (B4' : (psf + 4 * swpl * i + 4 + 4 <= datas + ns)%Z) by (cbv beta iota in B4; lia).
        destruct (rg3_rd4 Mi datas ns (psf + 4 * swpl * i + 4) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs1 & R1 & L1).
        exists bs1. intros _ _. split; [lia | split; assumption].
      - exists nil. intros E6 E7. rewrite E6, E7 in E67. cbn in E67. discriminate E67. }
    destruct X1 as (bs1 & X1).
    pose proof (rg3_F rom f6 f7 last regs Mi s psf (4 * swpl * i) (pdf + 4 * dwpl * i) (4 * swpl) (4 * dwpl) (dh - i) sls bs0 bs1 bd) as G.
    feed G ltac:(first [eassumption | nlia | (destruct last; cbv iota in Hl |- *; nlia)]).
    destruct G as (r1 & w & S1 & A11 & A25 & A16 & A28 & AG1).
    exists r1. eexists. split; [exact S1|].
    split; [apply rg3_Inv_store; [exact HI | lia | rewrite length_N_to_le_bytes; nlia]|].
    split; [exact (FInv3_agree regs r1 AG1 FI)|].
    split; [rewrite A11; f_equal; ring|]. split; [rewrite A25; f_equal; ring|].
    split; [rewrite A16; f_equal; ring|]. split; [rewrite A28; f_equal; ring | exact AG1].
  Qed.

  Lemma rg3_Fs : forall (k : nat) regs Mi i, fw = true -> (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z -> Inv3 Mi -> FInv3 regs ->
    getr regs 11 = Z_to_bv 64 (4 * swpl * i) -> getr regs 25 = Z_to_bv 64 (pdf + 4 * dwpl * i) ->
    getr regs 16 = Z_to_bv 64 (pdf + 4 * dwpl * i) -> getr regs 28 = Z_to_bv 64 (- (dh - i)) ->
    exists regs' M', msteps SEGS (mkst regs RG3_F Mi rom) (mkst regs' RG3_X1 M' rom) /\ Inv3 M' /\
      regs_agree (fun r : reg => In r [11; 12; 16; 21; 25; 26; 28]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Efw Hi Hk HI FI H11 H25 H16 H28.
    - destruct (rg3_F1 true regs Mi i Efw Hi ltac:(nlia) HI FI H11 H25 H16 H28) as (r1 & M1 & S1 & HI1 & _ & _ & _ & _ & _ & AG1).
      exists r1, M1. split; [exact S1 | split; [exact HI1 | exact AG1]].
    - destruct (rg3_F1 false regs Mi i Efw Hi ltac:(nlia) HI FI H11 H25 H16 H28)
        as (r1 & M1 & S1 & HI1 & FI1 & A11 & A25 & A16 & A28 & AG1).
      destruct (IH r1 M1 (i + 1)%Z Efw ltac:(lia) ltac:(lia) HI1 FI1 A11 A25 A16 A28) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]]].
  Qed.

  Lemma rg3_I1 : forall (last : bool) regs Mi i j, nofull = false -> (0 <= i < dh)%Z -> (0 <= j)%Z ->
    (if last then j = nfw - 1 else j < nfw - 1)%Z -> Inv3 Mi -> IInv3 i regs -> getr regs 24 = Z_to_bv 64 (4 * j) ->
    exists regs' M', msteps SEGS (mkst regs RG3_I Mi rom) (mkst regs' (if last then RG3_T2 else RG3_I) M' rom) /\ Inv3 M' /\
      IInv3 i regs' /\ getr regs' 24 = Z_to_bv 64 (4 * (j + 1)) /\ regs_agree (fun r : reg => In r [12; 15; 24]%list) regs regs'.
  Proof.
    intros last regs Mi i j Enf Hi Hj Hl HI II H24.
    assert (Hj' : (j < nfw)%Z) by (destruct last; cbv iota in Hl; lia).
    destruct (RW Enf) as ((ALs & ALd) & RB). destruct (RB i Hi) as (B1 & B2 & B3 & B4).
    assert (Mij : (0 <= 4 * swpl * i)%Z /\ (0 <= 4 * dwpl * i)%Z) by (split; apply Z.mul_nonneg_nonneg; lia).
    pose proof II as (I27 & I6 & I1 & I18 & I20 & I16 & I28 & I9 & I21 & I23 & I22 & I26 & I30 & I8).
    destruct (rg3_rd4 Mi datas ns (psF + 4 * swpl * i + 4 * j) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs0 & R0 & L0).
    destruct (rg3_rd4 Mi datas ns (psF + 4 * swpl * i + 4 * j + 4) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs1 & R1 & L1).
    pose proof (rg3_Inv_sok Mi (pdF + 4 * dwpl * i + 4 * j) 4 HI ltac:(lia) ltac:(nlia)) as SK.
    pose proof (rg3_I rom last regs Mi (psF + 4 * swpl * i) (pdF + 4 * dwpl * i) (4 * j) (4 * nfw) sls bs0 bs1) as G.
    feed G ltac:(first [eassumption | nlia | (destruct last; cbv iota in Hl |- *; nlia)]).
    destruct G as (r1 & w & S1 & A24 & AG1).
    exists r1. eexists. split; [exact S1|].
    split; [apply rg3_Inv_store; [exact HI | lia | rewrite length_N_to_le_bytes; nlia]|].
    split; [exact (IInv3_agree i regs r1 AG1 II)|].
    split; [rewrite A24; f_equal; ring | exact AG1].
  Qed.

  Lemma rg3_Is : forall (k : nat) regs Mi i j, nofull = false -> (0 <= i < dh)%Z -> (0 <= j)%Z -> (j + Z.of_nat k = nfw - 1)%Z ->
    Inv3 Mi -> IInv3 i regs -> getr regs 24 = Z_to_bv 64 (4 * j) ->
    exists regs' M', msteps SEGS (mkst regs RG3_I Mi rom) (mkst regs' RG3_T2 M' rom) /\ Inv3 M' /\
      regs_agree (fun r : reg => In r [12; 15; 24]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i j Enf Hi Hj Hk HI II H24.
    - destruct (rg3_I1 true regs Mi i j Enf Hi Hj ltac:(nlia) HI II H24) as (r1 & M1 & S1 & HI1 & _ & _ & AG1).
      exists r1, M1. split; [exact S1 | split; [exact HI1 | exact AG1]].
    - destruct (rg3_I1 false regs Mi i j Enf Hi Hj ltac:(nlia) HI II H24) as (r1 & M1 & S1 & HI1 & II1 & A24 & AG1).
      destruct (IH r1 M1 i (j + 1)%Z Enf Hi ltac:(lia) ltac:(lia) HI1 II1 A24) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]]].
  Qed.

  Lemma rg3_row1 : forall (last : bool) regs Mi i, nofull = false -> (0 <= i)%Z -> (if last then i = dh - 1 else i < dh - 1)%Z ->
    Inv3 Mi -> WInv3 regs -> getr regs 11 = Z_to_bv 64 i ->
    getr regs 6 = Z_to_bv 64 (psF + 4 * swpl * i) -> getr regs 27 = Z_to_bv 64 (psF + 4 * swpl * i) ->
    getr regs 18 = Z_to_bv 64 (pdF + 4 * dwpl * i) -> getr regs 1 = Z_to_bv 64 (pdF + 4 * dwpl * i) ->
    exists regs' M', msteps SEGS (mkst regs RG3_H2 Mi rom) (mkst regs' (if last then RG3_X2 else RG3_H2) M' rom) /\ Inv3 M' /\
      WInv3 regs' /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\
      getr regs' 6 = Z_to_bv 64 (psF + 4 * swpl * (i + 1)) /\ getr regs' 27 = Z_to_bv 64 (psF + 4 * swpl * (i + 1)) /\
      getr regs' 18 = Z_to_bv 64 (pdF + 4 * dwpl * (i + 1)) /\ getr regs' 1 = Z_to_bv 64 (pdF + 4 * dwpl * (i + 1)) /\
      regs_agree (fun r : reg => In r [1; 6; 9; 11; 12; 15; 16; 18; 21; 24; 27; 28]%list) regs regs'.
  Proof.
    intros last regs Mi i Enf Hi Hl HI WI H11 H6 H27 H18 H1.
    assert (Hi' : (i < dh)%Z) by (destruct last; cbv iota in Hl; lia).
    destruct (RW Enf) as ((ALs & ALd) & RB). destruct (RB i ltac:(lia)) as (B1 & B2 & B3 & B4).
    pose proof (Hnf Enf) as Hn1.
    assert (Mij : (0 <= 4 * swpl * i)%Z /\ (0 <= 4 * dwpl * i)%Z) by (split; apply Z.mul_nonneg_nonneg; lia).
    pose proof WI as (W2 & W5 & W7 & W20 & W19 & W23 & W22 & W17 & W25 & W26 & W30 & W8).
    pose proof (Inv3_rdn_frame Mi (s - 128) 8 _ HI ltac:(lia) ltac:(nlia) (C_nfw Enf)) as Cnfw.
    pose proof (rg3_H2 rom regs Mi s nfw (psF + 4 * swpl * i) (pdF + 4 * dwpl * i)) as G.
    feed G ltac:(first [eassumption | nlia]).
    destruct G as (r1 & S1 & A24 & A16 & A28 & A9 & A21 & AG1).
    assert (II : IInv3 i r1) by (unfold IInv3; splitc; first [eassumption | (gag AG1; eassumption)]).
    destruct (rg3_Is (Z.to_nat (nfw - 1)) r1 Mi i 0 Enf ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) HI II
                ltac:(rewrite A24; f_equal; ring)) as (r2 & Ma & S2 & HIa & AG2).
    assert (AG12 : regs_agree (fun r : reg => In r [9; 12; 15; 16; 21; 24; 28]%list) regs r2)
      by (eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2]).
    pose proof (Inv3_rdn_frame Ma (s - 120) 8 _ HIa ltac:(lia) ltac:(nlia) C_z) as Cz.
    pose proof (Inv3_rdn_frame Ma (s - 112) 8 _ HIa ltac:(lia) ltac:(nlia) C_dh) as Cdh.
    pose proof (rg3_T2 rom last r2 Ma s i dh (4 * dwpl) (4 * swpl) (psF + 4 * swpl * i) (pdF + 4 * dwpl * i)) as G.
    feed G ltac:(first [eassumption | nlia | (destruct last; cbv iota in Hl |- *; nlia) | (gag AG12; eassumption)]).
    destruct G as (r3 & S3 & C11 & C6 & C27 & C18 & C1 & AG3).
    assert (AG : regs_agree (fun r : reg => In r [1; 6; 9; 11; 12; 15; 16; 18; 21; 24; 27; 28]%list) regs r3)
      by (eapply regs_agree_trans; [regs_agree_weaken AG12 | regs_agree_weaken AG3]).
    exists r3, Ma. split; [eapply msteps_trans; [exact S1|]; eapply msteps_trans; [exact S2 | exact S3]|].
    split; [exact HIa|]. split; [exact (WInv3_agree regs r3 AG WI)|].
    split; [exact C11|].
    split; [rewrite C6; f_equal; ring|]. split; [rewrite C27; f_equal; ring|].
    split; [rewrite C18; f_equal; ring|]. split; [rewrite C1; f_equal; ring | exact AG].
  Qed.

  Lemma rg3_Hs : forall (k : nat) regs Mi i, nofull = false -> (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z -> Inv3 Mi -> WInv3 regs ->
    getr regs 11 = Z_to_bv 64 i ->
    getr regs 6 = Z_to_bv 64 (psF + 4 * swpl * i) -> getr regs 27 = Z_to_bv 64 (psF + 4 * swpl * i) ->
    getr regs 18 = Z_to_bv 64 (pdF + 4 * dwpl * i) -> getr regs 1 = Z_to_bv 64 (pdF + 4 * dwpl * i) ->
    exists regs' M', msteps SEGS (mkst regs RG3_H2 Mi rom) (mkst regs' RG3_X2 M' rom) /\ Inv3 M' /\
      regs_agree (fun r : reg => In r [1; 6; 9; 11; 12; 15; 16; 18; 21; 24; 27; 28]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Enf Hi Hk HI WI H11 H6 H27 H18 H1.
    - destruct (rg3_row1 true regs Mi i Enf Hi ltac:(nlia) HI WI H11 H6 H27 H18 H1)
        as (r1 & M1 & S1 & HI1 & _ & _ & _ & _ & _ & _ & AG1).
      exists r1, M1. split; [exact S1 | split; [exact HI1 | exact AG1]].
    - destruct (rg3_row1 false regs Mi i Enf Hi ltac:(nlia) HI WI H11 H6 H27 H18 H1)
        as (r1 & M1 & S1 & HI1 & WI1 & A11 & A6 & A27 & A18 & A1 & AG1).
      destruct (IH r1 M1 (i + 1)%Z Enf ltac:(lia) ltac:(lia) HI1 WI1 A11 A6 A27 A18 A1) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]]].
  Qed.

  Lemma rg3_L1 : forall (last : bool) regs Mi i, nolast = false -> (0 <= i)%Z -> (if last then i = dh - 1 else i < dh - 1)%Z ->
    Inv3 Mi -> LInv3 regs ->
    getr regs 11 = Z_to_bv 64 (4 * swpl * i) -> getr regs 10 = Z_to_bv 64 (pdl + 4 * dwpl * i) ->
    getr regs 20 = Z_to_bv 64 (pdl + 4 * dwpl * i) -> getr regs 9 = Z_to_bv 64 (- (dh - i)) ->
    exists regs' M', msteps SEGS (mkst regs RG3_L Mi rom) (mkst regs' (if last then RG_E else RG3_L) M' rom) /\ Inv3 M' /\
      LInv3 regs' /\ getr regs' 11 = Z_to_bv 64 (4 * swpl * (i + 1)) /\ getr regs' 10 = Z_to_bv 64 (pdl + 4 * dwpl * (i + 1)) /\
      getr regs' 20 = Z_to_bv 64 (pdl + 4 * dwpl * (i + 1)) /\ getr regs' 9 = Z_to_bv 64 (- (dh - (i + 1))) /\
      regs_agree (fun r : reg => In r [9; 10; 11; 18; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros last regs Mi i Enl Hi Hl HI LI H11 H10 H20 H9.
    assert (Hi' : (i < dh)%Z) by (destruct last; cbv iota in Hl; lia).
    pose proof rg3_FR as FRu.
    destruct (RL Enl) as ((ALs & ALd) & RB).
    destruct (RB 0%Z ltac:(lia)) as (B01 & _ & B03 & _). destruct (RB i ltac:(lia)) as (B1 & B2 & B3 & B4).
    pose proof (rg3w_if04 f3) as IF.
    assert (Mij : (0 <= 4 * swpl * i)%Z /\ (0 <= 4 * dwpl * i)%Z) by (split; apply Z.mul_nonneg_nonneg; lia).
    pose proof LI as (I2 & I5 & I17 & I14 & I7 & I19 & I16 & I28 & I15 & I6 & I30 & I8).
    destruct (C_mk Enl) as (mk & Cmk0).
    destruct (rg3_rd4 Mi datas ns (psl + 4 * swpl * i) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs0 & R0 & L0).
    destruct (rg3_rd4 Mi datad nd (pdl + 4 * dwpl * i) HI SOKd ltac:(lia) ltac:(lia) ltac:(lia)) as (bd & Rd & Ld).
    pose proof (rg3_Inv_sok Mi (pdl + 4 * dwpl * i) 4 HI ltac:(lia) ltac:(nlia)) as SK.
    pose proof (Inv3_rdn_frame Mi (s - 120) 8 _ HI ltac:(lia) ltac:(nlia) C_z) as Cz.
    pose proof (Inv3_rdn_frame Mi (s - 136) 8 _ HI ltac:(lia) ltac:(nlia) (C_psl Enl)) as Cpsl.
    pose proof (Inv3_rdn_frame Mi (s - 144) 8 _ HI ltac:(lia) ltac:(nlia) Cmk0) as Cmk.
    assert (X1 : exists bs1, f3 = false ->
      (psl + 4 * swpl * i + 8 < 2 ^ 64 /\ rdn SEGS Mi (Z_to_bv 64 (psl + 4 * swpl * i + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z).
    { destruct (rg3w_bool f3) as [E3 | E3].
      - exists nil. intros E. rewrite E3 in E. discriminate E.
      - assert (B4' : (psl + 4 * swpl * i + 4 + 4 <= datas + ns)%Z) by (rewrite E3 in B4; exact B4).
        destruct (rg3_rd4 Mi datas ns (psl + 4 * swpl * i + 4) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs1 & R1 & L1).
        exists bs1. intros _. split; [lia | split; assumption]. }
    destruct X1 as (bs1 & X1).
    pose proof (rg3_L rom f3 last regs Mi s psl (4 * swpl * i) (pdl + 4 * dwpl * i) (4 * swpl) (4 * dwpl) (dh - i) sls mk bs0 bs1 bd) as G.
    feed G ltac:(first [eassumption | nlia | (destruct last; cbv iota in Hl |- *; nlia)]).
    destruct G as (r1 & w & S1 & A11 & A10 & A20 & A9 & AG1).
    exists r1. eexists. split; [exact S1|].
    split; [apply rg3_Inv_store; [exact HI | lia | rewrite length_N_to_le_bytes; nlia]|].
    split; [exact (LInv3_agree regs r1 AG1 LI)|].
    split; [rewrite A11; f_equal; ring|]. split; [rewrite A10; f_equal; ring|].
    split; [rewrite A20; f_equal; ring|]. split; [rewrite A9; f_equal; ring | exact AG1].
  Qed.

  Lemma rg3_Ls : forall (k : nat) regs Mi i, nolast = false -> (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z -> Inv3 Mi -> LInv3 regs ->
    getr regs 11 = Z_to_bv 64 (4 * swpl * i) -> getr regs 10 = Z_to_bv 64 (pdl + 4 * dwpl * i) ->
    getr regs 20 = Z_to_bv 64 (pdl + 4 * dwpl * i) -> getr regs 9 = Z_to_bv 64 (- (dh - i)) ->
    exists regs' M', msteps SEGS (mkst regs RG3_L Mi rom) (mkst regs' RG_E M' rom) /\ Inv3 M' /\
      regs_agree (fun r : reg => In r [9; 10; 11; 18; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Enl Hi Hk HI LI H11 H10 H20 H9.
    - destruct (rg3_L1 true regs Mi i Enl Hi ltac:(nlia) HI LI H11 H10 H20 H9) as (r1 & M1 & S1 & HI1 & _ & _ & _ & _ & _ & AG1).
      exists r1, M1. split; [exact S1 | split; [exact HI1 | exact AG1]].
    - destruct (rg3_L1 false regs Mi i Enl Hi ltac:(nlia) HI LI H11 H10 H20 H9)
        as (r1 & M1 & S1 & HI1 & LI1 & A11 & A10 & A20 & A9 & AG1).
      destruct (IH r1 M1 (i + 1)%Z Enl ltac:(lia) ltac:(lia) HI1 LI1 A11 A10 A20 A9) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]]].
  Qed.

  Lemma rg3_ph1 : forall regs,
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 1 = Z_to_bv 64 dxb -> getr regs 14 = Z_to_bv 64 dwpl ->
    getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
    (fw = true -> getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0)) ->
    exists regs' M', msteps SEGS (mkst regs RG3_S1 MB rom) (mkst regs' RG3_X1 M' rom) /\ Inv3 M' /\
      regs_agree (fun r : reg => In r [1; 5; 7; 9; 11; 12; 13; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 28]%list) regs regs'.
  Proof.
    intros regs H2 H1 H14 H30 H8 HF.
    assert (BS : fw = true ->
      (0 <= psf < 2 ^ 64)%Z /\ (0 <= pdf < 2 ^ 64)%Z /\ (psf mod 4 = 0)%Z /\ (pdf mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
      getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0) /\
      rdn SEGS MB (Z_to_bv 64 (s - 224)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f6 then 1 else 0))) /\
      rdn SEGS MB (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
      rg_rows MB s dh).
    { intros E. destruct (RF E) as ((ALs & ALd) & RB). destruct (RB 0%Z ltac:(lia)) as (B1 & B2 & B3 & B4).
      pose proof (rg3w_if40 (f6 && negb f7)). destruct (HF E) as (X15 & X25 & X26).
      pose proof (C_f6 E). pose proof (C_rows (or_introl E)).
      splitc; first [eassumption | lia]. }
    destruct (rg3_S1 rom fw f6 f7 regs MB s dxb psf pdf swpl dwpl dh ltac:(lia) ltac:(lia) (proj1 Hdxb) (proj2 Hdxb)
                ltac:(lia) ltac:(lia) H1 H2 H14 BS) as (r1 & S1 & P1 & AG1).
    destruct (rg3w_bool fw) as [Efw | Efw].
    - rewrite Efw in S1.
      destruct (P1 Efw) as (X11 & X20 & X13 & X7 & X16 & X28 & X9 & X19 & X24 & X22 & X23 & X1).
      destruct (HF Efw) as (Y15 & Y25 & Y26).
      assert (FI : FInv3 r1) by (unfold FInv3; splitc; first [eassumption | (gag AG1; eassumption)]).
      destruct (rg3_Fs (Z.to_nat (dh - 1)) r1 MB 0 Efw ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) rg3_Inv_MB FI
                  ltac:(rewrite X11; f_equal; ring) ltac:(gag AG1; rewrite Y25; f_equal; ring)
                  ltac:(rewrite X16; f_equal; ring) ltac:(rewrite X28; f_equal; ring)) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2|]].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    - rewrite Efw in S1.
      exists r1, MB. split; [exact S1 | split; [exact rg3_Inv_MB | regs_agree_weaken AG1]].
  Qed.

  Lemma rg3_ph2 : forall regs Mi, Inv3 Mi ->
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
    getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
    (nofull = false -> getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF) ->
    exists regs' M', msteps SEGS (mkst regs RG3_X1 Mi rom) (mkst regs' RG3_X2 M' rom) /\ Inv3 M' /\
      regs_agree (fun r : reg => In r [1; 5; 6; 7; 9; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%list) regs regs'.
  Proof.
    intros regs Mi HI H2 H14 H30 H8 HW.
    pose proof (Inv3_rdn_frame Mi (s - 208) 8 _ HI ltac:(lia) ltac:(nlia) C_nf) as Cnf.
    assert (BX : nofull = false ->
      (0 <= psF < 2 ^ 64)%Z /\ (0 <= pdF < 2 ^ 64)%Z /\ (psF mod 4 = 0)%Z /\ (pdF mod 4 = 0)%Z /\
      getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF /\
      rdn SEGS Mi (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
      rdn SEGS Mi (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw))).
    { intros E. destruct (RW E) as ((ALs & ALd) & RB). destruct (RB 0%Z ltac:(lia)) as (B1 & B2 & B3 & B4).
      destruct (HW E) as (X6 & X18).
      pose proof (Inv3_rdn_frame Mi (s - 152) 8 _ HI ltac:(lia) ltac:(nlia) C_swpl).
      pose proof (Inv3_rdn_frame Mi (s - 128) 8 _ HI ltac:(lia) ltac:(nlia) (C_nfw E)).
      splitc; first [eassumption | lia]. }
    destruct (rg3_X1 rom nofull regs Mi s psF pdF nfw swpl dwpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cnf H2 H14 BX)
      as (r1 & S1 & P1 & AG1).
    destruct (rg3w_bool nofull) as [Enf | Enf].
    - rewrite Enf in S1. exists r1, Mi. split; [exact S1 | split; [exact HI | regs_agree_weaken AG1]].
    - rewrite Enf in S1.
      destruct (P1 Enf) as (X11 & X5 & X7 & X20 & X19 & X23 & X22 & X17 & X25 & X26 & X27 & X1).
      destruct (HW Enf) as (Y6 & Y18).
      assert (WI : WInv3 r1) by (unfold WInv3; splitc; first [eassumption | (gag AG1; eassumption)]).
      destruct (rg3_Hs (Z.to_nat (dh - 1)) r1 Mi 0 Enf ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) HI WI X11
                  ltac:(gag AG1; rewrite Y6; f_equal; ring) ltac:(rewrite X27; f_equal; ring)
                  ltac:(gag AG1; rewrite Y18; f_equal; ring) ltac:(rewrite X1; f_equal; ring)) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2|]].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  Lemma rg3_ph3 : forall regs Mi, Inv3 Mi ->
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
    getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
    (nolast = false -> getr regs 10 = Z_to_bv 64 pdl) ->
    exists regs' M', msteps SEGS (mkst regs RG3_X2 Mi rom) (mkst regs' RG_E M' rom) /\ Inv3 M' /\
      regs_agree (fun r : reg => In r [5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 28]%list) regs regs'.
  Proof.
    intros regs Mi HI H2 H14 H30 H8 HL.
    pose proof (Inv3_rdn_frame Mi (s - 216) 8 _ HI ltac:(lia) ltac:(nlia) C_nl) as Cnl.
    assert (BX : nolast = false ->
      (0 <= psl < 2 ^ 64)%Z /\ (0 <= pdl < 2 ^ 64)%Z /\ (psl mod 4 = 0)%Z /\ (pdl mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
      getr regs 10 = Z_to_bv 64 pdl /\
      rdn SEGS Mi (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) /\
      rdn SEGS Mi (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))) /\
      rdn SEGS Mi (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
      (exists mk : word, rdn SEGS Mi (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk)) /\
      rg_rows Mi s dh).
    { intros E. destruct (RL E) as ((ALs & ALd) & RB). destruct (RB 0%Z ltac:(lia)) as (B1 & B2 & B3 & B4).
      pose proof (rg3w_if04 f3). pose proof (HL E).
      destruct (C_mk E) as (mk & Cmk0).
      pose proof (Inv3_rdn_frame Mi (s - 136) 8 _ HI ltac:(lia) ltac:(nlia) (C_psl E)).
      pose proof (Inv3_rdn_frame Mi (s - 232) 8 _ HI ltac:(lia) ltac:(nlia) (C_f3 E)).
      pose proof (Inv3_rdn_frame Mi (s - 152) 8 _ HI ltac:(lia) ltac:(nlia) C_swpl).
      pose proof (Inv3_rdn_frame Mi (s - 144) 8 _ HI ltac:(lia) ltac:(nlia) Cmk0).
      pose proof (rg3_rows_Inv Mi HI (C_rows (or_intror E))).
      splitc; first [eassumption | lia | (eexists; eassumption)]. }
    destruct (rg3_X2 rom nolast f3 regs Mi s psl pdl swpl dwpl dh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cnl H2 H14 BX)
      as (r1 & S1 & P1 & AG1).
    destruct (rg3w_bool nolast) as [Enl | Enl].
    - rewrite Enl in S1. exists r1, Mi. split; [exact S1 | split; [exact HI | regs_agree_weaken AG1]].
    - rewrite Enl in S1.
      destruct (P1 Enl) as (X11 & X15 & X6 & X17 & X9 & X16 & X5 & X14 & X7 & X28 & X19 & X20).
      pose proof (HL Enl) as Y10.
      assert (LI : LInv3 r1) by (unfold LInv3; splitc; first [eassumption | (gag AG1; eassumption)]).
      destruct (rg3_Ls (Z.to_nat (dh - 1)) r1 Mi 0 Enl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) HI LI
                  ltac:(rewrite X11; f_equal; ring) ltac:(gag AG1; rewrite Y10; f_equal; ring)
                  ltac:(rewrite X20; f_equal; ring) ltac:(rewrite X9; f_equal; ring)) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2|]].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  Theorem rg3_loops : forall regs,
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 1 = Z_to_bv 64 dxb -> getr regs 14 = Z_to_bv 64 dwpl ->
    getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
    (fw = true -> getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0)) ->
    (nofull = false -> getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF) ->
    (nolast = false -> getr regs 10 = Z_to_bv 64 pdl) ->
    exists regs' M',
      msteps SEGS (mkst regs RG3_S1 MB rom) (mkst regs' RG_E M' rom)
      /\ Inv3 M' /\ getr regs' 2 = Z_to_bv 64 (s - 240)
      /\ regs_agree (fun r : reg => In r [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%list) regs regs'.
  Proof.
    intros regs H2 H1 H14 H30 H8 HF HW HL.
    destruct (rg3_ph1 regs H2 H1 H14 H30 H8 HF) as (r1 & M1 & S1 & HI1 & AG1).
    destruct (rg3_ph2 r1 M1 HI1 ltac:(gag AG1; exact H2) ltac:(gag AG1; exact H14) ltac:(gag AG1; exact H30) ltac:(gag AG1; exact H8)
                ltac:(intros E; destruct (HW E) as (X6 & X18); split; gag AG1; assumption)) as (r2 & M2 & S2 & HI2 & AG2).
    assert (AG12 : regs_agree (fun r : reg => In r [1; 5; 6; 7; 9; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%list) regs r2)
      by (eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2]).
    destruct (rg3_ph3 r2 M2 HI2 ltac:(gag AG12; exact H2) ltac:(gag AG12; exact H14) ltac:(gag AG12; exact H30) ltac:(gag AG12; exact H8)
                ltac:(intros E; gag AG12; exact (HL E))) as (r3 & M3 & S3 & HI3 & AG3).
    exists r3, M3. split; [eapply msteps_trans; [exact S1|]; eapply msteps_trans; [exact S2 | exact S3]|].
    split; [exact HI3|]. split.
    - gag AG3. gag AG12. exact H2.
    - eapply regs_agree_trans; [regs_agree_weaken AG12 | regs_agree_weaken AG3].
  Qed.

End RG3.

Section RopGen3W.
Context {fx : FPState}.

Local Ltac feedp G :=
  lazymatch type of G with
  | forall _ : ?P, _ =>
      lazymatch type of P with
      | Prop => specialize (G ltac:(assumption)); feedp G
      | _ => idtac
      end
  | _ => idtac
  end.

Theorem rg3_loops_W : rg_loops_spec RG3_S1.
Proof.
  intros MB rom s datad nd datas ns dh swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl fw f6 f7 nofull nolast f3 regs
    BLK GEO CELLS REGS.
  destruct BLK as (Hs & Hdd & Hds & SOKd & SOKs & SOKf & FR).
  destruct GEO as (Hgeo & Hdxb & Hnf & RF & RW & RL).
  destruct CELLS as (C_nl & C_nf & C_swpl & C_z & C_dh & C_rows & C_f6 & C_nfw & C_f3 & C_psl & C_mk).
  destruct REGS as (R2 & R1 & R14 & R30 & R8 & RFr & RWr & RLr).
  pose proof (rg3_loops MB rom s datad nd datas ns dh swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl fw f6 f7 nofull nolast f3) as L.
  feedp L.
  specialize (L regs). feedp L.
  destruct L as (regs' & M' & RUN & (HI & HG) & SP & AG).
  exists regs', M'.
  split; [exact RUN|]. split; [split; [intros x Hx _; apply HI, Hx | exact HG]|]. split; [exact SP|].
  regs_agree_weaken AG.
Qed.

End RopGen3W.
