(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac SeqExec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptRop LeptRop2Arith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptUb V23LeptRop2Segs V23LeptRopGSpec.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptRop_iface V23LeptRop2_iface V23LeptCmap2 V23LeptRop V23RopLowG V23LeptRop2Gset.
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

Lemma rgw_bool : forall b : bool, b = true \/ b = false.
Proof. intros []; auto. Qed.
Lemma rgw_if04 : forall b : bool, (0 <= (if b then 0 else 4) <= 4)%Z.
Proof. intros []; lia. Qed.
Lemma rgw_if40 : forall b : bool, (0 <= (if b then 4 else 0) <= 4)%Z.
Proof. intros []; lia. Qed.
Lemma rgw_wrr : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Section RG.
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

  Definition Inv (Mi : word -> option byte) : Prop :=
    (forall x : word, (u x < datad \/ datad + nd <= u x)%Z -> Mi x = MB x) /\ mem_grows MB Mi.

  Lemma Inv_rdn_frame : forall Mi (a : Z) (n : nat) bs, Inv Mi -> (s - 240 <= a)%Z -> (a + Z.of_nat n <= s)%Z ->
    rdn SEGS MB (Z_to_bv 64 a) n = Some bs -> rdn SEGS Mi (Z_to_bv 64 a) n = Some bs.
  Proof.
    intros Mi a n bs [HI _] Ha Hn HM. pose proof FR as FR'. use_apart FR'. rewrite <- HM.
    apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply HI. lia.
  Qed.

  Lemma rg_FR : (datad + nd <= s - 240 \/ s - 240 + 240 <= datad)%Z.
  Proof. exact FR. Qed.

  Lemma rg_Inv_MB : Inv MB.
  Proof. split; [intros; reflexivity | apply mem_grows_refl]. Qed.

  Lemma rg_Inv_store : forall Mi (a : Z) (bs : list byte),
    Inv Mi -> (datad <= a)%Z -> (a + Z.of_nat (length bs) <= datad + nd)%Z -> Inv (wbytes Mi (Z_to_bv 64 a) bs).
  Proof.
    intros Mi a bs [HI HG] Ha Hb. destruct bs as [|b0 bs']; [split; [exact HI | exact HG]|].
    cbn [length] in Hb. split.
    - intros x Hx. rewrite MemSplit.wbytes_outside by (cbn [length]; rewrite u_Z2bv by lia; lia). apply HI, Hx.
    - eapply mem_grows_trans; [exact HG | apply wbytes_grows].
  Qed.

  Lemma rg_Inv_sok : forall Mi (a : Z) (n : nat), Inv Mi -> (datad <= a)%Z -> (a + Z.of_nat n <= datad + nd)%Z ->
    store_ok SEGS Mi (Z_to_bv 64 a) n = true.
  Proof.
    intros Mi a n [_ HG] Ha Hn. eapply store_ok_mono; [exact HG|].
    destruct n as [|n']; [reflexivity|].
    eapply (store_ok_sub SEGS MB (Z_to_bv 64 datad) _ (Z.to_nat nd)); [ | exact SOKd | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma rg_rd4 : forall Mi base RS (a : Z), Inv Mi -> store_ok SEGS MB (Z_to_bv 64 base) (Z.to_nat RS) = true ->
    (0 <= base /\ base + RS <= 2 ^ 64)%Z -> (base <= a)%Z -> (a + 4 <= base + RS)%Z ->
    exists bs, rdn SEGS Mi (Z_to_bv 64 a) 4 = Some bs /\ length bs = 4%nat.
  Proof.
    intros Mi base RS a [_ HG] SOK Hb Ha H4.
    apply (store_ok_rdn SEGS Mi 4 (Z_to_bv 64 a) rgw_wrr).
    eapply store_ok_mono; [exact HG|].
    eapply (store_ok_sub SEGS MB (Z_to_bv 64 base) _ (Z.to_nat RS)); [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; lia.
  Qed.

  Lemma rg_rows_Inv : forall Mi, Inv Mi -> rg_rows MB s dh -> rg_rows Mi s dh.
  Proof.
    intros Mi HI (c28 & c30 & c38 & c40 & c48 & c50 & R28 & R30 & R38 & R40 & R48 & R50 & B).
    unfold rg_rows. exists c28, c30, c38, c40, c48, c50.
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ B)))))).
    all: apply (Inv_rdn_frame Mi _ 8 _ HI); [lia | nlia | assumption].
  Qed.

  Definition FInv (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 15 = Z_to_bv 64 psf /\ getr regs 13 = Z_to_bv 64 (4 * swpl) /\
    getr regs 7 = Z_to_bv 64 (4 * dwpl) /\ getr regs 20 = Z_to_bv 64 (psf + 4 * swpl) /\
    getr regs 19 = Z_to_bv 64 (if f6 then 1 else 0) /\ getr regs 24 = Z_to_bv 64 (if f7 then 1 else 0) /\
    getr regs 22 = Z_to_bv 64 1 /\ getr regs 23 = Z_to_bv 64 0 /\ getr regs 9 = Z_to_bv 64 0 /\ getr regs 1 = Z_to_bv 64 31 /\
    getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

  Definition IInv (i : Z) (regs : bvmap 5 word) : Prop :=
    getr regs 27 = Z_to_bv 64 (psF + 4 * swpl * i) /\ getr regs 6 = Z_to_bv 64 (psF + 4 * swpl * i) /\
    getr regs 1 = Z_to_bv 64 (pdF + 4 * dwpl * i) /\ getr regs 18 = Z_to_bv 64 (pdF + 4 * dwpl * i) /\
    getr regs 20 = Z_to_bv 64 (4 * nfw) /\ getr regs 16 = Z_to_bv 64 1 /\ getr regs 28 = Z_to_bv 64 1 /\
    getr regs 9 = Z_to_bv 64 1 /\ getr regs 21 = Z_to_bv 64 1 /\ getr regs 23 = Z_to_bv 64 32 /\
    getr regs 22 = Z_to_bv 64 18446744073709551611 /\ getr regs 26 = Z_to_bv 64 31 /\
    getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

  Definition WInv (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 5 = Z_to_bv 64 (4 * dwpl) /\ getr regs 7 = Z_to_bv 64 (4 * swpl) /\
    getr regs 20 = Z_to_bv 64 (4 * nfw) /\ getr regs 19 = Z_to_bv 64 0 /\ getr regs 23 = Z_to_bv 64 32 /\
    getr regs 22 = Z_to_bv 64 18446744073709551611 /\ getr regs 17 = Z_to_bv 64 1 /\ getr regs 25 = Z_to_bv 64 1 /\
    getr regs 26 = Z_to_bv 64 31 /\ getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

  Definition LInv (regs : bvmap 5 word) : Prop :=
    getr regs 2 = Z_to_bv 64 (s - 240) /\ getr regs 5 = Z_to_bv 64 (if f3 then 1 else 0) /\ getr regs 17 = Z_to_bv 64 0 /\
    getr regs 14 = Z_to_bv 64 0 /\ getr regs 7 = Z_to_bv 64 18446744073709551611 /\ getr regs 19 = Z_to_bv 64 31 /\
    getr regs 16 = Z_to_bv 64 32 /\ getr regs 28 = Z_to_bv 64 (psl + 4 * swpl) /\ getr regs 15 = Z_to_bv 64 (4 * dwpl) /\
    getr regs 6 = Z_to_bv 64 (4 * swpl) /\ getr regs 30 = Z_to_bv 64 sls /\ getr regs 8 = Z_to_bv 64 (32 - sls).

  Local Ltac inv_agree AG HI :=
    repeat match type of HI with _ /\ _ => let A := fresh "A" in destruct HI as [A HI] end;
    splitc; match goal with |- getr _ ?r = _ => rewrite (AG r ltac:(notin_list)); assumption end.

  Lemma FInv_agree : forall r r', regs_agree (fun x : reg => In x [11; 12; 16; 21; 25; 26; 28]%list) r r' -> FInv r -> FInv r'.
  Proof. intros r r' AG HI. unfold FInv in *. inv_agree AG HI. Qed.
  Lemma IInv_agree : forall i r r', regs_agree (fun x : reg => In x [12; 15; 24]%list) r r' -> IInv i r -> IInv i r'.
  Proof. intros i r r' AG HI. unfold IInv in *. inv_agree AG HI. Qed.
  Lemma WInv_agree : forall r r', regs_agree (fun x : reg => In x [1; 6; 9; 11; 12; 15; 16; 18; 21; 24; 27; 28]%list) r r' -> WInv r -> WInv r'.
  Proof. intros r r' AG HI. unfold WInv in *. inv_agree AG HI. Qed.
  Lemma LInv_agree : forall r r', regs_agree (fun x : reg => In x [9; 10; 11; 18; 20; 21; 22; 23]%list) r r' -> LInv r -> LInv r'.
  Proof. intros r r' AG HI. unfold LInv in *. inv_agree AG HI. Qed.

  Lemma rg_F1 : forall (last : bool) regs Mi i, fw = true -> (0 <= i)%Z -> (if last then i = dh - 1 else i < dh - 1)%Z ->
    Inv Mi -> FInv regs ->
    getr regs 11 = Z_to_bv 64 (4 * swpl * i) -> getr regs 25 = Z_to_bv 64 (pdf + 4 * dwpl * i) ->
    getr regs 16 = Z_to_bv 64 (pdf + 4 * dwpl * i) -> getr regs 28 = Z_to_bv 64 (- (dh - i)) ->
    exists regs' M', msteps SEGS (mkst regs RG_F Mi rom) (mkst regs' (if last then RG_X1 else RG_F) M' rom) /\ Inv M' /\
      FInv regs' /\ getr regs' 11 = Z_to_bv 64 (4 * swpl * (i + 1)) /\ getr regs' 25 = Z_to_bv 64 (pdf + 4 * dwpl * (i + 1)) /\
      getr regs' 16 = Z_to_bv 64 (pdf + 4 * dwpl * (i + 1)) /\ getr regs' 28 = Z_to_bv 64 (- (dh - (i + 1))) /\
      regs_agree (fun r : reg => In r [11; 12; 16; 21; 25; 26; 28]%list) regs regs'.
  Proof.
    intros last regs Mi i Efw Hi Hl HI FI H11 H25 H16 H28.
    assert (Hi' : (i < dh)%Z) by (destruct last; cbv iota in Hl; lia).
    pose proof rg_FR as FRu.
    destruct (RF Efw) as ((ALs & ALd) & RB).
    destruct (RB 0%Z ltac:(lia)) as (B01 & _ & B03 & _). destruct (RB i ltac:(lia)) as (B1 & B2 & B3 & B4).
    pose proof (rgw_if40 (f6 && negb f7)) as IF.
    assert (Mij : (0 <= 4 * swpl * i)%Z /\ (0 <= 4 * dwpl * i)%Z) by (split; apply Z.mul_nonneg_nonneg; lia).
    pose proof FI as (I2 & I15 & I13 & I7 & I20 & I19 & I24 & I22 & I23 & I9 & I1 & I30 & I8).
    destruct (rg_rd4 Mi datas ns (psf + 4 * swpl * i) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs0 & R0 & L0).
    destruct (rg_rd4 Mi datad nd (pdf + 4 * dwpl * i) HI SOKd ltac:(lia) ltac:(lia) ltac:(lia)) as (bd & Rd & Ld).
    pose proof (rg_Inv_sok Mi (pdf + 4 * dwpl * i) 4 HI ltac:(lia) ltac:(nlia)) as SK.
    pose proof (Inv_rdn_frame Mi (s - 120) 8 _ HI ltac:(lia) ltac:(nlia) C_z) as Cz.
    assert (X1 : exists bs1, f6 = true -> f7 = false ->
      (psf + 4 * swpl * i + 8 < 2 ^ 64 /\ rdn SEGS Mi (Z_to_bv 64 (psf + 4 * swpl * i + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z).
    { destruct (f6 && negb f7) eqn:E67.
      - assert (B4' : (psf + 4 * swpl * i + 4 + 4 <= datas + ns)%Z) by (cbv beta iota in B4; lia).
        destruct (rg_rd4 Mi datas ns (psf + 4 * swpl * i + 4) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs1 & R1 & L1).
        exists bs1. intros _ _. split; [lia | split; assumption].
      - exists nil. intros E6 E7. rewrite E6, E7 in E67. cbn in E67. discriminate E67. }
    destruct X1 as (bs1 & X1).
    pose proof (rg_F rom f6 f7 last regs Mi s psf (4 * swpl * i) (pdf + 4 * dwpl * i) (4 * swpl) (4 * dwpl) (dh - i) sls bs0 bs1 bd) as G.
    feed G ltac:(first [eassumption | nlia | (destruct last; cbv iota in Hl |- *; nlia)]).
    destruct G as (r1 & w & S1 & A11 & A25 & A16 & A28 & AG1).
    exists r1. eexists. split; [exact S1|].
    split; [apply rg_Inv_store; [exact HI | lia | rewrite length_N_to_le_bytes; nlia]|].
    split; [exact (FInv_agree regs r1 AG1 FI)|].
    split; [rewrite A11; f_equal; ring|]. split; [rewrite A25; f_equal; ring|].
    split; [rewrite A16; f_equal; ring|]. split; [rewrite A28; f_equal; ring | exact AG1].
  Qed.

  Lemma rg_Fs : forall (k : nat) regs Mi i, fw = true -> (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z -> Inv Mi -> FInv regs ->
    getr regs 11 = Z_to_bv 64 (4 * swpl * i) -> getr regs 25 = Z_to_bv 64 (pdf + 4 * dwpl * i) ->
    getr regs 16 = Z_to_bv 64 (pdf + 4 * dwpl * i) -> getr regs 28 = Z_to_bv 64 (- (dh - i)) ->
    exists regs' M', msteps SEGS (mkst regs RG_F Mi rom) (mkst regs' RG_X1 M' rom) /\ Inv M' /\
      regs_agree (fun r : reg => In r [11; 12; 16; 21; 25; 26; 28]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Efw Hi Hk HI FI H11 H25 H16 H28.
    - destruct (rg_F1 true regs Mi i Efw Hi ltac:(nlia) HI FI H11 H25 H16 H28) as (r1 & M1 & S1 & HI1 & _ & _ & _ & _ & _ & AG1).
      exists r1, M1. split; [exact S1 | split; [exact HI1 | exact AG1]].
    - destruct (rg_F1 false regs Mi i Efw Hi ltac:(nlia) HI FI H11 H25 H16 H28)
        as (r1 & M1 & S1 & HI1 & FI1 & A11 & A25 & A16 & A28 & AG1).
      destruct (IH r1 M1 (i + 1)%Z Efw ltac:(lia) ltac:(lia) HI1 FI1 A11 A25 A16 A28) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]]].
  Qed.

  Lemma rg_I1 : forall (last : bool) regs Mi i j, nofull = false -> (0 <= i < dh)%Z -> (0 <= j)%Z ->
    (if last then j = nfw - 1 else j < nfw - 1)%Z -> Inv Mi -> IInv i regs -> getr regs 24 = Z_to_bv 64 (4 * j) ->
    exists regs' M', msteps SEGS (mkst regs RG_I Mi rom) (mkst regs' (if last then RG_T2 else RG_I) M' rom) /\ Inv M' /\
      IInv i regs' /\ getr regs' 24 = Z_to_bv 64 (4 * (j + 1)) /\ regs_agree (fun r : reg => In r [12; 15; 24]%list) regs regs'.
  Proof.
    intros last regs Mi i j Enf Hi Hj Hl HI II H24.
    assert (Hj' : (j < nfw)%Z) by (destruct last; cbv iota in Hl; lia).
    destruct (RW Enf) as ((ALs & ALd) & RB). destruct (RB i Hi) as (B1 & B2 & B3 & B4).
    assert (Mij : (0 <= 4 * swpl * i)%Z /\ (0 <= 4 * dwpl * i)%Z) by (split; apply Z.mul_nonneg_nonneg; lia).
    pose proof II as (I27 & I6 & I1 & I18 & I20 & I16 & I28 & I9 & I21 & I23 & I22 & I26 & I30 & I8).
    destruct (rg_rd4 Mi datas ns (psF + 4 * swpl * i + 4 * j) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs0 & R0 & L0).
    destruct (rg_rd4 Mi datas ns (psF + 4 * swpl * i + 4 * j + 4) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs1 & R1 & L1).
    pose proof (rg_Inv_sok Mi (pdF + 4 * dwpl * i + 4 * j) 4 HI ltac:(lia) ltac:(nlia)) as SK.
    pose proof (rg_I rom last regs Mi (psF + 4 * swpl * i) (pdF + 4 * dwpl * i) (4 * j) (4 * nfw) sls bs0 bs1) as G.
    feed G ltac:(first [eassumption | nlia | (destruct last; cbv iota in Hl |- *; nlia)]).
    destruct G as (r1 & w & S1 & A24 & AG1).
    exists r1. eexists. split; [exact S1|].
    split; [apply rg_Inv_store; [exact HI | lia | rewrite length_N_to_le_bytes; nlia]|].
    split; [exact (IInv_agree i regs r1 AG1 II)|].
    split; [rewrite A24; f_equal; ring | exact AG1].
  Qed.

  Lemma rg_Is : forall (k : nat) regs Mi i j, nofull = false -> (0 <= i < dh)%Z -> (0 <= j)%Z -> (j + Z.of_nat k = nfw - 1)%Z ->
    Inv Mi -> IInv i regs -> getr regs 24 = Z_to_bv 64 (4 * j) ->
    exists regs' M', msteps SEGS (mkst regs RG_I Mi rom) (mkst regs' RG_T2 M' rom) /\ Inv M' /\
      regs_agree (fun r : reg => In r [12; 15; 24]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i j Enf Hi Hj Hk HI II H24.
    - destruct (rg_I1 true regs Mi i j Enf Hi Hj ltac:(nlia) HI II H24) as (r1 & M1 & S1 & HI1 & _ & _ & AG1).
      exists r1, M1. split; [exact S1 | split; [exact HI1 | exact AG1]].
    - destruct (rg_I1 false regs Mi i j Enf Hi Hj ltac:(nlia) HI II H24) as (r1 & M1 & S1 & HI1 & II1 & A24 & AG1).
      destruct (IH r1 M1 i (j + 1)%Z Enf Hi ltac:(lia) ltac:(lia) HI1 II1 A24) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]]].
  Qed.

  Lemma rg_row1 : forall (last : bool) regs Mi i, nofull = false -> (0 <= i)%Z -> (if last then i = dh - 1 else i < dh - 1)%Z ->
    Inv Mi -> WInv regs -> getr regs 11 = Z_to_bv 64 i ->
    getr regs 6 = Z_to_bv 64 (psF + 4 * swpl * i) -> getr regs 27 = Z_to_bv 64 (psF + 4 * swpl * i) ->
    getr regs 18 = Z_to_bv 64 (pdF + 4 * dwpl * i) -> getr regs 1 = Z_to_bv 64 (pdF + 4 * dwpl * i) ->
    exists regs' M', msteps SEGS (mkst regs RG_H2 Mi rom) (mkst regs' (if last then RG_X2 else RG_H2) M' rom) /\ Inv M' /\
      WInv regs' /\ getr regs' 11 = Z_to_bv 64 (i + 1) /\
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
    pose proof (Inv_rdn_frame Mi (s - 128) 8 _ HI ltac:(lia) ltac:(nlia) (C_nfw Enf)) as Cnfw.
    pose proof (rg_H2 rom regs Mi s nfw (psF + 4 * swpl * i) (pdF + 4 * dwpl * i)) as G.
    feed G ltac:(first [eassumption | nlia]).
    destruct G as (r1 & S1 & A24 & A16 & A28 & A9 & A21 & AG1).
    assert (II : IInv i r1) by (unfold IInv; splitc; first [eassumption | (gag AG1; eassumption)]).
    destruct (rg_Is (Z.to_nat (nfw - 1)) r1 Mi i 0 Enf ltac:(lia) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) HI II
                ltac:(rewrite A24; f_equal; ring)) as (r2 & Ma & S2 & HIa & AG2).
    assert (AG12 : regs_agree (fun r : reg => In r [9; 12; 15; 16; 21; 24; 28]%list) regs r2)
      by (eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2]).
    pose proof (Inv_rdn_frame Ma (s - 120) 8 _ HIa ltac:(lia) ltac:(nlia) C_z) as Cz.
    pose proof (Inv_rdn_frame Ma (s - 112) 8 _ HIa ltac:(lia) ltac:(nlia) C_dh) as Cdh.
    pose proof (rg_T2 rom last r2 Ma s i dh (4 * dwpl) (4 * swpl) (psF + 4 * swpl * i) (pdF + 4 * dwpl * i)) as G.
    feed G ltac:(first [eassumption | nlia | (destruct last; cbv iota in Hl |- *; nlia) | (gag AG12; eassumption)]).
    destruct G as (r3 & S3 & C11 & C6 & C27 & C18 & C1 & AG3).
    assert (AG : regs_agree (fun r : reg => In r [1; 6; 9; 11; 12; 15; 16; 18; 21; 24; 27; 28]%list) regs r3)
      by (eapply regs_agree_trans; [regs_agree_weaken AG12 | regs_agree_weaken AG3]).
    exists r3, Ma. split; [eapply msteps_trans; [exact S1|]; eapply msteps_trans; [exact S2 | exact S3]|].
    split; [exact HIa|]. split; [exact (WInv_agree regs r3 AG WI)|].
    split; [exact C11|].
    split; [rewrite C6; f_equal; ring|]. split; [rewrite C27; f_equal; ring|].
    split; [rewrite C18; f_equal; ring|]. split; [rewrite C1; f_equal; ring | exact AG].
  Qed.

  Lemma rg_Hs : forall (k : nat) regs Mi i, nofull = false -> (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z -> Inv Mi -> WInv regs ->
    getr regs 11 = Z_to_bv 64 i ->
    getr regs 6 = Z_to_bv 64 (psF + 4 * swpl * i) -> getr regs 27 = Z_to_bv 64 (psF + 4 * swpl * i) ->
    getr regs 18 = Z_to_bv 64 (pdF + 4 * dwpl * i) -> getr regs 1 = Z_to_bv 64 (pdF + 4 * dwpl * i) ->
    exists regs' M', msteps SEGS (mkst regs RG_H2 Mi rom) (mkst regs' RG_X2 M' rom) /\ Inv M' /\
      regs_agree (fun r : reg => In r [1; 6; 9; 11; 12; 15; 16; 18; 21; 24; 27; 28]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Enf Hi Hk HI WI H11 H6 H27 H18 H1.
    - destruct (rg_row1 true regs Mi i Enf Hi ltac:(nlia) HI WI H11 H6 H27 H18 H1)
        as (r1 & M1 & S1 & HI1 & _ & _ & _ & _ & _ & _ & AG1).
      exists r1, M1. split; [exact S1 | split; [exact HI1 | exact AG1]].
    - destruct (rg_row1 false regs Mi i Enf Hi ltac:(nlia) HI WI H11 H6 H27 H18 H1)
        as (r1 & M1 & S1 & HI1 & WI1 & A11 & A6 & A27 & A18 & A1 & AG1).
      destruct (IH r1 M1 (i + 1)%Z Enf ltac:(lia) ltac:(lia) HI1 WI1 A11 A6 A27 A18 A1) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]]].
  Qed.

  Lemma rg_L1 : forall (last : bool) regs Mi i, nolast = false -> (0 <= i)%Z -> (if last then i = dh - 1 else i < dh - 1)%Z ->
    Inv Mi -> LInv regs ->
    getr regs 11 = Z_to_bv 64 (4 * swpl * i) -> getr regs 10 = Z_to_bv 64 (pdl + 4 * dwpl * i) ->
    getr regs 20 = Z_to_bv 64 (pdl + 4 * dwpl * i) -> getr regs 9 = Z_to_bv 64 (- (dh - i)) ->
    exists regs' M', msteps SEGS (mkst regs RG_L Mi rom) (mkst regs' (if last then RG_E else RG_L) M' rom) /\ Inv M' /\
      LInv regs' /\ getr regs' 11 = Z_to_bv 64 (4 * swpl * (i + 1)) /\ getr regs' 10 = Z_to_bv 64 (pdl + 4 * dwpl * (i + 1)) /\
      getr regs' 20 = Z_to_bv 64 (pdl + 4 * dwpl * (i + 1)) /\ getr regs' 9 = Z_to_bv 64 (- (dh - (i + 1))) /\
      regs_agree (fun r : reg => In r [9; 10; 11; 18; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    intros last regs Mi i Enl Hi Hl HI LI H11 H10 H20 H9.
    assert (Hi' : (i < dh)%Z) by (destruct last; cbv iota in Hl; lia).
    pose proof rg_FR as FRu.
    destruct (RL Enl) as ((ALs & ALd) & RB).
    destruct (RB 0%Z ltac:(lia)) as (B01 & _ & B03 & _). destruct (RB i ltac:(lia)) as (B1 & B2 & B3 & B4).
    pose proof (rgw_if04 f3) as IF.
    assert (Mij : (0 <= 4 * swpl * i)%Z /\ (0 <= 4 * dwpl * i)%Z) by (split; apply Z.mul_nonneg_nonneg; lia).
    pose proof LI as (I2 & I5 & I17 & I14 & I7 & I19 & I16 & I28 & I15 & I6 & I30 & I8).
    destruct (C_mk Enl) as (mk & Cmk0).
    destruct (rg_rd4 Mi datas ns (psl + 4 * swpl * i) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs0 & R0 & L0).
    destruct (rg_rd4 Mi datad nd (pdl + 4 * dwpl * i) HI SOKd ltac:(lia) ltac:(lia) ltac:(lia)) as (bd & Rd & Ld).
    pose proof (rg_Inv_sok Mi (pdl + 4 * dwpl * i) 4 HI ltac:(lia) ltac:(nlia)) as SK.
    pose proof (Inv_rdn_frame Mi (s - 120) 8 _ HI ltac:(lia) ltac:(nlia) C_z) as Cz.
    pose proof (Inv_rdn_frame Mi (s - 136) 8 _ HI ltac:(lia) ltac:(nlia) (C_psl Enl)) as Cpsl.
    pose proof (Inv_rdn_frame Mi (s - 144) 8 _ HI ltac:(lia) ltac:(nlia) Cmk0) as Cmk.
    assert (X1 : exists bs1, f3 = false ->
      (psl + 4 * swpl * i + 8 < 2 ^ 64 /\ rdn SEGS Mi (Z_to_bv 64 (psl + 4 * swpl * i + 4)) 4 = Some bs1 /\ length bs1 = 4%nat)%Z).
    { destruct (rgw_bool f3) as [E3 | E3].
      - exists nil. intros E. rewrite E3 in E. discriminate E.
      - assert (B4' : (psl + 4 * swpl * i + 4 + 4 <= datas + ns)%Z) by (rewrite E3 in B4; exact B4).
        destruct (rg_rd4 Mi datas ns (psl + 4 * swpl * i + 4) HI SOKs ltac:(lia) ltac:(lia) ltac:(lia)) as (bs1 & R1 & L1).
        exists bs1. intros _. split; [lia | split; assumption]. }
    destruct X1 as (bs1 & X1).
    pose proof (rg_L rom f3 last regs Mi s psl (4 * swpl * i) (pdl + 4 * dwpl * i) (4 * swpl) (4 * dwpl) (dh - i) sls mk bs0 bs1 bd) as G.
    feed G ltac:(first [eassumption | nlia | (destruct last; cbv iota in Hl |- *; nlia)]).
    destruct G as (r1 & w & S1 & A11 & A10 & A20 & A9 & AG1).
    exists r1. eexists. split; [exact S1|].
    split; [apply rg_Inv_store; [exact HI | lia | rewrite length_N_to_le_bytes; nlia]|].
    split; [exact (LInv_agree regs r1 AG1 LI)|].
    split; [rewrite A11; f_equal; ring|]. split; [rewrite A10; f_equal; ring|].
    split; [rewrite A20; f_equal; ring|]. split; [rewrite A9; f_equal; ring | exact AG1].
  Qed.

  Lemma rg_Ls : forall (k : nat) regs Mi i, nolast = false -> (0 <= i)%Z -> (i + Z.of_nat k = dh - 1)%Z -> Inv Mi -> LInv regs ->
    getr regs 11 = Z_to_bv 64 (4 * swpl * i) -> getr regs 10 = Z_to_bv 64 (pdl + 4 * dwpl * i) ->
    getr regs 20 = Z_to_bv 64 (pdl + 4 * dwpl * i) -> getr regs 9 = Z_to_bv 64 (- (dh - i)) ->
    exists regs' M', msteps SEGS (mkst regs RG_L Mi rom) (mkst regs' RG_E M' rom) /\ Inv M' /\
      regs_agree (fun r : reg => In r [9; 10; 11; 18; 20; 21; 22; 23]%list) regs regs'.
  Proof.
    induction k as [|k IH]; intros regs Mi i Enl Hi Hk HI LI H11 H10 H20 H9.
    - destruct (rg_L1 true regs Mi i Enl Hi ltac:(nlia) HI LI H11 H10 H20 H9) as (r1 & M1 & S1 & HI1 & _ & _ & _ & _ & _ & AG1).
      exists r1, M1. split; [exact S1 | split; [exact HI1 | exact AG1]].
    - destruct (rg_L1 false regs Mi i Enl Hi ltac:(nlia) HI LI H11 H10 H20 H9)
        as (r1 & M1 & S1 & HI1 & LI1 & A11 & A10 & A20 & A9 & AG1).
      destruct (IH r1 M1 (i + 1)%Z Enl ltac:(lia) ltac:(lia) HI1 LI1 A11 A10 A20 A9) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2 | eapply regs_agree_trans; [exact AG1 | exact AG2]]].
  Qed.

  Lemma rg_ph1 : forall regs,
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 1 = Z_to_bv 64 dxb -> getr regs 14 = Z_to_bv 64 dwpl ->
    getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
    (fw = true -> getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0)) ->
    exists regs' M', msteps SEGS (mkst regs RG_S1 MB rom) (mkst regs' RG_X1 M' rom) /\ Inv M' /\
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
      pose proof (rgw_if40 (f6 && negb f7)). destruct (HF E) as (X15 & X25 & X26).
      pose proof (C_f6 E). pose proof (C_rows (or_introl E)).
      splitc; first [eassumption | lia]. }
    destruct (rg_S1 rom fw f6 f7 regs MB s dxb psf pdf swpl dwpl dh ltac:(lia) ltac:(lia) (proj1 Hdxb) (proj2 Hdxb)
                ltac:(lia) ltac:(lia) H1 H2 H14 BS) as (r1 & S1 & P1 & AG1).
    destruct (rgw_bool fw) as [Efw | Efw].
    - rewrite Efw in S1.
      destruct (P1 Efw) as (X11 & X20 & X13 & X7 & X16 & X28 & X9 & X19 & X24 & X22 & X23 & X1).
      destruct (HF Efw) as (Y15 & Y25 & Y26).
      assert (FI : FInv r1) by (unfold FInv; splitc; first [eassumption | (gag AG1; eassumption)]).
      destruct (rg_Fs (Z.to_nat (dh - 1)) r1 MB 0 Efw ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) rg_Inv_MB FI
                  ltac:(rewrite X11; f_equal; ring) ltac:(gag AG1; rewrite Y25; f_equal; ring)
                  ltac:(rewrite X16; f_equal; ring) ltac:(rewrite X28; f_equal; ring)) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2|]].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
    - rewrite Efw in S1.
      exists r1, MB. split; [exact S1 | split; [exact rg_Inv_MB | regs_agree_weaken AG1]].
  Qed.

  Lemma rg_ph2 : forall regs Mi, Inv Mi ->
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
    getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
    (nofull = false -> getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF) ->
    exists regs' M', msteps SEGS (mkst regs RG_X1 Mi rom) (mkst regs' RG_X2 M' rom) /\ Inv M' /\
      regs_agree (fun r : reg => In r [1; 5; 6; 7; 9; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%list) regs regs'.
  Proof.
    intros regs Mi HI H2 H14 H30 H8 HW.
    pose proof (Inv_rdn_frame Mi (s - 208) 8 _ HI ltac:(lia) ltac:(nlia) C_nf) as Cnf.
    assert (BX : nofull = false ->
      (0 <= psF < 2 ^ 64)%Z /\ (0 <= pdF < 2 ^ 64)%Z /\ (psF mod 4 = 0)%Z /\ (pdF mod 4 = 0)%Z /\
      getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF /\
      rdn SEGS Mi (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
      rdn SEGS Mi (Z_to_bv 64 (s - 128)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 nfw))).
    { intros E. destruct (RW E) as ((ALs & ALd) & RB). destruct (RB 0%Z ltac:(lia)) as (B1 & B2 & B3 & B4).
      destruct (HW E) as (X6 & X18).
      pose proof (Inv_rdn_frame Mi (s - 152) 8 _ HI ltac:(lia) ltac:(nlia) C_swpl).
      pose proof (Inv_rdn_frame Mi (s - 128) 8 _ HI ltac:(lia) ltac:(nlia) (C_nfw E)).
      splitc; first [eassumption | lia]. }
    destruct (rg_X1 rom nofull regs Mi s psF pdF nfw swpl dwpl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cnf H2 H14 BX)
      as (r1 & S1 & P1 & AG1).
    destruct (rgw_bool nofull) as [Enf | Enf].
    - rewrite Enf in S1. exists r1, Mi. split; [exact S1 | split; [exact HI | regs_agree_weaken AG1]].
    - rewrite Enf in S1.
      destruct (P1 Enf) as (X11 & X5 & X7 & X20 & X19 & X23 & X22 & X17 & X25 & X26 & X27 & X1).
      destruct (HW Enf) as (Y6 & Y18).
      assert (WI : WInv r1) by (unfold WInv; splitc; first [eassumption | (gag AG1; eassumption)]).
      destruct (rg_Hs (Z.to_nat (dh - 1)) r1 Mi 0 Enf ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) HI WI X11
                  ltac:(gag AG1; rewrite Y6; f_equal; ring) ltac:(rewrite X27; f_equal; ring)
                  ltac:(gag AG1; rewrite Y18; f_equal; ring) ltac:(rewrite X1; f_equal; ring)) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2|]].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  Lemma rg_ph3 : forall regs Mi, Inv Mi ->
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 14 = Z_to_bv 64 dwpl ->
    getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
    (nolast = false -> getr regs 10 = Z_to_bv 64 pdl) ->
    exists regs' M', msteps SEGS (mkst regs RG_X2 Mi rom) (mkst regs' RG_E M' rom) /\ Inv M' /\
      regs_agree (fun r : reg => In r [5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 28]%list) regs regs'.
  Proof.
    intros regs Mi HI H2 H14 H30 H8 HL.
    pose proof (Inv_rdn_frame Mi (s - 216) 8 _ HI ltac:(lia) ltac:(nlia) C_nl) as Cnl.
    assert (BX : nolast = false ->
      (0 <= psl < 2 ^ 64)%Z /\ (0 <= pdl < 2 ^ 64)%Z /\ (psl mod 4 = 0)%Z /\ (pdl mod 4 = 0)%Z /\ (1 <= dh < 2 ^ 24)%Z /\
      getr regs 10 = Z_to_bv 64 pdl /\
      rdn SEGS Mi (Z_to_bv 64 (s - 136)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 psl)) /\
      rdn SEGS Mi (Z_to_bv 64 (s - 232)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (if f3 then 1 else 0))) /\
      rdn SEGS Mi (Z_to_bv 64 (s - 152)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 swpl)) /\
      (exists mk : word, rdn SEGS Mi (Z_to_bv 64 (s - 144)) 8 = Some (word_to_le_bytes 8 mk)) /\
      rg_rows Mi s dh).
    { intros E. destruct (RL E) as ((ALs & ALd) & RB). destruct (RB 0%Z ltac:(lia)) as (B1 & B2 & B3 & B4).
      pose proof (rgw_if04 f3). pose proof (HL E).
      destruct (C_mk E) as (mk & Cmk0).
      pose proof (Inv_rdn_frame Mi (s - 136) 8 _ HI ltac:(lia) ltac:(nlia) (C_psl E)).
      pose proof (Inv_rdn_frame Mi (s - 232) 8 _ HI ltac:(lia) ltac:(nlia) (C_f3 E)).
      pose proof (Inv_rdn_frame Mi (s - 152) 8 _ HI ltac:(lia) ltac:(nlia) C_swpl).
      pose proof (Inv_rdn_frame Mi (s - 144) 8 _ HI ltac:(lia) ltac:(nlia) Cmk0).
      pose proof (rg_rows_Inv Mi HI (C_rows (or_intror E))).
      splitc; first [eassumption | lia | (eexists; eassumption)]. }
    destruct (rg_X2 rom nolast f3 regs Mi s psl pdl swpl dwpl dh ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Cnl H2 H14 BX)
      as (r1 & S1 & P1 & AG1).
    destruct (rgw_bool nolast) as [Enl | Enl].
    - rewrite Enl in S1. exists r1, Mi. split; [exact S1 | split; [exact HI | regs_agree_weaken AG1]].
    - rewrite Enl in S1.
      destruct (P1 Enl) as (X11 & X15 & X6 & X17 & X9 & X16 & X5 & X14 & X7 & X28 & X19 & X20).
      pose proof (HL Enl) as Y10.
      assert (LI : LInv r1) by (unfold LInv; splitc; first [eassumption | (gag AG1; eassumption)]).
      destruct (rg_Ls (Z.to_nat (dh - 1)) r1 Mi 0 Enl ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia) HI LI
                  ltac:(rewrite X11; f_equal; ring) ltac:(gag AG1; rewrite Y10; f_equal; ring)
                  ltac:(rewrite X20; f_equal; ring) ltac:(rewrite X9; f_equal; ring)) as (r2 & M2 & S2 & HI2 & AG2).
      exists r2, M2. split; [eapply msteps_trans; [exact S1 | exact S2] | split; [exact HI2|]].
      eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2].
  Qed.

  Theorem rg_loops : forall regs,
    getr regs 2 = Z_to_bv 64 (s - 240) -> getr regs 1 = Z_to_bv 64 dxb -> getr regs 14 = Z_to_bv 64 dwpl ->
    getr regs 30 = Z_to_bv 64 sls -> getr regs 8 = Z_to_bv 64 (32 - sls) ->
    (fw = true -> getr regs 15 = Z_to_bv 64 psf /\ getr regs 25 = Z_to_bv 64 pdf /\ getr regs 26 = Z_to_bv 64 (if f7 then 1 else 0)) ->
    (nofull = false -> getr regs 6 = Z_to_bv 64 psF /\ getr regs 18 = Z_to_bv 64 pdF) ->
    (nolast = false -> getr regs 10 = Z_to_bv 64 pdl) ->
    exists regs' M',
      msteps SEGS (mkst regs RG_S1 MB rom) (mkst regs' RG_E M' rom)
      /\ Inv M' /\ getr regs' 2 = Z_to_bv 64 (s - 240)
      /\ regs_agree (fun r : reg => In r [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%list) regs regs'.
  Proof.
    intros regs H2 H1 H14 H30 H8 HF HW HL.
    destruct (rg_ph1 regs H2 H1 H14 H30 H8 HF) as (r1 & M1 & S1 & HI1 & AG1).
    destruct (rg_ph2 r1 M1 HI1 ltac:(gag AG1; exact H2) ltac:(gag AG1; exact H14) ltac:(gag AG1; exact H30) ltac:(gag AG1; exact H8)
                ltac:(intros E; destruct (HW E) as (X6 & X18); split; gag AG1; assumption)) as (r2 & M2 & S2 & HI2 & AG2).
    assert (AG12 : regs_agree (fun r : reg => In r [1; 5; 6; 7; 9; 11; 12; 13; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28]%list) regs r2)
      by (eapply regs_agree_trans; [regs_agree_weaken AG1 | regs_agree_weaken AG2]).
    destruct (rg_ph3 r2 M2 HI2 ltac:(gag AG12; exact H2) ltac:(gag AG12; exact H14) ltac:(gag AG12; exact H30) ltac:(gag AG12; exact H8)
                ltac:(intros E; gag AG12; exact (HL E))) as (r3 & M3 & S3 & HI3 & AG3).
    exists r3, M3. split; [eapply msteps_trans; [exact S1|]; eapply msteps_trans; [exact S2 | exact S3]|].
    split; [exact HI3|]. split.
    - gag AG3. gag AG12. exact H2.
    - eapply regs_agree_trans; [regs_agree_weaken AG12 | regs_agree_weaken AG3].
  Qed.

End RG.

Lemma rg_loops12_W : forall {fx : FPState}, rg_loops_spec RG_S1.
Proof.
  intros fx MB rom s datad nd datas ns dh swpl dwpl dxb sls nfw psf pdf psF pdF psl pdl fw f6 f7 nofull nolast f3 regs
    BLK GEO CEL RGS.
  destruct BLK as (Hs & Hdd & Hds & SOKd & SOKs & SOKf & FR).
  destruct GEO as (Hgeo & Hdxb & Hnf & RF & RW & RL).
  destruct CEL as (C_nl & C_nf & C_swpl & C_z & C_dh & C_rows & C_f6 & C_nfw & C_f3 & C_psl & C_mk).
  destruct RGS as (R2 & R1 & R14 & R30 & R8 & RFw & RNf & RNl).
  edestruct rg_loops with (MB := MB) (rom := rom) (s := s) (datad := datad) (nd := nd) (datas := datas) (ns := ns)
    (dh := dh) (swpl := swpl) (dwpl := dwpl) (dxb := dxb) (sls := sls) (nfw := nfw) (psf := psf) (pdf := pdf) (psF := psF)
    (pdF := pdF) (psl := psl) (pdl := pdl) (fw := fw) (f6 := f6) (f7 := f7) (nofull := nofull) (nolast := nolast) (f3 := f3)
    (regs := regs) as (regs' & M' & RUN & INV & Q2 & AG).
  all: try (solve [eassumption]).
  exists regs', M'. split; [exact RUN|]. split; [| split; [exact Q2|]].
  - destruct INV as [I1 I2]. split; [intros x H1 _; apply I1; exact H1 | exact I2].
  - regs_agree_weaken AG.
Qed.

Lemma rg_pro_mem : forall {fx : FPState} (m : word -> option byte) (s dh : Z) (ret : word) (regs : bvmap 5 word),
  (240 <= s)%Z -> (s + 64 < 2 ^ 64)%Z ->
  (forall a : word, ~ (s - 112 <= bv_unsigned a < s)%Z ->
     wbytes (RLF m s ret regs) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 dh)) a = m a) /\
  mem_grows m (wbytes (RLF m s ret regs) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 dh))) /\
  rlcells (wbytes (RLF m s ret regs) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 dh))) s ret
    (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
    (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27).
Proof.
  intros fx m s dh ret regs Hs Hs64. split; [| split].
  - intros a Ha. pose proof (u64_range a) as Ua.
    rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; lia).
    apply RLF_outside; lia.
  - eapply mem_grows_trans; [| apply wbytes_grows].
    unfold RLF. repeat (eapply mem_grows_trans; [| apply wbytes_grows]). apply mem_grows_refl.
  - apply (rlcells_frame (RLF m s ret regs)); [lia | lia | apply rlcells_RLF; lia |].
    intros x Hx. rewrite wbytes_outside by (rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; lia). reflexivity.
Qed.

Lemma rg_rowb : forall base wpl y h ph c nw i : Z, (0 <= wpl)%Z -> (0 <= y)%Z -> (y + h <= ph)%Z -> (0 <= c)%Z -> (0 <= nw)%Z ->
  (c + nw <= wpl)%Z -> (0 <= i < h)%Z ->
  (base <= base + 4 * (y * wpl) + 4 * c + 4 * wpl * i /\ base + 4 * (y * wpl) + 4 * c + 4 * wpl * i + 4 * nw <= base + 4 * (wpl * ph))%Z.
Proof.
  intros base wpl y h ph c nw i H0 H1 H2 H3 H4 H5 H6.
  assert (wpl * (y + i + 1) <= wpl * ph)%Z by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (0 <= y * wpl)%Z by (apply Z.mul_nonneg_nonneg; lia). assert (0 <= wpl * i)%Z by (apply Z.mul_nonneg_nonneg; lia).
  assert (E : (wpl * (y + i + 1) = y * wpl + wpl * i + wpl)%Z) by ring.
  split; lia.
Qed.

Lemma rg_dmul : forall x d : Z, (d = 1 \/ d = 8)%Z -> (0 <= x)%Z -> (x <= x * d <= 8 * x)%Z.
Proof. intros x d [-> | ->] Hx; lia. Qed.

Section RopGenW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Theorem rasteropLow_gen_W : rasteropLow_gen_contract.
Proof.
  unfold rasteropLow_gen_contract, rasteropLow_arm_contract.
  intros C Ar A m md regs s datad dpixw dpixh d dwpl dx dy dw dh datas spixw spixh swpl sx sy ret S
    CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15 H16 H17 Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy
    Hdd Hds SHd SHs RCd RCs HARM Ld Ld0 Ld00 Ls HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *.
  assert (Hlo' : (c_top C - LSTK + 240 <= s)%Z) by exact Hlo.
  pose proof SHd as (Hdv & Hdpw & Hdph & Ewd & Hszd). pose proof SHs as (_ & Hspw & Hsph & Ews & Hszs).
  pose proof RCd as (Rdx0 & Rdy0 & Rdw1 & Rdh1 & Rdxw & Rdyh). pose proof RCs as (Rsx0 & Rsy0 & _ & _ & Rsxw & Rsyh).
  assert (DV : dval d) by (unfold dval; lia).
  pose proof (wpl_of_range dpixw d ltac:(lia) DV) as Hwd. rewrite <- Ewd in Hwd.
  pose proof (wpl_of_range spixw d ltac:(lia) DV) as Hws. rewrite <- Ews in Hws.
  pose proof (wpl_bits dpixw d ltac:(lia) ltac:(lia)) as WBd. rewrite <- Ewd in WBd.
  set (nd := (4 * (dwpl * dpixh))%Z) in *. set (ns := (4 * (swpl * spixh))%Z) in *.
  assert (Hnd : (0 < nd)%Z) by (subst nd; assert (1 * 1 <= dwpl * dpixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  assert (Hns : (0 < ns)%Z) by (subst ns; assert (1 * 1 <= swpl * spixh)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 datad) nd CK HW Ld Hnd) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  destruct (blk_range C A m md (Z_to_bv 64 datas) ns CK HW Ls Hns) as [Gs TOPs]. rewrite u_Z2bv in Gs, TOPs by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & AL16d & _). rewrite u_Z2bv in AL16d by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ls) as (_ & AL16s & _). rewrite u_Z2bv in AL16s by lia.
  pose proof (mod16_mod4 _ AL16d) as AL4d. pose proof (mod16_mod4 _ AL16s) as AL4s.
  assert (LVd : forall a : word, (datad <= u a < datad + nd)%Z ->
                exists p n, live A p = Some n /\ live (c_A0 C) p = None /\ (u p <= u a < u p + n)%Z).
  { intros a Ha. exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00 | lia]]. }
  assert (LVr : forall a : word, (datad <= u a < datad + nd)%Z ->
                exists p n, live A p = Some n /\ live Ar p = None /\ (u p <= u a < u p + n)%Z).
  { intros a Ha. exists (Z_to_bv 64 datad), nd. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0 | lia]]. }
  assert (SCR : forall a : word, ~ scratch C s a -> ~ (s - 240 <= u a < s)%Z) by (intros a Ha; unfold scratch in Ha; lia).
  assert (Htop : (s <= c_top C)%Z) by lia.
  assert (Hsb : (112 <= s /\ s < 2 ^ 64 /\ 240 <= s)%Z) by lia.
  assert (FRA : forall x : word, (s - 104 <= u x < s)%Z -> (u x < datad \/ datad + nd <= u x)%Z /\ (u x < s - 240 \/ s - 112 <= u x)%Z)
    by (intros x Hx; split; lia).
  assert (OA : forall a : word, ~ (s - 240 <= u a < s)%Z -> ~ (datad <= u a < datad + nd)%Z ->
            (u a < datad \/ datad + nd <= u a)%Z /\ (u a < s - 240 \/ s - 112 <= u a)%Z /\ ~ (s - 112 <= u a < s)%Z)
    by (intros a X1 X2; split; [lia | split; lia]).
  assert (CA : forall a : word, scratch C s a \/ (datad <= u a < datad + nd)%Z \/ (~ (s - 240 <= u a < s)%Z /\ ~ (datad <= u a < datad + nd)%Z))
    by (intros a; unfold scratch; lia).
  destruct HARM as [AR1 AR2].
  pose proof (rg_dmul dx d Hdv ltac:(lia)) as Mdx. pose proof (rg_dmul sx d Hdv ltac:(lia)) as Msx.
  pose proof (rg_dmul dw d Hdv ltac:(lia)) as Mdw. pose proof (rg_dmul dpixw d Hdv ltac:(lia)) as Mdpw.
  assert (MDW : (dx * d + dw * d <= dpixw * d)%Z) by (rewrite <- Z.mul_add_distr_r; apply Z.mul_le_mono_nonneg_r; lia).
  assert (Edy : (0 <= dy * dwpl <= (dpixh - 1) * dwpl)%Z) by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg_r]; lia).
  assert (Esy : (0 <= sy * swpl <= (spixh - 1) * swpl)%Z) by (split; [apply Z.mul_nonneg_nonneg | apply Z.mul_le_mono_nonneg_r]; lia).
  assert (Hs0 : (250000 <= s /\ s + 64 < 2 ^ 64)%Z) by lia.
  assert (Hdd0 : (4096 <= datad /\ 0 < nd /\ datad + nd + 2 ^ 27 <= 2 ^ 64 /\ datad mod 4 = 0)%Z) by lia.
  assert (Hds0 : (4096 <= datas /\ 0 < ns /\ datas + ns + 2 ^ 27 <= 2 ^ 64 /\ datas mod 4 = 0)%Z) by lia.
  assert (FR : disj_apart datad nd (s - 240) 240) by (unfold disj_apart; lia).
  assert (SOKf : store_ok SEGS m (Z_to_bv 64 (s - 240)) 240 = true)
    by (apply (W_sok_win C A m md); [exact CK | exact HW | lia | cbn; lia]).
  assert (JTm : rdn SEGS m (Z_to_bv 64 RG_JT12) 4 = Some (Z_to_le_bytes 4 RG_JT12V)).
  { rewrite <- p16_segs. rewrite (W_rdn_ro C A m md RG_JT12 4 HW) by (unfold RG_JT12; cbn; lia). rewrite p16_segs. exact jt_gen_rd. }
  assert (EP : Z_to_bv 64 PC_rasteropLow = RGP_ENTRY) by (apply bv_eq; reflexivity). rewrite EP.
  destruct (rg_pro al_rom regs m s datad dpixw dpixh d dwpl dx dy dw dh 12 datas spixw spixh swpl sx sy ltac:(lia) ltac:(lia)
              SHd SHs RCd RCs Rdh Rop Rdatas Rspw Rsph Rswpl Rsx Rsy SOKf H2 H10 H11 H12 H13 H14 H15 H16 H17)
    as (r1 & RUN1 & PR2 & PR1 & PR5 & PR6 & PR7 & PR8 & PR9 & PR10 & PR11 & PR13 & PR14 & PR16 & PR18 & PR19 & PR20 & PR21 & PR23 & PR24 & PR25
        & PR26 & PR27 & PR28 & PR29 & PR30 & PR31 & AG1).
  rewrite H1 in RUN1.
  destruct (rg_pro_mem m s dh ret regs ltac:(lia) ltac:(lia)) as (OUT1 & GR1 & RC1).
  set (PM := wbytes (RLF m s ret regs) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 8 (Z_to_bv 64 dh))) in RUN1, OUT1, GR1, RC1.
  assert (JTp : rdn SEGS PM (Z_to_bv 64 RG_JT12) 4 = Some (Z_to_le_bytes 4 RG_JT12V)).
  { rewrite <- JTm. apply rdn_ext; rewrite u_Z2bv by (unfold RG_JT12; lia); [unfold RG_JT12; lia|].
    intros x Hx. apply OUT1. unfold RG_JT12 in Hx. lia. }
  assert (C112 : rdn SEGS PM (Z_to_bv 64 (s - 112)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 dh))).
  { pose proof (rdn_wbytes_hit SEGS (word_to_le_bytes 8 (Z_to_bv 64 dh)) (RLF m s ret regs) (Z_to_bv 64 (s - 112))) as HH.
    rewrite length_N_to_le_bytes in HH. apply HH. rewrite u_Z2bv by lia. lia. }
  assert (SOKdP : store_ok SEGS PM (Z_to_bv 64 datad) (Z.to_nat nd) = true)
    by (eapply store_ok_mono; [exact GR1 | exact (blk_sok C A m md datad nd CK HW Ld ltac:(lia) ltac:(lia) ltac:(lia))]).
  assert (SOKsP : store_ok SEGS PM (Z_to_bv 64 datas) (Z.to_nat ns) = true)
    by (eapply store_ok_mono; [exact GR1 | exact (blk_sok C A m md datas ns CK HW Ls ltac:(lia) ltac:(lia) ltac:(lia))]).
  assert (SOKfP : store_ok SEGS PM (Z_to_bv 64 (s - 240)) 240 = true) by (eapply store_ok_mono; [exact GR1 | exact SOKf]).
  assert (ROWD : forall c nw i', (0 <= c)%Z -> (0 <= nw)%Z -> (c + nw <= dwpl)%Z -> (0 <= i' < dh)%Z ->
      (datad <= datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' /\ datad + 4 * (dy * dwpl) + 4 * c + 4 * dwpl * i' + 4 * nw <= datad + nd)%Z).
  { intros c nw i' X1 X2 X3 X4. apply (rg_rowb datad dwpl dy dh dpixh c nw i'); lia. }
  assert (ROWS : forall c nw i', (0 <= c)%Z -> (0 <= nw)%Z -> (c + nw <= swpl)%Z -> (0 <= i' < dh)%Z ->
      (datas <= datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' /\ datas + 4 * (sy * swpl) + 4 * c + 4 * swpl * i' + 4 * nw <= datas + ns)%Z).
  { intros c nw i' X1 X2 X3 X4. apply (rg_rowb datas swpl sy dh spixh c nw i'); lia. }
  assert (E0 : RGP_P0 = RG_P0) by (apply bv_eq; reflexivity). rewrite E0 in RUN1.
  destruct (rg_setup al_rom r1 PM s datad nd datas ns (dx * d) (sx * d) (dw * d) dy sy dh dwpl swpl dpixh spixh
              Hs0 Hdd0 Hds0 SOKdP SOKsP FR SOKfP JTp C112
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AR1 AR2 ltac:(lia)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ROWD ROWS
              PR2 PR1 PR5 PR6 PR7 PR8 PR9 PR10 PR11 PR13 PR14 PR16 PR18 PR19 PR23 PR24 PR25 PR26 PR27 PR28)
    as (r2 & M1 & fw & f6 & f7 & nofull & nolast & f3 & dxb & sls & nfw & psf & pdf & psF & pdF & psl & pdl &
        RUN2 & AG2 & OUT2 & GR2 & SOKd1 & SOKs1 & Hgeo & Hdxb & Hnf & C_nl & C_nf & C_swpl & C_z & C_dh & C_rows &
        C_f6 & C_nfw & C_f3 & C_psl & C_mk & RF & RW & RL & R2' & R1' & R14' & R30' & R8' & RFw & RNf & RNl).
  edestruct rg_loops with (MB := M1) (rom := al_rom) (s := s) (datad := datad) (nd := nd) (datas := datas) (ns := ns)
    (dh := dh) (swpl := swpl) (dwpl := dwpl) (dxb := dxb) (sls := sls) (nfw := nfw) (psf := psf) (pdf := pdf) (psF := psF)
    (pdF := pdF) (psl := psl) (pdl := pdl) (fw := fw) (f6 := f6) (f7 := f7) (nofull := nofull) (nolast := nolast) (f3 := f3)
    (regs := r2) as (r3 & M3 & RUN3 & INV3 & Q2 & AG3).
  all: try (solve [eassumption]).
  destruct INV3 as [I3 GR3].
  assert (RC3 : rlcells M3 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
                  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (rlcells_frame PM); [exact (proj1 Hsb) | exact (proj1 (proj2 Hsb)) | exact RC1 |].
    intros x Hx. destruct (FRA x Hx) as [F1 F2]. rewrite I3 by exact F1. apply OUT2. exact F2. }
  assert (EE : RG_E = RGP_E) by (apply bv_eq; reflexivity). rewrite EE in RUN3.
  destruct (rg_E al_rom r3 M3 s ret _ _ _ _ _ _ _ _ _ _ _ _ (proj2 (proj2 Hsb)) (proj1 (proj2 Hsb)) Hret RC3 Q2)
    as (r4 & RUN4 & G2 & G1 & G8 & G9 & G18 & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) |
                     eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | eapply msteps_trans; [exact RUN3 | exact RUN4]]] |].
  assert (OUTM : forall a : word, ~ (s - 240 <= u a < s)%Z -> ~ (datad <= u a < datad + nd)%Z -> M3 a = m a).
  { intros a Ha Hb. destruct (OA a Ha Hb) as (O1 & O2 & O3). rewrite I3 by exact O1. rewrite OUT2 by exact O2. apply OUT1. exact O3. }
  assert (CH : forall a, M3 a <> m a -> scratch C s a \/ (datad <= u a < datad + nd)%Z).
  { intros a NE. destruct (CA a) as [X | [X | [X1 X2]]]; [left; exact X | right; exact X | exfalso; apply NE; apply OUTM; assumption]. }
  assert (K3' : getr r4 3 = getr regs 3)
    by (rewrite (AG4 (3 : reg) ltac:(notin_list)), (AG3 (3 : reg) ltac:(notin_list)), (AG2 (3 : reg) ltac:(notin_list)),
                (AG1 (3 : reg) ltac:(notin_list)); reflexivity).
  assert (K4' : getr r4 4 = getr regs 4)
    by (rewrite (AG4 (4 : reg) ltac:(notin_list)), (AG3 (4 : reg) ltac:(notin_list)), (AG2 (4 : reg) ltac:(notin_list)),
                (AG1 (4 : reg) ltac:(notin_list)); reflexivity).
  apply HK.
  - apply (W_local C A m md M3 s CK HW Htop).
    + intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right; exact (LVd a R)].
    + eapply mem_grows_trans; [exact GR1 | eapply mem_grows_trans; [exact GR2 | exact GR3]].
  - apply cs_kept_intro; try assumption. rewrite G2, H2. reflexivity.
  - apply (POSTM_local C Ar A m md M3 s CK HW SUB). intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right; exact (LVr a R)].
  - intros a Ha Hb. apply OUTM; [exact (SCR a Ha) | exact Hb].
Qed.

End RopGenW.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
