(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmCall LbB_PmXp LbB_PmXv LbB_PmVec.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition set_v1A (c : pmc) (v : Z * Z * Z) : pmc :=
  {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
     c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := v; c_v2 := c_v2 c; c_v3 := c_v3 c; c_tr := c_tr c |}.
Definition set_v2A (c : pmc) (v : Z * list Z * Z) : pmc :=
  {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
     c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := v; c_v3 := c_v3 c; c_tr := c_tr c |}.
Definition set_v3A (c : pmc) (v : Z * list Z * Z) : pmc :=
  {| c_widx := c_widx c; c_icount := c_icount c; c_endian := c_endian c; c_reqconv := c_reqconv c;
     c_m1 := c_m1 c; c_m2 := c_m2 c; c_m3 := c_m3 c; c_v1 := c_v1 c; c_v2 := c_v2 c; c_v3 := v; c_tr := c_tr c |}.

Definition blkV1 (c : pmc) : Z * Z := (t3a (c_v1 c), OPND_SZ * t3c (c_v1 c)).
Definition blkV2 (c : pmc) : Z * Z := (t3a (c_v2 c), 4 * t3c (c_v2 c)).
Definition blkV3 (c : pmc) : Z * Z := (t3a (c_v3 c), 4 * t3c (c_v3 c)).

Lemma nodup_mid : forall {A : Type} (l1 l2 : list A) x, List.NoDup (l1 ++ x :: l2) -> ~ In x l1 /\ ~ In x l2.
Proof.
  intros A l1 l2 x ND. split.
  - intros Hin. exact (nodup_app_disj l1 (x :: l2) x x ND Hin (or_introl eq_refl) eq_refl).
  - intros Hin. apply nodup_app_r in ND. inversion ND as [|u v NI ND']; subst. exact (NI Hin).
Qed.

Lemma rin_ivs_of_in : forall X (iv : Z * Z) a, In iv X -> fst iv <= a < snd iv -> rin_ivs X a.
Proof.
  induction X as [|iv0 X IH]; intros iv a Hin Ha; [destruct Hin|].
  destruct Hin as [<-|Hin]; cbn; [left; exact Ha | right; exact (IH iv a Hin Ha)].
Qed.

Section Keep.
  Context {HCEIL : HeapCeil}.

  Definition vsel (c : pmc) (ho : Z) (xb : Z * Z) : Prop :=
    (ho = O_V1 /\ xb = blkV1 c) \/ (ho = O_V2 /\ xb = blkV2 c) \/ (ho = O_V3 /\ xb = blkV3 c).

  Lemma pmc_keep_but : forall (p : Z) L L' m m' (c : pmc) (ho : Z) (xb : Z * Z),
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L m (p + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L m (p + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L m (p + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ->
    @vec_opnd AC_A ASEGS LY_A MI_A L m (p + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A L m (p + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) ->
    @vec32 AC_A ASEGS LY_A MI_A L m (p + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) ->
    pmc_sh m c ->
    0 <= p -> p + PARSER_SIZE < 2 ^ 47 ->
    List.NoDup (c_blocks c) -> (forall q, In q (c_blocks c) -> 0 < fst q) ->
    vsel c ho xb ->
    (forall a, p + O_M1 <= a < p + PARSER_SIZE -> (a < p + ho \/ p + ho + 24 <= a) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall A n a, In (A, n) (c_blocks c) -> (A, n) <> xb -> A <= a < A + n -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall A n sbs, In (A, n) (c_blocks c) -> (A, n) <> xb -> Z.of_nat (length sbs) <= nsh n -> SHAD m A sbs -> SHAD m' A sbs) ->
    (forall b, In b (c_blocks c) -> b <> xb -> In b L -> In b L') ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L' m' (p + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L' m' (p + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) L' m' (p + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
    /\ umap_sh m' 24 (c_m1 c) /\ umap_sh m' 32 (c_m2 c) /\ umap_sh m' 24 (c_m3 c)
    /\ (ho <> O_V1 -> @vec_opnd AC_A ASEGS LY_A MI_A L' m' (p + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) /\ vsh_opnd m' (c_v1 c))
    /\ (ho <> O_V2 -> @vec32 AC_A ASEGS LY_A MI_A L' m' (p + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) /\ vsh32 m' (c_v2 c))
    /\ (ho <> O_V3 -> @vec32 AC_A ASEGS LY_A MI_A L' m' (p + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) /\ vsh32 m' (c_v3 c)).
  Proof.
    intros p L L' m m' c ho xb U1 U2 U3 V1 V2 V3 SHc Hp0 Hp1 ND BPOS SEL HEQ BEQ SEQ LIVE.

    set (P1 := umap_blocks 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))).
    set (P2 := umap_blocks 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))).
    set (P3 := umap_blocks 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))).
    set (P4 := vec_opnd_blocks (t3a (c_v1 c)) (t3c (c_v1 c))).
    set (P5 := if t3a (c_v2 c) =? 0 then [] else [(t3a (c_v2 c), 4 * t3c (c_v2 c))]).
    set (P6 := if t3a (c_v3 c) =? 0 then [] else [(t3a (c_v3 c), 4 * t3c (c_v3 c))]).
    set (P7 := c_tr c).
    assert (CB : c_blocks c = P1 ++ P2 ++ P3 ++ P4 ++ P5 ++ P6 ++ P7) by reflexivity.
    assert (I1 : forall b, In b P1 -> In b (c_blocks c)) by (intros b Hb; rewrite CB, !in_app_iff; tauto).
    assert (I2 : forall b, In b P2 -> In b (c_blocks c)) by (intros b Hb; rewrite CB, !in_app_iff; tauto).
    assert (I3 : forall b, In b P3 -> In b (c_blocks c)) by (intros b Hb; rewrite CB, !in_app_iff; tauto).
    assert (I4 : forall b, In b P4 -> In b (c_blocks c)) by (intros b Hb; rewrite CB, !in_app_iff; tauto).
    assert (I5 : forall b, In b P5 -> In b (c_blocks c)) by (intros b Hb; rewrite CB, !in_app_iff; tauto).
    assert (I6 : forall b, In b P6 -> In b (c_blocks c)) by (intros b Hb; rewrite CB, !in_app_iff; tauto).

    assert (XP4 : ho = O_V1 -> fst xb <> 0 -> P4 = [xb]).
    { intros E NZ. destruct SEL as [(E' & ->)|[(E' & ->)|(E' & ->)]]; [| exfalso; unfold O_V1, O_V2 in *; lia | exfalso; unfold O_V1, O_V3 in *; lia].
      subst P4. unfold vec_opnd_blocks, blkV1 in *. cbn [fst] in NZ. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [contradiction | reflexivity]. }
    assert (XP5 : ho = O_V2 -> fst xb <> 0 -> P5 = [xb]).
    { intros E NZ. destruct SEL as [(E' & ->)|[(E' & ->)|(E' & ->)]]; [exfalso; unfold O_V1, O_V2 in *; lia | | exfalso; unfold O_V2, O_V3 in *; lia].
      subst P5. unfold blkV2 in *. cbn [fst] in NZ. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [contradiction | reflexivity]. }
    assert (XP6 : ho = O_V3 -> fst xb <> 0 -> P6 = [xb]).
    { intros E NZ. destruct SEL as [(E' & ->)|[(E' & ->)|(E' & ->)]]; [exfalso; unfold O_V1, O_V3 in *; lia | exfalso; unfold O_V2, O_V3 in *; lia |].
      subst P6. unfold blkV3 in *. cbn [fst] in NZ. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [contradiction | reflexivity]. }
    assert (HO : ho = O_V1 \/ ho = O_V2 \/ ho = O_V3) by (destruct SEL as [(E & _)|[(E & _)|(E & _)]]; [left | right; left | right; right]; exact E).

    assert (NX : forall q, In q (c_blocks c) ->
              (ho = O_V1 -> ~ In q P4) -> (ho = O_V2 -> ~ In q P5) -> (ho = O_V3 -> ~ In q P6) -> q <> xb).
    { intros q Hq N4 N5 N6 E. subst q.
      destruct (Z.eq_dec (fst xb) 0) as [Z0|NZ]; [pose proof (BPOS xb Hq); lia|].
      destruct HO as [E|[E|E]].
      - pose proof (XP4 E NZ) as EP. apply (N4 E). rewrite EP. left. reflexivity.
      - pose proof (XP5 E NZ) as EP. apply (N5 E). rewrite EP. left. reflexivity.
      - pose proof (XP6 E NZ) as EP. apply (N6 E). rewrite EP. left. reflexivity. }

    assert (ND4 : ho = O_V1 -> fst xb <> 0 -> forall q, In q (P1 ++ P2 ++ P3) \/ In q (P5 ++ P6 ++ P7) -> ~ In q P4).
    { intros E NZ q Hq Hin. rewrite (XP4 E NZ) in Hin, CB. destruct Hin as [<-|[]].
      assert (E' : c_blocks c = (P1 ++ P2 ++ P3) ++ xb :: (P5 ++ P6 ++ P7)) by (rewrite CB, <- !app_assoc; reflexivity).
      pose proof ND as ND'. rewrite E' in ND'.
      destruct (nodup_mid _ _ _ ND') as [X1 X2]. destruct Hq as [Hq|Hq]; [exact (X1 Hq) | exact (X2 Hq)]. }
    assert (ND5 : ho = O_V2 -> fst xb <> 0 -> forall q, In q (P1 ++ P2 ++ P3 ++ P4) \/ In q (P6 ++ P7) -> ~ In q P5).
    { intros E NZ q Hq Hin. rewrite (XP5 E NZ) in Hin, CB. destruct Hin as [<-|[]].
      assert (E' : c_blocks c = (P1 ++ P2 ++ P3 ++ P4) ++ xb :: (P6 ++ P7)) by (rewrite CB, <- !app_assoc; reflexivity).
      pose proof ND as ND'. rewrite E' in ND'.
      destruct (nodup_mid _ _ _ ND') as [X1 X2]. destruct Hq as [Hq|Hq]; [exact (X1 Hq) | exact (X2 Hq)]. }
    assert (ND6 : ho = O_V3 -> fst xb <> 0 -> forall q, In q (P1 ++ P2 ++ P3 ++ P4 ++ P5) \/ In q P7 -> ~ In q P6).
    { intros E NZ q Hq Hin. rewrite (XP6 E NZ) in Hin, CB. destruct Hin as [<-|[]].
      assert (E' : c_blocks c = (P1 ++ P2 ++ P3 ++ P4 ++ P5) ++ xb :: P7) by (rewrite CB, <- !app_assoc; reflexivity).
      pose proof ND as ND'. rewrite E' in ND'.
      destruct (nodup_mid _ _ _ ND') as [X1 X2]. destruct Hq as [Hq|Hq]; [exact (X1 Hq) | exact (X2 Hq)]. }

    assert (EM4 : ho = O_V1 -> fst xb = 0 -> forall q, ~ In q P4).
    { intros E Z0 q Hin. destruct SEL as [(E' & ->)|[(E' & ->)|(E' & ->)]]; [| exfalso; unfold O_V1, O_V2 in *; lia | exfalso; unfold O_V1, O_V3 in *; lia].
      subst P4. unfold vec_opnd_blocks, blkV1 in *. cbn [fst] in Z0. rewrite Z0, Z.eqb_refl in Hin. destruct Hin. }
    assert (EM5 : ho = O_V2 -> fst xb = 0 -> forall q, ~ In q P5).
    { intros E Z0 q Hin. destruct SEL as [(E' & ->)|[(E' & ->)|(E' & ->)]]; [exfalso; unfold O_V1, O_V2 in *; lia | | exfalso; unfold O_V2, O_V3 in *; lia].
      subst P5. unfold blkV2 in *. cbn [fst] in Z0. rewrite Z0, Z.eqb_refl in Hin. destruct Hin. }
    assert (EM6 : ho = O_V3 -> fst xb = 0 -> forall q, ~ In q P6).
    { intros E Z0 q Hin. destruct SEL as [(E' & ->)|[(E' & ->)|(E' & ->)]]; [exfalso; unfold O_V1, O_V3 in *; lia | exfalso; unfold O_V2, O_V3 in *; lia |].
      subst P6. unfold blkV3 in *. cbn [fst] in Z0. rewrite Z0, Z.eqb_refl in Hin. destruct Hin. }
    assert (NI4 : forall q, In q (P1 ++ P2 ++ P3) \/ In q (P5 ++ P6 ++ P7) -> ho = O_V1 -> ~ In q P4).
    { intros q Hq E. destruct (Z.eq_dec (fst xb) 0) as [Z0|NZ]; [exact (EM4 E Z0 q) | exact (ND4 E NZ q Hq)]. }
    assert (NI5 : forall q, In q (P1 ++ P2 ++ P3 ++ P4) \/ In q (P6 ++ P7) -> ho = O_V2 -> ~ In q P5).
    { intros q Hq E. destruct (Z.eq_dec (fst xb) 0) as [Z0|NZ]; [exact (EM5 E Z0 q) | exact (ND5 E NZ q Hq)]. }
    assert (NI6 : forall q, In q (P1 ++ P2 ++ P3 ++ P4 ++ P5) \/ In q P7 -> ho = O_V3 -> ~ In q P6).
    { intros q Hq E. destruct (Z.eq_dec (fst xb) 0) as [Z0|NZ]; [exact (EM6 E Z0 q) | exact (ND6 E NZ q Hq)]. }
    assert (NX1 : forall q, In q P1 -> q <> xb).
    { intros q Hq. apply (NX q (I1 q Hq)); [apply NI4 | apply NI5 | apply NI6]; left; apply in_or_app; left; exact Hq. }
    assert (NX2 : forall q, In q P2 -> q <> xb).
    { intros q Hq. apply (NX q (I2 q Hq)); [apply NI4 | apply NI5 | apply NI6]; left; apply in_or_app; right; apply in_or_app; left; exact Hq. }
    assert (NX3 : forall q, In q P3 -> q <> xb).
    { intros q Hq. apply (NX q (I3 q Hq)); [apply NI4 | apply NI5 | apply NI6]; left; do 2 (apply in_or_app; right);
        [exact Hq | apply in_or_app; left; exact Hq | apply in_or_app; left; exact Hq]. }
    assert (NX4 : ho <> O_V1 -> forall q, In q P4 -> q <> xb).
    { intros NE q Hq. apply (NX q (I4 q Hq)); [intros E; contradiction | apply NI5 | apply NI6]; left; do 3 (apply in_or_app; right);
        [exact Hq | apply in_or_app; left; exact Hq]. }
    assert (NX5 : ho <> O_V2 -> forall q, In q P5 -> q <> xb).
    { intros NE q Hq. apply (NX q (I5 q Hq)); [apply NI4 | intros E; contradiction | apply NI6].
      - right. apply in_or_app; left; exact Hq.
      - left. do 4 (apply in_or_app; right). exact Hq. }
    assert (NX6 : ho <> O_V3 -> forall q, In q P6 -> q <> xb).
    { intros NE q Hq. apply (NX q (I6 q Hq)); [apply NI4 | apply NI5 | intros E; contradiction].
      - right. apply in_or_app; right; apply in_or_app; left; exact Hq.
      - right. apply in_or_app; left; exact Hq. }
    assert (HH24 : forall off, O_M1 <= off -> off + 40 <= O_V1 -> forall a, p + off <= a < p + off + 40 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros off H1 H2 a Ha. apply HEQ; [unfold O_V1, PARSER_SIZE in *; lia|]. left. destruct HO as [E|[E|E]]; rewrite E; unfold O_V1, O_V2, O_V3 in *; lia. }

    assert (UK : forall NS (V : Type) (nval : mem -> Z -> V -> Prop)
      (nval_agree : forall M M' p v, nval M p v -> HRepFacts.agree_on M M' (p + 20) (NS - 20) -> 0 < p -> p + NS <= 2 ^ 47 -> nval M' p v)
      (HNS : 24 <= NS) off bl bc ents,
      O_M1 <= off -> off + 40 <= O_V1 ->
      (forall b, In b (umap_blocks NS bl bc ents) -> In b (c_blocks c) /\ b <> xb) ->
      @umapx AC_A ASEGS LY_A MI_A NS V nval L m (p + off) bl bc ents ->
      @umapx AC_A ASEGS LY_A MI_A NS V nval L' m' (p + off) bl bc ents).
    { intros NS V nval nval_agree HNS off bl bc ents Ho1 Ho2 IB U.
      eapply (umapx_agree ASEGS LY_A MI_A NS V nval nval_agree HNS); [exact U | |].
      - intros a Ha. unfold umap_foot in Ha. destruct Ha as [Ha|[(Hbc & Ha)|(q & Hq & Ha)]].
        + apply (HH24 off Ho1 Ho2). lia.
        + assert (Hin : In (bl, 8 * bc) (umap_blocks NS bl bc ents)).
          { unfold umap_blocks. apply in_app_iff. left. destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]. }
          destruct (IB _ Hin) as [Hc Hx]. exact (BEQ bl (8 * bc) a Hc Hx Ha).
        + assert (Hin : In (q, NS) (umap_blocks NS bl bc ents)).
          { unfold umap_blocks. apply in_app_iff. right.
            apply in_map_iff in Hq. destruct Hq as ([q' kv] & Eq & Hin). cbn in Eq. subst q'.
            apply in_map_iff. exists (q, kv). split; [reflexivity | exact Hin]. }
          destruct (IB _ Hin) as [Hc Hx]. exact (BEQ q NS a Hc Hx Ha).
      - intros b n0 Hb Hl. apply LIVE; [exact (proj1 (IB _ Hb)) | exact (proj2 (IB _ Hb)) | exact Hl]. }
    assert (IB1 : forall b, In b P1 -> In b (c_blocks c) /\ b <> xb) by (intros b Hb; split; [exact (I1 b Hb) | exact (NX1 b Hb)]).
    assert (IB2 : forall b, In b P2 -> In b (c_blocks c) /\ b <> xb) by (intros b Hb; split; [exact (I2 b Hb) | exact (NX2 b Hb)]).
    assert (IB3 : forall b, In b P3 -> In b (c_blocks c) /\ b <> xb) by (intros b Hb; split; [exact (I3 b Hb) | exact (NX3 b Hb)]).
    pose proof SHc as (SH1 & SH2 & SH3 & SH4 & SH5 & SH6).
    split; [apply (UK 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia) O_M1); [unfold O_M1; lia | unfold O_M1, O_V1; lia | exact IB1 | exact U1]|].
    split; [apply (UK 32 (Z * Z * Z)%type (nval32 ASEGS) (nval32_agree ASEGS) ltac:(lia) O_M2); [unfold O_M1, O_M2; lia | unfold O_M2, O_V1; lia | exact IB2 | exact U2]|].
    split; [apply (UK 24 Z (nval24 ASEGS) (nval24_agree ASEGS) ltac:(lia) O_M3); [unfold O_M1, O_M3; lia | unfold O_M3, O_V1; lia | exact IB3 | exact U3]|].

    assert (USH : forall NS (V : Type) (t : Z * Z * list (Z * (Z * V))),
      (forall b, In b (umap_blocks NS (t3a t) (t3b t) (t3c t)) -> In b (c_blocks c) /\ b <> xb) ->
      umap_sh m NS t -> umap_sh m' NS t).
    { intros NS V [[bl bc] ents] IB [SB SN]. unfold umap_sh. cbn [t3a t3b t3c fst snd] in *. split.
      - intros Hbc. pose proof (SB Hbc) as AD. destruct AD as [Hn SH]. split; [exact Hn|].
        assert (Hin : In (bl, 8 * bc) (umap_blocks NS bl bc ents)).
        { unfold umap_blocks. apply in_app_iff. left. destruct (Z.eqb_spec bc 0); [lia | left; reflexivity]. }
        destruct (IB _ Hin) as [Hc Hx]. eapply (SEQ bl (8 * bc)); [exact Hc | exact Hx | rewrite shadow_of_length by lia; lia | exact SH].
      - intros q k v Hin. destruct (SN q k v Hin) as [Hn SH]. split; [exact Hn|].
        assert (Hin' : In (q, NS) (umap_blocks NS bl bc ents)).
        { unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (q, (k, v)). split; [reflexivity | exact Hin]. }
        destruct (IB _ Hin') as [Hc Hx]. eapply (SEQ q NS); [exact Hc | exact Hx | rewrite shadow_of_length by lia; lia | exact SH]. }
    split; [exact (USH 24 Z (c_m1 c) IB1 SH1)|].
    split; [exact (USH 32 (Z * Z * Z)%type (c_m2 c) IB2 SH2)|].
    split; [exact (USH 24 Z (c_m3 c) IB3 SH3)|].

    split; [| split].
    - intros NE.
      assert (IBv : t3a (c_v1 c) <> 0 -> In (blkV1 c) (c_blocks c) /\ blkV1 c <> xb).
      { intros Hb. assert (Hin : In (blkV1 c) P4) by (subst P4; unfold vec_opnd_blocks, blkV1; destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [lia | left; reflexivity]).
        split; [exact (I4 _ Hin) | exact (NX4 NE _ Hin)]. }
      split.
      + eapply vec_opnd_live; [eapply vec_opnd_frame; [exact V1|] |].
        * intros a Ha. unfold vec_opnd_fp, zwin in Ha. apply HEQ; [unfold O_V1, O_M1, PARSER_SIZE in *; lia|].
          destruct HO as [E|[E|E]]; [contradiction | rewrite E | rewrite E]; unfold O_V1, O_V2, O_V3 in *; lia.
        * intros Hb Hl. destruct (IBv ltac:(lia)) as [Hc Hx]. apply LIVE; [exact Hc | exact Hx | exact Hl].
      + intros Hb. pose proof V1 as (_ & _ & _ & Hlen & _). destruct (IBv Hb) as [Hc Hx].
        eapply (SEQ (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c))); [exact Hc | exact Hx | | exact (SH4 Hb)].
        rewrite cc_gen_length by (unfold OPND_SZ; lia). lia.
    - intros NE.
      assert (IBv : t3a (c_v2 c) <> 0 -> In (blkV2 c) (c_blocks c) /\ blkV2 c <> xb).
      { intros Hb. assert (Hin : In (blkV2 c) P5) by (subst P5; unfold blkV2; destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [lia | left; reflexivity]).
        split; [exact (I5 _ Hin) | exact (NX5 NE _ Hin)]. }
      split.
      + eapply vec32_live; [eapply vec32_frame; [exact V2|] |].
        * intros a Ha. unfold vec32_fp, zwin in Ha. destruct Ha as [Ha|(Hb & Ha)].
          -- apply HEQ; [unfold O_V2, O_M1, PARSER_SIZE in *; lia|].
             destruct HO as [E|[E|E]]; [rewrite E | contradiction | rewrite E]; unfold O_V1, O_V2, O_V3 in *; lia.
          -- pose proof V2 as (_ & _ & _ & Hlen & _). destruct (IBv Hb) as [Hc Hx].
             apply (BEQ (t3a (c_v2 c)) (4 * t3c (c_v2 c)) a Hc Hx). unfold Zlen in *. lia.
        * intros Hb Hl. destruct (IBv ltac:(lia)) as [Hc Hx]. apply LIVE; [exact Hc | exact Hx | exact Hl].
      + intros Hb. pose proof V2 as (_ & _ & _ & Hlen & _). destruct (IBv Hb) as [Hc Hx].
        eapply (SEQ (t3a (c_v2 c)) (4 * t3c (c_v2 c))); [exact Hc | exact Hx | | exact (SH5 Hb)].
        rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
    - intros NE.
      assert (IBv : t3a (c_v3 c) <> 0 -> In (blkV3 c) (c_blocks c) /\ blkV3 c <> xb).
      { intros Hb. assert (Hin : In (blkV3 c) P6) by (subst P6; unfold blkV3; destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [lia | left; reflexivity]).
        split; [exact (I6 _ Hin) | exact (NX6 NE _ Hin)]. }
      split.
      + eapply vec32_live; [eapply vec32_frame; [exact V3|] |].
        * intros a Ha. unfold vec32_fp, zwin in Ha. destruct Ha as [Ha|(Hb & Ha)].
          -- apply HEQ; [unfold O_V3, O_M1, PARSER_SIZE in *; lia|].
             destruct HO as [E|[E|E]]; [rewrite E | rewrite E | contradiction]; unfold O_V1, O_V2, O_V3 in *; lia.
          -- pose proof V3 as (_ & _ & _ & Hlen & _). destruct (IBv Hb) as [Hc Hx].
             apply (BEQ (t3a (c_v3 c)) (4 * t3c (c_v3 c)) a Hc Hx). unfold Zlen in *. lia.
        * intros Hb Hl. destruct (IBv ltac:(lia)) as [Hc Hx]. apply LIVE; [exact Hc | exact Hx | exact Hl].
      + intros Hb. pose proof V3 as (_ & _ & _ & Hlen & _). destruct (IBv Hb) as [Hc Hx].
        eapply (SEQ (t3a (c_v3 c)) (4 * t3c (c_v3 c))); [exact Hc | exact Hx | | exact (SH6 Hb)].
        rewrite cc_gen_length by (unfold Zlen in *; lia). lia.
  Qed.
End Keep.

Section Vup.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.

  Definition vwin (w : pmwA H) (ho : Z) (xb : Z * Z) (iv : Z * Z) : Prop :=
    fst iv <= snd iv /\
    ((wa_p w + ho <= fst iv /\ snd iv <= wa_p w + ho + 24)
     \/ (fst xb <> 0 /\ fst xb <= fst iv /\ snd iv <= fst xb + snd xb)
     \/ (fst xb <> 0 /\ sh (fst xb) <= fst iv /\ snd iv <= sh (fst xb) + nsh (snd xb))).

  Definition swin (w : pmwA H) (iv : Z * Z) : Prop := wa_lo w <= fst iv /\ fst iv <= snd iv /\ snd iv <= wa_s1 w.

  Definition sown (w : pmwA H) (iv : Z * Z) : Prop := wa_lo w <= fst iv /\ fst iv <= snd iv /\ snd iv <= wa_sp0 w - 104.
  Lemma sown_own : forall w iv, pmw_okA H w -> sown w iv -> own_ivl H w iv.
  Proof. intros w iv OK (S1 & S2 & S3). left. lia. Qed.
  Lemma swin_sown : forall w iv, pmw_okA H w -> swin w iv -> sown w iv.
  Proof.
    intros w iv OK (S1 & S2 & S3). pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). unfold sown. lia.
  Qed.

  Definition rfw (w : pmwA H) (iv : Z * Z) : Prop := fst iv <= snd iv /\ wa_s1 w <= fst iv /\ snd iv <= wa_s1 w + PM_RF_TOP.
  Definition vwinT (w : pmwA H) (ho : Z) (xb : Z * Z) (iv : Z * Z) : Prop := vwin w ho xb iv \/ rfw w iv.

  Lemma rfw_sown : forall w iv, pmw_okA H w -> rfw w iv -> sown w iv.
  Proof.
    intros w iv OK (R1 & R2 & R3). pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13). unfold sown, PM_RF_TOP in *. lia.
  Qed.

  Lemma stk_keep : forall m m' lo hi, stk asegs m lo hi -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    stk asegs m' lo hi.
  Proof.
    intros m m' lo hi (S1 & S2 & S3) WM DM. split; [exact S1|]. split; [exact S2|]. intros a Ha.
    destruct (S3 a Ha) as [W (b & Hb)]. split; [exact (WM _ W)|].
    unfold mrd in *. destruct (m (wa a)) as [b0|] eqn:E0.
    - pose proof (DM (wa a) ltac:(rewrite E0; discriminate)) as D. destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity | contradiction].
    - destruct (m' (wa a)) as [b1|]; [exists b1; reflexivity | exists b; exact Hb].
  Qed.

  Lemma xb_facts : forall (w : pmwA H) s LB LBs TB m c (xb : Z * Z), pmw_okA H w -> as_RHEAP H s LB m ->
    Permutation LB (wa_LB0 w ++ LBs ++ TB) -> Permutation (lbl LBs) (c_blocks c) -> In xb (c_blocks c) ->
    exists pid, In (pid, fst xb, snd xb) LBs /\ In (pid, fst xb, snd xb) LB /\ In xb (lbl LB) /\ ablock_range H (fst xb) (snd xb).
  Proof.
    intros w s LB LBs TB m c [A n] OK RH P1 P2 Hin. cbn [fst snd].
    apply (Permutation_in _ (Permutation_sym P2)) in Hin. destruct (lbl_in_inv LBs _ _ Hin) as (pid & Hp).
    exists pid. destruct (lbs_blk H HH w s LB LBs TB m (pid, A, n) RH P1 Hp) as (HL & RB).
    split; [exact Hp|]. split; [exact HL|]. split; [exact (lbl_in LB pid A n HL) | exact RB].
  Qed.

  Lemma blk_apart_p : forall (w : pmwA H) s LB m A n, pmw_okA H w -> as_RHEAP H s LB m -> In (A, n) (lbl LB) ->
    A + n + 16 <= wa_p w \/ wa_p w + PARSER_SIZE + 16 <= A.
  Proof.
    intros w s LB m A n OK RH Hin. destruct (lbl_in_inv LB A n Hin) as [pid Hb].
    pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
    destruct (p_frame H HH w OK) as (f & Hf & F1 & F2 & F3 & F4). unfold AFS_HDR in *. lia.
  Qed.

  Lemma vsw_client : forall w s LB m ho xb iv, pmw_okA H w -> as_RHEAP H s LB m -> (fst xb <> 0 -> In xb (lbl LB)) ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> sown w iv \/ vwin w ho xb iv -> aclient_write_ok H LB iv.
  Proof.
    intros w s LB m ho xb iv OK RH XB HO1 HO2 Hiv. unfold O_V1 in HO1.
    destruct Hiv as [Hiv|(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])].
    - exact (own_aclient H HH w LB iv OK (sown_own w iv OK Hiv)).
    - right; right; right; right; left. destruct (p_frame H HH w OK) as (f & Hf & P1 & P2 & P3 & P4). unfold PARSER_SIZE, AFS_HDR in *. lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      right; right; left. exists (pid, fst xb, snd xb). split; [exact Hb|]. cbn. lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      right; right; right; left. exists (pid, fst xb, snd xb). split; [exact Hb|]. cbn. lia.
  Qed.

  Lemma vsw_afs : forall w s LB m ho xb iv, pmw_okA H w -> as_RHEAP H s LB m -> (fst xb <> 0 -> In xb (lbl LB)) ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> sown w iv \/ vwin w ho xb iv -> afs_write_ok H (PMLF H w) iv.
  Proof.
    intros w s LB m ho xb iv OK RH XB HO1 HO2 Hiv. unfold O_V1 in HO1.
    pose proof (pmw_frame_facts H w OK) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct Hiv as [Hiv|(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])].
    - exact (own_afs H w iv OK (sown_own w iv OK Hiv) ltac:(destruct Hiv as (_ & X & _); exact X)).
    - right. destruct (wk_pin H w OK) as (f & Hf & P1 & P2). exists f. split; [right; exact Hf|]. unfold PARSER_SIZE in *. lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      left. unfold ATLS_PRIV_LO, ATLS_PRIV_HI, ATP, AIMG_TOP in *. split; [destruct RF; [left | right]; lia | right; lia].
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof (aapp_bounds _ _ RAPP Rn) as (B1 & B2 & B3 & B4 & B5).
      left. split.
      + pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE (fst xb) (snd xb) F8 ltac:(lia) ltac:(lia) Rn) as D. destruct D; [left | right]; lia.
      + right. assert (sh AIMG_TOP <= sh (fst xb)) by (apply sh_mono; lia).
        replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. unfold ATLS_PRIV_HI, ATP. lia.
  Qed.

  Lemma vsw_stack0 : forall w s LB m ho xb iv, pmw_okA H w -> as_RHEAP H s LB m -> (fst xb <> 0 -> In xb (lbl LB)) ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> sown w iv \/ vwin w ho xb iv -> stack0_ok iv.
  Proof.
    intros w s LB m ho xb iv OK RH XB HO1 HO2 Hiv. unfold O_V1 in HO1.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct Hiv as [Hiv|(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])].
    - exact (own_stack0_ok H w iv OK (sown_own w iv OK Hiv)).
    - destruct iv as [lo hi]. cbn [fst snd] in *. pose proof (wk_papp H w OK) as (PA & _ & _).
      eapply stack0_ok_aapp; [exact PA | lia | unfold PARSER_SIZE in *; lia].
    - destruct iv as [lo hi]. cbn [fst snd] in *.
      destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      eapply stack0_ok_aapp; [exact RAPP | lia | lia].
    - destruct iv as [lo hi]. cbn [fst snd] in *.
      destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof (stack0_ok_sh (fst xb) (snd xb) ltac:(lia) Rn RC) as SS. unfold stack0_ok in *. cbn [fst snd] in *. lia.
  Qed.

  Lemma vsw_aconst : forall w s LB m ho xb iv, pmw_okA H w -> as_RHEAP H s LB m -> (fst xb <> 0 -> In xb (lbl LB)) ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> sown w iv \/ vwin w ho xb iv -> aconst_ok iv.
  Proof.
    intros w s LB m ho xb iv OK RH XB HO1 HO2 Hiv. unfold O_V1 in HO1.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    destruct Hiv as [Hiv|(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])].
    - exact (own_aconst_ok H w iv OK (sown_own w iv OK Hiv)).
    - destruct iv as [lo hi]. cbn [fst snd] in *. pose proof (wk_papp H w OK) as (PA & _ & _).
      eapply aconst_ok_app; [exact PA | lia | unfold PARSER_SIZE in *; lia].
    - destruct iv as [lo hi]. cbn [fst snd] in *.
      destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      eapply aconst_ok_app; [exact RAPP | lia | lia].
    - destruct iv as [lo hi]. cbn [fst snd] in *.
      destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      assert (sh AIMG_TOP <= sh (fst xb)) by (apply sh_mono; lia).
      apply aconst_ok_high; [lia|]. replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. lia.
  Qed.

  Lemma vsw_img : forall w s LB m ho xb iv, pmw_okA H w -> as_RHEAP H s LB m -> (fst xb <> 0 -> In xb (lbl LB)) ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> sown w iv \/ vwin w ho xb iv -> AIMG_TOP <= fst iv.
  Proof.
    intros w s LB m ho xb iv OK RH XB HO1 HO2 Hiv. unfold O_V1 in HO1.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). pose proof (wk_stack H w OK) as (S1 & _).
    pose proof (p_range H w OK) as [PR1 PR2].
    destruct Hiv as [(J1 & J2 & J3)|(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])].
    - unfold AIMG_TOP in *. lia.
    - lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *. lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      assert (sh AIMG_TOP <= sh (fst xb)) by (apply sh_mono; lia).
      replace (sh AIMG_TOP) with 0x800d5000 in * by reflexivity. unfold AIMG_TOP. lia.
  Qed.

  Lemma vsw_apart_p : forall w s LB m ho xb iv a n, pmw_okA H w -> as_RHEAP H s LB m -> (fst xb <> 0 -> In xb (lbl LB)) ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> sown w iv \/ vwin w ho xb iv ->
    wa_p w <= a -> a + n <= wa_p w + PARSER_SIZE -> 0 <= n -> (a + n <= wa_p w + ho \/ wa_p w + ho + 24 <= a) ->
    a + n <= fst iv \/ snd iv <= a.
  Proof.
    intros w s LB m ho xb iv a n OK RH XB HO1 HO2 Hiv A1 A2 Hn AH. unfold O_V1 in HO1.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (p_range H w OK) as [PR1 PR2]. pose proof (wk_papp H w OK) as (PA & PA0 & PA16).
    destruct Hiv as [(J1 & J2 & J3)|(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])].
    - left. lia.
    - lia.
    - pose proof (blk_apart_p w s LB m (fst xb) (snd xb) OK RH ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as D.
      destruct D; [right | left]; lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof (aapp_bounds _ _ RAPP Rn) as (B1 & B2 & B3 & B4 & B5).
      pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE (fst xb) (snd xb) PA ltac:(lia) ltac:(lia) Rn) as D.
      destruct D; [right | left]; lia.
  Qed.

  Lemma vsw_apart_blk : forall w s LB m ho xb iv A k a n, pmw_okA H w -> as_RHEAP H s LB m -> (fst xb <> 0 -> In xb (lbl LB)) ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> sown w iv \/ vwin w ho xb iv ->
    In (A, k) (lbl LB) -> (A, k) <> xb -> A <= a -> a + n <= A + k -> 0 <= n ->
    a + n <= fst iv \/ snd iv <= a.
  Proof.
    intros w s LB m ho xb iv A k a n OK RH XB HO1 HO2 Hiv Hin Hne A1 A2 Hn. unfold O_V1 in HO1.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct (lbl_in_inv LB A k Hin) as [qid Hq].
    pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP). cbn [blk_addr blk_size fst snd] in *.
    destruct Hiv as [(J1 & J2 & J3)|(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])].
    - left. lia.
    - pose proof (blk_apart_p w s LB m A k OK RH Hin) as D. destruct D; [left | right]; lia.
    - pose proof (lbl_pairs_disj H HH s LB m (A, k) xb RH Hin (XB NZ) Hne) as D.
      cbn [fst snd] in D. destruct D; [left | right]; lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof (aapp_bounds _ _ RAPP Rn) as (B1 & B2 & B3 & B4 & B5).
      pose proof (aapp_disjoint_sh A k (fst xb) (snd xb) QAPP ltac:(lia) ltac:(lia) Rn) as D.
      destruct D; [right | left]; lia.
  Qed.

  Lemma vsw_apart_blksh : forall w s LB m ho xb iv A k a n, pmw_okA H w -> as_RHEAP H s LB m -> (fst xb <> 0 -> In xb (lbl LB)) ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> sown w iv \/ vwin w ho xb iv ->
    In (A, k) (lbl LB) -> (A, k) <> xb -> sh A <= a -> a + n <= sh A + nsh k -> 0 <= n ->
    a + n <= fst iv \/ snd iv <= a.
  Proof.
    intros w s LB m ho xb iv A k a n OK RH XB HO1 HO2 Hiv Hin Hne A1 A2 Hn. unfold O_V1 in HO1.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4). pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    destruct (lbl_in_inv LB A k Hin) as [qid Hq].
    pose proof (ah_blocks H HH _ _ _ _ RH Hq) as (Q0 & Q16 & Qn & QI & QC & QF & QAPP). cbn [blk_addr blk_size fst snd] in *.
    pose proof (aapp_bounds _ _ QAPP Qn) as (C1 & C2 & C3 & C4 & C5).
    assert (SH2 : sh A + nsh k <= sh aceil) by (unfold sh, nsh; pose proof aceil_al8; Z.div_mod_to_equations; lia).
    assert (SHA : sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
    destruct Hiv as [(J1 & J2 & J3)|(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])].
    - left. lia.
    - pose proof (wk_papp H w OK) as (PA & PA0 & PA16). pose proof (p_range H w OK) as [PR1 PR2].
      pose proof (aapp_disjoint_sh (wa_p w) PARSER_SIZE A k PA ltac:(lia) ltac:(lia) Qn) as D.
      destruct D; [left | right]; lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof (aapp_disjoint_sh (fst xb) (snd xb) A k RAPP ltac:(lia) ltac:(lia) Qn) as D.
      destruct D; [left | right]; lia.
    - destruct (lbl_in_inv LB (fst xb) (snd xb) ltac:(rewrite <- surjective_pairing; exact (XB NZ))) as [pid Hb].
      pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (R0 & R16 & Rn & RI & RC & RF & RAPP). cbn [blk_addr blk_size fst snd] in *.
      pose proof (lbl_pairs_disj H HH s LB m (A, k) xb RH Hin (XB NZ) Hne) as D. cbn [fst snd] in D.
      pose proof (sh_apart A k (fst xb) (snd xb) ltac:(lia) Qn ltac:(lia) Rn ltac:(Z.div_mod_to_equations; lia) ltac:(Z.div_mod_to_equations; lia) ltac:(lia)) as D2.
      destruct D2; [left | right]; lia.
  Qed.

  Lemma Forall_disjoint : forall (W : list (Z * Z)) a n,
    Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
  Proof.
    induction W as [|[lo hi] W IH]; intros a n F; cbn; [exact I|].
    split; [exact (Forall_inv F) | exact (IH a n (Forall_inv_tail F))].
  Qed.

  Lemma slots_munch : forall (w : pmwA H) m m' tbl W, pmw_okA H w -> slots_ok w m bvmap_empty tbl ->
    keys_ok (map fst tbl) = true -> keys_nonneg (map fst tbl) = true -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => snd iv <= wa_s1 w \/ wa_s1 w + PM_RF_TOP <= fst iv) W ->
    slots_ok w m' bvmap_empty tbl.
  Proof.
    intros w m m' tbl W OK SL Hk Hknn MU WM FW.
    unfold slots_ok in *. apply Forall_forall. intros [k e] Hin.
    pose proof (proj1 (Forall_forall _ _) SL (k, e) Hin) as C. cbn [fst snd] in *.
    pose proof (proj1 (forallb_forall _ _) Hknn k (in_map fst _ (k, e) Hin)) as Kk. apply Z.leb_le in Kk.
    pose proof (proj1 (forallb_forall _ _) Hk k (in_map fst _ (k, e) Hin)) as Kt. apply andb_true_iff in Kt as [_ Kt].
    apply Z.leb_le in Kt.
    eapply rw_cells_transport; [exact C | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
    apply Forall_disjoint. eapply Forall_impl; [| exact FW]. intros iv Hiv. cbn beta in *. lia.
  Qed.

  Lemma pmxa_vupd_genT : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' mo' c' WV WS (ho : Z) (xb : Z * Z) tbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    munch (WV ++ WS) m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    as_MPRES H mo mo' -> mem_inv asegs m' -> slots_ok w m' bvmap_empty tbl' ->
    Forall (vwinT w ho xb) WV -> Forall (swin w) WS ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE ->
    (fst xb <> 0 -> In xb (c_blocks c)) -> (fst xb <> 0 -> wr_at asegs m' (sh (fst xb)) (nsh (snd xb))) ->
    c_blocks c' = c_blocks c ->
    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m' (wa_p w + O_M1) (t3a (c_m1 c')) (t3b (c_m1 c')) (t3c (c_m1 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m' (wa_p w + O_M2) (t3a (c_m2 c')) (t3b (c_m2 c')) (t3c (c_m2 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m' (wa_p w + O_M3) (t3a (c_m3 c')) (t3b (c_m3 c')) (t3c (c_m3 c')) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V1) (t3a (c_v1 c')) (t3b (c_v1 c')) (t3c (c_v1 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V2) (t3a (c_v2 c')) (t3b (c_v2 c')) (t3c (c_v2 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V3) (t3a (c_v3 c')) (t3b (c_v3 c')) (t3c (c_v3 c')) ->
    pmc_sh m' c' ->
    PMXAT H LINV w s LB LBs m' mo' c' ins tbl' ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' mo' c' WV WS ho xb tbl' OK X0 Hknn Hfk MU WM DM MP' MI' SL' FV FS HO1 HO2
           XBc XBw CBe Cw Ci Ce Cr U1 U2 U3 V1 V2 V3 SHc.
    pose proof HO1 as HO1n. unfold O_V1 in HO1n.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    assert (XBf : fst xb <> 0 -> exists pid, In (pid, fst xb, snd xb) LBs /\ In (pid, fst xb, snd xb) LB /\ In xb (lbl LB)
                                             /\ ablock_range H (fst xb) (snd xb)).
    { intros NZ. destruct (xb_facts w s LB LBs TB m c xb OK RH OWN1 OWN2 (XBc NZ)) as (pid & A1 & A2 & A3 & A4).
      exists pid. split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact A4]. }
    assert (XB : fst xb <> 0 -> In xb (lbl LB)) by (intros NZ; destruct (XBf NZ) as (pid & _ & _ & A3 & _); exact A3).
    assert (FW : Forall (fun iv => sown w iv \/ vwin w ho xb iv) (WV ++ WS)).
    { apply Forall_app. split; [eapply Forall_impl; [| exact FV]; intros iv [Hiv|Hiv]; [right; exact Hiv | left; exact (rfw_sown w iv OK Hiv)]
                              | eapply Forall_impl; [| exact FS]; intros iv Hiv; left; exact (swin_sown w iv OK Hiv)]. }
    assert (FCW : Forall (aclient_write_ok H LB) (WV ++ WS)).
    { eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (vsw_client w s LB m ho xb iv OK RH XB HO1 HO2 Hiv). }
    pose proof (xa_xpres _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as XPR0.
    assert (STK2 : stk asegs m' (wa_lo w) (wa_sp0 w)) by exact (stk_keep m m' _ _ (xa_stk _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) WM DM).
    eapply (pmxa_xv H HH LINV w s LB LBs m mo c ins tbl ftbl TB spal s LB LBs m' mo' c' TB spal LB WV [] tbl');
      [exact OK | exact X0 | | exact MP' | exact MI' | exact STK2 | | | | | | | apply Forall_nil | | | | | exact Hfk | exact SL'
      | intros b Hb; exact Hb | intros b Hb; apply (Permutation_in _ (Permutation_sym OWN1)); apply in_app_iff; left; exact Hb
      | exact OWN1 | rewrite CBe; exact OWN2 | exact (lb_own_wmono _ _ _ (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) WM)
      | exact (xa_meas _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
      | exact (lb_own_wmono _ _ _ (proj1 (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)) WM) | exact (proj2 (xa_tb _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0))
      | | | | exact Cw | exact Ci | exact Ce | exact Cr | exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact V3 | exact SHc].
    -   eapply (ah_RHEAP_frame H HH); [exact RH | exact MU | exact WM | exact FCW].
    -   destruct (xa_errno _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [errv Herr]. exists errv.
      eapply rw_cells_transport; [exact Herr | exact MU | exact WM |]. apply Forall_disjoint.
      eapply Forall_impl; [| exact FW]. intros iv Hiv. cbn [cells_size csize Nat.add].
      pose proof (vsw_img w s LB m ho xb iv OK RH XB HO1 HO2 Hiv) as I0.
      left. rewrite (wk_tp H w OK). rewrite unsigned_lit by (unfold ATP; lia). eapply Z.le_trans; [| exact I0]. vm_compute. discriminate.
    -   eapply (ah_rauxv_frame H HH); [exact (xa_rauxv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | exact WM | exact FCW].
    -   eapply (ah_RFS_frame H HH); [exact (xa_rfs _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | exact WM |].
      eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (vsw_afs w s LB m ho xb iv OK RH XB HO1 HO2 Hiv).
    -   eapply ACONST_frame; [exact (xa_aconst _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | exact WM |].
      eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (vsw_aconst w s LB m ho xb iv OK RH XB HO1 HO2 Hiv).
    -   eapply stack0_transport; [exact (xa_stack0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | exact WM |].
      eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (vsw_stack0 w s LB m ho xb iv OK RH XB HO1 HO2 Hiv).
    -   eapply LINV_frame; [exact (xa_linv _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) | exact MU | exact WM |].
      eapply Forall_impl; [| exact FW]. intros iv Hiv. exact (vsw_img w s LB m ho xb iv OK RH XB HO1 HO2 Hiv).
    -   rewrite app_nil_r.
      eapply (xpres_of_munch H s LB); [exact HH | exact RH | exact MU | exact WM |].
      apply Forall_app. split.
      + apply Forall_forall. intros iv Hiv. right. intros a Ha. exact (rin_ivs_of_in WV iv a Hiv Ha).
      + eapply Forall_impl; [| exact FS]. intros iv (J1 & J2 & J3). left. lia.
    -   eapply Forall_impl; [| exact FV]. intros iv [(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])|(R1 & R2 & R3)].
      + right; left. unfold PARSER_SIZE, O_M1 in *. lia.
      + right; right; left. split; [exact LE|]. destruct (XBf NZ) as (pid & A1 & _). exists (pid, fst xb, snd xb). split; [exact A1 | cbn; lia].
      + right; right; right; left. split; [exact LE|]. destruct (XBf NZ) as (pid & A1 & _). exists (pid, fst xb, snd xb). split; [exact A1 | cbn; lia].
      + right; right; right; right. split; [exact R1 | split; [exact R2 | exact R3]].
    -   eapply Forall_impl; [| exact FV]. intros iv [(LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]])|(R1 & R2 & R3)]; right.
      + assert (WP : wr_at asegs m' (wa_p w) PARSER_SIZE).
        { pose proof (pmw_bounds H w OK) as BND. split; [lia|]. split; [unfold PARSER_SIZE in *; lia|]. intros i Hi. unfold wview.
          pose proof (DM _ (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0 i Hi)) as D.
          unfold wa. destruct (m' (Z_to_bv 64 (wa_p w + i))); [discriminate | contradiction]. }
        eapply wr_at_sub; [exact WP | lia | unfold PARSER_SIZE in *; lia | lia].
      + destruct (XBf NZ) as (pid & A1 & _). pose proof (lb_own_In _ _ _ (xa_lbown _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) A1) as WB. cbn [blk_addr blk_size fst snd] in WB.
        eapply wr_at_sub; [exact (wr_at_wmono _ _ _ _ WB WM) | lia | lia | lia].
      + eapply wr_at_sub; [exact (XBw NZ) | lia | lia | lia].
      + destruct STK2 as (T1 & T2 & T3). split; [lia|]. split; [unfold PM_RF_TOP in *; lia|]. intros i Hi.
        exact (proj1 (T3 (fst iv + i) ltac:(unfold PM_RF_TOP in *; lia))).
    -   intros i Hi. apply DM. replace (wa_p w + O_M1 + i) with (wa_p w + (O_M1 + i)) by lia.
      apply (xa_pdef _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0 (O_M1 + i)). unfold O_M1, PARSER_SIZE in *. lia.
    - rewrite (pm_phi_eq c'). unfold pm_prog. rewrite CBe, Cw. exact (proj1 (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)).
    - rewrite (pm_cap_eq c'). rewrite CBe. exact (proj1 (proj2 (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0))).
    - exact (proj2 (proj2 (proj2 (xa_al _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)))).
  Qed.

  Lemma pmxa_vupd_gen : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' mo' c' WV WS (ho : Z) (xb : Z * Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    munch (WV ++ WS) m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    Forall (vwin w ho xb) WV -> Forall (swin w) WS ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE ->
    (fst xb <> 0 -> In xb (c_blocks c)) -> (fst xb <> 0 -> wr_at asegs m' (sh (fst xb)) (nsh (snd xb))) ->
    c_blocks c' = c_blocks c ->
    c_widx c' = c_widx c -> c_icount c' = c_icount c -> c_endian c' = c_endian c -> c_reqconv c' = c_reqconv c ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m' (wa_p w + O_M1) (t3a (c_m1 c')) (t3b (c_m1 c')) (t3c (c_m1 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m' (wa_p w + O_M2) (t3a (c_m2 c')) (t3b (c_m2 c')) (t3c (c_m2 c')) ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m' (wa_p w + O_M3) (t3a (c_m3 c')) (t3b (c_m3 c')) (t3c (c_m3 c')) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V1) (t3a (c_v1 c')) (t3b (c_v1 c')) (t3c (c_v1 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V2) (t3a (c_v2 c')) (t3b (c_v2 c')) (t3c (c_v2 c')) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V3) (t3a (c_v3 c')) (t3b (c_v3 c')) (t3c (c_v3 c')) ->
    pmc_sh m' c' ->
    PMXAT H LINV w s LB LBs m' mo' c' ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' mo' c' WV WS ho xb OK X0 Hknn Hfk MU WM DM MP' MI' STK' FV FS HO1 HO2
           XBc XBw CBe Cw Ci Ce Cr U1 U2 U3 V1 V2 V3 SHc.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13).
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    assert (XBf : fst xb <> 0 -> exists pid, In (pid, fst xb, snd xb) LBs /\ In (pid, fst xb, snd xb) LB /\ In xb (lbl LB)
                                             /\ ablock_range H (fst xb) (snd xb)).
    { intros NZ. destruct (xb_facts w s LB LBs TB m c xb OK RH OWN1 OWN2 (XBc NZ)) as (pid & A1 & A2 & A3 & A4).
      exists pid. split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact A4]. }
    assert (SL2 : slots_ok w m' bvmap_empty tbl).
    { pose proof (xa_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as SL. unfold slots_ok in *. apply Forall_forall. intros [k e] Hin.
      pose proof (proj1 (Forall_forall _ _) SL (k, e) Hin) as C. cbn [fst snd] in *.
      pose proof (proj1 (forallb_forall _ _) Hknn k (in_map fst _ (k, e) Hin)) as Kk. apply Z.leb_le in Kk.
      eapply rw_cells_transport; [exact C | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
      apply Forall_disjoint. apply Forall_app. split.
      - eapply Forall_impl; [| exact FV]. intros iv (LE & [(I1 & I2)|[(NZ & I1 & I2)|(NZ & I1 & I2)]]).
        + right. pose proof (p_range H w OK) as [_ PR2]. unfold PARSER_SIZE in *. lia.
        + right. destruct (XBf NZ) as (pid & _ & _ & _ & (R0 & R16 & Rn & RI & RC & _)). lia.
        + right. destruct (XBf NZ) as (pid & _ & _ & _ & (R0 & R16 & Rn & RI & RC & _)).
          assert (sh aceil <= aceil) by (unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia).
          assert (sh (fst xb) + nsh (snd xb) <= sh aceil) by (unfold sh, nsh; pose proof aceil_al8; Z.div_mod_to_equations; lia). lia.
      - eapply Forall_impl; [| exact FS]. intros iv (J1 & J2 & J3). right. lia. }
    eapply (pmxa_vupd_genT w s LB LBs m mo c ins tbl ftbl TB spal m' mo' c' WV WS ho xb tbl);
      [exact OK | exact X0 | exact Hknn | exact Hfk | exact MU | exact WM | exact DM | exact MP' | exact MI' | exact SL2
      | eapply Forall_impl; [| exact FV]; intros iv Hiv; left; exact Hiv | exact FS | exact HO1 | exact HO2
      | exact XBc | exact XBw | exact CBe | exact Cw | exact Ci | exact Ce | exact Cr | exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact V3 | exact SHc].
  Qed.

  Lemma pmxa_keep_but : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' W (ho : Z) (xb : Z * Z),
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    munch W m m' -> wmono asegs m m' -> Forall (fun iv => sown w iv \/ vwin w ho xb iv) W ->
    O_V1 <= ho -> ho + 24 <= PARSER_SIZE -> vsel c ho xb ->
    @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m' (wa_p w + O_M1) (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) (lbl LB) m' (wa_p w + O_M2) (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c))
    /\ @umapx AC_A ASEGS LY_A MI_A 24 Z (nval24 ASEGS) (lbl LB) m' (wa_p w + O_M3) (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c))
    /\ umap_sh m' 24 (c_m1 c) /\ umap_sh m' 32 (c_m2 c) /\ umap_sh m' 24 (c_m3 c)
    /\ (ho <> O_V1 -> @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V1) (t3a (c_v1 c)) (t3b (c_v1 c)) (t3c (c_v1 c)) /\ vsh_opnd m' (c_v1 c))
    /\ (ho <> O_V2 -> @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V2) (t3a (c_v2 c)) (t3b (c_v2 c)) (t3c (c_v2 c)) /\ vsh32 m' (c_v2 c))
    /\ (ho <> O_V3 -> @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V3) (t3a (c_v3 c)) (t3b (c_v3 c)) (t3c (c_v3 c)) /\ vsh32 m' (c_v3 c)).
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' W ho xb OK X0 MU WM FW HO1 HO2 SEL.
    pose proof (pmw_bounds H w OK) as BND.
    pose proof (xa_rheap _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as RH.
    pose proof (xa_own _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) as [OWN1 OWN2].
    assert (BLK : forall q, In q (c_blocks c) -> In q (lbl LB) /\ 0 < fst q /\ fst q + snd q <= aceil).
    { intros [A n] Hin. destruct (xb_facts w s LB LBs TB m c (A, n) OK RH OWN1 OWN2 Hin) as (pid & _ & _ & A3 & (R0 & _ & _ & _ & RC & _)).
      split; [exact A3 | split; [exact R0 | exact RC]]. }
    assert (XBc : fst xb <> 0 -> In xb (c_blocks c)).
    { intros NZ. unfold c_blocks. rewrite !in_app_iff.
      destruct SEL as [(E & ->)|[(E & ->)|(E & ->)]]; unfold blkV1, blkV2, blkV3 in *; cbn [fst] in NZ.
      - right; right; right; left. unfold vec_opnd_blocks. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [contradiction | left; reflexivity].
      - right; right; right; right; left. destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [contradiction | left; reflexivity].
      - right; right; right; right; right; left. destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [contradiction | left; reflexivity]. }
    assert (XB : fst xb <> 0 -> In xb (lbl LB)) by (intros NZ; exact (proj1 (BLK xb (XBc NZ)))).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    apply (pmc_keep_but (wa_p w) (lbl LB) (lbl LB) m m' c ho xb
             (xa_m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
             (xa_v1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0) (xa_v3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)
             (proj1 (xa_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ X0)));
      [lia | pose proof (p_range H w OK) as [_ PR2]; unfold PARSER_SIZE in *; lia
      | exact (cblocks_nodup H HH s LB (wa_LB0 w) LBs TB m c RH OWN1 OWN2) | intros q Hq; exact (proj1 (proj2 (BLK q Hq))) | exact SEL | | | | intros b _ _ Hb; exact Hb].
    - intros a Ha AH. apply MU. rewrite unsigned_lit by (unfold O_M1, PARSER_SIZE in Ha; lia). eapply disjoint_outside; [| split; [apply Z.le_refl | apply Z.lt_add_pos_r, Z.lt_0_1]].
      apply Forall_disjoint. eapply Forall_impl; [| exact FW]. intros iv Hiv.
      apply (vsw_apart_p w s LB m ho xb iv a 1 OK RH XB HO1 HO2 Hiv); unfold O_M1, PARSER_SIZE in *; lia.
    - intros A n a Hin Hne Ha. apply MU. rewrite unsigned_lit by (pose proof (proj2 (BLK _ Hin)) as [B0 B1]; cbn [fst snd] in B0, B1; lia).
      destruct (BLK _ Hin) as [HinL _].
      eapply disjoint_outside; [| split; [apply Z.le_refl | apply Z.lt_add_pos_r, Z.lt_0_1]].
      apply Forall_disjoint. eapply Forall_impl; [| exact FW]. intros iv Hiv.
      apply (vsw_apart_blk w s LB m ho xb iv A n a 1 OK RH XB HO1 HO2 Hiv HinL Hne); lia.
    - intros A n sbs Hin Hne Hlen SH. destruct (BLK _ Hin) as [HinL _].
      eapply SHAD_transport; [exact SH | exact MU | exact WM |].
      apply Forall_disjoint. eapply Forall_impl; [| exact FW]. intros iv Hiv.
      apply (vsw_apart_blksh w s LB m ho xb iv A n (sh A) _ OK RH XB HO1 HO2 Hiv HinL Hne); lia.
  Qed.

  Lemma pmxa_vupd2 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' mo' WV WS xs',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    munch (WV ++ WS) m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    Forall (vwin w O_V2 (blkV2 c)) WV -> Forall (swin w) WS ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V2) (t3a (c_v2 c)) xs' (t3c (c_v2 c)) ->
    vsh32 m' (t3a (c_v2 c), xs', t3c (c_v2 c)) ->
    PMXAT H LINV w s LB LBs m' mo' (set_v2A c (t3a (c_v2 c), xs', t3c (c_v2 c))) ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' mo' WV WS xs' OK X0 Hknn Hfk MU WM DM MP' MI' STK' FV FS V2' SH'.
    assert (FW : Forall (fun iv => sown w iv \/ vwin w O_V2 (blkV2 c) iv) (WV ++ WS)).
    { apply Forall_app. split; [eapply Forall_impl; [| exact FV]; intros iv Hiv; right; exact Hiv
                              | eapply Forall_impl; [| exact FS]; intros iv Hiv; left; exact (swin_sown w iv OK Hiv)]. }
    destruct (pmxa_keep_but w s LB LBs m mo c ins tbl ftbl TB spal m' (WV ++ WS) O_V2 (blkV2 c) OK X0 MU WM FW
                ltac:(unfold O_V1, O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia) ltac:(right; left; split; reflexivity))
      as (U1 & U2 & U3 & S1 & S2 & S3 & K1 & _ & K3).
    destruct (K1 ltac:(unfold O_V1, O_V2; lia)) as [V1 S4]. destruct (K3 ltac:(unfold O_V2, O_V3; lia)) as [V3 S6].
    eapply (pmxa_vupd_gen w s LB LBs m mo c ins tbl ftbl TB spal m' mo' _ WV WS O_V2 (blkV2 c));
      [exact OK | exact X0 | exact Hknn | exact Hfk | exact MU | exact WM | exact DM | exact MP' | exact MI' | exact STK' | exact FV | exact FS
      | unfold O_V1, O_V2; lia | unfold O_V2, PARSER_SIZE; lia | | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact U1 | exact U2 | exact U3 | exact V1 | exact V2' | exact V3 |].
    - intros NZ. unfold c_blocks, blkV2 in *. cbn [fst] in NZ. rewrite !in_app_iff. right; right; right; right; left.
      destruct (Z.eqb_spec (t3a (c_v2 c)) 0); [contradiction | left; reflexivity].
    - intros NZ. unfold blkV2. cbn [fst snd] in *. pose proof (SH' NZ) as SH. cbn [t3a t3b t3c fst snd] in SH.
      destruct SH as (_ & _ & [_ WR]). pose proof V2' as (_ & _ & _ & Hlen & _).
      rewrite RtB_Iface.cc_gen_length in WR by (unfold Zlen in *; lia). exact WR.
    - cbn [set_v2A c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 pmc_sh]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
      split; [exact S4|]. split; [exact SH' | exact S6].
  Qed.

  Lemma pmxa_vupd1 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' mo' WV WS n',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    munch (WV ++ WS) m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    Forall (vwin w O_V1 (blkV1 c)) WV -> Forall (swin w) WS ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V1) (t3a (c_v1 c)) n' (t3c (c_v1 c)) ->
    vsh_opnd m' (t3a (c_v1 c), n', t3c (c_v1 c)) ->
    PMXAT H LINV w s LB LBs m' mo' (set_v1A c (t3a (c_v1 c), n', t3c (c_v1 c))) ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' mo' WV WS n' OK X0 Hknn Hfk MU WM DM MP' MI' STK' FV FS V1' SH'.
    assert (FW : Forall (fun iv => sown w iv \/ vwin w O_V1 (blkV1 c) iv) (WV ++ WS)).
    { apply Forall_app. split; [eapply Forall_impl; [| exact FV]; intros iv Hiv; right; exact Hiv
                              | eapply Forall_impl; [| exact FS]; intros iv Hiv; left; exact (swin_sown w iv OK Hiv)]. }
    destruct (pmxa_keep_but w s LB LBs m mo c ins tbl ftbl TB spal m' (WV ++ WS) O_V1 (blkV1 c) OK X0 MU WM FW
                ltac:(lia) ltac:(unfold O_V1, PARSER_SIZE; lia) ltac:(left; split; reflexivity))
      as (U1 & U2 & U3 & S1 & S2 & S3 & _ & K2 & K3).
    destruct (K2 ltac:(unfold O_V1, O_V2; lia)) as [V2 S5]. destruct (K3 ltac:(unfold O_V1, O_V3; lia)) as [V3 S6].
    eapply (pmxa_vupd_gen w s LB LBs m mo c ins tbl ftbl TB spal m' mo' _ WV WS O_V1 (blkV1 c));
      [exact OK | exact X0 | exact Hknn | exact Hfk | exact MU | exact WM | exact DM | exact MP' | exact MI' | exact STK' | exact FV | exact FS
      | lia | unfold O_V1, PARSER_SIZE; lia | | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact U1 | exact U2 | exact U3 | exact V1' | exact V2 | exact V3 |].
    - intros NZ. unfold c_blocks, blkV1 in *. cbn [fst] in NZ. rewrite !in_app_iff. right; right; right; left.
      unfold vec_opnd_blocks. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [contradiction | left; reflexivity].
    - intros NZ. unfold blkV1. cbn [fst snd] in *. pose proof (SH' NZ) as SH. cbn [t3a t3b t3c fst snd] in SH.
      destruct SH as (_ & _ & [_ WR]). pose proof V1' as (_ & _ & _ & Hlen & _).
      rewrite RtB_Iface.cc_gen_length in WR by (unfold OPND_SZ in *; lia). exact WR.
    - cbn [set_v1A c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 pmc_sh]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
      split; [exact SH'|]. split; [exact S5 | exact S6].
  Qed.

  Lemma pmxa_vupd1T : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' mo' WV WS n' tbl',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    munch (WV ++ WS) m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    as_MPRES H mo mo' -> mem_inv asegs m' -> slots_ok w m' bvmap_empty tbl' ->
    Forall (vwinT w O_V1 (blkV1 c)) WV -> Forall (swin w) WS ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V1) (t3a (c_v1 c)) n' (t3c (c_v1 c)) ->
    vsh_opnd m' (t3a (c_v1 c), n', t3c (c_v1 c)) ->
    PMXAT H LINV w s LB LBs m' mo' (set_v1A c (t3a (c_v1 c), n', t3c (c_v1 c))) ins tbl' ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' mo' WV WS n' tbl' OK X0 Hknn Hfk MU WM DM MP' MI' SL' FV FS V1' SH'.
    assert (FW : Forall (fun iv => sown w iv \/ vwin w O_V1 (blkV1 c) iv) (WV ++ WS)).
    { apply Forall_app. split; [eapply Forall_impl; [| exact FV]; intros iv [Hiv|Hiv]; [right; exact Hiv | left; exact (rfw_sown w iv OK Hiv)]
                              | eapply Forall_impl; [| exact FS]; intros iv Hiv; left; exact (swin_sown w iv OK Hiv)]. }
    destruct (pmxa_keep_but w s LB LBs m mo c ins tbl ftbl TB spal m' (WV ++ WS) O_V1 (blkV1 c) OK X0 MU WM FW
                ltac:(lia) ltac:(unfold O_V1, PARSER_SIZE; lia) ltac:(left; split; reflexivity))
      as (U1 & U2 & U3 & S1 & S2 & S3 & _ & K2 & K3).
    destruct (K2 ltac:(unfold O_V1, O_V2; lia)) as [V2 S5]. destruct (K3 ltac:(unfold O_V1, O_V3; lia)) as [V3 S6].
    eapply (pmxa_vupd_genT w s LB LBs m mo c ins tbl ftbl TB spal m' mo' _ WV WS O_V1 (blkV1 c) tbl');
      [exact OK | exact X0 | exact Hknn | exact Hfk | exact MU | exact WM | exact DM | exact MP' | exact MI' | exact SL' | exact FV | exact FS
      | lia | unfold O_V1, PARSER_SIZE; lia | | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact U1 | exact U2 | exact U3 | exact V1' | exact V2 | exact V3 |].
    - intros NZ. unfold c_blocks, blkV1 in *. cbn [fst] in NZ. rewrite !in_app_iff. right; right; right; left.
      unfold vec_opnd_blocks. destruct (Z.eqb_spec (t3a (c_v1 c)) 0); [contradiction | left; reflexivity].
    - intros NZ. unfold blkV1. cbn [fst snd] in *. pose proof (SH' NZ) as SH. cbn [t3a t3b t3c fst snd] in SH.
      destruct SH as (_ & _ & [_ WR]). pose proof V1' as (_ & _ & _ & Hlen & _).
      rewrite RtB_Iface.cc_gen_length in WR by (unfold OPND_SZ in *; lia). exact WR.
    - cbn [set_v1A c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 pmc_sh]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
      split; [exact SH'|]. split; [exact S5 | exact S6].
  Qed.

  Lemma pmxa_vupd3 : forall (w : pmwA H) s LB LBs m mo c ins tbl ftbl TB spal m' mo' WV WS xs',
    pmw_okA H w -> PMXAT H LINV w s LB LBs m mo c ins tbl ftbl TB spal ->
    keys_nonneg (map fst tbl) = true -> fkeys_ok (map fst ftbl) = true ->
    munch (WV ++ WS) m m' -> wmono asegs m m' -> (forall x, m x <> None -> m' x <> None) ->
    as_MPRES H mo mo' -> mem_inv asegs m' -> stk asegs m' (wa_lo w) (wa_s1 w) ->
    Forall (vwin w O_V3 (blkV3 c)) WV -> Forall (swin w) WS ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m' (wa_p w + O_V3) (t3a (c_v3 c)) xs' (t3c (c_v3 c)) ->
    vsh32 m' (t3a (c_v3 c), xs', t3c (c_v3 c)) ->
    PMXAT H LINV w s LB LBs m' mo' (set_v3A c (t3a (c_v3 c), xs', t3c (c_v3 c))) ins tbl ftbl TB spal.
  Proof.
    intros w s LB LBs m mo c ins tbl ftbl TB spal m' mo' WV WS xs' OK X0 Hknn Hfk MU WM DM MP' MI' STK' FV FS V3' SH'.
    assert (FW : Forall (fun iv => sown w iv \/ vwin w O_V3 (blkV3 c) iv) (WV ++ WS)).
    { apply Forall_app. split; [eapply Forall_impl; [| exact FV]; intros iv Hiv; right; exact Hiv
                              | eapply Forall_impl; [| exact FS]; intros iv Hiv; left; exact (swin_sown w iv OK Hiv)]. }
    destruct (pmxa_keep_but w s LB LBs m mo c ins tbl ftbl TB spal m' (WV ++ WS) O_V3 (blkV3 c) OK X0 MU WM FW
                ltac:(unfold O_V1, O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia) ltac:(right; right; split; reflexivity))
      as (U1 & U2 & U3 & S1 & S2 & S3 & K1 & K2 & _).
    destruct (K1 ltac:(unfold O_V1, O_V3; lia)) as [V1 S4]. destruct (K2 ltac:(unfold O_V2, O_V3; lia)) as [V2 S5].
    eapply (pmxa_vupd_gen w s LB LBs m mo c ins tbl ftbl TB spal m' mo' _ WV WS O_V3 (blkV3 c));
      [exact OK | exact X0 | exact Hknn | exact Hfk | exact MU | exact WM | exact DM | exact MP' | exact MI' | exact STK' | exact FV | exact FS
      | unfold O_V1, O_V3; lia | unfold O_V3, PARSER_SIZE; lia | | | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity
      | exact U1 | exact U2 | exact U3 | exact V1 | exact V2 | exact V3' |].
    - intros NZ. unfold c_blocks, blkV3 in *. cbn [fst] in NZ. rewrite !in_app_iff. right; right; right; right; right; left.
      destruct (Z.eqb_spec (t3a (c_v3 c)) 0); [contradiction | left; reflexivity].
    - intros NZ. unfold blkV3. cbn [fst snd] in *. pose proof (SH' NZ) as SH. cbn [t3a t3b t3c fst snd] in SH.
      destruct SH as (_ & _ & [_ WR]). pose proof V3' as (_ & _ & _ & Hlen & _).
      rewrite RtB_Iface.cc_gen_length in WR by (unfold Zlen in *; lia). exact WR.
    - cbn [set_v3A c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 pmc_sh]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
      split; [exact S4|]. split; [exact S5 | exact SH'].
  Qed.
End Vup.

Definition bsum (f : Z -> Z) (l : list (Z * Z)) : Z := fold_right (fun q acc => f (snd q) + acc) 0 l.
Definition phi1 (k : Z) : Z := if ICM_LARGE <? k then k else 0.

Lemma bsum_cons : forall f x l, bsum f (x :: l) = f (snd x) + bsum f l. Proof. reflexivity. Qed.
Lemma bsum_app : forall f l1 l2, bsum f (l1 ++ l2) = bsum f l1 + bsum f l2.
Proof. intros f l1 l2. induction l1 as [|x l1 IH]; [reflexivity|]. cbn [app]. rewrite !bsum_cons, IH. lia. Qed.
Lemma bsum_perm : forall f l l', Permutation l l' -> bsum f l = bsum f l'.
Proof. intros f l l' P. induction P; rewrite ?bsum_cons in *; lia. Qed.
Lemma bsum_le_len : forall f K l, (forall q, In q l -> f (snd q) <= K) -> bsum f l <= K * Z.of_nat (length l).
Proof.
  intros f K l HK. induction l as [|x l IH]; [cbn; lia|]. rewrite bsum_cons. cbn [length]. rewrite Nat2Z.inj_succ.
  pose proof (HK x (or_introl eq_refl)). pose proof (IH (fun q Hq => HK q (or_intror Hq))). lia.
Qed.
Lemma bsum_map_const : forall {V : Type} f NS (ents : list (Z * (Z * V))),
  bsum f (map (fun e => (fst e, NS)) ents) = f NS * Z.of_nat (length ents).
Proof.
  intros V f NS ents. induction ents as [|e ents IH]; [cbn; lia|]. cbn [map]. rewrite bsum_cons. cbn [snd length].
  rewrite Nat2Z.inj_succ, IH. lia.
Qed.
Lemma bsum_opt : forall f (b : bool) (q : Z * Z), bsum f (if b then [] else [q]) = (if b then 0 else f (snd q)).
Proof. intros f [|] q; [reflexivity|]. rewrite bsum_cons. unfold bsum. cbn [fold_right]. lia. Qed.
Lemma len_opt : forall (b : bool) (q : Z * Z), Z.of_nat (length (if b then [] else [q])) = (if b then 0 else 1).
Proof. intros [|] q; reflexivity. Qed.

Lemma lb_small_bsum : forall LB, lb_small LB = bsum nsmall (lbl LB).
Proof. induction LB as [|b LB IH]; [reflexivity|]. unfold lbl in *. cbn [map]. rewrite lb_small_cons, bsum_cons, IH. reflexivity. Qed.
Lemma nlarge_bsum : forall LB, nlarge LB = bsum nlg (lbl LB).
Proof. induction LB as [|b LB IH]; [reflexivity|]. unfold lbl in *. cbn [map]. rewrite nlarge_cons, bsum_cons, IH. reflexivity. Qed.
Lemma length_lbl_eq : forall LB : list block, length (lbl LB) = length LB.
Proof. intros LB. unfold lbl. apply length_map. Qed.
Lemma pm_phi_blocks_bsum : forall l, pm_phi_blocks l = 8 * bsum phi1 l.
Proof. intros l. reflexivity. Qed.

Lemma nsmall_le_64512 : forall k, nsmall k <= 64512.
Proof. intros k. unfold nsmall. destruct (Z.leb_spec k 64512); lia. Qed.
Lemma phi1_le : forall k, 0 <= k -> phi1 k <= k.
Proof. intros k Hk. unfold phi1. destruct (ICM_LARGE <? k); lia. Qed.
Lemma phi1_small : forall k, k <= 64512 -> phi1 k = 0.
Proof. intros k Hk. unfold phi1, ICM_LARGE. destruct (Z.ltb_spec 64512 k); lia. Qed.

Lemma umap_blocks_meas : forall {V : Type} NS bl bc (ents : list (Z * (Z * V))),
  0 <= NS <= 64512 -> 0 <= 8 * bc ->
  bsum nsmall (umap_blocks NS bl bc ents) <= 64512 + NS * Z.of_nat (length ents)
  /\ bsum nlg (umap_blocks NS bl bc ents) <= 1
  /\ Z.of_nat (length (umap_blocks NS bl bc ents)) <= 1 + Z.of_nat (length ents)
  /\ bsum phi1 (umap_blocks NS bl bc ents) <= 8 * bc.
Proof.
  intros V NS bl bc ents HNS Hbc. unfold umap_blocks.
  rewrite !bsum_app, !bsum_map_const, length_app, length_map, Nat2Z.inj_add, !bsum_opt, len_opt. cbn [snd].
  set (L := Z.of_nat (length ents)). assert (0 <= L) by (unfold L; lia).
  rewrite (phi1_small NS) by lia.
  assert (nsmall NS = NS) by (unfold nsmall; destruct (Z.leb_spec NS 64512); lia).
  assert (nlg NS = 0) by (unfold nlg; destruct (Z.ltb_spec 64512 NS); lia).
  pose proof (nsmall_le_64512 (8 * bc)). pose proof (nlg_bounds (8 * bc)). pose proof (phi1_le (8 * bc) Hbc).
  destruct (bc =? 0); nia.
Qed.

Lemma opt_block_meas : forall (b : bool) (a k : Z), 0 <= k ->
  bsum nsmall (if b then [] else [(a, k)]) <= 64512 /\ bsum nlg (if b then [] else [(a, k)]) <= 1
  /\ Z.of_nat (length (if b then [] else [(a, k)])) <= 1 /\ bsum phi1 (if b then [] else [(a, k)]) <= k.
Proof.
  intros b a k Hk. rewrite !bsum_opt, len_opt. cbn [snd].
  pose proof (nsmall_le_64512 k). pose proof (nlg_bounds k). pose proof (phi1_le k Hk). destruct b; lia.
Qed.

Lemma tr_meas : forall (l : list (Z * Z)), Zlength l <= 2 -> (forall q, In q l -> 0 < snd q <= 2 ^ 28) ->
  bsum nsmall l <= 2 * 64512 /\ bsum nlg l <= 2 /\ Z.of_nat (length l) <= 2 /\ bsum phi1 l <= 2 ^ 29.
Proof.
  intros l HL HP. unfold Zlength in HL.
  pose proof (bsum_le_len nsmall 64512 l (fun q _ => nsmall_le_64512 (snd q))).
  pose proof (bsum_le_len nlg 1 l (fun q _ => proj2 (nlg_bounds (snd q)))).
  pose proof (bsum_le_len phi1 (2 ^ 28) l (fun q Hq => Z.le_trans _ _ _ (phi1_le (snd q) ltac:(pose proof (HP q Hq); lia)) (proj2 (HP q Hq)))).
  lia.
Qed.

Lemma cblocks_meas : forall n c, 0 <= n -> pm_bud n c ->
  bsum nsmall (c_blocks c) <= 36 * n + 80 + 8 * 64512
  /\ Z.of_nat (length (c_blocks c)) <= n / 2 + n / 2 + n / 3 + 11
  /\ bsum nlg (c_blocks c) <= 8
  /\ bsum phi1 (c_blocks c) <= 24 * n + 3 * 4096 + 2 ^ 23 + 2 ^ 20 + 2 ^ 26 + 2 ^ 29.
Proof.
  intros n c Hn B.
  destruct B as ((Bn1 & Bn2 & Bn3) & Bb1 & Bb2 & Bb3 & Bv1 & Bv2 & Bv3 & Btr & Btrp).
  unfold c_blocks, vec_opnd_blocks. rewrite !bsum_app, !length_app, !Nat2Z.inj_add.
  destruct (umap_blocks_meas 24 (t3a (c_m1 c)) (t3b (c_m1 c)) (t3c (c_m1 c)) ltac:(lia) ltac:(lia)) as (S1 & G1 & L1 & P1).
  destruct (umap_blocks_meas 32 (t3a (c_m2 c)) (t3b (c_m2 c)) (t3c (c_m2 c)) ltac:(lia) ltac:(lia)) as (S2 & G2 & L2 & P2).
  destruct (umap_blocks_meas 24 (t3a (c_m3 c)) (t3b (c_m3 c)) (t3c (c_m3 c)) ltac:(lia) ltac:(lia)) as (S3 & G3 & L3 & P3).
  destruct (opt_block_meas (t3a (c_v1 c) =? 0) (t3a (c_v1 c)) (OPND_SZ * t3c (c_v1 c)) ltac:(lia)) as (S4 & G4 & L4 & P4).
  destruct (opt_block_meas (t3a (c_v2 c) =? 0) (t3a (c_v2 c)) (4 * t3c (c_v2 c)) ltac:(lia)) as (S5 & G5 & L5 & P5).
  destruct (opt_block_meas (t3a (c_v3 c) =? 0) (t3a (c_v3 c)) (4 * t3c (c_v3 c)) ltac:(lia)) as (S6 & G6 & L6 & P6).
  destruct (tr_meas (c_tr c) Btr Btrp) as (S7 & G7 & L7 & P7).
  unfold Zlength in Bn1, Bn2, Bn3.
  set (E1 := Z.of_nat (length (t3c (c_m1 c)))) in *. set (E2 := Z.of_nat (length (t3c (c_m2 c)))) in *.
  set (E3 := Z.of_nat (length (t3c (c_m3 c)))) in *.
  assert (E1 <= n / 2 + 1 /\ E2 <= n / 2 + 1 /\ E3 <= n / 3 + 1).
  { pose proof (Z.div_mod n 2 ltac:(lia)). pose proof (Z.mod_pos_bound n 2 ltac:(lia)).
    pose proof (Z.div_mod n 3 ltac:(lia)). pose proof (Z.mod_pos_bound n 3 ltac:(lia)). lia. }
  lia.
Qed.

Lemma pm_meas_of_bud : forall n c (LBs : list block), 0 <= n -> pm_bud n c -> Permutation (lbl LBs) (c_blocks c) ->
  pm_meas_ok n LBs.
Proof.
  intros n c LBs Hn B P. destruct (cblocks_meas n c Hn B) as (S & L & G & _).
  unfold pm_meas_ok. rewrite lb_small_bsum, nlarge_bsum, <- length_lbl_eq.
  rewrite (bsum_perm nsmall _ _ P), (bsum_perm nlg _ _ P), (Permutation_length P).
  unfold po_small, po_cnt, po_large. lia.
Qed.

Lemma pm_resv_of_bud : forall n c, 0 <= n < 2 ^ 24 -> pm_bud n c -> pm_cap c + PM_RESERVE <= po_cost n.
Proof.
  intros n c Hn B. destruct (cblocks_meas n c ltac:(lia) B) as (_ & _ & _ & P).
  unfold pm_cap. rewrite pm_phi_blocks_bsum. pose proof (po_cost_lo n) as _. unfold PM_RESERVE.
  eapply Z.le_trans; [| apply (Z.le_trans _ (2 ^ 34)); [apply Z.le_refl | ]].
  - lia.
  - unfold po_cost. apply Z.le_refl.
Qed.
