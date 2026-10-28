(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BMState BMem BCells BArr BExec BLFrame BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BakeStackRep BllocRepX RtB_IMemset.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Bridge LbB_Conv LbB_Call LbB_DStat LbB_NBr LbB_NMc LbB_NLeaf LbB_NPc1 LbB_NLoops LbB_NPc2 LbB_NPc3 LbB_NSn LbB_NVf LbB_NPfc LbB_NIvf.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_DPdK LbB_PqK.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac StoreOk MemSplit Hoare ShapeAlg SRealizes MmapSim
  RefMemcpyLib LibIface LibEff LibMaskBits ZStores SymExec3 SymExec3Sound SymRun3 LibTail SumWalkTac.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContLib StrLib ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DiagTac NumTac NumLeaf.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Notation SEGS := asegs (only parsing).
Local Ltac xms H := first [exact H | apply msteps_bridge; exact H].

Definition VSN_RET_MS : Z := 0x1747e4.
Definition VSN_RET_VF : Z := 0x174820.
Definition VSN_RETPC : Z := 0x174844.

Lemma w2lb_mod : forall (n : nat) v, (n <= 8)%nat ->
  word_to_le_bytes n (Z_to_bv 64 v) = word_to_le_bytes n (Z_to_bv 64 (v mod 2 ^ (8 * Z.of_nat n))).
Proof.
  intros n v Hn. unfold word_to_le_bytes. rewrite !Z_to_bv_unsigned.
  rewrite !(Z_to_le_bytes_wrap n 64) by lia.
  replace (v mod 2 ^ (8 * Z.of_nat n)) with (bv_wrap (N.of_nat (8 * n)) v).
  - symmetry. apply Z_to_le_bytes_wrap. lia.
  - unfold bv_wrap, bv_modulus. f_equal. f_equal. lia.
Qed.

Lemma fld0_of_rdn0 : forall M p L d (n : nat),
  rdn SEGS M (Z_to_bv 64 p) (Z.to_nat L) = Some (repeat (b8 0) (Z.to_nat L)) ->
  0 <= p -> p + L < 2 ^ 64 -> 0 <= d -> d + Z.of_nat n <= L -> (n = 8 \/ n = 4 \/ n = 1)%nat ->
  fld SEGS M (p + d) n 0.
Proof.
  intros M p L d n RD Hp HL Hd Hdn Hn. unfold fld.
  pose proof (rdn_length _ _ _ _ _ RD) as Hlen.
  assert (RS : rdn SEGS M (Z_to_bv 64 (p + d)) n = Some (firstn n (skipn (Z.to_nat d) (repeat (b8 0) (Z.to_nat L))))).
  { pose proof (rdn_skipn SEGS M (Z.to_nat L) (Z_to_bv 64 p) _ (Z.to_nat d) RD ltac:(lia)) as RK.
    rewrite w_add_nat, u64_of_Z, Z2Nat.id in RK by lia.
    apply (SeqExec.rdn_firstn SEGS M _ (Z_to_bv 64 (p + d)) _ n RK). lia. }
  rewrite RS. f_equal.
  assert (SR : forall (k m : nat) (b : byte), skipn k (repeat b m) = repeat b (m - k)).
  { intros k; induction k as [|k IH]; intros [|m] b; cbn; rewrite ?IH; try reflexivity. }
  assert (FR : forall (k m : nat) (b : byte), (k <= m)%nat -> firstn k (repeat b m) = repeat b k).
  { intros k; induction k as [|k IH]; intros [|m] b Hk; cbn; try reflexivity; [lia|]. rewrite IH by lia. reflexivity. }
  rewrite SR, FR by lia.
  destruct Hn as [-> | [-> | ->]]; reflexivity.
Qed.

Section Vsn.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.
  Variables (F : bvmap 5 word) (fc : bv 32).
  Variable gd : Z.
  Hypothesis Hgd : 0 <= gd < 2 ^ 64.
  Variables (R : bvmap 5 word) (M : mem) (s ret v conv lo shi : Z).

  Hypothesis Hra : getr R 1%bv = Z_to_bv 64 ret.
  Hypothesis Hret : ret_ok (Z_to_bv 64 ret).
  Hypothesis Hretr : 0 <= ret < 2 ^ 64.
  Hypothesis Hsp : getr R 2%bv = Z_to_bv 64 s.
  Hypothesis Ha0 : getr R 10%bv = Z_to_bv 64 (s + 2312).
  Hypothesis Ha1 : getr R 11%bv = Z_to_bv 64 24.
  Hypothesis Ha2 : getr R 12%bv = Z_to_bv 64 (s + 2336).
  Hypothesis Ha3 : getr R 13%bv = Z_to_bv 64 (s + 2208).
  Hypothesis Hslo : 2 ^ 33 <= s - 2624.
  Hypothesis Hshi : s + 2340 < 2 ^ 47.
  Hypothesis Hal : s mod 16 = 0.
  Hypothesis HD : mdef M (s - 2624) 4964.
  Hypothesis Fv : fld SEGS M (s + 2208) 8 v.
  Hypothesis Hv : 0 <= v < 2 ^ 64.
  Hypothesis F0 : fld SEGS M (s + 2336) 1 37.
  Hypothesis F1 : fld SEGS M (s + 2337) 1 108.
  Hypothesis F2 : fld SEGS M (s + 2338) 1 conv.
  Hypothesis F3 : fld SEGS M (s + 2339) 1 0.
  Hypothesis Hconv : conv = 117 \/ conv = 100 \/ conv = 120.
  Hypothesis Hvpos : conv = 100 -> v < 2 ^ 63.
  Hypothesis FCAN : fld SEGS M A_CANARY 8 gd.

  Hypothesis RF : rfull R.
  Hypothesis NI : ninv lo shi M.
  Hypothesis STK : stk asegs M lo s.
  Hypothesis CEIL : aceil <= lo.
  Hypothesis LOS : lo + AINTRIN_STACK + 1392 <= s.
  Hypothesis SHI : s + 2404 <= shi.

  Definition vsn_post (nc : Z) (R' : bvmap 5 word) (M' : mem) : Prop :=
    getr R' 10%bv = Z_to_bv 64 nc /\ 1 <= nc <= 21
    /\ (forall r, In r leaf_kept -> getr R' r = getr R r)
    /\ stores_in (fun a => zwin (s - 1328 - AINTRIN_STACK) s a \/ zwin (s + 2312) (s + 2312 + nc + 1) a) M M'
    /\ rfull R' /\ ninv lo shi M' /\ stk asegs M' lo s.

  Lemma vsnprintf_A : exists nc R' M',
    BExec.msteps SEGS (@mkst (PropExec.mkFP F fc) R (Z_to_bv 64 AREAL_VSNPRINTF) M (seg_rom SEGS)) (@mkst (PropExec.mkFP F fc) R' (Z_to_bv 64 ret) M' (seg_rom SEGS)) /\ vsn_post nc R' M'.
  Proof.
    pose proof NI as (ROC & _ & _ & RRC). pose proof aceil_facts as ((AF1 & AF2) & _).
    set (E := Eseed R [Z_to_bv 64 gd]).
    assert (HR : regs_ok E (srs sr_id [(10%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2312)); (12%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2336)); (13%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2208))]) R) by srs_ok.
    assert (HK : know_ok SEGS E M
      [KWr (SA (EVar 2) (-2624)) (ELit 4964); KRange (EVar 2) (2 ^ 33 + 2624) (2 ^ 47 - 2340); KAlign (EVar 2) 16; KRange (EVar 11) 24 24;
       KImg 0x10000 0x17e000; KImg 0x17e000 0x186000; KWord (SA (ELit 0) A_CANARY) (N.to_nat 8) (EVar 32)]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ s (-2624) 4964); [evs; exact Hsp | lia | lia | lia | lia | exact HD].
      - krv Hsp. - eapply kalign_var; [evs; exact Hsp | lia | lia | exact Hal]. - krv Ha1.
      - apply kimg_ro. exact ROC. - apply kimg_relro. exact RRC. - unfold A_CANARY, ASSPGUARD in *. (pose proof Hgd; kwa FCAN). }
    xrun_at HR HK (PropExec.mkFP F fc) AREAL_VSNPRINTF (seg_rom SEGS) 100%nat [AMEMSET_STUB; AVFPRINTF_STUB; VSN_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK. rename R' into R1. rename HR' into HR1. rename Hms into Hms1. wnorm_in Hms1.
    lazymatch type of Hms1 with msteps _ _ (mkst _ _ ?mm _) => set (M1 := mm) in Hms1 end.
    assert (ST1 : stores_in (zwin (s - 72) s) M M1) by (subst M1; stores_tower).
    assert (SV1 : slots SEGS M1 s [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]) by (subst M1; slots_tower).
    assert (Gcan1 : fld SEGS M1 (s - 48) 8 gd) by (unfold fld; subst M1; peel).
    assert (Gcs1 : fld SEGS M1 (s - 72) 8 (s + 2312)) by (unfold fld; subst M1; peel).
    assert (Gcn1 : fld SEGS M1 (s - 64) 8 23) by (unfold fld; subst M1; peel).
    regval HR1 (1%bv : reg) VSN_RET_MS X1. regval HR1 (2%bv : reg) (s - 304) X2.
    regval HR1 (10%bv : reg) (s - 304) X10. regval HR1 (11%bv : reg) 0 X11. regval HR1 (12%bv : reg) 232 X12.

    assert (HD1 : mdef M1 (s - 2624) 4964) by (eapply stores_in_mdef; [exact ST1 | exact HD]).

    assert (RF1 : rfull R1) by exact (msteps_full asegs _ _ Hms1 RF).
    assert (NI1 : ninv lo shi M1) by (eapply (ninv_keep lo shi M M1 _ NI ST1); intros a Ha; unfold zwin in Ha; clear - Ha CEIL LOS Hshi AF1; unfold AINTRIN_STACK in *; lia).
    pose proof NI1 as (MI1 & AC1 & S01 & RR1).
    assert (STK1 : stk asegs M1 lo (s - 304)).
    { eapply LbB_PqK.stk_keep; [exact (proj1 (stk_split asegs M lo (s - 304) s STK ltac:(clear - LOS; unfold AINTRIN_STACK in *; lia)))
        | eapply (munch_of_stores_in _ [(s - 72, s)]); [exact ST1 | intros x Hx; cbn [outside fst snd]; unfold zwin in Hx; clear - Hx; lia]
        | exact (wmono_of_stores_in _ _ _ ST1) | clear - CEIL AF1; unfold AIMG_TOP; lia]. }
    destruct (a_memset F fc R1 M1 (s - 304) 0 232 VSN_RET_MS (s - 304) lo shi RF1 X1 ltac:(unfold VSN_RET_MS; lia) eq_refl X2 X10 X11 X12
                ltac:(clear; lia) ltac:(clear; lia) ltac:(eapply mdef_sub; [exact HD1 | lia | lia])
                S01 ltac:(clear - LOS; unfold AINTRIN_STACK in *; lia) ltac:(clear - SHI; lia) STK1 CEIL ltac:(clear - LOS; lia) ltac:(clear; lia) MI1 AC1)
      as (R2 & M2 & Hms2 & RF2 & Y10 & ZK2 & ST2w & RD2 & MI2 & AC2 & S02' & STK2).
    assert (ST2 : stores_in (fun a => zwin (s - 304) (s - 72) a \/ zwin (s - 304 - AINTRIN_STACK) (s - 304) a) M1 M2).
    { eapply stores_in_weaken; [exact ST2w|]. intros a Ha. cbv beta in Ha. unfold zwin in *. lia. }
    assert (NI2 : ninv lo shi M2).
    { split; [exact MI2 | split; [exact AC2 | split; [exact S02' |]]].
      eapply relro_clear_hi; [exact RR1 | exact ST2 | intros a Ha; cbv beta in Ha; unfold zwin in Ha; clear - Ha CEIL LOS AF1; unfold AINTRIN_STACK in *; lia]. }
    assert (ST02 : stores_in (zwin (s - 304 - AINTRIN_STACK) s) M M2).
    { eapply (stores_in_join _ _ _ M M1 M2); [exact ST1 | exact ST2 | ..]; intros a Ha; cbv beta in *; unfold zwin, AINTRIN_STACK in *; lia. }
    assert (T02 : forall a (n : nat) x, (a + Z.of_nat n <= s - 304 - AINTRIN_STACK \/ s <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M2 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST02 | intros y Hy; unfold zwin, AINTRIN_STACK in *; lia | lia | lia | exact HF]. }
    assert (T12 : forall a (n : nat) x, (a + Z.of_nat n <= s - 304 - AINTRIN_STACK \/ s - 72 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M1 a n x -> fld SEGS M2 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST2 | intros y Hy; cbv beta; unfold zwin, AINTRIN_STACK in *; lia | lia | lia | exact HF]. }
    assert (Zf : forall d (n : nat), 0 <= d -> d + Z.of_nat n <= 232 -> (n = 8 \/ n = 4 \/ n = 1)%nat -> fld SEGS M2 (s - 304 + d) n 0).
    { intros d n Hd Hdn Hn. eapply (fld0_of_rdn0 M2 (s - 304) 232 d n); [exact RD2 | lia | lia | lia | lia | exact Hn]. }

    assert (Z2 : getr R2 2%bv = Z_to_bv 64 (s - 304)) by (rewrite (ZK2 2%bv) by inl; exact X2).
    assert (Z8 : getr R2 8%bv = Z_to_bv 64 (s + 2208)) by (rewrite (ZK2 8%bv) by inl; regval HR1 (8%bv : reg) (s + 2208) X; exact X).
    assert (Z9 : getr R2 9%bv = Z_to_bv 64 (s + 2336)) by (rewrite (ZK2 9%bv) by inl; regval HR1 (9%bv : reg) (s + 2336) X; exact X).
    assert (Z19 : getr R2 19%bv = Z_to_bv 64 (s + 2312)) by (rewrite (ZK2 19%bv) by inl; regval HR1 (19%bv : reg) (s + 2312) X; exact X).
    assert (Z18 : getr R2 18%bv = Z_to_bv 64 A_CANARY) by (rewrite (ZK2 18%bv) by inl; regval HR1 (18%bv : reg) A_CANARY X; exact X).
    set (E2 := Eseed R2 []).
    assert (HR2 : regs_ok E2 (srs sr_id [(8%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2512)); (9%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2640)); (19%bv : reg, EAlu ALU_ADD (EVar 2) (ELit 2616))]) R2) by srs_ok.
    assert (HK2 : know_ok SEGS E2 M2
      [KWr (SA (EVar 2) (-2320)) (ELit 4964); KRange (EVar 2) (2 ^ 33 + 2320) (2 ^ 47 - 2644); KAlign (EVar 2) 16;
       KImg 0x10000 0x17e000; KImg 0x17e000 0x186000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ (s - 304) (-2320) 4964); [evs; exact Z2 | lia | lia | lia | lia | replace (s - 304 + -2320) with (s - 2624) by lia; eapply stores_in_mdef; [exact ST02 | exact HD]].
      - krv Z2. - eapply kalign_var; [evs; exact Z2 | lia | lia | mlia].
      - apply kimg_ro. eapply mem_inv_hi; [exact ROC | exact ST02 | intros a Ha; unfold zwin, AINTRIN_STACK in Ha; lia].
      - apply kimg_relro. eapply relro_clear_hi; [exact RRC | exact ST02 | intros a Ha; unfold zwin, AINTRIN_STACK in Ha; lia]. }
    xrun_at HR2 HK2 (PropExec.mkFP F fc) VSN_RET_MS (seg_rom SEGS) 100%nat [AMEMSET_STUB; AVFPRINTF_STUB; VSN_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK2. rename R' into R3. rename HR' into HR3. rename Hms into Hms3. wnorm_in Hms3.
    lazymatch type of Hms3 with msteps _ _ (mkst _ _ ?mm _) => set (M3 := mm) in Hms3 end.
    assert (ST3 : stores_in (fun a => zwin (s - 232) (s - 144) a \/ zwin (s + 2312) (s + 2313) a) M2 M3) by (subst M3; stores_tower).
    assert (ST03 : stores_in (fun a => zwin (s - 304 - AINTRIN_STACK) s a \/ zwin (s + 2312) (s + 2313) a) M M3).
    { eapply (stores_in_join _ _ _ M M2 M3); [exact ST02 | exact ST3 | ..]; intros a Ha; cbv beta in *; unfold zwin, AINTRIN_STACK in *; lia. }
    assert (T23 : forall a (n : nat) x, (a + Z.of_nat n <= s - 232 \/ s - 144 <= a) -> a + Z.of_nat n <= s + 2312 -> 0 <= a -> fld SEGS M2 a n x -> fld SEGS M3 a n x).
    { intros a n x G1 G2 G3 HF. eapply (fld_via_stores SEGS); [exact ST3 | intros y Hy; cbv beta; unfold zwin, AINTRIN_STACK in *; lia | lia | lia | exact HF]. }
    assert (T03 : forall a (n : nat) x, (a + Z.of_nat n <= s - 304 - AINTRIN_STACK \/ s <= a) -> (a + Z.of_nat n <= s + 2312 \/ s + 2313 <= a) -> 0 <= a -> a + Z.of_nat n < 2 ^ 64 -> fld SEGS M a n x -> fld SEGS M3 a n x).
    { intros a n x G1 G2 G3 G4 HF. eapply (fld_via_stores SEGS); [exact ST03 | intros y Hy; cbv beta; unfold zwin, AINTRIN_STACK in *; lia | lia | lia | exact HF]. }
    pose proof (T23 (s - 304 + 0) 4%nat 0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) (Zf 0 4%nat ltac:(lia) ltac:(cbn; lia) ltac:(lia))) as Gflags3. replace (s - 304 + 0) with (s - 304) in Gflags3 by lia.
    pose proof (Zf 96 8%nat ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Gbsz2. assert (Gbsz3 : fld SEGS M3 (s - 304 + 96) 8 0) by (unfold fld in Gbsz2 |- *; subst M3; peel; exact Gbsz2).
    pose proof (Zf 136 4%nat ltac:(lia) ltac:(cbn; lia) ltac:(lia)) as Gmode2. assert (Gmode3 : fld SEGS M3 (s - 304 + 136) 4 0) by (unfold fld in Gmode2 |- *; subst M3; peel; exact Gmode2).
    assert (Gwrite3 : fld SEGS M3 (s - 304 + 72) 8 A_SN_WRITE_A) by (unfold fld; subst M3; peel).
    assert (Gbuf3 : fld SEGS M3 (s - 304 + 88) 8 (s - 304 + 255)) by (unfold fld; subst M3; peel).
    assert (EW4 : word_to_le_bytes 4 (Z_to_bv 64 (2 ^ 32 - 1)) = word_to_le_bytes 4 (Z_to_bv 64 18446744073709551615)).
    { rewrite (w2lb_mod 4 18446744073709551615) by lia. reflexivity. }
    assert (Glock3 : fld SEGS M3 (s - 304 + 140) 4 (2 ^ 32 - 1)) by (unfold fld; rewrite EW4; subst M3; peel).
    assert (Glbf3 : fld SEGS M3 (s - 304 + 144) 4 (2 ^ 32 - 1)) by (unfold fld; rewrite EW4; subst M3; peel).
    assert (Gcookie3 : fld SEGS M3 (s - 304 + 152) 8 (s - 304 + 232)) by (unfold fld; subst M3; peel).
    pose proof (T23 (s - 72) 8%nat (s + 2312) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) (T12 (s - 72) 8%nat (s + 2312) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Gcs1)) as Gcs3.
    replace (s - 72) with (s - 304 + 232) in Gcs3 by lia. replace (s + 2312) with (s - 304 + 2616) in Gcs3 by lia.
    pose proof (T23 (s - 64) 8%nat 23 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) (T12 (s - 64) 8%nat 23 ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Gcn1)) as Gcn3.
    replace (s - 64) with (s - 304 + 240) in Gcn3 by lia.
    pose proof (T03 (s + 2208) 8%nat v ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) Fv) as Fv3. replace (s + 2208) with (s - 304 + 2512) in Fv3 by lia.
    pose proof (T03 (s + 2336) 1%nat 37 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F0) as F03. replace (s + 2336) with (s - 304 + 2640) in F03 by lia.
    pose proof (T03 (s + 2337) 1%nat 108 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F1) as F13. replace (s + 2337) with (s - 304 + 2641) in F13 by lia.
    pose proof (T03 (s + 2338) 1%nat conv ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F2) as F23. replace (s + 2338) with (s - 304 + 2642) in F23 by lia.
    pose proof (T03 (s + 2339) 1%nat 0 ltac:(cbn; lia) ltac:(cbn; lia) ltac:(lia) ltac:(cbn; lia) F3) as F33. replace (s + 2339) with (s - 304 + 2643) in F33 by lia.
    assert (ROC3 : mem_inv asegs M3) by (eapply mem_inv_hi; [exact ROC | exact ST03 | intros a Ha; cbv beta in Ha; unfold zwin, AINTRIN_STACK in Ha; lia]).
    assert (RRC3 : relro_clear M3) by (eapply relro_clear_hi; [exact RRC | exact ST03 | intros a Ha; cbv beta in Ha; unfold zwin, AINTRIN_STACK in Ha; lia]).
    assert (FCAN3 : fld SEGS M3 A_CANARY 8 gd) by (eapply (fld_via_stores SEGS); [exact ST03 | intros y Hy; cbv beta; unfold zwin, AINTRIN_STACK, A_CANARY, ASSPGUARD in *; lia | unfold A_CANARY, ASSPGUARD; lia | unfold A_CANARY, ASSPGUARD; cbn; lia | exact FCAN]).
    assert (HD3 : mdef M3 (s - 304 - 2320) 4964) by (replace (s - 304 - 2320) with (s - 2624) by lia; eapply stores_in_mdef; [exact ST03 | exact HD]).
    regval HR3 (1%bv : reg) VSN_RET_VF Y1. regval HR3 (2%bv : reg) (s - 304) Y2. regval HR3 (10%bv : reg) (s - 304) Y10'.
    regval HR3 (11%bv : reg) (s - 304 + 2640) Y11. regval HR3 (12%bv : reg) (s - 304 + 2512) Y12.

    assert (RF3 : rfull R3) by exact (msteps_full asegs _ _ Hms3 RF2).
    assert (NI3 : ninv lo shi M3) by (eapply (ninv_keep lo shi M2 M3 _ NI2 ST3); intros a Ha; cbv beta in Ha; unfold zwin in Ha; clear - Ha CEIL LOS Hshi AF1; unfold AINTRIN_STACK in *; lia).
    assert (STK3 : stk asegs M3 lo (s - 304)).
    { eapply LbB_PqK.stk_keep; [exact STK2
        | eapply (munch_of_stores_in _ [(s - 232, s - 144); (s + 2312, s + 2313)]); [exact ST3 | intros x Hx; cbv beta in Hx; cbn [outside fst snd]; unfold zwin in Hx; clear - Hx; lia]
        | exact (wmono_of_stores_in _ _ _ ST3) | clear - CEIL AF1; unfold AIMG_TOP; lia]. }
    pose proof (vfprintf_icpt H HH F fc gd Hgd R3 M3 (s - 304) VSN_RET_VF v conv lo shi) as LV.
    repeat lazymatch type of LV with (exists _, _) => fail | forall _ : ?T, _ =>
      specialize (LV ltac:(first [eassumption | reflexivity | apply bv_eq; vm_compute; reflexivity | unfold VSN_RET_VF; lia | unfold IVF_FRAME; lia | mlia
                                  | unfold IVF_FRAME; replace (s - 304 - 2320) with (s - 2624) by lia; eapply stores_in_mdef; [exact ST03 | exact HD]
                                  | clear - LOS; unfold AINTRIN_STACK in *; lia | clear - SHI; lia])) end.
    destruct LV as (nc & R4 & M4 & Hms4 & P10 & Pnc & PK & PST & RF4 & NI4 & STK4).

    assert (ST04 : stores_in (fun a => zwin (s - 1328 - AINTRIN_STACK) s a \/ zwin (s + 2312) (s + 2312 + nc + 1) a) M M4).
    { eapply (stores_in_join _ _ _ M M3 M4); [exact ST03 | exact PST | ..]; intros a Ha; cbv beta in *; unfold zwin, AINTRIN_STACK in *; lia. }
    assert (SV4 : slots SEGS M4 s [Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv]).
    { eapply slots_agree; [exact SV1 | cbn; lia | lia |]. cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.mul Z.mul].
      assert (A12 : agree_on (zwin (s - 40) s) M1 M2) by (eapply stores_in_agree; [exact ST2 | intros b Hb; unfold zwin, AINTRIN_STACK in *; lia]).
      assert (A23 : agree_on (zwin (s - 40) s) M2 M3) by (eapply stores_in_agree; [exact ST3 | intros b Hb; cbv beta; unfold zwin, AINTRIN_STACK in *; lia]).
      assert (A34 : agree_on (zwin (s - 40) s) M3 M4) by (eapply stores_in_agree; [exact PST | intros b Hb; cbv beta; unfold zwin, AINTRIN_STACK in *; lia]).
      intros b Hb. rewrite (A34 b Hb), (A23 b Hb). exact (A12 b Hb). }
    assert (Gcan4 : fld SEGS M4 (s - 48) 8 gd).
    { eapply (fld_via_stores SEGS); [exact PST | intros y Hy; cbv beta; unfold zwin, AINTRIN_STACK in *; lia | lia | cbn; lia |].
      apply T23; [cbn; lia | cbn; lia | lia |]. apply T12; [cbn; clear - LOS; unfold AINTRIN_STACK in *; lia | lia | cbn; lia | exact Gcan1]. }
    assert (FCAN4 : fld SEGS M4 A_CANARY 8 gd) by (eapply (fld_via_stores SEGS); [exact ST04 | intros y Hy; cbv beta; unfold zwin, AINTRIN_STACK, A_CANARY, ASSPGUARD in *; lia | unfold A_CANARY, ASSPGUARD; lia | unfold A_CANARY, ASSPGUARD; cbn; lia | exact FCAN]).
    assert (V2' : getr R4 2%bv = Z_to_bv 64 (s - 304)) by (rewrite (PK 2%bv) by inl; exact Y2).
    assert (V18 : getr R4 18%bv = Z_to_bv 64 A_CANARY) by (rewrite (PK 18%bv) by inl; rewrite (syms_id_sound R2 _ _ R3 [18%bv] HR3 eq_refl 18%bv ltac:(inl)); exact Z18).
    set (E4 := Eseed R4 [Z_to_bv 64 nc; Z_to_bv 64 ret; getr R 8%bv; getr R 9%bv; getr R 18%bv; getr R 19%bv; Z_to_bv 64 gd]).
    assert (HR4 : regs_ok E4 sr_id R4) by (apply regs_ok_seed).
    assert (HK4 : know_ok SEGS E4 M4
      [KWr (SA (EVar 2) (-2320)) (ELit 4964); KRange (EVar 2) (2 ^ 33 + 2320) (2 ^ 47 - 2644); KAlign (EVar 2) 16;
       KRange (EVar 18) A_CANARY A_CANARY;
       KWord (SA (EVar 2) 256) (N.to_nat 8) (EVar 38); KWord (SA (ELit 0) A_CANARY) (N.to_nat 8) (EVar 38);
       KWord (SA (EVar 2) 296) (N.to_nat 8) (EVar 33); KWord (SA (EVar 2) 288) (N.to_nat 8) (EVar 34); KWord (SA (EVar 2) 280) (N.to_nat 8) (EVar 35);
       KWord (SA (EVar 2) 272) (N.to_nat 8) (EVar 36); KWord (SA (EVar 2) 264) (N.to_nat 8) (EVar 37);
       KImg 0x10000 0x17e000; KImg 0x17e000 0x186000]).
    { repeat apply Forall_cons; try apply Forall_nil.
      - eapply (kwr_of_mdef _ _ _ _ (s - 304) (-2320) 4964); [evs; exact V2' | lia | lia | lia | lia | replace (s - 304 + -2320) with (s - 2624) by lia; eapply stores_in_mdef; [exact ST04 | exact HD]].
      - krv V2'. - eapply kalign_var; [evs; exact V2' | lia | lia | mlia].
      - unfold A_CANARY, ASSPGUARD in *; krv V18.
      - (pose proof Hgd; kwv Gcan4 V2'). - unfold A_CANARY, ASSPGUARD in *; (pose proof Hgd; kwa FCAN4).
      - kwe (SV4 0%nat ltac:(cbn [length]; lia)) V2'. - kwe (SV4 1%nat ltac:(cbn [length]; lia)) V2'. - kwe (SV4 2%nat ltac:(cbn [length]; lia)) V2'.
      - kwe (SV4 3%nat ltac:(cbn [length]; lia)) V2'. - kwe (SV4 4%nat ltac:(cbn [length]; lia)) V2'.
      - apply kimg_ro. eapply mem_inv_hi; [exact ROC | exact ST04 | intros a Ha; cbv beta in Ha; unfold zwin, AINTRIN_STACK in Ha; lia].
      - apply kimg_relro. eapply relro_clear_hi; [exact RRC | exact ST04 | intros a Ha; cbv beta in Ha; unfold zwin, AINTRIN_STACK in Ha; lia]. }
    xrun_at HR4 HK4 (PropExec.mkFP F fc) VSN_RET_VF (seg_rom SEGS) 100%nat [AMEMSET_STUB; AVFPRINTF_STUB; VSN_RETPC] (SCR [] [] []) 40%N.
    { scs_auto. }
    clear HK4. rename Hms into Hms5.
    regval HR' (1%bv : reg) ret T1. regval HR' (10%bv : reg) nc T10.
    pose proof (@ret_at (PropExec.mkFP F fc) SEGS VSN_RETPC R' M4 (seg_rom SEGS) (Z_to_bv 64 ret) ltac:(vm_refl_bv) T1 Hret) as Hms6.
    exists nc, R', M4. split.
    { eapply BExec.msteps_trans; [xms Hms1|]. eapply BExec.msteps_trans; [xms Hms2|]. eapply BExec.msteps_trans; [xms Hms3|].
      eapply BExec.msteps_trans; [xms Hms4|]. eapply BExec.msteps_trans; [xms Hms5 | xms Hms6]. }
    split; [exact T10|]. split; [exact Pnc|]. split.
    { intros r Hr. unfold leaf_kept in Hr. cbn in Hr. repeat (destruct Hr as [<-|Hr]; [kept_chain HR' PK HR3 ZK2 HR1|]). destruct Hr. }
    split; [exact ST04|]. split; [exact (msteps_full asegs _ _ Hms5 RF4)|]. split; [exact NI4|].
    eapply LbB_PqK.stk_keep; [exact STK
      | eapply (munch_of_stores_in _ [(s - 1328 - AINTRIN_STACK, s); (s + 2312, s + 2312 + nc + 1)]); [exact ST04 | intros x Hx; cbv beta in Hx; cbn [outside fst snd]; unfold zwin in Hx; clear - Hx; lia]
      | exact (wmono_of_stores_in _ _ _ ST04) | clear - CEIL AF1; unfold AIMG_TOP; lia].
  Qed.
End Vsn.

