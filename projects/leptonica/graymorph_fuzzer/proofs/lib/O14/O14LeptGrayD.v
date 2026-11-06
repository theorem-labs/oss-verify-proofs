(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptRoom.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptStderr O14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14CL7a.
Import O14CL7a.O14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require Import O14LeptPixHdr O14LeptCmap2 O14LeptPixCopy O14LeptGrayD_iface O14SetBorder O14_code_gmD.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.O14 Require O14Gray3h O14Gray3hD.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section GrayDW.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma wpl8_ge : forall w, (0 <= w)%Z -> (w <= 4 * wpl_of w 8)%Z.
Proof.
  intros w Hw. unfold wpl_of.
  pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)) as E. pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)) as R.
  set (q := ((w * 8 + 31) / 32)%Z) in *. set (r := ((w * 8 + 31) mod 32)%Z) in *. clearbody q r. lia.
Qed.

(* [comment removed for export] *)
Theorem pixSetBorderVal_W : pixSetBorderVal_contract.
Proof.
  unfold pixSetBorderVal_contract, PC_pixSetBorderVal, SBV_STACK, gray8_shape.
  intros C Ar A m md regs s pixs w h cm data left right top bot val ret S CK HW SUB H2 Hs16 Hlo Hhi H1 Hret H10 H11 H12 H13 H14 H15
         Hl Hr Ht Hb Htb Hval PX (Hw1 & Hh1 & HOK) Lp Ld Ld0 Ld00 NEpd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_of_range w 8 ltac:(lia) DV) as Hwr. pose proof (wpl8_ge w ltac:(lia)) as Hw4.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (Hwplh : (0 < 4 * (wpl_of w 8 * h))%Z) by (assert (1 * 1 <= wpl_of w 8 * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Hwplh) as [Gd TOPd].
  pose proof (wf_data _ WF) as Rdat. cbn [p_data hdv] in Rdat. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (SOKd : store_ok SEGS m (Z_to_bv 64 data) (Z.to_nat (4 * (wpl_of w 8 * h))) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A m md (Z_to_bv 64 data) _ x CK HW Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  destruct (sbv_run m al_rom pixs w h (wpl_of w 8) data s left right top bot val ret
              (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hret Hl Hr Ht Hb Htb
              (PIX_rd_w SEGS _ _ _ PX) (PIX_rd_h SEGS _ _ _ PX) (PIX_rd_d SEGS _ _ _ PX) (PIX_rd_wpl SEGS _ _ _ PX) (PIX_rd_data SEGS _ _ _ PX)
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALd]]) SOKd ltac:(unfold disj_apart; lia) SOK ltac:(unfold disj_apart; lia)
              regs H1 H2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl H10 H11 H12 H13 H14 H15)
    as (r1 & m1 & RUN1 & INV1 & Q10 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & AG1).
  replace (Z_to_bv 64 95044) with (0x17344 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct INV1 as [OUT1 GR1].
  assert (OUTM : forall a : word, ~ (s - 96 <= u a < s)%Z -> ~ (data <= u a < data + 4 * (wpl_of w 8 * h))%Z -> m1 a = m a).
  { intros a Ha Hb'. rewrite OUT1 by lia. apply (M2_outside m w h data s ret _ _ _ _ _ _ _ _ _ ltac:(lia)); lia. }
  assert (CH : forall a, m1 a <> m a -> scratch C s a \/ (data <= u a < data + 4 * (wpl_of w 8 * h))%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) data) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (data + 4 * (wpl_of w 8 * h))) as [B2|B2]; [right; lia |]];
      (left; unfold scratch;
       destruct (Z_lt_ge_dec (u a) (s - 96)); [exfalso; apply NE; apply OUTM; lia|];
       destruct (Z_lt_ge_dec (u a) s); [lia|]; exfalso; apply NE; apply OUTM; lia). }
  apply HK.
  - apply (W_local C A m md m1 s CK HW Hhi).
    + intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
      exists (Z_to_bv 64 data), (4 * (wpl_of w 8 * h))%Z. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld00 | lia]].
    + eapply mem_grows_trans; [apply M2_grows | exact GR1].
  - apply cs_kept_intro; csr; try reflexivity.
  - apply (POSTM_local C Ar A m md m1 s CK HW SUB). intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 data), (4 * (wpl_of w 8 * h))%Z. rewrite u_Z2bv by lia. split; [exact Ld | split; [exact Ld0 | lia]].
  - apply (PIXat_frame m); [exact PX|]. intros x Hx. apply OUTM; [lia|].
    pose proof (ai_live_disjoint A m (m_vmmaps md) _ _ _ _ (w_inv _ _ _ _ HW) Lp Ld NEpd) as DJ. rewrite !u_Z2bv in DJ by lia.
    pose proof (round16_ge (4 * (wpl_of w 8 * h)) ltac:(lia)) as R16. unfold round16 in DJ at 1. change ((64 + 15) / 16)%Z with 4%Z in DJ. lia.
  - intros a Ha Hb'. apply OUTM; [lia | exact Hb'].
  - exact Q10.
Qed.

(* [comment removed for export] *)
Definition FRnull (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)).

Section Segs.
Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Lemma sbv_null_seg : forall regs m (s : Z) (ret : word),
    (200000 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    rdn SEGS m (Z_to_bv 64 0x2aa40) 8 = Some (Z_to_le_bytes 8 0x2bab0) -> rdn SEGS m (Z_to_bv 64 0x2bab0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17344 : word) m rom) (mkst regs' (0x1536c : word) (FRnull m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x1097a /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
      /\ getr regs' 24 = getr regs 24
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRnull.
    eexists. split.
    - zv F_17248 D_17248 (Z_to_bv 64 (s - 96)).
      stepST F_1724c D_1724c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_17250 D_17250 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_17254 D_17254 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_17258 D_17258 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_1725c D_1725c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_17260 D_17260 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_17264 D_17264 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_17268 D_17268 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_1726c D_1726c (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_17270 D_17270 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepb_tk F_17274 D_17274 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17380 D_17380.                                   (* [comment removed for export] *)
      stepLD F_17384 D_17384 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
      stepLD F_17388 D_17388 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
      sn F_1738c D_1738c.                                   (* [comment removed for export] *)
      stepb_ft F_17390 D_17390 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17394 D_17394. sn F_17398 D_17398. sn F_1739c D_1739c. sn F_173a0 D_173a0. sn F_173a4 D_173a4.
      stepLD8 F_173a8 D_173a8 ret.
      stepLD8 F_173ac D_173ac (getr regs 8).
      stepLD8 F_173b0 D_173b0 (getr regs 9).
      stepLD8 F_173b4 D_173b4 (getr regs 18).
      stepLD8 F_173b8 D_173b8 (getr regs 19).
      stepLD8 F_173bc D_173bc (getr regs 20).
      stepLD8 F_173c0 D_173c0 (getr regs 21).
      stepLD8 F_173c4 D_173c4 (getr regs 22).
      stepLD8 F_173c8 D_173c8 (getr regs 23).
      stepLD8 F_173cc D_173cc (getr regs 24).
      zv F_173d0 D_173d0 (Z_to_bv 64 s).
      sn F_173d4 D_173d4.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_msg_pixs_nd : str16 0x10298 16. Proof. str16_tac. Qed.
Lemma str_pixSetBorderVal : str16 0x1097a 15. Proof. str16_tac. Qed.

Theorem pixSetBorderVal_null_W : pixSetBorderVal_null_contract.
Proof.
  unfold pixSetBorderVal_null_contract, PC_pixSetBorderVal, SBV_STACK.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (sbv_null_seg al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & AG1).
  replace (Z_to_bv 64 95044) with (0x17344 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FRnull m s ret regs) md /\ POSTM C A s m (FRnull m s ret regs)) by (unfold FRnull; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FRnull m s ret regs) in *.
  apply (returnErrorInt_W C A M1 md r1 s 0x10298 0x1097a 16 15 ret (Z_to_bv 64 1) S CK HW1 Q2 Hs16 ltac:(unfold LSF; lia) Hhi Q1 Hret
           Q10 Q11 Q12 str_msg_pixs_nd str_pixSetBorderVal).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PM1|].
    eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

End GrayDW.
(* [comment removed for export] *)
(* [comment removed for export] *)
Module G3E.
Section G3W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition FR7 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)).
(* [comment removed for export] *)
Definition FRwh (m : word -> option byte) (s w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 4 (Z_to_bv 64 h)).

(* [comment removed for export] *)
Definition cells7 (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v s5v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) /\
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 s5v).

Lemma cells7_FR7 : forall m s ret regs, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells7 (FR7 m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21).
Proof. intros m s ret regs Hs Hs64. unfold cells7, FR7. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Lemma cells7_out : forall m m' (s : Z) ret s0v s1v s2v s3v s4v s5v,
  (forall x : word, (s - 56 <= u x < s)%Z -> m' x = m x) -> (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells7 m s ret s0v s1v s2v s3v s4v s5v -> cells7 m' s ret s0v s1v s2v s3v s4v s5v.
Proof.
  intros m m' s ret s0v s1v s2v s3v s4v s5v OUT Hs Hs64 (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold cells7.
  repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]).
Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma g3w_A : forall regs m (s pixs : Z) (vs : pixv) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs vs -> p_d vs = 8%Z -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x20004 : word) m rom) (mkst regs' (0x15c44 : word) (FR7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x20040 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ getr regs' 18 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixs vs ret Hs Hs64 Hp PX Hd DJ SOK H2 H1 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (PX1 : PIXat (FR7 m s ret regs) pixs vs).
    { unfold FR7. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd.
    unfold FR7 in *. eexists. split.
    - zv F_1ff08 D_1ff08 (Z_to_bv 64 (s - 64)).
      stepST F_1ff0c D_1ff0c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_1ff10 D_1ff10 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1ff14 D_1ff14 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_1ff18 D_1ff18 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_1ff1c D_1ff1c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_1ff20 D_1ff20 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_1ff24 D_1ff24 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepb_ft F_1ff28 D_1ff28 ltac:(condZ).                (* [comment removed for export] *)
      zv F_1ff2c D_1ff2c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_1ff30 D_1ff30.                                   (* [comment removed for export] *)
      stepb_ft F_167b4 D_167b4 ltac:(condZ).
      stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
      stepret F_167bc D_167bc (0x20030 : word) ltac:(bveq).
      sn F_1ff34 D_1ff34.                                   (* [comment removed for export] *)
      stepb_ft F_1ff38 D_1ff38 ltac:(condZ).                (* [comment removed for export] *)
      zv F_1ff3c D_1ff3c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_1ff40 D_1ff40.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3w_B : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (1 <= pixd)%Z -> PIXat m pixs vs -> PIXat m pixd vd ->
    (pixs + 64 <= s - 64 \/ s <= pixs)%Z -> (pixd + 64 <= s - 64 \/ s <= pixd)%Z ->
    (0 <= p_w vs < 2 ^ 31)%Z -> (0 <= p_h vs < 2 ^ 31)%Z -> (0 <= p_wpl vs < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x20040 : word) m rom) (mkst regs' (0x2007c : word) (FRwh m s (p_w vs) (p_h vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = Z_to_bv 64 (p_data vs) /\ getr regs' 9 = Z_to_bv 64 (p_data vd)
      /\ getr regs' 19 = Z_to_bv 64 pixd /\ getr regs' 10 = Z_to_bv 64 (p_wpl vs)
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 12; 13; 14; 19]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hs Hs64 Hp Hpd PX PXd DJ DJd Rw Rh Rwpl SOK H2 H10 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (wf_data _ WF) as Rdat. pose proof (wf_data _ WFd) as Rdatd.
    set (Ma := wbytes (wbytes m (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 64)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
    set (Mb := wbytes Ma (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 (p_w vs)))).
    assert (PXa : PIXat Ma pixs vs).
    { unfold Ma. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    assert (PXb : PIXat Mb pixs vs).
    { unfold Mb. apply PIXat_out; [exact PXa | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (PXc : PIXat (FRwh m s (p_w vs) (p_h vs)) pixs vs).
    { unfold FRwh. fold Ma. fold Mb. apply PIXat_out; [exact PXb | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (PXdc : PIXat (FRwh m s (p_w vs) (p_h vs)) pixd vd).
    { unfold FRwh. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PXd. }
    pose proof (PIX_rd_w SEGS _ _ _ PXa) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PXb) as Ch.
    pose proof (PIX_rd_data SEGS _ _ _ PXc) as Cds. pose proof (PIX_rd_data SEGS _ _ _ PXdc) as Cdd. pose proof (PIX_rd_wpl SEGS _ _ _ PXc) as Cwpl.
    unfold FRwh in *. fold Ma in Cds, Cdd, Cwpl |- *. fold Mb in Cds, Cdd, Cwpl |- *.
    eexists. split.
    - zv F_1ff44 D_1ff44 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      zv F_1ff48 D_1ff48 (Z_to_bv 64 (s - 60)).             (* [comment removed for export] *)
      zv F_1ff4c D_1ff4c (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
      zv F_1ff50 D_1ff50 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_1ff54 D_1ff54.                                   (* [comment removed for export] *)
      sn F_1ff58 D_1ff58.                                   (* [comment removed for export] *)
      stepb_ft F_15d38 D_15d38 ltac:(condZ).
      stepST F_15d3c D_15d3c (Z_to_bv 64 (s - 60)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15d40 D_15d40 ltac:(condZ).
      stepST F_15d44 D_15d44 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_15d48 D_15d48 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_15d50 D_15d50 ltac:(condZ).
      stepb_ft F_15d54 D_15d54 ltac:(condZ).
      fold Ma.
      stepLD F_15d58 D_15d58 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; exact Cw) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_15d5c D_15d5c (Z_to_bv 64 (s - 60)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_15d60 D_15d60 ltac:(condZ).
      fold Mb.
      stepLD F_15d64 D_15d64 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_15d68 D_15d68 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      sn F_15d6c D_15d6c.                                   (* [comment removed for export] *)
      stepb_tk F_15d70 D_15d70 ltac:(condZ).                (* [comment removed for export] *)
      sn F_15d7c D_15d7c.                                   (* [comment removed for export] *)
      stepret F_15d80 D_15d80 (0x20058 : word) ltac:(bveq).
      zv F_1ff5c D_1ff5c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_1ff60 D_1ff60.                                   (* [comment removed for export] *)
      stepb_ft F_16874 D_16874 ltac:(condZ).
      stepLD F_16878 D_16878 (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; exact Cds) ltac:(apply W2Lib.lez8; lia).
      stepret F_1687c D_1687c (0x20060 : word) ltac:(bveq).
      zv F_1ff64 D_1ff64 (Z_to_bv 64 (p_data vs)).          (* [comment removed for export] *)
      zv F_1ff68 D_1ff68 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      zv F_1ff6c D_1ff6c (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      sn F_1ff70 D_1ff70.                                   (* [comment removed for export] *)
      stepb_ft F_16874 D_16874 ltac:(condZ).
      stepLD F_16878 D_16878 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdd) ltac:(apply W2Lib.lez8; lia).
      stepret F_1687c D_1687c (0x20070 : word) ltac:(bveq).
      zv F_1ff74 D_1ff74 (Z_to_bv 64 (p_data vd)).          (* [comment removed for export] *)
      zv F_1ff78 D_1ff78 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_1ff7c D_1ff7c.                                   (* [comment removed for export] *)
      stepb_ft F_15a3c D_15a3c ltac:(condZ).
      stepLD F_15a40 D_15a40 (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; exact Cwpl) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_wpl vs)) by lia.
      stepret F_15a44 D_15a44 (0x2007c : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3w_E : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v s5v : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells7 m s ret s0v s1v s2v s3v s4v s5v ->
    getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x20288 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v s5v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5 & R6 & R7) H2.
    eexists. split.
    - stepLD F_2018c D_2018c (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_20190 D_20190 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_20194 D_20194 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_20198 D_20198 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2019c D_2019c (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
      stepLD F_201a0 D_201a0 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; exact R6) ltac:(apply bytes_le_to_Z_8).
      stepLD F_201a4 D_201a4 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; exact R7) ltac:(apply bytes_le_to_Z_8).
      zv F_201a8 D_201a8 (Z_to_bv 64 s).
      stepret F_201ac D_201ac ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_msg_pixs_nd' : str16 0x10298 16. Proof. str16_tac. Qed.
Lemma str_pixErodeGray3h : str16 0x103ba 14. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Theorem gray3h_W : forall RKt RBt, pixCreateTemplate_sure_contract RKt RBt -> gray3h_contract PC_pixErodeGray3h RKt RBt.
Proof.
  intros RKt RBt PCT. unfold pixCreateTemplate_sure_contract, PC_pixCreateTemplate in PCT. unfold gray3h_contract, PC_pixErodeGray3h, G3H_STACK, TP14, gray8_shape.
  intros C A m md regs s pixs w h data cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PX (Hw1 & Hh1 & HOK) Lp Ld kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_of_range w 8 ltac:(lia) DV) as Hwr. pose proof (wpl8_ge w ltac:(lia)) as Hw4.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat. cbn [p_data hdv] in Rdat.
  set (n := (4 * (wpl_of w 8 * h))%Z) in *. assert (En : n = (4 * (wpl_of w 8 * h))%Z) by reflexivity.
  assert (Hn0 : (0 < n)%Z) by (assert (1 * 1 <= wpl_of w 8 * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Hn0) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  (* [comment removed for export] *)
  destruct (g3w_A al_rom regs m s pixs (hdv w h 8 0 data) ret ltac:(lia) ltac:(lia) ltac:(lia) PX eq_refl ltac:(lia)
              (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q18 & AG1).
  replace (Z_to_bv 64 0x20004) with (0x20004 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR7 m s ret regs) md /\ POSTM C A s m (FR7 m s ret regs)) by (unfold FR7; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR7 m s ret regs) in *.
  pose proof (cells7_FR7 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 64 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR7. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x15c44 : word) with (Z_to_bv 64 89156) by (apply bv_eq; reflexivity).
  apply (PCT C A M1 md r1 (s - 64)%Z pixs w h 8%Z data cv (Z_to_bv 64 0x20040) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold PCT_STACK, LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw1 Hh1 Lp kR bR Hrm Hrk Hrb).
  intros A1 m2 vm1 r2 pixd datad HWa CSa PMa Hres PT Hrm1.
  replace (Z_to_bv 64 0x20040) with (0x20040 : word) by (apply bv_eq; reflexivity).
  pose proof PT as (Gpd & TOPpd & ALpd & Gdd & TOPdd & ALdd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPdd, L1d.
  assert (LEQ : forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 datad -> live A1 q = live A q).
  { destruct CMR as [[_ LEQ] | (ad & _ & B & _)]; [exact LEQ | lia]. }
  assert (SUBa : sub_live A A1).
  { intros q k Lq. rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence]. }
  pose proof (SUBa _ _ Lp) as Lp1. pose proof (SUBa _ _ Ld) as Ld1.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (hdv w h 8 0 data)).
  { apply (PIXat_frame M1); [exact PXs1|]. intros x Hx. exact (LIVK_at A M1 m2 pixs 64 x (proj2 PMa) Lp ltac:(lia) ltac:(lia) Hx). }
  assert (CE2 : cells7 m2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  { destruct CE1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold cells7.
    rewrite !(FRM_rdn16 C (s - 64) M1 m2 _ 8 CK (proj1 PMa)) by (cbn; lia). repeat split; assumption. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 pixs) by (csr; reflexivity).
  (* [comment removed for export] *)
  destruct (g3w_B al_rom r2 m2 s pixs pixd (hdv w h 8 0 data) (hdv w h 8 0 datad) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PXs2 PXd
              ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A1 m2 _ (s - 64) 8 CK HWa ltac:(lia) ltac:(cbn; lia)) E2 Hres E18)
    as (r3 & RUN3 & V2 & V8 & V9 & V19 & V10 & AG3). cbn [p_w p_h p_wpl p_data hdv] in RUN3, V8, V9, V10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (WP3 : W C A1 (FRwh m2 s w h) (with_vmmaps vm1 md) /\ POSTM C A1 s m2 (FRwh m2 s w h)) by (unfold FRwh; wp_win CK).
  destruct WP3 as [HW3 PM3]. set (M3 := FRwh m2 s w h) in *.
  assert (OUT3 : forall x : word, ~ (s - 64 <= u x < s - 56)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. unfold FRwh. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Ch3 : rdn SEGS M3 (Z_to_bv 64 (s - 64)) 4 = Some (Z_to_le_bytes 4 h)).
  { subst M3. unfold FRwh. replace (Z_to_le_bytes 4 h) with (word_to_le_bytes 4 (Z_to_bv 64 h)) by (unfold word_to_le_bytes; rewrite u_Z2bv by lia; reflexivity).
    apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (Cw3 : rdn SEGS M3 (Z_to_bv 64 (s - 64 + 4)) 4 = Some (Z_to_le_bytes 4 w)).
  { subst M3. unfold FRwh. replace (Z_to_le_bytes 4 w) with (word_to_le_bytes 4 (Z_to_bv 64 w)) by (unfold word_to_le_bytes; rewrite u_Z2bv by lia; reflexivity).
    replace (s - 64 + 4)%Z with (s - 60)%Z by lia. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  (* [comment removed for export] *)
  destruct (O14Gray3h.g3_run M3 al_rom w h (wpl_of w 8) data datad (s - 64) pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ch3 Cw3
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALd]]) ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALdd]])
              (blk_sok C A1 M3 _ data n CK HW3 Ld1 ltac:(lia) ltac:(lia) ltac:(lia)) (blk_sok C A1 M3 _ datad n CK HW3 L1d ltac:(lia) ltac:(lia) ltac:(lia))
              ltac:(unfold disj_apart; lia) r3 V2 V8 V9 V19 V10)
    as (r4 & M4 & RUN4 & INV4 & X2 & X10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  destruct INV4 as [OUT4 GR4].
  assert (CH : forall a, M4 a <> M3 a -> scratch C s a \/ (exists p k, live A1 p = Some k /\ live A p = None /\ (u p <= u a < u p + k)%Z)).
  { intros a NE. right. exists (Z_to_bv 64 datad), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L0d|]].
    destruct (Z_lt_ge_dec (u a) datad); [exfalso; apply NE; apply OUT4; lia|].
    destruct (Z_lt_ge_dec (u a) (datad + n)); [lia | exfalso; apply NE; apply OUT4; lia]. }
  assert (HW4 : W C A1 M4 (with_vmmaps vm1 md)).
  { apply (W_local C A1 M3 _ M4 s CK HW3 Hhi); [| exact GR4].
    intros a NE. destruct (CH a NE) as [X|(p & k & L & _ & R)]; [left; exact X | right; exists p, k]. split; [exact L | split; [| exact R]].
    destruct (bv_eq_dec _ p (Z_to_bv 64 datad)) as [->|NE']; [exact L00d|].
    exfalso. apply NE. apply OUT4.
    pose proof (ai_live_disjoint A1 M3 _ _ _ _ _ (w_inv _ _ _ _ HW3) L L1d NE') as D. rewrite u_Z2bv in D by lia.
    pose proof (ai_live_hull A1 M3 _ _ _ (w_inv _ _ _ _ HW3) L) as (Hk0 & _). pose proof (round16_ge k Hk0).
    pose proof (round16_ge n ltac:(lia)). lia. }
  assert (PM4 : POSTM C A s m M4).
  { eapply POSTM_trans; [exact PMa'|]. eapply POSTM_trans; [apply (POSTM_sub C A A1 s m2 M3 SUBa PM3)|].
    exact (POSTM_local C A A1 M3 _ M4 s CK HW3 SUBa CH). }
  assert (EQ4 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 datad -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z ->
                  (p + k <= s - 64)%Z -> (p <= u x < p + k)%Z -> M4 x = m2 x).
  { intros p k x L NE' G0 K0 Hlo' Hx. rewrite OUT4; [apply OUT3; lia|].
    pose proof (blk_apart C A1 M3 _ _ _ _ _ CK HW3 L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (apply zbv_ne2; lia).
  assert (NEspd : Z_to_bv 64 pixs <> Z_to_bv 64 datad) by (intros E; rewrite E in Lp; rewrite Lp in L0d; discriminate).
  assert (PXd4 : PIXat M4 pixd (hdv w h 8 0 datad)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ4 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) ltac:(lia) Hx)]).
  assert (PXs4 : PIXat M4 pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m2); [exact PXs2 | intros x Hx; exact (EQ4 pixs 64%Z x Lp1 NEspd ltac:(lia) ltac:(lia) ltac:(lia) Hx)]).
  assert (CE4 : cells7 M4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  { apply (cells7_out m2 M4 s); [| lia | lia | exact CE2]. intros x Hx. rewrite OUT4 by lia. apply OUT3. lia. }
  destruct (g3w_E al_rom r4 M4 s ret _ _ _ _ _ _ ltac:(lia) ltac:(lia) Hret CE4 X2) as (r5 & RUN5 & Y2 & Y1 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
  apply (HK A1 M4 vm1 r5 pixd datad HW4).
  - apply cs_kept_intro; csr; try reflexivity.
  - exact PM4.
  - rewrite (AG5 10) by (cbv; intuition discriminate). exact X10.
  - refine (conj Gpd (conj TOPpd (conj ALpd (conj Gdd (conj _ (conj ALdd (conj NEpd (conj L0p (conj L0d (conj L00p (conj L00d (conj L1p (conj _ (conj PXd4 _)))))))))))))).
    + exact TOPdd.
    + exact L1d.
    + left. split; [reflexivity | exact LEQ].
  - exact PXs4.
  - exact Hrm1.
Qed.

Section SegsN.
Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Lemma g3w_null_seg : forall regs m (s : Z) (ret : word),
    (200000 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    rdn SEGS m (Z_to_bv 64 0x2aa40) 8 = Some (Z_to_le_bytes 8 0x2bab0) -> rdn SEGS m (Z_to_bv 64 0x2bab0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x20004 : word) m rom) (mkst regs' (0x1543c : word) (FR7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x103ba /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FR7.
    eexists. split.
    - zv F_1ff08 D_1ff08 (Z_to_bv 64 (s - 64)).
      stepST F_1ff0c D_1ff0c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_1ff10 D_1ff10 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_1ff14 D_1ff14 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_1ff18 D_1ff18 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_1ff1c D_1ff1c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_1ff20 D_1ff20 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_1ff24 D_1ff24 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepb_tk F_1ff28 D_1ff28 ltac:(condZ).                (* [comment removed for export] *)
      sn F_20114 D_20114.                                   (* [comment removed for export] *)
      stepLD F_20118 D_20118 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
      stepLD F_2011c D_2011c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
      sn F_20120 D_20120.                                   (* [comment removed for export] *)
      stepb_ft F_20124 D_20124 ltac:(condZ).                (* [comment removed for export] *)
      sn F_20128 D_20128. sn F_2012c D_2012c. sn F_20130 D_20130.
      sn F_20150 D_20150. sn F_20154 D_20154. sn F_20158 D_20158.
      stepLD8 F_2015c D_2015c ret.
      stepLD8 F_20160 D_20160 (getr regs 8).
      stepLD8 F_20164 D_20164 (getr regs 9).
      stepLD8 F_20168 D_20168 (getr regs 18).
      stepLD8 F_2016c D_2016c (getr regs 19).
      stepLD8 F_20170 D_20170 (getr regs 20).
      stepLD8 F_20174 D_20174 (getr regs 21).
      zv F_20178 D_20178 (Z_to_bv 64 s).
      sn F_2017c D_2017c.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsN.

Theorem gray3h_null_W : gray3h_null_contract PC_pixErodeGray3h.
Proof.
  unfold gray3h_null_contract, PC_pixErodeGray3h, G3H_STACK.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (g3w_null_seg al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & AG1).
  replace (Z_to_bv 64 0x20004) with (0x20004 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR7 m s ret regs) md /\ POSTM C A s m (FR7 m s ret regs)) by (unfold FR7; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR7 m s ret regs) in *.
  apply (returnErrorPtr_W C A M1 md r1 s 0x10298 0x103ba 16 14 ret (Z_to_bv 64 0) S CK HW1 Q2 Hs16 ltac:(unfold LSF; lia) Hhi Q1 Hret
           Q10 Q11 Q12 str_msg_pixs_nd' str_pixErodeGray3h).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PM1|].
    eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

End G3W.
End G3E.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module G3D.
Section G3W.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition FR7 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)).
(* [comment removed for export] *)
Definition FRwh (m : word -> option byte) (s w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 4 (Z_to_bv 64 h)).

(* [comment removed for export] *)
Definition cells7 (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v s5v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) /\
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 s5v).

Lemma cells7_FR7 : forall m s ret regs, (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells7 (FR7 m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21).
Proof. intros m s ret regs Hs Hs64. unfold cells7, FR7. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Lemma cells7_out : forall m m' (s : Z) ret s0v s1v s2v s3v s4v s5v,
  (forall x : word, (s - 56 <= u x < s)%Z -> m' x = m x) -> (64 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells7 m s ret s0v s1v s2v s3v s4v s5v -> cells7 m' s ret s0v s1v s2v s3v s4v s5v.
Proof.
  intros m m' s ret s0v s1v s2v s3v s4v s5v OUT Hs Hs64 (R1 & R2 & R3 & R4 & R5 & R6 & R7). unfold cells7.
  repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]).
Qed.

Section Segs.
Variable rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma g3w_A : forall regs m (s pixs : Z) (vs : pixv) (ret : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> PIXat m pixs vs -> p_d vs = 8%Z -> (pixs + 64 <= s - 64 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x20854 : word) m rom) (mkst regs' (0x15c44 : word) (FR7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 1 = Z_to_bv 64 0x20890 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ getr regs' 18 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixs vs ret Hs Hs64 Hp PX Hd DJ SOK H2 H1 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (PX1 : PIXat (FR7 m s ret regs) pixs vs).
    { unfold FR7. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd.
    unfold FR7 in *. eexists. split.
    - zv F_20758 D_20758 (Z_to_bv 64 (s - 64)).
      stepST F_2075c D_2075c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_20760 D_20760 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_20764 D_20764 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_20768 D_20768 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_2076c D_2076c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_20770 D_20770 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_20774 D_20774 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepb_ft F_20778 D_20778 ltac:(condZ).                (* [comment removed for export] *)
      zv F_2077c D_2077c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_20780 D_20780.                                   (* [comment removed for export] *)
      stepb_ft F_167b4 D_167b4 ltac:(condZ).
      stepLD F_167b8 D_167b8 (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
      stepret F_167bc D_167bc (0x20880 : word) ltac:(bveq).
      sn F_20784 D_20784.                                   (* [comment removed for export] *)
      stepb_ft F_20788 D_20788 ltac:(condZ).                (* [comment removed for export] *)
      zv F_2078c D_2078c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_20790 D_20790.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3w_B : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (128 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (1 <= pixd)%Z -> PIXat m pixs vs -> PIXat m pixd vd ->
    (pixs + 64 <= s - 64 \/ s <= pixs)%Z -> (pixd + 64 <= s - 64 \/ s <= pixd)%Z ->
    (0 <= p_w vs < 2 ^ 31)%Z -> (0 <= p_h vs < 2 ^ 31)%Z -> (0 <= p_wpl vs < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 64)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 64) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x20890 : word) m rom) (mkst regs' (0x208cc : word) (FRwh m s (p_w vs) (p_h vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 64) /\ getr regs' 8 = Z_to_bv 64 (p_data vs) /\ getr regs' 9 = Z_to_bv 64 (p_data vd)
      /\ getr regs' 19 = Z_to_bv 64 pixd /\ getr regs' 10 = Z_to_bv 64 (p_wpl vs)
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 12; 13; 14; 19]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hs Hs64 Hp Hpd PX PXd DJ DJd Rw Rh Rwpl SOK H2 H10 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (wf_data _ WF) as Rdat. pose proof (wf_data _ WFd) as Rdatd.
    set (Ma := wbytes (wbytes m (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 64)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
    set (Mb := wbytes Ma (Z_to_bv 64 (s - 60)) (word_to_le_bytes 4 (Z_to_bv 64 (p_w vs)))).
    assert (PXa : PIXat Ma pixs vs).
    { unfold Ma. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    assert (PXb : PIXat Mb pixs vs).
    { unfold Mb. apply PIXat_out; [exact PXa | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (PXc : PIXat (FRwh m s (p_w vs) (p_h vs)) pixs vs).
    { unfold FRwh. fold Ma. fold Mb. apply PIXat_out; [exact PXb | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (PXdc : PIXat (FRwh m s (p_w vs) (p_h vs)) pixd vd).
    { unfold FRwh. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PXd. }
    pose proof (PIX_rd_w SEGS _ _ _ PXa) as Cw. pose proof (PIX_rd_h SEGS _ _ _ PXb) as Ch.
    pose proof (PIX_rd_data SEGS _ _ _ PXc) as Cds. pose proof (PIX_rd_data SEGS _ _ _ PXdc) as Cdd. pose proof (PIX_rd_wpl SEGS _ _ _ PXc) as Cwpl.
    unfold FRwh in *. fold Ma in Cds, Cdd, Cwpl |- *. fold Mb in Cds, Cdd, Cwpl |- *.
    eexists. split.
    - zv F_20794 D_20794 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      zv F_20798 D_20798 (Z_to_bv 64 (s - 60)).             (* [comment removed for export] *)
      zv F_2079c D_2079c (Z_to_bv 64 (s - 64)).             (* [comment removed for export] *)
      zv F_207a0 D_207a0 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_207a4 D_207a4.                                   (* [comment removed for export] *)
      sn F_207a8 D_207a8.                                   (* [comment removed for export] *)
      stepb_ft F_15d38 D_15d38 ltac:(condZ).
      stepST F_15d3c D_15d3c (Z_to_bv 64 (s - 60)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_ft F_15d40 D_15d40 ltac:(condZ).
      stepST F_15d44 D_15d44 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_15d48 D_15d48 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_15d50 D_15d50 ltac:(condZ).
      stepb_ft F_15d54 D_15d54 ltac:(condZ).
      fold Ma.
      stepLD F_15d58 D_15d58 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; exact Cw) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_15d5c D_15d5c (Z_to_bv 64 (s - 60)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_15d60 D_15d60 ltac:(condZ).
      fold Mb.
      stepLD F_15d64 D_15d64 (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_15d68 D_15d68 (Z_to_bv 64 (s - 64)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      sn F_15d6c D_15d6c.                                   (* [comment removed for export] *)
      stepb_tk F_15d70 D_15d70 ltac:(condZ).                (* [comment removed for export] *)
      sn F_15d7c D_15d7c.                                   (* [comment removed for export] *)
      stepret F_15d80 D_15d80 (0x208a8 : word) ltac:(bveq).
      zv F_207ac D_207ac (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_207b0 D_207b0.                                   (* [comment removed for export] *)
      stepb_ft F_16874 D_16874 ltac:(condZ).
      stepLD F_16878 D_16878 (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; exact Cds) ltac:(apply W2Lib.lez8; lia).
      stepret F_1687c D_1687c (0x208b0 : word) ltac:(bveq).
      zv F_207b4 D_207b4 (Z_to_bv 64 (p_data vs)).          (* [comment removed for export] *)
      zv F_207b8 D_207b8 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      zv F_207bc D_207bc (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      sn F_207c0 D_207c0.                                   (* [comment removed for export] *)
      stepb_ft F_16874 D_16874 ltac:(condZ).
      stepLD F_16878 D_16878 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdd) ltac:(apply W2Lib.lez8; lia).
      stepret F_1687c D_1687c (0x208c0 : word) ltac:(bveq).
      zv F_207c4 D_207c4 (Z_to_bv 64 (p_data vd)).          (* [comment removed for export] *)
      zv F_207c8 D_207c8 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_207cc D_207cc.                                   (* [comment removed for export] *)
      stepb_ft F_15a3c D_15a3c ltac:(condZ).
      stepLD F_15a40 D_15a40 (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; exact Cwpl) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_wpl vs)) by lia.
      stepret F_15a44 D_15a44 (0x208cc : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3w_E : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v s5v : word),
    (64 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells7 m s ret s0v s1v s2v s3v s4v s5v ->
    getr regs 2 = Z_to_bv 64 (s - 64) ->
    exists regs',
      msteps SEGS (mkst regs (0x20ad8 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v s5v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5 & R6 & R7) H2.
    eexists. split.
    - stepLD F_209dc D_209dc (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_209e0 D_209e0 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_209e4 D_209e4 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_209e8 D_209e8 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
      stepLD F_209ec D_209ec (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
      stepLD F_209f0 D_209f0 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; exact R6) ltac:(apply bytes_le_to_Z_8).
      stepLD F_209f4 D_209f4 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; exact R7) ltac:(apply bytes_le_to_Z_8).
      zv F_209f8 D_209f8 (Z_to_bv 64 s).
      stepret F_209fc D_209fc ret ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.

Lemma str_msg_pixs_nd' : str16 0x10298 16. Proof. str16_tac. Qed.
Lemma str_pixDilateGray3h : str16 0x10bf2 15. Proof. str16_tac. Qed.

(* [comment removed for export] *)
Theorem gray3h_W : forall RKt RBt, pixCreateTemplate_sure_contract RKt RBt -> gray3h_contract PC_pixDilateGray3h RKt RBt.
Proof.
  intros RKt RBt PCT. unfold pixCreateTemplate_sure_contract, PC_pixCreateTemplate in PCT. unfold gray3h_contract, PC_pixDilateGray3h, G3H_STACK, TP14, gray8_shape.
  intros C A m md regs s pixs w h data cv ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 PX (Hw1 & Hh1 & HOK) Lp Ld kR bR Hrm Hrk Hrb HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_of_range w 8 ltac:(lia) DV) as Hwr. pose proof (wpl8_ge w ltac:(lia)) as Hw4.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat. cbn [p_data hdv] in Rdat.
  set (n := (4 * (wpl_of w 8 * h))%Z) in *. assert (En : n = (4 * (wpl_of w 8 * h))%Z) by reflexivity.
  assert (Hn0 : (0 < n)%Z) by (assert (1 * 1 <= wpl_of w 8 * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Hn0) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  (* [comment removed for export] *)
  destruct (g3w_A al_rom regs m s pixs (hdv w h 8 0 data) ret ltac:(lia) ltac:(lia) ltac:(lia) PX eq_refl ltac:(lia)
              (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q18 & AG1).
  replace (Z_to_bv 64 0x20854) with (0x20854 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR7 m s ret regs) md /\ POSTM C A s m (FR7 m s ret regs)) by (unfold FR7; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR7 m s ret regs) in *.
  pose proof (cells7_FR7 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 64 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR7. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x3be10) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x15c44 : word) with (Z_to_bv 64 89156) by (apply bv_eq; reflexivity).
  apply (PCT C A M1 md r1 (s - 64)%Z pixs w h 8%Z data cv (Z_to_bv 64 0x20890) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold PCT_STACK, LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw1 Hh1 Lp kR bR Hrm Hrk Hrb).
  intros A1 m2 vm1 r2 pixd datad HWa CSa PMa Hres PT Hrm1.
  replace (Z_to_bv 64 0x20890) with (0x20890 : word) by (apply bv_eq; reflexivity).
  pose proof PT as (Gpd & TOPpd & ALpd & Gdd & TOPdd & ALdd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPdd, L1d.
  assert (LEQ : forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 datad -> live A1 q = live A q).
  { destruct CMR as [[_ LEQ] | (ad & _ & B & _)]; [exact LEQ | lia]. }
  assert (SUBa : sub_live A A1).
  { intros q k Lq. rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence]. }
  pose proof (SUBa _ _ Lp) as Lp1. pose proof (SUBa _ _ Ld) as Ld1.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (hdv w h 8 0 data)).
  { apply (PIXat_frame M1); [exact PXs1|]. intros x Hx. exact (LIVK_at A M1 m2 pixs 64 x (proj2 PMa) Lp ltac:(lia) ltac:(lia) Hx). }
  assert (CE2 : cells7 m2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  { destruct CE1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7). unfold cells7.
    rewrite !(FRM_rdn16 C (s - 64) M1 m2 _ 8 CK (proj1 PMa)) by (cbn; lia). repeat split; assumption. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 pixs) by (csr; reflexivity).
  (* [comment removed for export] *)
  destruct (g3w_B al_rom r2 m2 s pixs pixd (hdv w h 8 0 data) (hdv w h 8 0 datad) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PXs2 PXd
              ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A1 m2 _ (s - 64) 8 CK HWa ltac:(lia) ltac:(cbn; lia)) E2 Hres E18)
    as (r3 & RUN3 & V2 & V8 & V9 & V19 & V10 & AG3). cbn [p_w p_h p_wpl p_data hdv] in RUN3, V8, V9, V10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (WP3 : W C A1 (FRwh m2 s w h) (with_vmmaps vm1 md) /\ POSTM C A1 s m2 (FRwh m2 s w h)) by (unfold FRwh; wp_win CK).
  destruct WP3 as [HW3 PM3]. set (M3 := FRwh m2 s w h) in *.
  assert (OUT3 : forall x : word, ~ (s - 64 <= u x < s - 56)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. unfold FRwh. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Ch3 : rdn SEGS M3 (Z_to_bv 64 (s - 64)) 4 = Some (Z_to_le_bytes 4 h)).
  { subst M3. unfold FRwh. replace (Z_to_le_bytes 4 h) with (word_to_le_bytes 4 (Z_to_bv 64 h)) by (unfold word_to_le_bytes; rewrite u_Z2bv by lia; reflexivity).
    apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (Cw3 : rdn SEGS M3 (Z_to_bv 64 (s - 64 + 4)) 4 = Some (Z_to_le_bytes 4 w)).
  { subst M3. unfold FRwh. replace (Z_to_le_bytes 4 w) with (word_to_le_bytes 4 (Z_to_bv 64 w)) by (unfold word_to_le_bytes; rewrite u_Z2bv by lia; reflexivity).
    replace (s - 64 + 4)%Z with (s - 60)%Z by lia. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  (* [comment removed for export] *)
  destruct (O14Gray3hD.g3_run M3 al_rom w h (wpl_of w 8) data datad (s - 64) pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ch3 Cw3
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALd]]) ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALdd]])
              (blk_sok C A1 M3 _ data n CK HW3 Ld1 ltac:(lia) ltac:(lia) ltac:(lia)) (blk_sok C A1 M3 _ datad n CK HW3 L1d ltac:(lia) ltac:(lia) ltac:(lia))
              ltac:(unfold disj_apart; lia) r3 V2 V8 V9 V19 V10)
    as (r4 & M4 & RUN4 & INV4 & X2 & X10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  destruct INV4 as [OUT4 GR4].
  assert (CH : forall a, M4 a <> M3 a -> scratch C s a \/ (exists p k, live A1 p = Some k /\ live A p = None /\ (u p <= u a < u p + k)%Z)).
  { intros a NE. right. exists (Z_to_bv 64 datad), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L0d|]].
    destruct (Z_lt_ge_dec (u a) datad); [exfalso; apply NE; apply OUT4; lia|].
    destruct (Z_lt_ge_dec (u a) (datad + n)); [lia | exfalso; apply NE; apply OUT4; lia]. }
  assert (HW4 : W C A1 M4 (with_vmmaps vm1 md)).
  { apply (W_local C A1 M3 _ M4 s CK HW3 Hhi); [| exact GR4].
    intros a NE. destruct (CH a NE) as [X|(p & k & L & _ & R)]; [left; exact X | right; exists p, k]. split; [exact L | split; [| exact R]].
    destruct (bv_eq_dec _ p (Z_to_bv 64 datad)) as [->|NE']; [exact L00d|].
    exfalso. apply NE. apply OUT4.
    pose proof (ai_live_disjoint A1 M3 _ _ _ _ _ (w_inv _ _ _ _ HW3) L L1d NE') as D. rewrite u_Z2bv in D by lia.
    pose proof (ai_live_hull A1 M3 _ _ _ (w_inv _ _ _ _ HW3) L) as (Hk0 & _). pose proof (round16_ge k Hk0).
    pose proof (round16_ge n ltac:(lia)). lia. }
  assert (PM4 : POSTM C A s m M4).
  { eapply POSTM_trans; [exact PMa'|]. eapply POSTM_trans; [apply (POSTM_sub C A A1 s m2 M3 SUBa PM3)|].
    exact (POSTM_local C A A1 M3 _ M4 s CK HW3 SUBa CH). }
  assert (EQ4 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 datad -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z ->
                  (p + k <= s - 64)%Z -> (p <= u x < p + k)%Z -> M4 x = m2 x).
  { intros p k x L NE' G0 K0 Hlo' Hx. rewrite OUT4; [apply OUT3; lia|].
    pose proof (blk_apart C A1 M3 _ _ _ _ _ CK HW3 L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia. lia. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (apply zbv_ne2; lia).
  assert (NEspd : Z_to_bv 64 pixs <> Z_to_bv 64 datad) by (intros E; rewrite E in Lp; rewrite Lp in L0d; discriminate).
  assert (PXd4 : PIXat M4 pixd (hdv w h 8 0 datad)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ4 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) ltac:(lia) Hx)]).
  assert (PXs4 : PIXat M4 pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m2); [exact PXs2 | intros x Hx; exact (EQ4 pixs 64%Z x Lp1 NEspd ltac:(lia) ltac:(lia) ltac:(lia) Hx)]).
  assert (CE4 : cells7 M4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)).
  { apply (cells7_out m2 M4 s); [| lia | lia | exact CE2]. intros x Hx. rewrite OUT4 by lia. apply OUT3. lia. }
  destruct (g3w_E al_rom r4 M4 s ret _ _ _ _ _ _ ltac:(lia) ltac:(lia) Hret CE4 X2) as (r5 & RUN5 & Y2 & Y1 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & AG5).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN5 |].
  apply (HK A1 M4 vm1 r5 pixd datad HW4).
  - apply cs_kept_intro; csr; try reflexivity.
  - exact PM4.
  - rewrite (AG5 10) by (cbv; intuition discriminate). exact X10.
  - refine (conj Gpd (conj TOPpd (conj ALpd (conj Gdd (conj _ (conj ALdd (conj NEpd (conj L0p (conj L0d (conj L00p (conj L00d (conj L1p (conj _ (conj PXd4 _)))))))))))))).
    + exact TOPdd.
    + exact L1d.
    + left. split; [reflexivity | exact LEQ].
  - exact PXs4.
  - exact Hrm1.
Qed.

Section SegsN.
Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Lemma g3w_null_seg : forall regs m (s : Z) (ret : word),
    (200000 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 64)) 64 = true ->
    rdn SEGS m (Z_to_bv 64 0x2aa40) 8 = Some (Z_to_le_bytes 8 0x2bab0) -> rdn SEGS m (Z_to_bv 64 0x2bab0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x20854 : word) m rom) (mkst regs' (0x1543c : word) (FR7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10bf2 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FR7.
    eexists. split.
    - zv F_20758 D_20758 (Z_to_bv 64 (s - 64)).
      stepST F_2075c D_2075c (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_20760 D_20760 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_20764 D_20764 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_20768 D_20768 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_2076c D_2076c (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_20770 D_20770 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_20774 D_20774 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepb_tk F_20778 D_20778 ltac:(condZ).                (* [comment removed for export] *)
      sn F_20964 D_20964.                                   (* [comment removed for export] *)
      stepLD F_20968 D_20968 (Z_to_le_bytes 8 0x2bab0) (Z_to_bv 64 0x2bab0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
      stepLD F_2096c D_2096c (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
      sn F_20970 D_20970.                                   (* [comment removed for export] *)
      stepb_ft F_20974 D_20974 ltac:(condZ).                (* [comment removed for export] *)
      sn F_20978 D_20978. sn F_2097c D_2097c. sn F_20980 D_20980.
      sn F_209a0 D_209a0. sn F_209a4 D_209a4. sn F_209a8 D_209a8.
      stepLD8 F_209ac D_209ac ret.
      stepLD8 F_209b0 D_209b0 (getr regs 8).
      stepLD8 F_209b4 D_209b4 (getr regs 9).
      stepLD8 F_209b8 D_209b8 (getr regs 18).
      stepLD8 F_209bc D_209bc (getr regs 19).
      stepLD8 F_209c0 D_209c0 (getr regs 20).
      stepLD8 F_209c4 D_209c4 (getr regs 21).
      zv F_209c8 D_209c8 (Z_to_bv 64 s).
      sn F_209cc D_209cc.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsN.

Theorem gray3h_null_W : gray3h_null_contract PC_pixDilateGray3h.
Proof.
  unfold gray3h_null_contract, PC_pixDilateGray3h, G3H_STACK.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (g3w_null_seg al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & AG1).
  replace (Z_to_bv 64 0x20854) with (0x20854 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR7 m s ret regs) md /\ POSTM C A s m (FR7 m s ret regs)) by (unfold FR7; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR7 m s ret regs) in *.
  apply (returnErrorPtr_W C A M1 md r1 s 0x10298 0x10bf2 16 15 ret (Z_to_bv 64 0) S CK HW1 Q2 Hs16 ltac:(unfold LSF; lia) Hhi Q1 Hret
           Q10 Q11 Q12 str_msg_pixs_nd' str_pixDilateGray3h).
  intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
  apply (HK m4 r5 HW4).
  - apply cs_kept_intro; csr; try reflexivity.
  - eapply POSTM_trans; [exact PM1|].
    eapply (POSTM_range C A M1 _ m4); [exact CK | exact HW1 | exact OUT4 | lia | lia | lia].
  - exact A10.
Qed.

End G3W.
End G3D.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
