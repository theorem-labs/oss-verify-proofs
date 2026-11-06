(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptRoom.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptStderr V14LeptBase.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14CL7a.
Import V14CL7a.V14LeptErr.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require Import V14LeptPixHdr V14LeptCmap2 V14LeptPixCopy V14LeptGrayD_iface V14SetBorder V14_code_gmD.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.V14 Require V14Gray3h V14Gray3hD.
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
Context {PINS : @LeptPins AL LLU16} {P16 : V14Pins}.
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
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_of_range w 8 ltac:(lia) DV) as Hwr. pose proof (wpl8_ge w ltac:(lia)) as Hw4.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  assert (Hwplh : (0 < 4 * (wpl_of w 8 * h))%Z) by (assert (1 * 1 <= wpl_of w 8 * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Hwplh) as [Gd TOPd].
  pose proof (wf_data _ WF) as Rdat. cbn [p_data hdv] in Rdat. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  assert (SOKd : store_ok SEGS m (Z_to_bv 64 data) (Z.to_nat (4 * (wpl_of w 8 * h))) = true).
  { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
    unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
    destruct (blk_byte C A m md (Z_to_bv 64 data) _ x CK HW Ld ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  destruct (sbv_run m al_rom pixs w h (wpl_of w 8) data s left right top bot val ret
              (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
              ltac:(lia) ltac:(unfold is_aligned; rewrite <- (Z.add_0_r pixs); apply mod16_plus_mod8; [exact ALp | reflexivity])
              ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold is_aligned; exact Hs16) Hret Hl Hr Ht Hb Htb
              (PIX_rd_w SEGS _ _ _ PX) (PIX_rd_h SEGS _ _ _ PX) (PIX_rd_d SEGS _ _ _ PX) (PIX_rd_wpl SEGS _ _ _ PX) (PIX_rd_data SEGS _ _ _ PX)
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALd]]) SOKd ltac:(unfold disj_apart; lia) SOK ltac:(unfold disj_apart; lia)
              regs H1 H2 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl H10 H11 H12 H13 H14 H15)
    as (r1 & m1 & RUN1 & INV1 & Q10 & Q1 & Q2 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & AG1).
  replace (Z_to_bv 64 97020) with (0x17afc : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  destruct INV1 as [OUT1 GR1].
  assert (OUTM : forall a : word, ~ (s - 112 <= u a < s)%Z -> ~ (data <= u a < data + 4 * (wpl_of w 8 * h))%Z -> m1 a = m a).
  { intros a Ha Hb'. rewrite OUT1 by lia. apply (M2_outside m w h data s ret _ _ _ _ _ _ _ _ _ _ ltac:(lia)); lia. }
  assert (CH : forall a, m1 a <> m a -> scratch C s a \/ (data <= u a < data + 4 * (wpl_of w 8 * h))%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) data) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (data + 4 * (wpl_of w 8 * h))) as [B2|B2]; [right; lia |]];
      (left; unfold scratch;
       destruct (Z_lt_ge_dec (u a) (s - 112)); [exfalso; apply NE; apply OUTM; lia|];
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
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)).

Section Segs.
Variable rom : word -> option byte.
  (* [comment removed for export] *)
  Lemma sbv_null_seg : forall regs m (s : Z) (ret : word),
    (250000 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 112)) 112 = true ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x17afc : word) m rom) (mkst regs' (0x1547c : word) (FRnull m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x1097a /\ getr regs' 12 = Z_to_bv 64 1
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19
      /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23
      /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FRnull.
    eexists. split.
    - zv F_17a00 D_17a00 (Z_to_bv 64 (s - 112)).
      stepST F_17a04 D_17a04 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_17a08 D_17a08 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_17a0c D_17a0c (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_17a10 D_17a10 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_17a14 D_17a14 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_17a18 D_17a18 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_17a1c D_17a1c (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_17a20 D_17a20 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_17a24 D_17a24 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_17a28 D_17a28 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_17a2c D_17a2c (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepb_tk F_17a30 D_17a30 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17b98 D_17b98.                                   (* [comment removed for export] *)
      stepLD F_17b9c D_17b9c (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
      stepLD F_17ba0 D_17ba0 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
      sn F_17ba4 D_17ba4.                                   (* [comment removed for export] *)
      stepb_ft F_17ba8 D_17ba8 ltac:(condZ).                (* [comment removed for export] *)
      sn F_17bac D_17bac. sn F_17bb0 D_17bb0. sn F_17bb4 D_17bb4. sn F_17bb8 D_17bb8. sn F_17bbc D_17bbc.
      stepLD8 F_17bc0 D_17bc0 ret.
      stepLD8 F_17bc4 D_17bc4 (getr regs 8).
      stepLD8 F_17bc8 D_17bc8 (getr regs 9).
      stepLD8 F_17bcc D_17bcc (getr regs 18).
      stepLD8 F_17bd0 D_17bd0 (getr regs 19).
      stepLD8 F_17bd4 D_17bd4 (getr regs 20).
      stepLD8 F_17bd8 D_17bd8 (getr regs 21).
      stepLD8 F_17bdc D_17bdc (getr regs 22).
      stepLD8 F_17be0 D_17be0 (getr regs 23).
      stepLD8 F_17be4 D_17be4 (getr regs 24).
      stepLD8 F_17be8 D_17be8 (getr regs 25).
      zv F_17bec D_17bec (Z_to_bv 64 s).
      sn F_17bf0 D_17bf0.                                   (* [comment removed for export] *)
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
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 112) 112 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (sbv_null_seg al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & AG1).
  replace (Z_to_bv 64 97020) with (0x17afc : word) by (apply bv_eq; reflexivity).
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
Context {PINS : @LeptPins AL LLU16} {P16 : V14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition FR7 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).
(* [comment removed for export] *)
Definition FRwh (m : word -> option byte) (s w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 h)).

(* [comment removed for export] *)
Definition cells7 (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) /\
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 s5v) /\
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 s6v) /\
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 s7v) /\
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 s8v) /\
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 s9v) /\
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 s10v) /\
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 s11v).

Lemma cells7_FR7 : forall m s ret regs, (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells7 (FR7 m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
         (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27).
Proof. intros m s ret regs Hs Hs64. unfold cells7, FR7. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Lemma cells7_out : forall m m' (s : Z) ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v,
  (forall x : word, (s - 104 <= u x < s)%Z -> m' x = m x) -> (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells7 m s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v -> cells7 m' s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v.
Proof.
  intros m m' s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v OUT Hs Hs64 (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13). unfold cells7.
  repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]).
Qed.

Section Segs.
Variable rom : word -> option byte.

  Lemma al8_of16 : forall p, (p mod 16 = 0)%Z -> (p mod 8 = 0)%Z.
  Proof. intros p H. rewrite <- (Z.add_0_r p). apply mod16_plus_mod8; [exact H | reflexivity]. Qed.
  (* [comment removed for export] *)
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM, u_Z2bv by lia; rewrite EQ; reflexivity).
  Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].

  (* [comment removed for export] *)
  Lemma g3w_A : forall regs m (s pixs : Z) (vs : pixv) (ret : word),
    (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> p_d vs = 8%Z -> (pixs + 64 <= s - 160 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x27440 : word) m rom) (mkst regs' (0x15dd4 : word) (FR7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0x27494 /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ getr regs' 18 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd DJ SOK H2 H1 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (PX1 : PIXat (FR7 m s ret regs) pixs vs).
    { unfold FR7. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd.
    unfold FR7 in *. eexists. split.
    - zv F_27344 D_27344 (Z_to_bv 64 (s - 160)).
      stepST F_27348 D_27348 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_2734c D_2734c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_27350 D_27350 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_27354 D_27354 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_27358 D_27358 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_2735c D_2735c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_27360 D_27360 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_27364 D_27364 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_27368 D_27368 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_2736c D_2736c (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_27370 D_27370 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_27374 D_27374 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_27378 D_27378 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      stepb_ft F_2737c D_2737c ltac:(condZ).                (* [comment removed for export] *)
      zv F_27380 D_27380 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_27384 D_27384.                                   (* [comment removed for export] *)
      stepb_ft F_16c40 D_16c40 ltac:(condZ).
      zand F_16c44 D_16c44 andi_7 AL8.                      (* [comment removed for export] *)
      stepb_ft F_16c48 D_16c48 ltac:(condR).                (* [comment removed for export] *)
      stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
      stepret F_16c50 D_16c50 (0x27484 : word) ltac:(bveq).
      sn F_27388 D_27388.                                   (* [comment removed for export] *)
      stepb_ft F_2738c D_2738c ltac:(condZ).                (* [comment removed for export] *)
      zv F_27390 D_27390 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_27394 D_27394.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3w_B : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (1 <= pixd)%Z -> (pixs mod 8 = 0)%Z -> (pixd mod 8 = 0)%Z ->
    PIXat m pixs vs -> PIXat m pixd vd ->
    (pixs + 64 <= s - 160 \/ s <= pixs)%Z -> (pixd + 64 <= s - 160 \/ s <= pixd)%Z ->
    (0 <= p_w vs < 2 ^ 31)%Z -> (0 <= p_h vs < 2 ^ 31)%Z -> (0 <= p_wpl vs < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x27494 : word) m rom) (mkst regs' (0x274d0 : word) (FRwh m s (p_w vs) (p_h vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 19 = Z_to_bv 64 (p_data vs) /\ getr regs' 9 = Z_to_bv 64 (p_data vd)
      /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 10 = Z_to_bv 64 (p_wpl vs)
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hs Hs64 Hs16 Hp Hpd AL8 AL8d PX PXd DJ DJd Rw Rh Rwpl SOK H2 H10 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (wf_data _ WF) as Rdat. pose proof (wf_data _ WFd) as Rdatd.
    assert (SL108 : ((s - 108) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    assert (SL112 : ((s - 112) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    set (Ma := wbytes (wbytes m (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
    set (Mb := wbytes Ma (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 (p_w vs)))).
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
    - zv F_27398 D_27398 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      zv F_2739c D_2739c (Z_to_bv 64 (s - 108)).            (* [comment removed for export] *)
      zv F_273a0 D_273a0 (Z_to_bv 64 (s - 112)).            (* [comment removed for export] *)
      zv F_273a4 D_273a4 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_273a8 D_273a8.                                   (* [comment removed for export] *)
      sn F_273ac D_273ac.                                   (* [comment removed for export] *)
      zand F_15f04 D_15f04 andi_3 SL108.                    (* [comment removed for export] *)
      stepb_ft F_15f08 D_15f08 ltac:(condZ).
      stepb_ft F_15f0c D_15f0c ltac:(condR).                (* [comment removed for export] *)
      stepST F_15f10 D_15f10 (Z_to_bv 64 (s - 108)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_15f14 D_15f14 andi_3 SL112.                    (* [comment removed for export] *)
      stepb_ft F_15f18 D_15f18 ltac:(condZ).
      stepb_ft F_15f1c D_15f1c ltac:(condR).                (* [comment removed for export] *)
      stepST F_15f20 D_15f20 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_15f24 D_15f24.                                   (* [comment removed for export] *)
      stepb_tk F_15f28 D_15f28 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_15f34 D_15f34 ltac:(condZ).                (* [comment removed for export] *)
      zand F_15f38 D_15f38 andi_7 AL8.                      (* [comment removed for export] *)
      stepb_ft F_15f3c D_15f3c ltac:(condZ).
      sn F_15f40 D_15f40.                                   (* [comment removed for export] *)
      stepb_ft F_15f44 D_15f44 ltac:(condR).                (* [comment removed for export] *)
      fold Ma.
      stepLD F_15f48 D_15f48 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; exact Cw) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_15f4c D_15f4c (Z_to_bv 64 (s - 108)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_15f50 D_15f50 ltac:(condZ).
      sn F_15f54 D_15f54.                                   (* [comment removed for export] *)
      stepb_ft F_15f58 D_15f58 ltac:(condR).                (* [comment removed for export] *)
      fold Mb.
      stepLD F_15f5c D_15f5c (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_15f60 D_15f60 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_tk F_15f64 D_15f64 ltac:(condZ).                (* [comment removed for export] *)
      sn F_15fac D_15fac.                                   (* [comment removed for export] *)
      stepret F_15fb0 D_15fb0 (0x274ac : word) ltac:(bveq).
      zv F_273b0 D_273b0 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_273b4 D_273b4.                                   (* [comment removed for export] *)
      stepb_ft F_16d18 D_16d18 ltac:(condZ).
      zand F_16d1c D_16d1c andi_7 AL8.
      stepb_ft F_16d20 D_16d20 ltac:(condR).
      stepLD F_16d24 D_16d24 (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; exact Cds) ltac:(apply W2Lib.lez8; lia).
      stepret F_16d28 D_16d28 (0x274b4 : word) ltac:(bveq).
      zv F_273b8 D_273b8 (Z_to_bv 64 (p_data vs)).          (* [comment removed for export] *)
      zv F_273bc D_273bc (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      zv F_273c0 D_273c0 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      sn F_273c4 D_273c4.                                   (* [comment removed for export] *)
      stepb_ft F_16d18 D_16d18 ltac:(condZ).
      zand F_16d1c D_16d1c andi_7 AL8d.
      stepb_ft F_16d20 D_16d20 ltac:(condR).
      stepLD F_16d24 D_16d24 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdd) ltac:(apply W2Lib.lez8; lia).
      stepret F_16d28 D_16d28 (0x274c4 : word) ltac:(bveq).
      zv F_273c8 D_273c8 (Z_to_bv 64 (p_data vd)).          (* [comment removed for export] *)
      zv F_273cc D_273cc (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_273d0 D_273d0.                                   (* [comment removed for export] *)
      stepb_ft F_15bac D_15bac ltac:(condZ).
      zand F_15bb0 D_15bb0 andi_7 AL8.
      stepb_ft F_15bb4 D_15bb4 ltac:(condR).
      stepLD F_15bb8 D_15bb8 (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; exact Cwpl) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_wpl vs)) by lia.
      stepret F_15bbc D_15bbc (0x274d0 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3w_E : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells7 m s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ->
    getr regs 2 = Z_to_bv 64 (s - 160) ->
    exists regs',
      msteps SEGS (mkst regs (0x27958 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v
      /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13) H2.
    eexists. split.
    -
      stepLD F_2785c D_2785c (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27860 D_27860 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27864 D_27864 (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27868 D_27868 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2786c D_2786c (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27870 D_27870 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; exact R6) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27874 D_27874 (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; exact R7) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27878 D_27878 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; exact R8) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2787c D_2787c (word_to_le_bytes 8 s7v) s7v ltac:(addr_norm; exact R9) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27880 D_27880 (word_to_le_bytes 8 s8v) s8v ltac:(addr_norm; exact R10) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27884 D_27884 (word_to_le_bytes 8 s9v) s9v ltac:(addr_norm; exact R11) ltac:(apply bytes_le_to_Z_8).
      stepLD F_27888 D_27888 (word_to_le_bytes 8 s10v) s10v ltac:(addr_norm; exact R12) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2788c D_2788c (word_to_le_bytes 8 s11v) s11v ltac:(addr_norm; exact R13) ltac:(apply bytes_le_to_Z_8).
      zv F_27890 D_27890 (Z_to_bv 64 s).
      stepret F_27894 D_27894 ret ltac:(bveq).
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
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_of_range w 8 ltac:(lia) DV) as Hwr. pose proof (wpl8_ge w ltac:(lia)) as Hw4.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat. cbn [p_data hdv] in Rdat.
  set (n := (4 * (wpl_of w 8 * h))%Z) in *. assert (En : n = (4 * (wpl_of w 8 * h))%Z) by reflexivity.
  assert (Hn0 : (0 < n)%Z) by (assert (1 * 1 <= wpl_of w 8 * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Hn0) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  destruct (g3w_A al_rom regs m s pixs (hdv w h 8 0 data) ret ltac:(lia) ltac:(lia) ltac:(lia) (al8_of16 _ ALp) PX eq_refl ltac:(lia)
              (W_sok_win C A m md (s - 160) 160 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q18 & AG1).
  replace (Z_to_bv 64 0x27440) with (0x27440 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR7 m s ret regs) md /\ POSTM C A s m (FR7 m s ret regs)) by (unfold FR7; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR7 m s ret regs) in *.
  pose proof (cells7_FR7 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 160 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR7. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x44140) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x15dd4 : word) with (Z_to_bv 64 0x15dd4) by (apply bv_eq; reflexivity).
  apply (PCT C A M1 md r1 (s - 160)%Z pixs w h 8%Z data cv (Z_to_bv 64 0x27494) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold PCT_STACK, LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw1 Hh1 Lp kR bR Hrm Hrk Hrb).
  intros A1 m2 vm1 r2 pixd datad HWa CSa PMa Hres PT Hrm1.
  replace (Z_to_bv 64 0x27494) with (0x27494 : word) by (apply bv_eq; reflexivity).
  pose proof PT as (Gpd & TOPpd & ALpd & Gdd & TOPdd & ALdd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPdd, L1d.
  assert (LEQ : forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 datad -> live A1 q = live A q).
  { destruct CMR as [[_ LEQ] | (ad & _ & B & _)]; [exact LEQ | lia]. }
  assert (SUBa : sub_live A A1).
  { intros q k Lq. rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence]. }
  pose proof (SUBa _ _ Lp) as Lp1. pose proof (SUBa _ _ Ld) as Ld1.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (hdv w h 8 0 data)).
  { apply (PIXat_frame M1); [exact PXs1|]. intros x Hx. exact (LIVK_at A M1 m2 pixs 64 x (proj2 PMa) Lp ltac:(lia) ltac:(lia) Hx). }
  assert (CE2 : cells7 m2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { destruct CE1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). unfold cells7.
    rewrite !(FRM_rdn16 C (s - 160) M1 m2 _ 8 CK (proj1 PMa)) by (cbn; lia). repeat split; assumption. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 160)) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 pixs) by (csr; reflexivity).
  (* [comment removed for export] *)
  destruct (g3w_B al_rom r2 m2 s pixs pixd (hdv w h 8 0 data) (hdv w h 8 0 datad) ltac:(lia) ltac:(lia) Hs16 ltac:(lia) ltac:(lia)
              (al8_of16 _ ALp) (al8_of16 _ ALpd) PXs2 PXd
              ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A1 m2 _ (s - 112) 8 CK HWa ltac:(lia) ltac:(cbn; lia)) E2 Hres E18)
    as (r3 & RUN3 & V2 & V19 & V9 & V8 & V10 & AG3). cbn [p_w p_h p_wpl p_data hdv] in RUN3, V19, V9, V10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (WP3 : W C A1 (FRwh m2 s w h) (with_vmmaps vm1 md) /\ POSTM C A1 s m2 (FRwh m2 s w h)) by (unfold FRwh; wp_win CK).
  destruct WP3 as [HW3 PM3]. set (M3 := FRwh m2 s w h) in *.
  assert (OUT3 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. unfold FRwh. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Ch3 : rdn SEGS M3 (Z_to_bv 64 (s - 160 + 48)) 4 = Some (Z_to_le_bytes 4 h)).
  { subst M3. unfold FRwh. replace (Z_to_le_bytes 4 h) with (word_to_le_bytes 4 (Z_to_bv 64 h)) by (unfold word_to_le_bytes; rewrite u_Z2bv by lia; reflexivity).
    replace (s - 160 + 48)%Z with (s - 112)%Z by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (Cw3 : rdn SEGS M3 (Z_to_bv 64 (s - 160 + 52)) 4 = Some (Z_to_le_bytes 4 w)).
  { subst M3. unfold FRwh. replace (Z_to_le_bytes 4 w) with (word_to_le_bytes 4 (Z_to_bv 64 w)) by (unfold word_to_le_bytes; rewrite u_Z2bv by lia; reflexivity).
    replace (s - 160 + 52)%Z with (s - 108)%Z by lia. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  (* [comment removed for export] *)
  destruct (V14Gray3h.g3_run M3 al_rom w h (wpl_of w 8) data datad (s - 160) pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ch3 Cw3
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALd]]) ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALdd]])
              (blk_sok C A1 M3 _ data n CK HW3 Ld1 ltac:(lia) ltac:(lia) ltac:(lia)) (blk_sok C A1 M3 _ datad n CK HW3 L1d ltac:(lia) ltac:(lia) ltac:(lia))
              (W_sok_win C A1 M3 _ (s - 160) 48 CK HW3 ltac:(lia) ltac:(cbn; lia))
              ltac:(unfold disj_apart; lia) r3 V2 V8 V9 V19 V10)
    as (r4 & M4 & RUN4 & OUT4 & GR4 & X2 & X10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  assert (CH : forall a, M4 a <> M3 a -> scratch C s a \/ (datad <= u a < datad + n)%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) datad) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (datad + n)) as [B2|B2]; [right; lia |]];
      (left; unfold scratch;
       destruct (Z_lt_ge_dec (u a) (s - 160)); [exfalso; apply NE; apply OUT4; lia|];
       destruct (Z_lt_ge_dec (u a) (s - 112)); [lia|]; exfalso; apply NE; apply OUT4; lia). }
  assert (HW4 : W C A1 M4 (with_vmmaps vm1 md)).
  { apply (W_local C A1 M3 _ M4 s CK HW3 Hhi); [| exact GR4].
    intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 datad), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L00d | lia]]. }
  assert (PM4 : POSTM C A s m M4).
  { eapply POSTM_trans; [exact PMa'|]. eapply POSTM_trans; [apply (POSTM_sub C A A1 s m2 M3 SUBa PM3)|].
    apply (POSTM_local C A A1 M3 _ M4 s CK HW3 SUBa). intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 datad), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L0d | lia]]. }
  assert (EQ4 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 datad -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z ->
                  (p + k <= s - 160)%Z -> (p <= u x < p + k)%Z -> M4 x = m2 x).
  { intros p k x L NE' G0 K0 Hlo' Hx.
    pose proof (blk_apart C A1 M3 _ _ _ _ _ CK HW3 L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia.
    rewrite OUT4; [apply OUT3; lia | lia | lia]. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (apply zbv_ne2; lia).
  assert (NEspd : Z_to_bv 64 pixs <> Z_to_bv 64 datad) by (intros E; rewrite E in Lp; rewrite Lp in L0d; discriminate).
  assert (PXd4 : PIXat M4 pixd (hdv w h 8 0 datad)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ4 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) ltac:(lia) Hx)]).
  assert (PXs4 : PIXat M4 pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m2); [exact PXs2 | intros x Hx; exact (EQ4 pixs 64%Z x Lp1 NEspd ltac:(lia) ltac:(lia) ltac:(lia) Hx)]).
  assert (CE4 : cells7 M4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (cells7_out m2 M4 s); [| lia | lia | exact CE2]. intros x Hx. rewrite OUT4; [apply OUT3; lia | lia | lia]. }
  destruct (g3w_E al_rom r4 M4 s ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) Hret CE4 X2)
    as (r5 & RUN5 & Y2 & Y1 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & AG5).
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
    (250000 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x27440 : word) m rom) (mkst regs' (0x1554c : word) (FR7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x103ba /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FR7.
    eexists. split.
    - zv F_27344 D_27344 (Z_to_bv 64 (s - 160)).
      stepST F_27348 D_27348 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_2734c D_2734c (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_27350 D_27350 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_27354 D_27354 (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_27358 D_27358 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_2735c D_2735c (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_27360 D_27360 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_27364 D_27364 (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_27368 D_27368 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_2736c D_2736c (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_27370 D_27370 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_27374 D_27374 (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_27378 D_27378 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      stepb_tk F_2737c D_2737c ltac:(condZ).                (* [comment removed for export] *)
      sn F_277c4 D_277c4.                                   (* [comment removed for export] *)
      stepLD F_277c8 D_277c8 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
      stepLD F_277cc D_277cc (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
      sn F_277d0 D_277d0.                                   (* [comment removed for export] *)
      stepb_ft F_277d4 D_277d4 ltac:(condZ).                (* [comment removed for export] *)
      sn F_277d8 D_277d8. sn F_277dc D_277dc. sn F_277e0 D_277e0.
      sn F_27800 D_27800. sn F_27804 D_27804. sn F_27808 D_27808.
      stepLD8 F_2780c D_2780c ret.
      stepLD8 F_27810 D_27810 (getr regs 8).
      stepLD8 F_27814 D_27814 (getr regs 9).
      stepLD8 F_27818 D_27818 (getr regs 18).
      stepLD8 F_2781c D_2781c (getr regs 19).
      stepLD8 F_27820 D_27820 (getr regs 20).
      stepLD8 F_27824 D_27824 (getr regs 21).
      stepLD8 F_27828 D_27828 (getr regs 22).
      stepLD8 F_2782c D_2782c (getr regs 23).
      stepLD8 F_27830 D_27830 (getr regs 24).
      stepLD8 F_27834 D_27834 (getr regs 25).
      stepLD8 F_27838 D_27838 (getr regs 26).
      stepLD8 F_2783c D_2783c (getr regs 27).
      zv F_27840 D_27840 (Z_to_bv 64 s).
      sn F_27844 D_27844.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsN.

Theorem gray3h_null_W : gray3h_null_contract PC_pixErodeGray3h.
Proof.
  unfold gray3h_null_contract, PC_pixErodeGray3h, G3H_STACK.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 160) 160 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (g3w_null_seg al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & AG1).
  replace (Z_to_bv 64 0x27440) with (0x27440 : word) by (apply bv_eq; reflexivity).
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
Context {PINS : @LeptPins AL LLU16} {P16 : V14Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition FR7 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (getr regs 26)))
    (Z_to_bv 64 (s - 104)) (word_to_le_bytes 8 (getr regs 27)).
(* [comment removed for export] *)
Definition FRwh (m : word -> option byte) (s w h : Z) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
    (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 w)))
    (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 h)).

(* [comment removed for export] *)
Definition cells7 (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) /\
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 s5v) /\
  rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 s6v) /\
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 s7v) /\
  rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (word_to_le_bytes 8 s8v) /\
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (word_to_le_bytes 8 s9v) /\
  rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 s10v) /\
  rdn SEGS m (Z_to_bv 64 (s - 104)) 8 = Some (word_to_le_bytes 8 s11v).

Lemma cells7_FR7 : forall m s ret regs, (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells7 (FR7 m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
         (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27).
Proof. intros m s ret regs Hs Hs64. unfold cells7, FR7. repeat split; rdn_solve. Qed.

(* [comment removed for export] *)
Lemma cells7_out : forall m m' (s : Z) ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v,
  (forall x : word, (s - 104 <= u x < s)%Z -> m' x = m x) -> (160 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells7 m s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v -> cells7 m' s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v.
Proof.
  intros m m' s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v OUT Hs Hs64 (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13). unfold cells7.
  repeat split; (etransitivity; [apply rdn_ext; [rewrite u_Z2bv by lia; cbn; lia | intros x Hx; apply OUT; rewrite u_Z2bv in Hx by lia; cbn in Hx; lia] | eassumption]).
Qed.

Section Segs.
Variable rom : word -> option byte.

  Lemma al8_of16 : forall p, (p mod 16 = 0)%Z -> (p mod 8 = 0)%Z.
  Proof. intros p H. rewrite <- (Z.add_0_r p). apply mod16_plus_mod8; [exact H | reflexivity]. Qed.
  (* [comment removed for export] *)
  Ltac zand F D LEM EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite LEM, u_Z2bv by lia; rewrite EQ; reflexivity).
  Ltac condR := pin; first [ apply c_eq_refl | vm_compute; reflexivity ].

  (* [comment removed for export] *)
  Lemma g3w_A : forall regs m (s pixs : Z) (vs : pixv) (ret : word),
    (160 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= pixs)%Z -> (pixs mod 8 = 0)%Z -> PIXat m pixs vs -> p_d vs = 8%Z -> (pixs + 64 <= s - 160 \/ s <= pixs)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x28408 : word) m rom) (mkst regs' (0x15dd4 : word) (FR7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 1 = Z_to_bv 64 0x2845c /\ getr regs' 10 = Z_to_bv 64 pixs
      /\ getr regs' 18 = Z_to_bv 64 pixs
      /\ regs_agree (fun r => In r [1; 2; 10; 11; 18]%list) regs regs'.
  Proof.
    intros regs m s pixs vs ret Hs Hs64 Hp AL8 PX Hd DJ SOK H2 H1 H10. pose proof PX as (Hp0 & Hp64 & WF & _).
    assert (PX1 : PIXat (FR7 m s ret regs) pixs vs).
    { unfold FR7. repeat (apply PIXat_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]). exact PX. }
    pose proof (PIX_rd_d SEGS _ _ _ PX1) as Cd. rewrite Hd in Cd.
    unfold FR7 in *. eexists. split.
    - zv F_2830c D_2830c (Z_to_bv 64 (s - 160)).
      stepST F_28310 D_28310 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_28314 D_28314 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_28318 D_28318 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_2831c D_2831c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_28320 D_28320 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_28324 D_28324 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_28328 D_28328 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_2832c D_2832c (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_28330 D_28330 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_28334 D_28334 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_28338 D_28338 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_2833c D_2833c (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_28340 D_28340 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      stepb_ft F_28344 D_28344 ltac:(condZ).                (* [comment removed for export] *)
      zv F_28348 D_28348 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_2834c D_2834c.                                   (* [comment removed for export] *)
      stepb_ft F_16c40 D_16c40 ltac:(condZ).
      zand F_16c44 D_16c44 andi_7 AL8.                      (* [comment removed for export] *)
      stepb_ft F_16c48 D_16c48 ltac:(condR).                (* [comment removed for export] *)
      stepLD F_16c4c D_16c4c (Z_to_le_bytes 4 8) (Z_to_bv 64 8) ltac:(addr_norm; exact Cd) ltac:(apply W2Lib.lez4; lia).
      stepret F_16c50 D_16c50 (0x2844c : word) ltac:(bveq).
      sn F_28350 D_28350.                                   (* [comment removed for export] *)
      stepb_ft F_28354 D_28354 ltac:(condZ).                (* [comment removed for export] *)
      zv F_28358 D_28358 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_2835c D_2835c.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3w_B : forall regs m (s pixs pixd : Z) (vs vd : pixv),
    (256 <= s)%Z -> (s < 2 ^ 64)%Z -> (s mod 16 = 0)%Z -> (1 <= pixs)%Z -> (1 <= pixd)%Z -> (pixs mod 8 = 0)%Z -> (pixd mod 8 = 0)%Z ->
    PIXat m pixs vs -> PIXat m pixd vd ->
    (pixs + 64 <= s - 160 \/ s <= pixs)%Z -> (pixd + 64 <= s - 160 \/ s <= pixd)%Z ->
    (0 <= p_w vs < 2 ^ 31)%Z -> (0 <= p_h vs < 2 ^ 31)%Z -> (0 <= p_wpl vs < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 112)) 8 = true ->
    getr regs 2 = Z_to_bv 64 (s - 160) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 18 = Z_to_bv 64 pixs ->
    exists regs',
      msteps SEGS (mkst regs (0x2845c : word) m rom) (mkst regs' (0x28498 : word) (FRwh m s (p_w vs) (p_h vs)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 160) /\ getr regs' 19 = Z_to_bv 64 (p_data vs) /\ getr regs' 9 = Z_to_bv 64 (p_data vd)
      /\ getr regs' 8 = Z_to_bv 64 pixd /\ getr regs' 10 = Z_to_bv 64 (p_wpl vs)
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 19]%list) regs regs'.
  Proof.
    intros regs m s pixs pixd vs vd Hs Hs64 Hs16 Hp Hpd AL8 AL8d PX PXd DJ DJd Rw Rh Rwpl SOK H2 H10 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof PXd as (Hd0 & Hd64 & WFd & _).
    pose proof (wf_data _ WF) as Rdat. pose proof (wf_data _ WFd) as Rdatd.
    assert (SL108 : ((s - 108) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    assert (SL112 : ((s - 112) mod 4 = 0)%Z) by (apply mod0_sub; [lia | apply mod16_mod4; exact Hs16 | reflexivity]).
    set (Ma := wbytes (wbytes m (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 112)) (word_to_le_bytes 4 (Z_to_bv 64 0))).
    set (Mb := wbytes Ma (Z_to_bv 64 (s - 108)) (word_to_le_bytes 4 (Z_to_bv 64 (p_w vs)))).
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
    - zv F_28360 D_28360 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      zv F_28364 D_28364 (Z_to_bv 64 (s - 108)).            (* [comment removed for export] *)
      zv F_28368 D_28368 (Z_to_bv 64 (s - 112)).            (* [comment removed for export] *)
      zv F_2836c D_2836c (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_28370 D_28370.                                   (* [comment removed for export] *)
      sn F_28374 D_28374.                                   (* [comment removed for export] *)
      zand F_15f04 D_15f04 andi_3 SL108.                    (* [comment removed for export] *)
      stepb_ft F_15f08 D_15f08 ltac:(condZ).
      stepb_ft F_15f0c D_15f0c ltac:(condR).                (* [comment removed for export] *)
      stepST F_15f10 D_15f10 (Z_to_bv 64 (s - 108)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      zand F_15f14 D_15f14 andi_3 SL112.                    (* [comment removed for export] *)
      stepb_ft F_15f18 D_15f18 ltac:(condZ).
      stepb_ft F_15f1c D_15f1c ltac:(condR).                (* [comment removed for export] *)
      stepST F_15f20 D_15f20 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      sn F_15f24 D_15f24.                                   (* [comment removed for export] *)
      stepb_tk F_15f28 D_15f28 ltac:(condZ).                (* [comment removed for export] *)
      stepb_ft F_15f34 D_15f34 ltac:(condZ).                (* [comment removed for export] *)
      zand F_15f38 D_15f38 andi_7 AL8.                      (* [comment removed for export] *)
      stepb_ft F_15f3c D_15f3c ltac:(condZ).
      sn F_15f40 D_15f40.                                   (* [comment removed for export] *)
      stepb_ft F_15f44 D_15f44 ltac:(condR).                (* [comment removed for export] *)
      fold Ma.
      stepLD F_15f48 D_15f48 (Z_to_le_bytes 4 (p_w vs)) (Z_to_bv 64 (p_w vs)) ltac:(addr_norm; exact Cw) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_w vs)) by lia.
      stepST F_15f4c D_15f4c (Z_to_bv 64 (s - 108)) (Z_to_bv 64 (p_w vs)) ltac:(sok_in SOK).
      stepb_ft F_15f50 D_15f50 ltac:(condZ).
      sn F_15f54 D_15f54.                                   (* [comment removed for export] *)
      stepb_ft F_15f58 D_15f58 ltac:(condR).                (* [comment removed for export] *)
      fold Mb.
      stepLD F_15f5c D_15f5c (Z_to_le_bytes 4 (p_h vs)) (Z_to_bv 64 (p_h vs)) ltac:(addr_norm; exact Ch) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_h vs)) by lia.
      stepST F_15f60 D_15f60 (Z_to_bv 64 (s - 112)) (Z_to_bv 64 (p_h vs)) ltac:(sok_in SOK).
      stepb_tk F_15f64 D_15f64 ltac:(condZ).                (* [comment removed for export] *)
      sn F_15fac D_15fac.                                   (* [comment removed for export] *)
      stepret F_15fb0 D_15fb0 (0x28474 : word) ltac:(bveq).
      zv F_28378 D_28378 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_2837c D_2837c.                                   (* [comment removed for export] *)
      stepb_ft F_16d18 D_16d18 ltac:(condZ).
      zand F_16d1c D_16d1c andi_7 AL8.
      stepb_ft F_16d20 D_16d20 ltac:(condR).
      stepLD F_16d24 D_16d24 (Z_to_le_bytes 8 (p_data vs)) (Z_to_bv 64 (p_data vs)) ltac:(addr_norm; exact Cds) ltac:(apply W2Lib.lez8; lia).
      stepret F_16d28 D_16d28 (0x2847c : word) ltac:(bveq).
      zv F_28380 D_28380 (Z_to_bv 64 (p_data vs)).          (* [comment removed for export] *)
      zv F_28384 D_28384 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      zv F_28388 D_28388 (Z_to_bv 64 pixd).                 (* [comment removed for export] *)
      sn F_2838c D_2838c.                                   (* [comment removed for export] *)
      stepb_ft F_16d18 D_16d18 ltac:(condZ).
      zand F_16d1c D_16d1c andi_7 AL8d.
      stepb_ft F_16d20 D_16d20 ltac:(condR).
      stepLD F_16d24 D_16d24 (Z_to_le_bytes 8 (p_data vd)) (Z_to_bv 64 (p_data vd)) ltac:(addr_norm; exact Cdd) ltac:(apply W2Lib.lez8; lia).
      stepret F_16d28 D_16d28 (0x2848c : word) ltac:(bveq).
      zv F_28390 D_28390 (Z_to_bv 64 (p_data vd)).          (* [comment removed for export] *)
      zv F_28394 D_28394 (Z_to_bv 64 pixs).                 (* [comment removed for export] *)
      sn F_28398 D_28398.                                   (* [comment removed for export] *)
      stepb_ft F_15bac D_15bac ltac:(condZ).
      zand F_15bb0 D_15bb0 andi_7 AL8.
      stepb_ft F_15bb4 D_15bb4 ltac:(condR).
      stepLD F_15bb8 D_15bb8 (Z_to_le_bytes 4 (p_wpl vs)) (Z_to_bv 64 (p_wpl vs)) ltac:(addr_norm; exact Cwpl) ltac:(apply W2Lib.lez4; lia).
      rewrite (v_lw_small (p_wpl vs)) by lia.
      stepret F_15bbc D_15bbc (0x28498 : word) ltac:(bveq).
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma g3w_E : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v : word),
    (160 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> cells7 m s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v ->
    getr regs 2 = Z_to_bv 64 (s - 160) ->
    exists regs',
      msteps SEGS (mkst regs (0x28920 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v
      /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v /\ getr regs' 21 = s5v /\ getr regs' 22 = s6v /\ getr regs' 23 = s7v
      /\ getr regs' 24 = s8v /\ getr regs' 25 = s9v /\ getr regs' 26 = s10v /\ getr regs' 27 = s11v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v Hs Hs64 Hret (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13) H2.
    eexists. split.
    -
      stepLD F_28824 D_28824 (word_to_le_bytes 8 ret) ret ltac:(addr_norm; exact R1) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28828 D_28828 (word_to_le_bytes 8 s0v) s0v ltac:(addr_norm; exact R2) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2882c D_2882c (word_to_le_bytes 8 s1v) s1v ltac:(addr_norm; exact R3) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28830 D_28830 (word_to_le_bytes 8 s2v) s2v ltac:(addr_norm; exact R4) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28834 D_28834 (word_to_le_bytes 8 s3v) s3v ltac:(addr_norm; exact R5) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28838 D_28838 (word_to_le_bytes 8 s4v) s4v ltac:(addr_norm; exact R6) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2883c D_2883c (word_to_le_bytes 8 s5v) s5v ltac:(addr_norm; exact R7) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28840 D_28840 (word_to_le_bytes 8 s6v) s6v ltac:(addr_norm; exact R8) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28844 D_28844 (word_to_le_bytes 8 s7v) s7v ltac:(addr_norm; exact R9) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28848 D_28848 (word_to_le_bytes 8 s8v) s8v ltac:(addr_norm; exact R10) ltac:(apply bytes_le_to_Z_8).
      stepLD F_2884c D_2884c (word_to_le_bytes 8 s9v) s9v ltac:(addr_norm; exact R11) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28850 D_28850 (word_to_le_bytes 8 s10v) s10v ltac:(addr_norm; exact R12) ltac:(apply bytes_le_to_Z_8).
      stepLD F_28854 D_28854 (word_to_le_bytes 8 s11v) s11v ltac:(addr_norm; exact R13) ltac:(apply bytes_le_to_Z_8).
      zv F_28858 D_28858 (Z_to_bv 64 s).
      stepret F_2885c D_2885c ret ltac:(bveq).
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
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof HOK as (DV & Hw2 & Hh2 & Hsz).
  pose proof (wpl_of_range w 8 ltac:(lia) DV) as Hwr. pose proof (wpl8_ge w ltac:(lia)) as Hw4.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF) as Rdat. cbn [p_data hdv] in Rdat.
  set (n := (4 * (wpl_of w 8 * h))%Z) in *. assert (En : n = (4 * (wpl_of w 8 * h))%Z) by reflexivity.
  assert (Hn0 : (0 < n)%Z) by (assert (1 * 1 <= wpl_of w 8 * h)%Z by (apply Z.mul_le_mono_nonneg; lia); lia).
  destruct (blk_range C A m md (Z_to_bv 64 pixs) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  destruct (blk_range C A m md (Z_to_bv 64 data) _ CK HW Ld Hn0) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  (* [comment removed for export] *)
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  destruct (g3w_A al_rom regs m s pixs (hdv w h 8 0 data) ret ltac:(lia) ltac:(lia) ltac:(lia) (al8_of16 _ ALp) PX eq_refl ltac:(lia)
              (W_sok_win C A m md (s - 160) 160 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q18 & AG1).
  replace (Z_to_bv 64 0x28408) with (0x28408 : word) by (apply bv_eq; reflexivity).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR7 m s ret regs) md /\ POSTM C A s m (FR7 m s ret regs)) by (unfold FR7; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR7 m s ret regs) in *.
  pose proof (cells7_FR7 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (OUT1 : forall x : word, ~ (s - 160 <= u x < s)%Z -> M1 x = m x).
  { intros x Hx. subst M1. unfold FR7. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (PXs1 : PIXat M1 pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m); [exact PX | intros x Hx; apply OUT1; lia]).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x44140) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  replace (0x15dd4 : word) with (Z_to_bv 64 0x15dd4) by (apply bv_eq; reflexivity).
  apply (PCT C A M1 md r1 (s - 160)%Z pixs w h 8%Z data cv (Z_to_bv 64 0x2845c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold PCT_STACK, LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 PXs1 HOK Hw1 Hh1 Lp kR bR Hrm Hrk Hrb).
  intros A1 m2 vm1 r2 pixd datad HWa CSa PMa Hres PT Hrm1.
  replace (Z_to_bv 64 0x2845c) with (0x2845c : word) by (apply bv_eq; reflexivity).
  pose proof PT as (Gpd & TOPpd & ALpd & Gdd & TOPdd & ALdd & NEpd & L0p & L0d & L00p & L00d & L1p & L1d & PXd & CMR). rewrite <- En in TOPdd, L1d.
  assert (LEQ : forall q, q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 datad -> live A1 q = live A q).
  { destruct CMR as [[_ LEQ] | (ad & _ & B & _)]; [exact LEQ | lia]. }
  assert (SUBa : sub_live A A1).
  { intros q k Lq. rewrite LEQ; [exact Lq | intros ->; congruence | intros ->; congruence]. }
  pose proof (SUBa _ _ Lp) as Lp1. pose proof (SUBa _ _ Ld) as Ld1.
  assert (PMa' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (PXs2 : PIXat m2 pixs (hdv w h 8 0 data)).
  { apply (PIXat_frame M1); [exact PXs1|]. intros x Hx. exact (LIVK_at A M1 m2 pixs 64 x (proj2 PMa) Lp ltac:(lia) ltac:(lia) Hx). }
  assert (CE2 : cells7 m2 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { destruct CE1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13). unfold cells7.
    rewrite !(FRM_rdn16 C (s - 160) M1 m2 _ 8 CK (proj1 PMa)) by (cbn; lia). repeat split; assumption. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 160)) by (csr; reflexivity).
  assert (E18 : getr r2 18 = Z_to_bv 64 pixs) by (csr; reflexivity).
  (* [comment removed for export] *)
  destruct (g3w_B al_rom r2 m2 s pixs pixd (hdv w h 8 0 data) (hdv w h 8 0 datad) ltac:(lia) ltac:(lia) Hs16 ltac:(lia) ltac:(lia)
              (al8_of16 _ ALp) (al8_of16 _ ALpd) PXs2 PXd
              ltac:(lia) ltac:(lia) ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
              (W_sok_win C A1 m2 _ (s - 112) 8 CK HWa ltac:(lia) ltac:(cbn; lia)) E2 Hres E18)
    as (r3 & RUN3 & V2 & V19 & V9 & V8 & V10 & AG3). cbn [p_w p_h p_wpl p_data hdv] in RUN3, V19, V9, V10.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
  assert (WP3 : W C A1 (FRwh m2 s w h) (with_vmmaps vm1 md) /\ POSTM C A1 s m2 (FRwh m2 s w h)) by (unfold FRwh; wp_win CK).
  destruct WP3 as [HW3 PM3]. set (M3 := FRwh m2 s w h) in *.
  assert (OUT3 : forall x : word, ~ (s - 112 <= u x < s - 104)%Z -> M3 x = m2 x).
  { intros x Hx. subst M3. unfold FRwh. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
  assert (Ch3 : rdn SEGS M3 (Z_to_bv 64 (s - 160 + 48)) 4 = Some (Z_to_le_bytes 4 h)).
  { subst M3. unfold FRwh. replace (Z_to_le_bytes 4 h) with (word_to_le_bytes 4 (Z_to_bv 64 h)) by (unfold word_to_le_bytes; rewrite u_Z2bv by lia; reflexivity).
    replace (s - 160 + 48)%Z with (s - 112)%Z by lia. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  assert (Cw3 : rdn SEGS M3 (Z_to_bv 64 (s - 160 + 52)) 4 = Some (Z_to_le_bytes 4 w)).
  { subst M3. unfold FRwh. replace (Z_to_le_bytes 4 w) with (word_to_le_bytes 4 (Z_to_bv 64 w)) by (unfold word_to_le_bytes; rewrite u_Z2bv by lia; reflexivity).
    replace (s - 160 + 52)%Z with (s - 108)%Z by lia. rdn_peel1. apply rdn_wbytes_hit4. rewrite u_Z2bv by lia. lia. }
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  (* [comment removed for export] *)
  destruct (V14Gray3hD.g3_run M3 al_rom w h (wpl_of w 8) data datad (s - 160) pixd ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Ch3 Cw3
              ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALd]]) ltac:(split; [lia | split; [lia | apply mod16_mod4; exact ALdd]])
              (blk_sok C A1 M3 _ data n CK HW3 Ld1 ltac:(lia) ltac:(lia) ltac:(lia)) (blk_sok C A1 M3 _ datad n CK HW3 L1d ltac:(lia) ltac:(lia) ltac:(lia))
              (W_sok_win C A1 M3 _ (s - 160) 48 CK HW3 ltac:(lia) ltac:(cbn; lia))
              ltac:(unfold disj_apart; lia) r3 V2 V8 V9 V19 V10)
    as (r4 & M4 & RUN4 & OUT4 & GR4 & X2 & X10 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
  assert (CH : forall a, M4 a <> M3 a -> scratch C s a \/ (datad <= u a < datad + n)%Z).
  { intros a NE. destruct (Z_lt_ge_dec (u a) datad) as [B1|B1];
      [| destruct (Z_lt_ge_dec (u a) (datad + n)) as [B2|B2]; [right; lia |]];
      (left; unfold scratch;
       destruct (Z_lt_ge_dec (u a) (s - 160)); [exfalso; apply NE; apply OUT4; lia|];
       destruct (Z_lt_ge_dec (u a) (s - 112)); [lia|]; exfalso; apply NE; apply OUT4; lia). }
  assert (HW4 : W C A1 M4 (with_vmmaps vm1 md)).
  { apply (W_local C A1 M3 _ M4 s CK HW3 Hhi); [| exact GR4].
    intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 datad), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L00d | lia]]. }
  assert (PM4 : POSTM C A s m M4).
  { eapply POSTM_trans; [exact PMa'|]. eapply POSTM_trans; [apply (POSTM_sub C A A1 s m2 M3 SUBa PM3)|].
    apply (POSTM_local C A A1 M3 _ M4 s CK HW3 SUBa). intros a NE. destruct (CH a NE) as [X|R]; [left; exact X | right].
    exists (Z_to_bv 64 datad), n. rewrite u_Z2bv by lia. split; [exact L1d | split; [exact L0d | lia]]. }
  assert (EQ4 : forall (p k : Z) (x : word), live A1 (Z_to_bv 64 p) = Some k -> Z_to_bv 64 p <> Z_to_bv 64 datad -> (0 <= p < 2 ^ 64)%Z -> (0 <= k)%Z ->
                  (p + k <= s - 160)%Z -> (p <= u x < p + k)%Z -> M4 x = m2 x).
  { intros p k x L NE' G0 K0 Hlo' Hx.
    pose proof (blk_apart C A1 M3 _ _ _ _ _ CK HW3 L L1d NE' K0 ltac:(lia)) as D. rewrite !u_Z2bv in D by lia.
    rewrite OUT4; [apply OUT3; lia | lia | lia]. }
  assert (NEpdw : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (apply zbv_ne2; lia).
  assert (NEspd : Z_to_bv 64 pixs <> Z_to_bv 64 datad) by (intros E; rewrite E in Lp; rewrite Lp in L0d; discriminate).
  assert (PXd4 : PIXat M4 pixd (hdv w h 8 0 datad)) by (apply (PIXat_frame m2); [exact PXd | intros x Hx; exact (EQ4 pixd 64%Z x L1p NEpdw ltac:(lia) ltac:(lia) ltac:(lia) Hx)]).
  assert (PXs4 : PIXat M4 pixs (hdv w h 8 0 data)) by (apply (PIXat_frame m2); [exact PXs2 | intros x Hx; exact (EQ4 pixs 64%Z x Lp1 NEspd ltac:(lia) ltac:(lia) ltac:(lia) Hx)]).
  assert (CE4 : cells7 M4 s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)).
  { apply (cells7_out m2 M4 s); [| lia | lia | exact CE2]. intros x Hx. rewrite OUT4; [apply OUT3; lia | lia | lia]. }
  destruct (g3w_E al_rom r4 M4 s ret _ _ _ _ _ _ _ _ _ _ _ _ ltac:(lia) ltac:(lia) Hret CE4 X2)
    as (r5 & RUN5 & Y2 & Y1 & Y8 & Y9 & Y18 & Y19 & Y20 & Y21 & Y22 & Y23 & Y24 & Y25 & Y26 & Y27 & AG5).
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
    (250000 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 160)) 160 = true ->
    rdn SEGS m (Z_to_bv 64 0x32d70) 8 = Some (Z_to_le_bytes 8 0x33de0) -> rdn SEGS m (Z_to_bv 64 0x33de0) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x28408 : word) m rom) (mkst regs' (0x1554c : word) (FR7 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 10 = Z_to_bv 64 0x10298 /\ getr regs' 11 = Z_to_bv 64 0x10bf2 /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = getr regs 8 /\ getr regs' 9 = getr regs 9 /\ getr regs' 18 = getr regs 18 /\ getr regs' 19 = getr regs 19 /\ getr regs' 20 = getr regs 20 /\ getr regs' 21 = getr regs 21 /\ getr regs' 22 = getr regs 22 /\ getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\ getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\ getr regs' 27 = getr regs 27
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%list) regs regs'.
  Proof.
    intros regs m s ret Hs Hs64 SOK Rg Rs H2 H1 H10. unfold FR7.
    eexists. split.
    - zv F_2830c D_2830c (Z_to_bv 64 (s - 160)).
      stepST F_28310 D_28310 (Z_to_bv 64 (s - 8)) ret ltac:(sok_in SOK).
      stepST F_28314 D_28314 (Z_to_bv 64 (s - 16)) (getr regs 8) ltac:(sok_in SOK).
      stepST F_28318 D_28318 (Z_to_bv 64 (s - 24)) (getr regs 9) ltac:(sok_in SOK).
      stepST F_2831c D_2831c (Z_to_bv 64 (s - 32)) (getr regs 18) ltac:(sok_in SOK).
      stepST F_28320 D_28320 (Z_to_bv 64 (s - 40)) (getr regs 19) ltac:(sok_in SOK).
      stepST F_28324 D_28324 (Z_to_bv 64 (s - 48)) (getr regs 20) ltac:(sok_in SOK).
      stepST F_28328 D_28328 (Z_to_bv 64 (s - 56)) (getr regs 21) ltac:(sok_in SOK).
      stepST F_2832c D_2832c (Z_to_bv 64 (s - 64)) (getr regs 22) ltac:(sok_in SOK).
      stepST F_28330 D_28330 (Z_to_bv 64 (s - 72)) (getr regs 23) ltac:(sok_in SOK).
      stepST F_28334 D_28334 (Z_to_bv 64 (s - 80)) (getr regs 24) ltac:(sok_in SOK).
      stepST F_28338 D_28338 (Z_to_bv 64 (s - 88)) (getr regs 25) ltac:(sok_in SOK).
      stepST F_2833c D_2833c (Z_to_bv 64 (s - 96)) (getr regs 26) ltac:(sok_in SOK).
      stepST F_28340 D_28340 (Z_to_bv 64 (s - 104)) (getr regs 27) ltac:(sok_in SOK).
      stepb_tk F_28344 D_28344 ltac:(condZ).                (* [comment removed for export] *)
      sn F_2878c D_2878c.                                   (* [comment removed for export] *)
      stepLD F_28790 D_28790 (Z_to_le_bytes 8 0x33de0) (Z_to_bv 64 0x33de0) ltac:(addr_norm; repeat rdn_peel1; exact Rg) ltac:(apply W2Lib.lez8; lia).
      stepLD F_28794 D_28794 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; repeat rdn_peel1; exact Rs) ltac:(apply W2Lib.lez4; lia).
      sn F_28798 D_28798.                                   (* [comment removed for export] *)
      stepb_ft F_2879c D_2879c ltac:(condZ).                (* [comment removed for export] *)
      sn F_287a0 D_287a0. sn F_287a4 D_287a4. sn F_287a8 D_287a8.
      sn F_287c8 D_287c8. sn F_287cc D_287cc. sn F_287d0 D_287d0.
      stepLD8 F_287d4 D_287d4 ret.
      stepLD8 F_287d8 D_287d8 (getr regs 8).
      stepLD8 F_287dc D_287dc (getr regs 9).
      stepLD8 F_287e0 D_287e0 (getr regs 18).
      stepLD8 F_287e4 D_287e4 (getr regs 19).
      stepLD8 F_287e8 D_287e8 (getr regs 20).
      stepLD8 F_287ec D_287ec (getr regs 21).
      stepLD8 F_287f0 D_287f0 (getr regs 22).
      stepLD8 F_287f4 D_287f4 (getr regs 23).
      stepLD8 F_287f8 D_287f8 (getr regs 24).
      stepLD8 F_287fc D_287fc (getr regs 25).
      stepLD8 F_28800 D_28800 (getr regs 26).
      stepLD8 F_28804 D_28804 (getr regs 27).
      zv F_28808 D_28808 (Z_to_bv 64 s).
      sn F_2880c D_2880c.                                   (* [comment removed for export] *)
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End SegsN.

Theorem gray3h_null_W : gray3h_null_contract PC_pixDilateGray3h.
Proof.
  unfold gray3h_null_contract, PC_pixDilateGray3h, G3H_STACK.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 160) 160 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (g3w_null_seg al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A m md HW) (W_sev C A m md HW) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & AG1).
  replace (Z_to_bv 64 0x28408) with (0x28408 : word) by (apply bv_eq; reflexivity).
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
