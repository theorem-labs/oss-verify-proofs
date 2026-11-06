(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.V17 Require Import V17LeptStderr V17LeptBase V17LeptErr V17LeptPixHdr V17LeptDeser V17LeptKernPix V17LeptKernSegs V17LeptKernSegs2
  V17LeptKernC2d V17LeptKernCreate V17LeptKernDestroy V17LeptKernFromPix V17_code_133ec_14000 V17_code_16000_17000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit LeptRoomK.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KernFromPixB.
Context {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LLU17} {P16 : V17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
#[local] Definition kf_rest : list (bv 5) := [3; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Lemma kfp_loop : forall (k : nat) (fx : FPState) C A m md regs (s pix : Z) (v : pixv) (S : TSet) (kel arr : Z) (rows : Z -> Z) (kX bX : Z) A1 M1 vm1 r (i j : Z),
  frm_zero (@fp_csr fx) -> Cok C -> KX C A m md regs s kel arr (p_h v) (p_w v) rows S kX bX -> aroom A1 vm1 kX bX ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + 80 + LSF <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x30da0 ->
  W C A1 M1 (with_vmmaps vm1 md) -> POSTM C A s m M1 -> sub_live A A1 ->
  kcells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (p_w v) (p_h v) ->
  PIXK C A M1 pix v -> KEL C A A1 M1 kel arr (p_h v) (p_w v) rows ->
  (0 <= i < p_h v)%Z -> (0 <= j < p_w v)%Z -> (Z.of_nat k = (p_h v - 1 - i) * p_w v + (p_w v - 1 - j))%Z ->
  getr r 2 = Z_to_bv 64 (s - 64) -> getr r 8 = Z_to_bv 64 pix -> getr r 9 = Z_to_bv 64 kel -> getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 j ->
  getr r 4 = Z_to_bv 64 0x30da0 -> (forall x, In x kf_rest -> getr r x = getr regs x) ->
  realizes SEGS (mkCfg (@mkst fx r (0x162ec : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  induction k as [|k IH]; intros fx C A m md regs s pix v S kel arr rows kX bX A1 M1 vm1 r i j Hz CK HKX HRX Hs16 Hlo Hhi H4 HW PM SUB CE PK KL Hi Hj Hk R2 R8 R9 R18 R19 R4 RR;
    pose proof PK as (PX & Hd8 & Hw3 & Hh3 & Hw4 & Hsz & Hw2 & Hh2 & _);
    pose proof CK as [T1 T2 T3 T4 T5]; laypins; cbn [fst snd ll_img LLU17] in *; unfold LSF in *; unfold kf_rest in RR;
    (apply (kfp_body fx C A m md regs s pix v S kel arr rows A1 M1 vm1 r i j Hz CK Hs16 ltac:(unfold LSF; lia) Hhi H4 HW PM SUB CE PK KL Hi Hj R2 R8 R9 R18 R19 R4
              ltac:(unfold V17LeptKernFromPix.kf_rest; rest_solve)));
    intros fr cs M3 r6 Hz' HW3 PM3 CE3 PK3 KL3 X2 X8 X9 X18 X19 X4 XR; unfold V17LeptKernFromPix.kf_rest in XR;
    pose proof CE3 as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  - (* [comment removed for export] *)
    assert (Hij : (i + 1 = p_h v /\ j + 1 = p_w v)%Z) by nia.
    destruct (kfp_L4c (fx := mkFP fr cs) al_rom r6 M3 s (p_w v) (p_h v) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                C6 C7 X2 X18 X19) as (r7 & RUN7 & Q2 & Q8 & Q9 & AG7).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN7 |].
    apply (HKX (mkFP fr cs) A1 M3 vm1 r7 Hz' HW3 PM3 CE3 KL3 HRX Q2 ltac:(rewrite Q9; exact X9) ltac:(csr; reflexivity)).
    unfold kf_rest; rest_solve.
  - destruct (Z_lt_ge_dec (j + 1) (p_w v)) as [Hj1 | Hj1].
    + (* [comment removed for export] *)
      destruct (kfp_L4a (fx := mkFP fr cs) al_rom r6 M3 s (p_w v) (p_h v) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hj1 C6 X2 X18 X19)
        as (r7 & RUN7 & Q2 & Q18 & Q19 & Q8 & Q9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN7 |].
      apply (IH (mkFP fr cs) C A m md regs s pix v S kel arr rows kX bX A1 M3 vm1 r7 i (j + 1)%Z Hz' CK HKX HRX Hs16 ltac:(unfold LSF; lia) Hhi H4 HW3 PM3 SUB CE3 PK3 KL3
               ltac:(lia) ltac:(lia) ltac:(lia) Q2 ltac:(rewrite Q8; exact X8) ltac:(rewrite Q9; exact X9) Q18 Q19 ltac:(csr; reflexivity)).
      unfold kf_rest; rest_solve.
    + (* [comment removed for export] *)
      assert (Hi1 : (i + 1 < p_h v)%Z) by nia.
      destruct (kfp_L4b (fx := mkFP fr cs) al_rom r6 M3 s (p_w v) (p_h v) i j ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hi1
                  C6 C7 X2 X18 X19) as (r7 & RUN7 & Q2 & Q18 & Q19 & Q8 & Q9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN7 |].
      apply (IH (mkFP fr cs) C A m md regs s pix v S kel arr rows kX bX A1 M3 vm1 r7 (i + 1)%Z 0%Z Hz' CK HKX HRX Hs16 ltac:(unfold LSF; lia) Hhi H4 HW3 PM3 SUB CE3 PK3 KL3
               ltac:(lia) ltac:(lia) ltac:(nia) Q2 ltac:(rewrite Q8; exact X8) ltac:(rewrite Q9; exact X9) Q18 Q19 ltac:(csr; reflexivity)).
      unfold kf_rest; rest_solve.
Qed.

(* [comment removed for export] *)
Lemma wpl8_ge : forall w, (0 <= w)%Z -> (w <= 4 * wpl_of w 8)%Z.
Proof.
  intros w Hw. unfold wpl_of. pose proof (Z.div_mod (w * 8 + 31) 32 ltac:(lia)). pose proof (Z.mod_pos_bound (w * 8 + 31) 32 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Theorem kernelCreateFromPix_W : forall (fx : FPState) C A m md regs (s pix : Z) (v : pixv) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x30da0 ->
  getr regs 10 = Z_to_bv 64 pix -> getr regs 11 = Z_to_bv 64 2 -> getr regs 12 = Z_to_bv 64 2 ->
  PIXat m pix v -> pshape v -> live A (Z_to_bv 64 pix) = Some 64%Z -> live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_kfp (p_d v) (p_h v) <= kR)%Z -> (RB_kfp (p_d v) (p_h v) (p_w v) <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists kel arr rows, getr regs' 10 = Z_to_bv 64 kel /\ (1 <= kel)%Z /\ kern C A A' m' kel arr (p_h v) (p_w v) rows) ) ->
     aroom A' vm' (kR - RK_kfp (p_d v) (p_h v)) (bR - RB_kfp (p_d v) (p_h v) (p_w v)) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (0x16158 : word) m al_rom) md) S.
Proof.
  intros fx C A m md regs s pix v ret S Hz CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 PX SHP Lp Ld kR bR HRM HRK HRB HK.
  pose proof SHP as (Hw1 & Hh1 & (DV & Hw2 & Hh2 & Hsz) & Ewpl).
  assert (HRK0 : (0 <= RK_kfp (p_d v) (p_h v))%Z) by (unfold RK_kfp, RK_kern; destruct (p_d v =? 8)%Z; lia).
  assert (HRB0 : (0 <= RB_kfp (p_d v) (p_h v) (p_w v))%Z) by (unfold RB_kfp; destruct (p_d v =? 8)%Z; [apply RB_kern_nonneg; lia | lia]).
  assert (HRMF : aroom A (m_vmmaps md) (kR - RK_kfp (p_d v) (p_h v)) (bR - RB_kfp (p_d v) (p_h v) (p_w v))) by (apply (aroom_mono _ _ _ _ _ _ HRM); lia).
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_d _ WF). pose proof (wf_wpl _ WF). pose proof (wf_data _ WF).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU17] in *. unfold LSF in *.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  destruct (blk_range C A m md (Z_to_bv 64 pix) 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  assert (Hwh : (0 < p_wpl v * p_h v)%Z).
  { rewrite Ewpl. apply Z.mul_pos_pos; [|lia]. unfold wpl_of. pose proof (dval_range _ DV). apply Z.div_str_pos. nia. }
  destruct (blk_range C A m md (Z_to_bv 64 (p_data v)) _ CK HW Ld ltac:(lia)) as [Gd TOPd]. rewrite u_Z2bv in Gd, TOPd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Ld) as (_ & ALd & _). rewrite u_Z2bv in ALd by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp16 & _). rewrite u_Z2bv in ALp16 by lia.
  assert (ALp8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp16 | reflexivity]).
  (* [comment removed for export] *)
  destruct (kfp_A al_rom regs m s pix v ret ltac:(lia) ltac:(lia) PX Gp ltac:(lia) Hs16 ALp8 (W_sok_win C A m md (s - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) H2 H1 H10 H11 H12)
    as (r1 & RUN1 & Q2 & Q8 & Q18 & Q19 & Q10 & Q11 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := KF m s ret regs (p_w v) (p_h v) (p_d v)).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold KF; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (kcells_KF m s ret regs (p_w v) (p_h v) (p_d v) ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1. rewrite <- H1 in CE1.
  pose proof CE1 as (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  assert (OUT1 : forall x : word, ~ (s - 64 <= u x < s)%Z -> M1 x = m x) by (intros x Hx; subst M1; apply KF_out; lia).
  assert (PX1 : PIXat M1 pix v) by (apply (PIXat_frame m M1 pix v PX); intros x Hx; apply OUT1; lia).
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x30da0) by (rewrite (AG1 4) by (cbv; intuition discriminate); exact H4).
  assert (RR1 : forall x, In x kf_rest -> getr r1 x = getr regs x)
    by (unfold kf_rest; intros x Hx; apply AG1; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [notin_lit|]); destruct Hx).
  rewrite <- (with_vmmaps_same md) in HW1 |- *.
  (* [comment removed for export] *)
  assert (FAILT : forall r2 (msg k : Z), str16 msg k ->
            getr r2 2 = Z_to_bv 64 (s - 64) -> getr r2 1 = Z_to_bv 64 0x1626c -> getr r2 10 = Z_to_bv 64 msg -> getr r2 11 = Z_to_bv 64 0x10b6d -> getr r2 12 = Z_to_bv 64 0 ->
            (forall x, In x kf_rest -> getr r2 x = getr regs x) -> getr r2 4 = Z_to_bv 64 0x30da0 ->
            realizes SEGS (mkCfg (@mkst fx r2 (0x13ba4 : word) M1 al_rom) (with_vmmaps (m_vmmaps md) md)) S).
  { intros r2 msg k Smsg X2 X1 X10 X11 X12 XR X4. unfold kf_rest in XR.
    apply (returnErrorPtr_W C A M1 _ r2 (s - 64) msg 0x10b6d k 19 (Z_to_bv 64 0x1626c) (Z_to_bv 64 0) S CK HW1 X2
             ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity)
             X10 X11 X12 Smsg str_kernelCreateFromPix).
    intros m3 r3 HW3 OUT3 GR3 CS3 A10. unfold LSF in OUT3.
    replace (Z_to_bv 64 0x1626c) with (0x1626c : word) by (apply bv_eq; reflexivity).
    assert (CE3 : kcells m3 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (p_w v) (p_h v)).
    { apply (kcells_frame M1 m3 s); [lia | lia | exact CE1 |]. intros x Hx. apply OUT3. lia. }
    pose proof CE3 as (D1 & D2 & D3 & D4 & D5 & _).
    destruct (kfp_X0 al_rom r3 m3 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) ltac:(lia) ltac:(lia) ltac:(rewrite H1; exact Hret)
                D1 D2 D3 D4 D5 ltac:(csr; reflexivity) A10) as (r4 & RUN4 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact RUN4 |].
    rewrite H1. apply (HK fx A m3 (m_vmmaps md) r4 Hz HW3).
    - apply cs_kept_intro; csr; reflexivity.
    - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 _ m3 _ _ s CK HW1 OUT3); lia.
    - left. split; [exact V10 | intros q; reflexivity].
    - exact HRMF. }
  destruct (Z.eq_dec (p_d v) 8) as [Hd8 | Hdn].
  2:{ (* [comment removed for export] *)
      destruct (kfp_Bd al_rom r1 M1 s (p_d v) ltac:(lia) Hdn (W_sev_got C A M1 _ HW1) (W_sev C A M1 _ HW1) Q2 Q10 Q11) as (r2 & RUN2 & X2 & X1 & X10 & X11 & X12 & AG2).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
      apply (FAILT r2 0x10bf6%Z 13%Z str_pix_not_8bpp X2 X1 X10 X11 X12); [unfold kf_rest; rest_solve | csr; reflexivity]. }
  rewrite Hd8 in Q10, Ewpl.
  pose proof (wpl8_ge (p_w v) ltac:(lia)) as Hw4. rewrite <- Ewpl in Hw4.
  destruct (Z_lt_ge_dec 2 (Z.min (p_w v) (p_h v))) as [Hbig | Hsmall].
  2:{ (* [comment removed for export] *)
      destruct (kfp_Bc al_rom r1 M1 s (p_w v) (p_h v) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) C6 C7 (W_sev_got C A M1 _ HW1) (W_sev C A M1 _ HW1) Q2 Q10 Q11 Q18 Q19)
        as (r2 & RUN2 & X2 & X1 & X10 & X11 & X12 & AG2).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
      apply (FAILT r2 0x10aca%Z 16%Z str_cycx_invalid X2 X1 X10 X11 X12); [unfold kf_rest; rest_solve | csr; reflexivity]. }
  (* [comment removed for export] *)
  destruct (kfp_B al_rom r1 M1 s (p_w v) (p_h v) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) C6 C7 Q2 Q10 Q11 Q18 Q19) as (r2 & RUN2 & X2 & X1 & X10 & X11 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
  assert (Hsz' : (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z) by (rewrite Hd8, <- Ewpl in Hsz; exact Hsz).
  assert (PIXK1 : forall M', PIXat M' pix v -> PIXK C A M' pix v).
  { intros M' PX'. split; [exact PX'|]. split; [exact Hd8|]. repeat split; first [assumption | lia]. }
  (* [comment removed for export] *)
  assert (HKX : KX C A m md regs s 0 0 (p_h v) (p_w v) (fun _ => 0%Z) S (kR - RK_kfp (p_d v) (p_h v)) (bR - RB_kfp (p_d v) (p_h v) (p_w v)) /\
                forall kel arr rows, KX C A m md regs s kel arr (p_h v) (p_w v) rows S (kR - RK_kfp (p_d v) (p_h v)) (bR - RB_kfp (p_d v) (p_h v) (p_w v))).
  { assert (GEN : forall kel arr rows, KX C A m md regs s kel arr (p_h v) (p_w v) rows S (kR - RK_kfp (p_d v) (p_h v)) (bR - RB_kfp (p_d v) (p_h v) (p_w v))); [| split; [apply GEN | exact GEN]].
    intros kel arr rows fx' A1 M vm1 r Hz' HW' PM' CE' KL' HRX' R2' R9' R4' RR'. unfold V17LeptKernFromPix.kf_rest in RR'.
    pose proof CE' as (D1 & D2 & D3 & D4 & D5 & _).
    destruct (kfp_X2 (fx := fx') al_rom r M s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (Z_to_bv 64 kel) ltac:(lia) ltac:(lia)
                ltac:(rewrite H1; exact Hret) D1 D2 D3 D4 D5 R2' R9') as (r8 & RUN8 & V2 & V1 & V10 & V8 & V9 & V18 & V19 & AG8).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW')) | exact (mp_lazy _ (w_pure _ _ _ _ HW')) | exact RUN8 |].
    rewrite H1. apply (HK fx' A1 M vm1 r8 Hz' HW').
    - apply cs_kept_intro; csr; reflexivity.
    - exact PM'.
    - destruct KL' as [[K0 LQ] | [Hk K]]; [left | right].
      + split; [rewrite V10, K0; reflexivity | exact LQ].
      + exists kel, arr, rows. split; [exact V10 | split; [exact Hk | exact K]].
    - exact HRX'. }
  destruct HKX as [HKX0 HKXk].
  assert (X4 : getr r2 4 = Z_to_bv 64 0x30da0) by (csr; reflexivity).
  apply (kernelCreate_W C A M1 _ r2 (s - 64) (p_w v) (p_h v) (Z_to_bv 64 0x161b8) S kR bR CK HW1 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) X1 ltac:(red; apply bv_eq; reflexivity) X4 X10 X11 ltac:(lia) ltac:(lia) ltac:(nia) HRM ltac:(rewrite <- RK_kfp_8, <- Hd8; exact HRK) ltac:(rewrite <- RB_kfp_8, <- Hd8; exact HRB)).
  intros A2 m2 vm2 r3 HW2 CS2 PM2 RES HRM2. rewrite <- RK_kfp_8, <- RB_kfp_8, <- Hd8 in HRM2. rewrite ?with_vmmaps_twice in HW2 |- *.
  replace (Z_to_bv 64 0x161b8) with (0x161b8 : word) by (apply bv_eq; reflexivity).
  pose proof (kcells_FRM C M1 m2 s _ _ _ _ _ _ _ CK (proj1 PM2) ltac:(lia) ltac:(lia) CE1) as CE2. pose proof CE2 as (D1 & D2 & D3 & D4 & D5 & D6 & D7).
  assert (PX2 : PIXat m2 pix v).
  { apply (PIXat_frame M1 m2 pix v PX1). intros x Hx. exact (LIVK_at A M1 m2 pix 64 x (proj2 PM2) Lp ltac:(lia) ltac:(lia) Hx). }
  assert (PM2' : POSTM C A s m m2) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PM2]; lia]).
  assert (Y2 : getr r3 2 = Z_to_bv 64 (s - 64)) by (csr; reflexivity).
  assert (Y4 : getr r3 4 = Z_to_bv 64 0x30da0) by (csr; reflexivity).
  assert (Y8 : getr r3 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  assert (Y18 : getr r3 18 = Z_to_bv 64 2) by (csr; reflexivity).
  assert (Y19 : getr r3 19 = Z_to_bv 64 2) by (csr; reflexivity).
  assert (RR3 : forall x, In x kf_rest -> getr r3 x = getr regs x) by (unfold kf_rest; unfold kf_rest in RR1; rest_solve).
  set (N := Z.to_nat ((p_h v - 1 - 0) * p_w v + (p_w v - 1 - 0))).
  destruct RES as [[A0 LQ] | (kel & arr & rows & A4a & KR)].
  - (* [comment removed for export] *)
    destruct (kfp_C0 al_rom r3 m2 (W_sev_got C A2 m2 _ HW2) (W_sev C A2 m2 _ HW2) A0) as (r4 & RUN4 & V2 & V1 & V9 & V10 & V11 & V12 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
    apply (returnErrorInt_W C A2 m2 _ r4 (s - 64) 0x103f4 0x104b7 15 15 (Z_to_bv 64 0x162c4) (Z_to_bv 64 1) S CK HW2
             ltac:(rewrite V2; exact Y2) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
             V1 ltac:(red; apply bv_eq; reflexivity) V10 V11 V12 str_kel_not_defined str_kernelSetOrigin).
    intros m5 r5 HW5 OUT5 GR5 CS5 A10. unfold LSF in OUT5.
    replace (Z_to_bv 64 0x162c4) with (0x162c4 : word) by (apply bv_eq; reflexivity).
    assert (CE5 : kcells m5 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (p_w v) (p_h v)).
    { apply (kcells_frame m2 m5 s); [lia | lia | exact CE2 |]. intros x Hx. apply OUT5. lia. }
    pose proof CE5 as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    destruct (kfp_D al_rom r5 m5 s (p_w v) (p_h v) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E6 E7 ltac:(csr; reflexivity)) as (r6 & RUN6 & Z2 & Z18 & Z19 & Z8 & Z9 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN6 |].
    apply (kfp_loop N fx C A m md regs s pix v S 0 0 (fun _ => 0%Z) (kR - RK_kfp (p_d v) (p_h v)) (bR - RB_kfp (p_d v) (p_h v) (p_w v)) A2 m5 vm2 r6 0 0 Hz CK HKX0 HRM2 Hs16 ltac:(unfold LSF; lia) Hhi H4 HW5).
    + eapply POSTM_trans; [exact PM2'|]. apply (POSTM_sub C A A2); [apply sub_live_eq; exact LQ|]. eapply (POSTM_range C A2 m2 _ m5 _ _ s CK HW2 OUT5); lia.
    + apply sub_live_eq. exact LQ.
    + exact CE5.
    + apply PIXK1. apply (PIXat_frame m2 m5 pix v PX2). intros x Hx. apply OUT5. lia.
    + left. split; [reflexivity | exact LQ].
    + lia. + lia. + subst N. rewrite Z2Nat.id by nia. lia.
    + exact Z2. + rewrite Z8. csr. reflexivity. + rewrite Z9. csr. reflexivity. + exact Z18. + exact Z19.
    + csr. reflexivity.
    + unfold kf_rest; unfold kf_rest in RR3; rest_solve.
  - (* [comment removed for export] *)
    pose proof KR as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & ROWS & DIST & RQ).
    assert (Hk1 : (1 <= kel)%Z) by lia.
    destruct (kfp_C1 al_rom r3 m2 kel K1 ltac:(lia) ltac:(rewrite <- (Z.add_0_r kel); apply mod16_plus_mod8; [exact K3 | reflexivity]) (W_sok_blk C A2 m2 _ _ _ (kel + 8) 8 CK HW2 K4 ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia))
                A4a Y18 Y19) as (r4 & RUN4 & V2 & V9 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN4 |].
    set (m3 := wbytes (wbytes m2 _ _) _ _).
    assert (SUB2 : sub_live A A2).
    { intros q k Lq. rewrite (RQ q); [exact Lq | intros ->; rewrite Lq in K5; discriminate | intros ->; rewrite Lq in K15; discriminate |].
      intros i Hi ->. destruct (ROWS i Hi) as (_ & _ & _ & _ & _ & _ & G7 & _). rewrite Lq in G7. discriminate. }
    assert (WP3 : W C A2 m3 (with_vmmaps vm2 md) /\ POSTM C A s m m3).
    { subst m3.
      apply (WP_blk C A A2 m _ _ (Z_to_bv 64 kel) _ 24 _ s CK); [| exact K4 | exact K5 | exact K6 | exact SUB2 | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
      apply (WP_blk C A A2 m _ _ (Z_to_bv 64 kel) _ 24 _ s CK (conj HW2 PM2') K4 K5 K6 SUB2); rewrite ?length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (kel + 8 <= u x < kel + 16)%Z -> m3 x = m2 x).
    { intros x Hx. subst m3. rewrite !wbytes_outside; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; try lia. reflexivity. }
    assert (CE3 : kcells m3 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (p_w v) (p_h v)).
    { apply (kcells_frame m2 m3 s); [lia | lia | exact CE2 |]. intros x Hx. apply OUT3. lia. }
    pose proof CE3 as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    pose proof (live_apart C A2 m2 _ _ _ _ _ CK HW2 K4 (SUB2 _ _ Lp) ltac:(intros E; rewrite <- E, K5 in Lp; discriminate) ltac:(lia) ltac:(lia)) as APkp. rewrite !u_Z2bv in APkp by lia.
    pose proof (live_apart C A2 m2 _ _ _ _ _ CK HW2 K4 K14 ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as APka. rewrite !u_Z2bv in APka by lia.
    assert (KR3 : kern C A A2 m3 kel arr (p_h v) (p_w v) rows).
    { do 6 (split; [assumption|]).
      split; [subst m3; rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia); exact K7|].
      split; [subst m3; rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia); exact K8|].
      split; [subst m3; rewrite !rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ length]; lia); exact K9|].
      do 7 (split; [assumption|]). split; [| split; [exact DIST | exact RQ]].
      intros i Hi. destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). do 8 (split; [assumption|]).
      rewrite <- G9. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply OUT3. lia. }
    destruct (kfp_D al_rom r4 m3 s (p_w v) (p_h v) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) E6 E7 ltac:(rewrite V2; exact Y2)) as (r6 & RUN6 & Z2 & Z18 & Z19 & Z8 & Z9 & AG6).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN6 |].
    apply (kfp_loop N fx C A m md regs s pix v S kel arr rows (kR - RK_kfp (p_d v) (p_h v)) (bR - RB_kfp (p_d v) (p_h v) (p_w v)) A2 m3 vm2 r6 0 0 Hz CK (HKXk kel arr rows) HRM2 Hs16 ltac:(unfold LSF; lia) Hhi H4 HW3 PM3 SUB2 CE3).
    + apply PIXK1. apply (PIXat_frame m2 m3 pix v PX2). intros x Hx. apply OUT3. lia.
    + right. split; [exact Hk1 | exact KR3].
    + lia. + lia. + subst N. rewrite Z2Nat.id by nia. lia.
    + exact Z2. + rewrite Z8. csr. reflexivity. + rewrite Z9. exact V9. + exact Z18. + exact Z19.
    + csr. reflexivity.
    + unfold kf_rest; unfold kf_rest in RR3; rest_solve.
Qed.

End KernFromPixB.
