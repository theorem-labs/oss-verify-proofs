(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.kernel_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure AllocCredit.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptStderr O17LeptBase.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17CL7a.
Import O17CL7a.O17LeptErr. Import O17CL7a.O17LeptKernSegs2.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.O17 Require Import O17LeptPixHdr O17LeptDeser O17LeptKernPix O17LeptKernSegs O17LeptKernC2d O17LeptKernCreate O17LeptKernDestroy O17_code_15000_16000.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptCredit LeptRoomK.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section KernFromPix.
Context {AL : AllocLayout} {CL : CallocLayout} {ACR : AllocCredit}.
Context {PINS : @LeptPins AL LL17} {P16 : O17Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma str_pix_not_8bpp : str16 0x10ba0 13. Proof. str16_tac. Qed.
Lemma str_cycx_invalid : str16 0x10a74 16. Proof. str16_tac. Qed.
Lemma str_kernelCreateFromPix : str16 0x10b17 19. Proof. str16_tac. Qed.
Lemma str_kel_not_defined : str16 0x103e8 15. Proof. str16_tac. Qed.
Lemma str_kernelSetOrigin : str16 0x104ab 15. Proof. str16_tac. Qed.
Lemma str_kernelSetElement : str16 0x1054c 16. Proof. str16_tac. Qed.

#[local] Definition kf_rest : list (bv 5) := [3; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* [comment removed for export] *)
Definition KEL (C : lctx) (A A1 : AS) (M : word -> option byte) (kel arr h w : Z) (rows : Z -> Z) : Prop :=
  (kel = 0%Z /\ forall q, live A1 q = live A q) \/ ((1 <= kel)%Z /\ kern C A A1 M kel arr h w rows).

Lemma kern_mem : forall C A A1 M M' kel arr h w rows, kern C A A1 M kel arr h w rows ->
  (forall x : word, (kel <= u x < kel + 24)%Z -> M' x = M x) -> (forall x : word, (arr <= u x < arr + 8 * h)%Z -> M' x = M x) ->
  kern C A A1 M' kel arr h w rows.
Proof.
  intros C A A1 M M' kel arr h w rows (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & ROWS & DIST & RQ) Ek Ea.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  do 6 (split; [assumption|]).
  split; [rewrite <- K7; apply rdn_ext; rewrite u_Z2bv by lia; [lia | intros x Hx; apply Ek; lia]|].
  split; [rewrite <- K8; apply rdn_ext; rewrite u_Z2bv by lia; [lia | intros x Hx; apply Ek; lia]|].
  split; [rewrite <- K9; apply rdn_ext; rewrite u_Z2bv by lia; [lia | intros x Hx; apply Ek; lia]|].
  do 7 (split; [assumption|]). split; [| split; [exact DIST | exact RQ]].
  intros i Hi. destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). do 8 (split; [assumption|]).
  rewrite <- G9. apply rdn_ext; rewrite u_Z2bv by lia; [lia|]. intros x Hx. apply Ea. lia.
Qed.

Lemma KEL_mem : forall C A A1 M M' kel arr h w rows, KEL C A A1 M kel arr h w rows ->
  (kel <> 0%Z -> forall x : word, (kel <= u x < kel + 24)%Z -> M' x = M x) -> (kel <> 0%Z -> forall x : word, (arr <= u x < arr + 8 * h)%Z -> M' x = M x) ->
  KEL C A A1 M' kel arr h w rows.
Proof.
  intros C A A1 M M' kel arr h w rows [X | [Hk K]] Ek Ea; [left; exact X | right]. split; [exact Hk|].
  apply (kern_mem C A A1 M M'); [exact K | apply Ek; lia | apply Ea; lia].
Qed.

Lemma kcells_FRM : forall C M M' s ret s0v s1v s2v s3v w h, Cok C -> FRM C (s - 64) M M' ->
  (c_top C - LSTK <= s - 64)%Z -> (s <= c_top C)%Z ->
  kcells M s ret s0v s1v s2v s3v w h -> kcells M' s ret s0v s1v s2v s3v w h.
Proof.
  intros C M M' s ret s0v s1v s2v s3v w h CK F Hlo Hhi (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  pose proof CK as [T1 T2 T3 T4 T5]. unfold kcells.
  rewrite !(FRM_rdn16 C (s - 64) M M' _ _ CK F) by lia. repeat split; assumption.
Qed.

(* [comment removed for export] *)
Definition PIXK (C : lctx) (A : AS) (M : word -> option byte) (pix : Z) (v : pixv) : Prop :=
  PIXat M pix v /\ p_d v = 8%Z /\ (3 <= p_w v)%Z /\ (3 <= p_h v)%Z /\ (p_w v <= 4 * p_wpl v)%Z /\ (4 * (p_wpl v * p_h v) <= 2 ^ 26)%Z /\
  (p_w v <= 20000)%Z /\ (p_h v <= 20000)%Z /\
  (p_data v mod 16 = 0)%Z /\ (1 <= p_data v)%Z /\ (4096 <= pix)%Z /\ (pix + 64 <= alloc_top (c_vm C))%Z /\ (p_data v + 4 * (p_wpl v * p_h v) <= alloc_top (c_vm C))%Z /\
  live A (Z_to_bv 64 pix) = Some 64%Z /\ live A (Z_to_bv 64 (p_data v)) = Some (4 * (p_wpl v * p_h v))%Z.

Lemma PIXK_mem : forall C A M M' pix v, PIXK C A M pix v -> (forall x : word, (pix <= u x < pix + 64)%Z -> M' x = M x) -> PIXK C A M' pix v.
Proof.
  intros C A M M' pix v (PX & REST) E. split; [exact (PIXat_frame M M' pix v PX E) | exact REST].
Qed.

(* [comment removed for export] *)
Definition KX (C : lctx) (A : AS) (m : word -> option byte) (md : Model) (regs : bvmap 5 word) (s kel arr h w : Z) (rows : Z -> Z) (S : TSet) (kX bX : Z) : Prop :=
  forall (fx' : FPState) A1 M vm1 r, frm_zero (@fp_csr fx') -> W C A1 M (with_vmmaps vm1 md) -> POSTM C A s m M ->
    kcells M s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) w h ->
    KEL C A A1 M kel arr h w rows ->
    aroom A1 vm1 kX bX ->
    getr r 2 = Z_to_bv 64 (s - 64) -> getr r 9 = Z_to_bv 64 kel -> getr r 4 = Z_to_bv 64 0x30520 -> (forall x, In x kf_rest -> getr r x = getr regs x) ->
    realizes SEGS (mkCfg (@mkst fx' r (0x15a00 : word) M al_rom) (with_vmmaps vm1 md)) S.

(* [comment removed for export] *)
Lemma kfp_body : forall (fx : FPState) C A m md regs (s pix : Z) (v : pixv) (S : TSet) (kel arr : Z) (rows : Z -> Z) A1 M1 vm1 r (i j : Z),
  frm_zero (@fp_csr fx) -> Cok C ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + 80 + LSF <= s)%Z -> (s <= c_top C)%Z -> getr regs 4 = Z_to_bv 64 0x30520 ->
  W C A1 M1 (with_vmmaps vm1 md) -> POSTM C A s m M1 -> sub_live A A1 ->
  kcells M1 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (p_w v) (p_h v) ->
  PIXK C A M1 pix v -> KEL C A A1 M1 kel arr (p_h v) (p_w v) rows ->
  (0 <= i < p_h v)%Z -> (0 <= j < p_w v)%Z ->
  getr r 2 = Z_to_bv 64 (s - 64) -> getr r 8 = Z_to_bv 64 pix -> getr r 9 = Z_to_bv 64 kel -> getr r 18 = Z_to_bv 64 i -> getr r 19 = Z_to_bv 64 j ->
  getr r 4 = Z_to_bv 64 0x30520 -> (forall x, In x kf_rest -> getr r x = getr regs x) ->
  (forall fr cs M3 r6, frm_zero cs -> W C A1 M3 (with_vmmaps vm1 md) -> POSTM C A s m M3 ->
     kcells M3 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (p_w v) (p_h v) ->
     PIXK C A M3 pix v -> KEL C A A1 M3 kel arr (p_h v) (p_w v) rows ->
     getr r6 2 = Z_to_bv 64 (s - 64) -> getr r6 8 = Z_to_bv 64 pix -> getr r6 9 = Z_to_bv 64 kel -> getr r6 18 = Z_to_bv 64 i -> getr r6 19 = Z_to_bv 64 j ->
     getr r6 4 = Z_to_bv 64 0x30520 -> (forall x, In x kf_rest -> getr r6 x = getr regs x) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr cs) r6 (0x15a9c : word) M3 al_rom) (with_vmmaps vm1 md)) S) ->
  realizes SEGS (mkCfg (@mkst fx r (0x15a70 : word) M1 al_rom) (with_vmmaps vm1 md)) S.
Proof.
  intros fx C A m md regs s pix v S kel arr rows A1 M1 vm1 r i j Hz CK Hs16 Hlo Hhi H4 HW PM SUB CE PK KL Hi Hj R2 R8 R9 R18 R19 R4 RR HK7.
  pose proof PK as (PX & Hd8 & Hw3 & Hh3 & Hw4 & Hsz & Hw2 & Hh2 & ALd & Hd1 & Gp & TOPp & TOPd & LpA & LdA).
  pose proof (SUB _ _ LpA) as Lp. pose proof (SUB _ _ LdA) as Ld.
  pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_w _ WF). pose proof (wf_h _ WF). pose proof (wf_wpl _ WF). pose proof (wf_data _ WF).
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LL17] in *. unfold LSF in *. unfold kf_rest in RR.
  pose proof (alloc_top_lt (c_vm C)) as AT. unfold two_pow_64 in AT.
  (* [comment removed for export] *)
  destruct (kfp_L1 al_rom r M1 s i j (Z_to_bv 64 pix) ltac:(lia) ltac:(lia) R2 R8 R18 R19) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q13 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  (* [comment removed for export] *)
  assert (Hrow : (4 * (p_wpl v * i) + 4 * p_wpl v <= 4 * (p_wpl v * p_h v))%Z).
  { assert (p_wpl v * (i + 1) <= p_wpl v * p_h v)%Z by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (Hwy : (0 <= p_wpl v * i)%Z) by (apply Z.mul_nonneg_nonneg; lia).
  set (L := (p_data v + 4 * (p_wpl v * i))%Z). assert (EL : L = (p_data v + 4 * (p_wpl v * i))%Z) by reflexivity.
  assert (ALL : (L mod 4 = 0)%Z).
  { rewrite EL, Z.mul_comm, Z_mod_plus_full. rewrite <- (Z.add_0_r (p_data v)). apply mod16_plus_mod4; [exact ALd | reflexivity]. }
  pose proof (flip3_bounds L (p_wpl v) (L + j) ALL ltac:(lia)) as Hf.
  set (f := (L + j - (L + j) mod 4 + (3 - (L + j) mod 4))%Z). assert (Ef : f = (L + j - (L + j) mod 4 + (3 - (L + j) mod 4))%Z) by reflexivity.
  clearbody f L.
  destruct (M1 (Z_to_bv 64 f)) as [b|] eqn:Hb.
  2:{ exfalso. destruct (blk_byte C A1 M1 _ (Z_to_bv 64 (p_data v)) _ (Z_to_bv 64 f) CK HW Ld ltac:(rewrite !u_Z2bv by lia; lia)) as (_ & D & _). exact (D Hb). }
  pose proof (u8_range b) as Hb8.
  destruct (pgp_run al_rom r1 M1 (s - 64) (s - 56) pix j i v (Z_to_bv 64 0x15a84) b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) PX Hd8 ltac:(lia) Hw4 Hsz Hj Hi
              ltac:(rewrite <- (Z.add_0_r (p_data v)); apply mod16_plus_mod4; [exact ALd | reflexivity]) Hd1 Gp ltac:(lia) ltac:(lia)
              (W_sok_win C A1 M1 _ (s - 64 - 64) 64 CK HW ltac:(lia) ltac:(cbn; lia)) (W_sok_win C A1 M1 _ (s - 56) 4 CK HW ltac:(lia) ltac:(cbn; lia))
              ltac:(rewrite <- EL, <- Ef; exact Hb) (W_jt8 C A1 M1 _ HW) Q2 Q1 ltac:(red; apply bv_eq; reflexivity) Q10 Q11 Q12 Q13)
    as (r2 & RUN2 & P2 & P10 & P8 & P9 & P18 & P19 & P20 & AG2).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN2 |].
  replace (Z_to_bv 64 0x15a84) with (0x15a84 : word) by (apply bv_eq; reflexivity).
  set (M2 := wbytes (PGF M1 (s - 64) (s - 56) (Z_to_bv 64 0x15a84) r1 (p_w v) (p_h v) 8) (Z_to_bv 64 (s - 56)) (word_to_le_bytes 4 (Z_to_bv 64 (u b)))).
  assert (OUT2 : forall x : word, ~ (s - 128 <= u x < s - 64)%Z -> ~ (s - 56 <= u x < s - 52)%Z -> M2 x = M1 x).
  { intros x N1 N2. subst M2. rewrite wbytes_outside; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    apply PGF_out; lia. }
  assert (GR2 : mem_grows M1 M2).
  { subst M2. unfold PGF. repeat (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
  assert (HW2 : W C A1 M2 (with_vmmaps vm1 md)).
  { apply (W_local C A1 M1 _ M2 s CK HW ltac:(lia)); [|exact GR2]. intros a NE. left. unfold scratch.
    destruct (Z_lt_ge_dec (u a) (s - 128)); [exfalso; apply NE; apply OUT2; lia|].
    destruct (Z_lt_ge_dec (u a) (s - 52)); [lia|]. exfalso; apply NE; apply OUT2; lia. }
  assert (PM2 : POSTM C A s m M2).
  { eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A1 _ _ _ SUB).
    eapply (POSTM_range C A1 M1 _ M2 (s - 128) s s CK HW); [| lia | lia | lia]. intros a Na. apply OUT2; lia. }
  assert (CE2 : kcells M2 s (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (p_w v) (p_h v)).
  { apply (kcells_frame M1 M2 s); [lia | lia | exact CE |]. intros x Hx. apply OUT2; lia. }
  assert (PK2 : PIXK C A M2 pix v) by (apply (PIXK_mem C A M1 M2 pix v PK); intros x Hx; apply OUT2; lia).
  assert (KL2 : KEL C A A1 M2 kel arr (p_h v) (p_w v) rows).
  { apply (KEL_mem C A A1 M1 M2 _ _ _ _ _ KL); intros Hk x Hx; destruct KL as [[K0 _]|[_ K]]; try lia;
      pose proof K as (K1 & K2 & _ & _ & _ & _ & _ & _ & _ & K10 & K11 & _); apply OUT2; lia. }
  (* [comment removed for export] *)
  destruct (kfp_L2 al_rom r2 M2 s (u b) ltac:(lia) ltac:(lia) Hb8 ltac:(subst M2; apply rdn_wbytes_hit4; rewrite u_Z2bv by lia; lia) P2) as (r3 & RUN3 & X2 & X10 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN3 |].
  destruct (kfp_fcvt al_rom fx r3 M2 Hz) as (fr & cs & Hz' & RUN4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN4 |].
  clear Hz RUN1 RUN2 RUN3 RUN4.
  (* [comment removed for export] *)
  destruct (kfp_L3 (fx := mkFP fr cs) al_rom r3 M2 i j (Z_to_bv 64 kel) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity))
    as (r4 & RUN5 & Y2 & Y1 & Y10 & Y11 & Y12 & AG4).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN5 |].
  assert (Y2' : getr r4 2 = Z_to_bv 64 (s - 64)) by (rewrite Y2; csr; reflexivity).
  assert (RR4 : forall x, In x kf_rest -> getr r4 x = getr regs x) by (unfold kf_rest; rest_solve).
  assert (Y8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
  assert (Y9 : getr r4 9 = Z_to_bv 64 kel) by (csr; reflexivity).
  assert (Y18 : getr r4 18 = Z_to_bv 64 i) by (csr; reflexivity).
  assert (Y19 : getr r4 19 = Z_to_bv 64 j) by (csr; reflexivity).
  assert (Y4 : getr r4 4 = Z_to_bv 64 0x30520) by (csr; reflexivity).
  destruct KL2 as [[K0 LQ] | [Hk K]].
  - (* [comment removed for export] *)
    rewrite K0 in Y10.
    destruct (kse_null (fx := mkFP fr cs) al_rom r4 M2 (W_sev_got C A1 M2 _ HW2) (W_sev C A1 M2 _ HW2) Y10) as (r5 & RUN6 & V2 & V1 & V10 & V11 & V12 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN6 |].
    apply (returnErrorInt_W (fx := mkFP fr cs) C A1 M2 _ r5 (s - 64) 0x103e8 0x1054c 15 16 (Z_to_bv 64 0x15a9c) (Z_to_bv 64 1) S CK HW2
             ltac:(rewrite V2; exact Y2') ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia)
             ltac:(rewrite V1; exact Y1) ltac:(red; apply bv_eq; reflexivity) V10 V11 V12 str_kel_not_defined str_kernelSetElement).
    intros M3 r6 HW3 OUT3 GR3 CS3 A10. unfold LSF in OUT3.
    replace (Z_to_bv 64 0x15a9c) with (0x15a9c : word) by (apply bv_eq; reflexivity).
    apply (HK7 fr cs M3 r6 Hz' HW3).
    + eapply POSTM_trans; [exact PM2|]. apply (POSTM_sub C A A1 _ _ _ SUB).
      eapply (POSTM_range C A1 M2 _ M3 _ _ s CK HW2 OUT3); lia.
    + apply (kcells_frame M2 M3 s); [lia | lia | exact CE2 |]. intros x Hx. apply OUT3. lia.
    + apply (PIXK_mem C A M2 M3 pix v PK2). intros x Hx. apply OUT3. lia.
    + left. split; [exact K0 | exact LQ].
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. rewrite K0. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + unfold kf_rest; rest_solve.
  - (* [comment removed for export] *)
    pose proof K as (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15 & K16 & ROWS & DIST & RQ).
    destruct (ROWS i Hi) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
    assert (SOKr : store_ok SEGS M2 (Z_to_bv 64 (rows i + 4 * j)) 4 = true).
    { apply (W_sok_blk C A1 M2 _ _ _ (rows i + 4 * j) 4 CK HW2 G6); rewrite u_Z2bv by lia; cbn; lia. }
    destruct (kse_ok (fx := mkFP fr cs) al_rom r4 M2 kel (p_h v) (p_w v) arr (rows i) i j (Z_to_bv 64 0x15a9c) K1 ltac:(lia) K10 ltac:(lia) G1 ltac:(lia)
                Hi Hj ltac:(lia) ltac:(lia)
                ltac:(rewrite <- (w2b4_Z (p_h v)) by lia; exact K7) ltac:(rewrite <- (w2b4_Z (p_w v)) by lia; exact K8)
                ltac:(rewrite <- (w2b_Z 8 arr) by lia; exact K9) ltac:(rewrite <- (w2b_Z 8 (rows i)) by lia; exact G9)
                SOKr Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11 Y12) as (r5 & RUN6 & V2 & V10 & AG5).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN6 |].
    replace (Z_to_bv 64 0x15a9c) with (0x15a9c : word) by (apply bv_eq; reflexivity).
    set (M3 := wbytes M2 _ _).
    assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A s m M3).
    { subst M3. apply (WP_blk C A A1 m M2 _ (Z_to_bv 64 (rows i)) _ (4 * p_w v) _ s CK (conj HW2 PM2) G6 G7 G8 SUB); rewrite ?length_Z_to_le_bytes, !u_Z2bv by lia; cbn; lia. }
    destruct WP3 as [HW3 PM3].
    assert (OUT3 : forall x : word, ~ (rows i <= u x < rows i + 4 * p_w v)%Z -> M3 x = M2 x).
    { intros x Hx. subst M3. apply wbytes_outside; rewrite ?length_Z_to_le_bytes, ?u_Z2bv by lia; cbn; lia. }
    pose proof (live_apart C A1 M2 _ _ _ _ _ CK HW2 K4 G6 ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as APkr. rewrite !u_Z2bv in APkr by lia.
    pose proof (live_apart C A1 M2 _ _ _ _ _ CK HW2 K14 G6 ltac:(apply zbv_ne; lia) ltac:(lia) ltac:(lia)) as APar. rewrite !u_Z2bv in APar by lia.
    assert (NEpr : Z_to_bv 64 pix <> Z_to_bv 64 (rows i)) by (intros E; rewrite E, G7 in LpA; discriminate).
    pose proof (live_apart C A1 M2 _ _ _ _ _ CK HW2 Lp G6 NEpr ltac:(lia) ltac:(lia)) as APpr. rewrite !u_Z2bv in APpr by lia.
    apply (HK7 fr cs M3 r5 Hz' HW3 PM3).
    + apply (kcells_frame M2 M3 s); [lia | lia | exact CE2 |]. intros x Hx. apply OUT3. lia.
    + apply (PIXK_mem C A M2 M3 pix v PK2). intros x Hx. apply OUT3. lia.
    + right. split; [exact Hk|]. apply (kern_mem C A A1 M2 M3 _ _ _ _ _ K); intros x Hx; apply OUT3; lia.
    + rewrite V2. exact Y2'.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + csr. reflexivity.
    + unfold kf_rest; rest_solve.
Qed.

End KernFromPix.
