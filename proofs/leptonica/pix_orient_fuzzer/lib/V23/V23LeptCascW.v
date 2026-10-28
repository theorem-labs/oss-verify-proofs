(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic PFLib LeptDefs LeptStructs LeptArith LeptArith2 LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptPixCopyTR O23LeptPixHdrT2 O23LeptRbLib O23LeptRb2W O23LeptCascW.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCreateT2.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptErr V23LeptCasc V23LeptRb2W.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require V23LeptPixDestroyK V23LeptPixMisc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require SeqExec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma str_casc_null : str16 0x10355 16.
Proof. str16_tac. Qed.
Lemma str_casc : str16 0x15c90 26.
Proof. str16_tac. Qed.
Lemma str_casc_rb2 : str16 0x16386 20.
Proof. str16_tac. Qed.

Definition CASC_STACK : Z := 96 + RB2_STACK.

Section CascN.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Theorem pixReduceRankBinary2_null_W : forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RB2_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa6f20 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold RB2_STACK, LSF in Hlo.
  pose proof (W_sok_win C A m md (s - 208) 208 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  set (M1 := FRBn m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold FRBn; wp_win CK).
  destruct WP1 as [HW1 PM1].
  destruct (rb_N al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A M1 md HW1) (W_sev C A M1 md HW1) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (returnErrorPtr_W C A M1 md r1 s 0x10355 0x16386 16 20 ret (Z_to_bv 64 0) S CK HW1 Q2 Hs16
           ltac:(unfold LSF; lia) Hhi Q1 Hret Q10 Q11 Q12 str_casc_null str_casc_rb2).
  intros m2 r2 HW2 OUT2 MG2 CS2 V10.
  apply (HK m2 r2 HW2).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 md m2); [exact CK | exact HW1 | exact OUT2 | unfold LSF; lia | lia | lia].
  - exact V10.
Qed.

(* [comment removed for export] *)
Theorem pixReduceRankBinaryCascade_null_W : forall C A m md regs (s : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CASC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 0 ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0xa6c38 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H10 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold CASC_STACK, RB2_STACK, LSF in Hlo.
  pose proof (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  set (M1 := FCS m s ret regs).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; unfold FCS; wp_win CK).
  destruct WP1 as [HW1 PM1].
  destruct (cs_N al_rom regs m s ret ltac:(lia) ltac:(lia) SOK (W_sev_got C A M1 md HW1) (W_sev C A M1 md HW1) H2 H1 H10)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (returnErrorPtr_W C A M1 md r1 s 0x10355 0x15c90 16 26 ret (Z_to_bv 64 0) S CK HW1 Q2 Hs16
           ltac:(unfold LSF; lia) Hhi Q1 Hret Q10 Q11 Q12 str_casc_null str_casc).
  intros m2 r2 HW2 OUT2 MG2 CS2 V10.
  apply (HK m2 r2 HW2).
  - apply cs_kept_intro; csr; reflexivity.
  - eapply POSTM_trans; [exact PM1|]. eapply (POSTM_range C A M1 md m2); [exact CK | exact HW1 | exact OUT2 | unfold LSF; lia | lia | lia].
  - exact V10.
Qed.
End CascN.

Definition CSC (s : Z) (ret : word) (regs : bvmap 5 word) : list (Z * word) :=
  [(s - 8, ret); (s - 16, getr regs 8); (s - 24, getr regs 9); (s - 32, getr regs 18); (s - 40, getr regs 19); (s - 48, getr regs 20);
   (s - 56, getr regs 21); (s - 64, getr regs 22)]%Z.

Lemma cells_FCS : forall m s ret regs, (96 <= s)%Z -> (s < 2 ^ 64)%Z -> cellsZ (FCS m s ret regs) (CSC s ret regs).
Proof. intros m s ret regs Hs Hs64. unfold CSC, FCS. cbn [cellsZ]. repeat split; rdn_solve. Qed.

Section CascT.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma cw_sok_blk : forall C A m md (p : word) (k a : Z) (n : nat), Cok C -> W C A m md -> live A p = Some k ->
  (u p <= a)%Z -> (a + Z.of_nat n <= u p + k)%Z -> (u p + k < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 a) n = true.
Proof.
  intros C A m md p k a n CK HW L Hlo Hhi Hk. pose proof (u64_range p). rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|].
  intros x Hx. unfold wview. destruct (m x) eqn:E; [discriminate|]. exfalso.
  destruct (blk_byte C A m md p k x CK HW L ltac:(lia)) as (_ & D & _). exact (D E).
Qed.

Definition FTt (tab : Z) (mB m : word -> option byte) : Prop := forall a : word, ~ (tab <= u a < tab + 256)%Z -> m a = mB a.

(* [comment removed for export] *)
Lemma cs_tab_W : forall {fx : FPState} C Ar A md mB (s tab : Z) (S : TSet),
  Cok C -> sub_live Ar A -> live A (Z_to_bv 64 tab) = Some 256%Z -> live Ar (Z_to_bv 64 tab) = None ->
  live (c_A0 C) (Z_to_bv 64 tab) = None -> (4096 <= tab)%Z -> (tab + 256 < 2 ^ 64)%Z ->
  forall (n : nat) (r0 r : bvmap 5 word) (m : word -> option byte) (k : Z),
  W C A m md -> POSTM C Ar s mB m -> FTt tab mB m -> (0 <= k)%Z -> (Z.of_nat n = 255 - k)%Z ->
  regs_agree (fun x => In x [5; 6; 7; 11; 12; 13; 14; 16; 17; 22; 28; 29; 30; 31]%list) r0 r ->
  getr r 18 = Z_to_bv 64 tab -> getr r 15 = Z_to_bv 64 1 -> getr r 16 = Z_to_bv 64 (tab + k) -> getr r 17 = Z_to_bv 64 (tab + k) ->
  getr r 22 = Z_to_bv 64 (256 - k) ->
  (forall m' r', W C A m' md -> POSTM C Ar s mB m' -> FTt tab mB m' ->
     regs_agree (fun x => In x [1; 5; 6; 7; 10; 11; 12; 13; 14; 16; 17; 22; 28; 29; 30; 31]%list) r0 r' ->
     getr r' 1 = Z_to_bv 64 0xa6d58 -> getr r' 10 = getr r0 21 -> getr r' 11 = getr r0 20 -> getr r' 12 = Z_to_bv 64 tab ->
     realizes SEGS (mkCfg (mkst r' (0xa6f20 : word) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst r (0xa6cd0 : word) m al_rom) md) S.
Proof.
  intros fx C Ar A md mB s tab S CK SUB Lt Ltr Lt0 Ht Ht2.
  induction n as [|n IH]; intros r0 r m k HW PM FT Hk Hn AG R18 R15 R16 R17 R22 HC.
  - assert (Ek : k = 255%Z) by lia. subst k.
    pose proof (cw_sok_blk C A m md (Z_to_bv 64 tab) 256 (tab + 255) 1 CK HW Lt
                  ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia)) as SOK.
    destruct (cs_Tx al_rom r m tab 255 (u (getr r0 21)) (u (getr r0 20)) eq_refl Ht Ht2 SOK R18 R15 R16 R17 R22
                ltac:(rewrite (AG 21) by notin_lit; symmetry; apply zbv_self) ltac:(rewrite (AG 20) by notin_lit; symmetry; apply zbv_self))
      as (r' & x & RUN & V1 & V10 & V11 & V12 & AG').
    rewrite zbv_self in V10, V11.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply HC; [| | | | exact V1 | exact V10 | exact V11 | exact V12].
    + eapply W_store_blk; [exact CK | exact HW | exact Lt | exact Lt0 | rewrite !u_Z2bv by lia; lia
                          | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    + eapply POSTM_trans; [exact PM|]. eapply (POSTM_blk C Ar A m md (Z_to_bv 64 tab)); [exact CK | exact HW | exact Lt | exact Ltr | exact SUB
                          | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    + intros a Ha. rewrite wbytes_outside; [apply FT; exact Ha | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                                         | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    + eapply regs_agree_trans; [regs_agree_weaken AG | exact AG'].
  - pose proof (cw_sok_blk C A m md (Z_to_bv 64 tab) 256 (tab + k) 1 CK HW Lt
                  ltac:(rewrite u_Z2bv by lia; lia) ltac:(rewrite u_Z2bv by lia; cbn; lia) ltac:(rewrite u_Z2bv by lia; lia)) as SOK.
    destruct (cs_Tn al_rom r m tab k Hk ltac:(lia) Ht Ht2 SOK R18 R15 R16 R17 R22) as (r' & x & RUN & V18 & V15 & V16 & V17 & V22 & AG').
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].
    apply (IH r0 r' _ (k + 1)%Z); [| | | lia | lia | | exact V18 | exact V15 | exact V16 | exact V17 | exact V22 | exact HC].
    + eapply W_store_blk; [exact CK | exact HW | exact Lt | exact Lt0 | rewrite !u_Z2bv by lia; lia
                          | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    + eapply POSTM_trans; [exact PM|]. eapply (POSTM_blk C Ar A m md (Z_to_bv 64 tab)); [exact CK | exact HW | exact Lt | exact Ltr | exact SUB
                          | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
    + intros a Ha. rewrite wbytes_outside; [apply FT; exact Ha | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia
                                         | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia].
    + eapply regs_agree_trans; [exact AG | exact AG'].
Qed.
End CascT.

Lemma csw_m8 : forall s, (s mod 16 = 0)%Z -> ((s - 72) mod 8 = 0)%Z.
Proof. intros s H. replace (s - 72)%Z with (s + -72)%Z by lia. apply mod16_plus_mod8; [exact H | reflexivity]. Qed.

Ltac wbo := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; apply wbytes_outside; rewrite ?length_N_to_le_bytes, u_Z2bv by lia; cbn; lia.

Section CascW.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Lemma cs_tail_W : forall {fx : FPState} C A m md r regs (s tab : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CASC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr r 2 = Z_to_bv 64 (s - 96) -> getr r 9 = Z_to_bv 64 0 -> getr r 18 = Z_to_bv 64 tab ->
  getr regs 4 = Z_to_bv 64 0x1381d0 -> (forall x, In x [3; 4; 23; 24; 25; 26; 27]%list -> getr r x = getr regs x) ->
  live A (Z_to_bv 64 tab) = Some 256%Z -> live (c_A0 C) (Z_to_bv 64 tab) = None ->
  cellsZ m (CSC s ret regs) ->
  (forall A' m' vm' r', W C A' m' (with_vmmaps vm' md) -> cs_kept regs r' -> getr r' 10 = getr r 19 ->
     live A' (Z_to_bv 64 tab) = None -> (forall q, q <> Z_to_bv 64 tab -> live A' q = live A q) ->
     POSTM C A' (s - 96) m m' -> roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst r' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst r (0xa6d7c : word) m al_rom) md) S.
Proof.
  intros fx C A m md r regs s tab ret S CK HW Hs16 Hlo Hhi Hret H2 R2 R9 R18 H4 RR Lt Lt0 CE HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  unfold CASC_STACK, RB2_STACK, LSF in Hlo.
  destruct (cs_E al_rom r m R9) as (r1 & RUN1 & E1 & E10 & AG1).
  rzm HW RUN1.
  replace (0x10e818 : word) with (Z_to_bv 64 0x10e818) by (apply bv_eq; reflexivity).
  apply (W_free16 C A m md r1 (Z_to_bv 64 tab) (Z_to_bv 64 0xa6f04) 256 (s - 96) S CK HW ltac:(rewrite E10; exact R18) Lt Lt0 E1
           ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
  intros A' m' vm' r' HW' CS' Lt' LEQ PM RT.
  replace (Z_to_bv 64 0xa6f04) with (0xa6f04 : word) by (apply bv_eq; reflexivity).
  pose proof (cellsZ_frm C (s - 96) m m' (CSC s ret regs) CK (proj1 PM) ltac:(lia) ltac:(unfold CSC; fa9) CE) as CE'.
  unfold CSC in CE'.
  destruct (cs_F al_rom r' m' s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
              (getr regs 22) ltac:(lia) ltac:(lia) Hret CE' ltac:(csr; reflexivity))
    as (r2 & RUN2 & F2 & F1 & F10 & F8 & F9 & F18 & F19 & F20 & F21 & F22 & AG2).
  rzm HW' RUN2.
  apply (HK A' m' vm' r2 HW'); [| csr; reflexivity | exact Lt' | exact LEQ | exact PM | exact RT].
  apply cs_kept_intro; csr; reflexivity.
Qed.

Lemma cs_second_null_W : forall fr C Ar A m md regs (s pixs rc w h cm datas : Z) (ret : word) (S : TSet) (kR bR : Z)
    fr1 cs1 A2 m5 vm2 r5 (tab : Z),
  Cok C -> W C A2 m5 (with_vmmaps vm2 md) -> frm_zero cs1 -> (forall r : reg, In (u r) fs_list -> reg_get fr1 r = reg_get fr r) ->
  sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CASC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr r5 2 = Z_to_bv 64 (s - 96) -> getr r5 9 = Z_to_bv 64 0 -> getr r5 18 = Z_to_bv 64 tab -> getr r5 19 = Z_to_bv 64 1 ->
  getr r5 10 = Z_to_bv 64 0 -> (forall x, In x [3; 4; 23; 24; 25; 26; 27]%list -> getr r5 x = getr regs x) ->
  cellsZ m5 (CSC s ret regs) -> POSTM C Ar s m m5 -> LIVKe A datas m m5 -> PIXat m5 pixs (hdvr rc w h 1 cm datas) ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  live A2 (Z_to_bv 64 tab) = Some 256%Z -> live (c_A0 C) (Z_to_bv 64 tab) = None -> live A (Z_to_bv 64 tab) = None ->
  (forall q, q <> Z_to_bv 64 tab -> live A2 q = live A q) ->
  aroom A2 vm2 (kR - 1 - RK_pix) (bR - 2 ^ 17 - RB_pixT (4 * (wpl_of (w / 2) 1 * (h / 2)))) ->
  (RK_casc <= kR)%Z -> (RB_casc w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     cs_kept regs regs' -> POSTM C Ar s m m' -> LIVKe A datas m m' -> PIXat m' pixs (hdvr rc w h 1 cm datas) ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pix2 data2, getr regs' 10 = Z_to_bv 64 pix2 /\ (4 <= w)%Z /\ (4 <= h)%Z /\ O23LeptPixHdrT2.hdr_ok (w / 2 / 2) (h / 2 / 2) 1 /\
             O23LeptPixCreateT2.pixr_new C A A' m' pix2 data2 (set_data (O23LeptPixHdrT2.pix_hdr (w / 2 / 2) (h / 2 / 2) 1) data2)) ) ->
     aroom A' vm' (kR - RK_casc) (bR - RB_casc w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r5 (0xa6d58 : word) m5 al_rom) (with_vmmaps vm2 md)) S.
Proof.
  intros fr C Ar A m md regs s pixs rc w h cm datas ret S kR bR fr1 cs1 A2 m5 vm2 r5 tab CK HW5 FZ1 FS1 SUB H2 Hs16 Hlo Hhi Hret H4
    R2 R9 R18 R19 R10 RR CE5 PM5 LE5 PX5 Lp Lt2 Lt0 Lta LEQ Hrm HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof Hlo as Hlo'. unfold CASC_STACK, RB2_STACK, LSF in Hlo'.
  assert (SUBA2 : sub_live A A2).
  { intros q k Lq. rewrite LEQ; [exact Lq | intros E; rewrite E, Lta in Lq; discriminate]. }
  pose proof (W_sok_win C A2 m5 _ (s - 72) 8 CK HW5 ltac:(lia) ltac:(cbn; lia)) as SOK6.
  destruct (cs_C (fx := mkFP fr1 cs1) al_rom r5 m5 s ltac:(lia) ltac:(lia) SOK6 R2 R19) as (r6 & RUN6 & C1 & C10 & C11 & C12 & AG6).
  rzm HW5 RUN6.
  rewrite R10 in C10 |- *.
  assert (WP6 : W C A2 (wbytes m5 (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm2 md) /\
                POSTM C A s m5 (wbytes m5 (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0)))) by wp_win CK.
  destruct WP6 as [HW6 PA6].
  apply (pixReduceRankBinary2_null_W (fx := mkFP fr1 cs1) C A2 _ _ r6 (s - 96) (Z_to_bv 64 0xa6d6c) S CK HW6
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold RB2_STACK, LSF; lia) ltac:(lia)
           C1 ltac:(red; apply bv_eq; reflexivity) C10).
  intros m7 r7 HW7 CS7 PM7 V10.
  replace (Z_to_bv 64 0xa6d6c) with (0xa6d6c : word) by (apply bv_eq; reflexivity).
  pose proof (W_sok_win C A2 m7 _ (s - 80) 8 CK HW7 ltac:(lia) ltac:(cbn; lia)) as SOK8.
  destruct (cs_D (fx := mkFP fr1 cs1) al_rom r7 m7 s ltac:(lia) ltac:(lia) SOK8 ltac:(csr; reflexivity)) as (r8 & RUN8 & D1 & D10 & D19 & AG8).
  rzm HW7 RUN8.
  rewrite V10.
  assert (PA7 : POSTM C A s m5 m7).
  { eapply POSTM_trans; [exact PA6|]. apply (POSTM_sub C A A2); [exact SUBA2|]. eapply POSTM_mono; [|exact PM7]; lia. }
  assert (WP8 : W C A2 (wbytes m7 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (with_vmmaps vm2 md) /\
                POSTM C A s m5 (wbytes m7 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (Z_to_bv 64 0)))) by wp_win CK.
  destruct WP8 as [HW8 PA8].
  assert (Rpp : rdn SEGS (wbytes m7 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (Z_to_bv 64 (s - 72)) 8
                = Some (Z_to_le_bytes 8 0)).
  { rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
    rewrite (FRM_rdn16 C (s - 96) _ m7 (s - 72) 8 CK (proj1 PM7)) by (cbn; lia).
    rewrite SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia).
    rewrite w2l_Z8 by lia. reflexivity. }
  apply (V23LeptPixMisc.pixDestroy_null_W (fx := mkFP fr1 cs1) C A2 _ _ r8 (s - 96) (s - 72) None (Z_to_bv 64 0xa6d7c) S CK HW8
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(lia) ltac:(lia) D1
           ltac:(red; apply bv_eq; reflexivity) D10 ltac:(cbn; lia) (csw_m8 s Hs16) Rpp).
  intros m9 r9 HW9 CS9 PM9 OUT9.
  replace (Z_to_bv 64 0xa6d7c) with (0xa6d7c : word) by (apply bv_eq; reflexivity).
  assert (PA9 : POSTM C A s m5 m9).
  { eapply POSTM_trans; [exact PA8|]. apply (POSTM_sub C A A2); [exact SUBA2|]. eapply POSTM_mono; [|exact PM9]; lia. }
  pose proof (cellsZ_out m5 (wbytes m5 (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (s - 72) (s - 64) (CSC s ret regs)
                ltac:(wbo) ltac:(unfold CSC; fa9) CE5) as CE6.
  pose proof (cellsZ_frm C (s - 96) _ m7 (CSC s ret regs) CK (proj1 PM7) ltac:(lia) ltac:(unfold CSC; fa9) CE6) as CE7.
  pose proof (cellsZ_out m7 (wbytes m7 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (Z_to_bv 64 0))) (s - 80) (s - 72) (CSC s ret regs)
                ltac:(wbo) ltac:(unfold CSC; fa9) CE7) as CE8.
  pose proof (cellsZ_frm C (s - 96) _ m9 (CSC s ret regs) CK (proj1 PM9) ltac:(lia) ltac:(unfold CSC; fa9) CE8) as CE9.
  apply (cs_tail_W (fx := mkFP fr1 cs1) C A2 m9 _ r9 regs s tab ret S CK HW9 Hs16 Hlo Hhi Hret H2
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) H4 ltac:(erest) Lt2 Lt0 CE9).
  intros A5 m10 vm5 r10 HW10 CS10 R1010 Lt5 LEQ5 PM10 RT.
  rewrite with_vmmaps_twice in HW10 |- *.
  assert (SUBA5 : sub_live A A5).
  { intros q k Lq. rewrite LEQ5; [apply SUBA2; exact Lq | intros E; rewrite E, Lta in Lq; discriminate]. }
  assert (PA10 : POSTM C A s m5 m10).
  { eapply POSTM_trans; [exact PA9|]. apply (POSTM_sub C A A5); [exact SUBA5|]. eapply POSTM_mono; [|exact PM10]; lia. }
  apply (HK fr1 cs1 A5 m10 vm5 r10 HW10 FZ1 FS1 CS10).
  - eapply POSTM_trans; [exact PM5 | apply (POSTM_sub C Ar A); [exact SUB | exact PA10]].
  - apply (LIVKe_trans A datas m m5 m10); [exact LE5 | apply LIVKe_of; exact (proj2 PA10)].
  - exact (rbw_PIX_livk A m5 m10 pixs _ (proj2 PA10) Lp PX5).
  - left. split; [csr; reflexivity |].
    intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 tab)) as [->|NE]; [rewrite Lt5, Lta; reflexivity |].
    rewrite (LEQ5 q NE), (LEQ q NE). reflexivity.
  - rewrite with_vmmaps_vmmaps in RT.
    pose proof (RB_pixT_nonneg (4 * (wpl_of (w / 2) 1 * (h / 2)))) as N1.
    pose proof (RB_pixT_nonneg (4 * (wpl_of (w / 2 / 2) 1 * (h / 2 / 2)))) as N2.
    unfold RK_casc, RB_casc, RK_pix in *.
    pose proof (RT _ _ Hrm ltac:(lia) ltac:(lia)) as X.
    apply (aroom_mono A5 vm5 _ _ _ _ X); lia.
Qed.

Lemma cs_second_W : forall fr C Ar A m md regs (s pixs rc w h cm datas : Z) (ret : word) (S : TSet) (kR bR : Z)
    fr1 cs1 A1 A2 m5 vm2 r5 (tab pix1 data1 : Z),
  Cok C -> W C A2 m5 (with_vmmaps vm2 md) -> frm_zero cs1 -> (forall r : reg, In (u r) fs_list -> reg_get fr1 r = reg_get fr r) ->
  sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CASC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr r5 2 = Z_to_bv 64 (s - 96) -> getr r5 9 = Z_to_bv 64 0 -> getr r5 18 = Z_to_bv 64 tab -> getr r5 19 = Z_to_bv 64 1 ->
  getr r5 10 = Z_to_bv 64 pix1 -> (forall x, In x [3; 4; 23; 24; 25; 26; 27]%list -> getr r5 x = getr regs x) ->
  cellsZ m5 (CSC s ret regs) -> POSTM C Ar s m m5 -> LIVKe A datas m m5 -> PIXat m5 pixs (hdvr rc w h 1 cm datas) ->
  live A (Z_to_bv 64 pixs) = Some 64%Z ->
  live A1 (Z_to_bv 64 tab) = Some 256%Z -> live (c_A0 C) (Z_to_bv 64 tab) = None -> live A (Z_to_bv 64 tab) = None ->
  (0 <= tab < 2 ^ 64)%Z -> (forall q, q <> Z_to_bv 64 tab -> live A1 q = live A q) ->
  (2 <= w)%Z -> (2 <= h)%Z -> O23LeptPixHdrT2.hdr_ok (w / 2) (h / 2) 1 ->
  O23LeptPixCreateT2.pixr_new C A1 A2 m5 pix1 data1 (set_data (O23LeptPixHdrT2.pix_hdr (w / 2) (h / 2) 1) data1) ->
  aroom A2 vm2 (kR - 1 - RK_pix) (bR - 2 ^ 17 - RB_pixT (4 * (wpl_of (w / 2) 1 * (h / 2)))) ->
  (RK_casc <= kR)%Z -> (RB_casc w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     cs_kept regs regs' -> POSTM C Ar s m m' -> LIVKe A datas m m' -> PIXat m' pixs (hdvr rc w h 1 cm datas) ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pix2 data2, getr regs' 10 = Z_to_bv 64 pix2 /\ (4 <= w)%Z /\ (4 <= h)%Z /\ O23LeptPixHdrT2.hdr_ok (w / 2 / 2) (h / 2 / 2) 1 /\
             O23LeptPixCreateT2.pixr_new C A A' m' pix2 data2 (set_data (O23LeptPixHdrT2.pix_hdr (w / 2 / 2) (h / 2 / 2) 1) data2)) ) ->
     aroom A' vm' (kR - RK_casc) (bR - RB_casc w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r5 (0xa6d58 : word) m5 al_rom) (with_vmmaps vm2 md)) S.
Proof.
  intros fr C Ar A m md regs s pixs rc w h cm datas ret S kR bR fr1 cs1 A1 A2 m5 vm2 r5 tab pix1 data1 CK HW5 FZ1 FS1 SUB H2 Hs16 Hlo Hhi
    Hret H4 R2 R9 R18 R19 R10 RR CE5 PM5 LE5 PX5 Lp Lt1 Lt0 Lta Htab LEQ1 Hw2 Hh2 HOK2 PN Hrm HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof Hlo as Hlo'. unfold CASC_STACK, RB2_STACK, LSF in Hlo'.
  destruct PN as (B1 & B2 & B3 & B4 & B5 & B6 & NEpd1 & N1p & N1d & N0p & N0d & L2p & L2d & EQ2 & PX1 & _).
  cbn [p_wpl p_h set_data O23LeptPixHdrT2.pix_hdr] in B5, L2d.
  rewrite csw_hdvr in PX1.
  pose proof (Z.div_mod w 2 ltac:(lia)) as Dw. pose proof (Z.mod_pos_bound w 2 ltac:(lia)) as Mw.
  pose proof (Z.div_mod h 2 ltac:(lia)) as Dh. pose proof (Z.mod_pos_bound h 2 ltac:(lia)) as Mh.
  assert (Hwpl : (1 <= wpl_of (w / 2) 1)%Z) by (unfold wpl_of; apply Z.div_le_lower_bound; lia).
  pose proof (rbw_pos (wpl_of (w / 2) 1) (h / 2) Hwpl ltac:(lia)) as HR.
  assert (NEt1 : Z_to_bv 64 tab <> Z_to_bv 64 pix1) by (intros E; rewrite E, N1p in Lt1; discriminate).
  assert (NEt2 : Z_to_bv 64 tab <> Z_to_bv 64 data1) by (intros E; rewrite E, N1d in Lt1; discriminate).
  assert (Lt2 : live A2 (Z_to_bv 64 tab) = Some 256%Z) by (rewrite EQ2 by assumption; exact Lt1).
  assert (SUBA1 : sub_live A A1).
  { intros q k Lq. rewrite LEQ1; [exact Lq | intros E; rewrite E, Lta in Lq; discriminate]. }
  assert (SUB12 : sub_live A1 A2).
  { intros q k Lq. rewrite EQ2; [exact Lq | intros E; rewrite E, N1p in Lq; discriminate | intros E; rewrite E, N1d in Lq; discriminate]. }
  pose proof (sub_live_trans _ _ _ SUBA1 SUB12) as SUBA2.
  assert (Lap : live A (Z_to_bv 64 pix1) = None) by (rewrite <- LEQ1 by (intros E; apply NEt1; symmetry; exact E); exact N1p).
  assert (Lad : live A (Z_to_bv 64 data1) = None) by (rewrite <- LEQ1 by (intros E; apply NEt2; symmetry; exact E); exact N1d).
  pose proof (W_sok_win C A2 m5 _ (s - 72) 8 CK HW5 ltac:(lia) ltac:(cbn; lia)) as SOK6.
  destruct (cs_C (fx := mkFP fr1 cs1) al_rom r5 m5 s ltac:(lia) ltac:(lia) SOK6 R2 R19) as (r6 & RUN6 & C1 & C10 & C11 & C12 & AG6).
  rzm HW5 RUN6.
  rewrite R10 in C10 |- *.
  assert (WP6 : W C A2 (wbytes m5 (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) (with_vmmaps vm2 md) /\
                POSTM C A2 s m5 (wbytes m5 (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 pix1)))) by wp_win CK.
  destruct WP6 as [HW6 PB6].
  pose proof (rbw_PIX_livk A2 _ _ pix1 _ (proj2 PB6) L2p PX1) as PX6.
  apply (pixReduceRankBinary2_W fr1 cs1 C A A2 _ _ r6 (s - 96) pix1 1 (w / 2) (h / 2) 0 data1 tab (Z_to_bv 64 0xa6d6c) S
           CK HW6 FZ1 SUBA2 ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold RB2_STACK, LSF; lia) ltac:(lia) C1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
           C10 C11 ltac:(rewrite C12; exact R18) PX6 HOK2 ltac:(lia) ltac:(lia) L2p L2d Lad N0d NEpd1 Lt2 Htab
           (kR - 1 - RK_pix) (bR - 2 ^ 17 - RB_pixT (4 * (wpl_of (w / 2) 1 * (h / 2))))
           ltac:(rewrite with_vmmaps_vmmaps; exact Hrm) ltac:(unfold RK_casc in HkR; lia) ltac:(unfold RB_casc in HbR; lia)).
  intros fr2 cs2 A3 m7 vm3 r7 HW7 FZ2 FS2 CS7 PM7 LE7 PX7 RES7 Hrm3.
  rewrite with_vmmaps_twice in HW7 |- *.
  replace (Z_to_bv 64 0xa6d6c) with (0xa6d6c : word) by (apply bv_eq; reflexivity).
  assert (K23 : sub_live A2 A3).
  { destruct RES7 as [(_ & EQ3) | (pix2 & data2 & _ & _ & _ & _ & PN2)].
    - apply sub_live_eq; exact EQ3.
    - destruct PN2 as (_ & _ & _ & _ & _ & _ & _ & N2p & N2d & _ & _ & _ & _ & EQ3 & _).
      intros q k Lq. rewrite EQ3; [exact Lq | intros E; rewrite E, N2p in Lq; discriminate | intros E; rewrite E, N2d in Lq; discriminate]. }
  pose proof (sub_live_trans _ _ _ SUBA2 K23) as SUBA3.
  pose proof (W_sok_win C A3 m7 _ (s - 80) 8 CK HW7 ltac:(lia) ltac:(cbn; lia)) as SOK8.
  destruct (cs_D (fx := mkFP fr2 cs2) al_rom r7 m7 s ltac:(lia) ltac:(lia) SOK8 ltac:(csr; reflexivity)) as (r8 & RUN8 & D1 & D10 & D19 & AG8).
  rzm HW7 RUN8.
  assert (WP8 : W C A3 (wbytes m7 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr r7 10))) (with_vmmaps vm3 md) /\
                POSTM C A3 s m7 (wbytes m7 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr r7 10)))) by wp_win CK.
  destruct WP8 as [HW8 PB8].
  pose proof (LIVKe_pix A2 data1 _ m7 pix1 _ LE7 L2p NEpd1 ltac:(lia) PX6) as PX7'.
  pose proof (rbw_PIX_livk A3 _ _ pix1 _ (proj2 PB8) (K23 _ _ L2p) PX7') as PX8.
  assert (Rpp : rdn SEGS (wbytes m7 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr r7 10))) (Z_to_bv 64 (s - 72)) 8
                = Some (Z_to_le_bytes 8 pix1)).
  { rewrite rdn_wbytes_out_Z by (rewrite length_N_to_le_bytes; cbn; lia).
    rewrite (FRM_rdn16 C (s - 96) _ m7 (s - 72) 8 CK (proj1 PM7)) by (cbn; lia).
    rewrite SeqExec.rdn_wbytes_hit8 by (rewrite u_Z2bv by lia; lia).
    rewrite w2l_Z8 by lia. reflexivity. }
  apply (V23LeptPixDestroyK.pixDestroy_keep_W (fx := mkFP fr2 cs2) C A3 _ _ r8 (s - 96) (s - 72) pix1 0 0 (4 * (wpl_of (w / 2) 1 * (h / 2)))
           (hdvr 1 (w / 2) (h / 2) 1 0 data1) (CMAPV 0 0 0 0 0) (Z_to_bv 64 0xa6d7c) S CK HW8
           ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia) ltac:(lia)
           D1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity) (csw_m8 s Hs16) D10 Rpp PX8 eq_refl eq_refl eq_refl
           (K23 _ _ L2p) N0p (K23 _ _ L2d) N0d HR (fun E => NEpd1 (eq_sym E)) (or_introl eq_refl)).
  intros A4 m9 vm4 r9 HW9 CS9 PD9 PM9 R09 KP9 RT9.
  replace (Z_to_bv 64 0xa6d7c) with (0xa6d7c : word) by (apply bv_eq; reflexivity).
  rewrite with_vmmaps_twice in HW9 |- *.
  destruct PD9 as (P1 & P2 & _ & P4). cbn [p_data hdvr] in P2, P4.
  specialize (P2 ltac:(lia)).
  assert (L34 : forall q, q <> Z_to_bv 64 pix1 -> q <> Z_to_bv 64 data1 -> live A4 q = live A3 q).
  { intros q Q1 Q2. apply P4; [exact Q1 | intros _; exact Q2 | intros X; exfalso; apply X; reflexivity]. }
  assert (SUBA4 : sub_live A A4).
  { intros q k Lq. rewrite L34; [apply SUBA3; exact Lq | intros E; rewrite E, Lap in Lq; discriminate | intros E; rewrite E, Lad in Lq; discriminate]. }
  assert (Lt4 : live A4 (Z_to_bv 64 tab) = Some 256%Z) by (rewrite L34 by assumption; apply K23; exact Lt2).
  pose proof (cellsZ_out m5 (wbytes m5 (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) (s - 72) (s - 64) (CSC s ret regs)
                ltac:(wbo) ltac:(unfold CSC; fa9) CE5) as CE6.
  pose proof (cellsZ_frm C (s - 96) _ m7 (CSC s ret regs) CK (proj1 PM7) ltac:(lia) ltac:(unfold CSC; fa9) CE6) as CE7.
  pose proof (cellsZ_out m7 (wbytes m7 (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr r7 10))) (s - 80) (s - 72) (CSC s ret regs)
                ltac:(wbo) ltac:(unfold CSC; fa9) CE7) as CE8.
  pose proof (cellsZ_frm C (s - 72 + 8) _ m9 (CSC s ret regs) CK (proj1 PM9) ltac:(lia) ltac:(unfold CSC; fa9) CE8) as CE9.
  apply (cs_tail_W (fx := mkFP fr2 cs2) C A4 m9 _ r9 regs s tab ret S CK HW9 Hs16 Hlo Hhi Hret H2
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) H4 ltac:(erest) Lt4 Lt0 CE9).
  intros A5 m10 vm5 r10 HW10 CS10 R1010 Lt5 LEQ5 PM10 RT10.
  rewrite with_vmmaps_twice in HW10 |- *.
  assert (SUBA5 : sub_live A A5).
  { intros q k Lq. rewrite LEQ5; [apply SUBA4; exact Lq | intros E; rewrite E, Lta in Lq; discriminate]. }
  assert (PA10 : POSTM C A s m5 m10).
  { eapply POSTM_trans; [apply (POSTM_sub C A A2); [exact SUBA2 | exact PB6]|].
    eapply POSTM_trans; [eapply POSTM_mono; [|exact PM7]; lia|].
    eapply POSTM_trans; [apply (POSTM_sub C A A3); [exact SUBA3 | exact PB8]|].
    eapply POSTM_trans; [apply (POSTM_sub C A A4); [exact SUBA4 | eapply POSTM_mono; [|exact PM9]; lia]|].
    apply (POSTM_sub C A A5); [exact SUBA5 | eapply POSTM_mono; [|exact PM10]; lia]. }
  assert (L5 : forall q, q <> Z_to_bv 64 tab -> q <> Z_to_bv 64 pix1 -> q <> Z_to_bv 64 data1 -> live A5 q = live A3 q).
  { intros q Q0 Q1 Q2. rewrite (LEQ5 q Q0). apply L34; assumption. }
  apply (HK fr2 cs2 A5 m10 vm5 r10 HW10 FZ2 ltac:(intros r0 Hr0; rewrite (FS2 r0 Hr0); exact (FS1 r0 Hr0)) CS10).
  - eapply POSTM_trans; [exact PM5 | apply (POSTM_sub C Ar A); [exact SUB | exact PA10]].
  - apply (LIVKe_trans A datas m m5 m10); [exact LE5 | apply LIVKe_of; exact (proj2 PA10)].
  - exact (rbw_PIX_livk A m5 m10 pixs _ (proj2 PA10) Lp PX5).
  - destruct RES7 as [(V10 & EQ3) | (pix2 & data2 & V10 & Hw4 & Hh4 & HOK4 & PN2)].
    + left. split; [csr; reflexivity |].
      intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 tab)) as [->|Q0]; [rewrite Lt5, Lta; reflexivity |].
      destruct (bv_eq_dec _ q (Z_to_bv 64 pix1)) as [->|Q1]; [rewrite (LEQ5 _ Q0), P1, Lap; reflexivity |].
      destruct (bv_eq_dec _ q (Z_to_bv 64 data1)) as [->|Q2]; [rewrite (LEQ5 _ Q0), P2, Lad; reflexivity |].
      rewrite (L5 q Q0 Q1 Q2), EQ3, (EQ2 q Q1 Q2), (LEQ1 q Q0). reflexivity.
    + right. exists pix2, data2.
      destruct PN2 as (G1 & G2 & G3 & G4 & G5 & G6 & NE2 & N2p & N2d & N02p & N02d & L3p & L3d & EQ3 & PX2 & PD2).
      assert (Xp : forall q, live A2 q = None -> live A q = None).
      { intros q Nq. destruct (live A q) eqn:E; [rewrite (SUBA2 _ _ E) in Nq; discriminate | reflexivity]. }
      assert (NEq : forall q q', live A2 q = None -> live A2 q' <> None -> q <> q').
      { intros q q' Nq Sq E. rewrite E in Nq. exact (Sq Nq). }
      assert (Q2t : Z_to_bv 64 pix2 <> Z_to_bv 64 tab) by (apply NEq; [exact N2p | rewrite Lt2; discriminate]).
      assert (Q2p : Z_to_bv 64 pix2 <> Z_to_bv 64 pix1) by (apply NEq; [exact N2p | rewrite L2p; discriminate]).
      assert (Q2d : Z_to_bv 64 pix2 <> Z_to_bv 64 data1) by (apply NEq; [exact N2p | rewrite L2d; discriminate]).
      assert (Q3t : Z_to_bv 64 data2 <> Z_to_bv 64 tab) by (apply NEq; [exact N2d | rewrite Lt2; discriminate]).
      assert (Q3p : Z_to_bv 64 data2 <> Z_to_bv 64 pix1) by (apply NEq; [exact N2d | rewrite L2p; discriminate]).
      assert (Q3d : Z_to_bv 64 data2 <> Z_to_bv 64 data1) by (apply NEq; [exact N2d | rewrite L2d; discriminate]).
      assert (L5p : live A5 (Z_to_bv 64 pix2) = Some 64%Z) by (rewrite (L5 _ Q2t Q2p Q2d); exact L3p).
      assert (L4p : live A4 (Z_to_bv 64 pix2) = Some 64%Z) by (rewrite (L34 _ Q2p Q2d); exact L3p).
      split; [csr; reflexivity |]. split; [lia |]. split; [lia |]. split; [exact HOK4 |].
      unfold O23LeptPixCreateT2.pixr_new.
      do 6 (split; [assumption |]). split; [exact NE2 |].
      split; [exact (Xp _ N2p) |]. split; [exact (Xp _ N2d) |]. split; [exact N02p |]. split; [exact N02d |].
      split; [exact L5p |]. split; [rewrite (L5 _ Q3t Q3p Q3d); exact L3d |].
      split.
      * intros q Q3 Q4. destruct (bv_eq_dec _ q (Z_to_bv 64 tab)) as [->|Q0]; [rewrite Lt5, Lta; reflexivity |].
        destruct (bv_eq_dec _ q (Z_to_bv 64 pix1)) as [->|Q1]; [rewrite (LEQ5 _ Q0), P1, Lap; reflexivity |].
        destruct (bv_eq_dec _ q (Z_to_bv 64 data1)) as [->|Q2]; [rewrite (LEQ5 _ Q0), P2, Lad; reflexivity |].
        rewrite (L5 q Q0 Q1 Q2), (EQ3 q Q3 Q4), (EQ2 q Q1 Q2), (LEQ1 q Q0). reflexivity.
      * split; [| exact PD2].
        apply (rbw_PIX_livk A5 m9 m10 pix2 _ (proj2 PM10) L5p).
        apply (rbw_PIX_livk A4 _ m9 pix2 _ (proj2 PM9) L4p).
        exact (rbw_PIX_livk A3 m7 _ pix2 _ (proj2 PB8) L3p PX2).
  - rewrite with_vmmaps_vmmaps in RT9, RT10.
    pose proof (RB_pixT_nonneg (4 * (wpl_of (w / 2) 1 * (h / 2)))) as N1.
    pose proof (RB_pixT_nonneg (4 * (wpl_of (w / 2 / 2) 1 * (h / 2 / 2)))) as N2.
    unfold RK_casc, RB_casc, RK_pix in *.
    pose proof (RT9 _ _ Hrm3 ltac:(lia) ltac:(lia)) as X1.
    pose proof (RT10 _ _ X1 ltac:(lia) ltac:(lia)) as X2.
    apply (aroom_mono A5 vm5 _ _ _ _ X2); lia.
Qed.

(* [comment removed for export] *)
Theorem pixReduceRankBinaryCascade_11_W : forall fr cs C Ar A m md regs (s pixs rc w h cm datas : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CASC_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 0 ->
  getr regs 14 = Z_to_bv 64 0 ->
  PIXat m pixs (hdvr rc w h 1 cm datas) -> O23LeptPixHdrT2.hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  live Ar (Z_to_bv 64 datas) = None -> live (c_A0 C) (Z_to_bv 64 datas) = None -> pixs <> datas ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_casc <= kR)%Z -> (RB_casc w h <= bR)%Z ->
  (forall fr' cs' A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> frm_zero cs' ->
     (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     cs_kept regs regs' -> POSTM C Ar s m m' -> LIVKe A datas m m' -> PIXat m' pixs (hdvr rc w h 1 cm datas) ->
     ( (getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
       \/ (exists pix2 data2, getr regs' 10 = Z_to_bv 64 pix2 /\ (4 <= w)%Z /\ (4 <= h)%Z /\ O23LeptPixHdrT2.hdr_ok (w / 2 / 2) (h / 2 / 2) 1 /\
             O23LeptPixCreateT2.pixr_new C A A' m' pix2 data2 (set_data (O23LeptPixHdrT2.pix_hdr (w / 2 / 2) (h / 2 / 2) 1) data2)) ) ->
     aroom A' vm' (kR - RK_casc) (bR - RB_casc w h) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0xa6c38 : word) m al_rom) md) S.
Proof.
  intros fr cs C Ar A m md regs s pixs rc w h cm datas ret S CK HW FZ SUB H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 H13 H14
    PX HOK Hw Hh Lp Ld Ldr Ld0 NEpd kR bR Hrm HkR HbR HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *.
  pose proof Hlo as Hlo'. unfold CASC_STACK, RB2_STACK, LSF in Hlo'.
  pose proof PX as (Hp0 & Hp64 & WF & _).
  destruct (blk_range C A m md _ 64 CK HW Lp ltac:(lia)) as [Gp TOPp]. rewrite u_Z2bv in Gp, TOPp by lia.
  pose proof (ai_live_hull A m (m_vmmaps md) _ _ (w_inv _ _ _ _ HW) Lp) as (_ & ALp & _). rewrite u_Z2bv in ALp by lia.
  assert (ALp8 : (pixs mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pixs); apply mod16_plus_mod8; [exact ALp | reflexivity]).
  pose proof (RB_pixT_nonneg (4 * (wpl_of (w / 2) 1 * (h / 2)))) as NB1.
  pose proof (RB_pixT_nonneg (4 * (wpl_of (w / 2 / 2) 1 * (h / 2 / 2)))) as NB2.
  assert (HK5 : RK_casc = 5%Z) by reflexivity.
  pose proof (W_sok_win C A m md (s - 96) 96 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (cs_A (fx := mkFP fr cs) al_rom regs m s pixs (hdvr rc w h 1 cm datas) ret ltac:(lia) ltac:(lia) ltac:(lia) PX ltac:(lia)
              eq_refl ALp8 SOK H2 H1 H10 H11 H12 H13 H14)
    as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q21 & Q20 & Q19 & Q9 & Q8 & Q22 & AG1).
  rzm HW RUN1.
  assert (WP1 : W C A (FCS m s ret regs) md /\ POSTM C A s m (FCS m s ret regs)) by (unfold FCS; wp_win CK).
  destruct WP1 as [HW1 PM1].
  pose proof (cells_FCS m s ret regs ltac:(lia) ltac:(lia)) as CE1.
  pose proof (rbw_PIX_livk A m _ pixs _ (proj2 PM1) Lp PX) as PX1.
  assert (P4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  replace (0x10e6e0 : word) with (Z_to_bv 64 0x10e6e0) by (apply bv_eq; reflexivity).
  apply (W_calloc16_sure (fx := mkFP fr cs) C A (FCS m s ret regs) md r1 256 1 kR bR (Z_to_bv 64 0xa6cb0) (s - 96) S CK HW1 Q10 Q11
           ltac:(lia) ltac:(lia) ltac:(lia) Hrm ltac:(lia) ltac:(rewrite alloc_margin_small by lia; unfold RB_casc in HbR; lia)
           ltac:(unfold ROOM_NMAX; lia) Q1 ltac:(red; apply bv_eq; reflexivity) P4 Q2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
  intros A1 m2 vm1 r2 res HWa Hres CSa Hnz L0 L1 L00 LEQa ZERO AL16 TOP PMa Hrm1.
  replace (Z_to_bv 64 0xa6cb0) with (0xa6cb0 : word) by (apply bv_eq; reflexivity).
  change (256 * 1)%Z with 256%Z in L1, Hrm1.
  rewrite alloc_margin_small in Hrm1 by lia.
  pose proof (u64_range res) as Ures.
  assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
  set (tab := u res) in *. clearbody tab.
  rewrite Eres in Hres, L0, L1, L00, LEQa.
  clear ZERO TOP Hnz.
  destruct (blk_range C A1 m2 _ _ 256 CK HWa L1 ltac:(lia)) as [Gt TOPt]. rewrite u_Z2bv in Gt, TOPt by lia.
  assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
  pose proof (cellsZ_frm C (s - 96) _ m2 (CSC s ret regs) CK (proj1 PMa) ltac:(lia) ltac:(unfold CSC; fa9) CE1) as CE2.
  pose proof (rbw_PIX_livk A _ m2 pixs _ (proj2 PMa) Lp PX1) as PX2.
  destruct (cs_T0 (fx := mkFP fr cs) al_rom r2 m2 tab ltac:(lia) ltac:(lia) Hres) as (r3 & RUN3 & V18 & V15 & V16 & V17 & AG3).
  rzm HWa RUN3.
  apply (cs_tab_W (fx := mkFP fr cs) C A A1 _ m2 s tab S CK SUBa L1 L0 L00 ltac:(lia) ltac:(lia) 255 r3 r3 m2 0 HWa
           (POSTM_refl _ _ _ _) ltac:(intros a _; reflexivity) ltac:(lia) ltac:(reflexivity) (regs_agree_refl _ _)
           V18 V15 ltac:(rewrite V16; f_equal; lia) ltac:(rewrite V17; f_equal; lia) ltac:(csr; f_equal; lia)).
  intros m4 r4 HW4 PM4 FT4 AG4 K1 K10 K11 K12.
  pose proof (cellsZ_out m2 m4 tab (tab + 256) (CSC s ret regs) FT4 ltac:(unfold CSC; fa9) CE2) as CE4.
  pose proof (rbw_PIX_livk A m2 m4 pixs _ (proj2 PM4) Lp PX2) as PX4.
  apply (pixReduceRankBinary2_W fr cs C Ar A1 m4 _ r4 (s - 96) pixs rc w h cm datas tab (Z_to_bv 64 0xa6d58) S CK HW4 FZ
           (sub_live_trans _ _ _ SUB SUBa) ltac:(csr; reflexivity) ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold RB2_STACK, LSF; lia) ltac:(lia) K1 ltac:(red; apply bv_eq; reflexivity) ltac:(csr; reflexivity)
           ltac:(csr; reflexivity) ltac:(csr; reflexivity) K12 PX4 HOK Hw Hh (SUBa _ _ Lp) (SUBa _ _ Ld) Ldr Ld0 NEpd L1 ltac:(lia)
           (kR - 1) (bR - 2 ^ 17) ltac:(rewrite with_vmmaps_vmmaps; exact Hrm1)
           ltac:(unfold RK_casc, RK_pix in *; lia) ltac:(unfold RB_casc in HbR; lia)).
  intros fr1 cs1 A2 m5 vm2 r5 HW5 FZ1 FS1 CS5 PM5 LE5 PX5 RES5 Hrm2.
  rewrite with_vmmaps_twice in HW5 |- *.
  replace (Z_to_bv 64 0xa6d58) with (0xa6d58 : word) by (apply bv_eq; reflexivity).
  assert (PMs : POSTM C Ar s m m5).
  { eapply POSTM_trans; [apply (POSTM_sub C Ar A); [exact SUB | exact PM1]|].
    eapply POSTM_trans; [apply (POSTM_sub C Ar A); [exact SUB | eapply POSTM_mono; [|exact PMa]; lia]|].
    eapply POSTM_trans; [apply (POSTM_sub C Ar A); [exact SUB | exact PM4]|].
    eapply POSTM_mono; [|exact PM5]; lia. }
  assert (LEs : LIVKe A datas m m5).
  { apply (LIVKe_trans A datas m m4 m5).
    - apply LIVKe_of. eapply LIVK_trans; [exact (proj2 PM1)|]. eapply LIVK_trans; [exact (proj2 PMa)|]. exact (proj2 PM4).
    - intros q k i Lq NE Hi. exact (LE5 q k i (SUBa _ _ Lq) NE Hi). }
  pose proof (cellsZ_frm C (s - 96) _ m5 (CSC s ret regs) CK (proj1 PM5) ltac:(lia) ltac:(unfold CSC; fa9) CE4) as CE5.
  destruct RES5 as [(V10 & EQ2) | (pix1 & data1 & V10 & Hw2 & Hh2 & HOK2 & PN)].
  - apply (cs_second_null_W fr C Ar A m md regs s pixs rc w h cm datas ret S kR bR fr1 cs1 A2 m5 vm2 r5 tab CK HW5 FZ1 FS1 SUB
             H2 Hs16 Hlo Hhi Hret H4 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             V10 ltac:(erest) CE5 PMs LEs PX5 Lp ltac:(rewrite EQ2; exact L1) L00 L0
             ltac:(intros q Hq; rewrite EQ2; apply LEQa; exact Hq) Hrm2 HkR HbR HK).
  - apply (cs_second_W fr C Ar A m md regs s pixs rc w h cm datas ret S kR bR fr1 cs1 A1 A2 m5 vm2 r5 tab pix1 data1 CK HW5 FZ1 FS1
             SUB H2 Hs16 Hlo Hhi Hret H4 ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity) ltac:(csr; reflexivity)
             V10 ltac:(erest) CE5 PMs LEs PX5 Lp L1 L00 L0 ltac:(lia) LEQa Hw2 Hh2 HOK2 PN Hrm2 HkR HbR HK).
Qed.
End CascW.
