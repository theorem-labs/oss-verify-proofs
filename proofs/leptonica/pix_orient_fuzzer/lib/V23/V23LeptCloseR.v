(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac FPSteps.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2 LeptRecs LeptSel LeptSlots LeptExecT LeptExecB.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptBase V23LeptDilW V23LeptMbc V23LeptCloseSpec V23LeptCloseIface V23LeptCloseA.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptEroW V23LeptCloseSegs V23LeptCloseT V23LeptMorphN V23LeptPixMisc V23LeptCloseN.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdr O23LeptPixCopyT O23LeptCloseSpec O23LeptCloseIface O23LeptCloseA O23LeptCloseT O23LeptCloseP.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section CloseR.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

Ltac rzs HW RUN := eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN |].

Lemma cr_m16 : forall s k : Z, (s mod 16 = 0)%Z -> (k mod 16 = 0)%Z -> ((s - k) mod 16 = 0)%Z.
Proof. intros s k Hs Hk. rewrite Zminus_mod, Hs, Hk. reflexivity. Qed.

Lemma cr_cw8_fwd : forall m (p a v z : Z),
  (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z -> (0 <= p)%Z -> (p + 8 <= 2 ^ 64)%Z -> (a + 8 <= p \/ p + 8 <= a)%Z ->
  rdn SEGS m (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z) ->
  rdn SEGS (O23LeptCloseSegs.CW8 m p v) (Z_to_bv 64 a) 8 = Some (Z_to_le_bytes 8 z).
Proof.
  intros m p a v z Ha Ha8 Hp Hp8 Hd H. unfold O23LeptCloseSegs.CW8.
  rewrite rdn_wbytes_out_Z; [exact H|]. zlen. lia.
Qed.

Lemma cr_frm_rd : forall C x m m' (b z : Z), Cok C -> FRM C x m m' -> (c_top C - LSTK <= x)%Z -> (x <= b)%Z ->
  (0 <= b)%Z -> (b + 8 <= 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 z) -> rdn SEGS m' (Z_to_bv 64 b) 8 = Some (Z_to_le_bytes 8 z).
Proof.
  intros C x m m' b z CK F Hx Hb H0 H8 R.
  apply (cell_keep m m' b (b + 8) b z H0 H8 ltac:(lia) ltac:(lia)); [|exact R].
  intros a Ha. apply (FRM_pw C x m m' CK F Hx). lia.
Qed.

Lemma cr_rkA : forall regs r r' (L : list reg), O23LeptCloseT.rkept regs r -> regs_agree (fun x => In x L) r r' ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%list -> ~ In x L) -> O23LeptCloseT.rkept regs r'.
Proof. intros regs r r' L RK AG NI x Hx. rewrite (AG x (NI x Hx)). exact (RK x Hx). Qed.

Lemma cr_rkC : forall regs r r', O23LeptCloseT.rkept regs r -> cs_kept r r' -> O23LeptCloseT.rkept regs r'.
Proof. intros regs r r' RK CS x Hx. rewrite (cs_kept_get r r' x CS (rk_cs x Hx)). exact (RK x Hx). Qed.

Lemma cr_pc : forall (fx : FPState) (r : bvmap 5 word) (p q : word) (mm : word -> option byte) md S, q = p ->
  realizes SEGS (mkCfg (@mkst fx r q mm al_rom) md) S -> realizes SEGS (mkCfg (@mkst fx r p mm al_rom) md) S.
Proof. intros fx r p q mm md S E H. subst q. exact H. Qed.

Ltac kpcs := first [exact cs2 | exact cs8 | exact cs9 | exact cs18 | exact cs19].
Ltac kp := repeat match goal with
  | CS : cs_kept ?a ?b |- getr ?b ?x = _ => rewrite (cs_kept_get a b x CS) by kpcs
  | AG : regs_agree _ ?a ?b |- getr ?b ?x = _ => rewrite (AG x ltac:(notin_lit))
  end; assumption.
Ltac rkN := let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [notin_lit|]); destruct Hx.
Ltac rkgo RG :=
  lazymatch goal with
  | |- O23LeptCloseT.rkept RG ?b =>
      first [ assumption
            | match goal with CS : cs_kept ?a b |- _ => apply (cr_rkC RG a b); [rkgo RG | exact CS] end
            | match goal with AG : regs_agree _ ?a b |- _ => eapply (cr_rkA RG a b); [rkgo RG | exact AG | rkN] end ]
  end.
Ltac pcfix RUN :=
  lazymatch type of RUN with msteps _ (@mkst _ _ ?p _ _) _ =>
    lazymatch goal with |- realizes _ (mkCfg (@mkst _ _ ?q _ _) _) _ =>
      tryif constr_eq p q then idtac else replace q with p by (apply bv_eq; reflexivity)
    end
  end.

Lemma csc_refused : forall (sh : bool) (fr : bvmap 5 word) C Ar A m md regs (s pix1 w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet) (kR bR : Z)
    (fr1 : bvmap 5 word) (cs1 : bv 32) (A0 : AS) (m0 : word -> option byte) (vm0 : VmMaps) (r0 : bvmap 5 word) (kx bx : Z)
    (sel1 sel2 : Z) (sv1 sv2 : selv) (c1 c2 : Z -> Z -> Z),
  Cok C -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSC_STACK <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 4 = Z_to_bv 64 0x1381d0 -> sub_live Ar A ->
  frm_zero cs1 -> (forall r : reg, In (u r) fs_list -> reg_get fr1 r = reg_get fr r) ->
  W C A0 m0 (with_vmmaps vm0 md) ->
  getr r0 2 = Z_to_bv 64 (s - 112) -> getr r0 8 = Z_to_bv 64 pix1 -> getr r0 9 = Z_to_bv 64 32 ->
  getr r0 18 = Z_to_bv 64 (O23LeptCloseA.hsz sh) -> getr r0 19 = Z_to_bv 64 (O23LeptCloseA.vsz sh) -> getr r0 10 = Z_to_bv 64 0 -> O23LeptCloseT.rkept regs r0 ->
  RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0 ->
  O23LeptCloseT.sels_static C A sh sel1 sel2 sv1 sv2 ->
  (forall q, O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q -> ~ O23LeptCloseA.tblk pix1 datas cm cv q) ->
  O23LeptCloseA.cslm (fun q => O23LeptCloseA.sblk sel1 sv1 q \/ O23LeptCloseA.sblk sel2 sv2 q) A A0 cm cv cm cv ->
  aroom A0 vm0 kx bx -> (kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh) <= kx)%Z -> (bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm <= bx)%Z ->
  (0 <= kR - O23LeptCloseSpec.RK_csc (O23LeptCloseA.vsz sh))%Z -> (0 <= bR - O23LeptCloseSpec.RB_csc (O23LeptCloseA.vsz sh) w h cm)%Z ->
  csc_K fr C Ar A m md regs s pix1 (O23LeptCloseA.vsz sh) w h cm datas cv ret S kR bR ->
  realizes SEGS (mkCfg (@mkst (mkFP fr1 cs1) r0 (0xa4ad0 : word) m0 al_rom) (with_vmmaps vm0 md)) S.
Proof.
  intros sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr1 cs1 A0 m0 vm0 r0 kx bx sel1 sel2 sv1 sv2 c1 c2
    CK Hs16 Hlo Hhi Hret H2 H4 SUBA FZ FK HW0 R2 R8 R9 R18 R19 R10 RK RS SS DJ CSL ROOM Hk Hb Hk0 Hb0 HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. pose proof Hlo as Hlo'. unfold CSC_STACK in Hlo'.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  assert (M16 : ((s - 112) mod 16 = 0)%Z) by (apply cr_m16; [exact Hs16 | reflexivity]).
  pose proof RS as (_ & _ & _ & _ & _ & _ & _ & P1 & SA1 & SA2 & _).
  assert (B1 : (0 <= sel1 < 2 ^ 64)%Z) by (destruct SA1 as (_ & _ & (B & B' & _) & _); lia).
  assert (B2 : (0 <= sel2 < 2 ^ 64)%Z) by (destruct SA2 as (_ & _ & (B & B' & _) & _); lia).
  assert (PB : (1 <= pix1 < 2 ^ 64)%Z).
  { destruct P1 as ((Hp0 & Hp64 & _) & Lp & _).
    destruct (blk_range C A0 m0 _ (Z_to_bv 64 pix1) 64 CK HW0 Lp ltac:(lia)) as [Gp _].
    rewrite u_Z2bv in Gp by lia. lia. }
  clear P1 SA1 SA2.
  assert (RD1 : rdn SEGS (O23LeptCloseSegs.CW8 m0 (s - 56) 0) (Z_to_bv 64 (O23LeptCloseA.co1 sh s)) 8 = Some (Z_to_le_bytes 8 sel1)).
  { pose proof (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0 RS) as (_ & C1 & _).
    apply cr_cw8_fwd; try exact C1; destruct sh; unfold O23LeptCloseA.co1; lia. }
  destruct (@cs_D (mkFP fr1 cs1) al_rom sh r0 m0 s 0 sel1 ltac:(lia) ltac:(lia) B1
              (W_sok_win C A0 m0 _ (s - 56) 8 CK HW0 ltac:(lia) ltac:(cbn; lia)) RD1 R2 R10 R18 R19)
    as (r1 & RUN1 & Q1_1 & Q10_1 & Q11_1 & Q12_1 & AG1).
  pcfix RUN1. rzs HW0 RUN1.
  destruct (RST_store C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m0 (with_vmmaps vm0 md) (s - 56) 0
              CK Hlo Hhi HW0 ltac:(lia) ltac:(lia) RS) as [HW1 RS1].
  pose proof (CW8_rd m0 (s - 56) 0 ltac:(lia) ltac:(lia) ltac:(lia)) as S56_1.
  apply (pixDilate_null_W (fx := mkFP fr1 cs1) C A0 _ _ r1 (s - 112) sel1 _ S CK HW1 ltac:(kp) M16
           ltac:(unfold DIL_STACK; lia) ltac:(lia) Q1_1 (ret_ok_pcD sh) Q10_1 Q11_1 Q12_1).
  intros m2 r2 HW2 CS2 PM2 V10_2.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m2 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW1 RS1 PM2) as RS2.
  pose proof (cr_frm_rd C (s - 112) _ m2 (s - 56) 0 CK (proj1 PM2) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_1) as S56_2.
  pose proof (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m2 RS2) as (_ & _ & C2_2 & _).
  destruct (@cs_E (mkFP fr1 cs1) al_rom sh r2 m2 s 0 sel2 ltac:(lia) ltac:(lia) B2
              (W_sok_win C A0 m2 _ (s - 64) 8 CK HW2 ltac:(lia) ltac:(cbn; lia)) C2_2 ltac:(kp) V10_2)
    as (r3 & RUN3 & Q1_3 & Q19_3 & Q10_3 & Q11_3 & Q12_3 & AG3).
  pcfix RUN3. rzs HW2 RUN3.
  destruct (RST_store C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m2 (with_vmmaps vm0 md) (s - 64) 0
              CK Hlo Hhi HW2 ltac:(lia) ltac:(lia) RS2) as [HW3 RS3].
  pose proof (CW8_rd m2 (s - 64) 0 ltac:(lia) ltac:(lia) ltac:(lia)) as S64_3.
  pose proof (cr_cw8_fwd m2 (s - 64) (s - 56) 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_2) as S56_3.
  apply (pixDilate_null_W (fx := mkFP fr1 cs1) C A0 _ _ r3 (s - 112) sel2 _ S CK HW3 ltac:(kp) M16
           ltac:(unfold DIL_STACK; lia) ltac:(lia) Q1_3 (ret_ok_pcE sh) Q10_3 Q11_3 Q12_3).
  intros m4 r4 HW4 CS4 PM4 V10_4.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m4 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW3 RS3 PM4) as RS4.
  pose proof (cr_frm_rd C (s - 112) _ m4 (s - 56) 0 CK (proj1 PM4) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_3) as S56_4.
  pose proof (cr_frm_rd C (s - 112) _ m4 (s - 64) 0 CK (proj1 PM4) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_3) as S64_4.
  pose proof (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m4 RS4) as (_ & C1_4 & _).
  destruct (@cs_F (mkFP fr1 cs1) al_rom sh r4 m4 s 0 0 sel1 ltac:(lia) ltac:(lia) B1
              (W_sok_win C A0 m4 _ (s - 72) 8 CK HW4 ltac:(lia) ltac:(cbn; lia)) C1_4 ltac:(kp) V10_4 ltac:(kp))
    as (r5 & RUN5 & Q1_5 & Q18_5 & Q10_5 & Q11_5 & Q12_5 & AG5).
  pcfix RUN5. rzs HW4 RUN5.
  destruct (RST_store C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m4 (with_vmmaps vm0 md) (s - 72) 0
              CK Hlo Hhi HW4 ltac:(lia) ltac:(lia) RS4) as [HW5 RS5].
  pose proof (CW8_rd m4 (s - 72) 0 ltac:(lia) ltac:(lia) ltac:(lia)) as S72_5.
  pose proof (cr_cw8_fwd m4 (s - 72) (s - 56) 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_4) as S56_5.
  pose proof (cr_cw8_fwd m4 (s - 72) (s - 64) 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_4) as S64_5.
  apply (pixErode_null_W (fx := mkFP fr1 cs1) C A0 _ _ r5 (s - 112) sel1 _ S CK HW5 ltac:(kp) M16
           ltac:(unfold ERO_STACK; lia) ltac:(lia) Q1_5 (ret_ok_pcF sh) Q10_5 Q11_5 Q12_5).
  intros m6 r6 HW6 CS6 PM6 V10_6.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m6 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW5 RS5 PM6) as RS6.
  pose proof (cr_frm_rd C (s - 112) _ m6 (s - 56) 0 CK (proj1 PM6) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_5) as S56_6.
  pose proof (cr_frm_rd C (s - 112) _ m6 (s - 64) 0 CK (proj1 PM6) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_5) as S64_6.
  pose proof (cr_frm_rd C (s - 112) _ m6 (s - 72) 0 CK (proj1 PM6) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S72_5) as S72_6.
  pose proof (FCL_of_RST C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m6 RS6) as (_ & _ & C2_6 & _).
  destruct (@cs_G (mkFP fr1 cs1) al_rom sh r6 m6 s 0 0 sel2 ltac:(lia) ltac:(lia) B2 C2_6 ltac:(kp) ltac:(kp) ltac:(kp))
    as (r7 & RUN7 & Q1_7 & Q10_7 & Q11_7 & Q12_7 & AG7).
  pcfix RUN7. rzs HW6 RUN7.
  apply (pixErode_null_W (fx := mkFP fr1 cs1) C A0 _ _ r7 (s - 112) sel2 _ S CK HW6 ltac:(kp) M16
           ltac:(unfold ERO_STACK; lia) ltac:(lia) Q1_7 ltac:(red; apply bv_eq; reflexivity) Q10_7 Q11_7 Q12_7).
  intros m8 r8 HW8 CS8 PM8 V10_8.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m8 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW6 RS6 PM8) as RS8.
  pose proof (cr_frm_rd C (s - 112) _ m8 (s - 56) 0 CK (proj1 PM8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_6) as S56_8.
  pose proof (cr_frm_rd C (s - 112) _ m8 (s - 64) 0 CK (proj1 PM8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_6) as S64_8.
  pose proof (cr_frm_rd C (s - 112) _ m8 (s - 72) 0 CK (proj1 PM8) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S72_6) as S72_8.
  destruct (@cs_H (mkFP fr1 cs1) al_rom r8 m8 s ltac:(lia) ltac:(lia) ltac:(kp)) as (r9 & RUN9 & Q1_9 & Q10_9 & AG9).
  pcfix RUN9. rzs HW8 RUN9.
  apply (pixDestroy_null_W (fx := mkFP fr1 cs1) C A0 _ _ r9 (s - 112) (s - 64) None _ S CK HW8 ltac:(kp) M16
           ltac:(lia) ltac:(lia) Q1_9 ltac:(red; apply bv_eq; reflexivity) Q10_9 ltac:(unfold slotok; lia)
           (m8_sub s 64 Hs16 eq_refl) S64_8).
  intros m9 r10 HW9 CS10 PM9 OUT9.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m9 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW8 RS8 PM9) as RS9.
  pose proof (cr_frm_rd C (s - 112) _ m9 (s - 56) 0 CK (proj1 PM9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_8) as S56_9.
  pose proof (cr_frm_rd C (s - 112) _ m9 (s - 72) 0 CK (proj1 PM9) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S72_8) as S72_9.
  destruct (@cs_I (mkFP fr1 cs1) al_rom r10 m9 0 ltac:(kp) ltac:(kp)) as (r11 & RUN11 & Q1_11 & Q10_11 & Q11_11 & AG11).
  pcfix RUN11. rzs HW9 RUN11.
  apply (pixRemoveBorder_null_W (fx := mkFP fr1 cs1) C A0 _ _ r11 (s - 112) _ S CK HW9 ltac:(kp) M16
           ltac:(unfold LSF; lia) ltac:(lia) Q1_11 ltac:(red; apply bv_eq; reflexivity) Q10_11).
  intros m10 r12 HW10 CS12 PM10 V10_12.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m10 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW9 RS9 PM10) as RS10.
  pose proof (cr_frm_rd C (s - 112) _ m10 (s - 56) 0 CK (proj1 PM10) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_9) as S56_10.
  pose proof (cr_frm_rd C (s - 112) _ m10 (s - 72) 0 CK (proj1 PM10) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S72_9) as S72_10.
  destruct (@cs_J (mkFP fr1 cs1) al_rom r12 m10 s 0 ltac:(lia) ltac:(lia)
              (W_sok_win C A0 m10 _ (s - 64) 8 CK HW10 ltac:(lia) ltac:(cbn; lia)) ltac:(kp) V10_12)
    as (r13 & RUN13 & Q1_13 & Q10_13 & AG13).
  pcfix RUN13. rzs HW10 RUN13.
  destruct (RST_store C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 m10 (with_vmmaps vm0 md) (s - 64) 0
              CK Hlo Hhi HW10 ltac:(lia) ltac:(lia) RS10) as [HW11 RS11].
  pose proof (CW8_rd m10 (s - 64) 0 ltac:(lia) ltac:(lia) ltac:(lia)) as S64_11.
  pose proof (cr_cw8_fwd m10 (s - 64) (s - 56) 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S56_10) as S56_11.
  pose proof (cr_cw8_fwd m10 (s - 64) (s - 72) 0 0 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S72_10) as S72_11.
  apply (pixDestroy_null_W (fx := mkFP fr1 cs1) C A0 _ _ r13 (s - 112) (s - 56) None _ S CK HW11 ltac:(kp) M16
           ltac:(lia) ltac:(lia) Q1_13 ltac:(red; apply bv_eq; reflexivity) Q10_13 ltac:(unfold slotok; lia)
           (m8_sub s 56 Hs16 eq_refl) S56_11).
  intros m12 r14 HW12 CS14 PM12 OUT12.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m12 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW11 RS11 PM12) as RS12.
  pose proof (cr_frm_rd C (s - 112) _ m12 (s - 64) 0 CK (proj1 PM12) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_11) as S64_12.
  pose proof (cr_frm_rd C (s - 112) _ m12 (s - 72) 0 CK (proj1 PM12) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S72_11) as S72_12.
  destruct (@cs_K (mkFP fr1 cs1) al_rom r14 m12 s ltac:(lia) ltac:(lia) ltac:(kp)) as (r15 & RUN15 & Q1_15 & Q10_15 & AG15).
  pcfix RUN15. rzs HW12 RUN15.
  apply (pixDestroy_null_W (fx := mkFP fr1 cs1) C A0 _ _ r15 (s - 112) (s - 72) None _ S CK HW12 ltac:(kp) M16
           ltac:(lia) ltac:(lia) Q1_15 ltac:(red; apply bv_eq; reflexivity) Q10_15 ltac:(unfold slotok; lia)
           (m8_sub s 72 Hs16 eq_refl) S72_12).
  intros m13 r16 HW13 CS16 PM13 OUT13.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m13 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW12 RS12 PM13) as RS13.
  pose proof (cr_frm_rd C (s - 112) _ m13 (s - 64) 0 CK (proj1 PM13) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_12) as S64_13.
  destruct (@cs_L (mkFP fr1 cs1) al_rom r16 m13 s pix1 0 ltac:(lia) ltac:(lia) PB ltac:(lia) S64_13 ltac:(kp) ltac:(kp))
    as (r17 & RUN17 & Q1_17 & Q10_17 & Q11_17 & AG17).
  pcfix RUN17. rzs HW13 RUN17.
  apply (pixCopy_nullpixs_W (fx := mkFP fr1 cs1) C A0 _ _ r17 (s - 112) pix1 _ S CK HW13 ltac:(kp) M16
           ltac:(unfold LSF; lia) ltac:(lia) Q1_17 ltac:(red; apply bv_eq; reflexivity) Q10_17 Q11_17).
  intros m14 r18 HW14 CS18 PM14 V10_18.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m14 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW13 RS13 PM14) as RS14.
  pose proof (cr_frm_rd C (s - 112) _ m14 (s - 64) 0 CK (proj1 PM14) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) S64_13) as S64_14.
  destruct (@cs_M (mkFP fr1 cs1) al_rom r18 m14 s ltac:(lia) ltac:(lia) ltac:(kp)) as (r19 & RUN19 & Q1_19 & Q10_19 & AG19).
  pcfix RUN19. rzs HW14 RUN19.
  apply (pixDestroy_null_W (fx := mkFP fr1 cs1) C A0 _ _ r19 (s - 112) (s - 64) None _ S CK HW14 ltac:(kp) M16
           ltac:(lia) ltac:(lia) Q1_19 ltac:(red; apply bv_eq; reflexivity) Q10_19 ltac:(unfold slotok; lia)
           (m8_sub s 64 Hs16 eq_refl) S64_14).
  intros m15 r20 HW15 CS20 PM15 OUT15.
  pose proof (RST_same C Ar m s ret regs sh pix1 w h cm datas cv sel1 sel2 sv1 sv2 c1 c2 A0 _ (with_vmmaps vm0 md) m15 (s - 112)
                CK ltac:(lia) Hhi ltac:(lia) ltac:(lia) HW14 RS14 PM15) as RS15.
  destruct RS15 as (FS & C1 & C2 & Z1 & Z2 & SUB & PM & P1 & SA1 & SA2 & _ & _).
  assert (RK20 : O23LeptCloseT.rkept regs r20) by rkgo regs.
  eapply cr_pc;
    [| exact (csc_seld4 sh fr C Ar A m md regs s pix1 w h cm datas cv ret S kR bR fr1 cs1 A0 m15 vm0 r20 cm cv kx bx sel1 sel2 sv1 sv2
                CK Hs16 Hlo Hhi Hret H2 H4 SUBA FZ FK HW15 ltac:(kp) ltac:(kp) RK20 FS C1 C2 Z1 Z2 SUB PM P1 SA1 SA2 SS DJ CSL
                ROOM Hk Hb Hk0 Hb0 HK)].
  apply bv_eq; reflexivity.
Qed.

End CloseR.
