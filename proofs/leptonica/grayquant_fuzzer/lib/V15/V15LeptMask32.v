(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit FPSteps FPStepsV.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRoom LeptExec LeptExecW LeptExecFP.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptBase.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL7a.
Import V15CL7a.V15LeptErr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr. Import V15CL8a.V15LeptGqArms.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL9a.
Import V15CL9a.V15LeptPixDestroy. Import V15CL9a.V15LeptMask32_iface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid. Import V15CL10a.V15LeptPixCreateS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptPixCopyA V15LeptPixCopy V15LeptPixHdrS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL14a.
Import V15CL14a.V15LeptThrLeaf. Import V15CL14a.V15LeptDither_iface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL15a.
Import V15CL15a.V15LeptOwn.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL16a.
Import V15CL16a.V15LeptGq_iface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptMask32Loops.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import LeptExecT LeptArith LeptRoomPC LeptRoom14.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Chain.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V15Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
(* [comment removed for export] *)
#[local] Existing Instance exf_fxd | 100.


Definition PC_RETERR : word := 87484%bv.
Lemma PC_RETERR_eq : Z_to_bv 64 87484 = PC_RETERR. Proof. apply bv_eq; reflexivity. Qed.
Definition PC_PIXCREATE : word := 93000%bv.
Lemma PC_PIXCREATE_eq : Z_to_bv 64 93000 = PC_PIXCREATE. Proof. apply bv_eq; reflexivity. Qed.
Definition ex_r14 : reg := 14%bv. Definition ex_r18 : reg := 18%bv. Definition ex_r19 : reg := 19%bv. Definition ex_r20 : reg := 20%bv. Definition ex_r21 : reg := 21%bv.
Definition ex_r22 : reg := 22%bv. Definition ex_r23 : reg := 23%bv. Definition ex_r24 : reg := 24%bv. Definition ex_r25 : reg := 25%bv. Definition ex_r26 : reg := 26%bv.
Definition ex_rf18 : reg := 18%bv.

Lemma ne_live : forall (A : AS) (p q : word) (k : Z), live A p = Some k -> live A q = None -> p <> q.
Proof. intros A p q k L F ->. rewrite F in L. discriminate L. Qed.
Lemma hdr_ok_1 : forall w h d, hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h 1.
Proof.
  intros w h d (DV & Hw & Hh & _) Hw1 Hh1. unfold hdr_ok. split; [left; reflexivity|]. split; [exact Hw|]. split; [exact Hh|].
  assert (wpl_of w 1 <= 626)%Z by (unfold wpl_of; apply Z.div_le_upper_bound; lia).
  assert (0 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_pos; lia). nia.
Qed.

(* [comment removed for export] *)
Ltac m32_fsgnj ST HFA :=
  lazymatch type of ST with
  | ex_st ?segs ?E ?m ?rom ?ms0 (mkFP (fr_denot _ ?L ?fr) ?cs) ?pc ?sr ?log =>
      let F := fresh "F" in let D := fresh "D" in let ST' := fresh "ST" in let G := fresh "G" in
      ex_fetch segs pc F D;
      lazymatch type of D with
      | decode_any ?w = Some (Fsgnj ?op ?fmt ?rd ?rs1 ?rs2, _) =>
          lazymatch type of HFA with
          | _ = Z_to_bv 64 ?z =>
              assert (G : reg_get (fr_denot E L fr) rs1 = Z_to_bv 64 z)
                by (rewrite fr_get; let o := eval vm_compute in (fr_find L (ridx rs1)) in change (fr_find L (ridx rs1)) with o; exact HFA);
              let zr := eval vm_compute in (bv_unsigned (fpv_sgnj op fmt (Z_to_bv 64 z) (Z_to_bv 64 z))) in
              pose proof (exb_fsgnj segs E L fr cs m rom pc sr log ms0 w op fmt rd rs1 rs2 (Z_to_bv 64 z) (Z_to_bv 64 z) zr ST F (eq_refl _) D G G
                            ltac:(apply bv_eq; vm_cast_no_check (eq_refl zr))) as ST';
              clear F D G ST; rename ST' into ST; exb_norm ST
          end
      end
  end.

(* [comment removed for export] *)
Lemma m32_kept_frame2 : forall E (M M' : word -> option byte) (rb : expr) (s WIN rlo rlen q qn flo fhi : Z),
  (forall x : word, ~ (q <= bv_unsigned x < q + qn)%Z -> ~ (flo <= bv_unsigned x < fhi)%Z -> M' x = M x) -> edenot E rb = Z_to_bv 64 s -> (0 <= s < 2 ^ 64)%Z ->
  ex_apart (s + - WIN) WIN (q + 0) qn -> (- WIN <= rlo)%Z -> (rlo + rlen <= 0)%Z -> (s + rlo + rlen <= flo \/ fhi <= s + rlo)%Z ->
  ex_region_kept E M M' (rb, rlo, (rlo + rlen)%Z).
Proof.
  intros E M M' rb s WIN rlo rlen q qn flo fhi FRM He Rs AP H1 H2 H3. cbn [ex_region_kept]. rewrite He, u_Z2bv by lia. intros x Hx.
  unfold ex_apart in AP. apply FRM; lia.
Qed.

Lemma m32_pix_frm2 : forall C A (M m' : word -> option byte) md (p q n s F flo fhi : Z) (v : pixv), Cok C -> W C A M md ->
  live A (Z_to_bv 64 p) = Some 64%Z -> live A (Z_to_bv 64 q) = Some n -> Z_to_bv 64 p <> Z_to_bv 64 q -> (0 <= q < 2 ^ 64)%Z -> (0 <= p < 2 ^ 64)%Z -> (0 < n)%Z ->
  (c_top C - LSTK <= s - F)%Z -> (s - F <= flo)%Z -> (fhi <= s)%Z ->
  PIXat M p v -> (forall x : word, ~ (q <= u x < q + n)%Z -> ~ (flo <= u x < fhi)%Z -> m' x = M x) -> PIXat m' p v.
Proof.
  intros C A M m' md p q n s F flo fhi v CK HW Lp Lq NE Rq Rp Hn Hlo Hflo Hfhi PX FR. pose proof PX as (Hp0 & Hp64 & _).
  pose proof (exW_blk_apart C A M md p q 64 n CK HW Lp Lq ltac:(intros ->; apply NE; reflexivity) ltac:(lia) Rq ltac:(lia) ltac:(lia)) as AP.
  pose proof (exW_win_blk_apart_h C A M md s F p 64 CK HW Lp ltac:(lia) Rp Hlo) as WAP. unfold ex_apart in WAP.
  apply (PIXat_frame M); [exact PX|]. intros x Hx. apply FR; lia.
Qed.

Section Chains.
Hypothesis HLOOP4 : band32_loop_hop.
Hypothesis HLOOP5 : discr32_loop_hop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition F4_STOPS : list Z := [93000; 95132; 95788; 124236; 123232]%Z.
Definition F4_FDEF : list (nat * nat) := [(8%nat, 33%nat); (9%nat, 34%nat); (18%nat, 35%nat)].
Definition F4_STACK : Z := 144 + 112 + LSF + 64.
Lemma F4_ok : forall (fx : FPState) C A m md regs (s pixs w h cm datas : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + F4_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 284096 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 1 ->
  reg_get (@fp_regs fx) 10%bv = F32_ZERO -> reg_get (@fp_regs fx) 11%bv = F32_ZERO ->
  PIXat m pixs (hdv w h 32 cm datas) -> hdr_ok w h 32 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 32 * h))%Z -> (datas mod 16 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pix14 <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
      (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 0 datad cmap0) ->
      aroom A' vm' (kR - RK_pix) (bR - RB_pix14) ->
      realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 123164) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm datas ret S FZ CK HW0 H2 Hs16 HloS Hhi H1 Hret H4 H10 H11 H12 H13 HFA0 HFA1 PXs HOK Hw1 Hh1 Lpixs_a0 Ldatas_a0 ALdatas kR bR RM0 HkR HbR HC.
  unfold F4_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 144 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 284096)) by exact H4.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 144)%Z) by lia.
  assert (GLO2 : (s - 144 + Z.of_nat (Z.to_nat 144) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (144 <= s)%Z) by lia.
  cbn [fp_regs] in HFA0, HFA1. unfold F32_ZERO in HFA0, HFA1.
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (Rwpl : (1 <= wpl_of w 32 < 2 ^ 31)%Z).
  { destruct HOK as (_ & _ & _ & X). assert (1 <= wpl_of w 32)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  pose proof (hdr_ok_1 w h 32 HOK Hw1 Hh1) as HOK1.
  assert (Rwpl1 : (1 <= wpl_of w 1 < 2 ^ 31)%Z).
  { destruct HOK1 as (_ & _ & _ & X). assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  assert (Rn1 : (0 < 4 * (wpl_of w 1 * h))%Z) by nia.
  pose proof PXs as (Hps0 & Hps64 & WFs & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof (wf_data _ WFs) as RRdatas. cbn in RRdatas.
  destruct (exW_blk_rng C A0 m0 _ pixs 64 CK HW0 Lpixs_a0 RRpixs eq_refl) as (Gps1 & Gps2 & _).
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 36) (EVar 32) (EVar 39) (EVar 40) pixs s 144 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 36) (EVar 37) (EVar 38) (ELit 32) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  pose (F4_dummy := tt).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 144) (Z.to_nat 144) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 41) (EVar 32) (exW_canary SEGS 415784 m0) s 144 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430224 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1); KRange (EVar 40) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F4_STOPS F4_FDEF HK ST FZ.
  (* [comment removed for export] *)
  m32_fsgnj ST HFA1. m32_fsgnj ST HFA0.
  exb_adrive 2000%nat 6000%nat F4_STOPS F4_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 144 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 144 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (37%nat, w); (38%nat, h); (36%nat, pixs); (39%nat, datas); (40%nat, wpl_of w 32)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  rewrite PC_PIXCREATE_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCreate_sure_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) w h 1 (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0 Q12_0 Hw1 Hh1 HOK1 kR bR
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) HkR HbR) end end.
  intros A1 m1 vm1 r1 pixd datad HW1 CSx0 PMc0 A10_0 PXN RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct PXN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdatad & NEpd & Fpixd & Fdatad & F0pixd & F0datad & Lpixd_a1 & Ldatad_a1 & LEQ0 & PXd1 & _).
  change (p_wpl (set_data (pix_hdr w h 1) datad)) with (wpl_of w 1) in Gdd2, Ldatad_a1. change (p_h (set_data (pix_hdr w h 1) datad)) with h in Gdd2, Ldatad_a1.
  assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia. assert (RRdatad : (0 <= datad < 2 ^ 64)%Z) by lia.
  assert (SUB1 : sub_live A0 A1).
  { intros q0 kq Lq. rewrite (LEQ0 q0 (ne_live A0 q0 _ kq Lq Fpixd) (ne_live A0 q0 _ kq Lq Fdatad)). exact Lq. }
  pose proof LEQ0 as LEQK.
  pose proof (SUB1 _ _ Lpixs_a0) as Lpixs_a1. pose proof (SUB1 _ _ Ldatas_a0) as Ldatas_a1.
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fpixd) as NE_pixs_pixd.
  assert (NE_pixd_pixs : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (intros EE; exact (NE_pixs_pixd (eq_sym EE))).
  assert (NE_pixd_datad : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros EE; apply NEpd; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fdatad) as NE_pixs_datad.
  assert (NE_datad_datas : Z_to_bv 64 datad <> Z_to_bv 64 datas) by (intros EE; exact (ne_live A0 _ _ _ Ldatas_a0 Fdatad (eq_sym EE))).
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 144 datad (4 * (wpl_of w 1 * h)) CK HW1 Ldatad_a1 Rn1 RRdatad GLO1) as WAPdatad.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (exT_pix_livk A0 _ m1 pixs _ (exT_pix_sess C A0 m0 M0 _ s 144 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0) (proj2 PMc0) Lpixs_a0) as PXs1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 144 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 42%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1] 42%nat ltac:(vm_cast_no_check (eq_refl 42%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 42%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 42%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 74) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q12_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 LEQ0 RM0 A10_0 PXs.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exT_kn_pix SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) (EVar 74) (EVar 32) (EVar 75) (EVar 76) pixd s 144 _ CK HW1 Lpixd_a1 PXd1 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 144) (Z.to_nat 144) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) (EVar 77) (EVar 32) (exW_canary SEGS 415784 m1) s 144 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (exW_kn_clr SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) 217704 217712 217704 217712 HW1 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp1 (proj2 (Forall_app _ _ _) (conj HKx0_1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp1 HKx0_1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F4_STOPS F4_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 144 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 144 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (37%nat, w); (38%nat, h); (36%nat, pixs); (39%nat, datas); (40%nat, wpl_of w 32); (74%nat, pixd); (75%nat, datad); (76%nat, wpl_of w 1)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (PXsM1 : PIXat M1 pixs (hdv w h 32 cm datas)) by exact (exT_pix_sess C A1 m1 M1 _ s 144 pixs _ CK HW1 GLO1 Lpixs_a1 PXs1 FRs1).
  assert (PXdM1 : PIXat M1 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m1 M1 _ s 144 pixd _ CK HW1 GLO1 Lpixd_a1 PXd1 FRs1).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyRes0_W fxk C A0 A1 M1 _ Rc1 (s + OFF1) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs1 SUB1 Q2_1
             ltac:(unfold OFF1; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q10_1 Q11_1 PXsM1 PXdM1 eq_refl eq_refl eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m2 r2 HW2 CSx1 PMc1 PXd2 A10_1.
  pose proof CSx1 as CS1. clear CSx1.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_mono C A0 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (exT_pix_livk A0 M1 m2 pixs _ PXsM1 (proj2 PMc1) Lpixs_a0) as PXs2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 144 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 78%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 415784 m2] 78%nat ltac:(vm_cast_no_check (eq_refl 78%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 78%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 78%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 A10_1 PXsM1 PXdM1 PXd1 PXs1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m2 _ (s - 144) (Z.to_nat 144) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A1 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) (EVar 110) (EVar 32) (exW_canary SEGS 415784 m2) s 144 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (exW_kn_clr SEGS C A1 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) 217704 217712 217704 217712 HW2 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F4_STOPS F4_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A1 A0 m2 _ E2 log2 (EVar 32) s 144 [] CK HW2 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 144 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (37%nat, w); (38%nat, h); (36%nat, pixs); (39%nat, datas); (40%nat, wpl_of w 32); (74%nat, pixd); (75%nat, datad); (76%nat, wpl_of w 1)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  assert (PXsM2 : PIXat M2 pixs (hdv w h 32 cm datas)) by exact (exT_pix_sess C A1 m2 M2 _ s 144 pixs _ CK HW2 GLO1 Lpixs_a1 PXs2 FRs2).
  assert (PXdM2 : PIXat M2 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m2 M2 _ s 144 pixd _ CK HW2 GLO1 Lpixd_a1 PXd2 FRs2).
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyFmt0_W fxk C A0 A1 M2 _ Rc2 (s + OFF2) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs2 SUB1 Q2_2
             ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) Q1_2 ltac:(red; apply bv_eq; reflexivity) Q10_2 Q11_2 PXsM2 PXdM2 eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m3 r3 HW3 CSx2 PMc2 PXd3 A10_2.
  pose proof CSx2 as CS2. clear CSx2.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_mono C A0 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (exT_pix_livk A0 M2 m3 pixs _ PXsM2 (proj2 PMc2) Lpixs_a0) as PXs3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 144 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 111%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 111%nat ltac:(vm_cast_no_check (eq_refl 111%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 111%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 111%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 PM2 HW2 FRs2 PMc2 CS2 OFF2 A10_2 PXsM2 PXdM2 PXd2 PXs2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exT_kn_cells SEGS m3 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 36) (EVar 39) (EVar 40) pixs _ PXs3 eq_refl eq_refl eq_refl) as HKg3.
  pose proof (exT_kn_cells SEGS m3 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 74) (EVar 75) (EVar 76) pixd _ PXd3 eq_refl eq_refl eq_refl) as HKh3.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m3 _ (s - 144) (Z.to_nat 144) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 143) (EVar 32) (exW_canary SEGS 415784 m3) s 144 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (exW_kn_clr SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) 217704 217712 217704 217712 HW3 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKg3 (proj2 (Forall_app _ _ _) (conj HKh3 (proj2 (Forall_app _ _ _) (conj HKx0_3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKg3 HKh3 HKx0_3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F4_STOPS F4_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A1 A0 m3 _ E3 log3 (EVar 32) s 144 [] CK HW3 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 144 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (37%nat, w); (38%nat, h); (36%nat, pixs); (39%nat, datas); (40%nat, wpl_of w 32); (74%nat, pixd); (75%nat, datad); (76%nat, wpl_of w 1)]).
  exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r8 Q8_3. exW_regfactB BS3 HR ex_r9 Q9_3. exW_regfactB BS3 HR ex_r18 Q18_3. exW_regfactB BS3 HR ex_r20 Q20_3. exW_regfactB BS3 HR ex_r22 Q22_3. exW_regfactB BS3 HR ex_r24 Q24_3. exW_regfactB BS3 HR ex_r25 Q25_3. exW_regfactB BS3 HR ex_r21 Q21_3. exW_regfactB BS3 HR ex_r23 Q23_3. exW_regfactB BS3 HR ex_r26 Q26_3.
  clear BS3.
  (* [comment removed for export] *)
  pose (BSx3 := [(32%nat, s); (37%nat, w); (38%nat, h); (36%nat, pixs); (39%nat, datas); (40%nat, wpl_of w 32); (74%nat, pixd); (75%nat, datad); (76%nat, wpl_of w 1)]).
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-128)%Z 4%nat CELL0.
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-124)%Z 4%nat CELL1.
  clear BSx3.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HLOOP4 fxk C A1 A0 M3 _ Rc3 s w h pixd datad datas S CK HWs3 SUB1 Hlo Hhi Hs16 HOK Hw1 Hh1 Ldatad_a1 Fdatad F0datad Ldatas_a1 NE_datad_datas RRdatad RRdatas ALdatad ALdatas
             Q2_3 Q10_3 Q8_3 Q9_3 Q18_3 Q20_3 Q22_3 Q24_3 Q25_3 Q21_3 Q23_3 Q26_3 CELL0 CELL1) end.
  intros r4 m4 HW4 PMl3 AGR3 A10_3 FRM3.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3 | exact PMl3]. }
  assert (PXd4 : PIXat m4 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_frm C A1 M3 m4 _ pixd datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) _ CK HWs3 Lpixd_a1 Ldatad_a1 NE_pixd_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A1 m3 M3 _ s 144 pixd _ CK HW3 GLO1 Lpixd_a1 PXd3 FRs3) FRM3).
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-144)%Z, (-144 + 144)%Z)]).
  { constructor; [exact (exW_kept_frame E3 M3 m4 (EVar 32) s (-144) 144 datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) FRM3 eq_refl RS WAPdatad (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 144%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_keep _ _ _ _ _ [5%nat; 6%nat; 7%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 19%nat; 20%nat; 21%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 28%nat; 29%nat; 30%nat; 31%nat] HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 144%nat ltac:(vm_cast_no_check (eq_refl 144%nat))) (exW_agree_keep _ _ _ AGR3)) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 144%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 144%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 74) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q2_3 Q10_3 Q8_3 Q9_3 Q18_3 Q20_3 Q22_3 Q24_3 Q25_3 Q21_3 Q23_3 Q26_3 PM3 HW3 FRs3 AGR3 FRM3 PMl3 A10_3 CELL0 CELL1 PXd3 PXs3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m4 _ (s - 144) (Z.to_nat 144) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 176) (EVar 32) (exW_canary SEGS 415784 m4) s 144 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (exW_kn_clr SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) 217704 217712 217704 217712 HW4 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F4_STOPS F4_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A1 A0 m4 _ E4 log4 (EVar 32) s 144 [] CK HW4 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  pose proof (exW_win_only E4 m4 log4 (EVar 32) s 144 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs4. change (mem_denot E4 m4 log4) with M4 in FRs4.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BSF := [(32%nat, s); (37%nat, w); (38%nat, h); (36%nat, pixs); (39%nat, datas); (40%nat, wpl_of w 32); (74%nat, pixd); (75%nat, datad); (76%nat, wpl_of w 1)]).
  exW_regfactB BSF HR ex_r10 G10.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk A1 M4 vm1 RcF FZ HWs4) end.
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PM4 PMs4).
  + exists pixd, datad. split; [exact G10|].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a1 (conj Ldatad_a1 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A1 m4 M4 _ s 144 pixd _ CK HW4 GLO1 Lpixd_a1 PXd4 FRs4).
    * left. split; [reflexivity|]. intros q0 N1 N2. exact (LEQK q0 N1 N2).
  + exact RM1.
Qed.
Lemma str_10c84 : str16 68740 10. Proof. str16_tac. Qed.   (* [comment removed for export] *)
Lemma str_10b7c : str16 68476 23. Proof. str16_tac. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition F4D_STOPS : list Z := [87484; 123232]%Z.
Definition F4D_STACK : Z := 144 + 16 + LSF.
Lemma F4_d : forall (fx : FPState) C A m md regs (s pixs w h d : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + F4D_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixs -> reg_get (@fp_regs fx) 10%bv = F32_ZERO -> reg_get (@fp_regs fx) 11%bv = F32_ZERO ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= pixs < 2 ^ 64)%Z -> (pixs <> 0)%Z -> (pixs mod 16 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (0 <= d < 2 ^ 31)%Z -> d <> 32%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 0)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 123164) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h d ret S FZ CK HW0 H2 Hs16 HloS Hhi H1 Hret H10 HFA0 HFA1 Lpixs_a0 Rpixs NZpixs ALpixs Rw Rh Rd NEd Cw Ch Cd HC.
  unfold F4D_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 144 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 144)%Z) by lia.
  assert (GLO2 : (s - 144 + Z.of_nat (Z.to_nat 144) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (144 <= s)%Z) by lia.
  cbn [fp_regs] in HFA0, HFA1. unfold F32_ZERO in HFA0, HFA1.
  pose proof Rpixs as RRpixs.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 144 pixs 64 CK HW0 Lpixs_a0 ltac:(lia) Rpixs ltac:(lia)) as WAPpixs.
  assert (Rpixs2 : (4096 <= pixs)%Z /\ (pixs + 64 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A0 m0 _ (Z_to_bv 64 pixs) 64 CK HW0 Lpixs_a0 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia. split; [exact G1 | lia]. }
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 144) (Z.to_nat 144) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; d; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; d; exW_canary SEGS 415784 m0]) (EVar 40) (EVar 32) (exW_canary SEGS 415784 m0) s 144 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; d; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; d; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430224 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 36) 1 (2 ^ 47); KAlign (EVar 36) 16; KDisj (SA (EVar 32) (-144)) 144 (SA (EVar 36) 0) 64; KWord (SA (EVar 36) 0) 4 (EVar 37); KWord (SA (EVar 36) 4) 4 (EVar 38); KWord (SA (EVar 36) 8) 4 (EVar 39); KRange (EVar 37) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1); KRange (EVar 39) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); bv_unsigned (reg_get fr ex_r9); bv_unsigned (reg_get fr ex_rf18); pixs; w; h; d; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F4D_STOPS F4_FDEF HK ST FZ.
  m32_fsgnj ST HFA1. m32_fsgnj ST HFA0.
  exb_adriveS 2000%nat 6000%nat F4D_STOPS (SCR [true] [] []) F4_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 144 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (37%nat, w); (38%nat, h); (36%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  rewrite PC_RETERR_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) 68740 68476 10 23 (Z_to_bv 64 ra) (Z_to_bv 64 0) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q10_0 Q11_0 Q12_0 str_10c84 str_10b7c) end end.
  intros m1 r1 HW1 OUT0 GRW0 CSx0 A10_0.
  pose proof CSx0 as CS0. clear CSx0.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s + OFF0 - (16 + LSF)) (s + OFF0) s CK HWs0 OUT0); unfold OFF0, LSF; lia. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 36, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_out E0 M0 m1 (EVar 32) s OFF0 0 (s + OFF0 - (16 + LSF)) (s + OFF0) OUT0 eq_refl RS (or_intror (Z.le_refl _)))|]. constructor; [apply (exW_kept_out E0 M0 m1 (EVar 36) pixs 0 64 (s + OFF0 - (16 + LSF)) (s + OFF0) OUT0 eq_refl RRpixs); left; unfold OFF0, LSF; lia|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 41%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 415784 m1] 41%nat ltac:(vm_cast_no_check (eq_refl 41%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 41%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 41%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q12_0 Q1_0 Q2_0 PM0 HW0 OUT0 GRW0 CS0 OFF0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (ELit 0) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) A10_0) as HRx1. clear HRn1. rename HRx1 into HRn1.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m1 _ (s - 144) (Z.to_nat 144) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 73) (EVar 32) (exW_canary SEGS 415784 m1) s 144 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (exW_kn_clr SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) 217704 217712 217704 217712 HW1 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F4D_STOPS F4_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A0 M1 (with_vmmaps vm0 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A0 A0 m1 _ E1 log1 (EVar 32) s 144 [] CK HW1 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BSF := [(32%nat, s); (37%nat, w); (38%nat, h); (36%nat, pixs)]).
  exW_regfactB BSF HR ex_r10 G10.
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk M1 RcF FZ HWs1) end.
  - lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - eapply POSTM_trans; [exact PM1 | exact PMs1].
  - exact G10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem F4_W_gen : F4_contract.
Proof.
  unfold F4_contract, gq_F_contract.
  intros fx C X A m md regs s pix w h d cd data ad kd kna kn ret S FZ CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 (H11 & H12 & H13 & HFA0 & HFA1) OWN HOK Hw Hh kR bR RM HkR HbR HC.
  unfold GQ_STACK_F, TP_gq in *.
  destruct OWN as [P0 | OWN].
  - subst pix.
    apply (F4_null_W fx C A m md regs s ret S FZ CK HW H2 Hs16 ltac:(unfold GQ_ARM_STACK, LSF; lia) Hhi H1 Hret H10).
    intros fx' m' regs' FZ' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
    apply (HC fx' A m' (m_vmmaps md) regs' FZ' ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
    apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_mask, RK_pix in *; lia | clear - HbR; unfold RB_mask, RB_pix14 in *; lia].
  - destruct OWN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    destruct (Z.eq_dec d 32) as [->|ND].
    + apply (F4_ok fx C A m md regs s pix w h cd data ret S FZ CK HW H2 Hs16 ltac:(unfold F4_STACK, LSF; lia) Hhi H1 Hret H4 H10 H11 H12 H13 HFA0 HFA1
               PX HOK Hw Hh Lp Ld ALd kR bR RM HkR HbR).
      intros fx' A' m' vm' regs' FZ' HW' CS' PM' (pixd & datad & A0' & PN) RM'.
      apply (HC fx' A' m' vm' regs' FZ' HW' CS' PM'); [|exact RM'].
      right. exists pixd, w, h, 1%Z, 0%Z, datad, cmap0. split; [exact A0' | split; [exact PN|]].
      assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). nia.
    + pose proof PX as (_ & _ & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh. pose proof (wf_d _ WF) as Rd. cbn in Rw, Rh, Rd.
      apply (F4_d fx C A m md regs s pix w h d ret S FZ CK HW H2 Hs16 ltac:(unfold F4D_STACK, LSF; lia) Hhi H1 Hret H10 HFA0 HFA1 Lp ltac:(lia) ltac:(lia) ALp Rw Rh Rd ND
               ltac:(rewrite Z.add_0_r; exact (PIX_rd_w SEGS m pix _ PX)) (PIX_rd_h SEGS m pix _ PX) (PIX_rd_d SEGS m pix _ PX)).
      intros fx' m' regs' FZ' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
      apply (HC fx' A m' (m_vmmaps md) regs' FZ' ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
      apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_mask, RK_pix in *; lia | clear - HbR; unfold RB_mask, RB_pix14 in *; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition F5_STOPS : list Z := [93000; 95132; 95788; 125124]%Z.
Definition F5_FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition F5_STACK : Z := 208 + 112 + LSF + 64.
Lemma F5_ok : forall (fx : FPState) C A m md regs (s pixs w h cm datas : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + F5_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 284096 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 10 -> getr regs 12 = Z_to_bv 64 10 -> getr regs 13 = Z_to_bv 64 1 ->
  PIXat m pixs (hdv w h 32 cm datas) -> hdr_ok w h 32 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 32 * h))%Z -> (datas mod 16 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pix14 <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
      (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 0 datad cmap0) ->
      aroom A' vm' (kR - RK_pix) (bR - RB_pix14) ->
      realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 124628) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm datas ret S FZ CK HW0 H2 Hs16 HloS Hhi H1 Hret H4 H10 H11 H12 H13 PXs HOK Hw1 Hh1 Lpixs_a0 Ldatas_a0 ALdatas kR bR RM0 HkR HbR HC.
  unfold F5_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 208 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 284096)) by exact H4.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 208)%Z) by lia.
  assert (GLO2 : (s - 208 + Z.of_nat (Z.to_nat 208) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (208 <= s)%Z) by lia.
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (Rwpl : (1 <= wpl_of w 32 < 2 ^ 31)%Z).
  { destruct HOK as (_ & _ & _ & X). assert (1 <= wpl_of w 32)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  pose proof (hdr_ok_1 w h 32 HOK Hw1 Hh1) as HOK1.
  assert (Rwpl1 : (1 <= wpl_of w 1 < 2 ^ 31)%Z).
  { destruct HOK1 as (_ & _ & _ & X). assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  assert (Rn1 : (0 < 4 * (wpl_of w 1 * h))%Z) by nia.
  pose proof PXs as (Hps0 & Hps64 & WFs & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof (wf_data _ WFs) as RRdatas. cbn in RRdatas.
  destruct (exW_blk_rng C A0 m0 _ pixs 64 CK HW0 Lpixs_a0 RRpixs eq_refl) as (Gps1 & Gps2 & _).
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 32) (EVar 37) (EVar 38) pixs s 208 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 35) (EVar 36) (ELit 32) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  pose (F5_dummy := tt).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 208) (Z.to_nat 208) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 39) (EVar 32) (exW_canary SEGS 415784 m0) s 208 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430288 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; datas; wpl_of w 32; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F5_STOPS F5_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 208 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 208 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, datas); (38%nat, wpl_of w 32)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0. exW_regfactB BS0 HR ex_r4 Q4_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  rewrite PC_PIXCREATE_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCreate_sure_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) w h 1 (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q4_0 Q10_0 Q11_0 Q12_0 Hw1 Hh1 HOK1 kR bR
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) HkR HbR) end end.
  intros A1 m1 vm1 r1 pixd datad HW1 CSx0 PMc0 A10_0 PXN RM1.
  pose proof CSx0 as CS0. clear CSx0.
  rewrite with_vmmaps_twice in HW1 |- *.
  destruct PXN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdatad & NEpd & Fpixd & Fdatad & F0pixd & F0datad & Lpixd_a1 & Ldatad_a1 & LEQ0 & PXd1 & _).
  change (p_wpl (set_data (pix_hdr w h 1) datad)) with (wpl_of w 1) in Gdd2, Ldatad_a1. change (p_h (set_data (pix_hdr w h 1) datad)) with h in Gdd2, Ldatad_a1.
  assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia. assert (RRdatad : (0 <= datad < 2 ^ 64)%Z) by lia.
  assert (SUB1 : sub_live A0 A1).
  { intros q0 kq Lq. rewrite (LEQ0 q0 (ne_live A0 q0 _ kq Lq Fpixd) (ne_live A0 q0 _ kq Lq Fdatad)). exact Lq. }
  pose proof LEQ0 as LEQK.
  pose proof (SUB1 _ _ Lpixs_a0) as Lpixs_a1. pose proof (SUB1 _ _ Ldatas_a0) as Ldatas_a1.
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fpixd) as NE_pixs_pixd.
  assert (NE_pixd_pixs : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (intros EE; exact (NE_pixs_pixd (eq_sym EE))).
  assert (NE_pixd_datad : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros EE; apply NEpd; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fdatad) as NE_pixs_datad.
  assert (NE_datad_datas : Z_to_bv 64 datad <> Z_to_bv 64 datas) by (intros EE; exact (ne_live A0 _ _ _ Ldatas_a0 Fdatad (eq_sym EE))).
  pose proof (exW_win_blk_apart_h C A1 m1 _ s 208 datad (4 * (wpl_of w 1 * h)) CK HW1 Ldatad_a1 Rn1 RRdatad GLO1) as WAPdatad.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|]. apply (POSTM_mono C A0 (s + OFF0) s); [unfold OFF0; lia | exact PMc0]. }
  pose proof (exT_pix_livk A0 _ m1 pixs _ (exT_pix_sess C A0 m0 M0 _ s 208 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0) (proj2 PMc0) Lpixs_a0) as PXs1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF0 208 M0 m1 E0 (EVar 32) CK (proj1 PMc0) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 40%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1] 40%nat ltac:(vm_cast_no_check (eq_refl 40%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 40%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 40%nat E0 (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 72) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q12_0 Q1_0 Q2_0 Q4_0 PM0 HW0 FRs0 PMc0 CS0 OFF0 LEQ0 RM0 A10_0 PXs.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exT_kn_pix SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (EVar 73) (EVar 74) pixd s 208 _ CK HW1 Lpixd_a1 PXd1 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m1 _ (s - 208) (Z.to_nat 208) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) (EVar 75) (EVar 32) (exW_canary SEGS 415784 m1) s 208 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (exW_kn_clr SEGS C A1 m1 _ (ex_envL vals0 r1 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m1]) 217704 217712 217704 217712 HW1 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp1 (proj2 (Forall_app _ _ _) (conj HKx0_1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp1 HKx0_1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F5_STOPS F5_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A1 M1 (with_vmmaps vm1 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A1 A0 m1 _ E1 log1 (EVar 32) s 208 [] CK HW1 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 208 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, datas); (38%nat, wpl_of w 32); (72%nat, pixd); (73%nat, datad); (74%nat, wpl_of w 1)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  assert (PXsM1 : PIXat M1 pixs (hdv w h 32 cm datas)) by exact (exT_pix_sess C A1 m1 M1 _ s 208 pixs _ CK HW1 GLO1 Lpixs_a1 PXs1 FRs1).
  assert (PXdM1 : PIXat M1 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m1 M1 _ s 208 pixd _ CK HW1 GLO1 Lpixd_a1 PXd1 FRs1).
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyRes0_W fxk C A0 A1 M1 _ Rc1 (s + OFF1) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs1 SUB1 Q2_1
             ltac:(unfold OFF1; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q10_1 Q11_1 PXsM1 PXdM1 eq_refl eq_refl eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m2 r2 HW2 CSx1 PMc1 PXd2 A10_1.
  pose proof CSx1 as CS1. clear CSx1.
  assert (PM2 : POSTM C A0 s m0 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_mono C A0 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (exT_pix_livk A0 M1 m2 pixs _ PXsM1 (proj2 PMc1) Lpixs_a0) as PXs2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 208 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 76%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [exW_canary SEGS 415784 m2] 76%nat ltac:(vm_cast_no_check (eq_refl 76%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 76%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 76%nat E1 (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q1_1 Q2_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 A10_1 PXsM1 PXdM1 PXd1 PXs1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m2 _ (s - 208) (Z.to_nat 208) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A1 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) (EVar 108) (EVar 32) (exW_canary SEGS 415784 m2) s 208 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (exW_kn_clr SEGS C A1 m2 _ (ex_envL vals1 r2 [exW_canary SEGS 415784 m2]) 217704 217712 217704 217712 HW2 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F5_STOPS F5_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A1 A0 m2 _ E2 log2 (EVar 32) s 208 [] CK HW2 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 208 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, datas); (38%nat, wpl_of w 32); (72%nat, pixd); (73%nat, datad); (74%nat, wpl_of w 1)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  assert (PXsM2 : PIXat M2 pixs (hdv w h 32 cm datas)) by exact (exT_pix_sess C A1 m2 M2 _ s 208 pixs _ CK HW2 GLO1 Lpixs_a1 PXs2 FRs2).
  assert (PXdM2 : PIXat M2 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m2 M2 _ s 208 pixd _ CK HW2 GLO1 Lpixd_a1 PXd2 FRs2).
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyFmt0_W fxk C A0 A1 M2 _ Rc2 (s + OFF2) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs2 SUB1 Q2_2
             ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) Q1_2 ltac:(red; apply bv_eq; reflexivity) Q10_2 Q11_2 PXsM2 PXdM2 eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m3 r3 HW3 CSx2 PMc2 PXd3 A10_2.
  pose proof CSx2 as CS2. clear CSx2.
  assert (PM3 : POSTM C A0 s m0 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_mono C A0 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (exT_pix_livk A0 M2 m3 pixs _ PXsM2 (proj2 PMc2) Lpixs_a0) as PXs3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 208 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E2 M2 m3 _ [] _ HKc2 KEPT2) as HKk2.
  match type of HKk2 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E2 m3 kk') in HKk2 end.
  pose proof (regs_ok_agree 109%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa2.
  pose proof (exW_regs_call _ _ _ _ _ HRa2 (ex_regs_ok_junk vals2 r3 [exW_canary SEGS 415784 m3] 109%nat ltac:(vm_cast_no_check (eq_refl 109%nat))) CS2) as HRn3.
  clear HRa2.
  assert (HKa3 : know_ok SEGS (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) m3 _) by (exact (know_ok_agree SEGS 109%nat E2 _ m3 _ (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk2)).
  rewrite (fr_denot_agree 109%nat E2 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) _ fr (vals_app_agree vals2 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc2 HKk2 KEPT2 HC2 HWs2 PMs2 Q10_2 Q11_2 Q1_2 Q2_2 PM2 HW2 FRs2 PMc2 CS2 OFF2 A10_2 PXsM2 PXdM2 PXd2 PXs2.
  subst M2. clear log2. clear E2. try clear Rc2. clear KN2.
  lazymatch type of HRn3 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn3 end.
  pose proof (exT_kn_cells SEGS m3 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 34) (EVar 37) (EVar 38) pixs _ PXs3 eq_refl eq_refl eq_refl) as HKg3.
  pose proof (exT_kn_cells SEGS m3 (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 72) (EVar 73) (EVar 74) pixd _ PXd3 eq_refl eq_refl eq_refl) as HKh3.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m3 _ (s - 208) (Z.to_nat 208) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 141) (EVar 32) (exW_canary SEGS 415784 m3) s 208 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (exW_kn_clr SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) 217704 217712 217704 217712 HW3 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKg3 (proj2 (Forall_app _ _ _) (conj HKh3 (proj2 (Forall_app _ _ _) (conj HKx0_3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKg3 HKh3 HKx0_3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F5_STOPS F5_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A1 A0 m3 _ E3 log3 (EVar 32) s 208 [] CK HW3 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 208 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, datas); (38%nat, wpl_of w 32); (72%nat, pixd); (73%nat, datad); (74%nat, wpl_of w 1)]).
  exW_regfactB BS3 HR ex_r2 Q2_3. exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r20 Q20_3. exW_regfactB BS3 HR ex_r19 Q19_3. exW_regfactB BS3 HR ex_r21 Q21_3. exW_regfactB BS3 HR ex_r18 Q18_3. exW_regfactB BS3 HR ex_r8 Q8_3.
  clear BS3.
  (* [comment removed for export] *)
  pose (BSx3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, datas); (38%nat, wpl_of w 32); (72%nat, pixd); (73%nat, datad); (74%nat, wpl_of w 1)]).
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-112)%Z 4%nat CELL0.
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-108)%Z 4%nat CELL1.
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-120)%Z 4%nat CELL2.
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-124)%Z 4%nat CELL3.
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-128)%Z 4%nat CELL4.
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-132)%Z 4%nat CELL5.
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-136)%Z 4%nat CELL6.
  exW_cellB HK Hlf r0 BSx3 (EVar 32) s (-140)%Z 4%nat CELL7.
  clear BSx3.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HLOOP5 fxk C A1 A0 M3 _ Rc3 s w h pixd datad datas S CK HWs3 SUB1 Hlo Hhi Hs16 HOK Hw1 Hh1 Ldatad_a1 Fdatad F0datad Ldatas_a1 NE_datad_datas RRdatad RRdatas ALdatad ALdatas
             Q2_3 Q10_3 Q20_3 Q19_3 Q21_3 Q18_3 Q8_3 CELL0 CELL1 CELL2 CELL3 CELL4 CELL5 CELL6 CELL7) end.
  intros r4 m4 HW4 PMl3 AGR3 A10_3 FRM3.
  assert (PM4 : POSTM C A0 s m0 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3 | exact PMl3]. }
  assert (PXd4 : PIXat m4 pixd (set_data (pix_hdr w h 1) datad)).
  { apply (m32_pix_frm2 C A1 M3 m4 _ pixd datad (4 * (wpl_of w 1 * h)) s 208 (s + -200) (s + -140) _ CK HWs3 Lpixd_a1 Ldatad_a1 NE_pixd_datad RRdatad RRpixd Rn1 GLO1 ltac:(lia) ltac:(lia) (exT_pix_sess C A1 m3 M3 _ s 208 pixd _ CK HW3 GLO1 Lpixd_a1 PXd3 FRs3) FRM3). }
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, (-208)%Z, (-208 + 8)%Z); (EVar 32, (-140)%Z, (-140 + 140)%Z)]).
  { constructor; [exact (m32_kept_frame2 E3 M3 m4 (EVar 32) s 208 (-208) 8 datad (4 * (wpl_of w 1 * h)) (s + -200) (s + -140) FRM3 eq_refl RS WAPdatad ltac:(lia) ltac:(lia) ltac:(lia))|]. constructor; [exact (m32_kept_frame2 E3 M3 m4 (EVar 32) s 208 (-140) 140 datad (4 * (wpl_of w 1 * h)) (s + -200) (s + -140) FRM3 eq_refl RS WAPdatad ltac:(lia) ltac:(lia) ltac:(lia))|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_keep _ _ _ _ _ [1%nat; 5%nat; 6%nat; 7%nat; 9%nat; 10%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 18%nat; 19%nat; 20%nat; 22%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat] HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 142%nat ltac:(vm_cast_no_check (eq_refl 142%nat))) (exW_agree_keep _ _ _ AGR3)) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 142%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r4 ex_r10 (EVar 72) HRn4 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_3)) as HRx4. clear HRn4. rename HRx4 into HRn4.
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q2_3 Q10_3 Q20_3 Q19_3 Q21_3 Q18_3 Q8_3 PM3 HW3 FRs3 AGR3 FRM3 PMl3 A10_3 CELL0 CELL1 CELL2 CELL3 CELL4 CELL5 CELL6 CELL7 PXd3 PXs3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m4 _ (s - 208) (Z.to_nat 208) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 174) (EVar 32) (exW_canary SEGS 415784 m4) s 208 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (exW_kn_clr SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) 217704 217712 217704 217712 HW4 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F5_STOPS F5_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A1 A0 m4 _ E4 log4 (EVar 32) s 208 [] CK HW4 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  pose proof (exW_win_only E4 m4 log4 (EVar 32) s 208 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs4. change (mem_denot E4 m4 log4) with M4 in FRs4.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, datas); (38%nat, wpl_of w 32); (72%nat, pixd); (73%nat, datad); (74%nat, wpl_of w 1)]).
  exW_regfactB BSF HR ex_r10 G10.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk A1 M4 vm1 RcF FZ HWs4) end.
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PM4 PMs4).
  + exists pixd, datad. split; [exact G10|].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a1 (conj Ldatad_a1 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A1 m4 M4 _ s 208 pixd _ CK HW4 GLO1 Lpixd_a1 PXd4 FRs4).
    * left. split; [reflexivity|]. intros q0 N1 N2. exact (LEQK q0 N1 N2).
  + exact RM1.
Qed.
Lemma str_11038 : str16 69688 24. Proof. str16_tac. Qed.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition F5D_STOPS : list Z := [87484]%Z.
Definition F5D_STACK : Z := 208 + 16 + LSF.
Lemma F5_d : forall (fx : FPState) C A m md regs (s pixs w h d : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + F5D_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixs -> 
  live A (Z_to_bv 64 pixs) = Some 64%Z -> (0 <= pixs < 2 ^ 64)%Z -> (pixs <> 0)%Z -> (pixs mod 16 = 0)%Z ->
  (0 <= w < 2 ^ 31)%Z -> (0 <= h < 2 ^ 31)%Z -> (0 <= d < 2 ^ 31)%Z -> d <> 32%Z ->
  rdn SEGS m (Z_to_bv 64 (pixs + 0)) 4 = Some (Z_to_le_bytes 4 w) -> rdn SEGS m (Z_to_bv 64 (pixs + 4)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (pixs + 8)) 4 = Some (Z_to_le_bytes 4 d) ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 124628) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h d ret S FZ CK HW0 H2 Hs16 HloS Hhi H1 Hret H10  Lpixs_a0 Rpixs NZpixs ALpixs Rw Rh Rd NEd Cw Ch Cd HC.
  unfold F5D_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 208 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. cbn [fp_csr] in FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 208)%Z) by lia.
  assert (GLO2 : (s - 208 + Z.of_nat (Z.to_nat 208) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (208 <= s)%Z) by lia.
  pose proof Rpixs as RRpixs.
  pose proof (exW_win_blk_apart_h C A0 m0 _ s 208 pixs 64 CK HW0 Lpixs_a0 ltac:(lia) Rpixs ltac:(lia)) as WAPpixs.
  assert (Rpixs2 : (4096 <= pixs)%Z /\ (pixs + 64 <= alloc_top (c_vm C))%Z).
  { destruct (blk_range C A0 m0 _ (Z_to_bv 64 pixs) 64 CK HW0 Lpixs_a0 ltac:(lia)) as [G1 G2]. rewrite u_Z2bv in G1, G2 by lia. split; [exact G1 | lia]. }
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 208) (Z.to_nat 208) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0]) (EVar 38) (EVar 32) (exW_canary SEGS 415784 m0) s 208 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430288 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 34) 1 (2 ^ 47); KAlign (EVar 34) 16; KDisj (SA (EVar 32) (-208)) 208 (SA (EVar 34) 0) 64; KWord (SA (EVar 34) 0) 4 (EVar 35); KWord (SA (EVar 34) 4) 4 (EVar 36); KWord (SA (EVar 34) 8) 4 (EVar 37); KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 37) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; d; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adriveS 2000%nat 6000%nat F5D_STOPS (SCR [true] [] []) F5_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 208 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  rewrite PC_RETERR_eq.
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 (s + OFF0) 68740 69688 10 24 (Z_to_bv 64 ra) (Z_to_bv 64 0) S CK HWs0 Q2_0
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF0, LSF; lia) ltac:(unfold OFF0; lia) Q1_0
             ltac:(red; apply bv_eq; reflexivity) Q10_0 Q11_0 Q12_0 str_10c84 str_11038) end end.
  intros m1 r1 HW1 OUT0 GRW0 CSx0 A10_0.
  pose proof CSx0 as CS0. clear CSx0.
  assert (PM1 : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s + OFF0 - (16 + LSF)) (s + OFF0) s CK HWs0 OUT0); unfold OFF0, LSF; lia. }
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z); (EVar 34, 0%Z, 64%Z)]).
  { constructor; [exact (exW_kept_out E0 M0 m1 (EVar 32) s OFF0 0 (s + OFF0 - (16 + LSF)) (s + OFF0) OUT0 eq_refl RS (or_intror (Z.le_refl _)))|]. constructor; [apply (exW_kept_out E0 M0 m1 (EVar 34) pixs 0 64 (s + OFF0 - (16 + LSF)) (s + OFF0) OUT0 eq_refl RRpixs); left; unfold OFF0, LSF; lia|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 39%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 415784 m1] 39%nat ltac:(vm_cast_no_check (eq_refl 39%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 39%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 39%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q11_0 Q12_0 Q1_0 Q2_0 PM0 HW0 OUT0 GRW0 CS0 OFF0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (ELit 0) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) A10_0) as HRx1. clear HRn1. rename HRx1 into HRn1.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m1 _ (s - 208) (Z.to_nat 208) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 71) (EVar 32) (exW_canary SEGS 415784 m1) s 208 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (exW_kn_clr SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) 217704 217712 217704 217712 HW1 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat F5D_STOPS F5_FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A0 M1 (with_vmmaps vm0 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A0 A0 m1 _ E1 log1 (EVar 32) s 208 [] CK HW1 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BSF HR ex_r10 G10.
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ => apply (HC fxk M1 RcF FZ HWs1) end.
  - lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end.
  - eapply POSTM_trans; [exact PM1 | exact PMs1].
  - exact G10.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem F5_W_gen : F5_contract.
Proof.
  unfold F5_contract, gq_F_contract.
  intros fx C X A m md regs s pix w h d cd data ad kd kna kn ret S FZ CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 (H11 & H12 & H13) OWN HOK Hw Hh kR bR RM HkR HbR HC.
  unfold GQ_STACK_F, TP_gq in *.
  destruct OWN as [P0 | OWN].
  - subst pix.
    apply (F5_null_W fx C A m md regs s ret S FZ CK HW H2 Hs16 ltac:(unfold GQ_ARM_STACK, LSF; lia) Hhi H1 Hret H10).
    intros fx' m' regs' FZ' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
    apply (HC fx' A m' (m_vmmaps md) regs' FZ' ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
    apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_mask, RK_pix in *; lia | clear - HbR; unfold RB_mask, RB_pix14 in *; lia].
  - destruct OWN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    destruct (Z.eq_dec d 32) as [->|ND].
    + apply (F5_ok fx C A m md regs s pix w h cd data ret S FZ CK HW H2 Hs16 ltac:(unfold F5_STACK, LSF; lia) Hhi H1 Hret H4 H10 H11 H12 H13
               PX HOK Hw Hh Lp Ld ALd kR bR RM HkR HbR).
      intros fx' A' m' vm' regs' FZ' HW' CS' PM' (pixd & datad & A0' & PN) RM'.
      apply (HC fx' A' m' vm' regs' FZ' HW' CS' PM'); [|exact RM'].
      right. exists pixd, w, h, 1%Z, 0%Z, datad, cmap0. split; [exact A0' | split; [exact PN|]].
      assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). nia.
    + pose proof PX as (_ & _ & WF & _). pose proof (wf_w _ WF) as Rw. pose proof (wf_h _ WF) as Rh. pose proof (wf_d _ WF) as Rd. cbn in Rw, Rh, Rd.
      apply (F5_d fx C A m md regs s pix w h d ret S FZ CK HW H2 Hs16 ltac:(unfold F5D_STACK, LSF; lia) Hhi H1 Hret H10 Lp ltac:(lia) ltac:(lia) ALp Rw Rh Rd ND
               ltac:(rewrite Z.add_0_r; exact (PIX_rd_w SEGS m pix _ PX)) (PIX_rd_h SEGS m pix _ PX) (PIX_rd_d SEGS m pix _ PX)).
      intros fx' m' regs' FZ' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
      apply (HC fx' A m' (m_vmmaps md) regs' FZ' ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
      apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_mask, RK_pix in *; lia | clear - HbR; unfold RB_mask, RB_pix14 in *; lia].
Qed.
End Chains.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem F4_W : F4_contract. Proof. exact (F4_W_gen band32_loop_hop_W). Qed.
Theorem F5_W : F5_contract. Proof. exact (F5_W_gen discr32_loop_hop_W). Qed.
End Chain.
