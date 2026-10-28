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
Import V15CL7a.V15LeptErr. Import V15CL7a.V15LeptPixClone.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL8a.
Import V15CL8a.V15LeptPixHdr. Import V15CL8a.V15LeptGqArms.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL9a.
Import V15CL9a.V15LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL10a.
Import V15CL10a.V15LeptCmapValid. Import V15CL10a.V15LeptPixCreateS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15LeptCmap2 V15LeptPixCopyA V15LeptPixCopy V15LeptPixHdrS.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL14a.
Import V15CL14a.V15LeptThrLeaf. Import V15CL14a.V15LeptDither_iface.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL15a.
Import V15CL15a.V15LeptOwn.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15CL16a.
Import V15CL16a.V15LeptGq_iface.
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


Definition BAND_WIN : Z := 128.
Definition BAND_STACK : Z := 128 + 112 + LSF + 64.
Definition STOPS : list Z := [96700; 93000; 95132; 95788; 115564; 94372]%Z.
Definition FDEF : list (nat * nat) := [(8%nat, 33%nat)].
Definition PC_PIXCREATE : word := 93000%bv.
Lemma PC_PIXCREATE_eq : Z_to_bv 64 93000 = PC_PIXCREATE. Proof. apply bv_eq; reflexivity. Qed.
Definition ex_r14 : reg := 14%bv. Definition ex_r18 : reg := 18%bv. Definition ex_r19 : reg := 19%bv. Definition ex_r20 : reg := 20%bv. Definition ex_r22 : reg := 22%bv. Definition ex_r23 : reg := 23%bv.
Definition BAND_HEAD : Z := 115564.   Definition BAND_EXIT : Z := 116064.
Definition BAND_CLOB : list reg := [5; 6; 7; 11; 12; 13; 14; 15; 16; 17; 21; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

(* [comment removed for export] *)
Definition band_loop_hop : Prop := forall (fx : FPState) C A Ar M md regs (s w h d datad datag : Z) (S : TSet),
  Cok C -> W C A M md -> sub_live Ar A -> (c_top C - LSTK + BAND_WIN <= s)%Z -> (s <= c_top C)%Z ->
  hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> (d = 2 \/ d = 4 \/ d = 8)%Z ->
  live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 1 * h))%Z -> live Ar (Z_to_bv 64 datad) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  live A (Z_to_bv 64 datag) = Some (4 * (wpl_of w d * h))%Z ->
  Z_to_bv 64 datad <> Z_to_bv 64 datag -> (0 <= datad < 2 ^ 64)%Z -> (0 <= datag < 2 ^ 64)%Z ->
  getr regs 2 = Z_to_bv 64 (s + -128) -> getr regs 18 = Z_to_bv 64 datag -> getr regs 19 = Z_to_bv 64 (wpl_of w d) -> getr regs 20 = Z_to_bv 64 datad ->
  getr regs 10 = Z_to_bv 64 (wpl_of w 1) -> getr regs 9 = Z_to_bv 64 1 -> getr regs 8 = Z_to_bv 64 2 -> getr regs 23 = Z_to_bv 64 1 ->
  rdn SEGS M (Z_to_bv 64 (s + -112)) 4 = Some (Z_to_le_bytes 4 h) -> rdn SEGS M (Z_to_bv 64 (s + -108)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS M (Z_to_bv 64 (s + -116)) 4 = Some (Z_to_le_bytes 4 d) ->
  (forall regs' m', W C A m' md -> POSTM C Ar s M m' -> regs_agree (fun r => In r BAND_CLOB) regs regs' ->
      (forall x : word, ~ (datad <= u x < datad + 4 * (wpl_of w 1 * h))%Z -> m' x = M x) ->
      realizes SEGS (mkCfg (@mkst fx regs' (Z_to_bv 64 BAND_EXIT) m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 BAND_HEAD) M al_rom) md) S.

Lemma ne_live : forall (A : AS) (p q : word) (k : Z), live A p = Some k -> live A q = None -> p <> q.
Proof. intros A p q k L F ->. rewrite F in L. discriminate L. Qed.
Lemma hdr_ok_1 : forall w h d, hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z -> hdr_ok w h 1.
Proof.
  intros w h d (DV & Hw & Hh & _) Hw1 Hh1. unfold hdr_ok. split; [left; reflexivity|]. split; [exact Hw|]. split; [exact Hh|].
  assert (wpl_of w 1 <= 626)%Z by (unfold wpl_of; apply Z.div_le_upper_bound; lia).
  assert (0 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_pos; lia). nia.
Qed.

Section Band.
Hypothesis HRC2 : pixDestroy_rc2_contract.
Hypothesis HLOOP : band_loop_hop.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma band_ok_2 : forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BAND_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 284096 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 2 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 ->
  PIXat m pixs (hdv w h 2 cm data) -> hdr_ok w h 2 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 2 * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pix14 <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
      (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 0 datad cmap0) ->
      aroom A' vm' (kR - RK_pix) (bR - RB_pix14) ->
      realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 114844) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm data ret S CK HW0 H2 Hs16 HloS Hhi H1 Hret H4 H10 H11 H12 H13 H14 PXs HOK Hw1 Hh1 Lpixs_a0 F0pixs Ldata_a0 kR bR RM0 HkR HbR HC.
  unfold BAND_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 128 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 284096)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 128)%Z) by lia.
  assert (GLO2 : (s - 128 + Z.of_nat (Z.to_nat 128) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (128 <= s)%Z) by lia.
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (Rwpl : (1 <= wpl_of w 2 < 2 ^ 31)%Z).
  { destruct HOK as (_ & _ & _ & X). assert (1 <= wpl_of w 2)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  pose proof (hdr_ok_1 w h 2 HOK Hw1 Hh1) as HOK1.
  assert (Rwpl1 : (1 <= wpl_of w 1 < 2 ^ 31)%Z).
  { destruct HOK1 as (_ & _ & _ & X). assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  assert (Rn1 : (0 < 4 * (wpl_of w 1 * h))%Z) by nia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  pose proof PXs as (Hps0 & Hps64 & WFs & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof (wf_data _ WFs) as RRdata. cbn in RRdata.
  destruct (exW_blk_rng C A0 m0 _ pixs 64 CK HW0 Lpixs_a0 RRpixs eq_refl) as (Gps1 & Gps2 & _).
  assert (BLWpixs : (pixs + 64 <= s - 128)%Z) by lia.
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 2; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 32) (EVar 37) (EVar 38) pixs s 128 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 2; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 35) (EVar 36) (ELit 2) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 128) (Z.to_nat 128) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 2; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 2; exW_canary SEGS 415784 m0]) (EVar 39) (EVar 32) (exW_canary SEGS 415784 m0) s 128 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 2; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 2; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430208 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 2; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 128 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h 2 cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 128 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (PMB : POSTM C A0 s m0 M0) by exact (POSTM_trans _ _ _ _ _ _ PM0 PMs0).
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixClone_W fxk C A0 M0 _ Rc0 (s + OFF0)%Z pixs (hdv w h 2 cm data) (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(unfold OFF0; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q10_0 PXsM0 eq_refl Lpixs_a0 F0pixs) end end.
  intros m1 r1 EM1 HW1 CSx0 A10_0.
  pose proof CSx0 as CS0. clear CSx0.
  assert (PMR : POSTM C A0 s (wbytes M0 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) m1) by (rewrite EM1; apply POSTM_refl).
  assert (CLONEK : forall (Ax : AS) (mx my : word -> option byte) (mdx : Model) (pp : Z), W C Ax mx mdx -> sub_live A0 Ax -> (0 <= pp)%Z -> (c_top C - LSTK <= pp)%Z -> (pp + 8 <= s)%Z ->
             POSTM C A0 s m1 mx -> POSTM C Ax (pp + 8) (wbytes (wbytes mx (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) my -> POSTM C A0 s m0 my).
  { intros Ax mx my mdx pp HWx SUBx P0 P1 P2 PM23 PM34. eapply POSTM_trans; [exact PMB|].
    exact (exT_postm_clone C A0 A0 Ax M0 m1 mx my _ mdx s pp pixs (hdv w h 2 cm data) CK HWs0 HWx (sub_live_refl A0) SUBx PXsM0 eq_refl Lpixs_a0 P0 P1 P2 Hhi PMR PM23 PM34). }
  assert (PXs1 : PIXat m1 pixs (set_rc (hdv w h 2 cm data) 2)).
  { rewrite EM1, <- (w2b_Z 4 2) by lia. exact (PIX_wr_rc M0 pixs _ 2 PXsM0 ltac:(lia)). }
  pose proof (exT_wbytes_out M0 m1 (pixs + 20) (Z_to_le_bytes 4 2) EM1 ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia)) as OUT0.
  rewrite length_Z_to_le_bytes in OUT0. change (Z.of_nat 4) with 4%Z in OUT0.
  pose proof (POSTM_refl C A0 s m1) as PM1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [apply (exW_kept_out E0 M0 m1 (EVar 32) s OFF0 0 (pixs + 20) (pixs + 20 + 4) OUT0 eq_refl RS); right; unfold OFF0; lia|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 40%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 415784 m1] 40%nat ltac:(vm_cast_no_check (eq_refl 40%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 40%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 40%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 34) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q1_0 Q2_0 PM0 HW0 FRs0 CS0 OFF0 A10_0 PXsM0 PMB PMR EM1 OUT0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exT_kn_whd SEGS m1 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 34) (EVar 35) (EVar 36) (ELit 2) pixs _ PXs1 eq_refl eq_refl eq_refl eq_refl) as HKd1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m1 _ (s - 128) (Z.to_nat 128) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 128 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (exW_kn_clr SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) 217704 217712 217704 217712 HW1 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKd1 (proj2 (Forall_app _ _ _) (conj HKx0_1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKd1 HKx0_1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A0 M1 (with_vmmaps vm0 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A0 A0 m1 _ E1 log1 (EVar 32) s 128 [] CK HW1 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r12 Q12_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  rewrite PC_PIXCREATE_eq.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCreate_sure_W (fx := fxk) C A0 M1 _ Rc1 (s + OFF1) w h 1 (Z_to_bv 64 ra) S CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, LSF; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 Q11_1 Q12_1 Hw1 Hh1 HOK1 kR bR
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) HkR HbR) end end.
  intros A1 m2 vm1 r2 pixd datad HW2 CSx1 PMc1 A10_1 PXN RM1.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct PXN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdatad & NEpd & Fpixd & Fdatad & F0pixd & F0datad & Lpixd_a1 & Ldatad_a1 & LEQ1 & PXd2 & _).
  change (p_wpl (set_data (pix_hdr w h 1) datad)) with (wpl_of w 1) in Gdd2, Ldatad_a1. change (p_h (set_data (pix_hdr w h 1) datad)) with h in Gdd2, Ldatad_a1.
  assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia. assert (RRdatad : (0 <= datad < 2 ^ 64)%Z) by lia.
  assert (SUB1 : sub_live A0 A1).
  { intros q0 kq Lq. rewrite (LEQ1 q0 (ne_live A0 q0 _ kq Lq Fpixd) (ne_live A0 q0 _ kq Lq Fdatad)). exact Lq. }
  pose proof LEQ1 as LEQK.
  pose proof (SUB1 _ _ Lpixs_a0) as Lpixs_a1. pose proof (SUB1 _ _ Ldata_a0) as Ldata_a1.
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fpixd) as NE_pixs_pixd.
  assert (NE_pixd_pixs : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (intros EE; exact (NE_pixs_pixd (eq_sym EE))).
  assert (NE_pixd_datad : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros EE; apply NEpd; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fdatad) as NE_pixs_datad.
  assert (NE_datad_data : Z_to_bv 64 datad <> Z_to_bv 64 data) by (intros EE; exact (ne_live A0 _ _ _ Ldata_a0 Fdatad (eq_sym EE))).
  pose proof (exW_win_blk_apart_h C A1 m2 _ s 128 datad (4 * (wpl_of w 1 * h)) CK HW2 Ldatad_a1 Rn1 RRdatad GLO1) as WAPdatad.
  assert (PM2 : POSTM C A0 s m1 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_mono C A0 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (exT_pix_livk A0 _ m2 pixs _ (exT_pix_sess C A0 m1 M1 _ s 128 pixs _ CK HW1 GLO1 Lpixs_a0 PXs1 FRs1) (proj2 PMc1) Lpixs_a0) as PXs2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 128 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 73%nat E1 (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q12_1 Q1_1 Q2_1 Q4_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 LEQ1 RM0 A10_1 PXs1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exT_kn_pix SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) (EVar 105) (EVar 32) (EVar 106) (EVar 107) pixd s 128 _ CK HW2 Lpixd_a1 PXd2 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp2.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m2 _ (s - 128) (Z.to_nat 128) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) (EVar 108) (EVar 32) (exW_canary SEGS 415784 m2) s 128 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (exW_kn_clr SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) 217704 217712 217704 217712 HW2 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp2 (proj2 (Forall_app _ _ _) (conj HKx0_2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp2 HKx0_2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A1 A0 m2 _ E2 log2 (EVar 32) s 128 [] CK HW2 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  assert (PXsM2 : PIXat M2 pixs (set_rc (hdv w h 2 cm data) 2)) by exact (exT_pix_sess C A1 m2 M2 _ s 128 pixs _ CK HW2 GLO1 Lpixs_a1 PXs2 FRs2).
  assert (PXdM2 : PIXat M2 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m2 M2 _ s 128 pixd _ CK HW2 GLO1 Lpixd_a1 PXd2 FRs2).
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyRes0_W fxk C A0 A1 M2 _ Rc2 (s + OFF2) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs2 SUB1 Q2_2
             ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) Q1_2 ltac:(red; apply bv_eq; reflexivity) Q10_2 Q11_2 PXsM2 PXdM2 eq_refl eq_refl eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m3 r3 HW3 CSx2 PMc2 PXd3 A10_2.
  pose proof CSx2 as CS2. clear CSx2.
  assert (PM3 : POSTM C A0 s m1 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_mono C A0 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (exT_pix_livk A0 M2 m3 pixs _ PXsM2 (proj2 PMc2) Lpixs_a0) as PXs3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 128 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
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
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m3 _ (s - 128) (Z.to_nat 128) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 141) (EVar 32) (exW_canary SEGS 415784 m3) s 128 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (exW_kn_clr SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) 217704 217712 217704 217712 HW3 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A1 A0 m3 _ E3 log3 (EVar 32) s 128 [] CK HW3 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  assert (PXsM3 : PIXat M3 pixs (set_rc (hdv w h 2 cm data) 2)) by exact (exT_pix_sess C A1 m3 M3 _ s 128 pixs _ CK HW3 GLO1 Lpixs_a1 PXs3 FRs3).
  assert (PXdM3 : PIXat M3 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m3 M3 _ s 128 pixd _ CK HW3 GLO1 Lpixd_a1 PXd3 FRs3).
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyFmt0_W fxk C A0 A1 M3 _ Rc3 (s + OFF3) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs3 SUB1 Q2_3
             ltac:(unfold OFF3; lia) ltac:(unfold OFF3; lia) Q1_3 ltac:(red; apply bv_eq; reflexivity) Q10_3 Q11_3 PXsM3 PXdM3 eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m4 r4 HW4 CSx3 PMc3 PXd4 A10_3.
  pose proof CSx3 as CS3. clear CSx3.
  assert (PM4 : POSTM C A0 s m1 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_mono C A0 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  pose proof (exT_pix_livk A0 M3 m4 pixs _ PXsM3 (proj2 PMc3) Lpixs_a0) as PXs4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 128 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 142%nat ltac:(vm_cast_no_check (eq_refl 142%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 142%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 PM3 HW3 FRs3 PMc3 CS3 OFF3 A10_3 PXsM3 PXdM3 PXd3 PXs3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exT_kn_cells SEGS m4 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 34) (EVar 37) (EVar 38) pixs _ PXs4 eq_refl eq_refl eq_refl) as HKg4.
  pose proof (exT_kn_cells SEGS m4 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 105) (EVar 106) (EVar 107) pixd _ PXd4 eq_refl eq_refl eq_refl) as HKh4.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m4 _ (s - 128) (Z.to_nat 128) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 174) (EVar 32) (exW_canary SEGS 415784 m4) s 128 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (exW_kn_clr SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) 217704 217712 217704 217712 HW4 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKg4 (proj2 (Forall_app _ _ _) (conj HKh4 (proj2 (Forall_app _ _ _) (conj HKx0_4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKg4 HKh4 HKx0_4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A1 A0 m4 _ E4 log4 (EVar 32) s 128 [] CK HW4 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  pose proof (exW_win_only E4 m4 log4 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs4. change (mem_denot E4 m4 log4) with M4 in FRs4.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r18 Q18_4. exW_regfactB BS4 HR ex_r19 Q19_4. exW_regfactB BS4 HR ex_r20 Q20_4. exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r9 Q9_4. exW_regfactB BS4 HR ex_r8 Q8_4. exW_regfactB BS4 HR ex_r23 Q23_4.
  clear BS4.
  (* [comment removed for export] *)
  pose (BSx4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-112)%Z 4%nat CELLh. exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-108)%Z 4%nat CELLw.
  exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-116)%Z 4%nat CELLd.
  clear BSx4.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HLOOP fxk C A1 A0 M4 _ Rc4 s w h 2%Z datad data S CK HWs4 SUB1 Hlo Hhi HOK Hw1 Hh1 ltac:(lia) Ldatad_a1 Fdatad F0datad Ldata_a1 NE_datad_data RRdatad RRdata
             Q2_4 Q18_4 Q19_4 Q20_4 Q10_4 Q9_4 Q8_4 Q23_4 CELLh CELLw CELLd) end.
  intros r5 m5 HW5 PMl4 AGR4 FRM4.
  assert (PM5 : POSTM C A0 s m1 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4 | exact PMl4]. }
  assert (PXd5 : PIXat m5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_frm C A1 M4 m5 _ pixd datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) _ CK HWs4 Lpixd_a1 Ldatad_a1 NE_pixd_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A1 m4 M4 _ s 128 pixd _ CK HW4 GLO1 Lpixd_a1 PXd4 FRs4) FRM4).
  assert (PXs5 : PIXat m5 pixs (set_rc (hdv w h 2 cm data) 2)) by exact (exT_pix_frm C A1 M4 m5 _ pixs datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) _ CK HWs4 Lpixs_a1 Ldatad_a1 NE_pixs_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A1 m4 M4 _ s 128 pixs _ CK HW4 GLO1 Lpixs_a1 PXs4 FRs4) FRM4).
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, (-128)%Z, (-128 + 128)%Z)]).
  { constructor; [exact (exW_kept_frame E4 M4 m5 (EVar 32) s (-128) 128 datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) FRM4 eq_refl RS WAPdatad (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 175%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_keep _ _ _ _ _ [5%nat; 6%nat; 7%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 21%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] HRa4 (ex_regs_ok_junk vals4 r5 [exW_canary SEGS 415784 m5] 175%nat ltac:(vm_cast_no_check (eq_refl 175%nat))) (exW_agree_keep _ _ _ AGR4)) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) m5 _) by (exact (know_ok_agree SEGS 175%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 175%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q2_4 Q18_4 Q19_4 Q20_4 Q10_4 Q9_4 Q8_4 Q23_4 PM4 HW4 FRs4 AGR4 FRM4 PMl4 CELLh CELLw CELLd PXd4 PXs4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m5 _ (s - 128) (Z.to_nat 128) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 415784 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m5]).
  pose proof (exW_kn_fixed SEGS C A1 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) (EVar 207) (EVar 32) (exW_canary SEGS 415784 m5) s 128 415784 65536 212992 213416 213568 213416 213568
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (exW_kn_clr SEGS C A1 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) 217704 217712 217704 217712 HW5 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A1 M5 (with_vmmaps vm1 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A1 A0 m5 _ E5 log5 (EVar 32) s 128 [] CK HW5 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  pose proof (exW_win_only E5 m5 log5 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs5. change (mem_denot E5 m5 log5) with M5 in FRs5.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  (* [comment removed for export] *)
  pose (BSx5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-128)%Z 8%nat CELLpp.
  clear BSx5.
  assert (PXdM5 : PIXat M5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m5 M5 _ s 128 pixd _ CK HW5 GLO1 Lpixd_a1 PXd5 FRs5).
  assert (PXsM5 : PIXat M5 pixs (set_rc (hdv w h 2 cm data) 2)) by exact (exT_pix_sess C A1 m5 M5 _ s 128 pixs _ CK HW5 GLO1 Lpixs_a1 PXs5 FRs5).
  assert (PPlo : (s + OFF5 <= s + -128)%Z) by (unfold OFF5; lia). assert (PPhi : (s + -128 + 8 <= c_top C)%Z) by lia.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HRC2 fxk C A1 M5 _ Rc5 (s + OFF5)%Z (s + -128)%Z pixs (set_rc (hdv w h 2 cm data) 2) (Z_to_bv 64 ra) S CK HWs5 Q2_5
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF5, PXD2_STACK, ALLOC_STACK; lia) PPlo PPhi ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q1_5 ltac:(red; apply bv_eq; reflexivity) Q10_5 CELLpp
             PXsM5 eq_refl Lpixs_a1 F0pixs) end end.
  intros m6 r6 HW6 CSx5 PMD.
  pose proof CSx5 as CS5. clear CSx5.
  assert (PMB6 : POSTM C A0 s m0 m6).
  { apply (CLONEK A1 M5 m6 _ (s + -128)%Z HWs5 SUB1 ltac:(lia) ltac:(lia) ltac:(lia) (POSTM_trans _ _ _ _ _ _ PM5 PMs5) PMD). }
  assert (PXd6 : PIXat m6 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_patch2 C A1 A1 M5 m6 _ pixd pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) _ CK HWs5 Lpixd_a1 Lpixs_a1 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM5 (proj2 PMD) Lpixd_a1).
  assert (FRMx5 : FRM C (s + -120) (wbytes (wbytes M5 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 (s + -128)) (Z_to_le_bytes 8 0)) m6).
  { replace (s + -120)%Z with (s + -128 + 8)%Z by lia. exact (proj1 PMD). }
  pose proof (POSTM_refl C A0 s m6) as PM6.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, (-120)%Z, 0%Z)]).
  { constructor; [exact (exT_kept_patch2 C A1 _ s (-120) 128 M5 m6 E5 (EVar 32) pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) CK HWs5 Lpixs_a1 RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) FRMx5 Hlo Hhi eq_refl eq_refl eq_refl ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia))|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 208%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 415784 m6] 208%nat ltac:(vm_cast_no_check (eq_refl 208%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) m6 _) by (exact (know_ok_agree SEGS 208%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 208%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q1_5 Q2_5 PM5 HW5 FRs5 CS5 OFF5 CELLpp PXdM5 PXsM5 PPlo PPhi PXd5 PXs5 PMD FRMx5 CLONEK.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m6 _ (s - 128) (Z.to_nat 128) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 415784 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m6]).
  pose proof (exW_kn_fixed SEGS C A1 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) (EVar 240) (EVar 32) (exW_canary SEGS 415784 m6) s 128 415784 65536 212992 213416 213568 213416 213568
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (exW_kn_clr SEGS C A1 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) 217704 217712 217704 217712 HW6 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A1 M6 (with_vmmaps vm1 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A1 A0 m6 _ E6 log6 (EVar 32) s 128 [] CK HW6 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  pose proof (exW_win_only E6 m6 log6 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs6. change (mem_denot E6 m6 log6) with M6 in FRs6.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 2); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BSF HR ex_r10 G10.
  apply (HC A1 M6 vm1 RcF HWs6).
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PMB6 PMs6).
  + exists pixd, datad. split; [exact G10|].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a1 (conj Ldatad_a1 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A1 m6 M6 _ s 128 pixd _ CK HW6 GLO1 Lpixd_a1 PXd6 FRs6).
    * left. split; [reflexivity|]. intros q0 N1 N2. exact (LEQK q0 N1 N2).
  + exact RM1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma band_ok_4 : forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BAND_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 284096 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 2 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 ->
  PIXat m pixs (hdv w h 4 cm data) -> hdr_ok w h 4 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 4 * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pix14 <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
      (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 0 datad cmap0) ->
      aroom A' vm' (kR - RK_pix) (bR - RB_pix14) ->
      realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 114844) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm data ret S CK HW0 H2 Hs16 HloS Hhi H1 Hret H4 H10 H11 H12 H13 H14 PXs HOK Hw1 Hh1 Lpixs_a0 F0pixs Ldata_a0 kR bR RM0 HkR HbR HC.
  unfold BAND_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 128 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 284096)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 128)%Z) by lia.
  assert (GLO2 : (s - 128 + Z.of_nat (Z.to_nat 128) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (128 <= s)%Z) by lia.
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (Rwpl : (1 <= wpl_of w 4 < 2 ^ 31)%Z).
  { destruct HOK as (_ & _ & _ & X). assert (1 <= wpl_of w 4)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  pose proof (hdr_ok_1 w h 4 HOK Hw1 Hh1) as HOK1.
  assert (Rwpl1 : (1 <= wpl_of w 1 < 2 ^ 31)%Z).
  { destruct HOK1 as (_ & _ & _ & X). assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  assert (Rn1 : (0 < 4 * (wpl_of w 1 * h))%Z) by nia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  pose proof PXs as (Hps0 & Hps64 & WFs & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof (wf_data _ WFs) as RRdata. cbn in RRdata.
  destruct (exW_blk_rng C A0 m0 _ pixs 64 CK HW0 Lpixs_a0 RRpixs eq_refl) as (Gps1 & Gps2 & _).
  assert (BLWpixs : (pixs + 64 <= s - 128)%Z) by lia.
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 4; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 32) (EVar 37) (EVar 38) pixs s 128 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 4; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 35) (EVar 36) (ELit 4) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 128) (Z.to_nat 128) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 4; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 4; exW_canary SEGS 415784 m0]) (EVar 39) (EVar 32) (exW_canary SEGS 415784 m0) s 128 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 4; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 4; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430208 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 4; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 128 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h 4 cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 128 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (PMB : POSTM C A0 s m0 M0) by exact (POSTM_trans _ _ _ _ _ _ PM0 PMs0).
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixClone_W fxk C A0 M0 _ Rc0 (s + OFF0)%Z pixs (hdv w h 4 cm data) (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(unfold OFF0; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q10_0 PXsM0 eq_refl Lpixs_a0 F0pixs) end end.
  intros m1 r1 EM1 HW1 CSx0 A10_0.
  pose proof CSx0 as CS0. clear CSx0.
  assert (PMR : POSTM C A0 s (wbytes M0 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) m1) by (rewrite EM1; apply POSTM_refl).
  assert (CLONEK : forall (Ax : AS) (mx my : word -> option byte) (mdx : Model) (pp : Z), W C Ax mx mdx -> sub_live A0 Ax -> (0 <= pp)%Z -> (c_top C - LSTK <= pp)%Z -> (pp + 8 <= s)%Z ->
             POSTM C A0 s m1 mx -> POSTM C Ax (pp + 8) (wbytes (wbytes mx (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) my -> POSTM C A0 s m0 my).
  { intros Ax mx my mdx pp HWx SUBx P0 P1 P2 PM23 PM34. eapply POSTM_trans; [exact PMB|].
    exact (exT_postm_clone C A0 A0 Ax M0 m1 mx my _ mdx s pp pixs (hdv w h 4 cm data) CK HWs0 HWx (sub_live_refl A0) SUBx PXsM0 eq_refl Lpixs_a0 P0 P1 P2 Hhi PMR PM23 PM34). }
  assert (PXs1 : PIXat m1 pixs (set_rc (hdv w h 4 cm data) 2)).
  { rewrite EM1, <- (w2b_Z 4 2) by lia. exact (PIX_wr_rc M0 pixs _ 2 PXsM0 ltac:(lia)). }
  pose proof (exT_wbytes_out M0 m1 (pixs + 20) (Z_to_le_bytes 4 2) EM1 ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia)) as OUT0.
  rewrite length_Z_to_le_bytes in OUT0. change (Z.of_nat 4) with 4%Z in OUT0.
  pose proof (POSTM_refl C A0 s m1) as PM1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [apply (exW_kept_out E0 M0 m1 (EVar 32) s OFF0 0 (pixs + 20) (pixs + 20 + 4) OUT0 eq_refl RS); right; unfold OFF0; lia|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 40%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 415784 m1] 40%nat ltac:(vm_cast_no_check (eq_refl 40%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 40%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 40%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 34) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q1_0 Q2_0 PM0 HW0 FRs0 CS0 OFF0 A10_0 PXsM0 PMB PMR EM1 OUT0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exT_kn_whd SEGS m1 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 34) (EVar 35) (EVar 36) (ELit 4) pixs _ PXs1 eq_refl eq_refl eq_refl eq_refl) as HKd1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m1 _ (s - 128) (Z.to_nat 128) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 128 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (exW_kn_clr SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) 217704 217712 217704 217712 HW1 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKd1 (proj2 (Forall_app _ _ _) (conj HKx0_1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKd1 HKx0_1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A0 M1 (with_vmmaps vm0 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A0 A0 m1 _ E1 log1 (EVar 32) s 128 [] CK HW1 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r12 Q12_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  rewrite PC_PIXCREATE_eq.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCreate_sure_W (fx := fxk) C A0 M1 _ Rc1 (s + OFF1) w h 1 (Z_to_bv 64 ra) S CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, LSF; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 Q11_1 Q12_1 Hw1 Hh1 HOK1 kR bR
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) HkR HbR) end end.
  intros A1 m2 vm1 r2 pixd datad HW2 CSx1 PMc1 A10_1 PXN RM1.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct PXN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdatad & NEpd & Fpixd & Fdatad & F0pixd & F0datad & Lpixd_a1 & Ldatad_a1 & LEQ1 & PXd2 & _).
  change (p_wpl (set_data (pix_hdr w h 1) datad)) with (wpl_of w 1) in Gdd2, Ldatad_a1. change (p_h (set_data (pix_hdr w h 1) datad)) with h in Gdd2, Ldatad_a1.
  assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia. assert (RRdatad : (0 <= datad < 2 ^ 64)%Z) by lia.
  assert (SUB1 : sub_live A0 A1).
  { intros q0 kq Lq. rewrite (LEQ1 q0 (ne_live A0 q0 _ kq Lq Fpixd) (ne_live A0 q0 _ kq Lq Fdatad)). exact Lq. }
  pose proof LEQ1 as LEQK.
  pose proof (SUB1 _ _ Lpixs_a0) as Lpixs_a1. pose proof (SUB1 _ _ Ldata_a0) as Ldata_a1.
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fpixd) as NE_pixs_pixd.
  assert (NE_pixd_pixs : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (intros EE; exact (NE_pixs_pixd (eq_sym EE))).
  assert (NE_pixd_datad : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros EE; apply NEpd; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fdatad) as NE_pixs_datad.
  assert (NE_datad_data : Z_to_bv 64 datad <> Z_to_bv 64 data) by (intros EE; exact (ne_live A0 _ _ _ Ldata_a0 Fdatad (eq_sym EE))).
  pose proof (exW_win_blk_apart_h C A1 m2 _ s 128 datad (4 * (wpl_of w 1 * h)) CK HW2 Ldatad_a1 Rn1 RRdatad GLO1) as WAPdatad.
  assert (PM2 : POSTM C A0 s m1 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_mono C A0 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (exT_pix_livk A0 _ m2 pixs _ (exT_pix_sess C A0 m1 M1 _ s 128 pixs _ CK HW1 GLO1 Lpixs_a0 PXs1 FRs1) (proj2 PMc1) Lpixs_a0) as PXs2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 128 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 73%nat E1 (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q12_1 Q1_1 Q2_1 Q4_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 LEQ1 RM0 A10_1 PXs1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exT_kn_pix SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) (EVar 105) (EVar 32) (EVar 106) (EVar 107) pixd s 128 _ CK HW2 Lpixd_a1 PXd2 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp2.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m2 _ (s - 128) (Z.to_nat 128) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) (EVar 108) (EVar 32) (exW_canary SEGS 415784 m2) s 128 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (exW_kn_clr SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) 217704 217712 217704 217712 HW2 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp2 (proj2 (Forall_app _ _ _) (conj HKx0_2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp2 HKx0_2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A1 A0 m2 _ E2 log2 (EVar 32) s 128 [] CK HW2 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  assert (PXsM2 : PIXat M2 pixs (set_rc (hdv w h 4 cm data) 2)) by exact (exT_pix_sess C A1 m2 M2 _ s 128 pixs _ CK HW2 GLO1 Lpixs_a1 PXs2 FRs2).
  assert (PXdM2 : PIXat M2 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m2 M2 _ s 128 pixd _ CK HW2 GLO1 Lpixd_a1 PXd2 FRs2).
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyRes0_W fxk C A0 A1 M2 _ Rc2 (s + OFF2) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs2 SUB1 Q2_2
             ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) Q1_2 ltac:(red; apply bv_eq; reflexivity) Q10_2 Q11_2 PXsM2 PXdM2 eq_refl eq_refl eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m3 r3 HW3 CSx2 PMc2 PXd3 A10_2.
  pose proof CSx2 as CS2. clear CSx2.
  assert (PM3 : POSTM C A0 s m1 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_mono C A0 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (exT_pix_livk A0 M2 m3 pixs _ PXsM2 (proj2 PMc2) Lpixs_a0) as PXs3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 128 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
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
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m3 _ (s - 128) (Z.to_nat 128) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 141) (EVar 32) (exW_canary SEGS 415784 m3) s 128 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (exW_kn_clr SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) 217704 217712 217704 217712 HW3 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A1 A0 m3 _ E3 log3 (EVar 32) s 128 [] CK HW3 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  assert (PXsM3 : PIXat M3 pixs (set_rc (hdv w h 4 cm data) 2)) by exact (exT_pix_sess C A1 m3 M3 _ s 128 pixs _ CK HW3 GLO1 Lpixs_a1 PXs3 FRs3).
  assert (PXdM3 : PIXat M3 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m3 M3 _ s 128 pixd _ CK HW3 GLO1 Lpixd_a1 PXd3 FRs3).
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyFmt0_W fxk C A0 A1 M3 _ Rc3 (s + OFF3) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs3 SUB1 Q2_3
             ltac:(unfold OFF3; lia) ltac:(unfold OFF3; lia) Q1_3 ltac:(red; apply bv_eq; reflexivity) Q10_3 Q11_3 PXsM3 PXdM3 eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m4 r4 HW4 CSx3 PMc3 PXd4 A10_3.
  pose proof CSx3 as CS3. clear CSx3.
  assert (PM4 : POSTM C A0 s m1 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_mono C A0 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  pose proof (exT_pix_livk A0 M3 m4 pixs _ PXsM3 (proj2 PMc3) Lpixs_a0) as PXs4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 128 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 142%nat ltac:(vm_cast_no_check (eq_refl 142%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 142%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 PM3 HW3 FRs3 PMc3 CS3 OFF3 A10_3 PXsM3 PXdM3 PXd3 PXs3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exT_kn_cells SEGS m4 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 34) (EVar 37) (EVar 38) pixs _ PXs4 eq_refl eq_refl eq_refl) as HKg4.
  pose proof (exT_kn_cells SEGS m4 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 105) (EVar 106) (EVar 107) pixd _ PXd4 eq_refl eq_refl eq_refl) as HKh4.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m4 _ (s - 128) (Z.to_nat 128) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 174) (EVar 32) (exW_canary SEGS 415784 m4) s 128 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (exW_kn_clr SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) 217704 217712 217704 217712 HW4 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKg4 (proj2 (Forall_app _ _ _) (conj HKh4 (proj2 (Forall_app _ _ _) (conj HKx0_4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKg4 HKh4 HKx0_4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A1 A0 m4 _ E4 log4 (EVar 32) s 128 [] CK HW4 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  pose proof (exW_win_only E4 m4 log4 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs4. change (mem_denot E4 m4 log4) with M4 in FRs4.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r18 Q18_4. exW_regfactB BS4 HR ex_r19 Q19_4. exW_regfactB BS4 HR ex_r20 Q20_4. exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r9 Q9_4. exW_regfactB BS4 HR ex_r8 Q8_4. exW_regfactB BS4 HR ex_r23 Q23_4.
  clear BS4.
  (* [comment removed for export] *)
  pose (BSx4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-112)%Z 4%nat CELLh. exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-108)%Z 4%nat CELLw.
  exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-116)%Z 4%nat CELLd.
  clear BSx4.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HLOOP fxk C A1 A0 M4 _ Rc4 s w h 4%Z datad data S CK HWs4 SUB1 Hlo Hhi HOK Hw1 Hh1 ltac:(lia) Ldatad_a1 Fdatad F0datad Ldata_a1 NE_datad_data RRdatad RRdata
             Q2_4 Q18_4 Q19_4 Q20_4 Q10_4 Q9_4 Q8_4 Q23_4 CELLh CELLw CELLd) end.
  intros r5 m5 HW5 PMl4 AGR4 FRM4.
  assert (PM5 : POSTM C A0 s m1 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4 | exact PMl4]. }
  assert (PXd5 : PIXat m5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_frm C A1 M4 m5 _ pixd datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) _ CK HWs4 Lpixd_a1 Ldatad_a1 NE_pixd_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A1 m4 M4 _ s 128 pixd _ CK HW4 GLO1 Lpixd_a1 PXd4 FRs4) FRM4).
  assert (PXs5 : PIXat m5 pixs (set_rc (hdv w h 4 cm data) 2)) by exact (exT_pix_frm C A1 M4 m5 _ pixs datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) _ CK HWs4 Lpixs_a1 Ldatad_a1 NE_pixs_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A1 m4 M4 _ s 128 pixs _ CK HW4 GLO1 Lpixs_a1 PXs4 FRs4) FRM4).
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, (-128)%Z, (-128 + 128)%Z)]).
  { constructor; [exact (exW_kept_frame E4 M4 m5 (EVar 32) s (-128) 128 datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) FRM4 eq_refl RS WAPdatad (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 175%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_keep _ _ _ _ _ [5%nat; 6%nat; 7%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 21%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] HRa4 (ex_regs_ok_junk vals4 r5 [exW_canary SEGS 415784 m5] 175%nat ltac:(vm_cast_no_check (eq_refl 175%nat))) (exW_agree_keep _ _ _ AGR4)) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) m5 _) by (exact (know_ok_agree SEGS 175%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 175%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q2_4 Q18_4 Q19_4 Q20_4 Q10_4 Q9_4 Q8_4 Q23_4 PM4 HW4 FRs4 AGR4 FRM4 PMl4 CELLh CELLw CELLd PXd4 PXs4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m5 _ (s - 128) (Z.to_nat 128) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 415784 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m5]).
  pose proof (exW_kn_fixed SEGS C A1 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) (EVar 207) (EVar 32) (exW_canary SEGS 415784 m5) s 128 415784 65536 212992 213416 213568 213416 213568
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (exW_kn_clr SEGS C A1 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) 217704 217712 217704 217712 HW5 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A1 M5 (with_vmmaps vm1 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A1 A0 m5 _ E5 log5 (EVar 32) s 128 [] CK HW5 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  pose proof (exW_win_only E5 m5 log5 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs5. change (mem_denot E5 m5 log5) with M5 in FRs5.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  (* [comment removed for export] *)
  pose (BSx5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-128)%Z 8%nat CELLpp.
  clear BSx5.
  assert (PXdM5 : PIXat M5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m5 M5 _ s 128 pixd _ CK HW5 GLO1 Lpixd_a1 PXd5 FRs5).
  assert (PXsM5 : PIXat M5 pixs (set_rc (hdv w h 4 cm data) 2)) by exact (exT_pix_sess C A1 m5 M5 _ s 128 pixs _ CK HW5 GLO1 Lpixs_a1 PXs5 FRs5).
  assert (PPlo : (s + OFF5 <= s + -128)%Z) by (unfold OFF5; lia). assert (PPhi : (s + -128 + 8 <= c_top C)%Z) by lia.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HRC2 fxk C A1 M5 _ Rc5 (s + OFF5)%Z (s + -128)%Z pixs (set_rc (hdv w h 4 cm data) 2) (Z_to_bv 64 ra) S CK HWs5 Q2_5
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF5, PXD2_STACK, ALLOC_STACK; lia) PPlo PPhi ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q1_5 ltac:(red; apply bv_eq; reflexivity) Q10_5 CELLpp
             PXsM5 eq_refl Lpixs_a1 F0pixs) end end.
  intros m6 r6 HW6 CSx5 PMD.
  pose proof CSx5 as CS5. clear CSx5.
  assert (PMB6 : POSTM C A0 s m0 m6).
  { apply (CLONEK A1 M5 m6 _ (s + -128)%Z HWs5 SUB1 ltac:(lia) ltac:(lia) ltac:(lia) (POSTM_trans _ _ _ _ _ _ PM5 PMs5) PMD). }
  assert (PXd6 : PIXat m6 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_patch2 C A1 A1 M5 m6 _ pixd pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) _ CK HWs5 Lpixd_a1 Lpixs_a1 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM5 (proj2 PMD) Lpixd_a1).
  assert (FRMx5 : FRM C (s + -120) (wbytes (wbytes M5 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 (s + -128)) (Z_to_le_bytes 8 0)) m6).
  { replace (s + -120)%Z with (s + -128 + 8)%Z by lia. exact (proj1 PMD). }
  pose proof (POSTM_refl C A0 s m6) as PM6.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, (-120)%Z, 0%Z)]).
  { constructor; [exact (exT_kept_patch2 C A1 _ s (-120) 128 M5 m6 E5 (EVar 32) pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) CK HWs5 Lpixs_a1 RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) FRMx5 Hlo Hhi eq_refl eq_refl eq_refl ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia))|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 208%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 415784 m6] 208%nat ltac:(vm_cast_no_check (eq_refl 208%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) m6 _) by (exact (know_ok_agree SEGS 208%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 208%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q1_5 Q2_5 PM5 HW5 FRs5 CS5 OFF5 CELLpp PXdM5 PXsM5 PPlo PPhi PXd5 PXs5 PMD FRMx5 CLONEK.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m6 _ (s - 128) (Z.to_nat 128) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 415784 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m6]).
  pose proof (exW_kn_fixed SEGS C A1 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) (EVar 240) (EVar 32) (exW_canary SEGS 415784 m6) s 128 415784 65536 212992 213416 213568 213416 213568
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (exW_kn_clr SEGS C A1 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) 217704 217712 217704 217712 HW6 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A1 M6 (with_vmmaps vm1 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A1 A0 m6 _ E6 log6 (EVar 32) s 128 [] CK HW6 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  pose proof (exW_win_only E6 m6 log6 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs6. change (mem_denot E6 m6 log6) with M6 in FRs6.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 4); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BSF HR ex_r10 G10.
  apply (HC A1 M6 vm1 RcF HWs6).
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PMB6 PMs6).
  + exists pixd, datad. split; [exact G10|].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a1 (conj Ldatad_a1 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A1 m6 M6 _ s 128 pixd _ CK HW6 GLO1 Lpixd_a1 PXd6 FRs6).
    * left. split; [reflexivity|]. intros q0 N1 N2. exact (LEQK q0 N1 N2).
  + exact RM1.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma band_ok_8 : forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BAND_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 284096 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 2 -> getr regs 13 = Z_to_bv 64 1 -> getr regs 14 = Z_to_bv 64 1 ->
  PIXat m pixs (hdv w h 8 cm data) -> hdr_ok w h 8 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pixs) = None -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 8 * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pix <= kR)%Z -> (RB_pix14 <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
      (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 0 datad cmap0) ->
      aroom A' vm' (kR - RK_pix) (bR - RB_pix14) ->
      realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 114844) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm data ret S CK HW0 H2 Hs16 HloS Hhi H1 Hret H4 H10 H11 H12 H13 H14 PXs HOK Hw1 Hh1 Lpixs_a0 F0pixs Ldata_a0 kR bR RM0 HkR HbR HC.
  unfold BAND_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 128 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  assert (HTP : ex_keep (getr r0 ex_r4 = Z_to_bv 64 284096)) by exact H4.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 128)%Z) by lia.
  assert (GLO2 : (s - 128 + Z.of_nat (Z.to_nat 128) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (128 <= s)%Z) by lia.
  assert (Rw : (0 <= w < 2 ^ 31)%Z) by (destruct HOK as (_ & X & _); lia). assert (Rh : (0 <= h < 2 ^ 31)%Z) by (destruct HOK as (_ & _ & X & _); lia).
  assert (Rwpl : (1 <= wpl_of w 8 < 2 ^ 31)%Z).
  { destruct HOK as (_ & _ & _ & X). assert (1 <= wpl_of w 8)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  pose proof (hdr_ok_1 w h 8 HOK Hw1 Hh1) as HOK1.
  assert (Rwpl1 : (1 <= wpl_of w 1 < 2 ^ 31)%Z).
  { destruct HOK1 as (_ & _ & _ & X). assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). split; [assumption|]. nia. }
  assert (Rn1 : (0 < 4 * (wpl_of w 1 * h))%Z) by nia.
  assert (Hs8 : (s mod 8 = 0)%Z).
  { apply Z.mod_divide in Hs16; [|lia]. destruct Hs16 as [q0 Eq0]. rewrite Eq0. replace (q0 * 16)%Z with (q0 * 2 * 8)%Z by lia. apply Z_mod_mult. }
  pose proof PXs as (Hps0 & Hps64 & WFs & _). assert (RRpixs : (0 <= pixs < 2 ^ 64)%Z) by lia.
  pose proof (wf_data _ WFs) as RRdata. cbn in RRdata.
  destruct (exW_blk_rng C A0 m0 _ pixs 64 CK HW0 Lpixs_a0 RRpixs eq_refl) as (Gps1 & Gps2 & _).
  assert (BLWpixs : (pixs + 64 <= s - 128)%Z) by lia.
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 8; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 32) (EVar 37) (EVar 38) pixs s 128 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 8; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 35) (EVar 36) (ELit 8) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 128) (Z.to_nat 128) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 8; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 8; exW_canary SEGS 415784 m0]) (EVar 39) (EVar 32) (exW_canary SEGS 415784 m0) s 128 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 8; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 8; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430208 (2 ^ 63); KAlign (EVar 32) 16; KRange (EVar 35) 0 (2 ^ 31 - 1); KRange (EVar 36) 0 (2 ^ 31 - 1); KRange (EVar 38) 0 (2 ^ 31 - 1)]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 8; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 128 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  pose proof (exW_win_only E0 m0 log0 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs0. change (mem_denot E0 m0 log0) with M0 in FRs0.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r1 Q1_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  lazymatch type of Q2_0 with _ = Z_to_bv 64 (s + ?off) => pose (OFF0 := off) end.
  (* [comment removed for export] *)
  assert (PXsM0 : PIXat M0 pixs (hdv w h 8 cm data)) by exact (exT_pix_sess C A0 m0 M0 _ s 128 pixs _ CK HW0 GLO1 Lpixs_a0 PXs FRs0).
  assert (PMB : POSTM C A0 s m0 M0) by exact (POSTM_trans _ _ _ _ _ _ PM0 PMs0).
  lazymatch type of Q1_0 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixClone_W fxk C A0 M0 _ Rc0 (s + OFF0)%Z pixs (hdv w h 8 cm data) (Z_to_bv 64 ra) S CK HWs0 Q2_0
             ltac:(unfold OFF0; lia) ltac:(unfold OFF0; lia) Q1_0 ltac:(red; apply bv_eq; reflexivity) Q10_0 PXsM0 eq_refl Lpixs_a0 F0pixs) end end.
  intros m1 r1 EM1 HW1 CSx0 A10_0.
  pose proof CSx0 as CS0. clear CSx0.
  assert (PMR : POSTM C A0 s (wbytes M0 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 2)) m1) by (rewrite EM1; apply POSTM_refl).
  assert (CLONEK : forall (Ax : AS) (mx my : word -> option byte) (mdx : Model) (pp : Z), W C Ax mx mdx -> sub_live A0 Ax -> (0 <= pp)%Z -> (c_top C - LSTK <= pp)%Z -> (pp + 8 <= s)%Z ->
             POSTM C A0 s m1 mx -> POSTM C Ax (pp + 8) (wbytes (wbytes mx (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 pp) (Z_to_le_bytes 8 0)) my -> POSTM C A0 s m0 my).
  { intros Ax mx my mdx pp HWx SUBx P0 P1 P2 PM23 PM34. eapply POSTM_trans; [exact PMB|].
    exact (exT_postm_clone C A0 A0 Ax M0 m1 mx my _ mdx s pp pixs (hdv w h 8 cm data) CK HWs0 HWx (sub_live_refl A0) SUBx PXsM0 eq_refl Lpixs_a0 P0 P1 P2 Hhi PMR PM23 PM34). }
  assert (PXs1 : PIXat m1 pixs (set_rc (hdv w h 8 cm data) 2)).
  { rewrite EM1, <- (w2b_Z 4 2) by lia. exact (PIX_wr_rc M0 pixs _ 2 PXsM0 ltac:(lia)). }
  pose proof (exT_wbytes_out M0 m1 (pixs + 20) (Z_to_le_bytes 4 2) EM1 ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia)) as OUT0.
  rewrite length_Z_to_le_bytes in OUT0. change (Z.of_nat 4) with 4%Z in OUT0.
  pose proof (POSTM_refl C A0 s m1) as PM1.
  assert (KEPT0 : Forall (ex_region_kept E0 M0 m1) [(EVar 32, OFF0, 0%Z)]).
  { constructor; [apply (exW_kept_out E0 M0 m1 (EVar 32) s OFF0 0 (pixs + 20) (pixs + 20 + 4) OUT0 eq_refl RS); right; unfold OFF0; lia|]. constructor. }
  pose proof (ex_know_keepD SEGS E0 M0 m1 _ [] _ HKc0 KEPT0) as HKk0.
  match type of HKk0 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E0 m1 kk') in HKk0 end.
  pose proof (regs_ok_agree 40%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa0.
  pose proof (exW_regs_call _ _ _ _ _ HRa0 (ex_regs_ok_junk vals0 r1 [exW_canary SEGS 415784 m1] 40%nat ltac:(vm_cast_no_check (eq_refl 40%nat))) CS0) as HRn1.
  clear HRa0.
  assert (HKa1 : know_ok SEGS (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) m1 _) by (exact (know_ok_agree SEGS 40%nat E0 _ m1 _ (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk0)).
  rewrite (fr_denot_agree 40%nat E0 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) _ fr (vals_app_agree vals0 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r1 ex_r10 (EVar 34) HRn1 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_0)) as HRx1. clear HRn1. rename HRx1 into HRn1.
  clear HR HK Hlf Hms HKc0 HKk0 KEPT0 HC0 HWs0 PMs0 Q10_0 Q1_0 Q2_0 PM0 HW0 FRs0 CS0 OFF0 A10_0 PXsM0 PMB PMR EM1 OUT0.
  subst M0. clear log0. clear E0. try clear Rc0. clear KN0.
  lazymatch type of HRn1 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn1 end.
  pose proof (exT_kn_whd SEGS m1 (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 34) (EVar 35) (EVar 36) (ELit 8) pixs _ PXs1 eq_refl eq_refl eq_refl eq_refl) as HKd1.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m1 _ (s - 128) (Z.to_nat 128) CK HW1 GLO1 GLO2) as SOK1.
  pose proof (exW_canary_ok SEGS 415784 m1 (canary_any m1)) as CANOK1.
  pose (vals1 := vals0 ++ map (getr r1) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m1]).
  pose proof (exW_kn_fixed SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) (EVar 72) (EVar 32) (exW_canary SEGS 415784 m1) s 128 415784 65536 212992 213416 213568 213416 213568
                HW1 eq_refl (proj1 CANOK1) (proj2 CANOK1) eq_refl eq_refl eq_refl SOK1 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf1.
  pose proof (exW_kn_clr SEGS C A0 m1 _ (ex_envL vals0 r1 [exW_canary SEGS 415784 m1]) 217704 217712 217704 217712 HW1 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_1.
  pose proof (proj2 (Forall_app _ _ _) (conj HKd1 (proj2 (Forall_app _ _ _) (conj HKx0_1 (proj2 (Forall_app _ _ _) (conj HKf1 HKa1)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn1 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN1 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKd1 HKx0_1 HKf1 HKa1 SOK1 CANOK1.
  repeat match goal with H : getr r1 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc1 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E1 := EEx) in HR, Hlf, HK, Hms |- *; set (log1 := LLx) in Hms, Hlf; set (M1 := mem_denot E1 m1 log1) in Hms end.
  assert (WP1 : W C A0 M1 (with_vmmaps vm0 md) /\ POSTM C A0 s m1 M1).
  { subst M1. apply (exW_win_blks C A0 A0 m1 _ E1 log1 (EVar 32) s 128 [] CK HW1 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP1 as [HWs1 PMs1].
  pose proof (exW_win_only E1 m1 log1 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs1. change (mem_denot E1 m1 log1) with M1 in FRs1.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log1 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC1 : carry log1 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc1 : know_ok SEGS E1 M1 kn1) by (apply (carry_after SEGS E1 m1 log1 kn0 [] kn1 scs hs HC1 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact Hms |].
  pose (BS1 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8)]).
  exW_regfactB BS1 HR ex_r10 Q10_1. exW_regfactB BS1 HR ex_r11 Q11_1. exW_regfactB BS1 HR ex_r12 Q12_1. exW_regfactB BS1 HR ex_r1 Q1_1. exW_regfactB BS1 HR ex_r2 Q2_1. exW_regfactB BS1 HR ex_r4 Q4_1.
  clear BS1.
  lazymatch type of Q2_1 with _ = Z_to_bv 64 (s + ?off) => pose (OFF1 := off) end.
  (* [comment removed for export] *)
  rewrite PC_PIXCREATE_eq.
  lazymatch type of Q1_1 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCreate_sure_W (fx := fxk) C A0 M1 _ Rc1 (s + OFF1) w h 1 (Z_to_bv 64 ra) S CK HWs1 Q2_1
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF1, LSF; lia) ltac:(unfold OFF1; lia) Q1_1 ltac:(red; apply bv_eq; reflexivity) Q4_1 Q10_1 Q11_1 Q12_1 Hw1 Hh1 HOK1 kR bR
             ltac:(rewrite with_vmmaps_vmmaps; exact RM0) HkR HbR) end end.
  intros A1 m2 vm1 r2 pixd datad HW2 CSx1 PMc1 A10_1 PXN RM1.
  pose proof CSx1 as CS1. clear CSx1.
  rewrite with_vmmaps_twice in HW2 |- *.
  destruct PXN as (Gpd1 & Gpd2 & ALpixd & Gdd1 & Gdd2 & ALdatad & NEpd & Fpixd & Fdatad & F0pixd & F0datad & Lpixd_a1 & Ldatad_a1 & LEQ1 & PXd2 & _).
  change (p_wpl (set_data (pix_hdr w h 1) datad)) with (wpl_of w 1) in Gdd2, Ldatad_a1. change (p_h (set_data (pix_hdr w h 1) datad)) with h in Gdd2, Ldatad_a1.
  assert (RRpixd : (0 <= pixd < 2 ^ 64)%Z) by lia. assert (RRdatad : (0 <= datad < 2 ^ 64)%Z) by lia.
  assert (SUB1 : sub_live A0 A1).
  { intros q0 kq Lq. rewrite (LEQ1 q0 (ne_live A0 q0 _ kq Lq Fpixd) (ne_live A0 q0 _ kq Lq Fdatad)). exact Lq. }
  pose proof LEQ1 as LEQK.
  pose proof (SUB1 _ _ Lpixs_a0) as Lpixs_a1. pose proof (SUB1 _ _ Ldata_a0) as Ldata_a1.
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fpixd) as NE_pixs_pixd.
  assert (NE_pixd_pixs : Z_to_bv 64 pixd <> Z_to_bv 64 pixs) by (intros EE; exact (NE_pixs_pixd (eq_sym EE))).
  assert (NE_pixd_datad : Z_to_bv 64 pixd <> Z_to_bv 64 datad) by (intros EE; apply NEpd; apply (f_equal bv_unsigned) in EE; rewrite !u_Z2bv in EE by lia; exact EE).
  pose proof (ne_live A0 _ _ _ Lpixs_a0 Fdatad) as NE_pixs_datad.
  assert (NE_datad_data : Z_to_bv 64 datad <> Z_to_bv 64 data) by (intros EE; exact (ne_live A0 _ _ _ Ldata_a0 Fdatad (eq_sym EE))).
  pose proof (exW_win_blk_apart_h C A1 m2 _ s 128 datad (4 * (wpl_of w 1 * h)) CK HW2 Ldatad_a1 Rn1 RRdatad GLO1) as WAPdatad.
  assert (PM2 : POSTM C A0 s m1 m2).
  { eapply POSTM_trans; [exact PM1|]. eapply POSTM_trans; [exact PMs1|]. apply (POSTM_mono C A0 (s + OFF1) s); [unfold OFF1; lia | exact PMc1]. }
  pose proof (exT_pix_livk A0 _ m2 pixs _ (exT_pix_sess C A0 m1 M1 _ s 128 pixs _ CK HW1 GLO1 Lpixs_a0 PXs1 FRs1) (proj2 PMc1) Lpixs_a0) as PXs2.
  assert (KEPT1 : Forall (ex_region_kept E1 M1 m2) [(EVar 32, OFF1, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF1 128 M1 m2 E1 (EVar 32) CK (proj1 PMc1) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E1 M1 m2 _ [] _ HKc1 KEPT1) as HKk1.
  match type of HKk1 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E1 m2 kk') in HKk1 end.
  pose proof (regs_ok_agree 73%nat E1 (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) _ _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa1.
  pose proof (exW_regs_call _ _ _ _ _ HRa1 (ex_regs_ok_junk vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2] 73%nat ltac:(vm_cast_no_check (eq_refl 73%nat))) CS1) as HRn2.
  clear HRa1.
  assert (HKa2 : know_ok SEGS (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) m2 _) by (exact (know_ok_agree SEGS 73%nat E1 _ m2 _ (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk1)).
  rewrite (fr_denot_agree 73%nat E1 (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) _ fr (vals_app_agree vals1 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  pose proof (ex_regs_ok_reexpr _ _ r2 ex_r10 (EVar 105) HRn2 ltac:(apply ex_reg_ne0; vm_compute; discriminate) ltac:(exact A10_1)) as HRx2. clear HRn2. rename HRx2 into HRn2.
  clear HR HK Hlf Hms HKc1 HKk1 KEPT1 HC1 HWs1 PMs1 Q10_1 Q11_1 Q12_1 Q1_1 Q2_1 Q4_1 PM1 HW1 FRs1 PMc1 CS1 OFF1 LEQ1 RM0 A10_1 PXs1.
  subst M1. clear log1. clear E1. try clear Rc1. clear KN1.
  lazymatch type of HRn2 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn2 end.
  pose proof (exT_kn_pix SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) (EVar 105) (EVar 32) (EVar 106) (EVar 107) pixd s 128 _ CK HW2 Lpixd_a1 PXd2 eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp2.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m2 _ (s - 128) (Z.to_nat 128) CK HW2 GLO1 GLO2) as SOK2.
  pose proof (exW_canary_ok SEGS 415784 m2 (canary_any m2)) as CANOK2.
  pose (vals2 := vals1 ++ map (getr r2) ex_regs_list ++ map (Z_to_bv 64) [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]).
  pose proof (exW_kn_fixed SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) (EVar 108) (EVar 32) (exW_canary SEGS 415784 m2) s 128 415784 65536 212992 213416 213568 213416 213568
                HW2 eq_refl (proj1 CANOK2) (proj2 CANOK2) eq_refl eq_refl eq_refl SOK2 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf2.
  pose proof (exW_kn_clr SEGS C A1 m2 _ (ex_envL vals1 r2 [pixd; datad; wpl_of w 1; exW_canary SEGS 415784 m2]) 217704 217712 217704 217712 HW2 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_2.
  pose proof (proj2 (Forall_app _ _ _) (conj HKp2 (proj2 (Forall_app _ _ _) (conj HKx0_2 (proj2 (Forall_app _ _ _) (conj HKf2 HKa2)))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn2 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN2 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKp2 HKx0_2 HKf2 HKa2 SOK2 CANOK2.
  repeat match goal with H : getr r2 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc2 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E2 := EEx) in HR, Hlf, HK, Hms |- *; set (log2 := LLx) in Hms, Hlf; set (M2 := mem_denot E2 m2 log2) in Hms end.
  assert (WP2 : W C A1 M2 (with_vmmaps vm1 md) /\ POSTM C A0 s m2 M2).
  { subst M2. apply (exW_win_blks C A1 A0 m2 _ E2 log2 (EVar 32) s 128 [] CK HW2 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP2 as [HWs2 PMs2].
  pose proof (exW_win_only E2 m2 log2 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs2. change (mem_denot E2 m2 log2) with M2 in FRs2.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log2 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC2 : carry log2 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc2 : know_ok SEGS E2 M2 kn1) by (apply (carry_after SEGS E2 m2 log2 kn0 [] kn1 scs hs HC2 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact Hms |].
  pose (BS2 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS2 HR ex_r10 Q10_2. exW_regfactB BS2 HR ex_r11 Q11_2. exW_regfactB BS2 HR ex_r1 Q1_2. exW_regfactB BS2 HR ex_r2 Q2_2.
  clear BS2.
  lazymatch type of Q2_2 with _ = Z_to_bv 64 (s + ?off) => pose (OFF2 := off) end.
  (* [comment removed for export] *)
  assert (PXsM2 : PIXat M2 pixs (set_rc (hdv w h 8 cm data) 2)) by exact (exT_pix_sess C A1 m2 M2 _ s 128 pixs _ CK HW2 GLO1 Lpixs_a1 PXs2 FRs2).
  assert (PXdM2 : PIXat M2 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m2 M2 _ s 128 pixd _ CK HW2 GLO1 Lpixd_a1 PXd2 FRs2).
  lazymatch type of Q1_2 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyRes0_W fxk C A0 A1 M2 _ Rc2 (s + OFF2) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs2 SUB1 Q2_2
             ltac:(unfold OFF2; lia) ltac:(unfold OFF2; lia) Q1_2 ltac:(red; apply bv_eq; reflexivity) Q10_2 Q11_2 PXsM2 PXdM2 eq_refl eq_refl eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m3 r3 HW3 CSx2 PMc2 PXd3 A10_2.
  pose proof CSx2 as CS2. clear CSx2.
  assert (PM3 : POSTM C A0 s m1 m3).
  { eapply POSTM_trans; [exact PM2|]. eapply POSTM_trans; [exact PMs2|]. apply (POSTM_mono C A0 (s + OFF2) s); [unfold OFF2; lia | exact PMc2]. }
  pose proof (exT_pix_livk A0 M2 m3 pixs _ PXsM2 (proj2 PMc2) Lpixs_a0) as PXs3.
  assert (KEPT2 : Forall (ex_region_kept E2 M2 m3) [(EVar 32, OFF2, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF2 128 M2 m3 E2 (EVar 32) CK (proj1 PMc2) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
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
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m3 _ (s - 128) (Z.to_nat 128) CK HW3 GLO1 GLO2) as SOK3.
  pose proof (exW_canary_ok SEGS 415784 m3 (canary_any m3)) as CANOK3.
  pose (vals3 := vals2 ++ map (getr r3) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m3]).
  pose proof (exW_kn_fixed SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) (EVar 141) (EVar 32) (exW_canary SEGS 415784 m3) s 128 415784 65536 212992 213416 213568 213416 213568
                HW3 eq_refl (proj1 CANOK3) (proj2 CANOK3) eq_refl eq_refl eq_refl SOK3 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf3.
  pose proof (exW_kn_clr SEGS C A1 m3 _ (ex_envL vals2 r3 [exW_canary SEGS 415784 m3]) 217704 217712 217704 217712 HW3 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_3.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_3 (proj2 (Forall_app _ _ _) (conj HKf3 HKa3)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn3 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN3 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_3 HKf3 HKa3 SOK3 CANOK3.
  repeat match goal with H : getr r3 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc3 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E3 := EEx) in HR, Hlf, HK, Hms |- *; set (log3 := LLx) in Hms, Hlf; set (M3 := mem_denot E3 m3 log3) in Hms end.
  assert (WP3 : W C A1 M3 (with_vmmaps vm1 md) /\ POSTM C A0 s m3 M3).
  { subst M3. apply (exW_win_blks C A1 A0 m3 _ E3 log3 (EVar 32) s 128 [] CK HW3 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP3 as [HWs3 PMs3].
  pose proof (exW_win_only E3 m3 log3 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs3. change (mem_denot E3 m3 log3) with M3 in FRs3.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log3 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC3 : carry log3 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc3 : know_ok SEGS E3 M3 kn1) by (apply (carry_after SEGS E3 m3 log3 kn0 [] kn1 scs hs HC3 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW3)) | exact (mp_lazy _ (w_pure _ _ _ _ HW3)) | exact Hms |].
  pose (BS3 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS3 HR ex_r10 Q10_3. exW_regfactB BS3 HR ex_r11 Q11_3. exW_regfactB BS3 HR ex_r1 Q1_3. exW_regfactB BS3 HR ex_r2 Q2_3.
  clear BS3.
  lazymatch type of Q2_3 with _ = Z_to_bv 64 (s + ?off) => pose (OFF3 := off) end.
  (* [comment removed for export] *)
  assert (PXsM3 : PIXat M3 pixs (set_rc (hdv w h 8 cm data) 2)) by exact (exT_pix_sess C A1 m3 M3 _ s 128 pixs _ CK HW3 GLO1 Lpixs_a1 PXs3 FRs3).
  assert (PXdM3 : PIXat M3 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m3 M3 _ s 128 pixd _ CK HW3 GLO1 Lpixd_a1 PXd3 FRs3).
  lazymatch type of Q1_3 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (pixCopyFmt0_W fxk C A0 A1 M3 _ Rc3 (s + OFF3) pixd pixs _ _ (Z_to_bv 64 ra) S CK HWs3 SUB1 Q2_3
             ltac:(unfold OFF3; lia) ltac:(unfold OFF3; lia) Q1_3 ltac:(red; apply bv_eq; reflexivity) Q10_3 Q11_3 PXsM3 PXdM3 eq_refl eq_refl 
             Lpixs_a1 Lpixd_a1 Fpixd F0pixd NE_pixs_pixd) end end.
  intros m4 r4 HW4 CSx3 PMc3 PXd4 A10_3.
  pose proof CSx3 as CS3. clear CSx3.
  assert (PM4 : POSTM C A0 s m1 m4).
  { eapply POSTM_trans; [exact PM3|]. eapply POSTM_trans; [exact PMs3|]. apply (POSTM_mono C A0 (s + OFF3) s); [unfold OFF3; lia | exact PMc3]. }
  pose proof (exT_pix_livk A0 M3 m4 pixs _ PXsM3 (proj2 PMc3) Lpixs_a0) as PXs4.
  assert (KEPT3 : Forall (ex_region_kept E3 M3 m4) [(EVar 32, OFF3, 0%Z)]).
  { constructor; [exact (exW_kept_stack2 C s OFF3 128 M3 m4 E3 (EVar 32) CK (proj1 PMc3) Hlo Hhi eq_refl eq_refl eq_refl)|]. constructor. }
  pose proof (ex_know_keepD SEGS E3 M3 m4 _ [] _ HKc3 KEPT3) as HKk3.
  match type of HKk3 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E3 m4 kk') in HKk3 end.
  pose proof (regs_ok_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa3.
  pose proof (exW_regs_call _ _ _ _ _ HRa3 (ex_regs_ok_junk vals3 r4 [exW_canary SEGS 415784 m4] 142%nat ltac:(vm_cast_no_check (eq_refl 142%nat))) CS3) as HRn4.
  clear HRa3.
  assert (HKa4 : know_ok SEGS (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) m4 _) by (exact (know_ok_agree SEGS 142%nat E3 _ m4 _ (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk3)).
  rewrite (fr_denot_agree 142%nat E3 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) _ fr (vals_app_agree vals3 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc3 HKk3 KEPT3 HC3 HWs3 PMs3 Q10_3 Q11_3 Q1_3 Q2_3 PM3 HW3 FRs3 PMc3 CS3 OFF3 A10_3 PXsM3 PXdM3 PXd3 PXs3.
  subst M3. clear log3. clear E3. try clear Rc3. clear KN3.
  lazymatch type of HRn4 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn4 end.
  pose proof (exT_kn_cells SEGS m4 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 34) (EVar 37) (EVar 38) pixs _ PXs4 eq_refl eq_refl eq_refl) as HKg4.
  pose proof (exT_kn_cells SEGS m4 (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 105) (EVar 106) (EVar 107) pixd _ PXd4 eq_refl eq_refl eq_refl) as HKh4.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m4 _ (s - 128) (Z.to_nat 128) CK HW4 GLO1 GLO2) as SOK4.
  pose proof (exW_canary_ok SEGS 415784 m4 (canary_any m4)) as CANOK4.
  pose (vals4 := vals3 ++ map (getr r4) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m4]).
  pose proof (exW_kn_fixed SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) (EVar 174) (EVar 32) (exW_canary SEGS 415784 m4) s 128 415784 65536 212992 213416 213568 213416 213568
                HW4 eq_refl (proj1 CANOK4) (proj2 CANOK4) eq_refl eq_refl eq_refl SOK4 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf4.
  pose proof (exW_kn_clr SEGS C A1 m4 _ (ex_envL vals3 r4 [exW_canary SEGS 415784 m4]) 217704 217712 217704 217712 HW4 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_4.
  pose proof (proj2 (Forall_app _ _ _) (conj HKg4 (proj2 (Forall_app _ _ _) (conj HKh4 (proj2 (Forall_app _ _ _) (conj HKx0_4 (proj2 (Forall_app _ _ _) (conj HKf4 HKa4)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn4 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN4 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKg4 HKh4 HKx0_4 HKf4 HKa4 SOK4 CANOK4.
  repeat match goal with H : getr r4 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc4 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E4 := EEx) in HR, Hlf, HK, Hms |- *; set (log4 := LLx) in Hms, Hlf; set (M4 := mem_denot E4 m4 log4) in Hms end.
  assert (WP4 : W C A1 M4 (with_vmmaps vm1 md) /\ POSTM C A0 s m4 M4).
  { subst M4. apply (exW_win_blks C A1 A0 m4 _ E4 log4 (EVar 32) s 128 [] CK HW4 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP4 as [HWs4 PMs4].
  pose proof (exW_win_only E4 m4 log4 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs4. change (mem_denot E4 m4 log4) with M4 in FRs4.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log4 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC4 : carry log4 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc4 : know_ok SEGS E4 M4 kn1) by (apply (carry_after SEGS E4 m4 log4 kn0 [] kn1 scs hs HC4 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact Hms |].
  pose (BS4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS4 HR ex_r2 Q2_4. exW_regfactB BS4 HR ex_r18 Q18_4. exW_regfactB BS4 HR ex_r19 Q19_4. exW_regfactB BS4 HR ex_r20 Q20_4. exW_regfactB BS4 HR ex_r10 Q10_4. exW_regfactB BS4 HR ex_r9 Q9_4. exW_regfactB BS4 HR ex_r8 Q8_4. exW_regfactB BS4 HR ex_r23 Q23_4.
  clear BS4.
  (* [comment removed for export] *)
  pose (BSx4 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-112)%Z 4%nat CELLh. exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-108)%Z 4%nat CELLw.
  exW_cellB HK Hlf r0 BSx4 (EVar 32) s (-116)%Z 4%nat CELLd.
  clear BSx4.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HLOOP fxk C A1 A0 M4 _ Rc4 s w h 8%Z datad data S CK HWs4 SUB1 Hlo Hhi HOK Hw1 Hh1 ltac:(lia) Ldatad_a1 Fdatad F0datad Ldata_a1 NE_datad_data RRdatad RRdata
             Q2_4 Q18_4 Q19_4 Q20_4 Q10_4 Q9_4 Q8_4 Q23_4 CELLh CELLw CELLd) end.
  intros r5 m5 HW5 PMl4 AGR4 FRM4.
  assert (PM5 : POSTM C A0 s m1 m5).
  { eapply POSTM_trans; [exact PM4|]. eapply POSTM_trans; [exact PMs4 | exact PMl4]. }
  assert (PXd5 : PIXat m5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_frm C A1 M4 m5 _ pixd datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) _ CK HWs4 Lpixd_a1 Ldatad_a1 NE_pixd_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A1 m4 M4 _ s 128 pixd _ CK HW4 GLO1 Lpixd_a1 PXd4 FRs4) FRM4).
  assert (PXs5 : PIXat m5 pixs (set_rc (hdv w h 8 cm data) 2)) by exact (exT_pix_frm C A1 M4 m5 _ pixs datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) _ CK HWs4 Lpixs_a1 Ldatad_a1 NE_pixs_datad RRdatad (Z.lt_le_incl _ _ Rn1) (Z.le_refl _) (Z.le_refl _) (exT_pix_sess C A1 m4 M4 _ s 128 pixs _ CK HW4 GLO1 Lpixs_a1 PXs4 FRs4) FRM4).
  assert (KEPT4 : Forall (ex_region_kept E4 M4 m5) [(EVar 32, (-128)%Z, (-128 + 128)%Z)]).
  { constructor; [exact (exW_kept_frame E4 M4 m5 (EVar 32) s (-128) 128 datad (4 * (wpl_of w 1 * h)) datad (datad + 4 * (wpl_of w 1 * h)) FRM4 eq_refl RS WAPdatad (Z.le_refl _) (Z.le_refl _))|]. constructor. }
  pose proof (ex_know_keepD SEGS E4 M4 m5 _ [] _ HKc4 KEPT4) as HKk4.
  match type of HKk4 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E4 m5 kk') in HKk4 end.
  pose proof (regs_ok_agree 175%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) _ _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa4.
  pose proof (exW_regs_keep _ _ _ _ _ [5%nat; 6%nat; 7%nat; 11%nat; 12%nat; 13%nat; 14%nat; 15%nat; 16%nat; 17%nat; 21%nat; 23%nat; 24%nat; 25%nat; 26%nat; 27%nat; 28%nat; 29%nat; 30%nat; 31%nat] HRa4 (ex_regs_ok_junk vals4 r5 [exW_canary SEGS 415784 m5] 175%nat ltac:(vm_cast_no_check (eq_refl 175%nat))) (exW_agree_keep _ _ _ AGR4)) as HRn5.
  clear HRa4.
  assert (HKa5 : know_ok SEGS (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) m5 _) by (exact (know_ok_agree SEGS 175%nat E4 _ m5 _ (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk4)).
  rewrite (fr_denot_agree 175%nat E4 (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) _ fr (vals_app_agree vals4 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc4 HKk4 KEPT4 HC4 HWs4 PMs4 Q2_4 Q18_4 Q19_4 Q20_4 Q10_4 Q9_4 Q8_4 Q23_4 PM4 HW4 FRs4 AGR4 FRM4 PMl4 CELLh CELLw CELLd PXd4 PXs4.
  subst M4. clear log4. clear E4. try clear Rc4. clear KN4.
  lazymatch type of HRn5 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn5 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m5 _ (s - 128) (Z.to_nat 128) CK HW5 GLO1 GLO2) as SOK5.
  pose proof (exW_canary_ok SEGS 415784 m5 (canary_any m5)) as CANOK5.
  pose (vals5 := vals4 ++ map (getr r5) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m5]).
  pose proof (exW_kn_fixed SEGS C A1 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) (EVar 207) (EVar 32) (exW_canary SEGS 415784 m5) s 128 415784 65536 212992 213416 213568 213416 213568
                HW5 eq_refl (proj1 CANOK5) (proj2 CANOK5) eq_refl eq_refl eq_refl SOK5 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf5.
  pose proof (exW_kn_clr SEGS C A1 m5 _ (ex_envL vals4 r5 [exW_canary SEGS 415784 m5]) 217704 217712 217704 217712 HW5 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_5.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_5 (proj2 (Forall_app _ _ _) (conj HKf5 HKa5)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn5 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN5 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_5 HKf5 HKa5 SOK5 CANOK5.
  repeat match goal with H : getr r5 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc5 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E5 := EEx) in HR, Hlf, HK, Hms |- *; set (log5 := LLx) in Hms, Hlf; set (M5 := mem_denot E5 m5 log5) in Hms end.
  assert (WP5 : W C A1 M5 (with_vmmaps vm1 md) /\ POSTM C A0 s m5 M5).
  { subst M5. apply (exW_win_blks C A1 A0 m5 _ E5 log5 (EVar 32) s 128 [] CK HW5 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP5 as [HWs5 PMs5].
  pose proof (exW_win_only E5 m5 log5 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs5. change (mem_denot E5 m5 log5) with M5 in FRs5.
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log5 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC5 : carry log5 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc5 : know_ok SEGS E5 M5 kn1) by (apply (carry_after SEGS E5 m5 log5 kn0 [] kn1 scs hs HC5 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact Hms |].
  pose (BS5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BS5 HR ex_r10 Q10_5. exW_regfactB BS5 HR ex_r1 Q1_5. exW_regfactB BS5 HR ex_r2 Q2_5.
  clear BS5.
  lazymatch type of Q2_5 with _ = Z_to_bv 64 (s + ?off) => pose (OFF5 := off) end.
  (* [comment removed for export] *)
  pose (BSx5 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_cellB HK Hlf r0 BSx5 (EVar 32) s (-128)%Z 8%nat CELLpp.
  clear BSx5.
  assert (PXdM5 : PIXat M5 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_sess C A1 m5 M5 _ s 128 pixd _ CK HW5 GLO1 Lpixd_a1 PXd5 FRs5).
  assert (PXsM5 : PIXat M5 pixs (set_rc (hdv w h 8 cm data) 2)) by exact (exT_pix_sess C A1 m5 M5 _ s 128 pixs _ CK HW5 GLO1 Lpixs_a1 PXs5 FRs5).
  assert (PPlo : (s + OFF5 <= s + -128)%Z) by (unfold OFF5; lia). assert (PPhi : (s + -128 + 8 <= c_top C)%Z) by lia.
  lazymatch type of Q1_5 with _ = Z_to_bv 64 ?ra => lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (HRC2 fxk C A1 M5 _ Rc5 (s + OFF5)%Z (s + -128)%Z pixs (set_rc (hdv w h 8 cm data) 2) (Z_to_bv 64 ra) S CK HWs5 Q2_5
             ltac:(rewrite <- Zplus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold OFF5, PXD2_STACK, ALLOC_STACK; lia) PPlo PPhi ltac:(rewrite <- Zplus_mod_idemp_l, Hs8; reflexivity) Q1_5 ltac:(red; apply bv_eq; reflexivity) Q10_5 CELLpp
             PXsM5 eq_refl Lpixs_a1 F0pixs) end end.
  intros m6 r6 HW6 CSx5 PMD.
  pose proof CSx5 as CS5. clear CSx5.
  assert (PMB6 : POSTM C A0 s m0 m6).
  { apply (CLONEK A1 M5 m6 _ (s + -128)%Z HWs5 SUB1 ltac:(lia) ltac:(lia) ltac:(lia) (POSTM_trans _ _ _ _ _ _ PM5 PMs5) PMD). }
  assert (PXd6 : PIXat m6 pixd (set_data (pix_hdr w h 1) datad)) by exact (exT_pix_patch2 C A1 A1 M5 m6 _ pixd pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) _ CK HWs5 Lpixd_a1 Lpixs_a1 NE_pixd_pixs RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) PXdM5 (proj2 PMD) Lpixd_a1).
  assert (FRMx5 : FRM C (s + -120) (wbytes (wbytes M5 (Z_to_bv 64 (pixs + 20)) (Z_to_le_bytes 4 1)) (Z_to_bv 64 (s + -128)) (Z_to_le_bytes 8 0)) m6).
  { replace (s + -120)%Z with (s + -128 + 8)%Z by lia. exact (proj1 PMD). }
  pose proof (POSTM_refl C A0 s m6) as PM6.
  assert (KEPT5 : Forall (ex_region_kept E5 M5 m6) [(EVar 32, (-120)%Z, 0%Z)]).
  { constructor; [exact (exT_kept_patch2 C A1 _ s (-120) 128 M5 m6 E5 (EVar 32) pixs 64 (pixs + 20) (s + -128) (Z_to_le_bytes 4 1) (Z_to_le_bytes 8 0) CK HWs5 Lpixs_a1 RRpixs ltac:(lia) ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia) FRMx5 Hlo Hhi eq_refl eq_refl eq_refl ltac:(lia) ltac:(rewrite length_Z_to_le_bytes; lia))|]. constructor. }
  pose proof (ex_know_keepD SEGS E5 M5 m6 _ [] _ HKc5 KEPT5) as HKk5.
  match type of HKk5 with know_ok _ _ _ ?kk => let kk' := eval vm_compute in kk in change (know_ok SEGS E5 m6 kk') in HKk5 end.
  pose proof (regs_ok_agree 208%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HR) as HRa5.
  pose proof (exW_regs_call _ _ _ _ _ HRa5 (ex_regs_ok_junk vals5 r6 [exW_canary SEGS 415784 m6] 208%nat ltac:(vm_cast_no_check (eq_refl 208%nat))) CS5) as HRn6.
  clear HRa5.
  assert (HKa6 : know_ok SEGS (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) m6 _) by (exact (know_ok_agree SEGS 208%nat E5 _ m6 _ (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true)) HKk5)).
  rewrite (fr_denot_agree 208%nat E5 (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) _ fr (vals_app_agree vals5 _ _) ltac:(vm_cast_no_check (eq_refl true))).
  clear HR HK Hlf Hms HKc5 HKk5 KEPT5 HC5 HWs5 PMs5 Q10_5 Q1_5 Q2_5 PM5 HW5 FRs5 CS5 OFF5 CELLpp PXdM5 PXsM5 PPlo PPhi PXd5 PXs5 PMD FRMx5 CLONEK.
  subst M5. clear log5. clear E5. try clear Rc5. clear KN5.
  lazymatch type of HRn6 with regs_ok ?EE ?sr ?RR => let sr' := eval vm_compute in sr in change (regs_ok EE sr' RR) in HRn6 end.
  (* [comment removed for export] *)
  pose proof (W_sok_win C A1 m6 _ (s - 128) (Z.to_nat 128) CK HW6 GLO1 GLO2) as SOK6.
  pose proof (exW_canary_ok SEGS 415784 m6 (canary_any m6)) as CANOK6.
  pose (vals6 := vals5 ++ map (getr r6) ex_regs_list ++ map (Z_to_bv 64) [exW_canary SEGS 415784 m6]).
  pose proof (exW_kn_fixed SEGS C A1 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) (EVar 240) (EVar 32) (exW_canary SEGS 415784 m6) s 128 415784 65536 212992 213416 213568 213416 213568
                HW6 eq_refl (proj1 CANOK6) (proj2 CANOK6) eq_refl eq_refl eq_refl SOK6 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf6.
  pose proof (exW_kn_clr SEGS C A1 m6 _ (ex_envL vals5 r6 [exW_canary SEGS 415784 m6]) 217704 217712 217704 217712 HW6 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_6.
  pose proof (proj2 (Forall_app _ _ _) (conj HKx0_6 (proj2 (Forall_app _ _ _) (conj HKf6 HKa6)))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  rename HRn6 into HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN6 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKx0_6 HKf6 HKa6 SOK6 CANOK6.
  repeat match goal with H : getr r6 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_ret ST ret HRA Hret RcF HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E6 := EEx) in HR, Hlf, HK, Hms |- *; set (log6 := LLx) in Hms, Hlf; set (M6 := mem_denot E6 m6 log6) in Hms end.
  assert (WP6 : W C A1 M6 (with_vmmaps vm1 md) /\ POSTM C A0 s m6 M6).
  { subst M6. apply (exW_win_blks C A1 A0 m6 _ E6 log6 (EVar 32) s 128 [] CK HW6 SUB1 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP6 as [HWs6 PMs6].
  pose proof (exW_win_only E6 m6 log6 (EVar 32) s 128 Hlf ltac:(vm_cast_no_check (eq_refl true)) eq_refl RS) as FRs6. change (mem_denot E6 m6 log6) with M6 in FRs6.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW6)) | exact (mp_lazy _ (w_pure _ _ _ _ HW6)) | exact Hms |].
  pose (BSF := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs); (37%nat, data); (38%nat, wpl_of w 8); (105%nat, pixd); (106%nat, datad); (107%nat, wpl_of w 1)]).
  exW_regfactB BSF HR ex_r10 G10.
  apply (HC A1 M6 vm1 RcF HWs6).
  + lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 RcF [(2%nat, EVar 32); (4%nat, ELit 284096)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor; [symmetry; exact HTP | constructor]] | vm_compute; reflexivity] end.
  + exact (POSTM_trans _ _ _ _ _ _ PMB6 PMs6).
  + exists pixd, datad. split; [exact G10|].
    refine (conj Gpd1 (conj Gpd2 (conj ALpixd (conj Gdd1 (conj Gdd2 (conj ALdatad (conj NEpd (conj Fpixd (conj Fdatad (conj F0pixd (conj F0datad (conj Lpixd_a1 (conj Ldatad_a1 (conj _ _)))))))))))))).
    * exact (exT_pix_sess C A1 m6 M6 _ s 128 pixd _ CK HW6 GLO1 Lpixd_a1 PXd6 FRs6).
    * left. split; [reflexivity|]. intros q0 N1 N2. exact (LEQK q0 N1 N2).
  + exact RM1.
Qed.

End Band.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition STOPS_E : list Z := [87484]%Z.
Definition PC_RETERR : word := 87484%bv.
Lemma PC_RETERR_eq : Z_to_bv 64 87484 = PC_RETERR. Proof. apply bv_eq; reflexivity. Qed.
Lemma str_band_msg_d : str16 68159 17. Proof. str16_tac. Qed.
Lemma str_band_proc : str16 66596 21. Proof. str16_tac. Qed.

Lemma band_d_1 : forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BAND_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h 1 cm data) -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 114844) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm data ret S CK HW0 H2 Hs16 HloS Hhi H1 Hret H10 PXs Lpixs_a0 HC.
  unfold BAND_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 128 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 128)%Z) by lia.
  assert (GLO2 : (s - 128 + Z.of_nat (Z.to_nat 128) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (128 <= s)%Z) by lia.
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 1; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 32) (EVar 37) (EVar 38) pixs s 128 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 1; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 35) (EVar 36) (ELit 1) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  pose (STOPS := STOPS_E).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 128) (Z.to_nat 128) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 1; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 1; exW_canary SEGS 415784 m0]) (EVar 39) (EVar 32) (exW_canary SEGS 415784 m0) s 128 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 1; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 1; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430208 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 1; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 128 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 68159 66596 17 21 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_band_msg_d str_band_proc) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  exact (HC m1 r1 HW1 CSK PMK A10).
Qed.

Lemma band_d_16 : forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BAND_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h 16 cm data) -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 114844) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm data ret S CK HW0 H2 Hs16 HloS Hhi H1 Hret H10 PXs Lpixs_a0 HC.
  unfold BAND_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 128 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 128)%Z) by lia.
  assert (GLO2 : (s - 128 + Z.of_nat (Z.to_nat 128) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (128 <= s)%Z) by lia.
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 16; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 32) (EVar 37) (EVar 38) pixs s 128 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 16; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 35) (EVar 36) (ELit 16) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  pose (STOPS := STOPS_E).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 128) (Z.to_nat 128) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 16; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 16; exW_canary SEGS 415784 m0]) (EVar 39) (EVar 32) (exW_canary SEGS 415784 m0) s 128 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 16; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 16; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430208 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 16; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 128 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 68159 66596 17 21 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_band_msg_d str_band_proc) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  exact (HC m1 r1 HW1 CSK PMK A10).
Qed.

Lemma band_d_24 : forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BAND_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h 24 cm data) -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 114844) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm data ret S CK HW0 H2 Hs16 HloS Hhi H1 Hret H10 PXs Lpixs_a0 HC.
  unfold BAND_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 128 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 128)%Z) by lia.
  assert (GLO2 : (s - 128 + Z.of_nat (Z.to_nat 128) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (128 <= s)%Z) by lia.
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 24; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 32) (EVar 37) (EVar 38) pixs s 128 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 24; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 35) (EVar 36) (ELit 24) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  pose (STOPS := STOPS_E).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 128) (Z.to_nat 128) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 24; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 24; exW_canary SEGS 415784 m0]) (EVar 39) (EVar 32) (exW_canary SEGS 415784 m0) s 128 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 24; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 24; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430208 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 24; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 128 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 68159 66596 17 21 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_band_msg_d str_band_proc) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  exact (HC m1 r1 HW1 CSK PMK A10).
Qed.

Lemma band_d_32 : forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + BAND_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 10 = Z_to_bv 64 pixs ->
  PIXat m pixs (hdv w h 32 cm data) -> live A (Z_to_bv 64 pixs) = Some 64%Z ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 114844) m al_rom) md) S.
Proof.
  intros fx C A0 m0 md r0 s pixs w h cm data ret S CK HW0 H2 Hs16 HloS Hhi H1 Hret H10 PXs Lpixs_a0 HC.
  unfold BAND_STACK, LSF in *.
  assert (Hlo : (c_top C - LSTK + 128 <= s)%Z) by lia.
  assert (HRA : ex_keep (getr r0 ex_r1 = ret)) by exact H1.
  assert (HSP : ex_keep (getr r0 ex_r2 = Z_to_bv 64 s)) by exact H2.
  destruct fx as [fr cs]. pose proof I as FZ.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img ll_ro LLU16] in *. pose proof LSTK_val as LV.
  pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
  pose proof (POSTM_refl C A0 s m0) as PM0. pose proof (sub_live_refl A0) as SUB0.
  rewrite <- (with_vmmaps_same md) in HW0 |- *. set (vm0 := m_vmmaps md) in *.
  pose (valsI := @nil word).
  assert (GLO1 : (c_top C - LSTK <= s - 128)%Z) by lia.
  assert (GLO2 : (s - 128 + Z.of_nat (Z.to_nat 128) <= c_top C)%Z) by (rewrite Z2Nat.id by lia; lia).
  assert (RS : (0 <= s < 2 ^ 64)%Z) by lia.
  assert (RS2 : (128 <= s)%Z) by lia.
  pose proof (exT_kn_pix SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 32) (EVar 37) (EVar 38) pixs s 128 _ CK HW0 Lpixs_a0 PXs eq_refl eq_refl RS GLO1 eq_refl eq_refl) as HKp0.
  pose proof (exT_kn_whd SEGS m0 (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 34) (EVar 35) (EVar 36) (ELit 32) pixs _ PXs eq_refl eq_refl eq_refl eq_refl) as HKd0.
  pose (STOPS := STOPS_E).
  (* [comment removed for export] *)
  pose proof (W_sok_win C A0 m0 _ (s - 128) (Z.to_nat 128) CK HW0 GLO1 GLO2) as SOK0.
  pose proof (exW_canary_ok SEGS 415784 m0 (canary_any m0)) as CANOK0.
  pose (vals0 := valsI ++ map (getr r0) ex_regs_list ++ map (Z_to_bv 64) [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 32; exW_canary SEGS 415784 m0]).
  pose proof (exW_kn_fixed SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 32; exW_canary SEGS 415784 m0]) (EVar 39) (EVar 32) (exW_canary SEGS 415784 m0) s 128 415784 65536 212992 213416 213568 213416 213568
                HW0 eq_refl (proj1 CANOK0) (proj2 CANOK0) eq_refl eq_refl eq_refl SOK0 eq_refl RS2 (proj2 RS) eq_refl eq_refl eq_refl eq_refl ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKf0.
  pose proof (exW_kn_clr SEGS C A0 m0 _ (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 32; exW_canary SEGS 415784 m0]) 217704 217712 217704 217712 HW0 ltac:(exW_in) eq_refl eq_refl eq_refl eq_refl) as HKx0_0.
  assert (HKn0 : know_ok SEGS (ex_envL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 32; exW_canary SEGS 415784 m0]) m0 [KRange (EVar 32) 430208 (2 ^ 63); KAlign (EVar 32) 16]).
  { ex_know r0. }
  pose proof (proj2 (Forall_app _ _ _) (conj HKn0 (proj2 (Forall_app _ _ _) (conj HKp0 (proj2 (Forall_app _ _ _) (conj HKd0 (proj2 (Forall_app _ _ _) (conj HKx0_0 HKf0)))))))) as HK. cbn [app] in HK.
  match type of HK with Forall (kentry_ok ?sg ?e ?mm) ?l => change (know_ok sg e mm l) in HK end.
  ex_entryL valsI r0 [s; bv_unsigned (reg_get fr ex_r8); pixs; w; h; data; wpl_of w 32; exW_canary SEGS 415784 m0] HR.
  lazymatch type of HK with know_ok _ _ _ ?kn => set (KN0 := kn) in HK end.
  exb_open HR HK ST.
  clear HR HKn0 HKp0 HKd0 HKx0_0 HKf0 SOK0 CANOK0.
  repeat match goal with H : getr r0 _ = _ |- _ => clear H end.
  exb_adrive 2000%nat 6000%nat STOPS FDEF HK ST FZ.
  (* [comment removed for export] *)
  exb_exit ST Rc0 HR Hlf Hms.
  lazymatch type of Hms with msteps _ _ (mkst _ _ (mem_denot ?EEx _ ?LLx) _) => set (E0 := EEx) in HR, Hlf, HK, Hms |- *; set (log0 := LLx) in Hms, Hlf; set (M0 := mem_denot E0 m0 log0) in Hms end.
  assert (WP0 : W C A0 M0 (with_vmmaps vm0 md) /\ POSTM C A0 s m0 M0).
  { subst M0. apply (exW_win_blks C A0 A0 m0 _ E0 log0 (EVar 32) s 128 [] CK HW0 SUB0 Hlf); [vm_cast_no_check (eq_refl true) | reflexivity | exW_cmp | exact GLO1 | exact Hhi |]. constructor. }
  destruct WP0 as [HWs0 PMs0].
  lazymatch type of HK with know_ok _ _ _ ?kn0 =>
    let cc := eval vm_compute in (carry log0 kn0 []) in
    lazymatch cc with (?kn1, ?scs, ?hs) =>
      assert (HC0 : carry log0 kn0 [] = (kn1, scs, hs)) by (vm_cast_no_check (eq_refl (kn1, scs, hs)));
      assert (HKc0 : know_ok SEGS E0 M0 kn1) by (apply (carry_after SEGS E0 m0 log0 kn0 [] kn1 scs hs HC0 Hlf HK); split_scs)
    end end.
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW0)) | exact (mp_lazy _ (w_pure _ _ _ _ HW0)) | exact Hms |].
  pose (BS0 := [(32%nat, s); (35%nat, w); (36%nat, h); (34%nat, pixs)]).
  exW_regfactB BS0 HR ex_r10 Q10_0. exW_regfactB BS0 HR ex_r11 Q11_0. exW_regfactB BS0 HR ex_r12 Q12_0. exW_regfactB BS0 HR ex_r2 Q2_0.
  clear BS0.
  exW_regfactW r0 HR ex_r1 G1w.
  assert (CS0 : cs_kept r0 Rc0).
  { lazymatch type of HR with regs_ok ?EE ?sr _ => apply (exW_cs_of_sr EE sr r0 Rc0 [(2%nat, EVar 32)] HR); [exW_entry_vars | constructor; [symmetry; exact HSP | constructor] | vm_compute; reflexivity] end. }
  rewrite PC_RETERR_eq.
  lazymatch goal with |- realizes _ (mkCfg (@mkst ?fxk _ _ _ _) _) _ =>
    apply (returnErrorPtr_W (fx := fxk) C A0 M0 _ Rc0 s 68159 66596 17 21 ret (Z_to_bv 64 0) S CK HWs0 Q2_0
             Hs16 ltac:(unfold LSF; lia) Hhi (eq_trans G1w HRA) Hret Q10_0 Q11_0 Q12_0 str_band_msg_d str_band_proc) end.
  intros m1 r1 HW1 OUT GRW CSx A10.
  assert (PMK : POSTM C A0 s m0 m1).
  { eapply POSTM_trans; [exact PM0|]. eapply POSTM_trans; [exact PMs0|].
    apply (POSTM_range C A0 M0 _ m1 (s - (16 + LSF)) s s CK HWs0 OUT); unfold LSF; lia. }
  assert (CSK : cs_kept r0 r1) by (intros r Hr; rewrite (CSx r Hr); exact (CS0 r Hr)).
  unfold vm0 in *. rewrite (with_vmmaps_same md) in *.
  exact (HC m1 r1 HW1 CSK PMK A10).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem F3_W : pixDestroy_rc2_contract -> band_loop_hop -> F3_contract.
Proof.
  intros HRC2 HLOOP. unfold F3_contract, gq_F_contract.
  intros fx C X A m md regs s pix w h d cd data ad kd kna kn ret S FZ CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 (H11 & H12 & H13 & H14) OWN HOK Hw Hh kR bR RM HkR HbR HC.
  unfold GQ_STACK_F, TP_gq, RK_mask, RB_mask in *.
  assert (KD : forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' -> getr regs' 10 = Z_to_bv 64 0 ->
                 realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) md) S).
  { intros m' regs' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
    apply (HC fx A m' (m_vmmaps md) regs' FZ ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
    apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_pix in *; lia | clear - HbR; unfold RB_pix14 in *; lia]. }
  destruct OWN as [P0 | OWN].
  - subst pix.
    apply (F3_null_W fx C A m md regs s ret S FZ CK HW H2 Hs16 ltac:(unfold GQ_ARM_STACK, LSF; lia) Hhi H1 Hret H10).
    intros fx' m' regs' FZ' HW' CS' PM' A0'. rewrite <- (with_vmmaps_same md).
    apply (HC fx' A m' (m_vmmaps md) regs' FZ' ltac:(rewrite with_vmmaps_same; exact HW') CS' PM' (or_introl (conj A0' (fun q => eq_refl)))).
    apply (aroom_mono A (m_vmmaps md) kR bR); [exact RM | clear - HkR; unfold RK_pix in *; lia | clear - HbR; unfold RB_pix14 in *; lia].
  - destruct OWN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & Rpos & PX & Lp & Ld & FR & CMR).
    destruct (FR _ (or_introl eq_refl)) as [_ L0p].
    assert (KS : forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
                   (exists pixd datad, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 0 datad cmap0) ->
                   aroom A' vm' (kR - RK_pix) (bR - RB_pix14) -> realizes SEGS (mkCfg (@mkst fx regs' ret m' al_rom) (with_vmmaps vm' md)) S).
    { intros A' m' vm' regs' HW' CS' PM' (pixd & datad & A0' & PN) RM'.
      apply (HC fx A' m' vm' regs' FZ HW' CS' PM'); [|exact RM'].
      right. exists pixd, w, h, 1%Z, 0%Z, datad, cmap0. split; [exact A0' | split; [exact PN|]].
      assert (1 <= wpl_of w 1)%Z by (unfold wpl_of; apply Z.div_le_lower_bound; lia). nia. }
    pose proof HOK as (DV & _). destruct DV as [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]].
    + exact (band_d_1 fx C A m md regs s pix w h cd data ret S CK HW H2 Hs16 ltac:(unfold BAND_STACK, LSF; lia) Hhi H1 Hret H10 PX Lp KD).
    + exact (band_ok_2 HRC2 HLOOP fx C A m md regs s pix w h cd data ret S CK HW H2 Hs16 ltac:(unfold BAND_STACK, LSF; lia) Hhi H1 Hret H4 H10 H11 H12 H13 H14 PX HOK Hw Hh Lp L0p Ld kR bR RM HkR HbR KS).
    + exact (band_ok_4 HRC2 HLOOP fx C A m md regs s pix w h cd data ret S CK HW H2 Hs16 ltac:(unfold BAND_STACK, LSF; lia) Hhi H1 Hret H4 H10 H11 H12 H13 H14 PX HOK Hw Hh Lp L0p Ld kR bR RM HkR HbR KS).
    + exact (band_ok_8 HRC2 HLOOP fx C A m md regs s pix w h cd data ret S CK HW H2 Hs16 ltac:(unfold BAND_STACK, LSF; lia) Hhi H1 Hret H4 H10 H11 H12 H13 H14 PX HOK Hw Hh Lp L0p Ld kR bR RM HkR HbR KS).
    + exact (band_d_16 fx C A m md regs s pix w h cd data ret S CK HW H2 Hs16 ltac:(unfold BAND_STACK, LSF; lia) Hhi H1 Hret H10 PX Lp KD).
    + exact (band_d_24 fx C A m md regs s pix w h cd data ret S CK HW H2 Hs16 ltac:(unfold BAND_STACK, LSF; lia) Hhi H1 Hret H10 PX Lp KD).
    + exact (band_d_32 fx C A m md regs s pix w h cd data ret S CK HW H2 Hs16 ltac:(unfold BAND_STACK, LSF; lia) Hhi H1 Hret H10 PX Lp KD).
Qed.
End Chain.
