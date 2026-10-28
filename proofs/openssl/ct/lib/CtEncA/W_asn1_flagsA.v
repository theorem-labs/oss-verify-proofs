(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApBase ApPrim.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit R_cache_defs R_prim_defs R_sec_defs D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells ApRepDefs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA AsStruct RtCallA UnwindA UnwindX EdgesA W_cryptoA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit AFrameCall AFrameTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApBImg ApWalkTac ApRep ApFrame W_item_d2i_imgA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncP Require Import EncPure.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncA Require Import EncStmtA Fr_asn1_ex_i2c Fr_asn1_i2d_ex_primitive Fr_ASN1_item_ex_i2d Fr_asn1_item_flags_i2d W_asn1_enc_leavesA W_asn1_ex_i2cA W_asn1_i2d_primA W_asn1_item_exA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
(* [comment removed for export] *)
Local Ltac nrm := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *.
Local Ltac plia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP, RT_STACK in *; cbn [ar_FR ar_RT ar_SP0 ar_PMc push amb] in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac ab_ichk t u J :=
  first [ match goal with OK : absh_ok _ _ _ |- _ => ab_join t u J OK end
        | OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step; rewrite ?zxb_z8, ?sxb_z8; first [if_false | if_true] ].
Ltac lit_addr H := lazymatch type of H with
  | ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H
  | rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H end.
Ltac fz H := lazymatch type of H with ?T => change T with (frozen T) in H end.
Ltac thaw H := unfold frozen in H.

(* [comment removed for export] *)
Definition I2D_OCTET_STACK_A : Z := AFI_FRAME + ASN1_ITEM_EX_I2D_STACK_A.
(* [comment removed for export] *)
Definition I2D_OCTET_COST_A (n : Z) : Z := 8 + mcost n.
Definition A_TASN_ENC_C_A : Z := 0x733c0.       (* [comment removed for export] *)

Lemma cb_split2A : forall (m : mem) A a b bs,
  rw_cells ctasegs m A [CB (Z.to_nat (a + b)) bs] -> 0 <= a -> 0 <= b ->
  rw_cells ctasegs m A [CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] /\ rw_cells ctasegs m (A + a) [CB (Z.to_nat b) (skipn (Z.to_nat a) bs)].
Proof.
  intros m A a b bs H Ha Hb.
  pose proof H as [[WF _] _]. cbn in WF.
  assert (H2 : rw_cells ctasegs m A ([CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] ++ [CB (Z.to_nat b) (skipn (Z.to_nat a) bs)])).
  { eapply (rw_cells_recast m A _ _ H).
    - cbn. rewrite length_firstn, length_skipn. repeat split; lia.
    - cbn. rewrite !app_nil_r, firstn_skipn. reflexivity.
    - cbn. lia. }
  split; [exact (rw_cells_app_l _ _ _ _ H2)|].
  exact (rw_cells_skip m A [CB (Z.to_nat a) (firstn (Z.to_nat a) bs)] _ a H2 ltac:(cbn; lia)).
Qed.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FRM := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).
Local Notation E_oct_tail := (E_i2d_ASN1_OCTET_STRING_249f8c : uk_tail 2387508 2389112).
Local Notation E_item_tail := (E_ASN1_item_i2d_24a5d8 : uk_tail 2389112 2388412).
Local Notation E_afi_malloc := (E_asn1_item_flags_i2d_24a490 : uk_call 2388412 2388824 2084388).

(* [comment removed for export] *)
Lemma afi_open_obj : forall Σ1 OW LB m f q (k : nat) cs,
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m -> @fr_geo (push AR f 1) f 1 ->
  rw_cells ctasegs m (shad f) cs -> (k = 4 \/ k = 8)%nat -> nth_error (cells_bytes cs) k = Some z8 -> (k < length (cells_bytes cs))%nat ->
  ~ In q (map blk_id (OW ++ LB)) -> (forall b, In b LB -> blk_apart (q, f + 8 * Z.of_nat k, 8) b) ->
  @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((q, f + 8 * Z.of_nat k, 8) :: LB) m.
Proof.
  intros Σ1 OW LB m f q k cs HEAP GEO FRS Hk NTH KL Hq AP.
  destruct GEO as (G1 & G2 & G3 & G4 & G5).
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  apply (@frame_obj_open (push AR f 1) Σ1 OW LB m f 1%nat q (f + 8 * Z.of_nat k) 8 (or_introl eq_refl) HEAP);
    [clear - Hk; lia| change (fs_size 1) with 128; clear - Hk; lia| clear; lia| | exact Hq| exact AP].
  apply (acc_of_shadow_cells m (shad f) cs k (f + 8 * Z.of_nat k) 8 FRS ltac:(clear - F8; Z.div_mod_to_equations; lia) ltac:(clear - G1; lia) ltac:(clear; lia));
    [rewrite (shad_aligned_add f (8 * Z.of_nat k) F8) by (clear; lia); rewrite Z.mul_comm, Z.div_mul by (clear; lia); reflexivity| clear - KL; lia|].
  cbn [ushadow Z.div Z.modulo Z.eqb Z.to_nat repeat app length firstn].
  clear - NTH KL. revert NTH KL. generalize (cells_bytes cs) as bs. intros bs NTH KL.
  rewrite <- (firstn_skipn k bs) in NTH. rewrite nth_error_app2 in NTH by (rewrite length_firstn; lia).
  rewrite length_firstn, Nat.min_l, Nat.sub_diag in NTH by lia.
  destruct (skipn k bs) as [|b0 rest]; [discriminate|]. cbn in NTH. injection NTH as ->. reflexivity.
Qed.

(* [comment removed for export] *)
Definition i2d_octet_postA (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (Σ : rts RT) (OW LB : list block) (lo OUT len : Z) (m : mem)
    (p : bptr) (Σ' : rts RT) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (F' : bvmap 5 word) (fc' : bv 32) m' AD,
    ms' = MS (mkR ra sp gp (wz TP_A) t0 t1 t2 s0 s1 (Z_to_bv 64 (der_hl len + len)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom ctasegs)
    /\ mem_inv ctasegs m' /\ stk ctasegs m' lo (bv_unsigned sp)
    /\ AHEAP Σ' ((p, AD, der_hl len + len) :: OW) LB m' /\ ablock_range AD (der_hl len + len)
    /\ rt_credit RT Σ - I2D_OCTET_COST_A (der_hl len + len) <= rt_credit RT Σ'
    /\ agree_on (fun a => aclient_addr (OW ++ LB) (bv_unsigned sp) a /\ ~ (OUT <= a < OUT + 8)) m m'
    /\ rw_cells ctasegs m' OUT [C8 (wz AD)].

Lemma i2d_octet_walkA : forall {X : Type} (k : option bptr -> aprog bptr X) (Q : X -> rts RT -> machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (Σ : rts RT) (OW LB : list block) (lo : Z) (ras : list Z)
    (A len D fl OUT : Z) (src : list byte) (bA bD bO : block),
  AHEAP Σ OW LB m -> stk ctasegs m lo (bv_unsigned sp) -> ACEIL <= lo -> lo + I2D_OCTET_STACK_A <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 ->
  mem_inv ctasegs m -> tp = wz TP_A -> fr_depth_ok 4%nat -> I2D_OCTET_COST_A (der_hl len + len) <= rt_credit RT Σ ->
  crypto_statics m ->
  uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras -> uk_ctx I2D_ASN1_OCTET_STRING_A (bv_unsigned ra :: ras) ->
  In bA (OW ++ LB) -> blk_addr bA <= A -> A + ASN1_STRING_SIZE <= blk_addr bA + blk_size bA -> A mod 8 = 0 ->
  rw_cells ctasegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  0 < len < 65536 -> 0 <= fl < 2^64 ->
  In bD (OW ++ LB) -> blk_addr bD <= D -> D + len <= blk_addr bD + blk_size bD -> bytes_at ctasegs m D src -> length src = Z.to_nat len ->
  In bO (OW ++ LB) -> blk_addr bO <= OUT -> OUT + 8 <= blk_addr bO + blk_size bO -> OUT mod 8 = 0 -> rw_cells ctasegs m OUT [C8 (wz 0)] ->
  (A + ASN1_STRING_SIZE <= OUT \/ OUT + 8 <= A) -> (D + len <= OUT \/ OUT + 8 <= D) ->
  a0 = wz A -> a1 = wz OUT ->
  (forall p Σ' ms', ~ In p (map blk_id (OW ++ LB)) ->
     i2d_octet_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB lo OUT len m p Σ' ms' ->
     implAp (k (Some p)) Σ' Q ms') ->
  implAp (AMalloc (der_hl len + len) k) Σ Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz I2D_ASN1_OCTET_STRING_A) fc None m (seg_rom ctasegs)).
Proof.
  intros until bO. intros HEAP ST CEIL LO TOP AL16 MI -> FD CRED CS UW CTX AIN AL AH A8 HS LEN FLR DIN DL DH SRC SLEN OIN OL OH O8 HO SEPAO SEPDO -> -> K.
  unfold I2D_OCTET_STACK_A, ASN1_ITEM_EX_I2D_STACK_A, ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AFI_FRAME, AIE_FRAME, AIP_FRAME, AEI_FRAME in LO.
  unfold I2D_OCTET_COST_A in CRED.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (bv_unsigned_in_range 64 s0) as S0R.
  pose proof (der_hl_range len ltac:(clear - LEN; lia)) as HLR.
  assert (MC0 : 0 <= mcost (der_hl len + len)) by (unfold mcost; destruct (_ <=? _); clear - LEN HLR; lia).
  pose proof (AH_ceil _ _ _ _ HEAP) as (CE1 & CE2 & CE3).
  pose proof (AH_range_gen _ _ _ _ _ HEAP AIN) as (AB0 & _ & _ & ABC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP DIN) as (DB0 & _ & _ & DBC & _).
  pose proof (AH_range_gen _ _ _ _ _ HEAP OIN) as (OB0 & _ & _ & OBC & _). cbn [blk_addr blk_size fst snd] in *. nrm.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  unfold ASN1_STRING_SIZE in SEPAO. fz SEPAO. fz SEPDO.
  destruct (fr_depth_push 3%nat 0 0%nat FD) as [FLEN _].
  unfold I2D_ASN1_OCTET_STRING_A, MallocRep.wz.
  (* [comment removed for export] *)
  intros XX Φ DD SAFE LINK.
  fz HS. fz HO. assert (SRCF : frozen (bytes_at ctasegs m D src)) by exact SRC. clear SRC.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply cps_from_evt'.
  carve_frame 16%nat ST. do 4 zstep. zstep. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  carve_frame 16%nat ST. do 4 zstep. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  match goal with H : munch _ m m1 |- _ => rename H into MU1 end. match goal with H : wmono ctasegs m m1 |- _ => rename H into WM1 end.
  match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end.
  assert (HEAP1 : AHEAP Σ OW LB m1).
  { eapply AH_frame; [exact HEAP| exact MU1| exact WM1|]. constructor; [left; cbn [fst snd]; clear - CEIL LO TOP; plia| constructor]. }
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (bv_unsigned sp) HEAP MU1). constructor; [cbn [fst snd]; clear - CEIL LO; plia| constructor]. }
  apply evt_done. change (Z_to_bv 64 2388412) with (wz AFI_ENTRY).
  (* [comment removed for export] *)
  eapply (afi_pro_cps _) with (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP1| first [assumption | eapply stk_transport; [exact ST| exact MU1| exact WM1| cbn; clear; lia]]| exact CEIL| unfold AFI_FRAME, RT_STACK; clear - LO; lia| exact TOP| exact AL16| exact MI1| reflexivity| exact FLEN| clear - CRED MC0; lia|].
  intros Σ1 m3 f spa g junkf gj ra' t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' F1 fc1 j0 j8 jf24 jf40 jf64 jf72 jst
         HEAP3 FRESH GEO CR1 EL1 ST3 MI3 AGF FRL FRH FRF FRS SPA32 SPAL SPAH GSZ SAVJ.
  thaw HS. thaw HO. pose proof SRCF as SRC. thaw SRC. clear SRCF.
  unfold AFI_BODY, MallocRep.wz.
  pose proof GEO as (G1 & G2 & G3 & G4 & G5). change (fs_size 1) with 128 in G3, G4, G5.
  destruct (fr_depth_push 3%nat f 1%nat FD) as [_ FD1].
  pose proof (@AH_ceil (push AR f 1) _ _ _ _ HEAP3) as (CF1 & CF2 & CF3). nrm.
  assert (F8 : f mod 8 = 0) by (clear - G2; Z.div_mod_to_equations; lia).
  assert (Ef : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; clear - G1 G3 CF3; lia).
  assert (ESPA : bv_unsigned (Z_to_bv 64 spa) = spa) by (apply unsigned_lit; clear - CEIL LO0 LO SPAL SPAH SPR; lia).
  pose proof (FRESH _ AIN) as OFA. pose proof (FRESH _ DIN) as OFD. pose proof (FRESH _ OIN) as OFO.
  unfold off_fr in OFA, OFD, OFO. change (fs_size 1) with 128 in OFA, OFD, OFO.
  (* [comment removed for export] *)
  assert (AG3 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m3) by (eapply agree_on_trans; [exact AG1| exact AGF]).
  apply (rw_cells_agree _ _ _ _ _ AG3) in HS; [| intros xa Hxa; right; right; exists bA; split; [exact AIN| unfold asn1_string_cells, ASN1_STRING_SIZE in *; cbn in Hxa; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG3) in HO; [| intros xa Hxa; right; right; exists bO; split; [exact OIN| cbn in Hxa; lia]].
  apply (bytes_at_agree _ m m3 _ _ AG3) in SRC; [| intros xa Hxa; rewrite SLEN, Z2Nat.id in Hxa by lia; right; right; exists bD; split; [exact DIN| lia]].
  (* [comment removed for export] *)
  pose proof (rw_cells_app_l m3 (f + 32) [C8 (Z_to_bv 64 A)] _ (rw_cells_skip m3 f [_; _; _; _] _ 32 FRF eq_refl)) as HVAL.
  pose proof (rw_cells_app_l m3 (f + 64) [CB 8 jf64] _ (rw_cells_skip m3 f [_; _; _; _; _; _] _ 64 FRF eq_refl)) as HPC.
  clear FRF.
  ablock HEAP3 OIN ACCO OFFO'. unfold SHLO, SHHI in OFFO'. fz OFFO'.
  unfold asn1_string_cells, ASN1_STRING_SIZE, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (munch_refl [(spa, spa + 24)]%Z m3) as MU3. pose proof (wmono_refl ctasegs m3) as WM3.
  assert (OFFW3 : offshW [(spa, spa + 24)]%Z) by (cbn [offshW]; unfold SHLO, SHHI; clear - CF1 CF2 CEIL LO SPAL; lia).
  apply cps_from_evt'.
  (* [comment removed for export] *)
  zstep. sfalse. zstep. zstep. btaken.
  (* [comment removed for export] *)
  fz HS. fz HO. assert (SRCF : frozen (bytes_at ctasegs m3 D src)) by exact SRC. clear SRC.
  pose proof (@AH_offsh (push AR f 1) _ _ _ _ _ HEAP3 AIN) as OFFA. pose proof (@AH_offsh (push AR f 1) _ _ _ _ _ HEAP3 DIN) as OFFD.
  cbn [blk_addr blk_size fst snd] in OFFA, OFFD. unfold SHLO, SHHI in OFFA, OFFD. fz OFFA. fz OFFD.
  clear MU3 WM3. pose proof (munch_refl [(spa, spa); (f, f + 0); (shad f, shad f + 16)]%Z m3) as MUs. pose proof (wmono_refl ctasegs m3) as WMs.
  unfold afi_shadow_pro in FRS.
  assert (SHR : 2147450880 <= shad f /\ shad f + 16 <= 17594333495296).
  { unfold shad, SHB. pose proof (Z.div_pos f 8 ltac:(clear - G1; lia) ltac:(clear; lia)).
    assert (f / 8 + 16 <= 2 ^ 44) by (assert (f / 8 < 2 ^ 44 - 16); [apply Z.div_lt_upper_bound; clear - G3 CF3; lia | clear - H0; lia]). clear - H H0. lia. }
  thaw G5. sbstep. fz G5.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m4 end.
  match goal with H : munch _ m3 m4 |- _ => rename H into MU4 end. match goal with H : wmono ctasegs m3 m4 |- _ => rename H into WM4 end.
  match goal with H : mem_inv ctasegs m4 |- _ => rename H into MI4 end. match goal with H : rw_cells ctasegs m4 (shad f) _ |- _ => rename H into FRS4 end.
  assert (HEAP4 : @BnHeapA.AHEAP (push AR f 1) Σ1 OW LB m4).
  { eapply (@fr3_heap (push AR f 1) Σ1 OW LB m3 m4 f 1%nat spa spa 0 16 (or_introl eq_refl) HEAP3 MU4 WM4);
      [clear - CEIL LO SPAL; plia| clear - TOP SPAH; plia
      | change (fs_size 1) with 128; clear; lia| change (fs_size 1) with 128; clear; lia
      | intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))]. }
  assert (AG34 : agree_on (aclient_addr (OW ++ LB) spa) m3 m4).
  { eapply (@fr3_agree (push AR f 1) Σ1 OW LB m3 m3 m4 f 1%nat spa spa 0 16 (OW ++ LB) HEAP3 MU4 GEO);
      [change (fs_size 1) with 128; clear; lia| change (fs_size 1) with 128; clear; lia| clear - CEIL LO SPAL; plia| clear; lia
      | intros b Hb; exact Hb| exact FRESH]. }
  assert (ST4 : stk ctasegs m4 lo spa) by (first [assumption| eapply stk_transport; [exact ST3| exact MU4| exact WM4| cbn; clear; lia]]).
  thaw HS. thaw HO. pose proof SRCF as SRC. thaw SRC. clear SRCF. thaw OFFA. thaw OFFD. thaw OFFO'.
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HS; [| cbn; clear - OFFA OFA AL AH SHR ABC CEIL LO SPAL; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HO; [| cbn; clear - OFFO' OFO OL OH SHR OBC CEIL LO SPAL; lia].
  apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU4) in SRC; [| rewrite SLEN, Z2Nat.id by lia; cbn; clear - OFFD OFD DL DH SHR LEN DBC CEIL LO SPAL; lia].
  fz OFFA. fz OFFD. fz OFFO'.
  (* [comment removed for export] *)
  destruct (bptr_fresh (map blk_id (OW ++ LB))) as [qv Hqv].
  assert (HEAPv : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((qv, f + 32, 8) :: LB) m4).
  { replace (f + 32) with (f + 8 * Z.of_nat 4) by (clear; lia).
    eapply (afi_open_obj Σ1 OW LB m4 f qv 4%nat _ HEAP4 GEO FRS4); [left; reflexivity| reflexivity| cbn; clear; lia| exact Hqv|].
    intros b Hb. pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. change (fs_size 1) with 128 in O.
    unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
  destruct (bptr_fresh (map blk_id (OW ++ (qv, f + 32, 8) :: LB))) as [qp Hqp].
  assert (HEAPp : @BnHeapA.AHEAP (push AR f 1) Σ1 OW ((qp, f + 64, 8) :: (qv, f + 32, 8) :: LB) m4).
  { replace (f + 64) with (f + 8 * Z.of_nat 8) by (clear; lia).
    eapply (afi_open_obj Σ1 OW ((qv, f + 32, 8) :: LB) m4 f qp 8%nat _ HEAPv GEO FRS4); [right; reflexivity| reflexivity| cbn; clear; lia| exact Hqp|].
    intros b [<-|Hb]; [unfold blk_apart; cbn [blk_addr blk_size fst snd]; clear; lia|].
      pose proof (FRESH b (in_or_app _ _ _ (or_intror Hb))) as O. unfold off_fr in O. change (fs_size 1) with 128 in O.
      unfold blk_apart. cbn [blk_addr blk_size fst snd]. clear - O. lia. }
  set (LB2 := (qp, f + 64, 8) :: (qv, f + 32, 8) :: LB) in HEAPp.
  assert (INC2 : forall b, In b (OW ++ LB) -> In b (OW ++ LB2)) by (intros b Hb; apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; right; exact Hb]).
  assert (VIN : In (qv, f + 32, 8) (OW ++ LB2)) by (apply in_or_app; right; right; left; reflexivity).
  assert (PIN2 : In (qp, f + 64, 8) (OW ++ LB2)) by (apply in_or_app; right; left; reflexivity).
  assert (LIFT2 : forall L a, aclient_addr (L ++ LB) spa a -> aclient_addr (L ++ LB2) spa a).
  { intros L a [Ha|[Ha|(b & Hb & Hr)]]; [left; exact Ha| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
    apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; exact Hb| right; right; right; exact Hb]. }
  assert (DR : 0 <= D < 2^64) by (clear - DB0 DL DH DBC CF3 LEN; lia).
  (* [comment removed for export] *)
  first [ match type of HVAL with rw_cells _ m4 _ _ => idtac end
        | thaw G5; apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HVAL; [| cbn; clear - G5 SHR; lia]; fz G5 ].
  first [ match type of HPC with rw_cells _ m4 _ _ => idtac end
        | thaw G5; apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in HPC; [| cbn; clear - G5 SHR; lia]; fz G5 ].
  first [ match type of FRH with rw_cells _ m4 _ _ => idtac end
        | apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in FRH; [| cbn; clear - SHR CF3 CEIL LO SPAH; lia] ].
  first [ match type of FRL with rw_cells _ m4 _ _ => idtac end
        | apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU4 WM4) in FRL; [| cbn; clear - SHR CF3 CEIL LO SPAL SPAH GSZ; lia] ].
  clear MU4 WM4 HEAP3 HEAP4 HEAPv. try clear MI3. try clear ST3.
  pose proof (munch_refl (@nil (Z * Z)) m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  apply evt_done.
  eapply (@aie_len_cpsA (push AR f 1) _) with (lo := lo) (OW := OW) (LB := LB2) (PVAL := f + 32) (A := A) (len := len) (D := D) (fl := fl)
    (bPV := (qv, f + 32, 8)) (bA := bA); rewrite ?ESPA; try reflexivity.
  - exact HEAPp.
  - exact ST4.
  - unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
  - unfold ASN1_ITEM_EX_I2D_STACK_A, ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AIE_FRAME, AIP_FRAME, AEI_FRAME, RT_STACK. clear - LO SPAL. lia.
  - unfold USTACK_TOP. clear - TOP SPAH. lia.
  - clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
  - exact MI4.
  - exact FD1.
  - cbn [ar_RT push amb]. clear - CRED CR1 MC0. lia.
  - exact VIN.
  - clear - F8. uchk_open. Z.div_mod_to_equations. lia.
  - exact HVAL.
  - exact (INC2 _ AIN).
  - exact AL.
  - unfold ASN1_STRING_SIZE. exact AH.
  - clear - A8. uchk_open. exact A8.
  - exact HS.
  - clear - LEN. lia.
  - exact DR.
  - exact FLR.
  - (* [comment removed for export] *)
    intros Σ2 m5 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 HEAP5 CR2 EL2 ST5 MI5 AG5.
    cbn [ar_RT push amb] in CR2, EL2. rewrite (ret_pc_even 0x24733c) by (clear; lia).
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRL; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HPC; [| intros xa Hxa; cbn in Hxa; right; right; exists (qp, f + 64, 8); split; [exact PIN2| cbn; clear - Hxa; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HVAL; [| intros xa Hxa; cbn in Hxa; right; right; exists (qv, f + 32, 8); split; [exact VIN| cbn; clear - Hxa; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HS; [| intros xa Hxa; cbn in Hxa; right; right; exists bA; split; [exact (INC2 _ AIN)| clear - Hxa AL AH; lia]].
    apply (rw_cells_agree _ _ _ _ _ AG5) in HO; [| intros xa Hxa; cbn in Hxa; right; right; exists bO; split; [exact (INC2 _ OIN)| clear - Hxa OL OH; lia]].
    apply (bytes_at_agree _ m4 m5 _ _ AG5) in SRC; [| intros xa Hxa; rewrite SLEN, Z2Nat.id in Hxa by lia; right; right; exists bD; split; [exact (INC2 _ DIN)| clear - Hxa DL DH; lia]].
    (* [comment removed for export] *)
    assert (AG05 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m5).
    { eapply agree_on_trans; [exact AG3|]. eapply agree_on_trans.
      - eapply agree_on_mono; [exact AG34|]. intros a [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha].
      - eapply agree_on_mono; [exact AG5|]. intros a Ha. apply (LIFT2 OW). destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha]. }
    assert (CS5 : crypto_statics m5).
    { eapply crypto_statics_agree; [exact AG05| | exact CS]. intros a Ha. right; left. exact (ar_LIBW_cs a Ha). }
    assert (UW5 : uw_chain USTACK_TOP m5 spa (bv_unsigned sp) (bv_unsigned ra :: ras)).
    { eapply (uw_call m m5 spa (bv_unsigned sp) 16 [] (bv_unsigned ra) (bv_unsigned s0) ras);
        [exact UW| | reflexivity| clear - SPAH; lia| clear - AL16; uchk_open; Z.div_mod_to_equations; lia| unfold USTACK_TOP; clear - TOP; lia
        | exact S0R| rewrite !Z_to_bv_bv_unsigned; cbn [app]; exact FRH].
      eapply agree_on_mono; [exact AG05|]. intros a Ha. left. exact Ha. }
    pose proof (munch_refl (@nil (Z * Z)) m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
    apply cps_from_evt'.
    (* [comment removed for export] *)
    zstep. zstep. sfalse. zstep. zstep. zstep. zstep. zstep.
    apply evt_done.
    (* [comment removed for export] *)
    eapply (implAp_elim (AMalloc (der_hl len + len) k) Σ Σ2 Q _ XX Φ DD); [| exact SAFE| exact LINK| rewrite EL2; exact EL1].
    eapply (@CRYPTO_malloc_walkAp (push AR f 1) _ _ X) with (lo := lo) (OW := OW) (LB := LB2) (n := der_hl len + len) (ras := bv_unsigned ra :: ras);
      rewrite ?ESPA; try reflexivity.
    + exact HEAP5.
    + exact ST5.
    + unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
    + unfold CRYPTO_MALLOC_STACK, RT_STACK. clear - LO SPAL. lia.
    + unfold USTACK_TOP. clear - TOP SPAH. lia.
    + clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
    + exact MI5.
    + exact CS5.
    + clear - LEN HLR. lia.
    + cbn [ar_RT push amb]. clear - CRED CR1 CR2. lia.
    + exact UW5.
    + rewrite unsigned_lit by (clear; lia). exact (uk_ctx_call _ _ _ _ E_afi_malloc (uk_ctx_tail _ _ _ E_item_tail (uk_ctx_tail _ _ _ E_oct_tail CTX))).
    + (* [comment removed for export] *)
      intros pd Σ3 ms3 Hp PO.
      destruct PO as (v0 & v1 & v2 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & F3 & fc3 & m7 & AD & -> & MI7 & ST7 & AG7 & CR3 & BR & HEAP7 & ACC7 & (jd & HD)).
      rewrite ?ESPA in ST7, AG7. cbn [ar_RT push amb] in CR3. rewrite (ret_pc_even 0x247358) by (clear; lia). unfold MallocRep.wz.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5). unfold BnHeapA.ACEIL, STACK_WIN in BR4. cbn [ar_SP0 push amb] in BR4.
      set (OW2 := (pd, AD, der_hl len + len) :: OW) in HEAP7.
      assert (INC3 : forall b, In b (OW ++ LB2) -> In b (OW2 ++ LB2)) by (intros b Hb; right; exact Hb).
      assert (PDIN : In (pd, AD, der_hl len + len) (OW2 ++ LB2)) by (left; reflexivity).
      (* [comment removed for export] *)
      assert (NE : forall b, In b (OW ++ LB2) -> blk_id b <> pd) by (intros b Hb E; apply Hp; rewrite <- E; apply in_map; exact Hb).
      pose proof (@AH_disjoint_gen (push AR f 1) _ _ _ _ _ _ HEAP7 (INC3 _ (INC2 _ AIN)) PDIN (NE _ (INC2 _ AIN))) as DJA.
      pose proof (@AH_disjoint_gen (push AR f 1) _ _ _ _ _ _ HEAP7 (INC3 _ (INC2 _ DIN)) PDIN (NE _ (INC2 _ DIN))) as DJD.
      pose proof (@AH_disjoint_gen (push AR f 1) _ _ _ _ _ _ HEAP7 (INC3 _ (INC2 _ OIN)) PDIN (NE _ (INC2 _ OIN))) as DJO.
      pose proof (@AH_ow_off_fr (push AR f 1) _ _ _ _ f 1%nat _ HEAP7 (or_introl eq_refl) (or_introl eq_refl)) as OFPD.
      cbn [blk_addr blk_size fst snd] in DJA, DJD, DJO, OFPD. unfold off_fr in OFPD. change (fs_size 1) with 128 in OFPD. cbn [blk_addr blk_size fst snd] in OFPD.
      fz DJA. fz DJD. fz DJO.
      (* [comment removed for export] *)
      apply (rw_cells_agree _ _ _ _ _ AG7) in FRL; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia].
      apply (rw_cells_agree _ _ _ _ _ AG7) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia].
      apply (rw_cells_agree _ _ _ _ _ AG7) in HPC; [| intros xa Hxa; cbn in Hxa; right; right; exists (qp, f + 64, 8); split; [exact PIN2| cbn; clear - Hxa; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG7) in HVAL; [| intros xa Hxa; cbn in Hxa; right; right; exists (qv, f + 32, 8); split; [exact VIN| cbn; clear - Hxa; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG7) in HS; [| intros xa Hxa; cbn in Hxa; right; right; exists bA; split; [exact (INC2 _ AIN)| clear - Hxa AL AH; lia]].
      apply (rw_cells_agree _ _ _ _ _ AG7) in HO; [| intros xa Hxa; cbn in Hxa; right; right; exists bO; split; [exact (INC2 _ OIN)| clear - Hxa OL OH; lia]].
      apply (bytes_at_agree _ m5 m7 _ _ AG7) in SRC; [| intros xa Hxa; rewrite SLEN, Z2Nat.id in Hxa by lia; right; right; exists bD; split; [exact (INC2 _ DIN)| clear - Hxa DL DH; lia]].
      destruct (cb_split2A m7 AD (der_hl len) len jd HD ltac:(clear - HLR; lia) ltac:(clear - LEN; lia)) as [HD1 HD2]. clear HD.
      fz HS. fz HO. fz HD1. fz HD2. assert (SRCF : frozen (bytes_at ctasegs m7 D src)) by exact SRC. clear SRC.
      pose proof (munch_refl [(f + 64, f + 72)]%Z m7) as MU7. pose proof (wmono_refl ctasegs m7) as WM7.
      intros X2 Φ2 D2 SAFE2 LINK2.
      apply cps_from_evt'.
      (* [comment removed for export] *)
      zstep. sfalse. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m8 end.
      match goal with H : munch _ m7 m8 |- _ => rename H into MU8 end. match goal with H : wmono ctasegs m7 m8 |- _ => rename H into WM8 end.
      match goal with H : mem_inv ctasegs m8 |- _ => rename H into MI8 end.
      assert (ST8 : stk ctasegs m8 lo spa) by (first [assumption| eapply stk_transport; [exact ST7| exact MU8| exact WM8| cbn; clear; lia]]).
      assert (HEAP8 : @BnHeapA.AHEAP (push AR f 1) Σ3 OW2 LB2 m8).
      { eapply (@AH_frame (push AR f 1)); [exact HEAP7| exact MU8| exact WM8|].
        constructor; [right; right; exists (qp, f + 64, 8); split; [exact (INC3 _ PIN2)| cbn; clear; lia]| constructor]. }
      thaw HS. thaw HO. thaw HD1. thaw HD2. pose proof SRCF as SRC. thaw SRC. clear SRCF.
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in HS; [| cbn; clear - OFA AL AH; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in HO; [| cbn; clear - OFO OL OH; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in HD1; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - OFPD HLR LEN; lia].
      apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU8 WM8) in HD2; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; clear - OFPD HLR LEN; lia].
      apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU8) in SRC; [| rewrite SLEN, Z2Nat.id by lia; cbn; clear - OFD DL DH LEN; lia].
      thaw DJA. thaw DJD. thaw DJO.
      apply evt_done.
      eapply (@aie_write_cpsA (push AR f 1) _) with (lo := lo) (OW := OW2) (LB := LB2) (PVAL := f + 32) (A := A) (len := len) (D := D) (fl := fl) (PP := f + 64) (P := AD)
        (src := src) (j1 := firstn (Z.to_nat (der_hl len)) jd) (j2 := skipn (Z.to_nat (der_hl len)) jd)
        (bPV := (qv, f + 32, 8)) (bA := bA) (bPP := (qp, f + 64, 8)) (bP := (pd, AD, der_hl len + len)) (bD := bD); rewrite ?ESPA; try reflexivity.
      * exact HEAP8.
      * exact ST8.
      * unfold BnHeapA.ACEIL. cbn [ar_SP0 push amb]. exact CEIL.
      * unfold ASN1_ITEM_EX_I2D_STACK_A, ASN1_I2D_EX_PRIM_STACK_A, ASN1_EX_I2C_STACK_A, AIE_FRAME, AIP_FRAME, AEI_FRAME, RT_STACK. clear - LO SPAL. lia.
      * unfold USTACK_TOP. clear - TOP SPAH. lia.
      * clear - SPA32. uchk_open. Z.div_mod_to_equations. lia.
      * exact MI8.
      * exact FD1.
      * cbn [ar_RT push amb]. clear - CRED CR1 CR2 CR3. lia.
      * exact (INC3 _ VIN).
      * clear - F8. uchk_open. Z.div_mod_to_equations. lia.
      * exact HVAL.
      * exact (INC3 _ (INC2 _ AIN)).
      * exact AL.
      * unfold ASN1_STRING_SIZE. exact AH.
      * clear - A8. uchk_open. exact A8.
      * exact HS.
      * exact LEN.
      * exact FLR.
      * exact (INC3 _ PIN2).
      * clear - F8. uchk_open. Z.div_mod_to_equations. lia.
      * match goal with H : rw_cells ctasegs m8 (f + 64) _ |- _ => exact H end.
      * exact PDIN.
      * cbn. clear; lia.
      * exact HD1.
      * exact HD2.
      * exact (INC3 _ (INC2 _ DIN)).
      * exact DL.
      * exact DH.
      * exact SRC.
      * exact SLEN.
      * clear - OFPD HLR LEN. lia.
      * clear - DJD DL DH HLR LEN. lia.
      * unfold ASN1_STRING_SIZE. clear - DJA AL AH HLR LEN. lia.
      * clear - OFPD HLR LEN. lia.
      * clear. lia.
      * unfold ASN1_STRING_SIZE. clear - OFA AL AH. lia.
      * clear - OFD DL DH. lia.
      * (* [comment removed for export] *)
        intros Σ4 m9 w0 w1 w2 e1 e2 e3 e4 e5 e6 e7 w3 w4 w5 w6 F4 fc4 HEAP9 CR4 EL4 ST9 MI9 AG9 HPP9 HP19 HP29.
        cbn [ar_RT push amb] in CR4, EL4. rewrite (ret_pc_even 0x24737c) by (clear; lia). unfold MallocRep.wz in HPP9.
        fz DJA. fz DJD.
        apply (rw_cells_agree _ _ _ _ _ AG9) in FRL; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH GSZ; lia| cbn [outside fst snd]; clear - Hxa BR4 G3 CEIL LO SPAL; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG9) in FRH; [| intros xa Hxa; cbn [cells_size csize Nat.add] in Hxa; split; [left; unfold USTACK_TOP; clear - Hxa TOP SPAH; lia| cbn [outside fst snd]; clear - Hxa BR4 G3 CEIL LO SPAL SPAH; lia]].
        apply (rw_cells_agree _ _ _ _ _ AG9) in HO; [| intros xa Hxa; cbn in Hxa; split; [right; right; exists bO; split; [exact (INC3 _ (INC2 _ OIN))| clear - Hxa OL OH; lia]| cbn [outside fst snd]; thaw DJO; clear - Hxa DJO OL OH OFO; lia]].
        fz DJO.
        pose proof (INC3 _ (INC2 _ OIN)) as OIN3. ablock HEAP9 OIN3 ACCO9 OFFO9. fz OFFO9.
        pose proof (munch_refl [(OUT, OUT + 8)]%Z m9) as MU9. pose proof (wmono_refl ctasegs m9) as WM9.
        assert (OFFW9 : offshW [(OUT, OUT + 8)]%Z) by (pose proof OFFO' as XO; thaw XO; cbn [offshW]; unfold SHLO, SHHI; clear - XO OL OH; lia).
        apply cps_from_evt'.
        (* [comment removed for export] *)
        zstep. zstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m10 end.
        match goal with H : munch _ m9 m10 |- _ => rename H into MU10 end. match goal with H : wmono ctasegs m9 m10 |- _ => rename H into WM10 end.
        match goal with H : mem_inv ctasegs m10 |- _ => rename H into MI10 end. match goal with H : rw_cells ctasegs m10 OUT _ |- _ => rename H into HO10 end.
        assert (ST10 : stk ctasegs m10 lo spa) by (first [assumption| eapply stk_transport; [exact ST9| exact MU10| exact WM10| cbn; clear; lia]]).
        assert (HEAP10 : @BnHeapA.AHEAP (push AR f 1) Σ4 OW2 LB2 m10).
        { eapply (@AH_frame (push AR f 1)); [exact HEAP9| exact MU10| exact WM10|].
          constructor; [right; right; exists bO; split; [exact OIN3| cbn; clear - OL OH; lia]| constructor]. }
        first [ match type of FRL with rw_cells _ m10 _ _ => idtac end
              | apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU10 WM10) in FRL; [| cbn; clear - OBC OH CEIL LO SPAL; lia] ].
        first [ match type of FRH with rw_cells _ m10 _ _ => idtac end
              | apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU10 WM10) in FRH; [| cbn; clear - OBC OH CEIL LO SPAL SPAH; lia] ].
        apply evt_done. change (Z_to_bv 64 2388876) with (wz AFI_EXIT).
        (* [comment removed for export] *)
        eapply (@frame_obj_close (push AR f 1)) in HEAP10; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
        eapply (@frame_obj_close (push AR f 1)) in HEAP10; [| left; reflexivity| unfold in_fr; cbn [blk_addr blk_size fst snd]; change (fs_size 1) with 128; clear; lia].
        eapply (@afi_epi_cps AR _) with (lo := lo) (LB := LB) (gj := gj) (hrest := []);
          [exact HEAP10| intros b Hb; exact (FRESH b (in_or_app _ _ _ (or_intror Hb)))| exact ST10| exact CEIL| clear - LO SPAL; lia
          | unfold USTACK_TOP; exact TOP| exact SPAL| exact SPAH| exact GSZ| exact SAVJ| exact MI10
          | exact FRL| exact FRH| reflexivity|].
        intros Σ5 m' HEAP' CR' LIVE' ST' MI' AG'.
        eapply (implAp_elim (k (Some pd)) Σ3 Σ5 Q _ X2 Φ2 D2); [| exact SAFE2| exact LINK2| rewrite LIVE', EL4; reflexivity].
        apply K; [intros Hin; apply Hp; rewrite map_app in Hin |- *; apply in_app_or in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right; cbn; right; right; exact Hin]|].
        thaw DJA. thaw DJD. thaw DJO. thaw G5.
        unfold i2d_octet_postA. do 16 eexists. exists m', AD. split; [reflexivity|].
        split; [exact MI'|]. split; [exact ST'|]. split; [exact HEAP'|]. split; [exact BR|].
        split; [rewrite CR'; unfold I2D_OCTET_COST_A; clear - CR1 CR2 CR3 CR4; lia|].
        split.
        -- (* [comment removed for export] *)
           assert (STEP : forall (P1 P2 : Z -> Prop) mA mB mC, agree_on P1 m mA -> agree_on P2 mA mB -> (forall a, P1 a -> P2 a) -> agree_on P1 mB mC -> agree_on P1 m mC).
           { intros P1 P2 mA mB mC H1 H2 HI H3. eapply agree_on_trans; [exact H1|]. eapply agree_on_trans; [eapply agree_on_mono; [exact H2| exact HI]| exact H3]. }
           eapply agree_on_trans; [eapply agree_on_mono; [exact AG05| intros a [Ha _]; exact Ha]|].
           eapply agree_on_trans.
           { eapply agree_on_mono; [exact AG7|]. intros a [Ha _]. apply (LIFT2 OW). destruct Ha as [Ha|[Ha|Ha]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exact Ha]. }
           eapply agree_on_trans.
           { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU8)|]. intros a [Ha _]. cbn [outside fst snd]. split; [| exact I].
             destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEIL LO; lia| |].
             - destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
             - pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
           eapply agree_on_trans.
           { eapply agree_on_mono; [exact AG9|]. intros a [Ha Hn]. split; [apply (LIFT2 OW2); destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exists b; split; [right; exact Hb| exact Hr]]|].
             cbn [outside fst snd]. split; [| split; [| exact I]].
             - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha BR4 CEIL LO; lia| |].
               + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr BR1 BR5 HLR LEN; lia.
               + pose proof (@AH_disjoint_gen (push AR f 1) _ _ _ _ _ _ HEAP7 (INC3 _ (INC2 _ Hb)) PDIN (NE _ (INC2 _ Hb))) as DJ.
                 destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, DJ. clear - Hr DJ. lia.
             - destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [clear - Ha G3 CEIL LO; lia| |].
               + destruct Ha as [(l & h & Hin & Hr) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; injection E as <- <-; clear - Hr G4; lia.
               + pose proof (FRESH b Hb) as O. unfold off_fr in O. change (fs_size 1) with 128 in O. destruct b as [[bq' bA'] bn']; cbn [blk_addr blk_size fst snd] in Hr, O. clear - Hr O. lia. }
           eapply agree_on_trans.
           { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU10)|]. intros a [_ Hn]. cbn [outside fst snd]. split; [clear - Hn; lia| exact I]. }
           eapply agree_on_mono; [exact AG'|]. intros a [Ha _].
           destruct Ha as [Ha|[Ha|(b & Hb & Hr)]]; [left; clear - Ha SPAH; unfold USTACK_TOP in *; lia| right; left; exact Ha| right; right; exists b; split; [| exact Hr]].
           apply in_app_or in Hb as [Hb|Hb]; apply in_or_app; [left; right; exact Hb| right; exact Hb].
        -- eapply rw_cells_agree; [exact AG'| exact HO10|]. intros xa Hxa. cbn in Hxa. right; right. exists bO. split; [| clear - Hxa OL OH; lia].
           destruct (in_app_or _ _ _ OIN) as [X0|X0]; apply in_or_app; [left; right; exact X0| right; exact X0].
Qed.

End WithRT.
