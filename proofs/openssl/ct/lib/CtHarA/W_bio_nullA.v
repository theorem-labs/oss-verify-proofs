(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog BnBase BnModel BnTree ApBase ApLogic ApPrim CtSizes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct RtCallA W_cryptoA UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtFrameA Require Import AFrameKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit Fr_ossl_crypto_new_ex_data_ex Fr_CRYPTO_free_ex_data W_ex_dataA W_ex_dataA2 W_bio_ctrl.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHarA Require Import HarStmtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtTimeA Require Import BTacX.                (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Local Ltac alia := unfold BnHeapA.ACEIL, SEGTOP_A, SHHI, SHLO, STACK_WIN, USTACK_TOP in *; lia.
Import ListNotations.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  end.

(* [comment removed for export] *)
Local Notation E_bn_tail := (E_BIO_new_239854 : uk_tail 0x237894 0x23769c).
Local Notation E_bnx_zalloc := (E_BIO_new_ex_239668 : uk_call 0x23769c 0x2376e8 0x1fcef0).
Local Notation E_bnx_ned := (E_BIO_new_ex_2396f4 : uk_call 0x23769c 0x23776c 0x1f9d68).
Local Notation E_bf_call := (E_BIO_free_23986c : uk_call 0x2378bc 0x2378d4 0x2378e4).
Local Notation E_bfi_fed := (E_BIO_free_int_2399cc : uk_call 0x2378e4 0x237a18 0x1fa524).
Local Notation E_bfi_free := (E_BIO_free_int_2399e0 : uk_call 0x2378e4 0x237a2c 0x1fd334).

(* [comment removed for export] *)
Definition bio_zero_cells : list cell :=
  [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0);
   C4 (wz 0); C4 (wz 0);
   C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)].
Lemma zero128_cells : forall m A,
  rw_cells ctasegs m A [CB (Z.to_nat 128) (repeat (Z_to_bv 8 0) (Z.to_nat 128))] -> rw_cells ctasegs m A bio_zero_cells.
Proof. intros m A H. eapply rw_cells_recast; [exact H| cbn; repeat split; reflexivity| unfold bio_zero_cells, MallocRep.wz; bytes_lit_eq| reflexivity]. Qed.

(* [comment removed for export] *)
Ltac uw_call_ag_tac m0 N UW AG FR :=
  lazymatch type of FR with
  | rw_cells _ ?mX _ ?cs =>
      let pre := eval cbn [List.removelast] in (List.removelast (List.removelast cs)) in
      lazymatch goal with
      | |- uw_chain _ _ ?f1 ?fp1 _ =>
          eapply (uw_call m0 mX f1 fp1 N pre);
            [exact UW | exact AG | reflexivity | | | | apply bv_unsigned_in_range | rewrite !Z_to_bv_bv_unsigned; exact FR]
      end
  end.

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma null_meth_img2 : forall Σ OW LB m, AHEAP Σ OW LB m ->
  ro_cells ctasegs m (NULL_METHOD + 72) [C8 (Z_to_bv 64 0)] /\ ro_cells ctasegs m (NULL_METHOD + 80) [C8 (Z_to_bv 64 0)]
  /\ acc ctasegs m NULL_METHOD 112.
Proof.
  intros Σ OW LB m H. pose proof (AH_art _ _ _ _ H) as HA. split; [| split].
  - apply (relro_ro_cells m (NULL_METHOD + 72) _ (af_relro RT AF Σ m HA)); [cbn; auto| unfold RELRO_LO, NULL_METHOD; lia| unfold RELRO_HI, NULL_METHOD; cbn; lia| vm_compute; reflexivity].
  - apply (relro_ro_cells m (NULL_METHOD + 80) _ (af_relro RT AF Σ m HA)); [cbn; auto| unfold RELRO_LO, NULL_METHOD; lia| unfold RELRO_HI, NULL_METHOD; cbn; lia| vm_compute; reflexivity].
  - exact (proj2 (null_meth_img _ _ _ _ H)).
Qed.

(* [comment removed for export] *)
Lemma lib_off_fresh : forall Σ OW LB m0 (p : bptr) A n a,
  AHEAP Σ ((p, A, n) :: OW) LB m0 -> ~ In p (map blk_id (OW ++ LB)) -> lib_addr OW a -> ~ (A <= a < A + n).
Proof.
  intros Σ OW LB m0 p A n a HEAP Hp Ha.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _ & _). unfold SEGTOP_A in C1.
  pose proof (AH_range_gen _ _ _ _ (p, A, n) HEAP (or_introl eq_refl)) as (P0 & _ & _ & P3 & P4). cbn [blk_addr blk_size fst snd] in P0, P3, P4.
  destruct Ha as [Hs|(b & Hb & Hr)].
  - unfold LIBW_S in Hs. cbn [rin_ivs fst snd] in Hs. unfold BnHeapA.ACEIL in *. lia.
  - assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; apply in_or_app; left; exact Hb).
    pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) HEAP ltac:(right; apply in_or_app; left; exact Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia.
Qed.

(* [comment removed for export] *)
Lemma lib_agree_munch_fresh : forall Σ OW LB m0 (p : bptr) A n m m' W,
  AHEAP Σ ((p, A, n) :: OW) LB m0 -> ~ In p (map blk_id (OW ++ LB)) -> munch W m m' ->
  Forall (fun iv => ACEIL <= fst iv \/ (A <= fst iv /\ snd iv <= A + n)) W ->
  agree_on (lib_addr OW) m m'.
Proof.
  intros Σ OW LB m0 p A n m m' W HEAP Hp MU HW. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a Ha. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _ & _). unfold SEGTOP_A in C1. clear MU.
  pose proof (AH_range_gen _ _ _ _ (p, A, n) HEAP (or_introl eq_refl)) as (P0 & _ & _ & P3 & P4). cbn [blk_addr blk_size fst snd] in P0, P3, P4.
  induction HW as [|[u v] W H1 HW IH]; [exact I|]. cbn [outside fst snd] in *. split; [|exact IH]. clear IH HW.
  destruct Ha as [Hs|(b & Hb & Hr)].
  - unfold LIBW_S in Hs. cbn [rin_ivs fst snd] in Hs. unfold BnHeapA.ACEIL in *. lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(right; apply in_or_app; left; exact Hb)) as (_ & _ & _ & B3 & _).
    destruct H1 as [H1|[H1 H2]]; [unfold BnHeapA.ACEIL in *; lia|].
    assert (NE : blk_id b <> p) by (intros E; apply Hp; rewrite <- E; apply in_map; apply in_or_app; left; exact Hb).
    pose proof (AH_disjoint_gen _ _ _ _ b (p, A, n) HEAP ltac:(right; apply in_or_app; left; exact Hb) (or_introl eq_refl) NE) as DJ. cbn in DJ. lia.
Qed.

(* [comment removed for export] *)
Lemma lib_agree_munch_stack : forall Σ OW LB m0 m m' W,
  AHEAP Σ OW LB m0 -> munch W m m' -> Forall (fun iv => ACEIL <= fst iv) W -> agree_on (lib_addr OW) m m'.
Proof.
  intros Σ OW LB m0 m m' W HEAP MU HW. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|].
  intros a Ha. pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & _ & _). unfold SEGTOP_A in C1. clear MU.
  induction HW as [|[u v] W H1 HW IH]; [exact I|]. cbn [outside fst snd] in *. split; [|exact IH]. clear IH HW.
  destruct Ha as [Hs|(b & Hb & Hr)].
  - unfold LIBW_S in Hs. cbn [rin_ivs fst snd] in Hs. unfold BnHeapA.ACEIL in *. lia.
  - pose proof (AH_range_gen _ _ _ _ b HEAP ltac:(apply in_or_app; left; exact Hb)) as (_ & _ & _ & B3 & _). unfold BnHeapA.ACEIL in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem BIO_new_null_walkA : BIO_new_null_specA.
Proof.
  intros X. intros until Q. intros HEAP ST CEIL LO SPT SP16 MI -> FLEN CRED SF HXL HXIN UW CTX -> K.
  unfold BIO_NEW_NULL_STACK_A, NEW_EX_DATA_STACK_A, CNED_FRAME, CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK, BIO_NEW_NULL_COST_A, BIO_NEW_A, BIO_SIZE, SZ_BIO, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (bv_unsigned_in_range 64 s0) as S0R.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HXIN' : In (p_xl E, e_xl E, 40) (OW ++ LB)) by (apply in_or_app; left; exact HXIN).
  pose proof CEIL as CEILP. unfold BnHeapA.ACEIL in CEILP.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  pose proof (proj1 SF) as CS.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 6 zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  (* [comment removed for export] *)
  carve_frame 64%nat ST. do 9 zstep. zstep. zstep. do 4 zstep. zstep.
  name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; clear - SPR LO LO0; lia).
  assert (WOK1 : Forall (@BnHeapA.aclient_write_ok AR (OW ++ LB)) [(bv_unsigned sp - 64, bv_unsigned sp)]%Z).
  { constructor; [left; cbn [fst snd]; unfold USTACK_TOP; clear - CEIL LO SPT; lia| constructor]. }
  pose proof (AH_frame _ _ _ _ m1 _ HEAP MU WM WOK1) as HEAP1.
  assert (AG1 : agree_on (aclient_addr (OW ++ LB) (bv_unsigned sp)) m m1).
  { eapply (stack_munch_agree Σ OW LB m m1 _ (bv_unsigned sp) HEAP MU). constructor; [cbn [fst snd]; clear - CEIL LO; lia | constructor]. }
  assert (AGL1 : agree_on (lib_addr OW) m m1).
  { eapply (lib_agree_munch_stack Σ OW LB m); [exact HEAP| exact MU| constructor; [cbn [fst snd]; clear - CEIL LO; lia| constructor]]. }
  pose proof (crypto_statics_agree' _ _ _ CS AGL1) as CS1.
  (* [comment removed for export] *)
  assert (AGS1 : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. cbn [outside fst snd]. clear - Ha. lia. }
  apply evt_done.
  eapply (CRYPTO_zalloc_walkAp) with (n := 128) (lo := lo) (OW := OW) (LB := LB);
    [exact HEAP1| rewrite ESP; exact ST| exact CEIL| rewrite ESP; unfold CRYPTO_ZALLOC_STACK, CRYPTO_MALLOC_STACK, RT_STACK; clear - LO; lia
    | rewrite ESP; unfold USTACK_TOP; clear - SPT; lia| rewrite ESP; uchk_open; clear - SP16 SPR LO LO0; Z.div_mod_to_equations; lia| exact MI| reflexivity| exact CS1| reflexivity
    | clear; lia| unfold mcost; cbn; exact (af_credit_nonneg RT AF Σ m1 (AH_art _ _ _ _ HEAP1))
    | rewrite ESP; uw_call_ag_tac m 64 UW AGS1 FR; [clear; lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia]
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bnx_zalloc (uk_ctx_tail _ _ _ E_bn_tail CTX))
    |].
  intros pb Σ2 ms2 Hpb PO.
  destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & A & -> & MI2 & ST2 & AG2 & CR2 & BR & HEAP2 & ACCA & BLK).
  unfold MallocRep.wz in *. rewrite ESP in ST2, AG2.
  rewrite (ret_pc_even 0x2376e8) by (clear; lia).
  pose proof BR as (A0 & A16 & _ & ACE & AIMG).
  assert (EA : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - A0 ACE C3; unfold BnHeapA.ACEIL in *; lia).
  apply zero128_cells in BLK. unfold bio_zero_cells, MallocRep.wz in BLK.
  (* [comment removed for export] *)
  apply (rw_cells_agree _ _ _ _ _ AG2) in FR; [| intros a Ha; left; cbn in Ha; unfold USTACK_TOP; clear - Ha SPT; lia].
  unfold exlock_free in HXL.
  apply (rw_cells_agree _ _ _ _ _ AG1) in HXL; [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG2) in HXL; [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [exact HXIN'| cbn; clear - Ha; lia]].
  pose proof (aclient_lib _ _ _ _ _ AG2) as AGL2.
  pose proof (ap_statics_fixed_agree _ _ _ _ SF (agree_on_trans _ _ _ _ AGL1 AGL2)) as SF2. clear SF.
  assert (AGS2 : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m m2).
  { eapply agree_on_trans; [exact AGS1|]. eapply agree_on_mono; [exact AG2|]. intros a Ha. left. clear - Ha. lia. }
  (* [comment removed for export] *)
  assert (INC1 : forall b : block, In b (OW ++ LB) -> In b (((pb, A, 128) :: OW) ++ LB)) by (intros b Hb; right; exact Hb).
  pose proof (AH_offsh _ _ _ _ (pb, A, 128) HEAP2 (or_introl eq_refl)) as OSHA. cbn [blk_addr blk_size fst snd] in OSHA.
  assert (NEX : pb <> p_xl E) by (intros EQ; apply Hpb; rewrite EQ; apply in_map_iff; exists (p_xl E, e_xl E, 40); split; [reflexivity| exact HXIN']).
  pose proof (AH_disjoint_gen _ _ _ _ (pb, A, 128) (p_xl E, e_xl E, 40) HEAP2 (or_introl eq_refl) (INC1 _ HXIN') NEX) as DJX. cbn [blk_addr blk_size blk_id fst snd] in DJX.
  destruct (AH_shb _ _ _ _ HEAP2) as [SHB1' SHB2'].
  clear MU WM WOK1 HEAP1 AGL1 CS1 SHB1 SHB2.
  pose proof (munch_refl [(A, A + 128)]%Z m2) as MU2. pose proof (wmono_refl ctasegs m2) as WM2.
  assert (OFF2 : offshW [(A, A + 128)]%Z) by (cbn [offshW]; revert OSHA; unfold SHLO, SHHI; clear; intros; lia).
  assert (HXLf : frozen (rw_cells ctasegs m2 (e_xl E) mutex_free_cells)) by exact HXL. clear HXL.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  zstep. if_cases KA; zify_cond KA; [exfalso; rewrite ?EA in KA; clear - KA A0; lia|]. clear KA.
  zstep.
  zstep.
  zstep.
  zstep. zstep. zstep.
  zstep. zstep. zstep.
  zstep. zstep. zstep. zstep. zstep.
  name_mem m3.
  match goal with H : munch _ m2 m3 |- _ => rename H into MU3 end. match goal with H : wmono ctasegs m2 m3 |- _ => rename H into WM3 end.
  match goal with H : stk ctasegs m3 lo _ |- _ => rename H into ST3 end. match goal with H : mem_inv ctasegs m3 |- _ => rename H into MI3 end.
  match goal with H : rw_cells ctasegs m3 A _ |- _ => rename H into BLK3 end.
  match goal with H : rw_cells ctasegs m3 (bv_unsigned sp + -64) _ |- _ => rename H into FR3 end.
  assert (WOK2 : Forall (@BnHeapA.aclient_write_ok AR (((pb, A, 128) :: OW) ++ LB)) [(A, A + 128)]%Z).
  { constructor; [right; right; exists (pb, A, 128); split; [left; reflexivity| cbn; clear; lia]| constructor]. }
  pose proof (AH_frame _ _ _ _ m3 _ HEAP2 MU3 WM3 WOK2) as HEAP3.
  assert (AGL3 : agree_on (lib_addr OW) m2 m3).
  { eapply (lib_agree_munch_fresh Σ2 OW LB m2 pb A 128); [exact HEAP2| exact Hpb| exact MU3| constructor; [right; cbn [fst snd]; clear; lia| constructor]]. }
  pose proof (ap_statics_fixed_agree _ _ _ _ SF2 AGL3) as SF3.
  assert (AGS3 : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m m3).
  { eapply agree_on_trans; [exact AGS2|]. eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU3)|].
    intros a Ha. cbn [outside fst snd]. clear - Ha ACE CEIL LO. unfold BnHeapA.ACEIL in *. lia. }
  unfold frozen in HXLf.
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU3)) in HXLf; [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha DJX; lia].
  (* [comment removed for export] *)
  lazymatch type of BLK3 with rw_cells _ _ _ ?cs =>
    lazymatch eval cbv in (firstn 18%nat cs) with ?cs1 =>
    lazymatch eval cbv in (skipn 18%nat cs) with ?cs2 =>
      change cs with (cs1 ++ cs2) in BLK3 end end end.
  apply rw_cells_app in BLK3. destruct BLK3 as [HB1 HAD]. cbn [cells_size csize Nat.add] in HAD. replace (A + Z.of_nat 112) with (A + 112) in HAD by reflexivity.
  apply evt_done. eapply implAp_step.
  { eapply (@CRYPTO_new_ex_data_cpsA AR UK BE) with (lo := lo) (E := E) (pb := pb) (bio := A);
      [exact HEAP3| rewrite ESP; exact ST3| exact CEIL| rewrite ESP; unfold NEW_EX_DATA_STACK_A, CNED_FRAME, RT_STACK; clear - LO; lia
      | rewrite ESP; unfold USTACK_TOP; clear - SPT; lia| rewrite ESP; uchk_open; clear - SP16 SPR LO LO0; Z.div_mod_to_equations; lia| exact MI3| reflexivity| exact FLEN
      | revert CRED CR2; unfold mcost; cbn; clear; intros; lia| exact SF3| unfold exlock_free; exact HXLf| right; exact HXIN| left; reflexivity| exact NEX| exact HAD
      | rewrite ESP; uw_call_ag_tac m 64 UW AGS3 FR3; [clear; lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia]
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bnx_ned (uk_ctx_tail _ _ _ E_bn_tail CTX))
      | reflexivity| reflexivity| reflexivity]. }
  clear HXLf SF2 AGL2 AGL3.
  intros Σ4 ms4 PO.
  destruct PO as (y0 & y1 & y2 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & HEAP4 & EL4 & CR4 & HAD4 & HXL4).
  rewrite ?ESP in ST4, AG4.
  rewrite (ret_pc_even 0x23776c) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG4) in FR3;
    [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT; lia| clear - Ha ACE CEIL LO; unfold BnHeapA.ACEIL in *; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG4) in HB1;
    [| intros a Ha; cbn in Ha; split; [right; right; exists (pb, A, 128); split; [left; reflexivity| cbn; clear - Ha; lia]| clear - Ha; lia]].
  (* [comment removed for export] *)
  unfold MallocRep.wz in HAD4.
  pose proof (proj2 (rw_cells_app m4 A _ _) (conj HB1 HAD4)) as HB. clear HB1 HAD4. cbn [app] in HB.
  pose proof (proj1 SF3) as CS3.
  assert (AGL4 : agree_on (lib_addr OW) m3 m4).
  { eapply agree_on_mono; [exact AG4|]. intros a Ha. split; [| exact (fun Hr => lib_off_fresh _ _ _ _ pb A 128 a HEAP2 Hpb Ha ltac:(clear - Hr; lia))].
    eapply acl_sub; [exact INC1| | exact (lib_addr_aclient OW LB (bv_unsigned sp) a Ha)]. clear; lia. }
  pose proof (ap_statics_fixed_agree _ _ _ _ SF3 AGL4) as SF4. pose proof (proj1 SF4) as CS4. clear SF3 CS3.
  destruct (null_meth_img2 _ _ _ _ HEAP4) as (HMC4 & _ & ACCM4).
  pose proof (munch_refl [(A, A + 128)]%Z m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4.
  assert (HINB : In (pb, A, 128) (((pb, A, 128) :: OW) ++ LB)) by (left; reflexivity).
  ablock HEAP4 HINB ACCB4 OFFB4.
  clear WM3 ST3 MI3 HEAP3.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  zstep. first [if_false| idtac].
  unfold NULL_METHOD in HMC4, ACCM4 |- *. change (5560992 + 72) with 5561064 in HMC4.
  zstep.
  zstep. first [if_true| idtac].
  (* [comment removed for export] *)
  zstep. zstep. zstep.
  zstep. do 8 zstep. release_frame FR3 ST4 (bv_unsigned sp). zstep.
  name_mem m5.
  match goal with H : munch _ m4 m5 |- _ => rename H into MU5 end. match goal with H : wmono ctasegs m4 m5 |- _ => rename H into WM5 end.
  match goal with H : rw_cells ctasegs m5 A _ |- _ => rename H into HB5 end.
  apply evt_done. apply (K pb Σ4 _ Hpb).
  unfold bio_null_postA, BIO_NEW_NULL_COST_A, BIO_SIZE, MallocRep.wz.
  do 16 eexists. exists m5, A. split; [reflexivity|].
  split; [assumption|]. split; [assumption|].
  assert (OFFA : forall a, aclient_addr (OW ++ LB) (bv_unsigned sp) a -> ~ (A <= a < A + 128)).
  { intros a Ha. eapply (acl_off_fresh Σ Σ2 OW LB m m2 (bv_unsigned sp) lo pb A 128 a HEAP HEAP2 Hpb CEIL); [clear - LO; lia| exact Ha]. }
  split.
  { assert (INC : forall b : block, In b (OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact Hb).
    eapply agree_on_trans; [exact AG1|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG2|]; intros a Ha; eapply acl_sub; [exact INC| | exact Ha]; clear; lia|].
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU3)|]; intros a Ha; cbn [outside fst snd]; split; [exact (OFFA a Ha)| exact I]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG4|]; intros a Ha; split; [eapply acl_sub; [exact INC1| | exact Ha]; clear; lia| pose proof (OFFA a Ha) as Hx; clear - Hx; lia]|].
    eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU5)|]. intros a Ha. cbn [outside fst snd]. split; [exact (OFFA a Ha)| exact I]. }
  split; [revert CR2 CR4; unfold mcost; cbn; clear; intros; lia|].
  split; [exact BR|].
  split.
  { eapply AH_frame; [exact HEAP4| exact MU5| exact WM5|]. constructor; [right; right; exists (pb, A, 128); split; [left; reflexivity| cbn; clear; lia]| constructor]. }
  split; [unfold bio_null_cells, bio_cells, MallocRep.wz; exact HB5|].
  unfold exlock_free. eapply rw_cells_agree; [apply (agree_on_of_munch_nw _ _ _ MU5)| exact HXL4|].
  intros a Ha. cbn in Ha. cbn [outside fst snd]. split; [clear - Ha DJX; lia| exact I].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem BIO_free_null_walkA : BIO_free_null_specA.
Proof.
  intros X. intros until Q. intros HEAP HBIN NXB ST CEIL LO SPT SP16 MI -> FLEN CRED SF HXL HXIN HB UW CTX -> K.
  unfold BIO_FREE_NULL_STACK_A, FREE_EX_DATA_STACK_A, CFED_FRAME, CRYPTO_FREE_STACK, RT_STACK, BIO_FREE_NULL_COST_A, BIO_FREE_A, BIO_SIZE, MUTEX_SIZE, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in C1, C2, C3. unfold USTACK_TOP in SPT.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (HXIN' : In (p_xl E, e_xl E, 40) (OW ++ LB)) by (apply in_or_app; left; exact HXIN).
  assert (HBIN' : In (pb, A, 128) (OW ++ LB)) by (apply in_or_app; left; exact HBIN).
  pose proof CEIL as CEILP. unfold BnHeapA.ACEIL in CEILP.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HBIN') as (BB0 & _ & _ & BB3 & BB4). cbn [blk_addr blk_size fst snd] in BB0, BB3, BB4.
  pose proof (AH_range_gen _ _ _ _ _ HEAP HXIN') as (XB0 & _ & _ & XB3 & XB4). cbn [blk_addr blk_size fst snd] in XB0, XB3, XB4.
  pose proof (proj1 (AH_okA _ _ _ _ _ _ _ HEAP HBIN)) as ALB.
  assert (NBX : pb <> p_xl E) by exact NXB.
  pose proof (AH_disjoint_gen _ _ _ _ (pb, A, 128) (p_xl E, e_xl E, 40) HEAP HBIN' HXIN' ltac:(cbn; clear - NXB; congruence)) as DJX. cbn [blk_addr blk_size fst snd] in DJX.
  destruct (AH_acc _ _ _ _ _ HEAP HBIN') as [_ ACCB]. cbn [blk_addr blk_size fst snd] in ACCB.
  pose proof (AH_offsh _ _ _ _ _ HEAP HBIN') as OSHB. cbn [blk_addr blk_size fst snd] in OSHB.
  destruct (null_meth_img2 _ _ _ _ HEAP) as (_ & HMD & ACCM). unfold NULL_METHOD in HMD, ACCM. change (5560992 + 80) with 5561072 in HMD.
  destruct (AH_shb _ _ _ _ HEAP) as [SHB1 SHB2].
  assert (ACCS : acc ctasegs m (bv_unsigned sp - 32) 32).
  { apply (af_acc_stack RT AF Σ m _ _ (AH_art _ _ _ _ HEAP)); [| unfold USTACK_TOP; clear - SPT; lia].
    rewrite (AH_sp0 _ _ _ _ HEAP). clear - CEILP LO. unfold STACK_WIN in *. lia. }
  assert (EB : bv_unsigned (Z_to_bv 64 A) = A) by (apply unsigned_lit; clear - BB0 BB3 C3; unfold BnHeapA.ACEIL in *; lia).
  assert (AMO : amo_aligned AW (Z_to_bv 64 (A + 88)) = true) by (apply amo_aligned_w_intro; [clear - BB0 BB3 C3; unfold BnHeapA.ACEIL in *; lia| clear - ALB; Z.div_mod_to_equations; lia]).
  unfold bio_cells, MallocRep.wz in HB. unfold NULL_METHOD in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 128)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
  assert (OFF : offshW [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 128)]%Z).
  { cbn [offshW]. split; [clear - CEILP LO C2 SPT CEIL; unfold SHLO, SHHI, BnHeapA.ACEIL, STACK_WIN in *; lia|]. split; [revert OSHB; unfold SHLO, SHHI; clear; intros; lia| exact I]. }
  assert (HXLf : frozen (exlock_free m E)) by exact HXL. clear HXL.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  carve_frame 32%nat ST. do 4 zstep. zstep. zstep.
  (* [comment removed for export] *)
  carve_frame 48%nat ST. do 7 zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?EB in K0; clear - K0 BB0; lia|]. clear K0.
  zstep.                                   (* [comment removed for export] *)
  zstep.                                   (* [comment removed for export] *)
  zstep.                                   (* [comment removed for export] *)
  zstep.
  (* [comment removed for export] *)
  match goal with H : rw_cells ctasegs _ A _ |- _ => rename H into HB0 end.
  lazymatch type of HB0 with context [C4 (Z_to_bv 64 (bv_unsigned ?XX))] => change (bv_unsigned XX) with 0%Z in HB0 end.
  rewrite (sx32_small 1) by (clear; lia).
  zstep. change (bv_swrap 32 (1 + -1)) with 0.   (* [comment removed for export] *)
  zstep.
  zstep. first [if_false| idtac].
  zstep.
  zstep.
  zstep. rewrite (sx32_small 0) by (clear; lia).
  zstep. first [if_false| idtac].
  (* [comment removed for export] *)
  zstep. zstep. first [if_false| idtac].
  zstep. zstep. first [if_true| idtac].
  zstep. zstep. if_cases KM; zify_cond KM; [exfalso; revert KM; clear; rewrite ?unsigned_lit by lia; lia|]. clear KM.
  zstep. zstep. first [if_true| idtac].
  name_mem m1.
  match goal with H : rw_cells ctasegs m1 (bv_unsigned sp + -32) _ |- _ => rename H into FRo end.
  match goal with H : rw_cells ctasegs m1 (bv_unsigned sp + -80) _ |- _ => rename H into FRi end.
  match goal with H : stk ctasegs m1 lo _ |- _ => rename H into ST1 end. match goal with H : mem_inv ctasegs m1 |- _ => rename H into MI1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (apply unsigned_lit; clear - SPR LO LO0; lia).
  assert (ESPo : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; clear - SPR LO LO0; lia).
  assert (WOK1 : Forall (@BnHeapA.aclient_write_ok AR (OW ++ LB)) [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 128)]%Z).
  { constructor; [left; cbn [fst snd]; unfold USTACK_TOP; clear - CEIL LO SPT; lia|].
    constructor; [right; right; exists (pb, A, 128); split; [exact HBIN'| cbn; clear; lia]| constructor]. }
  pose proof (AH_frame _ _ _ _ m1 _ HEAP MU WM WOK1) as HEAP1.
  (* [comment removed for export] *)
  assert (STW : forall a, lib_addr [] a -> outside [(bv_unsigned sp - 80, bv_unsigned sp); (A, A + 128)]%Z a).
  { intros a [Hs|(b & Hb & _)]; [| destruct Hb]. cbn [outside fst snd]. unfold LIBW_S in Hs. cbn [rin_ivs fst snd] in Hs.
    clear - Hs CEILP LO BB4 BB3 C1. unfold BnHeapA.ACEIL, STACK_WIN in *. split; [lia|]. split; [lia| exact I]. }
  assert (AGL1 : agree_on (lib_addr []) m m1) by (eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)| exact STW]).
  pose proof (ap_statics_fixed_agree _ _ _ _ SF AGL1) as SF1. pose proof (proj1 SF1) as CS1.
  unfold frozen, exlock_free in HXLf.
  apply (rw_cells_agree _ _ _ _ _ (agree_on_of_munch_nw _ _ _ MU)) in HXLf;
    [| intros a Ha; cbn in Ha; cbn [outside fst snd]; clear - Ha XB3 DJX CEILP LO; unfold BnHeapA.ACEIL, STACK_WIN in *; lia].
  (* [comment removed for export] *)
  assert (AGS1 : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m m1).
  { eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU)|]. intros a Ha. cbn [outside fst snd]. clear - Ha BB3 CEIL LO. unfold BnHeapA.ACEIL in *. lia. }
  assert (UWo : uw_chain USTACK_TOP m1 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { uw_call_ag_tac m 32 UW AGS1 FRo; [clear; lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia]. }
  assert (UWi : uw_chain USTACK_TOP m1 (bv_unsigned sp + -80) (bv_unsigned sp + -32) (0x2378d4 :: bv_unsigned ra :: ras)).
  { eapply (uw_call m1 m1 _ _ 48 [CB 8 _; C8 s3; C8 s2; C8 s1]);
      [exact UWo | apply agree_on_refl | reflexivity | clear; lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT LO LO0; lia
      | clear - SPR; lia | ]. rewrite !Z_to_bv_bv_unsigned. match goal with |- rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -80) by (clear; lia) end. exact FRi. }
  (* [comment removed for export] *)
  lazymatch type of HB0 with rw_cells _ _ _ ?cs =>
    lazymatch eval cbv in (firstn 18%nat cs) with ?cs1 =>
    lazymatch eval cbv in (skipn 18%nat cs) with ?cs2 =>
      change cs with (cs1 ++ cs2) in HB0 end end end.
  apply rw_cells_app in HB0. destruct HB0 as [HB1 HAD]. cbn [cells_size csize Nat.add] in HAD. replace (A + Z.of_nat 112) with (A + 112) in HAD by reflexivity.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  apply evt_done. eapply implAp_step.
  { eapply (@CRYPTO_free_ex_data_cpsA AR UK BE) with (lo := lo) (E := E) (pb := pb) (bio := A);
      [exact HEAP1| rewrite ESP; exact ST1| exact CEIL| rewrite ESP; unfold FREE_EX_DATA_STACK_A, CFED_FRAME, RT_STACK; clear - LO; lia
      | rewrite ESP; unfold USTACK_TOP; clear - SPT; lia| rewrite ESP; uchk_open; clear - SP16 SPR LO LO0; Z.div_mod_to_equations; lia| exact MI1| reflexivity| exact FLEN
      | clear - CRED; lia| exact SF1| unfold exlock_free; exact HXLf| exact HXIN| exact HBIN| clear - NXB; congruence| exact HAD
      | rewrite ESP, ESPo; exact UWi
      | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bfi_fed (uk_ctx_call _ _ _ _ E_bf_call CTX))
      | reflexivity| reflexivity| reflexivity]. }
  clear HXLf HAD.
  intros Σ4 ms4 PO.
  destruct PO as (y0 & y1 & y2 & z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & y3 & y4 & y5 & y6 & F4 & fc4 & m4 & -> & MI4 & ST4 & AG4 & HEAP4 & EL4 & CR4 & HAD4 & HXL4).
  rewrite ?ESP in ST4, AG4.
  rewrite (ret_pc_even 0x237a18) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG4) in FRo;
    [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT; lia| clear - Ha BB3 CEIL LO; unfold BnHeapA.ACEIL in *; lia]].
  apply (rw_cells_agree _ _ _ _ _ AG4) in FRi;
    [| intros a Ha; cbn in Ha; split; [left; unfold USTACK_TOP; clear - Ha SPT; lia| clear - Ha BB3 CEIL LO; unfold BnHeapA.ACEIL in *; lia]].
  assert (CS4 : crypto_statics m4).
  { eapply crypto_statics_agree; [exact AG4| | exact (proj1 SF1)].
    intros a Ha. assert (HS : client_static a) by (apply client_static_intro; revert Ha; unfold libw, LIBW_A; cbn [rin_ivs fst snd]; clear; intros; lia).
    split; [right; left; exact HS|].
    intros Hr. eapply (blk_not_static _ _ LB m (pb, A, 128) a HEAP HBIN); [cbn; clear - Hr; lia| exact HS]. }
  assert (AGS4 : agree_on (fun a => bv_unsigned sp <= a < USTACK_TOP) m m4).
  { eapply agree_on_trans; [exact AGS1|]. eapply agree_on_mono; [exact AG4|]. intros a Ha. split; [left; clear - Ha; lia| clear - Ha BB3 CEIL LO; unfold BnHeapA.ACEIL in *; lia]. }
  assert (UWo4 : uw_chain USTACK_TOP m4 (bv_unsigned sp + -32) (bv_unsigned sp) (bv_unsigned ra :: ras)).
  { uw_call_ag_tac m 32 UW AGS4 FRo; [clear; lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT; lia]. }
  assert (UWi4 : uw_chain USTACK_TOP m4 (bv_unsigned sp + -80) (bv_unsigned sp + -32) (0x2378d4 :: bv_unsigned ra :: ras)).
  { eapply (uw_call m4 m4 _ _ 48 [CB 8 _; C8 s3; C8 s2; C8 s1]);
      [exact UWo4 | apply agree_on_refl | reflexivity | clear; lia | uchk_open; clear - SP16 SPR; Z.div_mod_to_equations; lia | unfold USTACK_TOP; clear - SPT LO LO0; lia
      | clear - SPR; lia | ]. rewrite !Z_to_bv_bv_unsigned. match goal with |- rw_cells _ _ ?a _ => replace a with (bv_unsigned sp + -80) by (clear; lia) end. exact FRi. }
  pose proof (munch_refl ([] : list (Z * Z)) m4) as MU4. pose proof (wmono_refl ctasegs m4) as WM4.
  rename MU into MU1. clear WM HEAP1 WOK1.
  apply implAp_from_evt.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  match goal with H : stk ctasegs m4 lo _ |- _ => rename H into ST4' end.
  apply evt_done.
  eapply CRYPTO_free_walkAp with (lo := lo) (A := A) (n := 128);
    [exact HEAP4| exact HBIN| rewrite ESP; exact ST4'| exact CEIL| rewrite ESP; unfold CRYPTO_FREE_STACK, RT_STACK; clear - LO; lia
    | rewrite ESP; unfold USTACK_TOP; clear - SPT; lia| rewrite ESP; uchk_open; clear - SP16 SPR LO LO0; Z.div_mod_to_equations; lia| exact MI4| reflexivity| exact CS4| reflexivity
    | rewrite ESP, ESPo; exact UWi4
    | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_bfi_free (uk_ctx_call _ _ _ _ E_bf_call CTX))
    |].
  intros Σ5 ms5 PO.
  destruct PO as (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & F5 & fc5 & m5 & -> & MI5 & ST5 & AG5 & CR5 & HEAP5).
  rewrite ?ESP in ST5, AG5.
  rewrite (ret_pc_even 0x237a2c) by (clear; lia).
  apply (rw_cells_agree _ _ _ _ _ AG5) in FRo; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; clear - Ha SPT; lia].
  apply (rw_cells_agree _ _ _ _ _ AG5) in FRi; [| intros a Ha; cbn in Ha; left; unfold USTACK_TOP; clear - Ha SPT; lia].
  unfold exlock_free in HXL4.
  apply (rw_cells_agree _ _ _ _ _ AG5) in HXL4;
    [| intros a Ha; cbn in Ha; right; right; exists (p_xl E, e_xl E, 40); split; [apply lb_remove_In; split; [exact HXIN'| cbn; clear - NXB; congruence]| cbn; clear - Ha; lia]].
  pose proof (munch_refl ([] : list (Z * Z)) m5) as MU5. pose proof (wmono_refl ctasegs m5) as WM5.
  clear MU4 WM4.
  eapply implAp_evt with (P := bio_free_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E pb lo m Σ5);
    [| intros ms' PO'; exact (K Σ5 ms' PO')].
  (* [comment removed for export] *)
  zstep. zstep. do 6 zstep. release_frame FRi ST5 (bv_unsigned sp + -32). zstep.
  do 3 zstep. release_frame FRo ST5 (bv_unsigned sp). zstep.
  apply evt_done. unfold bio_free_postA, BIO_FREE_NULL_COST_A, MallocRep.wz.
  do 17 eexists. eexists. split; [reflexivity|].
  split; [exact MI5|]. split; [assumption|].
  split.
  { pose proof (AH_nodup _ _ _ _ HEAP) as ND.
    assert (INC3 : forall b : block, In b (lb_remove pb OW ++ LB) -> In b (OW ++ LB) /\ blk_id b <> blk_id (pb, A, 128)).
    { intros b Hb. apply in_app_iff in Hb. destruct Hb as [Hb|Hb].
      - apply lb_remove_In in Hb. destruct Hb as [Hb Hn]. split; [| exact Hn]. apply in_or_app. left. exact Hb.
      - split; [apply in_or_app; right; exact Hb| exact (ids_disj OW LB pb A 128 ND HBIN b Hb)]. }
    assert (INC2 : forall b : block, In b (lb_remove pb OW ++ LB) -> In b (OW ++ LB)) by (intros b Hb; exact (proj1 (INC3 b Hb))).
    eapply agree_on_trans; [eapply agree_on_mono; [apply (agree_on_of_munch_nw _ _ _ MU1)|]; intros a Ha;
                            eapply (acl_outside2 Σ OW LB m _ (bv_unsigned sp) lo 80 (pb, A, 128) a HEAP HBIN' INC3 CEIL); [clear - LO; lia| clear; lia| exact Ha]|].
    eapply agree_on_trans; [eapply agree_on_mono; [exact AG4|]; intros a Ha; split; [eapply acl_sub; [exact INC2| | exact Ha]; clear; lia|];
                            pose proof (acl_off_block Σ OW LB m _ (bv_unsigned sp) lo (pb, A, 128) a HEAP HBIN' INC3 CEIL ltac:(clear - LO; lia) Ha) as Hx;
                            cbn [blk_addr blk_size fst snd] in Hx; clear - Hx; lia|].
    eapply agree_on_mono; [exact AG5|]. intros a Ha. eapply acl_sub; [| | exact Ha]; [| clear; lia].
    intros b Hb. apply (lb_remove_app_l pb); [| exact Hb]. intros b' Hb'. exact (ids_disj OW LB pb A 128 ND HBIN b' Hb'). }
  split; [clear - CR4 CR5; lia|].
  split; [exact HEAP5|].
  unfold exlock_free. exact HXL4.
Qed.
End WithRT.
