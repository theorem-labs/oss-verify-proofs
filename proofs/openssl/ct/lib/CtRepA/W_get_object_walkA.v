(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem RzCPS. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog BnBase BnModel BnTree ApBase ApState ApLogic ApInv ApErr ApParse.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit D_defs D_cs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require Import BnKit BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnTac BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit AsLoop.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import R_unwind_chain.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import RT_iface2 LibKitA ARun BnHeapA BnRepDefs BnRepA ImplA ImplAX BnIfaceA AsStruct UnwindA EdgesA UnwindX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require Import ApCells.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepP Require W_get_object W_get_object_walk.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApUTacB.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepA Require Import ApATac ApATacX ApBImg ApWalkTac ApRepDefs ApRep ApIface ApFrame W_akit W_get_objectA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac step := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := apre; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
(* [comment removed for export] *)
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Notation sbyte := CtRepP.W_get_object_walk.sbyte.
Import CtRepP.W_get_object(land_32_cases, land_192_cases, go_ret_cases, go_cls_cases, tag_loop_len, lor_le_add, go_tag_range).
Import CtRepP.W_get_object_walk(byte_lit, sxb_byte, sbyte_land255, sbyte_signed, land127_mod, land_split_255, land128_iff, land128_cases, sbyte_wrap_lt,
                                 shl56_sign, zext32_idem, get_length_len_max, ret_or_128, IM128, signed_small, zxb_lit, znth_range).

(* [comment removed for export] *)
Lemma payload_readA : forall m D d i a, bytes_at ctasegs m D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d ->
  0 <= i < zlength d -> a = wa (D + i) -> ov_read_bytes ctasegs m a 1 = Some [Z_to_bv 8 (znth d i)].
Proof.
  intros m D d i a HB HF Hi ->.
  assert (HN : nth_error (to_bytes d) (Z.to_nat i) = Some (Z_to_bv 8 (znth d i))).
  { unfold to_bytes. rewrite nth_error_map. unfold znth. destruct (Z.ltb_spec i 0); [lia|].
    destruct (nth_error d (Z.to_nat i)) as [c|] eqn:E; cbn.
    - rewrite (nth_error_nth _ _ _ E). reflexivity.
    - apply nth_error_None in E. unfold zlength in Hi. lia. }
  exact (u8ro_read ctasegs m D (to_bytes d) i _ _ HB HN ltac:(lia) eq_refl).
Qed.

Lemma rw_cells_CB_ofA : forall m A cs, rw_cells ctasegs m A cs -> rw_cells ctasegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [| exact I]. apply cells_bytes_length. exact W.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
Qed.

(* [comment removed for export] *)
Lemma lor_mul_addB : forall a r k, 0 <= a -> 0 <= k -> 0 <= r < 2 ^ k -> Z.lor (a * 2 ^ k) r = a * 2 ^ k + r.
Proof.
  intros a r k Ha Hk Hr.
  assert (NC : Z.land (a * 2 ^ k) r = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [L|L]; [rewrite (Z.mul_pow2_bits_low a k n) by lia; reflexivity|].
    destruct (Z.eq_dec r 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    rewrite (Z.bits_above_log2 r n); [apply Bool.andb_false_r|lia|]. apply (Z.lt_le_trans _ k); [apply Z.log2_lt_pow2; lia|lia]. }
  rewrite <- Z.lxor_lor by exact NC. symmetry. apply Z.add_nocarry_lxor. exact NC.
Qed.

(* [comment removed for export] *)
Local Notation E_new1 := (E_ASN1_get_object_221f14 : uk_call 0x223b30 0x223cf8 0x1fd52c).
Local Notation E_dbg1 := (E_ASN1_get_object_221f2c : uk_call 0x223b30 0x223d10 0x1fd844).
Local Notation E_err1 := (E_ASN1_get_object_221f3c : uk_call 0x223b30 0x223d20 0x1fdab8).
Local Notation E_new2 := (E_ASN1_get_object_221e9c : uk_call 0x223b30 0x223db4 0x1fd52c).
Local Notation E_dbg2 := (E_ASN1_get_object_221eb4 : uk_call 0x223b30 0x223dcc 0x1fd844).
Local Notation E_err2 := (E_ASN1_get_object_221ec4 : uk_call 0x223b30 0x223ddc 0x1fdab8).

Section WithRT.
Context {AR : ARun} {UK : UnwindKit} {BE : BnEdges}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation PMc := (@ar_PMc AR).
Local Notation FR := (@ar_FR AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Section Proofs.
  (* [comment removed for export] *)
  Hypothesis HE2 : ERR_new_specA_bo.
  Hypothesis HE3 : forall rs, rs_flen rs = 23 -> rs_fnlen rs = 16 -> ERR_set_debug_specA_bo rs A_ASN1_LIB_C_A A_ASN1_GET_OBJECT_FN_A.
  Hypothesis HE4 : forall rs lib reason, ERR_set_error_specA rs lib reason.

  Section Act.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (Σ : rts RT) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo : Z) (K : list block).
  Variables (D : Z) (d : list Z) (op omax PP PL PT PC : Z) (jl j2 j3 : list byte).
  Variable ras : list Z.   (* [comment removed for export] *)
  Hypothesis PRE : ap_preA Σ st m OW LB E bo sp lo GETOBJ_STACK_A GETOBJ_ERR_COST_A GETOBJ_FRAMES_A.
  Hypothesis TP : tp = wz TP_A.
  Hypothesis UW : uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) ras.
  Hypothesis CTX : uk_ctx ASN1_GET_OBJECT_A (bv_unsigned ra :: ras).
  Hypothesis NE : ras <> nil.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_okA m LB D d.
  Hypothesis OP0 : 0 <= op.
  Hypothesis OM0 : 0 < omax.
  Hypothesis OPM : op + omax <= zlength d.
  Hypothesis CELLS : go_cellsA_ok LB PP PL PT PC.
  Hypothesis CELLSD : go_cells_offA D (zlength d) PP PL PT PC.
  Hypothesis HPP : rw_cells ctasegs m PP [C8 (wz (D + op))].
  Hypothesis HPL : rw_cells ctasegs m PL [CB 8 jl].
  Hypothesis HPT : rw_cells ctasegs m PT [CB 4 j2].
  Hypothesis HPC : rw_cells ctasegs m PC [CB 4 j3].

  Let g : go_res := get_object d op omax.
  Local Notation b0 := (znth d op).
  (* [comment removed for export] *)
  Definition go_frameA : list cell := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Local Notation W0 := ([(bv_unsigned sp - 64, bv_unsigned sp); (PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)]%Z) (only parsing).

  (* [comment removed for export] *)
  Lemma ctx_factsA :
    Forall (fun c => 0 <= c < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 26
    /\ 12365824 <= ACEIL /\ 17594333495296 <= ACEIL /\ ACEIL + 8388608 <= 140737488355328
    /\ ACEIL <= lo /\ 12365824 <= lo /\ lo <= bv_unsigned sp - (64 + ERR_SET_ERROR_STACK) /\ 0 <= ERR_SET_ERROR_STACK
    /\ bv_unsigned sp + 16 <= USTACK_TOP /\ 0 <= bv_unsigned sp < 2 ^ 64 /\ bv_unsigned sp mod 16 = 0
    /\ Z.of_nat (length (to_bytes d)) = zlength d
    /\ (exists bd, In bd (OW ++ LB) /\ blk_addr bd <= D /\ D + zlength d <= blk_addr bd + blk_size bd /\ 0 < blk_addr bd /\ blk_addr bd + blk_size bd <= ACEIL
                   /\ (blk_addr bd + blk_size bd <= SHLO \/ SHHI <= blk_addr bd))
    /\ (forall A n, cellA_in LB A n -> exists b, In b (OW ++ LB) /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b /\ 0 < blk_addr b
                   /\ blk_addr b + blk_size b <= ACEIL /\ (blk_addr b + blk_size b <= SHLO \/ SHHI <= blk_addr b)
                   /\ In b LB /\ (blk_addr b + blk_size b <= 0x10000 \/ SEGTOP_A <= blk_addr b))
    /\ offshW W0.
  Proof.
    destruct PRE as (HEAP & AS & IDS & DC & ST & CEIL & LOSP & TOP & AL16 & MI & CRED & FRM).
    destruct PAY as (_ & DF & D0 & D63 & D26 & HB).
    pose proof (AH_ceil _ _ _ _ HEAP) as (C1 & C2 & C3). unfold SEGTOP_A, STACK_WIN, SHHI, USTACK_TOP in C1, C2, C3.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold GETOBJ_STACK_A in LOSP.
    assert (ESS : 0 <= ERR_SET_ERROR_STACK) by (unfold ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK; clear; lia).
    assert (CELL : forall A n, cellA_in LB A n -> exists b, In b (OW ++ LB) /\ blk_addr b <= A /\ A + n <= blk_addr b + blk_size b /\ 0 < blk_addr b
                   /\ blk_addr b + blk_size b <= BnHeapA.ACEIL /\ (blk_addr b + blk_size b <= SHLO \/ SHHI <= blk_addr b)
                   /\ In b LB /\ (blk_addr b + blk_size b <= 0x10000 \/ SEGTOP_A <= blk_addr b)).
    { intros A n (b & Hb & H1 & H2). assert (Hb' : In b (OW ++ LB)) by (apply in_or_app; right; exact Hb).
      pose proof (AH_range_gen _ _ _ _ _ HEAP Hb') as (R0 & _ & _ & R3 & R4). pose proof (AH_offsh _ _ _ _ _ HEAP Hb') as RO.
      exists b. repeat (split; [assumption|]). exact R4. }
    repeat (split; [first [assumption | lia] |]).
    split; [unfold to_bytes, zlength; rewrite length_map; reflexivity|].
    split.
    { destruct HB as [->|(b & Hb & H1 & H2)]; [unfold zlength in OPM; cbn in OPM; lia|].
      destruct (CELL D (zlength d) ltac:(exists b; auto)) as (b' & Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & _). exists b'. repeat (split; [assumption|]). exact Q6. }
    split; [exact CELL|].
    destruct CELLS as (Q1 & Q2 & Q3 & Q4 & _). apply CELL in Q1, Q2, Q3, Q4.
    destruct Q1 as (b1 & _ & X1 & Y1 & _ & _ & O1 & _). destruct Q2 as (b2 & _ & X2 & Y2 & _ & _ & O2 & _).
    destruct Q3 as (b3 & _ & X3 & Y3 & _ & _ & O3 & _). destruct Q4 as (b4 & _ & X4 & Y4 & _ & _ & O4 & _).
    cbn [offshW fst snd]. unfold SHLO, SHHI, BnHeapA.ACEIL in *. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Definition go_invA (m1 : mem) (j64 : list byte) (cpl cpt cpc : list cell) : Prop :=
    munch W0 m m1 /\ wmono ctasegs m m1 /\ mem_inv ctasegs m1 /\ stk ctasegs m1 lo (bv_unsigned sp + -64)
    /\ rw_cells ctasegs m1 (bv_unsigned sp + -64) (CB 8 j64 :: go_frameA)
    /\ rw_cells ctasegs m1 PP [C8 (Z_to_bv 64 (D + op))] /\ rw_cells ctasegs m1 PL cpl /\ rw_cells ctasegs m1 PT cpt /\ rw_cells ctasegs m1 PC cpc
    /\ bytes_at ctasegs m1 D (to_bytes d).

  (* [comment removed for export] *)
  Lemma acc_factsA : exists Db nD, acc ctasegs m Db nD /\ Db <= D /\ D + zlength d <= Db + nD /\ 0 < Db /\ Db + nD <= ACEIL
                     /\ acc ctasegs m PP 8 /\ acc ctasegs m PL 8 /\ acc ctasegs m PT 4 /\ acc ctasegs m PC 4
                     /\ 0 < PP /\ PP + 8 <= ACEIL /\ 0 < PL /\ PL + 8 <= ACEIL /\ 0 < PT /\ PT + 4 <= ACEIL /\ 0 < PC /\ PC + 4 <= ACEIL.
  Proof.
    destruct PRE as (HEAP & _). destruct ctx_factsA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (bd & Hbd & B1 & B2 & B3 & B4 & _) & CELL & _).
    destruct CELLS as (Q1 & Q2 & Q3 & Q4 & _).
    assert (ACCC : forall A n, cellA_in LB A n -> acc ctasegs m A n /\ 0 < A /\ A + n <= BnHeapA.ACEIL).
    { intros A n Q. destruct (CELL A n Q) as (b & Hb & H1 & H2 & H3 & H4 & _). split; [| lia]. eapply acc_sub; [exact (proj2 (AH_acc _ _ _ _ _ HEAP Hb))| exact H1| exact H2]. }
    exists (blk_addr bd), (blk_size bd). split; [exact (proj2 (AH_acc _ _ _ _ _ HEAP Hbd))|]. repeat (split; [assumption|]).
    destruct (ACCC _ _ Q1) as (A1 & R1 & S1). destruct (ACCC _ _ Q2) as (A2 & R2 & S2). destruct (ACCC _ _ Q3) as (A3 & R3 & S3). destruct (ACCC _ _ Q4) as (A4 & R4 & S4).
    repeat (split; [assumption|]). exact S4.
  Qed.

  Local Ltac go_unpack GI := destruct GI as (MU & WM & MI & ST & FRc & CPP & CPL & CPT & CPC & HB); unfold go_frameA in FRc.
  Local Ltac ctx := pose proof ctx_factsA as (DF & D0 & D63 & D26 & CL1 & CL2 & CL3 & CEIL & GLO & LO & ESS & TOP & SPR & AL16 & DLEN & BD & CELL & OFFW);
                   pose proof acc_factsA as (Db & nD & ACCD & DB1 & DB2 & DB3 & DB4 & ACCP & ACCL & ACCT & ACCC & PPlo & PPhi & PLlo & PLhi & PTlo & PThi & PClo & PChi);
                   pose proof CELLS as (CI1 & CI2 & CI3 & CI4 & AL1 & AL2 & AL3 & AL4 & C12 & C13 & C14 & C23 & C24 & C34);
                   pose proof CELLSD as (PD1 & PD2 & PD3 & PD4);
                   hide C12; hide C13; hide C14; hide C23; hide C24; hide C34; hide PD1; hide PD2; hide PD3; hide PD4.
  Local Ltac unhide6 := unfold hidden in *.

  Local Notation SHPP := (Z_to_bv 64 (Z.shiftr PP 3 + SHB)).
  Local Ltac gi_split MU WM MI ST FRc CPP CPL CPT CPC HB :=
    split; [exact MU|split; [exact WM|split; [exact MI|split; [exact ST|split; [exact FRc|split; [exact CPP|split; [exact CPL|split; [exact CPT|split; [exact CPC|exact HB]]]]]]]]].

  (* [comment removed for export] *)
  Lemma minus1_unsignedB : bv_unsigned (Z_to_bv 64 (-1)) = 18446744073709551615.
  Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma tag_loop_simA : forall fuel (len q max : Z) (x19 x20 x28 x30 x31 : word) m1 j64 cpl cpt cpc (POST : machine_state -> Prop),
    go_invA m1 j64 cpl cpt cpc ->
    bv_unsigned x28 = INT_MAX / 128 ->
    op + 1 <= q -> 1 <= max -> q + max = op + omax -> fuel = Z.to_nat max -> 0 <= len <= INT_MAX / 128 -> 128 <= znth d q ->
    (forall len' q' max' (x19' x20' x28' x30' x31' : word), tag_loop fuel d len q max = Some (len', q', max') ->
       Z.land (znth d q') 128 = 0 -> op + 1 <= q' -> 1 <= max' -> q' + max' = op + omax -> 0 <= len' <= INT_MAX / 128 ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 (max' - 1)) (Z_to_bv 64 len') sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (D + q' + 1)) (Z_to_bv 64 (D + q')) (Z_to_bv 64 SHB)
                  SHPP x19' x20' s5 s6 s7 s8 s9 s10 s11 x28' (Z_to_bv 64 (znth d q')) x30' x31')
             F (Z_to_bv 64 0x223d38) fc None m1 (seg_rom ctasegs))) ->
    (forall (x6 x7 x15 x16' x17 x19' x20' x28' x29' x30' x31' : word), tag_loop fuel d len q max = None ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) (Z_to_bv 64 (znth d op)) x6 x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) x15 x16' x17
                  SHPP x19' x20' s5 s6 s7 s8 s9 s10 s11 x28' x29' x30' x31')
             F (Z_to_bv 64 0x223db0) fc None m1 (seg_rom ctasegs))) ->
    evt ctasegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 (max - 1)) (Z_to_bv 64 len) sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (D + q + 1)) (Z_to_bv 64 (D + q)) (Z_to_bv 64 SHB)
               SHPP x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 (Z_to_bv 64 (znth d q)) x30 x31)
          F (Z_to_bv 64 0x223bd8) fc None m1 (seg_rom ctasegs)).
  Proof.
    induction fuel as [|fuel IH]; intros until POST; intros GI X28 Hq Hmax Hqm Hf Hlen B7 KEX KERR; [exfalso; lia|].
    rewrite ?IM128 in *.
    go_unpack GI. ctx. rewrite <- (Z_to_bv_bv_unsigned x28), X28.
    pose proof (znth_range d q DF) as BQ.
    cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub Z.add INT_MAX] in KEX, KERR.
    destruct (land128_cases (znth d q) BQ) as [(X & _ & _)|(_ & L128 & L127)]; [exfalso; lia|].
    rewrite L128 in KEX, KERR. cbn [Z.eqb] in KEX, KERR.
    (* [comment removed for export] *)
    step. if_cases KM; zc KM.
    - eapply KERR. rewrite (proj2 (Z.eqb_eq (max - 1) 0)) by lia. reflexivity.
    - rewrite (proj2 (Z.eqb_neq (max - 1) 0)) in KEX, KERR by lia.
      set (len' := Z.lor (Z.shiftl len 7) (Z.land (znth d q) 127)) in KEX, KERR.
      assert (SL : Z.shiftl len 7 = len * 2 ^ 7) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      assert (L127R : 0 <= Z.land (znth d q) 127 < 2 ^ 7) by (rewrite L127; lia).
      assert (LR : len' = len * 128 + Z.land (znth d q) 127).
      { subst len'. rewrite SL, (lor_mul_addB len (Z.land (znth d q) 127) 7) by lia. reflexivity. }
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit len) by lia. step. rewrite (unsigned_lit (znth d q)) by lia. step. step. rewrite !unsigned_lit by lia. fold len'. step. step.
      step. if_cases KO; zc KO.
      + rewrite ?unsigned_lit, ?signed_small in KO by lia. rewrite ?IM128 in KEX, KERR. rewrite (proj2 (Z.ltb_ge _ len')) in KEX, KERR by lia.
        (* [comment removed for export] *)
        pose proof (znth_range d (q + 1) DF) as BQ1.
        pose proof (payload_readA m1 D d (q + 1) (wa (D + q + 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
        rewrite (sxb_byte (znth d (q + 1))) by lia.
        step. rewrite (sbyte_land255 (znth d (q + 1))) by lia.
        (* [comment removed for export] *)
        step. if_cases KB; zc KB.
        * (* [comment removed for export] *)
          assert (KB' : znth d (q + 1) < 128) by (apply (sbyte_wrap_lt _ BQ1); lia).
          pose proof (proj1 (land128_iff _ BQ1) KB') as L0.
          replace (D + q + 2) with (D + (q + 1) + 1) by lia. replace (D + q + 1) with (D + (q + 1)) by lia. replace (max - 1 + -1) with (max - 1 - 1) by lia.
          eapply (KEX len' (q + 1) (max - 1)); [|exact L0|lia|lia|lia|lia].
          destruct fuel as [|fuel']; [exfalso; lia|]. cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub Z.add INT_MAX]. rewrite L0. reflexivity.
        * (* [comment removed for export] *)
          assert (KB' : 128 <= znth d (q + 1)) by (destruct (Z.lt_ge_cases (znth d (q + 1)) 128) as [Hl|Hl]; [exfalso; pose proof (proj2 (sbyte_wrap_lt _ BQ1) Hl); lia|exact Hl]).
          replace (D + q + 2) with (D + (q + 1) + 1) by lia. replace (D + q + 1) with (D + (q + 1)) by lia. replace (max - 1 + -1) with (max - 1 - 1) by lia.
          eapply (IH len' (q + 1) (max - 1)); [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|reflexivity|lia|lia|lia|lia|lia|exact KB'| |].
          -- intros len2 q2 max2 x19' x20' x28' x30' x31' HT. eapply KEX. exact HT.
          -- intros x6' x7' x15' x16' x17' x19' x20' x28' x29' x30' x31' HT. eapply KERR. exact HT.
      + rewrite ?unsigned_lit, ?signed_small in KO by lia. step. eapply KERR. subst len'. rewrite (proj2 (Z.ltb_lt _ _)) by (rewrite ?IM128; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition at_errA (POST : machine_state -> Prop) : Prop :=
    forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31 : word) m1 j64 cpl cpt cpc, go_invA m1 j64 cpl cpt cpc ->
      cells_size cpl = 8%nat -> cells_size cpt = 4%nat -> cells_size cpc = 4%nat ->
      evt ctasegs POST
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 PP) x10 x11 x12 x13 x14 x15 x16 x17 SHPP x19 x20 x21
                 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x223db0) fc None m1 (seg_rom ctasegs)).

  (* [comment removed for export] *)
  Lemma tag_finA : forall len' q' max' (x19 x20 x28 x30 x31 : word) m1 j64 (POST : machine_state -> Prop),
    go_invA m1 j64 [CB 8 jl] [CB 4 j2] [CB 4 j3] ->
    op + 1 <= q' -> 1 <= max' -> q' + max' = op + omax -> 0 <= len' <= INT_MAX / 128 -> znth d q' < 128 -> Z.land (znth d op) 31 = 31 ->
    tag_loop (Z.to_nat (omax - 1)) d 0 (op + 1) (omax - 1) = Some (len', q', max') ->
    (forall tag p1 max1 (x7 x15 x19 x20 x28 x29 x30 x31 : word) m1 j64,
       go_hdr d op omax = Some (tag, p1, max1) -> op + 1 <= p1 -> 1 <= max1 -> max1 = omax - (p1 - op) -> 0 <= tag <= INT_MAX ->
       go_invA m1 j64 [CB 8 jl] [CB 4 j2] [CB 4 j3] -> x15 = Z_to_bv 64 (D + p1) ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max1) x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) x15 (Z_to_bv 64 tag) (Z_to_bv 64 SHB)
                  SHPP x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x223c40) fc None m1 (seg_rom ctasegs))) ->
    (go_hdr d op omax = None -> at_errA POST) ->
    evt ctasegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 (max' - 1)) (Z_to_bv 64 len') sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (D + q' + 1)) (Z_to_bv 64 (D + q')) (Z_to_bv 64 SHB)
               SHPP x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 (Z_to_bv 64 (znth d q')) x30 x31)
          F (Z_to_bv 64 0x223d38) fc None m1 (seg_rom ctasegs)).
  Proof.
    intros until POST. intros GI Hq Hmax Hqm Hlen B7 K31 HT KLEN KERR.
    rewrite ?IM128 in *. pose proof GI as GI'. go_unpack GI. ctx.
    pose proof (znth_range d q' DF) as BQ. pose proof (znth_range d op DF) as B0R.
    destruct (land128_cases (znth d q') BQ) as [(_ & L128 & L127)|(X & _ & _)]; [|exfalso; lia].
    unfold go_hdr in KLEN, KERR. rewrite K31, Z.eqb_refl in KLEN, KERR. rewrite (proj2 (Z.eqb_neq (omax - 1) 0)) in KLEN, KERR by lia.
    rewrite HT, L127 in KLEN, KERR.
    assert (SL : Z.shiftl len' 7 = len' * 2 ^ 7) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    assert (TR : Z.lor (Z.shiftl len' 7) (znth d q') = len' * 128 + znth d q').
    { rewrite SL, (lor_mul_addB len' (znth d q') 7) by lia. reflexivity. }
    (* [comment removed for export] *)
    step. if_cases K2; zc K2.
    - eapply KERR; [rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity|exact GI'|reflexivity|reflexivity|reflexivity].
    - rewrite (proj2 (Z.eqb_neq (max' - 1) 0)) in KLEN by lia.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit len') by lia. step. rewrite !unsigned_lit by lia. step.
      eapply (KLEN (Z.lor (Z.shiftl len' 7) (znth d q')) (q' + 1) (max' - 1)); [reflexivity|lia|lia|lia|unfold INT_MAX; lia|exact GI'|f_equal; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma stage_tagA : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 : word) (POST : machine_state -> Prop),
    (forall tag p1 max1 (x7 x15 x19 x20 x28 x29 x30 x31 : word) m1 j64,
       go_hdr d op omax = Some (tag, p1, max1) -> op + 1 <= p1 -> 1 <= max1 -> max1 = omax - (p1 - op) -> 0 <= tag <= INT_MAX ->
       go_invA m1 j64 [CB 8 jl] [CB 4 j2] [CB 4 j3] -> x15 = Z_to_bv 64 (D + p1) ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max1) x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) x15 (Z_to_bv 64 tag) (Z_to_bv 64 SHB)
                  SHPP x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (Z_to_bv 64 0x223c40) fc None m1 (seg_rom ctasegs))) ->
    (go_hdr d op omax = None -> at_errA POST) ->
    evt ctasegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz PP) (wz PL) (wz PT) (wz PC) (wz omax) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_GET_OBJECT_A) fc None m (seg_rom ctasegs)).
  Proof.
    intros until POST. intros KLEN KERR.
    destruct PRE as (HEAP & AS & IDS & DC & ST & CEIL' & LOSP & TOP' & AL16' & MI & CRED & FRM). ctx.
    destruct PAY as (HB & _).
    pose proof HPP as CPP. pose proof HPL as CPL. pose proof HPT as CPT. pose proof HPC as CPC. unfold MallocRep.wz in CPP.
    unfold ASN1_GET_OBJECT_A, MallocRep.wz in *. subst tp.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctasegs m) as WM.
    pose proof (znth_range d op DF) as B0R.
    carve_frame 64%nat ST. do 8 step. step.
    (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    step. if_cases KK; zc KK; [exfalso; rewrite ?signed_small in KK by lia; lia|].
    rewrite ?(unsigned_lit PP) by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (munch_weaken [(bv_unsigned sp - 64, bv_unsigned sp)]%Z W0 m mx ltac:(intros x Hx; cbn [outside fst snd] in Hx |- *; clear - Hx; tauto)) in MU end.
    (* [comment removed for export] *)
    step.
    pose proof (payload_readA _ D d op (wa (D + op)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit (znth d op)) by lia.
    step. rewrite (unsigned_lit (znth d op)) by lia. step.
    name_mem m1.
    lazymatch type of FR with rw_cells _ _ _ (CB 8 ?jj :: _) => set (j64 := jj) in FR end.
    assert (GI : go_invA m1 j64 [CB 8 jl] [CB 4 j2] [CB 4 j3]) by (gi_split MU WM MI ST FR CPP CPL CPT CPC HB).
    assert (L31 : 0 <= Z.land (znth d op) 31 <= 31).
    { split; [apply Z.land_nonneg; right; lia|]. change 31 with (Z.ones 5) at 1. rewrite Z.land_ones by lia. change (2 ^ 5) with 32. pose proof (Z.mod_pos_bound (znth d op) 32). lia. }
    pose proof KLEN as KLEN'. pose proof KERR as KERR'.
    unfold go_hdr in KLEN, KERR.
    step. if_cases KT; zc KT.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) KT) in KLEN, KERR.
      step. step. if_cases K1; zc K1.
      + eapply KERR; [rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity|exact GI|reflexivity|reflexivity|reflexivity].
      + rewrite (proj2 (Z.eqb_neq (omax - 1) 0)) in KLEN by lia.
        step.
        ub. (* [comment removed for export] *)
        replace (omax + -1) with (omax - 1) by lia.
        eapply KLEN; [reflexivity|lia|lia|lia|unfold INT_MAX; lia|exact GI|f_equal; lia].
    - (* [comment removed for export] *)
      rewrite KT, Z.eqb_refl in KLEN, KERR.
      step. step. if_cases K1; zc K1.
      + eapply KERR; [rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity|exact GI|reflexivity|reflexivity|reflexivity].
      + rewrite (proj2 (Z.eqb_neq (omax - 1) 0)) in KLEN, KERR by lia.
        (* [comment removed for export] *)
        pose proof (znth_range d (op + 1) DF) as B1R.
        pose proof (payload_readA m1 D d (op + 1) (wa (D + op + 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. do 7 step. clear RD.
        rewrite (sxb_byte (znth d (op + 1))) by lia.
        step. rewrite (sbyte_land255 (znth d (op + 1))) by lia. step. if_cases KB; zc KB.
        * (* [comment removed for export] *)
          assert (KB' : znth d (op + 1) < 128) by (apply (sbyte_wrap_lt _ B1R); lia).
          pose proof (proj1 (land128_iff _ B1R) KB') as L0.
          replace (D + op + 2) with (D + (op + 1) + 1) by lia. replace (D + op + 1) with (D + (op + 1)) by lia. replace (omax + -2) with (omax - 1 - 1) by lia.
          eapply (tag_finA 0 (op + 1) (omax - 1)); [exact GI|lia|lia|lia|rewrite ?IM128; lia|exact KB'|exact KT| |exact KLEN'|exact KERR'].
          assert (F1 : exists f', Z.to_nat (omax - 1) = S f') by (exists (Z.to_nat (omax - 2)); lia). destruct F1 as [f' ->].
          cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub Z.add INT_MAX]. rewrite L0. reflexivity.
        * (* [comment removed for export] *)
          assert (KB' : 128 <= znth d (op + 1)) by (destruct (Z.lt_ge_cases (znth d (op + 1)) 128) as [Hl|Hl]; [exfalso; pose proof (proj2 (sbyte_wrap_lt _ B1R) Hl); lia|exact Hl]).
          replace (D + op + 2) with (D + (op + 1) + 1) by lia. replace (D + op + 1) with (D + (op + 1)) by lia. replace (omax + -2) with (omax - 1 - 1) by lia.
          eapply (tag_loop_simA (Z.to_nat (omax - 1)) 0 (op + 1) (omax - 1));
            [exact GI|first [exact minus1_unsignedB | reflexivity | (rewrite unsigned_lit by lia; reflexivity)]|lia|lia|lia|reflexivity|rewrite ?IM128; lia|exact KB'| |].
          -- (* [comment removed for export] *)
             intros len' q' max' x19' x20' x28' x30' x31' HT L0 Hq' Hm' Hqm' Hl'.
             pose proof (znth_range d q' DF) as BQ'.
             assert (B7 : znth d q' < 128) by (apply (proj2 (land128_iff _ BQ')); exact L0).
             eapply (tag_finA len' q' max'); [exact GI|lia|lia|lia|exact Hl'|exact B7|exact KT|exact HT|exact KLEN'|exact KERR'].
          -- intros x6' x7' x15' x16' x17' x19' x20' x28' x29' x30' x31' HT. rewrite HT in KERR.
             eapply KERR; [reflexivity|exact GI|reflexivity|reflexivity|reflexivity].
  Qed.

  Local Notation SHPL0 := (Z_to_bv 64 (Z.shiftr PL 3)).
  Local Notation SHPL := (Z_to_bv 64 (Z.shiftr PL 3 + SHB)).

  (* [comment removed for export] *)
  Lemma zskip_simA : forall fuel (p0 p cnt e : Z) (x5 x6 x7 x12 x13 x16 x19 x29 x30 x31 : word) m2 j64 cpl cpt cpc (POST : machine_state -> Prop),
    go_invA m2 j64 cpl cpt cpc -> x5 = Z_to_bv 64 (p - p0) ->
    op + 2 <= p0 <= p -> 0 < cnt -> p + cnt = e -> e <= op + omax -> fuel = Z.to_nat cnt -> cnt <= 127 ->
    (forall p' cnt' (x29' : word), skip_zeros fuel d p cnt = (p', cnt') -> 0 < cnt' -> znth d p' <> 0 -> p <= p' -> p' + cnt' = e ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) (Z_to_bv 64 (p' - p0)) (Z_to_bv 64 (D + p')) x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 (D + p')) x13 (Z_to_bv 64 omax) (Z_to_bv 64 (D + p0)) x16 (Z_to_bv 64 SHB)
                  SHPP x19 (Z_to_bv 64 (D + p0)) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cnt') x29' x30 x31)
              F (Z_to_bv 64 0x223da8) fc None m2 (seg_rom ctasegs))) ->
    (forall p' (x5' x6' x12' x28' x29' : word), skip_zeros fuel d p cnt = (p', 0) -> p' = e ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5' x6' x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12' x13 (Z_to_bv 64 omax) (Z_to_bv 64 (D + p0)) x16 (Z_to_bv 64 SHB)
                  SHPP x19 (Z_to_bv 64 (D + p0)) s5 s6 s7 s8 s9 s10 s11 x28' x29' x30 x31)
              F (Z_to_bv 64 0x223e04) fc None m2 (seg_rom ctasegs))) ->
    evt ctasegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12 x13 (Z_to_bv 64 omax) (Z_to_bv 64 (D + p0)) x16 (Z_to_bv 64 SHB)
               SHPP x19 (Z_to_bv 64 (D + p0)) s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 cnt) x29 x30 x31)
          F (Z_to_bv 64 0x223d60) fc None m2 (seg_rom ctasegs)).
  Proof.
    induction fuel as [|fuel IH]; intros until POST; intros GI X5 Hp Hc Hpc He Hf Hc7 KNZ KZ; [exfalso; lia|].
    subst x5. go_unpack GI. ctx.
    pose proof (znth_range d p DF) as BP.
    cbn -[Z.ltb Z.eqb Z.sub Z.add znth] in KNZ, KZ. rewrite (proj2 (Z.ltb_lt 0 cnt) Hc) in KNZ, KZ. cbn [andb] in KNZ, KZ.
    (* [comment removed for export] *)
    step. rewrite ?unsigned_lit by lia. replace (D + p0 + (p - p0)) with (D + p) by lia.
    step. step. ab_shload 1%Z. ab_join 6%Z 29%Z 0x223d74%Z ABok.
    step. rewrite ?unsigned_lit by lia. replace (D + p0 + (p - p0)) with (D + p) by lia.
    pose proof (payload_readA m2 D d p (wa (D + p)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit (znth d p)) by lia.
    (* [comment removed for export] *)
    step. if_cases KB; zc KB.
    - rewrite (proj2 (Z.eqb_neq _ _) KB) in KNZ. eapply KNZ; [reflexivity|lia|exact KB|lia|lia].
    - rewrite KB, Z.eqb_refl in KNZ, KZ.
      (* [comment removed for export] *)
      step. rewrite (unsigned_lit cnt), bk_swrap32_small by lia. step. rewrite ?unsigned_lit by lia.
      (* [comment removed for export] *)
      step. if_cases KC; zc KC.
      + (* [comment removed for export] *)
        eapply (IH p0 (p + 1) (cnt + -1) e); [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|f_equal; lia|lia|lia|lia|lia|lia|lia| |].
        * intros p' cnt' x29' HS. replace (cnt - 1) with (cnt + -1) in KNZ by lia. intros. eapply KNZ; [exact HS|lia|assumption|lia|lia].
        * intros p' x5' x6' x12' x28' x29' HS. replace (cnt - 1) with (cnt + -1) in KZ by lia. intros. eapply KZ; [exact HS|lia].
      + (* [comment removed for export] *)
        step.
        assert (C1' : cnt = 1) by lia. assert (F0 : fuel = 0%nat) by lia. subst fuel.
        replace (cnt - 1) with 0 in KZ by lia. cbn -[Z.add] in KZ.
        eapply KZ; [reflexivity|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma acc_simA : forall fuel (r e acc : Z) (x5 x6 x7 x13 x16 x19 x20 x30 x31 : word) m2 j64 cpl cpt cpc (POST : machine_state -> Prop),
    go_invA m2 j64 cpl cpt cpc ->
    op + 2 <= r -> r < e -> e <= op + omax -> e - r <= 8 -> fuel = Z.to_nat (e - r) -> 0 <= acc < 2 ^ (64 - 8 * (e - r)) ->
    bv_unsigned x7 = e - r + 1 ->
    (forall ret accp (x7' x12' x29' x31' : word), be_octets fuel d r (e - r) acc = (ret, e) -> ret = accp * 256 + znth d (e - 1) -> 0 <= accp < 2 ^ 56 ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5 x6 x7' sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12' x13 (Z_to_bv 64 omax) (Z_to_bv 64 ret) x16 (Z_to_bv 64 SHB)
                  SHPP x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) x29' (Z_to_bv 64 (accp * 256)) x31')
              F (Z_to_bv 64 0x223e64) fc None m2 (seg_rom ctasegs))) ->
    evt ctasegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 (D + r)) x13 (Z_to_bv 64 omax) (Z_to_bv 64 acc) x16 (Z_to_bv 64 SHB)
               SHPP x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 1) (Z_to_bv 64 (D + r)) x30 x31)
          F (Z_to_bv 64 0x223e24) fc None m2 (seg_rom ctasegs)).
  Proof.
    induction fuel as [|fuel IH]; intros until POST; intros GI Hr Hre He H8 Hf Hacc Hx7 KEX; [exfalso; lia|].
    go_unpack GI. ctx.
    pose proof (znth_range d r DF) as BR.
    cbn -[Z.ltb Z.mul Z.add Z.sub znth] in KEX. rewrite (proj2 (Z.ltb_lt 0 (e - r))) in KEX by lia.
    assert (P8 : 2 ^ (64 - 8 * (e - r)) * 256 = 2 ^ (64 - 8 * (e - (r + 1)))).
    { replace (64 - 8 * (e - (r + 1))) with (64 - 8 * (e - r) + 8) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    assert (P64 : 2 ^ (64 - 8 * (e - (r + 1))) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    (* [comment removed for export] *)
    pose proof (payload_readA m2 D d r (wa (D + r)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit (znth d r)) by lia.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit acc) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    step. step. rewrite Hx7, bk_swrap32_small by lia.
    step. rewrite !unsigned_lit by lia.
    assert (OR : Z.lor (acc * 256) (znth d r) = acc * 256 + znth d r).
    { rewrite <- Z.lxor_lor by (apply Z.bits_inj'; intros nn Hn; rewrite Z.land_spec, Z.bits_0;
        destruct (Z.lt_ge_cases nn 8) as [L|L]; [rewrite (Z.mul_pow2_bits_low acc 8 nn) by lia; reflexivity|];
        rewrite (Z.bits_above_log2 (znth d r) nn); [apply Bool.andb_false_r|lia|]; destruct (Z.eq_dec (znth d r) 0) as [->|NZ]; [cbn; lia|]; apply (Z.lt_le_trans _ 8); [apply Z.log2_lt_pow2; lia|lia]).
      symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros nn Hn. rewrite Z.land_spec, Z.bits_0.
      destruct (Z.lt_ge_cases nn 8) as [L|L]; [rewrite (Z.mul_pow2_bits_low acc 8 nn) by lia; reflexivity|].
      rewrite (Z.bits_above_log2 (znth d r) nn); [apply Bool.andb_false_r|lia|]. destruct (Z.eq_dec (znth d r) 0) as [->|NZ]; [cbn; lia|]. apply (Z.lt_le_trans _ 8); [apply Z.log2_lt_pow2; lia|lia]. }
    rewrite OR.
    step.
    (* [comment removed for export] *)
    step. if_cases KC; zc KC; rewrite ?signed_small in KC by lia.
    - (* [comment removed for export] *)
      replace (D + r + 1) with (D + (r + 1)) by lia.
      eapply (IH (r + 1) e (acc * 256 + znth d r)); [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|lia|lia|lia|lia|lia|lia|rewrite unsigned_lit by lia; lia|].
      intros ret accp x7' x12' x29' x31' HB' Hret Haccp. replace (e - r - 1) with (e - (r + 1)) in KEX by lia. eapply KEX; [exact HB'|exact Hret|exact Haccp].
    - (* [comment removed for export] *)
      assert (E1 : e = r + 1) by lia. assert (F0 : fuel = 0%nat) by lia. subst fuel. subst e. cbn -[Z.mul Z.add Z.sub znth] in KEX.
      replace (r + 1 - 1) with r in KEX by lia. replace (D + r + 1) with (D + (r + 1)) by lia.
      step.
      eapply (KEX (acc * 256 + znth d r) acc); [f_equal; f_equal; lia|reflexivity|].
      replace (64 - 8 * (r + 1 - r)) with 56 in Hacc by lia. exact Hacc.
  Qed.

  (* [comment removed for export] *)
  Lemma storelen_simA : forall len p2 (x5 x6 x7 x12 x16 x20 x21 x28 x29 x30 x31 : word) m2 j64 cpt cpc (POST : machine_state -> Prop),
    go_invA m2 j64 [CB 8 jl] cpt cpc -> cells_size cpt = 4%nat -> cells_size cpc = 4%nat -> 0 <= len < 2 ^ 63 -> x20 = Z_to_bv 64 (D + p2) ->
    (forall (x12' : word) m3, go_invA m3 j64 [C8 (Z_to_bv 64 len)] cpt cpc ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12' SHPL0 (Z_to_bv 64 omax) (Z_to_bv 64 len) x16 (Z_to_bv 64 SHB)
                  SHPP (Z_to_bv 64 (Z.land (znth d op) 32)) (Z_to_bv 64 (D + p2)) (Z_to_bv 64 0) s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x223cd8) fc None m3 (seg_rom ctasegs))) ->
    evt ctasegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12 SHPL0 (Z_to_bv 64 omax) (Z_to_bv 64 len) x16 (Z_to_bv 64 SHB)
               SHPP (Z_to_bv 64 (Z.land (znth d op) 32)) x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x223cc4) fc None m2 (seg_rom ctasegs)).
  Proof.
    intros until POST. intros GI SZT SZC Hlen -> KDEC.
    go_unpack GI. ctx.
    (* [comment removed for export] *)
    step.
    (* [comment removed for export] *)
    unfold hidden in C12, C23, C24, PD2. step. hide C12; hide C23; hide C24; hide PD2.
    name_mem m3.
    assert (GI3 : go_invA m3 j64 [C8 (Z_to_bv 64 len)] cpt cpc) by (gi_split MU WM MI ST FRc CPP CPL CPT CPC HB).
    eapply KDEC; exact GI3.
  Qed.

  (* [comment removed for export] *)
  Lemma stage_lenA : forall tag p1 max1 (x7 x15 x19 x20 x28 x29 x30 x31 : word) m1 j64 (POST : machine_state -> Prop),
    go_hdr d op omax = Some (tag, p1, max1) -> op + 1 <= p1 -> 1 <= max1 -> max1 = omax - (p1 - op) -> 0 <= tag <= INT_MAX ->
    go_invA m1 j64 [CB 8 jl] [CB 4 j2] [CB 4 j3] -> x15 = Z_to_bv 64 (D + p1) ->
    (forall (inf : bool) len p2 (x5 x6 x7' x12 x15' x16 x28' x29' x30' x31' : word) m3,
       get_length d p1 max1 = Some (inf, len, p2) -> inf && (Z.land (znth d op) 32 =? 0) = false -> p1 + 1 <= p2 <= op + omax -> 0 <= len ->
       go_invA m3 j64 [C8 (Z_to_bv 64 len)] [C4 (Z_to_bv 64 tag)] [C4 (Z_to_bv 64 (Z.land (znth d op) 192))] ->
       evt ctasegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5 x6 x7' sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12 SHPL0 (Z_to_bv 64 omax) x15' x16 (Z_to_bv 64 SHB)
                  SHPP (Z_to_bv 64 (Z.land (znth d op) 32)) (Z_to_bv 64 (D + p2)) (Z_to_bv 64 (if inf then 1 else 0)) s6 s7 s8 s9 s10 s11 x28' x29' x30' x31')
              F (Z_to_bv 64 0x223cd8) fc None m3 (seg_rom ctasegs))) ->
    (get_length d p1 max1 = None -> at_errA POST) ->
    (forall len p2, get_length d p1 max1 = Some (true, len, p2) -> Z.land (znth d op) 32 = 0 -> at_errA POST) ->
    evt ctasegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max1) x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) x15 (Z_to_bv 64 tag) (Z_to_bv 64 SHB)
               SHPP x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x223c40) fc None m1 (seg_rom ctasegs)).
  Proof.
    intros until POST. intros GH Hp1 Hm1 Hm1' Htag GI -> KDEC KERR1 KERR2.
    go_unpack GI. ctx. (* [comment removed for export] *)
    pose proof (znth_range d op DF) as B0R. pose proof (znth_range d p1 DF) as B1R.
    assert (L192 : 0 <= Z.land (znth d op) 192 <= 192) by (pose proof (land_192_cases (znth d op)); lia).
    assert (L32 : 0 <= Z.land (znth d op) 32 <= 32) by (pose proof (land_32_cases (znth d op)); lia).
    unfold INT_MAX in Htag.
    (* [comment removed for export] *)
    unfold hidden in C13, C23, C34, PD3. step. hide C13; hide C23; hide C34; hide PD3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit (znth d op)) by lia.
    unfold hidden in C14, C24, C34, PD4. step. hide C14; hide C24; hide C34; hide PD4.
    (* [comment removed for export] *)
    pose proof (payload_readA _ D d p1 (wa (D + p1)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit (znth d p1)) by lia.
    step. step. step. rewrite ?(unsigned_lit (znth d op)), ?(unsigned_lit PL) by lia.
    unfold get_length in KDEC, KERR1, KERR2. rewrite (proj2 (Z.ltb_ge max1 1)) in KDEC, KERR1, KERR2 by lia.
    (* [comment removed for export] *)
    step. if_cases K80; zc K80.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ 128) K80) in KDEC, KERR1, KERR2.
      step. rewrite (unsigned_lit (znth d p1)) by lia. step. step.
      step. if_cases KL; zc KL.
      + (* [comment removed for export] *)
        apply (shl56_sign (znth d p1) B1R) in KL.
        destruct (land128_cases (znth d p1) B1R) as [(X & _)|(_ & L128 & L127)]; [exfalso; lia|].
        rewrite L128 in KDEC, KERR1, KERR2. cbn [Z.eqb] in KDEC, KERR1, KERR2. rewrite L127 in KDEC, KERR1, KERR2 |- *.
        set (i := znth d p1 - 128) in *.
        (* [comment removed for export] *)
        step. if_cases KI; zc KI.
        * rewrite (proj2 (Z.ltb_lt (max1 - 1) i)) in KERR1 by lia.
          eapply KERR1; [reflexivity|gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|reflexivity|reflexivity|reflexivity].
        * rewrite (proj2 (Z.ltb_ge (max1 - 1) i)) in KDEC, KERR1, KERR2 by lia.
          (* [comment removed for export] *)
          step. if_cases KZ0; zc KZ0.
          -- rewrite KZ0 in KDEC |- *. cbn -[Z.ltb Z.eqb Z.sub Z.add znth LONG_MAX Z.land] in KDEC.
             step. step.
             eapply (storelen_simA 0 (p1 + 1)); [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|reflexivity|reflexivity|lia|f_equal; lia|].
             intros x12' m3 GI3. eapply (KDEC false 0 (p1 + 1)); [reflexivity|reflexivity|lia|lia|exact GI3].
          -- (* [comment removed for export] *)
             step. step. step. step. replace (D + p1 + 1) with (D + (p1 + 1)) by lia.
             eapply (zskip_simA (Z.to_nat i) (p1 + 1) (p1 + 1) i (p1 + 1 + i));
               [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|f_equal; lia|lia|lia|lia|lia|reflexivity|lia| |].
             ++ (* [comment removed for export] *)
                intros p' i' x29' HS Hi' NZ Hp' Hpi'. rewrite HS in KDEC, KERR1.
                (* [comment removed for export] *)
                step. step. if_cases K8; zc K8.
                ** rewrite (proj2 (Z.ltb_ge 8 i')) in KDEC, KERR1 by lia.
                   (* [comment removed for export] *)
                   step. step. if_cases KQ; zc KQ; [exfalso; rewrite ?unsigned_lit in KQ by lia; lia|]. clear KQ.
                   step. rewrite ?unsigned_lit by lia. step. step.
                   assert (P2 : 0 <= 0 < 2 ^ (64 - 8 * (p' + i' - p'))) by (split; [lia|]; apply Z.pow_pos_nonneg; lia).
                   eapply (acc_simA (Z.to_nat i') p' (p' + i') 0);
                     [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|lia|lia|lia|lia|f_equal; lia|exact P2|rewrite unsigned_lit by lia; lia|].
                   intros ret accp x7'' x12'' x29'' x31'' HBE Hret Haccp. replace (p' + i' - p') with i' in HBE by lia. rewrite HBE in KDEC, KERR1.
                   pose proof (znth_range d (p' + i' - 1) DF) as BL.
                   (* [comment removed for export] *)
                   step. if_cases KS; zc KS; rewrite ?unsigned_lit in KS by lia.
                   +++ rewrite (proj2 (Z.ltb_lt LONG_MAX ret)) in KERR1 by (unfold LONG_MAX; lia).
                       eapply KERR1; [reflexivity|gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|reflexivity|reflexivity|reflexivity].
                   +++ rewrite (proj2 (Z.ltb_ge LONG_MAX ret)) in KDEC by (unfold LONG_MAX; lia).
                       pose proof (be_octets_bounds _ _ _ _ _ _ _ HBE ltac:(lia) ltac:(eapply Forall_impl; [|exact DF]; intros c Hc; cbn in Hc; lia)) as (_ & _ & RET0).
                       (* [comment removed for export] *)
                       step. step. step.
                       eapply (storelen_simA ret (p' + i'));
                         [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|reflexivity|reflexivity|unfold LONG_MAX in *; lia|rewrite ?unsigned_lit by lia; f_equal; lia|].
                       intros x12' m3 GI3. eapply (KDEC false ret (p' + i')); [reflexivity|reflexivity|lia|lia|exact GI3].
                ** rewrite (proj2 (Z.ltb_lt 8 i')) in KERR1 by lia.
                   eapply KERR1; [reflexivity|gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|reflexivity|reflexivity|reflexivity].
             ++ (* [comment removed for export] *)
                intros p' x5' x6' x12' x28' x29' HS Hp'. rewrite HS in KDEC. subst p'.
                step. step. step.
                eapply (storelen_simA 0 (p1 + 1 + i));
                  [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|reflexivity|reflexivity|lia|f_equal; lia|].
                intros x12'' m3 GI3. eapply (KDEC false 0 (p1 + 1 + i)); [cbn; reflexivity|reflexivity|lia|lia|exact GI3].
      + (* [comment removed for export] *)
        assert (KL' : znth d p1 < 128) by (destruct (Z.lt_ge_cases (znth d p1) 128) as [X|X]; [exact X|exfalso; pose proof (proj2 (shl56_sign _ B1R) X); lia]).
        destruct (land128_cases (znth d p1) B1R) as [(_ & L128 & L127)|(X & _)]; [|exfalso; lia].
        rewrite L128, Z.eqb_refl in KDEC. rewrite L127.
        step.
        eapply (storelen_simA (znth d p1) (p1 + 1));
          [gi_split MU WM MI ST FRc CPP CPL CPT CPC HB|reflexivity|reflexivity|lia|f_equal; lia|].
        intros x12' m3 GI3. eapply (KDEC false (znth d p1) (p1 + 1)); [rewrite L127; reflexivity|reflexivity|lia|lia|exact GI3].
    - (* [comment removed for export] *)
      rewrite K80, Z.eqb_refl in KDEC, KERR2.
      unfold hidden in C12, C23, C24, PD2. step. hide C12; hide C23; hide C24; hide PD2.
      name_mem m3.
      assert (GI3 : go_invA m3 j64 [C8 (Z_to_bv 64 0)] [C4 (Z_to_bv 64 tag)] [C4 (Z_to_bv 64 (Z.land (znth d op) 192))]) by (gi_split MU WM MI ST FRc CPP CPL CPT CPC HB).
      step. if_cases KC; zc KC.
      + eapply (KERR2 0 (p1 + 1) eq_refl KC); [exact GI3|reflexivity|reflexivity|reflexivity].
      + step. step. step. replace (D + p1 + 1) with (D + (p1 + 1)) by lia.
        eapply (KDEC true 0 (p1 + 1)); [reflexivity|rewrite (proj2 (Z.eqb_neq _ 0) KC); reflexivity|lia|lia|exact GI3].
  Qed.

  (* [comment removed for export] *)
  Lemma lib_outA : forall ΣX (OWX : list block) mX a, @BnHeapA.AHEAP AR ΣX OWX LB mX -> lib_addr OWX a -> outside W0 a.
  Proof.
    intros ΣX OWX mX a HEAPX HL. ctx.
    destruct (CELL PP 8 CI1) as (b1 & _ & X1 & Y1 & Z1 & U1 & _ & L1 & R1). destruct (CELL PL 8 CI2) as (b2 & _ & X2 & Y2 & Z2 & U2 & _ & L2 & R2).
    destruct (CELL PT 4 CI3) as (b3 & _ & X3 & Y3 & Z3 & U3 & _ & L3 & R3). destruct (CELL PC 4 CI4) as (b4 & _ & X4 & Y4 & Z4 & U4 & _ & L4 & R4).
    unfold SEGTOP_A in R1, R2, R3, R4.
    destruct HL as [HS|(b & Hb & Hr)].
    - pose proof (LIBW_S_A a HS) as HA. unfold LIBW_A in HA. cbn [rin_ivs fst snd] in HA. cbn [outside fst snd].
      clear - HA X1 Y1 R1 X2 Y2 R2 X3 Y3 R3 X4 Y4 R4 CEIL LO ESS CL1. repeat split; lia.
    - assert (Hb' : In b (OWX ++ LB)) by (apply in_or_app; left; exact Hb).
      pose proof (AH_range_gen _ _ _ _ _ HEAPX Hb') as (_ & _ & _ & BC & _).
      pose proof (AH_nodup _ _ _ _ HEAPX) as ND. destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr, BC.
      pose proof (fun bb (Hbb : In bb LB) => AH_disjoint_gen _ _ _ _ bb (q, A, n) HEAPX (in_or_app _ _ _ (or_intror Hbb)) Hb' (ids_disj OWX LB q A n ND Hb bb Hbb)) as DJ.
      pose proof (DJ b1 L1) as D1. pose proof (DJ b2 L2) as D2. pose proof (DJ b3 L3) as D3. pose proof (DJ b4 L4) as D4. cbn [blk_addr blk_size fst snd] in D1, D2, D3, D4.
      cbn [outside fst snd]. clear - Hr BC D1 D2 D3 D4 X1 Y1 X2 Y2 X3 Y3 X4 Y4 CEIL LO ESS. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma ax_outA : forall ΣX (OWX : list block) mX a, @BnHeapA.AHEAP AR ΣX OWX LB mX ->
    ax_client LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_A) a -> outside W0 a.
  Proof.
    intros ΣX OWX mX a HEAPX [HX Hc]. ctx. cbn [rin_ivs fst snd app] in HX. cbn [outside fst snd].
    destruct Hc as [Hc|[Hc|(b & Hb & Hr)]].
    - clear - HX Hc. repeat split; lia.
    - destruct Hc as [(l & h & Hin & Hlh) _]. unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
      clear - HX Hin Hlh CL1 CEIL LO ESS. destruct Hin as [E0|[E0|[E0|[]]]]; injection E0 as <- <-; repeat split; lia.
    - pose proof (AH_range_gen _ _ _ _ _ HEAPX (in_or_app _ _ _ (or_intror Hb))) as (_ & _ & _ & BC & _).
      clear - HX Hr BC CEIL LO ESS. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma w0_coreA : forall m2, munch W0 m m2 -> wmono ctasegs m m2 ->
    AHEAP Σ OW LB m2 /\ agree_on (lib_addr OW) m m2
    /\ ax_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_A) m m2
    /\ (forall a, 0 <= a < 2 ^ 64 -> in_block K a -> m2 (wa a) = m (wa a)).
  Proof.
    intros m2 MU WM. ctx. destruct PRE as (HEAP & _).
    destruct (CELL PP 8 CI1) as (b1 & Hb1 & X1 & Y1 & _). destruct (CELL PL 8 CI2) as (b2 & Hb2 & X2 & Y2 & _).
    destruct (CELL PT 4 CI3) as (b3 & Hb3 & X3 & Y3 & _). destruct (CELL PC 4 CI4) as (b4 & Hb4 & X4 & Y4 & _).
    split; [| split; [| split]].
    - eapply (AH_frame Σ OW LB m m2 W0 HEAP MU WM).
      constructor; [left; cbn [fst snd]; clear - CEIL LO ESS TOP; unfold USTACK_TOP in *; lia|].
      constructor; [right; right; exists b1; cbn [fst snd]; auto|]. constructor; [right; right; exists b2; cbn [fst snd]; auto|].
      constructor; [right; right; exists b3; cbn [fst snd]; auto|]. constructor; [right; right; exists b4; cbn [fst snd]; auto| constructor].
    - eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. intros a HL. exact (lib_outA Σ OW m a HEAP HL).
    - unfold ax_pres. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. intros a HX. exact (ax_outA Σ OW m a HEAP HX).
    - intros a Ha Hin. apply MU. unfold wa. rewrite unsigned_lit by lia. apply (lib_outA Σ OW m a HEAP). right. eapply in_block_mono; [exact KOW| exact Hin].
  Qed.

  (* [comment removed for export] *)
  Lemma pre_at_callA : forall m2 j64 cpl cpt cpc, go_invA m2 j64 cpl cpt cpc ->
    ap_preA Σ st m2 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo ERR_SET_ERROR_STACK GETOBJ_ERR_COST_A GETOBJ_FRAMES_A
    /\ ax_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_A) m m2
    /\ (forall a, 0 <= a < 2 ^ 64 -> in_block K a -> m2 (wa a) = m (wa a)).
  Proof.
    intros m2 j64 cpl cpt cpc GI. go_unpack GI. ctx.
    destruct PRE as (HEAP & AS & IDS & DC & ST0 & CEIL' & LOSP & TOP' & AL16' & MI0 & CRED & FRM).
    destruct (w0_coreA m2 MU WM) as (HEAP2 & AGL & AXP & KB).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    split; [| split; [exact AXP| exact KB]].
    unfold ap_preA. rewrite ESP. split; [exact HEAP2|].
    split; [eapply ap_state_agree; [exact AS| exact AGL]|]. split; [exact IDS|].
    split; [pose proof AS as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)); eapply data_cells_agree; [exact DC| exact AGL| exact OD]|].
    split; [exact ST|]. split; [exact CEIL|]. split; [clear - LO; lia|]. split; [clear - TOP; unfold USTACK_TOP in *; lia|].
    split; [replace (bv_unsigned sp + -64) with (bv_unsigned sp - 64) by lia; rewrite Zminus_mod, AL16; reflexivity|].
    split; [exact MI|]. split; [exact CRED| exact FRM].
  Qed.

  (* [comment removed for export] *)
  Lemma pre_at_retA : forall m2, munch W0 m m2 -> wmono ctasegs m m2 -> mem_inv ctasegs m2 -> stk ctasegs m2 lo (bv_unsigned sp) ->
    ap_preA Σ st m2 OW LB E bo sp lo 0 0 0
    /\ ax_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_A) m m2
    /\ (forall a, 0 <= a < 2 ^ 64 -> in_block K a -> m2 (wa a) = m (wa a)).
  Proof.
    intros m2 MU WM MI2 ST2. ctx.
    destruct PRE as (HEAP & AS & IDS & DC & ST0 & CEIL' & LOSP & TOP' & AL16' & MI0 & CRED & FRM).
    destruct (w0_coreA m2 MU WM) as (HEAP2 & AGL & AXP & KB).
    split; [| split; [exact AXP| exact KB]].
    unfold ap_preA. split; [exact HEAP2|].
    split; [eapply ap_state_agree; [exact AS| exact AGL]|]. split; [exact IDS|].
    split; [pose proof AS as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)); eapply data_cells_agree; [exact DC| exact AGL| exact OD]|].
    split; [exact ST2|]. split; [exact CEIL|]. split; [clear - LO ESS; lia|]. split; [exact TOP'|]. split; [exact AL16|].
    split; [exact MI2|]. split; [clear - CRED; lia| clear - FRM; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma fin_commonA : forall ΣF (stF : ap_st bptr) mF OWF m4,
    ap_preA ΣF stF mF OWF LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo 0 0 0 -> (forall b, In b K -> In b OWF) ->
    munch [(PP, PP + 8)]%Z mF m4 -> wmono ctasegs mF m4 -> stk ctasegs m4 lo (bv_unsigned sp) -> mem_inv ctasegs m4 ->
    ap_preA ΣF stF m4 OWF LB E bo sp lo 0 0 0
    /\ (forall a, 0 <= a < 2 ^ 64 -> in_block K a -> m4 (wa a) = mF (wa a))
    /\ ax_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_A) mF m4.
  Proof.
    intros until m4. intros PREF KOWF MU WM ST4 MI4. ctx.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    destruct PREF as (HEAPF & ASF & IDSF & DCF & STF & _ & _ & _ & _ & MIF & CREDF & FRMF).
    destruct (CELL PP 8 CI1) as (b1 & _ & X1 & Y1 & _ & _ & _ & L1 & _).
    assert (SUB : forall a, outside W0 a -> outside [(PP, PP + 8)]%Z a) by (intros a Ha; cbn [outside fst snd] in Ha |- *; clear - Ha; tauto).
    assert (AGL : agree_on (lib_addr OWF) mF m4).
    { eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. intros a HL. apply SUB. exact (lib_outA ΣF OWF mF a HEAPF HL). }
    assert (HEAP4 : @BnHeapA.AHEAP AR ΣF OWF LB m4).
    { eapply (AH_frame ΣF OWF LB mF m4 _ HEAPF MU WM). constructor; [right; right; exists b1; cbn [fst snd]; split; [apply in_or_app; right; exact L1| auto]| constructor]. }
    split; [| split].
    - unfold ap_preA. split; [exact HEAP4|].
      split; [eapply ap_state_agree; [exact ASF| exact AGL]|]. split; [exact IDSF|].
      split; [pose proof ASF as (_ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & OD)); eapply data_cells_agree; [exact DCF| exact AGL| exact OD]|].
      split; [exact ST4|]. split; [exact CEIL|]. split; [clear - LO ESS; lia|]. split; [exact TOP|]. split; [exact AL16|].
      split; [exact MI4|]. split; [clear - CREDF; lia| clear - FRMF; lia].
    - intros a Ha Hin. apply MU. unfold wa. rewrite unsigned_lit by lia. apply SUB. apply (lib_outA ΣF OWF mF a HEAPF). right. eapply in_block_mono; [exact KOWF| exact Hin].
    - unfold ax_pres. eapply agree_on_mono; [exact (agree_on_of_munch_nw _ _ _ MU)|]. intros a HX. apply SUB. exact (ax_outA ΣF OWF mF a HEAPF HX).
  Qed.

  (* [comment removed for export] *)
  Lemma ap_preA_restock : forall Σ' (st' : ap_st bptr) m' OW' bo' (spw : word) stack cost frames,
    ap_preA Σ' st' m' OW' LB E bo' spw lo 0 0 0 -> lo <= bv_unsigned spw - stack -> 0 <= cost <= rt_credit RT Σ' ->
    0 <= frames -> Z.of_nat (length FR) + frames <= Z.of_nat FRAMES_MAX ->
    ap_preA Σ' st' m' OW' LB E bo' spw lo stack cost frames.
  Proof.
    intros until frames. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) H1 H2 H3 H4.
    unfold ap_preA. repeat (split; [first [assumption | lia]|]). lia.
  Qed.
  Lemma ap_preA_resp : forall Σ' (st' : ap_st bptr) m' OW' bo' (sp1 sp2 : word) stack cost frames,
    ap_preA Σ' st' m' OW' LB E bo' sp1 lo stack cost frames -> stk ctasegs m' lo (bv_unsigned sp2) -> lo <= bv_unsigned sp2 -> bv_unsigned sp2 + 16 <= USTACK_TOP ->
    bv_unsigned sp2 mod 16 = 0 -> ap_preA Σ' st' m' OW' LB E bo' sp2 lo 0 0 0.
  Proof.
    intros until frames. intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12) ST2 LE TOP2 AL2.
    unfold ap_preA. repeat (split; [first [assumption | lia]|]). lia.
  Qed.

  (* [comment removed for export] *)
  Definition site_okA (base line reason : Z) (rs : rsite) : Prop :=
    (base = 0x223cf4 /\ line = 95 /\ reason = 155 /\ rs = RS_too_long) \/ (base = 0x223db0 /\ line = 105 /\ reason = 123 /\ rs = RS_hdr_too_long).

  Definition raise_postA (base : Z) (x19 x20 x21 : word) (m2 : mem) (r : unit * ap_st bptr) (Σ' : rts RT) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' OW',
      ms' = MS (mkR (Z_to_bv 64 (base + 44)) (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) t0 t1 t2 sp (Z_to_bv 64 PP) a0 a1 a2 a3 a4 a5 a6 a7
                    SHPP x19 x20 x21 s6 s7 s8 s9 s10 s11 t3 t4' t5' t6')
               F' (Z_to_bv 64 (base + 44)) fc' None m' (seg_rom ctasegs)
      /\ ap_preA Σ' (snd r) m' OW' LB E bo (Z_to_bv 64 (bv_unsigned sp + -64)) lo 0 0 0
      /\ ax_pres LB (bv_unsigned sp + -64) LIBW_A m2 m'
      /\ rt_credit RT Σ - GETOBJ_ERR_COST_A <= rt_credit RT Σ'
      /\ (forall b, In b K -> In b OW') /\ (forall b, In b K -> ~ In (blk_id b) (es_ids (snd r)))
      /\ (forall a, 0 <= a < 2 ^ 64 -> in_block K a -> m' (wa a) = m (wa a)).

  Local Ltac ecu := unfold GETOBJ_ERR_COST_A, GETOBJ_FRAMES_A, ERR_NEW_COST, ERR_SET_DEBUG_COST, ERR_SET_ERROR_COST, ERR_VSET_ERROR_COST, ERR_NEW_FRAMES, ERR_SET_DEBUG_FRAMES,
                           ERR_SET_ERROR_FRAMES, ERR_VSET_ERROR_FRAMES, ERR_NEW_STACK, ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK, RT_STACK in *.
  (* [comment removed for export] *)
  Lemma raise_seqA : forall base line reason rs (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x28 x29 x30 x31 : word) m2 j64 cpl cpt cpc,
    site_okA base line reason rs -> go_invA m2 j64 cpl cpt cpc ->
    implAp (err_raise rs st) Σ (raise_postA base x19 x20 x21 m2)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp (wz TP_A) x5 x6 x7 sp (Z_to_bv 64 PP) x10 x11 x12 x13 x14 x15 x16 x17 SHPP x19 x20 x21
               s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 base) fc None m2 (seg_rom ctasegs)).
  Proof.
    intros until cpc. intros SITE GI.
    destruct (pre_at_callA m2 j64 cpl cpt cpc GI) as (PRE2 & LX2 & KP2).
    go_unpack GI. ctx.
    pose proof PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CRED0 & FRM0).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    assert (STK : ERR_NEW_STACK <= ERR_SET_ERROR_STACK /\ ERR_SET_DEBUG_STACK <= ERR_SET_ERROR_STACK)
      by (unfold ERR_NEW_STACK, ERR_SET_DEBUG_STACK, ERR_SET_ERROR_STACK, ERR_VSET_ERROR_STACK; clear; lia).
    destruct SITE as [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
    - unfold err_raise.
      (* [comment removed for export] *)
      assert (UWc : uw_chain USTACK_TOP m2 (bv_unsigned sp + -64) (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { uw_call_axX_tac m 64 UW LX2 FRc; [clear; lia | | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia].
        intros a Ha. apply rin_ivs_app in Ha as [Ha|Ha]; [cbn [rin_ivs fst snd app] in Ha; clear - Ha PPhi PLhi PThi PChi CEIL LO ESS; lia
          | pose proof (libw_below a Ha) as Hb; unfold SEGTOP_A in Hb; clear - Hb GLO LO ESS; lia]. }
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. step. apply evt_done.
        pose proof (HE2 bo) as W. unfold ap_stmtA in W.
        eapply W; [eapply ap_preA_weaken; [exact PRE2| ecu; clear; lia| ecu; clear; lia| ecu; clear; lia]| reflexivity| rewrite ESP; exact UWc | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_new1 CTX) | apply cons_ne | reflexivity| exact KOW| exact KIDS]. }
      intros r1 Σ1 ms1 PO1. cbv beta in PO1.
      destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & bo1 & -> & PREa & AXa & CRa & BKa & EBO1). subst bo1.
      pose proof AXa as AXa'. rewrite ESP in AXa'.
      apply (uw_chain_axpres _ _ _ _ _ _ _ AXa') in UWc; [| clear; lia | unfold SEGTOP_A; clear - GLO LO ESS; lia]. clear AXa'.
      match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end.
      assert (KIDS1 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      pose proof PREa as (_ & _ & _ & _ & STa & _ & _ & _ & _ & MIa & _ & _). rewrite ESP in STa.
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. unfold MallocRep.wz.
        pose proof (munch_refl (@nil (Z * Z)) mA) as MU1. pose proof (wmono_refl ctasegs mA) as WM1. do 6 step. apply evt_done.
        pose proof (HE3 RS_too_long eq_refl eq_refl bo) as W2. unfold ap_stmtA in W2.
        eapply W2; [eapply ap_preA_restock; [exact PREa| rewrite ESP; ecu; clear - LO; lia| ecu; clear - CRED0 CRa; lia| ecu; clear; lia| ecu; clear - FRM0; lia]
                  | reflexivity| rewrite ESP; exact UWc | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_dbg1 CTX) | apply cons_ne | unfold A_ASN1_LIB_C_A, A_ASN1_GET_OBJECT_FN_A, MallocRep.wz; cbn [rs_line RS_too_long]; repeat split; reflexivity| exact (proj1 BKa)| exact KIDS1]. }
      intros r2 Σ2 ms2 PO2. cbv beta in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & bo2 & -> & PREb & AXb & CRb & BKb & EBO2). subst bo2.
      pose proof AXb as AXb'. rewrite ESP in AXb'.
      apply (uw_chain_axpres _ _ _ _ _ _ _ AXb') in UWc; [| clear; lia | unfold SEGTOP_A; clear - GLO LO ESS; lia]. clear AXb'.
      match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end.
      assert (KIDS2 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKb) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      pose proof PREb as (_ & _ & _ & _ & STb & _ & _ & _ & _ & MIb & _ & _). rewrite ESP in STb.
      (* [comment removed for export] *)
      eapply implAp_mono.
      { apply implAp_from_evt. unfold MallocRep.wz.
        pose proof (munch_refl (@nil (Z * Z)) mB) as MU2. pose proof (wmono_refl ctasegs mB) as WM2. do 4 step. apply evt_done.
        pose proof (HE4 RS_too_long 13 155 bo) as W3. unfold ERR_set_error_specA, ap_stmtA in W3.
        eapply W3; [eapply ap_preA_restock; [exact PREb| rewrite ESP; ecu; clear - LO; lia| ecu; clear - CRED0 CRa CRb; lia| ecu; clear; lia| ecu; clear - FRM0; lia]
                  | reflexivity| rewrite ESP; exact UWc | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_err1 CTX) | apply cons_ne | unfold ERR_LIB_SYS, ERR_LIB_ASN1, MallocRep.wz; cbn [rs_code RS_too_long]; unfold ERR_LIB_ASN1; repeat split; first [reflexivity | (clear; lia)]| exact (proj1 BKb)| exact KIDS2]. }
      intros r3 Σ3 ms3 PO3. cbv beta in PO3.
      destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & bo3 & -> & PREc & AXc & CRc & BKc & EBO3). subst bo3.
      unfold raise_postA. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3.
      split; [match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end; reflexivity|].
      split; [exact PREc|].
      rewrite ESP in AXa, AXb, AXc.
      split; [eapply ax_pres_trans; [exact AXa| eapply ax_pres_trans; [exact AXb| exact AXc]]|].
      split; [ecu; clear - CRa CRb CRc; lia|].
      split; [exact (proj1 BKc)|]. split; [exact (proj1 (proj2 BKc))|].
      intros a Ha Hin. rewrite (proj2 (proj2 BKc) a Ha Hin), (proj2 (proj2 BKb) a Ha Hin), (proj2 (proj2 BKa) a Ha Hin). exact (KP2 a Ha Hin).
    - unfold err_raise.
      (* [comment removed for export] *)
      assert (UWc : uw_chain USTACK_TOP m2 (bv_unsigned sp + -64) (bv_unsigned sp) (bv_unsigned ra :: ras)).
      { uw_call_axX_tac m 64 UW LX2 FRc; [clear; lia | | clear; lia | clear - AL16; uchk_open; Z.div_mod_to_equations; lia | clear - TOP; unfold USTACK_TOP in *; lia].
        intros a Ha. apply rin_ivs_app in Ha as [Ha|Ha]; [cbn [rin_ivs fst snd app] in Ha; clear - Ha PPhi PLhi PThi PChi CEIL LO ESS; lia
          | pose proof (libw_below a Ha) as Hb; unfold SEGTOP_A in Hb; clear - Hb GLO LO ESS; lia]. }
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. step. apply evt_done.
        pose proof (HE2 bo) as W. unfold ap_stmtA in W.
        eapply W; [eapply ap_preA_weaken; [exact PRE2| ecu; clear; lia| ecu; clear; lia| ecu; clear; lia]| reflexivity| rewrite ESP; exact UWc | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_new2 CTX) | apply cons_ne | reflexivity| exact KOW| exact KIDS]. }
      intros r1 Σ1 ms1 PO1. cbv beta in PO1.
      destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & bo1 & -> & PREa & AXa & CRa & BKa & EBO1). subst bo1.
      pose proof AXa as AXa'. rewrite ESP in AXa'.
      apply (uw_chain_axpres _ _ _ _ _ _ _ AXa') in UWc; [| clear; lia | unfold SEGTOP_A; clear - GLO LO ESS; lia]. clear AXa'.
      match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end.
      assert (KIDS1 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      pose proof PREa as (_ & _ & _ & _ & STa & _ & _ & _ & _ & MIa & _ & _). rewrite ESP in STa.
      (* [comment removed for export] *)
      eapply implAp_abind.
      { apply implAp_from_evt. unfold MallocRep.wz.
        pose proof (munch_refl (@nil (Z * Z)) mA) as MU1. pose proof (wmono_refl ctasegs mA) as WM1. do 6 step. apply evt_done.
        pose proof (HE3 RS_hdr_too_long eq_refl eq_refl bo) as W2. unfold ap_stmtA in W2.
        eapply W2; [eapply ap_preA_restock; [exact PREa| rewrite ESP; ecu; clear - LO; lia| ecu; clear - CRED0 CRa; lia| ecu; clear; lia| ecu; clear - FRM0; lia]
                  | reflexivity| rewrite ESP; exact UWc | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_dbg2 CTX) | apply cons_ne | unfold A_ASN1_LIB_C_A, A_ASN1_GET_OBJECT_FN_A, MallocRep.wz; cbn [rs_line RS_hdr_too_long]; repeat split; reflexivity| exact (proj1 BKa)| exact KIDS1]. }
      intros r2 Σ2 ms2 PO2. cbv beta in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & bo2 & -> & PREb & AXb & CRb & BKb & EBO2). subst bo2.
      pose proof AXb as AXb'. rewrite ESP in AXb'.
      apply (uw_chain_axpres _ _ _ _ _ _ _ AXb') in UWc; [| clear; lia | unfold SEGTOP_A; clear - GLO LO ESS; lia]. clear AXb'.
      match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end.
      assert (KIDS2 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKb) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      pose proof PREb as (_ & _ & _ & _ & STb & _ & _ & _ & _ & MIb & _ & _). rewrite ESP in STb.
      (* [comment removed for export] *)
      eapply implAp_mono.
      { apply implAp_from_evt. unfold MallocRep.wz.
        pose proof (munch_refl (@nil (Z * Z)) mB) as MU2. pose proof (wmono_refl ctasegs mB) as WM2. do 4 step. apply evt_done.
        pose proof (HE4 RS_hdr_too_long 13 123 bo) as W3. unfold ERR_set_error_specA, ap_stmtA in W3.
        eapply W3; [eapply ap_preA_restock; [exact PREb| rewrite ESP; ecu; clear - LO; lia| ecu; clear - CRED0 CRa CRb; lia| ecu; clear; lia| ecu; clear - FRM0; lia]
                  | reflexivity| rewrite ESP; exact UWc | rewrite unsigned_lit by (clear; lia); exact (uk_ctx_call _ _ _ _ E_err2 CTX) | apply cons_ne | unfold ERR_LIB_SYS, ERR_LIB_ASN1, MallocRep.wz; cbn [rs_code RS_hdr_too_long]; unfold ERR_LIB_ASN1; repeat split; first [reflexivity | (clear; lia)]| exact (proj1 BKb)| exact KIDS2]. }
      intros r3 Σ3 ms3 PO3. cbv beta in PO3.
      destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & bo3 & -> & PREc & AXc & CRc & BKc & EBO3). subst bo3.
      unfold raise_postA. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3.
      split; [match goal with |- context [ret_pc (Z_to_bv 64 ?a)] => rewrite (ret_pc_even a) by (clear; lia) end; reflexivity|].
      split; [exact PREc|].
      rewrite ESP in AXa, AXb, AXc.
      split; [eapply ax_pres_trans; [exact AXa| eapply ax_pres_trans; [exact AXb| exact AXc]]|].
      split; [ecu; clear - CRa CRb CRc; lia|].
      split; [exact (proj1 BKc)|]. split; [exact (proj1 (proj2 BKc))|].
      intros a Ha Hin. rewrite (proj2 (proj2 BKc) a Ha Hin), (proj2 (proj2 BKb) a Ha Hin), (proj2 (proj2 BKa) a Ha Hin). exact (KP2 a Ha Hin).
  Qed.

  Local Notation GPOST := (getobj_postA ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 Σ OW LB E bo lo m K D PP PL PT PC g).
  Local Notation IPOST := (fun ms' : machine_state => implAp (go_eff g st) Σ GPOST ms').

  (* [comment removed for export] *)
  Lemma after_raiseA : forall ΣF OWF m2 mF j64 cpl cpt cpc,
    go_invA m2 j64 cpl cpt cpc -> @BnHeapA.AHEAP AR ΣF OWF LB mF -> ax_pres LB (bv_unsigned sp + -64) LIBW_A m2 mF ->
    cells_size cpl = 8%nat -> cells_size cpt = 4%nat -> cells_size cpc = 4%nat ->
    rw_cells ctasegs mF (bv_unsigned sp + -64) (CB 8 j64 :: go_frameA)
    /\ rw_cells ctasegs mF PP [C8 (Z_to_bv 64 (D + op))] /\ rw_cells ctasegs mF PL cpl /\ rw_cells ctasegs mF PT cpt /\ rw_cells ctasegs mF PC cpc
    /\ acc ctasegs mF PP 8 /\ offshW [(PP, PP + 8)]%Z.
  Proof.
    intros until cpc. intros GI HEAPF AXF BL BT BC. go_unpack GI. ctx.
    destruct (CELL PP 8 CI1) as (b1 & _ & X1 & Y1 & Z1 & U1 & O1 & L1 & R1). destruct (CELL PL 8 CI2) as (b2 & _ & X2 & Y2 & Z2 & U2 & _ & L2 & R2).
    destruct (CELL PT 4 CI3) as (b3 & _ & X3 & Y3 & Z3 & U3 & _ & L3 & R3). destruct (CELL PC 4 CI4) as (b4 & _ & X4 & Y4 & Z4 & U4 & _ & L4 & R4).
    unfold SEGTOP_A in R1, R2, R3, R4.
    assert (CLS : forall a, bv_unsigned sp + -64 <= a < bv_unsigned sp -> ax_client LB (bv_unsigned sp + -64) LIBW_A a).
    { intros a Ha. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha CL1 CEIL LO ESS; lia| left; clear - Ha TOP; unfold USTACK_TOP in *; lia]. }
    assert (CLB : forall b a A n, In b LB -> blk_addr b <= A -> A + n <= blk_addr b + blk_size b -> (blk_addr b + blk_size b <= 65536 \/ 12365824 <= blk_addr b) ->
                  A <= a < A + n -> ax_client LB (bv_unsigned sp + -64) LIBW_A a).
    { intros b a A n Hb HA Hn Hr Ha. split; [unfold LIBW_A; cbn [rin_ivs fst snd]; clear - Ha HA Hn Hr; lia| right; right; exists b; split; [exact Hb| clear - Ha HA Hn; lia]]. }
    split; [eapply rw_cells_agree; [exact AXF| exact FRc| intros a Ha; apply CLS; cbn [cells_size csize Nat.add go_frameA] in Ha; clear - Ha; lia]|].
    split; [eapply rw_cells_agree; [exact AXF| exact CPP| intros a Ha; cbn in Ha; eapply (CLB b1 a PP 8); [exact L1| exact X1| exact Y1| exact R1| clear - Ha; lia]]|].
    split; [eapply rw_cells_agree; [exact AXF| exact CPL| intros a Ha; rewrite BL in Ha; eapply (CLB b2 a PL 8); [exact L2| exact X2| exact Y2| exact R2| clear - Ha; lia]]|].
    split; [eapply rw_cells_agree; [exact AXF| exact CPT| intros a Ha; rewrite BT in Ha; eapply (CLB b3 a PT 4); [exact L3| exact X3| exact Y3| exact R3| clear - Ha; lia]]|].
    split; [eapply rw_cells_agree; [exact AXF| exact CPC| intros a Ha; rewrite BC in Ha; eapply (CLB b4 a PC 4); [exact L4| exact X4| exact Y4| exact R4| clear - Ha; lia]]|].
    split; [eapply acc_sub; [exact (proj2 (AH_acc _ _ _ _ _ HEAPF (in_or_app _ _ _ (or_intror L1))))| exact X1| exact Y1]|].
    cbn [offshW fst snd]. unfold SHLO, SHHI in *. clear - O1 X1 Y1. repeat split; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma err_pathA : g = go_fail GeHdr op -> at_errA IPOST.
  Proof.
    intros GEQ. unfold at_errA. intros until cpc. intros GI2 SZL SZT SZC. pose proof GI2 as GI2'. go_unpack GI2. ctx.
    apply evt_done. clearbody g. subst g. cbn [go_eff go_err go_fail].
    eapply implAp_post_evt; [eapply (raise_seqA 0x223db0 105 123 RS_hdr_too_long); [right; repeat split; reflexivity| exact GI2']|].
    intros r ΣF msF RP. cbv beta. unfold raise_postA in RP.
    destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF
                    & -> & PREF & AXF & CRF & KOWF & KIDF & KBF).
    change (2244016 + 44) with 2244060.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
    pose proof PREF as (HEAPF & ASF & IDSF & DCF & STF & _ & _ & _ & _ & MIF & _ & _). rewrite ESP in STF.
    destruct (after_raiseA ΣF OWF m1 mF j64 cpl cpt cpc GI2' HEAPF AXF SZL SZT SZC) as (FRF & CPPF & CPLF & CPTF & CPCF & ACCF & OFF1). unfold go_frameA in FRF.
    apply rw_cells_CB_ofA in CPLF. apply rw_cells_CB_ofA in CPTF. apply rw_cells_CB_ofA in CPCF. rewrite SZL in CPLF. rewrite SZT in CPTF. rewrite SZC in CPCF.
    clear MU WM MI ST HB FRc CPP CPL CPT CPC ACCD ACCP ACCL ACCT ACCC.
    pose proof (munch_refl [(PP, PP + 8)]%Z mF) as MU. pose proof (wmono_refl ctasegs mF) as WM.
    unfold MallocRep.wz. step. do 7 step. step. release_frame FRF STF (bv_unsigned sp). step.
    apply evt_done.
    destruct (fin_commonA ΣF (snd r) mF OWF mF PREF KOWF MU WM STF MIF) as (PRE4 & KP4 & LX4).
    unfold getobj_postA. cbn [go_err go_p go_ret go_len go_tag go_cls go_fail go_costA].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, FF, fcF, mF, OWF, (cells_bytes cpl), (cells_bytes cpt), (cells_bytes cpc).
    split; [reflexivity|].
    split; [exact PRE4|].
    split. { eapply ax_pres_trans; [exact (proj1 (proj2 (pre_at_callA _ _ _ _ _ GI2')))|]. eapply ax_pres_trans; [|exact LX4].
             eapply ax_pres_weaken; [exact AXF| lia| intros b Hb; exact Hb|]. intros a Ha. cbn [rin_ivs app fst snd] in Ha |- *. clear - Ha. tauto. }
    split; [exact CRF|].
    split; [split; [exact KOWF| split; [exact KIDF| intros a Ha Hin; exact (KBF a Ha Hin)]]|].
    split; [unfold MallocRep.wz; exact CPPF|].
    split; [reflexivity|]. split; [exact CPLF| split; [exact CPTF| exact CPCF]].
  Qed.

  Theorem go_mainA : forall (t0 t1 t2 t3 t4 t5 a5 a6 a7 : word),
    implAp (go_eff g st) Σ GPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz PP) (wz PL) (wz PT) (wz PC) (wz omax) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_GET_OBJECT_A) fc None m (seg_rom ctasegs)).
  Proof.
    intros. apply implAp_from_evt.
    eapply stage_tagA.
    - (* [comment removed for export] *)
      intros tag p1 max1 x7 x15 x19 x20 x28 x29 x30 x31 m1 j64 GH Hp1 Hm1 Hmx Htag GI E15.
      eapply (stage_lenA tag p1 max1 x7 x15 x19 x20 x28 x29 x30 x31 m1 j64 _ GH Hp1 Hm1 Hmx Htag GI E15).
      + (* [comment removed for export] *)
        intros inf len p2 x5 x6 x7' x12 x15' x16 x28' x29' x30' x31' m2 GL HI Hp2 Hlen GI2.
        pose proof (CtRepP.W_get_object_walk.g_cases d op omax OM0 _ _ _ _ _ _ GH GL HI) as GEQ.
        pose proof GI2 as GI2'. go_unpack GI2. ctx.
        assert (L32 : 0 <= Z.land (znth d op) 32 <= 32) by (pose proof (land_32_cases (znth d op)); lia).
        assert (INF : 0 <= (if inf then 1 else 0) <= 1) by (destruct inf; lia).
        pose proof (get_length_bounds d p1 max1 inf len p2 ltac:(eapply Forall_impl; [|exact DF]; intros c Hc; cbn in Hc; lia) GL) as [GB1 GB2].
        pose proof (get_length_len_max d p1 max1 inf len p2 ltac:(eapply Forall_impl; [|exact DF]; intros c Hc; cbn in Hc; lia) GL) as GB3. unfold LONG_MAX in GB3.
        step. rewrite ?unsigned_lit by lia. step. step. rewrite ?unsigned_lit by lia. step. if_cases KD; zc KD; rewrite ?signed_small in KD by lia.
        * (* [comment removed for export] *)
          rewrite (proj2 (Z.ltb_ge _ _)) in GEQ by lia.
          unfold hidden in C12, C13, C14, PD1. step. hide C12; hide C13; hide C14; hide PD1.
          step. rewrite ?unsigned_lit by lia. step.
          do 7 step. step. release_frame FRc ST (bv_unsigned sp). step.
          name_mem m3.
          apply evt_done. replace g with (get_object d op omax) by reflexivity. rewrite GEQ. cbn [go_eff go_err]. apply implAp_aret.
          destruct (pre_at_retA m3 MU WM MI ST) as (PRE3 & LX3 & KP3).
          unfold getobj_postA. cbn [go_err go_p go_ret go_len go_tag go_cls go_costA fst snd].
          eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m3, OW, jl, j2, j3.
          split; [unfold MallocRep.wz; reflexivity|].
          split; [exact PRE3|]. split; [exact LX3|]. split; [clear; lia|].
          split; [split; [exact KOW|split; [intros b Hb Hin; apply (KIDS b Hb); apply in_app_iff; left; exact Hin|exact KP3]]|].
          split; [unfold MallocRep.wz; exact CPP|].
          unfold MallocRep.wz. split; [reflexivity|]. split; [exact CPL|split; [exact CPT|exact CPC]].
        * (* [comment removed for export] *)
          rewrite (proj2 (Z.ltb_lt _ _)) in GEQ by lia.
          apply evt_done. replace g with (get_object d op omax) by reflexivity. rewrite GEQ. cbn [go_eff go_err].
          eapply implAp_post_evt; [eapply (raise_seqA 0x223cf4 95 155 RS_too_long); [left; repeat split; reflexivity|exact GI2']|].
          intros r ΣF msF RP. cbv beta. unfold raise_postA in RP.
          destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF
                          & -> & PREF & AXF & CRF & KOWF & KIDF & KBF).
          change (2243828 + 44) with 2243872.
          assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; lia).
          pose proof PREF as (HEAPF & ASF & IDSF & DCF & STF & _ & _ & _ & _ & MIF & _ & _). rewrite ESP in STF.
          destruct (after_raiseA ΣF OWF m2 mF j64 _ _ _ GI2' HEAPF AXF eq_refl eq_refl eq_refl) as (FRF & CPPF & CPLF & CPTF & CPCF & ACCF & OFF1). unfold go_frameA in FRF.
          clear MU WM MI ST HB FRc CPP CPL CPT CPC ACCD ACCP ACCL ACCT ACCC.
          pose proof (munch_refl [(PP, PP + 8)]%Z mF) as MU. pose proof (wmono_refl ctasegs mF) as WM.
          unfold MallocRep.wz. step. rewrite ?unsigned_lit by lia.
          unfold hidden in C12, C13, C14, PD1. step. hide C12; hide C13; hide C14; hide PD1.
          step. rewrite ?unsigned_lit by lia. step.
          do 7 step. step. release_frame FRF STF (bv_unsigned sp). step.
          name_mem m4.
          apply evt_done.
          destruct (fin_commonA ΣF (snd r) mF OWF m4 PREF KOWF MU WM STF ltac:(assumption)) as (PRE4 & KP4 & LX4).
          unfold getobj_postA. cbn [go_err go_p go_ret go_len go_tag go_cls go_costA fst snd].
          eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, FF, fcF, m4, OWF, jl, j2, j3.
          split; [reflexivity|].
          split; [exact PRE4|].
          split. { eapply ax_pres_trans; [exact (proj1 (proj2 (pre_at_callA _ _ _ _ _ GI2')))|]. eapply ax_pres_trans; [|exact LX4].
                   eapply ax_pres_weaken; [exact AXF|lia|intros b Hb; exact Hb|]. intros a Ha. cbn [rin_ivs app fst snd] in Ha |- *. clear - Ha. tauto. }
          split; [exact CRF|].
          split; [split; [exact KOWF| split; [exact KIDF| intros a Ha Hin; rewrite (KP4 a Ha Hin); exact (KBF a Ha Hin)]]|].
          split; [exact CPPF|].
          split; [f_equal; apply ret_or_128; apply land_32_cases|]. split; [exact CPLF|split; [exact CPTF|exact CPCF]].
      + (* [comment removed for export] *)
        intros GL. apply err_pathA. apply (CtRepP.W_get_object_walk.g_err d op omax OM0). right. exists tag, p1, max1. split; [exact GH|left; exact GL].
      + (* [comment removed for export] *)
        intros len p2 GL HZ. apply err_pathA. apply (CtRepP.W_get_object_walk.g_err d op omax OM0). right. exists tag, p1, max1. split; [exact GH|right; exists len, p2; split; [exact GL|exact HZ]].
    - (* [comment removed for export] *)
      intros GH. apply err_pathA. apply (CtRepP.W_get_object_walk.g_err d op omax OM0). left. exact GH.
  Qed.

  End Act.

  (* [comment removed for export] *)
  Theorem ASN1_get_object_walkA : ASN1_get_object_specA.
  Proof.
    unfold ASN1_get_object_specA. intros until j3. intros PRE TP UW CTX NE KOW KIDS PAY OP0 OM0 OPM CELLS CELLSD HPP HPL HPT HPC -> -> -> -> ->.
    eapply (go_mainA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 F fc m Σ st OW LB E bo lo K D d op omax PP PL PT PC jl j2 j3 ras);
      assumption.
  Qed.
End Proofs.
End WithRT.
