(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Stdio Prog LibProg ProgG.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import ApBase ApState ApInv ApErr ApParse ApBridge.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpInit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApIface ApWalkTac ApErrKit ApErrKit2 W_err_new W_err_set_debug W_err_set_error W_get_object.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Definition hidden (P : Prop) : Prop := P.
Local Ltac hide H := lazymatch type of H with ?T => change T with (hidden T) in H end.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 (Z_to_bv 64 ?z) => constr:(C1 (Z_to_bv 8 z))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

(* [comment removed for export] *)
Ltac zc H := rewrite ?bv_lts_zero_r, ?bv_lts_zero_l in H; unfold bv_eqb, bv_ltu, bv_lts, bv_leu in H; fold_lit_ux_in H; try zsimp_in H; zify_bool H.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma payload_read : forall m D d i a, bytes_at ctusegs m D (to_bytes d) -> Forall (fun c => 0 <= c < 256) d ->
  0 <= i < zlength d -> a = wa (D + i) -> ov_read_bytes ctusegs m a 1 = Some [Z_to_bv 8 (znth d i)].
Proof.
  intros m D d i a HB HF Hi ->.
  assert (HN : nth_error (to_bytes d) (Z.to_nat i) = Some (Z_to_bv 8 (znth d i))).
  { unfold to_bytes. rewrite nth_error_map. unfold znth. destruct (Z.ltb_spec i 0); [lia|].
    destruct (nth_error d (Z.to_nat i)) as [c|] eqn:E; cbn.
    - rewrite (nth_error_nth _ _ _ E). reflexivity.
    - apply nth_error_None in E. unfold zlength in Hi. lia. }
  exact (u8ro_read ctusegs m D (to_bytes d) i _ _ HB HN ltac:(lia) eq_refl).
Qed.

Lemma byte_lit : forall z, 0 <= z < 256 -> bv_unsigned (Z_to_bv 8 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. apply Z.mod_small. lia. Qed.
Definition sbyte (b : Z) : Z := if b <? 128 then b else b - 256.
Lemma sxb_byte : forall b, 0 <= b < 256 -> sxb (Z_to_bv 8 b) = Z_to_bv 64 (sbyte b).
Proof.
  intros b Hb. unfold sxb, sbyte. f_equal. unfold bv_signed. rewrite byte_lit by lia. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. change (256 `div` 2) with 128.
  destruct (Z.ltb_spec b 128).
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add _ (-1)) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma sbyte_land255 : forall b, 0 <= b < 256 -> Z.land (bv_unsigned (Z_to_bv 64 (sbyte b))) 255 = b.
Proof.
  intros b Hb. unfold sbyte. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2 ^ 64).
  change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  destruct (Z.ltb_spec b 128).
  - rewrite (Z.mod_small b (2 ^ 64)) by lia. apply Z.mod_small. lia.
  - rewrite <- (Z.mod_add _ 1 (2 ^ 64)) by lia. rewrite (Z.mod_small _ (2 ^ 64)) by lia.
    replace (b - 256 + 1 * 2 ^ 64) with (b + (2 ^ 56 - 1) * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma sbyte_signed : forall b, 0 <= b < 256 -> bv_signed (Z_to_bv 64 (sbyte b)) = sbyte b.
Proof.
  intros b Hb. unfold sbyte, bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ 64 `div` 2) with (2 ^ 63).
  destruct (Z.ltb_spec b 128).
  - rewrite (Z.mod_small b) by lia. rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_add (b - 256) 1 (2 ^ 64)) by lia. rewrite (Z.mod_small (b - 256 + 1 * 2 ^ 64)) by lia.
    replace (b - 256 + 1 * 2 ^ 64 + 2 ^ 63) with ((b - 256 + 2 ^ 63) + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma land127_mod : forall b, Z.land b 127 = b mod 128.
Proof. intros b. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_split_255 : forall b, 0 <= b < 256 -> b = Z.land b 127 + Z.land b 128.
Proof.
  intros b Hb.
  assert (E : Z.land b 255 = b) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; apply Z.mod_small; lia).
  rewrite <- E at 1. change 255 with (Z.lor 127 128). rewrite Z.land_lor_distr_r.
  pose proof (Z.add_lor_land (Z.land b 127) (Z.land b 128)) as A.
  assert (Z0 : Z.land (Z.land b 127) (Z.land b 128) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec, Z.bits_0.
    destruct (Z.testbit b n); [|reflexivity]. cbn.
    destruct (Z.eq_dec n 7) as [->|Hn7]; [reflexivity|].
    change 128 with (2 ^ 7). rewrite Z.pow2_bits_eqb by lia. rewrite (proj2 (Z.eqb_neq 7 n)) by lia. apply Bool.andb_false_r. }
  lia.
Qed.
Lemma land128_iff : forall b, 0 <= b < 256 -> (b < 128 <-> Z.land b 128 = 0).
Proof.
  intros b Hb. pose proof (land_split_255 b Hb) as E. pose proof (land127_mod b) as M. pose proof (Z.mod_pos_bound b 128 ltac:(lia)) as MB.
  pose proof (land_pow2_cases b 7 ltac:(lia)) as C. change (2 ^ 7) with 128 in C. lia.
Qed.
Lemma land128_cases : forall b, 0 <= b < 256 -> (b < 128 /\ Z.land b 128 = 0 /\ Z.land b 127 = b) \/ (128 <= b /\ Z.land b 128 = 128 /\ Z.land b 127 = b - 128).
Proof.
  intros b Hb. pose proof (land_split_255 b Hb) as E. pose proof (land127_mod b) as M. pose proof (Z.mod_pos_bound b 128 ltac:(lia)) as MB.
  pose proof (land_pow2_cases b 7 ltac:(lia)) as C. change (2 ^ 7) with 128 in C. lia.
Qed.
Lemma sbyte_wrap_lt : forall b, 0 <= b < 256 -> (Z.land (sbyte b) 18446744073709551615 < 9223372036854775808 <-> b < 128).
Proof.
  intros b Hb. unfold sbyte. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  destruct (Z.ltb_spec b 128).
  - rewrite Z.mod_small by lia. lia.
  - replace (b - 256) with ((b - 256 + 2 ^ 64) + (-1) * 2 ^ 64) by lia. rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma shl56_sign : forall b, 0 <= b < 256 -> (9223372036854775808 <= Z.land (Z.shiftl b 56) 18446744073709551615 <-> 128 <= b).
Proof.
  intros b Hb. rewrite Z.shiftl_mul_pow2 by lia. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite Z.mod_small by (split; [lia|]; change (2 ^ 64) with (256 * 2 ^ 56); nia). change 9223372036854775808 with (128 * 2 ^ 56). nia.
Qed.

Lemma zext32_idem : forall a, 0 <= a < 2 ^ 32 -> Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 a)) 32))) 32 = a.
Proof.
  intros a Ha. rewrite (unsigned_lit a) by lia.
  assert (E : Z.shiftl a 32 = a * 2 ^ 32) by (apply Z.shiftl_mul_pow2; lia).
  rewrite unsigned_lit by (rewrite E; lia). rewrite Z.shiftr_shiftl_l by lia. cbn. reflexivity.
Qed.

Lemma get_length_len_max : forall d p max inf len p', Forall (fun b => 0 <= b) d ->
  get_length d p max = Some (inf, len, p') -> len <= LONG_MAX.
Proof.
  intros d p max inf len p' Hd H. unfold get_length in H.
  destruct (max <? 1); [discriminate|]. destruct (znth d p =? 128); [inversion H; subst; unfold LONG_MAX; lia|].
  destruct (Z.land (znth d p) 128 =? 0).
  - inversion H; subst. change 127 with (Z.ones 7). rewrite Z.land_ones by lia. change (2 ^ 7) with 128. pose proof (Z.mod_pos_bound (znth d p) 128). unfold LONG_MAX. lia.
  - destruct (max - 1 <? Z.land (znth d p) 127); [discriminate|]. destruct (skip_zeros _ d (p + 1) _) as [p1 i1].
    destruct (8 <? i1); [discriminate|]. destruct (be_octets _ d p1 i1 0) as [ret p2].
    destruct (Z.ltb_spec LONG_MAX ret); [discriminate|]. inversion H; subst. lia.
Qed.

Lemma ret_or_128 : forall r (inf : bool), r = 0 \/ r = 32 ->
  Z.lor (r + 128) (if inf then 1 else 0) = Z.lor (Z.lor r (if inf then 1 else 0)) 128.
Proof. intros r inf [-> | ->]; destruct inf; reflexivity. Qed.

(* [comment removed for export] *)
Lemma rw_cells_CB_of : forall m A cs, rw_cells ctusegs m A cs -> rw_cells ctusegs m A [CB (cells_size cs) (cells_bytes cs)].
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [apply cells_bytes_length; exact W|exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact B.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. exact R.
Qed.

Lemma IM128 : INT_MAX / 128 = 16777215.
Proof. reflexivity. Qed.

Lemma signed_small : forall z, 0 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec z (2 ^ 63)); lia. Qed.

Lemma zxb_lit : forall z, 0 <= z < 256 -> zxb (Z_to_bv 8 z) = Z_to_bv 64 z.
Proof. intros z Hz. unfold zxb. rewrite byte_lit by lia. reflexivity. Qed.

Lemma znth_range : forall d i, Forall (fun c => 0 <= c < 256) d -> 0 <= znth d i < 256.
Proof.
  intros d i HF. unfold znth. destruct (i <? 0); [lia|]. destruct (nth_in_or_default (Z.to_nat i) d 0) as [H| ->]; [|lia].
  exact (proj1 (Forall_forall _ _) HF _ H).
Qed.

Lemma lor_mul_addU : forall a r k, 0 <= a -> 0 <= k -> 0 <= r < 2 ^ k -> Z.lor (a * 2 ^ k) r = a * 2 ^ k + r.
Proof.
  intros a r k Ha Hk Hr.
  assert (NC : Z.land (a * 2 ^ k) r = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.lt_ge_cases n k) as [L|L]; [rewrite (Z.mul_pow2_bits_low a k n) by lia; reflexivity|].
    destruct (Z.eq_dec r 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    rewrite (Z.bits_above_log2 r n); [apply Bool.andb_false_r|lia|]. apply (Z.lt_le_trans _ k); [apply Z.log2_lt_pow2; lia|lia]. }
  rewrite <- Z.lxor_lor by exact NC. symmetry. apply Z.add_nocarry_lxor. exact NC.
Qed.

Lemma sbyte_land127 : forall b, 0 <= b < 256 -> Z.land (bv_unsigned (Z_to_bv 64 (sbyte b))) 127 = Z.land b 127.
Proof.
  intros b Hb. rewrite !land127_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. unfold sbyte.
  destruct (Z.ltb_spec b 128); Z.div_mod_to_equations; lia.
Qed.

Lemma land7_mod : forall x, Z.land x 7 = x mod 8.
Proof. intros x. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land3_mod : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land_m64U : forall x, 0 <= x < 18446744073709551616 -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. exact H. Qed.
Lemma lxor_s63U : forall x, 0 <= x < 9223372036854775808 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x H. symmetry. apply Z.add_nocarry_lxor. apply Z.bits_inj'. intros k Hk.
  rewrite Z.land_spec, Z.bits_0. change 9223372036854775808 with (2 ^ 63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 k) as [<-|NE]; [|apply andb_false_r]. rewrite andb_true_r.
  destruct (Z.eq_dec x 0) as [->|NZ]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma impl_post_evt : forall {R} (t : itree node R) (Q : R -> machine_state -> Prop) ms,
  impl ctusegs (at_node ctusegs) t (fun r ms' => evt ctusegs (Q r) ms') ms -> impl ctusegs (at_node ctusegs) t Q ms.
Proof.
  induction t as [r|n k IH]; intros Q ms H; cbn in *.
  - eapply evt_cut; [exact H|]. intros ms' H'. exact H'.
  - eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|]. intros rsp. apply IH. apply Hk.
Qed.

Lemma implM_post_evt : forall {A} (c : PState -> itree node (exc (A * PState))) s (Q : A -> PState -> machine_state -> Prop) ms,
  implM ctusegs c s (fun a s' ms' => evt ctusegs (Q a s') ms') ms -> implM ctusegs c s Q ms.
Proof.
  intros A c s Q ms H. unfold implM in *. apply impl_post_evt. eapply impl_mono; [exact H|].
  intros [|[a s']] ms'; cbn; [intros _; apply evt_done; exact I|intros E; exact E].
Qed.

(* [comment removed for export] *)
Lemma ap_pre_restack : forall s st m OW LB E bo sp lo B errv canary stack stack',
  ap_pre s st m OW LB E bo sp lo B errv canary stack -> lo <= bv_unsigned sp - stack' -> ap_pre s st m OW LB E bo sp lo B errv canary stack'.
Proof.
  intros until stack'. intros H Hle. unfold ap_pre in *.
  destruct H as (A1 & A2 & A2' & A2'' & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13). repeat (split; [assumption|]). assumption.
Qed.

Section Proofs.
  Hypothesis HM : rmalloc_stmt.
  Hypothesis HF : rfree_stmt.

  Section Act.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : mem) (s : PState) (st : ap_st bptr) (OW LB : list block) (E : ap_env) (bo : Z * Z) (lo B : Z) (errv canary : word) (K : list block).
  Variables (D : Z) (d : list Z) (op omax PP PL PT PC : Z) (jl j2 j3 : list byte).
  Hypothesis PRE : ap_pre s st m OW LB E bo sp lo B errv canary GETOBJ_STACK.
  Hypothesis TP : tp = wz RATP.
  Hypothesis FRM : frm0 fc.
  Hypothesis KOW : forall b, In b K -> In b OW.
  Hypothesis KIDS : forall b, In b K -> ~ In (blk_id b) (es_ids st ++ env_ids E).
  Hypothesis PAY : payload_ok m LB D d.
  Hypothesis OP0 : 0 <= op.
  Hypothesis OM0 : 0 < omax.
  Hypothesis OPM : op + omax <= zlength d.
  Hypothesis CELLS : go_cells_ok (bv_unsigned sp) PP PL PT PC.
  Hypothesis BPP : PP + 8 <= B.
  Hypothesis BPL : PL + 8 <= B.
  Hypothesis BPT : PT + 4 <= B.
  Hypothesis BPC : PC + 4 <= B.
  Hypothesis HPP : rw_cells ctusegs m PP [C8 (wz (D + op))].
  Hypothesis HPL : rw_cells ctusegs m PL [CB 8 jl].
  Hypothesis HPT : rw_cells ctusegs m PT [CB 4 j2].
  Hypothesis HPC : rw_cells ctusegs m PC [CB 4 j3].

  Let g : go_res := get_object d op omax.
  Local Notation b0 := (znth d op).
  (* [comment removed for export] *)
  Definition go_frame : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  (* [comment removed for export] *)
  Local Notation W0 := ([(bv_unsigned sp - 8464, bv_unsigned sp); (PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)]%Z) (only parsing).

  Lemma dfacts : Forall (fun c => 0 <= c < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 30
                 /\ exists b, In b LB /\ blk_addr b <= D /\ D + zlength d <= blk_addr b + blk_size b.
  Proof using OM0 OP0 OPM PAY.
    destruct PAY as (_ & HF' & D0 & D63 & D30 & HB). split; [exact HF'|]. split; [exact D0|]. split; [exact D63|]. split; [exact D30|].
    destruct HB as [->|HB]; [unfold zlength in OPM; cbn in OPM; lia|exact HB].
  Qed.

  (* [comment removed for export] *)
  Definition go_inv (m1 : mem) (cpl cpt cpc : list cell) : Prop :=
    munch W0 m m1 /\ wmono ctusegs m m1 /\ mem_inv ctusegs m1 /\ stk ctusegs m1 lo (bv_unsigned sp + -48)
    /\ rw_cells ctusegs m1 (bv_unsigned sp + -48) go_frame
    /\ rw_cells ctusegs m1 PP [C8 (Z_to_bv 64 (D + op))] /\ rw_cells ctusegs m1 PL cpl /\ rw_cells ctusegs m1 PT cpt /\ rw_cells ctusegs m1 PC cpc
    /\ bytes_at ctusegs m1 D (to_bytes d) /\ rw_cells ctusegs m1 3355012 [C4 errv].

  (* [comment removed for export] *)
  Lemma ctx_facts :
    Forall (fun c => 0 <= c < 256) d /\ 0 < D /\ D + zlength d < 2 ^ 63 /\ zlength d < 2 ^ 30 /\ D + zlength d <= alloc_ceiling
    /\ alloc_ceiling <= lo /\ 3493888 <= lo /\ lo <= bv_unsigned sp - 8464 /\ bv_unsigned sp <= B /\ B < 2 ^ 63 /\ 0 <= bv_unsigned sp < 2 ^ 64
    /\ Z.of_nat (length (to_bytes d)) = zlength d.
  Proof using OM0 OP0 OPM PAY PRE.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB & B63 & ST & CEIL & GLO & LO & ERR & SSP & MI & SP16).
    destruct dfacts as (DF & D0 & D63 & D30 & blk & HBLK & BL1 & BL2).
    pose proof (LH_block_range _ _ _ _ HEAP ltac:(apply in_app_iff; right; exact HBLK)) as (BB0 & BB1 & BB2 & BB3 & BB4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    unfold GETOBJ_STACK, ERR_SET_ERROR_STACK, GLOBALS_TOP in *.
    repeat (split; [first [assumption|lia]|]). apply zlength_to_bytes.
  Qed.

  Local Ltac go_unpack GI := destruct GI as (MU & WM & MI & ST & FR & CPP & CPL & CPT & CPC & HB & ERR); unfold go_frame in FR.
  Local Ltac ctx := pose proof ctx_facts as (DF & D0 & D63 & D30 & DCEIL & CEIL & GLO & LO & SPB & B63 & SPR & DLEN);
                   pose proof CELLS as (C1 & C2 & C3 & C4 & C12 & C13 & C14 & C23 & C24 & C34);
                   hide C12; hide C13; hide C14; hide C23; hide C24; hide C34.
  Local Ltac unhide6 := unfold hidden in *.
  Local Ltac ltb_res C := repeat match type of C with context [Z.ltb ?x ?y] => first [rewrite (proj2 (Z.ltb_lt x y)) in C by lia | rewrite (proj2 (Z.ltb_ge x y)) in C by lia] end.

  (* [comment removed for export] *)
  Lemma tag_loop_sim : forall fuel (len q max : Z) (x6 x7 x28 x29 : word) m1 cpl cpt cpc (POST : machine_state -> Prop),
    go_inv m1 cpl cpt cpc ->
    bv_unsigned x6 = 18446744073709551615 -> bv_unsigned x7 = 1 ->
    op + 1 <= q -> 1 <= max -> q + max = op + omax -> fuel = Z.to_nat max -> 0 <= len <= INT_MAX / 128 -> 128 <= znth d q ->
    (forall len' q' max' (x6' x7' x28' x29' : word), tag_loop fuel d len q max = Some (len', q', max') ->
       Z.land (znth d q') 128 = 0 -> op + 1 <= q' -> 1 <= max' -> q' + max' = op + omax -> 0 <= len' <= INT_MAX / 128 ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 (Z.shiftl len' 7)) x6' x7' sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max') (Z_to_bv 64 (sbyte (znth d q')))
                  (Z_to_bv 64 (D + q')) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' x29' t5 t6)
             F (Z_to_bv 64 0xfd928) fc None m1 (seg_rom ctusegs))) ->
    (forall (x5 x6' x7' x16 x17 x18 x28' x29' : word), tag_loop fuel d len q max = None ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6' x7' sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) x16 x17
                  x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28' x29' t5 t6)
             F (Z_to_bv 64 0xfda04) fc None m1 (seg_rom ctusegs))) ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 len) x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max) (Z_to_bv 64 (sbyte (znth d q)))
               (Z_to_bv 64 (D + q)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0xfd8f0) fc None m1 (seg_rom ctusegs)).
  Proof using CELLS OM0 OP0 OPM PAY PRE.
    clear BPP BPC BPL BPT. induction fuel as [|fuel IH]; intros until POST; intros GI X6 X7 Hq Hmax Hqm Hf Hlen B7 KEX KERR; [exfalso; lia|].
    rewrite ?IM128 in *.
    pose proof GI as GI'. go_unpack GI. ctx.
    pose proof (znth_range d q DF) as BQ.
    cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub Z.add INT_MAX] in KEX, KERR.
    destruct (land128_cases (znth d q) BQ) as [(X & _ & _)|(_ & L128 & L127)]; [exfalso; lia|].
    rewrite L128 in KEX, KERR. cbn [Z.eqb] in KEX, KERR.
    (* [comment removed for export] *)
    step. if_cases C; [exfalso; zc C; rewrite ?X6 in C; lia|clear C].
    (* [comment removed for export] *)
    step. if_cases KM; zc KM; rewrite ?X7 in KM.
    - eapply KERR. rewrite (proj2 (Z.eqb_eq (max - 1) 0)) by lia. reflexivity.
    - rewrite (proj2 (Z.eqb_neq (max - 1) 0)) in KEX, KERR by lia.
      (* [comment removed for export] *)
      assert (L127R : 0 <= Z.land (znth d q) 127 <= 127) by (rewrite L127; lia).
      assert (SL : Z.shiftl len 7 = len * 128) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
      set (len' := Z.lor (Z.shiftl len 7) (Z.land (znth d q) 127)) in KEX, KERR.
      assert (LR : len' = len * 128 + Z.land (znth d q) 127).
      { subst len'. rewrite (Z.shiftl_mul_pow2 len 7) by lia. rewrite (lor_mul_addU len (Z.land (znth d q) 127) 7) by lia. reflexivity. }
      step. rewrite (unsigned_lit len) by lia. rewrite (Z.shiftr_div_pow2 len 17) by lia. change (2 ^ 17) with 131072.
      step. if_cases KO; zc KO; rewrite ?unsigned_lit in KO by lia.
      + (* [comment removed for export] *)
        eapply KERR. rewrite (proj2 (Z.ltb_lt _ len')) by (rewrite ?IM128; lia). reflexivity.
      + rewrite (proj2 (Z.ltb_ge _ len')) in KEX, KERR by (rewrite ?IM128; lia).
        step. rewrite (sbyte_land127 (znth d q)) by lia.
        pose proof (znth_range d (q + 1) DF) as BQ1.
        pose proof (payload_read m1 D d (q + 1) (wa (D + q + 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
        rewrite (sxb_byte (znth d (q + 1))) by lia.
        step. step. rewrite (unsigned_lit len) by lia.
        step. rewrite !unsigned_lit by lia. fold len'.
        step. step.
        step. if_cases KB; zc KB.
        * (* [comment removed for export] *)
          assert (KB' : 128 <= znth d (q + 1)) by (destruct (Z.lt_ge_cases (znth d (q + 1)) 128) as [Hl|Hl]; [exfalso; pose proof (proj2 (sbyte_wrap_lt _ BQ1) Hl); lia|exact Hl]).
          replace (D + q + 1) with (D + (q + 1)) by lia. replace (max + -1) with (max - 1) by lia.
          eapply (IH len' (q + 1) (max - 1)); [exact GI'|exact X6|exact X7|lia|lia|lia|lia|lia|exact KB'| |].
          -- intros len2 q2 max2 x6' x7' x28' x29' HT. eapply KEX. exact HT.
          -- intros x5' x6' x7' x16' x17' x18' x28' x29' HT. eapply KERR. exact HT.
        * (* [comment removed for export] *)
          assert (KB' : znth d (q + 1) < 128) by (destruct (Z.lt_ge_cases (znth d (q + 1)) 128) as [Hl|Hl]; [exact Hl|exfalso; pose proof (proj1 (sbyte_wrap_lt _ BQ1)); lia]).
          pose proof (proj1 (land128_iff _ BQ1) KB') as L0.
          step. rewrite (unsigned_lit len') by lia. step.
          replace (D + q + 1) with (D + (q + 1)) by lia. replace (max + -1) with (max - 1) by lia.
          eapply (KEX len' (q + 1) (max - 1)); [|exact L0|lia|lia|lia|lia].
          destruct fuel as [|fuel']; [exfalso; lia|]. cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub Z.add INT_MAX]. rewrite L0. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition at_err (POST : machine_state -> Prop) : Prop :=
    forall (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 : word) m1 cpl cpt cpc, go_inv m1 cpl cpt cpc ->
      cells_size cpl = 8%nat -> cells_size cpt = 4%nat -> cells_size cpc = 4%nat ->
      evt ctusegs POST
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
                 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
            F (Z_to_bv 64 0xfda04) fc None m1 (seg_rom ctusegs)).

  Lemma tag_fin : forall len q max (x5 x6 x7 x28 x29 : word) m1 (POST : machine_state -> Prop),
    go_inv m1 [CB 8 jl] [CB 4 j2] [CB 4 j3] -> x5 = Z_to_bv 64 (Z.shiftl len 7) ->
    op + 1 <= q -> 1 <= max -> q + max = op + omax -> 0 <= len <= INT_MAX / 128 -> znth d q < 128 -> Z.land (znth d op) 31 = 31 ->
    tag_loop (Z.to_nat (omax - 1)) d 0 (op + 1) (omax - 1) = Some (len, q, max) ->
    (forall tag p1 max1 (x5 x6 x7 x18 x28 x29 : word) m1,
       go_hdr d op omax = Some (tag, p1, max1) -> op + 1 <= p1 -> 1 <= max1 -> max1 = omax - (p1 - op) -> 0 <= tag <= INT_MAX ->
       go_inv m1 [CB 8 jl] [CB 4 j2] [CB 4 j3] -> x18 = Z_to_bv 64 (D + p1 - 1) ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max1) (Z_to_bv 64 tag)
                  x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
             F (Z_to_bv 64 0xfd97c) fc None m1 (seg_rom ctusegs))) ->
    (go_hdr d op omax = None -> at_err POST) ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max) (Z_to_bv 64 (sbyte (znth d q)))
               (Z_to_bv 64 (D + q)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0xfd928) fc None m1 (seg_rom ctusegs)).
  Proof using CELLS OM0 OP0 OPM PAY PRE.
    clear BPP BPC BPL BPT. intros until POST. intros GI -> Hq Hmax Hqm Hlen B7 K31 HT KLEN KERR.
    rewrite ?IM128 in *. pose proof GI as GI'. go_unpack GI. ctx.
    pose proof (znth_range d q DF) as BQ. pose proof (znth_range d op DF) as B0R.
    destruct (land128_cases (znth d q) BQ) as [(_ & L128 & L127)|(X & _ & _)]; [|exfalso; lia].
    unfold go_hdr in KLEN, KERR. rewrite K31, Z.eqb_refl in KLEN, KERR. rewrite (proj2 (Z.eqb_neq (omax - 1) 0)) in KLEN, KERR by lia.
    rewrite HT, L127 in KLEN, KERR.
    assert (SL : Z.shiftl len 7 = len * 128) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
    assert (TR : Z.lor (Z.shiftl len 7) (znth d q) = len * 128 + znth d q).
    { rewrite (Z.shiftl_mul_pow2 len 7) by lia. rewrite (lor_mul_addU len (znth d q) 7) by lia. reflexivity. }
    assert (SB : sbyte (znth d q) = znth d q) by (unfold sbyte; rewrite (proj2 (Z.ltb_lt _ _)) by lia; reflexivity).
    rewrite SB.
    step. step. if_cases C; [exfalso; zc C; lia|clear C].
    step. step. if_cases K2; zc K2.
    - eapply KERR; [rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity|exact GI'|reflexivity|reflexivity|reflexivity].
    - rewrite (proj2 (Z.eqb_neq (max - 1) 0)) in KLEN by lia.
      step. rewrite !unsigned_lit by lia. step.
      replace (max + -1) with (max - 1) by lia.
      eapply (KLEN (Z.lor (Z.shiftl len 7) (znth d q)) (q + 1) (max - 1)); [reflexivity|lia|lia|lia|unfold INT_MAX; lia|exact GI'|f_equal; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma stage_tag : forall (t0 t1 t2 t3 a5 a6 a7 : word) (POST : machine_state -> Prop),
    (forall tag p1 max1 (x5 x6 x7 x18 x28 x29 : word) m1,
       go_hdr d op omax = Some (tag, p1, max1) -> op + 1 <= p1 -> 1 <= max1 -> max1 = omax - (p1 - op) -> 0 <= tag <= INT_MAX ->
       go_inv m1 [CB 8 jl] [CB 4 j2] [CB 4 j3] -> x18 = Z_to_bv 64 (D + p1 - 1) ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max1) (Z_to_bv 64 tag)
                  x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
             F (Z_to_bv 64 0xfd97c) fc None m1 (seg_rom ctusegs))) ->
    (go_hdr d op omax = None -> at_err POST) ->
    evt ctusegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz PP) (wz PL) (wz PT) (wz PC) (wz omax) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_GET_OBJECT) fc None m (seg_rom ctusegs)).
  Proof using CELLS HPC HPL HPP HPT OM0 OP0 OPM PAY PRE.
    clear BPP BPC BPL BPT. intros until POST. intros KLEN KERR.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST & CEIL' & GLO' & LO' & ERR & SSP & MI & SP16). ctx.
    destruct PAY as (HB & _).
    pose proof HPP as CPP. pose proof HPL as CPL. pose proof HPT as CPT. pose proof HPC as CPC. unfold MallocRep.wz in CPP.
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    unfold MallocRep.wz in ERR. rewrite EA in ERR.
    unfold GETOBJ_STACK, ERR_SET_ERROR_STACK, GLOBALS_TOP, ASN1_GET_OBJECT, MallocRep.wz in *.
    pose proof (munch_refl W0 m) as MU. pose proof (wmono_refl ctusegs m) as WM.
    pose proof (znth_range d op DF) as B0R. pose proof (rw_cells_bound _ _ _ _ HPP) as RBP. pose proof (rw_cells_bound _ _ _ _ HPL) as RBL. pose proof (rw_cells_bound _ _ _ _ HPT) as RBT. pose proof (rw_cells_bound _ _ _ _ HPC) as RBC. cbn [cells_size csize] in RBP, RBL, RBT, RBC.
    pose proof KLEN as KLEN0. pose proof KERR as KERR0.
    carve_frame 48%nat ST. do 7 step. step.
    step. if_cases C; [exfalso; zc C; lia|clear C].
    step.
    step. step. if_cases C; [exfalso; zc C; rewrite ?land7_mod in C; rewrite ?unsigned_lit in C by lia; unhide6; lia|clear C].
    (* [comment removed for export] *)
    step. if_cases KK; [exfalso; zc KK; rewrite ?signed_small in KK by lia; lia|clear KK].
    (* [comment removed for export] *)
    step.
    step. if_cases C; [exfalso; zc C; lia|clear C].
    pose proof (payload_read _ D d op (wa (D + op)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit (znth d op)) by lia.
    step. rewrite (unsigned_lit (znth d op)) by lia. step.
    name_mem m1.
    assert (GI : go_inv m1 [CB 8 jl] [CB 4 j2] [CB 4 j3]).
    { split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|]. split; [exact CPP|]. split; [exact CPL|].
      split; [exact CPT|]. split; [exact CPC|]. split; [exact HB|exact ERR]. }
    assert (L31 : 0 <= Z.land (znth d op) 31 <= 31).
    { split; [apply Z.land_nonneg; right; lia|]. change 31 with (Z.ones 5) at 1. rewrite Z.land_ones by lia. change (2 ^ 5) with 32. pose proof (Z.mod_pos_bound (znth d op) 32). lia. }
    unfold go_hdr in KLEN, KERR.
    step. if_cases KT; zc KT.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) KT) in KLEN, KERR.
      step. step. if_cases C; [exfalso; zc C; lia|clear C].
      step. step. step. if_cases K1; zc K1.
      + eapply KERR; [rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity|exact GI|reflexivity|reflexivity|reflexivity].
      + rewrite (proj2 (Z.eqb_neq (omax - 1) 0)) in KLEN by lia.
        replace (omax + -1) with (omax - 1) by lia.
        eapply (KLEN (Z.land (znth d op) 31) (op + 1) (omax - 1)); [reflexivity|lia|lia|lia|unfold INT_MAX; lia|exact GI|f_equal; lia].
    - (* [comment removed for export] *)
      rewrite KT, Z.eqb_refl in KLEN, KERR.
      step. step. if_cases C; [exfalso; zc C; lia|clear C].
      step. step. if_cases K1; zc K1.
      + eapply KERR; [rewrite (proj2 (Z.eqb_eq _ _)) by lia; reflexivity|exact GI|reflexivity|reflexivity|reflexivity].
      + rewrite (proj2 (Z.eqb_neq (omax - 1) 0)) in KLEN, KERR by lia.
        pose proof (znth_range d (op + 1) DF) as B1.
        pose proof (payload_read _ D d (op + 1) (wa (D + op + 1)) HB DF ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD. step. clear RD.
        rewrite (sxb_byte (znth d (op + 1))) by lia.
        step. step. step. if_cases KB; zc KB.
        * apply (sbyte_wrap_lt (znth d (op + 1)) B1) in KB. pose proof (proj1 (land128_iff (znth d (op + 1)) B1) KB) as L0.
          replace (omax + -1) with (omax - 1) by lia. replace (D + op + 1) with (D + (op + 1)) by lia.
          eapply (tag_fin 0 (op + 1) (omax - 1)); [exact GI|reflexivity|lia|lia|lia|rewrite ?IM128; lia|exact KB|exact KT| |exact KLEN0|exact KERR0].
          destruct (Z.to_nat (omax - 1)) as [|n] eqn:EF; [exfalso; lia|]. cbn -[Z.shiftl Z.lor Z.land Z.ltb Z.div Z.eqb Z.sub Z.add INT_MAX]. rewrite L0. reflexivity.
        * assert (KB' : 128 <= znth d (op + 1)) by (destruct (Z.lt_ge_cases (znth d (op + 1)) 128) as [Hl|Hl]; [exfalso; pose proof (proj2 (sbyte_wrap_lt _ B1) Hl); lia|exact Hl]).
          step. step.
          replace (omax + -1) with (omax - 1) by lia. replace (D + op + 1) with (D + (op + 1)) by lia.
          eapply (tag_loop_sim (Z.to_nat (omax - 1)) 0 (op + 1) (omax - 1)); [exact GI|reflexivity|reflexivity|lia|lia|lia|reflexivity|rewrite ?IM128; lia|exact KB'| |].
          -- (* [comment removed for export] *)
             intros len' q' max' x6' x7' x28' x29' HT L0 Hq' Hm' Hqm' Hl'.
             pose proof (znth_range d q' DF) as BQ'.
             eapply (tag_fin len' q' max'); [exact GI|reflexivity|lia|lia|lia|exact Hl'|exact (proj2 (land128_iff _ BQ') L0)|exact KT|exact HT|exact KLEN0|exact KERR0].
          -- intros x5' x6' x7' x16 x17 x18 x28' x29' HT. eapply KERR; [rewrite HT; reflexivity|exact GI|reflexivity|reflexivity|reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma zskip_sim : forall fuel (p cnt e : Z) (x5 x6 x7 x12 x28 x29 : word) m2 cpl cpt cpc (POST : machine_state -> Prop),
    go_inv m2 cpl cpt cpc -> bv_unsigned x5 = 18446744073709551615 ->
    op + 2 <= p -> 0 < cnt -> p + cnt = e -> e <= op + omax -> fuel = Z.to_nat cnt -> cnt <= 127 ->
    (forall p' cnt', skip_zeros fuel d p cnt = (p', cnt') -> 0 < cnt' -> znth d p' <> 0 -> p <= p' -> p' + cnt' = e ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 (Z_to_bv 64 (znth d p')) x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12 (Z_to_bv 64 cnt') (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 (D + e)) (Z_to_bv 64 cnt')
                  (Z_to_bv 64 (D + p')) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
             F (Z_to_bv 64 0xfdaf8) fc None m2 (seg_rom ctusegs))) ->
    (forall p' (x6' x17' : word), skip_zeros fuel d p cnt = (p', 0) -> p' = e ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6' x7 sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12 (Z_to_bv 64 0) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 (D + e)) x17'
                  (Z_to_bv 64 (D + e)) (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
             F (Z_to_bv 64 0xfd9e4) fc None m2 (seg_rom ctusegs))) ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12 (Z_to_bv 64 cnt) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 (D + e)) (Z_to_bv 64 cnt)
               (Z_to_bv 64 (D + p)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0xfdacc) fc None m2 (seg_rom ctusegs)).
  Proof using CELLS OM0 OP0 OPM PAY PRE.
    clear BPP BPC BPL BPT. induction fuel as [|fuel IH]; intros until POST; intros GI X5 Hp Hc Hpc He Hf Hc7 KNZ KZ; [exfalso; lia|].
    pose proof GI as GI'. go_unpack GI. ctx.
    pose proof (znth_range d p DF) as BP.
    cbn -[Z.ltb Z.eqb Z.sub Z.add znth] in KNZ, KZ. rewrite (proj2 (Z.ltb_lt 0 cnt) Hc) in KNZ, KZ. cbn [andb] in KNZ, KZ.
    pose proof (payload_read m2 D d p (wa (D + p)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit (znth d p)) by lia.
    step. if_cases KB; zc KB.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ _) KB) in KNZ. eapply KNZ; [reflexivity|lia|exact KB|lia|lia].
    - rewrite KB, Z.eqb_refl in KNZ, KZ.
      step. if_cases C; [exfalso; zc C; rewrite ?X5 in C; lia|clear C].
      step. step. rewrite (unsigned_lit cnt), bk_swrap32_small by lia. step.
      step. if_cases KC; zc KC.
      + (* [comment removed for export] *)
        replace (D + p + 1) with (D + (p + 1)) by lia.
        eapply (IH (p + 1) (cnt + -1) e); [exact GI'|exact X5|lia|lia|lia|lia|lia|lia| |].
        * intros p' cnt' HS. replace (cnt - 1) with (cnt + -1) in KNZ by lia.
          intros. eapply KNZ; [exact HS|lia|assumption|lia|lia].
        * intros p' x6' x17' HS. replace (cnt - 1) with (cnt + -1) in KZ by lia.
          intros. eapply KZ; [exact HS|lia].
      + (* [comment removed for export] *)
        step. step. step. step.
        assert (C1' : cnt = 1) by lia. assert (F0 : fuel = 0%nat) by lia. subst fuel.
        replace (cnt - 1) with 0 in KZ by lia. cbn -[Z.add] in KZ.
        eapply KZ; [reflexivity|lia].
  Qed.

  (* [comment removed for export] *)
  Lemma acc_sim : forall fuel (r e acc : Z) (x5 x6 x7 x12 x17 x28 x29 : word) m2 cpl cpt cpc (POST : machine_state -> Prop),
    go_inv m2 cpl cpt cpc -> bv_unsigned x5 = 18446744073709551615 -> x6 = Z_to_bv 64 1 -> x17 = Z_to_bv 64 (e - r + 1) ->
    op + 2 <= r -> r < e -> e <= op + omax -> e - r <= 8 -> fuel = Z.to_nat (e - r) -> 0 <= acc < 2 ^ (64 - 8 * (e - r)) ->
    (forall ret accp (x17' : word), be_octets fuel d r (e - r) acc = (ret, e) -> ret = accp * 256 + znth d (e - 1) -> 0 <= accp < 2 ^ 56 ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 (Z_to_bv 64 (accp * 256)) sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12 (Z_to_bv 64 ret) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 (D + e)) x17'
                  (Z_to_bv 64 (D + e)) s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (znth d (e - 1))) x29 t5 t6)
             F (Z_to_bv 64 0xfdb34) fc None m2 (seg_rom ctusegs))) ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) x12 (Z_to_bv 64 acc) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 (D + e)) x17
               (Z_to_bv 64 (D + r)) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0xfdb18) fc None m2 (seg_rom ctusegs)).
  Proof using BPC BPP CELLS OM0 OP0 OPM PAY PRE.
    clear BPL BPT. induction fuel as [|fuel IH]; intros until POST; intros GI X5 -> -> Hr Hre He H8 Hf Hacc KEX; [exfalso; lia|].
    pose proof GI as GI'. go_unpack GI. ctx.
    pose proof (znth_range d r DF) as BR.
    cbn -[Z.ltb Z.mul Z.add Z.sub znth] in KEX. rewrite (proj2 (Z.ltb_lt 0 (e - r))) in KEX by lia.
    assert (P8 : 2 ^ (64 - 8 * (e - r)) * 256 = 2 ^ (64 - 8 * (e - (r + 1)))).
    { replace (64 - 8 * (e - (r + 1))) with (64 - 8 * (e - r) + 8) by lia. rewrite Z.pow_add_r by lia. reflexivity. }
    assert (P64 : 2 ^ (64 - 8 * (e - (r + 1))) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    step. if_cases C; [exfalso; zc C; rewrite ?X5 in C; lia|clear C].
    pose proof (payload_read m2 D d r (wa (D + r)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit (znth d r)) by lia.
    step. rewrite (unsigned_lit acc) by lia. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
    step.
    step. rewrite (unsigned_lit (e - r + 1)), bk_swrap32_small by lia.
    step. rewrite !unsigned_lit by lia.
    assert (OR : Z.lor (acc * 256) (znth d r) = acc * 256 + znth d r).
    { change 256 with (2 ^ 8). apply lor_mul_addU; lia. }
    rewrite OR.
    step. if_cases KC; zc KC; rewrite ?signed_small in KC by lia.
    - (* [comment removed for export] *)
      replace (D + r + 1) with (D + (r + 1)) by lia.
      eapply (IH (r + 1) e (acc * 256 + znth d r)); [exact GI'|exact X5|reflexivity|f_equal; lia|lia|lia|lia|lia|lia|lia|].
      intros ret accp x17' HB' Hret Haccp. replace (e - r - 1) with (e - (r + 1)) in KEX by lia. eapply KEX; [exact HB'|exact Hret|exact Haccp].
    - (* [comment removed for export] *)
      assert (E1 : e = r + 1) by lia. assert (F0 : fuel = 0%nat) by lia. subst fuel. subst e. cbn -[Z.mul Z.add Z.sub znth] in KEX.
      replace (r + 1 - 1) with r in KEX by lia. replace (D + r + 1) with (D + (r + 1)) by lia.
      eapply (KEX (acc * 256 + znth d r) acc); [f_equal; f_equal; lia|reflexivity|].
      replace (64 - 8 * (r + 1 - r)) with 56 in Hacc by lia. exact Hacc.
  Qed.

  Lemma store_len : forall (inf : bool) len pl p2 (x5 x6 x7 x16 x17 x28 x29 : word) m2 cpt cpc (POST : machine_state -> Prop),
    go_inv m2 [CB 8 jl] cpt cpc -> cells_size cpt = 4%nat -> cells_size cpc = 4%nat -> 0 <= len < 2 ^ 63 -> 0 <= pl < zlength d ->
    (inf = true -> znth d pl = 128) -> (inf = false -> znth d pl <> 128) ->
    (forall (x5' x6' x7' x11 x16' x17' x28' x29' : word) m3, go_inv m3 [C8 (Z_to_bv 64 len)] cpt cpc -> inf && (Z.land (znth d op) 32 =? 0) = false ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5' x6' x7' sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) x11 (Z_to_bv 64 (znth d pl)) (Z_to_bv 64 len) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) x16' x17'
                  (Z_to_bv 64 (D + p2)) (Z_to_bv 64 (if inf then 1 else 0)) (Z_to_bv 64 (Z.land (znth d op) 32)) s5 s6 s7 s8 s9 s10 s11 x28' x29' t5 t6)
             F (Z_to_bv 64 0xfda54) fc None m3 (seg_rom ctusegs))) ->
    (inf = true -> Z.land (znth d op) 32 = 0 -> at_err POST) ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 (znth d pl)) (Z_to_bv 64 len) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) x16 x17
               (Z_to_bv 64 (D + p2)) (Z_to_bv 64 (if inf then 1 else 0)) s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0xfd9e4) fc None m2 (seg_rom ctusegs)).
  Proof using CELLS OM0 OP0 OPM PAY PRE.
    clear BPP BPC BPL BPT. intros until POST. intros GI SZT SZC Hlen Hpl INF1 INF0 KDEC KERR.
    go_unpack GI. ctx. unhide6. pose proof (rw_cells_bound _ _ _ _ CPL) as RBL. cbn [cells_size csize] in RBL.
    pose proof (znth_range d op DF) as B0R. pose proof (znth_range d pl DF) as BPLR.
    assert (L32 : 0 <= Z.land (znth d op) 32 <= 32) by (pose proof (land_32_cases (znth d op)); lia).
    step. if_cases C; [exfalso; zc C; lia|clear C].
    step. step. if_cases C; [exfalso; zc C; rewrite ?land7_mod in C; rewrite ?unsigned_lit in C by lia; lia|clear C].
    step. rewrite (unsigned_lit (znth d op)) by lia.
    step.
    name_mem m3.
    assert (GI3 : go_inv m3 [C8 (Z_to_bv 64 len)] cpt cpc).
    { split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact FR|]. split; [exact CPP|]. split; [exact CPL|].
      split; [exact CPT|]. split; [exact CPC|]. split; [exact HB|exact ERR]. }
    step. if_cases KC; zc KC.
    - eapply KDEC; [exact GI3|rewrite (proj2 (Z.eqb_neq _ _) KC); apply Bool.andb_false_r].
    - step. step. if_cases K80; zc K80.
      + destruct inf; [exfalso; rewrite (INF1 eq_refl) in K80; lia|]. eapply KDEC; [exact GI3|reflexivity].
      + destruct inf; [|exfalso; exact (INF0 eq_refl K80)].
        eapply (KERR eq_refl KC); [exact GI3|reflexivity|exact SZT|exact SZC].
  Qed.

  (* [comment removed for export] *)
  Lemma stage_len : forall tag p1 max1 (x5 x6 x7 x18 x28 x29 : word) m1 (POST : machine_state -> Prop),
    go_hdr d op omax = Some (tag, p1, max1) -> op + 1 <= p1 -> 1 <= max1 -> max1 = omax - (p1 - op) -> 0 <= tag <= INT_MAX ->
    go_inv m1 [CB 8 jl] [CB 4 j2] [CB 4 j3] -> x18 = Z_to_bv 64 (D + p1 - 1) ->
    (forall (inf : bool) len p2 (x5' x6' x7' x11 x12 x16 x17 x28' x29' : word) m2,
       get_length d p1 max1 = Some (inf, len, p2) -> inf && (Z.land (znth d op) 32 =? 0) = false -> p1 + 1 <= p2 <= op + omax -> 0 <= len ->
       go_inv m2 [C8 (Z_to_bv 64 len)] [C4 (Z_to_bv 64 tag)] [C4 (Z_to_bv 64 (Z.land (znth d op) 192))] ->
       evt ctusegs POST
         (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5' x6' x7' sp (Z_to_bv 64 PP)
                  (Z_to_bv 64 (D + op)) x11 x12 (Z_to_bv 64 len) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) x16 x17
                  (Z_to_bv 64 (D + p2)) (Z_to_bv 64 (if inf then 1 else 0)) (Z_to_bv 64 (Z.land (znth d op) 32)) s5 s6 s7 s8 s9 s10 s11 x28' x29' t5 t6)
             F (Z_to_bv 64 0xfda54) fc None m2 (seg_rom ctusegs))) ->
    (get_length d p1 max1 = None -> at_err POST) ->
    (forall len p2, get_length d p1 max1 = Some (true, len, p2) -> Z.land (znth d op) 32 = 0 -> at_err POST) ->
    evt ctusegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP)
               (Z_to_bv 64 (D + op)) (Z_to_bv 64 PL) (Z_to_bv 64 PT) (Z_to_bv 64 PC) (Z_to_bv 64 omax) (Z_to_bv 64 (znth d op)) (Z_to_bv 64 max1) (Z_to_bv 64 tag)
               x18 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 0xfd97c) fc None m1 (seg_rom ctusegs)).
  Proof using BPC BPP CELLS OM0 OP0 OPM PAY PRE.
    clear BPL BPT. intros until POST. intros GH Hp1 Hm1 Hm1' Htag GI -> KDEC KERR1 KERR2.
    go_unpack GI. ctx. unhide6. pose proof (rw_cells_bound _ _ _ _ CPT) as RBT. pose proof (rw_cells_bound _ _ _ _ CPC) as RBC. cbn [cells_size csize] in RBT, RBC. (* [comment removed for export] *)
    pose proof (znth_range d op DF) as B0R. pose proof (znth_range d p1 DF) as B1R.
    assert (L192 : 0 <= Z.land (znth d op) 192 <= 192) by (pose proof (land_192_cases (znth d op)); lia).
    assert (L32 : 0 <= Z.land (znth d op) 32 <= 32) by (pose proof (land_32_cases (znth d op)); lia).
    unfold INT_MAX in Htag.
    (* [comment removed for export] *)
    step. if_cases C; [exfalso; zc C; lia|clear C].
    step. step. if_cases C; [exfalso; zc C; rewrite ?land3_mod in C; rewrite ?unsigned_lit in C by lia; lia|clear C].
    step.
    step. if_cases C; [exfalso; zc C; lia|clear C].
    step. step. if_cases C; [exfalso; zc C; rewrite ?land3_mod in C; rewrite ?unsigned_lit in C by lia; lia|clear C].
    step. rewrite (unsigned_lit (znth d op)) by lia.
    step. replace (D + p1 - 1 + 1) with (D + p1) by lia.
    step.
    name_mem m2.
    assert (GI' : go_inv m2 [CB 8 jl] [Cells.C4 (Z_to_bv 64 tag)] [Cells.C4 (Z_to_bv 64 (Z.land (znth d op) 192))]) by (split; [exact MU|split; [exact WM|split; [exact MI|split; [exact ST|split; [exact FR|split; [exact CPP|split; [exact CPL|split; [exact CPT|split; [exact CPC|split; [exact HB|exact ERR]]]]]]]]]]).
    (* [comment removed for export] *)
    pose proof (payload_read _ D d p1 (wa (D + p1)) HB DF ltac:(lia) eq_refl) as RD. step. clear RD.
    rewrite (zxb_lit (znth d p1)) by lia.
    step.
    unfold get_length in KDEC, KERR1, KERR2. rewrite (proj2 (Z.ltb_ge max1 1)) in KDEC, KERR1, KERR2 by lia.
    step. if_cases K80; zc K80.
    - (* [comment removed for export] *)
      rewrite (proj2 (Z.eqb_neq _ 128) K80) in KDEC, KERR1, KERR2.
      step. step. if_cases C; [exfalso; zc C; lia|clear C].
      step. rewrite (unsigned_lit (znth d p1)) by lia. step. step. replace (D + p1 - 1 + 2) with (D + (p1 + 1)) by lia.
      step. if_cases KL; zc KL.
      + (* [comment removed for export] *)
        apply (shl56_sign (znth d p1) B1R) in KL.
        destruct (land128_cases (znth d p1) B1R) as [(X & _)|(_ & L128 & L127)]; [exfalso; lia|].
        rewrite L128 in KDEC, KERR1, KERR2. cbn [Z.eqb] in KDEC, KERR1, KERR2. rewrite L127 in KDEC, KERR1, KERR2 |- *.
        set (i := znth d p1 - 128) in *.
        (* [comment removed for export] *)
        step. if_cases KI; zc KI.
        * rewrite (proj2 (Z.ltb_lt (max1 - 1) i)) in KERR1 by lia.
          eapply KERR1; [reflexivity|exact GI'|reflexivity|reflexivity|reflexivity].
        * rewrite (proj2 (Z.ltb_ge (max1 - 1) i)) in KDEC, KERR1, KERR2 by lia.
          step. if_cases KZ0; [exfalso; zc KZ0; lia|clear KZ0].
          (* [comment removed for export] *)
          step. rewrite ?(unsigned_lit i), ?bk_swrap32_small by lia.
          step. step. rewrite ?(zext32_idem (i + -1)) by lia.
          step. rewrite ?unsigned_lit by lia. step.
          replace (D + p1 + (i + -1) + 2) with (D + (p1 + 1 + i)) by lia.
          step. step.
          eapply (zskip_sim (Z.to_nat i) (p1 + 1) i (p1 + 1 + i)); [exact GI'|reflexivity|lia|lia|lia|lia|reflexivity|lia| |].
          -- (* [comment removed for export] *)
             intros p' i' HS Hi' NZ Hp' Hpi'. rewrite HS in KDEC, KERR1.
             step. step. if_cases K8; zc K8.
             ** (* [comment removed for export] *)
                rewrite (proj2 (Z.ltb_lt 8 i')) in KERR1 by lia.
                eapply KERR1; [reflexivity|exact GI'|reflexivity|reflexivity|reflexivity].
             ** rewrite (proj2 (Z.ltb_ge 8 i')) in KDEC, KERR1 by lia.
                step. if_cases KQ; [exfalso; zc KQ; lia|clear KQ].
                step. rewrite ?(unsigned_lit i'), ?bk_swrap32_small by lia.
                step. rewrite ?unsigned_lit by lia. replace (D + p' + i') with (D + (p' + i')) by lia.
                step. step. step.
                assert (P2 : 0 <= 0 < 2 ^ (64 - 8 * (p' + i' - p'))) by (split; [lia|]; apply Z.pow_pos_nonneg; lia).
                eapply (acc_sim (Z.to_nat i') p' (p' + i') 0); [exact GI'|reflexivity|reflexivity|f_equal; lia|lia|lia|lia|lia|f_equal; lia|exact P2|].
                intros ret accp x17' HBE Hret Haccp. replace (p' + i' - p') with i' in HBE by lia. rewrite HBE in KDEC, KERR1.
                pose proof (znth_range d (p' + i' - 1) DF) as BL.
                (* [comment removed for export] *)
                step. if_cases KS; zc KS.
                +++ rewrite (proj2 (Z.ltb_lt LONG_MAX ret)) in KERR1 by (unfold LONG_MAX; lia).
                    eapply KERR1; [reflexivity|exact GI'|reflexivity|reflexivity|reflexivity].
                +++ rewrite (proj2 (Z.ltb_ge LONG_MAX ret)) in KDEC by (unfold LONG_MAX; lia).
                    pose proof (be_octets_bounds _ _ _ _ _ _ _ HBE ltac:(lia) ltac:(eapply Forall_impl; [|exact DF]; intros c Hc; cbn in Hc; lia)) as (_ & _ & RET0).
                    step. step. step. step.
                    eapply (store_len false ret p1 (p' + i')); [exact GI'|reflexivity|reflexivity|unfold LONG_MAX in *; lia|lia|intros X; discriminate X|intros _; exact K80| |intros X; discriminate X].
                    intros x5' x6' x7' x11 x16 x17 x28' x29' m3 GI3 HI. eapply (KDEC false ret (p' + i')); [reflexivity|exact HI|lia|lia|exact GI3].
          -- (* [comment removed for export] *)
             intros p' x6' x17' HS Hp'. rewrite HS in KDEC. subst p'.
             eapply (store_len false 0 p1 (p1 + 1 + i)); [exact GI'|reflexivity|reflexivity|lia|lia|intros X; discriminate X|intros _; exact K80| |intros X; discriminate X].
             intros x5' x6'' x7' x11 x16 x17'' x28' x29' m3 GI3 HI. eapply (KDEC false 0 (p1 + 1 + i)); [cbn; reflexivity|exact HI|lia|lia|exact GI3].
      + (* [comment removed for export] *)
        assert (KL' : znth d p1 < 128) by (destruct (Z.lt_ge_cases (znth d p1) 128) as [X|X]; [exact X|exfalso; pose proof (proj2 (shl56_sign _ B1R) X); lia]).
        destruct (land128_cases (znth d p1) B1R) as [(_ & L128 & L127)|(X & _)]; [|exfalso; lia].
        rewrite L128, Z.eqb_refl in KDEC. rewrite L127.
        step.
        eapply (store_len false (znth d p1) p1 (p1 + 1)); [exact GI'|reflexivity|reflexivity|lia|lia|intros X; discriminate X|intros _; exact K80| |intros X; discriminate X].
        intros x5' x6' x7' x11 x16 x17 x28' x29' m3 GI3 HI. eapply (KDEC false (znth d p1) (p1 + 1)); [rewrite L127; reflexivity|exact HI|lia|lia|exact GI3].
    - (* [comment removed for export] *)
      rewrite K80, Z.eqb_refl in KDEC, KERR2.
      step. step. if_cases C; [exfalso; zc C; lia|clear C].
      step. step. replace (D + p1 - 1 + 2) with (D + (p1 + 1)) by lia. step. step.
      eapply (store_len true 0 p1 (p1 + 1)); [exact GI'|reflexivity|reflexivity|lia|lia|intros _; exact K80|intros X; discriminate X| |].
      + intros x5' x6' x7' x11 x16 x17 x28' x29' m3 GI3 HI. rewrite K80. eapply (KDEC true 0 (p1 + 1)); [reflexivity|exact HI|lia|lia|exact GI3].
      + intros _ HZ. exact (KERR2 0 (p1 + 1) eq_refl HZ).
  Qed.

  (* [comment removed for export] *)
  Lemma pre_at_call : forall m2 cpl cpt cpc, go_inv m2 cpl cpt cpc ->
    ap_pre s st m2 OW LB E bo (Z_to_bv 64 (bv_unsigned sp + -48)) lo B errv canary ERR_SET_ERROR_STACK
    /\ lx_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_AP) m m2
    /\ kept K m m2.
  Proof using BPC BPL BPP BPT CELLS KOW OM0 OP0 OPM PAY PRE.
    intros m2 cpl cpt cpc GI. go_unpack GI. ctx.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    assert (HW : Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= B) W0) by (repeat constructor; cbn; lia).
    split; [|split].
    - unfold ap_pre. rewrite ESP. split.
      { eapply LH_frame; [exact HEAP|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. apply W_ok_stack. cbn in *. lia. }
      split. { eapply (ap_state_of_munch st m m2); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch s (OW ++ LB) _ m m2); [exact DC|intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q k OD Hd))|exact HEAP|exact CEIL|exact MU|exact WM|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
      split. { eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. cbn in *. unfold RAUXV_CELL, GLOBALS_TOP in *. lia. }
      split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [unfold ERR_SET_ERROR_STACK; lia|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; eapply LH_frame; [exact HEAP|exact MU|exact WM|]; eapply Forall_impl; [|exact HW]; intros [x y] [Hx Hy]; apply W_ok_stack; cbn in *; lia|].
      split; [exact MI|]. replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) by lia. rewrite Zminus_mod, SP16. reflexivity.
    - eapply lx_pres_of_munch; [exact MU|exact WM|]. intros a Ha [HX Hc]. cbn [rin_ivs fst snd app] in HX. cbn.
      destruct Hc as [Hc|[(b & Hb & Hr)|Hc]].
      + repeat split; try lia; tauto.
      + destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr.
        pose proof (blk_bounds _ _ _ q A n HEAP ltac:(apply in_app_iff; right; exact Hb)). repeat split; lia.
      + unfold ralloc_static in Hc. repeat split; lia.
    - eapply (kept_of_munch s (OW ++ LB) _ m m2 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Definition site_ok (base line reason : Z) (rs : rsite) : Prop :=
    (base = 0xfda6c /\ line = 95 /\ reason = 155 /\ rs = RS_too_long) \/ (base = 0xfda04 /\ line = 105 /\ reason = 123 /\ rs = RS_hdr_too_long).

  (* [comment removed for export] *)
  Definition raise_post (base : Z) (x18 x19 x20 : word) (m2 : mem) (r : unit * ap_st bptr) (s' : PState) : machine_state -> Prop :=
    fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) m' OW' (errv' : word),
      ms' = MS (mkR (Z_to_bv 64 (base + 44)) (Z_to_bv 64 (bv_unsigned sp + -48)) gp (wz RATP) t0 t1 t2 sp (Z_to_bv 64 PP) a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 t3 t4' t5' t6')
               F' (Z_to_bv 64 (base + 44)) fc' None m' (seg_rom ctusegs)
      /\ frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k)
      /\ ap_pre s' (snd r) m' OW' LB E bo (Z_to_bv 64 (bv_unsigned sp + -48)) lo B errv' canary 0
      /\ lx_pres LB (bv_unsigned sp + -48) LIBW_AP m2 m'
      /\ ps_so s' = ps_so s /\ ps_fa s' = ps_fa s
      /\ blocks_kept K (snd r) OW' m m'.

  Lemma raise_seq : forall base line reason rs (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 : word) m2 cpl cpt cpc,
    site_ok base line reason rs -> go_inv m2 cpl cpt cpc ->
    implM ctusegs (interp (ap_embed (err_raise rs st))) s (raise_post base x18 x19 x20 m2)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp x5 x6 x7 sp (Z_to_bv 64 PP) x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20
               s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
          F (Z_to_bv 64 base) fc None m2 (seg_rom ctusegs)).
  Proof using BPC BPL BPP BPT CELLS FRM HF HM KIDS KOW OM0 OP0 OPM PAY PRE TP.
    intros until cpc. intros SITE GI.
    destruct (pre_at_call m2 cpl cpt cpc GI) as (PRE2 & LX2 & KP2).
    go_unpack GI. ctx. subst tp.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    destruct (lit_ok_auto A_ASN1_LIB_C 23 ltac:(vm_compute; reflexivity)) as (fs & fk & LF).
    destruct (lit_ok_auto A_ASN1_GET_OBJECT 16 ltac:(vm_compute; reflexivity)) as (ns & nk & LN).
    unfold err_raise.
    destruct SITE as [(-> & -> & -> & ->)|(-> & -> & -> & ->)].
    - unfold implM. iprefix. step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      eapply implM_abind.
      { pose proof (ERR_new_walk HF bo) as W. unfold ap_stmt in W. eapply W; [eapply ap_pre_stack_le; [exact PRE2|unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM|reflexivity|exact KOW|exact KIDS]. }
      intros r1 sA ms1 PO1. cbv beta in PO1.
      destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                       & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa & EBO1).
      subst bo1. replace (ret_pc (Z_to_bv 64 (1038956 + 4))) with (Z_to_bv 64 (1038956 + 4)) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS1 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 6 step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      eapply implM_abind.
      { pose proof (ERR_set_debug_walk HM HF RS_too_long A_ASN1_LIB_C A_ASN1_GET_OBJECT bo fs fk ns nk LF LN) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREa|rewrite ESP; unfold ERR_SET_DEBUG_STACK; lia]|reflexivity|exact FRM1|cbn; unfold A_ASN1_LIB_C, A_ASN1_GET_OBJECT, MallocRep.wz; repeat split; reflexivity|exact (proj1 BKa)|exact KIDS1]. }
      intros r2 sB ms2 PO2. cbv beta in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                       & -> & FRM2 & FE2 & PREb & LXb & SOb & FAb & BKb & EBO2).
      subst bo2.
      replace (ret_pc (Z_to_bv 64 (1038956 + 28))) with (Z_to_bv 64 (1038956 + 28)) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS2 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKb) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 4 step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      eapply implM_mono.
      { pose proof (ERR_set_error_walk RS_too_long 13 155 bo) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREb|rewrite ESP; unfold ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM2| |exact (proj1 BKb)|exact KIDS2].
        cbn. unfold ERR_LIB_SYS, MallocRep.wz. repeat split; try reflexivity; lia. }
      intros r3 sC ms3 PO3. cbv beta in PO3.
      destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                       & -> & FRM3 & FE3 & PREc & LXc & SOc & FAc & BKc & EBO3). subst bo3.
      replace (ret_pc (Z_to_bv 64 (1038956 + 44))) with (Z_to_bv 64 (1038956 + 44)) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold raise_post. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3.
      split; [reflexivity|]. split; [exact FRM3|]. split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|].
      split; [exact PREc|]. split; [rewrite <- ESP; eapply lx_pres_trans; [exact LXa|eapply lx_pres_trans; [exact LXb|exact LXc]]|].
      split; [rewrite SOc, SOb; exact SOa|]. split; [rewrite FAc, FAb; exact FAa|].
      split; [exact (proj1 BKc)|]. split; [exact (proj1 (proj2 BKc))|].
      eapply kept_trans; [exact KP2|]. eapply kept_trans; [exact (proj2 (proj2 BKa))|]. eapply kept_trans; [exact (proj2 (proj2 BKb))|exact (proj2 (proj2 BKc))].
    - unfold implM. iprefix. step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      eapply implM_abind.
      { pose proof (ERR_new_walk HF bo) as W. unfold ap_stmt in W. eapply W; [eapply ap_pre_stack_le; [exact PRE2|unfold ERR_NEW_STACK, ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM|reflexivity|exact KOW|exact KIDS]. }
      intros r1 sA ms1 PO1. cbv beta in PO1.
      destruct PO1 as (q0 & q1 & q2 & q10 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q3 & q4 & q5 & q6 & F1 & fc1 & mA & OW1 & errv1 & bo1
                       & -> & FRM1 & FE1 & PREa & LXa & SOa & FAa & BKa & EBO1).
      subst bo1. replace (ret_pc (Z_to_bv 64 (1038852 + 4))) with (Z_to_bv 64 (1038852 + 4)) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS1 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r1) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKa) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 6 step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      eapply implM_abind.
      { pose proof (ERR_set_debug_walk HM HF RS_hdr_too_long A_ASN1_LIB_C A_ASN1_GET_OBJECT bo fs fk ns nk LF LN) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREa|rewrite ESP; unfold ERR_SET_DEBUG_STACK; lia]|reflexivity|exact FRM1|cbn; unfold A_ASN1_LIB_C, A_ASN1_GET_OBJECT, MallocRep.wz; repeat split; reflexivity|exact (proj1 BKa)|exact KIDS1]. }
      intros r2 sB ms2 PO2. cbv beta in PO2.
      destruct PO2 as (p0 & p1' & p2' & p10 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p3 & p4 & p5 & p6 & F2 & fc2 & mB & OW2 & errv2 & bo2
                       & -> & FRM2 & FE2 & PREb & LXb & SOb & FAb & BKb & EBO2).
      subst bo2.
      replace (ret_pc (Z_to_bv 64 (1038852 + 28))) with (Z_to_bv 64 (1038852 + 28)) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (KIDS2 : forall b, In b K -> ~ In (blk_id b) (es_ids (snd r2) ++ env_ids E)).
      { intros b Hb Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [exact (proj1 (proj2 BKb) b Hb Hin)|]. apply (KIDS b Hb). apply in_app_iff. right. exact Hin. }
      unfold implM. iprefix. do 4 step.
      ihere.
      lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
        lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
      eapply implM_mono.
      { pose proof (ERR_set_error_walk RS_hdr_too_long 13 123 bo) as W. unfold ap_stmt in W.
        eapply W; [eapply ap_pre_restack; [exact PREb|rewrite ESP; unfold ERR_SET_ERROR_STACK; lia]|reflexivity|exact FRM2| |exact (proj1 BKb)|exact KIDS2].
        cbn. unfold ERR_LIB_SYS, MallocRep.wz. repeat split; try reflexivity; lia. }
      intros r3 sC ms3 PO3. cbv beta in PO3.
      destruct PO3 as (o0 & o1 & o2 & o10 & o11 & o12 & o13 & o14 & o15 & o16 & o17 & o3 & o4 & o5 & o6 & F3 & fc3 & mC & OW3 & errv3 & bo3
                       & -> & FRM3 & FE3 & PREc & LXc & SOc & FAc & BKc & EBO3). subst bo3.
      replace (ret_pc (Z_to_bv 64 (1038852 + 44))) with (Z_to_bv 64 (1038852 + 44)) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      unfold raise_post. exists o0, o1, o2, o10, o11, o12, o13, o14, o15, o16, o17, o3, o4, o5, o6, F3, fc3, mC, OW3, errv3.
      split; [reflexivity|]. split; [exact FRM3|]. split; [intros k Hk; rewrite (FE3 k Hk), (FE2 k Hk); apply (FE1 k Hk)|].
      split; [exact PREc|]. split; [rewrite <- ESP; eapply lx_pres_trans; [exact LXa|eapply lx_pres_trans; [exact LXb|exact LXc]]|].
      split; [rewrite SOc, SOb; exact SOa|]. split; [rewrite FAc, FAb; exact FAa|].
      split; [exact (proj1 BKc)|]. split; [exact (proj1 (proj2 BKc))|].
      eapply kept_trans; [exact KP2|]. eapply kept_trans; [exact (proj2 (proj2 BKa))|]. eapply kept_trans; [exact (proj2 (proj2 BKb))|exact (proj2 (proj2 BKc))].
  Qed.

  (* [comment removed for export] *)
  Lemma pre_at_ret : forall m2, munch W0 m m2 -> wmono ctusegs m m2 -> mem_inv ctusegs m2 -> stk ctusegs m2 lo (bv_unsigned sp) ->
    rw_cells ctusegs m2 3355012 [C4 errv] ->
    ap_pre s st m2 OW LB E bo sp lo B errv canary 0
    /\ lx_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_AP) m m2
    /\ kept K m m2.
  Proof using BPC BPL BPP BPT CELLS KOW OM0 OP0 OPM PAY PRE.
    intros m2 MU WM MI ST ERR. ctx.
    destruct PRE as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    assert (INCL : forall b, In b OW -> In b (OW ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    assert (HW : Forall (fun iv : Z * Z => lo <= fst iv /\ snd iv <= B) W0) by (repeat constructor; cbn; lia).
    assert (HEAP2 : RHEAP s (OW ++ LB) m2).
    { eapply LH_frame; [exact HEAP|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. apply W_ok_stack. cbn in *. lia. }
    split; [|split].
    - unfold ap_pre. split; [exact HEAP2|].
      split. { eapply (ap_state_of_munch st m m2); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch s (OW ++ LB) _ m m2); [exact DC|intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW _ i q k OD Hd))|exact HEAP|exact CEIL|exact MU|exact WM|].
               eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx. }
      split. { eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. eapply Forall_impl; [|exact HW]. intros [x y] [Hx Hy]. cbn in *. unfold RAUXV_CELL, GLOBALS_TOP in *. lia. }
      split; [lia|]. split; [lia|]. split; [exact ST|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAP2|].
      split; [exact MI|exact SP16].
    - eapply lx_pres_of_munch; [exact MU|exact WM|]. intros a Ha [HX Hc]. cbn [rin_ivs fst snd app] in HX. cbn.
      destruct Hc as [Hc|[(b & Hb & Hr)|Hc]].
      + repeat split; try lia; tauto.
      + destruct b as [[q A] n]. cbn [blk_addr blk_size fst snd] in Hr.
        pose proof (blk_bounds _ _ _ q A n HEAP ltac:(apply in_app_iff; right; exact Hb)). repeat split; lia.
      + unfold ralloc_static in Hc. repeat split; lia.
    - eapply (kept_of_munch s (OW ++ LB) _ m m2 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOW; exact Hb|exact CEIL|exact MU|].
      eapply Forall_impl; [|exact HW]. intros iv [Hx Hy]. left. exact Hx.
  Qed.

  (* [comment removed for export] *)
  Lemma fin_common : forall sF (st' : ap_st bptr) mX OW' (errv' : word) W m4,
    ap_pre sF st' mX OW' LB E bo (Z_to_bv 64 (bv_unsigned sp + -48)) lo B errv' canary 0 ->
    (forall b, In b K -> In b OW') ->
    munch W mX m4 -> wmono ctusegs mX m4 -> Forall (fun iv => iv = (PP, PP + 8)) W ->
    stk ctusegs m4 lo (bv_unsigned sp) -> mem_inv ctusegs m4 -> rw_cells ctusegs m4 3355012 [C4 errv'] ->
    ap_pre sF st' m4 OW' LB E bo sp lo B errv' canary 0 /\ kept K mX m4
    /\ lx_pres LB (bv_unsigned sp) ([(PP, PP + 8); (PL, PL + 8); (PT, PT + 4); (PC, PC + 4)] ++ LIBW_AP) mX m4.
  Proof using BPP CELLS OM0 OP0 OPM PAY PRE.
    intros until m4. intros PREX KOWX MU WM HW ST4 MI4 ERR4. ctx.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    destruct PREX as (HEAP & AS & IDS & DC & AUX & SPB' & B63' & ST0 & CEIL' & GLO' & LO' & ERR0 & SSP & MI0 & SP16). rewrite ESP in *.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SP16e).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    assert (INCL : forall b, In b OW' -> In b (OW' ++ LB)) by (intros b Hb; apply in_app_iff; left; exact Hb).
    pose proof (ap_state_es _ _ _ _ _ AS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & OD).
    assert (HWP : Forall (fun iv : Z * Z => fst iv = PP /\ snd iv = PP + 8) W).
    { eapply Forall_impl; [|exact HW]. intros iv ->. cbn. split; reflexivity. }
    assert (HEAP4 : RHEAP sF (OW' ++ LB) m4).
    { eapply LH_frame; [exact HEAP|exact MU|exact WM|]. eapply Forall_impl; [|exact HWP]. intros [x y] [Hx Hy]. cbn in Hx, Hy. subst. apply W_ok_stack. lia. }
    split; [|split].
    - unfold ap_pre. split; [exact HEAP4|].
      split. { eapply (ap_state_of_munch st' mX m4); [exact AS|exact HEAP|exact INCL|exact MU|exact WM|exact CEIL|unfold GLOBALS_TOP; exact GLO|].
               eapply Forall_impl; [|exact HWP]. intros [x y] [Hx Hy]. cbn in Hx, Hy |- *. left. lia. }
      split; [exact IDS|].
      split. { eapply (data_cells_of_munch sF (OW' ++ LB) _ mX m4); [exact DC|intros i q k Hd; apply INCL; exact (proj1 (optb_ok_nth OW' _ i q k OD Hd))|exact HEAP|exact CEIL|exact MU|exact WM|].
               eapply Forall_impl; [|exact HWP]. intros [x y] [Hx Hy]. cbn in Hx, Hy |- *. left. lia. }
      split. { eapply rauxv_ok_frame; [exact AUX|exact MU|exact WM|]. eapply Forall_impl; [|exact HWP]. intros [x y] [Hx Hy]. cbn in Hx, Hy |- *. unfold RAUXV_CELL. lia. }
      split; [lia|]. split; [lia|]. split; [exact ST4|]. split; [exact CEIL|]. split; [unfold GLOBALS_TOP; lia|]. split; [lia|].
      split; [unfold MallocRep.wz; rewrite EA; exact ERR4|]. split; [rewrite (ssp_canary_0 _ _ _ _ HEAP SSP); eapply RHEAP_ssp; exact HEAP4|].
      split; [exact MI4|exact SP16e].
    - eapply (kept_of_munch sF (OW' ++ LB) _ mX m4 K lo); [exact HEAP|intros b Hb; apply INCL; apply KOWX; exact Hb|exact CEIL|exact MU|].
      eapply Forall_impl; [|exact HWP]. intros [x y] [Hx Hy]. cbn in Hx, Hy |- *. left. lia.
    - eapply lx_pres_of_munch; [exact MU|exact WM|]. intros a Ha [HX Hc]. cbn [rin_ivs fst snd app] in HX. apply seg_outside.
      eapply Forall_impl; [|exact HWP]. intros [x y] [Hx Hy]. cbn in Hx, Hy |- *. lia.
  Qed.

  Local Notation GPOST := (getobj_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s OW LB E bo lo B canary m K D PP PL PT PC g).
  Local Notation IPOST := (fun ms' : machine_state => impl ctusegs (at_node ctusegs) (interp (ap_embed (go_eff g st)) s)
                              (epost (fun p : unit * ap_st bptr * PState => GPOST (fst p) (snd p))) ms').

  (* [comment removed for export] *)
  Lemma g_cases : forall tag p1 max1 (inf : bool) len p2,
    go_hdr d op omax = Some (tag, p1, max1) -> get_length d p1 max1 = Some (inf, len, p2) -> inf && (Z.land (znth d op) 32 =? 0) = false ->
    g = if omax - (p2 - op) <? len
        then mkGO (Some GeTooLong) (Z.lor (Z.land (znth d op) 32) (if inf then 1 else 0)) p2 len tag (Z.land (znth d op) 192)
        else mkGO None (Z.lor (Z.land (znth d op) 32) (if inf then 1 else 0)) p2 len tag (Z.land (znth d op) 192).
  Proof using OM0.
    intros tag p1 max1 inf len p2 GH GL HI. unfold g. rewrite get_object_eq. rewrite (proj2 (Z.leb_gt omax 0)) by lia.
    rewrite GH, GL. unfold V_ASN1_CONSTRUCTED. rewrite HI. reflexivity.
  Qed.

  Lemma g_err : go_hdr d op omax = None \/ (exists tag p1 max1, go_hdr d op omax = Some (tag, p1, max1) /\
                   (get_length d p1 max1 = None \/ exists len p2, get_length d p1 max1 = Some (true, len, p2) /\ Z.land (znth d op) 32 = 0)) ->
    g = go_fail GeHdr op.
  Proof using OM0.
    intros H. unfold g. rewrite get_object_eq. rewrite (proj2 (Z.leb_gt omax 0)) by lia.
    destruct H as [GH|(tag & p1 & max1 & GH & [GL|(len & p2 & GL & HZ)])]; rewrite GH; [reflexivity|rewrite GL; reflexivity|].
    rewrite GL. unfold V_ASN1_CONSTRUCTED. rewrite HZ. cbn. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma err_path : g = go_fail GeHdr op -> at_err IPOST.
  Proof using BPC BPL BPP BPT CELLS FRM HF HM KIDS KOW OM0 OP0 OPM PAY PRE TP.
    intros GEQ. unfold at_err. intros until cpc. intros GI2 SZL SZT SZC. pose proof GI2 as GI2'. go_unpack GI2. ctx. unhide6.
    apply evt_done. rewrite GEQ. cbn [go_eff go_err go_fail].
    lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
      lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
    eapply implM_post_evt. eapply implM_mono; [eapply (raise_seq 0xfda04 105 123 RS_hdr_too_long); [right; repeat split; reflexivity|exact GI2']|].
    intros r sF msF RP. cbv beta. unfold raise_post in RP.
    destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF
                    & -> & FRMF & FEF & PREF & LXF & SOF & FAF & BKF).
    change (1038852 + 44) with 1038896.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
    assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
    pose proof PREF as (HEAPF & ASF & IDSF & DCF & AUXF & SPBF & B63F & STF & CEILF & GLOF & LOF & ERRF & SSPF & MIF & SP16F). rewrite ESP in STF.
    unfold MallocRep.wz in ERRF. rewrite EA in ERRF.
    pose proof (agree_of_lx_pres _ _ _ _ _ LXF) as AGF.
    assert (CL : forall a, bv_unsigned sp + -48 <= a -> lx_client LB (bv_unsigned sp + -48) LIBW_AP a).
    { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|left; exact Ha]. }
    pose proof (rw_cells_bound _ _ _ _ CPL) as BL. pose proof (rw_cells_bound _ _ _ _ CPT) as BT. pose proof (rw_cells_bound _ _ _ _ CPC) as BC.
    apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [|intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in CPP; [|intros a Ha; apply CL; cbn in Ha; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in CPL; [|intros a Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in CPT; [|intros a Ha; apply CL; lia].
    apply (rw_cells_agree _ _ _ _ _ AGF) in CPC; [|intros a Ha; apply CL; lia].
    apply rw_cells_CB_of in CPL. apply rw_cells_CB_of in CPT. apply rw_cells_CB_of in CPC. rewrite SZL in CPL. rewrite SZT in CPT. rewrite SZC in CPC.
    clear MU WM MI ST HB ERR.
    pose proof (munch_refl (@nil (Z * Z)) mF) as MU. pose proof (wmono_refl ctusegs mF) as WM.
    step. do 6 step. step. release_frame FR STF (bv_unsigned sp). step.
    apply evt_done.
    destruct (fin_common sF (snd r) mF OWF errvF _ mF PREF (proj1 BKF) MU WM ltac:(constructor) STF MIF ERRF) as (PRE4 & KP4 & LX4).
    unfold getobj_post. cbn [go_err go_p go_ret go_len go_tag go_cls go_fail].
    eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, FF, fcF, mF, OWF, errvF, (cells_bytes cpl), (cells_bytes cpt), (cells_bytes cpc).
    split; [reflexivity|]. split; [exact FRMF|]. split; [exact FEF|].
    split; [exact PRE4|].
    split. { eapply lx_pres_trans; [exact (proj1 (proj2 (pre_at_call _ _ _ _ GI2')))|]. eapply lx_pres_trans; [|exact LX4].
             eapply lx_pres_weaken; [exact LXF|lia|intros b Hb; exact Hb|]. intros a Ha. cbn [rin_ivs app fst snd] in Ha |- *. clear - Ha. tauto. }
    split; [exact SOF|]. split; [exact FAF|].
    split; [split; [exact (proj1 BKF)|split; [exact (proj1 (proj2 BKF))|eapply kept_trans; [exact (proj2 (proj2 BKF))|exact KP4]]]|].
    split; [exact CPP|].
    split; [reflexivity|]. split; [exact CPL|split; [exact CPT|exact CPC]].
  Qed.

  Theorem go_main : forall (t0 t1 t2 t3 a5 a6 a7 : word),
    implM ctusegs (interp (ap_embed (go_eff g st))) s GPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz PP) (wz PL) (wz PT) (wz PC) (wz omax) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz ASN1_GET_OBJECT) fc None m (seg_rom ctusegs)).
  Proof using BPC BPL BPP BPT CELLS FRM HF HM HPC HPL HPP HPT KIDS KOW OM0 OP0 OPM PAY PRE TP.
    intros. unfold implM. iprefix.
    eapply stage_tag.
    - (* [comment removed for export] *)
      intros tag p1 max1 x5 x6 x7 x18 x28 x29 m1 GH Hp1 Hm1 Hmx Htag GI EX18.
      eapply (stage_len tag p1 max1 x5 x6 x7 x18 x28 x29 m1 _ GH Hp1 Hm1 Hmx Htag GI EX18).
      + (* [comment removed for export] *)
        intros inf len p2 y5 y6 y7 y11 y12 y16 y17 y28 y29 m2 GL HI Hp2 Hlen GI2.
        pose proof (g_cases _ _ _ _ _ _ GH GL HI) as GEQ.
        pose proof GI2 as GI2'. go_unpack GI2. ctx. unhide6.
        assert (L32 : 0 <= Z.land (znth d op) 32 <= 32) by (pose proof (land_32_cases (znth d op)); lia).
        assert (INF : 0 <= (if inf then 1 else 0) <= 1) by (destruct inf; lia).
        pose proof (get_length_bounds d p1 max1 inf len p2 ltac:(eapply Forall_impl; [|exact DF]; intros c Hc; cbn in Hc; lia) GL) as [GB1 GB2].
        pose proof (get_length_len_max d p1 max1 inf len p2 ltac:(eapply Forall_impl; [|exact DF]; intros c Hc; cbn in Hc; lia) GL) as GB3. unfold LONG_MAX in GB3.
        step. step. step. step. rewrite (unsigned_lit (D + op)) by lia. rewrite (unsigned_lit (D + p2 + - (D + op))) by lia. 
        step. if_cases C; [exfalso; zc C; rewrite ?(land_m64U (D + p2 + - (D + op))) in C by lia; rewrite ?land_m64U in C by lia; rewrite ?lxor_s63U in C by lia; ltb_res C; cbn in C; lia|clear C].
        step. if_cases KD; zc KD; rewrite !signed_small in KD by lia.
        * (* [comment removed for export] *)
          rewrite (proj2 (Z.ltb_ge _ _)) in GEQ by lia.
          step. step. step.
          do 6 step. step. release_frame FR ST (bv_unsigned sp). step. rewrite !unsigned_lit by lia.
          name_mem m3. subst tp.
          apply evt_done. rewrite GEQ. cbn [go_eff go_err aret ap_embed interp impl]. apply evt_done. unfold epost. cbn [fst snd].
          destruct (pre_at_ret m3 MU WM MI ST ERR) as (PRE3 & LX3 & KP3).
          unfold getobj_post. cbn [go_err go_p go_ret go_len go_tag go_cls].
          eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m3, OW, errv, jl, j2, j3.
          split; [unfold MallocRep.wz; reflexivity|]. split; [exact FRM|]. split; [intros; reflexivity|].
          split; [exact PRE3|]. split; [exact LX3|]. split; [reflexivity|]. split; [reflexivity|].
          split; [split; [exact KOW|split; [intros b Hb Hin; apply (KIDS b Hb); apply in_app_iff; left; exact Hin|exact KP3]]|].
          split; [unfold MallocRep.wz; exact CPP|].
          unfold MallocRep.wz. split; [|split; [exact CPL|split; [exact CPT|exact CPC]]].
          f_equal; first [reflexivity|apply Z.lor_comm].
        * (* [comment removed for export] *)
          rewrite (proj2 (Z.ltb_lt _ _)) in GEQ by lia.
          apply evt_done. rewrite GEQ. cbn [go_eff go_err].
          lazymatch goal with |- impl ?segs _ (?c ?stt) (epost ?EE) ?ms =>
            lazymatch EE with (fun p => ?Q (fst p) (snd p)) => change (implM segs c stt Q ms) end end.
          eapply implM_post_evt. eapply implM_mono; [eapply (raise_seq 0xfda6c 95 155 RS_too_long); [left; repeat split; reflexivity|exact GI2']|].
          intros r sF msF RP. cbv beta. unfold raise_post in RP.
          destruct RP as (w0 & w1 & w2 & w10 & w11 & w12 & w13 & w14 & w15 & w16 & w17 & w3 & w4 & w5 & w6 & FF & fcF & mF & OWF & errvF
                          & -> & FRMF & FEF & PREF & LXF & SOF & FAF & BKF).
          change (1038956 + 44) with 1039000.
          assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
          assert (EA : errno_addr (Z_to_bv 64 RATP) = 3355012) by (unfold errno_addr, RATP; rewrite unsigned_lit by lia; reflexivity).
          pose proof PREF as (HEAPF & ASF & IDSF & DCF & AUXF & SPBF & B63F & STF & CEILF & GLOF & LOF & ERRF & SSPF & MIF & SP16F). rewrite ESP in STF.
          unfold MallocRep.wz in ERRF. rewrite EA in ERRF.
          pose proof (agree_of_lx_pres _ _ _ _ _ LXF) as AGF.
          assert (CL : forall a, bv_unsigned sp + -48 <= a -> lx_client LB (bv_unsigned sp + -48) LIBW_AP a).
          { intros a Ha. split; [unfold LIBW_AP; cbn [rin_ivs fst snd]; lia|left; exact Ha]. }
          apply (rw_cells_agree _ _ _ _ _ AGF) in FR; [|intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AGF) in CPP; [|intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AGF) in CPL; [|intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AGF) in CPT; [|intros a Ha; apply CL; cbn in Ha; lia].
          apply (rw_cells_agree _ _ _ _ _ AGF) in CPC; [|intros a Ha; apply CL; cbn in Ha; lia].
          clear MU WM MI ST HB ERR.
          pose proof (munch_refl [(PP, PP + 8)]%Z mF) as MU. pose proof (wmono_refl ctusegs mF) as WM.
          unfold MallocRep.wz. step. step. step. step.
          do 6 step. step. release_frame FR STF (bv_unsigned sp). step. rewrite ?unsigned_lit by lia.
          name_mem m4.
          apply evt_done.
          destruct (fin_common sF (snd r) mF OWF errvF _ m4 PREF (proj1 BKF) MU WM ltac:(repeat constructor) STF MIF ERRF) as (PRE4 & KP4 & LX4).
          unfold getobj_post. cbn [go_err go_p go_ret go_len go_tag go_cls].
          eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, FF, fcF, m4, OWF, errvF, jl, j2, j3.
          split; [reflexivity|]. split; [exact FRMF|]. split; [exact FEF|].
          split; [exact PRE4|].
          split. { eapply lx_pres_trans; [exact (proj1 (proj2 (pre_at_call _ _ _ _ GI2')))|]. eapply lx_pres_trans; [|exact LX4].
                   eapply lx_pres_weaken; [exact LXF|lia|intros b Hb; exact Hb|]. intros a Ha. cbn [rin_ivs app fst snd] in Ha |- *. clear - Ha. tauto. }
          split; [exact SOF|]. split; [exact FAF|].
          split; [split; [exact (proj1 BKF)|split; [exact (proj1 (proj2 BKF))|eapply kept_trans; [exact (proj2 (proj2 BKF))|exact KP4]]]|].
          split; [exact CPP|].
          split; [f_equal; first [apply ret_or_128; apply land_32_cases|rewrite (Z.lor_comm (if inf then 1 else 0)); apply ret_or_128; apply land_32_cases]|]. split; [exact CPL|split; [exact CPT|exact CPC]].
      + (* [comment removed for export] *)
        intros GL. apply err_path. apply g_err. right. exists tag, p1, max1. split; [exact GH|left; exact GL].
      + (* [comment removed for export] *)
        intros len p2 GL HZ. apply err_path. apply g_err. right. exists tag, p1, max1. split; [exact GH|right; exists len, p2; split; [exact GL|exact HZ]].
    - (* [comment removed for export] *)
      intros GH. apply err_path. apply g_err. left. exact GH.
  Qed.

  End Act.

  (* [comment removed for export] *)
  Theorem ASN1_get_object_walk : ASN1_get_object_spec.
  Proof using HF HM.
    unfold ASN1_get_object_spec. intros until j3. intros PRE TP FRM KOW KIDS PAY OP0 OM0 OPM CELLS BPP BPL BPT BPC HPP HPL HPT HPC -> -> -> -> ->.
    eapply (go_main ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 F fc m s st OW LB E bo lo B errv canary K D d op omax PP PL PT PC jl j2 j3);
      assumption.
  Qed.
End Proofs.
End WithCeiling0.
