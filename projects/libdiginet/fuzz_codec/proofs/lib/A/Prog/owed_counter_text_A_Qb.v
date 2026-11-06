(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: region_kept_tcj_stack and region_kept_tcj_frame are the text of lib/A/ACem.v's
   region_kept_ownframe_aj (copied there from projects/libreac/fuzz_knock/proofs/lib/A/ACem.v) with the call's acall_kept
   replaced by a callee's tcj_kept (lib/A/Prog/CodecCJ.v), cpw_apresent_of_writable that of lib/A/AE7f.v's
   apresent_of_writable; the re-seat in cpw_call_reseat and cpw_rebase is the text of lib/A/AWalkFw2.v's reseatL (copied
   there from projects/libreac/fuzz_knock/proofs/lib/A/AWalkFw2.v) with the environment equation kept for env_agree,
   cpw_kept_std that of lib/A/AWalkFw1.v's aconstsF with the region_kept_val cases of
   projects/reac-pw/fuzz_qdisc/proofs/lib/A/QPgMain3.v:186-194, and cpw_leaf that of lib/A/Prog/CPgWalk.v's cw_leaf with the
   state's layout, astate and model taken through the calls' chain; for libdiginet/fuzz_codec's ASan build (image A).
   cpw_call, cpw_entry, cpw_kept_run, cpw_io, cpw_keep and cpw_sp_off are new. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/CPgWalkCall.v; 852 of its 903 lines of code are new or changed and 227 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_codec/lib/A/Prog/owed_counter_text_A_base.v; 257 of its 334 lines of code are new or changed and 826 lines of the source are left out. *)
(* owed_counter_text at image A: the second loop's vocabulary (fuzz_codec.c:418-426, 0x8405c-0x84168).
   seg[] is the caller's 8 bytes at atom 11 (the entry a1), *dots its byte at atom 12 (the entry a2), *dots' shadow byte
   a region at atom 332 = SB + dt / 8 (alias) holding atom 333. The loop head 0x8408c with i digits written is ss_Q n i b
   (b: the shadow byte of *dots is not 0, with the engine's fact dt & 7 < it). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YC85 YCeo.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgWalk CPgWalkKept CPgWalkFrame CPgWalkCall.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import owed_counter_text_A_base owed_counter_text_A_wr.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.


Definition oc_segv (n j : nat) : sv := if (j <? 8 - n)%nat then SLit 0 else SExt false 8 (SOff (310 + (j - (8 - n))) 0).
Definition oc_sgQ (n i : nat) : YP09.region :=
  YP09.mkRegion (Some 11%nat) 0 8 0 8 (map (fun j => YP09.mkChunk (Z.of_nat j) (CVal 1 (oc_segv n j))) (rev (seq 0 i))).
Definition oc_dtQ (i : nat) : YP09.region := YP09.mkRegion (Some 12%nat) 0 1 0 1 [YP09.mkChunk 0 (CVal 1 (SOff (340 + i) 0))].
Definition oc_dsQ (b : bool) : YP09.region :=
  YP09.mkRegion (Some 332%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (if b then SOff 333 0 else SLit 0))].
Definition oc_atomsQ (b : bool) : list (nat * afact) :=
  (if b then [(333%nat, mkAF 1 7 0)] else []) ++
  [(332%nat, mkAF 2147450880 17594333495295 0); (12%nat, mkAF 1 (2 ^ 47 - 1) 0); (11%nat, mkAF 1 (2 ^ 47 - 8) 0)] ++ oc_atoms.
Definition oc_condsQ (b : bool) : list acond :=
  if b then [mkAC BC_LT (SAlu ALU_AND (SOff 12 0) (SLit 7)) (SOff 333 0)] else [].
Definition oc_aliasQ : list (sv * sv) := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 12 0) (SLit 3)) (SOff 32 0), SOff 332 0) :: oc_alias.
Definition oc_factsQ (b : bool) : facts := mkFacts (oc_atomsQ b) (oc_condsQ b) oc_aliasQ.
Definition ocQ_regs (n i : nat) : list sv :=
  [SLit 0; SOff 1 0; SOff 70 0; SOff 3 0; SOff 4 0; SOff 5 0; SOff 6 0; SOff 12 0;
   SOff 2 0; SOff 70 0; SOff 11 (Z.of_nat i); SOff 11 0; SOff 332 0; SAlu ALU_AND (SOff 12 0) (SLit 7);
   SLit (Z.of_nat i); SLit (8 - Z.of_nat i); SLit 1; SOff 17 0;
   SLit ((Z.of_nat n - 8) mod 2 ^ 64); SLit 46; SOff 11 (Z.of_nat i); SOff 75 64; SOff 22 0; SOff 23 0;
   SOff 88 0; SOff 25 0; SOff 32 0; SOff 75 32; SOff 28 0; SOff 29 0; SOff 30 0; SOff 31 0].
Definition ocQ_deads : list nat := [1; 5; 6; 11; 17; 22; 23; 25; 28; 29; 30; 31]%nat.
Definition ss_Q (n i : nat) (b : bool) : sstate :=
  ss_havoc_regs (mkSS 0x8408c (ocQ_regs n i) [oc_sgQ n i; oc_dtQ i; oc_dsQ b; oc_dot n; oc_fs_ro; oc_s n; oc_fl; oc_r70; oc_stack]
    None (oc_factsQ b)) OC_RT ocQ_deads.
(* the digits written so far, as ct2_go builds them *)
Definition oc_segL (n : nat) (s : list Z) (i : nat) : list Z :=
  map (fun j => if (j <? 8 - n)%nat then 0 else nth (j - (8 - n)) s 0) (seq 0 i).
Definition INV_Q (n i : nat) (b : bool) (cx : occx) (E : env) (W3 : world tfibsegs) (m3 : word -> option byte) : Prop :=
  exists s dot d, oc_atoms_sd E n s dot /\
  codec_owe.ct1_owe (o_tb cx) 0 [] (repeat 0 8) = Some (Z.of_nat n, s, dot) /\
  length s = n /\ codec_text.ct_inv (Z.of_nat n) dot /\ Forall (fun v => 0 <= v < 128) s /\
  Forall (fun d0 => d0 = 0 \/ d0 = 1) dot /\
  ew E (340 + i) = Z_to_bv 64 d /\ 0 <= d < 256 /\
  DgnLib.ct2 (Z.of_nat n) s dot = DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat i) (8 - i) (oc_segL n s i) d.

(* ================================ the spec's steps ================================ *)
Lemma oc_segL_S : forall n s i, oc_segL n s (Datatypes.S i) = oc_segL n s i ++ [if (i <? 8 - n)%nat then 0 else nth (i - (8 - n)) s 0].
Proof. intros n s i. unfold oc_segL. rewrite seq_S, map_app. reflexivity. Qed.
Lemma oc_ct2_neg : forall n s dot i k seg d, Z.of_nat i - (8 - Z.of_nat n) < 0 ->
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat i) (Datatypes.S k) seg d =
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat (Datatypes.S i)) k (seg ++ [0]) d.
Proof.
intros n s dot i k seg d H. cbn [DgnLib.ct2_go]. rewrite (proj2 (Z.ltb_lt _ _) H).
replace (0 <=? Z.of_nat i - (8 - Z.of_nat n)) with false by (symmetry; apply Z.leb_gt; lia). cbn [andb].
f_equal. lia.
Qed.
Lemma oc_ct2_pos : forall n s dot i k seg d, 0 <= Z.of_nat i - (8 - Z.of_nat n) ->
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat i) (Datatypes.S k) seg d =
  let v := nth (Z.to_nat (Z.of_nat i - (8 - Z.of_nat n))) s 0 in
  if negb (nth (Z.to_nat (Z.of_nat i - (8 - Z.of_nat n))) dot 0 =? 0) then
    (if Z.of_nat i =? 7 then (DgnSpec.E_RANGE, seg ++ [v], d)
     else DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat (Datatypes.S i)) k (seg ++ [v]) (Z.lor d (2 ^ Z.of_nat i)))
  else DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat (Datatypes.S i)) k (seg ++ [v]) d.
Proof.
intros n s dot i k seg d H. cbn [DgnLib.ct2_go].
replace (Z.of_nat i - (8 - Z.of_nat n) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
rewrite (proj2 (Z.leb_le _ _) H). cbn [andb].
replace (Z.of_nat i + 1) with (Z.of_nat (Datatypes.S i)) by lia. reflexivity.
Qed.
Lemma oc_segv_nth : forall n s j, (j < 8)%nat -> (n <= 8)%nat ->
  (if (j <? 8 - n)%nat then 0 else nth (j - (8 - n)) s 0) =
  (if Z.of_nat j - (8 - Z.of_nat n) <? 0 then 0 else nth (Z.to_nat (Z.of_nat j - (8 - Z.of_nat n))) s 0).
Proof.
intros n s j Hj Hn. destruct (Nat.ltb_spec j (8 - n)) as [H | H].
- rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
- rewrite (proj2 (Z.ltb_ge _ _)) by lia. f_equal. lia.
Qed.

(* ================================ state plumbing ================================ *)
Lemma oc_alld_chunks : forall E b lo hi wlo whi cs cs' rs,
  all_disjoint E (YP09.mkRegion b lo hi wlo whi cs) rs -> all_disjoint E (YP09.mkRegion b lo hi wlo whi cs') rs.
Proof. intros E b lo hi wlo whi cs cs' rs. induction rs as [|r rs IH]; cbn; [auto|]. intros [H1 H2]. split; [exact H1 | exact (IH H2)]. Qed.
Section sw. Context {fx : YK11.FPState}.
(* the head chunk of the second region read through another symbolic value with the same denotation *)
Lemma oc_swap1 : forall E ss ms r0 b lo hi wlo whi o w v v' cs rs,
  st_ok tfibsegs E ss ms ->
  ss_mem ss = r0 :: YP09.mkRegion b lo hi wlo whi (YP09.mkChunk o (CVal w v) :: cs) :: rs ->
  sv_denot E v' = sv_denot E v ->
  st_ok tfibsegs E (mkSS (ss_pc ss) (ss_regs ss) (r0 :: YP09.mkRegion b lo hi wlo whi (YP09.mkChunk o (CVal w v') :: cs) :: rs)
    (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r0 b lo hi wlo whi o w v v' cs rs (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) Hm Hv.
unfold st_ok; cbn. repeat (split; [assumption|]). split; [|exact H9].
rewrite Hm in H8. destruct H8 as (Hwf & Hok & Hpd).
split; [cbn [regions_wf region_wf forallb chunk_inside YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks YP09.c_off
  c_len cv_len YP09.c_val] in *; exact Hwf|].
split.
- inversion Hok as [|r0' rs0 Hr0 Hrs]; subst. constructor; [exact Hr0|].
  inversion Hrs as [|r1 rs1 Hr1 Hrs1]; subst. constructor; [|exact Hrs1].
  destruct Hr1 as (R1 & R2 & R3 & R4). split; [exact R1|]. split; [exact R2|]. split; [exact R3|].
  inversion R4 as [|c0 cs0 Hc0 Hcs]; subst. constructor; [|exact Hcs].
  intros i Hi. destruct (Hc0 i Hi) as (bt & Hb & Hm2). exists bt. split; [|exact Hm2].
  cbn [YP09.c_off YP09.c_val cbyte] in *. rewrite Hv. exact Hb.
- cbn [pairwise_disjoint all_disjoint] in Hpd |- *. destruct Hpd as ((Ha & Hb) & Hc & Hd).
  split; [split; [exact Ha | exact Hb]|]. split; [exact (oc_alld_chunks _ _ _ _ _ _ _ _ _ Hc) | exact Hd].
Qed.
End sw.
(* a window of a region on the caller's bytes [q, q + n) that the contract lets the call write (twr_ok at the call
   state), seen from a later journal of the walk (its blocks, frames and own frames extend the call state's) *)
Lemma oc_awr_ok_cons_twr3 : forall B E r rs STK sp0 FP ly S lyc Sc own (W : world tfibsegs) memc sp q n m blc3 ly3 own3,
  YP09.r_base r = Some m -> bv_unsigned (ew E m) = q -> 0 <= YP09.r_wlo r -> YP09.r_whi r <= n ->
  twr_ok tfibsegs B STK sp0 FP ly S lyc Sc own W memc sp q n ->
  (forall b k, In (b, k) (ablocks B lyc Sc) -> In (b, k) blc3) ->
  (forall c p, frame_addr lyc c p = frame_addr ly3 c p) -> incl own own3 ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) blc3 ly3 own3 ->
  awr_ok E (r :: rs) STK sp0 FP (ablocks B ly S) blc3 ly3 own3.
Proof.
intros B E r rs STK sp0 FP ly S lyc Sc own W memc sp q n m blc3 ly3 own3 Hb Hq Hlo Hhi Htw Hbl Hfa Hown H a (r' & [<- | Hin] & Ha).
- rewrite Hb in Ha. cbn [base_val] in Ha. rewrite Hq in Ha.
  exact (oc_awr_move _ _ _ _ _ _ _ _ _ _ _ (proj1 (Htw a ltac:(lia))) Hbl Hfa Hown).
- apply H. exists r'. split; [exact Hin | exact Ha].
Qed.
(* the dots byte or-ed with bit i *)
Section ob. Context {fx : YK11.FPState}.
Lemma oc_or_byte : forall E k d i, ew E k = Z_to_bv 64 d -> 0 <= d < 256 -> 0 <= i < 8 ->
  sv_denot E (SAlu ALU_OR (SExt false 8 (SOff k 0)) (SLit (2 ^ i))) = Z_to_bv 64 (Z.lor d (2 ^ i)).
Proof.
intros E k d i Hk Hd Hi. rewrite denot_lit_U. f_equal.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SExt, U_SLit. cbv iota beta.
rewrite (U_atom E k d Hk) by lia. change (2 ^ Z.of_N 8) with 256. rewrite (Z.mod_small d) by lia.
assert (Hp : 0 <= 2 ^ i < 256) by (split; [apply Z.pow_nonneg; lia | change 256 with (2 ^ 8); apply Z.pow_lt_mono_r; lia]).
rewrite (zcanon_id d) by (unfold M64; lia). rewrite (zcanon_id (2 ^ i)) by (unfold M64; lia).
apply zcanon_id. unfold M64.
assert (0 <= Z.lor d (2 ^ i) < 256).
{ split; [apply Z.lor_nonneg; lia|].
  assert (H : Z.shiftr (Z.lor d (2 ^ i)) 8 = 0)
    by (rewrite Z.shiftr_lor, !Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256; rewrite !Z.div_small by lia; reflexivity).
  apply Z.shiftr_eq_0_iff in H. destruct H as [H | (H1 & H2)]; [lia|].
  change 256 with (2 ^ 8). apply (Z.log2_lt_pow2 _ 8 H1). exact H2. }
lia.
Qed.
End ob.


(* ================================ the second loop's steps on the spec ================================ *)
Lemma oc_lor_bound : forall d i, 0 <= d < 256 -> 0 <= i < 8 -> 0 <= Z.lor d (2 ^ i) < 256.
Proof.
intros d i Hd Hi.
assert (Hp : 0 <= 2 ^ i < 256) by (split; [apply Z.pow_nonneg; lia | change 256 with (2 ^ 8); apply Z.pow_lt_mono_r; lia]).
split; [apply Z.lor_nonneg; lia|].
assert (H : Z.shiftr (Z.lor d (2 ^ i)) 8 = 0)
  by (rewrite Z.shiftr_lor, !Z.shiftr_div_pow2 by lia; change (2 ^ 8) with 256; rewrite !Z.div_small by lia; reflexivity).
apply Z.shiftr_eq_0_iff in H. destruct H as [H | (H1 & H2)]; [lia|].
change 256 with (2 ^ 8). apply (Z.log2_lt_pow2 _ 8 H1). exact H2.
Qed.
Lemma oc_Q_neg : forall n s dot i d, (i < 8 - n)%nat -> (n <= 8)%nat ->
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat i) (8 - i) (oc_segL n s i) d =
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat (Datatypes.S i)) (8 - Datatypes.S i) (oc_segL n s (Datatypes.S i)) d.
Proof.
intros n s dot i d Hi Hn. replace (8 - i)%nat with (Datatypes.S (8 - Datatypes.S i)) by lia.
rewrite oc_ct2_neg by lia. rewrite oc_segL_S. rewrite (proj2 (Nat.ltb_lt i (8 - n))) by lia. reflexivity.
Qed.
Lemma oc_Q_dot0 : forall n s dot i d, (8 - n <= i)%nat -> (i < 8)%nat -> (n <= 8)%nat -> nth (i - (8 - n)) dot 0 = 0 ->
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat i) (8 - i) (oc_segL n s i) d =
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat (Datatypes.S i)) (8 - Datatypes.S i) (oc_segL n s (Datatypes.S i)) d.
Proof.
intros n s dot i d Hi Hi8 Hn Hd. replace (8 - i)%nat with (Datatypes.S (8 - Datatypes.S i)) by lia.
rewrite oc_ct2_pos by lia. cbv zeta.
replace (Z.to_nat (Z.of_nat i - (8 - Z.of_nat n))) with (i - (8 - n))%nat by lia. rewrite Hd. cbn [Z.eqb negb].
rewrite oc_segL_S. rewrite (proj2 (Nat.ltb_ge i (8 - n))) by lia. reflexivity.
Qed.
Lemma oc_Q_dot1 : forall n s dot i d, (8 - n <= i)%nat -> (i < 7)%nat -> (n <= 8)%nat -> nth (i - (8 - n)) dot 0 <> 0 ->
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat i) (8 - i) (oc_segL n s i) d =
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat (Datatypes.S i)) (8 - Datatypes.S i) (oc_segL n s (Datatypes.S i))
    (Z.lor d (2 ^ Z.of_nat i)).
Proof.
intros n s dot i d Hi Hi7 Hn Hd. replace (8 - i)%nat with (Datatypes.S (8 - Datatypes.S i)) by lia.
rewrite oc_ct2_pos by lia. cbv zeta.
replace (Z.to_nat (Z.of_nat i - (8 - Z.of_nat n))) with (i - (8 - n))%nat by lia.
rewrite (proj2 (Z.eqb_neq _ _) Hd). cbn [negb]. rewrite (proj2 (Z.eqb_neq (Z.of_nat i) 7)) by lia.
rewrite oc_segL_S. rewrite (proj2 (Nat.ltb_ge i (8 - n))) by lia. reflexivity.
Qed.
Lemma oc_Q_err : forall n s dot d, (1 <= n <= 8)%nat -> nth (7 - (8 - n)) dot 0 <> 0 ->
  fst (fst (DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat 7) (8 - 7) (oc_segL n s 7) d)) = DgnSpec.E_RANGE.
Proof.
intros n s dot d Hn Hd. change (8 - 7)%nat with (Datatypes.S 0). rewrite oc_ct2_pos by lia. cbv zeta.
replace (Z.to_nat (Z.of_nat 7 - (8 - Z.of_nat n))) with (7 - (8 - n))%nat by lia.
rewrite (proj2 (Z.eqb_neq _ _) Hd). reflexivity.
Qed.
Lemma oc_Q_end : forall n s dot d,
  DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat 8) (8 - 8) (oc_segL n s 8) d = (0, oc_segL n s 8, d).
Proof. reflexivity. Qed.



Lemma oc_Q_negs : forall n s dot m, (m <= 8 - n)%nat -> (n <= 8)%nat ->
  DgnLib.ct2 (Z.of_nat n) s dot = DgnLib.ct2_go (Z.of_nat n) s dot (Z.of_nat m) (8 - m) (oc_segL n s m) 0.
Proof.
intros n s dot m. induction m as [|m IH]; intros Hm Hn; [reflexivity|].
rewrite IH by lia. apply oc_Q_neg; lia.
Qed.
Section cl. Context {fx : YK11.FPState}.
(* the engine's condition dt & 7 < s for a non-zero shadow byte s of *dots (saddr_ok) *)
Lemma oc_cond_lt : forall E dt sv, ew E 12 = Z_to_bv 64 dt -> 0 <= dt < 2 ^ 63 -> ew E 333 = Z_to_bv 64 sv ->
  dt mod 8 < sv < 8 ->
  branch_taken BC_LT (sv_denot E (SAlu ALU_AND (SOff 12 0) (SLit 7))) (sv_denot E (SOff 333 0)) = true.
Proof.
intros E dt sv H12 Hdt H333 Hs.
assert (Ha : sv_denot E (SAlu ALU_AND (SOff 12 0) (SLit 7)) = Z_to_bv 64 (dt mod 8)).
{ rewrite denot_lit_U. f_equal. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (U_atom E 12 dt H12) by lia.
  change (zcanon 7) with 7. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8.
  apply zcanon_id. unfold M64. pose proof (Z.mod_pos_bound dt 8 ltac:(lia)). lia. }
rewrite Ha, sv_denot_SOff0, H333.
pose proof (Z.mod_pos_bound dt 8 ltac:(lia)).
rewrite YO0c.branch_lt. rewrite !unsigned_lit. unfold zcanon, M64, YO0b.s64.
rewrite (Z.mod_small (dt mod 8)) by lia. rewrite (Z.mod_small sv) by lia.
rewrite (proj2 (Z.ltb_lt (dt mod 8) (2 ^ 63))) by lia. rewrite (proj2 (Z.ltb_lt sv (2 ^ 63))) by lia.
apply Z.ltb_lt. lia.
Qed.
End cl.

(* ================================ seg[8] and *dots read off the second loop's regions ================================ *)
Section rg. Context {fx : YK11.FPState}.
Lemma oc_sext_byte : forall E a v, ew E a = Z_to_bv 64 v -> 0 <= v < 256 -> sv_denot E (SExt false 8 (SOff a 0)) = Z_to_bv 64 v.
Proof.
intros E a v Ha Hv. rewrite denot_lit_U. f_equal. rewrite U_SExt. cbv iota beta. rewrite (U_atom E a v Ha) by lia.
change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. apply zcanon_id. unfold M64. lia.
Qed.
Lemma oc_segL_len : forall n s i, length (oc_segL n s i) = i.
Proof. intros. unfold oc_segL. rewrite length_map, length_seq. reflexivity. Qed.
Lemma oc_nth_map_seq0 : forall (f : nat -> Z) i j, (j < i)%nat -> nth j (map f (seq 0 i)) 0 = f j.
Proof.
intros f i j Hj. rewrite (nth_indep _ 0 (f 0%nat)) by (rewrite length_map, length_seq; lia).
rewrite map_nth, seq_nth by lia. reflexivity.
Qed.
Lemma oc_segL_nth : forall n s i j, (j < i)%nat ->
  nth j (oc_segL n s i) 0 = if (j <? 8 - n)%nat then 0 else nth (j - (8 - n)) s 0.
Proof. intros n s i j Hj. unfold oc_segL. rewrite oc_nth_map_seq0 by exact Hj. reflexivity. Qed.
Lemma oc_garr8_sg : forall E (mm : word -> option byte) n s sg,
  (n <= 8)%nat -> length s = n -> Forall (fun v => 0 <= v < 128) s ->
  (forall k, (k < n)%nat -> ew E (310 + k) = Z_to_bv 64 (nth k s 0)) ->
  bv_unsigned (ew E 11) = sg ->
  region_ok tfibsegs E mm (oc_sgQ n 8) -> garr8 tfibsegs mm sg (oc_segL n s 8).
Proof.
intros E mm n s sg Hn Hl Hs Hk H11 HR j Hj. rewrite oc_segL_len in Hj. rewrite oc_segL_nth by exact Hj.
assert (Hv : 0 <= (if (j <? 8 - n)%nat then 0 else nth (j - (8 - n)) s 0) < 256).
{ destruct (Nat.ltb_spec j (8 - n)); [lia|].
  apply (codec_text.nth_Forall (fun v => 0 <= v < 256)); [|lia].
  eapply Forall_impl; [|exact Hs]. intros x Hx; cbv beta in *; lia. }
split; [|exact Hv].
eapply (field_of_region E mm 11 sg _ 0 8 0 8 (Z.of_nat j) 1%N (oc_segv n j)); [exact HR | exact H11 | | | lia | lia].
- unfold oc_sgQ. apply in_map_iff. exists j. split; [reflexivity|]. apply in_rev. rewrite rev_involutive. apply in_seq. lia.
- unfold oc_segv. destruct (Nat.ltb_spec j (8 - n)) as [H | H]; [reflexivity|].
  apply oc_sext_byte; [apply Hk; lia | lia].
Qed.
End rg.

(* ================================ tactics of the second loop ================================ *)
(* write windows: oc_awr's, and the regions on seg[8] (atom 11) and *dots (atom 12) by the contract's twr_ok *)
Ltac oc_awrQ :=
  lazymatch goal with |- awr_ok ?E ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok E rs' stk sp0 fp b0 bc ly own) end;
  lazymatch goal with AGx : forall n, (n < 33)%nat -> _ |- _ =>
  repeat lazymatch goal with
  | |- awr_ok _ [] _ _ _ _ _ _ _ => apply awr_ok_nil
  | |- awr_ok _ (YP09.mkRegion (Some 11%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
     lazymatch goal with Htw : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?q 8, HPx : Permutation _ _ |- _ =>
     eapply (oc_awr_ok_cons_twr3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q 8 11%nat);
       [ reflexivity | evalE AGx | cbn; lia | cbn; lia | exact Htw
       | intros ? ? Hx; exact (Permutation_in _ (Permutation_sym HPx) Hx)
       | intros ? ?; symmetry; lazymatch goal with EFx : forall c p, frame_addr _ c p = frame_addr _ c p |- _ => apply EFx end
       | intros ? Hx; right; exact Hx | ] end
  | |- awr_ok _ (YP09.mkRegion (Some 12%nat) _ _ _ _ _ :: _) _ _ _ _ _ _ _ =>
     lazymatch goal with Htw : twr_ok _ _ _ _ _ _ _ _ _ _ _ _ _ ?q 1, HPx : Permutation _ _ |- _ =>
     eapply (oc_awr_ok_cons_twr3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q 1 12%nat);
       [ reflexivity | evalE AGx | cbn; lia | cbn; lia | exact Htw
       | intros ? ? Hx; exact (Permutation_in _ (Permutation_sym HPx) Hx)
       | intros ? ?; symmetry; lazymatch goal with EFx : forall c p, frame_addr _ c p = frame_addr _ c p |- _ => apply EFx end
       | intros ? Hx; right; exact Hx | ] end
  | |- awr_ok _ (YP09.mkRegion _ _ _ ?wlo ?whi _ :: _) _ _ _ _ _ _ _ =>
     first
     [ lazymatch (eval vm_compute in (Z.leb whi wlo)) with true => apply awr_ok_cons_ro; [clear; cbn; lia|] end
     | lazymatch goal with Ux : bv_unsigned (ew _ 2) = ?spv, Hsp0 : ?spv <= ?s0 |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
       eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - s0));
       [reflexivity | evalE AGx; clear; lia | cbn [YP09.r_wlo YP09.r_whi]; oc_stk_lia | cbn [YP09.r_wlo YP09.r_whi]; oc_stk_lia |] end
     | lazymatch goal with E70x : ew _ 70 = Z_to_bv 64 ?s1, Hsp0 : _ <= ?s0 |- awr_ok _ _ _ ?s0 _ _ _ _ _ =>
       eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 70%nat (s1 - s0));
       [reflexivity | evalE AGx; clear; lia | cbn [YP09.r_wlo YP09.r_whi]; oc_stk_lia | cbn [YP09.r_wlo YP09.r_whi]; oc_stk_lia |] end
     | lazymatch goal with HFx : ?Fv = frame_addr _ 1 ?ps |- _ =>
       eapply (cw_awr_ok_cons_frame _ _ _ _ _ _ _ _ _ _ 1 ps 75%nat);
       [reflexivity | evalE AGx; try (lazymatch goal with EFx : forall c p, frame_addr ?l1 c p = frame_addr ?l2 c p |- _ => rewrite EFx end); exact HFx
       | left; reflexivity | clear; cbn; lia | clear; cbn; change (fs_frame_bytes 1) with 128; lia |] end ]
  end end.
(* the cover of a run's writes: oc_win's, and the bytes the call writes (seg[8], *dots: E, not the image) *)
Ltac oc_winQ a Hb :=
  first
  [ oc_win a Hb
  | lazymatch goal with AGx : forall n, (n < 33)%nat -> _ |- _ => revert Hb; evalE AGx; intros Hb end;
    first
    [ lazymatch goal with HnI : forall x, ?q <= x < ?q + 8 -> ~ in_img _ x |- _ =>
        right; left; split; [left; clear - Hb; lia | apply HnI; clear - Hb; lia] end
    | lazymatch goal with HnI : forall x, ?q <= x < ?q + 1 -> ~ in_img _ x |- _ =>
        right; left; split; [right; clear - Hb; lia | apply HnI; clear - Hb; lia] end ] ].

(* the join to a second-loop head tg: tg's facts, the dots chunk (region 1) into the fresh atom k holding w (eqtac proves
   the chunk's value is w), tg's regions, the dead registers into the window OC_RT *)
Ltac oc_joinQ HS tg k w eqtac :=
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let fa := eval vm_compute in (f_atoms (ss_facts tg)) in
    let cd := eval vm_compute in (f_conds (ss_facts tg)) in
    let al := eval vm_compute in (f_alias (ss_facts tg)) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_facts_incl3 tfibsegs Ex ssx msx fa cd al HS ltac:(incl_lit_tac) ltac:(incl_lit_tac)
      ltac:(incl_lit_tac)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let HS3 := fresh "HS3" in
    pose proof (st_ok_havoc_win tfibsegs k Ex ssx msx [w] HS ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    lazymatch eval vm_compute in (ss_mem ssx) with
    | ?r0 :: YP09.mkRegion ?b ?lo ?hi ?wlo ?whi (YP09.mkChunk ?o (CVal ?wd ?v) :: ?cs) :: ?rs =>
      let HS3 := fresh "HS3" in
      pose proof (oc_swap1 Ex ssx msx r0 b lo hi wlo whi o wd v (SOff k 0) cs rs HS ltac:(vm_compute; reflexivity)
        ltac:(eqtac)) as HS3;
      clear HS; rename HS3 into HS end end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let rs := eval vm_compute in (ss_mem tg) in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_submem tfibsegs Ex ssx msx rs HS ltac:(cbn [ss_mem]; submem_to) ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS end;
  norm_ss HS;
  let dlb := eval cbv in (map (fun n => Z_to_bv 5 (Z.of_nat n)) ocQ_deads) in
  oc_lit_regs HS dlb;
  lazymatch type of HS with st_ok _ ?Ex ?ssx ?msx =>
    let vals := constr:(map (fun r : bv 5 => getr (ms_regs msx) r) dlb) in
    let vals' := eval cbn [map ms_regs restrict] in vals in
    let HS3 := fresh "HS3" in
    pose proof (st_ok_havoc_win tfibsegs 400 Ex ssx msx vals' HS ltac:(vm_compute; reflexivity)) as HS3;
    clear HS; rename HS3 into HS;
    set_regs_rec HS 400%nat vals' 0%nat dlb end;
  norm_ss HS;
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    first [change ssx with tg in HS | let t := eval vm_compute in tg in idtac "OC-JOIN-MISMATCH" ssx t; fail 1] end.
