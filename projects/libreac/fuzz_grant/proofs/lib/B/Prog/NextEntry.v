(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a segment of reac_headamp_tx_next on fuzz_grant.asan (NextEntry), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AC8a.v. *)
(* Modified by Theorem Labs, 2026-10: image B (fuzz_grant.asan-ubsan) twin of lib/A/Prog/NextEntry.v at a working branch af735a950e2 (blob 8725db69d2a; the walk was ported from blob 7788bf8f6e4 at a working branch afd75724b5b, which differs from it only by 4 added and 0 removed lines, the licence header), restated over image B's listing, addresses and walk layer (lib/B/Prog) against GrantBContracts.v; frame 96 with twelve saved registers, UBSan traps T1 and T2, and the .rodata divisor read at 0x85fa4 (IMG_NEXT_DIV3) *)
(* reac_headamp_tx_next (fuzz_grant.asan-ubsan 0x85efc): the walk of its entry segment, from the
   first slot to the head of the edge scan LOOPD (0x85fb8) or to the return when the table is idle
   (src/reac_headamp_tx.c:111-112), and the theorem that the whole function meets
   tb_reac_headamp_tx_next_spec once the edge scan's cut (NextEdge.v) and the after-scan's cut
   (NextAfter.v) are given. The entry segment reaches AFTR only through the edge scan, and
   NextEdge.v proves nx_dloop_stmt from the after-scan's cut, so nx_walk takes the second cut only to
   have the shape HeadampTxNextClose.v composes.

   The entry segment writes only the twelve saved registers into its own frame. It is seated with
   the table's ten scalar fields read-only (HeadampTxNext.v ss_ro), so each run's frame keeps every
   byte outside that frame, and the table and the three caller bytes come out unchanged.

   What the segment settles, slot by slot:
     - the UBSan trap guards T1 `beqz a0` 0x85f30 (tx = 0) and T2 `bnez (a0 & 3)` 0x85f3c (tx not
       4-aligned) to the `unimp` at 0x8644c: the table is a live block, so 4096 <= tx and
       tx mod 16 = 0 (atom 10's fact PTRN 4), and the engine decides both inside the run;
     - the ASan checks #1 (0x85f60, lw tx+432; slow block 0x86450, report 0x8645c) and #2 (0x85f7c,
       lbu tx+437; slow block 0x864cc, report 0x864d4): the table's shadow entry mkSHE 10 0 460
       covers both granules whole, so the shadow byte is 0 and both take the fast branch, settled
       inside the run;
     - the load of the multiplier 0xAAAAAAAAAAAAAAAB at 0x85fa4 from .rodata 0x10320 (listing object
       34), read through nx_walk's premise IMG_NEXT_DIV3 (GrantBContracts.v) below;
     - the idle return 0x85f84 -> 0x862cc..0x86300: the twelve saved registers read back, a0 = 0,
       and the answer `silent T`. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0f YI16 YI0s YI67.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaRun PaShadow PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantFrame GrantRo YC1h.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import Mem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import
HeadampModel NextModel NextLemmas SlotNeeds_c HeadampI1.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import GrantBContracts HeadampTxNext.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Notation TX_SIZE := ATx.TX_SIZE.
#[local] Notation LAY_TX := ATx.LAY_TX.
#[local] Notation tx_vals := ATx.tx_vals.
#[local] Notation tx_fbyte := ATx.tx_fbyte.

Lemma ne_u32at_range : forall T k, 0 <= u32at T k < 4294967296.
Proof. intros T k. rewrite u32at_u32. apply u32_range. Qed.

(* A register's value from its symbolic value's unsigned reading. *)
Lemma ne_denot : forall E e v, U E e = v mod 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite denot_lit_U, H. apply Z_to_bv64_mod. Qed.

Lemma ne_U_off : forall E n c x v, bv_unsigned (ew E n) = x -> x + c = v ->
  U E (SOff n c) = v mod 2 ^ 64.
Proof. intros E n c x v Hx Hv. rewrite U_SOff, Hx, Hv. reflexivity. Qed.

(* `not` (xori rd, rs, -1) on a 64-bit value. *)
Lemma ne_lxor_ones : forall a n, 0 < n -> 0 <= a < 2 ^ n -> Z.lxor a (Z.ones n) = Z.ones n - a.
Proof.
  intros a n Hn Ha.
  assert (Hlog : Z.log2 a < n).
  { destruct (Z.eq_dec a 0) as [->|Hz]; [rewrite Z.log2_nonpos; lia|].
    apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia. }
  rewrite <- (Z.ldiff_ones_l_low a n) by lia.
  rewrite Z.ldiff_land.
  assert (E : Z.land (Z.ones n) (Z.lnot a) = Z.land (Z.lnot a) (Z.ones n)) by apply Z.land_comm.
  rewrite E. rewrite Z.land_ones by lia. unfold Z.lnot, Z.ones. rewrite Z.shiftl_1_l.
  replace (Z.pred (- a)) with ((2 ^ n - 1 - a) + (-1) * 2 ^ n) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma ne_U_not : forall E v z, zcanon z = Z.ones 64 ->
  U E (SAlu ALU_XOR v (SLit z)) = 2 ^ 64 - 1 - U E v.
Proof.
  intros E v z Hz. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, Hz.
  pose proof (U_range E v) as Hr. unfold M64 in Hr. rewrite ne_lxor_ones by lia.
  change (Z.ones 64) with (2 ^ 64 - 1). apply YP0m.zcanon_small. lia.
Qed.

(* The sign-extended 32-bit load of an unsigned 32-bit field is 0 exactly when the field is. *)
Lemma ne_sext32_0 : forall u, 0 <= u < 4294967296 ->
  (zcanon (bv_swrap 32 (u mod 2 ^ Z.of_N 32)) =? zcanon 0) = (u =? 0).
Proof.
  intros u Hu. change (2 ^ Z.of_N 32) with 4294967296. rewrite (Z.mod_small u) by lia.
  change (zcanon 0) with 0.
  destruct (Z.eqb_spec u 0) as [->|Hne]; [reflexivity|].
  apply Z.eqb_neq. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  unfold zcanon, M64. intros H. Z.div_mod_to_equations. lia.
Qed.

Ltac ne_skel_tac :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; vm_compute in Hr;
  repeat (destruct Hr as [Hr | Hr];
          [subst r; vm_compute; repeat (first [left; reflexivity | right]) |]);
  destruct Hr.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).

(* The multiplier of the dirty scan's division by 3, as image B's `ld t4` at 0x85fa4 reads it from
   .rodata 0x10320 (listing object 34): eight bytes, read-only. *)
Definition ROD34 : YP09.region := obj8_region 34 (SLit 12297829382473034411).

(* Every region the entry segment's states hold: ss_ro's four, and the multiplier's word, which the
   walk seats once the shadow base is in s5 and the two image words it was read through are gone. *)
Definition ne_regs : list YP09.region := nx_regs_ro ++ [ROD34].

(* Only the frame of these regions is written. *)
Lemma ne_wrange : forall (E : env) (rs : smem) (sp a : Z),
  (forall r, In r rs -> In (skel r) (skeleton ne_regs)) ->
  bv_unsigned (ew E 2) = sp -> in_wrange E rs a -> sp - NX_FRAME <= a < sp.
Proof.
  intros E rs sp a Hsk E2 (r & Hin & Ha).
  pose proof (Hsk r Hin) as Hs.
  unfold ne_regs, nx_regs_ro, ROD34, obj8_region, stack_region, got_regionP, bcell_regionP, TXSro,
    skeleton in Hs.
  cbn [app map skel YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi] in Hs.
  unfold NX_FRAME in *.
  destruct Hs as [Hs|[Hs|[Hs|[Hs|[Hs|Hs]]]]]; try (exfalso; exact Hs);
    symmetry in Hs; unfold skel in Hs;
    injection Hs as H1 H2 H3 H4 H5;
    rewrite ?H1, ?H2, ?H3, ?H4, ?H5 in Ha; cbn [base_val] in Ha.
  - rewrite E2 in Ha. lia.
  - lia.
  - lia.
  - lia.
  - lia.
Qed.

(* What the entry segment has changed so far: nothing outside its frame. *)
Definition ne_stk_same (W : world SEGS) (memc m : word -> option byte) (sp : Z) : Prop :=
  forall x : word, ~ (sp - NX_FRAME <= bv_unsigned x < sp) ->
    mrestrict (w_H W) m x = mrestrict (w_H W) memc x.

Lemma ne_stk_same_step : forall (W : world SEGS) memc m1 m2 (E : env) (rs : smem) (sp : Z),
  ne_stk_same W memc m1 sp ->
  frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
  (forall r, In r rs -> In (skel r) (skeleton ne_regs)) ->
  bv_unsigned (ew E 2) = sp ->
  ne_stk_same W memc m2 sp.
Proof.
  intros W memc m1 m2 E rs sp HS HF Hsk E2 x Hx.
  rewrite (HF x); [exact (HS x Hx)|].
  intros Hw. exact (Hx (ne_wrange E rs sp (bv_unsigned x) Hsk E2 Hw)).
Qed.

Lemma ne_apresent_grow : forall (H : word -> bool) m1 m2 a,
  mem_grows (mrestrict H m1) (mrestrict H m2) -> apresent H m1 a -> apresent H m2 a.
Proof.
  intros H m1 m2 a HG (Hh & b & Hb). split; [exact Hh|].
  pose proof (HG (Z_to_bv 64 a)) as G. unfold mrestrict in G. rewrite Hh in G.
  destruct (m2 (Z_to_bv 64 a)) as [b'|] eqn:E2; [exists b'; reflexivity|].
  exfalso. apply G; [rewrite Hb; discriminate | reflexivity].
Qed.

(* A byte outside the frame reads in the image view as it did at the call. *)
Lemma ne_stk_aview : forall (W : world SEGS) memc m sp a,
  ne_stk_same W memc m sp -> 0 <= a < 2 ^ 64 -> ~ (sp - NX_FRAME <= a < sp) ->
  aview SEGS (w_H W) m a = aview SEGS (w_H W) memc a.
Proof.
  intros W memc m sp a HS Ha Hst.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit_small; exact Ha).
  unfold aview, mbyte. rewrite (HS (Z_to_bv 64 a) ltac:(rewrite Hu; exact Hst)). reflexivity.
Qed.

(* The walk's own invariant from the segment's: everything outside the frame is kept, so nx_same
   holds for any d, and the three caller bytes (clear of the call's window) are untouched. *)
Lemma ne_same_of_stk : forall (W : world SEGS) memc m sp tx chp parp valp d,
  ne_stk_same W memc m sp -> nx_same W memc m sp tx chp parp valp d.
Proof.
  intros W memc m sp tx chp parp valp d HS x Hx _. apply HS.
  pose proof nx_frame_le. intros Hy. apply Hx. lia.
Qed.

Lemma ne_outq_of_stk : forall (W : world SEGS) memc m sp tx chp parp valp,
  ne_stk_same W memc m sp ->
  thd_out_ok sp tx chp -> thd_out_ok sp tx parp -> thd_out_ok sp tx valp ->
  nx_outq W memc m chp parp valp.
Proof.
  intros W memc m sp tx chp parp valp HS Hc Hp Hv.
  pose proof nx_stk_val as HNX. unfold NX_STK in HNX.
  assert (K : forall q, thd_out_ok sp tx q -> aview SEGS (w_H W) m q = aview SEGS (w_H W) memc q).
  { intros q (Hq0 & Hq1 & Hq2 & Hq3 & Hq4 & Hq5).
    apply (ne_stk_aview W memc m sp q HS); [lia|]. unfold NX_FRAME. lia. }
  split; [|split]; apply K; assumption.
Qed.

(* The table outside the frame is the table at the call. *)
Lemma ne_obj_kept : forall (W : world SEGS) memc m sp tx T,
  ne_stk_same W memc m sp -> 0 <= tx -> tx + 460 <= sp - NX_FRAME -> sp <= 2 ^ 47 ->
  obj_at SEGS (mrestrict (w_H W) memc) tx LAY_TX (tx_vals T) ->
  obj_at SEGS (mrestrict (w_H W) m) tx LAY_TX (tx_vals T).
Proof.
  intros W memc m sp tx T HS Htx Hsp Hsp47 HO.
  apply (proj2 (ATx.tx_obj_bytes SEGS (mrestrict (w_H W) m) tx T)).
  intros i Hi. pose proof (ATx.tx_fbyte_range i Hi) as Hir.
  rewrite <- (proj1 (ATx.tx_obj_bytes SEGS (mrestrict (w_H W) memc) tx T) HO i Hi).
  unfold mbyte. rewrite (HS (Z_to_bv 64 (tx + i))); [reflexivity|].
  assert (Hu : bv_unsigned (Z_to_bv 64 (tx + i)) = tx + i)
    by (apply unsigned_lit_small; unfold NX_FRAME in *; lia).
  rewrite Hu. unfold NX_FRAME in *. lia.
Qed.

(* An eight-byte value outside the frame reads as it did at the call. *)
Lemma ne_val8_kept : forall (W : world SEGS) memc m sp a v,
  ne_stk_same W memc m sp -> 0 <= a -> a + 8 <= sp - NX_FRAME -> sp <= 2 ^ 47 ->
  val_mem SEGS (mrestrict (w_H W) memc) a 8 v -> val_mem SEGS (mrestrict (w_H W) m) a 8 v.
Proof.
  intros W memc m sp a v HS Ha Hsp Hsp47 HV j Hj.
  rewrite <- (HV j Hj). unfold mbyte.
  rewrite (HS (Z_to_bv 64 (a + Z.of_nat j))); [reflexivity|].
  assert (Hu : bv_unsigned (Z_to_bv 64 (a + Z.of_nat j)) = a + Z.of_nat j)
    by (apply unsigned_lit_small; unfold NX_FRAME in *; lia).
  rewrite Hu. unfold NX_FRAME in *. lia.
Qed.

(* The table's bytes, as the memory-checking runtime's view gives them. *)
Definition ne_bytes (m : word -> option byte) (tx : Z) (T : list byte) : Prop :=
  forall i, tx_fbyte i = true -> mbyte SEGS m (tx + i) = Some (nth (Z.to_nat i) T (Z_to_bv 8 0)).

Lemma ne_val1 : forall m tx T k,
  ne_bytes m tx T -> tx_fbyte k = true -> val_mem SEGS m (tx + k) 1 (tb T k).
Proof.
  intros m tx T k HB Hk j Hj. destruct j as [|j]; [|lia].
  pose proof (tb_range T k) as Hr.
  rewrite le_byte_small by (cbn; lia).
  change (Z.of_nat 0%nat) with 0. rewrite Z.mul_0_r, Z.shiftr_0_r, Z.add_0_r.
  rewrite Z_to_bv8_tb. exact (HB k Hk).
Qed.

Lemma ne_val4 : forall m tx T k,
  ne_bytes m tx T -> (forall d, 0 <= d < 4 -> tx_fbyte (k + d) = true) ->
  val_mem SEGS m (tx + k) 4 (u32at T k).
Proof.
  intros m tx T k HB Hk j Hj.
  pose proof (tb_range T k). pose proof (tb_range T (k + 1)).
  pose proof (tb_range T (k + 2)). pose proof (tb_range T (k + 3)).
  assert (Hu : 0 <= u32at T k < 2 ^ (8 * Z.of_nat 4)).
  { change (2 ^ (8 * Z.of_nat 4)) with 4294967296. apply ne_u32at_range. }
  rewrite (le_byte_small (u32at T k) 4 j Hu Hj).
  replace (Z_to_bv 8 (Z.shiftr (u32at T k) (8 * Z.of_nat j)))
    with (Z_to_bv 8 (tb T (k + Z.of_nat j))).
  2:{ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 8) with 256. rewrite Z.shiftr_div_pow2 by lia.
      destruct j as [|[|[|[|j]]]]; try lia.
      - change (8 * Z.of_nat 0%nat) with 0. change (Z.of_nat 0%nat) with 0.
        rewrite Z.add_0_r, Z.pow_0_r, Z.div_1_r. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 1%nat) with 8. change (Z.of_nat 1%nat) with 1.
        change (2 ^ 8) with 256. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 2%nat) with 16. change (Z.of_nat 2%nat) with 2.
        change (2 ^ 16) with 65536. unfold u32at. Z.div_mod_to_equations. lia.
      - change (8 * Z.of_nat 3%nat) with 24. change (Z.of_nat 3%nat) with 3.
        change (2 ^ 24) with 16777216. unfold u32at. Z.div_mod_to_equations. lia. }
  rewrite Z_to_bv8_tb.
  replace (tx + k + Z.of_nat j) with (tx + (k + Z.of_nat j)) by lia.
  apply HB, Hk. lia.
Qed.

Ltac ne_reg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    assert (H : getr (ms_regs ms) r = sv_denot Ex e)
      by exact (st_ok_pi_restrict_reg Hh Ex ss ms r HS)
  end.

(* After each run: fold the run's frame into what the segment has kept so far. *)
Ltac ne_acc Usp :=
  repeat match goal with
  | H : frame_of _ _ (ms_mem _) (ms_mem _) |- _ => clear H
  | H : frame_of _ _ ?m0 ?m1 |- _ =>
      lazymatch m0 with mrestrict _ _ => fail | _ => clear H end
  end;
  match goal with
  | ACC : ne_stk_same _ _ ?m1 _,
    HFr : frame_of ?Ex ?rs (mrestrict _ ?m1) (mrestrict _ ?m2),
    HG : mem_grows (mrestrict _ ?m1) (mrestrict _ ?m2),
    GRO : mem_grows _ (mrestrict _ ?m1) |- _ =>
    let ACC' := fresh "ACC" in let GRO' := fresh "GRO" in
    pose proof (ne_stk_same_step _ _ _ _ Ex rs _ ACC HFr ltac:(ne_skel_tac) Usp) as ACC';
    pose proof (mem_grows_trans _ _ _ GRO HG) as GRO';
    clear ACC HFr HG GRO; rename ACC' into ACC; rename GRO' into GRO
  end.

(* The frame the prologue leaves: the twelve `sd` of 0x85f00..0x85f2c, ra at -8 down to s10 at -96. *)
Definition ne_saved_chunks : list YP09.chunk :=
  [ YP09.mkChunk (-96) (CVal 8 (SOff 26 0)); YP09.mkChunk (-88) (CVal 8 (SOff 25 0));
    YP09.mkChunk (-80) (CVal 8 (SOff 24 0)); YP09.mkChunk (-72) (CVal 8 (SOff 23 0));
    YP09.mkChunk (-64) (CVal 8 (SOff 22 0)); YP09.mkChunk (-56) (CVal 8 (SOff 21 0));
    YP09.mkChunk (-48) (CVal 8 (SOff 20 0)); YP09.mkChunk (-40) (CVal 8 (SOff 19 0));
    YP09.mkChunk (-32) (CVal 8 (SOff 18 0)); YP09.mkChunk (-24) (CVal 8 (SOff 9 0));
    YP09.mkChunk (-16) (CVal 8 (SOff 8 0)); YP09.mkChunk (-8) (CVal 8 (SOff 1 0)) ].

(* A register of a symbolic state, as a word: `getr (ms_regs ms) r = w64 v` becomes
   `U E e = v mod 2 ^ 64` for the register's symbolic value e. *)
Ltac ne_regval HSx :=
  lazymatch type of HSx with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    lazymatch goal with
    | |- getr (ms_regs ms) ?r = w64 ?v =>
      rewrite (st_ok_pi_restrict_reg Hh Ex ss ms r HSx);
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in
      change (sr_get (ss_regs ss) r) with e;
      unfold w64; apply ne_denot
    end
  end.

(* Close `U E e = v mod 2 ^ 64` for the values the entry segment leaves in registers: an atom plus
   an offset, a literal, or the `not` of the scan's base address. *)
Ltac ne_U_close Usp U10 U11 U12 U13 U32 :=
  lazymatch goal with
  | |- U ?Ex (SOff 2 _) = _ => apply (ne_U_off Ex 2 _ _ _ Usp); unfold NX_FRAME; lia
  | |- U ?Ex (SOff 10 _) = _ => apply (ne_U_off Ex 10 _ _ _ U10); lia
  | |- U ?Ex (SOff 11 _) = _ => apply (ne_U_off Ex 11 _ _ _ U11); lia
  | |- U ?Ex (SOff 12 _) = _ => apply (ne_U_off Ex 12 _ _ _ U12); lia
  | |- U ?Ex (SOff 13 _) = _ => apply (ne_U_off Ex 13 _ _ _ U13); lia
  | |- U ?Ex (SOff 32 _) = _ => apply (ne_U_off Ex 32 _ _ _ U32); lia
  | |- U _ (SLit _) = _ => rewrite U_SLit; vm_compute; reflexivity
  | |- U _ (SAlu ALU_XOR (SOff 10 _) (SLit _)) = _ =>
      rewrite ne_U_not by (vm_compute; reflexivity); rewrite U_SOff, U10;
      rewrite YP0m.zcanon_small by lia64; rewrite Z.mod_small by lia64; lia
  end.

Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
#[local] Notation tnext_post := (tb_reac_headamp_tx_next_post B).

(* The awr obligation of a run of the entry segment: only its own frame. *)
Lemma ne_awr : forall (E : env) STK sp0 FP ly S lyc Sc own (rs : smem) (sp : Z),
  (forall r, In r rs -> In (skel r) (skeleton ne_regs)) ->
  bv_unsigned (ew E 2) = sp -> sp0 - STK <= sp - NX_STK -> sp <= sp0 ->
  awr_ok E rs STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own.
Proof.
  intros E STK sp0 FP ly S lyc Sc own rs sp Hsk E2 Hlo Hhi a Hw.
  pose proof (ne_wrange E rs sp a Hsk E2 Hw) as Ha.
  pose proof nx_frame_le. left. unfold NX_FRAME in *. lia.
Qed.

(* The entry state, with the table's fields read-only. *)
Lemma nx_entry_ro : forall lyc Sc (W : world SEGS) (regs : bvmap 5 word) memc mdc
    (tx chp parp valp : Z) (T : list byte),
  AR SEGS B lyc Sc W memc mdc ->
  getr regs 10 = w64 tx -> getr regs 11 = w64 chp ->
  getr regs 12 = w64 parp -> getr regs 13 = w64 valp ->
  spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs <= 2 ^ 47 ->
  alloc_ceiling <= spZ regs - NX_STK ->
  (forall a, spZ regs - NX_STK <= a < spZ regs -> apresent (w_H W) memc a) ->
  In (tx, TX_SIZE) (ablocks B lyc Sc) ->
  length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) memc) tx LAY_TX (tx_vals T) ->
  thd_out_ok (spZ regs) tx chp -> thd_out_ok (spZ regs) tx parp -> thd_out_ok (spZ regs) tx valp ->
  byte_ok W memc chp -> byte_ok W memc parp -> byte_ok W memc valp ->
  st_ok_pi SEGS VAL (Eimg (Ereg regs (nx_extra tx T))) ss_ro
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_headamp_tx_next)) memc (seg_rom SEGS)))
  /\ sh_ok SEGS BxN nx_SH (Eimg (Ereg regs (nx_extra tx T))) (mrestrict (w_H W) memc).
Proof.
  intros lyc Sc W regs memc mdc tx chp parp valp T HAR H10 H11 H12 H13 Hsp16 Hspr Hceil Hpres
    Hg HL Hobj Hoc Hop Hov Rc Rp Rv.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof nx_stk_val as HNX.
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc tx TX_SIZE HAR Hg)
    as (Hg16 & Hg4096 & Hgceil & Hgh_ia & Hgpres & _).
  pose proof (blk_off_imgB B lyc Sc W memc mdc tx TX_SIZE HAR Hg) as Hgh_img.
  change (req_size TX_SIZE) with 460 in Hgceil, Hgh_ia, Hgpres, Hgh_img.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in Hgh_img.
  destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
  pose proof (pa_obj_img 35 ltac:(lia)) as HcellR.
  pose proof (pal_got_cell B TL) as HgcD.
  pose proof (pa_obj_img 1 ltac:(lia)) as HgotR.
  rewrite IMG_LO_B_val, IMG_TOP_B_val in HcellR, HgotR.
  pose proof (proj1 (ATx.tx_obj_bytes SEGS _ _ _) Hobj) as HBY.
  destruct Hoc as (Hc0 & Hc1 & Hc2 & Hc3 & Hc4 & Hc5).
  destruct Hop as (Hp0 & Hp1 & Hp2 & Hp3 & Hp4 & Hp5).
  destruct Hov as (Hv0 & Hv1 & Hv2 & Hv3 & Hv4 & Hv5).
  pose proof (ne_u32at_range T 432) as R33. pose proof (ne_u32at_range T 440) as R36.
  pose proof (ne_u32at_range T 444) as R37. pose proof (ne_u32at_range T 452) as R41.
  pose proof (ne_u32at_range T 456) as R42.
  pose proof (tb_range T 436) as R34. pose proof (tb_range T 437) as R35.
  pose proof (tb_range T 448) as R38. pose proof (tb_range T 449) as R39.
  pose proof (tb_range T 450) as R40.
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (nx_extra tx T))).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (nx_extra tx T)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E2 : ew E 2 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 chp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 parp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (u32at T 432))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (tb T 436))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 (u32at T 440))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
  assert (E37 : ew E 37 = Z_to_bv 64 (u32at T 444))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
  assert (E38 : ew E 38 = Z_to_bv 64 (tb T 448))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
  assert (E39 : ew E 39 = Z_to_bv 64 (tb T 449))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
  assert (E40 : ew E 40 = Z_to_bv 64 (tb T 450))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
  assert (E41 : ew E 41 = Z_to_bv 64 (u32at T 452))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 9)).
  assert (E42 : ew E 42 = Z_to_bv 64 (u32at T 456))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 10)).
  assert (EO1 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
    by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (EO35 : ew E (A_OBJ 35) = Z_to_bv 64 (VAL (A_OBJ 35)))
    by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
  { intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
  split.
  - unfold ss_ro. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold nx_regs_ro, stack_region, got_regionP, bcell_regionP, TXSro, TXS.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [unfold NX_FRAME; lia|]. split; [lia|].
        split; [|constructor]. intros o Ho. apply (apresent_writable SEGS). apply Hpres.
        unfold NX_FRAME in *. lia.
      * rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 35) 0) (VAL (A_OBJ 35)));
          [cbn [sv_denot]; rewrite EO35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | pose proof (pa_val_range (A_OBJ 35)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
      * rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) EO35) by (pose proof (pa_val_range (A_OBJ 35)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 35)) 0 8 BxN SB_NX);
          [cbn [sv_denot BxN]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
          | unfold SB_NX; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
      * rewrite (VB 10%nat tx E10) by lia. split; [lia|]. split; [lia|].
        split; [intros o Ho; lia|].
        repeat apply Forall_cons; try apply Forall_nil.
        -- apply (chunk_ok_val SEGS E _ tx 432 4 _ (u32at T 432));
             [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val4 (mrestrict (w_H W) memc) tx T 432 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 436 1 _ (tb T 436));
             [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val1 (mrestrict (w_H W) memc) tx T 436 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 437 1 _ (tb T 437));
             [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val1 (mrestrict (w_H W) memc) tx T 437 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 440 4 _ (u32at T 440));
             [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val4 (mrestrict (w_H W) memc) tx T 440 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 444 4 _ (u32at T 444));
             [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val4 (mrestrict (w_H W) memc) tx T 444 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 448 1 _ (tb T 448));
             [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val1 (mrestrict (w_H W) memc) tx T 448 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 449 1 _ (tb T 449));
             [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val1 (mrestrict (w_H W) memc) tx T 449 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 450 1 _ (tb T 450));
             [cbn [sv_denot]; rewrite E40, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val1 (mrestrict (w_H W) memc) tx T 450 HBY); vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 452 4 _ (u32at T 452));
             [cbn [sv_denot]; rewrite E41, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val4 (mrestrict (w_H W) memc) tx T 452 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
        -- apply (chunk_ok_val SEGS E _ tx 456 4 _ (u32at T 456));
             [cbn [sv_denot]; rewrite E42, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
             | cbn; lia | cbn; lia
             | apply (ne_val4 (mrestrict (w_H W) memc) tx T 456 HBY);
               intros d Hd; assert (d = 0 \/ d = 1 \/ d = 2 \/ d = 3) as [-> | [-> | [-> | ->]]] by lia;
               vm_compute; reflexivity].
    + apply pairwise_disjoint_of_extents.
      unfold nx_regs_ro, stack_region, got_regionP, bcell_regionP, TXSro, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB 10%nat tx E10) by lia.
      rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) EO1) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      rewrite (VB (A_OBJ 35) (VAL (A_OBJ 35)) EO35) by (pose proof (pa_val_range (A_OBJ 35)); lia).
      cbn [base_val]. rewrite Usp.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert Hgceil Hgh_img Hg4096 Hg16 Hspr Hceil HgcD HcellR HgotR C1 HNX.
      clear. unfold NX_FRAME. intros. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [nx_atoms f_atoms atoms_ok]. unfold afact_ok, PTRN, OUTF.
      cbn [af_lo af_hi af_al2].
      rewrite Usp, E10, E11, E12, E13, E32, E33, E34, E35, E36, E37, E38, E39, E40, E41, E42.
      rewrite !unsigned_lit_small by (unfold SB_NX; lia).
      change (2 ^ 4) with 16. rewrite ?Z.pow_0_r, ?Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try lia.
  - unfold sh_ok, nx_SH.
    assert (UBx : U E BxN = SHADOW_OFF).
    { unfold U, BxN. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SB_NX; lia). reflexivity. }
    constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
    + apply (shent_ok_of_block SEGS B LAWS lyc Sc W memc mdc E BxN 10 tx TX_SIZE 0 460 HAR Hg).
      * exact UBx.
      * unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply unsigned_lit_small. lia.
      * lia.
      * change (req_size TX_SIZE) with 460. lia.
    + apply (shent_ok_of_range SEGS (w_H W) memc E BxN 11 chp 1 chp 0 1 Rc UBx).
      * unfold U. cbn [sv_denot]. rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with chp by lia. exact Hc5.
    + apply (shent_ok_of_range SEGS (w_H W) memc E BxN 12 parp 1 parp 0 1 Rp UBx).
      * unfold U. cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with parp by lia. exact Hp5.
    + apply (shent_ok_of_range SEGS (w_H W) memc E BxN 13 valp 1 valp 0 1 Rv UBx).
      * unfold U. cbn [sv_denot]. rewrite E13, Z.add_0_r, Z_to_bv_bv_unsigned.
        apply unsigned_lit_small. lia.
      * lia.
      * lia.
      * cbn [Z.min Z.max]. intros x Hx. replace x with valp by lia. exact Hv5.
Qed.

(* The whole function: the entry segment, then the edge scan's cut at LOOPD (active <> 0, or
   active = 0 with a replay width), or the idle return (both 0). The premise IMG_NEXT_DIV3
   (GrantBContracts.v, a conjunct of hyps_reac_headamp_tx_next, which HeadampTxNextClose.v destructs)
   is the one image fact this walk takes: image B's read-only word at .rodata 0x10320, listing
   object 34, which the `ld t4` at 0x85fa4 reads, reads as image B's initial bytes
   0xAAAAAAAAAAAAAAAB under the contract's arodata_okP. *)
Theorem nx_walk : IMG_NEXT_DIV3 B -> nx_dloop_stmt B -> nx_after_stmt B -> tb_reac_headamp_tx_next_spec B.
Proof.
  intros HDIV3 DLOOP AFTER. unfold tb_reac_headamp_tx_next_spec.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs tx chp parp valp T
    HJ HROD Hra Hra4 Hgp Htp H10 H11 H12 H13 Hsp16 Hlo Hhi Hg HL Hobj Hrok H456 Wtab
    Hoc Hop Hov Dcp Dcv Dpv Wc Wp Wv Rc Rp Rv.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof nx_stk_val as HNX.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJpres & Hstk & _ & _).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  assert (Hlo' : sp0 - STK <= spZ regs - NX_STK) by exact Hlo.
  assert (Hspr : 2 ^ 46 <= spZ regs <= 2 ^ 47).
  { clear - C1 Hceil Hslo Hshi H47 Hlo' Hhi Hstk0 HNX. lia. }
  assert (Hac : alloc_ceiling <= spZ regs - NX_STK).
  { clear - Hceil Hslo Hlo' Hstk0. lia. }
  assert (Hpres : forall a, spZ regs - NX_STK <= a < spZ regs -> apresent (w_H W) memc a).
  { intros a Ha. apply HJpres. lia. }
  assert (Pc : apresent (w_H W) memc chp)
    by (apply (nx_present_of_twr B STK sp0 FP ly S lyc Sc own W memc (spZ regs) chp 1 chp Wc); lia).
  assert (Pp : apresent (w_H W) memc parp)
    by (apply (nx_present_of_twr B STK sp0 FP ly S lyc Sc own W memc (spZ regs) parp 1 parp Wp); lia).
  assert (Pv : apresent (w_H W) memc valp)
    by (apply (nx_present_of_twr B STK sp0 FP ly S lyc Sc own W memc (spZ regs) valp 1 valp Wv); lia).
  assert (Mt : forall a, tx <= a < tx + TX_SIZE -> nx_may_write B STK sp0 FP ly S lyc Sc own a)
    by (intros a Ha; exact (nx_may_write_of_twr B STK sp0 FP ly S lyc Sc own W memc (spZ regs) tx TX_SIZE a Wtab Ha)).
  assert (Mc : nx_may_write B STK sp0 FP ly S lyc Sc own chp)
    by (apply (nx_may_write_of_twr B STK sp0 FP ly S lyc Sc own W memc (spZ regs) chp 1 chp Wc); lia).
  assert (Mp : nx_may_write B STK sp0 FP ly S lyc Sc own parp)
    by (apply (nx_may_write_of_twr B STK sp0 FP ly S lyc Sc own W memc (spZ regs) parp 1 parp Wp); lia).
  assert (Mv : nx_may_write B STK sp0 FP ly S lyc Sc own valp)
    by (apply (nx_may_write_of_twr B STK sp0 FP ly S lyc Sc own W memc (spZ regs) valp 1 valp Wv); lia).
  assert (Hctx : nx_ctx B STK sp0 FP ly S lyc Sc own W memc mdc regs tx chp parp valp T).
  { exact (conj HAR (conj Hg (conj Hoc (conj Hop (conj Hov (conj Dcp (conj Dcv (conj Dpv
      (conj Pc (conj Pp (conj Pv (conj Rc (conj Rp (conj Rv (conj H456 (conj Hspr (conj Hac (conj Hsp16
      (conj Hlo' (conj Hhi (conj Mt (conj Mc (conj Mp (conj Mv (conj Hra (conj Hra4 (conj Hgp
      (conj Htp (conj H10 (conj H11 (conj H12 (conj H13 (conj HL (conj Hrok (conj Hobj Hpres))))))))))))))))))))))))))))))))))). }
  destruct (al_blocks _ _ LAWS lyc Sc W memc mdc tx TX_SIZE HAR Hg)
    as (Hg16 & Hg4096 & Hgceil & _ & _ & _).
  change (req_size TX_SIZE) with 460 in Hgceil.
  pose proof (blk_off_imgB B lyc Sc W memc mdc tx TX_SIZE HAR Hg) as Hgimg.
  change (req_size TX_SIZE) with 460 in Hgimg. rewrite IMG_LO_B_val, IMG_TOP_B_val in Hgimg.
  pose proof (pa_obj_img 34 ltac:(lia)) as Hk34. rewrite IMG_LO_B_val, IMG_TOP_B_val in Hk34.
  pose proof (proj2 (proj2 HDIV3) (w_H W) memc HROD) as VK.
  destruct (nx_entry_ro lyc Sc W regs memc mdc tx chp parp valp T HAR H10 H11 H12 H13
    Hsp16 Hspr Hac Hpres Hg HL Hobj Hoc Hop Hov Rc Rp Rv) as [HS SHOK].
  remember (Eimg (Ereg regs (nx_extra tx T))) as E eqn:HEdef.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (nx_extra tx T)) n)
    by (intros n Hn; subst E; apply Eimg_low; exact Hn).
  assert (E1 : ew E 1 = getr regs 1)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
  assert (E2 : ew E 2 = getr regs 2)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E10 : ew E 10 = Z_to_bv 64 tx)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
  assert (E11 : ew E 11 = Z_to_bv 64 chp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
  assert (E12 : ew E 12 = Z_to_bv 64 parp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
  assert (E13 : ew E 13 = Z_to_bv 64 valp)
    by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 13 13%bv eq_refl); exact H13).
  assert (E32 : ew E 32 = Z_to_bv 64 SB_NX)
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (u32 T 432))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E35 : ew E 35 = Z_to_bv 64 (tb T 437))
    by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (EO34 : ew E (A_OBJ 34) = Z_to_bv 64 (VAL (A_OBJ 34)))
    by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (HAE : env_agree 32 (Ereg regs (nx_extra tx T)) E)
    by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; reflexivity]).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  clear HEdef EL.
  assert (U10 : bv_unsigned (ew E 10) = tx) by (rewrite E10; apply unsigned_lit_small; lia64).
  assert (U11 : bv_unsigned (ew E 11) = chp)
    by (rewrite E11; apply unsigned_lit_small; destruct Hoc as (? & ? & _); lia64).
  assert (U12 : bv_unsigned (ew E 12) = parp)
    by (rewrite E12; apply unsigned_lit_small; destruct Hop as (? & ? & _); lia64).
  assert (U13 : bv_unsigned (ew E 13) = valp)
    by (rewrite E13; apply unsigned_lit_small; destruct Hov as (? & ? & _); lia64).
  assert (U32 : bv_unsigned (ew E 32) = SB_NX)
    by (rewrite E32; apply unsigned_lit_small; unfold SB_NX; lia64).
  assert (U35 : bv_unsigned (ew E 35) = tb T 437)
    by (rewrite E35; apply unsigned_lit_small; pose proof (tb_range T 437); lia64).
  pose proof (u32_range T 432) as R33.
  pose proof (tb_range T 437) as R35.
  assert (ACC : ne_stk_same W memc memc (spZ regs)) by (intros x _; reflexivity).
  assert (GRO : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by (apply mem_grows_refl).
  (* The saved registers, from the frame region of a state the prologue has run. *)
  assert (SAVED : forall (ms : machine_state) ss (i : nat),
    st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
    nth_error (ss_mem ss) i = Some (YP09.mkRegion (Some 2%nat) (-96) 0 (-96) 0 ne_saved_chunks) ->
    nx_saved W (ms_mem ms) regs (spZ regs)).
  { intros ms ss i HSs Hnth.
    assert (V : forall (n : nat) (r : bv 5) d, Z.of_nat n = bv_unsigned r ->
      In (YP09.mkChunk (- d) (CVal 8 (SOff n 0))) ne_saved_chunks ->
      ew E n = getr regs r ->
      val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (spZ regs - d) 8 (bv_unsigned (getr regs r))).
    { intros n r d Hn Hin Hew.
      pose proof (st_chunk_val SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) i _ 2 (- d) 8
        (SOff n 0) (spZ regs) (bv_unsigned (getr regs r)) HSs ltac:(destruct ss; exact Hnth)
        eq_refl Hin Usp) as Hv.
      replace (spZ regs - d) with (spZ regs + - d) by lia.
      apply Hv.
      - cbn [sv_denot]. rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - pose proof (bv_unsigned_in_range 64 (getr regs r)) as Hr.
        change (bv_modulus 64) with (2 ^ 64) in Hr. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). exact Hr.
      - lia. }
    assert (G : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
    { intros n r Hn Hr. rewrite (proj1 HAE n Hn). exact (ew_Ereg_nat regs _ n r Hr). }
    unfold nx_saved.
    split; [apply (V 1%nat 1%bv 8); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 8%nat 8%bv 16); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 9%nat 9%bv 24); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 18%nat 18%bv 32); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 19%nat 19%bv 40); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 20%nat 20%bv 48); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 21%nat 21%bv 56); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 22%nat 22%bv 64); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 23%nat 23%bv 72); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 24%nat 24%bv 80); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    split; [apply (V 25%nat 25%bv 88); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]|].
    apply (V 26%nat 26%bv 96); [reflexivity | unfold ne_saved_chunks; cbn; tauto | apply G; [lia | reflexivity]]. }
  (* Every LOOPD exit hands the edge scan its cut, from the machine at LOOPD. *)
  assert (TOLOOP : forall (msL : machine_state) mdL ssL,
    st_ok_pi SEGS VAL E ssL (restrict (w_H W) msL) -> ss_resv ssL = None ->
    ss_pc ssL = LOOPD ->
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W (ms_mem msL) mdL k ->
    ne_stk_same W memc (ms_mem msL) (spZ regs) ->
    mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem msL)) ->
    nx_saved W (ms_mem msL) regs (spZ regs) ->
    nx_at_loopd regs (ms_regs msL) tx chp parp valp 0 ->
    ~ (u32 T 432 = 0 /\ tb T 437 = 0) ->
    SRr SEGS W (mkCfg msL mdL)
      (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T)).
  { intros msL mdL ssL HSL Hrv Hpc HJL ACCL GROL HSV HAT Hact.
    rewrite (st_ok_pi_restrict_mkst _ _ _ _ HSL Hrv), Hpc.
    change (SRr SEGS W (cfg_at SEGS (BASE + LOOPD) (ms_regs msL) (ms_mem msL) mdL)
      (tnext_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs tx chp parp valp T)).
    refine (DLOOP 144%nat STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs (ms_regs msL)
      (ms_mem msL) mdL tx chp parp valp T 0 Hctx _ HSV _ Hact ltac:(lia) eq_refl
      ltac:(intros l Hl; lia) HAT).
    - (* nx_mid, with the three caller bytes untouched *)
      split; [exact HJL|].
      split; [exact (ne_same_of_stk W memc (ms_mem msL) (spZ regs) tx chp parp valp (tx + 432) ACCL)|].
      split.
      { pose proof HJL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJLp & _).
        intros a Ha. apply HJLp. lia. }
      split; [intros a Ha; exact (ne_apresent_grow _ _ _ a GROL Ha)|].
      exact (ne_outq_of_stk W memc (ms_mem msL) (spZ regs) tx chp parp valp ACCL Hoc Hop Hov).
    - (* the table *)
      exact (ne_obj_kept W memc (ms_mem msL) (spZ regs) tx T ACCL ltac:(lia)
        ltac:(unfold NX_FRAME; lia) ltac:(lia) Hobj). }
  unfold cfg_at.
  change (w64 (BASE + AF_reac_headamp_tx_next)) with (Z_to_bv 64 (BASE + AF_reac_headamp_tx_next)).
  (* the prologue, the trap guards T1 and T2, the shadow base, check #1 and the load of active:
     the engine decides T1 (atom 10 >= 4096), T2 (atom 10 is 16-aligned) and check #1 (the table's
     shadow entry) inside the run, which stops at the test of active, 0x85f68 *)
  paj_run_tok RUN HS HJ SHOK BspanN;
    [eapply ne_awr; [ne_skel_tac | exact Usp | exact Hlo' | exact Hhi] |].
  ne_acc Usp.
  (* The shadow base is in s5: the two image words it was read through have served, and the
     multiplier's word at object 34 joins the state. *)
  lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
    let rs := eval vm_compute in (ss_mem ssx) in
    lazymatch rs with
    | [?r0; _; _; ?r3] =>
      pose proof (st_ok_pi_submem E ssx _ [r0; r3] HSx ltac:(cbn [ss_mem]; submem_tac) eq_refl) as HS1;
      assert (RK : region_ok SEGS E (ms_mem (restrict (w_H W) msx)) ROD34);
      [| assert (DK : all_disjoint E ROD34 [r0; r3]);
         [| pose proof (st_ok_pi_add_region E _ _ ROD34 HS1 eq_refl RK DK) as HS2;
            cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2;
            clear HSx HS1 RK DK; rename HS2 into HS ] ]
    end
  end.
  { unfold region_ok, ROD34, obj8_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite EO34, unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 34)); lia64).
    split; [lia|]. split; [lia64|]. split; [intros o Ho; lia|].
    constructor; [|constructor].
    apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 34)) 0 8 (SLit 12297829382473034411) 12297829382473034411);
      [reflexivity | cbn; lia64 | cbn; lia |].
    rewrite Z.add_0_r.
    lazymatch goal with |- val_mem _ (ms_mem (restrict _ ?msx)) _ _ _ =>
      exact (ne_val8_kept W memc (ms_mem msx) (spZ regs) (VAL (A_OBJ 34)) 12297829382473034411 ACC
        ltac:(lia) ltac:(unfold NX_FRAME; lia) ltac:(lia) VK) end. }
  { apply all_disjoint_of_extents. unfold ROD34, obj8_region, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite Usp, EO34, E10, !unsigned_lit_small by (pose proof (pa_val_range (A_OBJ 34)); lia64).
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd].
    unfold NX_FRAME. repeat split; lia. }
  (* 0x85f68 `bnez a0`: a0 is the sign-extended `lw` of active *)
  psrr_branch_tok RUN BR HS SHOK BspanN.
  - (* active <> 0: on to the edge scan *)
    rewrite branch_ne_U, U_SExt, (U_atom E 33 (u32 T 432) E33), U_SLit in Hc by lia64.
    cbv beta iota in Hc. rewrite ne_sext32_0 in Hc by lia.
    apply (proj1 (negb_true_iff _)), Z.eqb_neq in Hc. rename Hc into Hact.
    paj_run_to_tok RUNTO HS HJ SHOK BspanN LOOPD;
      [eapply ne_awr; [ne_skel_tac | exact Usp | exact Hlo' | exact Hhi] |].
    ne_acc Usp.
    lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
      assert (HAT : nx_at_loopd regs (ms_regs msx) tx chp parp valp 0);
      [ unfold nx_at_loopd, nx_keep_gp;
        split; [exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W) msx) regs (nx_extra tx T)
                  [3; 4; 27]%bv HSx HAE ltac:(vm_compute; reflexivity))|];
        repeat match goal with |- _ /\ _ => split end;
        ne_regval HSx; ne_U_close Usp U10 U11 U12 U13 U32
      | exact (TOLOOP msx _ ssx HSx eq_refl eq_refl HJ ACC GRO (SAVED msx ssx 1%nat HSx eq_refl) HAT
          ltac:(intros [X _]; exact (Hact X))) ]
    end.
  - (* active = 0: the replay width decides *)
    rewrite branch_ne_U, U_SExt, (U_atom E 33 (u32 T 432) E33), U_SLit in Hc by lia64.
    cbv beta iota in Hc. rewrite ne_sext32_0 in Hc by lia.
    apply (proj1 (negb_false_iff _)), Z.eqb_eq in Hc. rename Hc into Hact0.
    paj_run_tok RUN HS HJ SHOK BspanN;
      [eapply ne_awr; [ne_skel_tac | exact Usp | exact Hlo' | exact Hhi] |].
    ne_acc Usp.
    (* 0x85f84 `beqz a0`: a0 is the `lbu` of replay_width *)
    psrr_branch_tok RUN BR HS SHOK BspanN.
    + (* replay_width = 0: idle, return 0 through the epilogue 0x862cc *)
      rewrite branch_eq_U, (U_atom E 35 (tb T 437) E35), U_SLit in Hc by lia64.
      change (zcanon 0) with 0 in Hc.
      apply Z.eqb_eq in Hc. rename Hc into Hw0.
      paj_run_tok RUN HS HJ SHOK BspanN;
        [eapply ne_awr; [ne_skel_tac | exact Usp | exact Hlo' | exact Hhi] |].
      ne_acc Usp.
      lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
        ne_reg HSx (1%bv : bv 5) R1; ne_reg HSx (10%bv : bv 5) R10;
        eapply (RET W _ _ _ _ _ HSx eq_refl ltac:(vm_compute; reflexivity));
        let matR := fresh "matR" in intros matR; cbn [ms_regs ms_mem];
        rewrite R1; cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned, Hra;
        eapply (nx_finish B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
          regs (ms_regs msx) (ms_mem msx) _ tx chp parp valp (tx + 432) T T 0 0 0 0);
        [ unfold TX_SIZE, ATx.TX_SIZE; lia | exact HAR | exact Hg | exact Hoc | exact Hop | exact Hov
        | exact Hspr | exact Hac
        | exact (nx_model_silent T tx Hact0 Hw0)
        | apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ
        | eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs (nx_extra tx T) HSx);
          [exact HAE | vm_compute; reflexivity]
        | exact (ne_same_of_stk W memc (ms_mem msx) (spZ regs) tx chp parp valp (tx + 432) ACC)
        | pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HJxp & _);
          intros a Ha; apply HJxp; lia
        | intros a Ha; exact (ne_apresent_grow _ _ _ a GRO Ha)
        | rewrite R10; unfold w64; apply ne_denot; apply (ne_U_off E 35 0 (tb T 437) 0 U35); lia
        | exact (ne_obj_kept W memc (ms_mem msx) (spZ regs) tx T ACC ltac:(lia)
            ltac:(unfold NX_FRAME; lia) ltac:(lia) Hobj)
        | exact Hrok
        | intros X; discriminate X
        | intros _; exact (ne_outq_of_stk W memc (ms_mem msx) (spZ regs) tx chp parp valp ACC Hoc Hop Hov) ]
      end.
    + (* replay_width <> 0: on to the edge scan *)
      rewrite branch_eq_U, (U_atom E 35 (tb T 437) E35), U_SLit in Hc by lia64.
      change (zcanon 0) with 0 in Hc.
      apply Z.eqb_neq in Hc. rename Hc into Hw.
      paj_run_to_tok RUNTO HS HJ SHOK BspanN LOOPD;
        [eapply ne_awr; [ne_skel_tac | exact Usp | exact Hlo' | exact Hhi] |].
      ne_acc Usp.
      lazymatch goal with HSx : st_ok_pi _ _ _ ?ssx (restrict _ ?msx) |- _ =>
        assert (HAT : nx_at_loopd regs (ms_regs msx) tx chp parp valp 0);
        [ unfold nx_at_loopd, nx_keep_gp;
          split; [exact (regs_kept_of_st_ok_pi E ssx (restrict (w_H W) msx) regs (nx_extra tx T)
                    [3; 4; 27]%bv HSx HAE ltac:(vm_compute; reflexivity))|];
          repeat match goal with |- _ /\ _ => split end;
          ne_regval HSx; ne_U_close Usp U10 U11 U12 U13 U32
        | exact (TOLOOP msx _ ssx HSx eq_refl eq_refl HJ ACC GRO (SAVED msx ssx 1%nat HSx eq_refl) HAT
            ltac:(intros [_ X]; exact (Hw X))) ]
      end.
Qed.

End h.
End f.
End d.
