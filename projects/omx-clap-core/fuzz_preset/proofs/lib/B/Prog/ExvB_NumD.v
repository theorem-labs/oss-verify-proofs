(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Rebound on the old-pin kit of record 4f18c75d4900 (rebind base a9d3e245c2b): memnorm enters only as EXN_keepM's
   step keep across the one store of the piece (the fsd at exv_pc 0x8dc), YAkMemnorm.memnorm_write under the step's
   own store_ok; the generic helpers come from ExvB_Num_eng (ex_ws_x's, same names). *)
(* Theorem Labs, 2026-10: fuzz_preset, image B (asan-ubsan, rebuilt pin f8f98a95bc52, unstripped twin 3b5e1a099b53),
   ex_value's NUMBER SEGMENT, sub-piece D of lib/B/Prog/ExvB_NumCut.v: CR (exv_pc 0x8d4, strtod's return site) ->
   CT (exv_pc 0xa70) | CC (exv_pc 0x910). Proves no function (kind: segment lemma): `exn_D : EXN_D B ARx SK E pos`.
   THE CODE (neutral listing, the internal file ex_value.fuzz_preset.asan-ubsan.s, a Theorem Labs lane's listing of the B' pin, lines 567-583
   and the slow path 771-773; offsets from ex_value's entry):
     0x8d4  ld a0,0(s7)        a0 := *(&end) = scr + cn                    (s7 = f + 32)
     0x8d8  ld a1,136(s1)      a1 := f + 64 (&num)                         (the s1 spill 136)
     0x8dc  fsd fa0,0(a1)      num := bits                                 (YK0o.v fp_step_fsd; awr_byte's in_frames arm)
     0x8e0  ld a3,144(s1)      a3 := shadow_addr q                         (the s1 spill 144; EXN_CC_pre's a3)
     0x8e4  beqz a0 -> 0xb50   UBSan `unimp`: NOT taken, scr + cn > 0 from 4096 <= scr
     0x8e8 .. 0x8f4            the 1-byte ASan check of end (srli / add s9 / lb / bnez); the slow arm
     0xc04  andi a2,a0,7  /  0xc08 blt a2,a1 -> 0x8f8: TAKEN from wdest_ok's shadow of the scratch, so the
                               `jal errpath_load1` at 0xc0c is unreachable
     0x8f8  lbu a0,0(a0)       the byte at end, (txt ++ [0])[cn]; 0x8fc bnez -> 0xa70 (CT, r = -1): strtod stopped early
     0x900  fclass.d a0,fa0    (exnD_step_fclass_d below: the shared fp_step_fclass, restated)
     0x904  andi a0,a0,897     the infinities and NaNs; 0x908 snez; 0x90c bnez -> 0xa70 (CT, r = -1); else CC (0x910).
   Every step is a hand step (YA0n.v SRr_step with YK11.v's / YK0o.v's single-step lemmas) whose instruction word is
   read from B's listing table (YC1fP.v pa_fetch_pw at PL_prog_B / PI_prog_B, certified against B_prog_tbl) and
   decoded by computation; no address is carried by a relocation. 17 instruction words, each checked against the
   neutral listing (0 mismatches).
   Section hypotheses: EXV_HYP, the cuts CT (EXN_T) and CC (EXN_Ec), lane M's EXN_keepM and the spill law
   EXN_keep_spill, each exactly as ExvB_NumCut.v states it.
   Numerals: 0x8d4 0x8d8 0x8dc 0x8e0 0x8e4 0x8e8 0x8ec 0x8f0 0x8f4 0x8f8 0x8fc 0x900 0x904 0x908 0x90c 0x910 0xa70
   0xb50 0xc04 0xc08 0xc0c (DERIVED: B address minus B's ex_value entry, both from the neutral listing); 620 784 372
   356 7408 (DERIVED: the branch immediates, target minus pc, 7408 = 2 ^ 13 - 784); 32 64 72 136 144 152 160 (LENGTH:
   the frame's `end` / `num` slots and the s1 spills of B's code); 128 (LENGTH: the class-1 frame, fs_frame_bytes 1);
   304 183 319 (LENGTH: pi_frame F_ex_value at prh_img_B, the spill offset below the entry sp, the frame's realignment
   bound); 4 8 (LENGTH: an instruction, a word / the shadow granule); 3 7 897 (WORD: the srli / andi immediates);
   0 2 3 4 8 9 10 11 12 13 18 19 20 21 22 23 24 25 26 27 (WORD: register numbers); 45 48 (WORD: '-' and '0');
   4096 2 ^ 47 2 ^ 64 1024 256 (LENGTH: address and value ranges; 1024 = 2 ^ 10, one past fclass's top bit);
   52 11 2047 10 (LENGTH / WORD: binary64's mantissa width, exponent width, its all-ones value, Z.log2 2047).
   No ADDRESS: every program counter is `exv_pc <offset>`. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04
YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YP0a YPsym YC4aP FCiface YGcfRoomKeep YC1fP YK0u YN01 YK1b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbn YK00 YA03 YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require PRH_Reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require ExvB_Num_eng.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import ExvB_Stmt ExvB_NumPure
  ExvB_NumCut ExvB_Open_kt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
(* lia over / and mod (the shadow map, the 32-aligned s1) *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Existing Instance prh_img_B.

(* ======== the fclass.d single step ========
   The shared `fp_step_fclass` (h-hpreset-7's walk kit, there as lib/Reusable/YFclsStep.v fp_step_fclass_d),
   RESTATED here because the kit file is not on this branch: the same statement and proof, in YK0o.v's fp_pipeline
   style (the sibling of YK0o.v's fp_step_fsd). LPS Sem.v: Fclass writes an INTEGER register; Fpu.v: fp_class,
   at fmt_double (the decode field FMT_D is convertible to it). *)
Lemma exnD_step_fclass_d : forall (fx : YK11.FPState) segs regs pc mem rom w rd rs1,
  fetch_word segs pc = Some w -> is_ecall w = false ->
  decode_any w = Some (Fclass FMT_D rd rs1, 4%Z) ->
  RiscvSemantics.step segs (@YK11.mkst fx regs pc mem rom) =
  MachineOk (@YK11.mkst fx (if bv_eqb rd 0%bv then regs
     else YK11.regupd regs rd (Z_to_bv 64 (fp_class fmt_double (bv_unsigned (reg_get (@YK11.fp_regs fx) rs1)))))
    (YK11.v_addi pc 4) mem rom).
Proof.
  intros fx segs regs pc mem rom w rd rs1 Hf He Hd.
  fp_pipeline Hf He Hd.
  destruct (is_x0 rd); cbv beta iota; rewrite b_npc4; destruct fx; reflexivity.
Qed.

(* ======== pure: the number arm's reading at the scan's stop ======== *)

Lemma exnD_skipn_cons : forall (x : list Z) (a : nat), (a < length x)%nat -> skipn a x = nth a x 0 :: skipn (S a) x.
Proof.
  induction x as [|b x IH]; intros a Ha; cbn [length] in Ha; [lia|].
  destruct a as [|a]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma exnD_skipn_skipn : forall (x : list Z) (a b : nat), skipn a (skipn b x) = skipn (b + a) x.
Proof.
  intros x a b. revert x. induction b as [|b IH]; intros x; [reflexivity|].
  destruct x as [|h x]; cbn [skipn Nat.add].
  - destruct a; reflexivity.
  - apply IH.
Qed.

Lemma exnD_skipn_nil : forall (x : list Z) (a : nat), (length x <= a)%nat -> skipn a x = [].
Proof.
  induction x as [|b x IH]; intros a Ha; [destruct a; reflexivity|].
  cbn [length] in Ha. destruct a as [|a]; [lia|]. cbn [skipn]. apply IH. lia.
Qed.

Lemma exnD_nth_skipn : forall (x : list Z) (a n : nat), nth n (skipn a x) 0 = nth (a + n) x 0.
Proof.
  intros x a n. revert x. induction a as [|a IH]; intros x; [reflexivity|].
  destruct x as [|h x]; cbn [skipn Nat.add nth].
  - destruct n; reflexivity.
  - apply IH.
Qed.

Lemma exnD_firstn_add : forall (l : list Z) (n m : nat), firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  intros l n m. revert l. induction n as [|n IH]; intros l; [reflexivity|].
  destruct l as [|h l]; cbn [firstn skipn Nat.add app].
  - destruct m; reflexivity.
  - f_equal. apply IH.
Qed.

Lemma exnD_sub_cons : forall (x : list Z) (a z : nat), (a < z)%nat -> (a < length x)%nat ->
  exn_sub x a z = nth a x 0 :: exn_sub x (S a) z.
Proof.
  intros x a z Haz Hax. unfold exn_sub. rewrite (exnD_skipn_cons x a Hax).
  replace (z - a)%nat with (S (z - S a)) by lia. reflexivity.
Qed.

Lemma exnD_sub_split : forall (x : list Z) (a b z : nat), (a <= b <= z)%nat ->
  exn_sub x a z = exn_sub x a b ++ exn_sub x b z.
Proof.
  intros x a b z H. unfold exn_sub.
  replace (z - a)%nat with ((b - a) + (z - b))%nat by lia.
  rewrite exnD_firstn_add, exnD_skipn_skipn.
  replace (a + (b - a))%nat with b by lia. reflexivity.
Qed.

Lemma exnD_sub_length : forall (x : list Z) (a z : nat), (z <= length x)%nat ->
  length (exn_sub x a z) = (z - a)%nat.
Proof. intros x a z Hz. unfold exn_sub. rewrite length_firstn, length_skipn. lia. Qed.

(* the scan's stop: span numch splits the text exactly at the first non-number byte (ExvB_NumPure's span steps) *)
Lemma exnD_span : forall (y : list Z) (n : nat),
  (n <= length y)%nat -> Forall (fun z => PjGrammar.numch z = true) (firstn n y) ->
  (n = length y \/ PjGrammar.numch (nth n y 0) = false) ->
  PjGrammar.span PjGrammar.numch y = (firstn n y, skipn n y).
Proof.
  induction y as [|b y IH]; intros n Hn Hall Hstop.
  - destruct n; [reflexivity | cbn [length] in Hn; lia].
  - destruct n as [|n].
    + destruct Hstop as [Hs|Hs]; [cbn [length] in Hs; lia|].
      cbn [nth] in Hs. exact (exn_span_cons_false b y Hs).
    + cbn [firstn] in Hall.
      rewrite (exn_span_cons_true b y (Forall_inv Hall)).
      rewrite (IH n); [reflexivity | cbn [length] in Hn; lia | exact (Forall_inv_tail Hall) |].
      destruct Hstop as [Hs|Hs]; [left; cbn [length] in Hs; lia | right; exact Hs].
Qed.

(* strtod's reading as the grammar's reader sees it (ReaderRes.jr_strtod over lib/Prog/strtod_c.strtod_model, the
   same FloatScan.scan_strtod as image B's strtod_c.strtod_model) *)
Lemma exnD_jr : forall txt bits cn, exv_strtod_model txt = Some (bits, cn) -> ReaderRes.jr_strtod txt = (cn, bits).
Proof.
  intros txt bits cn H. unfold ReaderRes.jr_strtod.
  change (OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog.strtod_c.strtod_model txt)
    with (exv_strtod_model txt).
  rewrite H. reflexivity.
Qed.

(* the reading of x from i1 when the scan stopped at j and strtod read (bits, cn) from x[i1, j): exn_N_unfold, the
   lead-digit facts and the span of the cut, and whole = (cn = |txt|) && finite bits *)
Lemma exnD_N : forall (x : list Z) (i1 j : nat) (c bits cn : Z),
  nth i1 x 0 = c ->
  (i1 + exn_sg c < length x)%nat ->
  PjGrammar.digit (nth (i1 + exn_sg c) x 0) = true ->
  ~ (nth (i1 + exn_sg c) x 0 = 48 /\ (S (i1 + exn_sg c) < length x)%nat /\
     PjGrammar.digit (nth (S (i1 + exn_sg c)) x 0) = true) ->
  Forall (fun z => PjGrammar.numch z = true) (exn_sub x (i1 + exn_sg c) j) ->
  (i1 + exn_sg c < j <= length x)%nat ->
  (j = length x \/ PjGrammar.numch (nth j x 0) = false) ->
  exv_strtod_model (exn_sub x i1 j) = Some (bits, cn) ->
  exn_N (skipn i1 x) =
    if (cn =? Z.of_nat (length (exn_sub x i1 j))) && PjGrammar.finite bits
    then Some (PjTree.JNum (exn_sub x i1 j) bits, skipn j x) else None.
Proof.
  intros x i1 j c bits cn. remember (i1 + exn_sg c)%nat as j0 eqn:Hj0.
  intros Hc Hl0 Hd Hnz Hall Hj Hstop Hsm.
  assert (Hi1 : (i1 < length x)%nat) by lia.
  assert (H1 : skipn i1 x = c :: skipn (S i1) x) by (rewrite <- Hc; apply exnD_skipn_cons; exact Hi1).
  assert (H2 : skipn (exn_sg c) (c :: skipn (S i1) x) = nth j0 x 0 :: skipn (S j0) x).
  { rewrite <- H1, exnD_skipn_skipn, <- Hj0. apply exnD_skipn_cons. lia. }
  assert (Hnz' : ((nth j0 x 0 =? 48) && match skipn (S j0) x with c1 :: _ => PjGrammar.digit c1 | [] => false end)
                 = false).
  { destruct (Z.eqb_spec (nth j0 x 0) 48) as [E|NE]; [|reflexivity].
    cbn [andb].
    destruct (Nat.lt_ge_cases (S j0) (length x)) as [Hlt|Hge].
    - rewrite (exnD_skipn_cons x (S j0) Hlt). cbv beta iota.
      destruct (PjGrammar.digit (nth (S j0) x 0)) eqn:Ed; [|reflexivity].
      exfalso. apply Hnz. split; [exact E|]. split; [exact Hlt | reflexivity].
    - rewrite (exnD_skipn_nil x (S j0) Hge). reflexivity. }
  assert (Hrest : Forall (fun z => PjGrammar.numch z = true) (exn_sub x (S j0) j)).
  { rewrite (exnD_sub_cons x j0 j) in Hall by lia. exact (Forall_inv_tail Hall). }
  assert (Hspan : PjGrammar.span PjGrammar.numch (skipn (S j0) x) = (exn_sub x (S j0) j, skipn j x)).
  { rewrite (exnD_span (skipn (S j0) x) (j - S j0)).
    - unfold exn_sub. rewrite exnD_skipn_skipn. replace (S j0 + (j - S j0))%nat with j by lia. reflexivity.
    - rewrite length_skipn. lia.
    - exact Hrest.
    - destruct Hstop as [Hs|Hs]; [left; rewrite length_skipn; lia|].
      right. rewrite exnD_nth_skipn. replace (S j0 + (j - S j0))%nat with j by lia. exact Hs. }
  assert (Htxt : firstn (exn_sg c) (c :: skipn (S i1) x) ++ nth j0 x 0 :: exn_sub x (S j0) j = exn_sub x i1 j).
  { rewrite <- H1. rewrite (exnD_sub_split x i1 j0 j) by lia. rewrite (exnD_sub_cons x j0 j) by lia.
    f_equal. unfold exn_sub. f_equal. lia. }
  rewrite exn_N_unfold. cbv zeta. rewrite H1. cbv beta iota.
  change (if c =? 45 then 1%nat else 0%nat) with (exn_sg c).
  rewrite H2. cbv beta iota. rewrite Hd. cbv beta iota delta [negb].
  rewrite Hnz'. cbv beta iota zeta. rewrite Hspan. cbn [fst snd]. rewrite Htxt.
  unfold PjGrammar.whole. rewrite (exnD_jr _ _ _ Hsm). cbn [fst snd]. reflexivity.
Qed.

(* the text is all number characters (the sign byte is '-' when exn_sg c = 1) *)
Lemma exnD_txt_numch : forall (x : list Z) (i1 j : nat) (c : Z),
  nth i1 x 0 = c -> (i1 + exn_sg c <= j <= length x)%nat ->
  Forall (fun z => PjGrammar.numch z = true) (exn_sub x (i1 + exn_sg c) j) ->
  Forall (fun z => PjGrammar.numch z = true) (exn_sub x i1 j).
Proof.
  intros x i1 j c Hc Hj Hall. unfold exn_sg in Hj, Hall. revert Hj Hall.
  destruct (Z.eqb_spec c 45) as [E|NE]; intros Hj Hall.
  - rewrite (exnD_sub_cons x i1 j) by lia. constructor.
    + rewrite Hc, E. reflexivity.
    + replace (S i1) with (i1 + 1)%nat by lia. exact Hall.
  - rewrite Nat.add_0_r in Hall. exact Hall.
Qed.

(* the byte at end = scr + cn of txt ++ [0] is zero iff strtod consumed the whole text *)
Lemma exnD_end_byte : forall (txt : list Z) (cn : Z),
  Forall (fun z => PjGrammar.numch z = true) txt -> 0 <= cn <= Z.of_nat (length txt) ->
  (nth (Z.to_nat cn) (txt ++ [0]) 0 =? 0) = (cn =? Z.of_nat (length txt)).
Proof.
  intros txt cn Hall Hcn.
  destruct (Z.eqb_spec cn (Z.of_nat (length txt))) as [E|NE].
  - rewrite E, Nat2Z.id, app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
  - rewrite app_nth1 by lia.
    assert (Hin : In (nth (Z.to_nat cn) txt 0) txt) by (apply nth_In; lia).
    rewrite Forall_forall in Hall. specialize (Hall _ Hin). cbv beta in Hall.
    destruct (Z.eqb_spec (nth (Z.to_nat cn) txt 0) 0) as [E0|NE0]; [|reflexivity].
    rewrite E0 in Hall. vm_compute in Hall. discriminate Hall.
Qed.

(* the fclass.d mask 897 = 0x381 (bit 0 -inf, 7 +inf, 8 sNaN, 9 qNaN) is zero iff the exponent field of the bits is
   not all ones, i.e. PjGrammar.finite; the register holds bits mod 2 ^ 64 *)
Lemma exnD_exp_mod : forall bits : Z,
  Z.land (Z.shiftr (bits mod 2 ^ 64) 52) 2047 = Z.land (Z.shiftr bits 52) 2047.
Proof.
  intros bits. apply Z.bits_inj'. intros n Hn.
  rewrite !Z.land_spec, !Z.shiftr_spec by lia.
  destruct (Z.lt_ge_cases n 11) as [Hlt|Hge].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - assert (H2047 : Z.testbit 2047 n = false).
    { apply Z.bits_above_log2; [lia|]. change (Z.log2 2047) with 10. lia. }
    rewrite H2047, !andb_false_r. reflexivity.
Qed.

Lemma exnD_fclass : forall bits : Z,
  (Z.land (fp_class fmt_double (bits mod 2 ^ 64)) 897 =? 0) = PjGrammar.finite bits.
Proof.
  intros bits. unfold fp_class, PjGrammar.finite. cbv zeta.
  unfold fp_exp_field.
  change (fp_mw fmt_double) with 52. change (Z.ones (fp_ew fmt_double)) with 2047.
  rewrite exnD_exp_mod.
  destruct (Z.land (Z.shiftr bits 52) 2047 =? 2047);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma exnD_fclass_range : forall a : Z, 0 <= fp_class fmt_double a < 1024.
Proof.
  intros a. unfold fp_class. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  vm_compute; split; congruence.
Qed.

(* ======== memory: one store of bs at A through the restricted view ======== *)
Section m.
Variable segs : list Segment.

Lemma exnD_store_ok : forall (m : word -> option byte) (n : nat) (a : Z),
  (forall i, 0 <= i < Z.of_nat n -> m (Z_to_bv 64 (a + i)) <> None) -> 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  store_ok segs m (Z_to_bv 64 a) n = true.
Proof.
  intros m n. induction n as [|n IH]; intros a Hp Ha Hn; [reflexivity|].
  cbn [store_ok]. unfold wview.
  destruct (m (Z_to_bv 64 a)) eqn:E.
  - rewrite Z_to_bv64_add1. apply IH; [| lia | lia].
    intros i Hi. replace (a + 1 + i) with (a + (1 + i)) by lia. apply Hp. lia.
  - exfalso. apply (Hp 0); [lia|]. rewrite Z.add_0_r. exact E.
Qed.

Lemma exnD_wb_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (x : word),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  (bv_unsigned x < A \/ A + Z.of_nat (length bs) <= bv_unsigned x) ->
  mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) x = mrestrict H mem x.
Proof.
  intros H mem A bs x HA HAn Hx. unfold munrestrict, mrestrict.
  destruct (H x) eqn:Hh; [reflexivity|].
  rewrite wbytes_outside; [cbv beta; rewrite Hh; reflexivity | rewrite YK00.u64_lit by lia; lia |].
  rewrite YK00.u64_lit by lia. exact Hx.
Qed.

Lemma exnD_wb_hid : forall (H : word -> bool) (mem m' : word -> option byte) (x : word),
  H x = true -> munrestrict H mem m' x = mem x.
Proof. intros H mem m' x Hh. unfold munrestrict. rewrite Hh. reflexivity. Qed.

Lemma exnD_wb_grow : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  mem_grows (mrestrict H mem) (mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs))).
Proof.
  intros H mem A bs HA HAn x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Hl|Hl]; [rewrite exnD_wb_out by lia; exact Hx|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Hu|Hu];
    [|rewrite exnD_wb_out by lia; exact Hx].
  unfold mrestrict in *. unfold munrestrict. destruct (H x) eqn:Hh; [exact Hx|].
  rewrite wbytes_inside; [discriminate | rewrite YK00.u64_lit by lia; lia | rewrite YK00.u64_lit by lia; lia].
Qed.

Lemma exnD_wb_in : forall (H : word -> bool) (mem : word -> option byte) (A v : Z) (k : nat),
  0 <= A -> A + 8 <= 2 ^ 64 -> (k < 8)%nat -> H (Z_to_bv 64 (A + Z.of_nat k)) = false ->
  mbyte segs (mrestrict H (munrestrict H mem
      (wbytes (mrestrict H mem) (Z_to_bv 64 A) (word_to_le_bytes 8 (Z_to_bv 64 v))))) (A + Z.of_nat k)
  = Some (Z_to_bv 8 (le_byte v 8 k)).
Proof.
  intros H mem A v k HA HA8 Hk Hh.
  assert (Hlen : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 v))) = 8)
    by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
  assert (E : nth_error (word_to_le_bytes 8 (Z_to_bv 64 v)) k = Some (Z_to_bv 8 (le_byte v 8 k))).
  { unfold word_to_le_bytes. rewrite nth_error_Z_to_le_bytes by lia. f_equal.
    rewrite le_byte_bv by lia. rewrite Z_to_bv_unsigned. reflexivity. }
  unfold mbyte, munrestrict, mrestrict. rewrite Hh.
  rewrite wbytes_inside; [| rewrite YK00.u64_lit by lia; lia | rewrite !YK00.u64_lit by lia; lia].
  rewrite !YK00.u64_lit by lia. replace (A + Z.of_nat k - A) with (Z.of_nat k) by lia. rewrite Nat2Z.id.
  f_equal. apply nth_error_nth. exact E.
Qed.

Lemma exnD_aview_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (z : Z),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  (z < A \/ A + Z.of_nat (length bs) <= z) ->
  aview segs H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) z = aview segs H mem z.
Proof.
  intros H mem A bs z HA HAn Hz Hout. apply aview_eq_of. apply exnD_wb_out; [lia | lia |].
  rewrite YK00.u64_lit by lia. exact Hout.
Qed.

Lemma exnD_byte : forall e, 0 <= e < 256 -> bv_unsigned (Z_to_bv 8 (le_byte e 1 0)) = e.
Proof.
  intros e He. rewrite Z_to_bv_unsigned. unfold le_byte.
  replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
  rewrite Z.shiftr_0_r, !(Z.mod_small e 256) by lia.
  replace (bv_wrap 8 e) with (e mod 256) by reflexivity. apply Z.mod_small. lia.
Qed.

(* a visible byte is a one-byte read of the restricted memory *)
Lemma exnD_aview_rdn : forall (H : word -> bool) (mem : word -> option byte) (a s : Z),
  aview segs H mem a = Some s -> exists sb, rdn segs (mrestrict H mem) (Z_to_bv 64 a) 1 = Some [sb] /\ bv_unsigned sb = s.
Proof.
  intros H mem a s Hv. unfold aview in Hv. cbv beta in Hv.
  lazymatch type of Hv with option_map _ ?t = _ => destruct t as [sb|] eqn:Eb end;
    cbn [option_map] in Hv; [|discriminate Hv].
  injection Hv as <-. exists sb. split; [|reflexivity].
  apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
  cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Eb.
Qed.
End m.

(* ======== registers ======== *)
(* the registers the stretch leaves alone: all but a0, a1, a2, a3 *)
Definition exnD_frame (R regs : bvmap 5 word) : Prop :=
  forall r : Prelude.reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> r <> 13%bv -> YK11.getr R r = YK11.getr regs r.

Lemma exnD_frame_refl : forall regs, exnD_frame regs regs.
Proof. intros regs r _ _ _ _. reflexivity. Qed.

Lemma exnD_frame_upd : forall R regs (d : Prelude.reg) v, (d = 10%bv \/ d = 11%bv \/ d = 12%bv \/ d = 13%bv) ->
  exnD_frame R regs -> exnD_frame (YK11.regupd R d v) regs.
Proof.
  intros R regs d v Hd HF r H10 H11 H12 H13. rewrite getr_other; [apply HF; assumption|].
  destruct Hd as [ Hd | [ Hd | [ Hd | Hd ] ] ]; rewrite Hd; assumption.
Qed.

Ltac exnD_rne := let H := fresh "Hr" in intro H; apply (f_equal bv_unsigned) in H; vm_compute in H; discriminate H.

Lemma exnD_kept : forall R regs, exnD_frame R regs -> EXN_regs_kept regs R.
Proof.
  intros R regs HF. unfold EXN_regs_kept.
  repeat split; apply HF; exnD_rne.
Qed.

(* bv_signed of a literal immediate, computed *)
Ltac exnD_bvs := repeat match goal with |- context [bv_signed ?i] =>
  let v := eval vm_compute in (bv_signed i) in
  lazymatch v with
  | Z0 => change (bv_signed i) with 0
  | Zpos ?p => change (bv_signed i) with (Zpos p)
  | Zneg ?p => change (bv_signed i) with (Zneg p)
  end end.

(* ======== the program counter and the listing ======== *)
Section fl. Context {rc : YM05.RunCeil}.
Lemma exnD_fetch_lem : forall off w,
  plookup B_prog_tpi (B_prog_sigma AS_ex_value - B_prog_base + off) = Some (PW w) ->
  fetch_word rsegs (w64 (exv_pc off)) = Some (Z_to_bv 32 w).
Proof.
  intros off w H. pose proof (pa_fetch_pw (PL := PL_prog_B) (PI := PI_prog_B) _ _ H) as F.
  unfold w64, exv_pc.
  replace (B_prog_sigma AS_ex_value + off)
    with (B_prog_val A_TEXT + (B_prog_sigma AS_ex_value - B_prog_base + off)).
  - exact F.
  - change (B_prog_val A_TEXT) with B_prog_base. lia.
Qed.

Lemma exnD_next : forall off k, YK11.v_addi (w64 (exv_pc off)) k = w64 (exv_pc (off + k)).
Proof. intros off k. unfold w64. rewrite YCbn.v_addi_lit. unfold exv_pc. f_equal. lia. Qed.

Lemma exnD_btgt : forall off k, YK11.btgt (w64 (exv_pc off)) k = w64 (exv_pc (off + k)).
Proof. intros off k. unfold YK11.btgt. apply exnD_next. Qed.
End fl.

(* the listing word at the offset (from B's table, by computation) and its decoding at the registers and immediates
   the proof names: the decoder builds its bv fields with Z_to_bv's opaque well-formedness proof, so the two forms
   are equal only by bv_eq *)
Ltac exnD_fetch off instr :=
  let k := eval vm_compute in (B_prog_sigma AS_ex_value - B_prog_base + off) in
  let e := eval vm_compute in (plookup B_prog_tpi k) in
  lazymatch e with
  | Some (PW ?w) =>
    pose proof (exnD_fetch_lem off w ltac:(vm_compute; reflexivity)) as Hf;
    assert (Hd : decode_any (Z_to_bv 32 w) = Some (instr, 4%Z))
      by (vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]);
    assert (He : is_ecall (Z_to_bv 32 w) = false) by (vm_compute; reflexivity)
  end.

Section st. Context {rc : YM05.RunCeil}.
(* one hand step at a cut-free pc: registers and pc change, memory does not *)
Lemma exnD_step : forall (W : world rsegs) (fxc : YK11.FPState) regs off mem md0 md Q regs' off',
  same_but_materialized md0 md ->
  RiscvSemantics.step rsegs (@YK11.mkst fxc regs (w64 (exv_pc off)) (mrestrict (w_H W) mem) (YK11.seg_rom rsegs)) =
    MachineOk (@YK11.mkst fxc regs' (w64 (exv_pc off')) (mrestrict (w_H W) mem) (YK11.seg_rom rsegs)) ->
  (forall md', same_but_materialized md0 md' ->
     SRr rsegs W (cfg_at (fx := fxc) rsegs (exv_pc off') regs' mem md') Q) ->
  SRr rsegs W (cfg_at (fx := fxc) rsegs (exv_pc off) regs mem md) Q.
Proof.
  intros W fxc regs off mem md0 md Q regs' off' Hs0 Hst HK. unfold cfg_at.
  eapply (SRr_step rsegs B_prog_wx W); [reflexivity | rewrite restrict_mkst_fx; exact Hst |].
  intros md' Hs. cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  apply HK. eapply same_but_materialized_trans; eassumption.
Qed.

(* one hand step that also writes memory: the new memory is the restricted write put back under the hidden part *)
Lemma exnD_step_m : forall (W : world rsegs) (fxc : YK11.FPState) regs off mem md0 md Q regs' off' m',
  same_but_materialized md0 md ->
  RiscvSemantics.step rsegs (@YK11.mkst fxc regs (w64 (exv_pc off)) (mrestrict (w_H W) mem) (YK11.seg_rom rsegs)) =
    MachineOk (@YK11.mkst fxc regs' (w64 (exv_pc off')) m' (YK11.seg_rom rsegs)) ->
  (forall md', same_but_materialized md0 md' ->
     SRr rsegs W (cfg_at (fx := fxc) rsegs (exv_pc off') regs' (munrestrict (w_H W) mem m') md') Q) ->
  SRr rsegs W (cfg_at (fx := fxc) rsegs (exv_pc off) regs mem md) Q.
Proof.
  intros W fxc regs off mem md0 md Q regs' off' m' Hs0 Hst HK. unfold cfg_at.
  eapply (SRr_step rsegs B_prog_wx W); [reflexivity | rewrite restrict_mkst_fx; exact Hst |].
  intros md' Hs. exact (HK md' (same_but_materialized_trans _ _ _ Hs0 Hs)).
Qed.
End st.

(* ======== frame geometry ======== *)
Lemma exnD_zmaxl_nonneg : forall l, 0 <= zmaxl l.
Proof. induction l as [|a l IH]; cbn [zmaxl fold_right]; [lia|]. unfold zmaxl in IH. lia. Qed.

(* the walk's stack need is at least the frame: 304 = pi_frame F_ex_value at prh_img_B *)
Lemma exnD_stk_ge : forall E, 304 <= exv_STK E.
Proof.
  intros E. unfold exv_STK, STK_ex_value. change (@pi_frame prh_img_B F_ex_value) with 304.
  pose proof (exnD_zmaxl_nonneg [STK_RT_ECALL; STK_RT_STR; STK_RT_STRTOD; STK_ex_string; STK_ex_word; STK_ex_ws]).
  lia.
Qed.

Lemma exnD_i1_nonneg : forall E, 0 <= exv_i1 E.
Proof.
  intros E. unfold exv_i1, exv_len, exv_X.
  destruct (exn_skip_suffix (skipn (Z.to_nat (e_i0 E)) (e_x E))) as (m & Hm & Hs).
  rewrite Hs. rewrite length_skipn in Hm. rewrite !length_skipn.
  assert (Hle : (length (e_x E) - Z.to_nat (e_i0 E) - m <= length (e_x E))%nat)
    by (apply Nat.le_trans with (length (e_x E) - Z.to_nat (e_i0 E))%nat; apply Nat.le_sub_l).
  apply Zle_minus_le_0. apply inj_le. exact Hle.
Qed.

Section p. Context {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Variable E : exv_e.
Variable pos : Z.
Hypothesis HYP : EXV_HYP B ARx SK.
Hypothesis HT : EXN_T B ARx SK E pos.
Hypothesis HC : EXN_Ec B ARx SK E pos.
Hypothesis MK : EXN_keepM B ARx SK E pos.
Hypothesis KS : EXN_keep_spill E.

(* the frame of the activation, apart from the s1 spills, the cursor and the scratch *)
Lemma exnD_geo : forall fxc lyc Sc Hpc Wc regs memc mdc k,
  EXV_PRE B ARx E -> EXB (fx := fxc) B ARx SK E lyc Sc Hpc Wc regs memc mdc k pos ->
  ARx lyc Sc Hpc Wc memc mdc /\ In (1, pos) (frames Sc) /\
  4096 <= frame_addr lyc 1 pos /\ frame_addr lyc 1 pos + 128 <= alloc_ceiling /\
  (forall z, frame_addr lyc 1 pos <= z < frame_addr lyc 1 pos + 128 -> apresent (w_H Wc) memc z) /\
  (forall i, 0 <= i <= 8 -> 0 <= shadow_addr (frame_addr lyc 1 pos) + i < 2 ^ 64 /\
     (shadow_addr (frame_addr lyc 1 pos) + i < frame_addr lyc 1 pos + 64 \/
      frame_addr lyc 1 pos + 72 <= shadow_addr (frame_addr lyc 1 pos) + i)) /\
  alloc_ceiling <= e_q E /\ e_q E + 40 <= 2 ^ 47 /\
  alloc_ceiling <= exv_s1 E + 136 /\ exv_s1 E + 160 <= 2 ^ 47 /\
  4096 <= e_scr E /\ e_scr E + exv_len E + 1 <= alloc_ceiling /\
  (e_scr E + exv_len E + 1 <= frame_addr lyc 1 pos \/ frame_addr lyc 1 pos + 128 <= e_scr E).
Proof.
  intros fxc lyc Sc Hpc Wc regs memc mdc k HPRE HB.
  pose proof (eh_laws B ARx SK HYP) as LAWS.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold EXV_PRE in HPRE. cbv zeta in HPRE.
  destruct HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & Hspq & Hqd & Hwin & _).
  destruct HFP as ((_ & _ & _ & _ & _ & Hastk & _) & _).
  destruct Hastk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & _ & Htop).
  destruct Hwin as (Hd0 & Hd16 & Hdtop & _).
  unfold EXB in HB. cbv zeta in HB.
  destruct HB as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HWD & HSB & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
  assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  destruct (frames_bounds_x rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HAR Hin) as (F1 & F2 & Happ).
  destruct (alx_frames rsegs B ARx LAWS _ _ _ _ _ _ 1 pos HAR Hin) as (_ & _ & Hpres & _).
  change (fs_frame_bytes 1) with 128 in F2, Happ, Hpres.
  pose proof (exv_s1_le E) as ((S1a & S1b) & _).
  pose proof (exnD_stk_ge E) as HSTK.
  unfold exv_sp, exv_STK in *.
  destruct HWD as (W1 & W2 & _).
  destruct HSB as (b & m & Hbm & Hb1 & Hb2 & _).
  destruct (alx_blocks rsegs B ARx LAWS _ _ _ _ _ _ _ _ HAR Hbm) as (_ & Hb4 & Hbc & _).
  pose proof (sep_block_frame_x rsegs B ARx LAWS _ _ _ _ _ _ b m 1 pos HAR Hbm Hin) as Hsep.
  change (fs_frame_bytes 1) with 128 in Hsep. unfold zdisjoint in Hsep. cbn [fst snd] in Hsep.
  assert (Hlen0 : 0 <= exv_len E) by (unfold exv_len; lia).
  assert (Hm : m <= req_size m) by (apply (proj2 (req_size_pos m ltac:(lia)))).
  split; [exact HAR|]. split; [exact Hin|]. split; [lia|]. split; [lia|].
  split; [intros z Hz; exact (proj1 (Hpres z Hz))|].
  split.
  { intros i Hi. unfold shadow_addr, SHADOW_OFF.
    unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
    split; [lia|]. destruct Happ as (_ & [Hlow | [Hhigh Hceil2]]); [right | left]; lia. }
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

Lemma exn_D : EXN_D B ARx SK E pos.
Proof.
  unfold EXN_D. intros fxc lyc Sc Hpc Wc regs memc mdc k c j bits cn HPRE HCR.
  pose proof (eh_laws B ARx SK HYP) as LAWS.
  pose proof asan_consts as (Hacl & _ & _ & _ & _).
  unfold EXN_CR_pre in HCR. cbv zeta in HCR.
  destruct HCR as (HBASE & HDISP & HCUR & HFSH & HSPAN & HJB & HSTOP & HSCR & HSTR & HCN & M32 & FA0 & R22 & R21
    & R23 & R20 & R27 & M136).
  destruct HBASE as (HEXB & M144 & M152).
  destruct (exnD_geo fxc lyc Sc Hpc Wc regs memc mdc k HPRE HEXB)
    as (HAR & Hin1 & Hf4 & Hfc & Hfrp & Hfsh & Hq1 & Hq2 & Hs1a & Hs1b & Hscr1 & Hscr2 & Hscrf).
  pose proof HEXB as HEXB'. unfold EXB in HEXB'. cbv zeta in HEXB'.
  destruct HEXB' as (HJ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R9 & _ & _ & R25 & _).
  pose proof HPRE as HPRE'. unfold EXV_PRE in HPRE'. cbv zeta in HPRE'.
  destruct HPRE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi0 & Hdep & _ & Hdl & _).
  set (f := frame_addr lyc 1 pos) in *.
  set (txt := exn_sub (e_x E) (EXN_i1 E) j) in *.
  pose proof HDISP as (Hlt & Hnth & _ & _).
  pose proof HSPAN as (Hl0 & Hd0 & Hnz0 & Hall).
  assert (Hlenx : exv_len E = Z.of_nat (length (e_x E))) by reflexivity.
  assert (Hltxt : length txt = (j - EXN_i1 E)%nat) by (unfold txt; apply exnD_sub_length; lia).
  assert (Hcnlen : cn <= exv_len E) by lia.
  assert (Htxtn : Forall (fun z => PjGrammar.numch z = true) txt)
    by (apply (exnD_txt_numch _ (EXN_i1 E) j c Hnth); [lia | exact Hall]).
  pose proof (exnD_N (e_x E) (EXN_i1 E) j c bits cn Hnth Hl0 Hd0 Hnz0 Hall HJB HSTOP HSTR) as HN. fold txt in HN.
  pose proof (exn_V_eq E c Hi0 HDISP) as HV.
  pose proof (exnD_i1_nonneg E) as Hi1nn.
  assert (FA0' : reg_get (@YK11.fp_regs fxc) 10%bv = Z_to_bv 64 bits)
    by (rewrite <- FA0; f_equal; apply bv_eq; reflexivity).
  change (exv_pc EXN_CR) with (exv_pc 0x8d4).
  (* ---- 0x8d4 ld a0,0(s7) ---- *)
  destruct (word_mem_ld rsegs (mrestrict (w_H Wc) memc) (f + 32) (e_scr E + cn)
    (proj1 (val_mem_word_mem _ _ _ _) M32) ltac:(lia) ltac:(lia)) as (bs1 & Hrd1 & Hbs1).
  set (R1 := YK11.regupd regs 10%bv (w64 (e_scr E + cn))).
  exnD_fetch 0x8d4 (Load SZ8 true 10%bv 23%bv 0%bv).
  apply (exnD_step Wc fxc regs 0x8d4 memc mdc mdc _ R1 0x8d8 (same_but_materialized_refl mdc)).
  { rewrite (step_ld _ _ _ _ _ _ _ _ _ bs1 (w64 (e_scr E + cn)) Hf He Hd); [rewrite exnD_next; reflexivity | | exact Hbs1].
    rewrite R23. unfold w64. rewrite YCbn.v_addi_lit. exnD_bvs. rewrite Z.add_0_r. exact Hrd1. }
  clear Hf He Hd. intros md1 Hsm1.
  assert (A1 : YK11.getr R1 10%bv = w64 (e_scr E + cn)) by (unfold R1; apply getr_same; discriminate).
  assert (HF1 : exnD_frame R1 regs) by (unfold R1; apply exnD_frame_upd; [left; reflexivity | apply exnD_frame_refl]).
  clearbody R1.
  (* ---- 0x8d8 ld a1,136(s1) ---- *)
  destruct (word_mem_ld rsegs (mrestrict (w_H Wc) memc) (exv_s1 E + 136) (f + 64)
    (proj1 (val_mem_word_mem _ _ _ _) M136) ltac:(lia) ltac:(lia)) as (bs2 & Hrd2 & Hbs2).
  set (R2 := YK11.regupd R1 11%bv (w64 (f + 64))).
  exnD_fetch 0x8d8 (Load SZ8 true 11%bv 9%bv 136%bv).
  apply (exnD_step Wc fxc R1 0x8d8 memc mdc md1 _ R2 0x8dc Hsm1).
  { rewrite (step_ld _ _ _ _ _ _ _ _ _ bs2 (w64 (f + 64)) Hf He Hd); [rewrite exnD_next; reflexivity | | exact Hbs2].
    rewrite (HF1 9%bv) by discriminate. rewrite R9. unfold w64. rewrite YCbn.v_addi_lit. exnD_bvs. exact Hrd2. }
  clear Hf He Hd. intros md2 Hsm2.
  assert (A2_10 : YK11.getr R2 10%bv = w64 (e_scr E + cn)) by (unfold R2; rewrite getr_other by discriminate; exact A1).
  assert (A2_11 : YK11.getr R2 11%bv = w64 (f + 64)) by (unfold R2; apply getr_same; discriminate).
  assert (HF2 : exnD_frame R2 regs) by (unfold R2; apply exnD_frame_upd; [right; left; reflexivity | exact HF1]).
  clearbody R2.
  (* ---- 0x8dc fsd fa0,0(a1) ---- *)
  exnD_fetch 0x8dc (FStore FMT_D 11%bv 10%bv 0%bv).
  apply (exnD_step_m Wc fxc R2 0x8dc memc mdc md2 _ R2 0x8e0
    (wbytes (mrestrict (w_H Wc) memc) (Z_to_bv 64 (f + 64)) (word_to_le_bytes 8 (Z_to_bv 64 bits))) Hsm2).
  { rewrite (fp_step_fsd fxc _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (f + 64)) Hf He Hd).
    - rewrite FA0', exnD_next. reflexivity.
    - rewrite A2_11. unfold w64. rewrite YCbn.v_addi_lit. exnD_bvs. rewrite Z.add_0_r. reflexivity.
    - apply exnD_store_ok; [| lia | lia]. intros i Hi.
      destruct (Hfrp (f + 64 + i) ltac:(lia)) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. discriminate. }
  clear Hf He Hd. intros md3 Hsm3.
  set (mem1 := munrestrict (w_H Wc) memc
    (wbytes (mrestrict (w_H Wc) memc) (Z_to_bv 64 (f + 64)) (word_to_le_bytes 8 (Z_to_bv 64 bits)))).
  assert (Hbl8 : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 bits))) = 8)
    by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
  (* the bytes the store kept: all but the num slot [f + 64, f + 72) *)
  assert (AV1 : forall z, 0 <= z < 2 ^ 64 -> (z < f + 64 \/ f + 72 <= z) ->
                  aview rsegs (w_H Wc) mem1 z = aview rsegs (w_H Wc) memc z).
  { intros z Hz Hout. unfold mem1. apply exnD_aview_out; rewrite ?Hbl8; lia. }
  assert (G1 : forall a, apresent (w_H Wc) memc a -> apresent (w_H Wc) mem1 a).
  { intros a Ha. eapply apresent_grows; [|exact Ha]. unfold mem1. apply exnD_wb_grow; rewrite ?Hbl8; lia. }
  assert (KW1 : forall z, 0 <= z < 2 ^ 64 -> ~ EXN_wz B E pos lyc z ->
                  aview rsegs (w_H Wc) mem1 z = aview rsegs (w_H Wc) memc z).
  { intros z Hz Hwz. apply AV1; [exact Hz|].
    destruct (Z_lt_le_dec z (f + 64)) as [Hz1|Hz1]; [left; exact Hz1|].
    destruct (Z_lt_le_dec z (f + 72)) as [Hz2|Hz2]; [|right; exact Hz2].
    exfalso. apply Hwz. unfold EXN_wz. right; right; left. unfold f in Hz1, Hz2. lia. }
  (* the journal across the store: awr_byte's in_frames arm *)
  assert (AJ1 : forall md', same_but_materialized mdc md' ->
    ajournal_x (SK := SK) rsegs B prh_pst ARx (exv_STK E + e_d E) (exv_sp E + e_d E) (exv_FP E)
      (e_ly E) (e_S E) (e_Hp E) (e_W E) (e_mem E) (e_md E) [(1, pos)] lyc Sc Hpc Wc mem1 md' k).
  { intros md' Hsm.
    apply (ajournal_x_exec (SK := SK) rsegs B prh_pst ARx LAWS B_prog_segs_low
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem1 md' (fun z => f + 64 <= z < f + 72) HJ).
    - intros x Hx. unfold mem1. apply exnD_wb_out; rewrite ?Hbl8; lia.
    - unfold mem1. apply exnD_wb_grow; rewrite ?Hbl8; lia.
    - intros x Hx. unfold mem1. apply exnD_wb_hid. exact Hx.
    - exact Hsm.
    - intros z Hz. right; right; right. exists 1, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 1) with 128. unfold f in Hz. lia. }
  (* memnorm across the store: the restricted write is LPS's EStore under store_ok (YAkMemnorm.memnorm_write),
     merged back under the hidden part (memnorm_munrestrict) *)
  assert (MN1 : YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs mem1).
  { intros Hmn. unfold mem1. apply YAkMemnorm.memnorm_munrestrict; [exact Hmn|].
    rewrite <- write_to_mem_wbytes. apply YAkMemnorm.memnorm_write; [apply YAkMemnorm.memnorm_mrestrict; exact Hmn|].
    replace (length (word_to_le_bytes 8 (Z_to_bv 64 bits))) with 8%nat
      by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
    apply exnD_store_ok; [| lia | lia]. intros i Hi.
    destruct (Hfrp (f + 64 + i) ltac:(lia)) as [Hh [b Hb]]. unfold mrestrict. rewrite Hh, Hb. discriminate. }
  (* EXB after the store, at the entry registers (lane M) *)
  pose proof (MK fxc lyc Sc Hpc Wc regs memc mdc k regs mem1 mdc k HPRE HEXB
    (AJ1 mdc (same_but_materialized_refl mdc)) KW1 G1 MN1 (exnD_kept regs regs (exnD_frame_refl regs))) as HB1.
  (* the spills, the cursor, the frame's shadow, the scratch, the num slot after the store *)
  assert (M136' : exv_spill E Wc mem1 136 (f + 64)).
  { apply (KS Wc memc mem1 136 _ M136). intros z Hz. apply AV1; lia. }
  assert (M144' : exv_spill E Wc mem1 144 (shadow_addr (e_q E))).
  { apply (KS Wc memc mem1 144 _ M144). intros z Hz. apply AV1; lia. }
  assert (M152' : exv_spill E Wc mem1 152 (e_v E)).
  { apply (KS Wc memc mem1 152 _ M152). intros z Hz. apply AV1; lia. }
  assert (HCUR1 : EXN_cur E Wc mem1 (exv_i1 E) (e_dl E)).
  { unfold EXN_cur, prhex_cur in HCUR |- *. destruct HCUR as (V1 & V2 & V3 & V4 & V5).
    refine (conj _ (conj _ (conj _ (conj _ _))));
      [ eapply ExvB_Num_eng.exw_val_kept with (m := memc); [|exact V1]
      | eapply ExvB_Num_eng.exw_val_kept with (m := memc); [|exact V2]
      | eapply ExvB_Num_eng.exw_val_kept with (m := memc); [|exact V3]
      | eapply ExvB_Num_eng.exw_val_kept with (m := memc); [|exact V4]
      | eapply ExvB_Num_eng.exw_val_kept with (m := memc); [|exact V5] ];
    intros z Hz; cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hz; apply AV1; lia. }
  assert (HFSH1 : EXN_fsh pos lyc Wc mem1).
  { unfold EXN_fsh in HFSH |- *. fold f in HFSH |- *. destruct HFSH as [F4 F8]. split.
    - rewrite <- F4. apply AV1; [exact (proj1 (Hfsh 4 ltac:(lia))) | exact (proj2 (Hfsh 4 ltac:(lia)))].
    - rewrite <- F8. apply AV1; [exact (proj1 (Hfsh 8 ltac:(lia))) | exact (proj2 (Hfsh 8 ltac:(lia)))]. }
  assert (HSCR1 : garr8 rsegs (mrestrict (w_H Wc) mem1) (e_scr E) (txt ++ [0])).
  { eapply ExvB_Num_eng.exw_garr8_kept with (m := memc); [|exact HSCR].
    intros a Ha. rewrite length_app, Hltxt in Ha. cbn [length] in Ha. apply AV1; lia. }
  assert (MFR : val_mem rsegs (mrestrict (w_H Wc) mem1) (f + 64) 8 bits).
  { intros kk Hkk. unfold mem1. apply exnD_wb_in; [lia | lia | exact Hkk |].
    destruct (Hfrp (f + 64 + Z.of_nat kk) ltac:(lia)) as [Hh _]. exact Hh. }
  (* the base invariant at the two exits *)
  assert (BASE1 : forall R md', same_but_materialized mdc md' -> exnD_frame R regs ->
    EXN_base B ARx SK E pos fxc lyc Sc Hpc Wc R mem1 md' k).
  { intros R md' Hsm HF. split; [|exact (conj M144' M152')].
    exact (MK fxc lyc Sc Hpc Wc regs memc mdc k R mem1 md' k HPRE HEXB (AJ1 md' Hsm) KW1 G1 MN1 (exnD_kept R regs HF)). }
  lazymatch goal with |- SRr _ _ _ ?Q =>
  assert (EXIT_CT : forall R md', same_but_materialized mdc md' -> exnD_frame R regs ->
    exn_N (skipn (EXN_i1 E) (e_x E)) = None ->
    SRr rsegs Wc (cfg_at (fx := fxc) rsegs (exv_pc 0xa70) R mem1 md') Q);
  [|assert (EXIT_CC : forall R md', same_but_materialized mdc md' -> exnD_frame R regs ->
    YK11.getr R 13%bv = w64 (shadow_addr (e_q E)) ->
    exn_N (skipn (EXN_i1 E) (e_x E)) = Some (PjTree.JNum txt bits, skipn j (e_x E)) ->
    SRr rsegs Wc (cfg_at (fx := fxc) rsegs (exv_pc 0x910) R mem1 md') Q)] end.
  { intros R md' Hsm HF HNone. change (exv_pc 0xa70) with (exv_pc EXN_CT).
    apply (HT fxc lyc Sc Hpc Wc R mem1 md' k (-1) HPRE).
    unfold EXN_CT_pre. split; [exact (BASE1 R md' Hsm HF)|].
    split; [rewrite (HF 21%bv) by exnD_rne; exact R21|].
    exists (exv_i1 E), (e_dep E), (e_dl E).
    split; [exact HCUR1|]. split; [exact Hdl|].
    rewrite HV, HNone. cbv beta iota. split; [reflexivity|]. split; lia. }
  { intros R md' Hsm HF H13 HSome. change (exv_pc 0x910) with (exv_pc EXN_CC).
    apply (HC fxc lyc Sc Hpc Wc R mem1 md' k c j bits HPRE).
    unfold EXN_CC_pre. cbv zeta. fold txt.
    split; [exact (BASE1 R md' Hsm HF)|].
    split; [exact HDISP|]. split; [exact HCUR1|]. split; [exact HFSH1|].
    split; [lia|]. split; [exact HSome|]. split; [exact HSCR1|]. split; [exact MFR|].
    split; [rewrite (HF 22%bv) by exnD_rne; exact R22|].
    split; [exact H13|].
    split; [rewrite (HF 21%bv) by exnD_rne; exact R21|].
    split; [rewrite (HF 20%bv) by exnD_rne; exact R20|].
    split; [rewrite (HF 27%bv) by exnD_rne; exact R27|].
    exact M136'. }
  (* ---- the tail from 0x8f8, reached with a0 = end by both sides of the shadow check ---- *)
  lazymatch goal with |- SRr _ _ _ ?Q =>
  assert (TAIL : forall R md', same_but_materialized mdc md' -> exnD_frame R regs ->
            YK11.getr R 10%bv = w64 (e_scr E + cn) -> YK11.getr R 13%bv = w64 (shadow_addr (e_q E)) ->
            SRr rsegs Wc (cfg_at (fx := fxc) rsegs (exv_pc 0x8f8) R mem1 md') Q) end.
  { intros R md' Hsm' HFR A10 A13.
    (* 0x8f8 lbu a0,0(a0) *)
    set (e := nth (Z.to_nat cn) (txt ++ [0]) 0).
    destruct (HSCR1 (Z.to_nat cn) ltac:(rewrite length_app, Hltxt; cbn [length]; lia)) as [Hve Hre].
    fold e in Hve, Hre. rewrite Z2Nat.id in Hve by lia.
    assert (Hrd8 : rdn rsegs (mrestrict (w_H Wc) mem1) (Z_to_bv 64 (e_scr E + cn)) 1 = Some [Z_to_bv 8 (le_byte e 1 0)]).
    { apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
      rewrite (Hve 0%nat ltac:(lia)). reflexivity. }
    set (R8 := YK11.regupd R 10%bv (w64 e)).
    exnD_fetch 0x8f8 (Load SZ1 false 10%bv 10%bv 0%bv).
    apply (exnD_step Wc fxc R 0x8f8 mem1 mdc md' _ R8 0x8fc Hsm').
    { rewrite (step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 (le_byte e 1 0)) Hf He Hd).
      - rewrite exnD_byte by exact Hre. rewrite exnD_next. reflexivity.
      - rewrite A10. unfold w64. rewrite YCbn.v_addi_lit. exnD_bvs. rewrite Z.add_0_r. exact Hrd8. }
    clear Hf He Hd. intros md8 Hsm8.
    assert (A8 : YK11.getr R8 10%bv = w64 e) by (unfold R8; apply getr_same; discriminate).
    assert (A8_13 : YK11.getr R8 13%bv = w64 (shadow_addr (e_q E))) by (unfold R8; rewrite getr_other by discriminate; exact A13).
    assert (HF8 : exnD_frame R8 regs) by (unfold R8; apply exnD_frame_upd; [left; reflexivity | exact HFR]).
    clearbody R8.
    pose proof (exnD_end_byte txt cn Htxtn HCN) as HEB. fold e in HEB.
    (* 0x8fc bnez a0 -> CT *)
    exnD_fetch 0x8fc (Branch BC_NE 10%bv 0%bv 372%bv).
    destruct (Z.eq_dec cn (Z.of_nat (length txt))) as [Ecn | Ecn].
    2: {
      assert (Hb : (cn =? Z.of_nat (length txt)) = false) by (apply Z.eqb_neq; exact Ecn).
      apply (exnD_step Wc fxc R8 0x8fc mem1 mdc md8 _ R8 0xa70 Hsm8).
      { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite exnD_btgt; reflexivity|].
        rewrite A8, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. rewrite HEB. exact Hb. }
      intros md9 Hsm9. apply (EXIT_CT R8 md9 Hsm9 HF8).
      rewrite HN, Hb. reflexivity. }
    assert (Hb : (cn =? Z.of_nat (length txt)) = true) by (apply Z.eqb_eq; exact Ecn).
    apply (exnD_step Wc fxc R8 0x8fc mem1 mdc md8 _ R8 0x900 Hsm8).
    { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite exnD_next; reflexivity|].
      rewrite A8, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. rewrite HEB. exact Hb. }
    clear Hf He Hd. intros md9 Hsm9.
    (* 0x900 fclass.d a0,fa0 *)
    set (K := fp_class fmt_double (bits mod 2 ^ 64)).
    pose proof (exnD_fclass_range (bits mod 2 ^ 64)) as HKr. fold K in HKr.
    set (R10 := YK11.regupd R8 10%bv (w64 K)).
    exnD_fetch 0x900 (Fclass FMT_D 10%bv 10%bv).
    apply (exnD_step Wc fxc R8 0x900 mem1 mdc md9 _ R10 0x904 Hsm9).
    { rewrite (exnD_step_fclass_d fxc _ _ _ _ _ _ _ _ Hf He Hd). rewrite FA0', Z_to_bv_unsigned, exnD_next.
      reflexivity. }
    clear Hf He Hd. intros md10 Hsm10.
    assert (A10' : YK11.getr R10 10%bv = w64 K) by (unfold R10; apply getr_same; discriminate).
    assert (A10_13 : YK11.getr R10 13%bv = w64 (shadow_addr (e_q E)))
      by (unfold R10; rewrite getr_other by discriminate; exact A8_13).
    assert (HF10 : exnD_frame R10 regs) by (unfold R10; apply exnD_frame_upd; [left; reflexivity | exact HF8]).
    clearbody R10.
    (* 0x904 andi a0,a0,897 *)
    set (R11 := YK11.regupd R10 10%bv (w64 (Z.land K 897))).
    exnD_fetch 0x904 (OpImm ALU_AND 10%bv 10%bv 897%bv).
    apply (exnD_step Wc fxc R10 0x904 mem1 mdc md10 _ R11 0x908 Hsm10).
    { rewrite (step_andi _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A10'. exnD_bvs. unfold YK11.v_andi, w64.
      rewrite YK00.u64_lit by lia. rewrite exnD_next. reflexivity. }
    clear Hf He Hd. intros md11 Hsm11.
    assert (A11 : YK11.getr R11 10%bv = w64 (Z.land K 897)) by (unfold R11; apply getr_same; discriminate).
    assert (A11_13 : YK11.getr R11 13%bv = w64 (shadow_addr (e_q E)))
      by (unfold R11; rewrite getr_other by discriminate; exact A10_13).
    assert (HF11 : exnD_frame R11 regs) by (unfold R11; apply exnD_frame_upd; [left; reflexivity | exact HF10]).
    clearbody R11.
    assert (HM : 0 <= Z.land K 897 < 2 ^ 64) by (apply (fp_Z_land_range_l 64); lia).
    (* 0x908 snez a0,a0 *)
    set (s12 := if 0 <? Z.land K 897 then 1 else 0).
    set (R12 := YK11.regupd R11 10%bv (w64 s12)).
    exnD_fetch 0x908 (Op ALU_SLTU 10%bv 0%bv 10%bv).
    apply (exnD_step Wc fxc R11 0x908 mem1 mdc md11 _ R12 0x90c Hsm11).
    { rewrite (step_sltu _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A11, getr_zero. unfold YK11.v_sltu, w64.
      rewrite YK00.c_ltu_lit by lia. rewrite exnD_next. unfold R12, s12, w64.
      destruct (0 <? Z.land K 897); reflexivity. }
    clear Hf He Hd. intros md12 Hsm12.
    assert (A12 : YK11.getr R12 10%bv = w64 s12) by (unfold R12; apply getr_same; discriminate).
    assert (A12_13 : YK11.getr R12 13%bv = w64 (shadow_addr (e_q E)))
      by (unfold R12; rewrite getr_other by discriminate; exact A11_13).
    assert (HF12 : exnD_frame R12 regs) by (unfold R12; apply exnD_frame_upd; [left; reflexivity | exact HF11]).
    clearbody R12.
    pose proof (exnD_fclass bits) as HFC. fold K in HFC.
    (* 0x90c bnez a0 -> CT, else CC *)
    exnD_fetch 0x90c (Branch BC_NE 10%bv 0%bv 356%bv).
    destruct (Z.eq_dec (Z.land K 897) 0) as [EM | EM].
    - apply (exnD_step Wc fxc R12 0x90c mem1 mdc md12 _ R12 0x910 Hsm12).
      { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite exnD_next; reflexivity|].
        rewrite A12, getr_zero. unfold s12. rewrite EM. reflexivity. }
      intros md13 Hsm13. apply (EXIT_CC R12 md13 Hsm13 HF12).
      + exact A12_13.
      + rewrite HN, Hb, <- HFC, EM. reflexivity.
    - apply (exnD_step Wc fxc R12 0x90c mem1 mdc md12 _ R12 0xa70 Hsm12).
      { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite exnD_btgt; reflexivity|].
        rewrite A12, getr_zero. unfold s12. replace (0 <? Z.land K 897) with true by (symmetry; apply Z.ltb_lt; lia).
        reflexivity. }
      intros md13 Hsm13. apply (EXIT_CT R12 md13 Hsm13 HF12).
      rewrite HN, <- HFC. replace (Z.land K 897 =? 0) with false by (symmetry; apply Z.eqb_neq; exact EM).
      rewrite andb_false_r. reflexivity. }
  (* ---- 0x8e0 ld a3,144(s1) ---- *)
  destruct (word_mem_ld rsegs (mrestrict (w_H Wc) mem1) (exv_s1 E + 144) (shadow_addr (e_q E))
    (proj1 (val_mem_word_mem _ _ _ _) M144') ltac:(lia) ltac:(lia)) as (bs3 & Hrd3 & Hbs3).
  set (R3 := YK11.regupd R2 13%bv (w64 (shadow_addr (e_q E)))).
  exnD_fetch 0x8e0 (Load SZ8 true 13%bv 9%bv 144%bv).
  apply (exnD_step Wc fxc R2 0x8e0 mem1 mdc md3 _ R3 0x8e4 Hsm3).
  { rewrite (step_ld _ _ _ _ _ _ _ _ _ bs3 (w64 (shadow_addr (e_q E))) Hf He Hd);
      [rewrite exnD_next; reflexivity | | exact Hbs3].
    rewrite (HF2 9%bv) by discriminate. rewrite R9. unfold w64. rewrite YCbn.v_addi_lit. exnD_bvs. exact Hrd3. }
  clear Hf He Hd. intros md4 Hsm4.
  assert (A3_10 : YK11.getr R3 10%bv = w64 (e_scr E + cn)) by (unfold R3; rewrite getr_other by discriminate; exact A2_10).
  assert (A3_13 : YK11.getr R3 13%bv = w64 (shadow_addr (e_q E))) by (unfold R3; apply getr_same; discriminate).
  assert (HF3 : exnD_frame R3 regs)
    by (unfold R3; apply exnD_frame_upd; [right; right; right; reflexivity | exact HF2]).
  clearbody R3.
  (* ---- 0x8e4 beqz a0 -> unimp (UBSan): NOT taken, a0 = scr + cn >= 4096 ---- *)
  exnD_fetch 0x8e4 (Branch BC_EQ 10%bv 0%bv 620%bv).
  apply (exnD_step Wc fxc R3 0x8e4 mem1 mdc md4 _ R3 0x8e8 Hsm4).
  { rewrite (step_beq_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite exnD_next; reflexivity|].
    rewrite A3_10, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. apply Z.eqb_neq. lia. }
  clear Hf He Hd. intros md5 Hsm5.
  (* ---- 0x8e8 srli a1,a0,3 ---- *)
  set (R4 := YK11.regupd R3 11%bv (w64 ((e_scr E + cn) / 8))).
  exnD_fetch 0x8e8 (ShiftImm ALU_SRL 11%bv 10%bv 3%bv).
  apply (exnD_step Wc fxc R3 0x8e8 mem1 mdc md5 _ R4 0x8ec Hsm5).
  { rewrite (step_srli _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A3_10. unfold YK11.v_srli, w64.
    rewrite YK00.u64_lit by lia. rewrite Z.shiftr_div_pow2 by (vm_compute; discriminate).
    replace (2 ^ bv_unsigned 3%bv) with 8 by (vm_compute; reflexivity). rewrite exnD_next. reflexivity. }
  clear Hf He Hd. intros md6 Hsm6.
  assert (A4_10 : YK11.getr R4 10%bv = w64 (e_scr E + cn)) by (unfold R4; rewrite getr_other by discriminate; exact A3_10).
  assert (A4_11 : YK11.getr R4 11%bv = w64 ((e_scr E + cn) / 8)) by (unfold R4; apply getr_same; discriminate).
  assert (A4_13 : YK11.getr R4 13%bv = w64 (shadow_addr (e_q E)))
    by (unfold R4; rewrite getr_other by discriminate; exact A3_13).
  assert (HF4 : exnD_frame R4 regs) by (unfold R4; apply exnD_frame_upd; [right; left; reflexivity | exact HF3]).
  clearbody R4.
  (* ---- 0x8ec add a1,a1,s9 (s9 = the shadow offset) ---- *)
  set (R5 := YK11.regupd R4 11%bv (w64 (shadow_addr (e_scr E + cn)))).
  exnD_fetch 0x8ec (Op ALU_ADD 11%bv 11%bv 25%bv).
  apply (exnD_step Wc fxc R4 0x8ec mem1 mdc md6 _ R5 0x8f0 Hsm6).
  { rewrite (step_add _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A4_11, (HF4 25%bv) by discriminate. rewrite R25.
    unfold YK11.v_add, w64. rewrite !YK00.u64_lit by (unfold SHADOW_OFF; lia). rewrite exnD_next.
    unfold R5, w64, shadow_addr. rewrite (Z.add_comm ((e_scr E + cn) / 8) SHADOW_OFF). reflexivity. }
  clear Hf He Hd. intros md7 Hsm7.
  assert (A5_10 : YK11.getr R5 10%bv = w64 (e_scr E + cn)) by (unfold R5; rewrite getr_other by discriminate; exact A4_10).
  assert (A5_11 : YK11.getr R5 11%bv = w64 (shadow_addr (e_scr E + cn))) by (unfold R5; apply getr_same; discriminate).
  assert (A5_13 : YK11.getr R5 13%bv = w64 (shadow_addr (e_q E)))
    by (unfold R5; rewrite getr_other by discriminate; exact A4_13).
  assert (HF5 : exnD_frame R5 regs) by (unfold R5; apply exnD_frame_upd; [right; left; reflexivity | exact HF4]).
  clearbody R5.
  (* ---- 0x8f0 lb a1,0(a1): the shadow byte of end (wdest_ok's range_addressable for the scratch, at mem1) ---- *)
  pose proof HB1 as HB1'. unfold EXB in HB1'. cbv zeta in HB1'.
  destruct HB1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
    & HWD1 & _).
  pose proof HWD1 as (_ & _ & _ & _ & HRA1 & _).
  destruct (HRA1 (e_scr E + cn) ltac:(lia)) as (s & Hsv & Hsok).
  assert (Hsv' : aview rsegs (w_H Wc) mem1 (shadow_addr (e_scr E + cn)) = Some s) by exact Hsv.
  destruct (exnD_aview_rdn rsegs _ _ _ _ Hsv') as (sb & Hrd6 & Hsb).
  assert (Hs8 : 0 <= s < 8) by (unfold saddr_ok in Hsok; pose proof (Z.mod_pos_bound (e_scr E + cn) 8); lia).
  set (R6 := YK11.regupd R5 11%bv (w64 s)).
  exnD_fetch 0x8f0 (Load SZ1 true 11%bv 11%bv 0%bv).
  apply (exnD_step Wc fxc R5 0x8f0 mem1 mdc md7 _ R6 0x8f4 Hsm7).
  { rewrite (step_lb _ _ _ _ _ _ _ _ _ sb Hf He Hd).
    - replace (v_lb sb) with (Z_to_bv 64 s) by (symmetry; exact (YCbn.cellval_small true sb s Hsb ltac:(lia))).
      rewrite exnD_next. reflexivity.
    - rewrite A5_11. unfold w64. rewrite YCbn.v_addi_lit. exnD_bvs. rewrite Z.add_0_r. exact Hrd6. }
  clear Hf He Hd. intros md8 Hsm8.
  assert (A6_10 : YK11.getr R6 10%bv = w64 (e_scr E + cn)) by (unfold R6; rewrite getr_other by discriminate; exact A5_10).
  assert (A6_11 : YK11.getr R6 11%bv = w64 s) by (unfold R6; apply getr_same; discriminate).
  assert (A6_13 : YK11.getr R6 13%bv = w64 (shadow_addr (e_q E)))
    by (unfold R6; rewrite getr_other by discriminate; exact A5_13).
  assert (HF6 : exnD_frame R6 regs) by (unfold R6; apply exnD_frame_upd; [right; left; reflexivity | exact HF5]).
  clearbody R6.
  (* ---- 0x8f4 bnez a1 -> the slow path 0xc04 ---- *)
  exnD_fetch 0x8f4 (Branch BC_NE 11%bv 0%bv 784%bv).
  destruct (Z.eqb_spec s 0) as [Es | Es].
  - apply (exnD_step Wc fxc R6 0x8f4 mem1 mdc md8 _ R6 0x8f8 Hsm8).
    { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite exnD_next; reflexivity|].
      rewrite A6_11, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. apply Z.eqb_eq. exact Es. }
    intros md9 Hsm9. exact (TAIL R6 md9 Hsm9 HF6 A6_10 A6_13).
  - apply (exnD_step Wc fxc R6 0x8f4 mem1 mdc md8 _ R6 0xc04 Hsm8).
    { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite exnD_btgt; reflexivity|].
      rewrite A6_11, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. apply Z.eqb_neq. exact Es. }
    clear Hf He Hd. intros md9 Hsm9.
    (* 0xc04 andi a2,a0,7 *)
    set (R7 := YK11.regupd R6 12%bv (w64 ((e_scr E + cn) mod 8))).
    exnD_fetch 0xc04 (OpImm ALU_AND 12%bv 10%bv 7%bv).
    apply (exnD_step Wc fxc R6 0xc04 mem1 mdc md9 _ R7 0xc08 Hsm9).
    { rewrite (step_andi _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A6_10. exnD_bvs. unfold YK11.v_andi, w64.
      rewrite YK00.u64_lit by lia. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia.
      rewrite exnD_next. reflexivity. }
    clear Hf He Hd. intros md10 Hsm10.
    assert (A7_10 : YK11.getr R7 10%bv = w64 (e_scr E + cn)) by (unfold R7; rewrite getr_other by discriminate; exact A6_10).
    assert (A7_11 : YK11.getr R7 11%bv = w64 s) by (unfold R7; rewrite getr_other by discriminate; exact A6_11).
    assert (A7_12 : YK11.getr R7 12%bv = w64 ((e_scr E + cn) mod 8)) by (unfold R7; apply getr_same; discriminate).
    assert (A7_13 : YK11.getr R7 13%bv = w64 (shadow_addr (e_q E)))
      by (unfold R7; rewrite getr_other by discriminate; exact A6_13).
    assert (HF7 : exnD_frame R7 regs) by (unfold R7; apply exnD_frame_upd; [right; right; left; reflexivity | exact HF6]).
    clearbody R7.
    (* 0xc08 blt a2,a1 -> 0x8f8: TAKEN (the partial granule holds end), so `jal errpath_load1` is unreachable *)
    exnD_fetch 0xc08 (Branch BC_LT 12%bv 11%bv 7408%bv).
    apply (exnD_step Wc fxc R7 0xc08 mem1 mdc md10 _ R7 0x8f8 Hsm10).
    { rewrite (step_blt_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite exnD_btgt; reflexivity|].
      rewrite A7_12, A7_11. unfold w64, YK11.c_lts.
      pose proof (Z.mod_pos_bound (e_scr E + cn) 8).
      rewrite YCbn.bv_lts_small by lia. apply Z.ltb_lt.
      destruct Hsok as [Hs0|[Hs1 Hs2]]; [exfalso; exact (Es Hs0) | exact Hs1]. }
    intros md11 Hsm11. exact (TAIL R7 md11 Hsm11 HF7 A7_10 A7_13).
Qed.
End p.

Print Assumptions exn_D.
