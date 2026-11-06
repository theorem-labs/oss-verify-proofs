(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm), sub-piece
   E of lib/B/Prog/PvB_NCut.v: R (0x8681c, strtod's return site) -> T (0x8688c) | C (0x86864), over h-verbs-1's ONE
   image-B program listing (lib/B/Listing_prog.v, PL_prog_B). It proves pnE_stmt (PvB_NCut.v).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search: `proof-index parse_value` (h-hpreset-7 04:10Z, EXIT=0
   unpiped, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its address, 0
   related; in an earlier delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent CONFIRM
   (ParseValueLookupConfirm 04:21Z): no released srealizes-form proof of this program's parse_value; new proof
   justified. Image A's number arm of ex_value (lib/A/Prog/S8aNumD.v at cold/h-s8a-number-d 18f7e2272a9) is the
   template of the hand steps and of the pure lemmas, which are image independent and are ported here, not Required.

   THE CODE (the neutral listing, the internal file parse_value.fuzz_preset.asan-ubsan.s; listing offset = B pc - 0x816cc):
     0x8681c addi a1,s3,8         a1 := v + 8 (&v->num)
     0x86820 .. 0x8682c            the 8-byte shadow check of v + 8: lbu of shadow(v + 8), bnez -> 0x86938 (report)
     0x86830 ld a0,0(s9)          a0 := *(fa + 32) = res + cn (strtod's end pointer)
     0x86834 fsd fa0,0(a1)        v->num := bits                      (hand step: YK0o.v fp_step_fsd)
     0x86838 beqz a0,0x86898      the UBSan null check of end (report)
     0x8683c .. 0x86848            the 1-byte shadow check of end, slow arm 0x868d4 andi / 0x868d8 blt back to 0x8684c
     0x8684c lbu a0,0(a0)         the byte at end; non-zero -> T (outcome (c): cn <> m)
     0x86854 fclass.d a0,fa0      (hand step: lib/Reusable/YFclsStep.v fp_step_fclass_d)
     0x86858 andi a0,a0,897 / snez / bnez -> T (outcome (c): not finite); else C.
   Every one of the 20 listing instructions is taken by hand (YA0n.v SRr_step with YK11.v's / YK0o.v's single-step
   lemmas and fp_step_fclass_d). The report arms are refuted: shadow(v + 8) is 0 (the node is addressable and
   8-aligned), end = res + cn is not 0, and the end byte's slow arm returns (saddr_ok).
   THE STORE: v->num is in the caller's footprint FP. Its 8 bytes lie in the node, which lives (prhReader_at at entry)
   in a live allocator block, a live fake frame of the caller, or the caller's window; pnE_sep turns each home into
   the write premise of YCbqG.v's ajournal_x_exec_fr (awr_byte or wr_fp_frame) and separates the 8 bytes from every
   block head, the parse_value fake frame, the image (the ledger's statics), the real frame and the shadow band;
   pnE_post carries every fact of the cut across the store.
   MEMNORM: R's last conjunct `YStrtodRowX.aj_memnorm SEGS mem` (the memory normal form, a state fact of the cut) goes
   to T's / C's last conjunct. The 19 steps that write no memory keep mem itself; the one store (fsd) is pnE_step_m,
   which takes the normal form across by lib/Reusable/YSRrMemnorm.v's SRr_step_inv at P := YAkMemnorm.memnorm SEGS
   (its laws srr_inv_laws_memnorm_k; YStrtodRowX.aj_memnorm is the same body, by conversion).
   ROOM: R's pn_rp1 (PvB_NCut.v, the room post of EAlloc (S m)) goes unchanged to T's outcome (c) and to C's: the steps
   keep the allocator state Sc. The ledger's statics include #102's g_most / g_own_ran_out (f97c prh_glob, prh_pst's
   seven cells), kept like the other five.

   Section hypotheses: LAWS (AR_laws_x, the kit's, at its harness-head length hl, a Section Context), PSTOK (a
   MARKED image fact, the ledger's statics are image bytes, PvB_X.v's text verbatim).
   Numerals: listing offsets 20816 .. 20884, 20888, 20928, 21000, 21004 (DERIVED: B pc - B_prog_base 0x816cc);
   1 8 15 16 24 32 56 64 (LENGTH: access widths, node fields and the node's v->num granule end v + 15, the end slot
   fa + 32, the class-0 frame's bytes); -104 -8 (LENGTH: pv_saved's slot range); 3 7 897 (WORD: srli / andi
   immediates); 0 10 11 12 19 21 22 23 25 (WORD: register numbers); 6 (LENGTH: the shift field's width);
   268 96 140 8052 60 44 (WORD: branch immediates read from the listing); 176 320 16560 (LENGTH: parse_value's real
   frame and the STK sum, as PvB_X.v); 4096, 2 ^ 47, 2 ^ 64, 256, 128, 1024 (LENGTH: address and value ranges);
   52 11 2047 10 (LENGTH / WORD: binary64's mantissa and exponent widths, its exponent all-ones, Z.log2 2047);
   45 (WORD: ASCII '-'). No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YA0o YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04
YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YP0a YPsym YC4aP FCiface YGcallMx YC1fP YK0u YN01 YK1b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YStrtodRowX YFclsStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbn YK00 YA03.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PRW_CallerJ.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_NCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YSRrMemnorm YAkMemnorm.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Instance PIBe : PrhImg := prh_img_B.

(* ======== pure (image independent; ported from image A's S8aNumD.v) ======== *)

(* the byte at end = res + cn of txt ++ [0] is zero iff strtod consumed the whole text *)
Lemma pnE_end_byte : forall (txt : list Z) (cn : Z),
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

(* the fclass.d mask 0x381 (bit 0 -inf, 7 +inf, 8 sNaN, 9 qNaN) is zero iff the bits are finite; the register holds
   bits mod 2 ^ 64 *)
Lemma pnE_exp_mod : forall bits : Z,
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

Lemma pnE_fclass : forall bits : Z,
  (Z.land (fp_class fmt_double (bits mod 2 ^ 64)) 897 =? 0) = PjGrammar.finite bits.
Proof.
  intros bits. unfold fp_class, PjGrammar.finite. cbv zeta.
  unfold fp_exp_field.
  change (fp_mw fmt_double) with 52. change (Z.ones (fp_ew fmt_double)) with 2047.
  rewrite pnE_exp_mod.
  destruct (Z.land (Z.shiftr bits 52) 2047 =? 2047);
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma pnE_fclass_range : forall a : Z, 0 <= fp_class fmt_double a < 1024.
Proof.
  intros a. unfold fp_class. cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
  vm_compute; split; congruence.
Qed.

(* the text strtod read is all number characters: the sign byte '-' and the scanned span *)
Lemma pnE_txt_numch : forall (c : Z) (y : list Z) (m : nat),
  (pn_sg c < m)%nat -> pn_span (c :: y) (pn_sg c) m ->
  Forall (fun z => PjGrammar.numch z = true) (firstn m (c :: y)).
Proof.
  intros c y m. unfold pn_span, pn_sg. destruct (c =? 45) eqn:E; intros Hm Hsp.
  - apply Z.eqb_eq in E. destruct m as [|m]; [lia|]. cbn [firstn]. constructor.
    + rewrite E. reflexivity.
    + cbn [skipn] in Hsp. replace (S m - 1)%nat with m in Hsp by lia. exact Hsp.
  - cbn [skipn] in Hsp. rewrite Nat.sub_0_r in Hsp. exact Hsp.
Qed.

Lemma pnE_pw_in2 : forall {X : Type} (R : X -> X -> Prop) (l : list X) x y,
  pairwise R l -> In x l -> In y l -> x <> y -> R x y \/ R y x.
Proof.
  intros X R l. induction l as [|a t IH]; intros x y P Hx Hy Ne; [destruct Hx|].
  destruct P as [F P]. rewrite Forall_forall in F.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - exfalso. exact (Ne eq_refl).
  - left. exact (F y Hy).
  - right. exact (F x Hx).
  - exact (IH x y P Hx Hy Ne).
Qed.

Lemma pnE_saved_rng : forall oc, In oc pv_saved -> -104 <= fst oc <= -8.
Proof.
  intros oc H. unfold pv_saved in H.
  repeat (destruct H as [<-|H]; [cbn [fst]; lia|]). destruct H.
Qed.

(* ======== memory: one store of bs at A through the restricted view (S8aNumD.v's, renamed) ======== *)
Section m.
Variable segs : list Segment.

Lemma pnE_store_ok : forall (m : word -> option byte) (n : nat) (a : Z),
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

Lemma pnE_wb_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (x : word),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  (bv_unsigned x < A \/ A + Z.of_nat (length bs) <= bv_unsigned x) ->
  mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) x = mrestrict H mem x.
Proof.
  intros H mem A bs x HA HAn Hx. unfold munrestrict, mrestrict.
  destruct (H x) eqn:Hh; [reflexivity|].
  rewrite wbytes_outside; [cbv beta; rewrite Hh; reflexivity | rewrite YK00.u64_lit by lia; lia |].
  rewrite YK00.u64_lit by lia. exact Hx.
Qed.

Lemma pnE_wb_hid : forall (H : word -> bool) (mem m' : word -> option byte) (x : word),
  H x = true -> munrestrict H mem m' x = mem x.
Proof. intros H mem m' x Hh. unfold munrestrict. rewrite Hh. reflexivity. Qed.

Lemma pnE_wb_grow : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  mem_grows (mrestrict H mem) (mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs))).
Proof.
  intros H mem A bs HA HAn x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Hl|Hl]; [rewrite pnE_wb_out by lia; exact Hx|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Hu|Hu];
    [|rewrite pnE_wb_out by lia; exact Hx].
  unfold mrestrict in *. unfold munrestrict. destruct (H x) eqn:Hh; [exact Hx|].
  rewrite wbytes_inside; [discriminate | rewrite YK00.u64_lit by lia; lia | rewrite YK00.u64_lit by lia; lia].
Qed.

Lemma pnE_wb_in : forall (H : word -> bool) (mem : word -> option byte) (A v : Z) (k : nat),
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

Lemma pnE_aview_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (z : Z),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  (z < A \/ A + Z.of_nat (length bs) <= z) ->
  aview segs H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) z = aview segs H mem z.
Proof.
  intros H mem A bs z HA HAn Hz Hout. apply aview_eq_of. apply pnE_wb_out; [lia | lia |].
  rewrite YK00.u64_lit by lia. exact Hout.
Qed.

Lemma pnE_byte : forall e, 0 <= e < 256 -> bv_unsigned (Z_to_bv 8 (le_byte e 1 0)) = e.
Proof.
  intros e He. rewrite Z_to_bv_unsigned. unfold le_byte.
  replace (2 ^ (8 * Z.of_nat 1)) with 256 by reflexivity. replace (8 * Z.of_nat 0) with 0 by reflexivity.
  rewrite Z.shiftr_0_r, !(Z.mod_small e 256) by lia.
  replace (bv_wrap 8 e) with (e mod 256) by reflexivity. apply Z.mod_small. lia.
Qed.
End m.

(* the registers a step sequence leaves alone: all but a0, a1, a2 *)
Definition pnE_frame (R regs : bvmap 5 word) : Prop :=
  forall r : Prelude.reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr R r = getr regs r.

Lemma pnE_frame_refl : forall regs, pnE_frame regs regs.
Proof. intros regs r _ _ _. reflexivity. Qed.

Lemma pnE_frame_upd : forall R regs (d : Prelude.reg) v, (d = 10%bv \/ d = 11%bv \/ d = 12%bv) ->
  pnE_frame R regs -> pnE_frame (YK11.regupd R d v) regs.
Proof.
  intros R regs d v Hd HF r H10 H11 H12. rewrite getr_other; [apply HF; assumption|].
  destruct Hd as [ Hd | [ Hd | Hd ] ]; rewrite Hd; assumption.
Qed.

(* bv_signed of a literal immediate, computed *)
Ltac pnE_bvs := repeat match goal with |- context [bv_signed ?i] =>
  let v := eval vm_compute in (bv_signed i) in
  lazymatch v with
  | Z0 => change (bv_signed i) with 0
  | Zpos ?p => change (bv_signed i) with (Zpos p)
  | Zneg ?p => change (bv_signed i) with (Zneg p)
  end end.

(* ======== the walk ======== *)
Section c. Context {fx0 : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Context {SK : YI16.sink_head}.
Context {PA : PAImg B_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PA).
#[local] Abbreviation BASE := (@pa_val _ B_prog_listing PA A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* MARKED image fact, discharged at PI_prog_B: alloc.c's five statics are image bytes the program owns (YC80x.v's
   PST_ok; PvB_X.v's PSTOK, verbatim) *)
Hypothesis PSTOK : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).

Lemma pnE_fetch : forall off w, plookup B_prog_tpi off = Some (PW w) ->
  fetch_word SEGS (Z_to_bv 64 (BASE + off)) = Some (Z_to_bv 32 w).
Proof. intros off w H. exact (@pa_fetch_pw _ _ PL_prog_B PA off w H). Qed.

Lemma pnE_next : forall off k, YK11.v_addi (Z_to_bv 64 (BASE + off)) k = Z_to_bv 64 (BASE + (off + k)).
Proof. intros off k. rewrite YCbn.v_addi_lit. f_equal. lia. Qed.

Lemma pnE_btgt : forall off k, YK11.btgt (Z_to_bv 64 (BASE + off)) k = Z_to_bv 64 (BASE + (off + k)).
Proof. intros off k. unfold YK11.btgt. apply pnE_next. Qed.

(* one hand step at a cut-free pc: registers and pc change, memory does not *)
Lemma pnE_step : forall (W : world SEGS) (fxc : YK11.FPState) regs off mem md0 md Q regs' off',
  same_but_materialized md0 md ->
  RiscvSemantics.step SEGS (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + off)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxc regs' (Z_to_bv 64 (BASE + off')) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) ->
  (forall md', same_but_materialized md0 md' -> SRr SEGS W (mkCfg (pn_ms fxc regs' off' mem) md') Q) ->
  SRr SEGS W (mkCfg (pn_ms fxc regs off mem) md) Q.
Proof.
  intros W fxc regs off mem md0 md Q regs' off' Hs0 Hst HK. unfold pn_ms.
  eapply (SRr_step SEGS (@pa_wx _ _ PA) W); [reflexivity | rewrite restrict_mkst_fx; exact Hst |].
  intros md' Hs. cbn [ms_mem YK11.mkst]. rewrite unrestrict_mkst_mrestrict.
  apply HK. eapply same_but_materialized_trans; eassumption.
Qed.

(* one hand step that also writes memory: the new memory is the restricted write put back under the hidden part; the
   memory normal form crosses the step (YSRrMemnorm.v SRr_step_inv) *)
Lemma pnE_step_m : forall (W : world SEGS) (fxc : YK11.FPState) regs off mem md0 md Q regs' off' m',
  same_but_materialized md0 md ->
  YAkMemnorm.memnorm SEGS mem ->
  RiscvSemantics.step SEGS (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + off)) (mrestrict (w_H W) mem) (YK11.seg_rom SEGS)) =
    MachineOk (@YK11.mkst fxc regs' (Z_to_bv 64 (BASE + off')) m' (YK11.seg_rom SEGS)) ->
  (forall md', same_but_materialized md0 md' -> YAkMemnorm.memnorm SEGS (munrestrict (w_H W) mem m') ->
     SRr SEGS W (mkCfg (pn_ms fxc regs' off' (munrestrict (w_H W) mem m')) md') Q) ->
  SRr SEGS W (mkCfg (pn_ms fxc regs off mem) md) Q.
Proof.
  intros W fxc regs off mem md0 md Q regs' off' m' Hs0 HPm Hst HK. unfold pn_ms.
  eapply (YC80x.SRr_step_inv SEGS (@pa_wx _ _ PA) (YAkMemnorm.memnorm SEGS)
    (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS) W);
    [reflexivity | rewrite restrict_mkst_fx; exact Hst | exact HPm |].
  intros md' Hs HPm'. exact (HK md' (same_but_materialized_trans _ _ _ Hs0 Hs) HPm').
Qed.

(* the listing word at the offset and its decoding at the registers and immediates the proof names: the decoder
   builds its bv fields with Z_to_bv's opaque well-formedness proof, so the two forms are equal only by bv_eq *)
Ltac pnE_fetch_tac off instr :=
  let e := eval vm_compute in (plookup B_prog_tpi off) in
  lazymatch e with
  | Some (PW ?w) =>
    pose proof (pnE_fetch off w ltac:(vm_compute; reflexivity)) as Hf;
    assert (Hd : decode_any (Z_to_bv 32 w) = Some (instr, 4%Z))
      by (vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]);
    assert (He : is_ecall (Z_to_bv 32 w) = false) by (vm_compute; reflexivity)
  end.

Lemma pnE_base_regs : forall en regs R Y fa c y,
  pn_base en regs Y fa c y -> pnE_frame R regs -> pn_base en R Y fa c y.
Proof.
  intros en regs R Y fa c y HB HF. unfold pn_base, pv_keep_regs in *.
  rewrite !HF by discriminate. exact HB.
Qed.

Lemma pnE_stk : forall en, 176 <= pe_STK en.
Proof.
  intros en. unfold pe_STK, STK_parse_value.
  match goal with |- 176 <= Z.of_nat ?n * ?f + ?l =>
    assert (E1 : f = 320) by reflexivity; assert (E2 : l = 16560) by reflexivity; rewrite E1, E2 end.
  assert (1 <= Z.of_nat (S (PjGrammar.MAXD - pe_d en))) by lia. nia.
Qed.

(* ---- the node's homes at entry (prhReader_at): a live allocator block, a live fake frame, the caller's window ---- *)
Lemma pnE_home : forall en, pv_pre B ARx en ->
  (exists b m0, In (b, m0) (ablocks B (pe_ly en) (pe_S en)) /\ 0 <= m0 /\ b <= pe_v en /\
     pe_v en + 56 <= b + req_size m0) \/
  (exists cid p, In (cid, p) (frames (pe_S en)) /\ frame_addr (pe_ly en) cid p <= pe_v en /\
     pe_v en + 56 <= frame_addr (pe_ly en) cid p + fs_frame_bytes cid) \/
  (pe_sp en <= pe_v en /\ pe_v en + 56 <= pe_sp en + pe_e en).
Proof.
  intros en HPRE.
  pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
  pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & _ & HLED0 & _).
  pose proof Hnode as (_ & _ & _ & _ & Hat & _).
  destruct Hat as [(a & k & Hin & Ha1 & Ha2) | [(b & m & Hin & _ & Hb1 & Hb2) | [(cid & p & Hin & Hf1 & Hf2) | Hw]]].
  - left. pose proof HLED0 as (_ & _ & HB & _).
    rewrite Forall_forall in HB. destruct (HB (a, k) Hin) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
    exists (a - cf_head), (k + cf_head). split; [exact Hblk|].
    pose proof (@cf_head_nonneg cp) as Hh0. assert (Hkh : 0 <= k + cf_head) by lia.
    pose proof (req_size_pos (k + cf_head) Hkh). split; lia.
  - left. exists b, m. split; [exact Hin|].
    pose proof (req_size_pos m ltac:(lia)). split; lia.
  - right; left. exists cid, p. auto.
  - right; right. unfold pe_sp. exact Hw.
Qed.

(* ---- the 8 bytes of v->num: where the store may write, and what it is apart from ---- *)
Lemma pnE_sep : forall en pos lyc Sc Hpc W' mem mdc k res (m : nat),
  pv_pre B ARx en ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc Hpc W' mem mdc k ->
  ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en) ++ [(res - cf_head, Z.of_nat m + 1 + cf_head)] ->
  forall x, pe_v en + 8 <= x < pe_v en + 16 ->
    (forall p n, In (p, n) (ablocks B lyc Sc) -> 0 <= n -> ~ (p <= x < p + 8)) /\
    ~ (frame_addr lyc 0 pos <= x < frame_addr lyc 0 pos + 64) /\
    ~ in_img SEGS x /\
    apresent (w_H W') mem x /\
    (awr_byte (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (ablocks B (pe_ly en) (pe_S en))
       (ablocks B lyc Sc) lyc [(0, pos)] x \/ wr_fp_frame (pe_FP en) (pe_S en) lyc x).
Proof.
  intros en pos lyc Sc Hpc W' mem mdc k res m HPRE HJ Hab x Hx.
  pose proof HPRE as (HFPRE & _).
  pose proof HFPRE as (HAFN & _).
  pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  destruct (alx_layout SEGS B ARx LAWS _ _ _ _ _ _ lyc HAR0 Hly) as (_ & Efa & _).
  pose proof (@alloc_ceiling_val rc) as (Hac & Hac4096).
  pose proof Hstk0 as (_ & HSTK0 & Hc1 & Hc2 & _).
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
  assert (HinF : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  assert (Hbl_in : forall b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) -> In (b, n) (ablocks B lyc Sc))
    by (intros b n H; rewrite Hab; apply in_or_app; left; exact H).
  assert (Hfr_in : forall cid p, In (cid, p) (frames (pe_S en)) -> In (cid, p) (frames Sc))
    by (intros cid p H; rewrite Hfrs; right; exact H).
  destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (Hfa0 & Hfac & _).
  rewrite Efb in Hfac.
  assert (HinFP : inFP (pe_FP en) x).
  { exists (pe_v en, pe_v en + 56). split; [unfold pe_FP; right; right; left; reflexivity | cbn [fst snd]; lia]. }
  unfold pe_sp in *.
  destruct (pnE_home en HPRE) as [(b & m0 & Hin & Hm0 & Hb1 & Hb2) | [(cid & p & Hin & Hf1 & Hf2) | (Hw1 & Hw2)]].
  - (* a live allocator block (b, m0) *)
    assert (HinC : In (b, m0) (ablocks B lyc Sc)) by exact (Hbl_in b m0 Hin).
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc b m0 HAR HinC) as (Hb16 & Hb4096 & Hbc & _ & Hbyt & HPW).
    split.
    { intros p n Hpn Hn0 Hr.
      destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc p n HAR Hpn) as (Hp16 & _ & _ & _ & _ & _).
      pose proof (req_size_pos n Hn0) as Hrq. pose proof (req_size_pos m0 Hm0) as Hrq0.
      destruct (Z.eq_dec p b) as [->|Hne]; [lia|].
      destruct (pnE_pw_in2 zdisjoint _ (p, req_size n) (b, req_size m0) HPW
        (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (p, n) Hpn)
        (in_map (fun b0 : Z * Z => (fst b0, req_size (snd b0))) _ (b, m0) HinC)
        ltac:(intros E; injection E; intros; lia)) as [Hd|Hd];
      unfold zdisjoint in Hd; cbn [fst snd] in Hd; lia. }
    split.
    { pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc b m0 0 pos HAR HinC HinF) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efb in Hd. lia. }
    split; [exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc b m0 x HAR HinC ltac:(lia))|].
    split; [exact (proj1 (Hbyt x ltac:(lia)))|].
    left. right; left. split; [exact HinFP|]. exists b, m0. split; [exact HinC | lia].
  - (* a live fake frame (cid, p) of the caller *)
    assert (HinC : In (cid, p) (frames Sc)) by exact (Hfr_in cid p Hin).
    rewrite <- (Efa cid p) in Hf1, Hf2.
    destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W' mem mdc cid p HAR HinC) as (Hal32 & _ & Hfbyt & _).
    split.
    { intros p0 n Hpn Hn0 Hr.
      destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc p0 n HAR Hpn) as (Hp16 & _ & _ & _ & _ & _).
      pose proof (req_size_pos n Hn0) as Hrq.
      pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc p0 n cid p HAR Hpn HinC) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
    split.
    { destruct (in_split _ _ Hin) as (l2 & l3 & El).
      pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc (0, pos) (cid, p) [] l2 l3 HAR
        ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Efb in Hd. lia. }
    split; [exact (frm_img_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc cid p x HAR HinC ltac:(lia))|].
    split; [exact (proj1 (Hfbyt x ltac:(lia)))|].
    right. split; [exact HinFP|]. exists cid, p. split; [exact Hin|].
    unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - (* the caller's window, at or above alloc_ceiling *)
    unfold pe_sp in Hw1, Hw2. split.
    { intros p n Hpn Hn0 Hr.
      destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc p n HAR Hpn) as (_ & _ & Hpc' & _).
      pose proof (req_size_pos n Hn0) as Hrq. lia. }
    split; [lia|].
    split; [intros Hi; pose proof (pa_segs_low x Hi); lia|].
    split; [apply Hpres; lia|].
    left. left. lia.
Qed.

Definition pnE_mem1 (H : word -> bool) (mem : word -> option byte) (v bits : Z) : word -> option byte :=
  munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 (v + 8)) (word_to_le_bytes 8 (Z_to_bv 64 bits))).

(* ---- every fact of the cut across the store v->num := bits ---- *)
Lemma pnE_post : forall en W' mem Y fa fl pos lyc Sc Hpc k (m : nat) res p1 bits mdc md',
  pv_pre B ARx en ->
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W' mem mdc k ->
  pn_ok B en m res lyc Sc Hpc W' mem ->
  pn_reader en p1 W' mem (fun a => pe_v en + 16 <= a < pe_v en + 24) ->
  same_but_materialized mdc md' ->
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W' (pnE_mem1 (w_H W') mem (pe_v en) bits) md' k /\
  pn_ok B en m res lyc Sc Hpc W' (pnE_mem1 (w_H W') mem (pe_v en) bits) /\
  pn_reader en p1 W' (pnE_mem1 (w_H W') mem (pe_v en) bits) (fun a => pe_v en + 8 <= a < pe_v en + 24) /\
  val_mem SEGS (rdW W' (pnE_mem1 (w_H W') mem (pe_v en) bits)) (pe_v en + 8) 8 bits /\
  (forall a (n : nat) vv,
     (forall j, 0 <= j < Z.of_nat n -> 0 <= a + j < 2 ^ 64 /\ (a + j < pe_v en + 8 \/ pe_v en + 16 <= a + j)) ->
     val_mem SEGS (rdW W' mem) a n vv -> val_mem SEGS (rdW W' (pnE_mem1 (w_H W') mem (pe_v en) bits)) a n vv) /\
  (forall a l,
     (forall j, 0 <= j < Z.of_nat (length l) -> 0 <= a + j < 2 ^ 64 /\ (a + j < pe_v en + 8 \/ pe_v en + 16 <= a + j)) ->
     garr8 SEGS (rdW W' mem) a l -> garr8 SEGS (rdW W' (pnE_mem1 (w_H W') mem (pe_v en) bits)) a l).
Proof.
  intros en W' mem Y fa fl pos lyc Sc Hpc k m res p1 bits mdc md' HPRE HBODY HOK HRD Hsame.
  set (mem1 := pnE_mem1 (w_H W') mem (pe_v en) bits).
  pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
  pose proof HFPRE as (HAFN & _).
  pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
  pose proof HRDP as (_ & _ & _ & _ & _ & Hwin & Hqlo & Hqhi & _ & _ & _ & _ & Hnode & Hqv & Htv & _).
  pose proof Hnode as (Hv4096 & Hv8 & _ & _ & _ & Hvam & Hvown & _).
  pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof HOK as (Hcf & Hres0 & Hres16 & HresL & Hres64 & HresNB & HresV & EHp & Hab & HRA & HHV & HLED).
  pose proof HRD as (HINOK & HSRC & HNODE & HVRA).
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof (@alloc_ceiling_val rc) as (Hac & Hac4096).
  pose proof (pnE_stk en) as HSTK.
  pose proof Hstk0 as (Hsp16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _ & Hc5 & Hc6).
  pose proof Hwin as (He0 & He16 & Hetop & _).
  pose proof (pnE_sep en pos lyc Sc Hpc W' mem mdc k res m HPRE HJ Hab) as SEP.
  assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
  destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (Hfa0 & Hfac & _).
  rewrite <- Efa in Hfa0, Hfac. rewrite Efb in Hfac.
  unfold amem_range in Hvam. unfold pe_sp in *.
  set (sp0 := spZ (pe_regs en)) in *. set (v := pe_v en) in *.
  assert (Ev : v = pe_v en) by reflexivity.
  assert (Esp0 : sp0 = pe_sp en) by reflexivity.
  assert (Esp1 : sp0 = spZ (pe_regs en)) by reflexivity.
  assert (Hbl : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 bits))) = 8)
    by (unfold word_to_le_bytes; rewrite length_Z_to_le_bytes; reflexivity).
  assert (Hvr : 4096 <= v /\ v + 56 <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (KEEP : forall z, 0 <= z < 2 ^ 64 -> (z < v + 8 \/ v + 16 <= z) ->
                   aview SEGS (w_H W') mem1 z = aview SEGS (w_H W') mem z).
  { intros z Hz Hout. unfold mem1, pnE_mem1. apply pnE_aview_out; rewrite ?Hbl; lia. }
  assert (GROW : mem_grows (mrestrict (w_H W') mem) (mrestrict (w_H W') mem1))
    by (unfold mem1, pnE_mem1; apply pnE_wb_grow; rewrite ?Hbl; lia).
  assert (KVb : forall a (n : nat) vv,
     (forall j, 0 <= j < Z.of_nat n -> 0 <= a + j < 2 ^ 64 /\ (a + j < v + 8 \/ v + 16 <= a + j)) ->
     val_mem SEGS (rdW W' mem) a n vv -> val_mem SEGS (rdW W' mem1) a n vv).
  { intros a n vv Hj Hv. apply (val_mem_kept SEGS (w_H W') (w_H W') mem mem1 a n vv); [|exact Hv].
    intros j Hjr. destruct (Hj j Hjr) as [Hj1 Hj2]. exact (KEEP (a + j) Hj1 Hj2). }
  assert (KGb : forall a l,
     (forall j, 0 <= j < Z.of_nat (length l) -> 0 <= a + j < 2 ^ 64 /\ (a + j < v + 8 \/ v + 16 <= a + j)) ->
     garr8 SEGS (rdW W' mem) a l -> garr8 SEGS (rdW W' mem1) a l).
  { intros a l Hj Hg jj Hjj. destruct (Hg jj Hjj) as [Hv Hr]. split; [|exact Hr].
    apply KVb; [|exact Hv]. intros j Hj1. cbn in Hj1. assert (j = 0) by lia. subst j.
    rewrite Z.add_0_r. exact (Hj (Z.of_nat jj) ltac:(lia)). }
  (* the shadow band is apart from the node (application memory) *)
  assert (SHO : forall z, 0 <= z < 2 ^ 47 -> 0 <= SHADOW_OFF + z / 8 < 2 ^ 64 /\
                  (SHADOW_OFF + z / 8 < v + 8 \/ v + 16 <= SHADOW_OFF + z / 8)).
  { intros z Hz. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
  assert (KRA : forall a n, 0 <= a -> a + n <= 2 ^ 47 ->
     range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF a n ->
     range_addressable (aview SEGS (w_H W') mem1) SHADOW_OFF a n).
  { intros a n Ha Hn HR z Hz. destruct (HR z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite <- Hs. unfold shadow_of_addr. destruct (SHO z ltac:(lia)) as [S1 S2]. exact (KEEP _ S1 S2). }
  assert (KHV : forall a n, shadow_hull_vis (aview SEGS (w_H W') mem) a n ->
     shadow_hull_vis (aview SEGS (w_H W') mem1) a n).
  { intros a n H s Hs. exact (aview_keeps_vis SEGS _ _ _ _ GROW (H s Hs)). }
  (* the real frame is in parse_value's stack window, which the node avoids *)
  assert (RFR : forall z, sp0 - 176 <= z < sp0 -> 0 <= z < 2 ^ 64 /\ (z < v + 8 \/ v + 16 <= z)).
  { intros z Hz. split; [lia|].
    destruct (Z_lt_le_dec z (v + 8)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec z (v + 16)) as [H2|H2]; [|right; exact H2].
    exfalso. destruct (Hvown z ltac:(lia)) as [_ Hn]. apply Hn. lia. }
  (* the fake frame *)
  assert (FFR : forall z, fa <= z < fa + 64 -> 0 <= z < 2 ^ 64 /\ (z < v + 8 \/ v + 16 <= z)).
  { intros z Hz. split; [lia|].
    destruct (Z_lt_le_dec z (v + 8)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec z (v + 16)) as [H2|H2]; [|right; exact H2].
    exfalso. destruct (SEP z ltac:(lia)) as (_ & Hn & _). apply Hn. rewrite <- Efa. lia. }
  split.
  { (* pv_body *)
    pose proof HFRM as (HY1 & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
    split.
    { split; [exact HY1|]. split; [exact HY32|].
      split; [intros a Ha; exact (apresent_grows _ _ _ _ GROW (HPR0 a Ha))|].
      split.
      { rewrite Forall_forall in Vsav |- *. intros oc Hoc. pose proof (pnE_saved_rng oc Hoc) as Hr.
        apply KVb; [intros j Hj; apply RFR; cbn in Hj; lia | exact (Vsav oc Hoc)]. }
      split; [apply KVb; [intros j Hj; apply RFR; cbn in Hj; lia | exact Vfa48]|].
      split; [apply KVb; [intros j Hj; apply FFR; cbn in Hj; lia | exact Vmagic]|].
      split; [apply KVb; [intros j Hj; apply FFR; cbn in Hj; lia | exact Vdesc]|].
      split; [apply KVb; [intros j Hj; apply FFR; cbn in Hj; lia | exact Vpc]|].
      split; [apply KVb; [intros j Hj; apply FFR; cbn in Hj; lia | exact Vfl]|].
      split; [intros a Ha; exact (apresent_grows _ _ _ _ GROW (HPRfa a Ha))|].
      split; [exact Hshlen|].
      apply KGb; [|exact Gsh]. rewrite Hshlen. intros j Hj.
      replace (SHADOW_OFF + fa / 8 + j) with (SHADOW_OFF + (fa + 8 * j) / 8).
      - apply SHO. lia.
      - replace (fa + 8 * j) with (fa + j * 8) by lia. rewrite Z.div_add by lia. lia. }
    split; [exact HinF|]. split; [exact Efa|]. split; [exact Efl|].
    split.
    { apply (ajournal_x_exec_fr (SK := SK) SEGS B (@prh_pst prh_img_B) ARx LAWS (@pa_segs_low _ _ PA)
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem1 md' (fun a => v + 8 <= a < v + 16) HJ).
      - intros x Hx. unfold mem1, pnE_mem1. apply pnE_wb_out; rewrite ?Hbl; [lia | lia |]. lia.
      - exact GROW.
      - intros x Hx. unfold mem1, pnE_mem1. apply pnE_wb_hid. exact Hx.
      - exact Hsame.
      - intros a Ha. exact (proj2 (proj2 (proj2 (proj2 (SEP a Ha))))). }
    intros a Ha Hnf. rewrite <- (HWIN a Ha Hnf). apply KEEP; [lia|].
    destruct (Z_lt_le_dec a (v + 8)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec a (v + 16)) as [H2|H2]; [|right; exact H2].
    exfalso. apply Hnf. exists (v, v + 56). split; [unfold pe_FP; right; right; left; reflexivity | cbn [fst snd]; lia]. }
  (* the new block's bounds *)
  assert (HinN : In (res - cf_head, Z.of_nat m + 1 + cf_head) (ablocks B lyc Sc))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  pose proof (@cf_head_nonneg cp) as Hh0.
  destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ HAR HinN) as (_ & HN4096 & HNc & _).
  assert (HNreq : req_size (Z.of_nat m + 1 + cf_head) = Z.of_nat m + 1 + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat m + 1 + cf_head) 0); lia).
  rewrite HNreq in HNc.
  split.
  { (* pn_ok *)
    unfold pn_ok. cbv zeta. do 9 (split; [assumption|]).
    split; [apply KRA; [lia | lia | exact HRA]|].
    split; [apply KHV; exact HHV|].
    destruct HLED as (HG & HND & HHB & HPM).
    split; [|split; [exact HND | split; [|exact HPM]]].
    - assert (KST : forall a n vv, Exists (fun r => fst r = a /\ snd r = Z.of_nat n) (@prh_pst prh_img_B) ->
                      val_mem SEGS (rdW W' mem) a n vv -> val_mem SEGS (rdW W' mem1) a n vv).
      { intros a n vv Hex Hv. apply KVb; [|exact Hv]. intros j Hj.
        assert (Hin : Exists (in_zr (a + j)) (@prh_pst prh_img_B)).
        { apply Exists_exists in Hex as (r & Hr & Ha & Hn). apply Exists_exists. exists r. split; [exact Hr|].
          unfold in_zr. lia. }
        destruct (PSTOK _ Hin) as [Himg _]. pose proof (pa_segs_low _ Himg) as Hlo.
        split; [unfold kLowMemEnd in Hlo; lia|].
        destruct (Z_lt_le_dec (a + j) (v + 8)) as [H1|H1]; [left; exact H1|].
        destruct (Z_lt_le_dec (a + j) (v + 16)) as [H2|H2]; [|right; exact H2].
        exfalso. destruct (SEP (a + j) ltac:(lia)) as (_ & _ & Hn & _). exact (Hn Himg). }
      destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & R6) & (G7 & R7) & Grest).
      split; [apply KST; [|exact G1]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [apply KST; [|exact G2]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [apply KST; [|exact G3]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [apply KST; [|exact G4]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [apply KST; [|exact G5]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [split; [apply KST; [|exact G6]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl]) | exact R6]|].
      split; [split; [apply KST; [|exact G7]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl]) | exact R7]|].
      exact Grest.
    - rewrite Forall_forall in HHB |- *. intros ak Hak.
      destruct (HHB ak Hak) as (Hk & Hblk & Hhp & Hal & Hv).
      split; [exact Hk|]. split; [exact Hblk|]. split; [exact Hhp|]. split; [exact Hal|].
      destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ HAR Hblk) as (_ & Hb4096 & Hbc & _).
      assert (Hkh : 0 <= snd ak + cf_head) by lia.
      pose proof (req_size_pos (snd ak + cf_head) Hkh) as Hrq.
      apply KVb; [|exact Hv]. intros j Hj. cbn in Hj. split; [lia|].
      destruct (Z_lt_le_dec (fst ak - cf_head + j) (v + 8)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec (fst ak - cf_head + j) (v + 16)) as [H2|H2]; [|right; exact H2].
      exfalso. assert (Hz : v + 8 <= fst ak - cf_head + j < v + 16) by lia.
      destruct (SEP _ Hz) as (Hn & _). apply (Hn _ _ Hblk); lia. }
  split.
  { (* pn_reader *)
    unfold pn_reader. cbv zeta. split; [|split; [|split]].
    - pose proof HINOK as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12).
      split; [apply KVb; [intros j Hj; cbn in Hj; lia | exact P1]|].
      split; [apply KVb; [intros j Hj; cbn in Hj; lia | exact P2]|].
      split; [apply KVb; [intros j Hj; cbn in Hj; lia | exact P3]|].
      split; [intros x Hx; exact (writable_at_grows SEGS _ _ x GROW (P4 x Hx))|].
      do 5 (split; [assumption|]).
      split; [apply KGb; [intros j Hj; lia | exact P10]|].
      split; assumption.
    - pose proof HSRC as (S1 & S2 & S3 & S4 & S5 & S6).
      pose proof HINOK as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _).
      split; [apply KGb; [intros j Hj; lia | exact S1]|].
      do 3 (split; [assumption|]).
      split; [apply KRA; [lia | lia | exact S5]|].
      intros Hl. apply KHV. exact (S6 Hl).
    - intros a Ha Hnw. rewrite <- (HNODE a Ha ltac:(intros H; apply Hnw; lia)). apply KEEP; lia.
    - apply KRA; [lia | lia | exact HVRA]. }
  split.
  { intros kk Hkk. unfold mem1, pnE_mem1. apply pnE_wb_in; [lia | lia | exact Hkk |].
    destruct (SEP (v + 8 + Z.of_nat kk) ltac:(lia)) as (_ & _ & _ & (Hh & _) & _). exact Hh. }
  split; [exact KVb | exact KGb].
Qed.

(* ======== sub-piece E ======== *)
Lemma pnE : pnE_stmt B ARx.
Proof.
  intros en HPRE KT KC W2 ms2 md2 HR.
  unfold pn_at_R in HR. cbv zeta in HR.
  destruct HR as (fx' & regs & mem & Y & fa & fl & pos & lyc & Sc & Hpc & k & c & y & m & res & bits & cn &
    Ems & HFZ & HFK & HBASE & HBODY & HOK & Hfrs & HROOM & HRD & Mstr & Gres & HSTR & Hcn & Mend & FA0 &
    R25 & R22 & R21 & HLEAD & Hm & HSPAN & HSTOP & HQP & HMN).
  subst ms2.
  pose proof HPRE as (HFPRE & HCTX & _ & _ & HCHN & HQCH & Hq10 & Hv11 & HRDP & HROOMp & HFRB & _).
  pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _).
  pose proof Hnode as (Hv4096 & Hv8 & _ & _ & _ & Hvam & _ & _).
  pose proof HBASE as (HKR & R9 & R19 & R20 & R24 & Hskip & Hc123 & Hc91 & Hc34 & Hc116 & Hc102 & Hc110).
  pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
  pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
  pose proof HJ as (HAR & _).
  pose proof HOK as (Hcf & Hres0 & Hres16 & HresL & Hres64 & HresNB & HresV & EHp & Hab & HRA & HHV & HLED).
  pose proof HRD as (HINOK & HSRC & HNODE & HVRA).
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof (@alloc_ceiling_val rc) as (Hac & Hac4096).
  pose proof (@cf_head_nonneg cp) as Hh0.
  unfold amem_range in Hvam.
  assert (Hvr : 4096 <= pe_v en /\ pe_v en + 56 <= 2 ^ 47) by (unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  (* the new block and the fake frame: their bounds *)
  assert (HinN : In (res - cf_head, Z.of_nat m + 1 + cf_head) (ablocks B lyc Sc))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W2 mem md2 _ _ HAR HinN) as (_ & HN4096 & HNc & _).
  assert (HNreq : req_size (Z.of_nat m + 1 + cf_head) = Z.of_nat m + 1 + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat m + 1 + cf_head) 0); lia).
  rewrite HNreq in HNc.
  destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W2 mem md2 0 pos HAR HinF) as (Hfa0 & Hfac & _).
  rewrite <- Efa in Hfa0, Hfac. change (fs_frame_bytes 0) with 64 in Hfac.
  (* the text strtod read *)
  assert (Hltxt : length (firstn m (c :: y)) = m) by (rewrite length_firstn; lia).
  assert (Htxtn : Forall (fun z => PjGrammar.numch z = true) (firstn m (c :: y)))
    by (apply pnE_txt_numch; [lia | exact HSPAN]).
  assert (FA0' : LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx') 10%bv = Z_to_bv 64 bits)
    by (rewrite <- FA0; f_equal; apply bv_eq; reflexivity).
  (* the cut across the store v->num := bits *)
  pose proof (pnE_post en W2 mem Y fa fl pos lyc Sc Hpc k m res _ bits md2 md2 HPRE HBODY HOK HRD
    (same_but_materialized_refl md2)) as (_ & OK1 & RD1 & NUM1 & KV1 & KG1).
  set (mem1 := pnE_mem1 (w_H W2) mem (pe_v en) bits) in *.
  assert (POST : forall md', same_but_materialized md2 md' ->
     pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W2 mem1 md' k)
    by (intros md' Hs; exact (proj1 (pnE_post en W2 mem Y fa fl pos lyc Sc Hpc k m res _ bits md2 md' HPRE HBODY HOK HRD Hs))).
  assert (Mstr1 : val_mem SEGS (rdW W2 mem1) (pe_v en + 16) 8 res).
  { apply KV1; [|exact Mstr]. intros j Hj. cbn in Hj. lia. }
  assert (Gres1 : garr8 SEGS (rdW W2 mem1) res (firstn m (c :: y) ++ [0])).
  { apply KG1; [|exact Gres]. intros j Hj. rewrite length_app, Hltxt in Hj. cbn [length] in Hj.
    split; [lia|]. destruct (Z_lt_le_dec (res + j) (pe_v en + 8)) as [H1|H1]; [left; exact H1|].
    right. destruct (Z_lt_le_dec (res + j) (pe_v en + 16)) as [H2|H2]; [|exact H2].
    exfalso. apply (HresV (res + j)); lia. }
  (* the two exits *)
  lazymatch goal with |- SRr _ _ _ ?Q =>
  assert (TOUT : forall R md', same_but_materialized md2 md' -> pnE_frame R regs ->
            YStrtodRowX.aj_memnorm SEGS mem1 ->
            (cn <> Z.of_nat m \/ PjGrammar.finite bits = false) ->
            SRr SEGS W2 (mkCfg (pn_ms fx' R 20928 mem1) md') Q);
  [|assert (COUT : forall R md', same_but_materialized md2 md' -> pnE_frame R regs ->
            YStrtodRowX.aj_memnorm SEGS mem1 ->
            cn = Z.of_nat m -> PjGrammar.finite bits = true ->
            SRr SEGS W2 (mkCfg (pn_ms fx' R 20888 mem1) md') Q)] end.
  { intros R md' Hs HFR HMN1 Hout. apply KT. unfold pn_at_T.
    exists fx', R, mem1, Y, fa, fl, pos, lyc, Sc, Hpc, k, (-1).
    split; [reflexivity|]. split; [exact HFZ|]. split; [exact HFK|].
    split; [exact (proj1 (pnE_base_regs en regs R Y fa c y HBASE HFR))|].
    split; [rewrite (HFR 21%bv) by discriminate; exact R21|].
    split; [exact (POST md' Hs)|]. split; [|exact HMN1].
    unfold pn_out. exists c, y. cbv zeta.
    split; [exact Hskip|]. do 6 (split; [assumption|]).
    right; right; left. split; [reflexivity|]. split; [exact HLEAD|].
    exists m, res, bits, cn.
    split; [exact Hm|]. split; [exact HSPAN|]. split; [exact HSTOP|]. split; [exact OK1|].
    split; [exact Hfrs|]. split; [exact HROOM|]. split; [exact HQP|]. split; [exact RD1|].
    split; [exact Mstr1|]. split; [exact NUM1|]. split; [exact Gres1|].
    split; [exact HSTR|]. split; [exact Hcn|]. exact Hout. }
  { intros R md' Hs HFR HMN1 Ecn Hfin. apply KC. unfold pn_at_C. cbv zeta.
    exists fx', R, mem1, Y, fa, fl, pos, lyc, Sc, Hpc, k, c, y, m, res, bits.
    split; [reflexivity|]. split; [exact HFZ|]. split; [exact HFK|].
    split; [exact (pnE_base_regs en regs R Y fa c y HBASE HFR)|].
    split; [exact (POST md' Hs)|]. split; [exact OK1|]. split; [exact Hfrs|]. split; [exact HROOM|].
    split; [exact RD1|]. split; [exact Mstr1|]. split; [exact NUM1|]. split; [exact Gres1|].
    split; [rewrite <- Ecn; exact HSTR|]. split; [exact Hfin|].
    split; [rewrite (HFR 22%bv) by discriminate; exact R22|].
    split; [rewrite (HFR 21%bv) by discriminate; exact R21|].
    split; [exact HLEAD|]. split; [exact Hm|]. split; [exact HSPAN|]. split; [exact HSTOP|].
    split; [exact HQP | exact HMN1]. }
  (* ---- 0x8681c addi a1,s3,8 ---- *)
  set (R1 := YK11.regupd regs 11%bv (w64 (pe_v en + 8))).
  pnE_fetch_tac 20816 (OpImm ALU_ADD 11%bv 19%bv 8%bv).
  apply (pnE_step W2 fx' regs 20816 mem md2 md2 _ R1 20820 (same_but_materialized_refl md2)).
  { rewrite (step_addi _ _ _ _ _ _ _ _ _ Hf He Hd), R19, pnE_next. pnE_bvs. unfold w64.
    rewrite YCbn.v_addi_lit. reflexivity. }
  clear Hf He Hd. intros md3 Hsm3.
  assert (A1_11 : getr R1 11%bv = w64 (pe_v en + 8)) by (unfold R1; apply getr_same; discriminate).
  assert (HF1 : pnE_frame R1 regs)
    by (unfold R1; apply pnE_frame_upd; [right; left; reflexivity | apply pnE_frame_refl]).
  clearbody R1.
  (* ---- 0x86820 srli a0,a1,3 ---- *)
  set (R2' := YK11.regupd R1 10%bv (w64 ((pe_v en + 8) / 8))).
  pnE_fetch_tac 20820 (ShiftImm ALU_SRL 10%bv 11%bv 3%bv).
  apply (pnE_step W2 fx' R1 20820 mem md2 md3 _ R2' 20824 Hsm3).
  { rewrite (step_srli _ _ _ _ _ _ _ _ _ Hf He Hd), A1_11, pnE_next. unfold YK11.v_srli, w64.
    rewrite YK00.u64_lit by lia. rewrite Z.shiftr_div_pow2 by (vm_compute; discriminate).
    replace (2 ^ bv_unsigned (3%bv : bv 6)) with 8 by (vm_compute; reflexivity). reflexivity. }
  clear Hf He Hd. intros md4 Hsm4.
  assert (A2_10 : getr R2' 10%bv = w64 ((pe_v en + 8) / 8)) by (unfold R2'; apply getr_same; discriminate).
  assert (A2_11 : getr R2' 11%bv = w64 (pe_v en + 8))
    by (unfold R2'; rewrite getr_other by discriminate; exact A1_11).
  assert (HF2 : pnE_frame R2' regs) by (unfold R2'; apply pnE_frame_upd; [left; reflexivity | exact HF1]).
  clearbody R2'.
  (* ---- 0x86824 add a0,a0,s7 ---- *)
  set (R3' := YK11.regupd R2' 10%bv (w64 ((pe_v en + 8) / 8 + SHADOW_OFF))).
  pnE_fetch_tac 20824 (Op ALU_ADD 10%bv 10%bv 23%bv).
  apply (pnE_step W2 fx' R2' 20824 mem md2 md4 _ R3' 20828 Hsm4).
  { rewrite (step_add _ _ _ _ _ _ _ _ _ Hf He Hd), A2_10, (HF2 23%bv) by discriminate.
    rewrite R23, pnE_next. unfold YK11.v_add, w64. rewrite !YK00.u64_lit by (unfold SHADOW_OFF; lia).
    reflexivity. }
  clear Hf He Hd. intros md5 Hsm5.
  assert (A3_10 : getr R3' 10%bv = w64 ((pe_v en + 8) / 8 + SHADOW_OFF))
    by (unfold R3'; apply getr_same; discriminate).
  assert (A3_11 : getr R3' 11%bv = w64 (pe_v en + 8))
    by (unfold R3'; rewrite getr_other by discriminate; exact A2_11).
  assert (HF3 : pnE_frame R3' regs) by (unfold R3'; apply pnE_frame_upd; [left; reflexivity | exact HF2]).
  clearbody R3'.
  (* ---- 0x86828 lbu a0,0(a0): shadow(v + 8) is 0 (the node is addressable and 8-aligned) ---- *)
  destruct (HVRA (pe_v en + 15) ltac:(lia)) as (s0 & Hs0v & Hs0ok).
  assert (Es0 : s0 = 0) by (unfold saddr_ok in Hs0ok; lia).
  subst s0.
  assert (Esh : shadow_of_addr SHADOW_OFF (pe_v en + 15) = (pe_v en + 8) / 8 + SHADOW_OFF)
    by (unfold shadow_of_addr; lia).
  rewrite Esh in Hs0v. unfold aview in Hs0v.
  destruct (mbyte SEGS (mrestrict (w_H W2) mem) ((pe_v en + 8) / 8 + SHADOW_OFF)) as [sb|] eqn:Esb;
    [|discriminate Hs0v].
  cbn [option_map] in Hs0v. injection Hs0v as Hsb.
  assert (Hrd4 : rdn SEGS (mrestrict (w_H W2) mem) (Z_to_bv 64 ((pe_v en + 8) / 8 + SHADOW_OFF)) 1 = Some [sb]).
  { apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
    cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Esb. }
  set (R4' := YK11.regupd R3' 10%bv (w64 0)).
  pnE_fetch_tac 20828 (Load SZ1 false 10%bv 10%bv 0%bv).
  apply (pnE_step W2 fx' R3' 20828 mem md2 md5 _ R4' 20832 Hsm5).
  { rewrite (step_lbu _ _ _ _ _ _ _ _ _ sb Hf He Hd).
    - rewrite Hsb, pnE_next. reflexivity.
    - rewrite A3_10. unfold w64. rewrite YCbn.v_addi_lit. pnE_bvs. rewrite Z.add_0_r. exact Hrd4. }
  clear Hf He Hd. intros md6 Hsm6.
  assert (A4_10 : getr R4' 10%bv = w64 0) by (unfold R4'; apply getr_same; discriminate).
  assert (A4_11 : getr R4' 11%bv = w64 (pe_v en + 8))
    by (unfold R4'; rewrite getr_other by discriminate; exact A3_11).
  assert (HF4 : pnE_frame R4' regs) by (unfold R4'; apply pnE_frame_upd; [left; reflexivity | exact HF3]).
  clearbody R4'.
  (* ---- 0x8682c bnez a0 -> 0x86938 (report): not taken ---- *)
  pnE_fetch_tac 20832 (Branch BC_NE 10%bv 0%bv 268%bv).
  apply (pnE_step W2 fx' R4' 20832 mem md2 md6 _ R4' 20836 Hsm6).
  { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_next; reflexivity|].
    rewrite A4_10, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. reflexivity. }
  clear Hf He Hd. intros md7 Hsm7.
  (* ---- 0x86830 ld a0,0(s9): end = res + cn ---- *)
  destruct (word_mem_ld SEGS (mrestrict (w_H W2) mem) (fa + 32) (res + cn)
    (proj1 (val_mem_word_mem _ _ _ _) Mend) ltac:(lia) ltac:(lia)) as (bs6 & Hrd6 & Hbs6).
  set (R6 := YK11.regupd R4' 10%bv (w64 (res + cn))).
  pnE_fetch_tac 20836 (Load SZ8 true 10%bv 25%bv 0%bv).
  apply (pnE_step W2 fx' R4' 20836 mem md2 md7 _ R6 20840 Hsm7).
  { rewrite (step_ld _ _ _ _ _ _ _ _ _ bs6 (w64 (res + cn)) Hf He Hd); [rewrite pnE_next; reflexivity | | exact Hbs6].
    rewrite (HF4 25%bv) by discriminate. rewrite R25. unfold w64. rewrite YCbn.v_addi_lit. pnE_bvs.
    rewrite Z.add_0_r. exact Hrd6. }
  clear Hf He Hd. intros md8 Hsm8.
  assert (A6_10 : getr R6 10%bv = w64 (res + cn)) by (unfold R6; apply getr_same; discriminate).
  assert (A6_11 : getr R6 11%bv = w64 (pe_v en + 8))
    by (unfold R6; rewrite getr_other by discriminate; exact A4_11).
  assert (HF6 : pnE_frame R6 regs) by (unfold R6; apply pnE_frame_upd; [left; reflexivity | exact HF4]).
  clearbody R6.
  (* ---- 0x86834 fsd fa0,0(a1): v->num := bits ---- *)
  pnE_fetch_tac 20840 (FStore FMT_D 11%bv 10%bv 0%bv).
  apply (pnE_step_m W2 fx' R6 20840 mem md2 md8 _ R6 20844
    (wbytes (mrestrict (w_H W2) mem) (Z_to_bv 64 (pe_v en + 8)) (word_to_le_bytes 8 (Z_to_bv 64 bits))) Hsm8 HMN).
  { rewrite (fp_step_fsd fx' _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (pe_v en + 8)) Hf He Hd).
    - rewrite FA0', pnE_next. reflexivity.
    - rewrite A6_11. unfold w64. rewrite YCbn.v_addi_lit. pnE_bvs. rewrite Z.add_0_r. reflexivity.
    - apply pnE_store_ok; [| lia | lia]. intros i Hi.
      assert (Hxi : pe_v en + 8 <= pe_v en + 8 + i < pe_v en + 16) by lia.
      destruct (pnE_sep en pos lyc Sc Hpc W2 mem md2 k res m HPRE HJ Hab _ Hxi) as (_ & _ & _ & (Hh & b0 & Hb0) & _).
      unfold mrestrict. rewrite Hh, Hb0. discriminate. }
  clear Hf He Hd. intros md9 Hsm9 HMN1.
  change (munrestrict (w_H W2) mem (wbytes (mrestrict (w_H W2) mem) (Z_to_bv 64 (pe_v en + 8))
    (word_to_le_bytes 8 (Z_to_bv 64 bits)))) with mem1.
  change (munrestrict (w_H W2) mem (wbytes (mrestrict (w_H W2) mem) (Z_to_bv 64 (pe_v en + 8))
    (word_to_le_bytes 8 (Z_to_bv 64 bits)))) with mem1 in HMN1.
  (* ---- 0x86838 beqz a0 -> 0x86898 (report): end is not NULL ---- *)
  pnE_fetch_tac 20844 (Branch BC_EQ 10%bv 0%bv 96%bv).
  apply (pnE_step W2 fx' R6 20844 mem1 md2 md9 _ R6 20848 Hsm9).
  { rewrite (step_beq_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_next; reflexivity|].
    rewrite A6_10, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. apply Z.eqb_neq. lia. }
  clear Hf He Hd. intros md10 Hsm10.
  (* ---- the tail from 0x8684c, reached with a0 = end by both sides of the shadow check ---- *)
  lazymatch goal with |- SRr _ _ _ ?Q =>
  assert (TAIL : forall R md', same_but_materialized md2 md' -> pnE_frame R regs ->
            getr R 10%bv = w64 (res + cn) -> SRr SEGS W2 (mkCfg (pn_ms fx' R 20864 mem1) md') Q) end.
  { intros R md' Hsm' HFR A10.
    (* 0x8684c lbu a0,0(a0) *)
    set (e := nth (Z.to_nat cn) (firstn m (c :: y) ++ [0]) 0).
    destruct (Gres1 (Z.to_nat cn) ltac:(rewrite length_app, Hltxt; cbn [length]; lia)) as [Hve Hre].
    fold e in Hve, Hre. rewrite Z2Nat.id in Hve by lia.
    assert (Hrd8 : rdn SEGS (mrestrict (w_H W2) mem1) (Z_to_bv 64 (res + cn)) 1 = Some [Z_to_bv 8 (le_byte e 1 0)]).
    { apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
      rewrite (Hve 0%nat ltac:(lia)). reflexivity. }
    set (R8' := YK11.regupd R 10%bv (w64 e)).
    pnE_fetch_tac 20864 (Load SZ1 false 10%bv 10%bv 0%bv).
    apply (pnE_step W2 fx' R 20864 mem1 md2 md' _ R8' 20868 Hsm').
    { rewrite (step_lbu _ _ _ _ _ _ _ _ _ (Z_to_bv 8 (le_byte e 1 0)) Hf He Hd).
      - rewrite pnE_byte by exact Hre. rewrite pnE_next. reflexivity.
      - rewrite A10. unfold w64. rewrite YCbn.v_addi_lit. pnE_bvs. rewrite Z.add_0_r. exact Hrd8. }
    clear Hf He Hd. intros md8' Hsm8'.
    assert (A8 : getr R8' 10%bv = w64 e) by (unfold R8'; apply getr_same; discriminate).
    assert (HF8 : pnE_frame R8' regs) by (unfold R8'; apply pnE_frame_upd; [left; reflexivity | exact HFR]).
    clearbody R8'.
    assert (Hcn' : 0 <= cn <= Z.of_nat (length (firstn m (c :: y)))) by (rewrite Hltxt; lia).
    pose proof (pnE_end_byte _ cn Htxtn Hcn') as HEB. fold e in HEB. rewrite Hltxt in HEB.
    (* 0x86850 bnez a0 -> T: strtod stopped short of the text's end *)
    pnE_fetch_tac 20868 (Branch BC_NE 10%bv 0%bv 60%bv).
    destruct (Z.eqb_spec cn (Z.of_nat m)) as [Ecn | Ecn].
    2: {
      apply (pnE_step W2 fx' R8' 20868 mem1 md2 md8' _ R8' 20928 Hsm8').
      { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_btgt; reflexivity|].
        rewrite A8, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. exact HEB. }
      intros md9' Hsm9'. exact (TOUT R8' md9' Hsm9' HF8 HMN1 (or_introl Ecn)). }
    apply (pnE_step W2 fx' R8' 20868 mem1 md2 md8' _ R8' 20872 Hsm8').
    { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_next; reflexivity|].
      rewrite A8, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. exact HEB. }
    clear Hf He Hd. intros md9' Hsm9'.
    (* 0x86854 fclass.d a0,fa0 *)
    set (K := fp_class fmt_double (bits mod 2 ^ 64)).
    pose proof (pnE_fclass_range (bits mod 2 ^ 64)) as HKr. fold K in HKr.
    set (R10' := YK11.regupd R8' 10%bv (w64 K)).
    pnE_fetch_tac 20872 (Fclass FMT_D 10%bv 10%bv).
    apply (pnE_step W2 fx' R8' 20872 mem1 md2 md9' _ R10' 20876 Hsm9').
    { rewrite (fp_step_fclass_d fx' _ _ _ _ _ _ _ _ Hf He Hd). rewrite FA0', Z_to_bv_unsigned, pnE_next. reflexivity. }
    clear Hf He Hd. intros md10' Hsm10'.
    assert (A10' : getr R10' 10%bv = w64 K) by (unfold R10'; apply getr_same; discriminate).
    assert (HF10 : pnE_frame R10' regs) by (unfold R10'; apply pnE_frame_upd; [left; reflexivity | exact HF8]).
    clearbody R10'.
    (* 0x86858 andi a0,a0,897 *)
    set (R11' := YK11.regupd R10' 10%bv (w64 (Z.land K 897))).
    pnE_fetch_tac 20876 (OpImm ALU_AND 10%bv 10%bv 897%bv).
    apply (pnE_step W2 fx' R10' 20876 mem1 md2 md10' _ R11' 20880 Hsm10').
    { rewrite (step_andi _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A10'. pnE_bvs. unfold YK11.v_andi, w64.
      rewrite YK00.u64_lit by lia. rewrite pnE_next. reflexivity. }
    clear Hf He Hd. intros md11' Hsm11'.
    assert (A11 : getr R11' 10%bv = w64 (Z.land K 897)) by (unfold R11'; apply getr_same; discriminate).
    assert (HF11 : pnE_frame R11' regs) by (unfold R11'; apply pnE_frame_upd; [left; reflexivity | exact HF10]).
    clearbody R11'.
    assert (HM : 0 <= Z.land K 897 < 2 ^ 64) by (apply Z_land_range; lia).
    (* 0x8685c snez a0,a0 *)
    set (s12 := if 0 <? Z.land K 897 then 1 else 0).
    set (R12' := YK11.regupd R11' 10%bv (w64 s12)).
    pnE_fetch_tac 20880 (Op ALU_SLTU 10%bv 0%bv 10%bv).
    apply (pnE_step W2 fx' R11' 20880 mem1 md2 md11' _ R12' 20884 Hsm11').
    { rewrite (step_sltu _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite A11, getr_zero. unfold YK11.v_sltu, w64.
      rewrite YK00.c_ltu_lit by lia. rewrite pnE_next. unfold R12', s12, w64.
      destruct (0 <? Z.land K 897); reflexivity. }
    clear Hf He Hd. intros md12' Hsm12'.
    assert (A12 : getr R12' 10%bv = w64 s12) by (unfold R12'; apply getr_same; discriminate).
    assert (HF12 : pnE_frame R12' regs) by (unfold R12'; apply pnE_frame_upd; [left; reflexivity | exact HF11]).
    clearbody R12'.
    pose proof (pnE_fclass bits) as HFC. fold K in HFC.
    (* 0x86860 bnez a0 -> T: not finite; else C *)
    pnE_fetch_tac 20884 (Branch BC_NE 10%bv 0%bv 44%bv).
    destruct (Z.eqb_spec (Z.land K 897) 0) as [EM | EM].
    - apply (pnE_step W2 fx' R12' 20884 mem1 md2 md12' _ R12' 20888 Hsm12').
      { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_next; reflexivity|].
        rewrite A12, getr_zero. unfold s12. rewrite EM. reflexivity. }
      intros md13' Hsm13'. apply (COUT R12' md13' Hsm13' HF12 HMN1 Ecn). symmetry. exact HFC.
    - apply (pnE_step W2 fx' R12' 20884 mem1 md2 md12' _ R12' 20928 Hsm12').
      { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_btgt; reflexivity|].
        rewrite A12, getr_zero. unfold s12.
        replace (0 <? Z.land K 897) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
      intros md13' Hsm13'. apply (TOUT R12' md13' Hsm13' HF12 HMN1). right. symmetry. exact HFC. }
  (* ---- 0x8683c srli a1,a0,3 ---- *)
  set (Q9 := YK11.regupd R6 11%bv (w64 ((res + cn) / 8))).
  pnE_fetch_tac 20848 (ShiftImm ALU_SRL 11%bv 10%bv 3%bv).
  apply (pnE_step W2 fx' R6 20848 mem1 md2 md10 _ Q9 20852 Hsm10).
  { rewrite (step_srli _ _ _ _ _ _ _ _ _ Hf He Hd), A6_10, pnE_next. unfold YK11.v_srli, w64.
    rewrite YK00.u64_lit by lia. rewrite Z.shiftr_div_pow2 by (vm_compute; discriminate).
    replace (2 ^ bv_unsigned (3%bv : bv 6)) with 8 by (vm_compute; reflexivity). reflexivity. }
  clear Hf He Hd. intros md11 Hsm11.
  assert (Q9_10 : getr Q9 10%bv = w64 (res + cn)) by (unfold Q9; rewrite getr_other by discriminate; exact A6_10).
  assert (Q9_11 : getr Q9 11%bv = w64 ((res + cn) / 8)) by (unfold Q9; apply getr_same; discriminate).
  assert (HQ9 : pnE_frame Q9 regs) by (unfold Q9; apply pnE_frame_upd; [right; left; reflexivity | exact HF6]).
  clearbody Q9.
  (* ---- 0x86840 add a1,a1,s7 ---- *)
  set (Q10 := YK11.regupd Q9 11%bv (w64 ((res + cn) / 8 + SHADOW_OFF))).
  pnE_fetch_tac 20852 (Op ALU_ADD 11%bv 11%bv 23%bv).
  apply (pnE_step W2 fx' Q9 20852 mem1 md2 md11 _ Q10 20856 Hsm11).
  { rewrite (step_add _ _ _ _ _ _ _ _ _ Hf He Hd), Q9_11, (HQ9 23%bv) by discriminate.
    rewrite R23, pnE_next. unfold YK11.v_add, w64. rewrite !YK00.u64_lit by (unfold SHADOW_OFF; lia).
    reflexivity. }
  clear Hf He Hd. intros md12 Hsm12.
  assert (Q10_10 : getr Q10 10%bv = w64 (res + cn)) by (unfold Q10; rewrite getr_other by discriminate; exact Q9_10).
  assert (Q10_11 : getr Q10 11%bv = w64 ((res + cn) / 8 + SHADOW_OFF)) by (unfold Q10; apply getr_same; discriminate).
  assert (HQ10 : pnE_frame Q10 regs) by (unfold Q10; apply pnE_frame_upd; [right; left; reflexivity | exact HQ9]).
  clearbody Q10.
  (* ---- 0x86844 lb a1,0(a1): the shadow byte of end (pn_ok's range_addressable, at mem1) ---- *)
  pose proof OK1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRA1 & _).
  destruct (HRA1 (res + cn) ltac:(lia)) as (s & Hsv & Hsok).
  unfold aview in Hsv.
  destruct (mbyte SEGS (mrestrict (w_H W2) mem1) (shadow_of_addr SHADOW_OFF (res + cn))) as [sb2|] eqn:Esb2;
    [|discriminate Hsv].
  cbn [option_map] in Hsv. injection Hsv as Hsb2.
  assert (Hs8 : 0 <= s < 8) by (unfold saddr_ok in Hsok; pose proof (Z.mod_pos_bound (res + cn) 8); lia).
  assert (Esh2 : shadow_of_addr SHADOW_OFF (res + cn) = (res + cn) / 8 + SHADOW_OFF) by (unfold shadow_of_addr; lia).
  rewrite Esh2 in Esb2.
  assert (Hrd11 : rdn SEGS (mrestrict (w_H W2) mem1) (Z_to_bv 64 ((res + cn) / 8 + SHADOW_OFF)) 1 = Some [sb2]).
  { apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
    cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Esb2. }
  set (Q11 := YK11.regupd Q10 11%bv (w64 s)).
  pnE_fetch_tac 20856 (Load SZ1 true 11%bv 11%bv 0%bv).
  apply (pnE_step W2 fx' Q10 20856 mem1 md2 md12 _ Q11 20860 Hsm12).
  { rewrite (step_lb _ _ _ _ _ _ _ _ _ sb2 Hf He Hd).
    - replace (v_lb sb2) with (Z_to_bv 64 s) by (symmetry; exact (YCbn.cellval_small true sb2 s Hsb2 ltac:(lia))).
      rewrite pnE_next. reflexivity.
    - rewrite Q10_11. unfold w64. rewrite YCbn.v_addi_lit. pnE_bvs. rewrite Z.add_0_r. exact Hrd11. }
  clear Hf He Hd. intros md13 Hsm13.
  assert (Q11_10 : getr Q11 10%bv = w64 (res + cn)) by (unfold Q11; rewrite getr_other by discriminate; exact Q10_10).
  assert (Q11_11 : getr Q11 11%bv = w64 s) by (unfold Q11; apply getr_same; discriminate).
  assert (HQ11 : pnE_frame Q11 regs) by (unfold Q11; apply pnE_frame_upd; [right; left; reflexivity | exact HQ10]).
  clearbody Q11.
  (* ---- 0x86848 bnez a1 -> 0x868d4 (the slow arm) ---- *)
  pnE_fetch_tac 20860 (Branch BC_NE 11%bv 0%bv 140%bv).
  destruct (Z.eqb_spec s 0) as [Es | Es].
  - apply (pnE_step W2 fx' Q11 20860 mem1 md2 md13 _ Q11 20864 Hsm13).
    { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_next; reflexivity|].
      rewrite Q11_11, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. apply Z.eqb_eq. exact Es. }
    intros md14 Hsm14. exact (TAIL Q11 md14 Hsm14 HQ11 Q11_10).
  - apply (pnE_step W2 fx' Q11 20860 mem1 md2 md13 _ Q11 21000 Hsm13).
    { rewrite (step_bne_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_btgt; reflexivity|].
      rewrite Q11_11, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. apply Z.eqb_neq. exact Es. }
    clear Hf He Hd. intros md14 Hsm14.
    (* 0x868d4 andi a2,a0,7 *)
    set (Q13 := YK11.regupd Q11 12%bv (w64 ((res + cn) mod 8))).
    pnE_fetch_tac 21000 (OpImm ALU_AND 12%bv 10%bv 7%bv).
    apply (pnE_step W2 fx' Q11 21000 mem1 md2 md14 _ Q13 21004 Hsm14).
    { rewrite (step_andi _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite Q11_10. pnE_bvs. unfold YK11.v_andi, w64.
      rewrite YK00.u64_lit by lia. change (bv_wrap 64 7) with (Z.ones 3). rewrite Z.land_ones by lia.
      rewrite pnE_next. reflexivity. }
    clear Hf He Hd. intros md15 Hsm15.
    assert (Q13_10 : getr Q13 10%bv = w64 (res + cn)) by (unfold Q13; rewrite getr_other by discriminate; exact Q11_10).
    assert (Q13_11 : getr Q13 11%bv = w64 s) by (unfold Q13; rewrite getr_other by discriminate; exact Q11_11).
    assert (Q13_12 : getr Q13 12%bv = w64 ((res + cn) mod 8)) by (unfold Q13; apply getr_same; discriminate).
    assert (HQ13 : pnE_frame Q13 regs) by (unfold Q13; apply pnE_frame_upd; [right; right; reflexivity | exact HQ11]).
    clearbody Q13.
    (* 0x868d8 blt a2,a1 -> 0x8684c: the access is within the granule's addressable prefix *)
    pnE_fetch_tac 21004 (Branch BC_LT 12%bv 11%bv 8052%bv).
    apply (pnE_step W2 fx' Q13 21004 mem1 md2 md15 _ Q13 20864 Hsm15).
    { rewrite (step_blt_tk _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnE_btgt; reflexivity|].
      rewrite Q13_12, Q13_11. unfold w64, YK11.c_lts.
      pose proof (Z.mod_pos_bound (res + cn) 8).
      rewrite YCbn.bv_lts_small by lia. apply Z.ltb_lt.
      destruct Hsok as [Hs0|[Hs1 Hs2]]; [exfalso; exact (Es Hs0) | exact Hs1]. }
    intros md16 Hsm16. exact (TAIL Q13 md16 Hsm16 HQ13 Q13_10).
Qed.

End c.
