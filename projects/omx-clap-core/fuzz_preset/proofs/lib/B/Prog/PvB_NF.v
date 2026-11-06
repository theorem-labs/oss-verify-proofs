(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset image B (asan-ubsan), parse_value 0x8637c, SEGMENT N (the number arm), sub-piece
   F of lib/B/Prog/PvB_NCut.v: C (0x86864) -> T (0x8688c), over h-verbs-1's ONE image-B program listing
   (lib/B/Listing_prog.v, PL_prog_B). It proves pnF_stmt (PvB_NCut.v).
   rule 24: no function proved
   rule 24: proves no function (kind: segment lemma). Reuse search: `proof-index parse_value` (h-hpreset-7 04:10Z, EXIT=0
   unpiped, index built 2026-10-29T04:26:29Z): "parse_value: 14 file(s) named for it, 35 file(s) use its address, 0
   related; in an earlier delivery 58 named for it and 794 name(s) that hold it, in 68 tree(s)"; second-agent CONFIRM
   (ParseValueLookupConfirm 04:21Z): no released srealizes-form proof of this program's parse_value; new proof
   justified. Lane E's lib/B/Prog/PvB_NE.v (cold/h-pvn-e ecc4968f66f) is the model of the hand steps, of the write
   separation and of the carry across a node store; image A's lib/A/Prog/S8aNumFT.v is the template of the tail.

   THE CODE (the neutral listing, the internal file parse_value.fuzz_preset.asan-ubsan.s; listing offset = B pc - 0x816cc):
     0x86864 srli a0,s3,3 / 0x86868 add a0,a0,s7 / 0x8686c lb a0,0(a0) / 0x86870 bnez a0,0x868e0
                                  the shadow check of v; the slow arm 0x868e0 is NOT reached (see below)
     0x86874 li a0,3              the number node's tag
     0x86878 sw a0,0(s3)          v->type := 3
     0x8687c lbu a0,0(s8) / 0x86880 bnez a0,0x86940   the shadow check of q (the caller's cursor)
     0x86884 li s5,0              the result code
     0x86888 sd s6,0(s4)          in->p := p1 + m, and T.
   All ten instructions are taken by hand (YA0n.v SRr_step through YK11.v's / YK14.v's single-step lemmas). Both
   report arms are refuted: the shadow byte of v reads 0 (the node is addressable for 56 bytes and 8-aligned, so
   saddr_ok at v + 7 forces 0), and the shadow byte of q reads 0 (the cursor is on the REAL stack, which the
   memory-checking runtime keeps at shadow 0: AR_laws_x's alx_zshadow_byte).
   THE TWO STORES are both in the caller's footprint FP (v's node and q's p field). The node lives, at entry, in a
   live allocator block, a live fake frame of the caller, or the caller's window (prhReader_at); pnF_sep turns each
   home into the write premise of YCbqG.v's ajournal_x_exec_fr (awr_byte or wr_fp_frame) and separates the node from
   the parse_value fake frame and the image; pnF_sepq does the same for q, which lies at or above alloc_ceiling;
   pnF_headv separates the 4 written bytes of v from every ledger head word (the heads are 8-aligned, so an overlap
   would put a head at v itself, which the node's home refutes - for a harness block's own user bytes by the node's
   56 zero bytes at entry, which force the head's size word to be 0). pnF_post carries every fact of the cut across
   the two stores.
   MEMNORM: C's last conjunct `YStrtodRowX.aj_memnorm SEGS mem` (the memory normal form, a state fact of the cut) goes
   to T's last conjunct. The eight steps that write no memory keep the memory itself; the two stores are pnF_step_m,
   which takes the normal form across by lib/Reusable/YSRrMemnorm.v's SRr_step_inv at P := YAkMemnorm.memnorm SEGS
   (its laws srr_inv_laws_memnorm_k; YStrtodRowX.aj_memnorm is the same body, by conversion).
   ROOM: C's pn_rp1 (PvB_NCut.v, the room post of EAlloc (S m)) goes unchanged to T's outcome (d): the steps keep the
   allocator state Sc. The ledger's statics include #102's g_most / g_own_ran_out (f97c prh_glob, prh_pst's seven
   cells), kept like the other five.

   Section hypotheses: LAWS (AR_laws_x at the head length hl, the kit's), PSTOK (a MARKED image fact: the ledger's
   five statics are image bytes the program owns; PvB_X.v's and PvB_NE.v's text verbatim).
   Numerals: listing offsets 20888 20892 20896 20900 20904 20908 20912 20916 20920 20924 20928 (DERIVED: B pc -
   B_prog_base 0x816cc; the ten instruction WORDS are read from the listing by pnF_fetch_tac, never written here);
   the register numbers 0 10 19 20 21 22 23 24 and the immediates 0 3 112 192 the words decode to (WORD);
   3 (WORD: the number node's tag); 4 7 8 16 24 56 64 (LENGTH: access widths and node / cursor field offsets, the
   granule end v + 7, the class-0 frame); -104 -8 (LENGTH: pv_saved's slot range); 176 320 16560 (LENGTH:
   parse_value's real frame and the STK sum, as PvB_X.v); 1 256 65536 16777216 4294967296 1099511627776
   281474976710656 72057594037927936 (LENGTH: the eight little-endian byte weights of a 64-bit word);
   4096, 0x7fff7f800000, 2 ^ 47, 2 ^ 62, 2 ^ 64 (LENGTH: address and value ranges, the allocator ceiling's lower
   bound of YCbq.v asan_consts); 6 (LENGTH: the shift field's width). No ADDRESS. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep YStrtodRowX.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbn YK00 YA03 YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PvB_Defs PvB_NCut.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require strtod_c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YSRrMemnorm YAkMemnorm.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Instance PIBf : PrhImg := prh_img_B.

(* ======== pure ======== *)

Lemma pnF_some_byte_eq : forall (b1 b2 : byte), Some b1 = Some b2 -> bv_unsigned b1 = bv_unsigned b2.
Proof. intros b1 b2 E. exact (f_equal (fun o => match o with Some b => bv_unsigned b | None => 0 end) E). Qed.

(* a 64-bit value whose eight little-endian bytes are 0 is 0 *)
Lemma pnF_zero_of_div : forall k, 0 <= k < 2 ^ 64 ->
  (forall i, (i < 8)%nat -> (k / 2 ^ (8 * Z.of_nat i)) mod 256 = 0) -> k = 0.
Proof.
  intros k Hk H.
  pose proof (H 0%nat ltac:(lia)) as H0. pose proof (H 1%nat ltac:(lia)) as H1.
  pose proof (H 2%nat ltac:(lia)) as H2. pose proof (H 3%nat ltac:(lia)) as H3.
  pose proof (H 4%nat ltac:(lia)) as H4. pose proof (H 5%nat ltac:(lia)) as H5.
  pose proof (H 6%nat ltac:(lia)) as H6. pose proof (H 7%nat ltac:(lia)) as H7.
  clear H. cbv beta in H0, H1, H2, H3, H4, H5, H6, H7.
  replace (2 ^ (8 * Z.of_nat 0)) with 1 in H0 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 1)) with 256 in H1 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 2)) with 65536 in H2 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 3)) with 16777216 in H3 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 4)) with 4294967296 in H4 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 5)) with 1099511627776 in H5 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 6)) with 281474976710656 in H6 by reflexivity.
  replace (2 ^ (8 * Z.of_nat 7)) with 72057594037927936 in H7 by reflexivity.
  rewrite Z.div_1_r in H0. lia.
Qed.

Lemma pnF_wtl_len : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros n v. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

Lemma pnF_wtl8_nth : forall v (kk : nat), (kk < 8)%nat ->
  nth_error (word_to_le_bytes 8 (Z_to_bv 64 v)) kk = Some (Z_to_bv 8 (le_byte v 8 kk)).
Proof.
  intros v kk Hk. unfold word_to_le_bytes. rewrite nth_error_Z_to_le_bytes by exact Hk. f_equal.
  apply bv_eq. cbv beta delta [YG0f.le_byte YO0f.le_byte]. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ (8 * Z.of_nat 8)).
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma pnF_wtl4_nth3 : forall (kk : nat), (kk < 4)%nat ->
  nth_error (word_to_le_bytes 4 (Z_to_bv 64 3)) kk = Some (Z_to_bv 8 (le_byte 3 4 kk)).
Proof. intros kk Hk. destruct kk as [|[|[|[|kk]]]]; try lia; vm_compute; reflexivity. Qed.

(* ======== memory: the two stores through the restricted view (PvB_NE.v's lemmas, for two windows) ======== *)
Section m.
Variable segs : list Segment.

Lemma pnF_store_ok : forall (m : word -> option byte) (n : nat) (a : Z),
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

Lemma pnF_wb_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (x : word),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  (bv_unsigned x < A \/ A + Z.of_nat (length bs) <= bv_unsigned x) ->
  mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) x = mrestrict H mem x.
Proof.
  intros H mem A bs x HA HAn Hx. unfold munrestrict, mrestrict.
  destruct (H x) eqn:Hh; [reflexivity|].
  rewrite wbytes_outside; [cbv beta; rewrite Hh; reflexivity | rewrite YK00.u64_lit by lia; lia |].
  rewrite YK00.u64_lit by lia. exact Hx.
Qed.

Lemma pnF_wb_hid : forall (H : word -> bool) (mem m' : word -> option byte) (x : word),
  H x = true -> munrestrict H mem m' x = mem x.
Proof. intros H mem m' x Hh. unfold munrestrict. rewrite Hh. reflexivity. Qed.

Lemma pnF_wb_grow : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 ->
  mem_grows (mrestrict H mem) (mrestrict H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs))).
Proof.
  intros H mem A bs HA HAn x Hx.
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Hl|Hl]; [rewrite pnF_wb_out by lia; exact Hx|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Hu|Hu];
    [|rewrite pnF_wb_out by lia; exact Hx].
  unfold mrestrict in *. unfold munrestrict. destruct (H x) eqn:Hh; [exact Hx|].
  rewrite wbytes_inside; [discriminate | rewrite YK00.u64_lit by lia; lia | rewrite YK00.u64_lit by lia; lia].
Qed.

Lemma pnF_aview_out : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (bs : list byte) (z : Z),
  0 <= A -> A + Z.of_nat (length bs) < 2 ^ 64 -> 0 <= z < 2 ^ 64 ->
  (z < A \/ A + Z.of_nat (length bs) <= z) ->
  aview segs H (munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 A) bs)) z = aview segs H mem z.
Proof.
  intros H mem A bs z HA HAn Hz Hout. apply aview_eq_of. apply pnF_wb_out; [lia | lia |].
  rewrite YK00.u64_lit by lia. exact Hout.
Qed.

Lemma pnF_wb_in8 : forall (H : word -> bool) (mem : word -> option byte) (A v : Z) (kk : nat),
  0 <= A -> A + 8 <= 2 ^ 64 -> (kk < 8)%nat -> H (Z_to_bv 64 (A + Z.of_nat kk)) = false ->
  mbyte segs (mrestrict H (munrestrict H mem
      (wbytes (mrestrict H mem) (Z_to_bv 64 A) (word_to_le_bytes 8 (Z_to_bv 64 v))))) (A + Z.of_nat kk)
  = Some (Z_to_bv 8 (le_byte v 8 kk)).
Proof.
  intros H mem A v kk HA HA8 Hk Hh.
  assert (Hlen : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 v))) = 8)
    by (rewrite pnF_wtl_len; reflexivity).
  pose proof (pnF_wtl8_nth v kk Hk) as E.
  unfold mbyte, munrestrict, mrestrict. rewrite Hh.
  rewrite wbytes_inside; [| rewrite YK00.u64_lit by lia; lia | rewrite !YK00.u64_lit by lia; lia].
  rewrite !YK00.u64_lit by lia. replace (A + Z.of_nat kk - A) with (Z.of_nat kk) by lia. rewrite Nat2Z.id.
  f_equal. apply nth_error_nth. exact E.
Qed.

Lemma pnF_wb_in4 : forall (H : word -> bool) (mem : word -> option byte) (A : Z) (kk : nat),
  0 <= A -> A + 4 <= 2 ^ 64 -> (kk < 4)%nat -> H (Z_to_bv 64 (A + Z.of_nat kk)) = false ->
  mbyte segs (mrestrict H (munrestrict H mem
      (wbytes (mrestrict H mem) (Z_to_bv 64 A) (word_to_le_bytes 4 (Z_to_bv 64 3))))) (A + Z.of_nat kk)
  = Some (Z_to_bv 8 (le_byte 3 4 kk)).
Proof.
  intros H mem A kk HA HA4 Hk Hh.
  assert (Hlen : Z.of_nat (length (word_to_le_bytes 4 (Z_to_bv 64 3))) = 4)
    by (rewrite pnF_wtl_len; reflexivity).
  pose proof (pnF_wtl4_nth3 kk Hk) as E.
  unfold mbyte, munrestrict, mrestrict. rewrite Hh.
  rewrite wbytes_inside; [| rewrite YK00.u64_lit by lia; lia | rewrite !YK00.u64_lit by lia; lia].
  rewrite !YK00.u64_lit by lia. replace (A + Z.of_nat kk - A) with (Z.of_nat kk) by lia. rewrite Nat2Z.id.
  f_equal. apply nth_error_nth. exact E.
Qed.

(* eight zero bytes read as the value 0 (a ledger head word the node's zeros cover) *)
Lemma pnF_val0_of_zero : forall (m : word -> option byte) a k,
  0 <= k < 2 ^ 64 -> val_mem segs m a 8 k ->
  (forall i, (i < 8)%nat -> mbyte segs m (a + Z.of_nat i) = Some (Z_to_bv 8 0)) -> k = 0.
Proof.
  intros m a k Hk Hv Hz. apply (pnF_zero_of_div k Hk).
  intros i Hi. pose proof (Hv i Hi) as Hvi. rewrite (Hz i Hi) in Hvi.
  pose proof (pnF_some_byte_eq _ _ Hvi) as Hu.
  rewrite !Z_to_bv_unsigned in Hu. unfold bv_wrap in Hu. change (bv_modulus 8) with 256 in Hu.
  cbv beta delta [YG0f.le_byte YO0f.le_byte] in Hu.
  rewrite Z.mod_mod in Hu by lia.
  rewrite Z.shiftr_div_pow2 in Hu by lia.
  replace (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hu by reflexivity.
  rewrite (Z.mod_small k (2 ^ 64)) in Hu by lia.
  rewrite Z.mod_0_l in Hu by lia. symmetry. exact Hu.
Qed.

Lemma pnF_mbyte_of_aview : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  aview segs H' m' a = aview segs H m a -> mbyte segs (mrestrict H' m') a = mbyte segs (mrestrict H m) a.
Proof.
  intros H H' m m' a E. unfold aview in E.
  destruct (mbyte segs (mrestrict H' m') a) as [b1|] eqn:E1;
  destruct (mbyte segs (mrestrict H m) a) as [b2|] eqn:E2; cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

Lemma pnF_saved_rng : forall oc, In oc pv_saved -> -104 <= fst oc <= -8.
Proof.
  intros oc H. unfold pv_saved in H.
  repeat (destruct H as [<-|H]; [cbn [fst]; lia|]). destruct H.
Qed.
End m.

(* the registers the ten steps leave alone: all but a0 and s5 *)
Definition pnF_frame (R regs : bvmap 5 word) : Prop :=
  forall r : Prelude.reg, r <> 10%bv -> r <> 21%bv -> getr R r = getr regs r.

Lemma pnF_frame_refl : forall regs, pnF_frame regs regs.
Proof. intros regs r _ _. reflexivity. Qed.

Lemma pnF_frame_upd : forall R regs (d : Prelude.reg) v, (d = 10%bv \/ d = 21%bv) ->
  pnF_frame R regs -> pnF_frame (YK11.regupd R d v) regs.
Proof.
  intros R regs d v Hd HF r H10 H21. rewrite getr_other; [apply HF; assumption|].
  destruct Hd as [Hd | Hd]; rewrite Hd; assumption.
Qed.

(* bv_signed of a literal immediate, computed *)
Ltac pnF_bvs := repeat match goal with |- context [bv_signed ?i] =>
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
   PST_ok; PvB_X.v's and PvB_NE.v's PSTOK, verbatim) *)
Hypothesis PSTOK : forall a, Exists (in_zr a) (@prh_pst prh_img_B) ->
  in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).

Lemma pnF_fetch : forall off w, plookup B_prog_tpi off = Some (PW w) ->
  fetch_word SEGS (Z_to_bv 64 (BASE + off)) = Some (Z_to_bv 32 w).
Proof. intros off w H. exact (@pa_fetch_pw _ _ PL_prog_B PA off w H). Qed.

Lemma pnF_next : forall off k, YK11.v_addi (Z_to_bv 64 (BASE + off)) k = Z_to_bv 64 (BASE + (off + k)).
Proof. intros off k. rewrite YCbn.v_addi_lit. f_equal. lia. Qed.

Lemma pnF_btgt : forall off k, YK11.btgt (Z_to_bv 64 (BASE + off)) k = Z_to_bv 64 (BASE + (off + k)).
Proof. intros off k. unfold YK11.btgt. apply pnF_next. Qed.

(* one hand step at a cut-free pc: registers and pc change, memory does not *)
Lemma pnF_step : forall (W : world SEGS) (fxc : YK11.FPState) regs off mem md0 md Q regs' off',
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

(* one hand step that also writes memory; the memory normal form crosses the step (YSRrMemnorm.v SRr_step_inv) *)
Lemma pnF_step_m : forall (W : world SEGS) (fxc : YK11.FPState) regs off mem md0 md Q regs' off' m',
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

Ltac pnF_fetch_tac off instr :=
  let e := eval vm_compute in (plookup B_prog_tpi off) in
  lazymatch e with
  | Some (PW ?w) =>
    pose proof (pnF_fetch off w ltac:(vm_compute; reflexivity)) as Hf;
    assert (Hd : decode_any (Z_to_bv 32 w) = Some (instr, 4%Z))
      by (vm_compute; repeat first [ reflexivity | (apply bv_eq; vm_compute; reflexivity) | f_equal ]);
    assert (He : is_ecall (Z_to_bv 32 w) = false) by (vm_compute; reflexivity)
  end.

Lemma pnF_keep_regs : forall en regs R Y fa,
  pv_keep_regs en regs Y fa -> pnF_frame R regs -> pv_keep_regs en R Y fa.
Proof.
  intros en regs R Y fa HK HF. unfold pv_keep_regs in *. rewrite !HF by discriminate. exact HK.
Qed.

Lemma pnF_stk : forall en, 176 <= pe_STK en.
Proof.
  intros en. unfold pe_STK, STK_parse_value.
  match goal with |- 176 <= Z.of_nat ?n * ?f + ?l =>
    assert (E1 : f = 320) by reflexivity; assert (E2 : l = 16560) by reflexivity; rewrite E1, E2 end.
  assert (1 <= Z.of_nat (S (PjGrammar.MAXD - pe_d en))) by lia. nia.
Qed.

(* ---- the node's homes at entry (prhReader_at) ---- *)
Lemma pnF_home : forall en, pv_pre B ARx en ->
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

(* ---- the node's 56 bytes: where a store may write, and what they are apart from ---- *)
Lemma pnF_sep : forall en pos lyc Sc Hpc W' mem mdc k res (m : nat),
  pv_pre B ARx en ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc Hpc W' mem mdc k ->
  ablocks B lyc Sc = ablocks B (pe_ly en) (pe_S en) ++ [(res - cf_head, Z.of_nat m + 1 + cf_head)] ->
  forall x, pe_v en <= x < pe_v en + 56 ->
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
  pose proof (pnF_stk en) as HSTK.
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
  destruct (pnF_home en HPRE) as [(b & m0 & Hin & Hm0 & Hb1 & Hb2) | [(cid & p & Hin & Hf1 & Hf2) | (Hw1 & Hw2)]].
  - assert (HinC : In (b, m0) (ablocks B lyc Sc)) by exact (Hbl_in b m0 Hin).
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc b m0 HAR HinC) as (Hb16 & Hb4096 & Hbc & _ & Hbyt & HPW).
    pose proof (req_size_pos m0 Hm0) as Hrq0.
    split.
    { pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc b m0 0 pos HAR HinC HinF) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Efb in Hd. lia. }
    split; [exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc b m0 x HAR HinC ltac:(lia))|].
    split; [exact (proj1 (Hbyt x ltac:(lia)))|].
    left. right; left. split; [exact HinFP|]. exists b, m0. split; [exact HinC | lia].
  - assert (HinC : In (cid, p) (frames Sc)) by exact (Hfr_in cid p Hin).
    rewrite <- (Efa cid p) in Hf1, Hf2.
    destruct (alx_frames SEGS B ARx LAWS lyc Sc Hpc W' mem mdc cid p HAR HinC) as (Hal32 & _ & Hfbyt & _).
    split.
    { destruct (in_split _ _ Hin) as (l2 & l3 & El).
      pose proof (sep_frames_pos_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc (0, pos) (cid, p) [] l2 l3 HAR
        ltac:(rewrite Hfrs, El; reflexivity)) as Hd.
      unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. rewrite Efb in Hd. lia. }
    split; [exact (frm_img_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc cid p x HAR HinC ltac:(lia))|].
    split; [exact (proj1 (Hfbyt x ltac:(lia)))|].
    right. split; [exact HinFP|]. exists cid, p. split; [exact Hin|].
    unfold in_zr, frame_rng. cbn [fst snd]. lia.
  - unfold pe_sp in Hw1, Hw2. split; [lia|].
    split; [intros Hi; pose proof (pa_segs_low x Hi); unfold kLowMemEnd in *; lia|].
    split; [apply Hpres; lia|].
    left. left. lia.
Qed.

(* ---- the cursor's 8 bytes: the caller's window, at or above alloc_ceiling ---- *)
Lemma pnF_sepq : forall en pos lyc Sc Hpc W' mem mdc k,
  pv_pre B ARx en ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc Hpc W' mem mdc k ->
  forall x, pe_q en <= x < pe_q en + 8 ->
    (forall p n, In (p, n) (ablocks B lyc Sc) -> 0 <= n -> p + 8 < x) /\
    ~ (frame_addr lyc 0 pos <= x < frame_addr lyc 0 pos + 64) /\
    ~ in_img SEGS x /\
    apresent (w_H W') mem x /\
    awr_byte (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en) (ablocks B (pe_ly en) (pe_S en))
       (ablocks B lyc Sc) lyc [(0, pos)] x.
Proof.
  intros en pos lyc Sc Hpc W' mem mdc k HPRE HJ x Hx.
  pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
  pose proof HFPRE as (HAFN & _).
  pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
  pose proof HRDP as (_ & _ & _ & _ & _ & Hwin & Hqlo & Hqhi & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof (pnF_stk en) as HSTK.
  pose proof Hstk0 as (_ & HSTK0 & Hc1 & Hc2 & _).
  pose proof Hwin as (He0 & He16 & Hetop & _).
  unfold pe_sp in *.
  assert (HinF : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
  destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (Hfa0 & Hfac & _).
  rewrite Efb in Hfac.
  split.
  { intros p n Hpn Hn0.
    destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc p n HAR Hpn) as (_ & _ & Hpc' & _).
    pose proof (req_size_pos n Hn0) as Hrq. lia. }
  split; [lia|].
  split; [intros Hi; pose proof (pa_segs_low x Hi); unfold kLowMemEnd in *; lia|].
  split; [apply Hpres; lia|].
  left. lia.
Qed.

(* ---- the 4 written bytes of v->type are apart from every ledger head word ---- *)
Lemma pnF_headv : forall en pos lyc Sc Hpc W' mem mdc k res (m : nat) p1,
  pv_pre B ARx en ->
  ajournal_x (SK := SK) SEGS B (@prh_pst prh_img_B) ARx (pe_STK en + pe_e en) (pe_sp en + pe_e en) (pe_FP en)
    (pe_ly en) (pe_S en) (pe_Hp en) (pe_W en) (pe_mem en) (pe_md en) [(0, pos)] lyc Sc Hpc W' mem mdc k ->
  pn_ok B en m res lyc Sc Hpc W' mem ->
  pn_reader en p1 W' mem (fun a => pe_v en + 8 <= a < pe_v en + 24) ->
  forall a kk, In (a, kk) ((res, Z.of_nat m + 1) :: pe_Lam en) ->
  forall x, pe_v en <= x < pe_v en + 4 -> ~ (a - cf_head <= x < a - cf_head + 8).
Proof.
  intros en pos lyc Sc Hpc W' mem mdc k res m p1 HPRE HJ HOK HRD a kk Hin x Hx Hov.
  pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
  pose proof HFPRE as (HAFN & _).
  pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
  pose proof HRDP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hnode & _ & _ & _ & HLED0 & _).
  pose proof Hnode as (Hv4096 & Hv8 & _ & Hvzero & Hvat & _ & _ & _).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
  pose proof HOK as (_ & Hres0 & _ & _ & _ & Hnb0 & _ & _ & Hab & _ & _ & HLED).
  pose proof HRD as (_ & _ & HNODE & _).
  pose proof (@cf_head_nonneg cp) as Hh0. pose proof (@cf_head_al cp) as Hh8.
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof (pnF_stk en) as HSTK.
  pose proof Hstk0 as (_ & HSTK0 & Hc1 & Hc2 & _).
  assert (HinF : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
  assert (Hfr_in : forall cid p, In (cid, p) (frames (pe_S en)) -> In (cid, p) (frames Sc))
    by (intros cid p H; rewrite Hfrs; right; exact H).
  assert (Hbl_in : forall b n, In (b, n) (ablocks B (pe_ly en) (pe_S en)) -> In (b, n) (ablocks B lyc Sc))
    by (intros b n H; rewrite Hab; apply in_or_app; left; exact H).
  assert (HinN : In (res - cf_head, Z.of_nat m + 1 + cf_head) (ablocks B lyc Sc))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  pose proof HLED as (_ & _ & HFB & _). rewrite Forall_forall in HFB.
  destruct (HFB (a, kk) Hin) as (Hk0 & Hblk & _ & Hal & Hval). cbn [fst snd] in Hk0, Hblk, Hal, Hval.
  (* the head word and the node are both 8-aligned, so an overlap puts the head word at the node *)
  assert (Eh : a - cf_head = pe_v en) by (Z.div_mod_to_equations; lia).
  pose proof (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hk0 Hh0)) as (Hrq1 & Hrq2).
  destruct Hin as [Heq | Hin].
  - (* the new block's head *)
    injection Heq as Ea Ekk. subst a kk.
    destruct (pnF_home en HPRE) as [(b & m0 & Hin0 & Hm0 & Hb1 & Hb2) |
      [(cid & p & Hinf & Hf1 & Hf2) | (Hw1 & Hw2)]].
    + assert (HinCb : In (b, m0) (ablocks B lyc Sc)) by exact (Hbl_in b m0 Hin0).
      pose proof (req_size_pos m0 Hm0) as (Hr1 & Hr2).
      assert (Hne : (res - cf_head, Z.of_nat m + 1 + cf_head) <> (b, m0))
        by (intros E; injection E as E1 E2; apply Hnb0; rewrite E1, E2; exact Hin0).
      pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ _ _ HAR HinN HinCb Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    + assert (HinCf : In (cid, p) (frames Sc)) by exact (Hfr_in cid p Hinf).
      destruct (alx_layout SEGS B ARx LAWS _ _ _ _ _ _ lyc HAR0 Hly) as (_ & Efa & _).
      rewrite <- (Efa cid p) in Hf1, Hf2.
      pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ cid p HAR HinN HinCf) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    + destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ HAR HinN) as (_ & _ & HNc & _).
      unfold pe_sp in Hw1, Hw2. lia.
  - (* an old ledger head *)
    unfold prhReader_at in Hvat.
    destruct Hvat as [(a' & k' & Hin' & Ha1 & Ha2) | [(b & n & Hinb & Hnl & Hb1 & Hb2) |
      [(cid & p & Hinf & Hf1 & Hf2) | (Hw1 & Hw2)]]].
    + pose proof HLED0 as (_ & _ & HFB0 & _). rewrite Forall_forall in HFB0.
      destruct (HFB0 (a', k') Hin') as (Hk0' & Hblk' & _ & Hal' & Hval').
      cbn [fst snd] in Hk0', Hblk', Hal', Hval'.
      assert (HinC' : In (a' - cf_head, k' + cf_head) (ablocks B lyc Sc)) by exact (Hbl_in _ _ Hblk').
      pose proof (req_size_pos (k' + cf_head) (Z.add_nonneg_nonneg _ _ Hk0' Hh0)) as (Hr1' & Hr2').
      destruct (Z.eq_dec (a - cf_head) (a' - cf_head)) as [Eaa | Nee].
      2: { pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ _ _ HAR Hblk HinC'
             ltac:(intros E; injection E as E1 E2; lia)) as Hd.
           unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
      destruct (Z.eq_dec kk k') as [Ekk' | Nkk].
      2: { pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ _ _ HAR Hblk HinC'
             ltac:(intros E; injection E as E1 E2; lia)) as Hd.
           unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
      (* the node's own harness block: its head word is the node's first 8 bytes, which are 0 at entry *)
      assert (Ech : cf_head = 0) by lia.
      assert (Hz8 : forall i, (i < 8)%nat ->
        mbyte SEGS (rdW W' mem) (pe_v en + Z.of_nat i) = Some (Z_to_bv 8 0)).
      { intros i Hi.
        assert (E1 : aview SEGS (w_H W') mem (pe_v en + Z.of_nat i) =
                     aview SEGS (w_H (pe_W en)) (pe_mem en) (pe_v en + Z.of_nat i))
          by (apply HNODE; [lia | cbv beta; lia]).
        rewrite (pnF_mbyte_of_aview SEGS _ _ _ _ _ E1).
        unfold pj_zeroR in Hvzero.
        assert (Hlen : (i < length (repeat 0 56))%nat).
        { change (length (repeat 0 56)) with 56%nat.
          apply (Nat.lt_le_trans i 8 56 Hi). apply Nat.leb_le. reflexivity. }
        destruct (Hvzero i Hlen) as (Hvm & _).
        assert (En : nth i (repeat 0 56) 0 = 0).
        { destruct (nth_in_or_default i (repeat 0 56) 0) as [Hi2|Hd2];
            [exact (repeat_spec 56 0 _ Hi2) | exact Hd2]. }
        rewrite En in Hvm. pose proof (Hvm 0%nat ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0. }
      assert (Hkk64 : 0 <= kk < 2 ^ 64).
      { destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ HAR Hblk) as (_ & _ & Hbc & _). lia. }
      assert (Ekk0 : kk = 0).
      { apply (pnF_val0_of_zero SEGS (rdW W' mem) (a - cf_head) kk Hkk64 Hval).
        rewrite Eh. exact Hz8. }
      lia.
    + assert (HinCb : In (b, n) (ablocks B lyc Sc)) by exact (Hbl_in b n Hinb).
      pose proof (req_size_pos n ltac:(lia)) as (Hr1 & Hr2).
      destruct (Z.eq_dec (a - cf_head) b) as [Eab | Nab].
      2: { pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ _ _ HAR Hblk HinCb
             ltac:(intros E; injection E as E1 E2; lia)) as Hd.
           unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
      destruct (Z.eq_dec (kk + cf_head) n) as [Esz | Nsz].
      2: { pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ _ _ HAR Hblk HinCb
             ltac:(intros E; injection E as E1 E2; lia)) as Hd.
           unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia. }
      exfalso. apply Hnl. replace (b + cf_head) with a by lia. replace (n - cf_head) with kk by lia. exact Hin.
    + assert (HinCf : In (cid, p) (frames Sc)) by exact (Hfr_in cid p Hinf).
      destruct (alx_layout SEGS B ARx LAWS _ _ _ _ _ _ lyc HAR0 Hly) as (_ & Efa & _).
      rewrite <- (Efa cid p) in Hf1, Hf2.
      pose proof (sep_block_frame_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ cid p HAR Hblk HinCf) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
    + destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ HAR Hblk) as (_ & _ & Hbc & _).
      unfold pe_sp in Hw1, Hw2. lia.
Qed.

Definition pnF_mem1 (H : word -> bool) (mem : word -> option byte) (v : Z) : word -> option byte :=
  munrestrict H mem (wbytes (mrestrict H mem) (Z_to_bv 64 v) (word_to_le_bytes 4 (Z_to_bv 64 3))).
Definition pnF_mem2 (H : word -> bool) (mem : word -> option byte) (v q pm : Z) : word -> option byte :=
  munrestrict H (pnF_mem1 H mem v)
    (wbytes (mrestrict H (pnF_mem1 H mem v)) (Z_to_bv 64 q) (word_to_le_bytes 8 (Z_to_bv 64 pm))).

(* ---- every fact of the cut across the two stores v->type := 3 and in->p := pm ---- *)
Lemma pnF_post : forall en W' mem Y fa fl pos lyc Sc Hpc k (m : nat) res p1 pm mdc md',
  pv_pre B ARx en ->
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W' mem mdc k ->
  pn_ok B en m res lyc Sc Hpc W' mem ->
  pn_reader en p1 W' mem (fun a => pe_v en + 8 <= a < pe_v en + 24) ->
  pe_text en <= pm <= pe_text en + pe_len en ->
  same_but_materialized mdc md' ->
  pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W'
    (pnF_mem2 (w_H W') mem (pe_v en) (pe_q en) pm) md' k /\
  pn_ok B en m res lyc Sc Hpc W' (pnF_mem2 (w_H W') mem (pe_v en) (pe_q en) pm) /\
  pn_reader en pm W' (pnF_mem2 (w_H W') mem (pe_v en) (pe_q en) pm)
    (fun a => pe_v en <= a < pe_v en + 4 \/ pe_v en + 8 <= a < pe_v en + 24) /\
  val_mem SEGS (rdW W' (pnF_mem2 (w_H W') mem (pe_v en) (pe_q en) pm)) (pe_v en) 4 3 /\
  (forall a (n : nat) vv,
     (forall j, 0 <= j < Z.of_nat n -> 0 <= a + j < 2 ^ 64 /\
        (a + j < pe_v en \/ pe_v en + 4 <= a + j) /\ (a + j < pe_q en \/ pe_q en + 8 <= a + j)) ->
     val_mem SEGS (rdW W' mem) a n vv ->
     val_mem SEGS (rdW W' (pnF_mem2 (w_H W') mem (pe_v en) (pe_q en) pm)) a n vv) /\
  (forall a l,
     (forall j, 0 <= j < Z.of_nat (length l) -> 0 <= a + j < 2 ^ 64 /\
        (a + j < pe_v en \/ pe_v en + 4 <= a + j) /\ (a + j < pe_q en \/ pe_q en + 8 <= a + j)) ->
     garr8 SEGS (rdW W' mem) a l ->
     garr8 SEGS (rdW W' (pnF_mem2 (w_H W') mem (pe_v en) (pe_q en) pm)) a l).
Proof.
  intros en W' mem Y fa fl pos lyc Sc Hpc k m res p1 pm mdc md' HPRE HBODY HOK HRD Hpm Hsame.
  set (mem1 := pnF_mem1 (w_H W') mem (pe_v en)).
  set (mem2 := pnF_mem2 (w_H W') mem (pe_v en) (pe_q en) pm).
  assert (Emem1 : mem1 = munrestrict (w_H W') mem
    (wbytes (mrestrict (w_H W') mem) (Z_to_bv 64 (pe_v en)) (word_to_le_bytes 4 (Z_to_bv 64 3)))) by reflexivity.
  assert (Emem2 : mem2 = munrestrict (w_H W') mem1
    (wbytes (mrestrict (w_H W') mem1) (Z_to_bv 64 (pe_q en)) (word_to_le_bytes 8 (Z_to_bv 64 pm)))) by reflexivity.
  pose proof HPRE as (HFPRE & _ & _ & _ & _ & _ & _ & _ & HRDP & _).
  pose proof HFPRE as (HAFN & _).
  pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
  pose proof HRDP as (_ & _ & _ & _ & _ & Hwin & Hqlo & Hqhi & _ & _ & _ & _ & Hnode & Hqv & Htv & _).
  pose proof Hnode as (Hv4096 & Hv8 & _ & _ & _ & Hvam & Hvown & _).
  pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof HOK as (Hcf & Hres0 & Hres16 & HresL & Hres64 & HresNB & HresV & EHp & Hab & HRA & HHV & HLED).
  pose proof HRD as (HINOK & HSRC & HNODE & HVRA).
  pose proof HINOK as (Cq & Cq8 & Cq16 & Crw & Cqm8 & Ct0 & Ctlen & Cp1 & Clen & Ctb & Cqt & Cd).
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof (@cf_head_nonneg cp) as Hh0.
  pose proof (pnF_stk en) as HSTK.
  pose proof Hstk0 as (Hsp16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _ & Hc5 & Hc6).
  pose proof Hwin as (He0 & He16 & Hetop & _).
  pose proof (pnF_sep en pos lyc Sc Hpc W' mem mdc k res m HPRE HJ Hab) as SEPV.
  pose proof (pnF_sepq en pos lyc Sc Hpc W' mem mdc k HPRE HJ) as SEPQ.
  pose proof (pnF_headv en pos lyc Sc Hpc W' mem mdc k res m p1 HPRE HJ HOK HRD) as HEADV.
  assert (Efb : fs_frame_bytes 0 = 64) by reflexivity.
  destruct (frames_bounds_x SEGS B ARx LAWS lyc Sc Hpc W' mem mdc 0 pos HAR HinF) as (Hfa0 & Hfac & _).
  rewrite <- Efa in Hfa0, Hfac. rewrite Efb in Hfac.
  unfold amem_range in Hvam. unfold pe_sp in *.
  assert (Esp : pe_sp en = spZ (pe_regs en)) by reflexivity.
  assert (Hvr : 4096 <= pe_v en /\ pe_v en + 56 <= 2 ^ 47)
    by (unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (Hqr : 0x7fff7f800000 + 176 <= pe_q en /\ pe_q en + 24 <= 2 ^ 47) by lia.
  assert (Hbl4 : Z.of_nat (length (word_to_le_bytes 4 (Z_to_bv 64 3))) = 4)
    by (rewrite pnF_wtl_len; reflexivity).
  assert (Hbl8 : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 pm))) = 8)
    by (rewrite pnF_wtl_len; reflexivity).
  assert (KEEP : forall z, 0 <= z < 2 ^ 64 -> (z < pe_v en \/ pe_v en + 4 <= z) ->
                   (z < pe_q en \/ pe_q en + 8 <= z) -> aview SEGS (w_H W') mem2 z = aview SEGS (w_H W') mem z).
  { intros z Hz H1 H2. rewrite Emem2.
    rewrite (pnF_aview_out SEGS (w_H W') mem1 (pe_q en) _ z) by (rewrite ?Hbl8; lia).
    rewrite Emem1. apply pnF_aview_out; rewrite ?Hbl4; lia. }
  assert (KEEPn : forall z, 0 <= z < 2 ^ 64 -> ~ (pe_v en <= z < pe_v en + 4) ->
                   ~ (pe_q en <= z < pe_q en + 8) -> aview SEGS (w_H W') mem2 z = aview SEGS (w_H W') mem z).
  { intros z Hz H1 H2. apply KEEP; [lia | | ].
    - destruct (Z_lt_le_dec z (pe_v en)) as [A|A]; [left; exact A|].
      destruct (Z_lt_le_dec z (pe_v en + 4)) as [C|C]; [exfalso; apply H1; split; assumption | right; exact C].
    - destruct (Z_lt_le_dec z (pe_q en)) as [A|A]; [left; exact A|].
      destruct (Z_lt_le_dec z (pe_q en + 8)) as [C|C]; [exfalso; apply H2; split; assumption | right; exact C]. }
  assert (GROW1 : mem_grows (rdW W' mem) (rdW W' mem1))
    by (rewrite Emem1; apply pnF_wb_grow; rewrite ?Hbl4; lia).
  assert (GROW2 : mem_grows (rdW W' mem1) (rdW W' mem2))
    by (rewrite Emem2; apply pnF_wb_grow; rewrite ?Hbl8; lia).
  assert (GROW : mem_grows (rdW W' mem) (rdW W' mem2)) by (eapply mem_grows_trans; eassumption).
  assert (KVb : forall a (n : nat) vv,
     (forall j, 0 <= j < Z.of_nat n -> 0 <= a + j < 2 ^ 64 /\
        (a + j < pe_v en \/ pe_v en + 4 <= a + j) /\ (a + j < pe_q en \/ pe_q en + 8 <= a + j)) ->
     val_mem SEGS (rdW W' mem) a n vv -> val_mem SEGS (rdW W' mem2) a n vv).
  { intros a n vv Hj Hv. apply (val_mem_kept SEGS (w_H W') (w_H W') mem mem2 a n vv); [|exact Hv].
    intros j Hjr. destruct (Hj j Hjr) as (Hj1 & Hj2 & Hj3). exact (KEEP (a + j) Hj1 Hj2 Hj3). }
  assert (KGb : forall a l,
     (forall j, 0 <= j < Z.of_nat (length l) -> 0 <= a + j < 2 ^ 64 /\
        (a + j < pe_v en \/ pe_v en + 4 <= a + j) /\ (a + j < pe_q en \/ pe_q en + 8 <= a + j)) ->
     garr8 SEGS (rdW W' mem) a l -> garr8 SEGS (rdW W' mem2) a l).
  { intros a l Hj Hg jj Hjj. destruct (Hg jj Hjj) as [Hv Hr]. split; [|exact Hr].
    apply KVb; [|exact Hv]. intros j Hj1. cbn in Hj1. assert (j = 0) by lia. subst j.
    rewrite Z.add_0_r. exact (Hj (Z.of_nat jj) ltac:(lia)). }
  (* the shadow band is apart from both windows *)
  assert (SHO : forall z, 0 <= z < 2 ^ 47 -> 0 <= SHADOW_OFF + z / 8 < 2 ^ 64 /\
                  (SHADOW_OFF + z / 8 < pe_v en \/ pe_v en + 4 <= SHADOW_OFF + z / 8) /\
                  (SHADOW_OFF + z / 8 < pe_q en \/ pe_q en + 8 <= SHADOW_OFF + z / 8)).
  { intros z Hz. unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *. lia. }
  assert (KRA : forall a n, 0 <= a -> a + n <= 2 ^ 47 ->
     range_addressable (aview SEGS (w_H W') mem) SHADOW_OFF a n ->
     range_addressable (aview SEGS (w_H W') mem2) SHADOW_OFF a n).
  { intros a n Ha Hn HR z Hz. destruct (HR z Hz) as (s & Hs & Hok). exists s. split; [|exact Hok].
    rewrite <- Hs. unfold shadow_of_addr. destruct (SHO z ltac:(lia)) as (S1 & S2 & S3). exact (KEEP _ S1 S2 S3). }
  assert (KHV : forall a n, shadow_hull_vis (aview SEGS (w_H W') mem) a n ->
     shadow_hull_vis (aview SEGS (w_H W') mem2) a n).
  { intros a n H s Hs. exact (aview_keeps_vis SEGS _ _ _ _ GROW (H s Hs)). }
  (* the real frame and the fake frame are apart from both windows *)
  assert (RFR : forall z, spZ (pe_regs en) - 176 <= z < spZ (pe_regs en) -> 0 <= z < 2 ^ 64 /\
                  (z < pe_v en \/ pe_v en + 4 <= z) /\ (z < pe_q en \/ pe_q en + 8 <= z)).
  { intros z Hz. split; [lia|]. split; [|left; lia].
    destruct (Z_lt_le_dec z (pe_v en)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec z (pe_v en + 4)) as [H2|H2]; [|right; exact H2].
    exfalso. destruct (Hvown z ltac:(lia)) as [_ Hn]. apply Hn. lia. }
  assert (FFR : forall z, fa <= z < fa + 64 -> 0 <= z < 2 ^ 64 /\
                  (z < pe_v en \/ pe_v en + 4 <= z) /\ (z < pe_q en \/ pe_q en + 8 <= z)).
  { intros z Hz. split; [lia|]. split; [|left; lia].
    destruct (Z_lt_le_dec z (pe_v en)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec z (pe_v en + 4)) as [H2|H2]; [|right; exact H2].
    exfalso. destruct (SEPV z ltac:(lia)) as (Hn & _). apply Hn. rewrite <- Efa. lia. }
  split.
  { (* pv_body *)
    pose proof HFRM as (HY1 & HY32 & HPR0 & Vsav & Vfa48 & Vmagic & Vdesc & Vpc & Vfl & HPRfa & Hshlen & Gsh).
    split.
    { split; [exact HY1|]. split; [exact HY32|].
      split; [intros a Ha; exact (apresent_grows _ _ _ _ GROW (HPR0 a Ha))|].
      split.
      { rewrite Forall_forall in Vsav |- *. intros oc Hoc. pose proof (pnF_saved_rng oc Hoc) as Hr.
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
        _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 md'
        (fun a => (pe_v en <= a < pe_v en + 4) \/ (pe_q en <= a < pe_q en + 8)) HJ).
      - intros x Hx. rewrite Emem2.
        rewrite (pnF_wb_out (w_H W') mem1 (pe_q en) _ x) by (rewrite ?Hbl8; lia).
        rewrite Emem1. apply pnF_wb_out; rewrite ?Hbl4; lia.
      - exact GROW.
      - intros x Hx. rewrite Emem2. rewrite pnF_wb_hid by exact Hx.
        rewrite Emem1. apply pnF_wb_hid. exact Hx.
      - exact Hsame.
      - intros a [Ha|Ha].
        + exact (proj2 (proj2 (proj2 (SEPV a ltac:(lia))))).
        + left. exact (proj2 (proj2 (proj2 (proj2 (SEPQ a Ha))))). }
    intros a Ha Hnf. rewrite <- (HWIN a Ha Hnf). apply KEEPn; [lia | |].
    - intros Hc. apply Hnf. exists (pe_v en, pe_v en + 56).
      split; [unfold pe_FP; right; right; left; reflexivity | cbn [fst snd]; lia].
    - intros Hc. apply Hnf. exists (pe_q en, pe_q en + 8).
      split; [unfold pe_FP; left; reflexivity | cbn [fst snd]; lia]. }
  (* the new block's bounds *)
  assert (HinN : In (res - cf_head, Z.of_nat m + 1 + cf_head) (ablocks B lyc Sc))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
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
                      val_mem SEGS (rdW W' mem) a n vv -> val_mem SEGS (rdW W' mem2) a n vv).
      { intros a n vv Hex Hv. apply KVb; [|exact Hv]. intros j Hj.
        assert (Hin : Exists (in_zr (a + j)) (@prh_pst prh_img_B)).
        { apply Exists_exists in Hex as (r & Hr & Ha & Hn). apply Exists_exists. exists r. split; [exact Hr|].
          unfold in_zr. lia. }
        destruct (PSTOK _ Hin) as [Himg _]. pose proof (pa_segs_low _ Himg) as Hlo.
        unfold kLowMemEnd in Hlo.
        split; [lia|]. split; [|left; lia].
        destruct (Z_lt_le_dec (a + j) (pe_v en)) as [H1|H1]; [left; exact H1|].
        destruct (Z_lt_le_dec (a + j) (pe_v en + 4)) as [H2|H2]; [|right; exact H2].
        exfalso. destruct (SEPV (a + j) ltac:(lia)) as (_ & Hn' & _). exact (Hn' Himg). }
      destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & R6) & (G7 & R7) & Grest).
      split; [apply KST; [|exact G1]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [apply KST; [|exact G2]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [apply KST; [|exact G3]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [apply KST; [|exact G4]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [apply KST; [|exact G5]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl])|].
      split; [split; [apply KST; [|exact G6]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl]) | exact R6]|].
      split; [split; [apply KST; [|exact G7]; unfold prh_pst; repeat (first [apply Exists_cons_hd; split; reflexivity | apply Exists_cons_tl]) | exact R7]|].
      exact Grest.
    - rewrite Forall_forall in HHB |- *. intros ak Hak. destruct ak as (aa & kk). cbn [fst snd] in *.
      destruct (HHB (aa, kk) Hak) as (Hk & Hblk & Hhp & Hal & Hv). cbn [fst snd] in Hk, Hblk, Hhp, Hal, Hv.
      split; [exact Hk|]. split; [exact Hblk|]. split; [exact Hhp|]. split; [exact Hal|].
      destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W' mem mdc _ _ HAR Hblk) as (_ & Hb4096 & Hbc & _).
      pose proof (req_size_pos (kk + cf_head) (Z.add_nonneg_nonneg _ _ Hk Hh0)) as (Hr1 & Hr2).
      destruct (SEPQ (pe_q en) ltac:(lia)) as (HbQ & _).
      pose proof (HbQ _ _ Hblk (Z.add_nonneg_nonneg _ _ Hk Hh0)) as HbQ'.
      apply KVb; [|exact Hv]. intros j Hj. cbn in Hj.
      split; [lia|]. split; [|left; lia].
      destruct (Z_lt_le_dec (aa - cf_head + j) (pe_v en)) as [H1|H1]; [left; exact H1|].
      destruct (Z_lt_le_dec (aa - cf_head + j) (pe_v en + 4)) as [H2|H2]; [|right; exact H2].
      exfalso. apply (HEADV aa kk Hak (aa - cf_head + j)); lia. }
  split.
  { (* pn_reader at the new cursor *)
    unfold pn_reader. cbv zeta. split; [|split; [|split]].
    - split.
      { intros kk Hkk. rewrite Emem2. apply pnF_wb_in8; [lia | lia | exact Hkk |].
        destruct (SEPQ (pe_q en + Z.of_nat kk) ltac:(lia)) as (_ & _ & _ & (Hh & _) & _). exact Hh. }
      split; [apply KVb; [intros j Hj; cbn in Hj; lia | exact Cq8]|].
      split; [apply KVb; [intros j Hj; cbn in Hj; lia | exact Cq16]|].
      split; [intros x Hx; exact (writable_at_grows SEGS _ _ x GROW (Crw x Hx))|].
      split; [exact Cqm8|]. split; [exact Ct0|]. split; [exact Ctlen|].
      split; [lia|]. split; [exact Clen|].
      split; [apply KGb; [intros j Hj; lia | exact Ctb]|].
      split; [exact Cqt | exact Cd].
    - pose proof HSRC as (S1 & S2 & S3 & S4 & S5 & S6).
      split; [apply KGb; [intros j Hj; lia | exact S1]|].
      split; [exact S2|]. split; [exact S3|]. split; [exact S4|].
      split; [apply KRA; [lia | lia | exact S5]|].
      intros Hl. apply KHV. exact (S6 Hl).
    - intros a Ha Hnw. cbv beta in Hnw.
      rewrite <- (HNODE a Ha ltac:(cbv beta; intros Hc; apply Hnw; right; exact Hc)).
      apply KEEPn; [lia | intros Hc; apply Hnw; left; exact Hc | lia].
    - apply KRA; [lia | lia | exact HVRA]. }
  split.
  { (* v->type = 3 *)
    apply (val_mem_kept SEGS (w_H W') (w_H W') mem1 mem2 (pe_v en) 4 3).
    - intros j Hj. rewrite Emem2. apply pnF_aview_out; rewrite ?Hbl8; lia.
    - intros kk Hkk. rewrite Emem1. apply pnF_wb_in4; [lia | lia | exact Hkk |].
      destruct (SEPV (pe_v en + Z.of_nat kk) ltac:(lia)) as (_ & _ & (Hh & _) & _). exact Hh. }
  split; [exact KVb | exact KGb].
Qed.

(* ======== sub-piece F ======== *)
Lemma pnF : pnF_stmt (SK := SK) B ARx.
Proof.
  intros en HPRE KT W2 ms2 md2 HC.
  unfold pn_at_C in HC. cbv zeta in HC.
  destruct HC as (fx' & regs & mem & Y & fa & fl & pos & lyc & Sc & Hpc & k & c & y & m & res & bits &
    Ems & HFZ & HFK & HBASE & HBODY & HOK & HFRS & HROOM & HRD & Mstr & Mnum & Gres & HSTR & Hfin &
    R22 & R21 & HLEAD & Hm & HSPAN & HSTOP & HQP & HMN).
  subst ms2.
  pose proof HPRE as (HFPRE & HCTX & _ & _ & HCHE & HCUR & Hq10 & Hv11 & HRDP & HROOMp & HFRB & _).
  pose proof HFPRE as (HAFN & _).
  pose proof HAFN as (HAR0 & _ & _ & _ & _ & Hstk0 & _).
  pose proof HRDP as (_ & _ & _ & _ & _ & Hwin & Hqlo & Hqhi & _ & _ & _ & _ & Hnode & Hqv & Htv & _).
  pose proof Hnode as (Hv4096 & Hv8 & _ & _ & _ & Hvam & _ & _).
  pose proof HBASE as (HKR & R9 & R19 & R20 & R24 & Hskip & Hc123 & Hc91 & Hc34 & Hc116 & Hc102 & Hc110).
  pose proof HKR as (R2 & R8 & R18 & R26 & R27 & R23 & R3 & R4).
  pose proof HBODY as (HFRM & HinF & Efa & Efl & HJ & HWIN).
  pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
  pose proof HOK as (Hcf & Hres0 & Hres16 & HresL & Hres64 & HresNB & HresV & EHp & Hab & HRA & HHV & HLED).
  pose proof HRD as (HINOK & HSRC & HNODE & HVRA).
  pose proof HINOK as (Cq & Cq8 & Cq16 & Crw & Cqm8 & Ct0 & Ctlen & Cp1 & Clen & Ctb & Cqt & Cd).
  pose proof asan_consts as (CC1 & CC2 & CC3 & CC4 & CC5).
  pose proof (pnF_stk en) as HSTK.
  pose proof Hstk0 as (Hsp16 & HSTK0 & Hc1 & Hc2 & Hc3 & Hc4 & _ & Hc5 & Hc6).
  pose proof Hwin as (He0 & He16 & Hetop & _).
  pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  unfold amem_range in Hvam.
  assert (Hvr : 4096 <= pe_v en /\ pe_v en + 56 <= 2 ^ 47)
    by (unfold kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (Hqr : 0x7fff7f800000 + 176 <= pe_q en /\ pe_q en + 24 <= 2 ^ 47) by lia.
  assert (Hpm : pe_text en <= pn_p1 en (c :: y) + Z.of_nat m <= pe_text en + pe_len en)
    by (unfold pn_p1 in *; lia).
  (* the cut across the two stores *)
  pose proof (pnF_post en W2 mem Y fa fl pos lyc Sc Hpc k m res _ (pn_p1 en (c :: y) + Z.of_nat m) md2 md2
    HPRE HBODY HOK HRD Hpm (same_but_materialized_refl md2)) as (_ & OK1 & RD1 & V3 & KV1 & KG1).
  set (mem1 := pnF_mem1 (w_H W2) mem (pe_v en)) in *.
  set (mem2 := pnF_mem2 (w_H W2) mem (pe_v en) (pe_q en) (pn_p1 en (c :: y) + Z.of_nat m)) in *.
  assert (Emem1 : mem1 = munrestrict (w_H W2) mem
    (wbytes (mrestrict (w_H W2) mem) (Z_to_bv 64 (pe_v en)) (word_to_le_bytes 4 (Z_to_bv 64 3)))) by reflexivity.
  assert (POST : forall md', same_but_materialized md2 md' ->
     pv_body B ARx en Y fa fl pos pv_shadow_open lyc Sc Hpc W2 mem2 md' k)
    by (intros md' Hs; exact (proj1 (pnF_post en W2 mem Y fa fl pos lyc Sc Hpc k m res _
          (pn_p1 en (c :: y) + Z.of_nat m) md2 md' HPRE HBODY HOK HRD Hpm Hs))).
  pose proof (pnF_sep en pos lyc Sc Hpc W2 mem md2 k res m HPRE HJ Hab) as SEPV.
  pose proof (pnF_sepq en pos lyc Sc Hpc W2 mem md2 k HPRE HJ) as SEPQ.
  assert (HinN : In (res - cf_head, Z.of_nat m + 1 + cf_head) (ablocks B lyc Sc))
    by (rewrite Hab; apply in_or_app; right; left; reflexivity).
  pose proof (@cf_head_nonneg cp) as Hh0.
  destruct (alx_blocks SEGS B ARx LAWS lyc Sc Hpc W2 mem md2 _ _ HAR HinN) as (_ & HN4096 & HNc & _).
  assert (HNreq : req_size (Z.of_nat m + 1 + cf_head) = Z.of_nat m + 1 + cf_head)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat m + 1 + cf_head) 0); lia).
  rewrite HNreq in HNc.
  assert (Hltxt : length (firstn m (c :: y)) = m) by (rewrite length_firstn; lia).
  (* the kept values of the node and of the block *)
  assert (Mstr1 : val_mem SEGS (rdW W2 mem2) (pe_v en + 16) 8 res)
    by (apply KV1; [intros j Hj; cbn in Hj; lia | exact Mstr]).
  assert (Mnum1 : val_mem SEGS (rdW W2 mem2) (pe_v en + 8) 8 bits)
    by (apply KV1; [intros j Hj; cbn in Hj; lia | exact Mnum]).
  assert (Gres1 : garr8 SEGS (rdW W2 mem2) res (firstn m (c :: y) ++ [0])).
  { apply KG1; [|exact Gres]. intros j Hj. rewrite length_app, Hltxt in Hj. cbn [length] in Hj.
    split; [lia|]. split; [|left; lia].
    destruct (Z_lt_le_dec (res + j) (pe_v en)) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec (res + j) (pe_v en + 4)) as [H2|H2]; [|right; exact H2].
    exfalso. apply (HresV (res + j)); lia. }
  (* the shadow byte of the node: 0, because the node is addressable and 8-aligned *)
  destruct (HVRA (pe_v en + 7) ltac:(lia)) as (s0 & Hs0v & Hs0ok).
  assert (Es0 : s0 = 0).
  { unfold saddr_ok in Hs0ok. assert (E7 : (pe_v en + 7) mod 8 = 7) by (Z.div_mod_to_equations; lia). lia. }
  subst s0.
  assert (Esh : shadow_of_addr SHADOW_OFF (pe_v en + 7) = pe_v en / 8 + SHADOW_OFF)
    by (unfold shadow_of_addr; Z.div_mod_to_equations; lia).
  rewrite Esh in Hs0v. unfold aview in Hs0v.
  destruct (mbyte SEGS (mrestrict (w_H W2) mem) (pe_v en / 8 + SHADOW_OFF)) as [sb|] eqn:Esb;
    [|discriminate Hs0v].
  cbn [option_map] in Hs0v. injection Hs0v as Hsb.
  assert (Hrdv : rdn SEGS (mrestrict (w_H W2) mem) (Z_to_bv 64 (pe_v en / 8 + SHADOW_OFF)) 1 = Some [sb]).
  { apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
    cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Esb. }
  (* the shadow byte of the cursor: 0, because the cursor is on the real stack *)
  assert (SHQ : aview SEGS (w_H W2) mem (SHADOW_OFF + pe_q en / 8) = Some 0).
  { apply (alx_zshadow_byte SEGS B ARx LAWS lyc Sc Hpc W2 mem md2 (pe_q en) HAR). rewrite Elo, Ehi. lia. }
  assert (SHB : SHADOW_OFF + pe_q en / 8 < pe_v en \/ pe_v en + 4 <= SHADOW_OFF + pe_q en / 8)
    by (unfold SHADOW_OFF, kLowMemEnd, kHighMemBeg, kHighMemEnd in *; lia).
  assert (SHQ1 : aview SEGS (w_H W2) mem1 (SHADOW_OFF + pe_q en / 8) = Some 0).
  { rewrite <- SHQ. rewrite Emem1. apply pnF_aview_out; rewrite ?pnF_wtl_len;
      [lia | lia | unfold SHADOW_OFF in *; lia | exact SHB]. }
  unfold aview in SHQ1.
  destruct (mbyte SEGS (mrestrict (w_H W2) mem1) (SHADOW_OFF + pe_q en / 8)) as [sq|] eqn:Esq;
    [|discriminate SHQ1].
  cbn [option_map] in SHQ1. injection SHQ1 as Hsq.
  assert (Hrdq : rdn SEGS (mrestrict (w_H W2) mem1) (Z_to_bv 64 (SHADOW_OFF + pe_q en / 8)) 1 = Some [sq]).
  { apply rdn_mbytes. split; [reflexivity|]. intros ii Hii. assert (ii = 0%nat) as -> by lia.
    cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Esq. }
  (* ---- 0x86864 srli a0,s3,3 ---- *)
  set (R1 := YK11.regupd regs 10%bv (w64 (pe_v en / 8))).
  pnF_fetch_tac 20888 (ShiftImm ALU_SRL 10%bv 19%bv 3%bv).
  apply (pnF_step W2 fx' regs 20888 mem md2 md2 _ R1 20892 (same_but_materialized_refl md2)).
  { rewrite (step_srli _ _ _ _ _ _ _ _ _ Hf He Hd), R19, pnF_next. unfold YK11.v_srli, w64.
    rewrite YK00.u64_lit by lia. rewrite Z.shiftr_div_pow2 by (vm_compute; discriminate).
    replace (2 ^ bv_unsigned (3%bv : bv 6)) with 8 by (vm_compute; reflexivity). reflexivity. }
  clear Hf He Hd. intros md3 Hsm3.
  assert (A1 : getr R1 10%bv = w64 (pe_v en / 8)) by (unfold R1; apply getr_same; discriminate).
  assert (HF1 : pnF_frame R1 regs)
    by (unfold R1; apply pnF_frame_upd; [left; reflexivity | apply pnF_frame_refl]).
  clearbody R1.
  (* ---- 0x86868 add a0,a0,s7 ---- *)
  set (R2' := YK11.regupd R1 10%bv (w64 (pe_v en / 8 + SHADOW_OFF))).
  pnF_fetch_tac 20892 (Op ALU_ADD 10%bv 10%bv 23%bv).
  apply (pnF_step W2 fx' R1 20892 mem md2 md3 _ R2' 20896 Hsm3).
  { rewrite (step_add _ _ _ _ _ _ _ _ _ Hf He Hd), A1, (HF1 23%bv) by discriminate.
    rewrite R23, pnF_next. unfold YK11.v_add, w64. rewrite !YK00.u64_lit by (unfold SHADOW_OFF; lia).
    reflexivity. }
  clear Hf He Hd. intros md4 Hsm4.
  assert (A2 : getr R2' 10%bv = w64 (pe_v en / 8 + SHADOW_OFF)) by (unfold R2'; apply getr_same; discriminate).
  assert (HF2 : pnF_frame R2' regs) by (unfold R2'; apply pnF_frame_upd; [left; reflexivity | exact HF1]).
  clearbody R2'.
  (* ---- 0x8686c lb a0,0(a0) ---- *)
  set (R3' := YK11.regupd R2' 10%bv (w64 0)).
  pnF_fetch_tac 20896 (Load SZ1 true 10%bv 10%bv 0%bv).
  apply (pnF_step W2 fx' R2' 20896 mem md2 md4 _ R3' 20900 Hsm4).
  { rewrite (step_lb _ _ _ _ _ _ _ _ _ sb Hf He Hd).
    - replace (v_lb sb) with (w64 0) by (unfold w64; symmetry; apply YCbn.v_lb_zero; exact Hsb).
      rewrite pnF_next. reflexivity.
    - rewrite A2. unfold w64. rewrite YCbn.v_addi_lit. pnF_bvs. rewrite Z.add_0_r. exact Hrdv. }
  clear Hf He Hd. intros md5 Hsm5.
  assert (A3 : getr R3' 10%bv = w64 0) by (unfold R3'; apply getr_same; discriminate).
  assert (HF3 : pnF_frame R3' regs) by (unfold R3'; apply pnF_frame_upd; [left; reflexivity | exact HF2]).
  clearbody R3'.
  (* ---- 0x86870 bnez a0 -> 0x868e0 (the check arm): not taken ---- *)
  pnF_fetch_tac 20900 (Branch BC_NE 10%bv 0%bv 112%bv).
  apply (pnF_step W2 fx' R3' 20900 mem md2 md5 _ R3' 20904 Hsm5).
  { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnF_next; reflexivity|].
    rewrite A3, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. reflexivity. }
  clear Hf He Hd. intros md6 Hsm6.
  (* ---- 0x86874 li a0,3 ---- *)
  set (R4' := YK11.regupd R3' 10%bv (w64 3)).
  pnF_fetch_tac 20904 (OpImm ALU_ADD 10%bv 0%bv 3%bv).
  apply (pnF_step W2 fx' R3' 20904 mem md2 md6 _ R4' 20908 Hsm6).
  { rewrite (step_addi _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite getr_zero, pnF_next.
    unfold YK11.v_addi, w64. pnF_bvs. rewrite YK00.u64_lit by lia. reflexivity. }
  clear Hf He Hd. intros md7 Hsm7.
  assert (A4 : getr R4' 10%bv = w64 3) by (unfold R4'; apply getr_same; discriminate).
  assert (HF4 : pnF_frame R4' regs) by (unfold R4'; apply pnF_frame_upd; [left; reflexivity | exact HF3]).
  clearbody R4'.
  (* ---- 0x86878 sw a0,0(s3): v->type := 3 ---- *)
  pnF_fetch_tac 20908 (Store SZ4 19%bv 10%bv 0%bv).
  apply (pnF_step_m W2 fx' R4' 20908 mem md2 md7 _ R4' 20912
    (wbytes (mrestrict (w_H W2) mem) (Z_to_bv 64 (pe_v en)) (word_to_le_bytes 4 (Z_to_bv 64 3))) Hsm7 HMN).
  { rewrite (step_sw_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (pe_v en)) (Z_to_bv 64 3) Hf He Hd).
    - rewrite pnF_next. reflexivity.
    - rewrite (HF4 19%bv) by discriminate. rewrite R19. unfold w64.
      rewrite YCbn.v_addi_lit. pnF_bvs. rewrite Z.add_0_r. reflexivity.
    - rewrite A4. reflexivity.
    - apply pnF_store_ok; [| lia | lia]. intros i Hi.
      destruct (SEPV (pe_v en + i) ltac:(lia)) as (_ & _ & (Hh & b0 & Hb0) & _).
      unfold mrestrict. rewrite Hh, Hb0. discriminate. }
  clear Hf He Hd. intros md8 Hsm8 HMN1.
  change (munrestrict (w_H W2) mem (wbytes (mrestrict (w_H W2) mem) (Z_to_bv 64 (pe_v en))
    (word_to_le_bytes 4 (Z_to_bv 64 3)))) with mem1.
  change (munrestrict (w_H W2) mem (wbytes (mrestrict (w_H W2) mem) (Z_to_bv 64 (pe_v en))
    (word_to_le_bytes 4 (Z_to_bv 64 3)))) with mem1 in HMN1.
  (* ---- 0x8687c lbu a0,0(s8): the shadow byte of the cursor ---- *)
  set (R5' := YK11.regupd R4' 10%bv (w64 0)).
  pnF_fetch_tac 20912 (Load SZ1 false 10%bv 24%bv 0%bv).
  apply (pnF_step W2 fx' R4' 20912 mem1 md2 md8 _ R5' 20916 Hsm8).
  { rewrite (step_lbu _ _ _ _ _ _ _ _ _ sq Hf He Hd).
    - rewrite Hsq, pnF_next. reflexivity.
    - rewrite (HF4 24%bv) by discriminate. rewrite R24. unfold w64.
      rewrite YCbn.v_addi_lit. pnF_bvs. rewrite Z.add_0_r. exact Hrdq. }
  clear Hf He Hd. intros md9 Hsm9.
  assert (A5 : getr R5' 10%bv = w64 0) by (unfold R5'; apply getr_same; discriminate).
  assert (HF5 : pnF_frame R5' regs) by (unfold R5'; apply pnF_frame_upd; [left; reflexivity | exact HF4]).
  clearbody R5'.
  (* ---- 0x86880 bnez a0 -> 0x86940 (the check arm): not taken ---- *)
  pnF_fetch_tac 20916 (Branch BC_NE 10%bv 0%bv 192%bv).
  apply (pnF_step W2 fx' R5' 20916 mem1 md2 md9 _ R5' 20920 Hsm9).
  { rewrite (step_bne_ft _ _ _ _ _ _ _ _ _ Hf He Hd); [rewrite pnF_next; reflexivity|].
    rewrite A5, getr_zero. unfold w64. rewrite YA03.c_eq_lit by lia. reflexivity. }
  clear Hf He Hd. intros md10 Hsm10.
  (* ---- 0x86884 li s5,0 ---- *)
  set (R6' := YK11.regupd R5' 21%bv (w64 0)).
  pnF_fetch_tac 20920 (OpImm ALU_ADD 21%bv 0%bv 0%bv).
  apply (pnF_step W2 fx' R5' 20920 mem1 md2 md10 _ R6' 20924 Hsm10).
  { rewrite (step_addi _ _ _ _ _ _ _ _ _ Hf He Hd). rewrite getr_zero, pnF_next.
    unfold YK11.v_addi, w64. pnF_bvs. rewrite YK00.u64_lit by lia. reflexivity. }
  clear Hf He Hd. intros md11 Hsm11.
  assert (A6 : getr R6' 21%bv = w64 0) by (unfold R6'; apply getr_same; discriminate).
  assert (HF6 : pnF_frame R6' regs) by (unfold R6'; apply pnF_frame_upd; [right; reflexivity | exact HF5]).
  clearbody R6'.
  (* ---- 0x86888 sd s6,0(s4): in->p := p1 + m, and T ---- *)
  pnF_fetch_tac 20924 (Store SZ8 20%bv 22%bv 0%bv).
  apply (pnF_step_m W2 fx' R6' 20924 mem1 md2 md11 _ R6' 20928
    (wbytes (mrestrict (w_H W2) mem1) (Z_to_bv 64 (pe_q en))
       (word_to_le_bytes 8 (Z_to_bv 64 (pn_p1 en (c :: y) + Z.of_nat m)))) Hsm11 HMN1).
  { rewrite (step_sd_at _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (pe_q en))
      (Z_to_bv 64 (pn_p1 en (c :: y) + Z.of_nat m)) Hf He Hd).
    - rewrite pnF_next. reflexivity.
    - rewrite (HF6 20%bv) by discriminate. rewrite R20. unfold w64.
      rewrite YCbn.v_addi_lit. pnF_bvs. rewrite Z.add_0_r. reflexivity.
    - rewrite (HF6 22%bv) by discriminate. exact R22.
    - apply pnF_store_ok; [| lia | lia]. intros i Hi.
      destruct (SEPQ (pe_q en + i) ltac:(lia)) as (_ & _ & _ & (Hh & b0 & Hb0) & _).
      assert (E : mrestrict (w_H W2) mem1 (Z_to_bv 64 (pe_q en + i)) =
                  mrestrict (w_H W2) mem (Z_to_bv 64 (pe_q en + i))).
      { rewrite Emem1. apply pnF_wb_out; rewrite ?pnF_wtl_len;
          [lia | lia | rewrite YK00.u64_lit by lia; lia]. }
      rewrite E. unfold mrestrict. rewrite Hh, Hb0. discriminate. }
  clear Hf He Hd. intros md12 Hsm12 HMN2.
  change (munrestrict (w_H W2) mem1 (wbytes (mrestrict (w_H W2) mem1) (Z_to_bv 64 (pe_q en))
    (word_to_le_bytes 8 (Z_to_bv 64 (pn_p1 en (c :: y) + Z.of_nat m))))) with mem2.
  change (munrestrict (w_H W2) mem1 (wbytes (mrestrict (w_H W2) mem1) (Z_to_bv 64 (pe_q en))
    (word_to_le_bytes 8 (Z_to_bv 64 (pn_p1 en (c :: y) + Z.of_nat m))))) with mem2 in HMN2.
  (* ---- T ---- *)
  apply KT. unfold pn_at_T.
  exists fx', R6', mem2, Y, fa, fl, pos, lyc, Sc, Hpc, k, 0.
  split; [reflexivity|]. split; [exact HFZ|]. split; [exact HFK|].
  split; [exact (pnF_keep_regs en regs R6' Y fa HKR HF6)|].
  split; [exact A6|].
  split; [exact (POST md12 Hsm12)|]. split; [|exact HMN2].
  unfold pn_out. exists c, y. cbv zeta.
  split; [exact Hskip|]. do 6 (split; [assumption|]).
  right; right; right. split; [reflexivity|]. split; [exact HLEAD|].
  exists m, res, bits.
  split; [exact Hm|]. split; [exact HSPAN|]. split; [exact HSTOP|]. split; [exact OK1|].
  split; [exact HFRS|]. split; [exact HROOM|]. split; [exact HQP|]. split; [exact RD1|].
  split; [exact V3|]. split; [exact Mstr1|]. split; [exact Mnum1|]. split; [exact Gres1|].
  split; [exact HSTR | exact Hfin].
Qed.

End c.
