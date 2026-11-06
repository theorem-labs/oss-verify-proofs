(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, a working branch), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, with its module names changed; 2359 of its 2428 lines of code are new or changed and 512 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_crt1: the image-A segment +0x4fc .. +0x5f8 of libreac/fuzz_decode's
   LLVMFuzzerTestOneInput, from llvm_a_st_4fc to llvm_a_st_5fc (Theorem llvm_a_crt1_ok : llvm_a_crt1_stmt,
   LLVMFuzzerTestOneInput_segs.v). Proves no function (kind: segment lemma).
   - c1_A: the decode-result check (the `bne a0,a1` at +0x524 into the abort block refuted) and, on a refused decode,
     the scan loop L1 (+0x544 .. +0x570) by induction on the count still to scan (c1_loop, the released fd_down.v
     scan-loop form): each byte's shadow fast path is shown to pass by the token engine, so its slow path and the
     inline __asan_report_load1 (+0x578 .. +0x584) are never stepped;
   - c1_B: slot 32(s1) := ns, then check_round_trip #1 at +0x5b4 by the statement's premise (c1_Bcrt) or one of the
     two skips (`blez a0`, `blt a1,s10`);
   - c1_T3 / c1_T2: check_braid #1 at +0x5d4 (c1_braid_call), __asan_memset at +0x5e4 (c1_memset_call, YC85.v
     aj_intrin_atS) and reac_decode_plain_le at +0x5f8 (c1_plain_call), the leaves through the shared bridge
     LLVMFuzzerTestOneInput_leafb.v (dec_leafb_journal).
   The engine idiom is fuzz_boxreg's ReadName.v (paj_run / paj_branch, awr_ok, the shadow token engine). *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow PaJournal DecodeSyms DecodeList
  DecodeAddr DecodePa DecodePaLib DecodeImg YC81 YC4b YC1g YC1h YC85 DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import DecodeCallocKit.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import check_round_trip_cg LLVMFuzzerTestOneInput_cg
  LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require ReacDecodeLib.
Module RDL := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.ReacDecodeLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* YC4b switches lia's division handling off for its importers; this file's arithmetic needs it. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

(* ------------------------------------------------------------------ *)
(* 0. The braid geometry (image A's reac_decode_c / check_braid_c)     *)
(* ------------------------------------------------------------------ *)

(* lib/Prog/SlotDownB.v even_mod2 / braid_pos_off and lib/Prog/reac_upstream_decode.v braid_pos_lin' /
   braid_byte_at', at image A's braid_pos / braid_off / braid_byte (the same text in lib/A/Prog/reac_decode_c.v and
   lib/A/Prog/check_braid_c.v). *)
Lemma c1_even_mod2 : forall ch, Z.even ch = (ch mod 2 =? 0).
Proof.
  intros ch. destruct (Z.Even_or_Odd ch) as [[q E]|[q E]].
  - rewrite (proj2 (Z.even_spec ch)) by (exists q; exact E). symmetry. apply Z.eqb_eq. subst. Z.div_mod_to_equations. lia.
  - assert (Z.even ch = false) by (rewrite <- Z.negb_odd; rewrite (proj2 (Z.odd_spec ch)) by (exists q; exact E); reflexivity).
    rewrite H. symmetry. apply Z.eqb_neq. subst. Z.div_mod_to_equations. lia.
Qed.

Lemma c1_braid_pos_off : forall s ch nch j, 0 <= ch -> 0 <= j < 3 ->
  CDec.braid_pos s ch nch j = 3 * (s * nch + 2 * (ch / 2)) + DCBc.braid_off ch j.
Proof.
  intros s ch nch j Hch Hj. unfold CDec.braid_pos, DCBc.braid_off. rewrite c1_even_mod2.
  assert (D : ch - ch mod 2 = 2 * (ch / 2)) by (Z.div_mod_to_equations; lia).
  rewrite D. destruct (ch mod 2 =? 0); destruct (Z.eqb_spec j 0); destruct (Z.eqb_spec j 1); lia.
Qed.

Lemma c1_braid_pos_lin : forall s ch nch k, 0 <= k < 3 ->
  CDec.braid_pos s ch nch k = 3 * (s * nch + (ch - ch mod 2)) +
    (if k =? 0 then 3 + ch mod 2 else if k =? 1 then 5 * (ch mod 2) else 1 + ch mod 2).
Proof.
  intros s ch nch k Hk. unfold CDec.braid_pos.
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  destruct (Z.eqb_spec (ch mod 2) 0) as [E|E];
  destruct (Z.eqb_spec k 0); destruct (Z.eqb_spec k 1); try rewrite E; lia.
Qed.

Lemma c1_braid_byte_at : forall bs nch ns ch s k, 0 <= ch -> 0 <= s < ns -> 0 <= k < 3 ->
  CDec.braid_byte bs nch ns (3 * (ch * ns + s) + k) = nth (Z.to_nat (50 + CDec.braid_pos s ch nch k)) bs (Z_to_bv 8 0).
Proof.
  intros bs nch ns ch s k Hch Hs Hk. unfold CDec.braid_byte.
  destruct (RDL.braid_div ch s k ns Hch Hs Hk) as (D1 & D2 & D3 & D4). rewrite D1, D2, D3, D4. reflexivity.
Qed.

(* lib/Prog/SlotDownB.v braid_map_of, read through a reader: the braid relation check_round_trip's contract asks
   (dec_crt_braid), from the decoder's output at out and the frame copy at res. *)
Lemma c1_crt_braid : forall (rd : reader) out res (body : list byte) nch ns,
  (forall j, (j < length (CDec.braid_out body nch ns))%nat ->
     rd (out + Z.of_nat j) = Some (bv_unsigned (nth j (CDec.braid_out body nch ns) (Z_to_bv 8 0)))) ->
  (forall j, (j < length body)%nat -> rd (res + Z.of_nat j) = Some (bv_unsigned (nth j body (Z_to_bv 8 0)))) ->
  50 + 3 * nch * ns <= Z.of_nat (length body) -> 0 < nch -> nch mod 2 = 0 -> 0 < ns ->
  dec_crt_braid rd (res + 50) out nch ns.
Proof.
  intros rd out res body nch ns HB HF HL Hnch Hev Hns ch s j Hch Hs Hj.
  exists (bv_unsigned (nth (Z.to_nat (50 + CDec.braid_pos s ch nch j)) body (Z_to_bv 8 0))).
  pose proof (Z.mod_pos_bound ch 2 ltac:(lia)) as Hm.
  assert (ch - ch mod 2 <= nch - 2) by (Z.div_mod_to_equations; lia).
  assert (s * nch <= (ns - 1) * nch) by nia.
  assert (ch * ns <= (nch - 1) * ns) by nia.
  assert (BP : 0 <= CDec.braid_pos s ch nch j <= 3 * nch * ns - 1).
  { rewrite c1_braid_pos_lin by lia.
    destruct (Z.eqb_spec j 0); destruct (Z.eqb_spec j 1); cbv beta iota; split; nia. }
  assert (LB : length (CDec.braid_out body nch ns) = Z.to_nat (3 * nch * ns)).
  { unfold CDec.braid_out. apply RDL.length_mapseq. }
  split.
  - assert (NE : nth_error (CDec.braid_out body nch ns) (Z.to_nat (3 * (ch * ns + s) + j)) =
                 Some (CDec.braid_byte body nch ns (3 * (ch * ns + s) + j))).
    { unfold CDec.braid_out. rewrite RDL.nth_error_mapseq by nia. cbn [Nat.add]. rewrite Z2Nat.id by nia. reflexivity. }
    replace (out + 3 * (ch * ns + s) + j) with (out + Z.of_nat (Z.to_nat (3 * (ch * ns + s) + j))) by nia.
    rewrite HB by (rewrite LB; nia).
    rewrite (nth_error_nth _ _ _ NE). rewrite c1_braid_byte_at by lia. reflexivity.
  - replace (res + 50 + 3 * (s * nch + 2 * (ch / 2)) + DCBc.braid_off ch j)
      with (res + Z.of_nat (Z.to_nat (50 + CDec.braid_pos s ch nch j)))
      by (rewrite Z2Nat.id by lia; rewrite c1_braid_pos_off by lia; lia).
    apply HF. lia.
Qed.

(* The spill area at s1 the segment reads (+0x4fc..+0x5f0) and writes (+0x58c), as one region on atom 9 (s1):
   eight 8-byte slots at s1 + 32 .. s1 + 88, named by the atoms 33, 32, 34 .. 39 of the environment. *)
Definition c1_spill (wlo whi : Z) : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 96 wlo whi
    [YP09.mkChunk 32 (CVal 8 (SOff 33 0)); YP09.mkChunk 40 (CVal 8 (SOff 32 0));
     YP09.mkChunk 48 (CVal 8 (SOff 34 0)); YP09.mkChunk 56 (CVal 8 (SOff 35 0));
     YP09.mkChunk 64 (CVal 8 (SOff 36 0)); YP09.mkChunk 72 (CVal 8 (SOff 37 0));
     YP09.mkChunk 80 (CVal 8 (SOff 38 0)); YP09.mkChunk 88 (CVal 8 (SOff 39 0))].
Definition c1_facts : facts := mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (32%nat, mkAF SB SB 0)] [] [].
(* The state at pc with the spill area written in [wlo, whi) only: empty (32, 32) where the code stores nothing,
   the slot 32(s1) (32, 40) from +0x58c on. *)
Definition c1_ss (pc wlo whi : Z) : sstate := mkSS pc sr_atoms [c1_spill wlo whi] None c1_facts.
Definition c1_extra (v32 nch64 len mode out nch32 ns64 : Z) : list word :=
  [w64 SB; w64 v32; w64 nch64; w64 len; w64 mode; w64 out; w64 nch32; w64 ns64].

(* a1 as the run leaves it at the `bne a0,a1` of +0x524: ((((nch & 1) <u 1) & ((wf & fits0) & fits481)) - 1) | ns,
   over the atoms 34 (nch), 26 (s10 = wf), 33 (slot 32 = fits0), 18 (s2 = the +0x4d0 size test) and 39 (ns). *)
Definition c1_a1 : sv :=
  SAlu ALU_OR
    (SAlu ALU_ADD
       (SAlu ALU_AND (SAlu ALU_SLTU (SAlu ALU_AND (SOff 34 0) (SLit 1)) (SLit 1))
          (SAlu ALU_AND (SAlu ALU_AND (SOff 26 0) (SOff 33 0)) (SOff 18 0)))
       (SLit (-1)))
    (SOff 39 0).

Lemma c1_lor_ones : forall s, 0 <= s < 2 ^ 64 -> Z.lor (2 ^ 64 - 1) s = 2 ^ 64 - 1.
Proof.
intros s Hs. apply Z.bits_inj'. intros n Hn. rewrite Z.lor_spec.
replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity.
destruct (Z.lt_ge_cases n 64) as [Hl|Hg].
- rewrite Z.ones_spec_low by lia. reflexivity.
- rewrite Z.ones_spec_high by lia. cbn [orb].
  destruct (Z.eq_dec s 0) as [->|Hnz]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
  apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

Lemma c1_a1_U : forall E wf f0 f481 n64 s64,
  U E (SOff 26 0) = wf -> U E (SOff 33 0) = f0 -> U E (SOff 18 0) = f481 -> U E (SOff 34 0) = n64 ->
  U E (SOff 39 0) = s64 -> (wf = 0 \/ wf = 1) -> (f0 = 0 \/ f0 = 1) -> (f481 = 0 \/ f481 = 1) ->
  0 <= n64 < 2 ^ 64 -> 0 <= s64 < 2 ^ 64 ->
  U E c1_a1 = if (wf =? 1) && (f0 =? 1) && (f481 =? 1) && (n64 mod 2 =? 0) then s64 else 2 ^ 64 - 1.
Proof.
intros E wf f0 f481 n64 s64 Hw H0 H4 Hn Hs Bw B0 B4 Rn Rs. unfold c1_a1.
rewrite !U_SAlu, !U_SLit, Hw, H0, H4, Hn, Hs. cbn [zalu_raw].
replace (Z.land n64 (zcanon 1)) with (n64 mod 2)
  by (change (zcanon 1) with (Z.ones 1); rewrite Z.land_ones by lia; reflexivity).
assert (Hm : 0 <= n64 mod 2 < 2) by (apply Z.mod_pos_bound; lia).
destruct Bw as [-> | ->]; destruct B0 as [-> | ->]; destruct B4 as [-> | ->];
(destruct (Z.eqb_spec (n64 mod 2) 0) as [Hz|Hz]; [rewrite Hz | replace (n64 mod 2) with 1 by lia]);
cbn [Z.eqb andb Pos.eqb];
lazymatch goal with |- zcanon (Z.lor ?u s64) = _ => let v := eval vm_compute in u in change u with v end;
first [ rewrite Z.lor_0_l; apply zcanon_id; unfold M64; lia
      | rewrite c1_lor_ones by lia; reflexivity ].
Qed.

(* The C-level reading of the two checks: under dec_a_mode_ok's ranges of nch / ns, reac_decode's success is the
   harness's wellformed && fits0 && size test && nch even, and reac_decode_plain_le's the same without the parity. *)
Lemma c1_dec_bits : forall len bs nch ns, -128 <= nch <= 127 -> -128 <= ns <= 127 ->
  CDec.decode_ok len bs nch ns =
    (CInsp.inspect_wf len bs && (dec_a_fits0 nch ns =? 1) && (dec_a_prod nch ns <? 481) && ((nch mod 2 ^ 64) mod 2 =? 0)) /\
  CPlain.plain_ok len bs nch ns = (CInsp.inspect_wf len bs && (dec_a_fits0 nch ns =? 1) && (dec_a_prod nch ns <? 481)).
Proof.
intros len bs nch ns Hn Hs. unfold CDec.decode_ok, CPlain.plain_ok, dec_a_fits0, dec_a_prod.
destruct (CInsp.inspect_wf len bs); cbn [andb]; [|split; reflexivity].
destruct (Z.ltb_spec 0 nch) as [Pn|Pn]; destruct (Z.ltb_spec 0 ns) as [Ps|Ps]; cbn [andb Z.eqb Pos.eqb];
  rewrite ?andb_false_r; try (split; reflexivity).
rewrite (Z.mod_small nch (2 ^ 32)), (Z.mod_small ns (2 ^ 32)), (Z.mod_small (nch * ns) (2 ^ 64)),
  (Z.mod_small nch (2 ^ 64)) by nia.
rewrite ?andb_true_r.
destruct (Z.leb_spec (nch * ns) 480); destruct (Z.ltb_spec (nch * ns) 481); try lia; cbn [andb];
  rewrite ?andb_true_r, ?andb_false_r; split; reflexivity.
Qed.

(* s8 as the run leaves it at +0x50c: (s10 & 32(s1)) & s2, the plain check's `wellformed && fits` of the next
   segment's +0x604. *)
Definition c1_s8 : sv := SAlu ALU_AND (SAlu ALU_AND (SOff 26 0) (SOff 33 0)) (SOff 18 0).

Lemma c1_s8_U : forall E wf f0 f481, U E (SOff 26 0) = wf -> U E (SOff 33 0) = f0 -> U E (SOff 18 0) = f481 ->
  (wf = 0 \/ wf = 1) -> (f0 = 0 \/ f0 = 1) -> (f481 = 0 \/ f481 = 1) ->
  U E c1_s8 = if (wf =? 1) && (f0 =? 1) && (f481 =? 1) then 1 else 0.
Proof.
intros E wf f0 f481 Hw H0 H4 Bw B0 B4. unfold c1_s8. rewrite !U_SAlu, Hw, H0, H4.
destruct Bw as [-> | ->]; destruct B0 as [-> | ->]; destruct B4 as [-> | ->]; vm_compute; reflexivity.
Qed.

Lemma c1_bit_eqb : forall b : bool, ((if b then 1 else 0) =? 1) = b.
Proof. intros [|]; reflexivity. Qed.
Lemma c1_bit01 : forall b : bool, (if b then 1 else 0) = 0 \/ (if b then 1 else 0) = 1.
Proof. intros [|]; [right | left]; reflexivity. Qed.

(* A word in the signed range reads back as itself, and the two signed branch conditions on such words. *)
Lemma c1_signed : forall z, -2 ^ 63 <= z < 2 ^ 63 -> bv_signed (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_signed. apply swrap64_id. unfold half64. lia. Qed.
Lemma c1_br_ge : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_GE (Z_to_bv 64 a) (Z_to_bv 64 b) = negb (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !c1_signed by lia. reflexivity. Qed.
Lemma c1_lit_mod : forall z, Z_to_bv 64 (z mod 2 ^ 64) = Z_to_bv 64 z.
Proof.
intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma c1_br_lt : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  branch_taken BC_LT (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. cbn [branch_taken]. unfold bv_lts. rewrite !c1_signed by lia. reflexivity. Qed.

(* An atom below the run's fresh atoms reads the same in the run's environment. *)
Lemma c1_U_agree : forall E E0 (n : nat), (forall m, (m < 512)%nat -> ew E m = ew E0 m) -> (n < 512)%nat ->
  U E (SOff n 0) = U E0 (SOff n 0).
Proof. intros E E0 n AG Hn. rewrite !U_SOff, (AG n Hn). reflexivity. Qed.
Lemma c1_denot_soff : forall E E0 (n : nat) v, (forall m, (m < 512)%nat -> ew E m = ew E0 m) -> (n < 512)%nat ->
  ew E0 n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof.
intros E E0 n v AG Hn Hv. rewrite denot_lit_U, U_SOff, (AG n Hn), Hv. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold bv_wrap, zcanon, M64. change (bv_modulus 64) with (2 ^ 64). rewrite Z.add_0_r, !Z.mod_mod by lia. reflexivity.
Qed.

Section crt1. Context {rc : YM05.RunCeil}.
(* The Variables of LLVMFuzzerTestOneInput_segs.v's Section seg, in its order. *)
Local Abbreviation tfib_sink_head := dec_A_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variable asink_img_laws : list Segment -> asyms -> asink_syms -> Prop.
Variable ro_below_ofl : list Segment -> Z -> Z -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.
Local Abbreviation dec_base := (dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI).

Lemma c1_rdword_range : forall (W : world segs) mem a v,
  rdword (aview segs (w_H W) mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros W mem a v H. unfold rdword in H.
repeat match type of H with context [aview segs (w_H W) mem ?x] =>
  let Hx := fresh "Hx" in destruct (aview segs (w_H W) mem x) eqn:Hx; [|discriminate H];
  apply (aview_byte segs) in Hx; destruct Hx as (? & _ & -> & ?) end.
injection H as <-. lia.
Qed.

(* The fields of dec_a_core and of the journal this segment reads, each found by its type (no positional destruct of
   the interface's conjunctions). *)
Lemma c1_core_J : forall cx ly' S' (W : world segs) regs mem md k, dec_a_core B cx ly' S' W regs mem md k ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W mem md k.
Proof. intros cx ly' S' W regs mem md k H. unfold dec_a_core in H. decompose [and] H. assumption. Qed.
Lemma c1_core_facts : forall cx ly' S' (W : world segs) regs mem md k, dec_a_core B cx ly' S' W regs mem md k ->
  YK11.getr regs 8 = w64 (d_sp0 cx) /\ YK11.getr regs 9 = w64 (d_sp1 cx) /\ spZ regs = d_sp1 cx /\
  d_sp0 cx - 240 <= d_sp1 cx /\ d_sp1 cx <= d_sp0 cx - 224 /\ d_sp1 cx mod 32 = 0 /\
  YK11.getr regs 3 = w64 (as_gp B) /\ YK11.getr regs 4 = w64 (as_tp B) /\
  4096 <= d_F cx /\ d_F cx mod 32 = 0 /\ frames S' = [(DEC_FCLASS, d_fpos cx)].
Proof. intros cx ly' S' W regs mem md k H. unfold dec_a_core in H. decompose [and] H. repeat split; assumption. Qed.
Lemma c1_J_facts : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W : world segs) mem md k,
  @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem md k ->
  AR segs B ly' S' W mem md /\ astk_ok STK ly sp0 /\ (forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) mem a) /\
  st_nev S' <= st_nev S + k /\ frames S' = own ++ frames S.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem md k H. unfold ajournal in H. decompose [and] H.
refine (conj _ (conj _ (conj _ (conj _ _)))); assumption.
Qed.
Lemma c1_stk_facts : forall STK ly sp0, astk_ok STK ly sp0 ->
  sp0 mod 16 = 0 /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= sp0 /\ sp0 <= ly_stk_hi ly /\
  ly_stk_hi ly <= 2 ^ 47 /\ ly_bot ly + STK < sp0 + ASTACK /\ sp0 <= ly_top ly /\ ly_top ly <= ly_stk_hi ly.
Proof. intros STK ly sp0 H. unfold astk_ok in H. decompose [and] H. repeat split; assumption. Qed.

(* The registers the run +0x4fc .. +0x58c leaves as they were, on both of its paths: all but a1 .. a6, s2, s6, s8
   and s10. *)
Definition c1_keepA : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 19; 20; 21; 23; 25; 27; 28; 29; 30; 31]%bv.

(* The write rights of a run: read-only regions, or the spill region on s1 (atom 9) inside the caller's stack
   window; the base of s1 is found in any hypothesis `bv_unsigned (ew _ 9) = sp1` about the run's environment. *)
Ltac c1_awr Ex sp0 sp1 :=
  lazymatch goal with |- awr_ok ?Ey ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ey rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
  [ apply awr_ok_nil
  | apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]
  | eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 9%nat (sp1 - sp0));
    [ reflexivity
    | repeat match goal with H : bv_unsigned (ew ?Ez 9) = sp1 |- context [bv_unsigned (ew ?Ez 9)] => rewrite H end; lia
    | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia |] ].

(* What a run whose regions write nothing leaves of the memory: all of it. *)
Ltac c1_nowin HF :=
  let x := fresh "x" in intros x; apply HF;
  let r := fresh "r" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
  intros (r & Hin & Ha); cbn [In ss_mem c1_ss c1_spill] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [subst r; cbn [YP09.r_wlo YP09.r_whi c1_spill] in Ha; lia |]); destruct Hin.

(* A register's symbolic value at a state, without unfolding its denotation. *)
Ltac c1_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict YK11.mkst] in Hr
  end.

Section F. Context {fx : YK11.FPState}.
Hypothesis LAWS : AR_laws segs B.
Let RUN := @paj_run fx rc dec_A_sink_head decode_listing PL_decode PI_decode B LAWS.
Let RUNTO := @paj_run_to fx rc dec_A_sink_head decode_listing PL_decode PI_decode B LAWS.
Let BR := @paj_branch fx rc decode_listing PI_decode.

Lemma c1_entry : forall pc wlo whi (W : world segs) regs mem sp1 v32 nch64 len mode out nch32 ns64,
  wlo = 32 -> (whi = 32 \/ whi = 40) ->
  YK11.getr regs 9 = w64 sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 ->
  rdword (aview segs (w_H W) mem) (sp1 + 32) = Some v32 ->
  rdword (aview segs (w_H W) mem) (sp1 + 40) = Some SB ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some nch64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some len ->
  rdword (aview segs (w_H W) mem) (sp1 + 64) = Some mode ->
  rdword (aview segs (w_H W) mem) (sp1 + 72) = Some out ->
  rdword (aview segs (w_H W) mem) (sp1 + 80) = Some nch32 ->
  rdword (aview segs (w_H W) mem) (sp1 + 88) = Some ns64 ->
  (forall o, 32 <= o < 40 -> apresent (w_H W) mem (sp1 + o)) ->
  st_ok_pi (pa_segs (L := decode_listing)) pa_val (Eimg (Ereg regs (c1_extra v32 nch64 len mode out nch32 ns64)))
    (c1_ss pc wlo whi)
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (pa_val A_TEXT + pc)) mem (YK11.seg_rom pa_segs))).
Proof.
intros pc wlo whi W regs mem sp1 v32 nch64 len mode out nch32 ns64 Hwlo Hwhi H9 Hsp1 Hal R32 R40 R48 R56 R64 R72 R80 R88
  Hpres. subst wlo. assert (Hwh : 32 <= whi <= 40) by lia.
set (E := Eimg (Ereg regs (c1_extra v32 nch64 len mode out nch32 ns64))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (c1_extra v32 nch64 len mode out nch32 ns64)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : bv_unsigned (ew E 9) = sp1).
{ rewrite EL by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl). rewrite H9.
  apply unsigned_lit_small. lia. }
assert (EX : forall j v, (j < 8)%nat -> nth j (c1_extra v32 nch64 len mode out nch32 ns64) (Z_to_bv 64 0) = w64 v ->
  ew E (32 + j) = Z_to_bv 64 v).
{ intros j v Hjl Hj. rewrite EL by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact Hj. }
assert (E32 : ew E 32 = Z_to_bv 64 SB) by exact (EX 0%nat SB ltac:(lia) eq_refl).
assert (E33 : ew E 33 = Z_to_bv 64 v32) by exact (EX 1%nat v32 ltac:(lia) eq_refl).
assert (E34 : ew E 34 = Z_to_bv 64 nch64) by exact (EX 2%nat nch64 ltac:(lia) eq_refl).
assert (E35 : ew E 35 = Z_to_bv 64 len) by exact (EX 3%nat len ltac:(lia) eq_refl).
assert (E36 : ew E 36 = Z_to_bv 64 mode) by exact (EX 4%nat mode ltac:(lia) eq_refl).
assert (E37 : ew E 37 = Z_to_bv 64 out) by exact (EX 5%nat out ltac:(lia) eq_refl).
assert (E38 : ew E 38 = Z_to_bv 64 nch32) by exact (EX 6%nat nch32 ltac:(lia) eq_refl).
assert (E39 : ew E 39 = Z_to_bv 64 ns64) by exact (EX 7%nat ns64 ltac:(lia) eq_refl).
clear EX.
pose proof (c1_rdword_range W mem _ _ R32). pose proof (c1_rdword_range W mem _ _ R48).
pose proof (c1_rdword_range W mem _ _ R56). pose proof (c1_rdword_range W mem _ _ R64).
pose proof (c1_rdword_range W mem _ _ R72). pose proof (c1_rdword_range W mem _ _ R80).
pose proof (c1_rdword_range W mem _ _ R88).
rewrite restrict_mkst_fx. unfold c1_ss.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- destruct Hwhi as [-> | ->]; vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold c1_spill, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9. split; [lia|]. split; [lia|].
  split; [intros o Ho; apply (apresent_writable segs); apply Hpres; lia|].
  repeat apply Forall_cons; try apply Forall_nil.
  + apply (chunk_ok_val segs E _ sp1 32 8 (SOff 33 0) v32);
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ R32).
  + apply (chunk_ok_val segs E _ sp1 40 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ R40).
  + apply (chunk_ok_val segs E _ sp1 48 8 (SOff 34 0) nch64);
      [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ R48).
  + apply (chunk_ok_val segs E _ sp1 56 8 (SOff 35 0) len);
      [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ R56).
  + apply (chunk_ok_val segs E _ sp1 64 8 (SOff 36 0) mode);
      [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ R64).
  + apply (chunk_ok_val segs E _ sp1 72 8 (SOff 37 0) out);
      [cbn [sv_denot]; rewrite E37, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ R72).
  + apply (chunk_ok_val segs E _ sp1 80 8 (SOff 38 0) nch32);
      [cbn [sv_denot]; rewrite E38, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ R80).
  + apply (chunk_ok_val segs E _ sp1 88 8 (SOff 39 0) ns64);
      [cbn [sv_denot]; rewrite E39, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
    exact (val_mem_of_rdword segs _ _ _ _ R88).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [c1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9. rewrite E32, unsigned_lit_small by (unfold SB; lia).
  change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

Lemma c1_U_reg : forall regs extra (n : nat) (r : bv 5) v, Z.of_nat n = bv_unsigned r -> (n < 32)%nat ->
  YK11.getr regs r = w64 v -> 0 <= v < 2 ^ 64 -> U (Eimg (Ereg regs extra)) (SOff n 0) = v.
Proof.
intros regs extra n r v Hn H32 Hr Hv. apply U_atom; [|exact Hv].
rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs extra n r Hn). exact Hr.
Qed.

(* The scan loop L1 (+0x544 .. +0x570), one iteration at a time: the byte at a3 (a read-only region holding the
   fill), a1's range for the shadow obligation, s2 the shadow base (the token engine's Bx), a2 = 0. *)
Definition c1_lbyte : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 165))].
Definition c1_lfacts : facts := mkFacts [(11%nat, mkAF 4096 (2 ^ 47 - 16) 0); (18%nat, mkAF SB SB 0)] [] [].
Definition c1_lss : sstate := mkSS 0x544 sr_atoms [c1_lbyte] None c1_lfacts.
(* The registers the loop leaves as they were: all but a1 .. a6. *)
Definition c1_keep : list (bv 5) := [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Lemma c1_val_mem1 : forall H (m : word -> option byte) a v, aview segs H m a = Some v -> val_mem segs (mrestrict H m) a 1 v.
Proof.
intros H m a v Hv kk Hk. assert (kk = 0%nat) as -> by lia.
destruct (aview_byte segs H m a v Hv) as (b & Hb & -> & Hr). change (a + Z.of_nat 0) with (a + 0). rewrite Z.add_0_r, Hb.
f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite Z.shiftr_0_r.
rewrite !Z.mod_small by lia. reflexivity.
Qed.

Lemma c1_lentry : forall (W : world segs) regs mem x,
  YK11.getr regs 11 = w64 x -> YK11.getr regs 13 = w64 x -> YK11.getr regs 18 = w64 SB ->
  4096 <= x <= 2 ^ 47 - 16 -> aview segs (w_H W) mem x = Some 165 ->
  st_ok_pi (pa_segs (L := decode_listing)) pa_val (Eimg (Ereg regs [])) c1_lss
    (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (pa_val A_TEXT + 0x544)) mem (YK11.seg_rom pa_segs))).
Proof.
intros W regs mem x H11 H13 H18 Hx Hb.
set (E := Eimg (Ereg regs [])).
assert (EL : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; subst E; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (U13 : bv_unsigned (ew E 13) = x) by (rewrite (EL 13%nat 13%bv eq_refl), H13; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = x) by (rewrite (EL 11%nat 11%bv eq_refl), H11; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = SB) by (rewrite (EL 18%nat 18%bv eq_refl), H18; apply unsigned_lit_small; unfold SB; lia).
rewrite restrict_mkst_fx. unfold c1_lss.
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_nil].
  unfold c1_lbyte, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val segs E _ x 0 1 (SLit 165) 165); [reflexivity | zside | zside |].
  rewrite Z.add_0_r. exact (c1_val_mem1 _ _ _ _ Hb).
- cbn [pairwise_disjoint all_disjoint]. split; exact I.
- split; [|split; exact I].
  cbn [c1_lfacts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U11, U18. rewrite Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia.
Qed.

Lemma c1_soff_val : forall E E0 (n : nat) z v, (forall m, (m < 512)%nat -> ew E m = ew E0 m) -> (n < 512)%nat ->
  ew E0 n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + z < 2 ^ 64 -> sv_denot E (SOff n z) = w64 (v + z).
Proof.
intros E E0 n z v AG Hn Hv Hr Hz. rewrite denot_lit_U, U_SOff, (AG n Hn), Hv. unfold w64.
rewrite unsigned_lit_small by lia. rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

(* One iteration of L1 from its head +0x544: the shadow check of the byte at a1 (its slow path re-entering at +0x554
   discharged by the token engine, so the inline __asan_report_load1 at +0x584 is never reached), the fill byte,
   the counter, and the back edge at +0x570; on exit the `j` +0x574 and the `bnez a2` +0x588 (a2 = 0) up to +0x58c. *)
Lemma c1_iter : forall (cnt : nat) (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own ly' S' k x Q,
  @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem md k ->
  YK11.getr regs 11 = w64 x -> YK11.getr regs 13 = w64 x -> YK11.getr regs 18 = w64 SB -> YK11.getr regs 12 = w64 0 ->
  YK11.getr regs 14 = w64 (Z.of_nat cnt + 1) -> Z.of_nat cnt + 1 < 2 ^ 32 ->
  4096 <= x <= 2 ^ 47 - 16 -> aview segs (w_H W) mem x = Some 165 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF x 1 ->
  (cnt <> 0%nat -> forall regs' mem' md', (forall r, In r c1_keep -> YK11.getr regs' r = YK11.getr regs r) ->
     YK11.getr regs' 11 = w64 (x + 1) -> YK11.getr regs' 13 = w64 (x + 1) -> YK11.getr regs' 12 = w64 0 ->
     YK11.getr regs' 14 = w64 (Z.of_nat cnt) -> (forall a, mem' a = mem a) ->
     @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem' md' k ->
     SRr segs W (mkCfg (YK11.mkst regs' (w64 (DEC_A_LLVMF + 0x544)) mem' (YK11.seg_rom segs)) md') Q) ->
  (cnt = 0%nat -> forall regs' mem' md', (forall r, In r c1_keep -> YK11.getr regs' r = YK11.getr regs r) ->
     YK11.getr regs' 12 = w64 0 -> (forall a, mem' a = mem a) ->
     @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem' md' k ->
     SRr segs W (mkCfg (YK11.mkst regs' (w64 (DEC_A_LLVMF + 0x58c)) mem' (YK11.seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x544)) mem (YK11.seg_rom segs)) md) Q.
Proof.
intros cnt W regs mem md STK sp0 FP ly S W0 mem0 md0 own ly' S' k x Q HJ H11 H13 H18 H12 H14 Hc32 Hx Hb Hra KN KX.
pose proof (c1_lentry W regs mem x H11 H13 H18 Hx Hb) as HS.
pose proof (st_ok_pi_pin_reg' _ _ _ 12%bv 0 HS ltac:(cbn [ms_regs restrict YK11.mkst]; exact H12) eq_refl) as HS1.
clear HS. rename HS1 into HS.
lazymatch type of HS with st_ok_pi _ _ _ ?ss _ => let v := eval vm_compute in ss in change ss with v in HS end.
set (E := Eimg (Ereg regs [])) in HS.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (SHOK : sh_ok pa_segs (SOff 18 0) [] E (mrestrict (w_H W) mem)) by constructor.
assert (EL : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; subst E; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg regs []) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
change (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x544)) mem (YK11.seg_rom segs)) with
  (YK11.mkst regs (Z_to_bv 64 (pa_val (L := decode_listing) A_TEXT + 0x544)) mem (YK11.seg_rom pa_segs)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ (* the shadow obligation of the byte at a1 *)
  assert (U18 : U E (SOff 18 0) = SB) by (subst E; exact (c1_U_reg regs [] 18 18%bv SB eq_refl ltac:(lia) H18 ltac:(unfold SB; lia))).
  assert (U11 : U E (SOff 11 0) = x) by (subst E; exact (c1_U_reg regs [] 11 11%bv x eq_refl ltac:(lia) H11 ltac:(lia))).
  cbn [ms_mem YK11.mkst]. change (rd_of pa_segs (mrestrict (w_H W) mem)) with (aview segs (w_H W) mem).
  rewrite U18, U11. exact Hra. }
{ c1_awr E sp0 x. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG : forall m, (m < 512)%nat -> ew Ex m = ew E m) by (intros m Hm; repeat rewrite ew_ewset_other by lia; reflexivity) end.
assert (HM1 : forall a, ms_mem ms a = mem a) by c1_nowin HF.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a4 - 1 <> 0: back to the head *)
  rewrite branch_ne_U in Hc.
  rewrite U_SLit, U_SOff, (AG 14%nat ltac:(lia)), (EL 14%nat 14%bv eq_refl), H14 in Hc. unfold w64 in Hc.
  rewrite unsigned_lit_small in Hc by lia. change (zcanon 0) with 0 in Hc.
  rewrite zcanon_id in Hc by (unfold M64; lia).
  assert (Hcnt : cnt <> 0%nat) by (intros ->; cbn in Hc; discriminate Hc).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x544; [c1_awr E sp0 x |].
  assert (HM2 : forall a, ms_mem ms0 a = mem a) by (intros a; rewrite <- (HM1 a); revert a; c1_nowin HF).
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG2 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
      by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG; exact Hm]) end.
  c1_reg HS (11%bv : bv 5) R11. c1_reg HS (13%bv : bv 5) R13. c1_reg HS (12%bv : bv 5) R12. c1_reg HS (14%bv : bv 5) R14.
  eapply KN; [exact Hcnt | | | | | | exact HM2 | exact HJ].
  + intros r Hr. pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] c1_keep HS ltac:(split; [intros n Hn; rewrite AG2 by lia; apply HAE; exact Hn | reflexivity]) ltac:(vm_compute; reflexivity) r Hr) as Hk.
    exact Hk.
  + rewrite R11. apply (c1_soff_val _ E 11 1 x AG2); [lia | exact (eq_trans (EL 11%nat 11%bv eq_refl) H11) | lia | lia].
  + rewrite R13. apply (c1_soff_val _ E 13 1 x AG2); [lia | exact (eq_trans (EL 13%nat 13%bv eq_refl) H13) | lia | lia].
  + rewrite R12. reflexivity.
  + rewrite R14. replace (Z.of_nat cnt) with (Z.of_nat cnt + 1 + -1) by lia.
    apply (c1_soff_val _ E 14 (-1) (Z.of_nat cnt + 1) AG2); [lia | exact (eq_trans (EL 14%nat 14%bv eq_refl) H14) | lia | lia].
- (* a4 - 1 = 0: out of the loop, through the `j` at +0x574 and the `bnez a2` at +0x588 (a2 = 0) *)
  rewrite branch_ne_U in Hc.
  rewrite U_SLit, U_SOff, (AG 14%nat ltac:(lia)), (EL 14%nat 14%bv eq_refl), H14 in Hc. unfold w64 in Hc.
  rewrite unsigned_lit_small in Hc by lia. change (zcanon 0) with 0 in Hc.
  rewrite zcanon_id in Hc by (unfold M64; lia).
  assert (Hcnt : cnt = 0%nat) by (destruct (Z.eqb_spec (Z.of_nat cnt + 1 + -1) 0); [lia | discriminate Hc]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x58c; [c1_awr E sp0 x |].
  assert (HM2 : forall a, ms_mem ms0 a = mem a) by (intros a; rewrite <- (HM1 a); revert a; c1_nowin HF).
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG2 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
      by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG; exact Hm]) end.
  c1_reg HS (12%bv : bv 5) R12.
  eapply KX; [exact Hcnt | | | exact HM2 | exact HJ].
  + intros r Hr. pose proof (regs_kept_of_st_ok_pi _ _ _ regs [] c1_keep HS ltac:(split; [intros n Hn; rewrite AG2 by lia; apply HAE; exact Hn | reflexivity]) ltac:(vm_compute; reflexivity) r Hr) as Hk.
    exact Hk.
  + rewrite R12. reflexivity.
Qed.

Lemma c1_aview_eqm : forall H (m m' : word -> option byte), (forall x, m' x = m x) ->
  forall a, aview segs H m' a = aview segs H m a.
Proof. intros H m m' E a. apply aview_eq_of. unfold mrestrict. rewrite E. reflexivity. Qed.

(* The loop L1 by induction on the count still to scan (the released fd_down's scan loop form): from the head with
   a1 = a3 = out + i and a4 = olen - i, it reaches +0x58c with a2 = 0, every register but a1 .. a6 kept and the
   memory as it was. *)
Lemma c1_loop : forall (cnt : nat) (W : world segs) regs mem md STK sp0 FP ly St W0 mem0 md0 own ly' St' k out olen i Q,
  @ajournal rc dec_A_sink_head segs B STK sp0 FP ly St W0 mem0 md0 own ly' St' W mem md k ->
  YK11.getr regs 11 = w64 (out + i) -> YK11.getr regs 13 = w64 (out + i) -> YK11.getr regs 18 = w64 SB ->
  YK11.getr regs 12 = w64 0 -> YK11.getr regs 14 = w64 (Z.of_nat cnt + 1) ->
  0 <= i -> i + Z.of_nat cnt + 1 = olen -> olen < 2 ^ 32 -> 4096 <= out -> out + olen <= 2 ^ 47 - 16 ->
  (forall j, 0 <= j < olen -> aview segs (w_H W) mem (out + j) = Some 165) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF out olen ->
  (forall regs' mem' md', (forall r, In r c1_keep -> YK11.getr regs' r = YK11.getr regs r) ->
     YK11.getr regs' 12 = w64 0 -> (forall a, mem' a = mem a) ->
     @ajournal rc dec_A_sink_head segs B STK sp0 FP ly St W0 mem0 md0 own ly' St' W mem' md' k ->
     SRr segs W (mkCfg (YK11.mkst regs' (w64 (DEC_A_LLVMF + 0x58c)) mem' (YK11.seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x544)) mem (YK11.seg_rom segs)) md) Q.
Proof.
induction cnt as [|cnt IH]; intros W regs mem md STK sp0 FP ly St W0 mem0 md0 own ly' St' k out olen i Q
  HJ H11 H13 H18 H12 H14 Hi Holen Hol32 Hout Houtc Hfill Hra K.
- apply (c1_iter 0 W regs mem md STK sp0 FP ly St W0 mem0 md0 own ly' St' k (out + i) Q HJ H11 H13 H18 H12 H14);
    [lia | lia | rewrite <- (Hfill i ltac:(lia)); reflexivity | eapply range_addressable_sub; [exact Hra | lia | lia]
    | intros C; exfalso; exact (C eq_refl) |].
  intros _ regs' mem' md' Hk H12' HM HJ'. exact (K regs' mem' md' Hk H12' HM HJ').
- apply (c1_iter (Datatypes.S cnt) W regs mem md STK sp0 FP ly St W0 mem0 md0 own ly' St' k (out + i) Q HJ H11 H13 H18 H12 H14);
    [lia | lia | rewrite <- (Hfill i ltac:(lia)); reflexivity | eapply range_addressable_sub; [exact Hra | lia | lia] | |
     intros C; discriminate C].
  intros _ regs' mem' md' Hk H11' H13' H12' H14' HM HJ'.
  apply (IH W regs' mem' md' STK sp0 FP ly St W0 mem0 md0 own ly' St' k out olen (i + 1) Q HJ').
  + rewrite H11'. f_equal. lia.
  + rewrite H13'. f_equal. lia.
  + rewrite Hk by (cbn; tauto). exact H18.
  + exact H12'.
  + rewrite H14'. f_equal. lia.
  + lia.
  + lia.
  + exact Hol32.
  + exact Hout.
  + exact Houtc.
  + intros j Hj. rewrite (c1_aview_eqm _ _ _ HM). exact (Hfill j Hj).
  + eapply range_addressable_ext; [|exact Hra]. intros c v Hc. rewrite (c1_aview_eqm _ _ _ HM). exact Hc.
  + intros regs'' mem'' md'' Hk2 H12'' HM2 HJ''. apply K; [| exact H12'' | | exact HJ''].
    * intros r Hr. rewrite (Hk2 r Hr). exact (Hk r Hr).
    * intros a. rewrite HM2. apply HM.
Qed.

(* Stage A, +0x4fc .. +0x58c: the decode-result check (the `bne a0,a1` at +0x524 into the abort block refuted from
   reac_decode's result and the harness's own copy of its test, c1_dec_bits), s2 / s6 / s10 reloaded, and on a
   refused decode (`bgez a0` at +0x530 not taken) the scan loop L1 over the 0xa5 fill (c1_loop). No store. *)
Lemma c1_A : forall (cx : dctx) (W : world segs) ly' S' regs mem md out mode nch ns Q,
  dec_a_core B cx ly' S' W regs mem md dec_ev_4fc ->
  In (out, dec_a_olen nch ns) (ablocks B ly' S') ->
  dec_a_mode_ok cx W mem mode nch ns ->
  YK11.getr regs 10 = w64 (if CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then ns else -1) ->
  YK11.getr regs 18 = w64 (if dec_a_prod nch ns <? 481 then 1 else 0) ->
  YK11.getr regs 25 = w64 (dec_a_olen nch ns) ->
  YK11.getr regs 26 = w64 (if CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) then 1 else 0) ->
  (CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = false -> dec_a_filled W mem out (dec_a_olen nch ns)) ->
  dec_a_slot cx (aview segs (w_H W) mem) 32 (dec_a_fits0 nch ns) ->
  dec_a_slot cx (aview segs (w_H W) mem) 40 SHADOW_OFF ->
  dec_a_slot cx (aview segs (w_H W) mem) 48 (nch mod 2 ^ 64) ->
  dec_a_slot cx (aview segs (w_H W) mem) 56 (dec_a_len (d_n cx)) ->
  dec_a_slot cx (aview segs (w_H W) mem) 64 mode ->
  dec_a_slot cx (aview segs (w_H W) mem) 72 out ->
  dec_a_slot cx (aview segs (w_H W) mem) 80 (nch mod 2 ^ 32) ->
  dec_a_slot cx (aview segs (w_H W) mem) 88 (ns mod 2 ^ 64) ->
  (forall regs' mem' md',
     (forall r, In r c1_keepA -> YK11.getr regs' r = YK11.getr regs r) ->
     YK11.getr regs' 18 = w64 SHADOW_OFF -> YK11.getr regs' 22 = w64 (dec_a_len (d_n cx)) ->
     YK11.getr regs' 24 = w64 (if CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then 1 else 0) ->
     YK11.getr regs' 26 = w64 (ns mod 2 ^ 64) ->
     (forall a, mem' a = mem a) ->
     @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
       [(DEC_FCLASS, d_fpos cx)] ly' S' W mem' md' dec_ev_4fc ->
     SRr segs W (mkCfg (YK11.mkst regs' (w64 (DEC_A_LLVMF + 0x58c)) mem' (YK11.seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x4fc)) mem (YK11.seg_rom segs)) md) Q.
Proof.
intros cx W ly' S' regs mem md out mode nch ns Q HC Hin HMO H10 H18 H25 H26 HFILL S32 S40 S48 S56 S64 S72 S80 S88 K.
destruct HMO as (_ & Hnch & Hns & _ & _).
destruct (c1_dec_bits (dec_a_len (d_n cx)) (d_body cx) nch ns Hnch Hns) as (Dd & Dp).
set (len := dec_a_len (d_n cx)) in *. set (body := d_body cx) in *.
set (wf := if CInsp.inspect_wf len body then 1 else 0) in *.
set (f481 := if dec_a_prod nch ns <? 481 then 1 else 0) in *.
set (f0 := dec_a_fits0 nch ns) in *. set (olen := dec_a_olen nch ns) in *.
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (R8 & R9 & Hsp & Hs01 & Hs01' & Hal & Rgp & Rtp & _ & _ & _).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & Hstk & Hpres & _ & _).
destruct (c1_stk_facts _ _ _ Hstk) as (Ha16 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
assert (Hsp1 : 2 ^ 46 <= d_sp1 cx <= 2 ^ 47) by lia.
assert (HP32 : forall o, 32 <= o < 40 -> apresent (w_H W) mem (d_sp1 cx + o)) by (intros o Ho; apply Hpres; lia).
unfold dec_a_slot in S32, S40, S48, S56, S64, S72, S80, S88.
change SHADOW_OFF with SB in S40.
assert (Bw : wf = 0 \/ wf = 1) by (unfold wf; apply c1_bit01).
assert (B4 : f481 = 0 \/ f481 = 1) by (unfold f481; apply c1_bit01).
assert (B0 : f0 = 0 \/ f0 = 1) by (unfold f0, dec_a_fits0; apply c1_bit01).
assert (Ha0 : -128 <= (if CDec.decode_ok len body nch ns then ns else -1) <= 127)
  by (destruct (CDec.decode_ok len body nch ns); lia).
pose proof (c1_entry 0x4fc 32 32 W regs mem (d_sp1 cx) f0 (nch mod 2 ^ 64) len mode out (nch mod 2 ^ 32)
  (ns mod 2 ^ 64) eq_refl (or_introl eq_refl) R9 Hsp1 Hal S32 S40 S48 S56 S64 S72 S80 S88 HP32) as HS.
set (X := c1_extra f0 (nch mod 2 ^ 64) len mode out (nch mod 2 ^ 32) (ns mod 2 ^ 64)) in HS.
set (E := Eimg (Ereg regs X)) in HS.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (SHOK : sh_ok pa_segs (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor.
assert (EL : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; subst E; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg regs X) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 f0) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (nch mod 2 ^ 64)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 len) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E37 : ew E 37 = Z_to_bv 64 out) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E39 : ew E 39 = Z_to_bv 64 (ns mod 2 ^ 64)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx) by (rewrite (EL 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U10 : U E (SOff 10 0) = (if CDec.decode_ok len body nch ns then ns else -1) mod 2 ^ 64).
{ apply U_atom; [|apply Z.mod_pos_bound; lia]. rewrite (EL 10%nat 10%bv eq_refl), H10.
  unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_mod by lia. reflexivity. }
assert (U18 : U E (SOff 18 0) = f481) by (apply U_atom; [rewrite (EL 18%nat 18%bv eq_refl), H18; reflexivity | lia]).
assert (U26 : U E (SOff 26 0) = wf) by (apply U_atom; [rewrite (EL 26%nat 26%bv eq_refl), H26; reflexivity | lia]).
assert (U33 : U E (SOff 33 0) = f0) by (apply U_atom; [exact E33 | lia]).
assert (U34 : U E (SOff 34 0) = nch mod 2 ^ 64) by (apply U_atom; [exact E34 | apply Z.mod_pos_bound; lia]).
assert (U39 : U E (SOff 39 0) = ns mod 2 ^ 64) by (apply U_atom; [exact E39 | apply Z.mod_pos_bound; lia]).
(* the value s8 gets at +0x50c, read in any environment that agrees with E below the fresh atoms *)
assert (S8 : forall Ez, (forall m, (m < 512)%nat -> ew Ez m = ew E m) ->
  Z_to_bv 64 (U Ez c1_s8) = w64 (if CPlain.plain_ok len body nch ns then 1 else 0)).
{ intros Ez AGz.
  rewrite (c1_s8_U Ez wf f0 f481) by first [rewrite (c1_U_agree _ E _ AGz) by lia; assumption | assumption].
  rewrite Dp. unfold wf, f481. rewrite !c1_bit_eqb. reflexivity. }
change (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x4fc)) mem (YK11.seg_rom segs)) with
  (YK11.mkst regs (Z_to_bv 64 (pa_val (L := decode_listing) A_TEXT + 0x4fc)) mem (YK11.seg_rom pa_segs)).
(* +0x4fc .. +0x524: the two tests; stop at the `bne a0,a1` into the abort block *)
paj_run_tok RUN HS HJ SHOK Bspan; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG : forall m, (m < 512)%nat -> ew Ex m = ew E m) by (intros m Hm; repeat rewrite ew_ewset_other by lia; reflexivity);
  assert (E9a : bv_unsigned (ew Ex 9) = d_sp1 cx) by (first [exact E9 | rewrite AG by lia; exact E9]) end.
assert (HM1 : forall a, ms_mem ms a = mem a) by c1_nowin HF.
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ne_U in Hc.
  lazymatch type of Hc with negb (U ?Ex ?A =? U ?Ex ?X) = true =>
    change (U Ex X) with (U Ex c1_a1) in Hc;
    try rewrite (c1_U_agree Ex E 10 AG ltac:(lia)) in Hc; rewrite U10 in Hc;
    rewrite (c1_a1_U Ex wf f0 f481 (nch mod 2 ^ 64) (ns mod 2 ^ 64)) in Hc
      by first [rewrite (c1_U_agree _ E _ AG) by lia; assumption | assumption | apply Z.mod_pos_bound; lia] end.
  unfold wf, f481 in Hc. rewrite !c1_bit_eqb, <- Dd in Hc.
  destruct (CDec.decode_ok len body nch ns); [rewrite Z.eqb_refl in Hc; discriminate Hc|].
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) in Hc by reflexivity. rewrite Z.eqb_refl in Hc. discriminate Hc. }
(* +0x528 .. +0x530: s2 := the shadow base, s6 := len; stop at `bgez a0` *)
paj_run_tok RUN HS HJ SHOK Bspan; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG2 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
    by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG; exact Hm]);
  assert (E9b : bv_unsigned (ew Ex 9) = d_sp1 cx) by (first [exact E9 | rewrite AG2 by lia; exact E9]) end.
assert (HM2 : forall a, ms_mem ms0 a = mem a) by (intros a; rewrite <- (HM1 a); revert a; c1_nowin HF).
clear HF HFr HG AG E9a HM1.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a0 >= 0: the decode was accepted; straight to +0x58c *)
  clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x58c; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
  assert (HM3 : forall a, ms_mem ms1 a = mem a) by (intros a; rewrite <- (HM2 a); revert a; c1_nowin HF).
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG3 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
      by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG2; exact Hm]) end.
  c1_reg HS (18%bv : bv 5) R18. c1_reg HS (22%bv : bv 5) R22. c1_reg HS (24%bv : bv 5) R24. c1_reg HS (26%bv : bv 5) R26.
  eapply K; [ | | | | | exact HM3 | exact HJ].
  + intros r Hr. exact (regs_kept_of_st_ok_pi _ _ _ regs X c1_keepA HS
      ltac:(split; [intros n Hn; try rewrite AG3 by lia; apply HAE; exact Hn | reflexivity]) ltac:(vm_compute; reflexivity) r Hr).
  + rewrite R18. exact (c1_denot_soff _ E 32 SB AG3 ltac:(lia) E32).
  + rewrite R22. exact (c1_denot_soff _ E 35 len AG3 ltac:(lia) E35).
  + rewrite R24, denot_lit_U.
    lazymatch goal with |- Z_to_bv 64 (U ?Ez ?T) = _ => change (U Ez T) with (U Ez c1_s8) end. apply S8. exact AG3.
  + rewrite R26. exact (c1_denot_soff _ E 39 (ns mod 2 ^ 64) AG3 ltac:(lia) E39).
- (* a0 < 0: reac_decode refused the frame, so the buffer still holds the fill; the scan loop L1 *)
  clear Hc. rename Hc0 into Hc.
  rewrite !denot_lit_U, U_SLit in Hc. try rewrite (c1_U_agree _ E 10 AG2 ltac:(lia)) in Hc.
  rewrite U10 in Hc. change (zcanon 0) with 0 in Hc.
  rewrite c1_lit_mod in Hc.
  rewrite c1_br_ge in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hdec : CDec.decode_ok len body nch ns = false).
  { destruct (CDec.decode_ok len body nch ns) eqn:Ed; [|reflexivity]. exfalso.
    unfold CDec.decode_ok in Ed. rewrite !andb_true_iff in Ed. destruct Ed as ((((_ & _) & _) & Hns0) & _).
    apply Z.ltb_lt in Hns0. lia. }
  pose proof (HFILL Hdec) as HFl.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x544; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
  assert (HM3 : forall a, ms_mem ms1 a = mem a) by (intros a; rewrite <- (HM2 a); revert a; c1_nowin HF).
  pmkst HS.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG3 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
      by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG2; exact Hm]) end.
  c1_reg HS (11%bv : bv 5) R11. c1_reg HS (12%bv : bv 5) R12. c1_reg HS (13%bv : bv 5) R13.
  c1_reg HS (14%bv : bv 5) R14. c1_reg HS (18%bv : bv 5) R18. c1_reg HS (22%bv : bv 5) R22.
  c1_reg HS (24%bv : bv 5) R24. c1_reg HS (26%bv : bv 5) R26.
  rewrite (c1_denot_soff _ E 37 out AG3 ltac:(lia) E37) in R11, R13.
  rewrite (c1_denot_soff _ E 25 olen AG3 ltac:(lia) (eq_trans (EL 25%nat 25%bv eq_refl) H25)) in R14.
  rewrite (c1_denot_soff _ E 32 SB AG3 ltac:(lia) E32) in R18.
  rewrite (c1_denot_soff _ E 35 len AG3 ltac:(lia) E35) in R22.
  rewrite (c1_denot_soff _ E 39 (ns mod 2 ^ 64) AG3 ltac:(lia) E39) in R26.
  rewrite denot_lit_U in R24.
  lazymatch type of R24 with _ = Z_to_bv 64 (U ?Ez ?T) => change (U Ez T) with (U Ez c1_s8) in R24 end.
  rewrite (S8 _ AG3) in R24.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs X c1_keepA HS
      ltac:(split; [intros n Hn; try rewrite AG3 by lia; apply HAE; exact Hn | reflexivity]) ltac:(vm_compute; reflexivity)) as KA.
  cbn [ms_regs restrict YK11.mkst] in KA.
  clear HS SHOK HEI.
  destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR3 & _ & _ & _ & _).
  assert (Hin3 : In (out, olen) (ablocks B ly' S')) by exact Hin.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ out olen HAR3 Hin3) as (_ & Ho4 & Hoc & _ & _ & _ & _).
  assert (Hol : 1 <= olen <= 3 * 127 * 127).
  { unfold olen, dec_a_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:Ep; [|lia].
    apply andb_true_iff in Ep as [Ep1 Ep2]. apply Z.ltb_lt in Ep1, Ep2. nia. }
  assert (Hreq : req_size olen = olen) by (unfold req_size; destruct (Z.eqb_spec olen 0); lia).
  rewrite Hreq in Hoc.
  refine (c1_loop (Z.to_nat (olen - 1)) W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ out olen 0 Q HJ _ _ _ _ _ _ _ _ _ _ _ _ _).
  + rewrite Z.add_0_r. exact R11.
  + rewrite Z.add_0_r. exact R13.
  + exact R18.
  + rewrite R12. reflexivity.
  + rewrite R14. unfold w64. f_equal. lia.
  + lia.
  + lia.
  + lia.
  + exact Ho4.
  + lia.
  + intros j Hj. rewrite (c1_aview_eqm _ _ _ HM3). exact (HFl j Hj).
  + exact (range_addressable_of_block segs B LAWS _ _ _ _ _ out olen out olen HAR3 Hin3 ltac:(lia)
      ltac:(rewrite Hreq; lia)).
  + intros regs'' mem'' md'' Hk H12'' HM'' HJ''.
    apply K.
    * intros r Hr. rewrite (Hk r ltac:(unfold c1_keep; unfold c1_keepA in Hr; cbn [In] in Hr |- *; intuition)).
      exact (KA r Hr).
    * rewrite (Hk 18%bv ltac:(cbn; tauto)). exact R18.
    * rewrite (Hk 22%bv ltac:(cbn; tauto)). exact R22.
    * rewrite (Hk 24%bv ltac:(cbn; tauto)). exact R24.
    * rewrite (Hk 26%bv ltac:(cbn; tauto)). exact R26.
    * intros a. rewrite HM''. apply HM3.
    * exact HJ''.
Qed.
End F.

(* ------------------------------------------------------------------ *)
(* The facts the segment carries from cut point to call site           *)
(* ------------------------------------------------------------------ *)

(* What the rest of the walk reads of memory (slot 32 apart, which +0x58c rewrites): the mode and its fields, the
   frame's local shadow, the copy, and the spill slots. *)
Definition c1_mem (cx : dctx) (res out mode nch ns : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  dec_a_mode_ok cx W mem mode nch ns /\
  dec_a_fsh cx (aview segs (w_H W) mem) 0 4 /\
  garr8 segs (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
  dec_a_slot cx (aview segs (w_H W) mem) 40 SHADOW_OFF /\
  dec_a_slot cx (aview segs (w_H W) mem) 48 (nch mod 2 ^ 64) /\
  dec_a_slot cx (aview segs (w_H W) mem) 56 (dec_a_len (d_n cx)) /\
  dec_a_slot cx (aview segs (w_H W) mem) 64 mode /\
  dec_a_slot cx (aview segs (w_H W) mem) 72 out /\
  dec_a_slot cx (aview segs (w_H W) mem) 80 (nch mod 2 ^ 32) /\
  dec_a_slot cx (aview segs (w_H W) mem) 88 (ns mod 2 ^ 64) /\
  dec_a_slot cx (aview segs (w_H W) mem) 112 (d_F cx).

(* The addresses c1_mem reads. *)
Definition c1_R (cx : dctx) (res mode : Z) (a : Z) : Prop :=
  (decode_obj 4 <= a < decode_obj 4 + 8) \/ (decode_obj 5 <= a < decode_obj 5 + 8) \/
  (decode_obj 6 <= a < decode_obj 6 + 8) \/ (mode + 4 <= a < mode + 12) \/
  (d_SH cx <= a < d_SH cx + 8) \/ (res <= a < res + Z.of_nat (length (d_body cx))) \/
  (d_sp1 cx + 40 <= a < d_sp1 cx + 120).

Lemma c1_rdword_kept : forall (W : world segs) mem mem' a v,
  (forall k, 0 <= k < 8 -> aview segs (w_H W) mem' (a + k) = aview segs (w_H W) mem (a + k)) ->
  rdword (aview segs (w_H W) mem) a = Some v -> rdword (aview segs (w_H W) mem') a = Some v.
Proof. intros W mem mem' a v Hk H. rewrite (rdword_ext _ _ a Hk). exact H. Qed.

Lemma c1_val_mem_kept : forall (W : world segs) mem mem' a (n : nat) v,
  (forall k, 0 <= k < Z.of_nat n -> aview segs (w_H W) mem' (a + k) = aview segs (w_H W) mem (a + k)) ->
  val_mem segs (mrestrict (w_H W) mem) a n v -> val_mem segs (mrestrict (w_H W) mem') a n v.
Proof.
intros W mem mem' a n v Hk H j Hj. rewrite (mbyte_of_aview segs (w_H W) (w_H W) mem mem' (a + Z.of_nat j)).
- exact (H j Hj).
- apply Hk. lia.
Qed.

Lemma c1_garr8_kept : forall (W : world segs) mem mem' p (l : list Z),
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs (w_H W) mem' (p + k) = aview segs (w_H W) mem (p + k)) ->
  garr8 segs (mrestrict (w_H W) mem) p l -> garr8 segs (mrestrict (w_H W) mem') p l.
Proof.
intros W mem mem' p l Hk H j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
apply (c1_val_mem_kept W mem mem' (p + Z.of_nat j) 1 _); [|exact Hv].
intros k Hk1. cbn in Hk1. replace (p + Z.of_nat j + k) with (p + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.

Lemma c1_mem_kept : forall cx res out mode nch ns (W : world segs) mem mem',
  c1_mem cx res out mode nch ns W mem ->
  (forall a, c1_R cx res mode a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  c1_mem cx res out mode nch ns W mem'.
Proof.
intros cx res out mode nch ns W mem mem'
  ((Hmc & Hnch & Hns & Hv4 & Hv8) & (F1 & F4 & F5 & F6) & Hres & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S112) HK.
unfold c1_R in HK. unfold dec_a_slot in *.
assert (KW : forall a v, (forall kk, 0 <= kk < 8 -> c1_R cx res mode (a + kk)) ->
  rdword (aview segs (w_H W) mem) a = Some v -> rdword (aview segs (w_H W) mem') a = Some v).
{ intros a v Ha. apply c1_rdword_kept. intros kk Hkk. apply HK. exact (Ha kk Hkk). }
unfold c1_R in KW.
refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
- split; [|split; [exact Hnch|split; [exact Hns|split]]].
  + destruct Hmc as [Hc | [Hc | [Hc | Hc]]]; [left | right; left | right; right; left | right; right; right];
      try exact Hc; (refine (KW _ _ _ Hc); intros kk Hkk; lia).
  + refine (c1_val_mem_kept W mem mem' _ _ _ _ Hv4). intros kk Hkk. apply HK. cbn in Hkk. lia.
  + refine (c1_val_mem_kept W mem mem' _ _ _ _ Hv8). intros kk Hkk. apply HK. cbn in Hkk. lia.
- split; [|split; [|split]].
  + intros i Hi. rewrite HK by lia. exact (F1 i Hi).
  + rewrite HK by lia. exact F4.
  + rewrite HK by lia. exact F5.
  + intros i Hi. rewrite HK by lia. exact (F6 i Hi).
- refine (c1_garr8_kept W mem mem' res _ _ Hres). intros kk Hkk. rewrite length_map in Hkk. apply HK. lia.
- refine (KW _ _ _ S40); intros kk Hkk; lia.
- refine (KW _ _ _ S48); intros kk Hkk; lia.
- refine (KW _ _ _ S56); intros kk Hkk; lia.
- refine (KW _ _ _ S64); intros kk Hkk; lia.
- refine (KW _ _ _ S72); intros kk Hkk; lia.
- refine (KW _ _ _ S80); intros kk Hkk; lia.
- refine (KW _ _ _ S88); intros kk Hkk; lia.
- refine (KW _ _ _ S112); intros kk Hkk; lia.
Qed.
Lemma c1_saved_at_range : Forall (fun o : Z * Z => 8 <= fst o <= 104) dec_a_saved_at.
Proof. unfold dec_a_saved_at. repeat constructor; cbn [fst]; lia. Qed.

(* The cross-state forms: a word, a value and a byte array whose bytes two views agree on. *)
Lemma c1_rdword_x : forall (r r' : reader) a v,
  (forall k, 0 <= k < 8 -> r' (a + k) = r (a + k)) -> rdword r a = Some v -> rdword r' a = Some v.
Proof. intros r r' a v Hk H. rewrite (rdword_ext r r' a Hk). exact H. Qed.
Lemma c1_val_mem_x : forall H H2 mem mem2 a (n : nat) v,
  (forall k, 0 <= k < Z.of_nat n -> aview segs H2 mem2 (a + k) = aview segs H mem (a + k)) ->
  val_mem segs (mrestrict H mem) a n v -> val_mem segs (mrestrict H2 mem2) a n v.
Proof.
intros H H2 mem mem2 a n v Hk Hv j Hj. rewrite (mbyte_of_aview segs H H2 mem mem2 (a + Z.of_nat j)).
- exact (Hv j Hj).
- apply Hk. lia.
Qed.
Lemma c1_garr8_x : forall H H2 mem mem2 p (l : list Z),
  (forall k, 0 <= k < Z.of_nat (length l) -> aview segs H2 mem2 (p + k) = aview segs H mem (p + k)) ->
  garr8 segs (mrestrict H mem) p l -> garr8 segs (mrestrict H2 mem2) p l.
Proof.
intros H H2 mem mem2 p l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
apply (c1_val_mem_x H H2 mem mem2 (p + Z.of_nat j) 1 _); [|exact Hv].
intros k Hk1. cbn in Hk1. replace (p + Z.of_nat j + k) with (p + (Z.of_nat j + k)) by lia. apply Hk. lia.
Qed.

(* dec_a_core at a later state of the walk: the journal is given, the frame list and the payload block are kept,
   the five registers it names are kept, and the bytes it reads (the saved words, the fake frame, the payload) are
   kept. *)
Lemma c1_core_move : forall cx ly' S' (W W2 : world segs) ly2 S2 regs regs2 mem mem2 md md2 k k2,
  dec_a_core B cx ly' S' W regs mem md k ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  frames S2 = frames S' ->
  (In (d_p cx, d_n cx) (ablocks B ly' S') -> In (d_p cx, d_n cx) (ablocks B ly2 S2)) ->
  (forall r, In r [2; 3; 4; 8; 9]%bv -> YK11.getr regs2 r = YK11.getr regs r) ->
  (forall a, (d_sp0 cx - 104 <= a < d_sp0 cx) \/ (d_F cx <= a < d_F cx + 64) \/
     (d_p cx <= a < d_p cx + Z.of_nat (length (d_pl cx))) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W2) mem2 a) ->
  dec_a_core B cx ly2 S2 W2 regs2 mem2 md2 k2.
Proof.
intros cx ly' S' W W2 ly2 S2 regs regs2 mem mem2 md md2 k k2
  (HJ & Hfr & H8 & H9 & Hsp & Hsp01 & Hal & Hgp & Htp & Hsv & HF4 & HFal & HFp & HFl & Hpin & Hpay) HJ' HFr HB HR HK HFP.
unfold dec_a_core.
refine (conj HJ' (conj _ (conj _ (conj _ (conj _ (conj Hsp01 (conj Hal (conj _ (conj _ (conj _
  (conj HF4 (conj HFal (conj HFP (conj _ (conj _ _))))))))))))))).
- rewrite HFr. exact Hfr.
- rewrite (HR 8%bv ltac:(cbn; tauto)). exact H8.
- rewrite (HR 9%bv ltac:(cbn; tauto)). exact H9.
- unfold spZ. rewrite (HR 2%bv ltac:(cbn; tauto)). exact Hsp.
- rewrite (HR 3%bv ltac:(cbn; tauto)). exact Hgp.
- rewrite (HR 4%bv ltac:(cbn; tauto)). exact Htp.
- unfold dec_a_saved in *. rewrite Forall_forall in Hsv |- *. intros o Ho.
  pose proof (proj1 (Forall_forall _ _) c1_saved_at_range o Ho) as Ro. cbv beta in Ro.
  refine (c1_rdword_x _ _ _ _ _ (Hsv o Ho)). intros kk Hkk. apply HK. left. lia.
- refine (c1_rdword_x _ _ _ _ _ HFl). intros kk Hkk. apply HK. right; left. lia.
- intros Hn. exact (HB (Hpin Hn)).
- refine (c1_garr8_x _ _ _ _ _ _ _ Hpay). intros kk Hkk. rewrite length_map in Hkk. apply HK. right; right. lia.
Qed.

(* The callee-saved registers from +0x5c4 (s3 = the buffer, s7 = the frame) to the end of the segment. *)
Definition c1_regs5 (cx : dctx) (res out nch ns : Z) (regs : bvmap 5 word) : Prop :=
  YK11.getr regs 18 = w64 SHADOW_OFF /\ YK11.getr regs 19 = w64 out /\ YK11.getr regs 20 = w64 res /\
  YK11.getr regs 21 = w64 (d_F cx) /\ YK11.getr regs 22 = w64 (dec_a_len (d_n cx)) /\
  YK11.getr regs 23 = w64 (d_F cx) /\
  YK11.getr regs 24 = w64 (if CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then 1 else 0) /\
  YK11.getr regs 25 = w64 (dec_a_olen nch ns) /\ YK11.getr regs 26 = w64 (ns mod 2 ^ 64) /\
  YK11.getr regs 27 = w64 (d_SH cx).

(* Where the two buffers, the fake frame and the payload lie (pure facts, fixed once the buffers exist): below the
   allocator ceiling, in application memory, and apart from each other. *)
Definition c1_geo (cx : dctx) (res out olen : Z) : Prop :=
  4096 <= d_F cx /\ d_F cx + 64 <= alloc_ceiling /\
  4096 <= res /\ res + req_size (dec_a_len (d_n cx)) <= alloc_ceiling /\ in_app res (req_size (dec_a_len (d_n cx))) /\
  4096 <= out /\ out + req_size olen <= alloc_ceiling /\ in_app out (req_size olen) /\
  zdisjoint (res, req_size (dec_a_len (d_n cx))) (out, req_size olen) /\
  zdisjoint (out, req_size olen) (d_F cx, 64) /\ zdisjoint (res, req_size (dec_a_len (d_n cx))) (d_F cx, 64) /\
  (0 < d_n cx -> 4096 <= d_p cx /\ d_p cx + d_n cx <= alloc_ceiling /\
     zdisjoint (out, req_size olen) (d_p cx, req_size (d_n cx))).

(* The read-only facts the walk carries (state-independent): the entry's read-only view and the two premises that
   keep the DEC_RO_RD bytes off the owned statics and errno, so the journal's image clause carries the view to every
   state (c1_rom_rd). *)
Definition c1_ro (cx : dctx) : Prop := dec_a_rom cx /\ dec_ro_rd_unowned B /\ dec_rom_no_errno B.

(* The state at +0x5b8 / +0x5c4 / +0x5d8, check_round_trip #1 done or skipped. The two buffers are temporaries of
   this function (not blocks of the entry state), which is what lets its callees write the second one. *)
Definition c1_st (cx : dctx) (res out mode nch ns : Z) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (ly' : alayout) (S' : astate) (k : Z) : Prop :=
  dec_a_core B cx ly' S' W regs mem md k /\ k <= dec_ev_5fc /\
  Permutation (ablocks B ly' S')
    (ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++ [(out, dec_a_olen nch ns)]) /\
  ~ In (res, dec_a_len (d_n cx)) (ablocks B (d_ly cx) (d_S cx)) /\
  ~ In (out, dec_a_olen nch ns) (ablocks B (d_ly cx) (d_S cx)) /\
  c1_geo cx res out (dec_a_olen nch ns) /\
  mo_le MT (d_S cx) S' (dec_spent_5fc MT (d_n cx)) /\ mo_ok MT S' (dec_rest_5fc MT) /\
  c1_regs5 cx res out nch ns regs /\
  c1_mem cx res out mode nch ns W mem /\ dec_a_slot cx (aview segs (w_H W) mem) 32 (ns mod 2 ^ 32) /\ c1_ro cx.

(* The bytes c1_st reads besides the mode tables: the saved words, the fake frame and its shadow, the payload, the
   copy, and the spill slots 32(s1) .. 112(s1). *)
Definition c1_K (cx : dctx) (res : Z) (a : Z) : Prop :=
  (d_sp0 cx - 104 <= a < d_sp0 cx) \/ (d_F cx <= a < d_F cx + 64) \/
  (d_p cx <= a < d_p cx + Z.of_nat (length (d_pl cx))) \/ (d_SH cx <= a < d_SH cx + 8) \/
  (res <= a < res + Z.of_nat (length (d_body cx))) \/ (d_sp1 cx + 32 <= a < d_sp1 cx + 120).

(* The state at +0x58c, out of the decode check (and the scan loop when the decode failed). *)
Definition c1_st58 (cx : dctx) (res out mode nch ns : Z) (W : world segs) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model) (ly' : alayout) (S' : astate) : Prop :=
  dec_a_core B cx ly' S' W regs mem md dec_ev_4fc /\
  ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++ [(out, dec_a_olen nch ns)] /\
  4096 <= res /\ 4096 <= out /\
  mo_le MT (d_S cx) S' (dec_spent_4fc MT (d_n cx)) /\ mo_ok MT S' (dec_rest_4fc MT) /\
  dec_a_fr cx regs /\
  YK11.getr regs 10 = w64 (if CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then ns else -1) /\
  YK11.getr regs 18 = w64 SHADOW_OFF /\ YK11.getr regs 20 = w64 res /\
  YK11.getr regs 22 = w64 (dec_a_len (d_n cx)) /\ YK11.getr regs 23 = w64 (ns mod 2 ^ 32) /\
  YK11.getr regs 24 = w64 (if CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then 1 else 0) /\
  YK11.getr regs 25 = w64 (dec_a_olen nch ns) /\ YK11.getr regs 26 = w64 (ns mod 2 ^ 64) /\
  c1_mem cx res out mode nch ns W mem /\ (exists v32, dec_a_slot cx (aview segs (w_H W) mem) 32 v32) /\
  (CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
     garr8 segs (mrestrict (w_H W) mem) out (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns))).

(* The two tails, stated over any float state: +0x5d8 (__asan_memset, reac_decode_plain_le) and +0x5b8 / +0x5c4
   (check_braid #1, then the same). *)
Definition c1_T2_stmt : Prop :=
  forall (fx : YK11.FPState) cx res out mode nch ns (W : world segs) regs mem md ly' S' k,
    dec_base cx -> dec_a_rom cx -> frm_zero (@fp_csr fx) ->
    c1_st cx res out mode nch ns W regs mem md ly' S' k ->
    SRr segs W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + 0x5d8)) mem (YK11.seg_rom segs)) md) (llvm_a_st_5fc B MT cx).
Definition c1_T3_stmt : Prop :=
  forall (fx : YK11.FPState) pc cx res out mode nch ns (W : world segs) regs mem md ly' S' k,
    (pc = 0x5b8 \/ pc = 0x5c4) -> dec_base cx -> dec_a_rom cx -> frm_zero (@fp_csr fx) ->
    c1_st cx res out mode nch ns W regs mem md ly' S' k ->
    CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
    garr8 segs (mrestrict (w_H W) mem) out (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns)) ->
    SRr segs W (mkCfg (@YK11.mkst fx regs (w64 (DEC_A_LLVMF + pc)) mem (YK11.seg_rom segs)) md) (llvm_a_st_5fc B MT cx).

(* GrantFrame.v rdword_of_val_mem (as copied in LLVMFuzzerTestOneInput_seg_entry.v): an 8-byte value of the view
   is a word of the reader. *)
Lemma c1_rdword_of_val_mem : forall H mem a v,
  val_mem segs (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview segs H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (B8 : forall k, (k < 8)%nat -> aview segs H mem (a + Z.of_nat k) = Some (le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (B8 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (B8 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (B8 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (B8 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (B8 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (B8 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (B8 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (B8 7%nat) by lia.
f_equal. apply le_bytes8. exact Hr.
Qed.

(* The constant cells of B, read at a state through AR's am_const. *)
Lemma c1_cell8 : forall ly S (W : world segs) mem md a v,
  @AR rc segs B ly S W mem md -> In (z8 (ANum a) v) (as_const B ly) -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) a = Some v.
Proof.
intros ly S W mem md a v HAR Hin Hv. destruct HAR as [HARm _].
pose proof (am_const _ _ _ _ HARm) as HC. rewrite Forall_forall in HC.
exact (rdword_cell B ly _ a v Hv (HC _ Hin)).
Qed.
Lemma c1_cell4 : forall ly S (W : world segs) mem md a v,
  @AR rc segs B ly S W mem md -> In (z4 (ANum a) v) (as_const B ly) ->
  forall k, (k < 4)%nat -> aview segs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v 4 k).
Proof.
intros ly S W mem md a v HAR Hin. destruct HAR as [HARm _].
pose proof (am_const _ _ _ _ HARm) as HC. rewrite Forall_forall in HC.
exact (HC _ Hin).
Qed.

Lemma c1_J_img : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W : world segs) mem md k,
  @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem md k ->
  forall a, in_img segs a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
    @fp_spares dec_A_sink_head FP a -> aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a.
Proof. intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem md k H. unfold ajournal in H. decompose [and] H. assumption. Qed.

(* check_round_trip's read-only view at its call: the DEC_RO_RD bytes are read-only image bytes outside every owned
   static and errno (dec_ro_rd_scoped), so the journal's image clause carries the entry's rom_view to them. *)
Lemma c1_rom_rd : forall cx own ly' S' (W : world segs) mem md k,
  dec_a_rom cx -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    own ly' S' W mem md k ->
  dec_rom_view_rd W mem.
Proof.
intros cx own ly' S' W mem md k HR HO HE HJ a Ha.
destruct (dec_ro_rd_scoped B HO HE a Ha) as [Hno Her].
destruct (dec_ro_rd_rom_clean a Ha) as [Hrom _].
rewrite (c1_J_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ a).
- exact (HR a Hrom).
- destruct Hrom as (sg & Hsg & _ & Hrg). exists sg. split; [exact Hsg | exact Hrg].
- exact Hno.
- exact Her.
- apply fp_spares_closed. intros (r & Hr & _). destruct Hr.
Qed.

Lemma c1_rom_rd_ro : forall cx own ly' S' (W : world segs) mem md k, c1_ro cx ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    own ly' S' W mem md k ->
  dec_rom_view_rd W mem.
Proof. intros cx own ly' S' W mem md k (HR & HO & HE) HJ. exact (c1_rom_rd cx own ly' S' W mem md k HR HO HE HJ). Qed.

(* The table words a REAC_MODE table's +4 / +8 fields hold lie in DEC_RO_RD (the +4 .. +11 bytes of each table). *)
Lemma c1_tab_ro : forall t k, (t = 0x20d40 \/ t = 0x20d80 \/ t = 0x20d60) -> 0 <= k < 8 -> dec_in_ro_rd (t + 4 + k).
Proof.
intros t k Ht Hk. unfold dec_in_ro_rd, DEC_RO_RD.
destruct Ht as [-> | [-> | ->]];
  repeat (first [apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | apply Exists_cons_tl]).
Qed.

(* dec_a_mode_ok at another state of the same walk: the pointer cells are constant cells of dec_crt_cells, read again
   at the new state; the table words are read-only image bytes (dec_rom_view_rd at both states); the frame's local
   is kept by the caller. *)
Lemma c1_mode_re : forall cx (W W' : world segs) mem mem' ly S md ly' S' md' mode nch ns,
  dec_crt_cells B ->
  @AR rc segs B ly S W mem md -> @AR rc segs B ly' S' W' mem' md' ->
  dec_rom_view_rd W mem -> dec_rom_view_rd W' mem' ->
  dec_a_mode_ok cx W mem mode nch ns ->
  (forall k, 0 <= k < 8 -> aview segs (w_H W') mem' (d_F cx + 36 + k) = aview segs (w_H W) mem (d_F cx + 36 + k)) ->
  dec_a_mode_ok cx W' mem' mode nch ns.
Proof.
intros cx W W' mem mem' ly S md ly' S' md' mode nch ns HCELLS HAR HAR' HV HV' (Hmc & Hnch & Hns & Hv4 & Hv8) HF.
assert (VK : forall a (n : nat) v, (forall k, 0 <= k < Z.of_nat n ->
   aview segs (w_H W') mem' (a + k) = aview segs (w_H W) mem (a + k)) ->
   val_mem segs (mrestrict (w_H W) mem) a n v -> val_mem segs (mrestrict (w_H W') mem') a n v).
{ intros a n v Hk Hv j Hj. rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (a + Z.of_nat j)).
  - exact (Hv j Hj).
  - apply Hk. lia. }
(* a table: the pointer word is a constant cell, the two 4-byte fields are read-only image bytes *)
assert (TB : forall c t, In (z8 (ANum c) t) (as_const B ly) -> In (z8 (ANum c) t) (as_const B ly') ->
   (t = 0x20d40 \/ t = 0x20d80 \/ t = 0x20d60) -> rdword (aview segs (w_H W) mem) c = Some mode ->
   rdword (aview segs (w_H W') mem') c = Some mode /\
   val_mem segs (mrestrict (w_H W') mem') (mode + 4) 4 (nch mod 2 ^ 32) /\
   val_mem segs (mrestrict (w_H W') mem') (mode + 8) 4 (ns mod 2 ^ 32)).
{ intros c t P0 P0' Ht Hc.
  assert (Ht64 : 0 <= t < 2 ^ 64) by (destruct Ht as [-> | [-> | ->]]; lia).
  rewrite (c1_cell8 _ _ _ _ _ _ _ HAR P0 Ht64) in Hc. injection Hc as <-.
  split; [exact (c1_cell8 _ _ _ _ _ _ _ HAR' P0' Ht64)|].
  assert (RO : forall k, 0 <= k < 8 -> aview segs (w_H W') mem' (t + 4 + k) = aview segs (w_H W) mem (t + 4 + k))
    by (intros k Hk; rewrite (HV' _ (c1_tab_ro t k Ht Hk)), (HV _ (c1_tab_ro t k Ht Hk)); reflexivity).
  split; (apply (VK _ 4%nat); [|assumption]); intros k Hk; cbn in Hk;
    [ exact (RO k ltac:(lia))
    | replace (t + 8 + k) with (t + 4 + (4 + k)) by lia; exact (RO (4 + k) ltac:(lia)) ]. }
destruct Hmc as [Hc | [Hc | [Hc | Hc]]].
- destruct (TB (decode_obj 4) 0x20d40 ltac:(dec_leafb_row HCELLS ly) ltac:(dec_leafb_row HCELLS ly') ltac:(lia) Hc)
    as (R0 & R4 & R8).
  split; [left; exact R0 | split; [exact Hnch | split; [exact Hns | split; [exact R4 | exact R8]]]].
- destruct (TB (decode_obj 5) 0x20d80 ltac:(dec_leafb_row HCELLS ly) ltac:(dec_leafb_row HCELLS ly') ltac:(lia) Hc)
    as (R0 & R4 & R8).
  split; [right; left; exact R0 | split; [exact Hnch | split; [exact Hns | split; [exact R4 | exact R8]]]].
- destruct (TB (decode_obj 6) 0x20d60 ltac:(dec_leafb_row HCELLS ly) ltac:(dec_leafb_row HCELLS ly') ltac:(lia) Hc)
    as (R0 & R4 & R8).
  split; [right; right; left; exact R0 | split; [exact Hnch | split; [exact Hns | split; [exact R4 | exact R8]]]].
- subst mode. split; [right; right; right; reflexivity|]. split; [exact Hnch|]. split; [exact Hns|].
  split; (apply (VK _ 4%nat); [|assumption]); intros k Hk;
    [replace (d_F cx + 32 + 4 + k) with (d_F cx + 36 + k) by lia | replace (d_F cx + 32 + 8 + k) with (d_F cx + 36 + (4 + k)) by lia];
    apply HF; cbn in Hk; lia.
Qed.
(* The addresses of c1_mem other than the mode's. *)
Definition c1_Rx (cx : dctx) (res : Z) (a : Z) : Prop :=
  (d_SH cx <= a < d_SH cx + 8) \/ (res <= a < res + Z.of_nat (length (d_body cx))) \/
  (d_sp1 cx + 40 <= a < d_sp1 cx + 120).

Lemma c1_mem_kept2 : forall cx res out mode nch ns (W W' : world segs) mem mem',
  c1_mem cx res out mode nch ns W mem -> dec_a_mode_ok cx W' mem' mode nch ns ->
  (forall a, c1_Rx cx res a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a) ->
  c1_mem cx res out mode nch ns W' mem'.
Proof.
intros cx res out mode nch ns W W' mem mem'
  (_ & (F1 & F4 & F5 & F6) & Hres & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S112) Hmode' HK.
unfold c1_Rx in HK. unfold dec_a_slot in *.
assert (KW : forall a v, (forall kk, 0 <= kk < 8 -> d_sp1 cx + 40 <= a + kk < d_sp1 cx + 120) ->
  rdword (aview segs (w_H W) mem) a = Some v -> rdword (aview segs (w_H W') mem') a = Some v).
{ intros a v Ha Hr. rewrite (rdword_ext (aview segs (w_H W) mem) (aview segs (w_H W') mem') a); [exact Hr|].
  intros kk Hkk. apply HK. right; right. exact (Ha kk Hkk). }
refine (conj Hmode' (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))))).
- split; [|split; [|split]].
  + intros i Hi. rewrite HK by lia. exact (F1 i Hi).
  + rewrite HK by lia. exact F4.
  + rewrite HK by lia. exact F5.
  + intros i Hi. rewrite HK by lia. exact (F6 i Hi).
- intros j Hj. destruct (Hres j Hj) as [Hv Hr]. split; [|exact Hr].
  intros k Hk. rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem').
  + exact (Hv k Hk).
  + apply HK. right; left. rewrite length_map in Hj. cbn in Hk. lia.
- refine (KW _ _ _ S40); intros kk Hkk; lia.
- refine (KW _ _ _ S48); intros kk Hkk; lia.
- refine (KW _ _ _ S56); intros kk Hkk; lia.
- refine (KW _ _ _ S64); intros kk Hkk; lia.
- refine (KW _ _ _ S72); intros kk Hkk; lia.
- refine (KW _ _ _ S80); intros kk Hkk; lia.
- refine (KW _ _ _ S88); intros kk Hkk; lia.
- refine (KW _ _ _ S112); intros kk Hkk; lia.
Qed.

(* c1_st at a later state of the walk, the allocator state moved by a callee: the journal and the meter at the new
   state are given; the callee kept the callee-saved registers, the block list up to order, the frame list, the bytes
   c1_K names and the fake frame's presence. The mode is read again at the new state (c1_mode_re, the table words
   through the read-only view the journal carries to both states). *)
Lemma c1_st_move : forall cx res out mode nch ns (W W2 : world segs) regs regs2 mem mem2 md md2 ly' S' ly2 S2 k k2,
  dec_crt_cells B ->
  c1_st cx res out mode nch ns W regs mem md ly' S' k ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly2 S2 W2 mem2 md2 k2 ->
  k2 <= dec_ev_5fc -> frames S2 = frames S' -> Permutation (ablocks B ly2 S2) (ablocks B ly' S') ->
  mo_le MT (d_S cx) S2 (dec_spent_5fc MT (d_n cx)) -> mo_ok MT S2 (dec_rest_5fc MT) ->
  aregs_preserved regs regs2 ->
  (forall a, c1_K cx res a -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W2) mem2 a) ->
  c1_st cx res out mode nch ns W2 regs2 mem2 md2 ly2 S2 k2.
Proof.
intros cx res out mode nch ns W W2 regs regs2 mem mem2 md md2 ly' S' ly2 S2 k k2 HCELLS
  (HC & Hk & HPm & Hnr & Hno & Hgeo & Hle & Hok & HR5 & HM & S32 & HRO) HJ2 Hk2 HFr HPm2 Hle2 Hok2 HP HK HFP.
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c1_core_J _ _ _ _ _ _ _ _ HC)) as (HAR & _ & _ & _ & _).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & _ & _ & _ & _).
pose proof (c1_rom_rd_ro _ _ _ _ _ _ _ _ HRO (c1_core_J _ _ _ _ _ _ _ _ HC)) as HV.
pose proof (c1_rom_rd_ro _ _ _ _ _ _ _ _ HRO HJ2) as HV2.
assert (HPr : forall r : Z, acallee_saved r -> YK11.getr regs2 (Z_to_bv 5 r) = YK11.getr regs (Z_to_bv 5 r))
  by exact HP.
unfold c1_st.
refine (conj _ (conj Hk2 (conj (Permutation_trans HPm2 HPm) (conj Hnr (conj Hno (conj Hgeo
  (conj Hle2 (conj Hok2 (conj _ (conj _ (conj _ HRO))))))))))).
- apply (c1_core_move cx ly' S' W W2 ly2 S2 regs regs2 mem mem2 md md2 k k2 HC HJ2 HFr).
  + intros Hin. exact (Permutation_in _ (Permutation_sym HPm2) Hin).
  + intros r Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]];
      first [ exact (HPr 2 ltac:(unfold acallee_saved; lia)) | exact (HPr 3 ltac:(unfold acallee_saved; lia))
            | exact (HPr 4 ltac:(unfold acallee_saved; lia)) | exact (HPr 8 ltac:(unfold acallee_saved; lia))
            | exact (HPr 9 ltac:(unfold acallee_saved; lia)) ].
  + intros a Ha. apply HK. unfold c1_K. destruct Ha as [Ha | [Ha | Ha]]; [left | right; left | right; right; left]; exact Ha.
  + exact HFP.
- destruct HR5 as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27). unfold c1_regs5.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))))).
  + rewrite <- R18. exact (HPr 18 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R19. exact (HPr 19 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R20. exact (HPr 20 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R21. exact (HPr 21 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R22. exact (HPr 22 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R23. exact (HPr 23 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R24. exact (HPr 24 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R25. exact (HPr 25 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R26. exact (HPr 26 ltac:(unfold acallee_saved; lia)).
  + rewrite <- R27. exact (HPr 27 ltac:(unfold acallee_saved; lia)).
- apply (c1_mem_kept2 cx res out mode nch ns W W2 mem mem2 HM).
  + destruct HM as (HMO & _).
    apply (c1_mode_re cx W W2 mem mem2 ly' S' md ly2 S2 md2 mode nch ns HCELLS HAR HAR2 HV HV2 HMO).
    intros kk Hkk. apply HK. right; left. lia.
  + intros a Ha. apply HK. unfold c1_Rx in Ha. unfold c1_K.
    destruct Ha as [Ha | [Ha | Ha]]; [right; right; right; left | right; right; right; right; left |
      right; right; right; right; right; lia]; exact Ha.
- unfold dec_a_slot in *. refine (c1_rdword_x _ _ _ _ _ S32). intros kk Hkk. apply HK.
  right; right; right; right; right. lia.
Qed.

(* The fields of the slot pre and of afn_pre this segment reads, each found by its type. *)
Lemma c1_base_afn : forall cx, dec_base cx ->
  @afn_pre rc segs B DEC_LLVMF_STK (d_ly cx) (d_S cx) (d_W cx) (d_regs cx) (d_mem cx) (d_md cx) [].
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma c1_base_ra : forall cx, dec_base cx -> raZ (d_regs cx) = RA_LLVMF.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma c1_base_len : forall cx, dec_base cx -> d_n cx = Z.of_nat (length (d_pl cx)).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma c1_base_nev : forall cx, dec_base cx -> st_nev (d_S cx) + DEC_EV_LIB <= EV_MAX.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma c1_base_bb : forall cx, dec_base cx -> blocks_bytes (d_S cx) + DEC_LIVE_LIB <= LIVE_MAX.
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma c1_base_pn : forall cx, dec_base cx ->
  (d_n cx = 0 /\ d_p cx = A_EMPTY) \/ (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma c1_afn_facts : forall STK ly S (W : world segs) regs mem md ch,
  @afn_pre rc segs B STK ly S W regs mem md ch ->
  4096 <= raZ regs /\ astk_ok STK ly (spZ regs) /\ achain ly (aview segs (w_H W) mem) (spZ regs) (s0Z regs) ch.
Proof.
intros STK ly S W regs mem md ch H. unfold afn_pre in H. decompose [and] H.
refine (conj _ (conj _ _)); assumption.
Qed.
Lemma c1_J_ly : forall STK sp0 FP ly S W0 mem0 md0 own ly' S' (W : world segs) mem md k,
  @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem md k ->
  ly_F ly' = ly_F ly /\ ly_top ly' = ly_top ly.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own ly' S' W mem md k H. unfold ajournal in H. decompose [and] H.
match goal with Hl : layout_le _ _ _ |- _ => unfold layout_le in Hl; decompose [and] Hl end.
split; assumption.
Qed.

(* The frame-pointer chain at a call to check_round_trip from this function (s0 = the entry sp, sp = s1, the
   return address one of DEC_LLVMF_RA_CRT): this function's frame record (RA_LLVMF and the caller's s0, the first
   two saved words) on top of the caller's chain, which the slot pre makes empty (afn_pre .. []). So the context is
   [ra] or [ra; RA_LLVMF], both in CTX_check_round_trip. The form of seg_early's e_trace, at achain. *)
Lemma c1_crt_chain : forall cx (W : world segs) own lyc Sc memT mdT k regsT,
  dec_base cx ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    own lyc Sc W memT mdT k ->
  dec_a_saved cx (aview segs (w_H W) memT) ->
  YK11.getr regsT 8 = w64 (d_sp0 cx) -> spZ regsT = d_sp1 cx -> In (raZ regsT) DEC_LLVMF_RA_CRT ->
  exists ch, @achain rc lyc (aview segs (w_H W) memT) (spZ regsT) (s0Z regsT) ch /\
    In (raZ regsT :: spine ch) (CTX_check_round_trip RA_LLVMF).
Proof.
intros cx W own lyc Sc memT mdT k regsT HB HJ Hsv R8 Hsp Hra.
pose proof (c1_base_afn cx HB) as HAFN. pose proof (c1_base_ra cx HB) as HRA.
destruct (c1_afn_facts _ _ _ _ _ _ _ _ HAFN) as (Hra4 & Hstk & Hch).
destruct (c1_stk_facts _ _ _ Hstk) as (Ha16 & Hceil & Hslo & Hshi & H47 & _ & Htop1 & Htop2).
destruct (c1_J_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & Etop).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
assert (Hsp1 : d_sp1 cx + 224 <= d_sp0 cx) by (unfold d_sp1; Z.div_mod_to_equations; lia).
assert (Hs0z : s0Z regsT = d_sp0 cx) by (unfold s0Z; rewrite R8; apply unsigned_lit_small; unfold d_sp0 in *; lia).
unfold dec_a_saved, dec_a_saved_at in Hsv.
apply Forall_cons_iff in Hsv as [S1 Hsv]. apply Forall_cons_iff in Hsv as [S8 _]. cbn [fst snd] in S1, S8.
assert (CTX : forall sp, In sp [[]; [RA_LLVMF]] -> In (raZ regsT :: sp) (CTX_check_round_trip RA_LLVMF)).
{ intros sp Hsp'. unfold CTX_check_round_trip. apply in_flat_map. exists (raZ regsT). split; [exact Hra|].
  cbn [In] in Hsp' |- *. destruct Hsp' as [<- | [<- | []]]; tauto. }
rewrite Hs0z, Hsp. unfold d_sp0 in *.
destruct (Z_lt_ge_dec (spZ (d_regs cx)) (ly_top (d_ly cx) - 16)) as [Hlt | Hge].
- exists [(spZ (d_regs cx), RA_LLVMF, s0Z (d_regs cx))]. split; [|exact (CTX [RA_LLVMF] ltac:(cbn; tauto))].
  right. rewrite Etop. split; [lia|]. split; [lia|]. split; [lia|]. split.
  + cbn [fpchain]. split; [reflexivity|]. split; [lia|].
    split; [rewrite S1; f_equal; exact HRA|]. split; [exact S8|]. split; [rewrite <- HRA; exact Hra4|].
    destruct (bad_next (spZ (d_regs cx)) (ly_top (d_ly cx)) (s0Z (d_regs cx))) eqn:Ebn; [reflexivity|].
    unfold bad_next in Ebn. apply orb_false_iff in Ebn as [Ebn Em]. apply orb_false_iff in Ebn as [Eb1 Eb2].
    apply Z.leb_gt in Eb1, Eb2. apply negb_false_iff, Z.eqb_eq in Em.
    destruct Hch as [(Hbad & _) | (Hv1 & Hv2 & Hv3 & Hfp & _)]; [exfalso; lia|].
    cbn [fpchain] in Hfp |- *. destruct Hfp as (r & Hr & Hr4). exists r. split; [|exact Hr4].
    rewrite <- Hr. apply rdword_ext. intros j Hj.
    apply (@aview_above_of_journal rc dec_A_sink_head decode_listing PI_decode B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
    lia.
  + apply Forall_cons; [cbn [fst]; lia | apply Forall_nil].
- exists []. split; [|exact (CTX [] ltac:(cbn; tauto))].
  left. split; [right; left; rewrite Etop; lia | reflexivity].
Qed.

(* The two buffers at +0x58c, from AR's block and frame laws: c1_geo, and neither buffer is a block of the entry
   state (dec_leafb_new_block). *)
Lemma c1_geo_58 : forall cx res out nch ns ly' S' (W : world segs) regs mem md k,
  AR_laws segs B -> dec_base cx ->
  dec_a_core B cx ly' S' W regs mem md k ->
  ablocks B ly' S' = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++ [(out, dec_a_olen nch ns)] ->
  c1_geo cx res out (dec_a_olen nch ns) /\
  ~ In (res, dec_a_len (d_n cx)) (ablocks B (d_ly cx) (d_S cx)) /\
  ~ In (out, dec_a_olen nch ns) (ablocks B (d_ly cx) (d_S cx)).
Proof.
intros cx res out nch ns ly' S' W regs mem md k LAWS HB HC Hbl.
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & _ & _ & _ & _).
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & _ & _ & _ & _ & _ & HF4 & _ & Hfrs).
destruct (c1_J_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (EF & _).
set (base := ablocks B (d_ly cx) (d_S cx)) in *.
set (len := dec_a_len (d_n cx)) in *. set (olen := dec_a_olen nch ns) in *.
assert (Ires : In (res, len) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
assert (Iout : In (out, olen) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Ires) as (_ & Hr4 & Hrc & Hrapp & _ & Hpw & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Iout) as (_ & Ho4 & Hoc & Hoapp & _).
assert (Ifr : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (EFa : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite EF; reflexivity).
destruct (frames_bounds segs B LAWS _ _ _ _ _ _ _ HAR Ifr) as (Hf4 & Hfc & _).
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR Ires Ifr) as Drf.
pose proof (sep_block_frame segs B LAWS _ _ _ _ _ _ _ _ _ HAR Iout Ifr) as Dof.
rewrite EFa in Hf4, Hfc, Drf, Dof.
replace (fs_frame_bytes DEC_FCLASS) with 64 in Hfc, Drf, Dof by reflexivity.
rewrite Hbl, !map_app in Hpw. cbn [map fst snd] in Hpw.
assert (Dro : zdisjoint (res, req_size len) (out, req_size olen)).
{ apply (pairwise_zdisjoint_split _ _ _ Hpw). exists (map (fun b => (fst b, req_size (snd b))) base), [], [].
  left. reflexivity. }
assert (Hnr : ~ In (res, len) base) by exact (dec_leafb_new_block B LAWS _ _ _ _ _ _ _ res len HAR Hbl (or_introl eq_refl)).
assert (Hno : ~ In (out, olen) base)
  by exact (dec_leafb_new_block B LAWS _ _ _ _ _ _ _ out olen HAR Hbl (or_intror (or_introl eq_refl))).
refine (conj _ (conj Hnr Hno)).
unfold c1_geo. fold len olen.
refine (conj Hf4 (conj Hfc (conj Hr4 (conj Hrc (conj Hrapp (conj Ho4 (conj Hoc (conj Hoapp (conj Dro (conj _ (conj Drf _))))))))))).
- unfold zdisjoint in *. cbn [fst snd] in *. lia.
- intros Hn. destruct (c1_base_pn cx HB) as [(Hn0 & _) | (_ & Hpin)]; [lia|]. fold base in Hpin.
  assert (Ipay : In (d_p cx, d_n cx) (ablocks B ly' S')) by (rewrite Hbl; apply in_or_app; left; exact Hpin).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Ipay) as (_ & Hp4 & Hpc & _).
  assert (Hrq : req_size (d_n cx) = d_n cx) by (unfold req_size; destruct (Z.eqb_spec (d_n cx) 0); lia).
  split; [exact Hp4|]. split; [lia|].
  destruct (in_split _ _ Hpin) as (l1 & l2 & Hsp).
  assert (D : zdisjoint (d_p cx, req_size (d_n cx)) (out, req_size olen)).
  { apply (pairwise_zdisjoint_split _ _ _ Hpw).
    exists (map (fun b => (fst b, req_size (snd b))) l1), (map (fun b => (fst b, req_size (snd b))) l2 ++
      [(res, req_size len)]), [].
    left. rewrite Hsp, map_app. cbn [map fst snd]. rewrite <- !app_assoc. reflexivity. }
  unfold zdisjoint in *. cbn [fst snd] in *. lia.
Qed.

Lemma c1_body_len : forall cx, dec_base cx -> Z.of_nat (length (d_body cx)) = dec_a_len (d_n cx).
Proof.
intros cx HB. pose proof (c1_base_len cx HB) as Hl. unfold d_body, dec_a_len, dec_a_u.
rewrite length_skipn. rewrite Hl. lia.
Qed.

Lemma c1_core_fpres : forall cx ly' S' (W : world segs) regs mem md k, dec_a_core B cx ly' S' W regs mem md k ->
  forall a, d_F cx <= a < d_F cx + 64 -> apresent (w_H W) mem a.
Proof. intros cx ly' S' W regs mem md k H. unfold dec_a_core in H. decompose [and] H. assumption. Qed.

Lemma c1_crt_max_nonneg : ameter_laws MT -> 0 <= dec_crt_cost_max MT.
Proof.
intros ML. unfold dec_crt_cost_max.
pose proof (mo_malloc_nonneg MT ML 1920 ltac:(lia)). pose proof (mo_malloc_nonneg MT ML 1016 ltac:(lia)).
pose proof (mo_malloc_nonneg MT ML 1440 ltac:(lia)). pose proof (mo_free_nonneg MT ML). lia.
Qed.
(* The meter on the paths that skip check_round_trip #1: what it would have cost stays unspent. *)
Lemma c1_meter_skip : forall s0 s n, ameter_laws MT ->
  mo_le MT s0 s (dec_spent_4fc MT n) -> mo_ok MT s (dec_rest_4fc MT) ->
  mo_le MT s0 s (dec_spent_5fc MT n) /\ mo_ok MT s (dec_rest_5fc MT).
Proof.
intros s0 s n ML H1 H2. pose proof (c1_crt_max_nonneg ML). split.
- apply (mo_le_mono MT ML _ _ _ _ H1). unfold dec_spent_5fc. lia.
- apply (mo_ok_le MT ML _ _ _ H2). unfold dec_rest_4fc. lia.
Qed.

(* c1_st at +0x5b8 / +0x5c4 / +0x5d8 from c1_st58 at +0x58c, when check_round_trip #1 is not called: the run
   +0x58c .. stored only slot 32(s1) (s7 = ns), moved the frame to s7 and reloaded s3 with the buffer. *)
Lemma c1_st_of58 : forall cx res out mode nch ns (W : world segs) regs mem md ly' S' regs' mem' md',
  AR_laws segs B -> ameter_laws MT -> dec_base cx -> dec_crt_cells B -> c1_ro cx ->
  c1_st58 cx res out mode nch ns W regs mem md ly' S' ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W mem' md' dec_ev_4fc ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  YK11.getr regs' 19 = w64 out -> YK11.getr regs' 23 = w64 (d_F cx) ->
  (forall a, 0 <= a < 2 ^ 64 /\ ~ (d_sp1 cx + 32 <= a < d_sp1 cx + 40) ->
     aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  rdword (aview segs (w_H W) mem') (d_sp1 cx + 32) = Some (ns mod 2 ^ 32) ->
  c1_st cx res out mode nch ns W regs' mem' md' ly' S' dec_ev_4fc.
Proof.
intros cx res out mode nch ns W regs mem md ly' S' regs' mem' md' LAWS ML HB HCELLS HRO
  (HC & Hbl & _ & _ & Hle & Hok & Hfr & _ & H18 & H20 & H22 & _ & H24 & H25 & H26 & HM & _ & _)
  HJ' HR R19 R23 HK HG S32.
destruct (c1_geo_58 cx res out nch ns ly' S' W regs mem md dec_ev_4fc LAWS HB HC Hbl) as (Hgeo & Hnr & Hno).
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & Hs01 & Hs01' & _ & _ & _ & _ & _ & _).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (c1_core_J _ _ _ _ _ _ _ _ HC)) as (HAR & Hstk & _ & _ & _).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ') as (HAR' & _ & _ & _ & _).
pose proof (c1_rom_rd_ro _ _ _ _ _ _ _ _ HRO (c1_core_J _ _ _ _ _ _ _ _ HC)) as HV.
pose proof (c1_rom_rd_ro _ _ _ _ _ _ _ _ HRO HJ') as HV'.
destruct (c1_stk_facts _ _ _ Hstk) as (_ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
pose proof Hgeo as (HF4 & HFc & Hr4 & Hrc & _ & Ho4 & Hoc & _ & _ & _ & _ & Hpay).
assert (KL : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a)
  by (intros a Ha; apply HK; lia).
destruct Hfr as (F19 & F21 & F27).
pose proof (c1_base_len cx HB) as Hlen. pose proof (c1_body_len cx HB) as Hblen.
assert (Hrq : dec_a_len (d_n cx) <= req_size (dec_a_len (d_n cx)))
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_len (d_n cx)) 0); lia).
destruct (c1_meter_skip _ _ _ ML Hle Hok) as (Hle' & Hok').
assert (Hk8 : dec_ev_4fc <= dec_ev_5fc) by (unfold dec_ev_4fc, dec_ev_5fc; lia).
unfold c1_st.
refine (conj _ (conj Hk8 (conj _ (conj Hnr (conj Hno (conj Hgeo
  (conj Hle' (conj Hok' (conj _ (conj _ (conj S32 HRO))))))))))).
- apply (c1_core_move cx ly' S' W W ly' S' regs regs' mem mem' md md' dec_ev_4fc dec_ev_4fc HC HJ' eq_refl (fun H => H)).
  + intros r Hr. apply HR. cbn [In] in Hr |- *. intuition.
  + intros a Ha. destruct Ha as [Ha | [Ha | Ha]].
    * apply HK. unfold d_sp1 in *. lia.
    * apply KL. lia.
    * apply KL. destruct (Z_lt_ge_dec 0 (d_n cx)) as [Hn | Hn]; [destruct (Hpay Hn) as (Hp4 & Hpc & _); lia | lia].
  + intros a Ha. apply HG. exact (c1_core_fpres _ _ _ _ _ _ _ _ HC a Ha).
- rewrite Hbl. apply Permutation_refl.
- unfold c1_regs5.
  refine (conj _ (conj R19 (conj _ (conj _ (conj _ (conj R23 (conj _ (conj _ (conj _ _))))))))).
  + rewrite (HR 18%bv ltac:(cbn; tauto)). exact H18.
  + rewrite (HR 20%bv ltac:(cbn; tauto)). exact H20.
  + rewrite (HR 21%bv ltac:(cbn; tauto)). exact F21.
  + rewrite (HR 22%bv ltac:(cbn; tauto)). exact H22.
  + rewrite (HR 24%bv ltac:(cbn; tauto)). exact H24.
  + rewrite (HR 25%bv ltac:(cbn; tauto)). exact H25.
  + rewrite (HR 26%bv ltac:(cbn; tauto)). exact H26.
  + rewrite (HR 27%bv ltac:(cbn; tauto)). exact F27.
- apply (c1_mem_kept2 cx res out mode nch ns W W mem mem' HM).
  + destruct HM as (HMO & _).
    apply (c1_mode_re cx W W mem mem' ly' S' md ly' S' md' mode nch ns HCELLS HAR HAR' HV HV' HMO).
    intros kk Hkk. apply KL. lia.
  + intros a Ha. unfold c1_Rx in Ha. destruct Ha as [Ha | [Ha | Ha]].
    * apply KL. unfold d_SH, shadow_addr, SHADOW_OFF in *. Z.div_mod_to_equations. lia.
    * apply KL. lia.
    * apply HK. lia.
Qed.

(* A byte array of the view, read byte by byte. *)
Lemma c1_garr8_view : forall H mem p (bs : list byte),
  garr8 segs (mrestrict H mem) p (map (fun b : byte => bv_unsigned b) bs) ->
  forall j, (j < length bs)%nat -> aview segs H mem (p + Z.of_nat j) = Some (bv_unsigned (nth j bs (Z_to_bv 8 0))).
Proof.
intros H mem p bs Hg j Hj.
destruct (Hg j ltac:(rewrite length_map; exact Hj)) as [Hv _].
pose proof (Hv 0%nat ltac:(lia)) as Hb. change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb.
unfold aview. rewrite Hb. cbn [option_map]. f_equal.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. rewrite dec_leafb_le_byte1. reflexivity.
Qed.

(* check_round_trip's cost at a geometry the decoder accepted (nch * ns <= 480, nch <= 127) is at most the budget
   the interface sets aside for it. *)
Lemma c1_crt_cost_le : forall nch ns, ameter_laws MT -> 0 < nch <= 127 -> 0 < ns -> nch * ns <= 480 ->
  dec_crt_cost MT nch ns <= dec_crt_cost_max MT.
Proof.
intros nch ns ML Hn Hs H480. unfold dec_crt_cost, dec_crt_cost_max.
pose proof (mo_malloc_mono MT ML (4 * (nch * ns)) 1920 ltac:(nia)).
pose proof (mo_malloc_mono MT ML (8 * nch) 1016 ltac:(lia)).
pose proof (mo_malloc_mono MT ML (3 * (nch * ns)) 1440 ltac:(nia)). lia.
Qed.

(* check_round_trip #1 at +0x5b4 by its contract, then the rest of the segment (c1_T3_stmt) from its return
   +0x5b8. The call state: c1_st at the call memory, and the meter still holding the call's budget. *)
Lemma c1_Bcrt : forall (fx0 : YK11.FPState),
  AR_laws segs B -> ameter_laws MT -> dec_crt_cells B -> dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  (forall fx' : YK11.FPState,
     @dec_check_round_trip_cg fx' rc B MT (decode_sigma DS_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  c1_T3_stmt ->
  forall cx res out mode nch ns (W : world segs) regsT memT mdT ly' S',
  dec_base cx -> dec_a_rom cx -> frm_zero (@fp_csr fx0) ->
  c1_st cx res out mode nch ns W regsT memT mdT ly' S' dec_ev_4fc ->
  mo_le MT (d_S cx) S' (dec_spent_4fc MT (d_n cx)) -> mo_ok MT S' (dec_rest_4fc MT) ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + 0x5b8) ->
  YK11.getr regsT 10 = w64 (res + 50) -> YK11.getr regsT 11 = w64 out ->
  YK11.getr regsT 12 = w64 nch -> YK11.getr regsT 13 = w64 ns ->
  CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true -> ns <= 12 ->
  garr8 segs (mrestrict (w_H W) memT) out (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns)) ->
  SRr segs W (@cfg_at fx0 segs (decode_sigma DS_check_round_trip) regsT memT mdT) (llvm_a_st_5fc B MT cx).
Proof.
intros fx0 LAWS ML HCELLS HOWN HERR CRT T3 cx res out mode nch ns W regsT memT mdT ly' S' HB HR Hfrm Hst
  Hle4 Hok4 R1 R10 R11 R12 R13 Hdec Hns12 Hgout.
pose proof Hst as (HC & _ & HPm & _ & _ & Hgeo & _ & _ & _ & HM & _).
pose proof HM as (HMO & _ & Hgres & _).
pose proof HMO as (_ & Hnch & Hns & _ & _).
pose proof Hdec as Hd. unfold CDec.decode_ok in Hd. rewrite !andb_true_iff in Hd.
destruct Hd as ((((Hwf & Hn0) & Hev) & Hs0) & H480).
apply Z.ltb_lt in Hn0, Hs0. apply Z.eqb_eq in Hev. apply Z.leb_le in H480.
pose proof Hwf as Hwf'. unfold CInsp.inspect_wf in Hwf'. rewrite !andb_true_iff in Hwf'.
destruct Hwf' as ((((Hlen & _) & _) & _) & _). apply Z.eqb_eq in Hlen.
set (len := dec_a_len (d_n cx)) in *. set (body := d_body cx) in *. set (olen := dec_a_olen nch ns) in *.
assert (Holen : olen = 3 * nch * ns)
  by (unfold olen, dec_a_olen; rewrite (proj2 (Z.ltb_lt 0 nch) Hn0), (proj2 (Z.ltb_lt 0 ns) Hs0); reflexivity).
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (R8 & R9 & Hsp & Hs01 & Hs01' & Hal & Rgp & Rtp & _ & _ & Hfrs).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & Hstk & _ & _ & _).
destruct (c1_stk_facts _ _ _ Hstk) as (Ha16 & Hceil & Hslo & Hshi & H47 & Hbot & _ & _).
destruct (c1_J_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (EF & Etop).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
assert (Hsp1 : d_sp1 cx + 224 <= d_sp0 cx) by (unfold d_sp1; Z.div_mod_to_equations; lia).
assert (Hsv : dec_a_saved cx (aview segs (w_H W) memT))
  by (unfold dec_a_core in HC; decompose [and] HC; assumption).
assert (Hraz : raZ regsT = DEC_A_LLVMF + 0x5b8)
  by (unfold raZ; rewrite R1; apply unsigned_lit_small; vm_compute; split; congruence).
assert (Hra : In (raZ regsT) DEC_LLVMF_RA_CRT) by (rewrite Hraz; unfold DEC_LLVMF_RA_CRT; cbn [map In]; left; reflexivity).
destruct (c1_crt_chain cx W _ ly' S' memT mdT dec_ev_4fc regsT HB HJ Hsv R8 Hsp Hra) as (ch & Hch & Hctx).
assert (Hbody : Z.of_nat (length body) = len) by exact (c1_body_len cx HB).
assert (Ires : In (res, len) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; left; reflexivity).
assert (Iout : In (out, olen) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; right; left; reflexivity).
pose proof (c1_crt_cost_le nch ns ML ltac:(lia) Hs0 H480) as Hcost.
assert (Hrest : 0 <= dec_rest_5fc MT).
{ unfold dec_rest_5fc, dec_rest_748, dec_rest_86c. pose proof (c1_crt_max_nonneg ML).
  pose proof (mo_malloc_nonneg MT ML 1440 ltac:(lia)). pose proof (mo_free_nonneg MT ML). lia. }
eapply SRr_bind.
{ refine (CRT fx0 DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)]
    ly' S' W memT mdT dec_ev_4fc regsT (res + 50) out nch ns res len out olen (dec_rest_4fc MT) ch
    HJ _ _ Rgp Rtp R10 R11 R12 R13 Hch Hctx _ _ _ Hfrm _ _ _ _ _ Ires _ _ Iout _ _ _ _ _ _ Hok4 _).
  - rewrite R1. vm_compute. reflexivity.
  - rewrite Hraz. vm_compute. discriminate.
  - rewrite Hsp. lia.
  - rewrite Hsp. unfold DEC_LLVMF_STK, DEC_CRT_STK, DEC_CRT_FRAME, ASTACK. lia.
  - rewrite Hsp. lia.
  - rewrite c1_even_mod2. apply Z.eqb_eq. exact Hev.
  - lia.
  - lia.
  - nia.
  - rewrite Hsp. unfold ly_bot in *. rewrite Etop. unfold DEC_CALLOC_DEPTH, DEC_CRT_FRAME, ASTACK in *. lia.
  - lia.
  - nia.
  - lia.
  - rewrite Holen. lia.
  - apply (c1_crt_braid _ out res body nch ns).
    + exact (c1_garr8_view _ _ _ _ Hgout).
    + exact (c1_garr8_view _ _ _ _ Hgres).
    + rewrite Hbody. nia.
    + exact Hn0.
    + exact Hev.
    + exact Hs0.
  - exact (c1_rom_rd cx _ ly' S' W memT mdT dec_ev_4fc HR HOWN HERR HJ).
  - pose proof (c1_base_nev cx HB). unfold dec_ev_4fc, DEC_CRT_EV, DEC_EV_LIB in *. lia.
  - rewrite (blocks_bytes_bsum B ly' S'), (bsum_perm _ _ HPm), !bsum_app.
    rewrite <- (blocks_bytes_bsum B (d_ly cx) (d_S cx)). cbn [bsum fold_right snd].
    pose proof (c1_base_bb cx HB). pose proof (c1_base_len cx HB).
    assert (Hn26 : d_n cx < 2 ^ 26).
    { destruct (c1_base_pn cx HB) as [(Hz & _) | (Hz & _)]; lia. }
    unfold len, dec_a_len, DEC_CRT_LIVE, DEC_LIVE_LIB, LIVE_MAX in *. nia.
  - unfold dec_rest_4fc. lia. }
cbv beta. intros W2 c2 Hwle (fx2 & ly2 & S2 & regs2 & mem2 & md2 & -> & Hfrm2 & HJ2 & HP & Hfr2 & HPm2 & HK & Hmle2).
rewrite R1.
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & _ & _ & _ & _).
destruct (c1_J_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (EF2 & _).
destruct HK as (K1 & K2 & _ & K4 & _ & _).
assert (Ifr : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (EFa : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite EF; reflexivity).
pose proof Hgeo as (HF4 & HFc & Hr4 & Hrc & _ & Ho4 & Hoc & _ & _ & _ & _ & Hpay).
assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
assert (Hoq : olen <= req_size olen) by (unfold req_size; destruct (Z.eqb_spec olen 0); lia).
(* the bytes the walk reads on are the call's to keep: stack bytes above its window, the frame and its shadow, the
   blocks *)
assert (KF : forall a, d_F cx <= a < d_F cx + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha. apply (K4 DEC_FCLASS (d_fpos cx) a Ifr); [left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EFa;
    replace (fs_frame_bytes DEC_FCLASS) with 64 by reflexivity; lia | tauto]. }
assert (KSH : forall a, d_SH cx <= a < d_SH cx + 8 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha. apply (K4 DEC_FCLASS (d_fpos cx) a Ifr); [right; unfold in_zr; cbn [fst snd]; rewrite EFa;
    replace (fs_frame_bytes DEC_FCLASS / 8) with 8 by reflexivity; unfold d_SH in Ha; lia | tauto]. }
assert (KB : forall b m a, In (b, m) (ablocks B ly' S') -> b <= a < b + req_size m ->
  aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros b m a Hin Ha. replace a with (b + (a - b)) by lia. apply (K2 b m (a - b) Hin); [lia | tauto]. }
assert (KS : forall a, d_sp1 cx <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memT a).
{ intros a Ha. apply K1; [lia|]. rewrite Hsp. lia. }
apply (T3 fx2 0x5b8 cx res out mode nch ns W2 regs2 mem2 md2 ly2 S2 (dec_ev_4fc + DEC_CRT_EV) (or_introl eq_refl) HB HR Hfrm2).
- apply (c1_st_move cx res out mode nch ns W W2 regsT regs2 memT mem2 mdT md2 ly' S' ly2 S2 dec_ev_4fc
    (dec_ev_4fc + DEC_CRT_EV) HCELLS Hst HJ2).
  + unfold dec_ev_4fc, DEC_CRT_EV, dec_ev_5fc. lia.
  + exact Hfr2.
  + exact HPm2.
  + apply (mo_le_mono MT ML _ _ _ _ (mo_le_trans MT ML _ _ _ _ _ Hle4 Hmle2)). unfold dec_spent_5fc. lia.
  + apply (mo_ok_step MT ML S' S2 (dec_crt_cost MT nch ns) (dec_rest_5fc MT)); [|exact Hmle2].
    apply (mo_ok_le MT ML _ _ _ Hok4). unfold dec_rest_4fc. lia.
  + exact HP.
  + intros a Ha. unfold c1_K in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]].
    * apply KS. lia.
    * apply KF. exact Ha.
    * destruct (Z_lt_ge_dec 0 (d_n cx)) as [Hn | Hn].
      -- assert (Ipay : In (d_p cx, d_n cx) (ablocks B ly' S')) by (unfold dec_a_core in HC; decompose [and] HC; auto).
         apply (KB _ _ a Ipay). pose proof (c1_base_len cx HB).
         unfold req_size; destruct (Z.eqb_spec (d_n cx) 0); lia.
      -- pose proof (c1_base_len cx HB). lia.
    * apply KSH. exact Ha.
    * apply (KB _ _ a Ires). pose proof (c1_body_len cx HB) as Hb'. fold len in Hb'. lia.
    * apply KS. lia.
  + assert (EFa2 : frame_addr ly2 DEC_FCLASS (d_fpos cx) = d_F cx)
      by (unfold d_F, frame_addr; rewrite EF2; reflexivity).
    pose proof (al_frames _ _ LAWS ly2 S2 W2 mem2 md2 _ _ HAR2 ltac:(rewrite Hfr2; exact Ifr)) as HAF.
    rewrite EFa2 in HAF. replace (fs_frame_bytes DEC_FCLASS) with 64 in HAF by reflexivity.
    destruct HAF as (_ & _ & HFP2 & _).
    intros a Ha. exact (proj1 (HFP2 a Ha)).
- exact Hdec.
- refine (c1_garr8_x _ _ _ _ _ _ _ Hgout). intros kk Hkk. rewrite length_map in Hkk.
  unfold CDec.braid_out in Hkk. rewrite RDL.length_mapseq in Hkk.
  apply (KB _ _ _ Iout). nia.
Qed.

Lemma c1_soff_reg : forall Ex regs X (n : nat) (r : bv 5),
  (forall m, (m < 512)%nat -> ew Ex m = ew (Eimg (Ereg regs X)) m) -> Z.of_nat n = bv_unsigned r ->
  sv_denot Ex (SOff n 0) = YK11.getr regs r.
Proof.
intros Ex regs X n r AG Hn. pose proof (u5_range r) as Hr.
rewrite denot_lit_U, U_SOff, (AG n ltac:(lia)), Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs X n r Hn), Z.add_0_r.
unfold zcanon, M64. rewrite Z.mod_small by (apply bv_unsigned_in_range).
apply Z_to_bv_bv_unsigned.
Qed.

(* A register's symbolic value at a call state (st_ok form). *)
Ltac c1_reg2 HS r Hr :=
  lazymatch type of HS with
  | st_ok ?sg ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg sg H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict YK11.mkst] in Hr
  end.

(* The braid relation at the image view gives check_braid's braid_map (decode's mrd): two bytes the view reads alike
   are the same byte. *)
Lemma c1_braid_map : forall (W : world segs) mem audio pcm nch ns,
  dec_crt_braid (aview segs (w_H W) mem) audio pcm nch ns -> DCBc.braid_map mem audio pcm nch ns.
Proof.
intros W mem audio pcm nch ns HB ch s j Hch Hs Hj.
destruct (HB ch s j Hch Hs Hj) as (v & H1 & H2).
destruct (dec_leafb_mrd_aview W mem _ v H1) as (b1 & M1 & E1).
destruct (dec_leafb_mrd_aview W mem _ v H2) as (b2 & M2 & E2).
assert (Eb : b2 = b1) by (apply bv_eq; congruence). subst b2.
exists b1. split; [exact M1 | exact M2].
Qed.

(* Where the bytes c1_K names lie: below the allocator ceiling or above s1 + 32 (so outside every callee's stack
   window), and outside the output buffer. *)
Lemma c1_K_out : forall cx res out mode nch ns (W : world segs) regs mem md ly' S' k,
  dec_base cx -> c1_st cx res out mode nch ns W regs mem md ly' S' k ->
  forall a, c1_K cx res a ->
  0 <= a < 2 ^ 64 /\ (a < alloc_ceiling \/ d_sp1 cx + 32 <= a) /\ ~ (out <= a < out + req_size (dec_a_olen nch ns)).
Proof.
intros cx res out mode nch ns W regs mem md ly' S' k HB Hst a Ha.
pose proof Hst as (HC & _ & _ & _ & _ & Hgeo & _).
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (_ & _ & _ & Hs01 & Hs01' & _ & _ & _ & _ & _ & _).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & Hstk & _ & _ & _).
destruct (c1_stk_facts _ _ _ Hstk) as (_ & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
pose proof Hgeo as (HF4 & HFc & Hr4 & Hrc & _ & Ho4 & Hoc & Hoapp & Dro & Dof & _ & Hpay).
pose proof (c1_base_len cx HB) as Hlen. pose proof (c1_body_len cx HB) as Hbl.
assert (Hrq : dec_a_len (d_n cx) <= req_size (dec_a_len (d_n cx)))
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_len (d_n cx)) 0); lia).
assert (Hoq : 1 <= req_size (dec_a_olen nch ns))
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_olen nch ns) 0); [lia|]; unfold dec_a_olen in *;
      destruct ((0 <? nch) && (0 <? ns)) eqn:Ep; [apply andb_true_iff in Ep as [E1 E2]; apply Z.ltb_lt in E1, E2; nia | lia]).
unfold zdisjoint in Dro, Dof. cbn [fst snd] in Dro, Dof.
unfold c1_K in Ha. destruct Ha as [Ha | [Ha | [Ha | [Ha | [Ha | Ha]]]]].
- lia.
- lia.
- destruct (Z_lt_ge_dec 0 (d_n cx)) as [Hn | Hn].
  + destruct (Hpay Hn) as (Hp4 & Hpc & Dpo). unfold zdisjoint in Dpo. cbn [fst snd] in Dpo.
    assert (Hrqn : req_size (d_n cx) = d_n cx) by (unfold req_size; destruct (Z.eqb_spec (d_n cx) 0); lia).
    rewrite Hrqn in Dpo. lia.
  + lia.
- unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Hoapp. unfold d_SH, shadow_addr, SHADOW_OFF in Ha. lia.
- lia.
- lia.
Qed.

(* check_braid #1 at +0x5d4 by its leaf contract through the shared bridge (dec_leafb_journal), then the rest of the
   segment (c1_T2_stmt) from its return +0x5d8. *)
Lemma c1_braid_call : forall (fx0 : YK11.FPState),
  AR_laws segs B -> dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx') ->
  c1_T2_stmt ->
  forall cx res out mode nch ns (W : world segs) regsT memT mdT ly' S' k,
  dec_base cx -> dec_a_rom cx -> frm_zero (@fp_csr fx0) ->
  c1_st cx res out mode nch ns W regsT memT mdT ly' S' k ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + 0x5d8) ->
  YK11.getr regsT 10 = w64 (res + 50) -> YK11.getr regsT 11 = w64 out ->
  YK11.getr regsT 12 = w64 nch -> YK11.getr regsT 13 = w64 ns ->
  CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
  garr8 segs (mrestrict (w_H W) memT) out (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns)) ->
  SRr segs W (mkCfg (@YK11.mkst fx0 regsT (Z_to_bv 64 (decode_sigma DS_check_braid)) memT (YK11.seg_rom segs)) mdT)
    (llvm_a_st_5fc B MT cx).
Proof.
intros fx0 LAWS HCELLS LCB T2 cx res out mode nch ns W regsT memT mdT ly' S' k HB HR Hfrm Hst R1 R10 R11 R12 R13
  Hdec Hgout.
pose proof Hst as (HC & Hk & HPm & _ & _ & Hgeo & Hle & Hok & _ & HM & _).
pose proof HM as (HMO & _ & Hgres & _). pose proof HMO as (_ & Hnch & Hns & _ & _).
pose proof Hdec as Hd. unfold CDec.decode_ok in Hd. rewrite !andb_true_iff in Hd.
destruct Hd as ((((Hwf & Hn0) & Hev) & Hs0) & H480).
apply Z.ltb_lt in Hn0, Hs0. apply Z.eqb_eq in Hev. apply Z.leb_le in H480.
pose proof Hwf as Hwf'. unfold CInsp.inspect_wf in Hwf'. rewrite !andb_true_iff in Hwf'.
destruct Hwf' as ((((Hlen & _) & _) & _) & _). apply Z.eqb_eq in Hlen.
pose proof (c1_body_len cx HB) as Hbody.
set (len := dec_a_len (d_n cx)) in *. set (body := d_body cx) in *. set (olen := dec_a_olen nch ns) in *.
assert (Holen : olen = 3 * nch * ns)
  by (unfold olen, dec_a_olen; rewrite (proj2 (Z.ltb_lt 0 nch) Hn0), (proj2 (Z.ltb_lt 0 ns) Hs0); reflexivity).
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (R8 & R9 & Hsp & Hs01 & Hs01' & Hal & Rgp & Rtp & _ & _ & Hfrs).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & Hstk & _ & _ & _).
destruct (c1_stk_facts _ _ _ Hstk) as (Ha16 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
assert (Hsp' : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = d_sp1 cx) by exact Hsp.
pose proof Hgeo as (HF4 & HFc & Hr4 & Hrc & Hrapp & Ho4 & Hoc & Hoapp & _).
fold len in Hrc. fold olen in Hoc.
assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
assert (Hoq : olen <= req_size olen) by (unfold req_size; destruct (Z.eqb_spec olen 0); lia).
assert (Ires : In (res, len) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; left; reflexivity).
assert (Iout : In (out, olen) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; right; left; reflexivity).
assert (HN : 0 < 3 * nch * ns) by (clear - Hn0 Hs0; nia).
eapply SRr_bind.
{ apply (@dec_leafb_journal fx0 rc dec_A_sink_head B LAWS W regsT memT DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx)
    (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' mdT k (d_sp1 cx - d_sp0 cx)
    (decode_sigma DS_check_braid) None [] (fun _ => True) HJ).
  - rewrite Hsp. lia.
  - unfold d_sp1. Z.div_mod_to_equations. lia.
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - rewrite R1. vm_compute. reflexivity.
  - exact Rgp.
  - exact Rtp.
  - intros a Ha. inversion Ha.
  - intros Hpre.
    refine (LCB fx0 ly' S' W regsT memT mdT (res + 50) out nch ns (d_sp1 cx - ESTACK) Hpre R10 R11 R12 R13
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbv zeta; rewrite ?Hsp'.
    + lia.
    + lia.
    + lia.
    + lia.
    + apply (c1_braid_map W memT).
      apply (c1_crt_braid _ out res body nch ns).
      * exact (c1_garr8_view _ _ _ _ Hgout).
      * exact (c1_garr8_view _ _ _ _ Hgres).
      * rewrite Hbody. lia.
      * exact Hn0.
      * exact Hev.
      * exact Hs0.
    + apply (dec_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); unfold ESTACK; lia.
    + unfold ESTACK, DCBc.CHECK_BRAID_FRAME. lia.
    + left. unfold DCBc.CHECK_BRAID_FRAME. rewrite Hev. lia.
    + left. unfold DCBc.CHECK_BRAID_FRAME. lia.
    + exact (dec_leafb_asan_cells B HCELLS ly' S' W memT mdT HAR).
    + apply dec_leafb_app_stack. unfold DCBc.CHECK_BRAID_FRAME. lia.
    + apply dec_leafb_app_stack. lia.
    + left. rewrite Hsp'. unfold ACells.GOT_CELL_K, ACells.MIDEND, DCBc.CHECK_BRAID_FRAME. lia.
    + apply (dec_leafb_addressable_block B LAWS ly' S' W memT mdT res len); [exact HAR | exact Ires | lia | | ].
      * rewrite Hev. lia.
      * rewrite Hev. lia.
    + apply (dec_leafb_addressable_block B LAWS ly' S' W memT mdT out olen); [exact HAR | exact Iout | lia | lia | lia].
    + apply (dec_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); unfold DCBc.CHECK_BRAID_FRAME; lia.
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + apply (dec_leafb_rng_block B LAWS ly' S' W memT mdT out olen); [exact HAR | exact Iout | lia | lia].
    + apply (dec_leafb_rng_block B LAWS ly' S' W memT mdT res len); [exact HAR | exact Ires | lia |].
      rewrite Hev. lia.
    + apply (dec_leafb_rng_shadow_block B LAWS ly' S' W memT mdT out olen); [exact HAR | exact Iout | lia | lia | lia].
    + apply (dec_leafb_rng_shadow_block B LAWS ly' S' W memT mdT res len); [exact HAR | exact Ires | lia | | ].
      * rewrite Hev. lia.
      * rewrite Hev. lia. }
cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & HK & HG & _).
rewrite R1.
apply (T2 fx0 cx res out mode nch ns W regs2 mem2 md2 ly' S' k HB HR Hfrm).
apply (c1_st_move cx res out mode nch ns W W regsT regs2 memT mem2 mdT md2 ly' S' ly' S' k k HCELLS Hst HJ2 Hk
  eq_refl (Permutation_refl _) Hle Hok HP).
- intros a Ha. destruct (c1_K_out cx res out mode nch ns W regsT memT mdT ly' S' k HB Hst a Ha) as (Hr & Hlo & _).
  apply HK; [exact Hr | rewrite Hsp; unfold ESTACK; lia | intros Hw; inversion Hw].
- intros a Ha. apply HG. exact (c1_core_fpres _ _ _ _ _ _ _ _ HC a Ha).
Qed.

(* ------------------------------------------------------------------ *)
(* The two calls of the tail: __asan_memset and reac_decode_plain_le   *)
(* ------------------------------------------------------------------ *)

Lemma c1_aregs_of : forall regs regs',
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> YK11.getr regs' r = YK11.getr regs r) ->
  aregs_preserved regs regs'.
Proof.
intros regs regs' H r Hr. unfold acallee_saved in Hr.
assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
  r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]];
  apply H; cbn [In]; repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.

Lemma c1_core_mono : forall cx ly' S' (W : world segs) regs mem md k k',
  dec_a_core B cx ly' S' W regs mem md k -> k <= k' -> dec_a_core B cx ly' S' W regs mem md k'.
Proof.
intros cx ly' S' W regs mem md k k' HC Hk.
apply (c1_core_move cx ly' S' W W ly' S' regs regs mem mem md md k k' HC).
- eapply ajournal_mono_k; [exact (c1_core_J _ _ _ _ _ _ _ _ HC) | exact Hk].
- reflexivity.
- exact (fun H => H).
- intros r _. reflexivity.
- intros a _. reflexivity.
- exact (c1_core_fpres _ _ _ _ _ _ _ _ HC).
Qed.

(* A byte array of raw bytes over visible addresses is a byte array of the view. *)
Lemma c1_garr8_of_bytes : forall (W : world segs) mem p (bs : list byte),
  LMem.bytes_at segs mem p bs ->
  (forall j, (j < length bs)%nat -> w_H W (Z_to_bv 64 (p + Z.of_nat j)) = false) ->
  garr8 segs (mrestrict (w_H W) mem) p (map (fun b : byte => bv_unsigned b) bs).
Proof.
intros W mem p bs (_ & _ & HB) HV j Hj. rewrite length_map in Hj.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj).
rewrite map_nth. split.
- intros k Hk. assert (k = 0%nat) as -> by lia. change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
  rewrite <- (dec_leafb_mrd W mem _ (HV j Hj)). rewrite (HB j Hj).
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hj). f_equal. symmetry. apply dec_leafb_le_byte1.
- pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R. exact R.
Qed.

Lemma c1_cell1 : forall ly S (W : world segs) mem md a v,
  @AR rc segs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) ->
  aview segs (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v HAR Hin. destruct HAR as [HARm _].
pose proof (am_const _ _ _ _ HARm) as HC. rewrite Forall_forall in HC.
assert (H : forall k, (k < 1)%nat -> aview segs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v 1 k)) by exact (HC _ Hin).
pose proof (H 0%nat ltac:(lia)) as H0. change (Z.of_nat 0) with 0 in H0. rewrite Z.add_0_r in H0. exact H0.
Qed.

(* The mode is one of the three tables (their pointer words are constant cells of dec_crt_cells) or the frame's
   local. *)
Lemma c1_mode_cases : forall cx ly S (W : world segs) mem md mode nch ns,
  dec_crt_cells B -> @AR rc segs B ly S W mem md -> dec_a_mode_ok cx W mem mode nch ns ->
  mode = 0x20d40 \/ mode = 0x20d80 \/ mode = 0x20d60 \/ mode = d_F cx + 32.
Proof.
intros cx ly S W mem md mode nch ns HCELLS HAR (Hmc & _).
destruct Hmc as [Hc | [Hc | [Hc | Hc]]].
- left. rewrite (c1_cell8 ly S W mem md (decode_obj 4) 0x20d40 HAR ltac:(dec_leafb_row HCELLS ly) ltac:(lia)) in Hc.
  injection Hc as <-. reflexivity.
- right; left. rewrite (c1_cell8 ly S W mem md (decode_obj 5) 0x20d80 HAR ltac:(dec_leafb_row HCELLS ly) ltac:(lia)) in Hc.
  injection Hc as <-. reflexivity.
- right; right; left.
  rewrite (c1_cell8 ly S W mem md (decode_obj 6) 0x20d60 HAR ltac:(dec_leafb_row HCELLS ly) ltac:(lia)) in Hc.
  injection Hc as <-. reflexivity.
- right; right; right. exact Hc.
Qed.

(* The one read of a table's first shadow granule (0) in this file: the dec_tab_zshadow_at conjunct of
   dec_crt_cells, picked by its statement, read at the state's AR by check_round_trip_cg.v's dec_tab_zshadow_rd. *)
Lemma c1_tab_sh0 : forall ly S (W : world segs) mem md T,
  dec_crt_cells B -> @AR rc segs B ly S W mem md -> (T = 0x20d40 \/ T = 0x20d80 \/ T = 0x20d60) ->
  aview segs (w_H W) mem (SHADOW_OFF + T / 8) = Some 0.
Proof.
intros ly S W mem md T HCELLS HAR HT.
assert (V : forall T', T' mod 8 = 0 -> dec_tab_zshadow_at B T' -> aview segs (w_H W) mem (SHADOW_OFF + T' / 8) = Some 0).
{ intros T' H8 HZ. pose proof (dec_tab_zshadow_rd B ly S W mem md T' HAR H8 HZ) as V0.
  unfold DCells.shadow_addr, DCells.ASAN_K in V0. unfold SHADOW_OFF. rewrite Z.add_comm. exact V0. }
destruct HT as [-> | [-> | ->]]; (apply V; [reflexivity | dec_leafb_row HCELLS ly]).
Qed.

(* The two 4-byte fields at mode + 4 are addressable: the tables' first shadow granule is 0 (c1_tab_sh0) and their
   second 4 (a constant cell of dec_crt_cells), and the frame's local has its two shadow bytes 0 / 4 (dec_a_fsh). *)
Lemma c1_mode_ra : forall cx ly S (W : world segs) mem md mode nch ns,
  dec_crt_cells B -> @AR rc segs B ly S W mem md ->
  dec_a_mode_ok cx W mem mode nch ns -> dec_a_fsh cx (aview segs (w_H W) mem) 0 4 -> d_F cx mod 32 = 0 ->
  0 <= d_F cx ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (mode + 4) 8.
Proof.
intros cx ly S W mem md mode nch ns HCELLS HAR HMO (_ & F4 & F5 & _) HF32 HF0.
assert (TBL : forall T T8, (T = 0x20d40 \/ T = 0x20d80 \/ T = 0x20d60) -> T8 = T + 8 ->
  In (z1 (ANum (DCells.shadow_addr T8)) 4) (as_const B ly) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (T + 4) 8).
{ intros T T8 HT HT8 H4 x Hx. unfold shadow_of_addr.
  pose proof (c1_tab_sh0 _ _ _ _ _ T HCELLS HAR HT) as V0. pose proof (c1_cell1 _ _ _ _ _ _ _ HAR H4) as V4.
  unfold DCells.shadow_addr, DCells.ASAN_K in V4. subst T8.
  assert (HT32 : T mod 32 = 0 /\ 0 <= T) by (destruct HT as [-> | [-> | ->]]; (split; [reflexivity | lia])).
  destruct HT32 as [HT32 HT0].
  destruct (Z_lt_ge_dec x (T + 8)) as [Hl | Hg].
  - exists 0. split; [| left; reflexivity].
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + T / 8) by (Z.div_mod_to_equations; lia).
    exact V0.
  - exists 4. split; [| right; split; [Z.div_mod_to_equations; lia | lia]].
    replace (SHADOW_OFF + x / 8) with ((T + 8) / 8 + 2147450880) by (unfold SHADOW_OFF; Z.div_mod_to_equations; lia).
    rewrite V4. reflexivity. }
destruct (c1_mode_cases cx ly S W mem md mode nch ns HCELLS HAR HMO) as [-> | [-> | [-> | ->]]].
- exact (TBL 0x20d40 0x20d48 ltac:(lia) eq_refl ltac:(dec_leafb_row HCELLS ly)).
- exact (TBL 0x20d80 0x20d88 ltac:(lia) eq_refl ltac:(dec_leafb_row HCELLS ly)).
- exact (TBL 0x20d60 0x20d68 ltac:(lia) eq_refl ltac:(dec_leafb_row HCELLS ly)).
- intros x Hx. unfold shadow_of_addr. unfold d_SH, shadow_addr in F4, F5.
  destruct (Z_lt_ge_dec x (d_F cx + 40)) as [Hl | Hg].
  + exists 0. split; [| left; reflexivity].
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + d_F cx / 8 + 4) by (Z.div_mod_to_equations; lia).
    exact F4.
  + exists 4. split; [| right; split; [Z.div_mod_to_equations; lia | lia]].
    replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + d_F cx / 8 + 5) by (Z.div_mod_to_equations; lia).
    exact F5.
Qed.

(* __asan_memset (out, 0xa5, olen) at +0x5e4 by the statement's aintrin_realizes (YC85.v aj_intrin_atS), then the
   rest from its return +0x5e8: the buffer holds the fill, every byte c1_K names is kept. *)
Lemma c1_memset_call : forall (fx0 : YK11.FPState),
  AR_laws segs B -> dec_crt_cells B ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (decode_sigma DS___asan_memset)) ->
  forall cx res out mode nch ns (W : world segs) regsT memT mdT ly' S' k Q,
  dec_base cx ->
  c1_st cx res out mode nch ns W regsT memT mdT ly' S' k ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + 0x5e8) ->
  YK11.getr regsT 10 = w64 out -> YK11.getr regsT 11 = w64 165 -> YK11.getr regsT 12 = w64 (dec_a_olen nch ns) ->
  (forall regs2 mem2 md2, c1_st cx res out mode nch ns W regs2 mem2 md2 ly' S' k ->
     dec_a_filled W mem2 out (dec_a_olen nch ns) ->
     SRr segs W (mkCfg (@YK11.mkst fx0 regs2 (w64 (DEC_A_LLVMF + 0x5e8)) mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx0 regsT (Z_to_bv 64 (decode_sigma DS___asan_memset)) memT (YK11.seg_rom segs)) mdT) Q.
Proof.
intros fx0 LAWS HCELLS AMS cx res out mode nch ns W regsT memT mdT ly' S' k Q HB Hst R1 R10 R11 R12 K.
pose proof Hst as (HC & Hk & HPm & Hnr & Hno & Hgeo & Hle & Hok & _ & HM & _).
pose proof HM as (HMO & _). pose proof HMO as (_ & Hnch & Hns & _ & _).
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (R8 & R9 & Hsp & Hs01 & Hs01' & Hal & Rgp & Rtp & _ & _ & Hfrs).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & Hstk & _ & _ & _).
destruct (c1_stk_facts _ _ _ Hstk) as (Ha16 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
pose proof Hgeo as (HF4 & HFc & Hr4 & Hrc & Hrapp & Ho4 & Hoc & Hoapp & _).
assert (Hol : 1 <= dec_a_olen nch ns <= 3 * 127 * 127).
{ unfold dec_a_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:Ep; [|lia].
  apply andb_true_iff in Ep as [Ep1 Ep2]. apply Z.ltb_lt in Ep1, Ep2. nia. }
assert (Hoq : req_size (dec_a_olen nch ns) = dec_a_olen nch ns)
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_olen nch ns) 0); lia).
rewrite Hoq in Hoc.
assert (Iout : In (out, dec_a_olen nch ns) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; right; left; reflexivity).
eapply SRr_bind.
{ apply (@aj_intrin_atS fx0 rc dec_A_sink_head segs B LAWS decode_segs_low OSet (decode_sigma DS___asan_memset) (AMS fx0)
    W regsT memT DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)]
    ly' S' mdT k out 165 (dec_a_olen nch ns) (d_sp1 cx - d_sp0 cx) (YK11.getr regsT 1) HJ R10 R11 R12).
  - lia.
  - lia.
  - lia.
  - rewrite Hsp. lia.
  - unfold d_sp1. Z.div_mod_to_equations. lia.
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - exact Rgp.
  - exact Rtp.
  - reflexivity.
  - rewrite R1. vm_compute. reflexivity.
  - intros a Ha. split.
    + right. right. left. exists out, (dec_a_olen nch ns). split; [exact Iout|]. split; [exact Hno | rewrite Hoq; lia].
    + unfold ESTACK. lia.
  - exact (amem_range_of_block segs B LAWS _ _ _ _ _ out (dec_a_olen nch ns) out (dec_a_olen nch ns) HAR Iout
      ltac:(lia) ltac:(rewrite Hoq; lia)).
  - exact (range_addressable_of_block segs B LAWS _ _ _ _ _ out (dec_a_olen nch ns) out (dec_a_olen nch ns) HAR Iout
      ltac:(lia) ltac:(rewrite Hoq; lia)).
  - intros Hn. exact (shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ out (dec_a_olen nch ns) out (dec_a_olen nch ns)
      HAR Iout ltac:(lia) ltac:(rewrite Hoq; lia) Hn).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & _ & Hset & HK & HG & _).
rewrite R1.
apply K.
- apply (c1_st_move cx res out mode nch ns W W regsT regs2 memT mem2 mdT md2 ly' S' ly' S' k k HCELLS Hst HJ2 Hk
    eq_refl (Permutation_refl _) Hle Hok HP).
  + intros a Ha. destruct (c1_K_out cx res out mode nch ns W regsT memT mdT ly' S' k HB Hst a Ha) as (Hr & Hlo & Hno').
    rewrite Hoq in Hno'.
    apply HK; [exact Hr | exact Hno' | unfold ESTACK; lia].
  + intros a Ha. apply HG. exact (c1_core_fpres _ _ _ _ _ _ _ _ HC a Ha).
- intros i Hi. rewrite (Hset i Hi). reflexivity.
Qed.

(* reac_decode_plain_le (res, len, mode, out) at +0x5f8 by its leaf contract through the shared bridge
   (dec_leafb_journal); its return +0x5fc is the segment's post. *)
Lemma c1_plain_call : forall (fx0 : YK11.FPState),
  AR_laws segs B -> dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx') ->
  forall cx res out mode nch ns (W : world segs) regsT memT mdT ly' S' k,
  dec_base cx -> frm_zero (@fp_csr fx0) -> k <= dec_ev_5fc ->
  c1_st cx res out mode nch ns W regsT memT mdT ly' S' k ->
  dec_a_filled W memT out (dec_a_olen nch ns) ->
  YK11.getr regsT 1 = w64 (DEC_A_LLVMF + 0x5fc) ->
  YK11.getr regsT 10 = w64 res -> YK11.getr regsT 11 = w64 (dec_a_len (d_n cx)) ->
  YK11.getr regsT 12 = w64 mode -> YK11.getr regsT 13 = w64 out ->
  SRr segs W (mkCfg (@YK11.mkst fx0 regsT (Z_to_bv 64 (decode_sigma DS_reac_decode_plain_le)) memT (YK11.seg_rom segs)) mdT)
    (llvm_a_st_5fc B MT cx).
Proof.
intros fx0 LAWS HCELLS LPL cx res out mode nch ns W regsT memT mdT ly' S' k HB Hfrm Hk5 Hst Hfill
  R1 R10 R11 R12 R13.
pose proof Hst as (HC & Hk & HPm & Hnr & Hno & Hgeo & Hle & Hok & HR5 & HM & S32 & HRO).
pose proof HM as (HMO & Hfsh & Hgres & _). pose proof HMO as (_ & Hnch & Hns & Hv4 & Hv8).
pose proof (c1_body_len cx HB) as Hbody.
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (R8 & R9 & Hsp & Hs01 & Hs01' & Hal & Rgp & Rtp & HFa4 & HF32 & Hfrs).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & Hstk & _ & _ & _).
destruct (c1_stk_facts _ _ _ Hstk) as (Ha16 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
destruct (c1_J_ly _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (EF & _).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
assert (Hsp' : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = d_sp1 cx) by exact Hsp.
pose proof Hgeo as (HF4 & HFc & Hr4 & Hrc & Hrapp & Ho4 & Hoc & Hoapp & Dro & _ & _ & _).
assert (Hlen26 : 0 <= dec_a_len (d_n cx) < 2 ^ 26).
{ pose proof (c1_base_len cx HB) as Hl. destruct (c1_base_pn cx HB) as [(Hz & _) | (Hz & _)];
  unfold dec_a_len, dec_a_u in *; lia. }
assert (Ha1 : bv_unsigned (YK11.getr regsT (Z_to_bv 5 11)) = dec_a_len (d_n cx))
  by (transitivity (bv_unsigned (w64 (dec_a_len (d_n cx)))); [f_equal; exact R11 | apply unsigned_lit_small; lia]).
assert (Hrq : dec_a_len (d_n cx) <= req_size (dec_a_len (d_n cx)))
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_len (d_n cx)) 0); lia).
assert (Hoq : dec_a_olen nch ns <= req_size (dec_a_olen nch ns))
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_olen nch ns) 0); lia).
assert (Ires : In (res, dec_a_len (d_n cx)) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; left; reflexivity).
assert (Iout : In (out, dec_a_olen nch ns) (ablocks B ly' S'))
  by (apply (Permutation_in _ (Permutation_sym HPm)); apply in_or_app; right; right; left; reflexivity).
assert (Ifr : In (DEC_FCLASS, d_fpos cx) (frames S')) by (rewrite Hfrs; left; reflexivity).
assert (EFa : frame_addr ly' DEC_FCLASS (d_fpos cx) = d_F cx) by (unfold d_F, frame_addr; rewrite EF; reflexivity).
pose proof (al_frames _ _ LAWS ly' S' W memT mdT _ _ HAR Ifr) as HAF. rewrite EFa in HAF.
replace (fs_frame_bytes DEC_FCLASS) with 64 in HAF by reflexivity.
destruct HAF as (_ & HFapp & _).
pose proof (c1_mode_cases cx ly' S' W memT mdT mode nch ns HCELLS HAR HMO) as HMC.
assert (Hmb : 0 <= mode /\ mode + 12 <= 2 ^ 47) by (destruct HMC as [-> | [-> | [-> | ->]]]; lia).
pose proof (c1_mode_ra cx ly' S' W memT mdT mode nch ns HCELLS HAR HMO Hfsh HF32 ltac:(lia)) as Hmra.
(* what plain_ok gives *)
assert (PK : CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
  dec_a_len (d_n cx) = 1492 /\ 0 < nch /\ 0 < ns /\ nch * ns <= 480 /\ dec_a_olen nch ns = 3 * nch * ns).
{ intros Hp. unfold CPlain.plain_ok in Hp. rewrite !andb_true_iff in Hp.
  destruct Hp as (((Hwf & Hn0) & Hs0) & H480). apply Z.ltb_lt in Hn0, Hs0. apply Z.leb_le in H480.
  pose proof Hwf as Hwf'. unfold CInsp.inspect_wf in Hwf'. rewrite !andb_true_iff in Hwf'.
  destruct Hwf' as ((((Hl & _) & _) & _) & _). apply Z.eqb_eq in Hl.
  refine (conj Hl (conj Hn0 (conj Hs0 (conj H480 _)))).
  unfold dec_a_olen. rewrite (proj2 (Z.ltb_lt 0 nch) Hn0), (proj2 (Z.ltb_lt 0 ns) Hs0). reflexivity. }
(* the mode's application bytes *)
assert (HMapp : forall i, 0 <= i < 8 -> ACells.app_mem (mode + 4 + i)).
{ intros i Hi. destruct HMC as [-> | [-> | [-> | ->]]];
    [ left; unfold ACells.LOWMEM_END; lia .. |].
  replace (d_F cx + 32 + 4 + i) with (d_F cx + (36 + i)) by lia.
  exact (dec_leafb_app_of_in_app (d_F cx) 64 (36 + i) HFapp ltac:(lia)). }
eapply SRr_bind.
{ apply (@dec_leafb_journal fx0 rc dec_A_sink_head B LAWS W regsT memT DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx)
    (d_S cx) (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly' S' mdT k (d_sp1 cx - d_sp0 cx)
    (decode_sigma DS_reac_decode_plain_le)
    (Some (if CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then ns else -1))
    (if CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns then [(out, out + 3 * nch * ns)] else [])
    (fun m2 => CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
       LMem.bytes_at segs m2 out (CPlain.plain_out (d_body cx) nch ns)) HJ).
  - rewrite Hsp. lia.
  - unfold d_sp1. Z.div_mod_to_equations. lia.
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - rewrite R1. vm_compute. reflexivity.
  - exact Rgp.
  - exact Rtp.
  - intros a Ha. destruct (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns) eqn:Ep; [|inversion Ha].
    destruct (PK ltac:(first [exact Ep | reflexivity])) as (_ & _ & _ & _ & Holen).
    unfold LCK.in_wr in Ha. apply Exists_exists in Ha as (pr & Hin & Hpr). destruct Hin as [<- | []].
    cbn [fst snd] in Hpr. right. right. left. exists out, (dec_a_olen nch ns).
    split; [exact Iout|]. split; [exact Hno | lia].
  - intros Hpre. rewrite <- Ha1.
    assert (Hol : 1 <= dec_a_olen nch ns <= 3 * 127 * 127).
    { unfold dec_a_olen. destruct ((0 <? nch) && (0 <? ns)) eqn:Ep; [|lia].
      apply andb_true_iff in Ep as [Ep1 Ep2]. apply Z.ltb_lt in Ep1, Ep2. nia. }
    refine (LPL fx0 ly' S' W regsT memT mdT (d_body cx) res mode out nch ns (d_sp1 cx - ESTACK) Hpre
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); cbv zeta; rewrite ?Hsp', ?Ha1.
    + exact R10.
    + exact R12.
    + exact R13.
    + lia.
    + lia.
    + lia.
    + intros Hl. split; [lia|].
      apply (dec_leafb_bytes_garr8 W memT res (d_body cx) Hgres); lia.
    + lia.
    + lia.
    + apply LMem.bytes_at_app. split.
      * apply (dec_leafb_bytes_le W memT (mode + 4) 4 _ (nch mod 2 ^ 32) Hv4); [| lia | lia].
        change (8 * Z.of_nat 4) with 32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite dec_leafb_mod_pow2_mod by lia. rewrite Z.mod_mod by lia. reflexivity.
      * rewrite LMem.length_le4. replace (mode + 4 + Z.of_nat 4) with (mode + 8) by lia.
        apply (dec_leafb_bytes_le W memT (mode + 8) 4 _ (ns mod 2 ^ 32) Hv8); [| lia | lia].
        change (8 * Z.of_nat 4) with 32. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
        rewrite dec_leafb_mod_pow2_mod by lia. rewrite Z.mod_mod by lia. reflexivity.
    + apply (dec_leafb_stk_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); unfold ESTACK; lia.
    + unfold ESTACK, CPlain.REAC_DECODE_PLAIN_LE_D. lia.
    + intros Hl. left. rewrite Hsp'. unfold CPlain.REAC_DECODE_PLAIN_LE_D. lia.
    + left. rewrite Hsp'. unfold CPlain.REAC_DECODE_PLAIN_LE_D. lia.
    + intros Hp. destruct (PK Hp) as (Hl & Hn0 & Hs0 & H480 & Holen). rewrite <- Holen.
      split; [apply (dec_leafb_wr_at_block B LAWS ly' S' W memT mdT out (dec_a_olen nch ns));
                [exact HAR | exact Iout | lia | lia]|].
      split; [lia|]. split.
      * unfold zdisjoint in Dro. cbn [fst snd] in Dro. lia.
      * left. rewrite Hsp'. unfold CPlain.REAC_DECODE_PLAIN_LE_D. lia.
    + apply dec_leafb_app_stack. unfold CPlain.REAC_DECODE_PLAIN_LE_D. lia.
    + apply dec_leafb_app_stack. lia.
    + exact (dec_leafb_asan_cells B HCELLS ly' S' W memT mdT HAR).
    + left. rewrite Hsp'. unfold ACells.GOT_CELL_K, ACells.MIDEND, CPlain.REAC_DECODE_PLAIN_LE_D. lia.
    + intros Hl. apply (dec_leafb_addressable_block B LAWS ly' S' W memT mdT res (dec_a_len (d_n cx)));
        [exact HAR | exact Ires | lia | lia | lia].
    + intros Hw. apply (dec_leafb_addressable W memT); [exact Hmra | lia | lia | unfold ACells.APPMEM_END; lia | exact HMapp].
    + intros Hp. destruct (PK Hp) as (_ & _ & _ & _ & Holen). rewrite <- Holen.
      apply (dec_leafb_addressable_block B LAWS ly' S' W memT mdT out (dec_a_olen nch ns));
        [exact HAR | exact Iout | lia | lia | lia].
    + apply (dec_leafb_rng_journal B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ); unfold CPlain.REAC_DECODE_PLAIN_LE_D; lia.
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + intros Hl. apply (dec_leafb_rng_block B LAWS ly' S' W memT mdT res (dec_a_len (d_n cx)));
        [exact HAR | exact Ires | lia | lia].
    + intros Hl. apply (dec_leafb_rng_shadow_block B LAWS ly' S' W memT mdT res (dec_a_len (d_n cx)));
        [exact HAR | exact Ires | lia | lia | lia].
    + intros Hw. apply dec_leafb_rng; [lia | lia |]. intros a Ha.
      destruct (Z_lt_ge_dec a (mode + 8)) as [Hl | Hg].
      * pose proof (Hv4 (Z.to_nat (a - (mode + 4))) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
        replace (mode + 4 + (a - (mode + 4))) with a in Hb by lia. exact (dec_leafb_mbyte_vis W memT _ _ Hb).
      * pose proof (Hv8 (Z.to_nat (a - (mode + 8))) ltac:(lia)) as Hb. rewrite Z2Nat.id in Hb by lia.
        replace (mode + 8 + (a - (mode + 8))) with a in Hb by lia. exact (dec_leafb_mbyte_vis W memT _ _ Hb).
    + intros Hw. exact (dec_leafb_rng_shadow W memT (mode + 4) 8 Hmra ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros Hp. destruct (PK Hp) as (_ & _ & _ & _ & Holen). rewrite <- Holen.
      apply (dec_leafb_rng_block B LAWS ly' S' W memT mdT out (dec_a_olen nch ns)); [exact HAR | exact Iout | lia | lia].
    + intros Hp. destruct (PK Hp) as (_ & _ & _ & _ & Holen). rewrite <- Holen.
      apply (dec_leafb_rng_shadow_block B LAWS ly' S' W memT mdT out (dec_a_olen nch ns));
        [exact HAR | exact Iout | lia | lia | lia].
    + intros x Hx. destruct (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns) eqn:Ep; [|inversion Hx].
      destruct (PK ltac:(first [exact Ep | reflexivity])) as (_ & _ & _ & _ & Holen).
      unfold LCK.in_wr in Hx. apply Exists_exists in Hx as (pr & Hin & Hpr). destruct Hin as [<- | []].
      cbn [fst snd] in Hpr.
      exact (dec_leafb_wr_block B LAWS ly' S' W memT mdT out (dec_a_olen nch ns) HAR Iout x ltac:(lia)). }
cbv beta. intros W2 c2 Hwle (-> & regs2 & mem2 & md2 & -> & HJ2 & HP & HRES & HK & HG & HX).
rewrite R1.
assert (Hst2 : c1_st cx res out mode nch ns W regs2 mem2 md2 ly' S' k).
{ apply (c1_st_move cx res out mode nch ns W W regsT regs2 memT mem2 mdT md2 ly' S' ly' S' k k HCELLS Hst HJ2 Hk
    eq_refl (Permutation_refl _) Hle Hok HP).
  - intros a Ha. destruct (c1_K_out cx res out mode nch ns W regsT memT mdT ly' S' k HB Hst a Ha) as (Hr & Hlo & Hno').
    apply HK; [exact Hr | rewrite Hsp; unfold ESTACK; lia |].
    destruct (CPlain.plain_ok (dec_a_len (d_n cx)) (d_body cx) nch ns) eqn:Ep; [| intros Hw; inversion Hw].
    destruct (PK ltac:(first [exact Ep | reflexivity])) as (_ & _ & _ & _ & Holen).
    intros Hw. unfold LCK.in_wr in Hw. apply Exists_exists in Hw as (pr & Hin & Hpr). destruct Hin as [<- | []].
    cbn [fst snd] in Hpr. lia.
  - intros a Ha. apply HG. exact (c1_core_fpres _ _ _ _ _ _ _ _ HC a Ha). }
pose proof Hst2 as (HC2 & _ & HPm2 & _ & _ & _ & Hle2 & Hok2 & HR52 & HM2 & S322 & _).
destruct HR52 as (Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
pose proof HM2 as (HMO2 & Hfsh2 & Hgres2 & T40 & T48 & T56 & T64 & T72 & T80 & T88 & T112).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ2) as (HAR2 & _ & _ & _ & _).
apply SRr_ret. unfold llvm_a_st_5fc. exists fx0, ly', S', regs2, mem2, md2, res, out, mode, nch, ns.
split; [reflexivity|]. split; [exact Hfrm|].
split; [exact (c1_core_mono _ _ _ _ _ _ _ _ _ HC2 Hk5)|].
split; [exact HPm2|]. split; [lia|]. split; [lia|].
split; [exact Hle2|]. split; [exact Hok2|].
split; [exact Q19|]. split; [exact Q23|]. split; [exact Q21|]. split; [exact Q27|].
split; [exact (HRES _ eq_refl)|].
split; [exact Q18|]. split; [exact Q20|]. split; [exact Q22|]. split; [exact Q24|]. split; [exact Q25|].
split; [exact Q26|].
split; [exact HMO2|]. split; [exact Hfsh2|]. split; [exact Hgres2|].
split.
{ intros Hp. destruct (PK Hp) as (_ & _ & _ & _ & Holen). pose proof (HX Hp) as Hb.
  apply (c1_garr8_of_bytes W mem2 out _ Hb). intros j Hj.
  assert (Hlo : length (CPlain.plain_out (d_body cx) nch ns) = Z.to_nat (3 * nch * ns))
    by (unfold CPlain.plain_out; rewrite !length_map, length_seq; reflexivity).
  rewrite Hlo in Hj.
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR2 Iout) as (_ & _ & _ & _ & Hpres & _).
  exact (proj1 (proj1 (Hpres (out + Z.of_nat j) ltac:(lia)))). }
split.
{ intros Hp i Hi. rewrite <- (Hfill i Hi). apply HK; [lia | rewrite Hsp; unfold ESTACK; lia |].
  rewrite Hp. intros Hw. inversion Hw. }
split; [exact S322|].
exact (conj T40 (conj T48 (conj T56 (conj T64 (conj T72 (conj T80 (conj T88 T112))))))).
Qed.

Section F2. Context {fx : YK11.FPState}.
Hypothesis LAWS : AR_laws segs B.
Let RUN := @paj_run fx rc dec_A_sink_head decode_listing PL_decode PI_decode B LAWS.
Let RUNTO := @paj_run_to fx rc dec_A_sink_head decode_listing PL_decode PI_decode B LAWS.
Let BR := @paj_branch fx rc decode_listing PI_decode.

(* The spill slot 32(s1) as a state's spill region says after +0x58c's `sd s7,32(s1)` (chunk 32 = s7's atom). *)
Lemma c1_slot32s : forall (W : world segs) Ex ss ms rg v,
  st_ok decodesegs0 Ex ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) 0 = Some rg ->
  YP09.r_base rg = Some 9%nat -> In (YP09.mkChunk 32 (CVal 8 (SOff 23 0))) (YP09.r_chunks rg) ->
  sv_denot Ex (SOff 23 0) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) (ms_mem ms)) (bv_unsigned (ew Ex 9) + 32) = Some v.
Proof.
intros W Ex ss ms rg v HS Hi Hb Hc He Hv.
pose proof (st_ok_mem_ok decodesegs0 Ex ss _ HS) as (_ & Hrs & _). cbn [ms_mem restrict] in Hrs.
pose proof (proj1 (Forall_forall _ _) Hrs rg (nth_error_In _ _ Hi)) as (_ & _ & _ & Hcs).
pose proof (val_of_chunk_ok decodesegs0 Ex _ _ 32 8 (SOff 23 0) v (proj1 (Forall_forall _ _) Hcs _ Hc) He Hv
  ltac:(lia)) as Hval.
rewrite Hb in Hval. cbn [base_val] in Hval. exact (c1_rdword_of_val_mem _ _ _ _ Hval Hv).
Qed.

(* Stage B, +0x58c .. : slot 32(s1) := ns, s7 := the frame; then
   - `blez a0` (+0x594) taken (the decode refused or ns <= 0): through +0x5bc / +0x5c0 to +0x5d8 (c1_T2_stmt);
   - else `blt a1,s10` (+0x59c, 12 < ns) taken: +0x5bc to +0x5c4 (c1_T3_stmt);
   - else check_round_trip #1 at +0x5b4 (c1_Bcrt). *)
Lemma c1_B : c1_T2_stmt -> c1_T3_stmt -> ameter_laws MT -> dec_crt_cells B ->
  dec_ro_rd_unowned B -> dec_rom_no_errno B ->
  (forall fx' : YK11.FPState,
     @dec_check_round_trip_cg fx' rc B MT (decode_sigma DS_check_round_trip) (CTX_check_round_trip RA_LLVMF)) ->
  forall cx res out mode nch ns (W : world segs) regs mem md ly' S',
  dec_base cx -> dec_a_rom cx -> frm_zero (@fp_csr fx) ->
  c1_st58 cx res out mode nch ns W regs mem md ly' S' ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x58c)) mem (YK11.seg_rom segs)) md) (llvm_a_st_5fc B MT cx).
Proof.
intros T2 T3 ML HCELLS HOWN HERR CRT cx res out mode nch ns W regs mem md ly' S' HB HR Hfrm H58.
assert (HRO : c1_ro cx) by exact (conj HR (conj HOWN HERR)).
pose proof H58 as (HC & Hbl & _ & _ & Hle & Hok & Hfr & H10 & H18 & H20 & H22 & H23 & H24 & H25 & H26 & HM & (v32 & S32)
  & Hgout).
pose proof HM as (HMO & _ & _ & S40 & S48 & S56 & S64 & S72 & S80 & S88 & _).
pose proof HMO as (_ & Hnch & Hns & _ & _).
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (R8 & R9 & Hsp & Hs01 & Hs01' & Hal & _ & _ & _ & _ & _).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & Hstk & Hpres & _ & _).
destruct (c1_stk_facts _ _ _ Hstk) as (Ha16 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
assert (Hsp1 : 2 ^ 46 <= d_sp1 cx <= 2 ^ 47) by lia.
assert (HP32 : forall o, 32 <= o < 40 -> apresent (w_H W) mem (d_sp1 cx + o)) by (intros o Ho; apply Hpres; lia).
destruct Hfr as (F19 & F21 & F27).
unfold dec_a_slot in S32, S40, S48, S56, S64, S72, S80, S88.
change SHADOW_OFF with SB in S40.
set (len := dec_a_len (d_n cx)) in *. set (body := d_body cx) in *. set (olen := dec_a_olen nch ns) in *.
pose proof (c1_entry 0x58c 32 40 W regs mem (d_sp1 cx) v32 (nch mod 2 ^ 64) len mode out (nch mod 2 ^ 32)
  (ns mod 2 ^ 64) eq_refl (or_intror eq_refl) R9 Hsp1 Hal S32 S40 S48 S56 S64 S72 S80 S88 HP32) as HS.
set (X := c1_extra v32 (nch mod 2 ^ 64) len mode out (nch mod 2 ^ 32) (ns mod 2 ^ 64)) in HS.
set (E := Eimg (Ereg regs X)) in HS.
assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env).
assert (SHOK : sh_ok pa_segs (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor.
assert (EL : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; subst E; rewrite Eimg_low by (pose proof (u5_range r); unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (HAE : env_agree 32 (Ereg regs X) E) by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx) by (rewrite (EL 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (E34 : ew E 34 = Z_to_bv 64 (nch mod 2 ^ 64)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E37 : ew E 37 = Z_to_bv 64 out) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (Ha0 : -128 <= (if CDec.decode_ok len body nch ns then ns else -1) <= 127)
  by (destruct (CDec.decode_ok len body nch ns); lia).
assert (U10 : U E (SOff 10 0) = (if CDec.decode_ok len body nch ns then ns else -1) mod 2 ^ 64).
{ apply U_atom; [|apply Z.mod_pos_bound; lia]. rewrite (EL 10%nat 10%bv eq_refl), H10. symmetry. apply c1_lit_mod. }
assert (U26 : U E (SOff 26 0) = ns mod 2 ^ 64)
  by (apply U_atom; [rewrite (EL 26%nat 26%bv eq_refl), H26; reflexivity | apply Z.mod_pos_bound; lia]).
(* registers and slots in any environment of the walk from here: below the fresh atoms it agrees with E *)
assert (SV : forall Ez (n : nat) (r : bv 5), (forall m, (m < 512)%nat -> ew Ez m = ew E m) ->
  Z.of_nat n = bv_unsigned r -> sv_denot Ez (SOff n 0) = YK11.getr regs r)
  by (intros Ez n r AGz Hn; exact (c1_soff_reg Ez regs X n r AGz Hn)).
assert (Hns32 : 0 <= ns mod 2 ^ 32 < 2 ^ 64) by (pose proof (Z.mod_pos_bound ns (2 ^ 32) ltac:(lia)); lia).
change (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x58c)) mem (YK11.seg_rom segs)) with
  (YK11.mkst regs (Z_to_bv 64 (pa_val (L := decode_listing) A_TEXT + 0x58c)) mem (YK11.seg_rom pa_segs)).
(* +0x58c .. +0x594: slot 32 := s7 (ns), s7 := s3 (the frame); stop at `blez a0` *)
paj_run_tok RUN HS HJ SHOK Bspan; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG : forall m, (m < 512)%nat -> ew Ex m = ew E m) by (intros m Hm; repeat rewrite ew_ewset_other by lia; reflexivity) end.
(* a run of this state (spill region writable at [32, 40) only) keeps every other byte *)
assert (WK : forall (Ex : env) rs m0 m1, bv_unsigned (ew Ex 9) = d_sp1 cx ->
  rs = ss_mem (c1_ss 0x58c 32 40) \/ (exists rg, rs = [rg] /\ YP09.r_base rg = Some 9%nat /\ YP09.r_wlo rg = 32 /\
     YP09.r_whi rg = 40) ->
  frame_of Ex rs m0 m1 -> forall x : word, ~ (d_sp1 cx + 32 <= bv_unsigned x < d_sp1 cx + 40) -> m1 x = m0 x).
{ intros Ex rs m0 m1 E9x Hrs HFx x Hx. apply HFx. intros (r & Hin & Ha).
  destruct Hrs as [-> | (rg & -> & Hb & Hl & Hh)].
  - cbn [In ss_mem c1_ss c1_spill] in Hin. destruct Hin as [Hin | []]. subst r.
    cbn [YP09.r_wlo YP09.r_whi YP09.r_base c1_spill base_val] in Ha. rewrite E9x in Ha. exact (Hx Ha).
  - destruct Hin as [Hin | []]. subst r. rewrite Hb, Hl, Hh in Ha. cbn [base_val] in Ha. rewrite E9x in Ha.
    exact (Hx Ha). }
assert (HM1 : forall x : word, ~ (d_sp1 cx + 32 <= bv_unsigned x < d_sp1 cx + 40) -> ms_mem ms x = mem x)
  by exact (WK E _ _ _ E9 (or_introl eq_refl) HF).
assert (GR1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
(* the bytes of the whole walk outside slot 32(s1), at any later memory that agrees with mem there *)
assert (KV : forall (m2 : word -> option byte),
  (forall x : word, ~ (d_sp1 cx + 32 <= bv_unsigned x < d_sp1 cx + 40) -> m2 x = mem x) ->
  forall a, 0 <= a < 2 ^ 64 /\ ~ (d_sp1 cx + 32 <= a < d_sp1 cx + 40) ->
  aview segs (w_H W) m2 a = aview segs (w_H W) mem a).
{ intros m2 Hm2 a Ha. apply aview_eq_of. unfold mrestrict. rewrite Hm2; [reflexivity|].
  rewrite unsigned_lit_small by lia. tauto. }
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* `blez a0` taken: the decode refused (a0 = -1) or ns <= 0; over +0x5bc / +0x5c0 to +0x5d8 *)
  clear Hc.
  lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
    let r1 := eval vm_compute in (ss_mem ss1) in
    assert (Hrs1 : ss_mem ss1 = r1) by (vm_compute; reflexivity) end.
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5d8; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
  assert (HM2 : forall x : word, ~ (d_sp1 cx + 32 <= bv_unsigned x < d_sp1 cx + 40) -> ms_mem ms0 x = mem x).
  { intros x Hx. rewrite <- (HM1 x Hx).
    refine (WK _ _ _ _ _ _ HF x Hx); [first [exact E9 | rewrite AG by lia; exact E9] |].
    right. eexists. split; [reflexivity|]. vm_compute. auto. }
  assert (GR2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR1 a Ha))).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss _ =>
    assert (AG2 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
      by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG; exact Hm]);
    let rr := eval vm_compute in (nth_error (ss_mem (abs_ss pa_val ss)) 0) in
    lazymatch rr with Some ?rg =>
      pose proof (c1_slot32s W Ex (abs_ss pa_val ss) ms0 rg (ns mod 2 ^ 32) HS ltac:(vm_compute; reflexivity)
        eq_refl ltac:(cbn; tauto) ltac:(rewrite (SV Ex 23%nat 23%bv AG2 eq_refl), H23; reflexivity) Hns32) as S32'
    end end.
  try rewrite (AG2 9%nat ltac:(lia)) in S32'. rewrite E9 in S32'.
  pmkst HS.
  c1_reg HS (19%bv : bv 5) R19. c1_reg HS (23%bv : bv 5) R23.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs X [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv HS
      ltac:(split; [intros n Hn; try rewrite AG2 by lia; apply HAE; exact Hn | reflexivity]) ltac:(vm_compute; reflexivity))
    as KA.
  cbn [ms_regs restrict YK11.mkst] in KA.
  eapply T2; [exact HB | exact HR | exact Hfrm |].
  apply (c1_st_of58 cx res out mode nch ns W regs mem md ly' S' _ _ _ LAWS ML HB HCELLS HRO H58 HJ KA).
  + rewrite R19. exact (eq_trans (c1_denot_soff _ E 37 out AG2 ltac:(lia) E37) eq_refl).
  + rewrite R23, (SV _ 19%nat 19%bv AG2 eq_refl). exact F19.
  + exact (KV _ HM2).
  + exact GR2.
  + exact S32'.
- (* a0 > 0: the decode accepted the frame, and a0 = ns *)
  rewrite !denot_lit_U, U_SLit in Hc. try rewrite (c1_U_agree _ E 10 AG ltac:(lia)) in Hc.
  rewrite U10 in Hc. change (zcanon 0) with 0 in Hc. rewrite c1_lit_mod in Hc.
  rewrite c1_br_ge in Hc by lia. apply negb_false_iff, Z.ltb_lt in Hc.
  assert (Hdec : CDec.decode_ok len body nch ns = true)
    by (destruct (CDec.decode_ok len body nch ns); [reflexivity | lia]).
  rewrite Hdec in Hc. pose proof (Hgout Hdec) as Hgo.
  destruct (c1_geo_58 cx res out nch ns ly' S' W regs mem md dec_ev_4fc LAWS HB HC Hbl) as (Hgeo & _ & _).
  pose proof Hgeo as (_ & _ & _ & _ & _ & Ho4 & Hoc & _ & _ & _ & _ & _). fold olen in Hoc.
  assert (Hoq : olen <= req_size olen) by (unfold req_size; destruct (Z.eqb_spec olen 0); lia).
  assert (Hbo : length (CDec.braid_out body nch ns) = Z.to_nat (3 * nch * ns))
    by (unfold CDec.braid_out; apply RDL.length_mapseq).
  assert (Holen : olen = 3 * nch * ns).
  { pose proof Hdec as Hd. unfold CDec.decode_ok in Hd. rewrite !andb_true_iff in Hd.
    destruct Hd as ((((_ & Hn0) & _) & Hs0) & _). apply Z.ltb_lt in Hn0, Hs0.
    unfold olen, dec_a_olen. rewrite (proj2 (Z.ltb_lt 0 nch) Hn0), (proj2 (Z.ltb_lt 0 ns) Hs0). reflexivity. }
  (* the decoder's output at any later memory that keeps the bytes outside slot 32(s1) *)
  assert (GO : forall m2 : word -> option byte,
    (forall x : word, ~ (d_sp1 cx + 32 <= bv_unsigned x < d_sp1 cx + 40) -> m2 x = mem x) ->
    garr8 segs (mrestrict (w_H W) m2) out (map (fun b : byte => bv_unsigned b) (CDec.braid_out body nch ns))).
  { intros m2 Hm2. refine (c1_garr8_x _ _ _ _ _ _ _ Hgo). intros kk Hkk. rewrite length_map, Hbo in Hkk.
    apply (KV _ Hm2). lia. }
  (* +0x598 .. +0x59c: a1 := 12; stop at `blt a1,s10` *)
  lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
    let r1 := eval vm_compute in (ss_mem ss1) in
    assert (Hrs1 : ss_mem ss1 = r1) by (vm_compute; reflexivity) end.
  paj_run_tok RUN HS HJ SHOK Bspan; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
  assert (HM2 : forall x : word, ~ (d_sp1 cx + 32 <= bv_unsigned x < d_sp1 cx + 40) -> ms_mem ms0 x = mem x).
  { intros x Hx. rewrite <- (HM1 x Hx).
    refine (WK _ _ _ _ _ _ HF x Hx); [first [exact E9 | rewrite AG by lia; exact E9] |].
    right. eexists. split; [reflexivity|]. vm_compute. auto. }
  assert (GR2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR1 a Ha))).
  clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG2 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
      by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG; exact Hm]) end.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* 12 < ns: check_round_trip #1 skipped; over +0x5bc / +0x5c0 to +0x5c4 *)
    clear Hc0.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x5c4; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
    assert (HM3 : forall x : word, ~ (d_sp1 cx + 32 <= bv_unsigned x < d_sp1 cx + 40) -> ms_mem ms1 x = mem x).
    { intros x Hx. rewrite <- (HM2 x Hx).
      refine (WK _ _ _ _ _ _ HF x Hx); [first [exact E9 | rewrite AG2 by lia; exact E9] |].
      right. eexists. split; [reflexivity|]. vm_compute. auto. }
    assert (GR3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR2 a Ha))).
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ss _ =>
      assert (AG3 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
        by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG2; exact Hm]);
      let rr := eval vm_compute in (nth_error (ss_mem (abs_ss pa_val ss)) 0) in
      lazymatch rr with Some ?rg =>
        pose proof (c1_slot32s W Ex (abs_ss pa_val ss) ms1 rg (ns mod 2 ^ 32) HS ltac:(vm_compute; reflexivity)
          eq_refl ltac:(cbn; tauto) ltac:(rewrite (SV Ex 23%nat 23%bv AG3 eq_refl), H23; reflexivity) Hns32) as S32'
      end end.
    try rewrite (AG3 9%nat ltac:(lia)) in S32'. rewrite E9 in S32'.
    pmkst HS.
    c1_reg HS (19%bv : bv 5) R19. c1_reg HS (23%bv : bv 5) R23.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs X [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv HS
        ltac:(split; [intros n Hn; try rewrite AG3 by lia; apply HAE; exact Hn | reflexivity]) ltac:(vm_compute; reflexivity))
      as KA.
    cbn [ms_regs restrict YK11.mkst] in KA.
    eapply T3; [right; reflexivity | exact HB | exact HR | exact Hfrm | | exact Hdec | exact (GO _ HM3)].
    apply (c1_st_of58 cx res out mode nch ns W regs mem md ly' S' _ _ _ LAWS ML HB HCELLS HRO H58 HJ KA).
    * rewrite R19. exact (c1_denot_soff _ E 37 out AG3 ltac:(lia) E37).
    * rewrite R23, (SV _ 19%nat 19%bv AG3 eq_refl). exact F19.
    * exact (KV _ HM3).
    * exact GR3.
    * exact S32'.
  + (* ns <= 12: check_round_trip #1 at +0x5b4 *)
    rewrite !denot_lit_U, U_SLit in Hc0. try rewrite (c1_U_agree _ E 26 AG2 ltac:(lia)) in Hc0.
    rewrite U26 in Hc0. rewrite c1_lit_mod in Hc0. change (zcanon 12) with 12 in Hc0.
    rewrite c1_br_lt in Hc0 by lia. apply Z.ltb_ge in Hc0.
    lazymatch type of HS with st_ok_pi _ _ _ ?ss1 _ =>
      let r1 := eval vm_compute in (ss_mem ss1) in
      assert (Hrs2 : ss_mem ss1 = r1) by (vm_compute; reflexivity) end.
    paj_run_tok RUN HS HJ SHOK Bspan; [c1_awr E (d_sp0 cx) (d_sp1 cx) |].
    assert (HM3 : forall x : word, ~ (d_sp1 cx + 32 <= bv_unsigned x < d_sp1 cx + 40) -> ms_mem ms1 x = mem x).
    { intros x Hx. rewrite <- (HM2 x Hx).
      refine (WK _ _ _ _ _ _ HF x Hx); [first [exact E9 | rewrite AG2 by lia; exact E9] |].
      right. eexists. split; [reflexivity|]. vm_compute. auto. }
    assert (GR3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms1) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG (GR2 a Ha))).
    clear HF HFr HG.
    lazymatch type of HS with st_ok _ ?Ex ?ss _ =>
      assert (AG3 : forall m, (m < 512)%nat -> ew Ex m = ew E m)
        by (intros m Hm; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG2; exact Hm]);
      let rr := eval vm_compute in (nth_error (ss_mem ss) 0) in
      lazymatch rr with Some ?rg =>
        pose proof (c1_slot32s W Ex ss ms1 rg (ns mod 2 ^ 32) HS ltac:(vm_compute; reflexivity)
          eq_refl ltac:(cbn; tauto) ltac:(rewrite (SV Ex 23%nat 23%bv AG3 eq_refl), H23; reflexivity) Hns32) as S32'
      end;
      pose proof (regs_kept_of_st_ok segs _ _ _ regs X [2; 3; 4; 8; 9; 18; 20; 21; 22; 24; 25; 26; 27]%bv HS
        ltac:(split; [intros n Hn; try rewrite AG3 by lia; apply HAE; exact Hn | reflexivity])
        ltac:(vm_compute; reflexivity)) as KA end.
    try rewrite (AG3 9%nat ltac:(lia)) in S32'. rewrite E9 in S32'.
    cbn [ms_regs restrict YK11.mkst] in KA.
    c1_reg2 HS (1%bv : bv 5) R1. c1_reg2 HS (10%bv : bv 5) R10. c1_reg2 HS (11%bv : bv 5) R11.
    c1_reg2 HS (12%bv : bv 5) R12. c1_reg2 HS (13%bv : bv 5) R13. c1_reg2 HS (19%bv : bv 5) R19.
    c1_reg2 HS (23%bv : bv 5) R23.
    lazymatch goal with H : img_env _ _ ?Ex |- _ => lazymatch type of HS with st_ok _ Ex _ _ =>
      cbn [sv_denot] in R1; rewrite (img_env_codeptr Ex H) in R1 end end.
    destruct (c1_geo_58 cx res out nch ns ly' S' W regs mem md dec_ev_4fc LAWS HB HC Hbl) as (Hgeo' & _ & _).
    pose proof Hgeo' as (_ & _ & Hr4 & Hrc & _).
    pose proof (c1_body_len cx HB) as Hbl'.
    assert (Hrq : dec_a_len (d_n cx) <= req_size (dec_a_len (d_n cx)))
      by (unfold req_size; destruct (Z.eqb_spec (dec_a_len (d_n cx)) 0); lia).
    fold len in Hrc, Hrq.
    pmkst HS.
    assert (Hst : c1_st cx res out mode nch ns W (ms_regs ms1) (ms_mem ms1) (with_vm_backing (m_vm_lazy md) mat1 md)
      ly' S' dec_ev_4fc).
    { apply (c1_st_of58 cx res out mode nch ns W regs mem md ly' S' _ _ _ LAWS ML HB HCELLS HRO H58 HJ KA).
      - rewrite R19. exact (c1_denot_soff _ E 37 out AG3 ltac:(lia) E37).
      - rewrite R23, (SV _ 19%nat 19%bv AG3 eq_refl). exact F19.
      - exact (KV _ HM3).
      - exact GR3.
      - exact S32'. }
    apply (c1_Bcrt fx LAWS ML HCELLS HOWN HERR CRT T3 cx res out mode nch ns W (ms_regs ms1) (ms_mem ms1) _ ly' S'
      HB HR Hfrm Hst Hle Hok).
    * rewrite R1. vm_compute. reflexivity.
    * rewrite R10. apply (c1_soff_val _ E 20 50 res AG3 ltac:(lia) (eq_trans (EL 20%nat 20%bv eq_refl) H20)); lia.
    * rewrite R11. exact (c1_denot_soff _ E 37 out AG3 ltac:(lia) E37).
    * rewrite R12, (c1_denot_soff _ E 34 _ AG3 ltac:(lia) E34). apply c1_lit_mod.
    * rewrite R13, (SV _ 26%nat 26%bv AG3 eq_refl), H26. apply c1_lit_mod.
    * exact Hdec.
    * exact Hc0.
    * exact (GO _ HM3).
Qed.
End F2.

(* The run state at pc from c1_st: the spill area read-only. *)
Lemma c1_st_ss : forall (fx : YK11.FPState) cx res out mode nch ns (W : world segs) regs mem md ly' S' k pc,
  c1_st cx res out mode nch ns W regs mem md ly' S' k ->
  st_ok_pi (pa_segs (L := decode_listing)) pa_val
    (Eimg (Ereg regs (c1_extra (ns mod 2 ^ 32) (nch mod 2 ^ 64) (dec_a_len (d_n cx)) mode out (nch mod 2 ^ 32)
      (ns mod 2 ^ 64))))
    (c1_ss pc 32 32)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (pa_val A_TEXT + pc)) mem (YK11.seg_rom pa_segs))).
Proof.
intros fx cx res out mode nch ns W regs mem md ly' S' k pc (HC & _ & _ & _ & _ & _ & _ & _ & _ & HM & S32 & _).
pose proof HM as (_ & _ & _ & S40 & S48 & S56 & S64 & S72 & S80 & S88 & _).
pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ.
destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (R8 & R9 & Hsp & Hs01 & Hs01' & Hal & _ & _ & _ & _ & _).
destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (HAR & Hstk & Hpres & _ & _).
destruct (c1_stk_facts _ _ _ Hstk) as (Ha16 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof alloc_ceiling_val as Hce. unfold DEC_LLVMF_STK in *.
unfold dec_a_slot in *. change SHADOW_OFF with SB in S40.
apply (@c1_entry fx pc 32 32 W regs mem (d_sp1 cx) _ _ _ _ _ _ _ eq_refl (or_introl eq_refl) R9 ltac:(lia) Hal
  S32 S40 S48 S56 S64 S72 S80 S88).
intros o Ho. apply Hpres. lia.
Qed.

(* c1_st after a run that wrote no memory and kept the callee-saved registers. *)
Lemma c1_st_run : forall cx res out mode nch ns (W : world segs) regs regs2 mem mem2 md md2 ly' S' k,
  dec_crt_cells B -> c1_st cx res out mode nch ns W regs mem md ly' S' k ->
  @ajournal rc dec_A_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W mem2 md2 k ->
  (forall x, mem2 x = mem x) ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> YK11.getr regs2 r = YK11.getr regs r) ->
  c1_st cx res out mode nch ns W regs2 mem2 md2 ly' S' k.
Proof.
intros cx res out mode nch ns W regs regs2 mem mem2 md md2 ly' S' k HCELLS Hst HJ2 HM HR.
pose proof Hst as (HC & Hk & _ & _ & _ & _ & Hle & Hok & _).
apply (c1_st_move cx res out mode nch ns W W regs regs2 mem mem2 md md2 ly' S' ly' S' k k HCELLS Hst HJ2 Hk eq_refl
  (Permutation_refl _) Hle Hok (c1_aregs_of regs regs2 HR)).
- intros a _. apply aview_eq_of. unfold mrestrict. rewrite HM. reflexivity.
- intros a Ha. destruct (c1_core_fpres _ _ _ _ _ _ _ _ HC a Ha) as (Hv & b & Hb). split; [exact Hv|].
  exists b. rewrite HM. exact Hb.
Qed.

Section F3. Context {fx : YK11.FPState}.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HCELLS : dec_crt_cells B.
Let RUN := @paj_run fx rc dec_A_sink_head decode_listing PL_decode PI_decode B LAWS.

(* The preamble of a run from c1_st at pc, up to the call it ends with. *)
Ltac c1_pre Hst pc :=
  lazymatch type of Hst with c1_st ?cx ?res ?out ?mode ?nch ?ns ?W ?regs ?mem ?md ?ly' ?S' ?k =>
  let HS := fresh "HS" in
  pose proof (c1_st_ss fx cx res out mode nch ns W regs mem md ly' S' k pc Hst) as HS;
  let HC := fresh "HC" in pose proof Hst as (HC & _);
  let HJ := fresh "HJ" in pose proof (c1_core_J _ _ _ _ _ _ _ _ HC) as HJ;
  let R9 := fresh "R9" in let Hsp := fresh "Hsp" in let Hs01 := fresh "Hs01" in let Hs01' := fresh "Hs01'" in
  destruct (c1_core_facts _ _ _ _ _ _ _ _ HC) as (_ & R9 & Hsp & Hs01 & Hs01' & _ & _ & _ & _ & _ & _);
  let Hstk := fresh "Hstk" in
  destruct (c1_J_facts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as (_ & Hstk & _ & _ & _);
  let Hceil := fresh "Hceil" in let Hslo := fresh "Hslo" in let Hshi := fresh "Hshi" in let H47 := fresh "H47" in
  destruct (c1_stk_facts _ _ _ Hstk) as (_ & Hceil & Hslo & Hshi & H47 & _ & _ & _);
  let Hce := fresh "Hce" in pose proof alloc_ceiling_val as Hce; unfold DEC_LLVMF_STK in *;
  set (X := c1_extra (ns mod 2 ^ 32) (nch mod 2 ^ 64) (dec_a_len (d_n cx)) mode out (nch mod 2 ^ 32) (ns mod 2 ^ 64))
    in HS;
  set (E := Eimg (Ereg regs X)) in HS;
  assert (HEI : img_env pa_val A_LIM E) by (subst E; apply Eimg_env);
  assert (SHOK : sh_ok pa_segs (SOff 32 0) [] E (mrestrict (w_H W) mem)) by constructor;
  assert (HAE : env_agree 32 (Ereg regs X) E)
    by (split; [intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]);
  assert (E9 : bv_unsigned (ew E 9) = d_sp1 cx)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl), R9;
        apply unsigned_lit_small; lia);
  change (YK11.mkst regs (w64 (DEC_A_LLVMF + pc)) mem (YK11.seg_rom segs)) with
    (YK11.mkst regs (Z_to_bv 64 (pa_val (L := decode_listing) A_TEXT + pc)) mem (YK11.seg_rom pa_segs));
  paj_run_tok RUN HS HJ SHOK Bspan; [c1_awr E (d_sp0 cx) (d_sp1 cx) |]
  end.

(* After c1_pre: the memory, the agreement below the fresh atoms, the kept registers, the call registers. *)
Ltac c1_post ms mem E X regs HS HAE HF HFr HG HM1 AG KA Ra Ra0 Ra1 Ra2 Ra3 :=
  assert (HM1 : forall x, ms_mem ms x = mem x) by c1_nowin HF;
  clear HF HFr HG;
  lazymatch type of HS with st_ok _ ?Ex _ _ =>
    assert (AG : forall m, (m < 512)%nat -> ew Ex m = ew E m)
      by (intros m Hm; repeat rewrite ew_ewset_other by lia; reflexivity);
    pose proof (regs_kept_of_st_ok segs _ _ _ regs X [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv HS
      ltac:(split; [intros n Hn; try rewrite AG by lia; apply HAE; exact Hn | reflexivity])
      ltac:(vm_compute; reflexivity)) as KA end;
  cbn [ms_regs restrict YK11.mkst] in KA;
  c1_reg2 HS (1%bv : bv 5) Ra; c1_reg2 HS (10%bv : bv 5) Ra0; c1_reg2 HS (11%bv : bv 5) Ra1;
  c1_reg2 HS (12%bv : bv 5) Ra2; c1_reg2 HS (13%bv : bv 5) Ra3;
  lazymatch goal with H : img_env _ _ ?Ex |- _ => lazymatch type of HS with st_ok _ Ex _ _ =>
    cbn [sv_denot] in Ra; rewrite (img_env_codeptr Ex H) in Ra end end;
  pmkst HS.

(* +0x5e8 .. +0x5f8: a0 = s4 (res), a1 = s6 (len), a2 = 64(s1) (mode), a3 = s3 (out); reac_decode_plain_le. *)
Lemma c1_T2b_at :
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx') ->
  forall cx res out mode nch ns (W : world segs) regs mem md ly' S' k,
  dec_base cx -> frm_zero (@fp_csr fx) ->
  c1_st cx res out mode nch ns W regs mem md ly' S' k -> dec_a_filled W mem out (dec_a_olen nch ns) ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x5e8)) mem (YK11.seg_rom segs)) md) (llvm_a_st_5fc B MT cx).
Proof.
intros LPL cx res out mode nch ns W regs mem md ly' S' k HB Hfrm Hst Hfill.
pose proof Hst as (_ & Hk & _ & _ & _ & _ & _ & _ & HR5 & _).
destruct HR5 as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
c1_pre Hst 0x5e8.
assert (E36 : ew E 36 = Z_to_bv 64 mode) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
c1_post ms mem E X regs HS HAE HF HFr HG HM1 AG KA Ra Ra0 Ra1 Ra2 Ra3.
apply (c1_plain_call fx LAWS HCELLS LPL cx res out mode nch ns W (ms_regs ms) (ms_mem ms) _ ly' S' k HB Hfrm Hk).
- exact (c1_st_run cx res out mode nch ns W regs (ms_regs ms) mem (ms_mem ms) md _ ly' S' k HCELLS Hst HJ HM1 KA).
- intros i Hi. rewrite <- (Hfill i Hi). apply aview_eq_of. unfold mrestrict. rewrite HM1. reflexivity.
- rewrite Ra. vm_compute. reflexivity.
- rewrite Ra0, (c1_soff_reg _ regs X 20 20%bv AG eq_refl). exact R20.
- rewrite Ra1, (c1_soff_reg _ regs X 22 22%bv AG eq_refl). exact R22.
- rewrite Ra2. exact (c1_denot_soff _ E 36 mode AG ltac:(lia) E36).
- rewrite Ra3, (c1_soff_reg _ regs X 19 19%bv AG eq_refl). exact R19.
Qed.

(* +0x5d8 .. +0x5e4: a1 = 0xa5, a0 = s3 (out), a2 = s9 (olen); __asan_memset, then c1_T2b_at. *)
Lemma c1_T2_at :
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (decode_sigma DS___asan_memset)) ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx') ->
  forall cx res out mode nch ns (W : world segs) regs mem md ly' S' k,
  dec_base cx -> frm_zero (@fp_csr fx) ->
  c1_st cx res out mode nch ns W regs mem md ly' S' k ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (DEC_A_LLVMF + 0x5d8)) mem (YK11.seg_rom segs)) md) (llvm_a_st_5fc B MT cx).
Proof.
intros AMS LPL cx res out mode nch ns W regs mem md ly' S' k HB Hfrm Hst.
pose proof Hst as (_ & Hk & _ & _ & _ & _ & _ & _ & HR5 & _).
destruct HR5 as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
c1_pre Hst 0x5d8.
c1_post ms mem E X regs HS HAE HF HFr HG HM1 AG KA Ra Ra0 Ra1 Ra2 Ra3.
apply (c1_memset_call fx LAWS HCELLS AMS cx res out mode nch ns W (ms_regs ms) (ms_mem ms) _ ly' S' k _ HB).
- exact (c1_st_run cx res out mode nch ns W regs (ms_regs ms) mem (ms_mem ms) md _ ly' S' k HCELLS Hst HJ HM1 KA).
- rewrite Ra. vm_compute. reflexivity.
- rewrite Ra0, (c1_soff_reg _ regs X 19 19%bv AG eq_refl). exact R19.
- rewrite Ra1. first [reflexivity | (rewrite denot_lit_U, U_SLit; reflexivity)].
- rewrite Ra2, (c1_soff_reg _ regs X 25 25%bv AG eq_refl). exact R25.
- intros regs2 mem2 md2 Hst2 Hfill2. exact (c1_T2b_at LPL cx res out mode nch ns W regs2 mem2 md2 ly' S' k HB Hfrm Hst2 Hfill2).
Qed.

(* +0x5b8 (the `j` over +0x5bc / +0x5c0) or +0x5c4 .. +0x5d4: a0 = s4 + 50, a1 = s3 (out), a2 = 48(s1) (nch),
   a3 = s10 (ns); check_braid #1, then c1_T2. *)
Lemma c1_T3_at :
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx') ->
  c1_T2_stmt ->
  forall pc cx res out mode nch ns (W : world segs) regs mem md ly' S' k,
  (pc = 0x5b8 \/ pc = 0x5c4) -> dec_base cx -> dec_a_rom cx -> frm_zero (@fp_csr fx) ->
  c1_st cx res out mode nch ns W regs mem md ly' S' k ->
  CDec.decode_ok (dec_a_len (d_n cx)) (d_body cx) nch ns = true ->
  garr8 segs (mrestrict (w_H W) mem) out (map (fun b : byte => bv_unsigned b) (CDec.braid_out (d_body cx) nch ns)) ->
  SRr segs W (mkCfg (YK11.mkst regs (w64 (DEC_A_LLVMF + pc)) mem (YK11.seg_rom segs)) md) (llvm_a_st_5fc B MT cx).
Proof.
intros LCB T2 pc cx res out mode nch ns W regs mem md ly' S' k Hpc HB HR Hfrm Hst Hdec Hgout.
pose proof Hst as (_ & Hk & _ & _ & _ & _ & _ & _ & HR5 & HM & _).
destruct HR5 as (R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & R27).
pose proof HM as (HMO & _). pose proof HMO as (_ & Hnch & Hns & _ & _).
pose proof Hst as (_ & _ & _ & _ & _ & Hgeo & _). pose proof Hgeo as (_ & _ & Hr4 & Hrc & _).
pose proof (c1_body_len cx HB) as Hbl.
assert (Hrq : 0 <= req_size (dec_a_len (d_n cx)))
  by (unfold req_size; destruct (Z.eqb_spec (dec_a_len (d_n cx)) 0); lia).
pose proof alloc_ceiling_val as Hce0.
destruct Hpc as [-> | ->]; [c1_pre Hst 0x5b8 | c1_pre Hst 0x5c4];
(assert (E34 : ew E 34 = Z_to_bv 64 (nch mod 2 ^ 64))
   by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)));
(assert (E20 : ew E 20 = Z_to_bv 64 res)
   by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact R20));
c1_post ms mem E X regs HS HAE HF HFr HG HM1 AG KA Ra Ra0 Ra1 Ra2 Ra3;
(apply (c1_braid_call fx LAWS HCELLS LCB T2 cx res out mode nch ns W (ms_regs ms) (ms_mem ms) _ ly' S' k HB HR Hfrm);
 [ exact (c1_st_run cx res out mode nch ns W regs (ms_regs ms) mem (ms_mem ms) md _ ly' S' k HCELLS Hst HJ HM1 KA)
 | rewrite Ra; vm_compute; reflexivity
 | rewrite Ra0; apply (c1_soff_val _ E 20 50 res AG ltac:(lia) E20); lia
 | rewrite Ra1, (c1_soff_reg _ regs X 19 19%bv AG eq_refl); exact R19
 | rewrite Ra2, (c1_denot_soff _ E 34 _ AG ltac:(lia) E34); apply c1_lit_mod
 | rewrite Ra3, (c1_soff_reg _ regs X 26 26%bv AG eq_refl), R26; apply c1_lit_mod
 | exact Hdec
 | refine (c1_garr8_x _ _ _ _ _ _ _ Hgout); intros kk _; apply aview_eq_of; unfold mrestrict; rewrite HM1; reflexivity ]).
Qed.
End F3.

Lemma c1_T2 : AR_laws segs B -> dec_crt_cells B ->
  (forall fx' : YK11.FPState, @aintrin_realizes fx' rc segs B OSet (decode_sigma DS___asan_memset)) ->
  (forall fx' : YK11.FPState, @dec_leaf_wr_at rc B (@LPlainLe.dec_reac_decode_plain_le_cg) fx') ->
  c1_T2_stmt.
Proof.
intros LAWS HCELLS AMS LPL fx cx res out mode nch ns W regs mem md ly' S' k HB _ Hfrm Hst.
exact (@c1_T2_at fx LAWS HCELLS AMS LPL cx res out mode nch ns W regs mem md ly' S' k HB Hfrm Hst).
Qed.

Lemma c1_T3 : AR_laws segs B -> dec_crt_cells B ->
  (forall fx' : YK11.FPState, @dec_leaf_at rc B (@LCheckBraid.dec_check_braid_cg) fx') ->
  c1_T2_stmt -> c1_T3_stmt.
Proof.
intros LAWS HCELLS LCB T2 fx pc cx res out mode nch ns W regs mem md ly' S' k Hpc HB HR Hfrm Hst Hdec Hgout.
exact (@c1_T3_at fx LAWS HCELLS LCB T2 pc cx res out mode nch ns W regs mem md ly' S' k Hpc HB HR Hfrm Hst Hdec Hgout).
Qed.

(* ------------------------------------------------------------------ *)
(* The segment +0x4fc .. +0x5f8                                        *)
(* ------------------------------------------------------------------ *)

Ltac c1_inkeep := cbn [In c1_keepA]; repeat (first [left; apply bv_eq; reflexivity | right]).

Theorem llvm_a_crt1_ok : llvm_a_crt1_stmt asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL
  RLO RHI.
Proof.
unfold llvm_a_crt1_stmt.
intros HCELLS HOWN HERR LAWS MDL ML MFS AMS CRT LCB LPL cx W c HB HR H4.
destruct H4 as (fx' & ly' & S' & regs & mem & md & res & out & mode & nch & ns & -> & Hfrm & HC & Hbl & Hr4 & Ho4 & Hle
  & Hok & Hfr & H10 & H18 & H20 & H22 & H23 & H24 & H25 & H26 & HMO & Hfsh & Hgres & Hgout & HFILL & S32 & S40 & S48
  & S56 & S64 & S72 & S80 & S88 & S112).
pose proof (c1_T2 LAWS HCELLS AMS LPL) as T2.
pose proof (c1_T3 LAWS HCELLS LCB T2) as T3.
assert (HM0 : c1_mem cx res out mode nch ns W mem)
  by exact (conj HMO (conj Hfsh (conj Hgres (conj S40 (conj S48 (conj S56 (conj S64 (conj S72 (conj S80
    (conj S88 S112)))))))))).
apply (@c1_A fx' LAWS cx W ly' S' regs mem md out mode nch ns _ HC
  ltac:(rewrite Hbl; apply in_or_app; right; right; left; reflexivity) HMO H10 H18 H25 H26 HFILL
  S32 S40 S48 S56 S64 S72 S80 S88).
intros regs2 mem2 md2 Hk H18' H22' H24' H26' HM HJ.
assert (KV : forall a, aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
  by (intros a; apply aview_eq_of; unfold mrestrict; rewrite HM; reflexivity).
destruct Hfr as (F19 & F21 & F27).
apply (@c1_B fx' LAWS T2 T3 ML HCELLS HOWN HERR CRT cx res out mode nch ns W regs2 mem2 md2 ly' S' HB HR Hfrm).
unfold c1_st58.
refine (conj _ (conj Hbl (conj Hr4 (conj Ho4 (conj Hle (conj Hok (conj _ (conj _ (conj H18' (conj _ (conj H22'
  (conj _ (conj H24' (conj _ (conj H26' (conj _ (conj _ _))))))))))))))))).
- apply (c1_core_move cx ly' S' W W ly' S' regs regs2 mem mem2 md md2 dec_ev_4fc dec_ev_4fc HC HJ eq_refl (fun H => H)).
  + intros r Hr. apply Hk. cbn [In] in Hr. destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]]; c1_inkeep.
  + intros a _. exact (KV a).
  + intros a Ha. destruct (c1_core_fpres _ _ _ _ _ _ _ _ HC a Ha) as (Hv & b & Hb). split; [exact Hv|].
    exists b. rewrite HM. exact Hb.
- unfold dec_a_fr. rewrite (Hk 19%bv ltac:(c1_inkeep)), (Hk 21%bv ltac:(c1_inkeep)), (Hk 27%bv ltac:(c1_inkeep)).
  exact (conj F19 (conj F21 F27)).
- rewrite (Hk 10%bv ltac:(c1_inkeep)). exact H10.
- rewrite (Hk 20%bv ltac:(c1_inkeep)). exact H20.
- rewrite (Hk 23%bv ltac:(c1_inkeep)). exact H23.
- rewrite (Hk 25%bv ltac:(c1_inkeep)). exact H25.
- apply (c1_mem_kept cx res out mode nch ns W mem mem2 HM0). intros a _. exact (KV a).
- exists (dec_a_fits0 nch ns). unfold dec_a_slot in *. refine (c1_rdword_x _ _ _ _ _ S32). intros kk _. exact (KV _).
- intros Hd. refine (c1_garr8_x _ _ _ _ _ _ _ (Hgout Hd)). intros kk _. exact (KV _).
Qed.

End crt1.
