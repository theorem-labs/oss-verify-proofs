(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_cmp_tail.v, with its module paths and module names changed; 1621 of its 1683 lines of code are new or changed and 532 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_inspect: one of the nine segment statements of lib/A/Prog/LLVMFuzzerTestOneInput_segs.v,
   proves no function (kind: segment lemma).

   llvm_a_inspect_ok : llvm_a_inspect_stmt. The 79 instructions +0x3c0 .. +0x4f8 of DecodeList.v:268-346, stepped by
   the Pa engine from llvm_a_st_3c0 (the return of malloc #2) to llvm_a_st_4fc (the return of reac_decode):
   - ins_head, +0x3c0 .. +0x4d0: the NULL check of the decode buffer (+0x3c0, decided: the block is >= 4096),
     reac_frame_inspect (+0x3d4), the length check and the four frame-field checks with their shadow checks
     (+0x3e0 .. +0x464), the spill of s2 (+0x46c), the inspect-result check (+0x474), the counter field's two
     shadow checks and its check (+0x478 .. +0x4c0), reac_frame_counter (+0x4c8) and its check (+0x4cc). The proof
     splits on the harness's `wellformed` (CInsp.inspect_wf): six paths reach +0x4d0 and are closed at the join
     ins_at4d0 by ins_close; the abort edges +0x474, +0x4c0 and +0x4cc into +0xa4c are refuted from the inspect and
     counter leaf posts, and every shadow check is the token engine's addressability obligation, discharged from
     the body block (no slow path at +0xa54 .. +0xb60 is stepped).
   - ins_tail, +0x4d0 .. +0x4f8: the size test, __asan_memset of the buffer (fill 0xa5, aj_intrin_at), the spill of
     the buffer pointer (+0x4f0) and reac_decode (+0x4f8), and the cut-point predicate llvm_a_st_4fc.
   Every leaf call goes through the shared bridge lib/A/Prog/LLVMFuzzerTestOneInput_leafb.v (dec_leafb_journal and
   the dec_leafb_* premise lemmas).
   Follows: the engine idiom of libreac/fuzz_boxreg lib/A/Prog/ReadName.v (a working branch
   1d92330b7ad: paj_run / paj_run_to / paj_branch, awr_ok, the shadow obligations, the journal); the branch
   conditions of the released ubsan lib/U/Prog/fd_down.v (568db058c1d). Lemma texts copied from sibling segment
   files are marked at each lemma with their source: a working branch f0f023a4fb8
   LLVMFuzzerTestOneInput_seg_crt1.v (rdword_of_val_mem, cell8, cell4, mode_re, core_kept) and
   a working branch 39c9a7df157 LLVMFuzzerTestOneInput_seg_up.v (fsh_kept). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaRun PaShadow DecodeSyms DecodeList DecodePa.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaJournal PaBase DecodeCJ.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import PaStep DecodePaLib DecodeImg YC1g YC1h YC81 YC4b YC85.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require DecodeShape Img0 AsanCells.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import DecodeAddr check_round_trip_cg
  LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require LeafCgKit reac_frame_counter_cg
  reac_frame_inspect_cg reac_decode_cg reac_frame_inspect_c reac_frame_counter_c reac_decode_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require Import LLVMFuzzerTestOneInput_leafb.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK0o.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LCK := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.LeafCgKit.
Module LCounter := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_counter_cg.
Module LInspect := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_cg.
Module LDecode := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_cg.
Module CInsp := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_inspect_c.
Module CCnt := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_frame_counter_c.
Module CDec := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.reac_decode_c.
Module ACells := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AsanCells.
Module AImg0 := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Img0.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section si. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := dec_A_sink_head.
Variable asink_syms : Type.
Variable tfib_K : asink_syms.
Variable asink_none : list Segment -> asink_syms -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
Variables RA_LLVMF A_EMPTY : Z.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := decodesegs0.
#[local] Notation PID := (@PI_decode rc).
#[local] Notation VAL := (@pa_val rc decode_listing PID).

Definition ins_spill : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 120 40 80
    [YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 48 (CVal 8 (SOff 33 0));
     YP09.mkChunk 64 (CVal 8 (SOff 34 0)); YP09.mkChunk 80 (CVal 8 (SOff 35 0));
     YP09.mkChunk 88 (CVal 8 (SOff 36 0)); YP09.mkChunk 112 (CVal 8 (SOff 19 0))].
Definition ins_facts0 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, YC4b.PTR 4);
           (18%nat, mkAF SB SB 0); (20%nat, YC4b.PTR 4)] [] [].
Definition ss_ins0 : sstate := mkSS 0x3c0 sr_atoms [ins_spill] None ins_facts0.
Definition ins_extra (fits nch64 mode nch32 ns64 : Z) : list word :=
  [Z_to_bv 64 fits; Z_to_bv 64 nch64; Z_to_bv 64 mode; Z_to_bv 64 nch32; Z_to_bv 64 ns64].

Lemma rdword_range : forall rd a v, (forall x b, rd x = Some b -> 0 <= b < 256) -> rdword rd a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros rd a v Hr Hw. unfold rdword in Hw.
repeat match type of Hw with context [match rd ?x with Some _ => _ | None => _ end] =>
  let b := fresh "b" in let Hb := fresh "Hb" in destruct (rd x) as [b|] eqn:Hb; [|discriminate]; apply Hr in Hb end.
injection Hw as <-. lia.
Qed.
Lemma aview_byte_range : forall H m x b, aview segs H m x = Some b -> 0 <= b < 256.
Proof.
intros H m x b Hb. unfold aview in Hb. destruct (YP09.mbyte segs (mrestrict H m) x) as [bb|]; [|discriminate].
cbn in Hb. injection Hb as <-. pose proof (bv_unsigned_in_range 8 bb) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.
Ltac ereg EL n r H := rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat _ _ n r eq_refl); exact H.

(* The bytes a garr8 array of the view holds stay when the view of each of its bytes does. *)
Lemma ins_garr8_kept : forall H (m m' : word -> option byte) p l,
  garr8 segs (mrestrict H m) p l ->
  (forall j, 0 <= j < Z.of_nat (length l) -> aview segs H m' (p + j) = aview segs H m (p + j)) ->
  garr8 segs (mrestrict H m') p l.
Proof.
  intros H m m' p l HG HK j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
  intros k Hk. assert (k = 0%nat) as -> by lia. pose proof (HV 0%nat Hk) as V.
  change (Z.of_nat 0) with 0 in *. rewrite Z.add_0_r in *.
  rewrite (mbyte_of_aview segs H H m m') by (apply HK; lia). exact V.
Qed.
(* An 8-byte slot word of the view stays when the view of its bytes does. *)
Lemma ins_rdword_kept : forall H (m m' : word -> option byte) a v,
  rdword (aview segs H m) a = Some v ->
  (forall i, 0 <= i < 8 -> aview segs H m' (a + i) = aview segs H m (a + i)) ->
  rdword (aview segs H m') a = Some v.
Proof.
  intros H m m' a v Hw HK. unfold rdword in *.
  rewrite !HK by lia. replace a with (a + 0) at 1 by lia. rewrite HK by lia. rewrite Z.add_0_r. exact Hw.
Qed.
(* The view after a symbolic run: the bytes outside the run's write windows are the bytes before it. *)
Lemma ins_kept_run : forall E (rs : smem) H (m0 m1 : word -> option byte) (P : Z -> Prop),
  frame_of E rs (mrestrict H m0) (mrestrict H m1) ->
  (forall a, in_wrange E rs a -> P a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ P a -> aview segs H m1 a = aview segs H m0 a.
Proof.
  intros E rs H m0 m1 P HF HW a Ha HP. unfold aview, YP09.mbyte.
  rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by exact Ha. intros Hw. exact (HP (HW a Hw)).
Qed.

(* The state at +0x3c0 without its configuration: llvm_a_st_3c0's body. *)
Definition ins_at3c0 (cx : dctx) (fx : YK11.FPState) (ly : alayout) (S : astate) (W : world segs)
    (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (res out mode nch ns : Z) : Prop :=
    frm_zero (@fp_csr fx) /\
    dec_a_core B cx ly S W regs mem md dec_ev_3c0 /\
    ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ++ [(res, dec_a_len (d_n cx))] ++
                       [(out, dec_a_olen nch ns)] /\
    4096 <= res /\ 4096 <= out /\
    mo_le MT (d_S cx) S (dec_spent_3c0 MT (d_n cx)) /\ mo_ok MT S (dec_rest_3c0 MT) /\
    dec_a_fr cx regs /\
    YK11.getr regs 10 = w64 out /\
    YK11.getr regs 18 = w64 SHADOW_OFF /\
    YK11.getr regs 20 = w64 res /\
    YK11.getr regs 26 = w64 (dec_a_len (d_n cx)) /\
    YK11.getr regs 24 = w64 (dec_a_prod nch ns) /\
    YK11.getr regs 25 = w64 (dec_a_olen nch ns) /\
    YK11.getr regs 23 = w64 (ns mod 2 ^ 32) /\
    YK11.getr regs 22 = w64 (mode + 8) /\
    dec_a_mode_ok cx W mem mode nch ns /\
    dec_a_fsh cx (aview segs (w_H W) mem) 0 4 /\
    garr8 segs (mrestrict (w_H W) mem) res (map (fun b : byte => bv_unsigned b) (d_body cx)) /\
    dec_a_slot cx (aview segs (w_H W) mem) 32 (dec_a_fits0 nch ns) /\
    dec_a_slot cx (aview segs (w_H W) mem) 48 (nch mod 2 ^ 64) /\
    dec_a_slot cx (aview segs (w_H W) mem) 64 mode /\
    dec_a_slot cx (aview segs (w_H W) mem) 80 (nch mod 2 ^ 32) /\
    dec_a_slot cx (aview segs (w_H W) mem) 88 (ns mod 2 ^ 64) /\
    dec_a_slot cx (aview segs (w_H W) mem) 112 (d_F cx).

(* The machine at +0x4d0, where every path of the inspect / counter checks joins: the journal and the registers the
   rest of the segment reads, the spilled words, and every byte outside the stack window the calls and the spill
   area used still the +0x3c0 byte. *)
Definition ins_at4d0 (cx : dctx) (ly : alayout) (S : astate) (W : world segs) (mem : word -> option byte)
    (res out mode nch ns : Z) (regs4 : bvmap 5 word) (mem4 : word -> option byte) (md4 : Model) : Prop :=
  @ajournal rc tfib_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W mem4 md4 dec_ev_3c0 /\
  spZ regs4 = d_sp1 cx /\
  YK11.getr regs4 3 = w64 (as_gp B) /\ YK11.getr regs4 4 = w64 (as_tp B) /\
  YK11.getr regs4 8 = w64 (d_sp0 cx) /\ YK11.getr regs4 9 = w64 (d_sp1 cx) /\
  dec_a_fr cx regs4 /\
  YK11.getr regs4 20 = w64 res /\ YK11.getr regs4 22 = w64 out /\
  YK11.getr regs4 23 = w64 (ns mod 2 ^ 32) /\ YK11.getr regs4 24 = w64 (dec_a_prod nch ns) /\
  YK11.getr regs4 25 = w64 (dec_a_olen nch ns) /\
  YK11.getr regs4 26 = w64 (if CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) then 1 else 0) /\
  dec_a_slot cx (aview segs (w_H W) mem4) 32 (dec_a_fits0 nch ns) /\
  dec_a_slot cx (aview segs (w_H W) mem4) 40 SHADOW_OFF /\
  dec_a_slot cx (aview segs (w_H W) mem4) 48 (nch mod 2 ^ 64) /\
  dec_a_slot cx (aview segs (w_H W) mem4) 56 (dec_a_len (d_n cx)) /\
  dec_a_slot cx (aview segs (w_H W) mem4) 64 mode /\
  dec_a_slot cx (aview segs (w_H W) mem4) 80 (nch mod 2 ^ 32) /\
  dec_a_slot cx (aview segs (w_H W) mem4) 88 (ns mod 2 ^ 64) /\
  dec_a_slot cx (aview segs (w_H W) mem4) 112 (d_F cx) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx + 120) ->
     aview segs (w_H W) mem4 a = aview segs (w_H W) mem a) /\
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem4 a).

(* ------------------------------------------------------------------ *)
(* The head: +0x3c0 .. +0x4d0                                          *)
(* ------------------------------------------------------------------ *)

(* The six body bytes the five frame-field checks read (+0x3f8, +0x418, +0x438, +0x458, +0x4a4, +0x4ac), as atoms
   37 .. 42 of the environment, after the five geometry words 32 .. 36 of ins_extra. *)
Definition ins_xh (fits nch64 mode nch32 ns64 : Z) (bs : list byte) : list word :=
  ins_extra fits nch64 mode nch32 ns64 ++
  map (fun i => Z_to_bv 64 (CInsp.inspect_byte bs i)) [12; 13; 14; 15; 1490; 1491]%nat.
Definition ins_facts_h : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (10%nat, YC4b.PTR 4);
           (18%nat, mkAF SB SB 0); (20%nat, YC4b.PTR 4);
           (37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0); (39%nat, mkAF 0 255 0); (40%nat, mkAF 0 255 0);
           (41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0)] [] [].
Definition ss_h0 : sstate := mkSS 0x3c0 sr_atoms [ins_spill] None ins_facts_h.


Lemma ins_byte_range : forall bs i, 0 <= CInsp.inspect_byte bs i < 256.
Proof.
intros bs i. unfold CInsp.inspect_byte. pose proof (bv_unsigned_in_range 8 (nth i bs (Z_to_bv 8 0))) as R.
change (bv_modulus 8) with 256 in R. lia.
Qed.

(* The body copy's six checked bytes as a read-only region of the symbolic state (base s4 = atom 20), once the
   length check (+0x3e0) has shown the copy is 1492 bytes long. *)
Definition ins_res_rg : YP09.region :=
  YP09.mkRegion (Some 20%nat) 12 1492 0 0
    [YP09.mkChunk 12 (CVal 1 (SOff 37 0)); YP09.mkChunk 13 (CVal 1 (SOff 38 0));
     YP09.mkChunk 14 (CVal 1 (SOff 39 0)); YP09.mkChunk 15 (CVal 1 (SOff 40 0));
     YP09.mkChunk 1490 (CVal 1 (SOff 41 0)); YP09.mkChunk 1491 (CVal 1 (SOff 42 0))].
Definition ins_spill_only (rs : smem) : bool :=
  forallb (fun r => match r_base r with
                    | Some k => (k =? 9)%nat && (r_lo r =? 32) && (r_hi r =? 120)
                    | None => false end) rs.

Lemma ins_body_val : forall H (m m' : word -> option byte) p bs (i : nat),
  garr8 segs (mrestrict H m) p (map (fun b : byte => bv_unsigned b) bs) -> (i < length bs)%nat ->
  aview segs H m' (p + Z.of_nat i) = aview segs H m (p + Z.of_nat i) ->
  val_mem segs (mrestrict H m') (p + Z.of_nat i) 1 (CInsp.inspect_byte bs i).
Proof.
intros H m m' p bs i HG Hi HK k Hk. assert (k = 0%nat) as -> by lia.
assert (Hi' : (i < length (map (fun b : byte => bv_unsigned b) bs))%nat) by (rewrite length_map; exact Hi).
destruct (HG i Hi') as [HV _]. pose proof (HV 0%nat ltac:(lia)) as V.
change (Z.of_nat 0) with 0 in *. rewrite Z.add_0_r in *.
rewrite (mbyte_of_aview segs H H m m') by exact HK.
rewrite V. f_equal. f_equal. unfold CInsp.inspect_byte.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by exact Hi'. rewrite map_nth. reflexivity.
Qed.

Section fxs. Context {fx : YK11.FPState}.
Lemma ins_add_res_ok : forall E ss (ms : machine_state) H (m0 : word -> option byte) res sp1 body,
  st_ok_pi segs VAL E ss (restrict H ms) -> ins_spill_only (ss_mem ss) = true ->
  bv_unsigned (ew E 20) = res -> bv_unsigned (ew E 9) = sp1 ->
  ew E 37 = w64 (CInsp.inspect_byte body 12) -> ew E 38 = w64 (CInsp.inspect_byte body 13) ->
  ew E 39 = w64 (CInsp.inspect_byte body 14) -> ew E 40 = w64 (CInsp.inspect_byte body 15) ->
  ew E 41 = w64 (CInsp.inspect_byte body 1490) -> ew E 42 = w64 (CInsp.inspect_byte body 1491) ->
  length body = 1492%nat ->
  garr8 segs (mrestrict H m0) res (map (fun b : byte => bv_unsigned b) body) ->
  (forall a, res <= a < res + 1492 -> aview segs H (ms_mem ms) a = aview segs H m0 a) ->
  4096 <= res -> res + 1492 <= sp1 + 32 -> sp1 < 2 ^ 47 ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (ss_regs ss) (ins_res_rg :: ss_mem ss) (ss_resv ss) (ss_facts ss)) (restrict H ms).
Proof.
intros E ss ms H m0 res sp1 body HS Hsp Hres Hsp1 E37 E38 E39 E40 E41 E42 Hlen HG HK H4096 Hlo Hsp47.
apply (st_ok_pi_add_region (PI := PID)); [exact HS | vm_compute; reflexivity | |].
- unfold ins_res_rg, region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite Hres. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  cbn [ms_mem restrict].
  assert (CK : forall (i : nat) (k : nat), ew E k = w64 (CInsp.inspect_byte body i) -> (i < 1492)%nat ->
    YP09.chunk_ok segs E (mrestrict H (ms_mem ms)) res (YP09.mkChunk (Z.of_nat i) (CVal 1 (SOff k 0)))).
  { intros i k Hk Hi. pose proof (ins_byte_range body i) as Hb.
    apply (chunk_ok_val segs E _ res (Z.of_nat i) 1 (SOff k 0) (CInsp.inspect_byte body i)).
    - cbn [sv_denot]. rewrite Hk, Z.add_0_r, unsigned_lit_small by lia. reflexivity.
    - change (2 ^ (8 * Z.of_N 1)) with 256. lia.
    - lia.
    - apply (ins_body_val H m0 (ms_mem ms) res body i HG ltac:(lia)). apply HK. lia. }
  repeat apply Forall_cons; try apply Forall_nil.
  + exact (CK 12%nat 37%nat E37 ltac:(lia)).
  + exact (CK 13%nat 38%nat E38 ltac:(lia)).
  + exact (CK 14%nat 39%nat E39 ltac:(lia)).
  + exact (CK 15%nat 40%nat E40 ltac:(lia)).
  + exact (CK 1490%nat 41%nat E41 ltac:(lia)).
  + exact (CK 1491%nat 42%nat E42 ltac:(lia)).
- unfold ins_spill_only in Hsp. revert Hsp. generalize (ss_mem ss) as rs. induction rs as [|r rs IH]; intros Hsp; [exact I|].
  cbn [forallb] in Hsp. apply andb_prop in Hsp as [Hr Hsp]. cbn [all_disjoint]. split; [|exact (IH Hsp)].
  destruct r as [[k|] lo hi wlo whi cs]; cbn [r_base r_lo r_hi] in Hr; [|discriminate].
  apply andb_prop in Hr as [Hr Hhi]. apply andb_prop in Hr as [Hk Hlo2].
  apply Nat.eqb_eq in Hk. apply Z.eqb_eq in Hlo2. apply Z.eqb_eq in Hhi. subst k lo hi.
  unfold extent_disjoint. cbn [ins_res_rg YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Hres, Hsp1. left. lia.
Qed.
End fxs.

(* a working branch f0f023a4fb8, LLVMFuzzerTestOneInput_seg_crt1.v:609-623
   c1_rdword_of_val_mem (itself GrantFrame.v rdword_of_val_mem): an 8-byte value of the view is a word of it. *)
Lemma ins_rdword_of_val_mem : forall H mem a v,
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

(* The registers the head leaves at +0x4d0 as they were at +0x3c0 (s6 = x22 holds a0 = out since +0x3c4). *)
Definition ins_keep : list (bv 5 * nat) :=
  [(2%bv, 2%nat); (3%bv, 3%nat); (4%bv, 4%nat); (8%bv, 8%nat); (9%bv, 9%nat); (19%bv, 19%nat); (20%bv, 20%nat);
   (21%bv, 21%nat); (22%bv, 10%nat); (23%bv, 23%nat); (24%bv, 24%nat); (25%bv, 25%nat); (27%bv, 27%nat)].
Definition ins_atom_b (e : sv) (n : nat) : bool :=
  match e with SOff k z => (k =? n)%nat && (z =? 0) | _ => false end.
Definition ins_regs_ok (ss : sstate) : bool :=
  forallb (fun p => ins_atom_b (sr_get (ss_regs ss) (fst p)) (snd p)) ins_keep.
Lemma ins_atom_b_eq : forall e n, ins_atom_b e n = true -> e = SOff n 0.
Proof.
intros e n H. destruct e; cbn in H; try discriminate.
apply andb_prop in H as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma ins_reg_get : forall ss r k, ins_regs_ok ss = true -> In (r, k) ins_keep -> sr_get (ss_regs ss) r = SOff k 0.
Proof.
intros ss r k H Hin. unfold ins_regs_ok in H. rewrite forallb_forall in H.
exact (ins_atom_b_eq _ _ (H (r, k) Hin)).
Qed.
(* The spill slots the head leaves at +0x4d0: an 8-byte chunk of the base-9 region holding an atom. *)
Definition ins_has_chunk (rs : smem) (off : Z) (n : nat) : bool :=
  existsb (fun r => match r_base r with
                    | Some k => (k =? 9)%nat &&
                        existsb (fun c => (c_off c =? off) &&
                          match YP09.c_val c with CVal w e => (w =? 8)%N && ins_atom_b e n | _ => false end)
                          (r_chunks r)
                    | None => false end) rs.
Definition ins_chunks_ok (ss : sstate) : bool :=
  ins_has_chunk (ss_mem ss) 32 32 && ins_has_chunk (ss_mem ss) 40 18 && ins_has_chunk (ss_mem ss) 48 33 &&
  ins_has_chunk (ss_mem ss) 56 26 && ins_has_chunk (ss_mem ss) 64 34 && ins_has_chunk (ss_mem ss) 80 35 &&
  ins_has_chunk (ss_mem ss) 88 36 && ins_has_chunk (ss_mem ss) 112 19.
Lemma ins_slot_of_chunk : forall E rs m off n b,
  mem_ok segs E m rs -> ins_has_chunk rs off n = true -> bv_unsigned (ew E 9) = b ->
  val_mem segs m (b + off) 8 (bv_unsigned (ew E n)).
Proof.
intros E rs m off n b HM H Hb. unfold ins_has_chunk in H. apply existsb_exists in H as (r & Hr & H).
destruct r as [[k|] lo hi wlo whi cs]; cbn [r_base r_chunks] in H; [|discriminate].
apply andb_prop in H as [Hk H]. apply Nat.eqb_eq in Hk. subst k.
apply existsb_exists in H as (c & Hc & H). destruct c as [o [w e| | |]]; cbn [c_off YP09.c_val] in H;
  [|rewrite andb_false_r in H; discriminate..].
apply andb_prop in H as [Ho H]. apply andb_prop in H as [Hw He]. apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw.
apply ins_atom_b_eq in He. subst o w e.
pose proof (mem_ok_region segs E m _ _ HM Hr) as HR.
pose proof (field_of_region_any E m 9 b cs lo hi wlo whi off 8 (SOff n 0) HR Hb Hc ltac:(lia)) as V.
cbn [sv_denot] in V. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in V.
change (N.to_nat 8) with 8%nat in V. change (8 * Z.of_N 8) with 64 in V.
rewrite Z.mod_small in V by (pose proof (bv_unsigned_in_range 64 (ew E n)) as R; change (bv_modulus 64) with (2 ^ 64) in R; lia).
exact V.
Qed.

(* Every path of the head ends at +0x4d0 in a symbolic state that keeps ins_keep's registers, has s10 = the
   harness's `wellformed`, and still holds the eight spill-slot chunks: that state is ins_at4d0. E agrees with the
   head's entry environment below the call atoms. *)
Lemma ins_close : forall (cx : dctx) (fx : YK11.FPState) ly S (W : world segs) regs mem md (res out mode nch ns : Z)
    (E : env) (ss : sstate) (ms : machine_state) md',
  ins_at3c0 cx fx ly S W regs mem md res out mode nch ns -> 0 <= dec_a_len (d_n cx) < 2 ^ 64 ->
  (forall n, (n < 43)%nat -> ew E n =
     ew (@Eimg rc decode_listing PID (Ereg regs (ins_xh (dec_a_fits0 nch ns) (nch mod 2 ^ 64) mode (nch mod 2 ^ 32)
          (ns mod 2 ^ 64) (d_body cx)))) n) ->
  st_ok_pi segs VAL E ss (restrict (w_H W) ms) ->
  ss_pc ss = 0x4d0 -> ss_resv ss = None ->
  ins_regs_ok ss = true ->
  U E (sr_get (ss_regs ss) 26) = (if CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) then 1 else 0) ->
  ins_chunks_ok ss = true ->
  @ajournal rc tfib_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S W (ms_mem ms) md' dec_ev_3c0 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (d_sp1 cx - 4096 <= a < d_sp1 cx + 120) ->
     aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a) ->
  SRr segs W (mkCfg ms md')
    (fun W2 c2 => W2 = W /\ exists regs4 mem4 md4,
       c2 = mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (VAL A_TEXT + 0x4d0)) mem4 (YK11.seg_rom segs)) md4 /\
       ins_at4d0 cx ly S W mem res out mode nch ns regs4 mem4 md4).
Proof.
intros cx fx ly S W regs mem md res out mode nch ns E ss ms md' H3 Hlen64 HAG HS Hpc Hrv HRG H26 HCH HJ HKR HGR.
pose proof H3 as (Hfrm & HCORE & Hbl & Hres & Hout & MLE & MOK & HFR & R10 & R18 & R20 & R26 & R24 & R25 & R23 & R22
  & HMODE & HFSH & HBODY & SL32 & SL48 & SL64 & SL80 & SL88 & SL112).
pose proof HCORE as (HJ0 & Hfrs & R8 & R9 & Rsp & Hsp1r & Hsp1m & R3 & R4 & _).
set (xh := ins_xh (dec_a_fits0 nch ns) (nch mod 2 ^ 64) mode (nch mod 2 ^ 32) (ns mod 2 ^ 64) (d_body cx)) in *.
assert (HE : forall n, (n < 43)%nat -> ew E n = ew (Ereg regs xh) n)
  by (intros n Hn; rewrite HAG by exact Hn; apply Eimg_low; unfold A_TEXT; lia).
assert (Hu64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z) by (intros z Hz; apply unsigned_lit_small; exact Hz).
(* a kept register reads the +0x3c0 register's value *)
assert (KR : forall (r : bv 5) (k : nat) (rk : bv 5) v, In (r, k) ins_keep -> Z.of_nat k = bv_unsigned rk ->
  YK11.getr regs rk = v -> getr (ms_regs ms) r = v).
{ intros r k rk v Hin Hk Hv. rewrite (st_ok_pi_restrict_reg (w_H W) E ss ms r HS).
  rewrite (ins_reg_get ss r k HRG Hin). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite HE by (unfold ins_keep in Hin; cbn [In] in Hin; repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <-; lia|]); destruct Hin).
  rewrite (ew_Ereg_nat regs xh k rk Hk). exact Hv. }
assert (Hms : ms = YK11.mkst (ms_regs ms) (Z_to_bv 64 (VAL A_TEXT + 0x4d0)) (ms_mem ms) (YK11.seg_rom segs)).
{ rewrite <- Hpc. exact (st_ok_pi_restrict_mkst (w_H W) E ss ms HS Hrv). }
apply SRr_ret. split; [reflexivity|]. exists (ms_regs ms), (ms_mem ms), md'.
split; [rewrite Hms at 1; reflexivity|].
assert (HM : mem_ok segs E (mrestrict (w_H W) (ms_mem ms)) (ss_mem ss))
  by (clear - HS; destruct ss; exact (st_ok_mem_ok segs E _ _ HS)).
assert (EX : forall j v, (j < 11)%nat -> nth j xh (Z_to_bv 64 0) = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (ew E (32 + j)) = v).
{ intros j v Hj Hv Hr. rewrite HE by lia. rewrite ew_Ereg_extra, Hv. apply Hu64. exact Hr. }
assert (ER : forall (k : nat) (rk : bv 5) v, (k < 32)%nat -> Z.of_nat k = bv_unsigned rk ->
  YK11.getr regs rk = w64 v -> 0 <= v < 2 ^ 64 -> bv_unsigned (ew E k) = v).
{ intros k rk v Hk Hkr Hv Hr. rewrite HE by lia. rewrite (ew_Ereg_nat regs xh k rk Hkr), Hv. apply Hu64. exact Hr. }
pose proof HJ0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof alloc_ceiling_val.
assert (Hsp1b : 0 <= d_sp1 cx < 2 ^ 47) by (unfold DEC_LLVMF_STK in *; lia).
assert (U9 : bv_unsigned (ew E 9) = d_sp1 cx) by (apply (ER 9%nat 9%bv); [lia | reflexivity | exact R9 | lia]).
assert (SLOT : forall off n v, ins_has_chunk (ss_mem ss) off n = true -> bv_unsigned (ew E n) = v -> 0 <= v < 2 ^ 64 ->
  dec_a_slot cx (aview segs (w_H W) (ms_mem ms)) off v).
{ intros off n v Hc Hv Hr. unfold dec_a_slot. apply ins_rdword_of_val_mem; [|exact Hr].
  rewrite <- Hv. exact (ins_slot_of_chunk E _ _ off n _ HM Hc U9). }
unfold ins_chunks_ok in HCH. repeat rewrite andb_true_iff in HCH.
destruct HCH as [[[[[[[C32 C40] C48] C56] C64] C80] C88] C112].
pose proof (rdword_range _ _ _ (aview_byte_range _ _) SL64) as Hmode64.
pose proof (rdword_range _ _ _ (aview_byte_range _ _) SL32) as Hfits64.
pose proof (rdword_range _ _ _ (aview_byte_range _ _) SL112) as HF64.
Ltac inkeep := unfold ins_keep; cbn [In]; repeat (first [left; reflexivity | right]).
unfold ins_at4d0.
split; [exact HJ|].
split; [unfold spZ in *; rewrite (KR 2%bv 2%nat 2%bv (YK11.getr regs 2) ltac:(inkeep) eq_refl eq_refl); exact Rsp|].
split; [exact (KR 3%bv 3%nat 3%bv _ ltac:(inkeep) eq_refl R3)|].
split; [exact (KR 4%bv 4%nat 4%bv _ ltac:(inkeep) eq_refl R4)|].
split; [exact (KR 8%bv 8%nat 8%bv _ ltac:(inkeep) eq_refl R8)|].
split; [exact (KR 9%bv 9%nat 9%bv _ ltac:(inkeep) eq_refl R9)|].
split.
{ destruct HFR as (F19 & F21 & F27).
  split; [exact (KR 19%bv 19%nat 19%bv _ ltac:(inkeep) eq_refl F19)|].
  split; [exact (KR 21%bv 21%nat 21%bv _ ltac:(inkeep) eq_refl F21) | exact (KR 27%bv 27%nat 27%bv _ ltac:(inkeep) eq_refl F27)]. }
split; [exact (KR 20%bv 20%nat 20%bv _ ltac:(inkeep) eq_refl R20)|].
split; [exact (KR 22%bv 10%nat 10%bv _ ltac:(inkeep) eq_refl R10)|].
split; [exact (KR 23%bv 23%nat 23%bv _ ltac:(inkeep) eq_refl R23)|].
split; [exact (KR 24%bv 24%nat 24%bv _ ltac:(inkeep) eq_refl R24)|].
split; [exact (KR 25%bv 25%nat 25%bv _ ltac:(inkeep) eq_refl R25)|].
split; [rewrite (st_ok_pi_restrict_reg (w_H W) E ss ms 26%bv HS), (denot_lit_U E _), H26; reflexivity|].
split; [apply (SLOT 32 32%nat); [exact C32 | exact (EX 0%nat _ ltac:(lia) eq_refl Hfits64) | exact Hfits64]|].
split; [apply (SLOT 40 18%nat); [exact C40 | apply (ER 18%nat 18%bv); [lia | reflexivity | exact R18 | unfold SHADOW_OFF; lia] | unfold SHADOW_OFF; lia]|].
assert (M64 : forall z m, 0 < m <= 2 ^ 64 -> 0 <= z mod m < 2 ^ 64) by (intros z m Hm; pose proof (Z.mod_pos_bound z m ltac:(lia)); lia).
split; [apply (SLOT 48 33%nat); [exact C48 | exact (EX 1%nat _ ltac:(lia) eq_refl (M64 nch (2 ^ 64) ltac:(lia))) | exact (M64 nch (2 ^ 64) ltac:(lia))]|].
split; [apply (SLOT 56 26%nat); [exact C56 | apply (ER 26%nat 26%bv); [lia | reflexivity | exact R26 | exact Hlen64] | exact Hlen64]|].
split; [apply (SLOT 64 34%nat); [exact C64 | exact (EX 2%nat _ ltac:(lia) eq_refl Hmode64) | exact Hmode64]|].
split; [apply (SLOT 80 35%nat); [exact C80 | exact (EX 3%nat _ ltac:(lia) eq_refl (M64 nch (2 ^ 32) ltac:(lia))) | exact (M64 nch (2 ^ 32) ltac:(lia))]|].
split; [apply (SLOT 88 36%nat); [exact C88 | exact (EX 4%nat _ ltac:(lia) eq_refl (M64 ns (2 ^ 64) ltac:(lia))) | exact (M64 ns (2 ^ 64) ltac:(lia))]|].
split; [apply (SLOT 112 19%nat); [exact C112 | apply (ER 19%nat 19%bv); [lia | reflexivity | exact (proj1 HFR) | exact HF64] | exact HF64]|].
split; [exact HKR | exact HGR].
Qed.

Lemma ew_ewset_lt : forall E k w n, (n < k)%nat -> ew (ewset E k w) n = ew E n.
Proof. intros E k w n Hn. cbn [ew ewset]. destruct (Nat.eqb_spec n k); [lia | reflexivity]. Qed.
Ltac ins_ewn := repeat (first [rewrite ew_ewset_lt by lia | rewrite ew_havoc_old by lia]).
Ltac ins_ewn_in H := repeat (first [rewrite ew_ewset_lt in H by lia | rewrite ew_havoc_old in H by lia]).

(* The branch conditions of the five frame-field checks, read back as Z facts. *)
Lemma ins_bne_false : forall E n c v, branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = false ->
  ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> v = c.
Proof.
intros E n c v Hc Hv Hr Hcr. rewrite branch_ne_U in Hc. rewrite (U_atom E n v Hv Hr), (U_lit E c Hcr) in Hc.
apply negb_false_iff in Hc. apply Z.eqb_eq in Hc. exact Hc.
Qed.
(* s10 after `addi a1,a1,-234; sltiu s10,a1,1` (+0x45c, +0x460) on the byte at 1491 (atom 42). *)
Lemma ins_sltu_val : forall E v, ew E 42 = w64 v -> 0 <= v < 256 ->
  U E (SAlu ALU_SLTU (SOff 42 (-234)) (SLit 1)) = if v =? 234 then 1 else 0.
Proof.
intros E v Hv Hr. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, Hv, unsigned_lit_small by lia.
unfold zcanon, M64. change (1 mod 2 ^ 64) with 1.
destruct (Z.eqb_spec v 234) as [-> | Hne].
- change ((234 + -234) mod 2 ^ 64) with 0. reflexivity.
- destruct (Z.ltb_spec ((v + -234) mod 2 ^ 64) 1) as [Hl | Hl]; [|reflexivity]. exfalso.
  destruct (Z_lt_le_dec v 234).
  + rewrite Z.mod_eq in Hl by lia. replace ((v + -234) / 2 ^ 64) with (-1) in Hl; [lia|].
    apply Z.div_unique with (r := v + -234 + 2 ^ 64); lia.
  + rewrite Z.mod_small in Hl by lia. lia.
Qed.
(* The +0x470 test: the inspect result's high word, srli a1,a0,32. *)
Lemma ins_srl32 : forall E a c, U E a = 2 ^ 32 + c -> 0 <= c < 2 ^ 16 -> U E (SAlu ALU_SRL a (SLit 32)) = 1.
Proof.
intros E a c Ha Hc. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit. change (Z.land (zcanon 32) 63) with 32.
rewrite Z.shiftr_div_pow2 by lia. replace ((2 ^ 32 + c) / 2 ^ 32) with 1. reflexivity.
apply Z.div_unique with (r := c); lia.
Qed.
Lemma ins_srl32_0 : forall E a, U E a = 0 -> U E (SAlu ALU_SRL a (SLit 32)) = 0.
Proof.
intros E a Ha. rewrite U_SAlu. cbn [zalu_raw]. rewrite Ha, U_SLit. change (Z.land (zcanon 32) 63) with 32. reflexivity.
Qed.
(* +0x4b0 / +0x4bc: the counter field, the inspect result's low 16 bits (slli a0,a0,48; srli a0,a0,48). *)
Lemma ins_lo16 : forall E a c, U E a = 2 ^ 32 + c -> 0 <= c < 2 ^ 16 ->
  U E (SAlu ALU_SRL (SAlu ALU_SLL a (SLit 48)) (SLit 48)) = c.
Proof.
intros E a c Ha Hc. rewrite !U_SAlu. cbn [zalu_raw]. rewrite Ha, !U_SLit. change (Z.land (zcanon 48) 63) with 48.
rewrite Z.shiftl_mul_pow2 by lia. unfold zcanon, M64.
replace ((2 ^ 32 + c) * 2 ^ 48) with (c * 2 ^ 48 + 2 ^ 16 * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. rewrite (Z.mod_small (c * 2 ^ 48)) by lia.
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia. apply Z.mod_small. lia.
Qed.

Lemma ins_bne_true : forall E n c v, branch_taken BC_NE (sv_denot E (SOff n 0)) (sv_denot E (SLit c)) = true ->
  ew E n = w64 v -> 0 <= v < 2 ^ 64 -> 0 <= c < 2 ^ 64 -> v <> c.
Proof.
intros E n c v Hc Hv Hr Hcr. rewrite branch_ne_U in Hc. rewrite (U_atom E n v Hv Hr), (U_lit E c Hcr) in Hc.
apply negb_true_iff in Hc. apply Z.eqb_neq in Hc. exact Hc.
Qed.
(* +0x4b4 / +0x4b8: s2 = (byte 15 << 8) | byte 14, the counter field as the harness reads it. *)
Lemma ins_or16 : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 256 -> 0 <= y < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL a (SLit 8)) b) = y + 256 * x.
Proof.
intros E a b x y Ha Hb Hx Hy. rewrite !U_SAlu. cbn [zalu_raw]. rewrite Ha, Hb, U_SLit.
change (Z.land (zcanon 8) 63) with 8. rewrite Z.shiftl_mul_pow2 by lia.
unfold zcanon at 2. unfold M64. rewrite (Z.mod_small (x * 2 ^ 8)) by lia.
assert (Hd : Z.land (x * 2 ^ 8) y = 0).
{ apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 8).
  - rewrite <- Z.shiftl_mul_pow2 by lia. rewrite Z.shiftl_spec_low by lia. reflexivity.
  - replace y with (y mod 2 ^ 8) by (apply Z.mod_small; lia). rewrite Z.mod_pow2_bits_high by lia. apply andb_false_r. }
rewrite <- (Z.lxor_lor _ _ Hd), <- (Z.add_nocarry_lxor _ _ Hd). unfold zcanon, M64. rewrite Z.mod_small by lia. lia.
Qed.

Ltac ins_awr U9 sp1 :=
  lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  repeat first
    [ apply awr_ok_nil
    | eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat sp1); [reflexivity | ins_ewn; exact U9 | | ];
      [cbn [YP09.r_wlo YP09.r_whi]; intros ? ?; left; unfold DEC_LLVMF_STK in *; lia | ]
    | eapply awr_ok_cons_ro; [reflexivity | ] ].
Ltac ins_md := lazymatch goal with |- context [with_vm_backing (m_vm_lazy ?m) ?mt ?m] =>
  let md' := fresh "md" in set (md' := with_vm_backing (m_vm_lazy m) mt m) in *; clearbody md' end.
(* After a run: every byte outside the stack window and the spill area is the +0x3c0 memory's (KR), and presence
   only grows (GR); the run's frame_of / mem_grows are consumed. *)
Ltac ins_kupd sp1 U9 KR GR :=
  lazymatch goal with HFr : frame_of ?Ex ?rsx (mrestrict ?H ?m0) (mrestrict ?H ?m1),
                      HG : mem_grows (mrestrict ?H ?m0) (mrestrict ?H ?m1) |- _ =>
   lazymatch type of KR with forall a, _ -> _ -> aview _ _ _ a = aview _ _ ?mem a =>
   let KR2 := fresh "KR" in let GR2 := fresh "GR" in
   assert (KR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) -> aview segs H m1 a = aview segs H mem a);
   [ let a := fresh "a" in let Ha := fresh "Ha" in let HnS := fresh "HnS" in let Hk := fresh "Hk" in
     intros a Ha HnS;
     assert (Hk : forall x, in_wrange Ex rsx x -> sp1 - 4096 <= x < sp1 + 120);
     [ let x := fresh "x" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
       intros x (r & Hin & Hr);
       let rs' := eval vm_compute in rsx in change (In r rs') in Hin;
       cbn [In] in Hin;
       repeat (let Hq := fresh "Hq" in destruct Hin as [Hq | Hin];
         [subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; ins_ewn_in Hr; try rewrite U9 in Hr; lia |]);
       try contradiction
     | etransitivity; [exact (ins_kept_run Ex rsx H m0 m1 _ HFr Hk a Ha HnS) | exact (KR a Ha HnS)] ]
   | ];
   assert (GR2 : forall a, apresent H mem a -> apresent H m1 a)
     by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply (apresent_grows H m0 m1 a HG); apply GR; exact Ha);
   clear KR GR HFr HG; rename KR2 into KR; rename GR2 into GR
  end end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H end;
  try ins_md.

Ltac ins_fin H3 Hlen64 HAG HS HJ KR GR :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict _ ?msx) =>
  apply (ins_close _ _ _ _ _ _ _ _ _ _ _ _ _ Ex ssx msx _ H3 Hlen64
    ltac:(let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; ins_ewn; exact (HAG n Hn)) HS);
  [ reflexivity | reflexivity | vm_compute; reflexivity | | vm_compute; reflexivity | exact HJ | exact KR | exact GR ];
  lazymatch goal with |- U _ ?e = _ => let e' := eval vm_compute in e in change e with e' end
  end.

(* dec_a_base's fields, read by type (decompose), never by position (seg_early's e_base_pn / e_base_afn form). *)
Lemma ins_base_pn : forall cx,
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  (d_n cx = 0 /\ d_p cx = A_EMPTY) \/ (0 < d_n cx < 2 ^ 26 /\ In (d_p cx, d_n cx) (ablocks B (d_ly cx) (d_S cx))).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma ins_base_len : forall cx,
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  d_n cx = Z.of_nat (length (d_pl cx)).
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma ins_base_afn : forall cx,
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  @afn_pre rc segs B DEC_LLVMF_STK (d_ly cx) (d_S cx) (d_W cx) (d_regs cx) (d_mem cx) (d_md cx) [].
Proof. intros cx H. unfold dec_a_base, dec_lib_pre_x in H. decompose [and] H. assumption. Qed.
Lemma ins_base_n : forall cx,
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  0 <= d_n cx < 2 ^ 26.
Proof. intros cx H. destruct (ins_base_pn cx H) as [[-> _] | [Hn _]]; lia. Qed.

Lemma ins_head :
  dec_crt_cells B -> AR_laws segs B ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LCounter.dec_reac_frame_counter_cg) fx) ->
  (forall fx : YK11.FPState, @dec_leaf_at rc B (@LInspect.dec_reac_frame_inspect_cg) fx) ->
  forall (cx : dctx) (fx : YK11.FPState) ly S (W : world segs) regs mem md (res out mode nch ns : Z),
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  ins_at3c0 cx fx ly S W regs mem md res out mode nch ns ->
  SRr segs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (VAL A_TEXT + 0x3c0)) mem (YK11.seg_rom segs)) md)
    (fun W2 c2 => W2 = W /\ exists regs4 mem4 md4,
       c2 = mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (VAL A_TEXT + 0x4d0)) mem4 (YK11.seg_rom segs)) md4 /\
       ins_at4d0 cx ly S W mem res out mode nch ns regs4 mem4 md4).
Proof.
intros HCELLS LAWS LCT LIN cx fx ly S W regs mem md res out mode nch ns HB H3.
pose proof H3 as (Hfrm & HCORE & Hbl & Hres & Hout & MLE & MOK & HFR & R10 & R18 & R20 & R26 & R24 & R25 & R23 & R22
  & HMODE & HFSH & HBODY & SL32 & SL48 & SL64 & SL80 & SL88 & SL112).
pose proof HCORE as (HJ & Hfrs & R8 & R9 & Rsp & Hsp1r & Hsp1m & R3 & R4 & HSAV & HF4096 & HFal & HFpres & HFL & Hpl & Hgarr).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs' & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5 & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (sp0 := d_sp0 cx) in *. set (sp1 := d_sp1 cx) in *.
set (len := dec_a_len (d_n cx)) in *. set (body := d_body cx) in *.
assert (STKv : DEC_LLVMF_STK = 32768) by reflexivity.
pose proof (rdword_range _ _ _ (aview_byte_range _ _) SL64) as Hmode64.
set (fits := dec_a_fits0 nch ns) in *.
set (xh := ins_xh fits (nch mod 2 ^ 64) mode (nch mod 2 ^ 32) (ns mod 2 ^ 64) body).
set (E := @Eimg rc decode_listing PID (Ereg regs xh)).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs xh) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (Hu64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z) by (intros z Hz; apply unsigned_lit_small; exact Hz).
assert (E9 : ew E 9 = w64 sp1) by ereg EL 9%nat (9%bv : bv 5) R9.
assert (E10 : ew E 10 = w64 out) by ereg EL 10%nat (10%bv : bv 5) R10.
assert (E18 : ew E 18 = w64 SHADOW_OFF) by ereg EL 18%nat (18%bv : bv 5) R18.
assert (E20 : ew E 20 = w64 res) by ereg EL 20%nat (20%bv : bv 5) R20.
assert (E19 : ew E 19 = w64 (d_F cx)) by ereg EL 19%nat (19%bv : bv 5) (proj1 HFR).
assert (E3 : ew E 3 = w64 (as_gp B)) by ereg EL 3%nat (3%bv : bv 5) R3.
assert (E4 : ew E 4 = w64 (as_tp B)) by ereg EL 4%nat (4%bv : bv 5) R4.
assert (E26 : ew E 26 = w64 len) by ereg EL 26%nat (26%bv : bv 5) R26.
assert (E2 : ew E 2 = YK11.getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Rsp).
Ltac exatom EL k := rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ k).
assert (E32 : ew E 32 = w64 fits) by exatom EL 0%nat.
assert (E33 : ew E 33 = w64 (nch mod 2 ^ 64)) by exatom EL 1%nat.
assert (E34 : ew E 34 = w64 mode) by exatom EL 2%nat.
assert (E35 : ew E 35 = w64 (nch mod 2 ^ 32)) by exatom EL 3%nat.
assert (E36 : ew E 36 = w64 (ns mod 2 ^ 64)) by exatom EL 4%nat.
assert (E37 : ew E 37 = w64 (CInsp.inspect_byte body 12)) by exatom EL 5%nat.
assert (E38 : ew E 38 = w64 (CInsp.inspect_byte body 13)) by exatom EL 6%nat.
assert (E39 : ew E 39 = w64 (CInsp.inspect_byte body 14)) by exatom EL 7%nat.
assert (E40 : ew E 40 = w64 (CInsp.inspect_byte body 15)) by exatom EL 8%nat.
assert (E41 : ew E 41 = w64 (CInsp.inspect_byte body 1490)) by exatom EL 9%nat.
assert (E42 : ew E 42 = w64 (CInsp.inspect_byte body 1491)) by exatom EL 10%nat.
assert (Hinout : In (out, dec_a_olen nch ns) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
assert (Hinres : In (res, len) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinout) as (Hout16 & _ & Houtc & Houtapp & Houtpres & _ & Holen).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinres) as (Hres16 & _ & Hresc & Hresapp & Hrespres & _ & Hlen).
assert (Hn26 : 0 <= d_n cx < 2 ^ 26) by exact (ins_base_n cx HB).
assert (Hlen26 : 0 <= len < 2 ^ 26) by (unfold len, dec_a_len; lia).
pose proof (req_size_pos0 len ltac:(lia)) as Hrqlen.
pose proof (req_size_pos0 (dec_a_olen nch ns) ltac:(lia)) as Hrqolen.
assert (Hblen : Z.of_nat (length body) = len).
{ pose proof (ins_base_len cx HB) as Hnl. unfold body, len. unfold d_body. rewrite length_skipn.
  unfold dec_a_u, dec_a_len. lia. }
assert (HSL : forall off v, dec_a_slot cx (aview segs (w_H W) mem) off v ->
  0 <= v < 2 ^ 64 /\ val_mem segs (mrestrict (w_H W) mem) (sp1 + off) 8 v)
  by (intros off v Hs; split; [exact (rdword_range _ _ _ (aview_byte_range _ _) Hs) | exact (val_mem_of_rdword segs _ _ _ _ Hs)]).
assert (HS : st_ok_pi segs VAL E ss_h0
  (restrict (w_H W) (YK11.mkst regs (Z_to_bv 64 (VAL A_TEXT + 0x3c0)) mem (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_h0. apply (pa_entry_st_ok_full (PI := PID)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold ins_spill, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, Hu64 by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable segs); apply Hpres; lia|].
    destruct (HSL _ _ SL32) as [V32 M32]. destruct (HSL _ _ SL48) as [V48 M48]. destruct (HSL _ _ SL64) as [V64 M64].
    destruct (HSL _ _ SL80) as [V80 M80]. destruct (HSL _ _ SL88) as [V88 M88]. destruct (HSL _ _ SL112) as [V112 M112].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val segs E _ sp1 32 8 (SOff 32 0) fits); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M32].
    + apply (chunk_ok_val segs E _ sp1 48 8 (SOff 33 0) (nch mod 2 ^ 64)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M48].
    + apply (chunk_ok_val segs E _ sp1 64 8 (SOff 34 0) mode); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M64].
    + apply (chunk_ok_val segs E _ sp1 80 8 (SOff 35 0) (nch mod 2 ^ 32)); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M80].
    + apply (chunk_ok_val segs E _ sp1 88 8 (SOff 36 0) (ns mod 2 ^ 64)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M88].
    + apply (chunk_ok_val segs E _ sp1 112 8 (SOff 19 0) (d_F cx)); [cbn [sv_denot]; rewrite E19, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M112].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [ins_facts_h f_atoms atoms_ok]. unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E9, E10, E18, E20, E37, E38, E39, E40, E41, E42.
    rewrite (Hu64 sp1), (Hu64 out), (Hu64 res), (Hu64 SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    rewrite !Hu64 by (pose proof (ins_byte_range body 12); pose proof (ins_byte_range body 13);
      pose proof (ins_byte_range body 14); pose proof (ins_byte_range body 15);
      pose proof (ins_byte_range body 1490); pose proof (ins_byte_range body 1491); lia).
    pose proof (ins_byte_range body 12); pose proof (ins_byte_range body 13);
      pose proof (ins_byte_range body 14); pose proof (ins_byte_range body 15);
      pose proof (ins_byte_range body 1490); pose proof (ins_byte_range body 1491).
    unfold SB, SHADOW_OFF. change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pose proof (@paj_run fx rc dec_A_sink_head decode_listing PL_decode PID B LAWS) as RUN.
pose proof (@paj_run_to fx rc dec_A_sink_head decode_listing PL_decode PID B LAWS) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PID)) as BR.
assert (SHOK : sh_ok segs (SOff 18 0) [] E (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
(* +0x3c0 .. +0x3d4: the NULL check of the decode buffer (decided: out >= 4096), the arguments, the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
1: { lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
       let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end.
     eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat sp1); [reflexivity | rewrite E9; apply Hu64; lia | | apply awr_ok_nil].
     cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. left. unfold DEC_LLVMF_STK in *; lia. }
set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
assert (HKR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
{ apply (ins_kept_run E (ss_mem ss_h0) (w_H W) mem (ms_mem ms) (fun a => sp1 - 4096 <= a < sp1 + 120) HFr).
  intros a (r & Hin & Ha). unfold ss_h0 in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [ins_spill YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite E9, Hu64 in Ha by lia. lia. }
assert (HGR1 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows (w_H W) mem (ms_mem ms) a HG Ha)).
assert (Usp_ms : bv_unsigned (getr (ms_regs ms) 2) = sp1) by (rewrite Rsp2, E2; exact Rsp).
assert (Ua0_ms : bv_unsigned (getr (ms_regs ms) 10) = res) by (rewrite Ra0, E20; apply Hu64; lia).
assert (Ua1_ms : bv_unsigned (getr (ms_regs ms) 11) = len) by (rewrite Ra1, E26; apply Hu64; lia).
assert (Usp' : bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 2)) = sp1) by exact Usp_ms.
assert (Ua0' : bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 10)) = res) by exact Ua0_ms.
assert (Ua1' : bv_unsigned (getr (ms_regs ms) (Z_to_bv 5 11)) = len) by exact Ua1_ms.
pose proof (proj1 HJ) as HAR1.
assert (Hceil1 : alloc_ceiling + 32768 - 4336 <= sp1 - 4096) by (unfold DEC_LLVMF_STK in *; lia).
(* reac_frame_inspect (+0x3d4), through the shared leaf bridge *)
eapply SRr_bind.
{ eapply (dec_leafb_journal (fx := fx) B LAWS W (ms_regs ms) (ms_mem ms) DEC_LLVMF_STK sp0 [] (d_ly cx) (d_S cx)
    (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S md1 dec_ev_3c0 (sp1 - sp0)
    (pa_sigma DS_reac_frame_inspect) _ [] (fun _ => True) HJ).
  - unfold spZ. rewrite Usp_ms. lia.
  - lia.
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - rewrite Rra. apply (ret_ok_codeptr_v (PI := PID)); [lia | reflexivity].
  - rewrite Rgp, E3. reflexivity.
  - rewrite Rtp, E4. reflexivity.
  - intros a Ha. unfold LCK.in_wr in Ha. apply Exists_nil in Ha. destruct Ha.
  - intros HPRE. eapply (LIN fx ly S W (ms_regs ms) (ms_mem ms) md1 body (sp1 - 4096) HPRE).
    all: cbv zeta.
    all: rewrite ?Usp', ?Ua0', ?Ua1'.
    all: unfold CInsp.REAC_FRAME_INSPECT_FRAME.
    + eapply (dec_leafb_stk_journal B); [exact HJ | unfold DEC_LLVMF_STK; lia | lia].
    + lia.
    + intros Hl. assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
      split; [lia|].
      split.
      { apply (dec_leafb_bytes_garr8 W (ms_mem ms) res body); [|lia|lia].
        apply (ins_garr8_kept (w_H W) mem (ms_mem ms) res _ HBODY).
        intros j Hj. rewrite length_map in Hj. apply HKR1; lia. }
      split; [unfold AsanKA.off_stk; rewrite Usp'; left; lia|].
      split; [apply dec_leafb_app_stack; lia|].
      split; [apply dec_leafb_app_stack; lia|].
      split; [exact (dec_leafb_asan_cells B HCELLS ly S W (ms_mem ms) md1 HAR1)|].
      split; [unfold AsanKA.off_stk, ACells.GOT_CELL_K; rewrite Usp'; left; lia|].
      split; [unfold AsanKA.off_stk, ACells.CELL_K; rewrite Usp'; left; lia|].
      eapply (dec_leafb_addressable_block B LAWS ly S W (ms_mem ms) md1 res len res 1492 HAR1 Hinres); lia.
    + eapply (dec_leafb_rng_journal B); [exact HJ | unfold DEC_LLVMF_STK; lia | lia].
    + intros _. exact (proj1 (dec_leafb_rng_cells W)).
    + intros _. exact (proj2 (dec_leafb_rng_cells W)).
    + intros Hl. assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
      eapply (dec_leafb_rng_block B LAWS ly S W (ms_mem ms) md1 res len res 1492 HAR1 Hinres); lia.
    + intros Hl. assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
      eapply (dec_leafb_rng_shadow_block B LAWS ly S W (ms_mem ms) md1 res len res 1492 HAR1 Hinres); lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HRES & HK2 & HG2 & _).
assert (HKR2 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) ->
  aview segs (w_H W) mem2 a = aview segs (w_H W) mem a).
{ intros a Ha Hn. rewrite HK2; [apply HKR1; assumption | exact Ha | unfold spZ, ESTACK; rewrite Usp_ms; lia |].
  unfold LCK.in_wr. intros Hx. apply Exists_nil in Hx. exact Hx. }
assert (HGR2 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) by (intros a Ha; apply HG2, HGR1, Ha).
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E9, Hu64 by lia; intros a Ha.
  - apply (mbyte_of_aview segs). rewrite HK2; [reflexivity | lia | unfold spZ, ESTACK; rewrite Usp_ms; lia |].
    unfold LCK.in_wr. intros Hx. apply Exists_nil in Hx. exact Hx.
  - intros _. apply (apresent_writable segs). apply HG2. apply HGR1. apply Hpres. unfold DEC_LLVMF_STK; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite Rra.
set (E1 := havoc E 512 (map (getr regs2) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 512)%nat -> ew E1 n = ew E n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (E1_516 : ew E1 516 = w64 (CInsp.inspect_result len body)).
{ unfold E1, havoc. cbn [ew]. cbn. rewrite <- Ua1'. apply HRES. reflexivity. }
assert (U9_1 : bv_unsigned (ew E1 9) = sp1) by (rewrite E1lo by lia; rewrite E9; apply Hu64; lia).
assert (SHOK1 : sh_ok segs (SOff 18 0) [] E1 (mrestrict (w_H W) mem2)) by constructor.
clear HJ HK2 HG2 HKR1 HGR1 HAR1.
pose proof (ins_byte_range body 12) as B12. pose proof (ins_byte_range body 13) as B13.
pose proof (ins_byte_range body 14) as B14. pose proof (ins_byte_range body 15) as B15.
pose proof (ins_byte_range body 1490) as B1490. pose proof (ins_byte_range body 1491) as B1491.
assert (Ga0 : getr regs2 10 = w64 (CInsp.inspect_result len body)) by (rewrite <- Ua1'; apply HRES; reflexivity).
assert (HAG : forall n, (n < 43)%nat -> ew E1 n = ew E n) by (intros n Hn; apply E1lo; lia).
assert (Hlen64 : 0 <= len < 2 ^ 64) by lia.
assert (U20_1 : bv_unsigned (ew E1 20) = res) by (rewrite E1lo by lia; rewrite E20; apply Hu64; lia).
assert (E1_26 : ew E1 26 = w64 len) by (rewrite E1lo by lia; exact E26).
assert (E1_37 : ew E1 37 = w64 (CInsp.inspect_byte body 12)) by (rewrite E1lo by lia; exact E37).
assert (E1_38 : ew E1 38 = w64 (CInsp.inspect_byte body 13)) by (rewrite E1lo by lia; exact E38).
assert (E1_39 : ew E1 39 = w64 (CInsp.inspect_byte body 14)) by (rewrite E1lo by lia; exact E39).
assert (E1_40 : ew E1 40 = w64 (CInsp.inspect_byte body 15)) by (rewrite E1lo by lia; exact E40).
assert (E1_41 : ew E1 41 = w64 (CInsp.inspect_byte body 1490)) by (rewrite E1lo by lia; exact E41).
assert (E1_42 : ew E1 42 = w64 (CInsp.inspect_byte body 1491)) by (rewrite E1lo by lia; exact E42).
assert (Hsp47 : 0 <= sp1 < 2 ^ 47) by (unfold DEC_LLVMF_STK in *; lia).
pose proof alloc_ceiling_val as Hac.
rename HKR2 into KR. rename HGR2 into GR.
assert (U18_1 : bv_unsigned (ew E1 18) = SHADOW_OFF) by (rewrite E1lo by lia; rewrite E18; apply Hu64; unfold SHADOW_OFF; lia).
Ltac ins_obl1 LAWS HJ Hinres U18 U20 res len :=
  lazymatch goal with |- range_addressable _ (U ?E (SOff 18 0)) (U ?E (SOff 20 ?k)) ?n =>
    rewrite (U_SOff E 18 0), (U_SOff E 20 k); ins_ewn; rewrite U18, U20, Z.add_0_r;
    rewrite !zcanon_id by (unfold M64, SHADOW_OFF in *; lia);
    exact (range_addressable_of_block segs B LAWS _ _ _ _ _ res len (res + k) n (proj1 HJ) Hinres ltac:(lia) ltac:(lia))
  end.
destruct (CInsp.inspect_wf len body) eqn:Hwf.
2: {
assert (HR0 : CInsp.inspect_result len body = 0) by (unfold CInsp.inspect_result; rewrite Hwf; reflexivity).
apply (st_ok_pi_pin_reg' _ _ _ 10%bv 0) in HS; [| change (getr regs2 10 = Z_to_bv 64 0); rewrite Ga0, HR0; reflexivity | reflexivity].
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
1: ins_awr U9_1 sp1.
ins_kupd sp1 U9_1 KR GR.
psrr_branch_tok RUN BR HS SHOK1 Bspan.
- (* s10 <> 1492: the length check fails, +0x468 *)
  paj_run_to_tok RUNTO HS HJ2 SHOK1 Bspan 0x4d0.
  1: ins_awr U9_1 sp1.
  ins_kupd sp1 U9_1 KR GR.
  ins_fin H3 Hlen64 HAG HS HJ2 KR GR.
  rewrite (Hwf : CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) = false). rewrite U_lit by lia. reflexivity.
- (* s10 = 1492 *)
  assert (Hl : len = 1492).
  { rewrite branch_ne_U in Hc. rewrite (U_atom E1 26 len) in Hc by (try (rewrite E1lo by lia; exact E26); lia).
    rewrite U_lit in Hc by lia. apply negb_false_iff in Hc. apply Z.eqb_eq in Hc. exact Hc. }
  assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?H ?msx) =>
    pose proof (ins_add_res_ok Ex ssx msx H mem res sp1 body HS ltac:(vm_compute; reflexivity) U20_1 U9_1
      E1_37 E1_38 E1_39 E1_40 E1_41 E1_42 ltac:(lia) HBODY) as HSr end.
  specialize (HSr ltac:(intros a Ha; apply KR; lia) Hres ltac:(lia) ltac:(lia)).
  clear HS. rename HSr into HS.
  paj_run_tok RUN HS HJ2 SHOK1 Bspan.
  all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
  all: try (ins_awr U9_1 sp1).
  ins_kupd sp1 U9_1 KR GR.
  psrr_branch_tok RUN BR HS SHOK1 Bspan.
  { (* byte 12 <> 0x88 *) paj_run_to_tok RUNTO HS HJ2 SHOK1 Bspan 0x4d0.
    all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
    all: try (ins_awr U9_1 sp1).
    ins_kupd sp1 U9_1 KR GR.
    ins_fin H3 Hlen64 HAG HS HJ2 KR GR.
    rewrite (Hwf : CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) = false). rewrite U_lit by lia. reflexivity. }
  paj_run_tok RUN HS HJ2 SHOK1 Bspan.
  all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
  all: try (ins_awr U9_1 sp1).
  ins_kupd sp1 U9_1 KR GR.
  psrr_branch_tok RUN BR HS SHOK1 Bspan.
  { (* byte 13 <> 0x19 *) paj_run_to_tok RUNTO HS HJ2 SHOK1 Bspan 0x4d0.
    all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
    all: try (ins_awr U9_1 sp1).
    ins_kupd sp1 U9_1 KR GR.
    ins_fin H3 Hlen64 HAG HS HJ2 KR GR.
    rewrite (Hwf : CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) = false). rewrite U_lit by lia. reflexivity. }
  paj_run_tok RUN HS HJ2 SHOK1 Bspan.
  all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
  all: try (ins_awr U9_1 sp1).
  ins_kupd sp1 U9_1 KR GR.
  psrr_branch_tok RUN BR HS SHOK1 Bspan.
  { (* byte 1490 <> 0xc2 *) paj_run_to_tok RUNTO HS HJ2 SHOK1 Bspan 0x4d0.
    all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
    all: try (ins_awr U9_1 sp1).
    ins_kupd sp1 U9_1 KR GR.
    ins_fin H3 Hlen64 HAG HS HJ2 KR GR.
    rewrite (Hwf : CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) = false). rewrite U_lit by lia. reflexivity. }
  paj_run_tok RUN HS HJ2 SHOK1 Bspan.
  all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
  all: try (ins_awr U9_1 sp1).
  ins_kupd sp1 U9_1 KR GR.
  match goal with Hc' : branch_taken BC_NE (sv_denot _ (SOff 37 0)) _ = false |- _ =>
    pose proof (ins_bne_false _ 37 136 _ Hc' ltac:(ins_ewn; exact E1_37) ltac:(lia) ltac:(lia)) as B12e end.
  match goal with Hc' : branch_taken BC_NE (sv_denot _ (SOff 38 0)) _ = false |- _ =>
    pose proof (ins_bne_false _ 38 25 _ Hc' ltac:(ins_ewn; exact E1_38) ltac:(lia) ltac:(lia)) as B13e end.
  match goal with Hc' : branch_taken BC_NE (sv_denot _ (SOff 41 0)) _ = false |- _ =>
    pose proof (ins_bne_false _ 41 194 _ Hc' ltac:(ins_ewn; exact E1_41) ltac:(lia) ltac:(lia)) as B1490e end.
  assert (B1491ne : (CInsp.inspect_byte body 1491 =? 234) = false).
  { unfold CInsp.inspect_wf in Hwf. rewrite Hl, B12e, B13e, B1490e in Hwf. exact Hwf. }
  psrr_branch_tok RUN BR HS SHOK1 Bspan.
  { (* the abort edge +0x474 (a1 = 0 against s10): refuted, s10 = 0 too *)
    exfalso.
    match goal with Hc' : branch_taken BC_NE (sv_denot ?Ex _) (sv_denot _ (SAlu ALU_SLTU (SOff 42 (-234)) (SLit 1))) = true |- _ =>
      rewrite branch_ne_U, (ins_sltu_val Ex (CInsp.inspect_byte body 1491) ltac:(ins_ewn; exact E1_42) B1491), B1491ne,
        U_lit in Hc' by lia; discriminate Hc' end. }
  paj_run_to_tok RUNTO HS HJ2 SHOK1 Bspan 0x4d0.
  all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
  all: try (ins_awr U9_1 sp1).
  ins_kupd sp1 U9_1 KR GR.
  ins_fin H3 Hlen64 HAG HS HJ2 KR GR.
  rewrite (Hwf : CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) = false).
  lazymatch goal with |- U ?Ex _ = _ =>
    rewrite (ins_sltu_val Ex (CInsp.inspect_byte body 1491) ltac:(ins_ewn; exact E1_42) B1491), B1491ne; reflexivity end.
}
(* wellformed: the five checks pass and s10 = 1 *)
assert (HW := Hwf). unfold CInsp.inspect_wf in HW. rewrite !andb_true_iff in HW.
destruct HW as [[[[Hl B12e] B13e] B1490e] B1491e].
apply Z.eqb_eq in Hl. apply Z.eqb_eq in B12e. apply Z.eqb_eq in B13e. apply Z.eqb_eq in B1490e. apply Z.eqb_eq in B1491e.
assert (Hcnt : 0 <= CInsp.inspect_counter body < 2 ^ 16) by (unfold CInsp.inspect_counter; lia).
assert (HR1 : CInsp.inspect_result len body = 2 ^ 32 + CInsp.inspect_counter body)
  by (unfold CInsp.inspect_result; rewrite Hwf; reflexivity).
assert (U516 : forall Ex, (forall n, (n < 528)%nat -> ew Ex n = ew E1 n) -> U Ex (SOff 516 0) = 2 ^ 32 + CInsp.inspect_counter body).
{ intros Ex HEx. apply U_atom; [rewrite HEx by lia; rewrite E1_516, HR1; reflexivity | lia]. }
assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?H ?msx) =>
  pose proof (ins_add_res_ok Ex ssx msx H mem res sp1 body HS ltac:(vm_compute; reflexivity) U20_1 U9_1
    E1_37 E1_38 E1_39 E1_40 E1_41 E1_42 ltac:(lia) HBODY) as HSr end.
specialize (HSr ltac:(intros a Ha; apply KR; lia) Hres ltac:(lia) ltac:(lia)).
clear HS. rename HSr into HS.
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
psrr_branch_tok RUN BR HS SHOK1 Bspan.
{ exfalso. match goal with Hc' : branch_taken BC_NE (sv_denot _ (SOff 26 0)) (sv_denot _ (SLit 1492)) = true |- _ =>
    exact (ins_bne_true _ 26 1492 len Hc' ltac:(ins_ewn; exact E1_26) ltac:(lia) ltac:(lia) Hl) end. }
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
psrr_branch_tok RUN BR HS SHOK1 Bspan.
{ exfalso. match goal with Hc' : branch_taken BC_NE (sv_denot _ (SOff 37 0)) (sv_denot _ (SLit 136)) = true |- _ =>
    exact (ins_bne_true _ 37 136 _ Hc' ltac:(ins_ewn; exact E1_37) ltac:(lia) ltac:(lia) B12e) end. }
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
psrr_branch_tok RUN BR HS SHOK1 Bspan.
{ exfalso. match goal with Hc' : branch_taken BC_NE (sv_denot _ (SOff 38 0)) (sv_denot _ (SLit 25)) = true |- _ =>
    exact (ins_bne_true _ 38 25 _ Hc' ltac:(ins_ewn; exact E1_38) ltac:(lia) ltac:(lia) B13e) end. }
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
psrr_branch_tok RUN BR HS SHOK1 Bspan.
{ exfalso. match goal with Hc' : branch_taken BC_NE (sv_denot _ (SOff 41 0)) (sv_denot _ (SLit 194)) = true |- _ =>
    exact (ins_bne_true _ 41 194 _ Hc' ltac:(ins_ewn; exact E1_41) ltac:(lia) ltac:(lia) B1490e) end. }
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
psrr_branch_tok RUN BR HS SHOK1 Bspan.
{ (* the abort edge +0x474: refuted, the high word is 1 = s10 *)
  exfalso. match goal with Hc' : branch_taken BC_NE (sv_denot ?Ex (SAlu ALU_SRL (SOff 516 0) (SLit 32))) (sv_denot _ (SAlu ALU_SLTU (SOff 42 (-234)) (SLit 1))) = true |- _ =>
    rewrite branch_ne_U, (ins_srl32 Ex (SOff 516 0) (CInsp.inspect_counter body)
      (U516 Ex ltac:(let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; ins_ewn; reflexivity)) Hcnt),
      (ins_sltu_val Ex (CInsp.inspect_byte body 1491) ltac:(ins_ewn; exact E1_42) B1491), B1491e in Hc';
    cbv in Hc'; discriminate Hc' end. }
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
Ltac ins_U516 U516 := let n := fresh "n" in let Hn := fresh "Hn" in
  lazymatch goal with |- U ?Ex _ = _ => apply (U516 Ex); intros n Hn; ins_ewn; reflexivity end.
psrr_branch_tok RUN BR HS SHOK1 Bspan.
{ (* +0x478 taken (the high word is 0): refuted *)
  exfalso. lazymatch goal with Hc' : branch_taken BC_EQ (sv_denot ?Ex (SAlu ALU_SRL (SOff 516 0) (SLit 32))) _ = true |- _ =>
    rewrite branch_eq_U in Hc';
    rewrite (ins_srl32 Ex (SOff 516 0) (CInsp.inspect_counter body)
      (U516 Ex ltac:(let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; ins_ewn; reflexivity)) Hcnt) in Hc';
    rewrite (U_lit Ex 0) in Hc' by lia; discriminate Hc' end. }
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
psrr_branch_tok RUN BR HS SHOK1 Bspan.
{ (* the abort edge +0x4c0: refuted, the inspect result's low half is the counter field s2 *)
  exfalso. lazymatch goal with Hc' : branch_taken BC_NE (sv_denot ?Ex (SAlu ALU_SRL (SAlu ALU_SLL (SOff 516 0) (SLit 48)) (SLit 48))) _ = true |- _ =>
    rewrite branch_ne_U in Hc';
    rewrite (ins_lo16 Ex (SOff 516 0) (CInsp.inspect_counter body)
      (U516 Ex ltac:(let n := fresh "n" in let Hn := fresh "Hn" in intros n Hn; ins_ewn; reflexivity)) Hcnt) in Hc';
    rewrite (ins_or16 Ex (SOff 40 0) (SOff 39 0) (CInsp.inspect_byte body 15) (CInsp.inspect_byte body 14)
      ltac:(apply U_atom; [ins_ewn; exact E1_40 | lia]) ltac:(apply U_atom; [ins_ewn; exact E1_39 | lia]) B15 B14) in Hc';
    unfold CInsp.inspect_counter in Hc'; rewrite Z.eqb_refl in Hc'; discriminate Hc' end. }
paj_run_tok RUN HS HJ2 SHOK1 Bspan.
all: try (ins_obl1 LAWS HJ2 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
pmkst HS.
prreg HS (10%bv : bv 5) Rc0. prreg HS (1%bv : bv 5) Rcra. prreg HS (2%bv : bv 5) Rcsp.
prreg HS (3%bv : bv 5) Rcgp. prreg HS (4%bv : bv 5) Rctp.
lazymatch type of Rc0 with getr (ms_regs ?msx) _ = _ => rename msx into msc end.
assert (Uc0 : bv_unsigned (getr (ms_regs msc) 10) = res) by (rewrite Rc0; ins_ewn; exact U20_1).
assert (Ucsp : bv_unsigned (getr (ms_regs msc) 2) = sp1) by (rewrite Rcsp; ins_ewn; rewrite E1lo by lia; rewrite E2; exact Rsp).
assert (Uc0' : bv_unsigned (getr (ms_regs msc) (Z_to_bv 5 10)) = res) by exact Uc0.
assert (Ucsp' : bv_unsigned (getr (ms_regs msc) (Z_to_bv 5 2)) = sp1) by exact Ucsp.
pose proof (proj1 HJ2) as HARc.
(* reac_frame_counter (+0x4c8), through the shared leaf bridge *)
eapply SRr_bind.
{ eapply (dec_leafb_journal (fx := fx) B LAWS W (ms_regs msc) (ms_mem msc) DEC_LLVMF_STK sp0 [] (d_ly cx) (d_S cx)
    (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S _ dec_ev_3c0 (sp1 - sp0)
    (pa_sigma DS_reac_frame_counter) _ [] (fun _ => True) HJ2).
  - unfold spZ. rewrite Ucsp. lia.
  - lia.
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - rewrite Rcra. apply (ret_ok_codeptr_v (PI := PID)); [lia | reflexivity].
  - rewrite Rcgp. ins_ewn. rewrite E1lo by lia. exact E3.
  - rewrite Rctp. ins_ewn. rewrite E1lo by lia. exact E4.
  - intros a Ha. unfold LCK.in_wr in Ha. apply Exists_nil in Ha. destruct Ha.
  - intros HPRE. eapply (LCT fx ly S W (ms_regs msc) (ms_mem msc) _ body (sp1 - 4096) HPRE).
    all: cbv zeta.
    all: rewrite ?Ucsp', ?Uc0'.
    all: unfold CCnt.REAC_FRAME_COUNTER_FRAME.
    + lia.
    + apply (dec_leafb_bytes_garr8 W (ms_mem msc) res body); [|lia|lia].
      apply (ins_garr8_kept (w_H W) mem (ms_mem msc) res _ HBODY).
      intros j Hj. rewrite length_map in Hj. apply KR; lia.
    + eapply (dec_leafb_stk_journal B); [exact HJ2 | unfold DEC_LLVMF_STK; lia | lia].
    + lia.
    + unfold AsanKA.off_stk; rewrite Ucsp'; left; lia.
    + apply dec_leafb_app_stack; lia.
    + apply dec_leafb_app_stack; lia.
    + exact (dec_leafb_asan_cells B HCELLS ly S W (ms_mem msc) _ HARc).
    + unfold AsanKA.off_stk, ACells.GOT_CELL_K; rewrite Ucsp'; left; lia.
    + unfold AsanKA.off_stk, ACells.CELL_K; rewrite Ucsp'; left; lia.
    + eapply (dec_leafb_addressable_block B LAWS ly S W (ms_mem msc) _ res len (res + 14) 2 HARc Hinres); lia.
    + eapply (dec_leafb_rng_journal B); [exact HJ2 | unfold DEC_LLVMF_STK; lia | lia].
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + eapply (dec_leafb_rng_block B LAWS ly S W (ms_mem msc) _ res len (res + 14) 2 HARc Hinres); lia.
    + eapply (dec_leafb_rng_shadow_block B LAWS ly S W (ms_mem msc) _ res len (res + 14) 2 HARc Hinres); lia. }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & mdc3 & -> & HJ3 & HP3 & HRES3 & HK3 & HG3 & _).
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) ->
  aview segs (w_H W) mem3 a = aview segs (w_H W) mem a).
{ intros a Ha Hn. rewrite HK3; [apply KR; assumption | exact Ha | unfold spZ, ESTACK; rewrite Ucsp; lia |].
  unfold LCK.in_wr. intros Hx. apply Exists_nil in Hx. exact Hx. }
assert (GR3 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem3 a) by (intros a Ha; apply HG3, GR, Ha).
jafter_call_keep_hi HS 544%nat regs3 (mrestrict (w_H W) mem3) HP3 [1%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; ins_ewn; rewrite U9_1; intros a Ha.
  - apply (mbyte_of_aview segs). rewrite HK3; [reflexivity | lia | unfold spZ, ESTACK; rewrite Ucsp; lia |].
    unfold LCK.in_wr. intros Hx. apply Exists_nil in Hx. exact Hx.
  - intros _. apply (apresent_writable segs). apply HG3. apply GR. apply Hpres. unfold DEC_LLVMF_STK; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
rewrite Rcra.
clear KR GR HK3 HG3. rename KR3 into KR. rename GR3 into GR.
lazymatch type of HS with st_ok_pi _ _ (havoc ?Ec ?k ?ws) _ _ =>
  assert (HEIc2 : img_env VAL A_LIM (havoc Ec k ws)) by (apply img_env_havoc_hi; [assumption | cbv; lia]);
  assert (Ec2_548 : ew (havoc Ec k ws) 548 = w64 (CCnt.counter_result body))
    by (unfold havoc; cbn [ew]; cbn; apply HRES3; reflexivity);
  assert (SHOK2 : sh_ok segs (SOff 18 0) [] (havoc Ec k ws) (mrestrict (w_H W) mem3)) by constructor end.
paj_run_tok RUN HS HJ3 SHOK2 Bspan.
all: try (ins_obl1 LAWS HJ3 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
psrr_branch_tok RUN BR HS SHOK2 Bspan.
{ (* the abort edge +0x4cc: refuted, reac_frame_counter returns the field s2 holds *)
  exfalso. lazymatch goal with Hc' : branch_taken BC_NE (sv_denot ?Ex (SAlu ALU_OR (SAlu ALU_SLL (SOff 40 0) (SLit 8)) (SOff 39 0))) (sv_denot _ (SOff 548 0)) = true |- _ =>
    rewrite branch_ne_U in Hc';
    rewrite (ins_or16 Ex (SOff 40 0) (SOff 39 0) (CInsp.inspect_byte body 15) (CInsp.inspect_byte body 14)
      ltac:(apply U_atom; [ins_ewn; exact E1_40 | lia]) ltac:(apply U_atom; [ins_ewn; exact E1_39 | lia]) B15 B14) in Hc';
    rewrite (U_atom Ex 548 (CCnt.counter_result body) ltac:(ins_ewn; exact Ec2_548)
      ltac:(unfold CCnt.counter_result, CCnt.counter_byte; pose proof B14; pose proof B15; unfold CInsp.inspect_byte in *; lia)) in Hc';
    unfold CCnt.counter_result, CCnt.counter_byte, CInsp.inspect_byte in Hc'; rewrite Z.eqb_refl in Hc'; discriminate Hc' end. }
paj_run_to_tok RUNTO HS HJ3 SHOK2 Bspan 0x4d0.
all: try (ins_obl1 LAWS HJ3 Hinres U18_1 U20_1 res len).
all: try (ins_awr U9_1 sp1).
ins_kupd sp1 U9_1 KR GR.
ins_fin H3 Hlen64 HAG HS HJ3 KR GR.
rewrite (Hwf : CInsp.inspect_wf (dec_a_len (d_n cx)) (d_body cx) = true).
lazymatch goal with |- U ?Ex _ = _ =>
  rewrite (ins_sltu_val Ex (CInsp.inspect_byte body 1491) ltac:(ins_ewn; exact E1_42) B1491), B1491e; reflexivity end.
Qed.
Definition ins_spill4 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 120 40 80
    [YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0));
     YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 38 0));
     YP09.mkChunk 64 (CVal 8 (SOff 34 0)); YP09.mkChunk 80 (CVal 8 (SOff 35 0));
     YP09.mkChunk 88 (CVal 8 (SOff 36 0)); YP09.mkChunk 112 (CVal 8 (SOff 19 0))].
Definition ins_facts4 : facts :=
  mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (20%nat, YC4b.PTR 4);
           (22%nat, YC4b.PTR 4); (37%nat, mkAF SB SB 0)] [] [].
Definition ss_ins4 : sstate := mkSS 0x4d0 sr_atoms [ins_spill4] None ins_facts4.
Definition ins_extra4 (fits nch64 mode nch32 ns64 len : Z) : list word :=
  [Z_to_bv 64 fits; Z_to_bv 64 nch64; Z_to_bv 64 mode; Z_to_bv 64 nch32; Z_to_bv 64 ns64; Z_to_bv 64 SHADOW_OFF;
   Z_to_bv 64 len].

(* The spill region of the symbolic state at the `jal reac_decode` (+0x4f8): ins_spill4 with the slot 72(s1) the run
   wrote at +0x4f0 (= out, atom 22). *)
Definition ins_t_spill5 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 32 120 40 80
    [YP09.mkChunk 72 (CVal 8 (SOff 22 0)); YP09.mkChunk 32 (CVal 8 (SOff 32 0)); YP09.mkChunk 40 (CVal 8 (SOff 37 0));
     YP09.mkChunk 48 (CVal 8 (SOff 33 0)); YP09.mkChunk 56 (CVal 8 (SOff 38 0)); YP09.mkChunk 64 (CVal 8 (SOff 34 0));
     YP09.mkChunk 80 (CVal 8 (SOff 35 0)); YP09.mkChunk 88 (CVal 8 (SOff 36 0)); YP09.mkChunk 112 (CVal 8 (SOff 19 0))].

(* ins_t_rdword_of_val_mem, ins_t_cell8, ins_t_rows and ins_t_saved_at_range are copied from
   a working branch f0f023a4fb8,
   proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_crt1.v:522-523, :607-700 (prefix c1_ renamed ins_t_);
   ins_t_fsh_kept is that branch's LLVMFuzzerTestOneInput_seg_up.v:362-371 up_fsh_kept. ins_t_mode_re started as that
   file's c1_mode_re; since the c-alpha amendment (a Theorem Labs lane cc88c36cf66) it reads no table word from dec_crt_cells. *)
Lemma ins_t_rdword_of_val_mem : forall H mem a v,
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

Lemma ins_t_cell8 : forall ly S (W : world segs) mem md a v,
  @AR rc segs B ly S W mem md -> In (z8 (ANum a) v) (as_const B ly) -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) a = Some v.
Proof.
intros ly S W mem md a v HAR Hin Hv. destruct HAR as [HARm _].
pose proof (am_const _ _ _ _ HARm) as HC. rewrite Forall_forall in HC.
exact (rdword_cell B ly _ a v Hv (HC _ Hin)).
Qed.
(* The one-byte constant cells (the tables' value-4 shadow rows of dec_crt_cells). *)
Lemma ins_t_cell1 : forall ly S (W : world segs) mem md a v,
  @AR rc segs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) ->
  aview segs (w_H W) mem a = Some (le_byte v 1 0).
Proof.
intros ly S W mem md a v HAR Hin. destruct HAR as [HARm _].
pose proof (am_const _ _ _ _ HARm) as HC. rewrite Forall_forall in HC.
pose proof (HC _ Hin) as H0.
change (forall k, (k < 1)%nat -> aview segs (w_H W) mem (a + Z.of_nat k) = Some (le_byte v 1 k)) in H0.
specialize (H0 0%nat ltac:(lia)). rewrite Nat2Z.inj_0, Z.add_0_r in H0. exact H0.
Qed.

Ltac ins_t_rows HCELLS ly :=
  let H := fresh "HC" in pose proof (HCELLS ly) as H;
  repeat match type of H with _ /\ _ => let H1 := fresh "Row" in destruct H as [H1 H] end.

(* dec_a_mode_ok at another state of the same walk. The pointer cell is a constant cell of dec_crt_cells, read again
   at the new state (the z8 rows decode_obj 4 / 5 / 6); the two geometry words at mode + 4 and mode + 8 are bytes the
   caller shows unchanged. That covers the frame's 12-byte local and the three REAC_MODE tables alike: since the
   c-alpha amendment the table words are not constant cells, and this segment carries them from the +0x3c0 memory
   (where llvm_a_st_3c0's dec_a_mode_ok reads them) by its own kept-byte facts: a table lies in the image, which no
   stack window and no allocator block of the segment touches (ins_t_tab_img). *)
Lemma ins_t_mode_re : forall cx (W W' : world segs) mem mem' ly S md ly' S' md' mode nch ns,
  dec_crt_cells B ->
  @AR rc segs B ly S W mem md -> @AR rc segs B ly' S' W' mem' md' ->
  dec_a_mode_ok cx W mem mode nch ns ->
  (forall k, 0 <= k < 8 -> aview segs (w_H W') mem' (mode + 4 + k) = aview segs (w_H W) mem (mode + 4 + k)) ->
  dec_a_mode_ok cx W' mem' mode nch ns.
Proof.
intros cx W W' mem mem' ly S md ly' S' md' mode nch ns HCELLS HAR HAR' (Hmc & Hnch & Hns & Hv4 & Hv8) HF.
assert (VK : forall a (n : nat) v, (forall k, 0 <= k < Z.of_nat n ->
   aview segs (w_H W') mem' (a + k) = aview segs (w_H W) mem (a + k)) ->
   val_mem segs (mrestrict (w_H W) mem) a n v -> val_mem segs (mrestrict (w_H W') mem') a n v).
{ intros a n v Hk Hv j Hj. rewrite (mbyte_of_aview segs (w_H W) (w_H W') mem mem' (a + Z.of_nat j)).
  - exact (Hv j Hj).
  - apply Hk. lia. }
assert (PC : forall c t, In (z8 (ANum c) t) (as_const B ly) -> In (z8 (ANum c) t) (as_const B ly') ->
   0 <= t < 2 ^ 64 -> rdword (aview segs (w_H W) mem) c = Some mode -> rdword (aview segs (w_H W') mem') c = Some mode).
{ intros c t P0 P0' Ht Hc. rewrite (ins_t_cell8 _ _ _ _ _ _ _ HAR P0 Ht) in Hc. injection Hc as <-.
  exact (ins_t_cell8 _ _ _ _ _ _ _ HAR' P0' Ht). }
split.
{ ins_t_rows HCELLS ly. ins_t_rows HCELLS ly'.
  destruct Hmc as [Hc | [Hc | [Hc | Hc]]].
  - left. exact (PC (decode_obj 4%nat) 0x20d40 ltac:(assumption) ltac:(assumption) ltac:(lia) Hc).
  - right; left. exact (PC (decode_obj 5%nat) 0x20d80 ltac:(assumption) ltac:(assumption) ltac:(lia) Hc).
  - right; right; left. exact (PC (decode_obj 6%nat) 0x20d60 ltac:(assumption) ltac:(assumption) ltac:(lia) Hc).
  - right; right; right. exact Hc. }
split; [exact Hnch|]. split; [exact Hns|].
split.
- apply (VK _ 4%nat); [|exact Hv4]. intros k Hk. change (Z.of_nat 4) with 4 in Hk. apply HF. lia.
- apply (VK _ 4%nat); [|exact Hv8]. intros k Hk. change (Z.of_nat 4) with 4 in Hk.
  replace (mode + 8 + k) with (mode + 4 + (4 + k)) by lia. apply HF. lia.
Qed.

Lemma ins_t_fsh_kept : forall (cx : dctx) (r r' : reader) (b4 b5 : Z),
  (forall i, 0 <= i < 8 -> r' (d_SH cx + i) = r (d_SH cx + i)) ->
  dec_a_fsh cx r b4 b5 -> dec_a_fsh cx r' b4 b5.
Proof.
intros cx r r' b4 b5 HK (F1 & F4 & F5 & F6). unfold dec_a_fsh.
split; [intros i Hi; rewrite HK by lia; apply F1, Hi|].
split; [rewrite HK by lia; exact F4|].
split; [rewrite HK by lia; exact F5|].
intros i Hi; rewrite HK by lia; apply F6, Hi.
Qed.

Lemma ins_t_saved_at_range : Forall (fun o : Z * Z => 8 <= fst o <= 104) dec_a_saved_at.
Proof. unfold dec_a_saved_at. repeat constructor; cbn [fst]; lia. Qed.

(* dec_a_core at a later state of the same allocator state: the journal is given, the five registers it names hold,
   and the bytes it reads (the saved words, the fake frame, the payload) are kept. After seg_crt1's c1_core_kept
   (LLVMFuzzerTestOneInput_seg_crt1.v:527-553), with the registers given as values. *)
Lemma ins_t_core_kept : forall cx ly' S' (W : world segs) regs regs' mem mem' md md' k k',
  dec_a_core B cx ly' S' W regs mem md k ->
  @ajournal rc tfib_sink_head segs B DEC_LLVMF_STK (d_sp0 cx) [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly' S' W mem' md' k' ->
  YK11.getr regs' 8 = w64 (d_sp0 cx) -> YK11.getr regs' 9 = w64 (d_sp1 cx) -> spZ regs' = d_sp1 cx ->
  YK11.getr regs' 3 = w64 (as_gp B) -> YK11.getr regs' 4 = w64 (as_tp B) ->
  (forall a, (d_sp0 cx - 104 <= a < d_sp0 cx) \/ (d_F cx <= a < d_F cx + 64) \/
     (d_p cx <= a < d_p cx + Z.of_nat (length (d_pl cx))) -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) ->
  dec_a_core B cx ly' S' W regs' mem' md' k'.
Proof.
intros cx ly' S' W regs regs' mem mem' md md' k k'
  (HJ & Hfr & _ & _ & _ & Hsp01 & Hal & _ & _ & Hsv & HF4 & HFal & HFp & HFl & Hpin & Hpay) HJ' H8 H9 Hsp Hgp Htp HK HG.
unfold dec_a_core.
refine (conj HJ' (conj Hfr (conj H8 (conj H9 (conj Hsp (conj Hsp01 (conj Hal (conj Hgp (conj Htp (conj _
  (conj HF4 (conj HFal (conj _ (conj _ (conj Hpin _))))))))))))))).
- unfold dec_a_saved in *. rewrite Forall_forall in Hsv |- *. intros o Ho.
  pose proof (proj1 (Forall_forall _ _) ins_t_saved_at_range o Ho) as Ro. cbv beta in Ro.
  refine (ins_rdword_kept (w_H W) mem mem' _ _ (Hsv o Ho) _). intros kk Hkk. apply HK. left. lia.
- intros a Ha. apply HG. exact (HFp a Ha).
- refine (ins_rdword_kept (w_H W) mem mem' _ _ HFl _). intros kk Hkk. apply HK. right; left. lia.
- refine (ins_garr8_kept (w_H W) mem mem' _ _ Hpay _). intros kk Hkk. rewrite length_map in Hkk. apply HK. right; right. lia.
Qed.

(* The mode is one of the three tables the pointer cells of dec_crt_cells name, or the frame's 12-byte local. *)
Lemma ins_t_mode_cases : forall cx ly S (W : world segs) mem md mode nch ns,
  dec_crt_cells B -> @AR rc segs B ly S W mem md -> dec_a_mode_ok cx W mem mode nch ns ->
  (mode = 0x20d40 \/ mode = 0x20d80 \/ mode = 0x20d60) \/ mode = d_F cx + 32.
Proof.
intros cx ly S W mem md mode nch ns HCELLS HAR (Hmc & _).
ins_t_rows HCELLS ly.
destruct Hmc as [Hc | [Hc | [Hc | Hc]]]; [left; left | left; right; left | left; right; right | right; exact Hc].
- rewrite (ins_t_cell8 ly S W mem md (decode_obj 4) 0x20d40 HAR ltac:(assumption) ltac:(lia)) in Hc.
  injection Hc as <-. reflexivity.
- rewrite (ins_t_cell8 ly S W mem md (decode_obj 5) 0x20d80 HAR ltac:(assumption) ltac:(lia)) in Hc.
  injection Hc as <-. reflexivity.
- rewrite (ins_t_cell8 ly S W mem md (decode_obj 6) 0x20d60 HAR ltac:(assumption) ltac:(lia)) in Hc.
  injection Hc as <-. reflexivity.
Qed.

(* THE one read of a table's shadow-zero granule in this file (the granule at the table's base, 0x20d40 / 0x20d80 /
   0x20d60): the dec_tab_zshadow_at conjunct of dec_crt_cells (a Theorem Labs lane e175e3e033a), picked by statement, read at
   this state by the statement's own dec_tab_zshadow_rd (AR's am_zshadow over that as_zero_shadow range). *)
Lemma ins_t_tab_sh0 : forall ly S (W : world segs) mem md t,
  dec_crt_cells B -> @AR rc segs B ly S W mem md -> (t = 0x20d40 \/ t = 0x20d80 \/ t = 0x20d60) ->
  aview segs (w_H W) mem (SHADOW_OFF + t / 8) = Some 0.
Proof.
intros ly S W mem md t HCELLS HAR Ht.
ins_t_rows HCELLS ly.
destruct Ht as [-> | [-> | ->]].
- change (SHADOW_OFF + 0x20d40 / 8) with (ACells.shadow_addr 0x20d40).
  exact (dec_tab_zshadow_rd B ly S W mem md 0x20d40 HAR eq_refl ltac:(assumption)).
- change (SHADOW_OFF + 0x20d80 / 8) with (ACells.shadow_addr 0x20d80).
  exact (dec_tab_zshadow_rd B ly S W mem md 0x20d80 HAR eq_refl ltac:(assumption)).
- change (SHADOW_OFF + 0x20d60 / 8) with (ACells.shadow_addr 0x20d60).
  exact (dec_tab_zshadow_rd B ly S W mem md 0x20d60 HAR eq_refl ltac:(assumption)).
Qed.

(* A table's two 4-byte fields are addressable: its first granule's shadow is 0 (ins_t_tab_sh0) and the second
   granule's is 4 (the value-4 z1 rows of dec_crt_cells, picked by statement). *)
Lemma ins_t_tab_ra : forall ly S (W : world segs) mem md t,
  dec_crt_cells B -> @AR rc segs B ly S W mem md -> (t = 0x20d40 \/ t = 0x20d80 \/ t = 0x20d60) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (t + 4) 8.
Proof.
intros ly S W mem md t HCELLS HAR Ht.
assert (Z0 : aview segs (w_H W) mem (SHADOW_OFF + t / 8) = Some 0 /\
             aview segs (w_H W) mem (SHADOW_OFF + (t + 8) / 8) = Some 4).
{ split; [exact (ins_t_tab_sh0 ly S W mem md t HCELLS HAR Ht)|].
  ins_t_rows HCELLS ly.
  destruct Ht as [-> | [-> | ->]].
  - change (SHADOW_OFF + (0x20d40 + 8) / 8) with (ACells.shadow_addr 0x20d48).
    exact (ins_t_cell1 ly S W mem md (ACells.shadow_addr 0x20d48) 4 HAR ltac:(assumption)).
  - change (SHADOW_OFF + (0x20d80 + 8) / 8) with (ACells.shadow_addr 0x20d88).
    exact (ins_t_cell1 ly S W mem md (ACells.shadow_addr 0x20d88) 4 HAR ltac:(assumption)).
  - change (SHADOW_OFF + (0x20d60 + 8) / 8) with (ACells.shadow_addr 0x20d68).
    exact (ins_t_cell1 ly S W mem md (ACells.shadow_addr 0x20d68) 4 HAR ltac:(assumption)). }
intros x Hx. unfold shadow_of_addr, saddr_ok.
destruct (Z_lt_dec x (t + 8)).
- exists 0. split; [|left; reflexivity].
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + t / 8) by (destruct Ht as [-> | [-> | ->]]; lia). exact (proj1 Z0).
- exists 4. split; [|right; destruct Ht as [-> | [-> | ->]]; lia].
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + (t + 8) / 8) by (destruct Ht as [-> | [-> | ->]]; lia).
  exact (proj2 Z0).
Qed.

(* A table's two geometry words lie in the loaded image: they are DEC_RO_RD bytes (a Theorem Labs lane cc88c36cf66), every one
   of which is a read-only image byte (dec_ro_rd_rom_clean). So no allocator block holds them. *)
Lemma ins_t_tab_img : forall t k, (t = 0x20d40 \/ t = 0x20d80 \/ t = 0x20d60) -> 0 <= k < 8 -> LCK.in_img (t + 4 + k).
Proof.
intros t k Ht Hk.
assert (Hro : dec_in_ro_rd (t + 4 + k)).
{ unfold dec_in_ro_rd, DEC_RO_RD. apply Exists_exists.
  destruct Ht as [-> | [-> | ->]].
  - exists (0x20d44, 8). split; [cbn [In]; right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - exists (0x20d84, 8). split; [cbn [In]; do 5 right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia].
  - exists (0x20d64, 8). split; [cbn [In]; do 4 right; left; reflexivity | unfold in_zr; cbn [fst snd]; lia]. }
destruct (dec_ro_rd_rom_clean _ Hro) as [(sg & Hin & _ & Hr) _].
exists sg. split; [exact Hin | exact Hr].
Qed.

(* The frame's local at d_F + 32 is addressable over its two 4-byte fields: its shadow bytes are 0 and 4. *)
Lemma ins_t_loc_ra : forall cx (r : reader), dec_a_fsh cx r 0 4 -> d_F cx mod 32 = 0 ->
  range_addressable r SHADOW_OFF (d_F cx + 32 + 4) 8.
Proof.
intros cx r (_ & F4 & F5 & _) Hal x Hx. unfold shadow_of_addr, saddr_ok.
unfold d_SH, shadow_addr in F4, F5.
destruct (Z_lt_dec x (d_F cx + 40)).
- exists 0. split; [|left; reflexivity].
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + d_F cx / 8 + 4) by lia. exact F4.
- exists 4. split; [|right; lia].
  replace (SHADOW_OFF + x / 8) with (SHADOW_OFF + d_F cx / 8 + 5) by lia. exact F5.
Qed.

(* The mode's two 4-byte fields as the raw bytes the leaf reads. *)
Lemma ins_t_mode_bytes : forall (W : world segs) m mode nch ns,
  val_mem segs (mrestrict (w_H W) m) (mode + 4) 4 (nch mod 2 ^ 32) ->
  val_mem segs (mrestrict (w_H W) m) (mode + 8) 4 (ns mod 2 ^ 32) ->
  0 <= mode -> mode + 12 <= 2 ^ 64 ->
  LMem.bytes_at segs m (mode + 4) (LMem.le4 (Z_to_bv 64 nch) ++ LMem.le4 (Z_to_bv 64 ns)).
Proof.
intros W m mode nch ns Hv4 Hv8 H0 Ht.
assert (Hm : forall z, bv_unsigned (Z_to_bv 64 z) mod 2 ^ (8 * Z.of_nat 4) = (z mod 2 ^ 32) mod 2 ^ (8 * Z.of_nat 4)).
{ intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (8 * Z.of_nat 4) with 32.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite !dec_leafb_mod_pow2_mod by lia. reflexivity. }
apply LMem.bytes_at_app. split.
- unfold LMem.le4. exact (dec_leafb_bytes_le W m (mode + 4) 4 _ _ Hv4 (Hm nch) ltac:(lia) ltac:(lia)).
- rewrite LMem.length_le4. replace (mode + 4 + Z.of_nat 4) with (mode + 8) by lia.
  unfold LMem.le4. exact (dec_leafb_bytes_le W m (mode + 8) 4 _ _ Hv8 (Hm ns) ltac:(lia) ltac:(lia)).
Qed.

(* A byte a value of the view shows is visible. *)
Lemma ins_t_vis_val : forall (W : world segs) m a (n : nat) v,
  val_mem segs (mrestrict (w_H W) m) a n v -> forall x, a <= x < a + Z.of_nat n -> w_H W (Z_to_bv 64 x) = false.
Proof.
intros W m a n v Hv x Hx. pose proof (Hv (Z.to_nat (x - a)) ltac:(lia)) as H.
rewrite Z2Nat.id in H by lia. replace (a + (x - a)) with x in H by lia.
exact (dec_leafb_mbyte_vis W m x _ H).
Qed.

(* Raw bytes at visible addresses are a garr8 array of the view (the converse of dec_leafb_bytes_garr8). *)
Lemma ins_t_garr8_of_bytes : forall (W : world segs) m p (bs : list byte),
  LMem.bytes_at segs m p bs ->
  (forall j, 0 <= j < Z.of_nat (length bs) -> w_H W (Z_to_bv 64 (p + j)) = false) ->
  garr8 segs (mrestrict (w_H W) m) p (map (fun b : byte => bv_unsigned b) bs).
Proof.
intros W m p bs (H0 & Ht & HB) HV j Hj. rewrite length_map in Hj.
rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; exact Hj). rewrite map_nth.
split.
- intros k Hk. assert (k = 0%nat) as -> by lia. rewrite Nat2Z.inj_0, Z.add_0_r.
  rewrite <- (dec_leafb_mrd W m (p + Z.of_nat j) (HV (Z.of_nat j) ltac:(lia))). rewrite (HB j Hj).
  rewrite (nth_error_nth' bs (Z_to_bv 8 0) Hj). rewrite dec_leafb_le_byte1. reflexivity.
- pose proof (bv_unsigned_in_range 8 (nth j bs (Z_to_bv 8 0))) as R. change (bv_modulus 8) with 256 in R. lia.
Qed.

(* What a successful decode_ok (lib/A/Prog/reac_decode_c.v:12) says of its arguments. *)
Lemma ins_t_dec_ok : forall len bs nch ns, CDec.decode_ok len bs nch ns = true ->
  CInsp.inspect_wf len bs = true /\ len = 1492 /\ 0 < nch /\ 0 < ns /\ dec_a_olen nch ns = 3 * nch * ns.
Proof.
intros len bs nch ns H. unfold CDec.decode_ok in H.
apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H H4]. apply andb_true_iff in H as [H _].
apply andb_true_iff in H as [Hw H2].
split; [exact Hw|]. split.
{ unfold CInsp.inspect_wf in Hw. repeat (apply andb_true_iff in Hw as [Hw _]). apply Z.eqb_eq in Hw. exact Hw. }
split; [apply Z.ltb_lt; exact H2|]. split; [apply Z.ltb_lt; exact H4|].
unfold dec_a_olen. rewrite H2, H4. reflexivity.
Qed.

(* The sltiu at +0x4d0 on a word below 2^64. *)
Lemma ins_t_sltu : forall x c, 0 <= x < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  alu64 ALU_SLTU (w64 x) (Z_to_bv 64 c) = w64 (if x <? c then 1 else 0).
Proof.
intros x c Hx Hc.
change (alu64 ALU_SLTU (w64 x) (Z_to_bv 64 c)) with (if bv_ltu (w64 x) (Z_to_bv 64 c) then Z_to_bv 64 1 else Z_to_bv 64 0).
unfold bv_ltu, w64. rewrite !unsigned_lit_small by assumption. destruct (x <? c); reflexivity.
Qed.

(* An 8-byte chunk of a region is the value of its atom. *)
Lemma ins_t_soff : forall E (n : nat) v, ew E n = w64 v -> 0 <= v < 2 ^ 64 ->
  bv_unsigned (sv_denot E (SOff n 0)) mod 2 ^ (8 * Z.of_N 8) = v.
Proof.
intros E n v Hn Hv. change (bv_unsigned (sv_denot E (SOff n 0))) with (U E (SOff n 0)).
rewrite U_SOff, Hn, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by exact Hv.
rewrite zcanon_id by (unfold M64; lia). change (8 * Z.of_N 8) with 64. apply Z.mod_small. exact Hv.
Qed.
(* A chunk of ins_t_spill5. *)
Ltac ins_t_in := unfold ins_t_spill5; cbn [YP09.r_chunks In]; repeat (first [left; reflexivity | right]).

Lemma ins_tail :
  dec_crt_cells B -> AR_laws segs B ->
  (forall fx : YK11.FPState, @aintrin_realizes fx rc segs B OSet (decode_sigma DS___asan_memset)) ->
  (forall fx : YK11.FPState, @dec_leaf_wr_at rc B (@LDecode.dec_reac_decode_cg) fx) ->
  forall (cx : dctx) (fx : YK11.FPState) ly S (W : world segs) regs mem md (res out mode nch ns : Z),
  dec_a_base asink_syms tfib_K asink_none ameta_inv arodata_okS RA_LLVMF A_EMPTY B MT XL RLO RHI cx ->
  ins_at3c0 cx fx ly S W regs mem md res out mode nch ns ->
  forall regs4 mem4 md4,
  ins_at4d0 cx ly S W mem res out mode nch ns regs4 mem4 md4 ->
  SRr segs W (mkCfg (@YK11.mkst fx regs4 (Z_to_bv 64 (VAL A_TEXT + 0x4d0)) mem4 (YK11.seg_rom segs)) md4)
    (llvm_a_st_4fc B MT cx).
Proof.
intros HCELLS LAWS AMEMSET LDE cx fx ly S W regs mem md res out mode nch ns HB H3 regs4 mem4 md4 H4.
destruct H3 as (Hfrm & HCORE & Hbl & Hres & Hout & MLE & MOK & HFR & R10 & R18 & R20 & R26 & R24 & R25 & R23 & R22
  & HMODE & HFSH & HBODY & SL32 & SL48 & SL64 & SL80 & SL88 & SL112).
destruct H4 as (HJ & Rsp & R3 & R4 & R8 & R9 & HFR4 & R20' & R22' & R23' & R24' & R25' & R26' & T32 & T40 & T48 & T56
  & T64 & T80 & T88 & T112 & HKR & HGR).
pose proof HCORE as (HJ0 & Hfrs & _ & _ & _ & Hsp1r & Hsp1m & _ & _ & HSAV & HF4096 & HFal & HFpres & HFL & Hpl & Hgarr).
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs' & Hnev & Hk & G1 & G2 & G3 & G4 & Hgone & Hpres & Hstk & G5 & HQT).
pose proof Hstk as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (sp0 := d_sp0 cx) in *. set (sp1 := d_sp1 cx) in *.
set (len := dec_a_len (d_n cx)) in *. set (body := d_body cx) in *.
set (olen := dec_a_olen nch ns) in *. set (fits := dec_a_fits0 nch ns) in *.
assert (STKv : DEC_LLVMF_STK = 32768) by reflexivity.
assert (Hu64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (w64 z) = z) by (intros z Hz; apply unsigned_lit_small; exact Hz).
assert (Hn26 : 0 <= d_n cx < 2 ^ 26) by exact (ins_base_n cx HB).
assert (Hlen26 : 0 <= len < 2 ^ 26) by (unfold len, dec_a_len; lia).
assert (Hmok : -128 <= nch <= 127 /\ -128 <= ns <= 127) by (destruct HMODE as (_ & H1 & H2 & _); lia).
assert (Holen : 1 <= olen <= 48387).
{ unfold olen, dec_a_olen. destruct ((0 <? nch) && (0 <? ns))%bool eqn:Eq; [|lia].
  apply andb_true_iff in Eq as [E1 E2]. apply Z.ltb_lt in E1. apply Z.ltb_lt in E2. nia. }
assert (Hinout : In (out, olen) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; right; left; reflexivity).
assert (Hinres : In (res, len) (ablocks B ly S)) by (rewrite Hbl; apply in_or_app; right; left; reflexivity).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinout) as (Hout16 & _ & Houtc & Houtapp & Houtpres & _ & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hinres) as (Hres16 & _ & Hresc & Hresapp & Hrespres & _ & _).
pose proof (req_size_pos0 len ltac:(lia)) as Hrqlen. pose proof (req_size_pos0 olen ltac:(lia)) as Hrqolen.
assert (Hrqo : req_size olen = olen) by (unfold req_size; destruct (Z.eqb_spec olen 0); lia).
assert (Hceil1 : alloc_ceiling + 32768 - 4336 <= sp1 - 4096) by (unfold DEC_LLVMF_STK in *; lia).
assert (HSL : forall off v, dec_a_slot cx (aview segs (w_H W) mem4) off v ->
  0 <= v < 2 ^ 64 /\ val_mem segs (mrestrict (w_H W) mem4) (sp1 + off) 8 v)
  by (intros off v Hs; split; [exact (rdword_range _ _ _ (aview_byte_range _ _) Hs) | exact (val_mem_of_rdword segs _ _ _ _ Hs)]).
(* the entry state at +0x4d0 *)
set (E := @Eimg rc decode_listing PID (Ereg regs4 (ins_extra4 fits (nch mod 2 ^ 64) mode (nch mod 2 ^ 32) (ns mod 2 ^ 64) len))).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n =
  ew (Ereg regs4 (ins_extra4 fits (nch mod 2 ^ 64) mode (nch mod 2 ^ 32) (ns mod 2 ^ 64) len)) n)
  by (intros n Hn; subst E; apply Eimg_low; exact Hn).
assert (E9 : ew E 9 = w64 sp1) by ereg EL 9%nat (9%bv : bv 5) R9.
assert (E19 : ew E 19 = w64 (d_F cx)) by ereg EL 19%nat (19%bv : bv 5) (proj1 HFR4).
assert (E20 : ew E 20 = w64 res) by ereg EL 20%nat (20%bv : bv 5) R20'.
assert (E22 : ew E 22 = w64 out) by ereg EL 22%nat (22%bv : bv 5) R22'.
assert (E25 : ew E 25 = w64 olen) by ereg EL 25%nat (25%bv : bv 5) R25'.
assert (E3 : ew E 3 = w64 (as_gp B)) by ereg EL 3%nat (3%bv : bv 5) R3.
assert (E4 : ew E 4 = w64 (as_tp B)) by ereg EL 4%nat (4%bv : bv 5) R4.
assert (E2 : ew E 2 = YK11.getr regs4 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs4 _ 2 2%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = sp1) by (rewrite E2; exact Rsp).
assert (E32 : ew E 32 = w64 fits) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 0)).
assert (E33 : ew E 33 = w64 (nch mod 2 ^ 64)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 1)).
assert (E34 : ew E 34 = w64 mode) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 2)).
assert (E35 : ew E 35 = w64 (nch mod 2 ^ 32)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 3)).
assert (E36 : ew E 36 = w64 (ns mod 2 ^ 64)) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 4)).
assert (E37 : ew E 37 = w64 SHADOW_OFF) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 5)).
assert (E38 : ew E 38 = w64 len) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra _ _ 6)).
assert (HS : st_ok_pi segs VAL E ss_ins4
  (restrict (w_H W) (YK11.mkst regs4 (Z_to_bv 64 (VAL A_TEXT + 0x4d0)) mem4 (YK11.seg_rom segs)))).
{ rewrite restrict_mkst_fx. unfold ss_ins4. apply (pa_entry_st_ok_full (PI := PID)).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold ins_spill4, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9, Hu64 by lia.
    split; [lia|]. split; [lia|].
    split; [intros o Ho; apply (apresent_writable segs); apply Hpres; lia|].
    destruct (HSL _ _ T32) as [V32 M32]. destruct (HSL _ _ T40) as [V40 M40]. destruct (HSL _ _ T48) as [V48 M48].
    destruct (HSL _ _ T56) as [V56 M56]. destruct (HSL _ _ T64) as [V64 M64].
    destruct (HSL _ _ T80) as [V80 M80]. destruct (HSL _ _ T88) as [V88 M88]. destruct (HSL _ _ T112) as [V112 M112].
    repeat apply Forall_cons; try apply Forall_nil.
    + apply (chunk_ok_val segs E _ sp1 32 8 (SOff 32 0) fits); [cbn [sv_denot]; rewrite E32, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M32].
    + apply (chunk_ok_val segs E _ sp1 40 8 (SOff 37 0) SHADOW_OFF); [cbn [sv_denot]; rewrite E37, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M40].
    + apply (chunk_ok_val segs E _ sp1 48 8 (SOff 33 0) (nch mod 2 ^ 64)); [cbn [sv_denot]; rewrite E33, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M48].
    + apply (chunk_ok_val segs E _ sp1 56 8 (SOff 38 0) len); [cbn [sv_denot]; rewrite E38, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M56].
    + apply (chunk_ok_val segs E _ sp1 64 8 (SOff 34 0) mode); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M64].
    + apply (chunk_ok_val segs E _ sp1 80 8 (SOff 35 0) (nch mod 2 ^ 32)); [cbn [sv_denot]; rewrite E35, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M80].
    + apply (chunk_ok_val segs E _ sp1 88 8 (SOff 36 0) (ns mod 2 ^ 64)); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M88].
    + apply (chunk_ok_val segs E _ sp1 112 8 (SOff 19 0) (d_F cx)); [cbn [sv_denot]; rewrite E19, Z.add_0_r, Hu64 by lia; reflexivity | zside | zside | exact M112].
  - cbn. tauto.
  - split; [|split; [exact I | exact I]].
    cbn [ins_facts4 f_atoms atoms_ok]. unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E9, E20, E22, E37. rewrite (Hu64 sp1), (Hu64 out), (Hu64 res), (Hu64 SHADOW_OFF) by (unfold SHADOW_OFF; lia).
    unfold SB, SHADOW_OFF. change (2 ^ 4) with 16. change (2 ^ 5) with 32. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
pose proof (@paj_run fx rc dec_A_sink_head decode_listing PL_decode PID B LAWS) as RUN.
assert (SHOK : sh_ok segs (SOff 37 0) [] E (mrestrict (w_H W) mem4)) by constructor.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
(* +0x4d0 .. +0x4e0: s2 := (s8 <u 481), the memset arguments, the call *)
paj_run_tok RUN HS HJ SHOK Bspan.
1: { lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
       let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end.
     eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat sp1); [reflexivity | rewrite E9; apply Hu64; lia | | apply awr_ok_nil].
     cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. left. unfold DEC_LLVMF_STK in *; lia. }
set (md1 := with_vm_backing (m_vm_lazy md4) mat md4) in *. clearbody md1.
pmkst HS.
prreg HS (10%bv : bv 5) Ra0. prreg HS (11%bv : bv 5) Ra1. prreg HS (12%bv : bv 5) Ra2.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp2. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
prreg HS (18%bv : bv 5) Rs2.
assert (E24 : ew E 24 = w64 (dec_a_prod nch ns)) by ereg EL 24%nat (24%bv : bv 5) R24'.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) ->
  aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem4 a).
{ apply (ins_kept_run E (ss_mem ss_ins4) (w_H W) mem4 (ms_mem ms) (fun a => sp1 - 4096 <= a < sp1 + 120) HFr).
  intros a (r & Hin & Ha). unfold ss_ins4 in Hin. cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [ins_spill4 YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite E9, Hu64 in Ha by lia. lia. }
assert (GR1 : forall a, apresent (w_H W) mem4 a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Ha; exact (apresent_grows (w_H W) mem4 (ms_mem ms) a HG Ha)).
pose proof (proj1 HJ) as HAR1.
assert (Usp_ms : spZ (ms_regs ms) = sp1) by (unfold spZ; rewrite Rsp2, E2; exact Rsp).
eapply SRr_bind.
{ eapply (aj_intrin_at (fx := fx) segs B LAWS DecodeImg.decode_segs_low OSet (decode_sigma DS___asan_memset)
    (AMEMSET fx) W (ms_regs ms) (ms_mem ms) DEC_LLVMF_STK sp0 [] (d_ly cx) (d_S cx) (d_W cx) (d_mem cx) (d_md cx)
    [(DEC_FCLASS, d_fpos cx)] ly S md1 dec_ev_3c0 out 165 olen (sp1 - sp0) (Z_to_bv 64 (VAL A_TEXT + 0x4e4)) HJ).
  - rewrite Ra0, E22. reflexivity.
  - rewrite Ra1. reflexivity.
  - rewrite Ra2, E25. reflexivity.
  - lia.
  - lia.
  - lia.
  - rewrite Usp_ms. lia.
  - lia.
  - lia.
  - unfold ESTACK. lia.
  - rewrite Rgp, E3. reflexivity.
  - rewrite Rtp, E4. reflexivity.
  - exact Rra.
  - apply (ret_ok_codeptr_v (PI := PID)); [lia | reflexivity].
  - intros a Ha. split; [|unfold ESTACK; lia].
    eapply (dec_leafb_awr_new B LAWS _ _ _ _ _ _ _ _ _ _ _ _ out olen a HAR1 Hbl);
      [apply in_or_app; right; left; reflexivity | rewrite Hrqo; lia].
  - eapply (amem_range_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hinout); lia.
  - eapply (range_addressable_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hinout); lia.
  - intros _. eapply (shadow_hull_vis_of_block segs B LAWS _ _ _ _ _ _ _ _ _ HAR1 Hinout); lia.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & Ha03 & Heff3 & Hkeep3 & Hpres3).
assert (KR3 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) -> ~ (out <= a < out + olen) ->
  aview segs (w_H W) mem3 a = aview segs (w_H W) mem4 a).
{ intros a Ha H1 H2. rewrite Hkeep3; [apply KR1; assumption | exact Ha | exact H2 | unfold ESTACK; lia]. }
assert (GR3 : forall a, apresent (w_H W) mem4 a -> apresent (w_H W) mem3 a) by (intros a Ha; apply Hpres3, GR1, Ha).
jafter_call_keep_hi HS 512%nat regs3 (mrestrict (w_H W) mem3) HP3 [0%nat] HS2.
match type of HS2 with ?tq -> _ => assert (HRK : tq) end.
{ cbn [ms_mem restrict]. apply Forall_cons; [|apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E9, Hu64 by lia; intros a Ha.
  - apply (mbyte_of_aview segs). rewrite Hkeep3; [reflexivity | lia | lia | unfold ESTACK; lia].
  - intros _. apply (apresent_writable segs). apply Hpres3. apply GR1. apply Hpres. unfold DEC_LLVMF_STK; lia. }
specialize (HS2 HRK). clear HRK HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
set (E1 := havoc E 512 (map (getr regs3) CLOB)) in HS.
assert (HEI1 : img_env VAL A_LIM E1) by (apply img_env_havoc_hi; [exact HEI | cbv; lia]).
assert (E1lo : forall n, (n < 512)%nat -> ew E1 n = ew E n) by (intros n Hn; apply ew_havoc_old; exact Hn).
assert (U9_1 : bv_unsigned (ew E1 9) = sp1) by (rewrite E1lo by lia; rewrite E9; apply Hu64; lia).
assert (SHOK1 : sh_ok segs (SOff 37 0) [] E1 (mrestrict (w_H W) mem3)) by constructor.
(* +0x4e4 .. +0x4f8: a0 := s4, a1 := len (56(s1)), a2 := mode (64(s1)), 72(s1) := out, a3 := out, the call *)
paj_run_tok RUN HS HJ3 SHOK1 Bspan.
1: { lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
       let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end.
     eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat sp1); [reflexivity | exact U9_1 | | apply awr_ok_nil].
     cbn [YP09.r_wlo YP09.r_whi]. intros a Ha. left. unfold DEC_LLVMF_STK in *; lia. }
set (md5 := with_vm_backing (m_vm_lazy md3) mat0 md3) in *. clearbody md5.
pmkst HS.
prreg HS (10%bv : bv 5) Rb0. prreg HS (11%bv : bv 5) Rb1. prreg HS (12%bv : bv 5) Rb2. prreg HS (13%bv : bv 5) Rb3.
prreg HS (1%bv : bv 5) Rbra. prreg HS (2%bv : bv 5) Rbsp. prreg HS (3%bv : bv 5) Rbgp. prreg HS (4%bv : bv 5) Rbtp.
prreg HS (8%bv : bv 5) Rb8. prreg HS (9%bv : bv 5) Rb9. prreg HS (18%bv : bv 5) Rb18.
prreg HS (19%bv : bv 5) Rb19. prreg HS (20%bv : bv 5) Rb20. prreg HS (21%bv : bv 5) Rb21.
prreg HS (22%bv : bv 5) Rb22. prreg HS (23%bv : bv 5) Rb23. prreg HS (24%bv : bv 5) Rb24.
prreg HS (25%bv : bv 5) Rb25. prreg HS (26%bv : bv 5) Rb26. prreg HS (27%bv : bv 5) Rb27.
(* the registers at the call, as values *)
assert (E8 : ew E 8 = w64 sp0) by ereg EL 8%nat (8%bv : bv 5) R8.
assert (E21 : ew E 21 = w64 (d_F cx)) by ereg EL 21%nat (21%bv : bv 5) (proj1 (proj2 HFR4)).
assert (E27 : ew E 27 = w64 (d_SH cx)) by ereg EL 27%nat (27%bv : bv 5) (proj2 (proj2 HFR4)).
assert (E23 : ew E 23 = w64 (ns mod 2 ^ 32)) by ereg EL 23%nat (23%bv : bv 5) R23'.
assert (E26 : ew E 26 = w64 (if CInsp.inspect_wf len body then 1 else 0)) by ereg EL 26%nat (26%bv : bv 5) R26'.
assert (B2 : YK11.getr (ms_regs ms0) (Z_to_bv 5 2) = YK11.getr regs4 2)
  by exact (eq_trans Rbsp (eq_trans (E1lo 2%nat ltac:(lia)) E2)).
assert (B3 : YK11.getr (ms_regs ms0) (Z_to_bv 5 3) = w64 (as_gp B))
  by exact (eq_trans Rbgp (eq_trans (E1lo 3%nat ltac:(lia)) E3)).
assert (B4 : YK11.getr (ms_regs ms0) (Z_to_bv 5 4) = w64 (as_tp B))
  by exact (eq_trans Rbtp (eq_trans (E1lo 4%nat ltac:(lia)) E4)).
assert (B8 : YK11.getr (ms_regs ms0) (Z_to_bv 5 8) = w64 sp0) by exact (eq_trans Rb8 (eq_trans (E1lo 8%nat ltac:(lia)) E8)).
assert (B9 : YK11.getr (ms_regs ms0) (Z_to_bv 5 9) = w64 sp1) by exact (eq_trans Rb9 (eq_trans (E1lo 9%nat ltac:(lia)) E9)).
assert (B10 : YK11.getr (ms_regs ms0) (Z_to_bv 5 10) = w64 res)
  by exact (eq_trans Rb0 (eq_trans (E1lo 20%nat ltac:(lia)) E20)).
assert (B11 : YK11.getr (ms_regs ms0) (Z_to_bv 5 11) = w64 len)
  by exact (eq_trans Rb1 (eq_trans (E1lo 38%nat ltac:(lia)) E38)).
assert (B12 : YK11.getr (ms_regs ms0) (Z_to_bv 5 12) = w64 mode)
  by exact (eq_trans Rb2 (eq_trans (E1lo 34%nat ltac:(lia)) E34)).
assert (B13 : YK11.getr (ms_regs ms0) (Z_to_bv 5 13) = w64 out)
  by exact (eq_trans Rb3 (eq_trans (E1lo 22%nat ltac:(lia)) E22)).
assert (B18 : YK11.getr (ms_regs ms0) (Z_to_bv 5 18) = w64 (if dec_a_prod nch ns <? 481 then 1 else 0)).
{ refine (eq_trans Rb18 _). rewrite (E1lo 24%nat) by lia. rewrite E24.
  apply ins_t_sltu; [unfold dec_a_prod; apply Z.mod_pos_bound; lia | lia]. }
assert (B19 : YK11.getr (ms_regs ms0) (Z_to_bv 5 19) = w64 (d_F cx))
  by exact (eq_trans Rb19 (eq_trans (E1lo 19%nat ltac:(lia)) E19)).
assert (B20 : YK11.getr (ms_regs ms0) (Z_to_bv 5 20) = w64 res)
  by exact (eq_trans Rb20 (eq_trans (E1lo 20%nat ltac:(lia)) E20)).
assert (B21 : YK11.getr (ms_regs ms0) (Z_to_bv 5 21) = w64 (d_F cx))
  by exact (eq_trans Rb21 (eq_trans (E1lo 21%nat ltac:(lia)) E21)).
assert (B22 : YK11.getr (ms_regs ms0) (Z_to_bv 5 22) = w64 out)
  by exact (eq_trans Rb22 (eq_trans (E1lo 22%nat ltac:(lia)) E22)).
assert (B23 : YK11.getr (ms_regs ms0) (Z_to_bv 5 23) = w64 (ns mod 2 ^ 32))
  by exact (eq_trans Rb23 (eq_trans (E1lo 23%nat ltac:(lia)) E23)).
assert (B24 : YK11.getr (ms_regs ms0) (Z_to_bv 5 24) = w64 (dec_a_prod nch ns))
  by exact (eq_trans Rb24 (eq_trans (E1lo 24%nat ltac:(lia)) E24)).
assert (B25 : YK11.getr (ms_regs ms0) (Z_to_bv 5 25) = w64 olen)
  by exact (eq_trans Rb25 (eq_trans (E1lo 25%nat ltac:(lia)) E25)).
assert (B26 : YK11.getr (ms_regs ms0) (Z_to_bv 5 26) = w64 (if CInsp.inspect_wf len body then 1 else 0))
  by exact (eq_trans Rb26 (eq_trans (E1lo 26%nat ltac:(lia)) E26)).
assert (B27 : YK11.getr (ms_regs ms0) (Z_to_bv 5 27) = w64 (d_SH cx))
  by exact (eq_trans Rb27 (eq_trans (E1lo 27%nat ltac:(lia)) E27)).
assert (Usp5 : bv_unsigned (YK11.getr (ms_regs ms0) (Z_to_bv 5 2)) = sp1) by (rewrite B2; exact Rsp).
assert (Usp_ms5 : spZ (ms_regs ms0) = sp1) by exact Usp5.
assert (Ua1' : bv_unsigned (YK11.getr (ms_regs ms0) (Z_to_bv 5 11)) = len) by (rewrite B11; apply Hu64; lia).
assert (Hsp0e : d_sp0 cx = sp0) by reflexivity. assert (Hsp1e : d_sp1 cx = sp1) by reflexivity.
assert (Hlene : dec_a_len (d_n cx) = len) by reflexivity. assert (Holen' : dec_a_olen nch ns = olen) by reflexivity.
(* the entry context: its AR, the payload block, the payload length *)
pose proof (ins_base_afn cx HB) as Hafn. pose proof (ins_base_pn cx HB) as Hblk.
pose proof (ins_base_len cx HB) as Hlenpl. destruct Hafn as (AR0 & _).
assert (Hblen : Z.of_nat (length body) = len)
  by (unfold body, len, d_body; rewrite length_skipn; unfold dec_a_u, dec_a_len; lia).
(* the fake frame: below the allocator ceiling, in application memory, apart from the decode buffer *)
destruct (al_layout _ _ LAWS _ _ _ _ _ ly AR0 Hly) as (_ & HFA & _).
assert (Hfb : fs_frame_bytes DEC_FCLASS = 64) by reflexivity.
assert (HinF : In (DEC_FCLASS, d_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds segs B LAWS _ _ _ _ _ _ _ HAR HinF) as (_ & Fb2 & Fb3).
rewrite HFA, Hfb in Fb2, Fb3. change (frame_addr (d_ly cx) DEC_FCLASS (d_fpos cx)) with (d_F cx) in Fb2, Fb3.
assert (HdOF : out + olen <= d_F cx \/ d_F cx + 64 <= out).
{ pose proof (sep_block_frame segs B LAWS _ _ _ _ _ out olen DEC_FCLASS (d_fpos cx) HAR Hinout HinF) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hrqo, HFA, Hfb in D. exact D. }
(* the body copy and the decode buffer are apart *)
assert (HdRO : res + req_size len <= out \/ out + olen <= res).
{ assert (Hbl' : ablocks B ly S = ablocks B (d_ly cx) (d_S cx) ++ (res, len) :: [] ++ (out, olen) :: []) by exact Hbl.
  pose proof (sep_blocks_pos segs B LAWS _ _ _ _ _ _ _ _ _ _ HAR Hbl') as D.
  unfold zdisjoint, block_rng in D. cbn [fst snd] in D. rewrite Hrqo in D. exact D. }
(* the payload block lies below the ceiling and apart from the decode buffer *)
assert (HnotO : ~ In (out, olen) (ablocks B (d_ly cx) (d_S cx) ++ [(res, len)])).
{ apply (dec_leafb_new_block B LAWS ly S W mem4 md4 _ [(out, olen)] out olen HAR); [|left; reflexivity].
  rewrite Hbl. apply app_assoc. }
assert (HPL : forall a, d_p cx <= a < d_p cx + Z.of_nat (length (d_pl cx)) ->
  0 <= a < 2 ^ 64 /\ ~ (sp1 - 4096 <= a < sp1 + 120) /\ ~ (out <= a < out + olen)).
{ intros a Ha. rewrite <- Hlenpl in Ha.
  destruct Hblk as [(Hn0 & _) | (Hn0 & Hin0)]; [lia|].
  assert (Hin : In (d_p cx, d_n cx) (ablocks B ly S)) by (apply Hpl; lia).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR Hin) as (_ & Hp4096 & Hpc & _).
  assert (Hne : (d_p cx, d_n cx) <> (out, olen))
    by (intros Heq; apply HnotO; rewrite <- Heq; apply in_or_app; left; exact Hin0).
  pose proof (sep_blocks segs B LAWS _ _ _ _ _ _ _ _ _ HAR Hin Hinout Hne) as D.
  unfold zdisjoint in D. cbn [fst snd] in D. rewrite Hrqo in D.
  pose proof (req_size_pos0 (d_n cx) ltac:(lia)) as Hq. lia. }
(* the memory at the call against the +0x3c0 memory *)
assert (KR5 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem3 a).
{ apply (ins_kept_run E1 _ (w_H W) mem3 (ms_mem ms0) (fun a => sp1 - 4096 <= a < sp1 + 120) HFr0).
  intros a (r & Hin & Ha). cbn [ss_mem In] in Hin. destruct Hin as [<- | []].
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U9_1 in Ha. lia. }
assert (K5 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) -> ~ (out <= a < out + olen) ->
  aview segs (w_H W) (ms_mem ms0) a = aview segs (w_H W) mem a).
{ intros a Ha H1 H2. rewrite (KR5 a Ha H1), (KR3 a Ha H1 H2). exact (HKR a Ha H1). }
assert (PR5 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
{ intros a Ha. apply (apresent_grows (w_H W) mem3 (ms_mem ms0) a HG0). apply GR3, HGR, Ha. }
assert (HAR0m : AR segs B ly S W mem md) by exact (proj1 HJ0).
assert (HAR5 : AR segs B ly S W (ms_mem ms0) md5) by exact (proj1 HJ3).
assert (KSH : forall i, 0 <= i < 8 -> 0 <= d_SH cx + i < 2 ^ 64 /\ ~ (sp1 - 4096 <= d_SH cx + i < sp1 + 120) /\
  ~ (out <= d_SH cx + i < out + olen)).
{ intros i Hi. assert (ESH : d_SH cx = SHADOW_OFF + d_F cx / 8) by reflexivity. unfold SHADOW_OFF in ESH.
  split; [lia|]. split; [lia|].
  intros Hx. apply (fshadow_not_app (d_F cx) 8 out (req_size olen) (d_SH cx + i) HF4096);
    [lia | exact Houtapp | lia | rewrite Hrqo; lia]. }
(* the mode at the call: its two geometry words are outside the stack window and the decode buffer, so kept from
   +0x3c0 (a table lies in the image, which the buffer, an allocator block, does not touch; the frame's local
   lies in the fake frame, apart from the buffer) *)
assert (KMF : forall q, 0 <= q < 8 -> 0 <= mode + 4 + q < 2 ^ 64 /\ ~ (sp1 - 4096 <= mode + 4 + q < sp1 + 120) /\
  ~ (out <= mode + 4 + q < out + olen)).
{ intros q Hq. destruct (ins_t_mode_cases cx ly S W mem md mode nch ns HCELLS HAR0m HMODE) as [HT | HL].
  - pose proof (ins_t_tab_img mode q HT Hq) as Himg. pose proof alloc_ceiling_val.
    split; [destruct HT as [-> | [-> | ->]]; lia|].
    split; [unfold DEC_LLVMF_STK in *; destruct HT as [-> | [-> | ->]]; lia|].
    intros Ho. apply (proj2 (dec_leafb_wr_block B LAWS ly S W mem md out olen HAR0m Hinout (mode + 4 + q)
      ltac:(rewrite Hrqo; lia))). exact Himg.
  - rewrite HL. split; [lia|]. split; lia. }
assert (HMODE5 : dec_a_mode_ok cx W (ms_mem ms0) mode nch ns).
{ apply (ins_t_mode_re cx W W mem (ms_mem ms0) ly S md ly S md5 mode nch ns HCELLS HAR0m HAR5 HMODE).
  intros kk Hkk. destruct (KMF kk Hkk) as (A1 & A2 & A3). exact (K5 _ A1 A2 A3). }
assert (HFSH5 : dec_a_fsh cx (aview segs (w_H W) (ms_mem ms0)) 0 4).
{ apply (ins_t_fsh_kept cx (aview segs (w_H W) mem)); [|exact HFSH].
  intros i Hi. destruct (KSH i Hi) as (A1 & A2 & A3). exact (K5 _ A1 A2 A3). }
assert (MODEF : range_addressable (aview segs (w_H W) (ms_mem ms0)) SHADOW_OFF (mode + 4) 8 /\
  (forall i, 0 <= i < 8 -> ACells.app_mem (mode + 4 + i)) /\ 4096 <= mode /\ mode + 12 <= alloc_ceiling).
{ destruct (ins_t_mode_cases cx ly S W mem md mode nch ns HCELLS HAR0m HMODE) as [HT | HL].
  - split; [exact (ins_t_tab_ra ly S W (ms_mem ms0) md5 mode HCELLS HAR5 HT)|].
    split; [intros i Hi; unfold ACells.app_mem, ACells.LOWMEM_END; left; destruct HT as [-> | [-> | ->]]; lia|].
    destruct HT as [-> | [-> | ->]]; split; lia.
  - rewrite HL. split; [exact (ins_t_loc_ra cx _ HFSH5 HFal)|].
    split; [|split; lia].
    intros i Hi. replace (d_F cx + 32 + 4 + i) with (d_F cx + (36 + i)) by lia.
    apply (dec_leafb_app_of_in_app (d_F cx) 64); [exact Fb3 | lia]. }
(* the leaf's written range is the decode buffer *)
assert (HWRo : forall a, LCK.in_wr (if CDec.decode_ok len body nch ns then [(out, out + 3 * nch * ns)] else []) a ->
  out <= a < out + olen).
{ intros a. destruct (CDec.decode_ok len body nch ns) eqn:Edec; intros Ha; unfold LCK.in_wr in Ha.
  - apply Exists_cons in Ha as [Ha | Ha]; [|apply Exists_nil in Ha; destruct Ha].
    cbn [fst snd] in Ha. destruct (ins_t_dec_ok _ _ _ _ Edec) as (_ & _ & _ & _ & Ho). rewrite Holen' in Ho. lia.
  - apply Exists_nil in Ha. destruct Ha. }
(* +0x4f8: reac_decode *)
eapply SRr_bind.
{ eapply (dec_leafb_journal (fx := fx) B LAWS W (ms_regs ms0) (ms_mem ms0) DEC_LLVMF_STK sp0 [] (d_ly cx) (d_S cx)
    (d_W cx) (d_mem cx) (d_md cx) [(DEC_FCLASS, d_fpos cx)] ly S md5 dec_ev_3c0 (sp1 - sp0)
    (pa_sigma DS_reac_decode) _ (if CDec.decode_ok len body nch ns then [(out, out + 3 * nch * ns)] else []) _ HJ3).
  - rewrite Usp_ms5. lia.
  - lia.
  - lia.
  - unfold ESTACK, DEC_LLVMF_STK. lia.
  - rewrite Rbra. apply (ret_ok_codeptr_v (PI := PID)); [lia | reflexivity].
  - exact B3.
  - exact B4.
  - intros a Ha. pose proof (HWRo a Ha) as Hr.
    eapply (dec_leafb_awr_new B LAWS _ _ _ _ _ _ _ _ _ _ _ _ out olen a HAR5 Hbl);
      [apply in_or_app; right; left; reflexivity | rewrite Hrqo; lia].
  - intros HPRE.
    pose proof (LDE fx ly S W (ms_regs ms0) (ms_mem ms0) md5 body res mode out nch ns (sp1 - 4096) HPRE) as L.
    cbv zeta in L. rewrite Ua1', Usp5 in L. apply L; clear L.
    + exact B10.
    + exact B12.
    + exact B13.
    + lia.
    + exact (proj1 (HSL _ _ T64)).
    + lia.
    + intros Hl. split; [lia|].
      apply (dec_leafb_bytes_garr8 W (ms_mem ms0) res body); [|lia|lia].
      apply (ins_garr8_kept (w_H W) mem (ms_mem ms0) res _ HBODY).
      intros j Hj. rewrite length_map in Hj. apply K5; lia.
    + lia.
    + lia.
    + destruct HMODE5 as (_ & _ & _ & Hv4 & Hv8). destruct MODEF as (_ & _ & M1 & M2).
      apply (ins_t_mode_bytes W); [exact Hv4 | exact Hv8 | lia | lia].
    + eapply (dec_leafb_stk_journal B); [exact HJ3 | unfold DEC_LLVMF_STK; lia | lia].
    + unfold CDec.REAC_DECODE_D. lia.
    + intros Hl. assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
      unfold AsanKA.off_stk. rewrite Usp5. left. unfold CDec.REAC_DECODE_D. lia.
    + unfold AsanKA.off_stk. rewrite Usp5. left. unfold CDec.REAC_DECODE_D. destruct MODEF as (_ & _ & M1 & M2). lia.
    + intros Hd. destruct (ins_t_dec_ok _ _ _ _ Hd) as (_ & Hl & Hn & Hs & Ho). rewrite Holen' in Ho.
      assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
      split; [|split; [lia|split; [lia|]]].
      * eapply (dec_leafb_wr_at_block B LAWS ly S W (ms_mem ms0) md5 out olen out (3 * nch * ns) HAR5 Hinout); lia.
      * unfold AsanKA.off_stk. rewrite Usp5. left. unfold CDec.REAC_DECODE_D. lia.
    + apply dec_leafb_app_stack. unfold CDec.REAC_DECODE_D. lia.
    + apply dec_leafb_app_stack. lia.
    + exact (dec_leafb_asan_cells B HCELLS ly S W (ms_mem ms0) md5 HAR5).
    + unfold AsanKA.off_stk, ACells.GOT_CELL_K, ACells.MIDEND. rewrite Usp5. left. unfold CDec.REAC_DECODE_D. lia.
    + intros Hl. assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
      eapply (dec_leafb_addressable_block B LAWS ly S W (ms_mem ms0) md5 res len res 1492 HAR5 Hinres); lia.
    + intros _. destruct MODEF as (MRA & MAPP & M1 & M2).
      apply (dec_leafb_addressable W (ms_mem ms0)); [exact MRA | lia | lia | unfold ACells.APPMEM_END; lia | exact MAPP].
    + intros Hd. destruct (ins_t_dec_ok _ _ _ _ Hd) as (_ & _ & Hn & Hs & Ho). rewrite Holen' in Ho.
      eapply (dec_leafb_addressable_block B LAWS ly S W (ms_mem ms0) md5 out olen out (3 * nch * ns) HAR5 Hinout); lia.
    + eapply (dec_leafb_rng_journal B);
        [exact HJ3 | unfold DEC_LLVMF_STK, CDec.REAC_DECODE_D; lia | unfold CDec.REAC_DECODE_D; lia].
    + exact (proj1 (dec_leafb_rng_cells W)).
    + exact (proj2 (dec_leafb_rng_cells W)).
    + intros Hl. assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
      eapply (dec_leafb_rng_block B LAWS ly S W (ms_mem ms0) md5 res len res 1492 HAR5 Hinres); lia.
    + intros Hl. assert (Hrq : req_size len = 1492) by (rewrite Hl; reflexivity).
      eapply (dec_leafb_rng_shadow_block B LAWS ly S W (ms_mem ms0) md5 res len res 1492 HAR5 Hinres); lia.
    + intros _. destruct HMODE5 as (_ & _ & _ & Hv4 & Hv8). destruct MODEF as (_ & _ & M1 & M2).
      apply (dec_leafb_rng W); [lia | lia |]. intros a Ha.
      destruct (Z_lt_dec a (mode + 8)).
      * apply (ins_t_vis_val W (ms_mem ms0) (mode + 4) 4 _ Hv4). change (Z.of_nat 4) with 4. lia.
      * apply (ins_t_vis_val W (ms_mem ms0) (mode + 8) 4 _ Hv8). change (Z.of_nat 4) with 4. lia.
    + intros _. destruct MODEF as (MRA & _ & M1 & M2).
      exact (dec_leafb_rng_shadow W (ms_mem ms0) (mode + 4) 8 MRA ltac:(lia) ltac:(lia) ltac:(lia)).
    + intros Hd. destruct (ins_t_dec_ok _ _ _ _ Hd) as (_ & _ & Hn & Hs & Ho). rewrite Holen' in Ho.
      eapply (dec_leafb_rng_block B LAWS ly S W (ms_mem ms0) md5 out olen out (3 * nch * ns) HAR5 Hinout); lia.
    + intros Hd. destruct (ins_t_dec_ok _ _ _ _ Hd) as (_ & _ & Hn & Hs & Ho). rewrite Holen' in Ho.
      eapply (dec_leafb_rng_shadow_block B LAWS ly S W (ms_mem ms0) md5 out olen out (3 * nch * ns) HAR5 Hinout); lia.
    + intros x Hx. apply (dec_leafb_wr_block B LAWS ly S W (ms_mem ms0) md5 out olen HAR5 Hinout x).
      pose proof (HWRo x Hx). lia. }
(* +0x4fc *)
cbv beta. intros W2 c2 _ (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & HRES6 & Heff6 & Hgr6 & HX6).
assert (P6 : forall r, acallee_saved r -> YK11.getr regs6 (Z_to_bv 5 r) = YK11.getr (ms_regs ms0) (Z_to_bv 5 r))
  by exact HP6.
assert (K6 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 4096 <= a < sp1 + 120) -> ~ (out <= a < out + olen) ->
  aview segs (w_H W) mem6 a = aview segs (w_H W) mem a).
{ intros a Ha H1 H2. rewrite Heff6; [exact (K5 a Ha H1 H2) | exact Ha | rewrite Usp_ms5; unfold ESTACK; lia |].
  intros Hw. apply H2. exact (HWRo a Hw). }
assert (PR6 : forall a, apresent (w_H W) mem a -> apresent (w_H W) mem6 a) by (intros a Ha; apply Hgr6, PR5, Ha).
pose proof (st_ok_region_nth E1 _ _ 0 ins_t_spill5 HS eq_refl) as RG5. cbn [ms_mem restrict] in RG5.
assert (SLm : forall off (n : nat) v, In (YP09.mkChunk off (CVal 8 (SOff n 0))) (YP09.r_chunks ins_t_spill5) ->
  ew E n = w64 v -> (n < 512)%nat -> 0 <= v < 2 ^ 64 -> 32 <= off <= 112 ->
  dec_a_slot cx (aview segs (w_H W) mem6) off v).
{ intros off n v Hin Hn Hn5 Hv Hoff.
  pose proof (field_of_region_any E1 _ 9%nat sp1 _ 32 120 40 80 off 8%N (SOff n 0) RG5 U9_1 Hin (Z.le_refl 8)) as VM.
  rewrite (ins_t_soff E1 n v (eq_trans (E1lo n Hn5) Hn) Hv) in VM.
  pose proof (ins_t_rdword_of_val_mem (w_H W) (ms_mem ms0) (sp1 + off) v VM Hv) as RW.
  unfold dec_a_slot. apply (ins_rdword_kept (w_H W) (ms_mem ms0) mem6 _ v RW).
  intros i Hi. apply Heff6; [lia | rewrite Usp_ms5; unfold ESTACK; lia |].
  intros Hw. pose proof (HWRo _ Hw). lia. }
assert (PCe : Z_to_bv 64 (VAL A_TEXT + 1276) = w64 (DEC_A_LLVMF + 0x4fc)).
{ change (w64 (DEC_A_LLVMF + 0x4fc)) with (Z_to_bv 64 (VAL A_TEXT + 1276)). reflexivity. }
apply SRr_ret. unfold llvm_a_st_4fc. cbv beta.
exists fx, ly, S, regs6, mem6, md6, res, out, mode, nch, ns.
split; [apply (f_equal (fun pc => mkCfg (@YK11.mkst fx regs6 pc mem6 (YK11.seg_rom segs)) md6));
        exact (eq_trans Rbra PCe)|].
split; [exact Hfrm|].
split.
{ apply (ins_t_core_kept cx ly S W regs regs6 mem mem6 md md6 dec_ev_3c0 dec_ev_4fc HCORE HJ6).
  - exact (eq_trans (P6 8 ltac:(unfold acallee_saved; lia)) B8).
  - exact (eq_trans (P6 9 ltac:(unfold acallee_saved; lia)) B9).
  - exact (eq_trans (f_equal bv_unsigned (P6 2 ltac:(unfold acallee_saved; lia))) Usp5).
  - exact (eq_trans (P6 3 ltac:(unfold acallee_saved; lia)) B3).
  - exact (eq_trans (P6 4 ltac:(unfold acallee_saved; lia)) B4).
  - intros a [Ha | [Ha | Ha]].
    + apply K6; lia.
    + apply K6; lia.
    + destruct (HPL a Ha) as (A1 & A2 & A3). exact (K6 a A1 A2 A3).
  - exact PR6. }
split; [exact Hbl|].
split; [exact Hres|]. split; [exact Hout|]. split; [exact MLE|]. split; [exact MOK|].
split.
{ split; [exact (eq_trans (P6 19 ltac:(unfold acallee_saved; lia)) B19)|].
  split; [exact (eq_trans (P6 21 ltac:(unfold acallee_saved; lia)) B21)|].
  exact (eq_trans (P6 27 ltac:(unfold acallee_saved; lia)) B27). }
split; [exact (HRES6 _ eq_refl)|].
split; [exact (eq_trans (P6 18 ltac:(unfold acallee_saved; lia)) B18)|].
split; [exact (eq_trans (P6 20 ltac:(unfold acallee_saved; lia)) B20)|].
split; [exact (eq_trans (P6 22 ltac:(unfold acallee_saved; lia)) B22)|].
split; [exact (eq_trans (P6 23 ltac:(unfold acallee_saved; lia)) B23)|].
split; [exact (eq_trans (P6 24 ltac:(unfold acallee_saved; lia)) B24)|].
split; [exact (eq_trans (P6 25 ltac:(unfold acallee_saved; lia)) B25)|].
split; [exact (eq_trans (P6 26 ltac:(unfold acallee_saved; lia)) B26)|].
split.
{ apply (ins_t_mode_re cx W W mem mem6 ly S md ly S md6 mode nch ns HCELLS HAR0m (proj1 HJ6) HMODE).
  intros kk Hkk. destruct (KMF kk Hkk) as (A1 & A2 & A3). exact (K6 _ A1 A2 A3). }
split.
{ apply (ins_t_fsh_kept cx (aview segs (w_H W) mem)); [|exact HFSH].
  intros i Hi. destruct (KSH i Hi) as (A1 & A2 & A3). exact (K6 _ A1 A2 A3). }
split.
{ apply (ins_garr8_kept (w_H W) mem mem6 res _ HBODY). intros j Hj. rewrite length_map in Hj. apply K6; lia. }
split.
{ intros Hd. destruct (ins_t_dec_ok _ _ _ _ Hd) as (_ & _ & Hn & Hs & Ho). rewrite Holen' in Ho.
  apply ins_t_garr8_of_bytes; [exact (HX6 Hd)|].
  intros j Hj. unfold CDec.braid_out in Hj. rewrite !length_map, length_seq in Hj. rewrite Z2Nat.id in Hj by lia.
  exact (proj1 (proj1 (Houtpres (out + j) ltac:(rewrite Hrqo; lia)))). }
split.
{ intros Hd i Hi. change (CDec.decode_ok len body nch ns = false) in Hd.
  rewrite (Heff6 (out + i)); [| lia | rewrite Usp_ms5; unfold ESTACK; lia |].
  - rewrite (KR5 (out + i)) by lia. rewrite (Heff3 i Hi). reflexivity.
  - rewrite Hd. intros Hw. unfold LCK.in_wr in Hw. apply Exists_nil in Hw. exact Hw. }
split; [exact (SLm 32 32%nat fits ltac:(ins_t_in) E32 ltac:(lia) (proj1 (HSL _ _ T32)) ltac:(lia))|].
split; [exact (SLm 40 37%nat SHADOW_OFF ltac:(ins_t_in) E37 ltac:(lia) (proj1 (HSL _ _ T40)) ltac:(lia))|].
split; [exact (SLm 48 33%nat (nch mod 2 ^ 64) ltac:(ins_t_in) E33 ltac:(lia) (proj1 (HSL _ _ T48)) ltac:(lia))|].
split; [exact (SLm 56 38%nat len ltac:(ins_t_in) E38 ltac:(lia) (proj1 (HSL _ _ T56)) ltac:(lia))|].
split; [exact (SLm 64 34%nat mode ltac:(ins_t_in) E34 ltac:(lia) (proj1 (HSL _ _ T64)) ltac:(lia))|].
split; [exact (SLm 72 22%nat out ltac:(ins_t_in) E22 ltac:(lia) ltac:(lia) ltac:(lia))|].
split; [exact (SLm 80 35%nat (nch mod 2 ^ 32) ltac:(ins_t_in) E35 ltac:(lia) (proj1 (HSL _ _ T80)) ltac:(lia))|].
split; [exact (SLm 88 36%nat (ns mod 2 ^ 64) ltac:(ins_t_in) E36 ltac:(lia) (proj1 (HSL _ _ T88)) ltac:(lia))|].
exact (SLm 112 19%nat (d_F cx) ltac:(ins_t_in) E19 ltac:(lia) (proj1 (HSL _ _ T112)) ltac:(lia)).
Qed.

(* ------------------------------------------------------------------ *)
(* The segment: +0x3c0 .. +0x4f8                                       *)
(* ------------------------------------------------------------------ *)

Theorem llvm_a_inspect_ok : @llvm_a_inspect_stmt rc asink_syms tfib_K asink_none ameta_inv arodata_okS
  RA_LLVMF A_EMPTY B MT XL RLO RHI.
Proof.
unfold llvm_a_inspect_stmt.
intros HCELLS LAWS ML MTL AMEMSET LCT LIN LDE cx W c HB HR H3c0.
destruct H3c0 as (fx & ly & S & regs & mem & md & res & out & mode & nch & ns & -> & H3).
change (w64 (DEC_A_LLVMF + 0x3c0)) with (Z_to_bv 64 (VAL A_TEXT + 0x3c0)).
eapply SRr_bind; [exact (ins_head HCELLS LAWS LCT LIN cx fx ly S W regs mem md res out mode nch ns HB H3) |].
cbv beta. intros W2 c2 _ (-> & regs4 & mem4 & md4 & -> & H4).
exact (ins_tail HCELLS LAWS AMEMSET LDE cx fx ly S W regs mem md res out mode nch ns HB H3 regs4 mem4 md4 H4).
Qed.
End si.
