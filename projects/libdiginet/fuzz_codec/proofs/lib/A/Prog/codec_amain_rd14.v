(* Segment RD14 (MASKS) of the image-A walk of LLVMFuzzerTestOneInput (fuzz_codec.asan): from the cut inv_rd .. 14
   at 0x81208 (lib/A/Prog/codec_amain_inv.v) to LATCH 0x8275c, through `jal check_text_masks` (0x82a38, with
   ra = 0x82a3c) and the `j 0x8275c` that follows it.
   The code reads n = fuzz_u32 (four input bytes) and mask = fuzz_u16 (two more); a missing byte reads 0 and the
   cursor (in.p at 152(sp1), in.n at 160(sp1)) moves by the bytes taken. The walk is cut at the three joins of
   those readers, each cut of the same shape as LATCH's (rd14_P: s10 = ops and a cursor; at 0x82a20 also a6 and
   a0, the two bytes of the mask, each below 256):
     0x81208 .. 0x82950  bytes 0 and 1, seg_rd14_holds;
     0x82950 .. 0x829bc  bytes 2 and 3, rd14_jA;
     0x829bc .. 0x82a20  bytes 4 and 5, rd14_jB;
     0x82a20 .. 0x8275c  a0 = addw (b0 + b1 << 8, (b2 | b3 << 8) << 16), the sign-extension of a 32-bit n, and
                         a1 = b5 << 8 | b4 < 2 ^ 16; check_text_masks bound through cdc_check_masks_specX with the
                         four agreements of lib/Prog/codec_text.v's masks_agree; the cut carried across the call by
                         lib/A/Prog/codec_amain_encl.v's am_call_kept and moved over the `j` by am_jump, rd14_tail.
   The input bytes are read with the shared pieces of lib/A/Prog/codec_amain_rdlib.v and codec_amain_rdin.v (the
   reader state rd_ss with an empty k window, the one-byte region rd_inr at the cursor, the obligation rd_in_obl of
   each instrumented check) over the extended token engine of lib/A/Prog/CPgTokJ.v. Each part enters the executor
   at its cut by rd_start and leaves it at the next cut by am_exit / am_mcut (rd14_out). The only bytes the walk
   writes are the cursor's sixteen (rd_zone .. 0 0). *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI00 YI04 YI09 YI08 YI16.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YO09 YE00 YE01 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw0 ACef AF0l ACej ACeh ACem ACep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A Require Import AWalkFw1 AWalkFw2 ACfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase CPgChkC CPgMainC CodecRo CodecGlobs CPgWalk.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CPgTokJ codec_amain_inv codec_amain_st.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import codec_amain_rdlib codec_amain_rdin codec_amain_encl.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require codec_text.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* the segment's atoms 37 / 38: the input bytes at the cursor and one past it *)
Definition rd14_AF : list (nat * afact) := [(37%nat, mkAF 0 255 0); (38%nat, mkAF 0 255 0)].

(* ================================ arithmetic ================================ *)
(* the 64-bit sign-extension of a 32-bit value is the register of its unsigned value (CPgBase.arg_u32A) *)
Lemma rd14_sext : forall x : bv 32, sext 64 x = w64 (DgnLib.s32 (bv_unsigned x)).
Proof.
intros x. rewrite sext64_lit. unfold w64, DgnLib.s32. f_equal.
pose proof (bv_unsigned_in_range 32 x) as R. change (bv_modulus 32) with (2 ^ 32) in R.
unfold bv_signed, bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2 ^ 31). change (bv_modulus 32) with (2 ^ 32).
destruct (Z.ltb_spec (bv_unsigned x) (2 ^ 31)).
- rewrite Z.mod_small by lia. lia.
- replace (bv_unsigned x + 2 ^ 31) with ((bv_unsigned x - 2 ^ 31) + 1 * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. rewrite Z.mod_small by lia. lia.
Qed.
(* the same at the shape a run leaves: a 32-bit value sign-extended into the register *)
Lemma rd14_arg_sext : forall x : bv 32, arg_u32A (sext 64 x) (bv_unsigned x).
Proof.
intros x. unfold arg_u32A. split.
- pose proof (bv_unsigned_in_range 32 x) as R. change (bv_modulus 32) with (2 ^ 32) in R. exact R.
- apply rd14_sext.
Qed.
(* hib << 8 | lo of two bytes (the text of lib/A/Prog/text_arg_A.v's ta_lor_byte) *)
Lemma rd14_lor_byte : forall hib lo, 0 <= hib < 256 -> 0 <= lo < 256 -> Z.lor (hib * 256) lo = lo + 256 * hib.
Proof.
intros hib lo Hh Hl.
assert (Hd : Z.land (hib * 256) lo = 0).
{ apply Z.bits_inj_0. intros i. rewrite Z.land_spec. destruct (Z_lt_le_dec i 8) as [Hi|Hi].
  - destruct (Z_lt_le_dec i 0) as [Hn|Hn]; [rewrite Z.testbit_neg_r by exact Hn; reflexivity|].
    replace (hib * 256) with (Z.shiftl hib 8) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite Z.shiftl_spec_low by exact Hi. reflexivity.
  - rewrite <- (Z.mod_small lo 256) by exact Hl. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_high by lia.
    apply Bool.andb_false_r. }
rewrite <- (Z.lxor_lor _ _ Hd). rewrite <- (Z.add_nocarry_lxor _ _ Hd). lia.
Qed.
(* a1 = (a0 << 8) | a6 at 0x82a28 / 0x82a34, with a0 and a6 two bytes (the form of text_arg_A.v's ta_U_v2) *)
Lemma rd14_U_m : forall E x4 x5, ew E 10 = Z_to_bv 64 x5 -> ew E 16 = Z_to_bv 64 x4 ->
  0 <= x4 < 256 -> 0 <= x5 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 10 0) (SLit 8)) (SOff 16 0)) = x4 + 256 * x5.
Proof.
intros E x4 x5 H10 H16 R4 R5. rewrite !U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 10 x5 H10), (U_atom E 16 x4 H16), U_SLit by lia.
change (Z.land (zcanon 8) 63) with 8. unfold zcanon, M64.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
rewrite (Z.mod_small (x5 * 256)) by lia. rewrite rd14_lor_byte by lia. apply Z.mod_small. lia.
Qed.
(* the same at the shape a run leaves *)
Lemma rd14_or_shl : forall E x4 x5, ew E 10 = Z_to_bv 64 x5 -> ew E 16 = Z_to_bv 64 x4 ->
  0 <= x4 < 256 -> 0 <= x5 < 256 ->
  alu64 ALU_OR (alu64 ALU_SLL (ew E 10) (Z_to_bv 64 8)) (ew E 16) = w64 (x4 + 256 * x5).
Proof.
intros E x4 x5 H10 H16 R4 R5.
replace (alu64 ALU_OR (alu64 ALU_SLL (ew E 10) (Z_to_bv 64 8)) (ew E 16))
  with (sv_denot E (SAlu ALU_OR (SAlu ALU_SLL (SOff 10 0) (SLit 8)) (SOff 16 0)))
  by (cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; reflexivity).
rewrite (denot_lit_U E _), (rd14_U_m E x4 x5 H10 H16 R4 R5). reflexivity.
Qed.
Lemma rd14_den_atom : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof. intros E n. cbn [sv_denot]. rewrite Z.add_0_r. apply Z_to_bv_bv_unsigned. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
(* the cut at a join of the readers: s10 = ops, a cursor, and the registers' own fact Pr *)
Definition rd14_P (g : ectx) (sp1 ops : Z) (Pr : bvmap 5 word -> Prop)
  : alayout -> astate -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
fun ly2 S2 W2 regs2 mem2 md2 => ops_at ops regs2 /\ (exists c, cur_at g sp1 c W2 mem2) /\ Pr regs2.
(* at 0x82a20: a6 is the fifth input byte and a0 the sixth, both below 256 *)
Definition rd14_Pc (regs : bvmap 5 word) : Prop :=
exists x4 x5, 0 <= x4 < 256 /\ 0 <= x5 < 256 /\ getr regs 16 = w64 x4 /\ getr regs 10 = w64 x5.
Definition rd14_Pt (regs : bvmap 5 word) : Prop := True.
(* the segment's atom list: the two input bytes it may read *)
Definition rd14_ys (g : ectx) (c : Z) : list Z := [rd_ib g c; rd_ib g (c + 1)].

Section b.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis LAWS : AR_laws tfibsegs B.

(* the cut's facts at a stop of the walk: mcommon at the stop's registers and memory, and the cursor j bytes on *)
Lemma rd14_mc : forall g pos sp1 c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 j,
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 k ->
env_agree 39 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_resv ss = None -> am_keep_ok (ss_regs ss) = true ->
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 0 0 a ->
   aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
YP09.chunk_ok tfibsegs E (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 152 (CVal 8 (SOff 35 j))) ->
YP09.chunk_ok tfibsegs E (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 160 (CVal 8 (SOff 36 (- j)))) ->
0 <= c -> 0 <= j -> c + j <= e_n g ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 /\
cur_at g sp1 (c + j) W2 (ms_mem ms).
Proof.
intros g pos sp1 c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 j HJ Hfr HC HJ3 HAG HS Hresv Hkeep KE Ca Cb Hc Hj Hcj.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
destruct (rd_zone_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (Happ & Hf4096 & Hfc & Hsp0 & Hsp & Hsp47 & Hclo).
destruct (am_facts B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
  (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hng & Hpg & Hpng & _).
unfold AM_HI in Hpng.
pose proof HS as HS'. rewrite Ems in HS'.
destruct HAG as (HA & HD).
assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (rewrite (HA 35%nat ltac:(lia)); exact (am_ew_CP g pos c regs2 ys)).
assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (rewrite (HA 36%nat ltac:(lia)); exact (am_ew_CN g pos c regs2 ys)).
assert (HAG35 : env_agree 35 (am_env g pos c regs2 ys) E)
  by (split; [intros n Hn; apply HA; lia | exact HD]).
split.
- apply (am_exit B MT K XM_LIB LAWS g pos sp1 0 0 c ys ly2 S2 W2 regs2 mem2 md2 ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3
    k (Z_to_bv 64 (ss_pc ss)) ss E HC HJ3 HAG35 HS' Hkeep).
  + intros a Ha. apply KE.
    * unfold am_keepzone in Ha. lia.
    * exact (rd_keep_apart g pos sp1 0 0 a Hf4096 Hfc Hsp0 Hsp ltac:(lia) ltac:(lia) Ha).
  + intros i Hi. pose proof HC as HSH. do 43 (destruct HSH as (_ & HSH)). destruct HSH as (HSH' & _).
    rewrite <- (HSH' i Hi). apply KE.
    * unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_mod (FA g pos) 8 ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound (FA g pos) 8 ltac:(lia)) as M. lia.
    * exact (rd_shadow_apart g pos sp1 0 0 i Happ Hf4096 Hfc Hsp0 Hsp Hclo ltac:(lia) ltac:(lia) Hi).
  + pose proof HC as HPerm. do 45 (destruct HPerm as (_ & HPerm)). exact HPerm.
- exact (rd_cur g sp1 c j W2 (ms_mem ms) E Ca Cb E35 E36 Hc Hj Hcj ltac:(lia) ltac:(lia)).
Qed.

(* the cut at a stop pc of the walk *)
Lemma rd14_out : forall g pos sp1 ops c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 pc j (Pr : bvmap 5 word -> Prop),
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2 mem2 md2 k ->
frames S2 = [(3, pos)] -> 0 <= k <= EV_LIB -> mo_le MT (e_S g) S2 0 ->
mcommon B MT K XM_LIB g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 -> ops_at ops regs2 ->
ajournal tfibsegs B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)] ly2 S2 W2
  (ms_mem ms) md3 k ->
env_agree 39 (am_env g pos c regs2 ys) E ->
st_ok tfibsegs E ss (restrict (w_H W2) ms) -> ss_pc ss = pc -> ss_resv ss = None ->
am_keep_ok (ss_regs ss) = true -> sr_get (ss_regs ss) 26%bv = SOff 26 0 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 0 0 a ->
   aview tfibsegs (w_H W2) (ms_mem ms) a = aview tfibsegs (w_H W2) mem2 a) ->
YP09.chunk_ok tfibsegs E (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 152 (CVal 8 (SOff 35 j))) ->
YP09.chunk_ok tfibsegs E (mrestrict (w_H W2) (ms_mem ms)) sp1 (YP09.mkChunk 160 (CVal 8 (SOff 36 (- j)))) ->
0 <= c -> 0 <= j -> c + j <= e_n g -> Pr (ms_regs ms) ->
mcut B MT K XM_LIB g pos sp1 0 pc (rd14_P g sp1 ops Pr) W2 {| cfg_ms := ms; cfg_model := md3 |}.
Proof.
intros g pos sp1 ops c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 pc j Pr
  HJ Hfr Hk Hmo HC Hops HJ3 HAG HS Hpc Hresv Hkeep H26 KE Ca Cb Hc Hj Hcj HPr.
destruct (rd14_mc g pos sp1 c ys ly2 S2 W2 regs2 mem2 md2 k E ss ms md3 j HJ Hfr HC HJ3 HAG HS Hresv Hkeep
  KE Ca Cb Hc Hj Hcj) as (HC3 & Hcur3).
pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) E ss ms HS Hresv) as Ems.
rewrite Hpc in Ems. rewrite Ems.
change {| cfg_ms := mkst (ms_regs ms) (Z_to_bv 64 pc) (ms_mem ms) (seg_rom tfibsegs); cfg_model := md3 |}
  with (cfg_at tfibsegs pc (ms_regs ms) (ms_mem ms) md3).
apply (am_mcut B MT K XM_LIB g pos sp1 0 pc _ ly2 S2 W2 (ms_regs ms) (ms_mem ms) md3 k HJ3 Hfr Hk Hmo HC3).
cbv beta. split.
- destruct Hops as (Hops & R26). split; [exact Hops|].
  rewrite (st_ok_restrict_reg tfibsegs (w_H W2) E ss ms 26%bv HS), H26.
  destruct HAG as (HA & _). cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (HA 26%nat ltac:(lia)).
  rewrite (am_ew_reg g pos c regs2 ys 26 26%bv eq_refl). exact R26.
- split; [exists (c + j); exact Hcur3 | exact HPr].
Qed.
End b.
End a.

(* ================================ tactics ================================ *)
(* the state of a reader cut of this segment: no k window, the two byte atoms *)
Ltac rd14_run B2 B33 EFA := cwj_run ltac:(rdj_awr B2 B33 EFA).
Ltac rd14_run_to B2 B33 EFA pc := cwj_run_to ltac:(rdj_awr B2 B33 EFA) pc.
Ltac rd14_keep B2 B33 := cw_keep ltac:(rdj_kwr B2 B33).
(* a `beqz` on in.n - j *)
Ltac rd14_brz Hb E36 :=
rewrite branch_eq_U in Hb;
lazymatch type of Hb with context [U ?Ev (SOff 36 ?o)] =>
  rewrite (cw_U_offx Ev 36 _ o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia)) in Hb end;
rewrite U_lit in Hb by lia; rewrite Z.mod_small in Hb by lia;
first [apply Z.eqb_eq in Hb | apply Z.eqb_neq in Hb].
(* a `bnez` on in.n - j *)
Ltac rd14_brne Hb E36 :=
rewrite branch_ne_U in Hb;
lazymatch type of Hb with context [U ?Ev (SOff 36 ?o)] =>
  rewrite (cw_U_offx Ev 36 _ o ltac:(rewrite ?ew_ewset_other by lia; exact E36) ltac:(lia)) in Hb end;
rewrite U_lit in Hb by lia; rewrite Z.mod_small in Hb by lia;
first [apply negb_true_iff, Z.eqb_neq in Hb | apply negb_false_iff, Z.eqb_eq in Hb].
(* a register at a stop, as the value of an atom of the base env *)
Ltac rd14_reg r EY :=
lazymatch goal with HS : YP0l.st_ok _ ?Ev ?ssx (restrict (w_H ?Wx) ?msx) |- _ =>
  rewrite (st_ok_restrict_reg tfibsegs (w_H Wx) Ev ssx msx (r : bv 5) HS);
  let e := eval vm_compute in (sr_get (ss_regs ssx) (r : bv 5)) in
  change (sr_get (ss_regs ssx) (r : bv 5)) with e end;
first [ reflexivity
      | rewrite rd14_den_atom, ?ew_ewset_other by lia; rewrite EY; reflexivity ].

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Variable K : asink_syms.
Variable XM_LIB : Z -> Z.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : TfibLib B.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis CMASKS : cdc_check_masks_specX tfibsegs B MT AM_check_masks.

(* the common prelude of the four parts: the numbers of the cut, the entry state, the base atoms *)
Ltac rd14_pre HJ0 pc :=
lazymatch goal with
| HJ : ajournal tfibsegs ?Bv _ _ _ _ _ _ _ _ [(3, ?pos)] ?ly2 ?S2 ?W2 ?mem2 ?md2 ?k,
  Hfr : frames ?S2 = [(3, ?pos)],
  HC : mcommon ?Bv ?MTv ?Kv ?XMv ?g ?pos ?sp1 0 ?ly2 ?S2 ?W2 ?regs2 ?mem2 ?md2,
  Hcur : cur_at ?g ?sp1 ?c ?W2 ?mem2 |- _ =>
  destruct (am_facts Bv MTv Kv XMv LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as
    (EFA & Hf64 & Hf4096 & Hfceil & FS3 & Hchi & Hclo & Hsp32 & Hsp & Hsp0c & Hsp047 & Hsp016 & Hpres &
     Hn & Hp & Hpn & Hblk);
  unfold AM_HI in Hchi, Hpn;
  pose proof Hcur as (Hc & C152 & C160);
  pose proof Hwx_tfa as Hwx; pose proof tfib_segs_low as Hsegs;
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
  assert (FFS : LLVMF_STK = 32768) by reflexivity;
  assert (HAF : atoms_ok (am_env g pos c regs2 (rd14_ys g c)) rd14_AF)
    by (unfold rd14_AF; cbn [atoms_ok]; unfold afact_ok; cbn [af_lo af_hi af_al2];
        pose proof (am_ew_y g pos c regs2 (rd14_ys g c) 0) as Y0;
        pose proof (am_ew_y g pos c regs2 (rd14_ys g c) 1) as Y1;
        unfold AM_X0 in Y0, Y1; cbn [Nat.add] in Y0, Y1; rewrite Y0, Y1;
        unfold rd14_ys; cbn [nth];
        pose proof (rd_ib_range g c); pose proof (rd_ib_range g (c + 1));
        rewrite !unsigned_lit_small by lia; rewrite !Z.pow_0_r, !Z.mod_1_r; repeat split; lia);
  destruct (rd_start Bv MTv Kv XMv TL LAWS g pos sp1 ly2 S2 W2 regs2 mem2 md2 k c (rd14_ys g c) rd14_AF pc 0 0 []
    HJ Hfr HC Hcur ltac:(lia) ltac:(lia) ltac:(lia) (Forall_nil _) eq_refl HAF) as [HS SHOK];
  assert (HAE : env_agree 39 (am_env g pos c regs2 (rd14_ys g c)) (am_env g pos c regs2 (rd14_ys g c)))
    by apply env_agree_refl;
  remember (am_env g pos c regs2 (rd14_ys g c)) as E eqn:HEE;
  assert (B2 : bv_unsigned (ew E 2) = sp1)
    by (subst E; pose proof HC as (_ & _ & R2 & _);
        rewrite (am_ew_reg g pos c regs2 (rd14_ys g c) 2 2%bv eq_refl), R2; unfold w64;
        apply unsigned_lit_small; lia);
  assert (B33 : bv_unsigned (ew E 33) = FA g pos)
    by (subst E; rewrite (am_ew_F g pos c regs2 (rd14_ys g c)); apply unsigned_lit_small; lia);
  assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; exact (am_ew_SB g pos c regs2 (rd14_ys g c)));
  assert (E35 : ew E 35 = Z_to_bv 64 (e_p g + c)) by (subst E; exact (am_ew_CP g pos c regs2 (rd14_ys g c)));
  assert (E36 : ew E 36 = Z_to_bv 64 (e_n g - c)) by (subst E; exact (am_ew_CN g pos c regs2 (rd14_ys g c)));
  assert (EY0 : ew E 37 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 0)))
    by (subst E; rewrite Z.add_0_r; exact (am_ew_y g pos c regs2 (rd14_ys g c) 0));
  assert (EY1 : ew E 38 = Z_to_bv 64 (rd_ib g (c + Z.of_nat 1)))
    by (subst E; exact (am_ew_y g pos c regs2 (rd14_ys g c) 1));
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ rd_zone g pos sp1 0 0 a ->
    aview tfibsegs (w_H W2) mem2 a = aview tfibsegs (w_H W2) mem2 a) by (intros; reflexivity);
  pose proof (rd_in_sep Bv MTv Kv XMv LAWS g pos sp1 0 ly2 S2 W2 regs2 mem2 md2 k HJ Hfr HC) as HSEP;
  cw_keep_j0 HJ HJ0;
  unfold cfg_at; change (w64 pc) with (Z_to_bv 64 pc)
end.
(* the cut at the stop, with the register fact Pr *)
Ltac rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE pc j Pr :=
lazymatch goal with
| HS : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  lazymatch type of HC with
  | mcommon ?Bv ?MTv ?Kv ?XMv ?g ?pos ?sp1 0 ?ly2 ?S2 ?W ?regs2 ?mem2 ?md2 =>
    lazymatch type of Hops with
    | ops_at ?ops _ =>
      lazymatch type of Hcur with
      | cur_at _ _ ?c _ _ =>
        let Ca := fresh "Ca" in let Cb := fresh "Cb" in
        rd_chunk HS 2%nat 152 Ca; rd_chunk HS 2%nat 160 Cb;
        rewrite ?ew_ewset_other in Ca, Cb by lia; rewrite B2 in Ca, Cb;
        rewrite ?wvb_collapse in HJm;
        apply (rd14_out Bv MTv Kv XMv LAWS g pos sp1 ops c (rd14_ys g c) ly2 S2 W regs2 mem2 md2 _ Ef ssf msf _
          pc j Pr HJ0 Hfr Hk Hmo HC Hops HJm
          ltac:(rewrite <- HEE; env_agree_chain HAE) HS ltac:(reflexivity) ltac:(reflexivity)
          ltac:(vm_compute; reflexivity) ltac:(reflexivity) KE Ca Cb ltac:(lia) ltac:(lia) ltac:(lia))
      end end end
end.

(* 0x82a20 .. 0x82a38: the two arguments; `jal check_text_masks`; 0x82a3c `j 0x8275c` *)
Lemma rd14_tail : forall g pos sp1 ops W2 c2,
  mcut B MT K XM_LIB g pos sp1 0 0x82a20 (rd14_P g sp1 ops rd14_Pc) W2 c2 ->
  SRr tfibsegs W2 c2 (inv_latch B MT K XM_LIB g pos sp1 ops).
Proof using MTL TL LAWS CMASKS.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & Hcur) &
  (x4 & x5 & Hx4 & Hx5 & R16 & R10)).
rd14_pre HJ0 0x82a20.
assert (E10 : ew E 10 = Z_to_bv 64 x5)
  by (subst E; exact (eq_trans (am_ew_reg g pos c regs2 (rd14_ys g c) 10 10%bv eq_refl) R10)).
assert (E16 : ew E 16 = Z_to_bv 64 x4)
  by (subst E; exact (eq_trans (am_ew_reg g pos c regs2 (rd14_ys g c) 16 16%bv eq_refl) R16)).
pose proof HC as (Hpre & _).
pose proof Hpre as HPRE. unfold e_pre, codec_lib_pre_x in HPRE.
destruct HPRE as (HFN & Hra0 & Hq10 & Hq11 & Hpn0 & Hnpl & HPL & Hfr0 & Hev0 & Hlive0 & HROS & HSNK & HFD & HSORT &
  HAM & HMOK).
pose proof HC as HPerm0. do 45 (destruct HPerm0 as (_ & HPerm0)).
pose proof HC as (_ & _ & R2x & _ & _ & R3x & R4x & _).
(* 0x82a20 .. 0x82a38: the two arguments and the `jal`; stop at check_text_masks's entry *)
rd14_run_to B2 B33 EFA 0x842b0. rd14_keep B2 B33.
rreg HS (1%bv : bv 5) G1. rreg HS (2%bv : bv 5) G2. rreg HS (3%bv : bv 5) G3. rreg HS (4%bv : bv 5) G4.
rreg HS (10%bv : bv 5) G10. rreg HS (11%bv : bv 5) G11. rreg HS (26%bv : bv 5) G26.
(* the cut's facts at the call state *)
lazymatch goal with HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ => rewrite ?wvb_collapse in HJm end.
rd_chunk HS 2%nat 152 Ca. rd_chunk HS 2%nat 160 Cb.
rewrite ?ew_ewset_other in Ca, Cb by lia. rewrite B2 in Ca, Cb.
lazymatch goal with
| HS : YP0l.st_ok _ ?Ef ?ssf (restrict (w_H ?W) ?msf), HJm : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
  destruct (rd14_mc B MT K XM_LIB LAWS g pos sp1 c (rd14_ys g c) ly2 S2 W regs2 mem2 md2 _ Ef ssf msf _ 0
    HJ0 Hfr HC HJm ltac:(rewrite <- HEE; env_agree_chain HAE) HS ltac:(reflexivity)
    ltac:(vm_compute; reflexivity) KE Ca Cb ltac:(lia) ltac:(lia) ltac:(lia)) as (HCc & Hcurc)
end.
(* the state at the call *)
lazymatch goal with HS : YP0l.st_ok _ _ ?ssx (restrict _ ?msx) |- _ =>
  let Hshape := fresh "Hshape" in
  pose proof (st_ok_restrict_mkst tfibsegs (w_H W2) _ ssx msx HS eq_refl) as Hshape;
  cbn [ss_pc] in Hshape; rewrite Hshape in HS |- *; clear Hshape end.
(* the two arguments *)
lazymatch type of G10 with getr _ _ = sext 64 ?x => pose proof (rd14_arg_sext x) as HA0 end.
rewrite <- G10 in HA0.
assert (HA1 : arg_zxA 16 (getr (ms_regs ms) 11) (x4 + 256 * x5)).
{ split; [lia|]. rewrite G11.
  lazymatch type of G11 with _ = alu64 _ (alu64 _ (ew ?Ev _) _) _ =>
    apply (rd14_or_shl Ev x4 x5 ltac:(rewrite ?ew_ewset_other by lia; exact E10)
      ltac:(rewrite ?ew_ewset_other by lia; exact E16) Hx4 Hx5) end. }
destruct (codec_text.masks_agree _ (x4 + 256 * x5) (proj1 HA0) ltac:(lia)) as (A1 & A2 & A3 & A4).
(* check_text_masks through its contract *)
eapply SRr_bind.
{ eapply (CMASKS LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(3, pos)]
    ly2 S2 W2 (ms_mem ms) _ k (ms_regs ms) _ (x4 + 256 * x5)).
  - split; [eassumption|].
    split; [rewrite G1; apply ret_ok_even; vm_compute; reflexivity|].
    split; [unfold raZ; rewrite G1, unsigned_lit_small by lia; lia|].
    split; [rewrite G3, ?ew_ewset_other by lia; subst E;
            rewrite (am_ew_reg g pos c regs2 (rd14_ys g c) 3 3%bv eq_refl); exact R3x|].
    split; [rewrite G4, ?ew_ewset_other by lia; subst E;
            rewrite (am_ew_reg g pos c regs2 (rd14_ys g c) 4 4%bv eq_refl); exact R4x|].
    assert (Hsp2 : spZ (ms_regs ms) = sp1)
      by (unfold spZ; rewrite G2, ?ew_ewset_other by lia; exact B2).
    split; [rewrite Hsp2; pose proof (Z.div_mod sp1 32 ltac:(lia)) as Dm; rewrite Hsp32, Z.add_0_r in Dm;
            rewrite Dm; replace (32 * (sp1 / 32)) with ((2 * (sp1 / 32)) * 16) by lia; apply Z_mod_mult|].
    split; [rewrite Hsp2; unfold T_check_masks; lia|].
    split; [rewrite Hsp2; lia|].
    split; [unfold EV_CDC, EV_LIB in *; lia|].
    rewrite (blocks_bytes_bsum B ly2 S2), (bsum_perm _ _ HPerm0), <- (blocks_bytes_bsum B (e_ly g) (e_S g)).
    unfold LIVE_CDC, LIVE_LIB in *. lia.
  - exact HA0.
  - exact HA1.
  - exact A1.
  - exact A2.
  - exact A3.
  - exact A4. }
cbv beta. intros W3 c3 Hwle HP.
destruct HP as (ly3 & S3 & regs3 & mem3 & md4 & -> & HJ4 & HPR & Hfrs3 & HPerm3 & HIO3 & HMLE3 & HK3 & _).
unfold EV_CDC in HJ4. rewrite Z.add_0_r in HJ4.
destruct (am_call_kept B MT K XM_LIB LAWS g pos sp1 0 ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ _ (c + 0)
  T_check_masks cno_wr ly3 S3 W3 regs3 mem3 md4 _ HJ Hfr HCc Hcurc
  ltac:(intros aa Ha; destruct Ha) HJ4 HPR HPerm3 HK3) as (HC4 & Hcur4 & _).
(* 0x82a3c `j 0x8275c` *)
rewrite G1. cbn [sv_denot].
change (mkCfg (mkst regs3 (Z_to_bv 64 535100) mem3 (seg_rom tfibsegs)) md4)
  with (cfg_at tfibsegs 0x82a3c regs3 mem3 md4).
unfold inv_latch.
eapply (am_jump B MT K XM_LIB LAWS g pos sp1 0 0x82a3c PC_LATCH _ W3 _);
  [vm_compute; reflexivity | unfold PC_LATCH; lia | intros ? ? ? ? ? ? ? HPx; exact HPx |].
apply (am_mcut B MT K XM_LIB g pos sp1 0 0x82a3c _ ly3 S3 W3 regs3 mem3 md4 k HJ4
  ltac:(rewrite Hfrs3; exact Hfr) Hk (mo_le_trans MT MTL _ _ _ 0 0 Hmo HMLE3) HC4).
cbv beta. split.
- destruct Hops as (Hops & R26). split; [exact Hops|].
  assert (H26' : getr regs3 26 = getr (ms_regs ms) 26) by exact (HPR 26 ltac:(unfold acallee_saved; lia)).
  rewrite H26', G26, ?ew_ewset_other by lia.
  subst E. rewrite (am_ew_reg g pos c regs2 (rd14_ys g c) 26 26%bv eq_refl). exact R26.
- exists (c + 0). exact Hcur4.
Qed.

(* 0x829bc .. 0x82a20: the fifth and sixth input bytes (a6 and a0) *)
Lemma rd14_jB : forall g pos sp1 ops W2 c2,
  mcut B MT K XM_LIB g pos sp1 0 0x829bc (rd14_P g sp1 ops rd14_Pt) W2 c2 ->
  SRr tfibsegs W2 c2 (inv_latch B MT K XM_LIB g pos sp1 ops).
Proof using MTL TL LAWS CMASKS.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & Hcur) & _).
rd14_pre HJ0 0x829bc.
(* 0x829bc ld a7,160(s1); 0x829c0 beqz a7 *)
rd14_run B2 B33 EFA. rd14_keep B2 B33.
cw_branch Hb1; rd14_brz Hb1 E36.
- (* no byte left: 0x82a18 li a6,0; 0x82a1c li a0,0 *)
  rd14_run_to B2 B33 EFA 0x82a20. rd14_keep B2 B33.
  apply rd14_tail. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x82a20 0 rd14_Pc.
  exists 0, 0. split; [lia|]. split; [lia|]. split; [rd14_reg (16%bv : bv 5) EY0 | rd14_reg (10%bv : bv 5) EY0].
- (* a byte is left: its check, then 0x829ec beqz t0 *)
  rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
  rd14_run B2 B33 EFA. try (rd_obl LAWS HJ0 Hfr HC c E35 E32). rd14_keep B2 B33.
  cw_branch Hb2; rd14_brz Hb2 E36.
  + (* exactly one byte: 0x82a1c li a0,0 *)
    rd14_run_to B2 B33 EFA 0x82a20. rd14_keep B2 B33.
    apply rd14_tail. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x82a20 1 rd14_Pc.
    exists (rd_ib g (c + Z.of_nat 0)), 0.
    pose proof (rd_ib_range g (c + Z.of_nat 0)).
    split; [lia|]. split; [lia|]. split; [rd14_reg (16%bv : bv 5) EY0 | rd14_reg (10%bv : bv 5) EY0].
  + (* two bytes: the second check, 0x82a10 lbu a0, 0x82a14 j 0x82a20 *)
    rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
    rd14_run_to B2 B33 EFA 0x82a20. try (rd_obl LAWS HJ0 Hfr HC c E35 E32). rd14_keep B2 B33.
    apply rd14_tail. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x82a20 2 rd14_Pc.
    exists (rd_ib g (c + Z.of_nat 0)), (rd_ib g (c + Z.of_nat 1)).
    pose proof (rd_ib_range g (c + Z.of_nat 0)). pose proof (rd_ib_range g (c + Z.of_nat 1)).
    split; [lia|]. split; [lia|]. split; [rd14_reg (16%bv : bv 5) EY0 | rd14_reg (10%bv : bv 5) EY1].
Qed.

(* 0x82950 .. 0x829bc: the third and fourth input bytes (a4 and a5), both dead at the next cut *)
Lemma rd14_jA : forall g pos sp1 ops W2 c2,
  mcut B MT K XM_LIB g pos sp1 0 0x82950 (rd14_P g sp1 ops rd14_Pt) W2 c2 ->
  SRr tfibsegs W2 c2 (inv_latch B MT K XM_LIB g pos sp1 ops).
Proof using MTL TL LAWS CMASKS.
intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & (c & Hcur) & _).
rd14_pre HJ0 0x82950.
rd14_run B2 B33 EFA. rd14_keep B2 B33.
cw_branch Hb1; rd14_brz Hb1 E36.
- (* no byte left: 0x829b8 li a4,0 *)
  rd14_run_to B2 B33 EFA 0x829bc. rd14_keep B2 B33.
  apply rd14_jB. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x829bc 0 rd14_Pt. exact I.
- rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
  rd14_run B2 B33 EFA. try (rd_obl LAWS HJ0 Hfr HC c E35 E32). rd14_keep B2 B33.
  cw_branch Hb2; rd14_brz Hb2 E36.
  + (* exactly one byte: 0x829b0 li a5,0; j 0x829bc *)
    rd14_run_to B2 B33 EFA 0x829bc. rd14_keep B2 B33.
    apply rd14_jB. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x829bc 1 rd14_Pt. exact I.
  + (* two bytes: the second check, 0x829a4 lbu a5, slli, j 0x829bc *)
    rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
    rd14_run_to B2 B33 EFA 0x829bc. try (rd_obl LAWS HJ0 Hfr HC c E35 E32). rd14_keep B2 B33.
    apply rd14_jB. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x829bc 2 rd14_Pt. exact I.
Qed.

(* 0x81208 .. 0x82950: the first and second input bytes (a2 and a3) *)
Theorem seg_rd14_holds : seg_rd14 B MT K XM_LIB.
Proof using MTL TL LAWS CMASKS.
unfold seg_rd14. intros g pos sp1 ops W2 c2 H.
destruct H as (ly2 & S2 & regs2 & mem2 & md2 & k & -> & HJ & Hfr & Hk & Hmo & HC & Hops & Hkind &
  (c & pv & dv & od & Hcur & Hc1 & Hpd & R23 & Hkat)).
replace (rd_pc 14) with 0x81208 by (vm_compute; reflexivity).
rd14_pre HJ0 0x81208.
(* 0x81208 ld a3,160(s1); 0x8120c beqz a3 *)
rd14_run B2 B33 EFA. rd14_keep B2 B33.
cw_branch Hb1; rd14_brz Hb1 E36.
- (* no byte left: 0x81320, 0x829b0, 0x829bc *)
  rd14_run_to B2 B33 EFA 0x829bc. rd14_keep B2 B33.
  apply rd14_jB. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x829bc 0 rd14_Pt. exact I.
- rd_in_add LAWS HJ0 Hfr HC c 0%nat E35 EY0 HSEP.
  rd14_run B2 B33 EFA. try (rd_obl LAWS HJ0 Hfr HC c E35 E32). rd14_keep B2 B33.
  (* 0x8123c bnez a4 *)
  cw_branch Hb2; rd14_brne Hb2 E36.
  + (* two bytes: the second check, 0x81268 lbu a3, slli, j 0x82950 *)
    rd_in_add LAWS HJ0 Hfr HC c 1%nat E35 EY1 HSEP.
    rd14_run_to B2 B33 EFA 0x82950. try (rd_obl LAWS HJ0 Hfr HC c E35 E32). rd14_keep B2 B33.
    apply rd14_jA. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x82950 2 rd14_Pt. exact I.
  + (* exactly one byte: 0x81240 j 0x8294c; li a3,0 *)
    rd14_run_to B2 B33 EFA 0x82950. rd14_keep B2 B33.
    apply rd14_jA. rd14_exit HJ0 Hfr Hk Hmo HC Hops Hcur HAE HEE B2 KE 0x82950 1 rd14_Pt. exact I.
Qed.

End d.
End c.
