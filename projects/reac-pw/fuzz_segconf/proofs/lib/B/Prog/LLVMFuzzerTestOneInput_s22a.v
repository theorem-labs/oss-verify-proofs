(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PutStringB_Base.v, with its module paths and module names changed; 702 of its 770 lines of code are new or changed and 1945 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): piece 1 of segment
   S14 of the walk of the test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), S14 piece a: the
   statement s22_p1_stmt of LLVMFuzzerTestOneInput_s22k.v, from the head of the inlined m_declared loop at turn i
   (cut K85b0c i, 0x85b0c) to the continue join (S22_JOIN, 0x85b58) when m->seg[i].ignore is set, or to the return
   of the strrchr wrapper (S22_VR, 0x85ba4) when it is not.

   proves function LLVMFuzzerTestOneInput (segment S14 piece only; reuse search, rule 24: released units, the earlier
   proof delivery and working heads; the result is recorded with the commissioning brief; none: written new).

   THE FORM: plugin-hostd/fuzz_command's lib/A/Prog/chain_words_s1.v (a plain run through stores to the frame's
   shadow, the region fshadow_region, its write permission by awr_byte's in_frames disjunct) and its harness walk's
   LLVMFuzzerTestOneInput_s45.v (a string wrapper taken by PaArt.aj_art_at), at origin/ossv/recipes 3abc3740de97;
   the seed of image A's twin piece (the LLVMFuzzerTestOneInput_s22a.v of image A's S14 walk (piece a), in progress,
   sha256 186ccb366a88: the alias of m + (i << 8), the shadow byte of the ignore word as a region of literal 0),
   renamed to image B's registers and slots; the keep facts of image B's S21 / ret kit (image B's S21 / ret commit
   315447ae529c, LLVMFuzzerTestOneInput_s25k.v s25_img_kept / s25_lit_kept) and S01 / S02 kit (image B's S01 / S02
   commit c9accd8a8a50, LLVMFuzzerTestOneInput_s12k.v lk_hblk / lk_word_kept / lk_pres_reg).

   The code (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s:853-890, SegList.v:902-939):
   - 0x85b0c .. 0x85b1c: a0 := 184(s1) = SH(FR); sb zero,4(a0); sb zero,5(a0); sb 4,6(a0): v's three shadow bytes
     00 00 04 (v in scope, LFO_N -> LFO_NV);
   - 0x85b20 .. 0x85b24: the UBSan trap i = 32 (beq s4,32), decided in the run by the fact 0 <= i <= 31 (i < m->n <=
     32, sa_mconf);
   - 0x85b28 .. 0x85b30: the UBSan trap M + 256 i wraps (bltu ~M, i << 8), decided in the run by the facts ~M >= 2^63
     (208(s1) = ~M, M + 9236 <= 2^63 by lt_hblk's sa_addr) and i << 8 <= 7936;
   - 0x85b34 .. 0x85b4c: s8 := 192(s1) = m, s3 := m + (i << 8) (an alias of the seed names it as s11's atom), a0 :=
     s3 + 24, and the instrumented check of the 4-byte word at a0: the seed holds its shadow byte (0, the block m is
     addressable over the whole granule) through an alias of (a0 >> 3) + a6, so the run reads 0 and bnez a1 falls
     through; the slow block 0x85e18 is never entered;
   - 0x85b50 .. 0x85b54: lw a0,0(a0) (m->seg[i].ignore, seg_spec.mseg_enc's flag), beqz a0: split; not taken: one
     step to the join 0x85b58, closed by S22_JOIN_stmt with x_decl (S i) = x_decl i (s22_decl_step_skip, ignore set);
   - 0x85b98 .. 0x85ba0: a1 := 46, a0 := s3, jal of the strrchr wrapper, taken by RtSeg.astrrchr_realizes through
     PaArt.aj_art_at over the segment's name (s22_name_str), closed by S22_VR_stmt with the answer turned into
     SegModel.strrchr's by s22_strrchr_none / s22_strrchr_some.
   Every cut fact between the two points is carried by p1_keep: the run writes only v's three shadow bytes and the
   wrapper only its scratch window below s1.

   Section hypotheses: TL (PALib: the errno cell's environment api_env for aj_art_at) and ASTRRCHR (the strrchr
   wrapper's row, RtSeg.astrrchr_realizes at pa_sigma SS___interceptor_trampoline_strrchr). LAWS is
   YG0q.AR_laws_ok. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaStep PaShadow SegSyms SegList SegPa PaJournal SegPaLib PaDenot PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaLibF PaLibG PaCall PaArt PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s22k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the symbolic state at V0 = 0x85b0c ----
   Every register is its own atom. Extra atoms: 32 = SH(FR) (the word at 184(s1)), 33 = m (192(s1)), 34 = ~m
   (208(s1)), 35 = g, the word m->seg[i].ignore (0 or 1), 36 = the shadow byte's address of &m->seg[i].ignore.
   Regions: the three s1 slots (atom 9 = s1), read only; the frame's 64 shadow bytes at SH(FR), written only in
   [4, 7) (v's three bytes); the ignore word at s11 + 24 (atom 27 = &m->seg[i]); its shadow byte (atom 36), which
   holds 0. Aliases: m + (i << 8) is s11's atom; (s11 + 24 >> 3) + a6 is atom 36. Facts: i in [0, 31] (atom 20 = s4),
   ~m in [2^63, 2^64 - 1], g in [0, 1]. *)
Definition p1_s1 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 216 0 0
    [YP09.mkChunk 184 (CVal 8 (SOff 32 0)); YP09.mkChunk 192 (CVal 8 (SOff 33 0));
     YP09.mkChunk 208 (CVal 8 (SOff 34 0))].
Definition p1_sh : YP09.region := fshadow_region 32 3 4 7 [].
Definition p1_ig : YP09.region := YP09.mkRegion (Some 27%nat) 24 28 0 0 [YP09.mkChunk 24 (CVal 4 (SOff 35 0))].
Definition p1_igsh : YP09.region := YP09.mkRegion (Some 36%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition p1_al_s3 : sv * sv := (SAlu ALU_ADD (SOff 33 0) (SAlu ALU_SLL (SOff 20 0) (SLit 8)), SOff 27 0).
Definition p1_al_sh : sv * sv := (SAlu ALU_ADD (SAlu ALU_SRL (SOff 27 24) (SLit 3)) (SOff 16 0), SOff 36 0).
Definition p1_facts : facts :=
  mkFacts [(20%nat, mkAF 0 31 0); (34%nat, mkAF 9223372036854775808 18446744073709551615 0); (35%nat, mkAF 0 1 0)]
    [] [p1_al_s3; p1_al_sh].
Definition ss_p1 : sstate := mkSS LO_K85b0c sr_atoms [p1_s1; p1_sh; p1_ig; p1_igsh] None p1_facts.

(* the write permission of the runs: every region but the frame's shadow is read only; the shadow window's bytes are
   given by HSHF *)
Ltac p1_awr HSHF U :=
  lazymatch goal with |- awr_ok ?sg ?Bv ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?f0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg Bv Ex rs' stk spx fp b0 bc f0 lyx own) end;
  repeat first
    [ apply awr_ok_nil
    | apply awr_ok_cons_ro; [cbn; lia|]
    | eapply awr_ok_cons_gen;
      [ reflexivity | exact U
      | let a := fresh "a" in let Ha := fresh "Ha" in
        intros a Ha; cbn [YP09.r_wlo YP09.r_whi] in Ha; apply HSHF; lia
      | ] ].

(* a byte outside the runs' write windows is kept (the windows are the frame's shadow [4, 7) only) *)
Ltac p1_nowin HFr U :=
  apply aview_eq_of; apply HFr; rewrite unsigned_lit_small by lia;
  let r := fresh "r" in let Hin := fresh "Hin" in let Hrg := fresh "Hrg" in
  intros (r & Hin & Hrg);
  cbn [In ss_mem add_cond ss_p1] in Hin;
  repeat (destruct Hin as [<- | Hin];
    [ cbn [p1_s1 p1_sh p1_ig p1_igsh fshadow_region YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hrg;
      first [ lia | rewrite U in Hrg; lia ] |]);
  destruct Hin.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition p1_E (regs : bvmap 5 word) (xs : list Z) : env := Eimg (Ereg regs (map (Z_to_bv 64) xs)).

Lemma p1_E_reg : forall regs xs n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (p1_E regs xs) n = getr regs r.
Proof.
intros regs xs n r Hn. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold p1_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma p1_E_extra : forall regs xs j, (j < length xs)%nat -> (32 + j < A_TEXT)%nat ->
  ew (p1_E regs xs) (32 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
intros regs xs j Hj Hj2. unfold p1_E. rewrite Eimg_low by exact Hj2.
rewrite ew_Ereg_extra. apply map_nth.
Qed.

(* a value read through the reader is a value of the restricted memory (image A's twin, p1_val_mem) *)
Lemma p1_val_mem : forall H mem a n v, sa_val (aview SEGS H mem) a n v -> val_mem SEGS (mrestrict H mem) a n v.
Proof.
intros H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte SEGS (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:E; [|cbn [option_map] in Hv; discriminate].
cbn [option_map] in Hv. injection Hv as Hv. f_equal.
first [ rewrite <- Hv
      | change (YG0f.le_byte v n k) with (YO0f.le_byte v n k) in *; rewrite <- Hv
      | change (YO0f.le_byte v n k) with (YG0f.le_byte v n k) in *; rewrite <- Hv
      | unfold YG0f.le_byte, YO0f.le_byte in *; rewrite <- Hv ].
symmetry. apply Z_to_bv_bv_unsigned.
Qed.
(* a word read through the reader is a 64-bit value *)
Lemma p1_rdword_rng : forall H mem a v, rdword (aview SEGS H mem) a = Some v -> 0 <= v < 2 ^ 64.
Proof.
intros H mem a v E. unfold rdword in E.
destruct (aview SEGS H mem a) as [b0|] eqn:E0; [|discriminate].
destruct (aview SEGS H mem (a + 1)) as [b1|] eqn:E1; [|discriminate].
destruct (aview SEGS H mem (a + 2)) as [b2|] eqn:E2; [|discriminate].
destruct (aview SEGS H mem (a + 3)) as [b3|] eqn:E3; [|discriminate].
destruct (aview SEGS H mem (a + 4)) as [b4|] eqn:E4; [|discriminate].
destruct (aview SEGS H mem (a + 5)) as [b5|] eqn:E5; [|discriminate].
destruct (aview SEGS H mem (a + 6)) as [b6|] eqn:E6; [|discriminate].
destruct (aview SEGS H mem (a + 7)) as [b7|] eqn:E7; [|discriminate].
injection E as <-.
pose proof (sa_aview_rng _ _ _ _ _ E0). pose proof (sa_aview_rng _ _ _ _ _ E1).
pose proof (sa_aview_rng _ _ _ _ _ E2). pose proof (sa_aview_rng _ _ _ _ _ E3).
pose proof (sa_aview_rng _ _ _ _ _ E4). pose proof (sa_aview_rng _ _ _ _ _ E5).
pose proof (sa_aview_rng _ _ _ _ _ E6). pose proof (sa_aview_rng _ _ _ _ _ E7).
lia.
Qed.
(* the chunks of the seed, from the reader's bytes *)
Lemma p1_chunk8 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> rdword (rdW W mem) (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 8 (SOff n 0))).
Proof.
intros W mem E base off n v En Hrd.
pose proof (p1_rdword_rng _ _ _ _ Hrd) as R.
apply (chunk_ok_val SEGS E _ base off 8 _ v); [| change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); exact R | cbn; lia |].
- cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- exact (val_mem_of_rdword SEGS _ _ _ _ Hrd).
Qed.
Lemma p1_chunk4 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> sa_val (rdW W mem) (base + off) 4 v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 4 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (chunk_ok_val SEGS E _ base off 4 _ v); [| change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hv | cbn; lia |].
- cbn [sv_denot]. rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- exact (p1_val_mem _ _ _ 4 _ Hrd).
Qed.
Lemma p1_chunk1z : forall (W : world SEGS) mem E base,
  rdW W mem base = Some 0 -> YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk 0 (CVal 1 (SLit 0))).
Proof.
intros W mem E base Hb.
apply (chunk_ok_val SEGS E _ base 0 1 _ 0); [reflexivity | change (2 ^ (8 * Z.of_N 1)) with 256; lia | cbn; lia |].
apply (p1_val_mem _ _ _ 1 0). intros k Hk. destruct k as [|k]; [|lia]. rewrite Z.add_0_r, Z.add_0_r. exact Hb.
Qed.
(* a byte the symbolic state holds as a literal chunk of a region, read back through the reader *)
Lemma p1_rd1 : forall E (H : word -> bool) mem n b lo hi wlo whi cs off v,
  YP09.region_ok SEGS E (mrestrict H mem) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk off (CVal 1 (SLit v))) cs -> 0 <= v < 256 ->
  aview SEGS H mem (b + off) = Some v.
Proof.
intros E H mem n b lo hi wlo whi cs off v HR Hb Hin Hv.
pose proof (field_of_region_any (segs := SEGS) E _ n b cs lo hi wlo whi off 1%N (SLit v) HR Hb Hin
  ltac:(cbn; lia)) as HV.
specialize (HV 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in HV.
replace (bv_unsigned (sv_denot E (SLit v)) mod 2 ^ (8 * Z.of_N 1)) with v in HV
  by (cbn [sv_denot]; rewrite unsigned_lit_small by lia; symmetry; apply Z.mod_small; cbn; lia).
unfold aview. rewrite HV. cbn [option_map]. f_equal.
rewrite le_byte_small by (cbn; lia).
change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.

(* ---- seed: the state at 0x85b0c is an instance of ss_p1 ---- *)
Lemma p1_seed : forall (W : world SEGS) (regs : bvmap 5 word) mem s1 sh m x iz g,
  getr regs 9 = w64 s1 -> getr regs 16 = w64 SHADOW_OFF -> getr regs 20 = w64 iz -> getr regs 27 = w64 x ->
  x = m + 256 * iz -> 0 <= iz <= 31 -> 0 <= m -> m + 9236 <= s1 -> 0 <= g <= 1 ->
  0x7fff7f800000 <= s1 -> s1 + 216 <= 2 ^ 47 -> SHADOW_OFF <= sh -> sh + 64 <= s1 ->
  (forall o, 4 <= o < 7 -> apresent (w_H W) mem (sh + o)) ->
  rdword (rdW W mem) (s1 + 184) = Some sh -> rdword (rdW W mem) (s1 + 192) = Some m ->
  rdword (rdW W mem) (s1 + 208) = Some (lt_not m) ->
  sa_val (rdW W mem) (x + 24) 4 g -> rdW W mem (SHADOW_OFF + (x + 24) / 8) = Some 0 ->
  (sh + 64 <= x + 24 \/ x + 28 <= sh) ->
  (sh + 64 <= SHADOW_OFF + (x + 24) / 8 \/ SHADOW_OFF + (x + 24) / 8 + 1 <= sh) ->
  (x + 28 <= SHADOW_OFF + (x + 24) / 8 \/ SHADOW_OFF + (x + 24) / 8 + 1 <= x + 24) ->
  st_ok_pi SEGS VAL (p1_E regs [sh; m; lt_not m; g; SHADOW_OFF + (x + 24) / 8]) ss_p1
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85b0c)) mem (seg_rom SEGS))).
Proof.
intros W regs mem s1 sh m x iz g R9 R16 R20 R27 Hx Hiz Hm Hms1 Hg Hs1 Hs1' Hsh Hsh' Hpres H184 H192 H208 Hval
  Hshb D1 D2 D3.
assert (HSB : SHADOW_OFF = 0x7fff8000) by reflexivity.
pose proof (Z.div_pos (x + 24) 8 ltac:(lia) ltac:(lia)) as Hd0.
pose proof (Z.div_le_upper_bound (x + 24) 8 (2 ^ 44) ltac:(lia) ltac:(lia)) as Hd1.
set (shb := SHADOW_OFF + (x + 24) / 8) in *.
set (E := p1_E regs [sh; m; lt_not m; g; shb]).
assert (EE : forall k (r : bv 5) v, Z.of_nat k = bv_unsigned r -> getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  ew E k = Z_to_bv 64 v /\ bv_unsigned (ew E k) = v).
{ intros k r v Hk0 Hr Hv. assert (Ek : ew E k = getr regs r) by exact (p1_E_reg regs _ k r Hk0).
  rewrite Ek, Hr. split; [reflexivity|]. apply unsigned_lit_small. exact Hv. }
destruct (EE 9%nat 9%bv s1 eq_refl R9 ltac:(lia)) as [E9 U9].
destruct (EE 16%nat 16%bv SHADOW_OFF eq_refl R16 ltac:(lia)) as [E16 U16].
destruct (EE 20%nat 20%bv iz eq_refl R20 ltac:(lia)) as [E20 U20].
destruct (EE 27%nat 27%bv x eq_refl R27 ltac:(lia)) as [E27 U27].
assert (E32 : ew E 32 = Z_to_bv 64 sh)
  by exact (p1_E_extra regs [sh; m; lt_not m; g; shb] 0 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 m)
  by exact (p1_E_extra regs [sh; m; lt_not m; g; shb] 1 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E34 : ew E 34 = Z_to_bv 64 (lt_not m))
  by exact (p1_E_extra regs [sh; m; lt_not m; g; shb] 2 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E35 : ew E 35 = Z_to_bv 64 g)
  by exact (p1_E_extra regs [sh; m; lt_not m; g; shb] 3 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (E36 : ew E 36 = Z_to_bv 64 shb)
  by exact (p1_E_extra regs [sh; m; lt_not m; g; shb] 4 ltac:(cbn; lia) ltac:(unfold A_TEXT; lia)).
assert (U32 : bv_unsigned (ew E 32) = sh) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = lt_not m) by (rewrite E34; apply unsigned_lit_small; unfold lt_not; lia).
assert (U35 : bv_unsigned (ew E 35) = g) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = shb) by (rewrite E36; apply unsigned_lit_small; unfold shb; lia).
unfold ss_p1. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, p1_E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil;
    unfold YP09.region_ok, p1_s1, p1_sh, p1_ig, p1_igsh, fshadow_region;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    repeat apply Forall_cons; try apply Forall_nil.
    * exact (p1_chunk8 W mem E s1 184 32 sh E32 H184).
    * exact (p1_chunk8 W mem E s1 192 33 m E33 H192).
    * exact (p1_chunk8 W mem E s1 208 34 (lt_not m) E34 H208).
  + change (fs_frame_bytes 3 / 8) with 64. rewrite U32. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
  + rewrite U27. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. exact (p1_chunk4 W mem E x 24 35 g E35 ltac:(lia) Hval).
  + rewrite U36. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil]. exact (p1_chunk1z W mem E shb Hshb).
- apply pairwise_disjoint_of_extents. unfold p1_s1, p1_sh, p1_ig, p1_igsh, fshadow_region, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. change (fs_frame_bytes 3 / 8) with 64.
  rewrite U9, U32, U27, U36.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- split; [|split; [exact I|]].
  + cbn [p1_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U34, U35.
    rewrite !Z.pow_0_r, !Z.mod_1_r. unfold lt_not.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
  + cbn [p1_facts f_alias alias_ok p1_al_s3 p1_al_sh]. split; [|split; [|exact I]].
    * apply bv_eq. change (U E (SAlu ALU_ADD (SOff 33 0) (SAlu ALU_SLL (SOff 20 0) (SLit 8))) = U E (SOff 27 0)).
      rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
      rewrite (U_atom E 33 m E33), (U_atom E 20 iz E20), (U_atom E 27 x E27) by lia.
      rewrite U_lit by lia. change (Z.land 8 63) with 8. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 8) with 256.
      rewrite (zcanon_small (iz * 256)) by lia. rewrite zcanon_small by lia. lia.
    * rewrite (denot_shx E 27 16 24 x SHADOW_OFF E27 E16) by (unfold SHADOW_OFF; lia).
      cbn [sv_denot]. rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
Qed.

(* ---- facts carried by a reader that agrees on the bytes they read ---- *)
Lemma p1_word_kept : forall (rd rd' : reader) a v,
  (forall x, a <= x < a + 8 -> rd' x = rd x) -> rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v HK H. rewrite (rdword_ext rd rd' a); [exact H|]. intros k Hk. apply HK. lia. Qed.
Lemma p1_bytes_kept : forall (rd rd' : reader) a bs,
  (forall x, a <= x < a + Z.of_nat (length bs) -> rd' x = rd x) -> sa_bytes rd a bs -> sa_bytes rd' a bs.
Proof. intros rd rd' a bs HK H i Hi. rewrite HK by lia. exact (H i Hi). Qed.
Lemma p1_val_kept : forall (rd rd' : reader) a n v,
  (forall x, a <= x < a + Z.of_nat n -> rd' x = rd x) -> sa_val rd a n v -> sa_val rd' a n v.
Proof. intros rd rd' a n v HK H k Hk. rewrite HK by lia. exact (H k Hk). Qed.
(* the frame's shadow after `sb zero,4; sb zero,5; sb 4,6` through SH(FR) (0x85b10 .. 0x85b1c): v in scope, every
   other byte as before *)
Lemma p1_fsh : forall (rd rd' : reader) sh,
  sa_zs rd sh (lt_fsh LFO_N) ->
  (forall j, 0 <= j < 36 -> ~ (4 <= j < 7) -> rd' (sh + j) = rd (sh + j)) ->
  rd' (sh + 4) = Some 0 -> rd' (sh + 5) = Some 0 -> rd' (sh + 6) = Some 4 ->
  sa_zs rd' sh (lt_fsh LFO_NV).
Proof.
intros rd rd' sh H HK H4 H5 H6 j Hj. rewrite lt_fsh_len in Hj.
destruct (Nat.eq_dec j 4) as [->|N4]; [exact H4|].
destruct (Nat.eq_dec j 5) as [->|N5]; [exact H5|].
destruct (Nat.eq_dec j 6) as [->|N6]; [exact H6|].
rewrite HK; [| lia | intros [Ha Hb]; lia].
rewrite (H j ltac:(rewrite lt_fsh_len; exact Hj)).
f_equal. clear - Hj N4 N5 N6.
do 36 (destruct j as [|j]; [first [reflexivity | lia] |]). lia.
Qed.
(* a callee-saved register a call keeps (image B's S01 / S02 walk's lk_pres_reg) *)
Lemma p1_pres_reg : forall regs regs' (r : bv 5) z,
  aregs_preserved regs regs' -> acallee_saved z -> Z_to_bv 5 z = r -> getr regs' r = getr regs r.
Proof. intros regs regs' r z HP Hz <-. exact (HP z Hz). Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASTRRCHR : forall fx0 : YK11.FPState,
  @RtSeg.astrrchr_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_strrchr).
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let BR := paj_branch (PI := PI).

(* the entry sp and the realigned base S1 (addi sp,sp,-352 at 0x84dc0, andi sp,sp,-32 at 0x84e00) *)
Lemma p1_sp : forall cx, lt_base B MT cx ->
  x_sp0 cx mod 16 = 0 /\ alloc_ceiling + STK_LLVMFuzzerTestOneInput <= x_sp0 cx /\ x_sp0 cx <= 2 ^ 47 /\
  x_s1 cx mod 32 = 0 /\ x_sp0 cx - 368 <= x_s1 cx /\ x_s1 cx <= x_sp0 cx - 352.
Proof.
intros cx HB. destruct HB as (HPRE & _). destruct HPRE as (_ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hal & _ & Hceil & Hslo & Hshi & H47 & _).
unfold x_s1, x_sp0, LT_FRAME in *.
set (s := spZ (x_regs cx)) in *. clearbody s.
repeat split; lia.
Qed.

(* a live block of a state is a harness block of that state (image B's S01 / S02 walk's lk_hblk) *)
Lemma p1_hblk : forall ly S (W : world SEGS) mem md a n,
  AR SEGS B ly S W mem md -> In (a, n) (ablocks B ly S) -> lt_hblk B ly S (rdW W mem) a n.
Proof.
intros ly S W mem md a n HAR Hin.
destruct (al_blocks _ _ LAWS ly S W mem md a n HAR Hin) as (H16 & H4096 & Hceil & _ & _ & _ & Hn).
pose proof (req_size_pos n ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split; [exact Hin|]. split; [exact H4096|]. split; [exact H16|].
split; [lia|]. split; [lia|].
split; [exact (amem_range_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
split; [exact (range_addressable_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia))|].
intros Hn0. exact (shadow_hull_vis_of_block SEGS B LAWS ly S W mem md a n a n HAR Hin ltac:(lia) ltac:(lia) Hn0).
Qed.

(* the image facts across a write outside the image (image B's S21 / ret walk's s25_lit_kept / s25_img_kept) *)
Lemma p1_lit_kept : forall H (mem mem' : word -> option byte) a s,
  (forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x) ->
  sa_lit SEGS B (aview SEGS H mem) a s -> sa_lit SEGS B (aview SEGS H mem') a s.
Proof.
intros H mem mem' a s K (Ha & ((Hzs & Hn0) & _) & Hpin & Hrom & Himg).
split; [exact Ha|]. split; [|split; [exact Hpin | split; [exact Hrom | exact Himg]]].
split; [|exact (sa_tail_of_romtail SEGS H mem' _ Hrom)].
split; [|exact Hn0].
intros i Hi. rewrite K; [exact (Hzs i Hi)|].
rewrite length_app in Hi. cbn [length] in Hi.
refine (proj1 (Himg (a + Z.of_nat i) _)). lia.
Qed.
Lemma p1_img_kept : forall cx H (mem mem' : word -> option byte),
  (forall x, kImgLo <= x < kImgEnd -> aview SEGS H mem' x = aview SEGS H mem x) ->
  lt_img B cx (aview SEGS H mem) -> lt_img B cx (aview SEGS H mem').
Proof.
intros cx H mem mem' K0 HI.
assert (K : forall x, in_img SEGS x -> aview SEGS H mem' x = aview SEGS H mem x).
{ intros x Hx. apply K0. pose proof (pa_img_range x Hx) as Hr. unfold kImgLo. lia. }
unfold lt_img in *. destruct HI as (HRO & HIM & HGI).
destruct HIM as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & H14 & H15).
split; [|split].
- intros a Hro Ho He. rewrite K0; [exact (HRO a Hro Ho He)|].
  destruct Hro as [(s & Hs & _ & Hr) | Hr].
  + pose proof (pa_img_range a (ex_intro _ s (conj Hs Hr))) as Ha. unfold kImgLo. lia.
  + unfold RLO_A, RHI_A, SEG_RLO, SEG_RHI in Hr. unfold kImgLo, kImgEnd. lia.
- unfold seg_himg.
  split.
  { intros kk Hkk. rewrite K; [exact (H1 kk Hkk)|]. refine (proj1 (H2 _ _)). lia. }
  split; [exact H2|].
  split.
  { intros s Hs. destruct (H3 s Hs) as [L A]. exact (conj (p1_lit_kept H mem mem' _ s K L) A). }
  split.
  { intros s Hs. destruct (H4 s Hs) as [L A]. exact (conj (p1_lit_kept H mem mem' _ s K L) A). }
  split.
  { destruct H5 as (Hp & Hi & Hr). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hr i Hn) as (tp & Htp & Hl). exists tp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (pin_spec.row_addr catA i)); [exact Htp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)).
      unfold pin_spec.row_addr, pin_spec.CAT_ROW, pin_spec.CAT_BYTES. unfold pin_spec.CAT_N in Hn. lia.
    - exact (p1_lit_kept H mem mem' tp _ K Hl). }
  split; [exact H6|].
  split.
  { destruct H7 as (Hp & Hi & Hw). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn. destruct (Hw i Hn) as (wp & Hwp & Hl). exists wp. split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') (wordsA + 8 * Z.of_nat i)); [exact Hwp|].
      intros kk Hkk. apply K. refine (proj1 (Hi _ _)). lia.
    - exact (p1_lit_kept H mem mem' wp _ K Hl). }
  split.
  { destruct H8 as (Hp & Hi & Hv). split; [exact Hp|]. split; [exact Hi|].
    intros i Hn kk Hkk. rewrite K; [exact (Hv i Hn kk Hkk)|]. refine (proj1 (Hi _ _)). lia. }
  split.
  { destruct H9 as (Hg & g & Hgd). split.
    - rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') gotwA); [exact Hg|].
      intros kk Hkk. apply K0. unfold gotwA, kImgLo, kImgEnd. lia.
    - exists g. rewrite (rdword_ext (aview SEGS H mem) (aview SEGS H mem') guardA); [exact Hgd|].
      intros kk Hkk. apply K0. unfold guardA, kImgLo, kImgEnd. lia. }
  exact (conj H10 (conj H11 (conj H12 (conj H13 (conj H14 H15))))).
- unfold ltoi_GI in *. intros i Hi. rewrite K; [exact (HGI i Hi)|].
  refine (proj1 (H12 _ _)). unfold LONGL_W, LONGL_N. lia.
Qed.

(* ---- what the piece writes, and the facts of K85b0c it keeps ----
   The run writes v's three shadow bytes SH(FR) + 4 .. 6, the strrchr wrapper its scratch window [S1 - 8192, S1). *)
Definition p1_X (cx : lcx) (a : Z) : Prop :=
  (x_sh cx + 4 <= a < x_sh cx + 7) \/ (x_s1 cx - 2 * ESTACK <= a < x_s1 cx).

Lemma p1_keep : forall cx i c m tab mt ly S (W : world SEGS) regs mem md k acc regs' mem' md',
  lt_base B MT cx -> s22_inv B MT cx i c m tab mt LFO_N ly S W regs mem md k acc ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ p1_X cx a -> rdW W mem' a = rdW W mem a) ->
  rdW W mem' (x_sh cx + 4) = Some 0 -> rdW W mem' (x_sh cx + 5) = Some 0 -> rdW W mem' (x_sh cx + 6) = Some 4 ->
  s22_inv B MT cx i c m tab mt LFO_NV ly S W regs' mem' md' k acc.
Proof.
intros cx i c m tab mt ly S W regs mem md k acc regs' mem' md' HB HI HJ' P2 P3 P4 P8 P9 HK H4 H5 H6.
destruct HI as (Hi & Hdecl & HC & Hc & Hm & Htab & Hmt & HSL & HCM & HTABS).
pose proof (p1_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as (HF & HIMG & HBL & HBUD).
destruct HF as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _).
pose proof (proj1 HJ') as HAR'.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite HSTK in Hsp0.
assert (Hfin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EF : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds SEGS B LAWS ly S W mem md _ _ HAR Hfin) as (Hf0 & Hfc & Hfapp).
rewrite EF in Hf0, Hfc, Hfapp. change (fs_frame_bytes LT_FCLS) with 512 in Hfc, Hfapp.
assert (Hsh1 : SHADOW_OFF <= x_sh cx).
{ unfold x_sh, shadow_addr. pose proof (Z.div_pos (x_fr cx) 8 ltac:(lia) ltac:(lia)). lia. }
assert (Hsh2 : x_sh cx + 64 <= kHighMemBeg).
{ unfold x_sh, shadow_addr, SHADOW_OFF, kHighMemBeg.
  pose proof (Z.div_le_mono (x_fr cx) 140737479966720 8 ltac:(lia) ltac:(lia)) as Hd.
  change (140737479966720 / 8) with 17592184995840 in Hd. lia. }
unfold SHADOW_OFF, kHighMemBeg in Hsh1, Hsh2.
assert (KL : forall a, 0 <= a < kLowMemEnd -> rdW W mem' a = rdW W mem a).
{ intros a Ha. unfold kLowMemEnd in Ha. apply HK; [lia|]. unfold p1_X, ESTACK. intros [Hx|Hx]; lia. }
assert (KH : forall a, 17594333495296 <= a < alloc_ceiling -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK; [lia|]. unfold p1_X, ESTACK. intros [Hx|Hx]; lia. }
assert (KS : forall a, x_s1 cx <= a < 2 ^ 64 -> rdW W mem' a = rdW W mem a).
{ intros a Ha. apply HK; [lia|]. unfold p1_X, ESTACK. intros [Hx|Hx]; lia. }
assert (KA : forall lo n a, in_app lo n -> lo <= a < lo + n -> rdW W mem' a = rdW W mem a).
{ intros lo n a (H0 & [Hl | (Hh1 & Hh2)]) Ha; [apply KL | apply KH];
  unfold kLowShadowBeg, kLowMemEnd, kHighMemBeg, ASAN_CEIL in *; lia. }
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> rdW W mem' a = rdW W mem a).
{ intros p n a Hin Ha. destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & _ & _ & Happ & _ & _ & Hn).
  pose proof (req_size_pos n ltac:(lia)) as [_ Hrq]. exact (KA p (req_size n) a Happ ltac:(lia)). }
assert (KF : forall a, x_fr cx <= a < x_fr cx + 512 -> rdW W mem' a = rdW W mem a)
  by (intros a Ha; exact (KA _ _ a Hfapp Ha)).
assert (Hoff : forall o v, In (o, v) (LT_LV cx c m ++ LT_LD cx m tab mt i) -> 16 <= o <= 216).
{ intros o v Hin. unfold LT_LV, LT_LD in Hin. cbn [app In] in Hin.
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- _; lia |]). destruct Hin. }
split; [exact Hi|]. split; [exact Hdecl|].
split.
{ (* lt_core *)
  split; [|split; [|split; [exact HBL | exact HBUD]]].
  - split; [exact HJ'|].
    rewrite P2, P3, P4, P8, P9.
    split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R8|]. split; [exact R9|].
    split.
    { intros j r Hj. assert (Hj13 : (j < length LT_SAVED)%nat) by (apply nth_error_Some; congruence).
      change (length LT_SAVED) with 13%nat in Hj13.
      apply (p1_word_kept (rdW W mem)); [|exact (HSV j r Hj)]. intros a Ha. apply KS. lia. }
    split; [apply (p1_word_kept (rdW W mem)); [|exact HH0]; intros a Ha; apply KF; lia|].
    split; [apply (p1_word_kept (rdW W mem)); [|exact HH8]; intros a Ha; apply KF; lia|].
    split; [apply (p1_word_kept (rdW W mem)); [|exact HH16]; intros a Ha; apply KF; lia|].
    split; [apply (p1_word_kept (rdW W mem)); [|exact HFL]; intros a Ha; apply KF; unfold LT_FLAGW in *; lia|].
    split; [apply (p1_word_kept (rdW W mem)); [|exact H200]; intros a Ha; apply KS; lia|].
    split.
    { apply (p1_fsh (rdW W mem) (rdW W mem') (x_sh cx) HSH); [|exact H4 | exact H5 | exact H6].
      intros j Hj Hn. apply HK; [lia|]. unfold p1_X, ESTACK. intros [Hx|Hx]; lia. }
    apply (p1_word_kept (rdW W mem)); [|exact H184]; intros a Ha; apply KS; lia.
  - apply (p1_img_kept cx (w_H W) mem mem'); [|exact HIMG].
    intros a Ha. apply KL. unfold kImgLo, kImgEnd, kLowMemEnd in *. lia. }
split; [exact (p1_hblk ly S W mem' md' c _ HAR' (proj1 Hc))|].
split; [exact (p1_hblk ly S W mem' md' m _ HAR' (proj1 Hm))|].
split; [exact (p1_hblk ly S W mem' md' tab _ HAR' (proj1 Htab))|].
split; [exact (p1_hblk ly S W mem' md' mt _ HAR' (proj1 Hmt))|].
split.
{ intros o v Hin. pose proof (Hoff o v Hin) as Ho.
  apply (p1_word_kept (rdW W mem)); [|exact (HSL o v Hin)]. intros a Ha. apply KS. lia. }
split.
{ destruct HCM as ((bs1 & Hb1 & He1) & (bs2 & Hb2 & He2)).
  pose proof (proj1 He1) as L1. pose proof (proj1 He2) as L2.
  split; [exists bs1 | exists bs2]; (split; [|assumption]).
  - apply (p1_bytes_kept (rdW W mem)); [|exact Hb1]. intros a Ha.
    apply (KB c seg_spec.SEG_C_SIZE a (proj1 Hc)). unfold seg_spec.SEG_C_SIZE in *. lia.
  - apply (p1_bytes_kept (rdW W mem)); [|exact Hb2]. intros a Ha.
    apply (KB m seg_spec.SEG_M_SIZE a (proj1 Hm)). unfold seg_spec.SEG_M_SIZE in *. lia. }
{ destruct HTABS as (Hcap & (bs & Hb & He) & Hg & Hv & (bs' & Hb' & He') & Hlt).
  pose proof (proj1 He) as Lt. pose proof (proj1 He') as Lm.
  assert (Etn : x_tabn cx = 18 * (x_cap cx + 1)) by reflexivity.
  assert (Emn : x_mtn cx = 20 * (x_cap cx + 1)) by reflexivity.
  split; [exact Hcap|].
  split.
  { exists bs. split; [|exact He]. apply (p1_bytes_kept (rdW W mem)); [|exact Hb]. intros a Ha.
    rewrite Lt in Ha. apply (KB tab (x_tabn cx) a (proj1 Htab)). lia. }
  split.
  { unfold sa_guardtab in *. apply (p1_bytes_kept (rdW W mem)); [|exact Hg]. intros a Ha.
    unfold seg_spec.GUARD_BYTES, seg_spec.RVLAN_SIZE in *. rewrite repeat_length in Ha.
    apply (KB tab (x_tabn cx) a (proj1 Htab)). lia. }
  split.
  { apply (p1_val_kept (rdW W mem)); [|exact Hv]. intros a Ha. apply KF. unfold FO_N in *. lia. }
  split; [|exact Hlt].
  exists bs'. split; [|exact He']. apply (p1_bytes_kept (rdW W mem)); [|exact Hb']. intros a Ha.
  rewrite Lm in Ha. apply (KB mt (x_mtn cx) a (proj1 Hmt)). lia. }
Qed.

Lemma s22_p1 : s22_p1_stmt B MT.
Proof.
unfold s22_p1_stmt, LT_K85b0c_stmt.
intros i HJOIN HVR cx ly S W regs mem md k acc c m tab mt HB0 HFRM Hi HCORE HcB Hm Htab Hmt
  R16 R20 R22 R26 R27 Hdecl HSL HCM HTABS.
assert (HINV : s22_inv B MT cx i c m tab mt LFO_N ly S W regs mem md k acc)
  by exact (conj Hi (conj Hdecl (conj HCORE (conj HcB (conj Hm (conj Htab (conj Hmt (conj HSL (conj HCM HTABS))))))))).
pose proof (p1_sp cx HB0) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof HB0 as (HAFN & _).
pose proof HAFN as (_ & _ & _ & Hgp0 & Htp0 & _).
pose proof HCORE as (HFR & HIMG & HBL & HBUD).
pose proof HFR as (HJ & R2 & R3 & R4 & R8 & R9 & HSV & HH0 & HH8 & HH16 & HFL & H200 & HSH & H184).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & Hly & _ & _ & _ & Hfrs & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. rewrite HSTK in Hsp0.
assert (Ho16 : (x_s1 cx - x_sp0 cx) mod 16 = 0) by lia.
(* the frame and its shadow *)
assert (Hfin : In (LT_FCLS, x_fpos cx) (frames S)) by (rewrite Hfrs; left; reflexivity).
assert (EFA : frame_addr ly LT_FCLS (x_fpos cx) = x_fr cx).
{ unfold x_fr, frame_addr. pose proof Hly as (_ & _ & _ & _ & _ & EF & _). rewrite EF. reflexivity. }
destruct (frames_bounds SEGS B LAWS ly S W mem md _ _ HAR Hfin) as (HF4096 & HFceil & HFapp).
destruct (al_frames _ _ LAWS ly S W mem md _ _ HAR Hfin) as (HF32 & _ & _ & HFSpres).
rewrite EFA in HF4096, HFceil, HFapp, HF32, HFSpres.
change (fs_frame_bytes LT_FCLS) with 512 in HFceil, HFapp, HFSpres. change (512 / 8) with 64 in HFSpres.
assert (Hsh1 : SHADOW_OFF + 512 <= x_sh cx).
{ unfold x_sh, shadow_addr. pose proof (Z.div_le_mono 4096 (x_fr cx) 8 ltac:(lia) ltac:(lia)) as Hd.
  change (4096 / 8) with 512 in Hd. lia. }
assert (Hsh2 : x_sh cx + 64 <= kHighMemBeg).
{ unfold x_sh, shadow_addr, SHADOW_OFF, kHighMemBeg.
  pose proof (Z.div_le_mono (x_fr cx) 140737479966720 8 ltac:(lia) ltac:(lia)) as Hd.
  change (140737479966720 / 8) with 17592184995840 in Hd. lia. }
(* the block m and turn i's segment in it *)
pose proof Hm as (HinM & HM4096 & HM16 & HaM).
pose proof HaM as (_ & HM63 & _).
destruct (al_blocks _ _ LAWS ly S W mem md m seg_spec.SEG_M_SIZE HAR HinM) as (_ & _ & HMceil & HMapp & _ & _ & _).
pose proof (sep_block_frame SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE LT_FCLS (x_fpos cx) HAR HinM Hfin)
  as HMF.
rewrite EFA in HMF. unfold zdisjoint in HMF. cbn [fst snd] in HMF.
change (req_size seg_spec.SEG_M_SIZE) with 9236 in HMceil, HMapp, HMF.
change (fs_frame_bytes LT_FCLS) with 512 in HMF.
unfold seg_spec.SEG_M_SIZE in HM63.
assert (Hi32 : (i < 32)%nat).
{ pose proof HCM as (_ & (bs & _ & Henc)). destruct Henc as (_ & Hle & _). unfold x_mcF in Hi. lia. }
destruct (s22_mseg_at cx i c m (rdW W mem) HCM Hi) as (f & Hf & Henc).
destruct (s22_name_str cx i c m (rdW W mem) HCM Hi) as (Hstrz0 & Hlen16 & Hnf).
set (x := seg_spec.mseg_addr m i) in *.
assert (Hx : x = m + 256 * Z.of_nat i) by (unfold x, seg_spec.mseg_addr, seg_spec.MSEG_SIZE; lia).
set (name := SegModel.ms_name (x_seg cx i)) in *.
remember (if SegModel.ms_ignore (x_seg cx i) then 1 else 0) as g eqn:Hgdef.
assert (Hg : 0 <= g <= 1) by (rewrite Hgdef; destruct (SegModel.ms_ignore (x_seg cx i)); lia).
(* the ignore word m->seg[i].ignore at x + 24: the flag, 1 or 0 *)
assert (Hig : sa_val (rdW W mem) (x + 24) 4 g).
{ pose proof Henc as (Hflen & _ & _ & _ & Hfig & _).
  intros kk Hkk.
  assert (Hidx : (24 + kk < length f)%nat) by lia.
  pose proof (Hf (24 + kk)%nat Hidx) as Hb.
  replace (x + 24 + Z.of_nat kk) with (x + Z.of_nat (24 + kk)) by lia.
  rewrite Hb. f_equal.
  unfold seg_spec.flag_enc, seg_spec.fldz, seg_spec.fld in Hfig.
  change (Z.to_nat seg_spec.MS_IGNORE) with 24%nat in Hfig. change (Z.to_nat 4) with 4%nat in Hfig.
  assert (Hn : nth (24 + kk) f ZB0 = nth kk (firstn 4 (skipn 24 f)) ZB0).
  { rewrite nth_firstn. destruct (Nat.ltb_spec kk 4); [|lia]. rewrite nth_skipn. reflexivity. }
  rewrite Hn, Hfig, Hgdef. clear - Hkk.
  destruct (SegModel.ms_ignore (x_seg cx i)); do 4 (destruct kk as [|kk]; [vm_compute; reflexivity|]); lia. }
(* its shadow byte is 0: the whole granule [x + 24, x + 32) lies in the block m *)
assert (Hshb : rdW W mem (SHADOW_OFF + (x + 24) / 8) = Some 0).
{ pose proof (range_addressable_of_block SEGS B LAWS ly S W mem md m seg_spec.SEG_M_SIZE (x + 24) 8 HAR HinM
    ltac:(lia) ltac:(change (req_size seg_spec.SEG_M_SIZE) with 9236; lia)) as HRA.
  destruct (HRA (x + 24) ltac:(lia)) as (s0 & Hs0 & Hok0).
  destruct (HRA (x + 31) ltac:(lia)) as (s7 & Hs7 & Hok7).
  unfold shadow_of_addr in Hs0, Hs7.
  assert (Hq : (x + 31) / 8 = (x + 24) / 8) by lia.
  rewrite Hq, Hs0 in Hs7. injection Hs7 as <-.
  rewrite Hs0. unfold saddr_ok in Hok7. destruct Hok7 as [-> | Hok7]; [reflexivity | lia]. }
(* where the regions of the seed lie *)
assert (D1 : x_sh cx + 64 <= x + 24 \/ x + 28 <= x_sh cx).
{ destruct HMapp as (_ & [Hl | (Hh & _)]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; [right | left]; lia. }
assert (D2 : x_sh cx + 64 <= SHADOW_OFF + (x + 24) / 8 \/ SHADOW_OFF + (x + 24) / 8 + 1 <= x_sh cx).
{ unfold x_sh, shadow_addr. destruct HMF as [HMF | HMF]; [right | left]; lia. }
assert (D3 : x + 28 <= SHADOW_OFF + (x + 24) / 8 \/ SHADOW_OFF + (x + 24) / 8 + 1 <= x + 24).
{ destruct HMapp as (_ & [Hl | (Hh & _)]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; [left | right]; lia. }
pose proof (HSL 192 m ltac:(apply in_or_app; left; unfold LT_LV; cbn [In]; repeat (first [left; reflexivity | right])))
  as H192.
pose proof (HSL 208 (lt_not m) ltac:(apply in_or_app; left; unfold LT_LV; cbn [In];
  repeat (first [left; reflexivity | right]))) as H208.
pose proof (p1_seed W regs mem (x_s1 cx) (x_sh cx) m x (Z.of_nat i) g R9 R16 R20 R27 Hx ltac:(lia) ltac:(lia)
  ltac:(lia) Hg ltac:(lia) ltac:(lia) ltac:(unfold SHADOW_OFF in *; lia) ltac:(unfold kHighMemBeg in *; lia)
  (fun o Ho => proj1 (HFSpres o ltac:(lia))) H184 H192 H208 Hig Hshb D1 D2 D3) as HS.
set (E := p1_E regs [x_sh cx; m; lt_not m; g; SHADOW_OFF + (x + 24) / 8]) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, p1_E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; exact (p1_E_reg regs _ n r Hn)).
assert (E32 : ew E 32 = Z_to_bv 64 (x_sh cx))
  by exact (p1_E_extra regs [x_sh cx; m; lt_not m; g; SHADOW_OFF + (x + 24) / 8] 0 ltac:(cbn; lia)
    ltac:(unfold A_TEXT; lia)).
assert (E33 : ew E 33 = Z_to_bv 64 m)
  by exact (p1_E_extra regs [x_sh cx; m; lt_not m; g; SHADOW_OFF + (x + 24) / 8] 1 ltac:(cbn; lia)
    ltac:(unfold A_TEXT; lia)).
assert (E35 : ew E 35 = Z_to_bv 64 g)
  by exact (p1_E_extra regs [x_sh cx; m; lt_not m; g; SHADOW_OFF + (x + 24) / 8] 3 ltac:(cbn; lia)
    ltac:(unfold A_TEXT; lia)).
assert (U32 : bv_unsigned (ew E 32) = x_sh cx)
  by (rewrite E32; apply unsigned_lit_small; clear - Hsh1 Hsh2; unfold kHighMemBeg, SHADOW_OFF in *; lia).
(* the write permission of v's three shadow bytes: the frame's shadow, by awr_byte's in_frames disjunct *)
assert (HSHF : forall a, x_sh cx + 4 <= a < x_sh cx + 7 ->
  awr_byte SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (ablocks B (x_ly cx) (x_S cx))
    (ablocks B ly S) (frames (x_S cx)) ly [(LT_FCLS, x_fpos cx)] a).
{ intros a Ha. right; right; right; left. exists LT_FCLS, (x_fpos cx). split; [left; reflexivity|]. right.
  unfold in_zr. cbn [fst snd]. rewrite EFA. change (fs_frame_bytes LT_FCLS / 8) with 64. unfold x_sh in Ha. lia. }
unfold cfg_at. change (w64 (BASE + LO_K85b0c)) with (Z_to_bv 64 (BASE + LO_K85b0c)).
(* 0x85b0c .. 0x85b54: SH(FR) + 4 .. 6 := 00 00 04, the traps i = 32 and M + 256 i wraps (decided by the facts),
   s8 := m, s3 := &m->seg[i], its ignore word's check (the shadow byte 0 of the seed), lw a0 = g; then beqz a0 *)
paj_run_sh RUNP HS HJ.
{ p1_awr HSHF U32. }
cbn [ms_mem mkst] in HF, HFr, HG, HJ.
rename HFr into HFr1. clear HF HG.
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv1 := mdx) in *; clearbody mdv1 end.
rename ms into ms1.
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) -> rdW W (ms_mem ms1) a = rdW W mem a).
{ intros a Ha Hn. p1_nowin HFr1 U32. }
(* the string facts the call reads, at every memory that keeps the block m's bytes *)
assert (HXM : x + 32 <= x_sh cx + 4 \/ x_sh cx + 7 <= x).
{ destruct HMapp as (_ & [Hl | (Hh & _)]); unfold kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *; [left | right]; lia. }
psrr_branch_pi RUNP BR HS.
- (* a0 = 0: m->seg[i].ignore is not set: 0x85b54 taken, a1 := 46, a0 := s3, the jal of strrchr (0x85ba0) *)
  assert (Hign : SegModel.ms_ignore (x_seg cx i) = false).
  { rewrite branch_eq_U in Hc. rewrite (U_atom E 35 g E35) in Hc by lia. rewrite U_lit in Hc by lia.
    apply Z.eqb_eq in Hc. rewrite Hgdef in Hc.
    destruct (SegModel.ms_ignore (x_seg cx i)); [discriminate Hc | reflexivity]. }
  clear Hc.
  paj_run_shc RUNP RUNC HS HJ.
  { p1_awr HSHF U32. }
  rename HFr into HFr2. clear HF HG.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
  rename ms into ms2.
  assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) ->
    rdW W (ms_mem ms2) a = rdW W mem a).
  { intros a Ha Hn. rewrite <- (K1 a Ha Hn). p1_nowin HFr2 U32. }
  (* v's three shadow bytes, from the frame's shadow region of the symbolic state *)
  lazymatch type of HS with st_ok _ _ ?ssx _ =>
    let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_region_nth E ssx _ 1%nat r0 HS ltac:(vm_compute; reflexivity)) as HR1 end.
  cbn [ms_mem restrict] in HR1.
  pose proof (p1_rd1 E (w_H W) (ms_mem ms2) 32 (x_sh cx) _ _ _ _ _ 4 0 HR1 U32
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as S4.
  pose proof (p1_rd1 E (w_H W) (ms_mem ms2) 32 (x_sh cx) _ _ _ _ _ 5 0 HR1 U32
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as S5.
  pose proof (p1_rd1 E (w_H W) (ms_mem ms2) 32 (x_sh cx) _ _ _ _ _ 6 4 HR1 U32
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as S6.
  clear HR1.
  (* the registers at the call *)
  pmkst HS.
  assert (C1r : getr (ms_regs ms2) 1 = Z_to_bv 64 (BASE + 3556)) by (prreg HS (1%bv : bv 5) R; exact R).
  assert (C2r : getr (ms_regs ms2) 2 = getr regs 2) by (prreg HS (2%bv : bv 5) R; rewrite R; exact (EE 2%nat 2%bv eq_refl)).
  assert (C3r : getr (ms_regs ms2) 3 = getr regs 3) by (prreg HS (3%bv : bv 5) R; rewrite R; exact (EE 3%nat 3%bv eq_refl)).
  assert (C4r : getr (ms_regs ms2) 4 = getr regs 4) by (prreg HS (4%bv : bv 5) R; rewrite R; exact (EE 4%nat 4%bv eq_refl)).
  assert (C8r : getr (ms_regs ms2) 8 = getr regs 8) by (prreg HS (8%bv : bv 5) R; rewrite R; exact (EE 8%nat 8%bv eq_refl)).
  assert (C9r : getr (ms_regs ms2) 9 = getr regs 9) by (prreg HS (9%bv : bv 5) R; rewrite R; exact (EE 9%nat 9%bv eq_refl)).
  assert (C20r : getr (ms_regs ms2) 20 = getr regs 20)
    by (prreg HS (20%bv : bv 5) R; rewrite R; exact (EE 20%nat 20%bv eq_refl)).
  assert (C22r : getr (ms_regs ms2) 22 = getr regs 22)
    by (prreg HS (22%bv : bv 5) R; rewrite R; exact (EE 22%nat 22%bv eq_refl)).
  assert (C26r : getr (ms_regs ms2) 26 = getr regs 26)
    by (prreg HS (26%bv : bv 5) R; rewrite R; exact (EE 26%nat 26%bv eq_refl)).
  assert (C27r : getr (ms_regs ms2) 27 = getr regs 27)
    by (prreg HS (27%bv : bv 5) R; rewrite R; exact (EE 27%nat 27%bv eq_refl)).
  assert (C10r : getr (ms_regs ms2) 10 = w64 x)
    by (prreg HS (10%bv : bv 5) R; rewrite R, (EE 27%nat 27%bv eq_refl); exact R27).
  assert (C11r : getr (ms_regs ms2) 11 = w64 46) by (prreg HS (11%bv : bv 5) R; rewrite R; reflexivity).
  assert (C19r : getr (ms_regs ms2) 19 = w64 x)
    by (prreg HS (19%bv : bv 5) R; rewrite R, (EE 27%nat 27%bv eq_refl); exact R27).
  assert (C24r : getr (ms_regs ms2) 24 = w64 m) by (prreg HS (24%bv : bv 5) R; rewrite R, E33; reflexivity).
  assert (Csp : spZ (ms_regs ms2) = x_sp0 cx + (x_s1 cx - x_sp0 cx)).
  { unfold spZ. rewrite C2r, R2. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  (* the name at the call: a C string of at most 15 bytes in the block m *)
  assert (KX : forall a, x <= a < x + 32 -> rdW W (ms_mem ms2) a = rdW W mem a).
  { intros a Ha. apply K12; lia. }
  assert (Hstrz : sa_strz (rdW W (ms_mem ms2)) x name).
  { destruct Hstrz0 as [Hz Hn0]. split; [|exact Hn0]. intros j Hj. rewrite KX; [exact (Hz j Hj)|].
    rewrite length_app in Hj. cbn [length] in Hj. lia. }
  destruct (sa_strz_bytes SEGS (w_H W) (ms_mem ms2) x name Hstrz) as (HBy & HN0 & HZS).
  assert (HZS' : map (fun b : byte => bv_unsigned b) (seg_spec.zb name) = name) by exact HZS.
  assert (HL : astr_len (seg_spec.zb name) = Z.of_nat (length name))
    by (unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity).
  pose proof (proj1 HJ) as HAR2.
  destruct (al_blocks _ _ LAWS ly S W (ms_mem ms2) mdv2 m seg_spec.SEG_M_SIZE HAR2 HinM)
    as (_ & _ & _ & _ & HMpres2 & _ & _).
  change (req_size seg_spec.SEG_M_SIZE) with 9236 in HMpres2.
  pose proof (p1_img_kept cx (w_H W) mem (ms_mem ms2)
    (fun a Ha => K12 a ltac:(unfold kImgLo, kImgEnd in Ha; lia)
       ltac:(unfold kImgLo, kImgEnd, SHADOW_OFF in *; lia)) HIMG) as HIMG2.
  eapply SRr_bind.
  { apply (aj_art_at (fx := fx) SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
      (pa_sigma SS___interceptor_trampoline_strrchr) W (ms_regs ms2) (ms_mem ms2) STK_LLVMFuzzerTestOneInput
      (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S mdv2 k
      (x_s1 cx - x_sp0 cx) (Z_to_bv 64 (BASE + 3556))
      (fun regs' _ => (getr regs' 10 = w64 0 /\ ~ In 46 (map (fun b : byte => bv_unsigned b) (seg_spec.zb name))) \/
         (exists j, RtSeg.last_at (map (fun b : byte => bv_unsigned b) (seg_spec.zb name)) 46 j /\
                    getr regs' 10 = w64 (x + Z.of_nat j)))
      HJ Csp Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite HSTK; unfold ESTACK; lia) C1r
      (fun a F => False_ind _ F)).
    apply (ASTRRCHR fx ly S W (ms_regs ms2) (ms_mem ms2) mdv2 x 46 (seg_spec.zb name)).
    - apply (ecall_pre_stk_at SEGS B (2 * ESTACK) STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx)
        (x_S cx) (x_W cx) (x_mem cx) (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W (ms_mem ms2) mdv2 k (ms_regs ms2)
        (x_s1 cx - x_sp0 cx) HJ Csp Ho16 ltac:(lia) ltac:(unfold ESTACK; lia) ltac:(rewrite HSTK; unfold ESTACK; lia)).
      + rewrite C1r. apply ret_ok_codeptr_v; [lia | reflexivity].
      + rewrite C3r, R3. exact Hgp0.
      + rewrite C4r, R4. exact Htp0.
    - exact C10r.
    - exact C11r.
    - lia.
    - lia.
    - apply (astr_atR_view SEGS). split; [exact HBy | exact HN0].
    - rewrite HL. apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) ly S W (ms_regs ms2) (ms_mem ms2) mdv2 m
        seg_spec.SEG_M_SIZE); [exact HAR2 | exact HinM | lia | unfold seg_spec.SEG_M_SIZE; lia | lia |].
      rewrite Csp. unfold ESTACK. lia.
    - rewrite HL. apply (amem_range_of_block SEGS B LAWS ly S W (ms_mem ms2) mdv2 m seg_spec.SEG_M_SIZE);
        [exact HAR2 | exact HinM | lia | change (req_size seg_spec.SEG_M_SIZE) with 9236; lia].
    - rewrite HL. intros a Ha. apply (aview_some_of_apresent SEGS). apply (proj1 (HMpres2 a ltac:(lia))).
    - destruct HIMG2 as (HRO2 & _ & _). intros a Hrom Ho He. apply HRO2; [left; exact Hrom | exact Ho | exact He]. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
  rewrite HZS' in HQ2.
  (* the registers and the memory after the call *)
  assert (P2 : getr regs2 2 = getr regs 2)
    by (rewrite (p1_pres_reg _ _ 2%bv 2 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C2r).
  assert (P3 : getr regs2 3 = getr regs 3)
    by (rewrite (p1_pres_reg _ _ 3%bv 3 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C3r).
  assert (P4 : getr regs2 4 = getr regs 4)
    by (rewrite (p1_pres_reg _ _ 4%bv 4 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C4r).
  assert (P8 : getr regs2 8 = getr regs 8)
    by (rewrite (p1_pres_reg _ _ 8%bv 8 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C8r).
  assert (P9 : getr regs2 9 = getr regs 9)
    by (rewrite (p1_pres_reg _ _ 9%bv 9 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C9r).
  assert (P19 : getr regs2 19 = w64 x)
    by (rewrite (p1_pres_reg _ _ 19%bv 19 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C19r).
  assert (P20 : getr regs2 20 = getr regs 20)
    by (rewrite (p1_pres_reg _ _ 20%bv 20 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C20r).
  assert (P22 : getr regs2 22 = getr regs 22)
    by (rewrite (p1_pres_reg _ _ 22%bv 22 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C22r).
  assert (P24 : getr regs2 24 = w64 m)
    by (rewrite (p1_pres_reg _ _ 24%bv 24 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C24r).
  assert (P26 : getr regs2 26 = getr regs 26)
    by (rewrite (p1_pres_reg _ _ 26%bv 26 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C26r).
  assert (P27 : getr regs2 27 = getr regs 27)
    by (rewrite (p1_pres_reg _ _ 27%bv 27 HP2 ltac:(unfold acallee_saved; lia) ltac:(apply bv_eq; reflexivity)); exact C27r).
  assert (HINV2 : s22_inv B MT cx i c m tab mt LFO_NV ly S W regs2 mem2 md2 k acc).
  { apply (p1_keep cx i c m tab mt ly S W regs mem md k acc regs2 mem2 md2 HB0 HINV HJ2 P2 P3 P4 P8 P9).
    - intros a Ha Hn. unfold p1_X in Hn.
      rewrite (HK2 a Ha); [| intros Hw; apply Hn; right; lia | intros F; exact F].
      apply K12; [exact Ha|]. intros Hw; apply Hn; left; exact Hw.
    - rewrite (HK2 (x_sh cx + 4) ltac:(unfold kHighMemBeg, SHADOW_OFF in *; lia)
        ltac:(unfold ESTACK, kHighMemBeg, SHADOW_OFF in *; lia) ltac:(intros F; exact F)). exact S4.
    - rewrite (HK2 (x_sh cx + 5) ltac:(unfold kHighMemBeg, SHADOW_OFF in *; lia)
        ltac:(unfold ESTACK, kHighMemBeg, SHADOW_OFF in *; lia) ltac:(intros F; exact F)). exact S5.
    - rewrite (HK2 (x_sh cx + 6) ltac:(unfold kHighMemBeg, SHADOW_OFF in *; lia)
        ltac:(unfold ESTACK, kHighMemBeg, SHADOW_OFF in *; lia) ltac:(intros F; exact F)). exact S6. }
  assert (RK2 : s22_rk m i regs2).
  { split; [rewrite P20; exact R20|]. split; [rewrite P22; exact R22|].
    split; [rewrite P26; exact R26 | rewrite P27; exact R27]. }
  unfold S22_VR_stmt in HVR.
  destruct HQ2 as [(R10' & Hnin) | (j & Hlast & R10')].
  + refine (HVR cx ly S W regs2 mem2 md2 k acc c m tab mt 0 HB0 HFRM HINV2 Hign _ R10' P19 P24 RK2).
    left. split; [reflexivity | exact (s22_strrchr_none name 46 Hnf Hnin)].
  + refine (HVR cx ly S W regs2 mem2 md2 k acc c m tab mt (x + Z.of_nat j) HB0 HFRM HINV2 Hign _ R10' P19 P24 RK2).
    right. exists j. split; [exact (s22_strrchr_some name 46 j Hnf Hlast) | reflexivity].
- (* a0 <> 0: m->seg[i].ignore is set: 0x85b54 not taken, to the join 0x85b58 *)
  assert (Hign : SegModel.ms_ignore (x_seg cx i) = true).
  { rewrite branch_eq_U in Hc. rewrite (U_atom E 35 g E35) in Hc by lia. rewrite U_lit in Hc by lia.
    apply Z.eqb_neq in Hc. rewrite Hgdef in Hc.
    destruct (SegModel.ms_ignore (x_seg cx i)); [reflexivity | exfalso; apply Hc; reflexivity]. }
  clear Hc.
  paj_run_to_sh RUNTOP HS HJ S22_JOIN.
  { p1_awr HSHF U32. }
  cbn [ms_mem mkst] in HF, HFr, HG, HJ.
  rename HFr into HFr2. clear HF HG.
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?mdx |} _ => set (mdv2 := mdx) in *; clearbody mdv2 end.
  rename ms into ms2.
  assert (K12 : forall a, 0 <= a < 2 ^ 64 -> ~ (x_sh cx + 4 <= a < x_sh cx + 7) ->
    rdW W (ms_mem ms2) a = rdW W mem a).
  { intros a Ha Hn. rewrite <- (K1 a Ha Hn). p1_nowin HFr2 U32. }
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let r0 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
    pose proof (st_ok_pi_region_nth E ssx _ 1%nat r0 HS ltac:(vm_compute; reflexivity)) as HR1 end.
  cbn [ms_mem restrict] in HR1.
  pose proof (p1_rd1 E (w_H W) (ms_mem ms2) 32 (x_sh cx) _ _ _ _ _ 4 0 HR1 U32
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as S4.
  pose proof (p1_rd1 E (w_H W) (ms_mem ms2) 32 (x_sh cx) _ _ _ _ _ 5 0 HR1 U32
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as S5.
  pose proof (p1_rd1 E (w_H W) (ms_mem ms2) 32 (x_sh cx) _ _ _ _ _ 6 4 HR1 U32
    ltac:(cbn [In]; repeat (first [left; reflexivity | right])) ltac:(lia)) as S6.
  clear HR1.
  pmkst HS.
  assert (C2r : getr (ms_regs ms2) 2 = getr regs 2) by (prreg HS (2%bv : bv 5) R; rewrite R; exact (EE 2%nat 2%bv eq_refl)).
  assert (C3r : getr (ms_regs ms2) 3 = getr regs 3) by (prreg HS (3%bv : bv 5) R; rewrite R; exact (EE 3%nat 3%bv eq_refl)).
  assert (C4r : getr (ms_regs ms2) 4 = getr regs 4) by (prreg HS (4%bv : bv 5) R; rewrite R; exact (EE 4%nat 4%bv eq_refl)).
  assert (C8r : getr (ms_regs ms2) 8 = getr regs 8) by (prreg HS (8%bv : bv 5) R; rewrite R; exact (EE 8%nat 8%bv eq_refl)).
  assert (C9r : getr (ms_regs ms2) 9 = getr regs 9) by (prreg HS (9%bv : bv 5) R; rewrite R; exact (EE 9%nat 9%bv eq_refl)).
  assert (C16r : getr (ms_regs ms2) 16 = getr regs 16)
    by (prreg HS (16%bv : bv 5) R; rewrite R; exact (EE 16%nat 16%bv eq_refl)).
  assert (C20r : getr (ms_regs ms2) 20 = getr regs 20)
    by (prreg HS (20%bv : bv 5) R; rewrite R; exact (EE 20%nat 20%bv eq_refl)).
  assert (C22r : getr (ms_regs ms2) 22 = getr regs 22)
    by (prreg HS (22%bv : bv 5) R; rewrite R; exact (EE 22%nat 22%bv eq_refl)).
  assert (C26r : getr (ms_regs ms2) 26 = getr regs 26)
    by (prreg HS (26%bv : bv 5) R; rewrite R; exact (EE 26%nat 26%bv eq_refl)).
  assert (C27r : getr (ms_regs ms2) 27 = getr regs 27)
    by (prreg HS (27%bv : bv 5) R; rewrite R; exact (EE 27%nat 27%bv eq_refl)).
  assert (C24r : getr (ms_regs ms2) 24 = w64 m) by (prreg HS (24%bv : bv 5) R; rewrite R, E33; reflexivity).
  unfold S22_JOIN_stmt in HJOIN.
  refine (HJOIN cx ly S W (ms_regs ms2) (ms_mem ms2) mdv2 k acc c m tab mt HB0 HFRM _ _ _ C24r _).
  + unfold x_decl. apply s22_decl_step_skip; [exact Hi | exact (proj1 Hdecl) | left; exact Hign].
  + apply (p1_keep cx i c m tab mt ly S W regs mem md k acc (ms_regs ms2) (ms_mem ms2) mdv2 HB0 HINV HJ
      C2r C3r C4r C8r C9r); [| exact S4 | exact S5 | exact S6].
    intros a Ha Hn. apply K12; [exact Ha|]. intros Hw. apply Hn. left. exact Hw.
  + rewrite C16r. exact R16.
  + split; [rewrite C20r; exact R20|]. split; [rewrite C22r; exact R22|].
    split; [rewrite C26r; exact R26 | rewrite C27r; exact R27].
Qed.

End e.
End f.
End d.
