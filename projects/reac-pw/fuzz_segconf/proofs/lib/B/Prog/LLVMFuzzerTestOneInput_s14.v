(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the head of the top loop of LLVMFuzzerTestOneInput's ASan+UBSan walk (plugin-hostd/fuzz_command image B, 0x86654 .. 0x866bc with r > 0: UBSan's p + 1 tests, the header bytes, the cases r = 1, r = 2 and r >= 3 with the out-of-line high byte 0x86888 .. 0x868b0, 0x86a64 .. 0x86a78, the 8192 clamp), from LT_LH_stmt's state to the mid point LH_M1_stmt, the B twin of lib/A/Prog/LLVMFuzzerTestOneInput_s23.v, in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACh6.v (a segment lemma from one point of the function to the next, its seed lemma cl_seedX) and A/ACbk.v (the walk through the branches). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/LLVMFuzzerTestOneInput_s23.v, with its module paths, module names and numbers changed; 1206 of its 1286 lines of code are new or changed and 389 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, ASan+UBSan image B (fuzz_segconf.asan-ubsan, pin sha256 c3796c0b38f3): the walk of the
   test harness's entry function LLVMFuzzerTestOneInput (0x84dc0), segment S04 of PLAN-asanubsan-main section 2.3:
   lt_seg_S04 : lt_seg_S04_stmt (LLVMFuzzerTestOneInput_defs.v), K85110 f -> K85210 f, 0x85110 .. 0x8520c
   (dis/LLVMFuzzerTestOneInput.fuzz_segconf.asan-ubsan.s lines 214-277, listing SegList.v slots 212-275).

   What the code does: with s8 the cursor and s4 the bytes left (K85110 f: seg_cur_at / seg_cur_n), fuzz_u8 reads
   the label byte into s10 (0 when s4 = 0), fuzz_u16 the length lo | hi << 8 (the cases s4 = 0, 1, 2 and >= 3;
   s3 and s4 move past the bytes read), the instrumented checks 4-6 of the three loads (0x85120, 0x85160, 0x85194;
   their slow blocks 0x85564, 0x855ac, 0x855b8) and UBSan's three pointer tests `bgeu 1, p + k` (0x8511c, 0x8515c,
   0x85190, to the trap 0x85ff8); s7 = min(len, s4) (`bltu` 0x851b8), s8 = s3 + s7 with UBSan's two take tests
   (0x851c4 no wrap, 0x851d4 the null-ness xor); 160(s1) := s4; for s7 <> 0 memchr(s3, 0, s7) (0x851ec), else
   a0 = 0; 152(s1) := s7; s4 := (a0 ? a0 - s3 : s7), the text's length; a0 := s4 + 1 and malloc (0x8520c), whose
   return is K85210 f.

   THE FORM: plugin-hostd/fuzz_command's image-B harness walk (origin/ossv/recipes 3abc3740de97): its
   lib/B/Prog/LLVMFuzzerTestOneInput_s23.v for the header bytes (a seed with the cursor's bytes as a region and the
   cursor's range as a fact, so the instrumented checks vanish by the region's shadow entry and UBSan's p + k tests
   are decided in the run), its _s24.v:574-579 for a trap branch the run cannot decide (psrr_branch_tok, the trap
   side refuted by exfalso and the arithmetic fact, B-DELTA.md section 2.2 (c)), its _s41.v aw_strnlen_loc for the
   runtime call; image A's S01 / S02 walk (LLVMFuzzerTestOneInput_s12.v, image A's S01 / S02 commit 119b28fad68f)
   for the allocator call and the cut's premises from the run's registers (prreg) and the call's post. The walk is cut
   at three inner points, each stated as "from this point to the return, under the entry's context" in the shape
   of the defs file's cut statements:
     0x85110 K85110 f --K-->  0x851dc S4_T f  (the reads and the take, 160(s1) := N1)
     0x851dc S4_T f   --T-->  0x851f8 S4_M f  (memchr, or a0 = 0 when NP = 0)
     0x851f8 S4_M f   --M-->  0x85208 S4_C f  (152(s1) := NP, s4 := the text's length)
     0x85208 S4_C f   --C-->  0x85210 K85210 f (malloc(n + 1))
   The trap branches of S04 (map section 10, the UBSan-only walk's lib/U/Prog/Seg/L01.v rows 4-8): 0x8511c,
   0x8515c, 0x85190 decided in the run by the cursor's range [4096, 0x7fffff800000] (the payload's block from
   AR_blocks_law, or the empty object 0x5dee20); with 0, 1 or 2 bytes left (s7 = 0) the run decides 0x851c4 and
   0x851d4 too; with 3 or more, 0x851c4 is split and its trap side refuted (P1 + NP < 2 ^ 64: NP <= 65535 and
   P1 <= 0x7fffff800003), and the run decides 0x851d4 from the split's condition s8 >= s3 >= 4099. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI08 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q YF0m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaSB SegGlob PaDenot PaArt PaLibF
PaLibG.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase SegRo SegRecBase SegRep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_c SegInstB LLVMFuzzerTestOneInput_inst LLVMFuzzerTestOneInput_defs LLVMFuzzerTestOneInput_s14k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require MemchrDef ConstsViewDef.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Local Open Scope Z_scope.

(* ============================== the inner cut points (offsets from BASE = 0x84dc0) ============================== *)
(* 0x851dc `beqz s7,851f4`: the reads and the take done, 160(s1) = N1 *)
Definition LO_S4T : Z := 0x41c.
(* 0x851f8 `sd s7,152(s1)`: memchr returned (or a0 = 0 when NP = 0) *)
Definition LO_S4M : Z := 0x438.
(* 0x85208 `addi a0,s4,1`: s4 = the text's length *)
Definition LO_S4C : Z := 0x448.

(* the shadow base: atom 32, the word at 200(s1) (lt_frame), which the instrumented checks add (0x85124 ..) *)
Definition S14x : sv := SOff 32 0.
Definition S14span : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* s1 = sp = S1 (atom 9): above 2 ^ 46 and 32-aligned, which keeps a window of s1 slots out of the shadow band *)
Definition S14F9 : nat * afact := (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5).
(* the seed of segment K (0x85110): atom 32 the shadow base (the word at 200(s1)), atoms 33 .. 35 the cursor's first
   three bytes; the region of the s1 slots the run reads (200(s1)) and writes (160(s1)), and the region of the h
   cursor bytes the run loads (read-only; its shadow entry makes the instrumented checks vanish); the facts: S1, the
   shadow base, the cursor in [4096, 0x7fffff800000] (UBSan's p + k tests), the bytes left in [lo20, hi20], the
   bytes *)
Definition s14_rF : YP09.region := YP09.mkRegion (Some 9%nat) 160 208 160 168 [YP09.mkChunk 200 (CVal 8 (SOff 32 0))].
Definition s14_bchunks : list YP09.chunk :=
  [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0)); YP09.mkChunk 2 (CVal 1 (SOff 35 0))].
Definition s14_rP (h : Z) : YP09.region := YP09.mkRegion (Some 24%nat) 0 h 0 0 (firstn (Z.to_nat h) s14_bchunks).
Definition s14_factsK (lo20 hi20 : Z) : facts :=
  mkFacts [S14F9; (32%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (24%nat, mkAF 4096 0x7fffff800000 0);
    (20%nat, mkAF lo20 hi20 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)] [] [].
Definition s14_xK (b0 b1 b2 : Z) : list word := map (Z_to_bv 64) [SHADOW_OFF; b0; b1; b2].
Definition s14_SHK (h : Z) : list shent := [mkSHE 24 0 h].
(* a byte the reader shows is a 1-byte field of the restricted memory (fuzz_command's _s23.v lhh_aval1,
   lhh_val_of_aval) *)
Lemma s14_aval1 : forall (rd : reader) a v, rd a = Some v -> 0 <= v < 256 -> aval_mem rd a 1 v.
Proof.
intros rd a v H Hv k Hk. assert (k = 0%nat) as -> by lia. cbn [Z.of_nat]. rewrite Z.add_0_r, H. f_equal.
unfold YG0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
change (2 ^ 8) with 256. rewrite !(Z.mod_small v 256 Hv). reflexivity.
Qed.
Lemma s14_val_of_aval : forall segs H (mem : word -> option byte) a n v,
  aval_mem (aview segs H mem) a n v -> val_mem segs (mrestrict H mem) a n v.
Proof.
intros segs H mem a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H mem) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate Hv].
injection Hv as Hb. rewrite <- (Z_to_bv_bv_unsigned 8 b). rewrite Hb. reflexivity.
Qed.
(* a term's denotation from its value *)
Lemma s14_den : forall E e v, U E e = v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* the u16 length the run computes, (byte 2 << 8) | byte 1 (0x851b0 .. 0x851b4), is byte 1 + 256 byte 2 *)
Lemma s14_U_len : forall E b1 b2, ew E 34 = Z_to_bv 64 b1 -> ew E 35 = Z_to_bv 64 b2 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  U E (SAlu ALU_OR (SAlu ALU_SLL (SOff 35 0) (SLit 8)) (SOff 34 0)) = b1 + b2 * 256.
Proof.
intros E b1 b2 H1 H2 R1 R2.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 35 b2 H2) by lia. rewrite U_lit by lia. rewrite (U_atom E 34 b1 H1) by lia.
change (Z.land 8 63) with 8.
assert (Hs : Z.shiftl b2 8 = b2 * 256) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
rewrite (zcanon_id (Z.shiftl b2 8)) by (unfold M64; rewrite Hs; lia).
rewrite Z.lor_comm, (k14_lor b1 b2 R1 R2). apply zcanon_id. unfold M64. lia.
Qed.

(* `sub s4,a0,s3` as the run writes it, a0 + s3 * -1: the value t of a0 = s3 + t *)
Lemma s14_sub_val : forall a t, 0 <= a -> 0 <= t -> a + t < 2 ^ 64 ->
  zcanon (zalu_raw 63 64 ALU_ADD (a + t) (zcanon (zmd_raw 64 M_MUL a (zcanon (-1))))) = t.
Proof.
intros a t Ha Ht Hat. unfold zcanon, M64. cbn [zalu_raw zmd_raw].
change ((-1) mod 2 ^ 64) with (2 ^ 64 - 1).
replace (a * (2 ^ 64 - 1)) with (- a + a * 2 ^ 64) by ring. rewrite Z_mod_plus_full.
rewrite Zplus_mod_idemp_r. replace (a + t + - a) with t by ring. apply Z.mod_small. lia.
Qed.
(* a register of the symbolic state as its term's denotation, before prreg's normalisation *)
Ltac s14_rreg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
      pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
      cbn [ms_regs restrict mkst] in Hr
  end.
(* the environment at the end of a run agrees with the seed's on every atom below 1024 (the run's own atoms, the
   token atoms of the instrumented checks, start at 1024) *)
Ltac s14_envlow HS E Hagr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E' _ _ =>
      assert (Hagr : YP06.env_agree 1024 E E')
        by (split; [intros nn Hnn; repeat (rewrite ew_ewset_other by lia); reflexivity | reflexivity])
  end.
(* a register goal at the end of a run: kept (its own atom, the hypothesis EEo ties the atom to the cut's register
   and an assumption gives its value), or set (left as a goal over U) *)
Ltac s14_kept HS Hagr EEo :=
  lazymatch goal with
  | |- getr _ ?rr = _ =>
      let Q := fresh "Q" in s14_rreg HS rr Q; rewrite Q; clear Q;
      cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
      match goal with |- context [ew ?E' ?n] => try rewrite (proj1 Hagr n ltac:(lia)); rewrite (EEo n rr eq_refl) end;
      first [ reflexivity | assumption ]
  end.
Ltac s14_val HS :=
  lazymatch goal with
  | |- getr _ ?rr = w64 _ => let Q := fresh "Q" in s14_rreg HS rr Q; rewrite Q; clear Q; unfold w64; apply s14_den
  end.
(* a U goal at the end of a run, over the seed's environment *)
Ltac s14_toE E Hagr :=
  lazymatch goal with
  | |- U ?E' ?e = _ =>
      unfold U; try rewrite (YP06.sv_denot_agree 1024 E E' e Hagr (eq_refl : sv_atoms_lt 1024 e = true)); fold (U E e)
  end.
(* s1's atom at the end of a run: the seed's (the run's own atoms are above 1024) *)
Ltac s14_e9 E9u := repeat (rewrite ew_ewset_other by lia); exact E9u.
(* a branch condition at the end of a run, over the seed's environment and in U form *)
Ltac s14_HcE Hc E Hagr :=
  unfold U in Hc;
  repeat match type of Hc with
    | context [sv_denot ?E' ?e] =>
        lazymatch E' with
        | E => fail
        | _ => rewrite (YP06.sv_denot_agree 1024 E E' e Hagr (eq_refl : sv_atoms_lt 1024 e = true)) in Hc
        end
    end;
  repeat match type of Hc with
    | context [bv_unsigned (sv_denot E ?e)] => change (bv_unsigned (sv_denot E e)) with (U E e) in Hc
    end.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

Definition s14_E (regs : bvmap 5 word) (extra : list word) : env := Eimg (Ereg regs extra).
Lemma s14_E_reg : forall regs extra n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (s14_E regs extra) n = getr regs r.
Proof.
intros regs extra n r H. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
unfold s14_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact H.
Qed.
Lemma s14_E_extra : forall regs extra j, (j < length extra)%nat -> (j < 16)%nat ->
  ew (s14_E regs extra) (32 + j) = nth j extra (Z_to_bv 64 0).
Proof.
intros regs extra j Hj H16. unfold s14_E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra.
Qed.
(* the seed of a stretch with no region and no fact *)
Lemma s14_seed0 : forall pc (W : world SEGS) regs extra mem,
  st_ok_pi SEGS VAL (s14_E regs extra) (mkSS pc sr_atoms [] None (mkFacts [] [] []))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros pc W regs extra mem. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s14_E. apply regs_ok_Eimg_Ereg.
- reflexivity.
- apply Forall_nil.
- exact I.
- split; [exact I | split; [exact I | exact I]].
Qed.
(* a run that has no write window keeps every byte *)
Lemma s14_nowin_kept : forall E (W : world SEGS) (m m' : word -> option byte),
  frame_of E [] (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
  forall a, 0 <= a < 2 ^ 64 -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' HF a Ha.
apply (kept_of_frame (segs:=SEGS) E [] (w_H W) m m' (fun _ => False) HF); [|exact Ha|tauto].
intros b wlo whi a' Hin. cbn [windows map In] in Hin. destruct Hin.
Qed.
(* the word a region's 8-byte chunk holds, at a state the region is part of *)
Lemma s14_region_word : forall E H (mem : word -> option byte) r n b off e v,
  region_ok SEGS E (mrestrict H mem) r -> YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks r) -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview SEGS H mem) (b + off) = Some v.
Proof.
intros E H mem r n b off e v (_ & _ & _ & HC) Hb Hn Hin He Hv.
rewrite Hb in HC. cbn [base_val] in HC. rewrite Hn in HC.
rewrite Forall_forall in HC. specialize (HC _ Hin).
apply rdword_of_val_mem; [|exact Hv].
apply (val_of_chunk_ok SEGS E _ b off 8 e v HC He); [exact Hv | cbn; lia].
Qed.
(* a run whose only write window is one region's keeps every byte outside it *)
Lemma s14_win_kept : forall E (W : world SEGS) (m m' : word -> option byte) r n b,
  frame_of E [r] (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> YP09.r_base r = Some n -> bv_unsigned (ew E n) = b ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (b + YP09.r_wlo r <= a < b + YP09.r_whi r) -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' r n b HF Hb Hn a Ha Hw.
apply (kept_of_frame (segs:=SEGS) E [r] (w_H W) m m' (fun a => b + YP09.r_wlo r <= a < b + YP09.r_whi r) HF);
  [|exact Ha|exact Hw].
intros bb wlo whi a' Hin Ha'. unfold windows in Hin. cbn [map In] in Hin.
destruct Hin as [Hq | []]. destruct r as [rb rlo rhi rwlo rwhi rcs]. cbn [YP09.r_base] in Hb. subst rb.
injection Hq as <- <- <-. cbn [base_val] in Ha'. rewrite Hn in Ha'. cbn [YP09.r_wlo YP09.r_whi]. lia.
Qed.
(* a cursor byte of the region, from the payload's byte at that address (fuzz_command's _s23.v lhh_chunk1) *)
Lemma s14_chunk1 : forall (W : world SEGS) mem E base off (n : nat) v,
  ew E n = Z_to_bv 64 v -> 0 <= v < 256 -> rdW W mem (base + off) = Some v ->
  YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) base (YP09.mkChunk off (CVal 1 (SOff n 0))).
Proof.
intros W mem E base off n v En Hv Hrd.
apply (YI04.chunk_ok_val SEGS E _ base off 1 _ v); [cbn [sv_denot]; rewrite En, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
  | zside | zside |].
apply s14_val_of_aval. exact (s14_aval1 _ _ _ Hrd Hv).
Qed.
(* a run of segment K keeps every byte outside 160(s1) .. 168(s1) *)
Lemma s14_winK_kept : forall E (W : world SEGS) (m m' : word -> option byte) h b,
  frame_of E [s14_rF; s14_rP h] (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> bv_unsigned (ew E 9) = b ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (b + 160 <= a < b + 168) -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' h b HF Hn a Ha Hw.
apply (kept_of_frame (segs:=SEGS) E [s14_rF; s14_rP h] (w_H W) m m' (fun a => b + 160 <= a < b + 168) HF);
  [|exact Ha|exact Hw].
intros bb wlo whi a' Hin Ha'. unfold windows in Hin. cbn [map In] in Hin.
destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <- <-; cbn [base_val] in Ha'; [rewrite Hn in Ha'; lia | lia].
Qed.
(* a run whose windows are all inside s1 + [lo, hi) or empty keeps every byte outside s1 + [lo, hi) *)
Lemma s14_wins_kept : forall E (W : world SEGS) (m m' : word -> option byte) rs b lo hi,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> bv_unsigned (ew E 9) = b ->
  Forall (fun r => (YP09.r_base r = Some 9%nat /\ lo <= YP09.r_wlo r /\ YP09.r_whi r <= hi) \/
                   YP09.r_whi r <= YP09.r_wlo r) rs ->
  forall a, 0 <= a < 2 ^ 64 -> ~ (b + lo <= a < b + hi) -> rdW W m' a = rdW W m a.
Proof.
intros E W m m' rs b lo hi HF Hn HFa a Ha Hw.
apply (kept_of_frame (segs:=SEGS) E rs (w_H W) m m' (fun a => b + lo <= a < b + hi) HF); [|exact Ha|exact Hw].
intros bb wlo whi a' Hin Ha'. unfold windows in Hin. apply in_map_iff in Hin. destruct Hin as (r & Hq & Hr).
injection Hq as <- <- <-. rewrite Forall_forall in HFa.
destruct (HFa r Hr) as [(Hb & H1 & H2) | Hz]; [rewrite Hb in Ha'; cbn [base_val] in Ha'; rewrite Hn in Ha'; lia | lia].
Qed.
Ltac s14_wins_ok :=
  repeat (apply Forall_cons; [cbv beta; first [left; split; [reflexivity | cbn; lia] | right; cbn; lia] |]);
  apply Forall_nil.
(* every byte outside 160(s1) .. 168(s1) is kept from the segment's entry memory: the runs' frames, chained *)
Ltac s14_chain E9u cx :=
  let a := fresh "a" in let Ha := fresh "Ha" in let Hw := fresh "Hw" in
  intros a Ha Hw;
  repeat lazymatch goal with
  | |- aview _ _ ?m1 a = _ =>
      match goal with
      | HF : frame_of _ _ (mrestrict _ _) (mrestrict _ m1) |- _ =>
          rewrite (s14_wins_kept _ _ _ _ _ (x_s1 cx) 160 168 HF ltac:(s14_e9 E9u) ltac:(s14_wins_ok) a Ha Hw)
      end
  end; reflexivity.
(* turn f's numbers over the cursor's bytes *)
Lemma s14_vals : forall cx f,
  x_at cx f = x_cur cx f + Z.of_nat (length (seg_spec.seg_cur (x_pl cx) f)) -
    Z.of_nat (length (k14_tl (seg_spec.seg_cur (x_pl cx) f))) /\
  x_n1 cx f = Z.of_nat (length (k14_tl (seg_spec.seg_cur (x_pl cx) f))) /\
  x_np cx f = Z.of_nat (length (k14_take (seg_spec.seg_cur (x_pl cx) f))) /\
  x_curn cx f = Z.of_nat (length (seg_spec.seg_cur (x_pl cx) f)).
Proof.
intros cx f. unfold x_at, x_cur, x_n1, x_np, x_curn, seg_spec.seg_turn_at, seg_spec.seg_cur_at, seg_spec.seg_cur_n.
rewrite k14_tl_eq, k14_np_eq. repeat split; lia.
Qed.

Section e.
Variable B : asyms.
Variable MT : ameter_ops.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* image B's record of the image facts a walk cannot compute over an abstract SEGS (lib/B/Prog/SegRecBase.v) *)
Hypothesis IMGF : seg_img_facts SEGS B.
(* the record's symbols are image B's (lib/B/YF0m.v): the stack guard's .got word and the memchr window's
   unownedness come from it (SegRecCells.seg_rec_cells, SegRecBase.seg_snl_unowned) *)
Hypothesis HSY : YF0m.SegBSyms B.
Hypothesis AMALLOC4 : forall fx0 : YK11.FPState, @amalloc04_rule fx0 rc SK SEGS B MT.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B memchr_loA memchr_hiA (pa_sigma SS___interceptor_trampoline_memchr).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
(* the kit at this Section's hypotheses *)
Let K_core_keep := k14_core_keep B MT MTL TL IMGF HSY AMALLOC4 AMEMCHR.
Let K_malloc_at := k14_malloc_at B MT MTL TL IMGF HSY AMALLOC4 AMEMCHR.
Let K_memchr_at := k14_memchr_at B MT MTL TL IMGF HSY AMALLOC4 AMEMCHR.
Let K_hblk := k14_hblk B MT MTL TL IMGF HSY AMALLOC4 AMEMCHR.
Let K_sp := k14_sp B MT MTL TL IMGF HSY AMALLOC4 AMEMCHR.
Let K_cur_rd := k14_cur_rd B MT MTL TL IMGF HSY AMALLOC4 AMEMCHR.
Let K_payload_live := k14_payload_live B MT MTL TL IMGF HSY AMALLOC4 AMEMCHR.

(* the part every inner cut of S04 shares with K85110 f: the core at turn f with c and m, both harness blocks, c and
   m holding the state after f turns, the counters' bounds *)
Definition S4_body (cx : lcx) ly S (W : world SEGS) (regs : bvmap 5 word) mem md (k acc : Z) (c m : Z) (f : nat)
  : Prop :=
  lt_core B MT cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] /\
  lt_hblk B ly S (rdW W mem) c seg_spec.SEG_C_SIZE /\ lt_hblk B ly S (rdW W mem) m seg_spec.SEG_M_SIZE /\
  lt_cm (rdW W mem) c m (x_st cx f) /\
  lt_cnt f (seg_spec.seg_rc (x_st cx f)) (seg_spec.seg_mc (x_st cx f)).

(* ---- 0x85208: s4 = the text's length; s2 = nfiles, s3 = P1, s5 = 0, s6 = m, s8 = P1 + NP, s9 = f, s10 = lb;
   152(s1) = NP, 160(s1) = N1 ---- *)
Definition S4_C_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  S4_body cx ly S W regs mem md k acc c m f ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 19 = w64 (x_at cx f) ->
  getr regs 20 = w64 (seg_spec.seg_txt_n (x_pl cx) f) -> getr regs 21 = w64 0 -> getr regs 22 = w64 m ->
  getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f) ->
  getr regs 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++
    [(152, x_np cx f); (160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S4C) regs mem md) (lt_post B MT cx).

(* ---- segment C: 0x85208 .. 0x8520c, a0 := s4 + 1, malloc(n + 1) to K85210 f ---- *)
Lemma s14_C : forall f, LTA_K85210 B MT f -> S4_C_stmt f.
Proof.
intros f HKA cx ly S W regs mem md k acc c m HB Hfrm Hf HBODY R18 R19 R20 R21 R22 R24 R25 R26 HSL.
pose proof (HKA fx) as HK. clear HKA.
destruct HBODY as (HC & HHc & HHm & HCM & HCNT).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
pose proof (s14_seed0 LO_S4C W regs [] mem) as HS.
assert (SHOK : sh_ok SEGS S14x [] (s14_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (HEI : img_env VAL A_LIM (s14_E regs [])) by (unfold s14_E; apply Eimg_env).
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs []) n = getr regs rr)
  by (intros n rr Hn; exact (s14_E_reg regs [] n rr Hn)).
pose proof HC as (HF & _). pose proof (proj1 HF) as HJ.
remember (s14_E regs []) as E eqn:HE. clear HE.
(* the text's length: at most 65535 *)
assert (Htn : 0 <= seg_spec.seg_txt_n (x_pl cx) f <= 65535).
{ rewrite (k14_txt_eq (x_pl cx) f Hf). pose proof (k14_n_le (seg_spec.seg_cur (x_pl cx) f)). lia. }
unfold cfg_at, w64.
(* 0x85208 .. 0x8520c: a0 := s4 + 1, jal malloc *)
paj_run_tok RUN HS HJ SHOK S14span.
{ apply awr_ok_nil. }
lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10.
assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26]%bv -> getr (ms_regs ms) r = getr regs r).
{ intros r Hr. cbn [In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
      rewrite P; apply EEo; reflexivity | ]).
  destruct Hr. }
pose proof (s14_nowin_kept E W mem (ms_mem ms) HFr) as KM.
pose proof (K_core_keep cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (ms_regs ms) (ms_mem ms) md1 (x_s1 cx) (x_s1 cx) HB HC HJ
  ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia) ltac:(lia)
  (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
  (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
eapply (K_malloc_at cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (seg_spec.seg_txt_n (x_pl cx) f + 1) _ _ HB HC1).
- lia.
- lia.
- cbn [k14_bsum snd]. unfold seg_spec.SEG_M_SIZE, seg_spec.SEG_C_SIZE, LIVE_LTOI. lia.
- rewrite P10, (EEo 20%nat 20%bv eq_refl), R20. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- rewrite YP03.unsigned_lit_small by lia. lia.
- intros ly2 S2 W2 regs2 mem2 md2 t HC2 HHt HPr Hres HKS HKB.
  replace (6 + 2 * (x_nf cx - Z.of_nat f) - 1) with (5 + 2 * (x_nf cx - Z.of_nat f)) in HC2 by ring.
  pose proof HC2 as (HF2 & _ & HBL2 & _). pose proof (proj1 (proj1 HF2)) as HAR2.
  assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
    by (intros r z Hz Hr; exact (k14_pres_reg _ _ r z HPr Hz Hr)).
  pose proof HC as (_ & _ & HBL & _).
  assert (Hinc : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. right. left. reflexivity. }
  assert (Hinm : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S)).
  { apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. left. reflexivity. }
  apply (HK cx ly2 S2 W2 regs2 mem2 md2 (k + 1) (acc + mo_malloc MT (seg_spec.seg_txt_n (x_pl cx) f + 1)) c m t
    HB Hfrm Hf HC2).
  + apply (K_hblk ly2 S2 W2 mem2 md2 c _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right. right. left. reflexivity.
  + apply (K_hblk ly2 S2 W2 mem2 md2 m _ HAR2).
    unfold lt_blocks in HBL2. apply (Permutation_in _ (Permutation_sym HBL2)). cbn [app]. right. left. reflexivity.
  + exact HHt.
  + exact Hres.
  + rewrite (Hpres 18%bv 18) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 18%bv ltac:(cbn; tauto)). exact R18.
  + rewrite (Hpres 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 19%bv ltac:(cbn; tauto)). exact R19.
  + rewrite (Hpres 20%bv 20) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 20%bv ltac:(cbn; tauto)). exact R20.
  + rewrite (Hpres 21%bv 21) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
  + rewrite (Hpres 22%bv 22) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
  + rewrite (Hpres 24%bv 24) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 24%bv ltac:(cbn; tauto)). exact R24.
  + rewrite (Hpres 25%bv 25) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 25%bv ltac:(cbn; tauto)). exact R25.
  + rewrite (Hpres 26%bv 26) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
    rewrite (KR 26%bv ltac:(cbn; tauto)). exact R26.
  + apply (k14_slots_kept cx (rdW W mem)); [|exact HSL].
    intros o v Hin x Hx.
    assert (Ho : 16 <= o <= 216).
    { rewrite in_app_iff in Hin. cbn [LT_L In] in Hin.
      repeat match goal with H : _ \/ _ |- _ => destruct H end;
      match goal with H : (_, _) = (o, v) |- _ => injection H as <- _; lia | H : False |- _ => destruct H end. }
    rewrite (HKS x) by lia. apply KM. lia.
  + apply (k14_cm_kept (rdW W mem)); [| |exact HCM].
    * intros x Hx. replace x with (c + (x - c)) by ring. rewrite (HKB c seg_spec.SEG_C_SIZE (x - c) Hinc) by lia.
      apply KM. pose proof (proj2 (proj2 (proj2 HHc))) as (Hca & Hcb & _). lia.
    * intros x Hx. replace x with (m + (x - m)) by ring. rewrite (HKB m seg_spec.SEG_M_SIZE (x - m) Hinm) by lia.
      apply KM. pose proof (proj2 (proj2 (proj2 HHm))) as (Hma & Hmb & _). lia.
  + exact HCNT.
Qed.

(* ---- the facts the inner segments share ---- *)
(* the stack from S1 to the entry sp is present at every point of the harness (the journal's stack clause) *)
(* the fact S14F9 at a point of the harness *)
Lemma s14_s1F : forall cx ly S (W : world SEGS) regs mem md k acc rem o O extra,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  afact_ok (s14_E regs extra) 9 (mkAF (2 ^ 46) (2 ^ 47) 5).
Proof.
intros cx ly S W regs mem md k acc rem o O extra HB HC.
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
pose proof HC as ((_ & _ & _ & _ & _ & R9 & _) & _).
unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite (s14_E_reg regs extra 9 9%bv eq_refl), R9. unfold w64. rewrite unsigned_lit_small by lia.
change (2 ^ 5) with 32. split; [lia|]. split; [exact Hs1al | lia].
Qed.
Lemma s14_stk_pres : forall cx ly S (W : world SEGS) regs mem md k acc rem o O,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  forall a, x_s1 cx <= a < x_sp0 cx -> apresent (w_H W) mem a.
Proof.
intros cx ly S W regs mem md k acc rem o O HB HC a Ha.
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct HC as ((HJ & _) & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
apply Hpres. assert (HLS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. lia.
Qed.
(* a window of the walk's s1 slots is in the function's own stack window *)
Lemma s14_awr_win : forall cx E lo hi FP bl0 blc fr0 lyx own,
  lt_base B MT cx -> bv_unsigned (ew E 9) = x_s1 cx -> 0 <= lo -> hi <= 352 ->
  awr_ok SEGS B E [YP09.mkRegion (Some 9%nat) lo hi lo hi []] STK_LLVMFuzzerTestOneInput (x_sp0 cx) FP bl0 blc fr0
    lyx own.
Proof.
intros cx E lo hi FP bl0 blc fr0 lyx own HB Hew Hlo Hhi a (r & Hin & Ha).
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Hew in Ha.
left. assert (HLS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. lia.
Qed.
(* the seed of a stretch whose one region is a window of s1 slots *)
Lemma s14_seed_win : forall cx ly S W regs mem md k acc rem o O pc lo hi G extra,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  regions_wf [YP09.mkRegion (Some 9%nat) lo hi lo hi []] = true -> 0 <= lo -> hi <= 352 ->
  facts_ok (s14_E regs extra) G ->
  st_ok_pi SEGS VAL (s14_E regs extra) (mkSS pc sr_atoms [YP09.mkRegion (Some 9%nat) lo hi lo hi []] None G)
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + pc)) mem (seg_rom SEGS))).
Proof.
intros cx ly S W regs mem md k acc rem o O pc lo hi G extra HB HC Hwf Hlo Hhi HG.
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
pose proof HC as ((_ & R2 & _ & _ & _ & R9 & _) & _).
assert (E9 : bv_unsigned (ew (s14_E regs extra) 9) = x_s1 cx).
{ rewrite (s14_E_reg regs extra 9 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold s14_E. apply regs_ok_Eimg_Ereg.
- exact Hwf.
- apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite E9.
  split; [lia|]. split; [lia|]. split; [|constructor].
  intros o' Ho'. apply (apresent_writable SEGS). apply (s14_stk_pres cx ly S W regs mem md k acc rem o O HB HC). lia.
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- exact HG.
Qed.
(* the slots of LT_L: below 128 or in 168 .. 224 *)
Lemma s14_LT_L_off : forall cx c m o v, In (o, v) (LT_L cx c m) -> (16 <= o /\ o + 8 <= 128) \/ (168 <= o <= 216).
Proof.
intros cx c m o v Hin. cbn [LT_L In] in Hin.
repeat match goal with H : _ \/ _ |- _ => destruct H end;
match goal with H : (_, _) = (o, v) |- _ => injection H as <- _; lia | H : False |- _ => destruct H end.
Qed.
(* the take's address and count: inside the input, the count at most the bytes left after the header *)
Lemma s14_pt : forall cx f, lt_base B MT cx ->
  x_p cx <= x_at cx f /\ x_at cx f + x_np cx f <= x_p cx + x_n cx /\ 0 <= x_np cx f /\ x_np cx f <= x_n1 cx f /\
  x_n1 cx f <= x_n cx.
Proof.
intros cx f HB. pose proof HB as (_ & _ & _ & _ & _ & _ & _ & HLEN & _).
unfold x_at, x_np, x_n1, seg_spec.seg_turn_at. rewrite k14_np_eq, k14_tl_eq.
pose proof (k14_tail_len (x_pl cx) f) as (H1 & H2). lia.
Qed.
(* the payload's block, when the payload has a byte *)
Lemma s14_pblk : forall cx ly S (W : world SEGS) regs mem md k acc rem o O,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O -> 0 < x_n cx ->
  4096 <= x_p cx /\ x_p cx + x_n cx <= alloc_ceiling.
Proof.
intros cx ly S W regs mem md k acc rem o O HB HC Hn.
pose proof HC as ((HJ & _) & _ & HBL & _). pose proof (proj1 HJ) as HAR.
pose proof (K_payload_live cx ly S O HB HBL Hn) as Hin.
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq]. lia.
Qed.
(* the slots of a point kept by a memory that agrees outside one window of s1 slots *)
Lemma s14_slots_win : forall cx (rd rd' : reader) L lo hi,
  (forall x, 0 <= x < 2 ^ 64 -> ~ (x_s1 cx + lo <= x < x_s1 cx + hi) -> rd' x = rd x) ->
  (forall o v, In (o, v) L -> (o + 8 <= lo \/ hi <= o) /\ 0 <= x_s1 cx + o /\ x_s1 cx + o + 8 <= 2 ^ 64) ->
  lt_slots cx rd L -> lt_slots cx rd' L.
Proof.
intros cx rd rd' L lo hi HK Ho H. apply (k14_slots_kept cx rd rd' L); [|exact H].
intros o v Hin x Hx. pose proof (Ho o v Hin). apply HK; lia.
Qed.

(* ---- 0x851f8: memchr's answer in a0 (P1 + n when the taken bytes hold a NUL at n, else 0), s7 = NP; s2, s3, s5,
   s6, s8, s9, s10 as at S4_C; 160(s1) = N1 ---- *)
Definition S4_M_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  S4_body cx ly S W regs mem md k acc c m f ->
  getr regs 10 = w64 (if seg_spec.seg_txt_n (x_pl cx) f <? x_np cx f
                      then x_at cx f + seg_spec.seg_txt_n (x_pl cx) f else 0) ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 19 = w64 (x_at cx f) -> getr regs 21 = w64 0 -> getr regs 22 = w64 m ->
  getr regs 23 = w64 (x_np cx f) -> getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f) ->
  getr regs 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S4M) regs mem md) (lt_post B MT cx).

(* the cut S4_C from a state a run of segment M reaches *)
Lemma s14_M_to_C : forall f, S4_C_stmt f ->
  forall cx ly S W regs mem md k acc c m regs' mem' md',
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx -> S4_body cx ly S W regs mem md k acc c m f ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 152 <= a < x_s1 cx + 160) -> rdW W mem' a = rdW W mem a) ->
  rdword (rdW W mem') (x_s1 cx + 152) = Some (x_np cx f) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 18 = w64 (x_nf cx) -> getr regs' 19 = w64 (x_at cx f) ->
  getr regs' 20 = w64 (seg_spec.seg_txt_n (x_pl cx) f) -> getr regs' 21 = w64 0 -> getr regs' 22 = w64 m ->
  getr regs' 24 = w64 (x_at cx f + x_np cx f) -> getr regs' 25 = w64 (Z.of_nat f) ->
  getr regs' 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S4C) regs' mem' md') (lt_post B MT cx).
Proof.
intros f HCC cx ly S W regs mem md k acc c m regs' mem' md' HB Hfrm Hf HBODY HSL HJ' KM H152
  P2 P3 P4 P8 P9 R18 R19 R20 R21 R22 R24 R25 R26.
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
destruct HBODY as (HC & HHc & HHm & HCM & HCNT).
pose proof (K_core_keep cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] regs' mem' md' (x_s1 cx + 152) (x_s1 cx + 160) HB HC HJ' KM
  ltac:(lia) ltac:(lia) ltac:(lia) P2 P3 P4 P8 P9) as HC'.
pose proof (proj1 HJ') as HAR'.
pose proof HC as (_ & _ & HBL & _).
assert (Hinc : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. right. left. reflexivity. }
assert (Hinm : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. left. reflexivity. }
pose proof (proj1 (proj1 HC)) as HJ0. pose proof (proj1 HJ0) as HAR0.
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR0 Hinc) as (_ & Hc4096 & Hcceil & _).
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR0 Hinm) as (_ & Hm4096 & Hmceil & _).
pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ Hrc].
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hrm].
apply (HCC cx ly S W regs' mem' md' k acc c m HB Hfrm Hf); [|exact R18 | exact R19 | exact R20 | exact R21 | exact R22
  | exact R24 | exact R25 | exact R26 |].
- split; [exact HC'|]. split; [exact (K_hblk ly S W mem' md' c _ HAR' Hinc)|].
  split; [exact (K_hblk ly S W mem' md' m _ HAR' Hinm)|]. split; [|exact HCNT].
  apply (k14_cm_kept (rdW W mem)); [| |exact HCM]; intros x Hx; apply KM; lia.
- intros o v Hin. rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  + apply (s14_slots_win cx (rdW W mem) (rdW W mem') (LT_L cx c m) 152 160).
    * intros x Hx0 Hx. apply KM; [exact Hx0 | exact Hx].
    * intros o' v' Hin'. pose proof (s14_LT_L_off cx c m o' v' Hin'). lia.
    * intros o' v' Hin'. apply HSL. apply in_or_app. left. exact Hin'.
    * exact Hin.
  + cbn [In] in Hin. destruct Hin as [Hq | [Hq | [Hq | []]]]; injection Hq as <- <-.
    * exact H152.
    * apply (k14_word_kept (rdW W mem)); [|apply HSL; apply in_or_app; right; left; reflexivity].
      intros x Hx. apply KM; lia.
    * apply (k14_word_kept (rdW W mem)); [|apply HSL; apply in_or_app; right; right; left; reflexivity].
      intros x Hx. apply KM; lia.
Qed.

(* ---- segment M: 0x851f8 .. 0x85204, 152(s1) := s7, s4 := (a0 ? a0 - s3 : s7) to S4_C f ---- *)
Definition s14_rM : YP09.region := YP09.mkRegion (Some 9%nat) 152 160 152 160 [].
Lemma s14_M : forall f, S4_C_stmt f -> S4_M_stmt f.
Proof.
intros f HCC cx ly S W regs mem md k acc c m HB Hfrm Hf HBODY R10 R18 R19 R21 R22 R23 R24 R25 R26 HSL.
pose proof HBODY as (HC & _).
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s14_pt cx f HB) as (Hat0 & Hatn & Hnp0 & Hnpn & Hn1n).
assert (Htn : 0 <= seg_spec.seg_txt_n (x_pl cx) f <= x_np cx f).
{ rewrite (k14_txt_eq (x_pl cx) f Hf). unfold x_np. rewrite k14_np_eq.
  pose proof (k14_n_le (seg_spec.seg_cur (x_pl cx) f)). lia. }
assert (Hnpmax : x_np cx f <= 65535).
{ unfold x_np. rewrite k14_np_eq. pose proof (k14_n_le (seg_spec.seg_cur (x_pl cx) f)). lia. }
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs []) n = getr regs rr)
  by (intros n rr Hn; exact (s14_E_reg regs [] n rr Hn)).
assert (HEI : img_env VAL A_LIM (s14_E regs [])) by (unfold s14_E; apply Eimg_env).
pose proof HC as ((HJ & _ & _ & _ & _ & R9 & _) & _).
assert (E9 : bv_unsigned (ew (s14_E regs []) 9) = x_s1 cx).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (SHOK : sh_ok SEGS S14x [] (s14_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold cfg_at, w64.
destruct (Z.ltb_spec (seg_spec.seg_txt_n (x_pl cx) f) (x_np cx f)) as [Hlt | Hge].
- (* the taken bytes hold a NUL: a0 = P1 + n >= 4096, so beqz a0 is not taken *)
  assert (Hn0 : 0 < x_n cx) by lia.
  pose proof (s14_pblk cx ly S W regs mem md k acc _ _ _ HB HC Hn0) as (Hp4096 & Hpceil).
  assert (E10 : ew (s14_E regs []) 10 = Z_to_bv 64 (x_at cx f + seg_spec.seg_txt_n (x_pl cx) f))
    by (rewrite (EEo 10%nat 10%bv eq_refl), R10; reflexivity).
  pose proof (s14_seed_win cx ly S W regs mem md k acc _ _ _ LO_S4M 152 160
    (mkFacts [S14F9; (10%nat, mkAF 4096 (2 ^ 47) 0)] [] []) [] HB HC eq_refl ltac:(lia) ltac:(lia)) as HS0.
  assert (HS : st_ok_pi SEGS VAL (s14_E regs []) (mkSS LO_S4M sr_atoms [s14_rM] None
      (mkFacts [S14F9; (10%nat, mkAF 4096 (2 ^ 47) 0)] [] []))
      (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_S4M)) mem (seg_rom SEGS)))).
  { apply HS0. split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok S14F9 fst snd]. split; [exact (s14_s1F cx ly S W regs mem md k acc _ _ _ [] HB HC)|].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E10.
    rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity]. }
  clear HS0.
  remember (s14_E regs []) as E eqn:HE. clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4C.
  { exact (s14_awr_win cx E 152 160 _ _ _ _ _ _ HB E9 ltac:(lia) ltac:(lia)). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s14_rM) in
    pose proof (st_ok_pi_region_nth E ssx _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
  pmkst HS.
  pose proof (s14_win_kept E W mem (ms_mem ms) s14_rM 9 (x_s1 cx) HFr eq_refl E9) as KM.
  cbn [YP09.r_wlo YP09.r_whi s14_rM] in KM.
  apply (s14_M_to_C f HCC cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) md1 HB Hfrm Hf HBODY HSL HJ KM).
  + apply (s14_region_word E (w_H W) (ms_mem ms) _ 9 (x_s1 cx) 152 (SOff 23 0) (x_np cx f) HR0 eq_refl E9);
      [cbn; tauto | | lia].
    cbn [sv_denot]. rewrite (EEo 23%nat 23%bv eq_refl), R23, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned.
  + prreg HS (2%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (3%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (4%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (8%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (9%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (18%bv : bv 5) P; rewrite P, (EEo 18%nat 18%bv eq_refl); exact R18.
  + prreg HS (19%bv : bv 5) P; rewrite P, (EEo 19%nat 19%bv eq_refl); exact R19.
  + s14_rreg HS (20%bv : bv 5) Q. rewrite Q. unfold w64.
    assert (E19 : ew E 19 = Z_to_bv 64 (x_at cx f)) by (rewrite (EEo 19%nat 19%bv eq_refl), R19; reflexivity).
    assert (Q20 : U E (SAlu ALU_ADD (SOff 10 0) (SMd M_MUL (SOff 19 0) (SLit (-1)))) = seg_spec.seg_txt_n (x_pl cx) f).
    { rewrite U_SAlu, U_SMd, U_SLit. rewrite (U_atom E 10 _ E10) by lia. rewrite (U_atom E 19 _ E19) by lia.
      apply s14_sub_val; lia. }
    rewrite <- Q20. unfold U. symmetry. apply Z_to_bv_bv_unsigned.
  + prreg HS (21%bv : bv 5) P; rewrite P, (EEo 21%nat 21%bv eq_refl); exact R21.
  + prreg HS (22%bv : bv 5) P; rewrite P, (EEo 22%nat 22%bv eq_refl); exact R22.
  + prreg HS (24%bv : bv 5) P; rewrite P, (EEo 24%nat 24%bv eq_refl); exact R24.
  + prreg HS (25%bv : bv 5) P; rewrite P, (EEo 25%nat 25%bv eq_refl); exact R25.
  + prreg HS (26%bv : bv 5) P; rewrite P, (EEo 26%nat 26%bv eq_refl); exact R26.
- (* no NUL: a0 = 0, so beqz a0 is taken and s4 = s7 = NP, the text's length *)
  assert (Etn : seg_spec.seg_txt_n (x_pl cx) f = x_np cx f) by lia.
  pose proof (s14_seed_win cx ly S W regs mem md k acc _ _ _ LO_S4M 152 160 (mkFacts [S14F9] [] []) [] HB HC eq_refl
    ltac:(lia) ltac:(lia)
    ltac:(split; [cbn [f_atoms atoms_ok S14F9 fst snd]; exact (conj (s14_s1F cx ly S W regs mem md k acc _ _ _ [] HB HC) I)
                 | split; [exact I | exact I]])) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (10%bv : bv 5) 0 HS0 ltac:(cbn [ms_regs restrict mkst]; exact R10) eq_refl) as HS.
  clear HS0.
  remember (s14_E regs []) as E eqn:HE. clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4C.
  { exact (s14_awr_win cx E 152 160 _ _ _ _ _ _ HB E9 ltac:(lia) ltac:(lia)). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  lazymatch type of HS with st_ok_pi _ _ _ ?ssx _ =>
    let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s14_rM) in
    pose proof (st_ok_pi_region_nth E ssx _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as HR0 end.
  pmkst HS.
  pose proof (s14_win_kept E W mem (ms_mem ms) s14_rM 9 (x_s1 cx) HFr eq_refl E9) as KM.
  cbn [YP09.r_wlo YP09.r_whi s14_rM] in KM.
  apply (s14_M_to_C f HCC cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) md1 HB Hfrm Hf HBODY HSL HJ KM).
  + apply (s14_region_word E (w_H W) (ms_mem ms) _ 9 (x_s1 cx) 152 (SOff 23 0) (x_np cx f) HR0 eq_refl E9);
      [cbn; tauto | | lia].
    cbn [sv_denot]. rewrite (EEo 23%nat 23%bv eq_refl), R23, Z.add_0_r. unfold w64. apply Z_to_bv_bv_unsigned.
  + prreg HS (2%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (3%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (4%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (8%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (9%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (18%bv : bv 5) P; rewrite P, (EEo 18%nat 18%bv eq_refl); exact R18.
  + prreg HS (19%bv : bv 5) P; rewrite P, (EEo 19%nat 19%bv eq_refl); exact R19.
  + prreg HS (20%bv : bv 5) P; rewrite P, (EEo 23%nat 23%bv eq_refl), R23, Etn; reflexivity.
  + prreg HS (21%bv : bv 5) P; rewrite P, (EEo 21%nat 21%bv eq_refl); exact R21.
  + prreg HS (22%bv : bv 5) P; rewrite P, (EEo 22%nat 22%bv eq_refl); exact R22.
  + prreg HS (24%bv : bv 5) P; rewrite P, (EEo 24%nat 24%bv eq_refl); exact R24.
  + prreg HS (25%bv : bv 5) P; rewrite P, (EEo 25%nat 25%bv eq_refl); exact R25.
  + prreg HS (26%bv : bv 5) P; rewrite P, (EEo 26%nat 26%bv eq_refl); exact R26.
Qed.

(* ---- 0x851dc: the reads and the take done; s3 = P1, s4 = N1, s7 = NP, s8 = P1 + NP, s10 = lb; s2, s5, s6, s9 as at
   K85110; 160(s1) = N1 ---- *)
Definition S4_T_stmt (f : nat) : Prop :=
  forall cx ly S W regs mem md k acc (c m : Z),
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx ->
  S4_body cx ly S W regs mem md k acc c m f ->
  getr regs 18 = w64 (x_nf cx) -> getr regs 19 = w64 (x_at cx f) -> getr regs 20 = w64 (x_n1 cx f) ->
  getr regs 21 = w64 0 -> getr regs 22 = w64 m -> getr regs 23 = w64 (x_np cx f) ->
  getr regs 24 = w64 (x_at cx f + x_np cx f) -> getr regs 25 = w64 (Z.of_nat f) ->
  getr regs 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S4T) regs mem md) (lt_post B MT cx).

(* the cut S4_M from a state a stretch of segment T reaches: the memory agrees outside one window below S1 *)
Lemma s14_to_M : forall f, S4_M_stmt f ->
  forall cx ly S W regs mem md k acc c m regs' mem' md' wlo whi,
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx -> S4_body cx ly S W regs mem md k acc c m f ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(160, x_n1 cx f); (176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (wlo <= a < whi) -> rdW W mem' a = rdW W mem a) ->
  alloc_ceiling <= wlo -> wlo <= whi -> whi <= x_s1 cx ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 10 = w64 (if seg_spec.seg_txt_n (x_pl cx) f <? x_np cx f
                       then x_at cx f + seg_spec.seg_txt_n (x_pl cx) f else 0) ->
  getr regs' 18 = w64 (x_nf cx) -> getr regs' 19 = w64 (x_at cx f) -> getr regs' 21 = w64 0 ->
  getr regs' 22 = w64 m -> getr regs' 23 = w64 (x_np cx f) -> getr regs' 24 = w64 (x_at cx f + x_np cx f) ->
  getr regs' 25 = w64 (Z.of_nat f) -> getr regs' 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S4M) regs' mem' md') (lt_post B MT cx).
Proof.
intros f HMM cx ly S W regs mem md k acc c m regs' mem' md' wlo whi HB Hfrm Hf HBODY HSL HJ' KM Hlo Hlh Hhi
  P2 P3 P4 P8 P9 R10 R18 R19 R21 R22 R23 R24 R25 R26.
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
destruct HBODY as (HC & HHc & HHm & HCM & HCNT).
pose proof (K_core_keep cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] regs' mem' md' wlo whi HB HC HJ' KM
  Hlo Hlh ltac:(lia) P2 P3 P4 P8 P9) as HC'.
pose proof (proj1 HJ') as HAR'.
pose proof HC as (_ & _ & HBL & _).
assert (Hinc : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. right. left. reflexivity. }
assert (Hinm : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. left. reflexivity. }
pose proof (proj1 (proj1 HC)) as HJ0. pose proof (proj1 HJ0) as HAR0.
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR0 Hinc) as (_ & Hc4096 & Hcceil & _).
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR0 Hinm) as (_ & Hm4096 & Hmceil & _).
pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ Hrc].
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hrm].
apply (HMM cx ly S W regs' mem' md' k acc c m HB Hfrm Hf); [|exact R10 | exact R18 | exact R19 | exact R21 | exact R22
  | exact R23 | exact R24 | exact R25 | exact R26 |].
- split; [exact HC'|]. split; [exact (K_hblk ly S W mem' md' c _ HAR' Hinc)|].
  split; [exact (K_hblk ly S W mem' md' m _ HAR' Hinm)|]. split; [|exact HCNT].
  apply (k14_cm_kept (rdW W mem)); [| |exact HCM]; intros x Hx; apply KM; lia.
- apply (s14_slots_win cx (rdW W mem) (rdW W mem') _ (wlo - x_s1 cx) (whi - x_s1 cx)); [| |exact HSL].
  + intros x Hx0 Hx. apply KM; [exact Hx0 | lia].
  + intros o v Hin. rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
    * pose proof (s14_LT_L_off cx c m o v Hin). lia.
    * cbn [In] in Hin. destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <-; lia.
Qed.

(* the taken bytes at P1, at a point where lt_core holds *)
Lemma s14_take_rd : forall cx ly S (W : world SEGS) regs mem md k acc rem o O f,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  forall i, (i < length (k14_take (seg_spec.seg_cur (x_pl cx) f)))%nat ->
  rdW W mem (x_at cx f + Z.of_nat i) = Some (nth i (k14_take (seg_spec.seg_cur (x_pl cx) f)) 0).
Proof.
intros cx ly S W regs mem md k acc rem o O f HB HC i Hi.
pose proof (k14_tail_len (x_pl cx) f) as (H1 & H2).
rewrite (k14_take_nth _ i Hi).
replace (x_at cx f + Z.of_nat i)
  with (x_cur cx f + Z.of_nat (length (seg_spec.seg_cur (x_pl cx) f) - length (k14_tl (seg_spec.seg_cur (x_pl cx) f)) + i))
  by (unfold x_at, x_cur, seg_spec.seg_turn_at, seg_spec.seg_cur_at; rewrite k14_tl_eq; lia).
apply (K_cur_rd cx ly S W regs mem md k acc rem o O f HB HC). lia.
Qed.

(* ---- segment T: 0x851dc .. 0x851f4, memchr(s3, 0, s7) when s7 <> 0, else a0 := 0, to S4_M f ---- *)
Lemma s14_T : forall f, S4_M_stmt f -> S4_T_stmt f.
Proof.
intros f HMM cx ly S W regs mem md k acc c m HB Hfrm Hf HBODY R18 R19 R20 R21 R22 R23 R24 R25 R26 HSL.
pose proof HBODY as (HC & _).
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof (s14_pt cx f HB) as (Hat0 & Hatn & Hnp0 & Hnpn & Hn1n).
assert (Htn : 0 <= seg_spec.seg_txt_n (x_pl cx) f <= x_np cx f).
{ rewrite (k14_txt_eq (x_pl cx) f Hf). unfold x_np. rewrite k14_np_eq.
  pose proof (k14_n_le (seg_spec.seg_cur (x_pl cx) f)). lia. }
assert (Hnpmax : x_np cx f <= 65535).
{ unfold x_np. rewrite k14_np_eq. pose proof (k14_n_le (seg_spec.seg_cur (x_pl cx) f)). lia. }
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs []) n = getr regs rr)
  by (intros n rr Hn; exact (s14_E_reg regs [] n rr Hn)).
assert (HEI : img_env VAL A_LIM (s14_E regs [])) by (unfold s14_E; apply Eimg_env).
pose proof HC as ((HJ & _) & _).
assert (SHOK : sh_ok SEGS S14x [] (s14_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
unfold cfg_at, w64.
destruct (Z.eq_dec (x_np cx f) 0) as [Hz | Hnz].
- (* NP = 0: beqz s7 taken, a0 := 0 *)
  pose proof (s14_seed0 LO_S4T W regs [] mem) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (23%bv : bv 5) 0 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R23, Hz; reflexivity)
    eq_refl) as HS.
  clear HS0.
  remember (s14_E regs []) as E eqn:HE. clear HE.
  paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4M.
  { apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  pmkst HS.
  pose proof (s14_nowin_kept E W mem (ms_mem ms) HFr) as KM.
  apply (s14_to_M f HMM cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) md1 (x_s1 cx) (x_s1 cx)
    HB Hfrm Hf HBODY HSL HJ ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia) ltac:(lia)).
  + prreg HS (2%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (3%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (4%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (8%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (9%bv : bv 5) P; rewrite P; apply EEo; reflexivity.
  + prreg HS (10%bv : bv 5) P; rewrite P. rewrite Hz. replace (seg_spec.seg_txt_n (x_pl cx) f <? 0) with false
      by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  + prreg HS (18%bv : bv 5) P; rewrite P, (EEo 18%nat 18%bv eq_refl); exact R18.
  + prreg HS (19%bv : bv 5) P; rewrite P, (EEo 19%nat 19%bv eq_refl); exact R19.
  + prreg HS (21%bv : bv 5) P; rewrite P, (EEo 21%nat 21%bv eq_refl); exact R21.
  + prreg HS (22%bv : bv 5) P; rewrite P, (EEo 22%nat 22%bv eq_refl); exact R22.
  + prreg HS (23%bv : bv 5) P; rewrite P, Hz; reflexivity.
  + prreg HS (24%bv : bv 5) P; rewrite P, (EEo 24%nat 24%bv eq_refl); exact R24.
  + prreg HS (25%bv : bv 5) P; rewrite P, (EEo 25%nat 25%bv eq_refl); exact R25.
  + prreg HS (26%bv : bv 5) P; rewrite P, (EEo 26%nat 26%bv eq_refl); exact R26.
- (* NP > 0: beqz s7 not taken (s7 in [1, 65535]), memchr(P1, 0, NP) *)
  assert (Hn0 : 0 < x_n cx) by lia.
  pose proof (s14_pblk cx ly S W regs mem md k acc _ _ _ HB HC Hn0) as (Hp4096 & Hpceil).
  assert (E23 : ew (s14_E regs []) 23 = Z_to_bv 64 (x_np cx f)) by (rewrite (EEo 23%nat 23%bv eq_refl), R23; reflexivity).
  assert (HS : st_ok_pi SEGS VAL (s14_E regs []) (mkSS LO_S4T sr_atoms [] None
      (mkFacts [(23%nat, mkAF 1 65535 0)] [] []))
      (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_S4T)) mem (seg_rom SEGS)))).
  { rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
    - unfold s14_E. apply regs_ok_Eimg_Ereg.
    - reflexivity.
    - apply Forall_nil.
    - exact I.
    - split; [|split; [exact I | exact I]].
      cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E23.
      rewrite unsigned_lit_small by lia. rewrite Z.pow_0_r, Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity]. }
  remember (s14_E regs []) as E eqn:HE. clear HE.
  paj_run_tok RUN HS HJ SHOK S14span.
  { apply awr_ok_nil. }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  pmkst HS.
  pose proof (s14_nowin_kept E W mem (ms_mem ms) HFr) as KM.
  assert (KR : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%bv ->
    getr (ms_regs ms) r = getr regs r).
  { intros r Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [ let P := fresh "P" in lazymatch goal with |- getr _ ?rr = _ => prreg HS rr P end;
        rewrite P; apply EEo; reflexivity | ]).
    destruct Hr. }
  pose proof (K_core_keep cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (ms_regs ms) (ms_mem ms) md1 (x_s1 cx) (x_s1 cx) HB HC HJ
    ltac:(intros a Ha _; exact (KM a Ha)) ltac:(lia) ltac:(lia) ltac:(lia)
    (KR 2%bv ltac:(cbn; tauto)) (KR 3%bv ltac:(cbn; tauto)) (KR 4%bv ltac:(cbn; tauto))
    (KR 8%bv ltac:(cbn; tauto)) (KR 9%bv ltac:(cbn; tauto))) as HC1.
  prreg HS (1%bv : bv 5) P1. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11. prreg HS (12%bv : bv 5) P12.
  eapply (K_memchr_at cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
    [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] (x_at cx f) (x_np cx f) _ _ HB HC1).
  + rewrite P10, (EEo 19%nat 19%bv eq_refl), R19. reflexivity.
  + rewrite P11. reflexivity.
  + rewrite P12, (EEo 23%nat 23%bv eq_refl), R23. reflexivity.
  + exact P1.
  + apply ret_ok_codeptr_v; [lia | reflexivity].
  + exact Hn0.
  + exact Hat0.
  + exact Hatn.
  + exact Hnp0.
  + intros regs2 mem2 md2 kk HC2 HPr Hfb H10 KM2.
    (* kk is the text's length: the first NUL of the taken bytes *)
    assert (Ekk : kk = seg_spec.seg_txt_n (x_pl cx) f).
    { rewrite (k14_txt_eq (x_pl cx) f Hf). destruct Hfb as (F1 & F2 & F3).
      apply (k14_first_nul (rdW W (ms_mem ms)) (x_at cx f) (k14_take (seg_spec.seg_cur (x_pl cx) f)) kk).
      - exact (s14_take_rd cx ly S W (ms_regs ms) (ms_mem ms) md1 k acc _ _ _ f HB HC1).
      - unfold x_np in F1. rewrite k14_np_eq in F1. exact F1.
      - exact F2.
      - unfold x_np in F3. rewrite k14_np_eq in F3. exact F3. }
    subst kk.
    assert (Hpres : forall r z, acallee_saved z -> Z_to_bv 5 z = r -> getr regs2 r = getr (ms_regs ms) r)
      by (intros r z Hz Hr; exact (k14_pres_reg _ _ r z HPr Hz Hr)).
    (* 0x851f0: j 0x851f8 *)
    pose proof (s14_seed0 0x430 W regs2 [] mem2) as HS2.
    assert (SHOK2 : sh_ok SEGS S14x [] (s14_E regs2 []) (mrestrict (w_H W) mem2)) by apply Forall_nil.
    assert (HEI2 : img_env VAL A_LIM (s14_E regs2 [])) by (unfold s14_E; apply Eimg_env).
    assert (EE2 : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs2 []) n = getr regs2 rr)
      by (intros n rr Hn; exact (s14_E_reg regs2 [] n rr Hn)).
    pose proof HC2 as ((HJ2 & _) & _).
    remember (s14_E regs2 []) as E2 eqn:HE2. clear HE2.
    paj_run_to_tok RUNTO HS2 HJ2 SHOK2 S14span LO_S4M.
    { apply awr_ok_nil. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
    pmkst HS2.
    pose proof (s14_nowin_kept E2 W mem2 (ms_mem ms0) HFr0) as KM3.
    apply (s14_to_M f HMM cx ly S W regs mem md k acc c m (ms_regs ms0) (ms_mem ms0) md3
      (x_s1 cx - ESTACK) (x_s1 cx) HB Hfrm Hf HBODY HSL HJ2).
    * intros a Ha Hw. rewrite (KM3 a Ha), (KM2 a Ha Hw). exact (KM a Ha).
    * assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hes. lia.
    * assert (Hes : ESTACK = 4096) by reflexivity. rewrite Hes. lia.
    * lia.
    * prreg HS2 (2%bv : bv 5) P; rewrite P, (EE2 2%nat 2%bv eq_refl).
      rewrite (Hpres 2%bv 2) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). apply KR. cbn; tauto.
    * prreg HS2 (3%bv : bv 5) P; rewrite P, (EE2 3%nat 3%bv eq_refl).
      rewrite (Hpres 3%bv 3) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). apply KR. cbn; tauto.
    * prreg HS2 (4%bv : bv 5) P; rewrite P, (EE2 4%nat 4%bv eq_refl).
      rewrite (Hpres 4%bv 4) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). apply KR. cbn; tauto.
    * prreg HS2 (8%bv : bv 5) P; rewrite P, (EE2 8%nat 8%bv eq_refl).
      rewrite (Hpres 8%bv 8) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). apply KR. cbn; tauto.
    * prreg HS2 (9%bv : bv 5) P; rewrite P, (EE2 9%nat 9%bv eq_refl).
      rewrite (Hpres 9%bv 9) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]). apply KR. cbn; tauto.
    * prreg HS2 (10%bv : bv 5) P; rewrite P, (EE2 10%nat 10%bv eq_refl), H10.
      destruct (seg_spec.seg_txt_n (x_pl cx) f <? x_np cx f); reflexivity.
    * prreg HS2 (18%bv : bv 5) P; rewrite P, (EE2 18%nat 18%bv eq_refl).
      rewrite (Hpres 18%bv 18) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
      rewrite (KR 18%bv ltac:(cbn; tauto)). exact R18.
    * prreg HS2 (19%bv : bv 5) P; rewrite P, (EE2 19%nat 19%bv eq_refl).
      rewrite (Hpres 19%bv 19) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
      rewrite (KR 19%bv ltac:(cbn; tauto)). exact R19.
    * prreg HS2 (21%bv : bv 5) P; rewrite P, (EE2 21%nat 21%bv eq_refl).
      rewrite (Hpres 21%bv 21) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
      rewrite (KR 21%bv ltac:(cbn; tauto)). exact R21.
    * prreg HS2 (22%bv : bv 5) P; rewrite P, (EE2 22%nat 22%bv eq_refl).
      rewrite (Hpres 22%bv 22) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
      rewrite (KR 22%bv ltac:(cbn; tauto)). exact R22.
    * prreg HS2 (23%bv : bv 5) P; rewrite P, (EE2 23%nat 23%bv eq_refl).
      rewrite (Hpres 23%bv 23) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
      rewrite (KR 23%bv ltac:(cbn; tauto)). exact R23.
    * prreg HS2 (24%bv : bv 5) P; rewrite P, (EE2 24%nat 24%bv eq_refl).
      rewrite (Hpres 24%bv 24) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
      rewrite (KR 24%bv ltac:(cbn; tauto)). exact R24.
    * prreg HS2 (25%bv : bv 5) P; rewrite P, (EE2 25%nat 25%bv eq_refl).
      rewrite (Hpres 25%bv 25) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
      rewrite (KR 25%bv ltac:(cbn; tauto)). exact R25.
    * prreg HS2 (26%bv : bv 5) P; rewrite P, (EE2 26%nat 26%bv eq_refl).
      rewrite (Hpres 26%bv 26) by (first [unfold acallee_saved; lia | apply bv_eq; reflexivity]).
      rewrite (KR 26%bv ltac:(cbn; tauto)). exact R26.
Qed.

(* ---- segment K's facts ---- *)
(* the cursor: at or above 4096 (the payload's block, or the empty object 0x5dee20), its bytes left inside the input
   and below the allocator's ceiling *)
Lemma s14_cur_bnd : forall cx ly S (W : world SEGS) regs mem md k acc rem o O f,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  4096 <= x_cur cx f /\ x_cur cx f + x_curn cx f <= alloc_ceiling /\ x_p cx <= x_cur cx f /\
  x_cur cx f + x_curn cx f <= x_p cx + x_n cx /\ 0 <= x_curn cx f <= x_n cx /\ x_n cx < 2 ^ 26.
Proof.
intros cx ly S W regs mem md k acc rem o O f HB HC.
pose proof HB as (_ & _ & _ & _ & _ & _ & Hpn & HLEN & _).
pose proof (k14_tail_len (x_pl cx) f) as ((_ & Hcl) & _).
pose proof asan_consts as (C1 & _).
unfold x_cur, x_curn, seg_spec.seg_cur_at, seg_spec.seg_cur_n.
destruct Hpn as [[Hn0 Hp] | [Hn Hin]].
- rewrite Hp. rewrite HLEN in Hn0. unfold emptyA. lia.
- pose proof (s14_pblk cx ly S W regs mem md k acc rem o O HB HC ltac:(lia)) as (H1 & H2). lia.
Qed.
(* the atoms of segment K's seed *)
Lemma s14_EK : forall regs b0 b1 b2,
  ew (s14_E regs (s14_xK b0 b1 b2)) 32 = Z_to_bv 64 SHADOW_OFF /\ ew (s14_E regs (s14_xK b0 b1 b2)) 33 = Z_to_bv 64 b0 /\
  ew (s14_E regs (s14_xK b0 b1 b2)) 34 = Z_to_bv 64 b1 /\ ew (s14_E regs (s14_xK b0 b1 b2)) 35 = Z_to_bv 64 b2.
Proof.
intros regs b0 b1 b2.
split; [|split; [|split]].
- exact (s14_E_extra regs (s14_xK b0 b1 b2) 0 ltac:(cbn; lia) ltac:(lia)).
- exact (s14_E_extra regs (s14_xK b0 b1 b2) 1 ltac:(cbn; lia) ltac:(lia)).
- exact (s14_E_extra regs (s14_xK b0 b1 b2) 2 ltac:(cbn; lia) ltac:(lia)).
- exact (s14_E_extra regs (s14_xK b0 b1 b2) 3 ltac:(cbn; lia) ltac:(lia)).
Qed.
(* the seed of segment K at 0x85110 *)
Lemma s14_seedK : forall cx ly S W regs mem md k acc rem o O f h lo20 hi20 b0 b1 b2,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O ->
  0 <= h <= 3 -> getr regs 24 = w64 (x_cur cx f) -> 4096 <= x_cur cx f <= 0x7fffff800000 ->
  x_cur cx f + h <= alloc_ceiling ->
  getr regs 20 = w64 (x_curn cx f) -> lo20 <= x_curn cx f <= hi20 -> 0 <= x_curn cx f < 2 ^ 64 ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 ->
  (0 < h -> rdW W mem (x_cur cx f + 0) = Some b0) -> (1 < h -> rdW W mem (x_cur cx f + 1) = Some b1) ->
  (2 < h -> rdW W mem (x_cur cx f + 2) = Some b2) ->
  st_ok_pi SEGS VAL (s14_E regs (s14_xK b0 b1 b2)) (mkSS LO_K85110 sr_atoms [s14_rF; s14_rP h] None
      (s14_factsK lo20 hi20))
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + LO_K85110)) mem (seg_rom SEGS))).
Proof.
intros cx ly S W regs mem md k acc rem o O f h lo20 hi20 b0 b1 b2 HB HC Hh R24 Hcur Hcurh R20 H20 H20r B0 B1 B2
  H0 H1 H2.
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
pose proof HC as ((_ & _ & _ & _ & _ & R9 & _ & _ & _ & _ & _ & H200 & _) & _).
destruct (s14_EK regs b0 b1 b2) as (E32 & E33 & E34 & E35).
set (E := s14_E regs (s14_xK b0 b1 b2)) in *.
assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
  by (intros n rr Hn; exact (s14_E_reg regs _ n rr Hn)).
assert (E9u : bv_unsigned (ew E 9) = x_s1 cx).
{ rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
assert (E24 : ew E 24 = Z_to_bv 64 (x_cur cx f)) by (rewrite (EEo 24%nat 24%bv eq_refl), R24; reflexivity).
assert (E24u : bv_unsigned (ew E 24) = x_cur cx f) by (rewrite E24; apply unsigned_lit_small; lia).
assert (E20 : ew E 20 = Z_to_bv 64 (x_curn cx f)) by (rewrite (EEo 20%nat 20%bv eq_refl), R20; reflexivity).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- unfold E, s14_E. apply regs_ok_Eimg_Ereg.
- assert (h = 0 \/ h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | [-> | ->]]] by lia; vm_compute; reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  + unfold region_ok, s14_rF. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E9u. split; [lia|]. split; [lia|]. split.
    * intros o' Ho'. apply (apresent_writable SEGS). apply (s14_stk_pres cx ly S W regs mem md k acc rem o O HB HC). lia.
    * constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (x_s1 cx) 200 8 (SOff 32 0) SHADOW_OFF);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); unfold SHADOW_OFF; lia | cbn; lia |].
      exact (val_mem_of_rdword SEGS _ _ _ _ H200).
  + unfold region_ok, s14_rP. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E24u. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
    assert (C0 : 0 < h -> YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (x_cur cx f) (YP09.mkChunk 0 (CVal 1 (SOff 33 0))))
      by (intros Hl; exact (s14_chunk1 W mem E (x_cur cx f) 0 33 b0 E33 B0 (H0 Hl))).
    assert (C1' : 1 < h -> YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (x_cur cx f) (YP09.mkChunk 1 (CVal 1 (SOff 34 0))))
      by (intros Hl; exact (s14_chunk1 W mem E (x_cur cx f) 1 34 b1 E34 B1 (H1 Hl))).
    assert (C2' : 2 < h -> YP09.chunk_ok SEGS E (mrestrict (w_H W) mem) (x_cur cx f) (YP09.mkChunk 2 (CVal 1 (SOff 35 0))))
      by (intros Hl; exact (s14_chunk1 W mem E (x_cur cx f) 2 35 b2 E35 B2 (H2 Hl))).
    unfold s14_bchunks.
    assert (h = 0 \/ h = 1 \/ h = 2 \/ h = 3) as [-> | [-> | [-> | ->]]] by lia;
      [change (Z.to_nat 0) with 0%nat | change (Z.to_nat 1) with 1%nat | change (Z.to_nat 2) with 2%nat
      | change (Z.to_nat 3) with 3%nat]; cbn [firstn];
      repeat apply Forall_cons; try apply Forall_nil; first [apply C0; lia | apply C1'; lia | apply C2'; lia].
- cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint, s14_rF, s14_rP.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite E9u, E24u.
  repeat match goal with |- _ /\ _ => split end; try exact I; lia.
- split; [|split; [exact I | exact I]].
  cbn [s14_factsK f_atoms atoms_ok S14F9 fst snd].
  split; [exact (s14_s1F cx ly S W regs mem md k acc rem o O _ HB HC)|].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E32, E24, E20, E33, E34, E35.
  rewrite !unsigned_lit_small by (unfold SHADOW_OFF; lia). rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; first [exact I | lia | reflexivity].
Qed.
(* the shadow entry of the h cursor bytes *)
Lemma s14_shK : forall (W : world SEGS) mem E cur h,
  ew E 32 = Z_to_bv 64 SHADOW_OFF -> ew E 24 = Z_to_bv 64 cur -> 0 <= cur -> 0 <= h -> cur + h < 2 ^ 64 ->
  range_addressable (rdW W mem) SHADOW_OFF cur h ->
  (forall x, cur <= x < cur + h -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  sh_ok SEGS S14x (s14_SHK h) E (mrestrict (w_H W) mem).
Proof.
intros W mem E cur h E32 E24 H0 Hh Hhi HRA Hap. unfold sh_ok, s14_SHK. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem E S14x 24 cur h cur 0 h HRA).
- unfold S14x. rewrite (U_atom E 32 SHADOW_OFF E32) by (unfold SHADOW_OFF; lia). reflexivity.
- rewrite (U_atom E 24 cur E24) by lia. reflexivity.
- lia.
- lia.
- intros x Hx. apply Hap. lia.
Qed.
(* segment K's one write window, 160(s1) .. 168(s1), is in the function's stack window *)
Lemma s14_awrK : forall cx E h FP bl0 blc fr0 lyx own,
  lt_base B MT cx -> bv_unsigned (ew E 9) = x_s1 cx ->
  awr_ok SEGS B E [s14_rF; s14_rP h] STK_LLVMFuzzerTestOneInput (x_sp0 cx) FP bl0 blc fr0 lyx own.
Proof.
intros cx E h FP bl0 blc fr0 lyx own HB Hew a (r & Hin & Ha).
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
destruct Hin as [<- | [<- | []]]; cbn [s14_rF s14_rP YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; [|lia].
rewrite Hew in Ha. left. assert (HLS : STK_LLVMFuzzerTestOneInput = 32768) by reflexivity. lia.
Qed.

(* the cut S4_T from a state a run of segment K reaches *)
Lemma s14_K_to_T : forall f, S4_T_stmt f ->
  forall cx ly S W regs mem md k acc c m regs' mem' md',
  lt_base B MT cx -> sa_frm0 -> Z.of_nat f < x_nf cx -> S4_body cx ly S W regs mem md k acc c m f ->
  lt_slots cx (rdW W mem) (LT_L cx c m ++ [(176, seg_spec.b2z (seg_spec.seg_ret (x_st cx f)))]) ->
  ajournal SEGS B STK_LLVMFuzzerTestOneInput (x_sp0 cx) (ltoi_PG longlA) (x_ly cx) (x_S cx) (x_W cx) (x_mem cx)
    (x_md cx) [(LT_FCLS, x_fpos cx)] ly S W mem' md' k ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 160 <= a < x_s1 cx + 168) -> rdW W mem' a = rdW W mem a) ->
  rdword (rdW W mem') (x_s1 cx + 160) = Some (bv_unsigned (getr regs' 20)) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 ->
  getr regs' 18 = w64 (x_nf cx) -> getr regs' 19 = w64 (x_at cx f) -> getr regs' 20 = w64 (x_n1 cx f) ->
  getr regs' 21 = w64 0 -> getr regs' 22 = w64 m -> getr regs' 23 = w64 (x_np cx f) ->
  getr regs' 24 = w64 (x_at cx f + x_np cx f) -> getr regs' 25 = w64 (Z.of_nat f) ->
  getr regs' 26 = w64 (seg_spec.seg_lb (x_pl cx) f) ->
  SRr SEGS W (cfg_at SEGS (BASE + LO_S4T) regs' mem' md') (lt_post B MT cx).
Proof.
intros f HTT cx ly S W regs mem md k acc c m regs' mem' md' HB Hfrm Hf HBODY HSL HJ' KM H160
  P2 P3 P4 P8 P9 R18 R19 R20 R21 R22 R23 R24 R25 R26.
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
pose proof (s14_pt cx f HB) as (_ & _ & Hnp0 & Hnpn & Hn1n).
pose proof HB as (_ & _ & _ & _ & _ & _ & Hpn & _).
assert (Hn26 : x_n cx < 2 ^ 26) by (destruct Hpn as [[-> _] | [H _]]; lia).
destruct HBODY as (HC & HHc & HHm & HCM & HCNT).
pose proof (K_core_keep cx ly S W regs mem md k acc (6 + 2 * (x_nf cx - Z.of_nat f)) LFO0
  [(m, seg_spec.SEG_M_SIZE); (c, seg_spec.SEG_C_SIZE)] regs' mem' md' (x_s1 cx + 160) (x_s1 cx + 168) HB HC HJ' KM
  ltac:(lia) ltac:(lia) ltac:(lia) P2 P3 P4 P8 P9) as HC'.
pose proof (proj1 HJ') as HAR'.
pose proof HC as (_ & _ & HBL & _).
assert (Hinc : In (c, seg_spec.SEG_C_SIZE) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. right. left. reflexivity. }
assert (Hinm : In (m, seg_spec.SEG_M_SIZE) (ablocks B ly S)).
{ apply (Permutation_in _ (Permutation_sym HBL)). cbn [app]. left. reflexivity. }
pose proof (proj1 (proj1 HC)) as HJ0. pose proof (proj1 HJ0) as HAR0.
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR0 Hinc) as (_ & Hc4096 & Hcceil & _).
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR0 Hinm) as (_ & Hm4096 & Hmceil & _).
pose proof (req_size_pos seg_spec.SEG_C_SIZE ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as [_ Hrc].
pose proof (req_size_pos seg_spec.SEG_M_SIZE ltac:(unfold seg_spec.SEG_M_SIZE; lia)) as [_ Hrm].
apply (HTT cx ly S W regs' mem' md' k acc c m HB Hfrm Hf); [| exact R18 | exact R19 | exact R20 | exact R21 | exact R22
  | exact R23 | exact R24 | exact R25 | exact R26 |].
- split; [exact HC'|]. split; [exact (K_hblk ly S W mem' md' c _ HAR' Hinc)|].
  split; [exact (K_hblk ly S W mem' md' m _ HAR' Hinm)|]. split; [|exact HCNT].
  apply (k14_cm_kept (rdW W mem)); [| |exact HCM]; intros x Hx; apply KM; lia.
- intros o v Hin. rewrite in_app_iff in Hin. destruct Hin as [Hin | Hin].
  + apply (s14_slots_win cx (rdW W mem) (rdW W mem') (LT_L cx c m) 160 168).
    * intros x Hx0 Hx. apply KM; [exact Hx0 | exact Hx].
    * intros o' v' Hin'. pose proof (s14_LT_L_off cx c m o' v' Hin'). lia.
    * intros o' v' Hin'. apply HSL. apply in_or_app. left. exact Hin'.
    * exact Hin.
  + cbn [In] in Hin. destruct Hin as [Hq | [Hq | []]]; injection Hq as <- <-.
    * rewrite H160, R20. unfold w64. apply f_equal. apply unsigned_lit_small. lia.
    * apply (k14_word_kept (rdW W mem)); [|apply HSL; apply in_or_app; right; left; reflexivity].
      intros x Hx. apply KM; lia.
Qed.

(* the word the run stored at 160(s1) is s4's final term *)
Ltac s14_slot160 HS Hagr E9u W cx Hslot :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E' ?ssx (restrict _ ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) (20%bv : bv 5)) in
      let r0 := eval vm_compute in (nth 0 (ss_mem ssx) s14_rF) in
      let HR0 := fresh "HR0" in let HRx := fresh "HRx" in
      pose proof (st_ok_pi_region_nth E' ssx _ 0%nat r0 HS ltac:(vm_compute; reflexivity)) as HR0;
      pose proof (st_ok_pi_restrict_reg (w_H W) E' ssx msx (20%bv : bv 5) HS) as HRx;
      change (sr_get (ss_regs ssx) (20%bv : bv 5)) with e in HRx;
      cbn [ms_regs restrict mkst] in HRx;
      assert (Hslot : rdword (rdW W (ms_mem msx)) (x_s1 cx + 160) = Some (bv_unsigned (getr (ms_regs msx) 20)))
        by (apply (s14_region_word E' (w_H W) (ms_mem msx) r0 9 (x_s1 cx) 160 e);
            [exact HR0 | reflexivity | first [exact E9u | rewrite (proj1 Hagr 9%nat ltac:(lia)); exact E9u] | cbn; tauto
            | rewrite <- HRx; symmetry; apply Z_to_bv_bv_unsigned
            | pose proof (bv_unsigned_in_range 64 (getr (ms_regs msx) 20)) as RR; change (bv_modulus 64) with (2 ^ 64) in RR;
              exact RR])
  end.

(* the cursor's first h bytes lie in the payload's block: addressable, and outside the shadow band *)
Lemma s14_cursh : forall cx ly S (W : world SEGS) regs mem md k acc rem o O f h,
  lt_base B MT cx -> lt_core B MT cx ly S W regs mem md k acc rem o O -> 0 < h <= x_curn cx f ->
  range_addressable (rdW W mem) SHADOW_OFF (x_cur cx f) h /\
  (forall x, x_cur cx f <= x < x_cur cx f + h -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
Proof.
intros cx ly S W regs mem md k acc rem o O f h HB HC Hh.
pose proof (s14_cur_bnd cx ly S W regs mem md k acc rem o O f HB HC) as (Hc4096 & Hcceil & Hpc & Hcpn & Hcn & Hn26).
assert (Hn : 0 < x_n cx) by lia.
pose proof HC as ((HJ & _) & _ & HBL & _). pose proof (proj1 HJ) as HAR.
pose proof (K_payload_live cx ly S O HB HBL Hn) as Hin.
destruct (al_blocks _ _ LAWS ly S W mem md _ _ HAR Hin) as (_ & Hp4096 & Hpceil & Happ & _).
pose proof (req_size_pos (x_n cx) ltac:(lia)) as [_ Hreq].
pose proof asan_consts as (C1 & _).
split.
- apply (range_addressable_of_block SEGS B LAWS ly S W mem md (x_p cx) (x_n cx)); [exact HAR | exact Hin | lia | lia].
- intros x Hx. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *. lia.
Qed.
(* ---- segment K: 0x85110 .. 0x851d8, lb, the u16, the take (checks 4-6; traps 0x8511c .. 0x851d4), 160(s1) := N1,
   to S4_T f ---- *)
Lemma s14_K : forall f, S4_T_stmt f -> LT_K85110_stmt B MT f.
Proof.
unfold LT_K85110_stmt.
intros f HTT cx ly S W regs mem md k acc c m HB Hfrm Hf HC HHc HHm R14 R18 R20 R21 R22 R24 R25 HSL HCM HCNT.
assert (HBODY : S4_body cx ly S W regs mem md k acc c m f) by exact (conj HC (conj HHc (conj HHm (conj HCM HCNT)))).
pose proof (K_sp cx HB) as (Hal0 & Hsp0 & Hsp47 & Hs1al & Hs1lo & Hs1hi).
pose proof asan_consts as (C1 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HC as ((HJ & _ & _ & _ & _ & R9 & _) & _).
pose proof (s14_cur_bnd cx ly S W regs mem md k acc _ _ _ f HB HC) as (Hc4096 & Hcceil & Hpc & Hcpn & Hcn & Hn26).
pose proof (K_cur_rd cx ly S W regs mem md k acc _ _ _ f HB HC) as HCR.
pose proof (k14_lb_eq (x_pl cx) f Hf) as Hlb.
pose proof (k14_cur_bytes (x_pl cx) f) as Hbytes.
pose proof (s14_vals cx f) as (Vat & Vn1 & Vnp & Vcn).
revert HCR Hlb Hbytes Vat Vn1 Vnp Vcn.
destruct (seg_spec.seg_cur (x_pl cx) f) as [|b0 [|b1 [|b2 r]]] eqn:Ecur; intros HCR Hlb Hbytes Vat Vn1 Vnp Vcn.
- (* no byte left: s10 = 0, the length 0, nothing taken *)
  destruct k14_shape0 as (Q_lb & Q_tl & Q_take & _).
  rewrite Q_tl in Vat, Vn1. rewrite Q_take in Vnp. rewrite Q_lb in Hlb. cbn [length Z.of_nat] in Vat, Vn1, Vnp, Vcn.
  pose proof (s14_seedK cx ly S W regs mem md k acc _ _ _ f 0 0 0 0 0 0 HB HC ltac:(lia) R24 ltac:(lia) ltac:(lia)
    R20 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros; lia) ltac:(intros; lia) ltac:(intros; lia))
    as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (20%bv : bv 5) 0 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R20, Vcn; reflexivity)
    eq_refl) as HS1. clear HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (14%bv : bv 5) 1 HS1 ltac:(cbn [ms_regs restrict mkst]; exact R14) eq_refl) as HS.
  clear HS1.
  destruct (s14_EK regs 0 0 0) as (E32 & _ & _ & _).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs (s14_xK 0 0 0)) n = getr regs rr)
    by (intros n rr Hn; exact (s14_E_reg regs _ n rr Hn)).
  assert (E24 : ew (s14_E regs (s14_xK 0 0 0)) 24 = Z_to_bv 64 (x_cur cx f))
    by (rewrite (EEo 24%nat 24%bv eq_refl), R24; reflexivity).
  assert (E9u : bv_unsigned (ew (s14_E regs (s14_xK 0 0 0)) 9) = x_s1 cx).
  { rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (s14_shK W mem (s14_E regs (s14_xK 0 0 0)) (x_cur cx f) 0 E32 E24 ltac:(lia) ltac:(lia) ltac:(lia)
    ltac:(intros x Hx; lia) ltac:(intros x Hx; lia)) as SHOK.
  assert (HEI : img_env VAL A_LIM (s14_E regs (s14_xK 0 0 0))) by (unfold s14_E; apply Eimg_env).
  remember (s14_E regs (s14_xK 0 0 0)) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4T.
  { exact (s14_awrK cx E 0 _ _ _ _ _ _ HB E9u). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  s14_envlow HS E Hagr.
  s14_slot160 HS Hagr E9u W cx H160.
  pmkst HS.
  pose proof (s14_winK_kept E W mem (ms_mem ms) 0 (x_s1 cx) HFr E9u) as KM.
  apply (s14_K_to_T f HTT cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) md1 HB Hfrm Hf HBODY HSL HJ KM H160).
  all: first [s14_kept HS Hagr EEo | s14_val HS; s14_toE E Hagr].
  all: rewrite ?U_lit by lia; rewrite ?(U_atom E 24 (x_cur cx f) E24) by lia; lia.
- (* one byte left: s10 = lb, the length 0, nothing taken *)
  pose proof (Forall_inv Hbytes) as B0. cbv beta in B0.
  pose proof (HCR 0%nat ltac:(cbn; lia)) as HR0. cbn [nth Z.of_nat] in HR0.
  destruct (k14_shape1 b0) as (Q_lb & Q_tl & Q_take & _).
  rewrite Q_tl in Vat, Vn1. rewrite Q_take in Vnp. rewrite Q_lb in Hlb. cbn [length Z.of_nat] in Vat, Vn1, Vnp, Vcn.
  destruct (s14_cursh cx ly S W regs mem md k acc _ _ _ f 1 HB HC ltac:(lia)) as (HRA & HAP).
  pose proof (s14_seedK cx ly S W regs mem md k acc _ _ _ f 1 1 1 b0 0 0 HB HC ltac:(lia) R24 ltac:(lia) ltac:(lia)
    R20 ltac:(lia) ltac:(lia) B0 ltac:(lia) ltac:(lia) ltac:(intros; exact HR0) ltac:(intros; lia) ltac:(intros; lia))
    as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (20%bv : bv 5) 1 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R20, Vcn; reflexivity)
    eq_refl) as HS1. clear HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (14%bv : bv 5) 1 HS1 ltac:(cbn [ms_regs restrict mkst]; exact R14) eq_refl) as HS.
  clear HS1.
  destruct (s14_EK regs b0 0 0) as (E32 & E33 & _ & _).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs (s14_xK b0 0 0)) n = getr regs rr)
    by (intros n rr Hn; exact (s14_E_reg regs _ n rr Hn)).
  assert (E24 : ew (s14_E regs (s14_xK b0 0 0)) 24 = Z_to_bv 64 (x_cur cx f))
    by (rewrite (EEo 24%nat 24%bv eq_refl), R24; reflexivity).
  assert (E9u : bv_unsigned (ew (s14_E regs (s14_xK b0 0 0)) 9) = x_s1 cx).
  { rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (s14_shK W mem (s14_E regs (s14_xK b0 0 0)) (x_cur cx f) 1 E32 E24 ltac:(lia) ltac:(lia) ltac:(lia)
    HRA HAP) as SHOK.
  assert (HEI : img_env VAL A_LIM (s14_E regs (s14_xK b0 0 0))) by (unfold s14_E; apply Eimg_env).
  remember (s14_E regs (s14_xK b0 0 0)) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4T.
  { exact (s14_awrK cx E 1 _ _ _ _ _ _ HB E9u). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  s14_envlow HS E Hagr.
  s14_slot160 HS Hagr E9u W cx H160.
  pmkst HS.
  pose proof (s14_winK_kept E W mem (ms_mem ms) 1 (x_s1 cx) HFr E9u) as KM.
  apply (s14_K_to_T f HTT cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) md1 HB Hfrm Hf HBODY HSL HJ KM H160).
  all: first [s14_kept HS Hagr EEo | s14_val HS; s14_toE E Hagr].
  all: rewrite ?U_lit by lia;
    rewrite ?(U_atom_off E 24 (x_cur cx f) 1 E24), ?(U_atom E 33 b0 E33) by lia; lia.
- (* two bytes left: s10 = lb, the length's low byte, nothing taken *)
  pose proof (Forall_inv Hbytes) as B0. pose proof (Forall_inv (Forall_inv_tail Hbytes)) as B1. cbv beta in B0, B1.
  pose proof (HCR 0%nat ltac:(cbn; lia)) as HR0. pose proof (HCR 1%nat ltac:(cbn; lia)) as HR1.
  cbn [nth Z.of_nat] in HR0, HR1.
  destruct (k14_shape2 b0 b1) as (Q_lb & Q_tl & Q_take & _).
  rewrite Q_tl in Vat, Vn1. rewrite Q_take in Vnp. rewrite Q_lb in Hlb. cbn [length Z.of_nat] in Vat, Vn1, Vnp, Vcn.
  destruct (s14_cursh cx ly S W regs mem md k acc _ _ _ f 2 HB HC ltac:(lia)) as (HRA & HAP).
  pose proof (s14_seedK cx ly S W regs mem md k acc _ _ _ f 2 2 2 b0 b1 0 HB HC ltac:(lia) R24 ltac:(lia) ltac:(lia)
    R20 ltac:(lia) ltac:(lia) B0 B1 ltac:(lia) ltac:(intros; exact HR0) ltac:(intros; exact HR1) ltac:(intros; lia))
    as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (20%bv : bv 5) 2 HS0 ltac:(cbn [ms_regs restrict mkst]; rewrite R20, Vcn; reflexivity)
    eq_refl) as HS1. clear HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (14%bv : bv 5) 1 HS1 ltac:(cbn [ms_regs restrict mkst]; exact R14) eq_refl) as HS.
  clear HS1.
  destruct (s14_EK regs b0 b1 0) as (E32 & E33 & E34 & _).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs (s14_xK b0 b1 0)) n = getr regs rr)
    by (intros n rr Hn; exact (s14_E_reg regs _ n rr Hn)).
  assert (E24 : ew (s14_E regs (s14_xK b0 b1 0)) 24 = Z_to_bv 64 (x_cur cx f))
    by (rewrite (EEo 24%nat 24%bv eq_refl), R24; reflexivity).
  assert (E9u : bv_unsigned (ew (s14_E regs (s14_xK b0 b1 0)) 9) = x_s1 cx).
  { rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (s14_shK W mem (s14_E regs (s14_xK b0 b1 0)) (x_cur cx f) 2 E32 E24 ltac:(lia) ltac:(lia) ltac:(lia)
    HRA HAP) as SHOK.
  assert (HEI : img_env VAL A_LIM (s14_E regs (s14_xK b0 b1 0))) by (unfold s14_E; apply Eimg_env).
  remember (s14_E regs (s14_xK b0 b1 0)) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4T.
  { exact (s14_awrK cx E 2 _ _ _ _ _ _ HB E9u). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  s14_envlow HS E Hagr.
  s14_slot160 HS Hagr E9u W cx H160.
  pmkst HS.
  pose proof (s14_winK_kept E W mem (ms_mem ms) 2 (x_s1 cx) HFr E9u) as KM.
  apply (s14_K_to_T f HTT cx ly S W regs mem md k acc c m (ms_regs ms) (ms_mem ms) md1 HB Hfrm Hf HBODY HSL HJ KM H160).
  all: first [s14_kept HS Hagr EEo | s14_val HS; s14_toE E Hagr].
  all: rewrite ?U_lit by lia;
    rewrite ?(U_atom_off E 24 (x_cur cx f) 2 E24), ?(U_atom E 33 b0 E33) by lia; lia.
- (* three or more bytes left: s10 = lb, the length lo + 256 hi, NP = min(length, left) taken *)
  pose proof (Forall_inv Hbytes) as B0. pose proof (Forall_inv (Forall_inv_tail Hbytes)) as B1.
  pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hbytes))) as B2. cbv beta in B0, B1, B2.
  pose proof (HCR 0%nat ltac:(cbn; lia)) as HR0. pose proof (HCR 1%nat ltac:(cbn; lia)) as HR1.
  pose proof (HCR 2%nat ltac:(cbn; lia)) as HR2.
  cbn [nth Z.of_nat] in HR0, HR1, HR2.
  destruct (k14_shape3 b0 b1 b2 r B1 B2) as (Q_lb & Q_tl & Q_take).
  rewrite Q_tl in Vat, Vn1. rewrite Q_take in Vnp. rewrite Q_lb in Hlb. cbn [length] in Vat, Vn1, Vnp, Vcn.
  rewrite length_firstn in Vnp.
  destruct (s14_cursh cx ly S W regs mem md k acc _ _ _ f 3 HB HC ltac:(lia)) as (HRA & HAP).
  pose proof (s14_seedK cx ly S W regs mem md k acc _ _ _ f 3 3 (2 ^ 26) b0 b1 b2 HB HC ltac:(lia) R24 ltac:(lia)
    ltac:(lia) R20 ltac:(lia) ltac:(lia) B0 B1 B2 ltac:(intros; exact HR0) ltac:(intros; exact HR1)
    ltac:(intros; exact HR2)) as HS0.
  pose proof (st_ok_pi_pin_reg' _ _ _ (14%bv : bv 5) 1 HS0 ltac:(cbn [ms_regs restrict mkst]; exact R14) eq_refl) as HS.
  clear HS0.
  destruct (s14_EK regs b0 b1 b2) as (E32 & E33 & E34 & E35).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew (s14_E regs (s14_xK b0 b1 b2)) n = getr regs rr)
    by (intros n rr Hn; exact (s14_E_reg regs _ n rr Hn)).
  assert (E24 : ew (s14_E regs (s14_xK b0 b1 b2)) 24 = Z_to_bv 64 (x_cur cx f))
    by (rewrite (EEo 24%nat 24%bv eq_refl), R24; reflexivity).
  assert (E9u : bv_unsigned (ew (s14_E regs (s14_xK b0 b1 b2)) 9) = x_s1 cx).
  { rewrite (EEo 9%nat 9%bv eq_refl), R9. unfold w64. apply unsigned_lit_small. lia. }
  pose proof (s14_shK W mem (s14_E regs (s14_xK b0 b1 b2)) (x_cur cx f) 3 E32 E24 ltac:(lia) ltac:(lia) ltac:(lia)
    HRA HAP) as SHOK.
  assert (HEI : img_env VAL A_LIM (s14_E regs (s14_xK b0 b1 b2))) by (unfold s14_E; apply Eimg_env).
  remember (s14_E regs (s14_xK b0 b1 b2)) as E eqn:HE. clear HE.
  unfold cfg_at, w64.
  paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4T.
  { exact (s14_awrK cx E 3 _ _ _ _ _ _ HB E9u). }
  lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md1 := d) in *; clearbody md1 end.
  assert (E20 : ew E 20 = Z_to_bv 64 (x_curn cx f)) by (rewrite (EEo 20%nat 20%bv eq_refl), R20; reflexivity).
  s14_envlow HS E Hagr.
  psrr_branch_tok RUN BR HS SHOK S14span.
  + (* the length is below the bytes left after the header: NP = the length *)
    assert (Hc1 : b1 + b2 * 256 < x_curn cx f - 3).
    { rewrite branch_ltu_U in Hc. s14_HcE Hc E Hagr. rewrite (s14_U_len E b1 b2 E34 E35 B1 B2) in Hc.
      rewrite (U_atom_off E 20 (x_curn cx f) (-3) E20) in Hc by lia. apply Z.ltb_lt in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4T.
    { apply (s14_awrK cx _ 3 _ _ _ _ _ _ HB). s14_e9 E9u. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
    s14_envlow HS E Hagr2.
    psrr_branch_tok RUN BR HS SHOK S14span.
    { (* the trap 0x85ff8 (0x851c4): P1 + NP would wrap; it does not *)
      exfalso. rewrite branch_ltu_U in Hc. s14_HcE Hc E Hagr2.
      rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc. rewrite (s14_U_len E b1 b2 E34 E35 B1 B2) in Hc.
      rewrite (U_atom_off E 24 (x_cur cx f) 3 E24) in Hc by lia.
      rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4T.
    { apply (s14_awrK cx _ 3 _ _ _ _ _ _ HB). s14_e9 E9u. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
    s14_envlow HS E Hagr3.
    s14_slot160 HS Hagr3 E9u W cx H160.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst _ _ (ms_mem ?msf) _; cfg_model := ?mdf |} _ =>
      assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 160 <= a < x_s1 cx + 168) ->
        rdW W (ms_mem msf) a = rdW W mem a) by (s14_chain E9u cx);
      apply (s14_K_to_T f HTT cx ly S W regs mem md k acc c m (ms_regs msf) (ms_mem msf) mdf HB Hfrm Hf HBODY HSL HJ
        KM H160)
    end.
    all: first [s14_kept HS Hagr3 EEo | s14_val HS; s14_toE E Hagr3].
    all: rewrite ?(s14_U_len E b1 b2 E34 E35 B1 B2), ?(U_SAlu E ALU_ADD); cbn [zalu_raw];
      rewrite ?(s14_U_len E b1 b2 E34 E35 B1 B2), ?(U_atom_off E 24 (x_cur cx f) 3 E24),
        ?(U_atom_off E 20 (x_curn cx f) (-3) E20), ?(U_atom E 20 (x_curn cx f) E20), ?(U_atom E 24 (x_cur cx f) E24),
        ?(U_atom E 33 b0 E33) by lia;
      rewrite ?zcanon_id by (unfold M64; lia); lia.
  + (* the length is at least the bytes left after the header: NP = the bytes left *)
    assert (Hc1 : x_curn cx f - 3 <= b1 + b2 * 256).
    { rewrite branch_ltu_U in Hc. s14_HcE Hc E Hagr. rewrite (s14_U_len E b1 b2 E34 E35 B1 B2) in Hc.
      rewrite (U_atom_off E 20 (x_curn cx f) (-3) E20) in Hc by lia. apply Z.ltb_ge in Hc. exact Hc. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4T.
    { apply (s14_awrK cx _ 3 _ _ _ _ _ _ HB). s14_e9 E9u. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md2 := d) in *; clearbody md2 end.
    s14_envlow HS E Hagr2.
    psrr_branch_tok RUN BR HS SHOK S14span.
    { (* the trap 0x85ff8 (0x851c4): P1 + NP would wrap; it does not *)
      exfalso. rewrite branch_ltu_U in Hc. s14_HcE Hc E Hagr2.
      rewrite U_SAlu in Hc. cbn [zalu_raw] in Hc.
      rewrite (U_atom E 20 (x_curn cx f) E20), (U_atom E 24 (x_cur cx f) E24) in Hc by lia.
      rewrite (U_atom_off E 24 (x_cur cx f) 3 E24) in Hc by lia.
      rewrite zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc. lia. }
    clear Hc.
    paj_run_to_tok RUNTO HS HJ SHOK S14span LO_S4T.
    { apply (s14_awrK cx _ 3 _ _ _ _ _ _ HB). s14_e9 E9u. }
    lazymatch goal with |- SRr _ _ {| cfg_ms := _; cfg_model := ?d |} _ => set (md3 := d) in *; clearbody md3 end.
    s14_envlow HS E Hagr3.
    s14_slot160 HS Hagr3 E9u W cx H160.
    pmkst HS.
    lazymatch goal with |- SRr _ _ {| cfg_ms := mkst _ _ (ms_mem ?msf) _; cfg_model := ?mdf |} _ =>
      assert (KM : forall a, 0 <= a < 2 ^ 64 -> ~ (x_s1 cx + 160 <= a < x_s1 cx + 168) ->
        rdW W (ms_mem msf) a = rdW W mem a) by (s14_chain E9u cx);
      apply (s14_K_to_T f HTT cx ly S W regs mem md k acc c m (ms_regs msf) (ms_mem msf) mdf HB Hfrm Hf HBODY HSL HJ
        KM H160)
    end.
    all: first [s14_kept HS Hagr3 EEo | s14_val HS; s14_toE E Hagr3].
    all: rewrite ?(s14_U_len E b1 b2 E34 E35 B1 B2), ?(U_SAlu E ALU_ADD); cbn [zalu_raw];
      rewrite ?(s14_U_len E b1 b2 E34 E35 B1 B2), ?(U_atom_off E 24 (x_cur cx f) 3 E24),
        ?(U_atom_off E 20 (x_curn cx f) (-3) E20), ?(U_atom E 20 (x_curn cx f) E20), ?(U_atom E 24 (x_cur cx f) E24),
        ?(U_atom E 33 b0 E33) by lia;
      rewrite ?zcanon_id by (unfold M64; lia); lia.
Qed.

(* ---- S04: K85110 f -> S4_T f -> S4_M f -> S4_C f -> K85210 f ---- *)
Lemma lt_seg_S04 : lt_seg_S04_stmt B MT.
Proof. intros f HK. exact (s14_K f (s14_T f (s14_M f (s14_C f HK)))). Qed.

End e.
End f.
End d.
Print Assumptions lt_seg_S04.
